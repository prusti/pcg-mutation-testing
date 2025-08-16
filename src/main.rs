#![feature(rustc_private)]
#![feature(let_chains)]

extern crate borrowck;

use pcg_mutation_testing::MutatorData;

use pcg_mutation_testing::mutator::Mutant;
use pcg_mutation_testing::mutator::MutantRange;
use pcg_mutation_testing::mutator::Mutation;
use pcg_mutation_testing::mutator::Mutator;

use pcg_mutation_testing::mutator::expiry_order::AbstractExpiryOrder;
use pcg_mutation_testing::mutator::expiry_order::BorrowExpiryOrder;
use pcg_mutation_testing::mutator::move_from_borrowed::MoveFromBorrowed;
use pcg_mutation_testing::mutator::mutably_lend_shared::MutablyLendShared;
use pcg_mutation_testing::mutator::read_from_write::ReadFromWriteOnly;
use pcg_mutation_testing::mutator::write_to_shared::WriteToShared;

use pcg_mutation_testing::utils::env_feature_enabled;

use std::cell::RefCell;
use std::collections::HashMap;
use std::collections::HashSet;
use std::fs::File;
use std::io::Write;
use std::path::Path;
use std::path::PathBuf;

use indexmap::map::IndexMap;

use serde::Serialize;

use pcg_mutation_testing::rustc_interface;
use pcg_mutation_testing::rustc_interface::borrowck::consumers;

use pcg_mutation_testing::rustc_interface::errors::fallback_fluent_bundle;

use pcg_mutation_testing::rustc_interface::middle::query::queries::mir_borrowck::ProvidedValue;
use pcg_mutation_testing::rustc_interface::middle::ty::TyCtxt;
use pcg_mutation_testing::rustc_interface::middle::util::Providers;

use pcg_mutation_testing::rustc_interface::session::Session;

use pcg_mutation_testing::rustc_interface::driver::Callbacks;
use pcg_mutation_testing::rustc_interface::driver::DEFAULT_LOCALE_RESOURCES;

use pcg_mutation_testing::errors::get_registered_errors;
use pcg_mutation_testing::errors::initialize_error_tracking;
use pcg_mutation_testing::errors::track_body_error_codes;

use pcg_mutation_testing::rustc_interface::driver;
use pcg_mutation_testing::rustc_interface::driver::Compilation;

use pcg_mutation_testing::rustc_interface::hir;
use pcg_mutation_testing::rustc_interface::hir::def_id::LocalDefId;

use pcg_mutation_testing::rustc_interface::interface::interface::Compiler;
use pcg_mutation_testing::rustc_interface::interface::Config;

use pcg_mutation_testing::rustc_interface::ast::Crate;

use pcg::borrow_checker::r#impl::NllBorrowCheckerImpl;
use pcg::pcg::BodyWithBorrowckFacts;
use pcg::run_pcg;
use pcg::utils::CompilerCtxt;
use pcg::PcgCtxt;
use pcg::PcgOutput;

use tracing::info;

// Thread-local map for storing intermediate compilation results that our tool will mutate
thread_local! {
    pub static BODIES:
        RefCell<HashMap<LocalDefId, BodyWithBorrowckFacts<'static>>> =
        RefCell::new(HashMap::default());
}

// Indicates the result of running the borrow checker on a mutant
#[derive(Serialize)]
enum BorrowCheckInfo {
    NoRun,
    Passed,
    Failed { error_codes: HashSet<String> },
}

// Information we record about each mutant if `MUTANTS_LOG` is set
#[derive(Serialize)]
struct LogEntry {
    mutation_type: String,
    borrow_check_info: BorrowCheckInfo,
    // ID of the MIR definition that this mutant was created from
    definition: String,
    range: MutantRange,
    info: String,
}

// Allows us to un our tool from within a compiler session
struct MutatorCallbacks {
    mutations: Vec<Box<dyn Mutation + Send>>,
    results_dir: PathBuf,
}

impl Callbacks for MutatorCallbacks {
    fn config(&mut self, config: &mut Config) {
        assert!(config.override_queries.is_none());
        config.override_queries = Some(set_mir_borrowck);
    }

    fn after_crate_root_parsing<'tcx>(
        &mut self,
        compiler: &Compiler,
        _crate: &Crate,
    ) -> Compilation {
        let fallback_bundle = fallback_fluent_bundle(DEFAULT_LOCALE_RESOURCES.to_vec(), false);
        compiler
            .sess
            .dcx()
            .make_silent(fallback_bundle, None, false);
        Compilation::Continue
    }

    fn after_analysis(&mut self, compiler: &Compiler, tcx: TyCtxt<'_>) -> Compilation {
        run_mutation_tests(tcx, compiler, &mut self.mutations, &self.results_dir);
        if in_cargo_crate() {
            Compilation::Continue
        } else {
            Compilation::Stop
        }
    }
}

fn mir_borrowck<'tcx>(tcx: TyCtxt<'tcx>, def_id: LocalDefId) -> ProvidedValue<'tcx> {
    let body_with_facts = {
        let consumer_opts = consumers::ConsumerOptions::PoloniusInputFacts;
        consumers::get_body_with_borrowck_facts(tcx, def_id, consumer_opts)
    };
    // Store intermediate compilation results in our thread-local map
    unsafe {
        let body: pcg::rustc_interface::borrowck::BodyWithBorrowckFacts<'tcx> =
            std::mem::transmute(body_with_facts);
        let body: BodyWithBorrowckFacts<'tcx> = body.into();
        let body: BodyWithBorrowckFacts<'static> = std::mem::transmute(body);
        BODIES.with(|state| {
            let mut map = state.borrow_mut();
            assert!(map.insert(def_id, body).is_none());
        });
    }
    let mut providers = Providers::default();
    rustc_interface::borrowck::provide(&mut providers);
    let original_mir_borrowck = providers.mir_borrowck;
    original_mir_borrowck(tcx, def_id)
}

fn set_mir_borrowck(_session: &Session, providers: &mut Providers) {
    providers.mir_borrowck = mir_borrowck;
}

fn cargo_crate_name() -> Option<String> {
    std::env::var("CARGO_CRATE_NAME").ok()
}

// The main loop of our tool. Runs every `Mutation` in `Mutations` on each
// MIR body in `BODIES`
fn run_mutation_tests<'tcx>(
    tcx: TyCtxt<'tcx>,
    compiler: &Compiler,
    mutations: &mut Vec<Box<dyn Mutation + Send>>,
    results_dir: &PathBuf,
) {
    if in_cargo_crate() && std::env::var("CARGO_PRIMARY_PACKAGE").is_err() {
        // We're running in cargo, but not compiling the primary package
        // We don't want to check dependencies, so abort
        return;
    }

    // Run every `Mutation` on a given MIR body
    fn run_mutation_tests_for_body<'a, 'mir: 'a, 'tcx: 'mir>(
        tcx: TyCtxt<'tcx>,
        compiler: &'a Compiler,
        mutations: &'a mut Vec<Box<dyn Mutation + Send>>,
        mutants_log: &'a mut IndexMap<String, LogEntry>,
        mutator_results: &'a mut HashMap<String, MutatorData>,
        passed_bodies: &'a mut HashMap<LocalDefId, BodyWithBorrowckFacts<'tcx>>,
        def_id: LocalDefId,
        body_with_borrowck_facts: &'a BodyWithBorrowckFacts<'tcx>,
        mut analysis: PcgOutput<'mir, 'tcx>,
    ) {
        for mutation in mutations.iter_mut() {
            let mutator_data = mutator_results
                .entry(mutation.name())
                .or_insert(MutatorData {
                    instances: 0,
                    passed: 0,
                    failed: 0,
                    panicked: 0,
                    error_codes: HashSet::new(),
                });
            // let body = &body_with_borrowck_facts.body;
            let promoted = &body_with_borrowck_facts.promoted;

            // Weaken `dyn Mutation + Send` to `dyn Mutation`
            let mutation: &Box<dyn Mutation> = unsafe { std::mem::transmute(&*mutation) };
            let borrow_checker_impl: &'tcx NllBorrowCheckerImpl<'_, 'tcx> = unsafe {
                std::mem::transmute(&NllBorrowCheckerImpl::new(tcx, body_with_borrowck_facts))
            };
            let body_ref = &body_with_borrowck_facts.body;

            let ctx: CompilerCtxt<'_, '_> = CompilerCtxt::new(body_ref, tcx, borrow_checker_impl);
            let mut mutator = Mutator::new(mutation, ctx, &mut analysis, ctx.body());

            while let Some(Mutant { body, range, info }) = mutator.next() {
                info!(
                    "{}Mutation {} generated mutant at {:?}",
                    cargo_crate_name().map_or("".to_string(), |name| format!("{name}: ")),
                    mutation.name(),
                    range,
                );
                mutator_data.instances += 1;
                let do_borrowck = env_feature_enabled("DO_BORROWCK").unwrap_or(true);

                // It is possible that the compiler raises an ICE when borrow checking a mutant.
                // In this case catch the unwind and do not count it as `Passed` or `Failed`
                let maybe_panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    let borrow_check_info = if do_borrowck {
                        track_body_error_codes(def_id);

                        let (borrowck_result, mutant_body_with_borrowck_facts) = {
                            // Pass this mutant to the borrow checker
                            let consumer_opts =
                                borrowck::consumers::ConsumerOptions::PoloniusInputFacts;
                            borrowck::do_mir_borrowck(tcx, &body, &promoted, Some(consumer_opts))
                        };
                        if let Some(_) = borrowck_result.tainted_by_errors {
                            mutator_data.failed += 1;
                            let error_codes = get_registered_errors();
                            for error_code in error_codes.iter() {
                                mutator_data.error_codes.insert(error_code.to_string());
                            }
                            BorrowCheckInfo::Failed {
                                error_codes: error_codes
                                    .iter()
                                    .map(|err_code| err_code.to_string())
                                    .collect(),
                            }
                        } else {
                            mutator_data.passed += 1;
                            if env_feature_enabled("PCG_VISUALIZATION").unwrap_or(false) {
                                // Because we have forked `rustc_borrowck`, there are two identical
                                // definitions of `BodyWithBorrowckFacts`. Here we convert from the
                                // version provided by `rustc_private` to the version defined in our
                                // fork `borrowck`.
                                let body: pcg::rustc_interface::borrowck::BodyWithBorrowckFacts<
                                    '_,
                                > = unsafe {
                                    std::mem::transmute(*mutant_body_with_borrowck_facts.unwrap())
                                };
                                passed_bodies.insert(def_id, body.into());
                            }
                            BorrowCheckInfo::Passed
                        }
                    } else {
                        BorrowCheckInfo::NoRun
                    };
                    let log_entry = LogEntry {
                        mutation_type: mutator.name(),
                        borrow_check_info,
                        definition: format!("{def_id:?}"),
                        range,
                        info,
                    };
                    if env_feature_enabled("MUTANTS_LOG").unwrap_or(false) {
                        mutants_log.insert(mutants_log.len().to_string(), log_entry);
                    }
                    compiler.sess.dcx().reset_err_count();
                }));

                if let Err(_) = maybe_panic {
                    mutator_data.panicked += 1
                }
            }
        }
    }

    let mut mutator_results: HashMap<String, MutatorData> = HashMap::new();
    let mut mutants_log: IndexMap<String, LogEntry> = IndexMap::new();
    let mut passed_bodies: HashMap<LocalDefId, BodyWithBorrowckFacts<'tcx>> = HashMap::new();

    let mut body_map: HashMap<LocalDefId, BodyWithBorrowckFacts<'tcx>> =
        unsafe { std::mem::transmute(BODIES.take()) };

    initialize_error_tracking();

    // Mutation test each body in the crate
    for def_id in tcx.hir().body_owners() {
        let item_name = tcx.def_path_str(def_id.to_def_id()).to_string();
        if let Ok(function) = std::env::var("PCG_SKIP_FUNCTION")
            && function == item_name
        {
            info!("Skipping function: {item_name} because PCG_SKIP_FUNCTION is set to {function}");
            continue;
        }

        let kind = tcx.def_kind(def_id);
        let item_name = tcx.def_path_str(def_id.to_def_id()).to_string();
        match kind {
            hir::def::DefKind::Fn | hir::def::DefKind::AssocFn => {
                if let Some(body) = body_map.remove(&def_id) {
                    info!(
                        "{}Running mutation testing on function: {}",
                        cargo_crate_name().map_or("".to_string(), |name| format!("{name}: ")),
                        item_name,
                    );
                    info!("Path: {:?}", body.body.span);

                    let safety = tcx.fn_sig(def_id).skip_binder().safety();
                    if safety == hir::Safety::Unsafe {
                        continue;
                    }
                    std::env::set_var("PCG_VALIDITY_CHECKS", "false");

                    let borrow_checker_impl = NllBorrowCheckerImpl::new(tcx, &body);
                    let ctx: CompilerCtxt<'_, '_> =
                        CompilerCtxt::new(&body.body, tcx, &borrow_checker_impl);
                    let pcg_ctx = PcgCtxt::new(&body.body, ctx.tcx(), ctx.bc());
                    let analysis = run_pcg(&pcg_ctx, None);

                    run_mutation_tests_for_body(
                        tcx,
                        compiler,
                        mutations,
                        &mut mutants_log,
                        &mut mutator_results,
                        &mut passed_bodies,
                        def_id,
                        &body,
                        analysis,
                    );
                }
            }
            _ => {}
        }
    }

    if let Ok(vis_dir) = std::env::var("PCG_VISUALIZATION_DATA_DIR") {
        let mut item_names = vec![];
        for (def_id, body) in passed_bodies.drain() {
            let borrow_checker_impl = NllBorrowCheckerImpl::new(tcx, &body);
            let ctx: CompilerCtxt<'_, '_> =
                CompilerCtxt::new(&body.body, tcx, &borrow_checker_impl);
            let pcg_ctx = PcgCtxt::new(&body.body, ctx.tcx(), ctx.bc());
            let item_name = ctx.tcx().def_path_str(def_id.to_def_id()).to_string();
            let item_dir = format!("{vis_dir}/{item_name}");
            item_names.push(item_name);
            run_pcg(&pcg_ctx, Some(item_dir.as_ref()));
        }

        let file_path = format!("{vis_dir}/functions.json");

        let json_data = serde_json::to_string(
            &item_names
                .iter()
                .map(|name| (name.clone(), name.clone()))
                .collect::<std::collections::HashMap<_, _>>(),
        )
        .expect("Failed to serialize item names to JSON");
        let mut file = File::create(file_path).expect("Failed to create JSON file");
        file.write_all(json_data.as_bytes())
            .expect("Failed to write item names to JSON file");
    }

    if let Some(crate_name) = cargo_crate_name() {
        let mut crate_name_suffix = 0;
        let mut mutants_log_path = results_dir
            .join(crate_name.clone() + "-mutants")
            .with_extension("json");
        let mut mutator_results_path = results_dir.join(crate_name.clone()).with_extension("json");

        while Path::exists(&*mutants_log_path) {
            let unique_crate_name = crate_name.clone() + "-" + &crate_name_suffix.to_string();
            crate_name_suffix += 1;
            mutants_log_path = results_dir
                .join(unique_crate_name.clone() + "-mutants")
                .with_extension("json");
            mutator_results_path = results_dir.join(unique_crate_name).with_extension("json");
        }

        if env_feature_enabled("MUTANTS_LOG").unwrap_or(false) {
            let mut mutants_log_file = File::create(&mutants_log_path).expect(&format!(
                "Failed to create output file {mutants_log_path:?}"
            ));
            let mutants_log_string = serde_json::to_string_pretty(&mutants_log).unwrap();
            mutants_log_file
                .write_all(mutants_log_string.as_bytes())
                .expect("Failed to write results to file");
        }

        let mut mutator_results_file = File::create(&mutator_results_path).expect(&format!(
            "Failed to create output file {mutator_results_path:?}"
        ));
        let mutator_results_string = serde_json::to_string_pretty(&mutator_results).unwrap();
        mutator_results_file
            .write_all(mutator_results_string.as_bytes())
            .expect("Failed to write results to file");
    }
}

fn in_cargo_crate() -> bool {
    std::env::var("CARGO_CRATE_NAME").is_ok()
}

fn init_tracing() {
    tracing_subscriber::fmt()
        .with_max_level(tracing::Level::INFO)
        .with_writer(std::io::stderr)
        .init();
}

fn main() {
    let mut rustc_args = vec!["rustc".to_string()];

    if !std::env::args().any(|arg| arg.starts_with("--edition=")) {
        rustc_args.push("--edition=2018".to_string());
    }
    if env_feature_enabled("PCG_POLONIUS").unwrap_or(false) {
        rustc_args.push("-Zpolonius".to_string());
    }
    if !in_cargo_crate() {
        rustc_args.push("-Zno-codegen".to_string());
    }

    rustc_args.extend(std::env::args().skip(1));

    let results_dir: PathBuf = match std::env::var("RESULTS_DIR") {
        Ok(str) => str.into(),
        _ => std::env::current_dir().unwrap(),
    };

    assert!(
        Path::exists(Path::new(&results_dir)),
        "Results directory {results_dir:?} does not exist"
    );

    let mut callbacks = MutatorCallbacks {
        mutations: vec![
            Box::new(BorrowExpiryOrder),
            Box::new(AbstractExpiryOrder),
            Box::new(MutablyLendShared),
            Box::new(ReadFromWriteOnly),
            Box::new(WriteToShared),
            Box::new(MoveFromBorrowed),
        ],
        results_dir,
    };
    init_tracing();
    driver::RunCompiler::new(&rustc_args, &mut callbacks).run();
}
