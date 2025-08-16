use super::utils::fresh_local;
use super::utils::has_named_local;

use super::mutator_impl::Mutant;
use super::mutator_impl::MutantIterator;
use super::mutator_impl::MutantLocation;
use super::mutator_impl::MutantRange;
use super::mutator_impl::MutantStream;
use super::mutator_impl::Mutation;

use crate::rustc_interface::middle::mir::Body;
use crate::rustc_interface::middle::mir::FakeReadCause;
use crate::rustc_interface::middle::mir::Place as MirPlace;
use crate::rustc_interface::middle::mir::PlaceRef;
use crate::rustc_interface::middle::mir::Statement;
use crate::rustc_interface::middle::mir::StatementKind;
use crate::rustc_interface::middle::ty::Region;
use crate::rustc_interface::middle::ty::RegionKind;
use crate::rustc_interface::middle::ty::Ty;

use pcg::pcg::CapabilityKind;
use pcg::free_pcs::PcgLocation;
use pcg::pcg::EvalStmtPhase;
use pcg::utils::CompilerCtxt;
use pcg::utils::Place;

// `ReadFromWriteOnly` creates mutants which read from places with W capability
pub struct ReadFromWriteOnly;

struct Iter<'a, 'tcx: 'a> {
    write_only: Vec<Place<'tcx>>,
    ctx: CompilerCtxt<'a, 'tcx>,
    body: &'a Body<'tcx>,
    curr: PcgLocation<'tcx>,
}

impl<'a, 'mir: 'a, 'tcx: 'mir> Iter<'a, 'tcx> {
    fn maybe_next(&mut self) -> Option<Mutant<'tcx>> {
        let place = self.write_only.pop()?;
        let lent_place = PlaceRef::from(place).to_place(self.ctx.tcx());
        let mut mutant_body = self.body.clone();

        let erased_region = Region::new_from_kind(self.ctx.tcx(), RegionKind::ReErased);
        let borrow_ty = Ty::new_mut_ref(
            self.ctx.tcx(),
            erased_region,
            lent_place.ty(&self.body.local_decls, self.ctx.tcx()).ty,
        );

        let fresh_local = fresh_local(&mut mutant_body, borrow_ty);

        let statement_index = self.curr.location.statement_index;
        let bb_index = self.curr.location.block;
        let bb = mutant_body.basic_blocks_mut().get_mut(bb_index)?;
        let statement_source_info = bb.statements.get(statement_index)?.source_info;

        // Statment that reads `place` into a `fresh_local`
        let new_read = Statement {
            source_info: statement_source_info,
            kind: StatementKind::FakeRead(Box::new((
                FakeReadCause::ForLet(None),
                MirPlace::from(fresh_local),
            ))),
        };
        let info = format!(
            "{:?} was write-only, so inserted {:?}",
            lent_place, &new_read
        );
        // Insert `new_read` between `curr` and `next`
        bb.statements.insert(statement_index + 1, new_read);

        let borrow_loc = MutantLocation {
            basic_block: self.curr.location.block.index(),
            statement_index: statement_index + 1,
        };

        Some(Mutant {
            body: mutant_body,
            range: MutantRange {
                start: borrow_loc.clone(),
                end: borrow_loc,
            },
            info,
        })
    }
}

impl<'a, 'mir: 'a, 'tcx: 'mir> MutantIterator<'a, 'mir, 'tcx> for Iter<'a, 'tcx> {
    fn next(&mut self) -> Option<Mutant<'tcx>> {
        while !self.write_only.is_empty() {
            if let Some(mutant) = self.maybe_next() {
                return Some(mutant);
            }
        }
        return None;
    }
}

impl ReadFromWriteOnly {}

impl Mutation for ReadFromWriteOnly {
    fn make_stream<'a, 'mir: 'a, 'tcx: 'mir>(
        &self,
        ctx: CompilerCtxt<'a, 'tcx>,
        body: &'a Body<'tcx>,
        curr: PcgLocation<'tcx>,
        next: PcgLocation<'tcx>,
    ) -> MutantStream<'a, 'mir, 'tcx> {
        // We consider only places that are W at the `PostMain` of `curr` and `PostOperands` of `next`
        // because a borrow could expire which restores E capability at the `PostOperands` phase.
        let write_only_in_curr: Vec<_> = curr.states[EvalStmtPhase::PostMain]
            .places_with_capapability(CapabilityKind::Write)
            .into_iter()
            .collect();

        let write_only_in_next: Vec<_> = next.states[EvalStmtPhase::PostOperands]
            .places_with_capapability(CapabilityKind::Write)
            .into_iter()
            .collect();

        let write_only = write_only_in_curr
            .iter()
            .filter(|place| write_only_in_next.contains(place))
            .filter(|place| has_named_local(**place, body))
            .map(|place| *place)
            .collect();

        MutantStream::new(Box::new(Iter {
            write_only,
            ctx,
            body,
            curr,
        }))
    }
    fn name(&self) -> String {
        "read-from-write-only".into()
    }
}
