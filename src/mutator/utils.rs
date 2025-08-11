use pcg::borrow_pcg::borrow_pcg_edge::BorrowPcgEdgeLike;
use pcg::borrow_pcg::edge::borrow::BorrowEdge;
use pcg::borrow_pcg::edge::kind::BorrowPcgEdgeKind;
use pcg::borrow_pcg::graph::BorrowsGraph;

use pcg::utils::place::Place;


use crate::rustc_interface::ast::ast::BindingMode;

use crate::rustc_interface::middle::ty::Region;
use crate::rustc_interface::middle::ty::Ty;

use crate::rustc_interface::middle::mir::BasicBlock;
use crate::rustc_interface::middle::mir::BasicBlockData;
use crate::rustc_interface::middle::mir::BindingForm;
use crate::rustc_interface::middle::mir::Body;
use crate::rustc_interface::middle::mir::BorrowKind;
use crate::rustc_interface::middle::mir::ClearCrossCrate;
use crate::rustc_interface::middle::mir::Local;
use crate::rustc_interface::middle::mir::LocalDecl;
use crate::rustc_interface::middle::mir::LocalInfo;
use crate::rustc_interface::middle::mir::MutBorrowKind;
use crate::rustc_interface::middle::mir::SourceInfo;
use crate::rustc_interface::middle::mir::VarBindingForm;

// Create a fresh local with a bogus source span
pub(crate) fn fresh_local<'tcx>(body: &mut Body<'tcx>, ty: Ty<'tcx>) -> Local {
    let mut fresh_local_decl = LocalDecl::with_source_info(ty, bogus_source_info(body));
    let local_info = {
        let var_binding_form = VarBindingForm {
            binding_mode: BindingMode::NONE,
            opt_ty_info: None,
            opt_match_place: None,
            pat_span: bogus_source_info(body).span,
        };
        let binding_form = BindingForm::Var(var_binding_form);
        ClearCrossCrate::Set(Box::new(LocalInfo::User(binding_form)))
    };
    fresh_local_decl.local_info = local_info;
    body.local_decls.push(fresh_local_decl)
}

pub(crate) fn fresh_basic_block<'tcx>(body: &mut Body<'tcx>) -> BasicBlock {
    body.basic_blocks_mut().push(BasicBlockData::new(None))
}

pub(crate) fn bogus_source_info<'tcx>(body: &Body<'tcx>) -> SourceInfo {
    body.local_decls.iter().next().unwrap().source_info
}

pub(crate) fn is_mut(kind: BorrowKind) -> bool {
    match kind {
        BorrowKind::Mut {
            kind: MutBorrowKind::Default,
        } => true,
        _ => false,
    }
}

pub(crate) fn is_shared(kind: BorrowKind) -> bool {
    match kind {
        BorrowKind::Shared => true,
        _ => false,
    }
}

// Returns every place blocked by a borrow edge satisfying `p`
pub(crate) fn borrowed_places<'graph, 'tcx>(
    graph: &'graph BorrowsGraph<'tcx>,
    p: fn(BorrowKind) -> bool,
) -> impl Iterator<Item = (Place<'tcx>, Region<'tcx>)> + 'graph {
    graph
        .edges()
        .flat_map(move |edge_ref| match edge_ref.kind() {
            BorrowPcgEdgeKind::Borrow(borrow_edge) => match borrow_edge {
                BorrowEdge::Local(local_borrow) => {
                    if borrow_edge.kind().iter().any(|kind| p(*kind)) {
                        local_borrow
                            .blocked_place
                            .as_current_place()
                            .map(|place| (place, local_borrow.region))
                    } else {
                        None
                    }
                }
                _ => None,
            },
            _ => None,
        })
}

pub(crate) fn has_named_local<'tcx>(place: Place<'tcx>, body: &Body<'tcx>) -> bool {
    match body.local_decls.get(place.local) {
        Some(local_decl) => local_decl.is_user_variable(),
        None => false,
    }
}
