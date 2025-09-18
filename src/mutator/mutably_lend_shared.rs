use super::utils::borrowed_places;
use super::utils::fresh_local;
use super::utils::has_named_local;
use super::utils::is_shared;

use std::collections::HashSet;

use super::mutator_impl::Mutant;
use super::mutator_impl::MutantIterator;
use super::mutator_impl::MutantLocation;
use super::mutator_impl::MutantRange;
use super::mutator_impl::MutantStream;
use super::mutator_impl::Mutation;

use crate::rustc_interface::middle::mir::Body;
use crate::rustc_interface::middle::mir::BorrowKind;
use crate::rustc_interface::middle::mir::MutBorrowKind;
use crate::rustc_interface::middle::mir::Place as MirPlace;
use crate::rustc_interface::middle::mir::PlaceRef;
use crate::rustc_interface::middle::mir::Rvalue;
use crate::rustc_interface::middle::mir::Statement;
use crate::rustc_interface::middle::mir::StatementKind;
use crate::rustc_interface::middle::ty::Region;
use crate::rustc_interface::middle::ty::Ty;

use pcg::results::PcgLocation;
use pcg::pcg::EvalStmtPhase;
use pcg::utils::CompilerCtxt;
use pcg::utils::Place;

// `MutablyLendShared` creates mutants which mutably borrow a place behind a shared borrow
pub struct MutablyLendShared;

struct Iter<'a, 'tcx: 'a> {
    immutably_lent: Vec<(Place<'tcx>, Region<'tcx>)>,
    ctx: CompilerCtxt<'a, 'tcx>,
    body: &'a Body<'tcx>,
    curr: PcgLocation<'a, 'tcx>,
}

impl<'a, 'mir: 'a, 'tcx: 'mir> MutantIterator<'a, 'mir, 'tcx> for Iter<'a, 'tcx> {
    fn next(&mut self) -> Option<Mutant<'tcx>> {
        while !self.immutably_lent.is_empty() {
            if let Some(mutant) = self.maybe_next() {
                return Some(mutant);
            }
        }
        return None;
    }
}

impl<'a, 'mir: 'a, 'tcx: 'mir> Iter<'a, 'tcx> {
    fn maybe_next(&mut self) -> Option<Mutant<'tcx>> {
        let (place, region) = self.immutably_lent.pop()?;
        let lent_place = PlaceRef::from(place).to_place(self.ctx.tcx());
        let mut mutant_body = self.body.clone();

        let borrow_ty = Ty::new_mut_ref(
            self.ctx.tcx(),
            region,
            lent_place.ty(&self.body.local_decls, self.ctx.tcx()).ty,
        );

        let fresh_local = fresh_local(&mut mutant_body, borrow_ty);

        let statement_index = self.curr.location.statement_index;
        let bb_index = self.curr.location.block;
        let bb = mutant_body.basic_blocks_mut().get_mut(bb_index)?;
        let statement_source_info = bb.statements.get(statement_index)?.source_info;

        let default_mut_borrow = BorrowKind::Mut {
            kind: MutBorrowKind::Default,
        };

        // Statement which mutably borrows `lent_place` into a `fresh_local`
        let new_borrow = Statement {
            source_info: statement_source_info,
            kind: StatementKind::Assign(Box::new((
                MirPlace::from(fresh_local),
                Rvalue::Ref(region, default_mut_borrow, lent_place),
            ))),
        };
        let info = format!("{:?} was shared, so inserted {:?}", lent_place, &new_borrow);

        // Insert `new_borrow` between `curr` and `next`
        bb.statements.insert(statement_index + 1, new_borrow);

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

impl Mutation for MutablyLendShared {
    fn make_stream<'a, 'mir: 'a, 'tcx: 'mir>(
        &self,
        ctx: CompilerCtxt<'a, 'tcx>,
        body: &'a Body<'tcx>,
        curr: PcgLocation<'a, 'tcx>,
        next: PcgLocation<'a, 'tcx>,
    ) -> MutantStream<'a, 'mir, 'tcx> {
        let immutably_lent_in_curr = {
            let borrows_graph = curr.states[EvalStmtPhase::PostMain].borrow_pcg().graph();
            borrowed_places(borrows_graph, is_shared)
        };

        let immutably_lent_in_next = {
            let borrows_graph = next.states[EvalStmtPhase::PostOperands]
                .borrow_pcg()
                .graph();
            borrowed_places(borrows_graph, is_shared)
                .map(|(place, _)| place)
                .collect::<HashSet<_>>()
        };

        let immutably_lent = immutably_lent_in_curr
            .filter(|(place, _)| immutably_lent_in_next.contains(place))
            .filter(|(place, _)| has_named_local(*place, body))
            .collect();

        MutantStream::new(Box::new(Iter {
            immutably_lent,
            ctx,
            body,
            curr,
        }))
    }
    fn name(&self) -> String {
        "mutably-lend-shared".into()
    }
}
