use super::utils::borrowed_places;
use super::utils::fresh_local;
use super::utils::has_named_local;
use super::utils::is_mut;

use std::collections::HashSet;

use super::mutator_impl::Mutant;
use super::mutator_impl::MutantIterator;
use super::mutator_impl::MutantLocation;
use super::mutator_impl::MutantRange;
use super::mutator_impl::MutantStream;
use super::mutator_impl::Mutation;

use crate::rustc_interface::middle::mir::Body;
use crate::rustc_interface::middle::mir::Operand;
use crate::rustc_interface::middle::mir::Place as MirPlace;
use crate::rustc_interface::middle::mir::PlaceRef;
use crate::rustc_interface::middle::mir::Rvalue;
use crate::rustc_interface::middle::mir::Statement;
use crate::rustc_interface::middle::mir::StatementKind;

use pcg::results::PcgLocation;
use pcg::pcg::EvalStmtPhase;
use pcg::utils::CompilerCtxt;
use pcg::utils::Place;

// `MoveFromBorrowed` creates mutants which move out of a place behind a mutable borrow
pub struct MoveFromBorrowed;

struct Iter<'a, 'tcx: 'a> {
    borrowed: Vec<Place<'tcx>>,
    ctx: CompilerCtxt<'a, 'tcx>,
    body: &'a Body<'tcx>,
    curr: PcgLocation<'tcx>,
}

impl<'a, 'mir: 'a, 'tcx: 'mir> MutantIterator<'a, 'mir, 'tcx> for Iter<'a, 'tcx> {
    fn next(&mut self) -> Option<Mutant<'tcx>> {
        while !self.borrowed.is_empty() {
            if let Some(mutant) = self.maybe_next() {
                return Some(mutant);
            }
        }
        return None;
    }
}

impl<'a, 'mir: 'a, 'tcx: 'mir> Iter<'a, 'tcx> {
    fn maybe_next(&mut self) -> Option<Mutant<'tcx>> {
        let place = self.borrowed.pop()?;
        let mut mutant_body = self.body.clone();
        let lent_place = PlaceRef::from(place).to_place(self.ctx.tcx());

        let lent_place_ty = lent_place.ty(&self.body.local_decls, self.ctx.tcx()).ty;

        let fresh_local = fresh_local(&mut mutant_body, lent_place_ty);

        let statement_index = self.curr.location.statement_index;
        let bb_index = self.curr.location.block;
        let bb = mutant_body.basic_blocks_mut().get_mut(bb_index)?;
        let statement_source_info = bb.statements.get(statement_index)?.source_info;

        // Statement that moves `lent_place` into a `fresh_local`
        let new_move = Statement {
            source_info: statement_source_info,
            kind: StatementKind::Assign(Box::new((
                MirPlace::from(fresh_local),
                Rvalue::Use(Operand::Move(lent_place)),
            ))),
        };
        let info = format!("{:?} was lent, so inserted {:?}", lent_place, &new_move);
        // Insert `new_move` between `curr` and `next`
        bb.statements.insert(statement_index + 1, new_move);

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

impl Mutation for MoveFromBorrowed {
    fn make_stream<'a, 'mir: 'a, 'tcx: 'mir>(
        &self,
        ctx: CompilerCtxt<'a, 'tcx>,
        body: &'a Body<'tcx>,
        curr: PcgLocation<'tcx>,
        next: PcgLocation<'tcx>,
    ) -> MutantStream<'a, 'mir, 'tcx> {
        let lent_in_curr = {
            let borrows_graph = curr.states[EvalStmtPhase::PostMain].borrow_pcg().graph();
            borrowed_places(borrows_graph, is_mut)
                .map(|(place, _)| place)
                .collect::<HashSet<_>>()
        };

        let lent_in_next = {
            let borrows_graph = next.states[EvalStmtPhase::PostOperands]
                .borrow_pcg()
                .graph();
            borrowed_places(borrows_graph, is_mut)
                .map(|(place, _)| place)
                .collect::<HashSet<_>>()
        };
        let borrowed = lent_in_curr
            .iter()
            .filter(|place| lent_in_next.contains(place))
            .filter(|place| has_named_local(**place, body))
            .map(|place| *place)
            .collect();

        MutantStream::new(Box::new(Iter {
            borrowed,
            ctx,
            body,
            curr,
        }))
    }
    fn name(&self) -> String {
        "move-from-borrowed".into()
    }
}
