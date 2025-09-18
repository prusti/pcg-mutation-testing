use super::utils::bogus_source_info;
use super::utils::borrowed_places;
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
use crate::rustc_interface::middle::mir::PlaceRef;
use crate::rustc_interface::middle::mir::Rvalue;
use crate::rustc_interface::middle::mir::Statement;
use crate::rustc_interface::middle::mir::StatementKind;

use pcg::results::PcgLocation;
use pcg::pcg::EvalStmtPhase;
use pcg::utils::CompilerCtxt;
use pcg::utils::Place;

// `WriteToShared` creates mutants which write to shared borrows
pub struct WriteToShared;

struct Iter<'a, 'tcx: 'a> {
    shared: Vec<Place<'tcx>>,
    ctx: CompilerCtxt<'a, 'tcx>,
    body: &'a Body<'tcx>,
    curr: PcgLocation<'a, 'tcx>,
}

impl<'a, 'mir: 'a, 'tcx: 'mir> Iter<'a, 'tcx> {
    fn maybe_next(&mut self) -> Option<Mutant<'tcx>> {
        let place = self.shared.pop()?;
        let shared_place = PlaceRef::from(*place).to_place(self.ctx.tcx());
        let mut mutant_body = self.body.clone();

        let statement_index = self.curr.location.statement_index;

        // Statment which writes to `shared_place`
        let new_assign = Statement {
            source_info: bogus_source_info(&mutant_body),
            kind: StatementKind::Assign(Box::new((shared_place, Rvalue::Len(shared_place)))),
        };
        let info = format!(
            "{:?} was shared, so inserted {:?}",
            shared_place, &new_assign
        );

        let bb_index = self.curr.location.block;
        let bb = mutant_body.basic_blocks_mut().get_mut(bb_index)?;
        // Insert `new_assign` between `curr` and `next`
        bb.statements.insert(statement_index + 1, new_assign);

        let borrow_loc = MutantLocation {
            basic_block: self.curr.location.block.index(),
            statement_index: statement_index + 1,
        };

        let mention_loc = MutantLocation {
            basic_block: self.curr.location.block.index(),
            statement_index: statement_index + 1,
        };

        Some(Mutant {
            body: mutant_body,
            range: MutantRange {
                start: borrow_loc,
                end: mention_loc,
            },
            info,
        })
    }
}

impl<'a, 'mir: 'a, 'tcx: 'mir> MutantIterator<'a, 'mir, 'tcx> for Iter<'a, 'tcx> {
    fn next(&mut self) -> Option<Mutant<'tcx>> {
        while !self.shared.is_empty() {
            if let Some(mutant) = self.maybe_next() {
                return Some(mutant);
            }
        }
        return None;
    }
}

impl Mutation for WriteToShared {
    fn make_stream<'a, 'mir: 'a, 'tcx: 'mir>(
        &self,
        ctx: CompilerCtxt<'a, 'tcx>,
        body: &'a Body<'tcx>,
        curr: PcgLocation<'a, 'tcx>,
        next: PcgLocation<'a, 'tcx>,
    ) -> MutantStream<'a, 'mir, 'tcx> {
        let shared_in_curr = {
            let borrows_graph = curr.states[EvalStmtPhase::PostMain].borrow_pcg().graph();
            borrowed_places(borrows_graph, is_shared)
                .map(|(place, _)| place)
                .collect::<HashSet<_>>()
        };

        let shared_in_next = {
            let borrows_graph = next.states[EvalStmtPhase::PostOperands]
                .borrow_pcg()
                .graph();
            borrowed_places(borrows_graph, is_shared)
        };

        let shared = shared_in_next
            .filter(|(place, _)| shared_in_curr.contains(place))
            .filter(|(place, _)| has_named_local(*place, body))
            .map(|(place, _)| place)
            .collect();

        MutantStream::new(Box::new(Iter {
            shared,
            ctx,
            body,
            curr,
        }))
    }
    fn name(&self) -> String {
        "write-to-shared".into()
    }
}
