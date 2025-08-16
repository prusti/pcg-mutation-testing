use serde::Serialize;

use crate::rustc_interface::middle::mir::BasicBlock;
use crate::rustc_interface::middle::mir::Body;

use pcg::free_pcs::PcgLocation;
use pcg::utils::CompilerCtxt;
use pcg::PcgOutput;

use std::collections::VecDeque;

#[derive(Serialize, Clone, Debug)]
pub struct MutantLocation {
    pub basic_block: usize,
    pub statement_index: usize,
}

#[derive(Serialize, Clone, Debug)]
pub struct MutantRange {
    pub start: MutantLocation,
    pub end: MutantLocation,
}

// A `Mutant` is a MIR `Body` along with a description of the mutation performed
// and a source range describing where the mutation appears
pub struct Mutant<'tcx> {
    pub body: Body<'tcx>,
    pub range: MutantRange,
    pub info: String,
}

pub struct MutantStream<'a, 'mir: 'a, 'tcx: 'mir> {
    // ctx: CompilerCtxt<'tcx, 'tcx>,
    // body: &'tcx Body<'tcx>,
    // curr: PcgLocation<'tcx>,
    // next: PcgLocation<'tcx>,
    iter: Box<dyn MutantIterator<'a, 'mir, 'tcx> + 'a>,
}

impl<'a, 'mir: 'a, 'tcx: 'mir> MutantStream<'a, 'mir, 'tcx> {
    pub fn new(iter: Box<dyn MutantIterator<'a, 'mir, 'tcx> + 'a>) -> Self {
        Self { iter }
    }
    pub fn next(&mut self) -> Option<Mutant<'tcx>> {
        self.iter.next()
    }
}

pub trait MutantIterator<'a, 'mir, 'tcx> {
    fn next(&mut self) -> Option<Mutant<'tcx>>;
}

// A `Mutation` uses a MIR `Body` and the analyses for two consecutive
// statements to produce a set of mutant MIR `Body`s.
pub trait Mutation {
    fn make_stream<'a, 'mir: 'a, 'tcx: 'mir>(
        &self,
        ctx: CompilerCtxt<'a, 'tcx>,
        body: &'a Body<'tcx>,
        curr: PcgLocation<'tcx>,
        next: PcgLocation<'tcx>,
    ) -> MutantStream<'a, 'mir, 'tcx>;
    fn name(&self) -> String;
}

// A `Mutator` generates mutants for a MIR `Body` using a `Mutation`.
// It can be repeatedly queried for new mutants until it has finished traversing
// the entire `Body`.
pub struct Mutator<'a, 'mir: 'a, 'tcx: 'mir> {
    mutation: &'a Box<dyn Mutation>,
    analysis: &'a mut PcgOutput<'mir, 'tcx>,
    ctx: CompilerCtxt<'a, 'tcx>,
    body: &'a Body<'tcx>,
    mutants: Option<MutantStream<'a, 'mir, 'tcx>>,
    basic_blocks: VecDeque<BasicBlock>,
    bb_stmts: Option<Vec<PcgLocation<'tcx>>>,
    stmt_idx: usize,
    // borrowck: NllBorrowCheckerImpl<'tcx, 'tcx>,
}

impl<'a, 'mir: 'a, 'tcx: 'mir> Mutator<'a, 'mir, 'tcx> {
    pub fn new(
        mutation: &'a Box<dyn Mutation>,
        ctx: CompilerCtxt<'a, 'tcx>,
        analysis: &'a mut PcgOutput<'mir, 'tcx>,
        body: &'a Body<'tcx>,
    ) -> Self {
        Self {
            mutation,
            analysis,
            ctx,
            body,
            mutants: None,
            basic_blocks: body.basic_blocks.indices().collect(),
            bb_stmts: None,
            stmt_idx: 0,
        }
    }

    pub fn name(&self) -> String {
        self.mutation.name()
    }

    fn curr_bb(&self) -> Option<BasicBlock> {
        Some(*self.basic_blocks.front()?)
    }

    // Return the next `Mutant` that can be generated from this body
    pub fn next(&mut self) -> Option<Mutant<'tcx>> {
        // Seek until we generate some `Mutant`s or finish traversing
        // the body

        while !self.basic_blocks.is_empty() {
            let old_num_bb = self.basic_blocks.len();
            let old_stmt_idx = self.stmt_idx;

            if let Some(mutants) = &mut self.mutants
                && let Some(mutant) = mutants.next()
            {
                return Some(mutant);
            } else if let Some(bb_stmts) = &self.bb_stmts
                && let Some(curr) = bb_stmts.get(self.stmt_idx)
                && let Some(next) = bb_stmts.get(self.stmt_idx + 1)
            {
                self.mutants = Some(self.mutation.make_stream(
                    self.ctx,
                    &self.body,
                    curr.clone(),
                    next.clone(),
                ));
                self.stmt_idx += 1;
            } else {
                self.stmt_idx = 0;
                self.bb_stmts = if let Some(curr_bb) = self.curr_bb()
                    && let Ok(Some(pcg_bb)) = self.analysis.get_all_for_bb(curr_bb)
                {
                    Some(pcg_bb.statements)
                } else {
                    None
                };
                self.basic_blocks.pop_front();
            }

            // Sanity check for termination
            assert!(self.basic_blocks.len() < old_num_bb || self.stmt_idx > old_stmt_idx);
        }

        None
    }
}
