use super::utils::bogus_source_info;
use super::utils::borrowed_places;
use super::utils::fresh_basic_block;
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
use crate::rustc_interface::middle::mir::BorrowKind;
use crate::rustc_interface::middle::mir::Mutability;
use crate::rustc_interface::middle::mir::Place as MirPlace;
use crate::rustc_interface::middle::mir::PlaceRef;
use crate::rustc_interface::middle::mir::Rvalue;
use crate::rustc_interface::middle::mir::Statement;
use crate::rustc_interface::middle::mir::StatementKind;
use crate::rustc_interface::middle::mir::Terminator;
use crate::rustc_interface::middle::mir::TerminatorKind;
use crate::rustc_interface::middle::ty::Region;
use crate::rustc_interface::middle::ty::RegionVid;
use crate::rustc_interface::middle::ty::Ty;
use crate::rustc_interface::middle::ty::TyCtxt;

use pcg::results::PcgLocation;

use pcg::pcg::EvalStmtPhase;
use pcg::pcg::PcgNode;

use pcg::utils::place::Place;
use pcg::utils::CompilerCtxt;

use pcg::borrow_pcg::borrow_pcg_edge::BlockedNode;
use pcg::borrow_pcg::borrow_pcg_edge::BorrowPcgEdgeLike;
use pcg::borrow_pcg::borrow_pcg_edge::BorrowPcgEdgeRef;
use pcg::borrow_pcg::edge::kind::BorrowPcgEdgeKind;
use pcg::borrow_pcg::edge_data::EdgeData;
use pcg::borrow_pcg::graph::BorrowsGraph;

// Returns the places for each node that blocks `place` on a path that
// includes at least one edge satisfying `is_blocking_edge` and consisting
// only of edges that satisfy `is_valid_edge`
fn places_blocking<'mir, 'tcx>(
    place: Place<'tcx>,
    borrows_graph: &BorrowsGraph<'tcx>,
    ctx: CompilerCtxt<'mir, 'tcx>,
    is_blocking_edge: impl Fn(&HashSet<BorrowPcgEdgeKind<'tcx>>) -> bool,
    is_valid_edge: impl Fn(&BorrowPcgEdgeKind<'tcx>) -> bool,
) -> HashSet<Place<'tcx>> {
    let node = place.into();
    let mut to_visit: Vec<(BorrowPcgEdgeRef<'_, '_>, HashSet<BorrowPcgEdgeKind<'_>>)> =
        borrows_graph
            .frozen_graph()
            .get_edges_blocking(node, ctx)
            .into_iter()
            .filter(|edge| is_valid_edge(edge.kind()))
            .map(|edge| (edge, HashSet::new()))
            .collect();
    let mut places: HashSet<Place<'tcx>> = HashSet::new();

    while let Some((curr, mut kind_set)) = to_visit.pop() {
        kind_set.insert(curr.kind().clone());
        if is_blocking_edge(&kind_set) {
            let mut nodes: Vec<_> = curr
                .blocked_by_nodes(ctx)
                .flat_map(|node| node.as_current_place())
                .collect();
            places.extend(nodes.drain(..));
        }
        let incident_nodes = curr.blocked_by_nodes(ctx);
        let adjacent_edges = incident_nodes
            .map(BlockedNode::from)
            .flat_map(|node| borrows_graph.frozen_graph().get_edges_blocking(node, ctx))
            .filter(|edge| is_valid_edge(edge.kind()))
            .map(|edge| (edge, kind_set.clone()));
        to_visit.extend(adjacent_edges);
    }
    places
}

// Given a list of MIR places, produce a list of MIR statements which reborrow those places
// into fresh local variables in the same order
fn places_to_statements<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mut Body<'tcx>,
    mut places: Vec<Place<'tcx>>,
) -> Vec<Statement<'tcx>> {
    places
        .drain(..)
        .map(|place| {
            let mir_place = PlaceRef::from(*place).to_place(tcx);
            let region = Region::new_var(tcx, RegionVid::MAX);
            let target_ty = Ty::new_mut_ref(tcx, region, mir_place.ty(&body.local_decls, tcx).ty);
            let target = fresh_local(body, target_ty);
            Statement {
                source_info: bogus_source_info(body),
                kind: StatementKind::Assign(Box::new((
                    MirPlace::from(target),
                    Rvalue::Ref(region, BorrowKind::Shared, mir_place),
                ))),
            }
        })
        .collect()
}

struct Iter<'a, 'tcx: 'a> {
    mutant_sequences: Vec<(Place<'tcx>, Place<'tcx>)>,
    ctx: CompilerCtxt<'a, 'tcx>,
    body: &'a Body<'tcx>,
    curr: PcgLocation<'a, 'tcx>,
    next: PcgLocation<'a, 'tcx>,
}

impl<'a, 'mir: 'a, 'tcx: 'mir> MutantIterator<'a, 'mir, 'tcx> for Iter<'a, 'tcx> {
    fn next(&mut self) -> Option<Mutant<'tcx>> {
        while !self.mutant_sequences.is_empty() {
            if let Some(mutant) = self.maybe_next() {
                return Some(mutant);
            }
        }
        return None;
    }
}

impl<'a, 'mir: 'a, 'tcx: 'mir> Iter<'a, 'tcx> {
    fn maybe_next(&mut self) -> Option<Mutant<'tcx>> {
        let (place, blocking_place) = self.mutant_sequences.pop()?;
        let mut mutant_body = self.body.clone();
        let mutant_sequence = places_to_statements(
            self.ctx.tcx(),
            &mut mutant_body,
            vec![place, blocking_place], // (p2, p1)
        );
        let curr_bb_index = self.curr.location.block;
        // Split the original basic block between `curr` and `next`
        let bb = mutant_body
            .basic_blocks_mut()
            .get_mut(curr_bb_index)
            .unwrap();
        let mut tail_statements = bb
            .statements
            .drain(self.next.location.statement_index..)
            .collect();

        let bb_terminator = bb.terminator.take();
        let tail_bb_index = fresh_basic_block(&mut mutant_body);
        let tail_bb = mutant_body
            .basic_blocks_mut()
            .get_mut(tail_bb_index)
            .unwrap();
        tail_bb.statements.append(&mut tail_statements);
        tail_bb.terminator = bb_terminator;

        let bogus_source_info = bogus_source_info(&mutant_body);

        // `mutant_bb` is the branch in which we expire p2 before p1
        let mutant_bb_index = fresh_basic_block(&mut mutant_body);
        let mutant_bb = mutant_body
            .basic_blocks_mut()
            .get_mut(mutant_bb_index)
            .unwrap();
        mutant_bb.statements = mutant_sequence.clone();
        mutant_bb.terminator = Some(Terminator {
            source_info: bogus_source_info,
            kind: TerminatorKind::Unreachable,
        });

        let start_loc = MutantLocation {
            basic_block: mutant_bb_index.into(),
            statement_index: 0,
        };

        let end_loc = MutantLocation {
            basic_block: mutant_bb_index.into(),
            statement_index: self.curr.location.statement_index,
        };

        let bb = mutant_body
            .basic_blocks_mut()
            .get_mut(curr_bb_index)
            .unwrap();

        // Terminator of the original basic block becomes a false branch.
        // Control will always flow to `tail_bb` but the compiler type-checks
        // the body as if it could go to `mutant_bb`.
        bb.terminator = Some(Terminator {
            source_info: bogus_source_info,
            kind: TerminatorKind::FalseEdge {
                real_target: tail_bb_index,
                imaginary_target: mutant_bb_index,
            },
        });

        Some(Mutant {
            body: mutant_body,
            range: MutantRange {
                start: start_loc,
                end: end_loc,
            },
            info: format!("created mutant expiry sequence {:?}", mutant_sequence).to_string(),
        })
    }
}

// BorrowExpiryOrder identifies a place p1 which blocks another place p2 via a mutable
// borrow and attempts to use p2 before p1
pub struct BorrowExpiryOrder;

impl Mutation for BorrowExpiryOrder {
    fn make_stream<'a, 'mir: 'a, 'tcx: 'mir>(
        &self,
        ctx: CompilerCtxt<'a, 'tcx>,
        body: &'a Body<'tcx>,
        curr: PcgLocation<'a, 'tcx>,
        next: PcgLocation<'a, 'tcx>,
    ) -> MutantStream<'a, 'mir, 'tcx> {
        let mut mutant_sequences = vec![];

        let borrows_graph = next.states[EvalStmtPhase::PostOperands]
            .borrow_pcg()
            .graph();

        let mutably_borrowed_places: HashSet<Place<'tcx>> = borrowed_places(&borrows_graph, is_mut)
            .map(|(place, _)| (*place).into())
            .collect();

        // Identify blocking places for each mutably borrowed place
        for place_ref in mutably_borrowed_places.iter() {
            let place = *place_ref;
            if has_named_local(place, body) {
                let mut blocking_places = places_blocking(
                    place,
                    &borrows_graph,
                    ctx,
                    |kind_set| {
                        kind_set.iter().any(|kind| match kind {
                            BorrowPcgEdgeKind::Borrow(borrow_edge) => {
                                borrow_edge.kind().iter().any(|kind| is_mut(*kind))
                            }
                            _ => false,
                        })
                    },
                    |kind| match kind {
                        BorrowPcgEdgeKind::Borrow(borrow_edge) => {
                            borrow_edge.kind().iter().any(|kind| is_mut(*kind))
                        }
                        BorrowPcgEdgeKind::BorrowPcgExpansion(expansion) => {
                            let ctx = ctx;
                            let base = expansion.base();
                            match base {
                                PcgNode::Place(p) => {
                                    p.ty(ctx).ty.ref_mutability() == Some(Mutability::Mut)
                                }
                                PcgNode::LifetimeProjection(rp) => {
                                    rp.place().ty(ctx).ty.ref_mutability()
                                        == Some(Mutability::Mut)
                                }
                            }
                        }
                        _ => true,
                    },
                );
                for blocking_place in blocking_places.drain() {
                    if has_named_local(blocking_place, body) {
                        mutant_sequences.push((place, blocking_place));
                    }
                }
            }
        }

        MutantStream::new(Box::new(Iter {
            mutant_sequences,
            ctx,
            body,
            curr,
            next,
        }))
    }
    fn name(&self) -> String {
        "borrow-expiry-order".into()
    }
}

// AbstractExpiryOrder identifies a place p1 which blocks another place p2 via a mutable
// borrow and through an abstraction edge and attempts to use p2 before p1
pub struct AbstractExpiryOrder;

impl Mutation for AbstractExpiryOrder {
    fn make_stream<'a, 'mir: 'a, 'tcx: 'mir>(
        &self,
        ctx: CompilerCtxt<'a, 'tcx>,
        body: &'a Body<'tcx>,
        curr: PcgLocation<'a, 'tcx>,
        next: PcgLocation<'a, 'tcx>,
    ) -> MutantStream<'a, 'mir, 'tcx> {
        let mut mutant_sequences = vec![];

        let borrows_graph = next.states[EvalStmtPhase::PostOperands]
            .borrow_pcg()
            .graph();

        let mutably_borrowed_places: HashSet<Place<'tcx>> = borrowed_places(&borrows_graph, is_mut)
            .map(|(place, _)| (*place).into())
            .collect();

        // Identify blocking places for each mutably borrowed place
        for place_ref in mutably_borrowed_places.iter() {
            let place = *place_ref;
            if has_named_local(place, body) {
                let mut blocking_places = places_blocking(
                    place,
                    &borrows_graph,
                    ctx,
                    |kind_set| {
                        kind_set.iter().any(|kind| match kind {
                            BorrowPcgEdgeKind::Abstraction(_) => true,
                            _ => false,
                        }) && kind_set.iter().any(|kind| match kind {
                            BorrowPcgEdgeKind::Borrow(borrow_edge) => {
                                borrow_edge.kind().iter().any(|kind| is_mut(*kind))
                            }
                            _ => false,
                        })
                    },
                    |kind| match kind {
                        BorrowPcgEdgeKind::Borrow(borrow_edge) => {
                            borrow_edge.kind().iter().any(|kind| is_mut(*kind))
                        }
                        BorrowPcgEdgeKind::BorrowPcgExpansion(expansion) => {
                            let ctx = ctx;
                            let base = expansion.base();
                            match base {
                                PcgNode::Place(p) => {
                                    p.ty(ctx).ty.ref_mutability() == Some(Mutability::Mut)
                                }
                                PcgNode::LifetimeProjection(rp) => {
                                    rp.place().ty(ctx).ty.ref_mutability()
                                        == Some(Mutability::Mut)
                                }
                            }
                        }
                        _ => true,
                    },
                );
                for blocking_place in blocking_places.drain() {
                    if has_named_local(blocking_place, body) {
                        mutant_sequences.push((place, blocking_place));
                    }
                }
            }
        }
        MutantStream::new(Box::new(Iter {
            mutant_sequences,
            ctx,
            body,
            curr,
            next,
        }))
    }
    fn name(&self) -> String {
        "abstract-expiry-order".into()
    }
}
