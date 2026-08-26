/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Systems.Cascade.PandaMason

/-!
# Edge-level PANDA topology regression

## i. Overview

This module audits the retained 18-node, 24-edge projection at branch level. It lists all five
simple source-to-through paths, both simple source-to-drop paths, and the six simple loops up to
the canonical base nodes 2, 11, and 16 in the paper's one-based numbering. Every node list is
paired with its unique edge refinement, so parallel-branch identities cannot disappear behind a
coefficient matrix.

The two side-ring loops and four main-ring loops are distinct. The latter independently select
the direct or circulating route at each side coupler. Counts, edge refinements, path simplicity,
and retained adjacency are proved facts rather than comments.

A negative control cross-wires the two asymmetric half-ring joins. The resulting graph has the
same node and edge types and all the same gains, but the expected right-ring refinement vanishes.
This sentinel therefore detects topology errors that a scalar formula chosen after the fact could
hide.

## ii. Key results

- `Panda.topologyThroughPaths_card`: exactly five listed through paths.
- `Panda.topologyDropPaths_card`: exactly two listed drop paths.
- `Panda.topologyCanonicalLoops_card`: exactly six listed canonical loops.
- `Panda.topology_path_refinements`: all seven path refinements, with edge identities.
- `Panda.topology_loop_refinements`: all six loop refinements, with edge identities.
- `Panda.topology_miswired_rightDetour_not_refined`: asymmetric cross-wire sentinel.

## iii. Table of contents

- A. Retained adjacency
- B. Through and drop paths
- C. Canonically based simple loops
- D. Edge-refinement teeth
- E. Asymmetric mis-wiring sentinel

## iv. References

This is an edge-topology audit of the directed Definition-11 projection. It neither identifies
that projection with NSV'16's undirected graph nor asserts passivity, reciprocity, losslessness,
causality, stability, resonance, bandwidth, dispersion, or material realization.
-/

@[expose] public section

namespace Optics

noncomputable section

namespace Panda

open Physlib.SignalFlowGraph
/-!
## A. Retained adjacency
-/
/-- Adjacency in the retained 24-edge topology, independent of all gains. -/
def TopologyAdjacent (first second : Node) : Prop :=
  ∃ edge : Edge, edgeSource edge = first ∧ edgeTarget edge = second

/-- Retained adjacency has a computable decision procedure by enumerating the 24 edge labels. -/
instance topologyAdjacentDecidable (first second : Node) :
    Decidable (TopologyAdjacent first second) := by
  unfold TopologyAdjacent
  infer_instance
/-!
## B. Through and drop paths
-/
/-- The direct bus path to the through port. -/
def topologyThroughDirect : List Node := [0, 2]

/-- The main-ring path using both direct side-coupler branches. -/
def topologyThroughMainDirect : List Node := [0, 3, 8, 9, 4, 6, 13, 14, 1, 2]

/-- The main-ring path circulating through the right side ring only. -/
def topologyThroughRightCirculation : List Node :=
  [0, 3, 8, 11, 12, 10, 9, 4, 6, 13, 14, 1, 2]

/-- The main-ring path circulating through the left side ring only. -/
def topologyThroughLeftCirculation : List Node :=
  [0, 3, 8, 9, 4, 6, 13, 16, 17, 15, 14, 1, 2]

/-- The main-ring path circulating through both side rings. -/
def topologyThroughBothCirculations : List Node :=
  [0, 3, 8, 11, 12, 10, 9, 4, 6, 13, 16, 17, 15, 14, 1, 2]

/-- The five retained simple source-to-through paths. -/
def topologyThroughPaths : Finset (List Node) :=
  {topologyThroughDirect, topologyThroughMainDirect,
    topologyThroughRightCirculation, topologyThroughLeftCirculation,
    topologyThroughBothCirculations}

/-- There are five distinct retained source-to-through paths in the audit. -/
lemma topologyThroughPaths_card : topologyThroughPaths.card = 5 := by decide

/-- The direct right-coupler route to the drop port. -/
def topologyDropDirect : List Node := [0, 3, 8, 9, 4, 7]

/-- The right-side-ring circulation route to the drop port. -/
def topologyDropRightCirculation : List Node := [0, 3, 8, 11, 12, 10, 9, 4, 7]

/-- The two retained simple source-to-drop paths. -/
def topologyDropPaths : Finset (List Node) :=
  {topologyDropDirect, topologyDropRightCirculation}

/-- There are two distinct retained source-to-drop paths in the audit. -/
lemma topologyDropPaths_card : topologyDropPaths.card = 2 := by decide

/-- Every listed through path is repetition-free, has the declared terminals, and follows retained
adjacency. -/
lemma topologyThroughPaths_sound (path : List Node) (hPath : path ∈ topologyThroughPaths) :
    path.Nodup ∧ path.head? = some 0 ∧ path.getLast? = some 2 ∧
      path.IsChain TopologyAdjacent := by
  simp only [topologyThroughPaths, Finset.mem_insert, Finset.mem_singleton] at hPath
  rcases hPath with rfl | rfl | rfl | rfl | rfl
  all_goals decide

/-- Every listed drop path is repetition-free, has the declared terminals, and follows retained
adjacency. -/
lemma topologyDropPaths_sound (path : List Node) (hPath : path ∈ topologyDropPaths) :
    path.Nodup ∧ path.head? = some 0 ∧ path.getLast? = some 7 ∧
      path.IsChain TopologyAdjacent := by
  simp only [topologyDropPaths, Finset.mem_insert, Finset.mem_singleton] at hPath
  rcases hPath with rfl | rfl
  all_goals decide
/-!
## C. Canonically based simple loops
-/
/-- The three-edge right side-ring loop, based at source node eleven. -/
def topologyRightLoop : List Node := [10, 11, 12, 10]

/-- The three-edge left side-ring loop, based at source node sixteen. -/
def topologyLeftLoop : List Node := [15, 16, 17, 15]

/-- The main loop using both direct side-coupler branches, based at source node two. -/
def topologyMainDirectLoop : List Node := [1, 3, 8, 9, 4, 6, 13, 14, 1]

/-- The main loop circulating through the right side ring only. -/
def topologyMainRightLoop : List Node := [1, 3, 8, 11, 12, 10, 9, 4, 6, 13, 14, 1]

/-- The main loop circulating through the left side ring only. -/
def topologyMainLeftLoop : List Node := [1, 3, 8, 9, 4, 6, 13, 16, 17, 15, 14, 1]

/-- The main loop circulating through both side rings. -/
def topologyMainBothLoop : List Node :=
  [1, 3, 8, 11, 12, 10, 9, 4, 6, 13, 16, 17, 15, 14, 1]

/-- The six simple loops, with one canonical base point selected for each cyclic rotation class. -/
def topologyCanonicalLoops : Finset (List Node) :=
  {topologyRightLoop, topologyLeftLoop, topologyMainDirectLoop,
    topologyMainRightLoop, topologyMainLeftLoop, topologyMainBothLoop}

/-- The audit contains six distinct canonically based loops. -/
lemma topologyCanonicalLoops_card : topologyCanonicalLoops.card = 6 := by decide

/-- Every listed loop closes, has no repeated node before closure, and follows retained
adjacency. -/
lemma topologyCanonicalLoops_sound (loop : List Node) (hLoop : loop ∈ topologyCanonicalLoops) :
    loop ≠ [] ∧ loop.head? = loop.getLast? ∧ loop.dropLast.Nodup ∧
      loop.IsChain TopologyAdjacent := by
  simp only [topologyCanonicalLoops, Finset.mem_insert, Finset.mem_singleton] at hLoop
  rcases hLoop with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide
/-!
## D. Edge-refinement teeth
-/
/-- All five through paths have exactly the displayed edge refinements. -/
lemma topology_path_refinements (p : Parameters) :
    refiningEdgeLists (signalMultigraph p) topologyThroughDirect = { [0] } ∧
      refiningEdgeLists (signalMultigraph p) topologyThroughMainDirect =
        { [1, 4, 5, 11, 12, 16, 17, 23, 3] } ∧
      refiningEdgeLists (signalMultigraph p) topologyThroughRightCirculation =
        { [1, 4, 6, 7, 8, 9, 11, 12, 16, 17, 23, 3] } ∧
      refiningEdgeLists (signalMultigraph p) topologyThroughLeftCirculation =
        { [1, 4, 5, 11, 12, 16, 18, 19, 20, 22, 23, 3] } ∧
      refiningEdgeLists (signalMultigraph p) topologyThroughBothCirculations =
        { [1, 4, 6, 7, 8, 9, 11, 12, 16, 18, 19, 20, 22, 23, 3] } := by
  simp [refiningEdgeLists, Physlib.SignalFlowGraph.Multigraph.edgesBetween,
    signalMultigraph, edgeSource, edgeTarget, topologyThroughDirect,
    topologyThroughMainDirect, topologyThroughRightCirculation,
    topologyThroughLeftCirculation, topologyThroughBothCirculations]
  all_goals decide

/-- Both drop paths have exactly the displayed edge refinements. -/
lemma topology_drop_path_refinements (p : Parameters) :
    refiningEdgeLists (signalMultigraph p) topologyDropDirect =
        { [1, 4, 5, 11, 13] } ∧
      refiningEdgeLists (signalMultigraph p) topologyDropRightCirculation =
        { [1, 4, 6, 7, 8, 9, 11, 13] } := by
  simp [refiningEdgeLists, Physlib.SignalFlowGraph.Multigraph.edgesBetween,
    signalMultigraph, edgeSource, edgeTarget, topologyDropDirect,
    topologyDropRightCirculation]
  all_goals decide

/-- All six canonical loops have exactly the displayed edge refinements. -/
lemma topology_loop_refinements (p : Parameters) :
    refiningEdgeLists (signalMultigraph p) topologyRightLoop = { [10, 7, 8] } ∧
      refiningEdgeLists (signalMultigraph p) topologyLeftLoop = { [21, 19, 20] } ∧
      refiningEdgeLists (signalMultigraph p) topologyMainDirectLoop =
        { [2, 4, 5, 11, 12, 16, 17, 23] } ∧
      refiningEdgeLists (signalMultigraph p) topologyMainRightLoop =
        { [2, 4, 6, 7, 8, 9, 11, 12, 16, 17, 23] } ∧
      refiningEdgeLists (signalMultigraph p) topologyMainLeftLoop =
        { [2, 4, 5, 11, 12, 16, 18, 19, 20, 22, 23] } ∧
      refiningEdgeLists (signalMultigraph p) topologyMainBothLoop =
        { [2, 4, 6, 7, 8, 9, 11, 12, 16, 18, 19, 20, 22, 23] } := by
  simp [refiningEdgeLists, Physlib.SignalFlowGraph.Multigraph.edgesBetween,
    signalMultigraph, edgeSource, edgeTarget, topologyRightLoop, topologyLeftLoop,
    topologyMainDirectLoop, topologyMainRightLoop, topologyMainLeftLoop,
    topologyMainBothLoop]
  all_goals decide

/-- The right side-loop edge list has gain `cr * r1 * r2`. -/
lemma topology_rightLoop_gain (p : Parameters) :
    edgeListGain (signalMultigraph p) [10, 7, 8] =
      (p.rightCoupler.throughAmplitude : ℂ) * p.rightRoundTripCoefficient := by
  simp [edgeListGain, signalMultigraph, edgeGain, Parameters.rightRoundTripCoefficient]

/-- The left side-loop edge list has gain `cl * l1 * l2`. -/
lemma topology_leftLoop_gain (p : Parameters) :
    edgeListGain (signalMultigraph p) [21, 19, 20] =
      (p.leftCoupler.throughAmplitude : ℂ) * p.leftRoundTripCoefficient := by
  simp [edgeListGain, signalMultigraph, edgeGain, Parameters.leftRoundTripCoefficient]

/-- The five through-path edge products retain every coupler and propagation choice. -/
lemma topology_throughPath_gains (p : Parameters) :
    edgeListGain (signalMultigraph p) [0] =
        (p.inputCoupler.throughAmplitude : ℂ) ∧
      edgeListGain (signalMultigraph p) [1, 4, 5, 11, 12, 16, 17, 23, 3] =
        DirectionalCoupler.crossCoefficient p.inputCoupler *
          p.mainQuarterOneCoefficient * p.rightCoupler.throughAmplitude *
          p.mainQuarterTwoCoefficient * p.outputCoupler.throughAmplitude *
          p.mainQuarterThreeCoefficient * p.leftCoupler.throughAmplitude *
          p.mainQuarterFourCoefficient *
          DirectionalCoupler.crossCoefficient p.inputCoupler ∧
      edgeListGain (signalMultigraph p)
          [1, 4, 6, 7, 8, 9, 11, 12, 16, 17, 23, 3] =
        DirectionalCoupler.crossCoefficient p.inputCoupler *
          p.mainQuarterOneCoefficient *
          DirectionalCoupler.crossCoefficient p.rightCoupler *
          p.rightHalfOneCoefficient * p.rightHalfTwoCoefficient *
          DirectionalCoupler.crossCoefficient p.rightCoupler *
          p.mainQuarterTwoCoefficient * p.outputCoupler.throughAmplitude *
          p.mainQuarterThreeCoefficient * p.leftCoupler.throughAmplitude *
          p.mainQuarterFourCoefficient *
          DirectionalCoupler.crossCoefficient p.inputCoupler ∧
      edgeListGain (signalMultigraph p)
          [1, 4, 5, 11, 12, 16, 18, 19, 20, 22, 23, 3] =
        DirectionalCoupler.crossCoefficient p.inputCoupler *
          p.mainQuarterOneCoefficient * p.rightCoupler.throughAmplitude *
          p.mainQuarterTwoCoefficient * p.outputCoupler.throughAmplitude *
          p.mainQuarterThreeCoefficient *
          DirectionalCoupler.crossCoefficient p.leftCoupler *
          p.leftHalfOneCoefficient * p.leftHalfTwoCoefficient *
          DirectionalCoupler.crossCoefficient p.leftCoupler *
          p.mainQuarterFourCoefficient *
          DirectionalCoupler.crossCoefficient p.inputCoupler ∧
      edgeListGain (signalMultigraph p)
          [1, 4, 6, 7, 8, 9, 11, 12, 16, 18, 19, 20, 22, 23, 3] =
        DirectionalCoupler.crossCoefficient p.inputCoupler *
          p.mainQuarterOneCoefficient *
          DirectionalCoupler.crossCoefficient p.rightCoupler *
          p.rightHalfOneCoefficient * p.rightHalfTwoCoefficient *
          DirectionalCoupler.crossCoefficient p.rightCoupler *
          p.mainQuarterTwoCoefficient * p.outputCoupler.throughAmplitude *
          p.mainQuarterThreeCoefficient *
          DirectionalCoupler.crossCoefficient p.leftCoupler *
          p.leftHalfOneCoefficient * p.leftHalfTwoCoefficient *
          DirectionalCoupler.crossCoefficient p.leftCoupler *
          p.mainQuarterFourCoefficient *
          DirectionalCoupler.crossCoefficient p.inputCoupler := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [edgeListGain, signalMultigraph, edgeGain] <;> ring

/-- The two drop-path edge products distinguish direct and right-ring-circulating routes. -/
lemma topology_dropPath_gains (p : Parameters) :
    edgeListGain (signalMultigraph p) [1, 4, 5, 11, 13] =
        DirectionalCoupler.crossCoefficient p.inputCoupler *
          p.mainQuarterOneCoefficient * p.rightCoupler.throughAmplitude *
          p.mainQuarterTwoCoefficient *
          DirectionalCoupler.crossCoefficient p.outputCoupler ∧
      edgeListGain (signalMultigraph p) [1, 4, 6, 7, 8, 9, 11, 13] =
        DirectionalCoupler.crossCoefficient p.inputCoupler *
          p.mainQuarterOneCoefficient *
          DirectionalCoupler.crossCoefficient p.rightCoupler *
          p.rightHalfOneCoefficient * p.rightHalfTwoCoefficient *
          DirectionalCoupler.crossCoefficient p.rightCoupler *
          p.mainQuarterTwoCoefficient *
          DirectionalCoupler.crossCoefficient p.outputCoupler := by
  constructor <;> simp [edgeListGain, signalMultigraph, edgeGain] <;> ring

/-- The four main-loop edge products independently retain both side-ring route choices. -/
lemma topology_mainLoop_gains (p : Parameters) :
    edgeListGain (signalMultigraph p) [2, 4, 5, 11, 12, 16, 17, 23] =
        (p.inputCoupler.throughAmplitude : ℂ) * p.mainQuarterOneCoefficient *
          p.rightCoupler.throughAmplitude * p.mainQuarterTwoCoefficient *
          p.outputCoupler.throughAmplitude * p.mainQuarterThreeCoefficient *
          p.leftCoupler.throughAmplitude * p.mainQuarterFourCoefficient ∧
      edgeListGain (signalMultigraph p) [2, 4, 6, 7, 8, 9, 11, 12, 16, 17, 23] =
        (p.inputCoupler.throughAmplitude : ℂ) * p.mainQuarterOneCoefficient *
          DirectionalCoupler.crossCoefficient p.rightCoupler *
          p.rightHalfOneCoefficient * p.rightHalfTwoCoefficient *
          DirectionalCoupler.crossCoefficient p.rightCoupler *
          p.mainQuarterTwoCoefficient * p.outputCoupler.throughAmplitude *
          p.mainQuarterThreeCoefficient * p.leftCoupler.throughAmplitude *
          p.mainQuarterFourCoefficient ∧
      edgeListGain (signalMultigraph p)
          [2, 4, 5, 11, 12, 16, 18, 19, 20, 22, 23] =
        (p.inputCoupler.throughAmplitude : ℂ) * p.mainQuarterOneCoefficient *
          p.rightCoupler.throughAmplitude * p.mainQuarterTwoCoefficient *
          p.outputCoupler.throughAmplitude * p.mainQuarterThreeCoefficient *
          DirectionalCoupler.crossCoefficient p.leftCoupler *
          p.leftHalfOneCoefficient * p.leftHalfTwoCoefficient *
          DirectionalCoupler.crossCoefficient p.leftCoupler *
          p.mainQuarterFourCoefficient ∧
      edgeListGain (signalMultigraph p)
          [2, 4, 6, 7, 8, 9, 11, 12, 16, 18, 19, 20, 22, 23] =
        (p.inputCoupler.throughAmplitude : ℂ) * p.mainQuarterOneCoefficient *
          DirectionalCoupler.crossCoefficient p.rightCoupler *
          p.rightHalfOneCoefficient * p.rightHalfTwoCoefficient *
          DirectionalCoupler.crossCoefficient p.rightCoupler *
          p.mainQuarterTwoCoefficient * p.outputCoupler.throughAmplitude *
          p.mainQuarterThreeCoefficient *
          DirectionalCoupler.crossCoefficient p.leftCoupler *
          p.leftHalfOneCoefficient * p.leftHalfTwoCoefficient *
          DirectionalCoupler.crossCoefficient p.leftCoupler *
          p.mainQuarterFourCoefficient := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [edgeListGain, signalMultigraph, edgeGain] <;> ring

/-- The loop intersection audit records both non-touching and touching cases used by Mason
cofactors. -/
lemma topology_loop_touch_audit :
    Disjoint topologyRightLoop.dropLast.toFinset topologyLeftLoop.dropLast.toFinset ∧
      Disjoint topologyRightLoop.dropLast.toFinset topologyMainDirectLoop.dropLast.toFinset ∧
      Disjoint topologyLeftLoop.dropLast.toFinset topologyMainDirectLoop.dropLast.toFinset ∧
      Disjoint topologyRightLoop.dropLast.toFinset topologyMainLeftLoop.dropLast.toFinset ∧
      Disjoint topologyLeftLoop.dropLast.toFinset topologyMainRightLoop.dropLast.toFinset ∧
      ¬Disjoint topologyRightLoop.dropLast.toFinset topologyMainRightLoop.dropLast.toFinset ∧
      ¬Disjoint topologyLeftLoop.dropLast.toFinset topologyMainLeftLoop.dropLast.toFinset := by
  decide
/-!
## E. Asymmetric mis-wiring sentinel
-/
/-- The wrong targets obtained by cross-wiring the two first-to-second half-ring joins. -/
def topologyMiswiredEdgeTarget : Edge → Node := fun edge ↦
  if edge = 7 then 17 else if edge = 19 then 12 else edgeTarget edge

/-- A deliberately cross-wired graph that preserves every gain and both finite counts. -/
def topologyMiswiredMultigraph (p : Parameters) :
    Physlib.SignalFlowGraph.Multigraph Node Edge where
  source := edgeSource
  target := topologyMiswiredEdgeTarget
  gain := edgeGain p

/-- The gain-free topology of the cross-wired negative control. -/
def topologyMiswiredSkeleton : Physlib.SignalFlowGraph.Multigraph Node Edge where
  source := edgeSource
  target := topologyMiswiredEdgeTarget
  gain := fun _ ↦ 0

/-- The cross-wire changes the right half join from node thirteen to node eighteen. -/
lemma topology_miswired_join_sentinel :
    topologyMiswiredEdgeTarget 7 = 17 ∧ edgeTarget 7 = 12 := by decide

/-- The asymmetric cross-wire is not the retained graph, regardless of the scalar gains. -/
lemma topologyMiswiredMultigraph_ne (p : Parameters) :
    topologyMiswiredMultigraph p ≠ signalMultigraph p := by
  intro hGraph
  have hTarget := congrArg (fun graph => graph.target 7) hGraph
  simp [topologyMiswiredMultigraph, topologyMiswiredEdgeTarget,
    signalMultigraph, edgeTarget] at hTarget

private lemma topology_miswired_skeleton_rightDetour_not_refined :
    [1, 4, 6, 7, 8, 9, 11, 13] ∉
      refiningEdgeLists topologyMiswiredSkeleton topologyDropRightCirculation := by
  decide

/-- The expected right-circulation refinement disappears after the asymmetric join cross-wire. -/
lemma topology_miswired_rightDetour_not_refined (p : Parameters) :
    [1, 4, 6, 7, 8, 9, 11, 13] ∉
      refiningEdgeLists (topologyMiswiredMultigraph p) topologyDropRightCirculation := by
  change [1, 4, 6, 7, 8, 9, 11, 13] ∉
    refiningEdgeLists topologyMiswiredSkeleton topologyDropRightCirculation
  exact topology_miswired_skeleton_rightDetour_not_refined

end Panda

end

end Optics
