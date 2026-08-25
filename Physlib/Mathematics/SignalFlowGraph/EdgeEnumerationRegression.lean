/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Mathematics.SignalFlowGraph.EdgeEnumeration
public import Physlib.Mathematics.SignalFlowGraph.ExtractionRegression

/-!
# Regression tests for the edge-level enumeration

## i. Overview

The extraction regressions proved that the gain matrix cannot separate two parallel edges of gains
`a` and `b` from a single edge of gain `a + b`: the two multigraphs have the same gain matrix.
This file proves that the edge-level enumeration does separate them. The step from the first node
to the second has **two** refinements in the parallel-edge multigraph and **one** in the
single-edge multigraph, so the enumerations differ as finite sets even though every value computed
from them agrees.

That is the content of the outstanding regression row: distinct parallel branches remain distinct
through the enumeration, while the quantities the enumeration computes are unchanged. Both halves
are proved here, and the second is evaluated **from the enumeration**: the refinement sums are
expanded by identifying the refinement set with an image of the edge set and taking the gain of a
one-edge list, with no appeal to the theorem relating them to the gain matrix. Only afterwards is
that hand-expanded value shown to meet the general theorem, so the two routes to `a + b` share no
step.

## ii. Key results

- `Physlib.SignalFlowGraph.card_refiningEdgeLists_parallelPair`: the step has two refinements in
  the parallel-edge multigraph.
- `Physlib.SignalFlowGraph.card_refiningEdgeLists_singleEdge`: it has one in the single-edge
  multigraph.
- `Physlib.SignalFlowGraph.card_refiningEdgeLists_ne`: the two enumerations are different finite
  sets, so parallel branches stay distinct through the enumeration.
- `Physlib.SignalFlowGraph.sum_refining_parallelPair`: the refinement sum is `a + b`, evaluated
  from the enumeration itself.
- `Physlib.SignalFlowGraph.pathGain_toMatrix_parallelPair`: that hand-expanded value meets the
  general theorem, which computes the same number through the gain matrix.

## iii. Table of contents

- A. The enumerations separate parallel edges
- B. The refinement sums, hand-expanded

## iv. References

This closes regression row G-02 of `goal.md` section I.3, "distinct parallel branches remain
distinct in compilation and Mason enumeration". The pair of multigraphs is the one introduced in
`Physlib.Mathematics.SignalFlowGraph.ExtractionRegression`, where their gain matrices were proved
equal.

These are decidable evaluations and algebraic identities on complex matrices. No physical,
optical, or signal-processing interpretation is asserted.

-/

@[expose] public section

namespace Physlib.SignalFlowGraph

open Matrix

/-!

## A. The enumerations separate parallel edges

-/

/-- The step between the two nodes has two edge-level refinements when the edges are parallel. -/
lemma card_refiningEdgeLists_parallelPair (a b : ℂ) :
    ((refiningEdgeLists (parallelPair a b) [0, 1]).card) = 2 := by
  rw [refiningEdgeLists_pair, edgesBetween_parallelPair,
    Finset.card_image_of_injective _ (fun x y h => by simpa using h), Finset.card_univ,
    Fintype.card_fin]

/-- It has one refinement when there is a single edge. -/
lemma card_refiningEdgeLists_singleEdge (c : ℂ) :
    ((refiningEdgeLists (singleEdge c) [0, 1]).card) = 1 := by
  rw [refiningEdgeLists_pair, edgesBetween_singleEdge,
    Finset.card_image_of_injective _ (fun x y h => by simpa using h), Finset.card_univ,
    Fintype.card_fin]

/-- The two enumerations are different finite sets. The gain matrices of these two multigraphs
are equal, by `toMatrix_parallelPair_eq_singleEdge`, so the matrix layer cannot separate them; the
edge-level enumeration does. -/
lemma card_refiningEdgeLists_ne (a b : ℂ) :
    (refiningEdgeLists (parallelPair a b) [0, 1]).card
      ≠ (refiningEdgeLists (singleEdge (a + b)) [0, 1]).card := by
  rw [card_refiningEdgeLists_parallelPair, card_refiningEdgeLists_singleEdge]
  decide

/-!

## B. The refinement sums, hand-expanded

-/

/-- The two refinements of the parallel step sum to `a + b`. This is evaluated from the
enumeration itself: the refinement set is the image of the edge set, and the gain of a one-edge
list is that edge's gain. Nothing here passes through `pathGain_toMatrix`, so a swapped gain, an
omitted branch, or a wrong edge-list product would fail it. -/
lemma sum_refining_parallelPair (a b : ℂ) :
    ∑ l ∈ refiningEdgeLists (parallelPair a b) [0, 1], edgeListGain (parallelPair a b) l
      = a + b := by
  rw [refiningEdgeLists_pair, edgesBetween_parallelPair,
    Finset.sum_image fun x _ y _ h => by simpa using h]
  simp [edgeListGain, parallelPair, Fin.sum_univ_two]

/-- The single refinement of the single-edge step sums to that edge's gain. -/
lemma sum_refining_singleEdge (c : ℂ) :
    ∑ l ∈ refiningEdgeLists (singleEdge c) [0, 1], edgeListGain (singleEdge c) l = c := by
  rw [refiningEdgeLists_pair, edgesBetween_singleEdge,
    Finset.sum_image fun x _ y _ h => by simpa using h]
  simp [edgeListGain, singleEdge]

/-- The two enumerations, which are different finite sets, nevertheless sum to the same value.
Both sides were evaluated from the enumerations, not read off the gain matrix. -/
lemma sum_refining_parallelPair_eq_singleEdge (a b : ℂ) :
    ∑ l ∈ refiningEdgeLists (parallelPair a b) [0, 1], edgeListGain (parallelPair a b) l
      = ∑ l ∈ refiningEdgeLists (singleEdge (a + b)) [0, 1],
          edgeListGain (singleEdge (a + b)) l := by
  rw [sum_refining_parallelPair, sum_refining_singleEdge]

/-- The hand-expanded refinement sum meets the general theorem: the left side is computed through
the gain matrix and the right side from the enumeration, with no step in common. -/
lemma pathGain_toMatrix_parallelPair (a b : ℂ) :
    pathGain (parallelPair a b).toMatrix [0, 1] = a + b := by
  rw [pathGain_toMatrix, sum_refining_parallelPair]

/-- The same for the single-edge multigraph. -/
lemma pathGain_toMatrix_singleEdge (c : ℂ) :
    pathGain (singleEdge c).toMatrix [0, 1] = c := by
  rw [pathGain_toMatrix, sum_refining_singleEdge]

/-- The edge-level determinants of the two multigraphs agree, because their gain matrices do. -/
lemma edgeGraphDet_parallelPair_eq_singleEdge (a b : ℂ) :
    edgeGraphDet (parallelPair a b) = edgeGraphDet (singleEdge (a + b)) := by
  rw [edgeGraphDet_eq_det, edgeGraphDet_eq_det, toMatrix_parallelPair_eq_singleEdge]

end Physlib.SignalFlowGraph
