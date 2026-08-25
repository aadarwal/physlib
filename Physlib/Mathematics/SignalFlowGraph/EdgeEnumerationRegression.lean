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
are proved here, the second by evaluating the refinement sum and meeting the matrix-level path
gain.

## ii. Key results

- `Physlib.SignalFlowGraph.card_refiningEdgeLists_parallelPair`: the step has two refinements in
  the parallel-edge multigraph.
- `Physlib.SignalFlowGraph.card_refiningEdgeLists_singleEdge`: it has one in the single-edge
  multigraph.
- `Physlib.SignalFlowGraph.refiningEdgeLists_ne`: the two enumerations are different finite sets,
  so parallel branches stay distinct through the enumeration.
- `Physlib.SignalFlowGraph.sum_edgeListGain_parallelPair`: the refinement sum is `a + b`, which is
  the matrix-level path gain, so nothing is lost.

## iii. Table of contents

- A. The enumerations separate parallel edges
- B. The refinement sum agrees with the matrix level

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

/-- The two enumerations are different finite sets. The gain matrices of these two multigraphs are
equal, so the matrix layer cannot separate them; the edge-level enumeration does. -/
lemma refiningEdgeLists_ne (a b c : ℂ) :
    (refiningEdgeLists (parallelPair a b) [0, 1]).card
      ≠ (refiningEdgeLists (singleEdge c) [0, 1]).card := by
  rw [card_refiningEdgeLists_parallelPair, card_refiningEdgeLists_singleEdge]
  decide

/-!

## B. The refinement sum agrees with the matrix level

-/

/-- Summing the two refinements of the parallel step returns the matrix-level path gain, so the
finer enumeration computes the same value. -/
lemma sum_edgeListGain_parallelPair (a b : ℂ) :
    pathGain (parallelPair a b).toMatrix [0, 1]
      = ∑ l ∈ refiningEdgeLists (parallelPair a b) [0, 1], edgeListGain (parallelPair a b) l :=
  pathGain_toMatrix _ _

/-- The same for the single-edge multigraph. -/
lemma sum_edgeListGain_singleEdge (c : ℂ) :
    pathGain (singleEdge c).toMatrix [0, 1]
      = ∑ l ∈ refiningEdgeLists (singleEdge c) [0, 1], edgeListGain (singleEdge c) l :=
  pathGain_toMatrix _ _

/-- The edge-level determinants of the two multigraphs agree, because their gain matrices do. -/
lemma edgeGraphDet_parallelPair_eq_singleEdge (a b : ℂ) :
    edgeGraphDet (parallelPair a b) = edgeGraphDet (singleEdge (a + b)) := by
  rw [edgeGraphDet_eq_det, edgeGraphDet_eq_det, toMatrix_parallelPair_eq_singleEdge]

end Physlib.SignalFlowGraph
