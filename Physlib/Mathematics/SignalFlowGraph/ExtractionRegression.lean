/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Mathematics.SignalFlowGraph.BasicRegression
public import Physlib.Mathematics.SignalFlowGraph.Extraction

/-!
# Regression tests for signal-flow graph extraction

## i. Overview

The point of the multigraph layer is that it carries information the gain matrix does not. Two
parallel edges of gains `a` and `b` and a single edge of gain `a + b` have the **same** gain
matrix. These distinguishable edge-indexed presentations therefore collapse to the same matrix,
and the residual gap in regression row G-02 is a fact about the matrix representation rather than
an oversight in it.

An edge of gain zero is likewise still an edge: the edges joining an ordered pair of nodes do not
change when the gains are replaced, so the topology is fixed by the source and target maps alone.

The extraction hooks are also exercised. Turning a linear system into a gain matrix and reading
its system matrix back returns the original system, and a nonsymmetric system pins both the
coefficient orientation and the source/sink order of the inverse entries.

## ii. Key results

- `Physlib.SignalFlowGraph.toMatrix_parallelPair`: the gain matrix of two parallel edges.
- `Physlib.SignalFlowGraph.toMatrix_parallelPair_eq_singleEdge`: two parallel edges and one edge
  carrying their sum have the same gain matrix, so the matrix layer cannot separate them.
- `Physlib.SignalFlowGraph.edgesBetween_setGain_zero`: zeroing the gains leaves the edges alone.
- `Physlib.SignalFlowGraph.graphDet_ofSystemMatrix_twoNodeLoop`: the extraction round trip on the
  two-node feedback system.
- `Physlib.SignalFlowGraph.gain_ofSystemMatrix_nonsymmetric_forward`: a nonsymmetric inverse-entry
  sentinel for source/sink order.

## iii. Table of contents

- A. The gain matrix loses edge identity
- B. Zero gains do not remove edges
- C. Extraction from a linear system

## iv. References

The gap made concrete in section A is regression row G-02 of `goal.md` section I.3, "distinct
parallel branches remain distinct in compilation and Mason enumeration". This file shows the gain
matrix cannot meet it; an edge-based enumeration proved equal to the matrix-level sums is
scheduled separately.

These are algebraic regressions on complex matrices. No physical, optical, or signal-processing
interpretation is asserted.

-/

@[expose] public section

namespace Physlib.SignalFlowGraph

open Matrix

/-!

## A. The gain matrix loses edge identity

-/

/-- Two parallel edges from the first node to the second. -/
def parallelPair (a b : ℂ) : Multigraph (Fin 2) (Fin 2) where
  source := fun _ => 0
  target := fun _ => 1
  gain := ![a, b]

/-- A single edge from the first node to the second. -/
def singleEdge (c : ℂ) : Multigraph (Fin 2) (Fin 1) where
  source := fun _ => 0
  target := fun _ => 1
  gain := fun _ => c

/-- The gain matrix of two parallel edges carries their sum in the single nonzero entry. -/
lemma toMatrix_parallelPair (a b : ℂ) :
    (parallelPair a b).toMatrix = !![0, 0; a + b, 0] := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [Multigraph.toMatrix, Multigraph.edgesBetween, parallelPair, Fin.sum_univ_two]

/-- The gain matrix of a single edge. -/
lemma toMatrix_singleEdge (c : ℂ) : (singleEdge c).toMatrix = !![0, 0; c, 0] := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [Multigraph.toMatrix, Multigraph.edgesBetween, singleEdge]

/-- Two parallel edges and a single edge carrying their sum have the same gain matrix. These
edge-indexed presentations therefore collapse at the matrix layer, which is why the node-level
enumeration cannot meet regression row G-02 and an edge-level one is needed. -/
lemma toMatrix_parallelPair_eq_singleEdge (a b : ℂ) :
    (parallelPair a b).toMatrix = (singleEdge (a + b)).toMatrix := by
  rw [toMatrix_parallelPair, toMatrix_singleEdge]

/-- Both edges of the parallel pair join the same ordered pair of nodes. -/
lemma edgesBetween_parallelPair (a b : ℂ) :
    (parallelPair a b).edgesBetween 0 1 = Finset.univ := by
  ext e
  simp [parallelPair]

/-- The single edge joins that ordered pair of nodes. -/
lemma edgesBetween_singleEdge (c : ℂ) :
    (singleEdge c).edgesBetween 0 1 = Finset.univ := by
  ext e
  simp [singleEdge, Subsingleton.elim e 0]

/-- The two multigraphs are nevertheless different: one has two edges joining the pair of nodes
and the other has one. -/
lemma card_edgesBetween_parallelPair (a b : ℂ) :
    ((parallelPair a b).edgesBetween 0 1).card = 2 := by
  rw [edgesBetween_parallelPair, Finset.card_univ, Fintype.card_fin]

/-- The single-edge multigraph has one such edge. -/
lemma card_edgesBetween_singleEdge (c : ℂ) :
    ((singleEdge c).edgesBetween 0 1).card = 1 := by
  rw [edgesBetween_singleEdge, Finset.card_univ, Fintype.card_fin]

/-!

## B. Zero gains do not remove edges

-/

/-- Zeroing every gain leaves the edges joining each ordered pair of nodes untouched, so an edge
of gain zero is still an edge and the topology does not depend on the gains. -/
lemma edgesBetween_setGain_zero (a b : ℂ) (j i : Fin 2) :
    ((parallelPair a b).setGain 0).edgesBetween j i = (parallelPair a b).edgesBetween j i := rfl

/-- In particular the zeroed multigraph still has two edges joining the pair of nodes, while its
gain matrix is zero. -/
lemma card_edgesBetween_setGain_zero (a b : ℂ) :
    (((parallelPair a b).setGain 0).edgesBetween 0 1).card = 2 := by
  rw [edgesBetween_setGain_zero, card_edgesBetween_parallelPair]

/-!

## C. Extraction from a linear system

-/

/-- Reading the system matrix back off the graph of a linear system returns that system. -/
lemma systemMatrix_ofSystemMatrix_twoNodeLoop (a b : ℂ) :
    systemMatrix (ofSystemMatrix (systemMatrix (twoNodeLoop a b))) = !![1, -b; -a, 1] := by
  rw [systemMatrix_ofSystemMatrix, systemMatrix_twoNodeLoop]

/-- The graph determinant of the extracted graph is the determinant of the original system. -/
lemma graphDet_ofSystemMatrix_twoNodeLoop (a b : ℂ) :
    graphDet (ofSystemMatrix (systemMatrix (twoNodeLoop a b))) = 1 - a * b := by
  rw [graphDet_ofSystemMatrix, det_systemMatrix_twoNodeLoop]

/-- A nonsymmetric two-node system used to pin extraction and inverse-entry orientation. -/
def nonsymmetricSystem : Matrix (Fin 2) (Fin 2) ℂ := !![1, 2; 3, 5]

/-- Extraction takes `1 - M`, with row/column orientation unchanged. -/
lemma ofSystemMatrix_nonsymmetric :
    ofSystemMatrix nonsymmetricSystem = !![0, -2; -3, -4] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [ofSystemMatrix, nonsymmetricSystem]

/-- The gain from node zero to node one reads inverse row one, column zero. -/
lemma gain_ofSystemMatrix_nonsymmetric_forward :
    gain (ofSystemMatrix nonsymmetricSystem) 0 1 = 3 := by
  rw [gain_ofSystemMatrix, nonsymmetricSystem, Matrix.inv_def, Matrix.adjugate_fin_two_of,
    Matrix.det_fin_two_of]
  norm_num [Matrix.smul_apply, Ring.inverse_eq_inv]

/-- Reversing source and sink reads the distinct inverse row zero, column one. -/
lemma gain_ofSystemMatrix_nonsymmetric_reverse :
    gain (ofSystemMatrix nonsymmetricSystem) 1 0 = 2 := by
  rw [gain_ofSystemMatrix, nonsymmetricSystem, Matrix.inv_def, Matrix.adjugate_fin_two_of,
    Matrix.det_fin_two_of]
  norm_num [Matrix.smul_apply, Ring.inverse_eq_inv]

end Physlib.SignalFlowGraph
