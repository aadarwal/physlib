/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Mathematics.SignalFlowGraph.Basic

/-!
# Regression tests for the node equations of a signal-flow graph

## i. Overview

The two-node feedback graph has an edge of gain `a` from the input node to the output node and an
edge of gain `b` back, so its single loop has gain `a * b`. Its system determinant is `1 - a * b`
and its gain from input to output is `a / (1 - a * b)`. Both are computed here from the matrix
inverse alone, with no topology and no Mason formula. The companion regression file for Mason's
formula derives the same value from paths and loops, so the two routes can later be compared
rather than one restating the other.

The second example fixes the solvability hypothesis. At `a = b = 1` the loop gain is one, the
system determinant vanishes, and the node equation with zero input has more than one solution.
So `Physlib.SignalFlowGraph.existsUnique_isNodeSolution_iff` is not merely a sufficient
criterion, and nonvanishing is load-bearing whenever the totalized inverse expression is
interpreted as a solved response.

## ii. Key results

- `Physlib.SignalFlowGraph.det_systemMatrix_twoNodeLoop`: the system determinant is `1 - a * b`.
- `Physlib.SignalFlowGraph.gain_twoNodeLoop`: the gain is `a / (1 - a * b)`.
- `Physlib.SignalFlowGraph.not_existsUnique_twoNodeLoop_one`: at unit loop gain the node equation
  does not have a unique solution.

## iii. Table of contents

- A. The two-node feedback graph
- B. Unit loop gain defeats unique solvability

## iv. References

The closed form `a / (1 - a * b)` for a single feedback loop is the elementary case of Mason's
formula and appears throughout the source development; see U. Siddique, S. M. Beillahi, and
S. Tahar, "On the Formal Analysis of Photonic Signal Processing Systems", FMICS 2015, LNCS 9128,
Definition 4 (p. 168). Here it is obtained from the matrix inverse, not from that formula.

These are algebraic regressions on complex matrices. No physical, optical, or signal-processing
interpretation is asserted.

-/

@[expose] public section

namespace Physlib.SignalFlowGraph

noncomputable section

open Matrix

/-!

## A. The two-node feedback graph

-/

/-- The gain matrix of the two-node feedback graph: an edge of gain `a` from node `0` to node `1`
and an edge of gain `b` back from node `1` to node `0`. -/
def twoNodeLoop (a b : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![0, b; a, 0]

/-- The system matrix of the two-node feedback graph. -/
lemma systemMatrix_twoNodeLoop (a b : ℂ) :
    systemMatrix (twoNodeLoop a b) = !![1, -b; -a, 1] := by
  rw [systemMatrix, twoNodeLoop]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The system determinant of the two-node feedback graph is one minus its loop gain. -/
lemma det_systemMatrix_twoNodeLoop (a b : ℂ) :
    (systemMatrix (twoNodeLoop a b)).det = 1 - a * b := by
  rw [systemMatrix_twoNodeLoop, det_fin_two_of]
  ring

/-- The gain from node `0` to node `1` of the two-node feedback graph, computed from the matrix
inverse. At `1 - a * b = 0` this is an equality of totalized algebraic expressions, not a solved
network response. -/
lemma gain_twoNodeLoop (a b : ℂ) : gain (twoNodeLoop a b) 0 1 = a / (1 - a * b) := by
  rw [gain, systemMatrix_twoNodeLoop, inv_def, adjugate_fin_two_of]
  have hdet : (!![(1 : ℂ), -b; -a, 1]).det = 1 - a * b := by
    rw [det_fin_two_of]
    ring
  rw [hdet]
  simp [Ring.inverse_eq_inv, div_eq_inv_mul]

/-!

## B. Unit loop gain defeats unique solvability

-/

/-- At unit loop gain the system determinant vanishes. -/
lemma det_systemMatrix_twoNodeLoop_one : (systemMatrix (twoNodeLoop 1 1)).det = 0 := by
  rw [det_systemMatrix_twoNodeLoop]
  ring

/-- At unit loop gain the node equation does not have a unique solution for every input, so the
nonvanishing hypothesis of the solvability criterion is load-bearing. -/
lemma not_existsUnique_twoNodeLoop_one :
    ¬ ∀ v : Fin 2 → ℂ, ∃! x, IsNodeSolution (twoNodeLoop 1 1) v x := by
  rw [existsUnique_isNodeSolution_iff, isUnit_iff_ne_zero]
  exact fun hcon => hcon det_systemMatrix_twoNodeLoop_one

/-- Explicitly, the all-ones vector is a nonzero solution of the zero-input node equation at unit
loop gain, alongside the zero solution. -/
lemma isNodeSolution_twoNodeLoop_one_ones :
    IsNodeSolution (twoNodeLoop 1 1) 0 (fun _ => 1) := by
  rw [isNodeSolution_iff, systemMatrix_twoNodeLoop]
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

end

end Physlib.SignalFlowGraph
