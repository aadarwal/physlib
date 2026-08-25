/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Mathematics.SignalFlowGraph.CombinatoricsRegression
public import Physlib.Mathematics.SignalFlowGraph.Mason

/-!
# Regression tests for Mason's formula on representative graphs

## i. Overview

The single feedback loop is checked end to end, and the point of the check is that the two sides
are reached by routes that never meet. The left side is the entry `a / (1 - a * b)` of the inverse
system matrix, computed from the adjugate of a two-by-two matrix. The right side is the quotient
of a path sum by a loop sum: the numerator came from the decidable enumeration of forward paths
and the denominator from the alternating sum over families of non-touching loops. Neither
computation mentions the other, so their agreement is evidence rather than restatement.

The remaining examples audit the loop families themselves. Three disjoint self-loops produce all
three orders of the alternating sum with the expected signs. A two-node graph carrying both
self-loops and a two-cycle produces three first-order loops but only **one** second-order term,
because the two-cycle touches both self-loops and so forms a non-touching pair with neither; a
development that summed over all pairs of loops rather than over non-touching pairs would get an
extra term here and fail.

The last example returns to unit loop gain, where the graph determinant vanishes, and connects it
to the failure of unique solvability proved in the first regression file.

## ii. Key results

- `Physlib.SignalFlowGraph.graphDet_twoNodeLoop`: the loop sum for the single feedback loop.
- `Physlib.SignalFlowGraph.gain_eq_masonGain_twoNodeLoop`: the matrix-inverse gain and Mason's
  quotient agree.
- `Physlib.SignalFlowGraph.graphDet_diagThree`: three disjoint self-loops give all three orders.
- `Physlib.SignalFlowGraph.graphDet_fullTwoNode`: a touching two-cycle contributes no
  second-order term.
- `Physlib.SignalFlowGraph.graphDet_twoNodeLoop_one`: unit loop gain annihilates the determinant.

## iii. Table of contents

- A. The single feedback loop, end to end
- B. Auditing the loop families
- C. Unit loop gain

## iv. References

The agreement checked in section A is `goal.md` section I.3 regression row G-01, "Mason gain
equals the matrix-inverse transfer for representative graphs". The audits in section B are row
G-03, "self-loops, touching loops, and non-touching loop families have the audited gains/signs".

Row G-02, "distinct parallel branches remain distinct in compilation and Mason enumeration", is
**not** addressed here and cannot be, because the loops and paths of this development are
node-level. It is scheduled separately.

The closed form `a / (1 - a * b)` for a single feedback loop is the elementary case of Mason's
formula; see U. Siddique, S. M. Beillahi, and S. Tahar, "On the Formal Analysis of Photonic
Signal Processing Systems", FMICS 2015, LNCS 9128, Definition 4 (p. 168).

These are algebraic regressions on complex matrices. No physical, optical, or signal-processing
interpretation is asserted.

-/

@[expose] public section

namespace Physlib.SignalFlowGraph

open Matrix

/-!

## A. The single feedback loop, end to end

-/

/-- The loop sum for the two-node feedback graph is one minus its loop gain. -/
theorem graphDet_twoNodeLoop (a b : ℂ) : graphDet (twoNodeLoop a b) = 1 - a * b := by
  rw [graphDet_eq_det, det_systemMatrix_twoNodeLoop]

/-- Mason's quotient for the two-node feedback graph. -/
theorem masonGain_twoNodeLoop (a b : ℂ) :
    masonGain (twoNodeLoop a b) 0 1 = a / (1 - a * b) := by
  rw [masonGain, masonNumerator_twoNodeLoop, graphDet_twoNodeLoop]

/-- The matrix-inverse gain and Mason's quotient agree for the single feedback loop. The left side
was computed from the adjugate of the system matrix and the right side from a forward-path sum
divided by a loop sum, with no step in common. -/
theorem gain_eq_masonGain_twoNodeLoop (a b : ℂ) :
    gain (twoNodeLoop a b) 0 1 = masonGain (twoNodeLoop a b) 0 1 := by
  rw [gain_twoNodeLoop, masonGain_twoNodeLoop]

/-- Equivalently, the forward-path sum computes the cofactor of the system matrix for this
graph. -/
theorem masonNumerator_eq_adjugate_twoNodeLoop {a b : ℂ} (h : a * b ≠ 1) :
    masonNumerator (twoNodeLoop a b) 0 1 = (systemMatrix (twoNodeLoop a b)).adjugate 1 0 := by
  have hdet : graphDet (twoNodeLoop a b) ≠ 0 := by
    rw [graphDet_twoNodeLoop]
    exact sub_ne_zero_of_ne fun hcon => h hcon.symm
  exact (gain_eq_masonGain_iff _ 0 1 hdet).mp (gain_eq_masonGain_twoNodeLoop a b)

/-!

## B. Auditing the loop families

-/

/-- Three disjoint self-loops. -/
def diagThree (c d e : ℂ) : Matrix (Fin 3) (Fin 3) ℂ := !![c, 0, 0; 0, d, 0; 0, 0, e]

/-- Three disjoint self-loops produce all three orders of the alternating sum, with alternating
signs: the single loops, the three non-touching pairs, and the one non-touching triple. -/
theorem graphDet_diagThree (c d e : ℂ) :
    graphDet (diagThree c d e)
      = 1 - (c + d + e) + (c * d + c * e + d * e) - c * d * e := by
  rw [graphDet_eq_det, systemMatrix]
  have hmat : (1 : Matrix (Fin 3) (Fin 3) ℂ) - diagThree c d e
      = !![1 - c, 0, 0; 0, 1 - d, 0; 0, 0, 1 - e] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagThree]
  rw [hmat]
  simp [Matrix.det_fin_three]
  ring

/-- A two-node graph carrying both self-loops and a two-cycle. -/
def fullTwoNode (c d f g : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![c, f; g, d]

/-- The graph with two self-loops and a two-cycle has three first-order loops but only one
second-order term. The two-cycle touches both self-loops, so it pairs with neither; a development
that summed over all pairs of loops instead of over non-touching pairs would produce extra terms
here. -/
theorem graphDet_fullTwoNode (c d f g : ℂ) :
    graphDet (fullTwoNode c d f g) = 1 - c - d - f * g + c * d := by
  rw [graphDet_eq_det, systemMatrix]
  have hmat : (1 : Matrix (Fin 2) (Fin 2) ℂ) - fullTwoNode c d f g = !![1 - c, -f; -g, 1 - d] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [fullTwoNode]
  rw [hmat, det_fin_two_of]
  ring

/-!

## C. Unit loop gain

-/

/-- At unit loop gain the graph determinant vanishes, which is the loop-side reading of the
failure of unique solvability recorded in the first regression file. -/
theorem graphDet_twoNodeLoop_one : graphDet (twoNodeLoop 1 1) = 0 := by
  rw [graphDet_twoNodeLoop]
  ring

/-- At unit loop gain the node equations do not have a unique solution for every input. -/
theorem not_existsUnique_of_graphDet_twoNodeLoop_one :
    ¬ ∀ v : Fin 2 → ℂ, ∃! x, IsNodeSolution (twoNodeLoop 1 1) v x := by
  rw [← graphDet_ne_zero_iff]
  exact fun hcon => hcon graphDet_twoNodeLoop_one

end Physlib.SignalFlowGraph
