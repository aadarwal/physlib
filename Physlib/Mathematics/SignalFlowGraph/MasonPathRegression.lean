/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Mathematics.SignalFlowGraph.MasonPath
public import Physlib.Mathematics.SignalFlowGraph.NumeratorRegression

/-!
# Regression tests for Mason's gain formula over forward paths

## i. Overview

The single feedback loop is carried through the finished formula. Its gain, computed from the
adjugate of a two-by-two matrix, is `a / (1 - a * b)`; Mason's quotient, computed from the
decidable enumeration of forward paths divided by the alternating sum over loop families, is the
same. That agreement was already checked directly for this graph before the general theorem
existed, so this file also confirms that the general theorem specialises to what the earlier
direct computation gave, rather than replacing it.

The orbit path is also evaluated. The permutation that swaps the two nodes routes the sink back
to the source, and its orbit path is the two-node forward path; that is what the bijection
attaches to the closing family, and it is checked here by computation rather than by an argument.

## ii. Key results

- `Physlib.SignalFlowGraph.masonGain_twoNodeLoop_eq_gain`: Mason's quotient is the gain for the
  single feedback loop, now as an instance of the general theorem.
- `Physlib.SignalFlowGraph.orbitPath_swap`: the orbit path of the closing family of the two-node
  feedback graph is its forward path.

## iii. Table of contents

- A. The single feedback loop under the general theorem
- B. The orbit path of a closing family

## iv. References

The general theorem exercised here is `Physlib.SignalFlowGraph.masonGain_eq_gain`, the classical
statement of Mason's rule; see U. Siddique, S. M. Beillahi, and S. Tahar, "On the Formal Analysis
of Photonic Signal Processing Systems", FMICS 2015, LNCS 9128, Definition 4 (p. 168).

These are algebraic regressions on complex matrices. No physical, optical, or signal-processing
interpretation is asserted.

-/

@[expose] public section

namespace Physlib.SignalFlowGraph

open Matrix

/-!

## A. The single feedback loop under the general theorem

-/

/-- For the single feedback loop, Mason's quotient is the gain, as an instance of the general
lemma rather than by direct computation. -/
lemma masonGain_twoNodeLoop_eq_gain {a b : ℂ} (h : a * b ≠ 1) :
    masonGain (twoNodeLoop a b) 0 1 = gain (twoNodeLoop a b) 0 1 := by
  refine masonGain_eq_gain _ 0 1 ?_
  rw [graphDet_twoNodeLoop]
  exact sub_ne_zero_of_ne fun hcon => h hcon.symm

/-- The general theorem specialises to the value computed directly before it existed. -/
lemma masonGain_twoNodeLoop_eq {a b : ℂ} (h : a * b ≠ 1) :
    masonGain (twoNodeLoop a b) 0 1 = a / (1 - a * b) := by
  rw [masonGain_twoNodeLoop_eq_gain h, gain_twoNodeLoop]

/-- The forward-path numerator is the cofactor for this graph, now unconditionally. -/
lemma masonNumerator_eq_adjugate_twoNodeLoop' (a b : ℂ) :
    masonNumerator (twoNodeLoop a b) 0 1 = (systemMatrix (twoNodeLoop a b)).adjugate 1 0 :=
  masonNumerator_eq_adjugate _ 0 1

/-!

## B. The orbit path of a closing family

-/

/-- The permutation swapping the two nodes routes the sink back to the source. -/
lemma swap_apply_one : (Equiv.swap (0 : Fin 2) 1) 1 = 0 := by
  rw [Equiv.swap_apply_right]

/-- The orbit path of that closing family is the two-node forward path, which is what the
bijection attaches to it. -/
lemma orbitPath_swap : orbitPath (Equiv.swap (0 : Fin 2) 1) 1 = [0, 1] := by
  have hne : (Equiv.swap (0 : Fin 2) 1) 1 ≠ 1 := by
    rw [swap_apply_one]
    decide
  have hnd : ([0, 1] : List (Fin 2)).Nodup := by decide
  have hhead : ([0, 1] : List (Fin 2)).head? = some 0 := rfl
  have hlast : ([0, 1] : List (Fin 2)).getLast? = some 1 := rfl
  have hform : ([0, 1] : List (Fin 2)).formPerm = Equiv.swap 0 1 := List.formPerm_pair 0 1
  have hdisj : Disjoint (1 : Equiv.Perm (Fin 2)).support ([0, 1] : List (Fin 2)).toFinset := by
    simp
  have := orbitPath_mul (p := ([0, 1] : List (Fin 2))) (τ := 1) (s := 0) (t := 1)
    hnd hhead hlast hdisj
  rwa [hform, mul_one] at this

end Physlib.SignalFlowGraph
