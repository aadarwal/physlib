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
attaches to the closing family, and it is settled here by evaluation, so the check does not lean
on the recovery lemma it exercises. A second statement records that the recovery lemma delivers
the same list.

## ii. Key results

- `Physlib.SignalFlowGraph.masonGain_twoNodeLoop_eq_gain`: Mason's quotient is the gain for the
  single feedback loop, now as an instance of the general theorem.
- `Physlib.SignalFlowGraph.masonGain_twoNodeLoop_eq`: and it takes the value computed directly
  before the general theorem existed.
- `Physlib.SignalFlowGraph.orbitPath_swap`: the orbit path of the closing family of the two-node
  feedback graph is its forward path, settled by evaluation.
- `Physlib.SignalFlowGraph.orbitPath_swap_eq_recovery`: the recovery lemma agrees with it.

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

/-!

## B. The orbit path of a closing family

-/

/-- The permutation swapping the two nodes routes the sink back to the source. -/
lemma swap_apply_one : (Equiv.swap (0 : Fin 2) 1) 1 = 0 := by
  rw [Equiv.swap_apply_right]

/-- The orbit path of that closing family is the two-node forward path, which is what the
bijection attaches to it. This is settled by evaluation, so it does not lean on the recovery
lemma it is meant to exercise. -/
lemma orbitPath_swap : orbitPath (Equiv.swap (0 : Fin 2) 1) 1 = [0, 1] := by decide

/-- The recovery lemma delivers the same list on this instance, so the two agree where they
overlap. -/
lemma orbitPath_swap_eq_recovery :
    orbitPath ((([0, 1] : List (Fin 2)).formPerm) * 1) 1 = [0, 1] :=
  orbitPath_mul (by decide) rfl rfl (by simp)

end Physlib.SignalFlowGraph
