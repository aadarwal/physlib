/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Mathematics.ZTransform.DifferenceEquationRegression
public import Physlib.Mathematics.ZTransform.Existence

/-!
# Regression tests for the existence of causal solutions

## i. Overview

The one-pole recurrence driven by the unit impulse closes a loop that spans the whole
development. Its causal solution is constructed by recursion on the index in
`Physlib.Mathematics.ZTransform.Existence`, with no formula in sight; the causal geometric
sequence is defined in `Physlib.Mathematics.ZTransform.Convergence` by scaling a unit step, with
no recurrence in sight; and uniqueness in
`Physlib.Mathematics.ZTransform.DifferenceEquation` forces them to be the same sequence. Three
constructions that never mention each other meet on one object.

Because a causal solution now exists and is unique, the transfer relation no longer depends on a
solution supplied as a hypothesis. The second example states it in that form for the one-pole
recurrence while retaining the convergence and denominator hypotheses required for evaluation.

## ii. Key results

- `Physlib.ZTransform.recurrenceSolution_onePole`: the recursively constructed causal solution of
  the one-pole recurrence is the geometric sequence.
- `Physlib.ZTransform.transform_recurrenceSolution_onePole`: the transfer relation for the
  one-pole recurrence, with no solution supplied as a hypothesis.

## iii. Table of contents

- A. The constructed solution of the one-pole recurrence
- B. The transfer relation with no solution hypothesis

## iv. References

The existence construction has no counterpart in any fetched source of the Concordia HVG corpus;
U. Siddique, M. Y. Mahmoud, and S. Tahar, "On the Formalization of Z-Transform in HOL", ITP 2014,
LNCS 8558, Definition 10 and Theorem 11 (p. 492) take a solution as given. So these are not
parity regressions.

These are algebraic regressions on complex sequences. No physical, optical, or signal-processing
interpretation is asserted.

-/

@[expose] public section

namespace Physlib.ZTransform

noncomputable section

/-!

## A. The constructed solution of the one-pole recurrence

-/

/-- The lag set of the one-pole recurrence excludes the lag zero, so its feedback is strictly
causal. -/
lemma zero_notMem_onePole_lags : (0 : ℕ) ∉ ({1} : Finset ℕ) := by decide

/-- The recursively constructed causal solution of the one-pole recurrence driven by the unit
impulse is the causal geometric sequence. The two are built by unrelated means and are forced
together by uniqueness. -/
lemma recurrenceSolution_onePole (a : ℂ) :
    recurrenceSolution {1} {0} (onePoleFeedback a) onePoleFeedforward unitImpulse
      = geometricSeq a :=
  (eq_recurrenceSolution zero_notMem_onePole_lags unitImpulse_isCausal (geometricSeq_isCausal a)
    (isRecurrenceSolution_geometricSeq a)).symm

/-!

## B. The transfer relation with no solution hypothesis

-/

/-- The transfer relation for the one-pole recurrence, stated for the constructed solution rather
than for a solution supplied as a hypothesis. -/
lemma transform_recurrenceSolution_onePole {a z : ℂ} (ha : a ≠ 0) (hz : ‖a‖ < ‖z‖)
    (hden : 1 - delaySymbol {1} (onePoleFeedback a) z⁻¹ ≠ 0) :
    transform (recurrenceSolution {1} {0} (onePoleFeedback a) onePoleFeedforward unitImpulse) z
      = transferFunction {1} {0} (onePoleFeedback a) onePoleFeedforward z *
        transform unitImpulse z := by
  have hmem : z ∈ ROC (geometricSeq a) := by
    rw [ROC_geometricSeq ha]
    exact hz
  refine transform_recurrenceSolution zero_notMem_onePole_lags unitImpulse_isCausal
    (summable_seriesTerm_unitImpulse z) ?_ hden
  rw [recurrenceSolution_onePole]
  exact hmem.2

/-- The value of that relation in closed form: the constructed solution has the one-pole
transform. -/
lemma transform_recurrenceSolution_onePole_eq
    {a z : ℂ} (ha : a ≠ 0) (hz : ‖a‖ < ‖z‖) :
    transform (recurrenceSolution {1} {0} (onePoleFeedback a) onePoleFeedforward unitImpulse) z
      = (1 - a * z⁻¹)⁻¹ := by
  rw [recurrenceSolution_onePole, transform_geometricSeq ha hz]

end

end Physlib.ZTransform
