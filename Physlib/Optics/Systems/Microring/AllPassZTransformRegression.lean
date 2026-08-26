/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Systems.Microring.AllPassZTransform

/-!
# Regression tests for the all-pass causal Z-transform semantics

## i. Overview

This file checks the causal recurrence independently of its quotient transfer. The through
coefficient `3 / 5` and one-pass coefficient `1 / 2` give

```text
y[0] = 3/5,    y[1] = -8/25,
H(1) = 1/7,    H(I) = 75/109 + (32/109) I.
```

The nonreal sample pins the reciprocal-variable convention: at `z = I`, its inverse is `-I`.
The separate bridge regression compares these values with the optical ring semantics.

These are algebraic, discrete-time regression fixtures. The sample calculations do not by
themselves establish a region of convergence, material delay law, continuous-time realization,
or electromagnetic power normalization.

## ii. Key results

- `allPassZRegression_output_zero`: the undelayed impulse response sample.
- `allPassZRegression_output_one`: the first feedback sample and feedforward sign.
- `allPassZRegression_output_two`: the next feedback-only sample and lag-set sentinel.
- `allPassZRegression_transfer_one`: direct reciprocal-variable evaluation at resonance.
- `allPassZRegression_transfer_I`: the nonreal reciprocal-variable convention sentinel.

## iii. Table of contents

- A. Causal recurrence samples
- B. Reciprocal-variable transfer values

## iv. References

These adversarial fixtures are Physlib-original. Source comparisons for the neutral Z-transform
API live in its production modules; this file makes no additional source-parity claim.
-/

@[expose] public section

namespace Optics

noncomputable section

namespace AllPass

open Physlib.ZTransform

/-! ## A. Causal recurrence samples -/

/-- The causal impulse response of the exact resonant `3-4-5` fixture. -/
def allPassZRegressionOutput : ℤ → ℂ :=
  causalOutput (3 / 5) (1 / 2) unitImpulse

/-- The independently stated recurrence starts with the direct through coefficient `3 / 5`. -/
lemma allPassZRegression_output_zero : allPassZRegressionOutput 0 = 3 / 5 := by
  have hRecurrence := causalOutput_isRecurrenceSolution
    (3 / 5) (1 / 2) unitImpulse_isCausal
  have hAtZero := hRecurrence.apply 0
  have hOutputNegative : causalOutput (3 / 5) (1 / 2) unitImpulse (-1) = 0 :=
    causalOutput_isCausal (3 / 5) (1 / 2) unitImpulse (-1) (by norm_num)
  norm_num [zFeedbackLags, zFeedforwardLags, zFeedbackCoefficients,
    zFeedforwardCoefficients, unitImpulse] at hAtZero
  rw [hOutputNegative] at hAtZero
  simpa [allPassZRegressionOutput] using hAtZero

/-- The first delayed sample is `-8 / 25`, pinning both feedback and feedforward signs. -/
lemma allPassZRegression_output_one : allPassZRegressionOutput 1 = -8 / 25 := by
  have hRecurrence := causalOutput_isRecurrenceSolution
    (3 / 5) (1 / 2) unitImpulse_isCausal
  have hAtOne := hRecurrence.apply 1
  have hZero : causalOutput (3 / 5) (1 / 2) unitImpulse 0 = 3 / 5 := by
    simpa [allPassZRegressionOutput] using allPassZRegression_output_zero
  norm_num [zFeedbackLags, zFeedforwardLags, zFeedbackCoefficients,
    zFeedforwardCoefficients, unitImpulse] at hAtOne
  rw [hZero] at hAtOne
  norm_num [allPassZRegressionOutput, zFeedbackLags, zFeedforwardLags,
    zFeedbackCoefficients, zFeedforwardCoefficients, unitImpulse] at hAtOne ⊢
  exact hAtOne

/-- Reversing the delayed feedforward sign would give the wrong first sample. -/
lemma allPassZRegression_output_one_ne_positive : allPassZRegressionOutput 1 ≠ 8 / 25 := by
  rw [allPassZRegression_output_one]
  norm_num

/-- The next sample is feedback-only, pinning the single positive feedback lag. -/
lemma allPassZRegression_output_two : allPassZRegressionOutput 2 = -12 / 125 := by
  have hRecurrence := causalOutput_isRecurrenceSolution
    (3 / 5) (1 / 2) unitImpulse_isCausal
  have hAtTwo := hRecurrence.apply 2
  have hOne : causalOutput (3 / 5) (1 / 2) unitImpulse 1 = -8 / 25 := by
    simpa [allPassZRegressionOutput] using allPassZRegression_output_one
  norm_num [zFeedbackLags, zFeedforwardLags, zFeedbackCoefficients,
    zFeedforwardCoefficients, unitImpulse] at hAtTwo
  rw [hOne] at hAtTwo
  norm_num [allPassZRegressionOutput, zFeedbackLags, zFeedforwardLags,
    zFeedbackCoefficients, zFeedforwardCoefficients, unitImpulse] at hAtTwo ⊢
  exact hAtTwo

/-! ## B. Reciprocal-variable transfer values -/

/-- Direct expansion of the coefficient symbols gives the resonant transfer `1 / 7`. -/
lemma allPassZRegression_transfer_one : zTransfer (3 / 5) (1 / 2) 1 = 1 / 7 := by
  norm_num [zTransfer, Physlib.ZTransform.transferFunction,
    zFeedbackLags, zFeedforwardLags, zFeedbackCoefficients,
    zFeedforwardCoefficients, Physlib.ZTransform.delaySymbol]

/-- At `z = I`, direct expansion uses `z⁻¹ = -I` and gives the pinned nonreal value. -/
lemma allPassZRegression_transfer_I :
    zTransfer (3 / 5) (1 / 2) Complex.I = 75 / 109 + 32 / 109 * Complex.I := by
  rw [zTransfer, Physlib.ZTransform.transferFunction,
    delaySymbol_zFeedbackCoefficients, delaySymbol_zFeedforwardCoefficients,
    Complex.inv_I]
  have hInverse : (1 + (3 / 10 : ℂ) * Complex.I)⁻¹ =
      (100 - 30 * Complex.I) / 109 := by
    apply inv_eq_of_mul_eq_one_right
    field_simp
    ring_nf
    norm_num [Complex.I_sq]
  rw [show 1 - (3 / 5 : ℂ) * (1 / 2) * -Complex.I =
    1 + 3 / 10 * Complex.I by ring]
  conv_lhs =>
    rw [div_eq_mul_inv, hInverse]
  ring_nf
  norm_num [Complex.I_sq]
  ring

/-- The nonreal value rejects the opposite reciprocal-variable sign. -/
lemma allPassZRegression_transfer_I_ne_conjugate :
    zTransfer (3 / 5) (1 / 2) Complex.I ≠ 75 / 109 - 32 / 109 * Complex.I := by
  rw [allPassZRegression_transfer_I]
  intro h
  have hIm := congrArg Complex.im h
  norm_num at hIm

end AllPass

end

end Optics
