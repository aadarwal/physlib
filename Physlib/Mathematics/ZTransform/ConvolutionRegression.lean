/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Mathematics.ZTransform.BasicRegression
public import Physlib.Mathematics.ZTransform.Convolution

/-!
# Regression tests for the convolution theorem

## i. Overview

The convolution theorem is instantiated at the causal geometric sequence convolved with itself,
where both sides can be written in closed form: the transform of the convolution is the square of
the one-pole rational function. This is a direct specialization of the generic theorem and the
geometric closed form, so it is a smoke test of their composition rather than an independent
calculation of the left-hand side.

The remaining examples exercise identification rather than prediction. The impulse response of
the geometric sequence is the sequence itself at every nonnegative index, so its value at index
one is the ratio. Reading a parameter back off a measured response is the direction that matters
when a model is to be fitted rather than simulated, and it is available here because the causal
convolution is determined by, and determines, the nonnegative-index samples.

## ii. Key results

- `Physlib.ZTransform.transform_convolution_geometricSeq`: the convolution theorem at the
  geometric sequence, both sides in closed form.
- `Physlib.ZTransform.convolution_geometricSeq_unitImpulse`: the impulse response of the
  geometric sequence.
- `Physlib.ZTransform.convolution_geometricSeq_unitImpulse_one`: its value at index one is the
  ratio, so the parameter is read off the response.
- `Physlib.ZTransform.convolution_not_commutative_regression`: a negative-index sentinel proves
  that the one-sided convolution is not commutative and pins which factor supplies the lag.

## iii. Table of contents

- A. The convolution theorem in closed form
- B. Reading a parameter off the impulse response
- C. One-sided orientation and noncommutativity

## iv. References

The convolution theorem exercised here is `Physlib.ZTransform.transform_convolution`, which rests
on Mathlib's Cauchy product. The closed forms for the geometric sequence come from
`Physlib.Mathematics.ZTransform.Convergence`. No fetched source in the Concordia HVG corpus
contains a z-transform convolution theorem, so these are not parity regressions.

These are algebraic regressions on complex sequences. No physical, optical, or signal-processing
interpretation is asserted, and nothing here is a claim about a measurement procedure.

-/

@[expose] public section

namespace Physlib.ZTransform

noncomputable section

/-!

## A. The convolution theorem in closed form

-/

/-- The convolution of the causal geometric sequence with itself has transform the square of the
one-pole rational function. This directly specializes the generic convolution theorem and the
geometric transform formula. -/
lemma transform_convolution_geometricSeq {a z : ℂ} (ha : a ≠ 0) (hz : ‖a‖ < ‖z‖) :
    transform (convolution (geometricSeq a) (geometricSeq a)) z = ((1 - a * z⁻¹)⁻¹) ^ 2 := by
  have hmem : z ∈ ROC (geometricSeq a) := by
    rw [ROC_geometricSeq ha]
    exact hz
  rw [transform_convolution (geometricSeq_isCausal a) hmem.2 hmem.2,
    transform_geometricSeq ha hz, sq]

/-!

## B. Reading a parameter off the impulse response

-/

/-- The impulse response of the causal geometric sequence is the sequence itself at every
nonnegative index. -/
lemma convolution_geometricSeq_unitImpulse (a : ℂ) (m : ℕ) :
    convolution (geometricSeq a) unitImpulse (m : ℤ) = a ^ m := by
  rw [convolution_unitImpulse_right, geometricSeq_natCast]

/-- The impulse response at index one is the ratio, so the parameter of a one-pole system is
recovered from its response to a known input. -/
lemma convolution_geometricSeq_unitImpulse_one (a : ℂ) :
    convolution (geometricSeq a) unitImpulse ((1 : ℕ) : ℤ) = a := by
  rw [convolution_geometricSeq_unitImpulse, pow_one]

/-- Two causal geometric sequences with the same impulse response have the same ratio. -/
lemma eq_of_convolution_geometricSeq_eq {a b : ℂ}
    (heq : convolution (geometricSeq a) unitImpulse
      = convolution (geometricSeq b) unitImpulse) : a = b := by
  have h := congrFun heq ((1 : ℕ) : ℤ)
  rwa [convolution_geometricSeq_unitImpulse_one, convolution_geometricSeq_unitImpulse_one] at h

/-!

## C. One-sided orientation and noncommutativity

-/

/-- A negative-index sample in the left factor is never read by the one-sided convolution. -/
lemma convolution_regressionAtNegOne_delayImpulse_zero :
    convolution regressionAtNegOne (delay 1 unitImpulse) 0 = 0 := by
  rw [convolution]
  have hterm : ∀ k : ℕ,
      regressionAtNegOne k * delay 1 unitImpulse (0 - k) = 0 := by
    intro k
    have hk : (k : ℤ) ≠ -1 := by omega
    rw [regressionAtNegOne, if_neg hk, zero_mul]
  simp only [hterm, tsum_zero]

/-- Reversing the factors reads that negative-index sample at lag one. -/
lemma convolution_delayImpulse_regressionAtNegOne_zero :
    convolution (delay 1 unitImpulse) regressionAtNegOne 0 = 1 := by
  rw [convolution, tsum_eq_single 1]
  · simp [delay, unitImpulse, regressionAtNegOne]
  · intro k hk
    have hne : (k : ℤ) - ((1 : ℕ) : ℤ) ≠ 0 := by omega
    have hdelay : delay 1 unitImpulse (k : ℤ) = 0 := by
      rw [delay, unitImpulse, if_neg hne]
    rw [hdelay, zero_mul]

/-- The causal convolution is not commutative on two-sided sequences. This sentinel also pins
that the nonnegative lag indexes the left factor. -/
lemma convolution_not_commutative_regression :
    convolution regressionAtNegOne (delay 1 unitImpulse) ≠
      convolution (delay 1 unitImpulse) regressionAtNegOne := by
  intro h
  have hzero := congrFun h 0
  rw [convolution_regressionAtNegOne_delayImpulse_zero,
    convolution_delayImpulse_regressionAtNegOne_zero] at hzero
  exact zero_ne_one hzero

end

end Physlib.ZTransform
