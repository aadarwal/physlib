/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Mathematics.ZTransform.Convolution

/-!
# Regression tests for the convolution theorem

## i. Overview

The convolution theorem is instantiated at the causal geometric sequence convolved with itself,
where both sides can be written in closed form: the transform of the convolution is the square of
the one-pole rational function. That is a genuine check, because the left-hand side is computed
through the Cauchy product of two series and the right-hand side through a single geometric sum,
so the two routes are independent.

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

## iii. Table of contents

- A. The convolution theorem in closed form
- B. Reading a parameter off the impulse response

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
one-pole rational function. The left side is a Cauchy product of two series and the right side a
single geometric sum, so the two routes to the value are independent. -/
theorem transform_convolution_geometricSeq {a z : ℂ} (ha : a ≠ 0) (hz : ‖a‖ < ‖z‖) :
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
theorem convolution_geometricSeq_unitImpulse (a : ℂ) (m : ℕ) :
    convolution (geometricSeq a) unitImpulse (m : ℤ) = a ^ m := by
  rw [convolution_unitImpulse_right, geometricSeq_natCast]

/-- The impulse response at index one is the ratio, so the parameter of a one-pole system is
recovered from its response to a known input. -/
theorem convolution_geometricSeq_unitImpulse_one (a : ℂ) :
    convolution (geometricSeq a) unitImpulse ((1 : ℕ) : ℤ) = a := by
  rw [convolution_geometricSeq_unitImpulse, pow_one]

/-- Two causal geometric sequences with the same impulse response have the same ratio. -/
theorem eq_of_convolution_geometricSeq_eq {a b : ℂ}
    (heq : convolution (geometricSeq a) unitImpulse
      = convolution (geometricSeq b) unitImpulse) : a = b := by
  have h := congrFun heq ((1 : ℕ) : ℤ)
  rwa [convolution_geometricSeq_unitImpulse_one, convolution_geometricSeq_unitImpulse_one] at h

end

end Physlib.ZTransform
