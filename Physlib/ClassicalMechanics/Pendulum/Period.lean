/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.ClassicalMechanics.Pendulum.SmallAngle
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
/-!

# Exact period of the simple gravity pendulum

## i. Overview

The oscillation period of a simple pendulum released from rest at amplitude `θ₀`
is not elementary. It is given by a complete elliptic integral of the first kind,

`K(m) = ∫₀^{π/2} (1 − m sin² φ)^{-1/2} dφ`,

via `T = 4 √(ℓ/g) K(sin²(θ₀/2))`. Mathlib does not currently name Legendre’s `K`
(it has the Weierstrass `℘`-function instead). This file defines `K` as that
integral, defines the corresponding exact period, and proves the small-amplitude
evaluation `K(0) = π/2`, which recovers Huygens’s period.

The identification of `exactPeriod θ₀` with the actual return time of a solution
of the nonlinear ODE is left as a TODO: it is a quadrature of the energy first
integral, not a missing definition.

## ii. Key results

- `completeEllipticK` : complete elliptic integral of the first kind as an integral
- `completeEllipticK_zero` : `K(0) = π/2`
- `exactPeriod` : `4 √(ℓ/g) K(sin²(θ₀/2))`
- `exactPeriod_zero` : at vanishing amplitude this is Huygens’s period

## iii. Table of contents

- A. The complete elliptic integral `K`
- B. The exact period
- C. Recovery of the small-angle period

## iv. References

- Landau & Lifshitz, Mechanics, 3rd ed., §11 (the period as an elliptic integral).

-/

@[expose]
public section

open Real MeasureTheory intervalIntegral

namespace ClassicalMechanics
namespace SimplePendulum

TODO "Prove that a solution of the nonlinear pendulum ODE released from rest at
    amplitude `θ₀ ∈ (0, π)` is periodic with period `exactPeriod S θ₀`."

/-!
## A. The complete elliptic integral `K`

-/

/-- The complete elliptic integral of the first kind,
  `K(m) = ∫₀^{π/2} (1 − m sin² φ)^{-1/2} dφ`.
  For the pendulum one takes `m = sin²(θ₀/2)`. -/
noncomputable def completeEllipticK (m : ℝ) : ℝ :=
  ∫ φ in (0 : ℝ)..π / 2, (1 - m * sin φ ^ 2) ^ (-(1 / 2 : ℝ))

lemma completeEllipticK_zero : completeEllipticK 0 = π / 2 := by
  unfold completeEllipticK
  have h : (fun φ : ℝ => (1 - (0 : ℝ) * sin φ ^ 2) ^ (-(1 / 2 : ℝ))) = fun _ => 1 := by
    funext φ
    simp
  rw [h, intervalIntegral.integral_const]
  simp

/-!
## B. The exact period

-/

variable (S : SimplePendulum)

/-- The exact period of a simple pendulum released from rest at amplitude `θ₀`,
  `T = 4 √(ℓ/g) K(sin²(θ₀/2))`. -/
noncomputable def exactPeriod (θ0 : ℝ) : ℝ :=
  4 * √(S.ℓ / S.g) * completeEllipticK (sin (θ0 / 2) ^ 2)

/-!
## C. Recovery of the small-angle period

-/

lemma exactPeriod_zero : S.exactPeriod 0 = S.smallAnglePeriod := by
  unfold exactPeriod smallAnglePeriod
  simp [completeEllipticK_zero]
  ring

end SimplePendulum
end ClassicalMechanics
