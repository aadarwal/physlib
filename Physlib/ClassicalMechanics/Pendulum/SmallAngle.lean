/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.ClassicalMechanics.Pendulum.SimplePendulum
public import Mathlib.Analysis.Asymptotics.Lemmas
/-!

# Small-angle motion of the simple gravity pendulum

## i. Overview

For small angular displacements the restoring torque is linear in the angle, and the
nonlinear equation reduces to the harmonic oscillator `θ̈ + ω² θ = 0` with
`ω = √(g/ℓ)`. This file records that specialisation on Physlib `Time` and the
angular chart `EuclideanSpace ℝ (Fin 1)`.

## ii. Key results

- `LinearizedEquationOfMotion`
- `smallAnglePeriod` (Huygens)
- `releasedFromRest` and its periodicity
- `sin_sub_id_isLittleO`

## iii. Table of contents

- A. The linearized equation
- B. Huygens’s period
- C. Release from rest
- D. The small-angle expansion of `sin`

## iv. References

- Huygens, *Horologium oscillatorium* (1673).
- Landau & Lifshitz, Mechanics, 3rd ed., §21.

-/

@[expose]
public section

open Real InnerProductSpace Time

namespace ClassicalMechanics
namespace SimplePendulum

variable (S : SimplePendulum)

/-!
## A. The linearized equation
-/

/-- Linearized ODE `θ̈ + ω² θ = 0` in the angular chart. -/
def LinearizedEquationOfMotion (θ : Trajectory) : Prop :=
  ∀ t, ∂ₜ (∂ₜ θ) t + (S.omega ^ 2) • θ t = 0

/-!
## B. Huygens’s period
-/

/-- Huygens’s period `T₀ = 2π √(ℓ/g)`, independent of amplitude. -/
noncomputable def smallAnglePeriod : ℝ := 2 * π * √(S.ℓ / S.g)

lemma smallAnglePeriod_eq : S.smallAnglePeriod = 2 * π / S.omega := by
  unfold smallAnglePeriod omega
  rw [sqrt_div S.ℓ_pos.le, sqrt_div S.g_pos.le]
  field_simp [(sqrt_pos.mpr S.g_pos).ne', (sqrt_pos.mpr S.ℓ_pos).ne']

/-!
## C. Release from rest
-/

/-- Released from rest at angle `θ₀`, in the small-angle approximation. -/
noncomputable def releasedFromRest (θ0 : ℝ) : Trajectory := fun t =>
  EuclideanSpace.single 0 (θ0 * cos (S.omega * t.val))

lemma releasedFromRest_init (θ0 : ℝ) : S.releasedFromRest θ0 0 = EuclideanSpace.single 0 θ0 := by
  simp [releasedFromRest]

lemma releasedFromRest_periodic (θ0 : ℝ) (t : Time) :
    S.releasedFromRest θ0 (t + (S.smallAnglePeriod : Time)) = S.releasedFromRest θ0 t := by
  unfold releasedFromRest
  have hωT : S.omega * S.smallAnglePeriod = 2 * π := by
    rw [S.smallAnglePeriod_eq]
    field_simp [S.omega_ne_zero]
  have : S.omega * (t.val + S.smallAnglePeriod) = S.omega * t.val + 2 * π := by
    rw [mul_add, hωT]
  simp [Time.add_val, this, cos_add_two_pi]

/-!
## D. The small-angle expansion of `sin`
-/

/-- `sin θ = θ + o(θ)` as `θ → 0`. -/
lemma sin_sub_id_isLittleO :
    (fun θ : ℝ => sin θ - θ) =o[nhds (0 : ℝ)] fun θ => θ := by
  simpa [sin_zero, smul_eq_mul] using (hasDerivAt_sin (0 : ℝ)).isLittleO

end SimplePendulum
end ClassicalMechanics
