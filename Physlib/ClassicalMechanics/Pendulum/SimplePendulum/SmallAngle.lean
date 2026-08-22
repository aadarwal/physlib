/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.ClassicalMechanics.HarmonicOscillator.Basic
public import Physlib.ClassicalMechanics.Pendulum.SimplePendulum.Basic
/-!

# Small-angle motion of the simple gravity pendulum

## i. Overview

Near the bottom of its swing the torque of the simple gravity pendulum is
`-m g ℓ sin θ ≈ -m g ℓ θ`, so for small angles the equation of motion `I θ̈ = -m g ℓ sin θ`
linearizes to `I θ̈ = -m g ℓ θ`: the equation of a harmonic oscillator whose mass is the moment
of inertia `I = m ℓ²` of the pendulum and whose spring constant is the coefficient `m g ℓ` of
the linearized torque. The angular frequency `√(k/m)` of this oscillator is `√(g/ℓ)`, which is
exactly the constant `ω` of `SimplePendulum.Basic`, there described as the frequency of the
small oscillations.

This module packages the oscillator of the small oscillations as
`SimplePendulum.toHarmonicOscillator`, defines the linearized equation of motion
`θ̈ + ω² θ = 0` on the same Euclidean lift of the angle as the nonlinear equation, and proves
that for smooth lifts of the angle it is the equation of motion of the associated harmonic
oscillator, so that the solution theory of the harmonic oscillator applies verbatim to the
small oscillations of the pendulum.

## ii. Key results

- `SimplePendulum.toHarmonicOscillator` is the harmonic oscillator to which the pendulum
  linearizes, of mass `I = m ℓ²` and spring constant `m g ℓ`. The simp lemmas
  `toHarmonicOscillator_m` and `toHarmonicOscillator_k` record its data, and
  `toHarmonicOscillator_ω` identifies its angular frequency with the constant
  `SimplePendulum.ω` of the pendulum.
- `SimplePendulum.LinearizedEquationOfMotion` is the small-angle equation of motion
  `θ̈ + ω² θ = 0`. Its rotational Newton form is `linearizedEquationOfMotion_iff_newton`, and
  `linearizedEquationOfMotion_iff` identifies it, for smooth lifts of the angle, with the
  equation of motion of the associated harmonic oscillator.

## iii. Table of contents

- A. The harmonic oscillator of small oscillations
  - A.1. The associated harmonic oscillator
  - A.2. The frequency of the associated oscillator
- B. The linearized equation of motion
  - B.1. The linearized equation
  - B.2. Equivalence with the equation of motion of the oscillator

## iv. References

References for the small-angle motion of the simple pendulum include:
- Landau & Lifshitz, Mechanics, 3rd ed., §21.
- The module `Physlib.ClassicalMechanics.Pendulum.SimplePendulum.Basic`, whose equation of
  motion this module linearizes.

-/

@[expose] public section

namespace ClassicalMechanics

open Time
open scoped ContDiff

namespace SimplePendulum

variable (S : SimplePendulum)

/-!

## A. The harmonic oscillator of small oscillations

Replacing `sin θ` by `θ` in the equation of motion `I θ̈ = -m g ℓ sin θ` produces the equation
of a harmonic oscillator: the moment of inertia plays the role of the mass, and the coefficient
`m g ℓ` of the linearized torque plays the role of the spring constant. We record this
oscillator once and for all; its solution theory is the solution theory of the small
oscillations of the pendulum.

-/

/-!

### A.1. The associated harmonic oscillator

The data of the associated oscillator: the mass `I = m ℓ²` and the spring constant `m g ℓ`,
both positive because the data of the pendulum is.

-/

/-- The harmonic oscillator to which the pendulum linearizes: mass `I = m ℓ²`, spring
  constant `m g ℓ`. -/
noncomputable def toHarmonicOscillator : HarmonicOscillator where
  m := S.inertia
  k := S.m * S.g * S.ℓ
  m_pos := S.inertia_pos
  k_pos := by have := S.m_pos; have := S.g_pos; have := S.ℓ_pos; positivity

/-- The mass of the harmonic oscillator associated to the simple pendulum is the moment of
  inertia `I = m ℓ²` of the pendulum about its pivot. -/
@[simp]
lemma toHarmonicOscillator_m : S.toHarmonicOscillator.m = S.inertia := rfl

/-- The spring constant of the harmonic oscillator associated to the simple pendulum is
  `m g ℓ`, the coefficient of the linearized torque. -/
@[simp]
lemma toHarmonicOscillator_k : S.toHarmonicOscillator.k = S.m * S.g * S.ℓ := rfl

/-!

### A.2. The frequency of the associated oscillator

The angular frequency `√(k/m) = √(m g ℓ / m ℓ²)` of the associated oscillator collapses, the
mass cancelling, to `√(g/ℓ)`: the constant `ω` of the pendulum, as promised by its description
in `SimplePendulum.Basic` as the frequency of the small oscillations.

-/

/-- The angular frequency of the harmonic oscillator associated to the simple pendulum is the
  angular frequency `ω = √(g/ℓ)` of the small oscillations of the pendulum. -/
lemma toHarmonicOscillator_ω : S.toHarmonicOscillator.ω = S.ω := by
  unfold HarmonicOscillator.ω SimplePendulum.ω
  rw [toHarmonicOscillator_k, toHarmonicOscillator_m, inertia]
  congr 1
  field_simp

/-!

## B. The linearized equation of motion

The linearized equation of motion is the equation `θ̈ + ω² θ = 0` obtained from the scalar form
`θ̈ + ω² sin θ = 0` of the equation of motion by replacing `sin θ` with `θ`. It is stated, like
the nonlinear equation, on the Euclidean lift of the angle, and it is exactly the associated
harmonic oscillator's form of Newton's second law: multiplying by the moment of inertia converts
one pointwise equation into the other.

-/

/-!

### B.1. The linearized equation

The equation `θ̈ + ω² θ = 0`, together with its rotational Newton form `I θ̈ = -m g ℓ θ`, in
which the right-hand side is the force of the associated harmonic oscillator.

-/

/-- The linearized equation of motion `θ̈ + ω² θ = 0` of the simple pendulum, the small-angle
  form of the equation of motion, in which the torque is replaced by its linearization at the
  bottom of the swing. -/
def LinearizedEquationOfMotion (θ : Time → EuclideanSpace ℝ (Fin 1)) : Prop :=
  ∀ t, ∂ₜ (∂ₜ θ) t + (S.ω ^ 2) • θ t = 0

/-- The linearized equation of motion in the rotational form of Newton's second law: at every
  instant the rate of change `I θ̈` of the angular momentum equals the force `-m g ℓ θ` of the
  associated harmonic oscillator. No smoothness is required: the two pointwise equations differ
  by the nonzero factor `I`. -/
lemma linearizedEquationOfMotion_iff_newton (θ : Time → EuclideanSpace ℝ (Fin 1)) :
    S.LinearizedEquationOfMotion θ ↔
      ∀ t, S.toHarmonicOscillator.m • ∂ₜ (∂ₜ θ) t =
        HarmonicOscillator.force S.toHarmonicOscillator (θ t) := by
  simp only [LinearizedEquationOfMotion]
  refine forall_congr' fun t => ?_
  rw [HarmonicOscillator.force_eq_linear, toHarmonicOscillator_m, toHarmonicOscillator_k,
    neg_smul, eq_neg_iff_add_eq_zero, ← S.ω_sq_mul_inertia, mul_comm (S.ω ^ 2) S.inertia,
    ← smul_smul, ← smul_add, smul_eq_zero, or_iff_right S.inertia_ne_zero]

/-!

### B.2. Equivalence with the equation of motion of the oscillator

For a smooth lift of the angle, the linearized equation of motion is the equation of motion of
the associated harmonic oscillator, through the latter's own form of Newton's second law. The
solution theory of the harmonic oscillator thereby becomes available to the small oscillations
of the pendulum.

-/

/-- For a smooth lift of the angle, the linearized equation of motion of the simple pendulum is
  the equation of motion of the associated harmonic oscillator. The oscillator's equation of
  motion is the vanishing of the variational gradient of its action, which is totalized;
  smoothness is the regularity under which that variational description agrees with the pointwise
  one. The smoothness-free pointwise content is `linearizedEquationOfMotion_iff_newton`. -/
lemma linearizedEquationOfMotion_iff (θ : Time → EuclideanSpace ℝ (Fin 1))
    (hθ : ContDiff ℝ ∞ θ) :
    S.LinearizedEquationOfMotion θ ↔ S.toHarmonicOscillator.EquationOfMotion θ := by
  rw [S.toHarmonicOscillator.equationOfMotion_iff_newtons_2nd_law θ hθ]
  exact S.linearizedEquationOfMotion_iff_newton θ

end SimplePendulum

end ClassicalMechanics
