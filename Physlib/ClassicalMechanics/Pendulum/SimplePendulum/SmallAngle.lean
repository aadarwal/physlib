/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.ClassicalMechanics.HarmonicOscillator.Solution
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
- `SimplePendulum.smallAngleTrajectory` is the small-angle motion determined by a choice of
  initial conditions, the trajectory of the associated harmonic oscillator: it is smooth
  (`smallAngleTrajectory_contDiff`), it assumes its initial data at time `0`
  (`smallAngleTrajectory_at_zero`, `smallAngleTrajectory_velocity_at_zero`), and it satisfies
  the linearized equation of motion (`smallAngleTrajectory_linearizedEquationOfMotion`).
- `SimplePendulum.linearized_unique`: a smooth solution of the linearized equation of motion
  with the initial data of `IC` is `smallAngleTrajectory IC`. Together with the previous point,
  this is the existence and uniqueness of the small-angle motions.
- `SimplePendulum.releasedFromRest` is the motion released from rest at angle `θ₀`, the cosine
  `θ₀ cos (ω t)`; `releasedFromRest_eq` identifies it with the small-angle trajectory of the
  initial conditions with initial angle `θ₀` and zero initial angular velocity.

## iii. Table of contents

- A. The harmonic oscillator of small oscillations
  - A.1. The associated harmonic oscillator
  - A.2. The frequency of the associated oscillator
- B. The linearized equation of motion
  - B.1. The linearized equation
  - B.2. Equivalence with the equation of motion of the oscillator
- C. Small-angle trajectories
  - C.1. The trajectory of given initial conditions
  - C.2. Existence and uniqueness
  - C.3. Release from rest

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

/-!

## C. Small-angle trajectories

For small angles the pendulum is its associated harmonic oscillator, and the solution theory
of the oscillator transfers verbatim: every choice of initial angle and initial angular
velocity determines a smooth motion, unique among the smooth solutions of the linearized
equation of motion. This section performs the transfer, and specializes it to the classical
motion released from rest at a given angle.

-/

/-!

### C.1. The trajectory of given initial conditions

The small-angle motion determined by an initial angle `IC.x₀` and an initial angular velocity
`IC.v₀` is the trajectory of the associated harmonic oscillator for the same initial
conditions. It is smooth in time and assumes the prescribed initial data at time `0`.

-/

/-- The small-angle motion of the simple pendulum with initial angle `IC.x₀` and initial
  angular velocity `IC.v₀`: the trajectory of the associated harmonic oscillator with the same
  initial conditions. -/
noncomputable def smallAngleTrajectory (IC : HarmonicOscillator.InitialConditions) :
    Time → EuclideanSpace ℝ (Fin 1) :=
  IC.trajectory S.toHarmonicOscillator

/-- The small-angle trajectories of the simple pendulum are smooth in time. -/
lemma smallAngleTrajectory_contDiff (IC : HarmonicOscillator.InitialConditions)
    {n : WithTop ℕ∞} : ContDiff ℝ n (S.smallAngleTrajectory IC) :=
  HarmonicOscillator.InitialConditions.trajectory_contDiff S.toHarmonicOscillator IC

/-- At time `0` the small-angle trajectory passes through its initial angle. -/
lemma smallAngleTrajectory_at_zero (IC : HarmonicOscillator.InitialConditions) :
    S.smallAngleTrajectory IC 0 = IC.x₀ := by
  simp [smallAngleTrajectory]

/-- At time `0` the small-angle trajectory moves with its initial angular velocity. -/
lemma smallAngleTrajectory_velocity_at_zero (IC : HarmonicOscillator.InitialConditions) :
    ∂ₜ (S.smallAngleTrajectory IC) 0 = IC.v₀ := by
  simp [smallAngleTrajectory]

/-!

### C.2. Existence and uniqueness

The small-angle trajectories solve the linearized equation of motion, and they are the only
smooth solutions: a smooth solution with the initial data of `IC` is the small-angle
trajectory of `IC`. Both statements are the corresponding statements for the associated
harmonic oscillator, read through the equivalence `linearizedEquationOfMotion_iff` of the two
equations of motion.

-/

/-- The small-angle trajectories satisfy the linearized equation of motion: for every choice
  of initial conditions the linearized equation has a smooth solution assuming them. -/
lemma smallAngleTrajectory_linearizedEquationOfMotion
    (IC : HarmonicOscillator.InitialConditions) :
    S.LinearizedEquationOfMotion (S.smallAngleTrajectory IC) :=
  (S.linearizedEquationOfMotion_iff _ (S.smallAngleTrajectory_contDiff IC)).mpr
    (HarmonicOscillator.InitialConditions.trajectory_equationOfMotion S.toHarmonicOscillator IC)

/-- Uniqueness of the small-angle motions: a smooth solution of the linearized equation of
  motion is determined by its initial angle and initial angular velocity, being the
  small-angle trajectory of those initial conditions. This is the uniqueness theorem for the
  associated harmonic oscillator, transferred through `linearizedEquationOfMotion_iff`. -/
lemma linearized_unique (IC : HarmonicOscillator.InitialConditions)
    (θ : Time → EuclideanSpace ℝ (Fin 1)) (hθ : ContDiff ℝ ∞ θ)
    (h : S.LinearizedEquationOfMotion θ) (h0 : θ 0 = IC.x₀) (hv : ∂ₜ θ 0 = IC.v₀) :
    θ = S.smallAngleTrajectory IC :=
  HarmonicOscillator.InitialConditions.trajectories_unique S.toHarmonicOscillator IC θ hθ
    ⟨(S.linearizedEquationOfMotion_iff θ hθ).mp h, h0, hv⟩

/-!

### C.3. Release from rest

The classical small-angle experiment: the pendulum is displaced to an angle `θ₀` and released
from rest. Its motion is the cosine `θ₀ cos (ω t)`, the small-angle trajectory of the initial
conditions with initial angle `θ₀` and zero initial angular velocity; it starts at the angle
`θ₀` with vanishing angular velocity, and satisfies the linearized equation of motion.

-/

/-- The small-angle motion of the pendulum released from rest at initial angle `θ₀`: the
  cosine `θ₀ cos (ω t)` of angular frequency `ω`. -/
noncomputable def releasedFromRest (θ₀ : ℝ) : Time → EuclideanSpace ℝ (Fin 1) :=
  fun t => Real.cos (S.ω * t.val) • EuclideanSpace.single (0 : Fin 1) θ₀

/-- The motion released from rest at angle `θ₀` is the small-angle trajectory of the initial
  conditions with initial angle `θ₀` and zero initial angular velocity. -/
lemma releasedFromRest_eq (θ₀ : ℝ) :
    S.releasedFromRest θ₀ = S.smallAngleTrajectory ⟨EuclideanSpace.single 0 θ₀, 0⟩ := by
  funext t
  ext i
  simp [releasedFromRest, smallAngleTrajectory,
    HarmonicOscillator.InitialConditions.trajectory, toHarmonicOscillator_ω]

/-- At time `0` the motion released from rest at angle `θ₀` is at the angle `θ₀`. -/
lemma releasedFromRest_at_zero (θ₀ : ℝ) :
    S.releasedFromRest θ₀ 0 = EuclideanSpace.single 0 θ₀ := by
  simp [releasedFromRest]

/-- The motion released from rest at angle `θ₀` is genuinely released from rest: its angular
  velocity at time `0` vanishes. -/
lemma releasedFromRest_velocity_at_zero (θ₀ : ℝ) : ∂ₜ (S.releasedFromRest θ₀) 0 = 0 := by
  rw [S.releasedFromRest_eq θ₀]
  exact S.smallAngleTrajectory_velocity_at_zero ⟨EuclideanSpace.single 0 θ₀, 0⟩

/-- The motion released from rest at angle `θ₀` satisfies the linearized equation of
  motion. -/
lemma releasedFromRest_linearizedEquationOfMotion (θ₀ : ℝ) :
    S.LinearizedEquationOfMotion (S.releasedFromRest θ₀) := by
  rw [S.releasedFromRest_eq θ₀]
  exact S.smallAngleTrajectory_linearizedEquationOfMotion ⟨EuclideanSpace.single 0 θ₀, 0⟩

end SimplePendulum

end ClassicalMechanics
