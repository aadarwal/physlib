/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.ClassicalMechanics.EulerLagrange
public import Physlib.ClassicalMechanics.HamiltonsEquations
public import Physlib.ClassicalMechanics.Pendulum.SimplePendulum.Geometric.Basic
public import Physlib.Mathematics.Calculus.Gradient
/-!

# The simple gravity pendulum

## i. Overview

A simple gravity pendulum is a bob of mass `m` fixed to one end of a rigid massless rod of length
`ℓ`, the other end of which is pinned at a pivot, swinging in a vertical plane under a uniform
gravitational acceleration `g`. Its configuration is the angle `θ` of the rod from the downward
vertical. The bob moves on the circle of radius `ℓ` about the pivot, so its moment of inertia
about the pivot is `I = m ℓ²` and its kinetic energy is `T = ½ I θ̇²`. Swinging out to the angle
`θ` raises the bob by `ℓ (1 - cos θ)` against gravity, so the potential energy is
`V = m g ℓ (1 - cos θ)`, normalised to vanish at the bottom of the swing. Balancing the rate of
change of the angular momentum about the pivot against the torque `-m g ℓ sin θ` of gravity gives
the equation of motion `I θ̈ = -m g ℓ sin θ`, equivalently `θ̈ + (g/ℓ) sin θ = 0`. The mass drops
out of the motion, which is governed by the single quantity `ω = √(g/ℓ)`, the angular frequency of
the small oscillations about the bottom.

The configuration of the pendulum is genuinely an angle modulo a full turn, an element of the
circle `SimplePendulum.ConfigurationSpace`. As for the harmonic oscillator, the dynamics in this
file are written instead on the Euclidean lift `Time → EuclideanSpace ℝ (Fin 1)`: the angle is
carried by a real number, from which the configuration is recovered by
`SimplePendulum.ConfigurationSpace.ofAngle`, and the one-dimensional Euclidean space stands in for
both the configuration space and its tangent space, so that the Euler–Lagrange operator of Physlib
applies verbatim. Two lifts differing by `2π n` describe the same motion; this, and the connection
of the model here with the geometric configuration space, is proved in a later module.

## ii. Key results

- `SimplePendulum` contains the input data of the problem: the mass `m` of the bob, the length `ℓ`
  of the rod and the gravitational acceleration `g`.
- `SimplePendulum.ω` is the angular frequency `√(g/ℓ)` of the small oscillations, and
  `SimplePendulum.inertia` is the moment of inertia `m ℓ²` of the bob about the pivot. They are
  tied together by `SimplePendulum.ω_sq_mul_inertia`, the identity by which the mass cancels from
  the equation of motion.
- `SimplePendulum.kineticEnergy`, `SimplePendulum.potentialEnergy` and `SimplePendulum.energy` are
  the energies, with the bounds `potentialEnergy_nonneg`, `potentialEnergy_le` and
  `potentialEnergy_eq_zero_iff`, the gradient `gradient_potentialEnergy` of the potential and the
  time derivatives `kineticEnergy_deriv`, `potentialEnergy_deriv` and `energy_deriv`.
- `SimplePendulum.lagrangian` is the Lagrangian `T - V` of the pendulum, and
  `SimplePendulum.torque` is the torque about the pivot, the quantity conjugate to the angle.
- `SimplePendulum.EquationOfMotion` is the equation of motion `I θ̈ = τ(θ)`, with its scalar form
  `equationOfMotion_iff_scalar` and its independence of the mass `equationOfMotion_iff_of_eq_ω`;
  `SimplePendulum.IsSolution` is a classical, that is smooth, solution of it.
- `SimplePendulum.gradLagrangian` is the variational derivative of the action, computed by
  `gradLagrangian_eq_eulerLagrangeOp` and `gradLagrangian_eq_torque`.

## iii. Table of contents

- A. The input data
  - A.1. The structure of the input data
  - A.2. Simple inequalities for the input data
- B. Frequency and moment of inertia
  - B.1. The angular frequency
  - B.2. The moment of inertia
- C. The energies
  - C.1. The definitions of the energies
  - C.2. Simple equalities and bounds for the energies
  - C.3. Smoothness of the energies and the gradient of the potential
  - C.4. Time derivatives of the energies
- D. The Lagrangian
  - D.1. The definition of the Lagrangian and equalities for it
  - D.2. Smoothness of the Lagrangian
  - D.3. Gradients of the Lagrangian
- E. The torque and the equation of motion
  - E.1. The torque
  - E.2. The equation of motion
  - E.3. Classical solutions
  - E.4. The scalar equation and independence of the mass
- F. The variational derivative of the action
  - F.1. The definition of the variational derivative
  - F.2. Equality with the Euler–Lagrange operator
  - F.3. The variational derivative in terms of the torque

## iv. References

References for the simple gravity pendulum include:
- Landau & Lifshitz, Mechanics, 3rd ed., §5 and §21.
- Arnold, Mathematical Methods of Classical Mechanics, 2nd ed., §4.

-/

@[expose] public section

namespace ClassicalMechanics
open Real InnerProductSpace

/-!

## A. The input data

We start by defining a structure containing the input data of the simple pendulum, and proving
basic properties thereof. The input data consists of the mass `m` of the bob, the length `ℓ` of
the rod, and the gravitational acceleration `g`; everything else in this file is built from these
three numbers.

-/

/-!

### A.1. The structure of the input data

The three numbers are carried by a structure, together with the positivity assumptions: a
pendulum with a massless bob, a rod of zero length or no gravity is not a pendulum.

-/

/-- The simple gravity pendulum is specified by the mass `m` of its bob, the length `ℓ` of its
  rod, and the gravitational acceleration `g`. All three are assumed to be positive. The
  configuration of the pendulum is the angle of the rod from the downward vertical. -/
structure SimplePendulum where
  /-- The mass of the bob. -/
  m : ℝ
  /-- The length of the massless rod. -/
  ℓ : ℝ
  /-- The gravitational acceleration. -/
  g : ℝ
  m_pos : 0 < m
  ℓ_pos : 0 < ℓ
  g_pos : 0 < g

namespace SimplePendulum

variable (S : SimplePendulum)

/-!

### A.2. Simple inequalities for the input data

The positivity of the input data is used most often through the corresponding non-vanishing
statements, which is the form in which the field-clearing tactics consume it.

-/

/-- The mass of the bob is not equal to zero. -/
@[simp]
lemma m_ne_zero : S.m ≠ 0 := S.m_pos.ne'

/-- The length of the rod is not equal to zero. -/
@[simp]
lemma ℓ_ne_zero : S.ℓ ≠ 0 := S.ℓ_pos.ne'

/-- The gravitational acceleration is not equal to zero. -/
@[simp]
lemma g_ne_zero : S.g ≠ 0 := S.g_pos.ne'

/-!

## B. Frequency and moment of inertia

Two derived quantities control the dynamics of the pendulum: the angular frequency `ω = √(g/ℓ)`
of the small oscillations about the bottom of the swing, and the moment of inertia `I = m ℓ²` of
the bob about the pivot.

The mass enters the equation of motion only through `I`, where it cancels against the mass in the
torque of gravity; what survives is `ω`. The identity performing that cancellation is
`ω_sq_mul_inertia`.

-/

/-!

### B.1. The angular frequency

Linearising `sin θ ≈ θ` about the bottom of the swing turns the equation of motion into that of a
harmonic oscillator of angular frequency `√(g/ℓ)`. The exact motion is not harmonic, but this
frequency is the natural time scale of the pendulum and appears throughout its analysis.

-/

/-- The angular frequency of the simple pendulum, `ω`, is defined as `√(g/ℓ)`. It is the angular
  frequency of the small oscillations of the pendulum about the bottom of its swing. -/
noncomputable def ω : ℝ := √(S.g / S.ℓ)

/-- The angular frequency of the simple pendulum is positive. -/
@[simp]
lemma ω_pos : 0 < S.ω := sqrt_pos.mpr (div_pos S.g_pos S.ℓ_pos)

/-- The angular frequency of the simple pendulum is not equal to zero. -/
lemma ω_ne_zero : S.ω ≠ 0 := S.ω_pos.ne'

/-- The square of the angular frequency of the simple pendulum is equal to `g/ℓ`. -/
lemma ω_sq : S.ω ^ 2 = S.g / S.ℓ := sq_sqrt (div_pos S.g_pos S.ℓ_pos).le

/-- The inverse of the square of the angular frequency of the simple pendulum is `ℓ/g`. -/
lemma inverse_ω_sq : (S.ω ^ 2)⁻¹ = S.ℓ / S.g := by rw [ω_sq, inv_div]

/-!

### B.2. The moment of inertia

The bob is a point mass at the fixed distance `ℓ` from the pivot, so the moment of inertia of the
pendulum about the pivot is `m ℓ²`. It is the coefficient relating the angular acceleration to
the torque, and so plays for the angle the role that the mass plays for a position.

-/

/-- The moment of inertia of the simple pendulum about its pivot is `I = m ℓ²`, the moment of
  inertia of a point mass `m` at distance `ℓ` from the axis. -/
noncomputable def inertia : ℝ := S.m * S.ℓ ^ 2

/-- The moment of inertia of the simple pendulum is positive. -/
lemma inertia_pos : 0 < S.inertia := mul_pos S.m_pos (pow_pos S.ℓ_pos 2)

/-- The moment of inertia of the simple pendulum is not equal to zero. -/
@[simp]
lemma inertia_ne_zero : S.inertia ≠ 0 := S.inertia_pos.ne'

/-- The square of the angular frequency times the moment of inertia is `m g ℓ`, the coefficient
  appearing in the potential energy and in the torque. This is the identity by which the mass
  cancels from the equation of motion. -/
lemma ω_sq_mul_inertia : S.ω ^ 2 * S.inertia = S.m * S.g * S.ℓ := by
  rw [ω_sq, inertia]
  field_simp

open MeasureTheory Time
open scoped ContDiff Gradient

/-!

## C. The energies

The simple pendulum has a kinetic energy determined by the rate of change of its angle, and a
potential energy determined by the height of the bob, hence by the angle itself. These combine to
give the total energy of the pendulum.

Here we state and prove a number of properties of these energies, including the gradient of the
potential energy, which is the object entering the equation of motion.

-/

/-!

### C.1. The definitions of the energies

We define the three energies; it is these energies which control the dynamics of the pendulum,
through the Lagrangian.

-/

/-- The kinetic energy of the simple pendulum along a lift `θ` of the angle is
  $\frac{1}{2} I ‖\dot θ‖^2$, where `I` is the moment of inertia about the pivot. -/
noncomputable def kineticEnergy (θ : Time → EuclideanSpace ℝ (Fin 1)) : Time → ℝ := fun t =>
  (1 / (2 : ℝ)) * S.inertia * ⟪∂ₜ θ t, ∂ₜ θ t⟫_ℝ

/-- The potential energy of the simple pendulum at the angle `x` is `m g ℓ (1 - cos θ)`, the work
  done against gravity in raising the bob from the bottom of the swing. It is normalised to
  vanish at the bottom. -/
noncomputable def potentialEnergy (x : EuclideanSpace ℝ (Fin 1)) : ℝ :=
  S.m * S.g * S.ℓ * (1 - Real.cos (x 0))

/-- The energy of the simple pendulum is the kinetic energy plus the potential energy. -/
noncomputable def energy (θ : Time → EuclideanSpace ℝ (Fin 1)) : Time → ℝ := fun t =>
  S.kineticEnergy θ t + S.potentialEnergy (θ t)

/-!

### C.2. Simple equalities and bounds for the energies

Besides the definitional unfoldings, the potential energy of the pendulum satisfies two bounds
that the harmonic oscillator has no analogue of: it is bounded, between `0` at the bottom of the
swing and `2 m g ℓ` at the top, and it vanishes exactly at the bottom.

-/

/-- The kinetic energy of the simple pendulum, written out. -/
lemma kineticEnergy_eq (θ : Time → EuclideanSpace ℝ (Fin 1)) :
    S.kineticEnergy θ = fun t => (1 / (2 : ℝ)) * S.inertia * ⟪∂ₜ θ t, ∂ₜ θ t⟫_ℝ := rfl

/-- The potential energy of the simple pendulum, written out. -/
lemma potentialEnergy_eq (x : EuclideanSpace ℝ (Fin 1)) :
    S.potentialEnergy x = S.m * S.g * S.ℓ * (1 - Real.cos (x 0)) := rfl

/-- The energy of the simple pendulum, written out. -/
lemma energy_eq (θ : Time → EuclideanSpace ℝ (Fin 1)) :
    S.energy θ = fun t => S.kineticEnergy θ t + S.potentialEnergy (θ t) := rfl

/-- The potential energy of the simple pendulum is non-negative, the bottom of the swing being
  the lowest point of the circle on which the bob moves. -/
lemma potentialEnergy_nonneg (x : EuclideanSpace ℝ (Fin 1)) : 0 ≤ S.potentialEnergy x := by
  have hc : 0 < S.m * S.g * S.ℓ := mul_pos (mul_pos S.m_pos S.g_pos) S.ℓ_pos
  have h : (0 : ℝ) ≤ 1 - Real.cos (x 0) := by
    have := Real.cos_le_one (x 0)
    linarith
  rw [potentialEnergy_eq]
  exact mul_nonneg hc.le h

/-- The potential energy of the simple pendulum is at most `2 m g ℓ`, its value at the top of the
  swing. -/
lemma potentialEnergy_le (x : EuclideanSpace ℝ (Fin 1)) :
    S.potentialEnergy x ≤ 2 * (S.m * S.g * S.ℓ) := by
  have hc : 0 < S.m * S.g * S.ℓ := mul_pos (mul_pos S.m_pos S.g_pos) S.ℓ_pos
  have h : 1 - Real.cos (x 0) ≤ 2 := by
    have := Real.neg_one_le_cos (x 0)
    linarith
  calc S.potentialEnergy x = S.m * S.g * S.ℓ * (1 - Real.cos (x 0)) := S.potentialEnergy_eq x
    _ ≤ S.m * S.g * S.ℓ * 2 := mul_le_mul_of_nonneg_left h hc.le
    _ = 2 * (S.m * S.g * S.ℓ) := by ring

/-- The potential energy of the simple pendulum vanishes exactly at the bottom of the swing, that
  is exactly at the angles which are whole multiples of a full turn. -/
lemma potentialEnergy_eq_zero_iff (x : EuclideanSpace ℝ (Fin 1)) :
    S.potentialEnergy x = 0 ↔ Real.cos (x 0) = 1 := by
  have hc : S.m * S.g * S.ℓ ≠ 0 := (mul_pos (mul_pos S.m_pos S.g_pos) S.ℓ_pos).ne'
  rw [potentialEnergy_eq, mul_eq_zero, or_iff_right hc, sub_eq_zero, eq_comm]

/-!

### C.3. Smoothness of the energies and the gradient of the potential

The potential energy is a smooth function of the angle, and its gradient on the one-dimensional
Euclidean lift is `m g ℓ sin θ` times the unit vector of the angular coordinate. This gradient is
what the equation of motion balances against the angular acceleration, so we record it here, once,
together with the gradient of the cosine of the angular coordinate from which it comes.

-/

/-- The potential energy of the simple pendulum is a smooth function of the angle. -/
@[fun_prop]
lemma potentialEnergy_contDiff (n : WithTop ℕ∞) : ContDiff ℝ n S.potentialEnergy := by
  unfold potentialEnergy
  fun_prop

/-- The potential energy of the simple pendulum is a differentiable function of the angle. -/
@[fun_prop]
lemma differentiable_potentialEnergy : Differentiable ℝ S.potentialEnergy :=
  (S.potentialEnergy_contDiff 1).differentiable one_ne_zero

/-- The gradient of the cosine of the angular coordinate on the one-dimensional Euclidean lift.
  This is the chain rule applied to `Real.cos` and to the coordinate functional, whose gradient
  is `gradient_coord`. It is specific to the cosine potential of the pendulum. -/
lemma gradient_cos_coord (x : EuclideanSpace ℝ (Fin 1)) :
    gradient (fun y : EuclideanSpace ℝ (Fin 1) => Real.cos (y 0)) x =
      -Real.sin (x 0) • EuclideanSpace.single 0 1 := by
  have hdiff : DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (Fin 1) => y 0) x := by fun_prop
  have hcoord : HasGradientAt (fun y : EuclideanSpace ℝ (Fin 1) => y 0)
      (EuclideanSpace.single 0 1) x := by
    simpa [gradient_coord] using hdiff.hasGradientAt
  have hf : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 1) => Real.cos (y 0))
      (toDual ℝ (EuclideanSpace ℝ (Fin 1))
        (-Real.sin (x 0) • EuclideanSpace.single 0 1)) x := by
    refine ((Real.hasDerivAt_cos (x 0)).hasFDerivAt.comp x hcoord.hasFDerivAt).congr_fderiv ?_
    ext y
    simp [toDual_apply_apply, EuclideanSpace.inner_single_left, mul_comm]
  simpa using hf.hasGradientAt.gradient

/-- The gradient of the potential energy of the simple pendulum is `m g ℓ sin θ` times the unit
  vector of the angular coordinate. -/
lemma gradient_potentialEnergy (x : EuclideanSpace ℝ (Fin 1)) :
    gradient S.potentialEnergy x =
      (S.m * S.g * S.ℓ * Real.sin (x 0)) • EuclideanSpace.single 0 1 := by
  have hcos : DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (Fin 1) => Real.cos (y 0)) x := by
    fun_prop
  have h : S.potentialEnergy = fun y : EuclideanSpace ℝ (Fin 1) =>
      -(S.m * S.g * S.ℓ) * Real.cos (y 0) + S.m * S.g * S.ℓ := by
    funext y
    rw [potentialEnergy_eq]
    ring
  rw [h, gradient_add_const, gradient_const_mul _ hcos, gradient_cos_coord]
  module

/-- Along a smooth lift of the angle the kinetic energy is differentiable in time. -/
@[fun_prop]
lemma kineticEnergy_differentiable (θ : Time → EuclideanSpace ℝ (Fin 1)) (hθ : ContDiff ℝ ∞ θ) :
    Differentiable ℝ (S.kineticEnergy θ) := by
  rw [kineticEnergy_eq]
  fun_prop

/-- Along a smooth lift of the angle the potential energy is differentiable in time. -/
@[fun_prop]
lemma potentialEnergy_differentiable (θ : Time → EuclideanSpace ℝ (Fin 1)) (hθ : ContDiff ℝ ∞ θ) :
    Differentiable ℝ (fun t => S.potentialEnergy (θ t)) := by
  have hd : Differentiable ℝ θ := hθ.differentiable (by simp)
  fun_prop

/-- Along a smooth lift of the angle the energy is differentiable in time. -/
@[fun_prop]
lemma energy_differentiable (θ : Time → EuclideanSpace ℝ (Fin 1)) (hθ : ContDiff ℝ ∞ θ) :
    Differentiable ℝ (S.energy θ) := by
  rw [energy_eq]
  fun_prop

/-!

### C.4. Time derivatives of the energies

For a general smooth lift of the angle, which need not satisfy the equation of motion, we can
compute the time derivatives of the energies. Each is an inner product against the angular
velocity: the equation of motion will be exactly the statement that the two contributions cancel.

-/

/-- The rate of change of the kinetic energy is the angular velocity paired with the angular
  momentum's rate of change, `I θ̈`. -/
lemma kineticEnergy_deriv (θ : Time → EuclideanSpace ℝ (Fin 1)) (hθ : ContDiff ℝ ∞ θ) :
    ∂ₜ (S.kineticEnergy θ) = fun t => ⟪∂ₜ θ t, S.inertia • ∂ₜ (∂ₜ θ) t⟫_ℝ := by
  funext t
  unfold kineticEnergy
  have hd : DifferentiableAt ℝ (∂ₜ θ) t :=
    (deriv_differentiable_of_contDiff θ hθ).differentiableAt
  rw [Time.deriv_eq, fderiv_const_mul (by fun_prop), _root_.smul_apply,
    fderiv_inner_apply (𝕜 := ℝ) hd hd, ← Time.deriv_eq]
  simp [inner_smul_right, real_inner_comm]
  ring

/-- The rate of change of the potential energy is the angular velocity paired with the gradient
  of the potential. -/
lemma potentialEnergy_deriv (θ : Time → EuclideanSpace ℝ (Fin 1)) (hθ : ContDiff ℝ ∞ θ) :
    ∂ₜ (fun t => S.potentialEnergy (θ t)) =
      fun t => ⟪∂ₜ θ t, gradient S.potentialEnergy (θ t)⟫_ℝ := by
  funext t
  have hd : DifferentiableAt ℝ θ t := (hθ.differentiable (by simp)).differentiableAt
  have hV : DifferentiableAt ℝ S.potentialEnergy (θ t) :=
    (S.potentialEnergy_contDiff ∞).differentiable (by simp) (θ t)
  have hf : HasFDerivAt (fun t => S.potentialEnergy (θ t)) _ t :=
    hV.hasFDerivAt.comp t hd.hasFDerivAt
  rw [Time.deriv_eq, hf.fderiv]
  simp [Time.deriv_eq]

/-- The rate of change of the energy is the angular velocity paired with the sum of `I θ̈` and
  the gradient of the potential; the equation of motion is exactly the vanishing of that sum. -/
lemma energy_deriv (θ : Time → EuclideanSpace ℝ (Fin 1)) (hθ : ContDiff ℝ ∞ θ) :
    ∂ₜ (S.energy θ) =
      fun t => ⟪∂ₜ θ t, S.inertia • ∂ₜ (∂ₜ θ) t + gradient S.potentialEnergy (θ t)⟫_ℝ := by
  unfold energy
  funext t
  rw [Time.deriv_eq, fderiv_fun_add (by fun_prop) (S.potentialEnergy_differentiable θ hθ t)]
  simp only [_root_.add_apply, ← Time.deriv_eq, S.kineticEnergy_deriv θ hθ,
    S.potentialEnergy_deriv θ hθ, ← inner_add_right]

end SimplePendulum

end ClassicalMechanics

end
