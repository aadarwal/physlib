/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.ClassicalMechanics.EulerLagrange
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
`V = m g ℓ (1 - cos θ)`, normalized to vanish at the bottom of the swing. Balancing the rate of
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
applies verbatim. Two lifts differing by `2π n` describe the same motion, as the invariance
theorems of section K prove; the full connection of the model here with the geometric
configuration space is made in a later module, section K recording the one fact needed here,
that lifts differing by whole turns describe the same configuration.

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
  `SimplePendulum.torque` is the torque about the pivot, the generalized force conjugate to
  the angle.
- `SimplePendulum.EquationOfMotion` is the equation of motion `I θ̈ = τ(θ)`, with its scalar form
  `equationOfMotion_iff_scalar` and its independence of the mass `equationOfMotion_iff_of_eq_ω`;
  `SimplePendulum.IsSolution` is a smooth solution of it.
- `SimplePendulum.gradLagrangian` is the variational derivative of the action, computed by
  `gradLagrangian_eq_eulerLagrangeOp` and `gradLagrangian_eq_torque`.
- `SimplePendulum.equationOfMotion_iff_gradLagrangian_zero` identifies the equation of motion,
  for smooth lifts of the angle, with the vanishing of the variational derivative of the action,
  and `SimplePendulum.isSolution_iff` characterizes the solutions as the smooth critical points
  of the action.
- `SimplePendulum.energy_conservation_of_equationOfMotion`,
  `SimplePendulum.energy_conservation_of_equationOfMotion'` and
  `SimplePendulum.IsSolution.energy_eq` express the conservation of energy along the motions of
  the pendulum.
- `SimplePendulum.equationOfMotion_const_zero` and `SimplePendulum.equationOfMotion_const_pi`
  are the hanging and the inverted equilibrium, packaged as the first explicit solutions of the
  pendulum by `SimplePendulum.isSolution_const_zero` and `SimplePendulum.isSolution_const_pi`,
  and `SimplePendulum.equationOfMotion_const_iff` shows that the constant solutions are exactly
  the equilibria.
- `SimplePendulum.separatrixEnergy` is the energy `2 m g ℓ` of the inverted equilibrium, the
  threshold between libration and rotation: below it the bob never reaches the top of the swing
  (`neg_one_lt_cos_of_energy_lt`), above it the angular velocity never vanishes
  (`deriv_ne_zero_of_energy_gt`), and at a turning point the potential energy equals the total
  energy (`potentialEnergy_eq_energy_of_deriv_eq_zero`).
- `SimplePendulum.equationOfMotion_add_int_mul_two_pi` and
  `SimplePendulum.isSolution_add_int_mul_two_pi`, with the invariance of the energies and the
  torque, show that the lifted dynamics is unchanged by shifting the lift by a whole number of
  turns, and `SimplePendulum.ofAngle_add_int_mul_two_pi_coord` confirms that the shifted lift
  describes the same configuration.

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
  - E.3. Smooth solutions
  - E.4. The scalar equation and independence of the mass
- F. The variational derivative of the action
  - F.1. The definition of the variational derivative
  - F.2. Equality with the Euler–Lagrange operator
  - F.3. The variational derivative in terms of the torque
- G. Equation of motion and the variational principle
  - G.1. Equivalence with the vanishing of the variational derivative
  - G.2. The variational characterization of solutions
- H. Energy conservation
  - H.1. Energy conservation in terms of time derivatives
  - H.2. Energy conservation in terms of constant energy
  - H.3. Energy conservation for solutions
- I. Equilibria
  - I.1. The hanging equilibrium
  - I.2. The inverted equilibrium
  - I.3. The constant solutions are the equilibria
- J. Energy regimes
  - J.1. The separatrix energy
  - J.2. Energy bounds
  - J.3. Libration and rotation
  - J.4. Turning points
- K. Independence of the lift
  - K.1. Invariance of the potential energy and the torque
  - K.2. Invariance of the energy
  - K.3. Invariance of the equation of motion and its solutions
  - K.4. The shifted lift describes the same configuration

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

Linearizing `sin θ ≈ θ` about the bottom of the swing turns the equation of motion into that of a
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
def inertia : ℝ := S.m * S.ℓ ^ 2

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

open Time
open scoped ContDiff

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

/-- The potential energy of the simple pendulum at the angle `x` is `m g ℓ (1 - cos (x 0))`, the
  work done against gravity in raising the bob from the bottom of the swing. It is normalized to
  vanish at the bottom. -/
noncomputable def potentialEnergy (x : EuclideanSpace ℝ (Fin 1)) : ℝ :=
  S.m * S.g * S.ℓ * (1 - Real.cos (x 0))

/-- The energy of the simple pendulum is the kinetic energy plus the potential energy. -/
noncomputable def energy (θ : Time → EuclideanSpace ℝ (Fin 1)) : Time → ℝ := fun t =>
  S.kineticEnergy θ t + S.potentialEnergy (θ t)

/-!

### C.2. Simple equalities and bounds for the energies

Besides the definitional unfoldings, the potential energy of the pendulum is non-negative and
vanishes exactly at the bottom of the swing, just as the potential energy of the harmonic
oscillator is non-negative and vanishes exactly at the origin. What has no harmonic-oscillator
analogue is the upper bound: the potential energy of the pendulum is at most `2 m g ℓ`, its
value at the top of the swing.

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

/-- The potential energy of the simple pendulum vanishes exactly when the cosine of the angle is
  equal to `1`, that is exactly at the bottom of the swing. -/
lemma potentialEnergy_eq_zero_iff (x : EuclideanSpace ℝ (Fin 1)) :
    S.potentialEnergy x = 0 ↔ Real.cos (x 0) = 1 := by
  have hc : S.m * S.g * S.ℓ ≠ 0 := (mul_pos (mul_pos S.m_pos S.g_pos) S.ℓ_pos).ne'
  rw [potentialEnergy_eq, mul_eq_zero, or_iff_right hc, sub_eq_zero, eq_comm]

/-!

### C.3. Smoothness of the energies and the gradient of the potential

The potential energy is a smooth function of the angle, and its gradient on the one-dimensional
Euclidean lift is `m g ℓ sin θ` times the unit vector of the angular coordinate. This gradient is
what the equation of motion balances against the angular acceleration, so we record it here, once.
The subsection also records that, along a smooth lift of the angle, each of the three energies is
a differentiable function of the time — differentiability in time along the lift, as distinct
from the differentiability in the angle of the potential energy — which is the differentiability
that the time derivatives of section C.4 consume.

-/

/-- The potential energy of the simple pendulum is a smooth function of the angle. -/
@[fun_prop]
lemma potentialEnergy_contDiff (n : WithTop ℕ∞) : ContDiff ℝ n S.potentialEnergy := by
  unfold potentialEnergy
  fun_prop

/-- The potential energy of the simple pendulum is a differentiable function of the angle. This
  is differentiability in the angle; for differentiability in time along a smooth lift of the
  angle see `potentialEnergy_differentiable`. -/
@[fun_prop]
lemma differentiable_potentialEnergy : Differentiable ℝ S.potentialEnergy :=
  (S.potentialEnergy_contDiff 1).differentiable one_ne_zero

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
  rw [h, gradient_add_const, gradient_const_mul _ hcos,
    gradient_comp_coord 0 x (Real.hasDerivAt_cos (x 0))]
  module

/-- Along a smooth lift of the angle the kinetic energy is differentiable in time. -/
@[fun_prop]
lemma kineticEnergy_differentiable (θ : Time → EuclideanSpace ℝ (Fin 1)) (hθ : ContDiff ℝ ∞ θ) :
    Differentiable ℝ (S.kineticEnergy θ) := by
  rw [kineticEnergy_eq]
  fun_prop

/-- Along a smooth lift of the angle the potential energy is a differentiable function of the
  time. This is differentiability in time along the lift; for differentiability in the angle see
  `differentiable_potentialEnergy`. -/
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
    (S.potentialEnergy_contDiff 1).differentiable one_ne_zero (θ t)
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

/-!

## D. The Lagrangian

The pendulum is a conservative system, so its Lagrangian is the kinetic energy minus the potential
energy, `L = ½ I θ̇² - m g ℓ (1 - cos θ)`. As for the harmonic oscillator, it is defined as a
function on phase space, of the time, the angle and the angular velocity separately; that it is
`T - V` along a lift of the angle is then a lemma rather than the definition.

The Lagrangian carries no explicit time dependence, the pendulum being autonomous; the time
argument is kept because it is the type the Euler–Lagrange operator of Physlib expects.

-/

/-!

### D.1. The definition of the Lagrangian and equalities for it

The Lagrangian is written directly in terms of the moment of inertia and the potential energy,
so that the equalities below are the two ways of reading it: expanded in the input data, and as
the kinetic energy minus the potential energy along a lift of the angle.

-/

set_option linter.unusedVariables false in
/-- The Lagrangian of the simple pendulum, `L(t, θ, θ̇) = ½ I ‖θ̇‖² - V(θ)`, the kinetic energy
  minus the potential energy as a function on phase space. It does not depend on the time. -/
@[nolint unusedArguments]
noncomputable def lagrangian (t : Time) (x v : EuclideanSpace ℝ (Fin 1)) : ℝ :=
  (1 / (2 : ℝ)) * S.inertia * ⟪v, v⟫_ℝ - S.potentialEnergy x

/-- The Lagrangian of the simple pendulum, written out in the input data. -/
lemma lagrangian_eq :
    S.lagrangian = fun _ x v =>
      (1 / (2 : ℝ)) * S.inertia * ⟪v, v⟫_ℝ - S.m * S.g * S.ℓ * (1 - Real.cos (x 0)) := by
  funext t x v
  rw [lagrangian, potentialEnergy_eq]

/-- Along a lift of the angle the Lagrangian of the simple pendulum is the kinetic energy minus
  the potential energy. -/
lemma lagrangian_eq_kineticEnergy_sub_potentialEnergy (t : Time)
    (θ : Time → EuclideanSpace ℝ (Fin 1)) :
    S.lagrangian t (θ t) (∂ₜ θ t) = S.kineticEnergy θ t - S.potentialEnergy (θ t) := rfl

/-!

### D.2. Smoothness of the Lagrangian

The Lagrangian is a smooth function of all of its arguments jointly. This is the hypothesis that
the Euler–Lagrange theorem of Physlib places on a Lagrangian, so it is recorded on the uncurried
form `↿S.lagrangian`.

-/

/-- The Lagrangian of the simple pendulum is a smooth function of the time, the angle and the
  angular velocity jointly. -/
@[fun_prop]
lemma contDiff_lagrangian (n : WithTop ℕ∞) : ContDiff ℝ n ↿S.lagrangian := by
  rw [lagrangian_eq]
  fun_prop

/-!

### D.3. Gradients of the Lagrangian

The Euler–Lagrange operator is built from the two partial gradients of the Lagrangian. The
gradient in the angle is minus the gradient of the potential energy, that is the torque of
section E; the gradient in the angular velocity is the angular momentum `I θ̇`.

-/

/-- The gradient of the Lagrangian of the simple pendulum in the angle is minus the gradient of
  the potential energy, `-m g ℓ sin θ` times the unit vector of the angular coordinate. -/
lemma gradient_lagrangian_position_eq (t : Time) (x v : EuclideanSpace ℝ (Fin 1)) :
    gradient (fun x => S.lagrangian t x v) x =
      -((S.m * S.g * S.ℓ * Real.sin (x 0)) • EuclideanSpace.single 0 1) := by
  have h : (fun y : EuclideanSpace ℝ (Fin 1) => S.lagrangian t y v) =
      fun y => (-1 : ℝ) * S.potentialEnergy y + (1 / (2 : ℝ)) * S.inertia * ⟪v, v⟫_ℝ := by
    funext y
    rw [lagrangian]
    ring
  rw [h, gradient_add_const, gradient_const_mul _ (S.differentiable_potentialEnergy x),
    gradient_potentialEnergy]
  module

/-- The gradient of the Lagrangian of the simple pendulum in the angular velocity is the angular
  momentum `I θ̇` about the pivot. -/
lemma gradient_lagrangian_velocity_eq (t : Time) (x v : EuclideanSpace ℝ (Fin 1)) :
    gradient (S.lagrangian t x) v = S.inertia • v := by
  have h : S.lagrangian t x = fun y : EuclideanSpace ℝ (Fin 1) =>
      ((1 / (2 : ℝ)) * S.inertia) * ⟪y, y⟫_ℝ + -S.potentialEnergy x := by
    funext y
    rw [lagrangian]
    ring
  rw [h, gradient_add_const, gradient_const_mul_inner_self]
  module

/-!

## E. The torque and the equation of motion

Gravity exerts on the bob a torque `-m g ℓ sin θ` about the pivot, the generalized force conjugate
to the angle, and the equation of motion balances it against the rate of change `I θ̈` of the
angular momentum.

We take that pointwise relation as the definition of the equation of motion, rather than the
vanishing of the variational derivative of the action, which is how the harmonic oscillator defines
its own. The reason is that the variational derivative is defined to be `0` whenever no variational
gradient exists, so its vanishing holds vacuously for every lift of the angle too rough to admit
one; it says what it is meant to say only under a smoothness assumption. The pointwise equation is
totalized too — `∂ₜ` is `fderiv`, which is `0` off differentiability — but its totalization cannot
make the equation vacuously true: both sides remain genuine, and generally unequal, functions of
time. A rough lift can still satisfy the equation accidentally — a discontinuous lift hopping
between equilibrium angles solves it, as section E.3 explains — which is why the notion of a
solution, `IsSolution`, demands smoothness as well. It is also the form in which the equation of
motion is solved and used. The two agree for smooth lifts, by
`equationOfMotion_iff_gradLagrangian_zero` of section G, which is one rearrangement away from
`gradLagrangian_eq_torque` of section F.

-/

/-!

### E.1. The torque

The pendulum is conservative, so the generalized force conjugate to the angle is minus the
gradient of the potential energy. It is a torque about the pivot rather than a force, the angle
being the coordinate; this is why it is `m g ℓ sin θ` and not `m g sin θ`.

-/

/-- The generalized force of the simple pendulum conjugate to the angle, that is the torque about
  the pivot, is minus the gradient of the potential energy, `τ = -∂V/∂θ`. -/
noncomputable def torque (x : EuclideanSpace ℝ (Fin 1)) : EuclideanSpace ℝ (Fin 1) :=
  -gradient S.potentialEnergy x

/-- The torque of the simple pendulum is `-m g ℓ sin θ` times the unit vector of the angular
  coordinate. It is restoring near the bottom of the swing: for `|θ| < π` it opposes the
  displacement, and it vanishes both at the bottom and at the inverted position. -/
lemma torque_eq (x : EuclideanSpace ℝ (Fin 1)) :
    S.torque x = -((S.m * S.g * S.ℓ * Real.sin (x 0)) • EuclideanSpace.single 0 1) := by
  rw [torque, gradient_potentialEnergy]

/-- The single component of the torque of the simple pendulum is `-m g ℓ sin θ`. -/
lemma torque_apply (x : EuclideanSpace ℝ (Fin 1)) :
    S.torque x 0 = -(S.m * S.g * S.ℓ * Real.sin (x 0)) := by
  rw [torque_eq]
  simp

/-!

### E.2. The equation of motion

The equation of motion of the simple pendulum equates the rate of change of the angular momentum
about the pivot with the torque of gravity, at every instant.

-/

/-- The equation of motion of the simple pendulum: at every instant the rate of change `I θ̈` of
  the angular momentum about the pivot equals the torque `τ(θ)` of gravity.

  This pointwise relation, and not the vanishing of the variational derivative of the action, is
  the definition of the equation of motion here; see the discussion in section E. For a smooth
  lift of the angle the two agree, by `equationOfMotion_iff_gradLagrangian_zero` of section G. -/
def EquationOfMotion (θ : Time → EuclideanSpace ℝ (Fin 1)) : Prop :=
  ∀ t, S.inertia • ∂ₜ (∂ₜ θ) t = S.torque (θ t)

/-- The equation of motion of the simple pendulum with all of its terms on one side: at every
  instant the rate of change `I θ̈` of the angular momentum plus the gradient of the potential
  energy vanishes. This is the rotational form of Newton's second law, in the shape in which
  `DampedHarmonicOscillator` states its own; the sum on the left is exactly the combination that
  `energy_deriv` pairs with the velocity `∂ₜ θ`. -/
lemma equationOfMotion_iff_newtons_2nd_law (θ : Time → EuclideanSpace ℝ (Fin 1)) :
    S.EquationOfMotion θ ↔
      ∀ t, S.inertia • ∂ₜ (∂ₜ θ) t + gradient S.potentialEnergy (θ t) = 0 := by
  simp only [EquationOfMotion, torque, eq_neg_iff_add_eq_zero]

/-!

### E.3. Smooth solutions

A solution of the pendulum is a smooth lift satisfying the equation of motion. Smoothness is part
of the definition because the bare pointwise equation, being totalized, admits unphysical
solutions: a lift jumping between the equilibrium angles `0` and `π` has zero torque everywhere,
and — being locally constant wherever it is differentiable at all — it has `∂ₜ θ`, and hence
`∂ₜ (∂ₜ θ)`, identically zero, so it satisfies the equation even when it is nowhere continuous.
Demanding smoothness excludes such junk, and is the regularity under which the variational
description of the motion agrees with the pointwise one.

-/

/-- A solution of the simple pendulum is a smooth lift of the angle satisfying the equation of
  motion. -/
def IsSolution (θ : Time → EuclideanSpace ℝ (Fin 1)) : Prop :=
  ContDiff ℝ ∞ θ ∧ S.EquationOfMotion θ

/-- A solution of the simple pendulum is smooth. -/
lemma IsSolution.contDiff {S : SimplePendulum} {θ : Time → EuclideanSpace ℝ (Fin 1)}
    (h : S.IsSolution θ) : ContDiff ℝ ∞ θ := h.1

/-- A solution of the simple pendulum satisfies the equation of motion. -/
lemma IsSolution.equationOfMotion {S : SimplePendulum} {θ : Time → EuclideanSpace ℝ (Fin 1)}
    (h : S.IsSolution θ) : S.EquationOfMotion θ := h.2

/-!

### E.4. The scalar equation and independence of the mass

The angle is a single number, so the vector equation of motion is equivalent to the scalar
equation obtained by reading off its one component. Dividing that component by the moment of
inertia, using `ω_sq_mul_inertia`, cancels the mass and leaves `θ̈ + ω² sin θ = 0`: two pendulums
with the same `ω = √(g/ℓ)` have exactly the same angular motions, whatever their masses.

-/

/-- The equation of motion of the simple pendulum in scalar form, `θ̈ + ω² sin θ = 0`. The mass
  has cancelled: only the angular frequency `ω = √(g/ℓ)` survives. -/
lemma equationOfMotion_iff_scalar (θ : Time → EuclideanSpace ℝ (Fin 1)) :
    S.EquationOfMotion θ ↔ ∀ t, ∂ₜ (∂ₜ θ) t 0 + S.ω ^ 2 * Real.sin (θ t 0) = 0 := by
  simp only [EquationOfMotion]
  refine forall_congr' fun t => ?_
  have hcomp : (S.inertia • ∂ₜ (∂ₜ θ) t = S.torque (θ t)) ↔
      S.inertia * ∂ₜ (∂ₜ θ) t 0 = -(S.m * S.g * S.ℓ * Real.sin (θ t 0)) := by
    rw [← S.torque_apply (θ t)]
    constructor
    · intro h
      simpa using congrArg (fun y : EuclideanSpace ℝ (Fin 1) => y 0) h
    · intro h
      ext i
      fin_cases i
      simpa using h
  rw [hcomp, ← S.ω_sq_mul_inertia]
  constructor
  · intro h
    have h' : S.inertia * (∂ₜ (∂ₜ θ) t 0 + S.ω ^ 2 * Real.sin (θ t 0)) = 0 := by
      linear_combination h
    exact (mul_eq_zero.mp h').resolve_left S.inertia_ne_zero
  · intro h
    linear_combination S.inertia * h

/-- Two simple pendulums with the same angular frequency have the same angular equation of
  motion, and hence the same angular motions; in particular, changing only the mass does not
  affect the angular motion. An equal `ω` still permits different lengths, and so different
  trajectories of the bob in space. -/
lemma equationOfMotion_iff_of_eq_ω (S' : SimplePendulum) (h : S'.ω = S.ω)
    (θ : Time → EuclideanSpace ℝ (Fin 1)) :
    S'.EquationOfMotion θ ↔ S.EquationOfMotion θ := by
  rw [S'.equationOfMotion_iff_scalar, S.equationOfMotion_iff_scalar, h]

/-!

## F. The variational derivative of the action

The action of the simple pendulum is the time integral of the Lagrangian along a lift of the
angle. Its variational derivative is computed here, in two steps: it is the Euler–Lagrange
operator of the Lagrangian, and that operator is the torque minus the rate of change of the
angular momentum.

-/

/-!

### F.1. The definition of the variational derivative

The variational derivative is that of Physlib's variational calculus, applied to the action of the
pendulum. Recall that it is defined to be `0` when no variational gradient exists, so the lemmas
below are stated for smooth lifts of the angle.

-/

/-- The variational derivative of the action of the simple pendulum, the action being the time
  integral of the Lagrangian along a lift of the angle. -/
noncomputable def gradLagrangian (θ : Time → EuclideanSpace ℝ (Fin 1)) :
    Time → EuclideanSpace ℝ (Fin 1) :=
  (δ (q':=θ), ∫ t, S.lagrangian t (q' t) (fderiv ℝ q' t 1))

/-!

### F.2. Equality with the Euler–Lagrange operator

For a smooth lift of the angle the variational derivative of the action is the Euler–Lagrange
operator of the Lagrangian, by the general theorem `euler_lagrange_varGradient`; the hypotheses
of that theorem are the smoothness of the lift and `contDiff_lagrangian`.

-/

/-- For a smooth lift of the angle the variational derivative of the action of the simple
  pendulum is the Euler–Lagrange operator of its Lagrangian. -/
lemma gradLagrangian_eq_eulerLagrangeOp (θ : Time → EuclideanSpace ℝ (Fin 1))
    (hθ : ContDiff ℝ ∞ θ) :
    S.gradLagrangian θ = eulerLagrangeOp S.lagrangian θ := by
  rw [gradLagrangian, euler_lagrange_varGradient _ _ hθ (S.contDiff_lagrangian _)]

/-!

### F.3. The variational derivative in terms of the torque

Evaluating the Euler–Lagrange operator with the gradients of section D.3 gives the variational
derivative as the torque minus the rate of change of the angular momentum. Its vanishing is
therefore the equation of motion of section E; that equivalence is
`equationOfMotion_iff_gradLagrangian_zero` of section G.

-/

/-- For a smooth lift of the angle the variational derivative of the action of the simple
  pendulum is the torque minus the rate of change `I θ̈` of the angular momentum. -/
lemma gradLagrangian_eq_torque (θ : Time → EuclideanSpace ℝ (Fin 1)) (hθ : ContDiff ℝ ∞ θ) :
    S.gradLagrangian θ = fun t => S.torque (θ t) - S.inertia • ∂ₜ (∂ₜ θ) t := by
  funext t
  rw [S.gradLagrangian_eq_eulerLagrangeOp θ hθ, eulerLagrangeOp]
  simp [S.gradient_lagrangian_position_eq, S.gradient_lagrangian_velocity_eq, S.torque_eq,
    Time.deriv_smul _ S.inertia (deriv_differentiable_of_contDiff θ hθ)]

/-!

## G. Equation of motion and the variational principle

Section E took the pointwise balance of the angular momentum's rate of change against the torque
as the definition of the equation of motion, and section F computed the variational derivative of
the action. This section proves that for smooth lifts of the angle the two agree: the pointwise
law is exactly the Euler–Lagrange equation of the action, the statement that the motion is a
critical point of the action. The equivalence holds only under smoothness — the variational
derivative is `0` by convention on lifts too rough to admit a variational gradient, so on such
lifts its vanishing says nothing — which is why section E took the pointwise form as primary.

-/

/-!

### G.1. Equivalence with the vanishing of the variational derivative

By `gradLagrangian_eq_torque` the variational derivative of the action along a smooth lift is
the torque minus the rate of change of the angular momentum, so its vanishing is a rearrangement
of the equation of motion.

-/

/-- For a smooth lift of the angle the equation of motion of the simple pendulum holds if and
  only if the variational derivative of the action vanishes: the smooth motions of the pendulum
  are the critical points of its action. -/
lemma equationOfMotion_iff_gradLagrangian_zero (θ : Time → EuclideanSpace ℝ (Fin 1))
    (hθ : ContDiff ℝ ∞ θ) :
    S.EquationOfMotion θ ↔ S.gradLagrangian θ = 0 := by
  rw [S.gradLagrangian_eq_torque θ hθ, funext_iff]
  simp only [EquationOfMotion, Pi.zero_apply, sub_eq_zero]
  exact forall_congr' fun t => eq_comm

/-!

### G.2. The variational characterization of solutions

A solution was defined in section E.3 as a smooth lift satisfying the equation of motion.
Substituting the equivalence of G.1 for the equation of motion turns this into the variational
characterization: the solutions of the pendulum are exactly the smooth lifts of the angle along
which the variational derivative of the action vanishes.

-/

/-- A lift of the angle is a solution of the simple pendulum if and only if it is smooth and the
  variational derivative of the action vanishes along it. -/
lemma isSolution_iff (θ : Time → EuclideanSpace ℝ (Fin 1)) :
    S.IsSolution θ ↔ ContDiff ℝ ∞ θ ∧ S.gradLagrangian θ = 0 :=
  and_congr_right fun hθ => S.equationOfMotion_iff_gradLagrangian_zero θ hθ

/-!

## H. Energy conservation

The pendulum is conservative: along any smooth lift of the angle satisfying the equation of
motion the energy is constant. No computation remains to be done here: by `energy_deriv` the
rate of change of the energy is the angular velocity paired with the sum of `I θ̈` and the
gradient of the potential, and the equation of motion is exactly the vanishing of that sum.

-/

/-!

### H.1. Energy conservation in terms of time derivatives

The first form of energy conservation: the time derivative of the energy vanishes identically
along any smooth lift of the angle satisfying the equation of motion.

-/

/-- Along a smooth lift of the angle satisfying the equation of motion the time derivative of
  the energy of the simple pendulum vanishes. -/
lemma energy_conservation_of_equationOfMotion (θ : Time → EuclideanSpace ℝ (Fin 1))
    (hθ : ContDiff ℝ ∞ θ) (h : S.EquationOfMotion θ) : ∂ₜ (S.energy θ) = 0 := by
  rw [S.equationOfMotion_iff_newtons_2nd_law θ] at h
  funext t
  rw [S.energy_deriv θ hθ]
  simp [h t]

/-!

### H.2. Energy conservation in terms of constant energy

The second form: the energy is differentiable in time along a smooth lift of the angle, so the
vanishing of its derivative makes it a constant function of the time, equal to its initial
value.

-/

/-- Along a smooth lift of the angle satisfying the equation of motion the energy of the simple
  pendulum at any time is equal to its initial value. -/
lemma energy_conservation_of_equationOfMotion' (θ : Time → EuclideanSpace ℝ (Fin 1))
    (hθ : ContDiff ℝ ∞ θ) (h : S.EquationOfMotion θ) (t : Time) :
    S.energy θ t = S.energy θ 0 := by
  apply is_const_of_fderiv_eq_zero (𝕜 := ℝ) (S.energy_differentiable θ hθ)
  intro t
  ext p
  rw [p.eq_one_smul, map_smul, ← Time.deriv_eq,
    S.energy_conservation_of_equationOfMotion θ hθ h]
  simp

/-!

### H.3. Energy conservation for solutions

The hypotheses of energy conservation — smoothness and the equation of motion — are exactly the
two components of being a solution, so for solutions conservation takes its most compact form.

-/

/-- The energy of the simple pendulum along a solution at any time is equal to its initial
  value. -/
lemma IsSolution.energy_eq {S : SimplePendulum} {θ : Time → EuclideanSpace ℝ (Fin 1)}
    (h : S.IsSolution θ) (t : Time) : S.energy θ t = S.energy θ 0 :=
  S.energy_conservation_of_equationOfMotion' θ h.contDiff h.equationOfMotion t

/-!

## I. Equilibria

The two configurations at which the torque of gravity vanishes — the bob hanging at rest below
the pivot and the bob balanced above it — give constant solutions of the equation of motion, the
first explicit solutions appearing in this file. This section verifies the two, and proves the
converse: a constant lift solves the equation of motion only where the torque vanishes, that is
only at the angles `π n`. The constant solutions are exactly the equilibria.

-/

/-!

### I.1. The hanging equilibrium

At the angle `0` the bob hangs at rest at the bottom of its swing. The lift is constant, so the
angular momentum does not change, and the torque vanishes with `sin 0`: both sides of the
equation of motion are zero.

-/

/-- The constant lift at the angle `0` — the bob hanging at rest at the bottom of its swing —
  satisfies the equation of motion of the simple pendulum. -/
lemma equationOfMotion_const_zero :
    S.EquationOfMotion (fun _ => (0 : EuclideanSpace ℝ (Fin 1))) := by
  intro t
  have h1 : ∂ₜ (fun _ : Time => (0 : EuclideanSpace ℝ (Fin 1))) = fun _ => 0 := by
    funext s
    simp
  rw [h1]
  simp [torque_eq]

/-- The hanging equilibrium is a solution of the simple pendulum: the constant lift at the angle
  `0` is smooth and satisfies the equation of motion. It is the first explicit solution of this
  file. -/
lemma isSolution_const_zero : S.IsSolution (fun _ => 0) :=
  ⟨contDiff_const, S.equationOfMotion_const_zero⟩

/-!

### I.2. The inverted equilibrium

At the angle `π` the bob is balanced directly above the pivot, where the torque vanishes with
`sin π`; the pendulum stays there. That this balance is unstable — neighbouring solutions run
away from it — is a statement about non-constant solutions, and is not proved here.

-/

/-- The constant lift at the angle `π` — the bob balanced directly above the pivot — satisfies
  the equation of motion of the simple pendulum. -/
lemma equationOfMotion_const_pi :
    S.EquationOfMotion (fun _ => EuclideanSpace.single 0 Real.pi) := by
  intro t
  have h1 : ∂ₜ (fun _ : Time => EuclideanSpace.single (0 : Fin 1) Real.pi) = fun _ => 0 := by
    funext s
    simp
  rw [h1]
  simp [torque_eq]

/-- The inverted equilibrium is a solution of the simple pendulum: the constant lift at the
  angle `π` is smooth and satisfies the equation of motion. -/
lemma isSolution_const_pi : S.IsSolution (fun _ => EuclideanSpace.single 0 Real.pi) :=
  ⟨contDiff_const, S.equationOfMotion_const_pi⟩

/-!

### I.3. The constant solutions are the equilibria

For a constant lift the angular momentum does not change, so the equation of motion reduces to
the vanishing of the torque, that is to `sin θ = 0`, which holds exactly at the multiples of
`π`. The constant solutions are therefore exactly the equilibria: the hanging equilibrium, the
inverted equilibrium, and their copies shifted by whole turns.

-/

/-- A constant lift satisfies the equation of motion of the simple pendulum if and only if the
  sine of its angle vanishes — classically, the angles straight down and straight up: the
  constant solutions are exactly the equilibria. -/
lemma equationOfMotion_const_iff (x : EuclideanSpace ℝ (Fin 1)) :
    S.EquationOfMotion (fun _ => x) ↔ Real.sin (x 0) = 0 := by
  have h1 : ∂ₜ (fun _ : Time => x) = fun _ => 0 := by
    funext s
    simp
  have he : EuclideanSpace.single (0 : Fin 1) (1 : ℝ) ≠ 0 :=
    fun h => one_ne_zero ((PiLp.single_eq_zero_iff 2 (0 : Fin 1)).mp h)
  have hc : S.m * S.g * S.ℓ ≠ 0 := (mul_pos (mul_pos S.m_pos S.g_pos) S.ℓ_pos).ne'
  simp only [EquationOfMotion, h1, Time.deriv_const, smul_zero, forall_const]
  rw [eq_comm, torque_eq, neg_eq_zero, smul_eq_zero, or_iff_left he, mul_eq_zero,
    or_iff_right hc]

/-!

## J. Energy regimes

Energy conservation divides the smooth motions of the pendulum into regimes according to the
value of the conserved energy, the threshold being the energy `2 m g ℓ` of the inverted
equilibrium. Below the threshold the potential energy cannot reach its value at the top of the
swing, so the bob never reaches the top; classically this is the regime of libration, the bob
swinging back and forth. Above the threshold the kinetic energy can never vanish, so the bob
never halts; classically this is the regime of rotation, the pendulum circulating over the top.
This is the phase portrait of the pendulum drawn in Arnold §4, whose level curves of the energy
are closed ovals below the threshold and unbounded waves above it. This section proves the
below- and above-threshold bounds characteristic of each regime, from two elementary bounds
relating the energies — the librating and rotating motions themselves are not constructed
here — and characterizes the turning points, the instants at which the velocity vanishes and
the potential energy exhausts the total energy.

-/

/-!

### J.1. The separatrix energy

The threshold between the regimes is the energy of the inverted equilibrium: no kinetic energy,
and the potential energy `2 m g ℓ` of the top of the swing. It is called the separatrix energy
after the curve it names in the phase portrait, the level set of the energy separating the
closed orbits of libration from the unbounded orbits of rotation. Only the threshold value is
used in this file: the separatrix motions themselves — the non-constant solutions asymptotic to
the inverted equilibrium — are not constructed here.

-/

/-- The separatrix energy of the simple pendulum is `2 m g ℓ`, the energy of the inverted
  equilibrium. It is the threshold separating the two regimes of the motion, libration below it
  and rotation above it. -/
def separatrixEnergy : ℝ := 2 * (S.m * S.g * S.ℓ)

/-- The separatrix energy of the simple pendulum, written out. -/
lemma separatrixEnergy_eq : S.separatrixEnergy = 2 * (S.m * S.g * S.ℓ) := rfl

/-- The separatrix energy of the simple pendulum is positive. -/
lemma separatrixEnergy_pos : 0 < S.separatrixEnergy :=
  mul_pos two_pos (mul_pos (mul_pos S.m_pos S.g_pos) S.ℓ_pos)

/-- The energy of the simple pendulum along the inverted equilibrium is the separatrix energy:
  the bob balanced at the top has no kinetic energy and the full potential energy `2 m g ℓ`. -/
lemma energy_const_pi :
    S.energy (fun _ => EuclideanSpace.single 0 Real.pi) = fun _ => S.separatrixEnergy := by
  funext t
  simp only [energy_eq, kineticEnergy_eq, Time.deriv_const, inner_zero_left, mul_zero,
    zero_add, potentialEnergy_eq, separatrixEnergy_eq, PiLp.single_apply, reduceIte, Real.cos_pi]
  ring

/-!

### J.2. Energy bounds

Two elementary bounds drive the regime theorems: the kinetic energy is non-negative, so the
potential energy is at most the total energy; and the potential energy is non-negative, so
`I θ̇²` is at most twice the total energy. None of the bounds of this subsection uses the
equation of motion — they hold along every lift of the angle.

-/

/-- The kinetic energy of the simple pendulum is non-negative along every lift of the angle. -/
lemma kineticEnergy_nonneg (θ : Time → EuclideanSpace ℝ (Fin 1)) (t : Time) :
    0 ≤ S.kineticEnergy θ t := by
  simp only [kineticEnergy_eq]
  exact mul_nonneg (mul_nonneg (by norm_num) S.inertia_pos.le) real_inner_self_nonneg

/-- The moment of inertia times the square of the angular speed, `I θ̇²`, is at most twice the
  total energy, along every lift of the angle. -/
lemma inertia_mul_inner_deriv_le (θ : Time → EuclideanSpace ℝ (Fin 1)) (t : Time) :
    S.inertia * ⟪∂ₜ θ t, ∂ₜ θ t⟫_ℝ ≤ 2 * S.energy θ t := by
  have hV := S.potentialEnergy_nonneg (θ t)
  have hE : S.energy θ t = (1 / (2 : ℝ)) * S.inertia * ⟪∂ₜ θ t, ∂ₜ θ t⟫_ℝ
      + S.potentialEnergy (θ t) := by
    rw [energy_eq, kineticEnergy_eq]
  linarith

/-- The potential energy of the simple pendulum is at most the total energy along every lift of
  the angle. -/
lemma potentialEnergy_le_energy (θ : Time → EuclideanSpace ℝ (Fin 1)) (t : Time) :
    S.potentialEnergy (θ t) ≤ S.energy θ t := by
  have hK := S.kineticEnergy_nonneg θ t
  have hE : S.energy θ t = S.kineticEnergy θ t + S.potentialEnergy (θ t) := by
    rw [energy_eq]
  linarith

/-!

### J.3. Libration and rotation

Along a smooth solution with energy below the separatrix energy, the potential energy — being
at most the conserved total energy — stays strictly below `2 m g ℓ`, so the cosine of the angle
stays strictly above `-1`: the bob never reaches the top of the swing, and the motion is a
libration, swinging back and forth — though only the bound is proved here. Along a smooth
solution with energy above the separatrix energy the angular velocity can never vanish, for at
such an instant the whole energy would be potential, and the potential energy never exceeds
`2 m g ℓ`; the velocity being continuous, it keeps a fixed sign, and the motion is a rotation
over the top — though only the non-vanishing is proved here.

-/

/-- Libration: along a smooth lift of the angle satisfying the equation of motion, with energy
  below the separatrix energy, the cosine of the angle stays strictly above `-1` — the bob
  never reaches the top of the swing. -/
lemma neg_one_lt_cos_of_energy_lt (θ : Time → EuclideanSpace ℝ (Fin 1))
    (hθ : ContDiff ℝ ∞ θ) (h : S.EquationOfMotion θ)
    (hE : S.energy θ 0 < S.separatrixEnergy) (t : Time) : -1 < Real.cos (θ t 0) := by
  have hc : 0 < S.m * S.g * S.ℓ := mul_pos (mul_pos S.m_pos S.g_pos) S.ℓ_pos
  have hV : S.m * S.g * S.ℓ * (1 - Real.cos (θ t 0)) < 2 * (S.m * S.g * S.ℓ) := by
    rw [← S.potentialEnergy_eq (θ t), ← S.separatrixEnergy_eq]
    calc S.potentialEnergy (θ t) ≤ S.energy θ t := S.potentialEnergy_le_energy θ t
      _ = S.energy θ 0 := S.energy_conservation_of_equationOfMotion' θ hθ h t
      _ < S.separatrixEnergy := hE
  nlinarith [hV, hc]

/-- Rotation: along a smooth lift of the angle satisfying the equation of motion, with energy
  above the separatrix energy, the angular velocity never vanishes — the bob never halts. -/
lemma deriv_ne_zero_of_energy_gt (θ : Time → EuclideanSpace ℝ (Fin 1))
    (hθ : ContDiff ℝ ∞ θ) (h : S.EquationOfMotion θ)
    (hE : S.separatrixEnergy < S.energy θ 0) (t : Time) : ∂ₜ θ t ≠ 0 := by
  intro h0
  have hK : S.kineticEnergy θ t = 0 := by
    simp only [kineticEnergy_eq]
    simp [h0]
  have ht : S.energy θ t = S.kineticEnergy θ t + S.potentialEnergy (θ t) := by
    rw [energy_eq]
  have hle := S.potentialEnergy_le (θ t)
  have hcons := S.energy_conservation_of_equationOfMotion' θ hθ h t
  have hsep : S.separatrixEnergy = 2 * (S.m * S.g * S.ℓ) := S.separatrixEnergy_eq
  linarith

/-!

### J.4. Turning points

At an instant where the angular velocity vanishes the kinetic energy vanishes with it, and the
conserved total energy is purely potential. These are the turning points of the motion, where a
librating bob halts at the extremes of its arc before swinging back; by the rotation theorem of
J.3 they can occur only at energies not above the separatrix energy.

-/

/-- Turning points: along a smooth lift of the angle satisfying the equation of motion, at an
  instant where the angular velocity vanishes, the potential energy equals the conserved total
  energy. -/
lemma potentialEnergy_eq_energy_of_deriv_eq_zero (θ : Time → EuclideanSpace ℝ (Fin 1))
    (hθ : ContDiff ℝ ∞ θ) (h : S.EquationOfMotion θ) (t : Time) (h0 : ∂ₜ θ t = 0) :
    S.potentialEnergy (θ t) = S.energy θ 0 := by
  have hK : S.kineticEnergy θ t = 0 := by
    simp only [kineticEnergy_eq]
    simp [h0]
  have ht : S.energy θ t = S.kineticEnergy θ t + S.potentialEnergy (θ t) := by
    rw [energy_eq]
  have hcons := S.energy_conservation_of_equationOfMotion' θ hθ h t
  linarith

/-!

## K. Independence of the lift

The dynamics of this file are written on a lift of the motion: the real angle `θ t 0` stands for
the configuration `ConfigurationSpace.ofAngle (θ t 0)`, and two lifts differing by a whole
number of turns carry the same configurations. This section proves that the dynamical
quantities listed below — the energies, the torque, and the equation of motion and its
solutions — are invariant under the deck transformations `θ ↦ θ + 2π n` of the angular lift;
the packaging of this invariance at the level of configuration-space trajectories comes with
the geometric bridge in a later module. The section closes by making the starting point
precise: the shifted lift does describe the same configuration, by the periodicity of the
angular lift of the geometric configuration space.

-/

/-!

### K.1. Invariance of the potential energy and the torque

The potential energy and the torque depend on the angle only through its cosine and its sine,
and both have period `2π`: neither quantity changes when the angle is shifted by a whole number
of turns.

-/

/-- The potential energy of the simple pendulum is invariant under shifting the angle by a
  whole number of turns. -/
lemma potentialEnergy_add_int_mul_two_pi (x : EuclideanSpace ℝ (Fin 1)) (n : ℤ) :
    S.potentialEnergy (x + (n * (2 * Real.pi)) • EuclideanSpace.single 0 1) =
      S.potentialEnergy x := by
  have h0 : (x + (n * (2 * Real.pi)) • EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 1)) 0 =
      x 0 + n * (2 * Real.pi) := by
    simp
  rw [potentialEnergy_eq, potentialEnergy_eq, h0, Real.cos_add_int_mul_two_pi]

/-- The torque of the simple pendulum is invariant under shifting the angle by a whole number
  of turns. -/
lemma torque_add_int_mul_two_pi (x : EuclideanSpace ℝ (Fin 1)) (n : ℤ) :
    S.torque (x + (n * (2 * Real.pi)) • EuclideanSpace.single 0 1) = S.torque x := by
  have h0 : (x + (n * (2 * Real.pi)) • EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 1)) 0 =
      x 0 + n * (2 * Real.pi) := by
    simp
  rw [torque_eq, torque_eq, h0, Real.sin_add_int_mul_two_pi]

/-!

### K.2. Invariance of the energy

The shift of the lift is constant in time, so it drops out of the velocity, and the kinetic
energy is unchanged by any constant shift at all; the potential energy is unchanged by the
invariance of K.1. Together the two give the invariance of the energy under shifting the lift
by a whole number of turns.

-/

/-- The kinetic energy of the simple pendulum along a lift of the angle is invariant under
  shifting the lift by any constant: the shift drops out of the velocity. -/
lemma kineticEnergy_add_const (θ : Time → EuclideanSpace ℝ (Fin 1))
    (c : EuclideanSpace ℝ (Fin 1)) :
    S.kineticEnergy (fun t => θ t + c) = S.kineticEnergy θ := by
  have hd : ∂ₜ (fun t => θ t + c) = ∂ₜ θ := by
    funext s
    rw [Time.deriv_eq, Time.deriv_eq, fderiv_add_const]
  funext t
  simp only [kineticEnergy_eq, hd]

/-- The energy of the simple pendulum along a lift of the angle is invariant under shifting the
  lift by a whole number of turns: K.1 supplies the invariance of the potential energy, and the
  velocity is unchanged by a constant shift. -/
lemma energy_add_int_mul_two_pi (θ : Time → EuclideanSpace ℝ (Fin 1)) (n : ℤ) :
    S.energy (fun t => θ t + (n * (2 * Real.pi)) • EuclideanSpace.single 0 1) =
      S.energy θ := by
  funext t
  simp only [energy_eq, S.kineticEnergy_add_const θ _, S.potentialEnergy_add_int_mul_two_pi (θ t) n]

/-!

### K.3. Invariance of the equation of motion and its solutions

Both sides of the equation of motion are invariant under the shift: the angular momentum,
because the shift is constant in time, and the torque, by the invariance of K.1. Smoothness is
likewise unaffected by adding a constant, so being a solution is invariant as well.

-/

/-- A lift of the angle shifted by a whole number of turns satisfies the equation of motion of
  the simple pendulum if and only if the lift itself does. -/
lemma equationOfMotion_add_int_mul_two_pi (θ : Time → EuclideanSpace ℝ (Fin 1)) (n : ℤ) :
    S.EquationOfMotion (fun t => θ t + (n * (2 * Real.pi)) • EuclideanSpace.single 0 1) ↔
      S.EquationOfMotion θ := by
  have hd : ∂ₜ (fun t => θ t + (n * (2 * Real.pi)) • EuclideanSpace.single 0 1) = ∂ₜ θ := by
    funext s
    rw [Time.deriv_eq, Time.deriv_eq, fderiv_add_const]
  simp only [EquationOfMotion, hd, torque_add_int_mul_two_pi]

/-- A lift of the angle shifted by a whole number of turns is a solution of the simple pendulum
  if and only if the lift itself is. -/
lemma isSolution_add_int_mul_two_pi (θ : Time → EuclideanSpace ℝ (Fin 1)) (n : ℤ) :
    S.IsSolution (fun t => θ t + (n * (2 * Real.pi)) • EuclideanSpace.single 0 1) ↔
      S.IsSolution θ := by
  have hcd : ContDiff ℝ ∞ (fun t => θ t + (n * (2 * Real.pi)) • EuclideanSpace.single 0 1) ↔
      ContDiff ℝ ∞ θ := by
    constructor
    · intro h
      have h2 := h.sub (contDiff_const (c := (n * (2 * Real.pi)) • EuclideanSpace.single 0 1))
      simpa using h2
    · exact fun h => h.add contDiff_const
  exact and_congr hcd (S.equationOfMotion_add_int_mul_two_pi θ n)

/-!

### K.4. The shifted lift describes the same configuration

Finally the statement giving the previous invariances their meaning: the lift and its shift by
a whole number of turns project to the same point of the configuration space, by the
periodicity of the angular lift `ConfigurationSpace.ofAngle` with period `2π`.

-/

/-- A lift of the angle and its shift by a whole number of turns describe the same
  configuration of the simple pendulum. -/
lemma ofAngle_add_int_mul_two_pi_coord (x : EuclideanSpace ℝ (Fin 1)) (n : ℤ) :
    ConfigurationSpace.ofAngle
        ((x + (n * (2 * Real.pi)) • EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) 0) =
      ConfigurationSpace.ofAngle (x 0) := by
  have h0 : (x + (n * (2 * Real.pi)) • EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 1)) 0 =
      x 0 + n * (2 * Real.pi) := by
    simp
  rw [h0]
  exact ConfigurationSpace.ofAngle_periodic.int_mul n (x 0)

end SimplePendulum

end ClassicalMechanics

end
