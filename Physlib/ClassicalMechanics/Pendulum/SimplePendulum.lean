/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.ClassicalMechanics.EulerLagrange
public import Physlib.ClassicalMechanics.HamiltonsEquations
public import Physlib.ClassicalMechanics.Pendulum.Geometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Calculus.MeanValue
/-!

# The simple gravity pendulum

## i. Overview

The simple gravity pendulum is a classical mechanical system consisting of a point
mass `m` constrained to a massless rod of length `ℓ`, swinging in a vertical plane
under uniform gravity `g`.

The geometric configuration space is the circle `S¹`, formalised in
`Physlib.ClassicalMechanics.Pendulum.Geometric.Basic` and embedded into `Space 2`.
The Euler–Lagrange operator of Physlib acts on trajectories in a complete inner-product
space, so the dynamics in this file use the angular chart
`EuclideanSpace ℝ (Fin 1)`, exactly as the harmonic oscillator uses a Euclidean chart
for pedagogical dynamics. Time is Physlib `Time`.

## ii. Key results

- `SimplePendulum` contains the input data.
- `EquationOfMotion` is vanishing of the variational gradient of the action.
- `equationOfMotion_tfae` equates this with Newton’s second law, Hamilton’s equations,
  the variational principle for the action, and the Hamilton variational principle.
- Energy is conserved along solutions.

Small-angle motion is in `SmallAngle`; the exact period as an elliptic integral is in
`Period`.

## iii. Table of contents

- A. The input data
- B. Inertia and small-angle frequency
- C. Trajectories
- D. The energies
- E. Lagrangian and the equation of motion
- F. Newton’s second law
- G. Energy conservation
- H. Hamiltonian formulation
- I. Equivalences between the formulations

## iv. References

- Landau & Lifshitz, Mechanics, 3rd ed., §5 and §21.

-/

@[expose]
public noncomputable section

namespace ClassicalMechanics
open Real InnerProductSpace MeasureTheory Time
open scoped ContDiff Gradient

TODO "Develop the Euler–Lagrange equation intrinsically on the tangent bundle of
    `ConfigurationSpace` (the circle), and prove that the Euclidean chart used here is
    the corresponding local coordinate description."

/-!
## A. The input data
-/

/-- The simple gravity pendulum is specified by a mass `m`, a rod length `ℓ`,
  and a gravitational acceleration `g`. All three are assumed positive.
  The angle `θ` is measured from the downward vertical. -/
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

@[simp] lemma m_ne_zero : S.m ≠ 0 := S.m_pos.ne'
@[simp] lemma ℓ_ne_zero : S.ℓ ≠ 0 := S.ℓ_pos.ne'
@[simp] lemma g_ne_zero : S.g ≠ 0 := S.g_pos.ne'

/-- Position of the bob in `Space 2` for a configuration of this pendulum. -/
def toSpace (q : ConfigurationSpace) : Space 2 :=
  ConfigurationSpace.toSpace S.ℓ q

/-!
## B. Inertia and small-angle frequency
-/

/-- The moment of inertia of the bob about the pivot, `I = m ℓ²`. -/
def inertia : ℝ := S.m * S.ℓ ^ 2

lemma inertia_pos : 0 < S.inertia :=
  mul_pos S.m_pos (sq_pos_of_ne_zero S.ℓ_ne_zero)

@[simp] lemma inertia_ne_zero : S.inertia ≠ 0 := S.inertia_pos.ne'

/-- The small-angle angular frequency `ω = √(g/ℓ)`. Named `omega` rather than `ω`
  so that `ContDiff` can keep `ω` as a smoothness index. -/
noncomputable def omega : ℝ := √(S.g / S.ℓ)

lemma omega_pos : 0 < S.omega := sqrt_pos.mpr (div_pos S.g_pos S.ℓ_pos)

@[simp] lemma omega_ne_zero : S.omega ≠ 0 := S.omega_pos.ne'

lemma omega_sq : S.omega ^ 2 = S.g / S.ℓ := sq_sqrt (div_pos S.g_pos S.ℓ_pos).le

/-- The unit vector of the one-dimensional angular chart, so that `x 0 = ⟪x, S.basis⟫_ℝ`. -/
@[nolint unusedArguments]
def basis (_S : SimplePendulum) : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 1

lemma inner_basis (x : EuclideanSpace ℝ (Fin 1)) :
    ⟪x, S.basis⟫_ℝ = x 0 := by
  simp [basis, EuclideanSpace.inner_single_right]

lemma coord_eq_inner (x : EuclideanSpace ℝ (Fin 1)) :
    x 0 = ⟪x, S.basis⟫_ℝ := (S.inner_basis x).symm

/-!
## C. Trajectories
-/

/-- A trajectory in the angular chart. Time is Physlib `Time`; the value is the
  lift of the angle to `EuclideanSpace ℝ (Fin 1)`. -/
abbrev Trajectory := Time → EuclideanSpace ℝ (Fin 1)

/-- The configuration on `S¹` along a chart trajectory. -/
def configuration (θ : Trajectory) (t : Time) : ConfigurationSpace :=
  ConfigurationSpace.ofCoord (θ t)

/-- The bob’s position in `Space 2` along a chart trajectory. -/
def spaceTrajectory (θ : Trajectory) (t : Time) : Space 2 :=
  S.toSpace (configuration θ t)

/-!
## D. The energies
-/

/-- Kinetic energy `(1/2) I ‖θ̇‖²`. -/
noncomputable def kineticEnergy (θ : Trajectory) : Time → ℝ := fun t =>
  (1 / (2 : ℝ)) * S.inertia * ⟪∂ₜ θ t, ∂ₜ θ t⟫_ℝ

/-- Potential energy, zero at the bottom `θ = 0`. -/
noncomputable def potentialEnergy (x : EuclideanSpace ℝ (Fin 1)) : ℝ :=
  S.m * S.g * S.ℓ * (1 - Real.cos (x 0))

/-- Mechanical energy `T + V`. -/
noncomputable def energy (θ : Trajectory) : Time → ℝ := fun t =>
  S.kineticEnergy θ t + S.potentialEnergy (θ t)

lemma kineticEnergy_eq (θ : Trajectory) :
    S.kineticEnergy θ = fun t => (1 / (2 : ℝ)) * S.inertia * ⟪∂ₜ θ t, ∂ₜ θ t⟫_ℝ := rfl

lemma potentialEnergy_eq (x : EuclideanSpace ℝ (Fin 1)) :
    S.potentialEnergy x = S.m * S.g * S.ℓ * (1 - Real.cos (x 0)) := rfl

@[fun_prop]
lemma potentialEnergy_contDiff (n : WithTop ℕ∞) : ContDiff ℝ n S.potentialEnergy := by
  unfold potentialEnergy
  fun_prop

@[fun_prop]
lemma differentiable_potentialEnergy : Differentiable ℝ S.potentialEnergy :=
  (S.potentialEnergy_contDiff 1).differentiable one_ne_zero

private lemma gradient_add_const' {f : EuclideanSpace ℝ (Fin 1) → ℝ} {c : ℝ}
    (x : EuclideanSpace ℝ (Fin 1)) :
    gradient (fun y => f y + c) x = gradient f x :=
  congrArg (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin 1))).symm (fderiv_add_const c)

lemma hasFDerivAt_coord (x : EuclideanSpace ℝ (Fin 1)) :
    HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 1) => y 0)
      (innerSL ℝ S.basis) x := by
  have h : (fun y : EuclideanSpace ℝ (Fin 1) => y 0) = fun y => ⟪S.basis, y⟫_ℝ := by
    funext y; rw [real_inner_comm]; exact S.coord_eq_inner y
  rw [h]
  simpa using (innerSL ℝ S.basis).hasFDerivAt

lemma gradient_cos_coord (x : EuclideanSpace ℝ (Fin 1)) :
    gradient (fun y : EuclideanSpace ℝ (Fin 1) => Real.cos (y 0)) x =
      -Real.sin (x 0) • S.basis := by
  have hfun : (fun y : EuclideanSpace ℝ (Fin 1) => Real.cos (y 0)) =
      Real.cos ∘ fun y => y 0 := rfl
  have hf := (hasDerivAt_cos (x 0)).hasFDerivAt.comp x (S.hasFDerivAt_coord x)
  refine ext_inner_right (𝕜 := ℝ) fun y => ?_
  unfold gradient
  rw [hfun, InnerProductSpace.toDual_symm_apply, hf.fderiv]
  simp [real_inner_smul_left, basis, EuclideanSpace.inner_single_left]
  ring

lemma gradient_potentialEnergy (x : EuclideanSpace ℝ (Fin 1)) :
    gradient S.potentialEnergy x = (S.m * S.g * S.ℓ * Real.sin (x 0)) • S.basis := by
  have h' : (fun y : EuclideanSpace ℝ (Fin 1) => S.potentialEnergy y) =
      fun y => (-(S.m * S.g * S.ℓ)) * Real.cos (y 0) + (S.m * S.g * S.ℓ) := by
    funext y; simp [potentialEnergy]; ring
  change gradient (fun y : EuclideanSpace ℝ (Fin 1) => S.potentialEnergy y) x = _
  rw [h', gradient_add_const']
  unfold gradient
  rw [fderiv_const_mul (by fun_prop) (-(S.m * S.g * S.ℓ)), map_smul]
  change (-(S.m * S.g * S.ℓ)) • gradient (fun y : EuclideanSpace ℝ (Fin 1) => Real.cos (y 0)) x =
    (S.m * S.g * S.ℓ * Real.sin (x 0)) • S.basis
  rw [S.gradient_cos_coord]
  module

/-!
## E. Lagrangian and the equation of motion
-/

set_option linter.unusedVariables false in
/-- The Lagrangian `L(t, θ, θ̇) = (1/2) I ‖θ̇‖² − V(θ)`. -/
@[nolint unusedArguments]
noncomputable def lagrangian (t : Time) (x v : EuclideanSpace ℝ (Fin 1)) : ℝ :=
  (1 / (2 : ℝ)) * S.inertia * ⟪v, v⟫_ℝ - S.potentialEnergy x

lemma lagrangian_eq :
    S.lagrangian = fun _ x v =>
      (1 / (2 : ℝ)) * S.inertia * ⟪v, v⟫_ℝ - S.m * S.g * S.ℓ * (1 - Real.cos (x 0)) := by
  funext t x v
  simp [lagrangian, potentialEnergy]

@[fun_prop]
lemma contDiff_lagrangian (n : WithTop ℕ∞) : ContDiff ℝ n ↿S.lagrangian := by
  rw [lagrangian_eq]
  fun_prop

lemma gradient_lagrangian_position_eq (t : Time) (x v : EuclideanSpace ℝ (Fin 1)) :
    gradient (fun x => S.lagrangian t x v) x = -((S.m * S.g * S.ℓ * Real.sin (x 0)) • S.basis) := by
  have h : (fun y : EuclideanSpace ℝ (Fin 1) => S.lagrangian t y v) =
      fun y => (-1) * S.potentialEnergy y +
        ((1 / (2 : ℝ)) * S.inertia * ⟪v, v⟫_ℝ) := by
    funext y; simp [lagrangian]; ring
  rw [h, gradient_add_const']
  unfold gradient
  rw [fderiv_const_mul (by fun_prop) (-1), map_smul]
  change (-1 : ℝ) • gradient S.potentialEnergy x =
    -((S.m * S.g * S.ℓ * Real.sin (x 0)) • S.basis)
  rw [S.gradient_potentialEnergy]
  module

lemma gradient_inner_self (x : EuclideanSpace ℝ (Fin 1)) :
    gradient (fun y : EuclideanSpace ℝ (Fin 1) => ⟪y, y⟫_ℝ) x = (2 : ℝ) • x := by
  refine ext_inner_right (𝕜 := ℝ) fun y => ?_
  unfold gradient
  rw [InnerProductSpace.toDual_symm_apply,
    fderiv_inner_apply (𝕜 := ℝ) differentiableAt_fun_id differentiableAt_fun_id]
  simp [real_inner_comm, inner_smul_right, two_mul]

lemma gradient_const_mul_inner_self (c : ℝ) (x : EuclideanSpace ℝ (Fin 1)) :
    gradient (fun y : EuclideanSpace ℝ (Fin 1) => c * ⟪y, y⟫_ℝ) x = (2 * c) • x := by
  unfold gradient
  rw [fderiv_const_mul (by fun_prop) c, map_smul]
  show c • gradient (fun y : EuclideanSpace ℝ (Fin 1) => ⟪y, y⟫_ℝ) x = (2 * c) • x
  rw [gradient_inner_self, smul_smul, mul_comm]

lemma gradient_lagrangian_velocity_eq (t : Time) (x v : EuclideanSpace ℝ (Fin 1)) :
    gradient (S.lagrangian t x) v = S.inertia • v := by
  have h : (fun y : EuclideanSpace ℝ (Fin 1) => S.lagrangian t x y) =
      fun y => ((1 / (2 : ℝ)) * S.inertia) * ⟪y, y⟫_ℝ + (-S.potentialEnergy x) := by
    funext y; simp [lagrangian]; ring
  change gradient (fun y : EuclideanSpace ℝ (Fin 1) => S.lagrangian t x y) v = S.inertia • v
  rw [h, gradient_add_const', gradient_const_mul_inner_self]
  module

/-- The variational derivative of the action. -/
noncomputable def gradLagrangian (θ : Trajectory) : Trajectory :=
  (δ (q':=θ), ∫ t, S.lagrangian t (q' t) (fderiv ℝ q' t 1))

lemma gradLagrangian_eq_eulerLagrangeOp (θ : Trajectory) (hq : ContDiff ℝ ∞ θ) :
    S.gradLagrangian θ = eulerLagrangeOp S.lagrangian θ := by
  rw [gradLagrangian, euler_lagrange_varGradient _ _ hq (S.contDiff_lagrangian _)]

/-- The equation of motion: the variational gradient of the action vanishes. -/
def EquationOfMotion (θ : Trajectory) : Prop := S.gradLagrangian θ = 0

lemma equationOfMotion_iff_gradLagrangian_zero (θ : Trajectory) :
    S.EquationOfMotion θ ↔ S.gradLagrangian θ = 0 := Iff.rfl

/-!
## F. Newton’s second law
-/

/-- Tangential force `- m g sin θ`, as a vector in the angular chart. -/
noncomputable def force (x : EuclideanSpace ℝ (Fin 1)) : EuclideanSpace ℝ (Fin 1) :=
  - gradient S.potentialEnergy x

lemma force_eq (x : EuclideanSpace ℝ (Fin 1)) :
    S.force x = -((S.m * S.g * S.ℓ * Real.sin (x 0)) • S.basis) := by
  simp [force, S.gradient_potentialEnergy]

lemma gradLagrangian_eq_force (θ : Trajectory) (hθ : ContDiff ℝ ∞ θ) :
    S.gradLagrangian θ = fun t => S.force (θ t) - S.inertia • ∂ₜ (∂ₜ θ) t := by
  funext t
  rw [S.gradLagrangian_eq_eulerLagrangeOp θ hθ, eulerLagrangeOp]
  simp [S.gradient_lagrangian_position_eq, S.gradient_lagrangian_velocity_eq, force,
    S.gradient_potentialEnergy, Time.deriv_smul _ S.inertia (deriv_differentiable_of_contDiff θ hθ)]

lemma equationOfMotion_iff_newtons_2nd_law (θ : Time → EuclideanSpace ℝ (Fin 1))
    (hθ : ContDiff ℝ ∞ θ) :
    S.EquationOfMotion θ ↔
      ∀ t, S.inertia • ∂ₜ (∂ₜ θ) t = S.force (θ t) := by
  rw [EquationOfMotion, S.gradLagrangian_eq_force θ hθ, funext_iff]
  simp only [Pi.zero_apply, sub_eq_zero]
  exact forall_congr' fun t => eq_comm

/-!
## G. Energy conservation
-/

@[fun_prop]
lemma kineticEnergy_differentiable (θ : Time → EuclideanSpace ℝ (Fin 1)) (hθ : ContDiff ℝ ∞ θ) :
    Differentiable ℝ (S.kineticEnergy θ) := by
  rw [kineticEnergy_eq]
  fun_prop

@[fun_prop]
lemma potentialEnergy_differentiable (θ : Time → EuclideanSpace ℝ (Fin 1)) (hθ : ContDiff ℝ ∞ θ) :
    Differentiable ℝ (fun t => S.potentialEnergy (θ t)) := by
  have : Differentiable ℝ θ := hθ.differentiable (by simp)
  fun_prop

@[fun_prop]
lemma energy_differentiable (θ : Time → EuclideanSpace ℝ (Fin 1)) (hθ : ContDiff ℝ ∞ θ) :
    Differentiable ℝ (S.energy θ) := by
  unfold energy
  fun_prop

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

lemma potentialEnergy_deriv (θ : Time → EuclideanSpace ℝ (Fin 1)) (hθ : ContDiff ℝ ∞ θ) :
    ∂ₜ (fun t => S.potentialEnergy (θ t)) =
      fun t => ⟪∂ₜ θ t, gradient S.potentialEnergy (θ t)⟫_ℝ := by
  funext t
  have hd : DifferentiableAt ℝ θ t := (hθ.differentiable (by simp)).differentiableAt
  have hV : DifferentiableAt ℝ S.potentialEnergy (θ t) :=
    (S.potentialEnergy_contDiff ∞).differentiable (by simp) (θ t)
  rw [Time.deriv_eq]
  have hf : HasFDerivAt (fun t => S.potentialEnergy (θ t)) _ t :=
    hV.hasFDerivAt.comp t hd.hasFDerivAt
  rw [hf.fderiv]
  simp [Time.deriv_eq]

lemma energy_deriv (θ : Time → EuclideanSpace ℝ (Fin 1)) (hθ : ContDiff ℝ ∞ θ) :
    ∂ₜ (S.energy θ) =
      fun t => ⟪∂ₜ θ t, S.inertia • ∂ₜ (∂ₜ θ) t + gradient S.potentialEnergy (θ t)⟫_ℝ := by
  unfold energy
  funext t
  rw [Time.deriv_eq, fderiv_fun_add (by fun_prop) (S.potentialEnergy_differentiable θ hθ t)]
  simp only [_root_.add_apply, ← Time.deriv_eq, S.kineticEnergy_deriv θ hθ,
    S.potentialEnergy_deriv θ hθ, ← inner_add_right]

lemma energy_conservation_of_equationOfMotion (θ : Trajectory) (hθ : ContDiff ℝ ∞ θ)
    (h : S.EquationOfMotion θ) : ∂ₜ (S.energy θ) = 0 := by
  rw [S.equationOfMotion_iff_newtons_2nd_law θ hθ] at h
  funext t
  rw [S.energy_deriv θ hθ]
  simp [h, force]

lemma energy_conservation_of_equationOfMotion' (θ : Trajectory) (hθ : ContDiff ℝ ∞ θ)
    (h : S.EquationOfMotion θ) (t : Time) : S.energy θ t = S.energy θ 0 := by
  apply is_const_of_fderiv_eq_zero (𝕜 := ℝ) (S.energy_differentiable θ hθ)
  intro t
  ext p
  rw [p.eq_one_smul, map_smul, ← Time.deriv_eq, S.energy_conservation_of_equationOfMotion θ hθ h]
  simp

/-!
## H. Hamiltonian formulation
-/

/-- The canonical momentum `p = ∂L/∂θ̇ = I θ̇`, as a linear equivalence between
  velocities and momenta in the angular chart. -/
noncomputable def toCanonicalMomentum (t : Time) (x : EuclideanSpace ℝ (Fin 1)) :
    EuclideanSpace ℝ (Fin 1) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 1) where
  toFun v := gradient (S.lagrangian t x ·) v
  invFun p := (1 / S.inertia) • p
  left_inv v := by
    simp [S.gradient_lagrangian_velocity_eq]
  right_inv p := by
    simp [S.gradient_lagrangian_velocity_eq, smul_smul, S.inertia_ne_zero]
  map_add' v1 v2 := by
    simp [S.gradient_lagrangian_velocity_eq]
  map_smul' c v := by
    simp [S.gradient_lagrangian_velocity_eq]
    module

lemma toCanonicalMomentum_eq (t : Time) (x v : EuclideanSpace ℝ (Fin 1)) :
    S.toCanonicalMomentum t x v = S.inertia • v :=
  S.gradient_lagrangian_velocity_eq t x v

/-- The Hamiltonian `H(t, p, θ) = p θ̇ − L`, the Legendre transform of the Lagrangian. -/
noncomputable def hamiltonian (t : Time) (p x : EuclideanSpace ℝ (Fin 1)) : ℝ :=
  ⟪p, (S.toCanonicalMomentum t x).symm p⟫_ℝ - S.lagrangian t x ((S.toCanonicalMomentum t x).symm p)

lemma hamiltonian_eq :
    S.hamiltonian = fun _ p x =>
      (1 / (2 : ℝ)) * (1 / S.inertia) * ⟪p, p⟫_ℝ + S.potentialEnergy x := by
  funext t p x
  simp only [hamiltonian, toCanonicalMomentum, lagrangian, one_div, LinearEquiv.coe_symm_mk',
    inner_smul_right, inner_smul_left, starRingEnd_apply, star_trivial]
  field_simp [S.inertia_ne_zero]
  try ring

@[fun_prop]
lemma hamiltonian_contDiff (n : WithTop ℕ∞) : ContDiff ℝ n ↿S.hamiltonian := by
  rw [hamiltonian_eq]
  fun_prop

lemma gradient_hamiltonian_position_eq (t : Time) (x p : EuclideanSpace ℝ (Fin 1)) :
    gradient (S.hamiltonian t p) x = gradient S.potentialEnergy x := by
  have h : (fun y : EuclideanSpace ℝ (Fin 1) => S.hamiltonian t p y) =
      fun y => S.potentialEnergy y +
        ((1 / (2 : ℝ)) * (1 / S.inertia) * ⟪p, p⟫_ℝ) := by
    funext y; simp [hamiltonian_eq]; ring
  change gradient (fun y : EuclideanSpace ℝ (Fin 1) => S.hamiltonian t p y) x =
    gradient S.potentialEnergy x
  rw [h, gradient_add_const']

lemma gradient_hamiltonian_momentum_eq (t : Time) (x p : EuclideanSpace ℝ (Fin 1)) :
    gradient (S.hamiltonian t · x) p = (1 / S.inertia) • p := by
  have h : (fun y : EuclideanSpace ℝ (Fin 1) => S.hamiltonian t y x) =
      fun y => ((1 / (2 : ℝ)) * (1 / S.inertia)) * ⟪y, y⟫_ℝ + S.potentialEnergy x := by
    funext y; simp [hamiltonian_eq]
  change gradient (fun y : EuclideanSpace ℝ (Fin 1) => S.hamiltonian t y x) p =
    (1 / S.inertia) • p
  rw [h, gradient_add_const', gradient_const_mul_inner_self]
  module

lemma hamiltonian_eq_energy (θ : Time → EuclideanSpace ℝ (Fin 1)) :
    (fun t => S.hamiltonian t (S.toCanonicalMomentum t (θ t) (∂ₜ θ t)) (θ t)) = S.energy θ := by
  funext t
  rw [hamiltonian_eq]
  unfold energy kineticEnergy
  simp [toCanonicalMomentum_eq, norm_smul, abs_of_pos S.inertia_pos]
  field_simp [S.inertia_ne_zero]
  try ring

/-- The Hamilton-equations operator of `S.hamiltonian`, vanishing exactly on solutions of
  Hamilton's equations. -/
noncomputable def hamiltonEqOp (p θ : Trajectory) :=
  ClassicalMechanics.hamiltonEqOp (S.hamiltonian) p θ

lemma equationOfMotion_iff_hamiltonEqOp_eq_zero (θ : Trajectory) (hθ : ContDiff ℝ ∞ θ) :
    S.EquationOfMotion θ ↔
      S.hamiltonEqOp (fun t => S.toCanonicalMomentum t (θ t) (∂ₜ θ t)) θ = 0 := by
  rw [hamiltonEqOp, hamiltonEqOp_eq_zero_iff_hamiltons_equations]
  simp [S.toCanonicalMomentum_eq, S.gradient_hamiltonian_momentum_eq,
    S.gradient_hamiltonian_position_eq]
  rw [S.equationOfMotion_iff_newtons_2nd_law θ hθ]
  simp [Time.deriv_smul _ S.inertia (deriv_differentiable_of_contDiff θ hθ), force]

/-!
## I. Equivalences between the formulations
-/

lemma equationOfMotion_tfae (θ : Time → EuclideanSpace ℝ (Fin 1)) (hθ : ContDiff ℝ ∞ θ) :
    List.TFAE [S.EquationOfMotion θ,
      (∀ t, S.inertia • ∂ₜ (∂ₜ θ) t = S.force (θ t)),
      S.hamiltonEqOp (fun t => S.toCanonicalMomentum t (θ t) (∂ₜ θ t)) θ = 0,
      (δ (q':=θ), ∫ t, S.lagrangian t (q' t) (fderiv ℝ q' t 1)) = 0,
      (δ (pq':= fun t => (S.toCanonicalMomentum t (θ t) (∂ₜ θ t), θ t)),
        ∫ t, ⟪(pq' t).1, ∂ₜ (Prod.snd ∘ pq') t⟫_ℝ -
          S.hamiltonian t (pq' t).1 (pq' t).2) = 0] := by
  rw [← S.equationOfMotion_iff_hamiltonEqOp_eq_zero, ← S.equationOfMotion_iff_newtons_2nd_law]
  rw [hamiltons_equations_varGradient, euler_lagrange_varGradient]
  simp only [List.tfae_cons_self]
  rw [← S.gradLagrangian_eq_eulerLagrangeOp, ← S.equationOfMotion_iff_gradLagrangian_zero]
  simp only [List.tfae_cons_self]
  erw [← S.equationOfMotion_iff_hamiltonEqOp_eq_zero]
  simp only [List.tfae_cons_self, List.tfae_singleton]
  all_goals first
    | exact hθ
    | exact S.contDiff_lagrangian _
    | exact S.hamiltonian_contDiff _
    | (simp only [S.toCanonicalMomentum_eq]; fun_prop)

end SimplePendulum
end ClassicalMechanics

end
