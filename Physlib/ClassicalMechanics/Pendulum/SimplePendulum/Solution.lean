/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.ClassicalMechanics.Pendulum.SimplePendulum.Basic
public import Mathlib.Analysis.ODE.ExistUnique
/-!

# Uniqueness of the solutions of the simple pendulum

## i. Overview

The equation of motion of the simple pendulum, `θ̈ + ω² sin θ = 0`, is nonlinear, and unlike the
harmonic oscillator it has no solution in closed elementary form. Whatever is to be proved about
"the" motion of the pendulum released with a given angle and angular velocity must therefore rest
on the general theory of ordinary differential equations rather than on an explicit formula. This
module supplies the uniqueness half of that foundation: two smooth solutions of the equation of
motion with the same initial angle and the same initial angular velocity coincide for all time.

The argument is the one used for the damped harmonic oscillator. The second-order equation is
rewritten as the first-order system `(θ, θ̇)' = (θ̇, -ω² sin θ)` on the phase space, whose
right-hand side, the phase-space vector field of the pendulum, is globally Lipschitz because `sin`
is. The global uniqueness theorem for Lipschitz first-order systems, Mathlib's
`ODE_solution_unique_univ`, then gives the result. The uniqueness is global in time and does not
depend on the size of the motion: it holds for librations and rotations alike.

## ii. Key results

- `SimplePendulum.phaseVectorField` is the phase-space vector field `(θ, θ̇) ↦ (θ̇, -ω² sin θ)`,
  and `SimplePendulum.phaseVectorField_lipschitz` proves that it is globally Lipschitz, with
  constant `1 + ω²`.
- `SimplePendulum.acceleration_eq_of_equationOfMotion` solves the equation of motion for the
  angular acceleration, and `SimplePendulum.phaseCurve_hasDerivAt` shows that the phase curve
  `(θ, θ̇)` of a smooth solution is an integral curve of the phase-space vector field.
- `SimplePendulum.equationOfMotion_unique` proves that two smooth solutions of the equation of
  motion with the same initial angle and angular velocity are equal, and
  `SimplePendulum.IsSolution.eq_of_initial` is the same statement for solutions.

## iii. Table of contents

- A. The phase-space vector field
  - A.1. The definition of the vector field
  - A.2. The Lipschitz bound
- B. The phase curve of a solution
  - B.1. The angular acceleration along a solution
  - B.2. The phase curve as an integral curve
- C. Uniqueness of the solutions

## iv. References

References for the uniqueness of the motions of the pendulum include:
- Landau & Lifshitz, Mechanics, 3rd ed., §11, for motion in one dimension.
- Arnold, Mathematical Methods of Classical Mechanics, 2nd ed., §4, for the phase plane of the
  pendulum.

The reduction to a first-order system on the phase space follows
`DampedHarmonicOscillator.equationOfMotion_unique`.

-/

@[expose] public section

namespace ClassicalMechanics
open Real
open Time
open scoped ContDiff

namespace SimplePendulum

variable (S : SimplePendulum)

/-!

## A. The phase-space vector field

The equation of motion `θ̈ + ω² sin θ = 0` is of second order. Taking the angular velocity as a
second unknown turns it into the first-order system `(θ, θ̇)' = (θ̇, -ω² sin θ)` on the phase
space, the product of two copies of the one-dimensional Euclidean space carrying the angle and its
rate of change. The right-hand side of this system is the phase-space vector field of the
pendulum. Its first component is the projection onto the angular velocity, and its second is `ω²`
times the sine of the angle; as the derivative of `sin` is bounded by one, the field is globally
Lipschitz on the phase space. This is the hypothesis under which the general uniqueness theorem
for first-order systems applies with no restriction on the time interval or on the size of the
motion.

-/

/-!

### A.1. The definition of the vector field

-/

/-- The phase-space vector field of the simple pendulum, sending `(θ, θ̇)` to
  `(θ̇, -ω² sin θ)`. It is the right-hand side of the first-order system on the phase space
  equivalent to the equation of motion `θ̈ + ω² sin θ = 0`. -/
noncomputable def phaseVectorField (p : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) :
    EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1) :=
  (p.2, -(S.ω ^ 2 * Real.sin (p.1 0)) • EuclideanSpace.single 0 1)

/-!

### A.2. The Lipschitz bound

-/

/-- The phase-space vector field of the simple pendulum is globally Lipschitz, with constant
  `1 + ω²`: the first component is the projection onto the angular velocity, and the second is
  `ω²` times `sin` of the angle, and `sin` is Lipschitz with constant one. -/
lemma phaseVectorField_lipschitz :
    LipschitzWith (Real.toNNReal (1 + S.ω ^ 2)) S.phaseVectorField := by
  refine LipschitzWith.of_dist_le_mul fun p q => ?_
  have hω : (0 : ℝ) ≤ S.ω ^ 2 := sq_nonneg _
  have hpq : (0 : ℝ) ≤ dist p q := dist_nonneg
  have h1 : dist p.1 q.1 ≤ dist p q := by rw [Prod.dist_eq]; exact le_max_left _ _
  have h2 : dist p.2 q.2 ≤ dist p q := by rw [Prod.dist_eq]; exact le_max_right _ _
  have h3 : |p.1 0 - q.1 0| ≤ dist p.1 q.1 := by
    rw [dist_eq_norm, ← Real.norm_eq_abs, ← PiLp.sub_apply]
    exact PiLp.norm_apply_le _ _
  have hsmul : ∀ a b : ℝ, dist (a • (EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 1)))
      (b • EuclideanSpace.single 0 1) = |a - b| := by
    intro a b
    rw [dist_eq_norm, ← sub_smul, norm_smul, PiLp.norm_single, norm_one, mul_one,
      Real.norm_eq_abs]
  rw [Real.coe_toNNReal _ (by positivity), Prod.dist_eq]
  refine max_le ?_ ?_
  · show dist p.2 q.2 ≤ _
    nlinarith
  · show dist (_ • _) (_ • _) ≤ _
    rw [hsmul, neg_sub_neg, ← mul_sub, abs_mul, abs_of_nonneg hω]
    have hsin : |Real.sin (q.1 0) - Real.sin (p.1 0)| ≤ dist p q := by
      refine (Real.abs_sin_sub_sin_le _ _).trans ?_
      rw [abs_sub_comm]
      exact h3.trans h1
    nlinarith

/-!

## B. The phase curve of a solution

A smooth lift `θ` of the angle satisfying the equation of motion determines the phase curve
`t ↦ (θ t, θ̇ t)` in the phase space. Solving the equation of motion for the angular acceleration
shows that this curve is an integral curve of the phase-space vector field: its velocity at every
instant is the value of the field at its position. The curve is parametrised here by a real
variable through the canonical equivalence `Time.toRealCLE.symm : ℝ ≃L[ℝ] Time`, as the
uniqueness theorem of Mathlib is stated for curves on `ℝ`.

-/

/-!

### B.1. The angular acceleration along a solution

-/

/-- Solving the equation of motion for the angular acceleration: along a solution the second
  derivative of the angle is `-ω² sin θ` times the unit vector of the angular coordinate, the
  mass having cancelled. -/
lemma acceleration_eq_of_equationOfMotion (θ : Time → EuclideanSpace ℝ (Fin 1))
    (h : S.EquationOfMotion θ) (t : Time) :
    ∂ₜ (∂ₜ θ) t = -(S.ω ^ 2 * Real.sin (θ t 0)) • EuclideanSpace.single 0 1 := by
  have hs := (S.equationOfMotion_iff_scalar θ).mp h t
  ext i
  fin_cases i
  simpa using eq_neg_of_add_eq_zero_left hs

/-!

### B.2. The phase curve as an integral curve

-/

/-- The phase curve `τ ↦ (θ t, θ̇ t)` (with `t = toRealCLE.symm τ`) of a smooth solution `θ`
  solves the first-order phase-space ODE with vector field `phaseVectorField`. -/
lemma phaseCurve_hasDerivAt (θ : Time → EuclideanSpace ℝ (Fin 1))
    (hθ : ContDiff ℝ ∞ θ) (h : S.EquationOfMotion θ) (τ : ℝ) :
    HasDerivAt (fun τ : ℝ => (θ (Time.toRealCLE.symm τ), ∂ₜ θ (Time.toRealCLE.symm τ)))
      (S.phaseVectorField (θ (Time.toRealCLE.symm τ), ∂ₜ θ (Time.toRealCLE.symm τ))) τ := by
  simp only [phaseVectorField]
  rw [← S.acceleration_eq_of_equationOfMotion θ h (Time.toRealCLE.symm τ)]
  exact (Time.hasDerivAt_comp_toRealCLE_symm θ τ (hθ.differentiable (by simp) _)).prodMk
    (Time.hasDerivAt_comp_toRealCLE_symm (∂ₜ θ) τ (deriv_differentiable_of_contDiff θ hθ _))

/-!

## C. Uniqueness of the solutions

The phase curves of two smooth solutions with the same initial angle and angular velocity are two
integral curves of the same globally Lipschitz vector field through the same point at time zero.
By the global uniqueness theorem `ODE_solution_unique_univ` they coincide, and reading off the
first component the two solutions are equal. The energy is conserved along a solution, but it is
not used here: the nonlinear equation of motion is handled exactly as the linear damped one, by the
first-order reduction alone.

-/

/-- Any two smooth solutions of the equation of motion of the simple pendulum with the same
  initial angle and angular velocity are equal. -/
lemma equationOfMotion_unique (x y : Time → EuclideanSpace ℝ (Fin 1))
    (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y)
    (hEOMx : S.EquationOfMotion x) (hEOMy : S.EquationOfMotion y)
    (h0 : x 0 = y 0) (hv0 : ∂ₜ x 0 = ∂ₜ y 0) :
    x = y := by
  have hIC : (fun τ : ℝ => (x (Time.toRealCLE.symm τ), ∂ₜ x (Time.toRealCLE.symm τ))) 0 =
      (fun τ : ℝ => (y (Time.toRealCLE.symm τ), ∂ₜ y (Time.toRealCLE.symm τ))) 0 := by
    have h00 : Time.toRealCLE.symm (0 : ℝ) = (0 : Time) := map_zero Time.toRealCLE.symm
    simp only [h00, h0, hv0]
  have hEq := ODE_solution_unique_univ
    (v := fun _ p => S.phaseVectorField p) (s := fun _ => Set.univ) (t₀ := (0 : ℝ))
    (f := fun τ : ℝ => (x (Time.toRealCLE.symm τ), ∂ₜ x (Time.toRealCLE.symm τ)))
    (g := fun τ : ℝ => (y (Time.toRealCLE.symm τ), ∂ₜ y (Time.toRealCLE.symm τ)))
    (fun _ => S.phaseVectorField_lipschitz.lipschitzOnWith)
    (fun τ => ⟨S.phaseCurve_hasDerivAt x hx hEOMx τ, Set.mem_univ _⟩)
    (fun τ => ⟨S.phaseCurve_hasDerivAt y hy hEOMy τ, Set.mem_univ _⟩)
    hIC
  funext t
  have h1 := congrFun hEq (Time.toRealCLE t)
  simp only [ContinuousLinearEquiv.symm_apply_apply] at h1
  exact (Prod.ext_iff.mp h1).1

/-- Two solutions of the simple pendulum with the same initial angle and angular velocity are
  equal. -/
lemma IsSolution.eq_of_initial {S : SimplePendulum} {x y : Time → EuclideanSpace ℝ (Fin 1)}
    (hx : S.IsSolution x) (hy : S.IsSolution y) (h0 : x 0 = y 0) (hv0 : ∂ₜ x 0 = ∂ₜ y 0) :
    x = y :=
  S.equationOfMotion_unique x y hx.contDiff hy.contDiff hx.equationOfMotion hy.equationOfMotion
    h0 hv0

end SimplePendulum

end ClassicalMechanics
