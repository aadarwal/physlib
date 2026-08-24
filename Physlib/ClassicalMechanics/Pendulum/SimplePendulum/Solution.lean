/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.ClassicalMechanics.Pendulum.SimplePendulum.Basic
public import Mathlib.Analysis.ODE.ExistUnique
/-!

# Existence and uniqueness of the solutions of the simple pendulum

## i. Overview

The equation of motion of the simple pendulum, `θ̈ + ω² sin θ = 0`, is nonlinear, and unlike the
harmonic oscillator it has no solution in closed elementary form. Whatever is to be proved about
"the" motion of the pendulum released with a given angle and angular velocity must therefore rest
on the general theory of ordinary differential equations rather than on an explicit formula. This
module supplies that foundation: two smooth solutions of the equation of motion with the same
initial angle and the same initial angular velocity coincide for all time, and for any initial
angle and angular velocity there is a solution on some interval of time about the initial instant.

The argument is the one used for the damped harmonic oscillator. The second-order equation is
rewritten as the first-order system `(θ, θ̇)' = (θ̇, -ω² sin θ)` on the phase space, whose
right-hand side, the phase-space vector field of the pendulum, is globally Lipschitz because `sin`
is. The global uniqueness theorem for Lipschitz first-order systems, Mathlib's
`ODE_solution_unique_univ`, then gives the uniqueness. The uniqueness is global in time and does
not depend on the size of the motion: it holds for librations and rotations alike. Existence comes
from the Picard–Lindelöf theorem applied to the same first-order system, the phase-space vector
field being smooth; the theorem is local, and so is the statement proved here.

The equation of motion contains no first derivative of the angle: there is no damping. Reversing
the direction of time therefore carries solutions to solutions, and combined with uniqueness this
shows that a pendulum released from rest retraces its path, the angle being an even function of
the time since release.

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
- `SimplePendulum.isSolution_comp_neg` proves that the time reversal `t ↦ θ (-t)` of a solution
  is a solution, and `SimplePendulum.releasedFromRest_even` that a solution released from rest is
  an even function of time.
- `SimplePendulum.exists_local_solution` proves, from the Picard–Lindelöf theorem, that for any
  initial angle and angular velocity there is a curve with that initial data satisfying the
  equation of motion at all times within some `ε > 0` of the initial instant.

## iii. Table of contents

- A. The phase-space vector field
  - A.1. The definition of the vector field
  - A.2. The Lipschitz bound
- B. The phase curve of a solution
  - B.1. The angular acceleration along a solution
  - B.2. The phase curve as an integral curve
- C. Uniqueness of the solutions
- D. Time-reversal symmetry
  - D.1. The derivative under time reversal
  - D.2. Time reversal of solutions
  - D.3. Motions released from rest
- E. Local existence
  - E.1. Smoothness of the phase-space vector field
  - E.2. Curves on `Time` from curves on `ℝ`
  - E.3. Local existence of solutions

## iv. References

References for the existence and uniqueness of the motions of the pendulum include:
- Landau & Lifshitz, Mechanics, 3rd ed., §11, for motion in one dimension.
- Arnold, Mathematical Methods of Classical Mechanics, 2nd ed., §4, for the phase plane of the
  pendulum.
- Arnold, Ordinary Differential Equations, Chapter 4 (Proofs of the main theorems), for the
  existence and uniqueness theorem by Picard iteration.

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

/-!

## D. Time-reversal symmetry

The equation of motion `I θ̈ = τ(θ)` is of second order and contains no first derivative of the
angle: there is no damping. Under the reversal of time `t ↦ -t` the angular velocity changes sign
and the angular acceleration does not, so the reversed curve `t ↦ θ (-t)` of a solution is again a
solution. Together with the uniqueness of section C this has a physical consequence: a pendulum
released from rest at the instant `0` retraces its path, the angle at time `-t` being the angle at
time `t`. The chain rule for `∂ₜ` under the reflection of `Time` is stated first; it is a general
fact about `Time.deriv` and a candidate for promotion to `Physlib.SpaceAndTime.Time.Derivatives`.

-/

/-!

### D.1. The derivative under time reversal

-/

/-- The chain rule for the time derivative under the reversal of time: the derivative of
  `t ↦ f (-t)` at `t` is minus the derivative of `f` at `-t`. A general fact about `Time.deriv`,
  stated here for the time reversal of solutions; a candidate for promotion to
  `Physlib.SpaceAndTime.Time.Derivatives`. -/
lemma deriv_comp_neg {M : Type} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (f : Time → M) (t : Time) (hf : DifferentiableAt ℝ f (-t)) :
    ∂ₜ (fun s => f (-s)) t = -∂ₜ f (-t) := by
  have hneg : HasFDerivAt (fun s : Time => -s) (-ContinuousLinearMap.id ℝ Time) t :=
    (hasFDerivAt_id t).neg
  have h : HasFDerivAt (fun s => f (-s))
      ((fderiv ℝ f (-t)).comp (-ContinuousLinearMap.id ℝ Time)) t :=
    hf.hasFDerivAt.comp t hneg
  rw [Time.deriv_eq, Time.deriv_eq, h.fderiv]
  simp

/-- The second derivative is unchanged by the reversal of time: for a smooth curve `f`, the second
  derivative of `t ↦ f (-t)` at `t` is the second derivative of `f` at `-t`, the two changes of
  sign cancelling. -/
lemma deriv_deriv_comp_neg {M : Type} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (f : Time → M) (hf : ContDiff ℝ ∞ f) (t : Time) :
    ∂ₜ (∂ₜ (fun s => f (-s))) t = ∂ₜ (∂ₜ f) (-t) := by
  have h1 : ∂ₜ (fun s => f (-s)) = fun s => -∂ₜ f (-s) := by
    funext s
    exact SimplePendulum.deriv_comp_neg f s (hf.differentiable (by simp) _)
  have h2 : ∂ₜ (fun s => -∂ₜ f (-s)) t = -∂ₜ (fun s => ∂ₜ f (-s)) t :=
    Time.deriv_neg (fun s => ∂ₜ f (-s))
  rw [h1, h2, SimplePendulum.deriv_comp_neg (∂ₜ f) t (deriv_differentiable_of_contDiff f hf _),
    neg_neg]

/-!

### D.2. Time reversal of solutions

-/

/-- The time reversal `t ↦ θ (-t)` of a solution of the simple pendulum is a solution: the
  equation of motion has no velocity term, and the angular acceleration is unchanged by the
  reversal. -/
lemma isSolution_comp_neg {S : SimplePendulum} {θ : Time → EuclideanSpace ℝ (Fin 1)}
    (h : S.IsSolution θ) : S.IsSolution (fun t => θ (-t)) := by
  refine ⟨h.contDiff.comp contDiff_neg, fun t => ?_⟩
  rw [SimplePendulum.deriv_deriv_comp_neg θ h.contDiff t]
  exact h.equationOfMotion (-t)

/-!

### D.3. Motions released from rest

-/

/-- A solution of the simple pendulum released from rest at the instant `0` is an even function
  of time: it retraces its path, `θ (-t) = θ t`. The time reversal of the solution has the same
  initial angle and, the initial angular velocity being zero, the same initial angular velocity,
  so the two coincide by uniqueness. -/
lemma releasedFromRest_even {S : SimplePendulum} {θ : Time → EuclideanSpace ℝ (Fin 1)}
    (h : S.IsSolution θ) (hv : ∂ₜ θ 0 = 0) (t : Time) : θ (-t) = θ t := by
  have h0 : (fun s => θ (-s)) 0 = θ 0 := by simp
  have hv0 : ∂ₜ (fun s => θ (-s)) 0 = ∂ₜ θ 0 := by
    rw [SimplePendulum.deriv_comp_neg θ 0 (h.contDiff.differentiable (by simp) _), neg_zero, hv,
      neg_zero]
  exact congrFun (IsSolution.eq_of_initial (isSolution_comp_neg h) h h0 hv0) t

/-!

## E. Local existence

The uniqueness of section C says that a solution with given initial angle and angular velocity is
unique if it exists. Existence comes from the Picard–Lindelöf theorem, in the form Mathlib states
it for a time-independent `C¹` vector field: the field admits an integral curve through any point,
defined on an open interval about the initial instant. Applied to the phase-space vector field of
the pendulum, which is smooth, this gives a curve `(θ, θ̇)` in the phase space through the initial
data, and its first component is the required angle. Mathlib's curve is parametrised by `ℝ`, so it
is pulled back to `Time` through `Time.toRealCLE`; the derivative of the pulled-back curve is read
off through the converse of the bridge lemma `Time.hasDerivAt_comp_toRealCLE_symm`.

The statement is local: the equation of motion is proved for the times within `ε` of the initial
instant, for some `ε > 0`, and nothing is claimed about the curve outside that interval. Global
existence, which follows from the global Lipschitz bound of section A, is not proved here.

-/

/-!

### E.1. Smoothness of the phase-space vector field

-/

/-- The phase-space vector field of the simple pendulum is smooth: its components are the
  projection onto the angular velocity and `sin` of the angle. -/
@[fun_prop]
lemma phaseVectorField_contDiff (n : WithTop ℕ∞) : ContDiff ℝ n S.phaseVectorField := by
  unfold phaseVectorField
  fun_prop

/-!

### E.2. Curves on `Time` from curves on `ℝ`

-/

/-- The converse of the bridge `Time.hasDerivAt_comp_toRealCLE_symm`: if the curve `γ : ℝ → M`
  has derivative `v` at `toRealCLE t`, then the curve `t ↦ γ (toRealCLE t)` on `Time` has time
  derivative `v` at `t`. A general fact about `Time.deriv` and a candidate for promotion to
  `Physlib.SpaceAndTime.Time.Derivatives`. -/
lemma deriv_comp_toRealCLE_of_hasDerivAt {M : Type} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (γ : ℝ → M) (t : Time) (v : M) (h : HasDerivAt γ v (Time.toRealCLE t)) :
    ∂ₜ (fun s => γ (Time.toRealCLE s)) t = v := by
  have h' : HasFDerivAt (fun s => γ (Time.toRealCLE s))
      (((1 : ℝ →L[ℝ] ℝ).smulRight v).comp (Time.toRealCLE : Time →L[ℝ] ℝ)) t :=
    h.hasFDerivAt.comp t Time.toRealCLE.hasFDerivAt
  rw [Time.deriv_eq, h'.fderiv]
  change Time.toRealCLE 1 • v = v
  change (1 : Time).val • v = v
  rw [Time.one_val, one_smul]

/-!

### E.3. Local existence of solutions

-/

/-- The pointwise equation of motion in terms of the angular frequency: the moment of inertia
  times the acceleration `-ω² sin θ` is the torque. -/
lemma inertia_smul_eq_torque (x : EuclideanSpace ℝ (Fin 1)) :
    S.inertia • (-(S.ω ^ 2 * Real.sin (x 0)) • EuclideanSpace.single 0 1) = S.torque x := by
  rw [torque_eq, smul_smul, ← neg_smul]
  congr 1
  rw [← S.ω_sq_mul_inertia]
  ring

/-- **Local existence** of solutions of the simple pendulum: for any initial angle `x₀` and
  angular velocity `v₀` there are `ε > 0` and a curve `θ` with `θ 0 = x₀` and `∂ₜ θ 0 = v₀`
  satisfying the equation of motion at every time within `ε` of the initial instant. This is the
  Picard–Lindelöf theorem applied to the phase-space vector field, the first component of the
  integral curve through `(x₀, v₀)` being the angle. -/
lemma exists_local_solution (x₀ v₀ : EuclideanSpace ℝ (Fin 1)) :
    ∃ ε > (0 : ℝ), ∃ θ : Time → EuclideanSpace ℝ (Fin 1), θ 0 = x₀ ∧ ∂ₜ θ 0 = v₀ ∧
      ∀ t : Time, |t.val| ≤ ε → S.inertia • ∂ₜ (∂ₜ θ) t = S.torque (θ t) := by
  obtain ⟨α, hα0, ε, hε, hα⟩ :=
    ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀
      ((S.phaseVectorField_contDiff 1).contDiffAt (x := (x₀, v₀))) 0
  have hmem : ∀ t : Time, |t.val| ≤ ε / 2 → Time.toRealCLE t ∈ Set.Ioo (0 - ε) (0 + ε) := by
    intro t ht
    have := abs_le.mp ht
    change t.val ∈ Set.Ioo (0 - ε) (0 + ε)
    constructor <;> linarith
  have hd1 : ∀ t : Time, Time.toRealCLE t ∈ Set.Ioo (0 - ε) (0 + ε) →
      ∂ₜ (fun s => (α (Time.toRealCLE s)).1) t = (α (Time.toRealCLE t)).2 := by
    intro t ht
    have hαt := hα _ ht
    have hfst := (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin 1))
      (EuclideanSpace ℝ (Fin 1))).hasFDerivAt.comp_hasDerivAt (Time.toRealCLE t) hαt
    apply deriv_comp_toRealCLE_of_hasDerivAt (fun τ => (α τ).1) t
    simpa [Function.comp_def, phaseVectorField] using hfst
  have hd2 : ∀ t : Time, Time.toRealCLE t ∈ Set.Ioo (0 - ε) (0 + ε) →
      ∂ₜ (∂ₜ (fun s => (α (Time.toRealCLE s)).1)) t =
        (S.phaseVectorField (α (Time.toRealCLE t))).2 := by
    intro t ht
    have hαt := hα _ ht
    have hU : IsOpen {s : Time | Time.toRealCLE s ∈ Set.Ioo (0 - ε) (0 + ε)} :=
      isOpen_Ioo.preimage Time.toRealCLE.continuous
    have hev : ∂ₜ (fun s => (α (Time.toRealCLE s)).1) =ᶠ[nhds t]
        fun s => (α (Time.toRealCLE s)).2 :=
      Filter.eventuallyEq_of_mem (hU.mem_nhds ht) fun s hs => hd1 s hs
    have h2 : ∂ₜ (fun s => (α (Time.toRealCLE s)).2) t =
        (S.phaseVectorField (α (Time.toRealCLE t))).2 := by
      have hsnd := (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin 1))
        (EuclideanSpace ℝ (Fin 1))).hasFDerivAt.comp_hasDerivAt (Time.toRealCLE t) hαt
      apply deriv_comp_toRealCLE_of_hasDerivAt (fun τ => (α τ).2) t
      simpa [Function.comp_def] using hsnd
    rw [Time.deriv_eq, hev.fderiv_eq, ← Time.deriv_eq, h2]
  have h0 : Time.toRealCLE (0 : Time) ∈ Set.Ioo (0 - ε) (0 + ε) := by
    rw [map_zero]
    constructor <;> linarith
  refine ⟨ε / 2, half_pos hε, fun t => (α (Time.toRealCLE t)).1, ?_, ?_, ?_⟩
  · show (α (Time.toRealCLE 0)).1 = x₀
    rw [map_zero, hα0]
  · rw [hd1 0 h0, map_zero, hα0]
  · intro t ht
    rw [hd2 t (hmem t ht)]
    exact S.inertia_smul_eq_torque _

end SimplePendulum

end ClassicalMechanics
