/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Polarization.Linear
public import Physlib.Optics.Polarization.RelativePhase

/-!
# Ideal linear retarders

## i. Overview

This file defines an ideal linear retarder from two orthogonal Jones eigenaxes. The declared axis
is the reference principal axis and has eigenvalue one. Its orthogonal axis has eigenvalue
`exp (-I * retardance)`, so positive retardance is a phase delay under Physlib's realization
convention `Re (z * exp (I * carrierPhase))`.

This fixes a useful common-phase gauge but does not model the common propagation phase or
reference-plane delay of a physical plate. The terms “fast axis” and “slow axis” remain deferred
until the material and propagation conventions are human-certified. Unitarity and intensity
statements concern raw Jones amplitudes, not electromagnetic irradiance or modal power.

## ii. Key results

- `JonesMatrix.linearRetarderPhase`: the unit complex eigenvalue representing positive delay.
- `JonesMatrix.linearRetarder`: the spectral Jones matrix of a rotated ideal retarder.
- `JonesMatrix.linearRetarder_isUnitary`: algebraic unitarity.
- `JonesMatrix.linearRetarder_act`: decomposition in the two principal-axis components.
- `JonesMatrix.linearRetarder_act_intensity`: preservation of squared Jones intensity.

## iii. Table of contents

- A. Relative phase convention
- B. Spectral definition and entries
- C. Projector identities
- D. Structural retarder laws
- E. Action on Jones vectors

## iv. References

The construction is derived from the imported Jones-vector API and Mathlib's intrinsic
`Real.Angle` and unit-circle APIs. Physical naming and source certification remain recorded in
`tbd.md`.
-/

@[expose] public section

namespace Optics

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace JonesMatrix

/-!

## A. Relative phase convention
-/

/-- The Jones eigenvalue on the axis orthogonal to a retarder reference axis.

With the realization convention `Re (z * exp (I * carrierPhase))`, positive retardance delays the
orthogonal component relative to the reference-axis component. -/
def linearRetarderPhase (retardance : Real.Angle) : ℂ :=
  ((-retardance).toCircle : ℂ)

/-- Zero retardance has unit relative phase. -/
@[simp]
lemma linearRetarderPhase_zero : linearRetarderPhase 0 = 1 := by
  simp [linearRetarderPhase]

/-- Adding retardances multiplies their relative phase factors. -/
lemma linearRetarderPhase_add (first second : Real.Angle) :
    linearRetarderPhase (first + second) =
      linearRetarderPhase first * linearRetarderPhase second := by
  simp only [linearRetarderPhase, neg_add_rev, Real.Angle.toCircle_add, Circle.coe_mul,
    mul_comm]

/-- Negating retardance inverts its relative phase factor. -/
lemma linearRetarderPhase_neg (retardance : Real.Angle) :
    linearRetarderPhase (-retardance) = (linearRetarderPhase retardance)⁻¹ := by
  simp [linearRetarderPhase, Real.Angle.toCircle_neg, Circle.coe_inv]

/-- A retarder relative phase has complex norm one. -/
@[simp]
lemma norm_linearRetarderPhase (retardance : Real.Angle) :
    ‖linearRetarderPhase retardance‖ = 1 := by
  exact Circle.norm_coe (-retardance).toCircle

/-- Complex conjugation negates retardance. -/
lemma star_linearRetarderPhase (retardance : Real.Angle) :
    star (linearRetarderPhase retardance) = linearRetarderPhase (-retardance) := by
  rw [linearRetarderPhase_neg]
  change star (((-retardance).toCircle : ℂ)) =
    (((-retardance).toCircle : ℂ))⁻¹
  rw [← Circle.coe_inv, Circle.coe_inv_eq_conj]
  rfl

/-- A retarder relative phase multiplied by its conjugate is one. -/
lemma star_mul_linearRetarderPhase (retardance : Real.Angle) :
    star (linearRetarderPhase retardance) * linearRetarderPhase retardance = 1 := by
  rw [star_linearRetarderPhase, ← linearRetarderPhase_add]
  simp

/-- A retarder relative phase is `cos retardance - I * sin retardance`. -/
lemma linearRetarderPhase_eq_cos_sub_sin_mul_I (retardance : Real.Angle) :
    linearRetarderPhase retardance =
      (Real.Angle.cos retardance : ℂ) -
        (Real.Angle.sin retardance : ℂ) * Complex.I := by
  rw [linearRetarderPhase, Real.Angle.coe_toCircle,
    Real.Angle.cos_neg, Real.Angle.sin_neg]
  push_cast
  ring

/-- For a real retardance representative, the relative phase is `exp (-I * retardance)`. -/
lemma linearRetarderPhase_coe (retardance : ℝ) :
    linearRetarderPhase (retardance : Real.Angle) =
      Complex.exp ((-retardance : ℂ) * Complex.I) := by
  rw [linearRetarderPhase, ← Real.Angle.coe_neg, Real.Angle.toCircle_coe, Circle.coe_exp]
  norm_num

/-- Multiplication by a retarder phase shifts the realized carrier by the signed retardance.

This equation fixes the sign convention independently of circular-polarization handedness. -/
lemma linearRetarderPhase_realize_mul (z : Phasor) (retardance carrierPhase : ℝ) :
    Phasor.realize
        (linearRetarderPhase (retardance : Real.Angle) * z) carrierPhase =
      Phasor.realize z (carrierPhase - retardance) := by
  rw [Phasor.realize, Phasor.realize, linearRetarderPhase_coe]
  congr 1
  calc
    (Complex.exp ((-retardance : ℂ) * Complex.I) * z) *
        Complex.exp ((carrierPhase : ℂ) * Complex.I) =
      z * (Complex.exp ((-retardance : ℂ) * Complex.I) *
        Complex.exp ((carrierPhase : ℂ) * Complex.I)) := by ring
    _ = z * Complex.exp
        (((-retardance : ℂ) * Complex.I) +
          ((carrierPhase : ℂ) * Complex.I)) := by rw [Complex.exp_add]
    _ = z * Complex.exp (((carrierPhase - retardance : ℝ) : ℂ) * Complex.I) := by
      congr 2
      push_cast
      ring

/-- A positive quarter-wave retardance has relative phase `-I`. -/
@[simp]
lemma linearRetarderPhase_pi_div_two :
    linearRetarderPhase (((Real.pi / 2 : ℝ) : Real.Angle)) = -Complex.I := by
  simp [linearRetarderPhase, Real.Angle.toCircle_coe, Circle.coe_exp]

/-- A negative quarter-wave retardance has relative phase `I`. -/
@[simp]
lemma linearRetarderPhase_neg_pi_div_two :
    linearRetarderPhase (((-Real.pi / 2 : ℝ) : Real.Angle)) = Complex.I := by
  simp [linearRetarderPhase, Real.Angle.toCircle_coe, Circle.coe_exp]

/-- A half-wave retardance has relative phase `-1`. -/
@[simp]
lemma linearRetarderPhase_pi :
    linearRetarderPhase (Real.pi : Real.Angle) = -1 := by
  simp [linearRetarderPhase, Real.Angle.toCircle_coe, Circle.coe_exp]

/-!

## B. Spectral definition and entries
-/

/-- The rank-one spectral projector associated with a linear Jones axis. -/
private def linearAxisProjector (axis : Real.Angle) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.vecMulVec (JonesVector.linearPolarization axis).components
    (star (JonesVector.linearPolarization axis).components)

/-- The ideal linear retarder whose orthogonal axis is delayed by `retardance` relative to its
declared reference principal axis. -/
def linearRetarder (axis retardance : Real.Angle) : JonesMatrix :=
  ⟨Matrix.vecMulVec (JonesVector.linearPolarization axis).components
      (star (JonesVector.linearPolarization axis).components) +
    linearRetarderPhase retardance •
      Matrix.vecMulVec
        (JonesVector.linearPolarization (axis + (Real.pi / 2 : ℝ))).components
        (star (JonesVector.linearPolarization
          (axis + (Real.pi / 2 : ℝ))).components)⟩

private lemma linearRetarder_entries_eq_projectors (axis retardance : Real.Angle) :
    (linearRetarder axis retardance).entries =
      linearAxisProjector axis + linearRetarderPhase retardance •
        linearAxisProjector (axis + (Real.pi / 2 : ℝ)) := rfl

/-- A linear retarder is the sum of its reference-axis projector and its phase-weighted
orthogonal-axis projector. -/
@[simp]
lemma linearRetarder_entries (axis retardance : Real.Angle) :
    (linearRetarder axis retardance).entries =
      Matrix.vecMulVec (JonesVector.linearPolarization axis).components
          (star (JonesVector.linearPolarization axis).components) +
        linearRetarderPhase retardance •
          Matrix.vecMulVec
            (JonesVector.linearPolarization (axis + (Real.pi / 2 : ℝ))).components
            (star (JonesVector.linearPolarization
              (axis + (Real.pi / 2 : ℝ))).components) := rfl

/-- The first diagonal entry of a linear retarder. -/
@[simp]
lemma linearRetarder_entries_zero_zero (axis retardance : Real.Angle) :
    (linearRetarder axis retardance).entries 0 0 =
      (Real.Angle.cos axis : ℂ) ^ 2 +
        linearRetarderPhase retardance * (Real.Angle.sin axis : ℂ) ^ 2 := by
  simp [linearRetarder, JonesVector.linearPolarization,
    Matrix.vecMulVec, Real.Angle.cos_add_pi_div_two,
    Real.Angle.sin_add_pi_div_two]
  ring

/-- The first-row off-diagonal entry of a linear retarder. -/
@[simp]
lemma linearRetarder_entries_zero_one (axis retardance : Real.Angle) :
    (linearRetarder axis retardance).entries 0 1 =
      (1 - linearRetarderPhase retardance) *
        Real.Angle.cos axis * Real.Angle.sin axis := by
  simp [linearRetarder, JonesVector.linearPolarization,
    Matrix.vecMulVec, Real.Angle.cos_add_pi_div_two,
    Real.Angle.sin_add_pi_div_two]
  ring

/-- The second-row off-diagonal entry of a linear retarder. -/
@[simp]
lemma linearRetarder_entries_one_zero (axis retardance : Real.Angle) :
    (linearRetarder axis retardance).entries 1 0 =
      (1 - linearRetarderPhase retardance) *
        Real.Angle.cos axis * Real.Angle.sin axis := by
  simp [linearRetarder, JonesVector.linearPolarization,
    Matrix.vecMulVec, Real.Angle.cos_add_pi_div_two,
    Real.Angle.sin_add_pi_div_two]
  ring

/-- The second diagonal entry of a linear retarder. -/
@[simp]
lemma linearRetarder_entries_one_one (axis retardance : Real.Angle) :
    (linearRetarder axis retardance).entries 1 1 =
      (Real.Angle.sin axis : ℂ) ^ 2 +
        linearRetarderPhase retardance * (Real.Angle.cos axis : ℂ) ^ 2 := by
  simp [linearRetarder, JonesVector.linearPolarization,
    Matrix.vecMulVec, Real.Angle.cos_add_pi_div_two,
    Real.Angle.sin_add_pi_div_two]
  ring

/-- A zero-axis retarder is diagonal in the declared Jones coordinate basis. -/
lemma linearRetarder_zero_axis_entries (retardance : Real.Angle) :
    (linearRetarder 0 retardance).entries =
      !![1, 0; 0, linearRetarderPhase retardance] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-!

## C. Projector identities
-/

private lemma linearPolarization_star_dot_self (axis : Real.Angle) :
    star (JonesVector.linearPolarization axis).components ⬝ᵥ
      (JonesVector.linearPolarization axis).components = 1 := by
  rw [dotProduct, Fin.sum_univ_two]
  change (starRingEnd ℂ) (Real.Angle.cos axis) * Real.Angle.cos axis +
      (starRingEnd ℂ) (Real.Angle.sin axis) * Real.Angle.sin axis = 1
  simp only [Complex.conj_ofReal]
  norm_cast
  nlinarith [axis.cos_sq_add_sin_sq]

private lemma linearAxisProjector_add_orthogonal (axis : Real.Angle) :
    linearAxisProjector axis +
      linearAxisProjector (axis + (Real.pi / 2 : ℝ)) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [linearAxisProjector, JonesVector.linearPolarization, Matrix.vecMulVec,
      Real.Angle.cos_add_pi_div_two, Real.Angle.sin_add_pi_div_two]
  all_goals norm_cast
  all_goals nlinarith [axis.cos_sq_add_sin_sq]

private lemma linearAxisProjector_conjTranspose (axis : Real.Angle) :
    (linearAxisProjector axis)ᴴ = linearAxisProjector axis := by
  rw [linearAxisProjector, Matrix.conjTranspose_vecMulVec]
  simp

private lemma linearAxisProjector_isIdempotentElem (axis : Real.Angle) :
    IsIdempotentElem (linearAxisProjector axis) := by
  unfold linearAxisProjector
  change Matrix.vecMulVec (JonesVector.linearPolarization axis).components
      (star (JonesVector.linearPolarization axis).components) *
      Matrix.vecMulVec (JonesVector.linearPolarization axis).components
        (star (JonesVector.linearPolarization axis).components) = _
  rw [Matrix.vecMulVec_mul_vecMulVec, linearPolarization_star_dot_self]
  simp

private lemma linearAxisProjector_mul_orthogonal (axis : Real.Angle) :
    linearAxisProjector axis *
      linearAxisProjector (axis + (Real.pi / 2 : ℝ)) = 0 := by
  change Matrix.vecMulVec (JonesVector.linearPolarization axis).components
      (star (JonesVector.linearPolarization axis).components) *
    Matrix.vecMulVec
      (JonesVector.linearPolarization (axis + (Real.pi / 2 : ℝ))).components
      (star (JonesVector.linearPolarization
        (axis + (Real.pi / 2 : ℝ))).components) = 0
  rw [Matrix.vecMulVec_mul_vecMulVec]
  have hdot :
      star (JonesVector.linearPolarization axis).components ⬝ᵥ
        (JonesVector.linearPolarization
          (axis + (Real.pi / 2 : ℝ))).components = 0 := by
    rw [dotProduct, Fin.sum_univ_two]
    simp [JonesVector.linearPolarization, Real.Angle.cos_add_pi_div_two,
      Real.Angle.sin_add_pi_div_two]
    ring_nf
  rw [hdot]
  simp

private lemma linearAxisProjector_orthogonal_mul (axis : Real.Angle) :
    linearAxisProjector (axis + (Real.pi / 2 : ℝ)) *
      linearAxisProjector axis = 0 := by
  rw [← Matrix.conjTranspose_eq_zero]
  simp only [Matrix.conjTranspose_mul]
  rw [linearAxisProjector_conjTranspose, linearAxisProjector_conjTranspose,
    linearAxisProjector_mul_orthogonal]

private lemma linearAxisProjector_add_pi (axis : Real.Angle) :
    linearAxisProjector (axis + (Real.pi : Real.Angle)) =
      linearAxisProjector axis := by
  rw [linearAxisProjector, linearAxisProjector,
    JonesVector.linearPolarization_add_pi]
  ext i j
  simp [JonesVector.scale, Matrix.vecMulVec]

private lemma linearAxisProjector_mulVec (axis : Real.Angle) (J : JonesVector) :
    linearAxisProjector axis *ᵥ J.components =
      J.linearComponent axis • (JonesVector.linearPolarization axis).components := by
  rw [linearAxisProjector, Matrix.vecMulVec_mulVec]
  ext i
  simp [JonesVector.linearComponent, PiLp.inner_apply, dotProduct,
    RCLike.inner_apply, mul_comm]

/-!

## D. Structural retarder laws
-/

/-- Zero retardance gives the identity Jones matrix. -/
@[simp]
lemma linearRetarder_zero (axis : Real.Angle) :
    linearRetarder axis 0 = identity := by
  apply JonesMatrix.ext
  rw [linearRetarder_entries_eq_projectors, linearRetarderPhase_zero, one_smul]
  exact linearAxisProjector_add_orthogonal axis

/-- A linear retarder is periodic in its declared axis with period `π`. -/
lemma linearRetarder_axis_add_pi (axis retardance : Real.Angle) :
    linearRetarder (axis + (Real.pi : Real.Angle)) retardance =
      linearRetarder axis retardance := by
  apply JonesMatrix.ext
  rw [linearRetarder_entries_eq_projectors, linearRetarder_entries_eq_projectors,
    linearAxisProjector_add_pi]
  have haxis :
      (axis + (Real.pi : Real.Angle)) + (Real.pi / 2 : ℝ) =
        (axis + (Real.pi / 2 : ℝ)) + (Real.pi : Real.Angle) := by
    abel
  rw [haxis, linearAxisProjector_add_pi]

/-- Swapping the principal axes and negating retardance changes only the common Jones phase. -/
lemma linearRetarder_axis_add_pi_div_two (axis retardance : Real.Angle) :
    linearRetarder axis retardance =
      (linearRetarder (axis + (Real.pi / 2 : ℝ)) (-retardance)).scale
        (linearRetarderPhase retardance) := by
  apply JonesMatrix.ext
  rw [linearRetarder_entries_eq_projectors, scale_entries,
    linearRetarder_entries_eq_projectors]
  have haxis :
      (axis + (Real.pi / 2 : ℝ)) + (Real.pi / 2 : ℝ) =
        axis + (Real.pi : Real.Angle) := by
    rw [add_assoc]
    congr 1
    rw [← Real.Angle.coe_add]
    congr 1
    ring
  rw [haxis, linearAxisProjector_add_pi, linearRetarderPhase_neg]
  simp only [smul_add, smul_smul]
  have hphase : linearRetarderPhase retardance ≠ 0 :=
    Circle.coe_ne_zero (-retardance).toCircle
  rw [mul_inv_cancel₀ hphase]
  module

/-- Retardances add when ideal linear retarders have the same reference axis.

On the left side of this statement, the `first` retarder acts first. -/
lemma linearRetarder_comp (axis first second : Real.Angle) :
    (linearRetarder axis second).comp (linearRetarder axis first) =
      linearRetarder axis (first + second) := by
  apply JonesMatrix.ext
  change
    (linearRetarder axis second).entries * (linearRetarder axis first).entries =
      (linearRetarder axis (first + second)).entries
  rw [linearRetarder_entries_eq_projectors, linearRetarder_entries_eq_projectors,
    linearRetarder_entries_eq_projectors, linearRetarderPhase_add]
  rw [mul_add, add_mul, add_mul]
  rw [linearAxisProjector_isIdempotentElem]
  rw [Algebra.smul_mul_assoc, linearAxisProjector_orthogonal_mul, smul_zero]
  rw [Algebra.mul_smul_comm, linearAxisProjector_mul_orthogonal, smul_zero]
  rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm,
    linearAxisProjector_isIdempotentElem]
  simp [smul_smul, mul_comm]

/-- Conjugate transposition negates the retardance of an ideal linear retarder. -/
lemma linearRetarder_conjTranspose (axis retardance : Real.Angle) :
    (linearRetarder axis retardance).entriesᴴ =
      (linearRetarder axis (-retardance)).entries := by
  rw [linearRetarder_entries_eq_projectors, Matrix.conjTranspose_add,
    Matrix.conjTranspose_smul, linearAxisProjector_conjTranspose,
    linearAxisProjector_conjTranspose, star_linearRetarderPhase,
    linearRetarder_entries_eq_projectors]

/-- Negating retardance gives a left inverse at the same reference axis. -/
lemma linearRetarder_neg_comp (axis retardance : Real.Angle) :
    (linearRetarder axis (-retardance)).comp
      (linearRetarder axis retardance) = identity := by
  rw [linearRetarder_comp]
  simp

/-- Negating retardance gives a right inverse at the same reference axis. -/
lemma linearRetarder_comp_neg (axis retardance : Real.Angle) :
    (linearRetarder axis retardance).comp
      (linearRetarder axis (-retardance)) = identity := by
  rw [linearRetarder_comp]
  simp

/-- Every ideal linear retarder is algebraically unitary. -/
lemma linearRetarder_isUnitary (axis retardance : Real.Angle) :
    (linearRetarder axis retardance).IsUnitary := by
  rw [IsUnitary, Matrix.mem_unitaryGroup_iff']
  rw [Matrix.star_eq_conjTranspose, linearRetarder_conjTranspose]
  exact congrArg JonesMatrix.entries
    (linearRetarder_neg_comp axis retardance)

/-- The determinant of a linear retarder is its relative phase eigenvalue. -/
lemma linearRetarder_det (axis retardance : Real.Angle) :
    Matrix.det (linearRetarder axis retardance).entries =
      linearRetarderPhase retardance := by
  rw [Matrix.det_fin_two]
  simp only [linearRetarder_entries_zero_zero, linearRetarder_entries_zero_one,
    linearRetarder_entries_one_zero, linearRetarder_entries_one_one]
  have haxis : ((Real.Angle.cos axis : ℂ) ^ 2 +
      (Real.Angle.sin axis : ℂ) ^ 2) = 1 := by
    norm_cast
    exact Real.Angle.cos_sq_add_sin_sq axis
  calc
    _ = linearRetarderPhase retardance *
        (((Real.Angle.cos axis : ℂ) ^ 2 +
          (Real.Angle.sin axis : ℂ) ^ 2) ^ 2) := by ring
    _ = linearRetarderPhase retardance := by rw [haxis]; ring

/-!

## E. Action on Jones vectors
-/

/-- A retarder multiplies only the orthogonal coordinate in its rotated principal-axis basis. -/
lemma linearRetarder_act (axis retardance : Real.Angle) (J : JonesVector) :
    (linearRetarder axis retardance).act J =
      JonesVector.ofLinearComponents axis (J.linearComponent axis)
        (linearRetarderPhase retardance *
          J.linearComponent (axis + (Real.pi / 2 : ℝ))) := by
  ext i
  change ((linearRetarder axis retardance).entries *ᵥ J.components) i = _
  rw [linearRetarder_entries_eq_projectors, Matrix.add_mulVec,
    Matrix.smul_mulVec, linearAxisProjector_mulVec,
    linearAxisProjector_mulVec]
  fin_cases i <;>
    simp [JonesVector.ofLinearComponents, JonesVector.linearPolarization,
      Real.Angle.cos_add_pi_div_two, Real.Angle.sin_add_pi_div_two] <;>
    ring

/-- The declared reference axis is an eigenstate with eigenvalue one. -/
@[simp]
lemma linearRetarder_act_axis (axis retardance : Real.Angle) :
    (linearRetarder axis retardance).act
      (JonesVector.linearPolarization axis) =
        JonesVector.linearPolarization axis := by
  rw [linearRetarder_act]
  simp [JonesVector.linearComponent_linearPolarization, JonesVector.scale]

/-- The orthogonal principal axis is an eigenstate with the retarder relative phase. -/
lemma linearRetarder_act_orthogonal (axis retardance : Real.Angle) :
    (linearRetarder axis retardance).act
      (JonesVector.linearPolarization (axis + (Real.pi / 2 : ℝ))) =
        JonesVector.scale (linearRetarderPhase retardance)
          (JonesVector.linearPolarization (axis + (Real.pi / 2 : ℝ))) := by
  rw [linearRetarder_act]
  have href :
      (JonesVector.linearPolarization (axis + (Real.pi / 2 : ℝ))).linearComponent
        axis = 0 := by
    rw [JonesVector.linearComponent_linearPolarization]
    simp
  rw [href]
  simp [JonesVector.ofLinearComponents_orthogonal]

/-- A retarder sends a linear input to its phase-shifted principal-axis decomposition. -/
lemma linearRetarder_act_linearPolarization (axis retardance input : Real.Angle) :
    (linearRetarder axis retardance).act
      (JonesVector.linearPolarization input) =
        JonesVector.ofLinearComponents axis
          (Real.Angle.cos (input - axis))
          (linearRetarderPhase retardance * Real.Angle.sin (input - axis)) := by
  rw [linearRetarder_act]
  rw [JonesVector.linearComponent_linearPolarization,
    JonesVector.linearComponent_linearPolarization]
  congr 2
  rw [sub_add_eq_sub_sub, Real.Angle.cos_sub_pi_div_two]

/-- A zero-axis retarder leaves the first Jones coordinate unchanged and phase-shifts the
second. -/
lemma linearRetarder_zero_axis_act (retardance : Real.Angle) (J : JonesVector) :
    (linearRetarder 0 retardance).act J =
      JonesVector.ofComponents (J.components 0)
        (linearRetarderPhase retardance * J.components 1) := by
  rw [linearRetarder_act]
  ext i
  fin_cases i <;>
    simp [JonesVector.linearComponent_eq, JonesVector.ofLinearComponents,
      JonesVector.ofComponents]

/-- A zero-axis retarder subtracts its retardance from an equal-amplitude state's relative phase.

This exact family includes diagonal, antidiagonal, quadrature, and selected elliptical Jones
states without assigning circular-polarization handedness. -/
lemma linearRetarder_zero_axis_act_equalAmplitudeRelativePhase
    (retardance relativePhase : Real.Angle) :
    (linearRetarder 0 retardance).act
      (JonesVector.equalAmplitudeRelativePhase relativePhase) =
        JonesVector.equalAmplitudeRelativePhase (relativePhase - retardance) := by
  rw [linearRetarder_zero_axis_act]
  ext i
  fin_cases i
  · rfl
  · simp only [JonesVector.equalAmplitudeRelativePhase, JonesVector.ofComponents_one,
      JonesVector.ofComponents_zero, linearRetarderPhase, sub_eq_add_neg,
      Real.Angle.toCircle_add, Circle.coe_mul]
    ring_nf

/-- An ideal linear retarder preserves squared raw Jones amplitude. -/
@[simp]
lemma linearRetarder_act_intensity (axis retardance : Real.Angle) (J : JonesVector) :
    ((linearRetarder axis retardance).act J).intensity = J.intensity :=
  (linearRetarder_isUnitary axis retardance).act_intensity J

end JonesMatrix

end

end Optics
