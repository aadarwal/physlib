/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Physlib.Mathematics.MatrixRank
public import Physlib.Optics.Polarization.Linear

/-!
# Ideal linear polarizers

## i. Overview

This file defines an ideal linear polarizer as the rank-one Jones projector onto a normalized
linear-polarization axis. Its central action theorem says that the component extracts the input's
complex analyzer amplitude and returns that amplitude along the transmission axis.

All intensity statements here concern squared raw Jones amplitude. They are not claims about
electromagnetic irradiance, Poynting flux, modal power, or physical passivity; those require a
later field-normalization bridge.

## ii. Key results

- `JonesMatrix.linearPolarizer`: the outer-product projector onto a linear Jones axis.
- `JonesMatrix.linearPolarizer_isStarProjection`: self-adjoint idempotence.
- `JonesMatrix.linearPolarizer_rank_eq_one`: exact rank.
- `JonesMatrix.linearPolarizer_act`: analyzer-amplitude projection.
- `JonesMatrix.linearPolarizer_act_intensity_le`: squared-Jones-intensity contraction.

## iii. Table of contents

- A. Projector definition and entries
- B. Projection structure
- C. Action and squared Jones intensity

## iv. References

The implementation is derived from the imported Jones-vector API and Mathlib's rank-one matrix
identities.
-/

@[expose] public section

namespace Optics

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace JonesMatrix

/-!

## A. Projector definition and entries
-/

/-- The ideal linear-polarizer Jones matrix at transmission-axis angle `θ`. -/
def linearPolarizer (θ : Real.Angle) : JonesMatrix :=
  let u := (JonesVector.linearPolarization θ).components
  ⟨Matrix.vecMulVec u (star u)⟩

/-- The ideal linear polarizer is the outer product of its unit transmission-axis vector. -/
@[simp]
lemma linearPolarizer_entries (θ : Real.Angle) :
    (linearPolarizer θ).entries =
      Matrix.vecMulVec (JonesVector.linearPolarization θ).components
        (star (JonesVector.linearPolarization θ).components) := rfl

/-- The first diagonal entry of an ideal linear polarizer is `cos θ²`. -/
@[simp]
lemma linearPolarizer_entries_zero_zero (θ : Real.Angle) :
    (linearPolarizer θ).entries 0 0 = Real.Angle.cos θ ^ 2 := by
  simp [linearPolarizer, JonesVector.linearPolarization, Matrix.vecMulVec]
  ring

/-- The first-row off-diagonal entry of an ideal linear polarizer is `cos θ sin θ`. -/
@[simp]
lemma linearPolarizer_entries_zero_one (θ : Real.Angle) :
    (linearPolarizer θ).entries 0 1 = Real.Angle.cos θ * Real.Angle.sin θ := by
  simp [linearPolarizer, JonesVector.linearPolarization, Matrix.vecMulVec]

/-- The second-row off-diagonal entry of an ideal linear polarizer is `cos θ sin θ`. -/
@[simp]
lemma linearPolarizer_entries_one_zero (θ : Real.Angle) :
    (linearPolarizer θ).entries 1 0 = Real.Angle.cos θ * Real.Angle.sin θ := by
  simp [linearPolarizer, JonesVector.linearPolarization, Matrix.vecMulVec, mul_comm]

/-- The second diagonal entry of an ideal linear polarizer is `sin θ²`. -/
@[simp]
lemma linearPolarizer_entries_one_one (θ : Real.Angle) :
    (linearPolarizer θ).entries 1 1 = Real.Angle.sin θ ^ 2 := by
  simp [linearPolarizer, JonesVector.linearPolarization, Matrix.vecMulVec]
  ring

/-!

## B. Projection structure
-/

/-- The conjugated transmission-axis vector has unit dot product with the axis vector. -/
lemma linearPolarization_star_dot_self (θ : Real.Angle) :
    star (JonesVector.linearPolarization θ).components ⬝ᵥ
      (JonesVector.linearPolarization θ).components = 1 := by
  rw [dotProduct, Fin.sum_univ_two]
  change (starRingEnd ℂ) (Real.Angle.cos θ) * Real.Angle.cos θ +
      (starRingEnd ℂ) (Real.Angle.sin θ) * Real.Angle.sin θ = 1
  simp only [Complex.conj_ofReal]
  norm_cast
  nlinarith [Real.Angle.cos_sq_add_sin_sq θ]

/-- An ideal linear polarizer has Hermitian Jones matrix. -/
lemma linearPolarizer_isHermitian (θ : Real.Angle) :
    (linearPolarizer θ).entries.IsHermitian := by
  change (linearPolarizer θ).entriesᴴ = (linearPolarizer θ).entries
  rw [linearPolarizer_entries, Matrix.conjTranspose_vecMulVec]
  simp

/-- An ideal linear-polarizer matrix is idempotent. -/
lemma linearPolarizer_entries_isIdempotentElem (θ : Real.Angle) :
    IsIdempotentElem (linearPolarizer θ).entries := by
  change Matrix.vecMulVec (JonesVector.linearPolarization θ).components
      (star (JonesVector.linearPolarization θ).components) *
      Matrix.vecMulVec (JonesVector.linearPolarization θ).components
        (star (JonesVector.linearPolarization θ).components) = _
  rw [Matrix.vecMulVec_mul_vecMulVec, linearPolarization_star_dot_self]
  simp

/-- An ideal linear-polarizer matrix is a self-adjoint idempotent. -/
lemma linearPolarizer_isStarProjection (θ : Real.Angle) :
    IsStarProjection (linearPolarizer θ).entries where
  isIdempotentElem := linearPolarizer_entries_isIdempotentElem θ
  isSelfAdjoint := by
    change star (linearPolarizer θ).entries = (linearPolarizer θ).entries
    rw [Matrix.star_eq_conjTranspose]
    exact linearPolarizer_isHermitian θ

/-- The trace of an ideal linear-polarizer Jones matrix is one. -/
lemma linearPolarizer_trace (θ : Real.Angle) :
    Matrix.trace (linearPolarizer θ).entries = 1 := by
  change Matrix.trace (Matrix.vecMulVec
      (JonesVector.linearPolarization θ).components
      (star (JonesVector.linearPolarization θ).components)) = 1
  rw [Matrix.trace_vecMulVec, dotProduct_comm, linearPolarization_star_dot_self]

/-- An ideal linear polarizer has matrix rank one. -/
lemma linearPolarizer_rank_eq_one (θ : Real.Angle) :
    (linearPolarizer θ).entries.rank = 1 := by
  rw [Matrix.rank_eq_one_iff_ne_zero_and_det_eq_zero]
  constructor
  · intro hzero
    have htrace := linearPolarizer_trace θ
    rw [hzero] at htrace
    simp at htrace
  · simpa [linearPolarizer] using
      (Matrix.det_vecMulVec
        (JonesVector.linearPolarization θ).components
        (star (JonesVector.linearPolarization θ).components))

/-- An ideal linear polarizer is not algebraically unitary: it is a rank-one projector, not a
lossless Jones transformation. -/
lemma linearPolarizer_not_isUnitary (θ : Real.Angle) :
    ¬ (linearPolarizer θ).IsUnitary := by
  intro hunitary
  have hunit : (linearPolarizer θ).entriesᴴ * (linearPolarizer θ).entries = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp hunitary
  rw [linearPolarizer_isHermitian, linearPolarizer_entries_isIdempotentElem] at hunit
  have htrace := congrArg Matrix.trace hunit
  rw [linearPolarizer_trace] at htrace
  norm_num at htrace

/-- Composing an ideal linear polarizer with itself gives the same polarizer. -/
@[simp]
lemma linearPolarizer_comp_self (θ : Real.Angle) :
    (linearPolarizer θ).comp (linearPolarizer θ) = linearPolarizer θ := by
  apply JonesMatrix.ext
  exact linearPolarizer_entries_isIdempotentElem θ

/-- A linear polarizer is periodic in its transmission-axis angle with period `π`. -/
lemma linearPolarizer_add_pi (θ : Real.Angle) :
    linearPolarizer (θ + (Real.pi : Real.Angle)) = linearPolarizer θ := by
  apply JonesMatrix.ext
  rw [linearPolarizer_entries, linearPolarizer_entries,
    JonesVector.linearPolarization_add_pi]
  ext i j
  simp [JonesVector.scale, Matrix.vecMulVec]

/-!

## C. Action and squared Jones intensity
-/

/-- The ideal linear polarizer extracts the axial component and restores that axis. -/
lemma linearPolarizer_act (θ : Real.Angle) (J : JonesVector) :
    (linearPolarizer θ).act J =
      JonesVector.scale (J.linearComponent θ) (JonesVector.linearPolarization θ) := by
  ext i
  change (Matrix.vecMulVec (JonesVector.linearPolarization θ).components
      (star (JonesVector.linearPolarization θ).components) *ᵥ J.components) i = _
  rw [Matrix.vecMulVec_mulVec]
  simp [JonesVector.scale, JonesVector.linearComponent, PiLp.inner_apply,
    dotProduct, RCLike.inner_apply, mul_comm]

/-- An ideal linear polarizer transmits its own axis state unchanged. -/
@[simp]
lemma linearPolarizer_act_axis (θ : Real.Angle) :
    (linearPolarizer θ).act (JonesVector.linearPolarization θ) =
      JonesVector.linearPolarization θ := by
  rw [linearPolarizer_act]
  simp [JonesVector.scale]

/-- An ideal linear polarizer transmits a scaled copy of its own axis state unchanged. -/
lemma linearPolarizer_act_scale_axis (z : ℂ) (θ : Real.Angle) :
    (linearPolarizer θ).act
      (JonesVector.scale z (JonesVector.linearPolarization θ)) =
        JonesVector.scale z (JonesVector.linearPolarization θ) := by
  rw [linearPolarizer_act, JonesVector.linearComponent_scale]
  simp

/-- An ideal linear polarizer extinguishes the orthogonal linear-polarization state. -/
@[simp]
lemma linearPolarizer_act_orthogonal (θ : Real.Angle) :
    (linearPolarizer θ).act
      (JonesVector.linearPolarization (θ + (Real.pi / 2 : ℝ))) =
        JonesVector.ofComponents 0 0 := by
  rw [linearPolarizer_act, JonesVector.linearComponent_linearPolarization]
  ext i
  fin_cases i <;> simp [JonesVector.scale, JonesVector.ofComponents]

/-- An ideal linear polarizer extinguishes every scaled orthogonal linear-polarization state. -/
lemma linearPolarizer_act_scale_orthogonal (z : ℂ) (θ : Real.Angle) :
    (linearPolarizer θ).act
      (JonesVector.scale z
        (JonesVector.linearPolarization (θ + (Real.pi / 2 : ℝ)))) =
          JonesVector.ofComponents 0 0 := by
  rw [linearPolarizer_act, JonesVector.linearComponent_scale,
    JonesVector.linearComponent_linearPolarization]
  ext i
  fin_cases i <;> simp [JonesVector.scale, JonesVector.ofComponents]

/-- The squared Jones intensity after a linear polarizer is the squared modulus of the input's
axial component. -/
lemma linearPolarizer_act_intensity (θ : Real.Angle) (J : JonesVector) :
    ((linearPolarizer θ).act J).intensity = Complex.normSq (J.linearComponent θ) := by
  rw [linearPolarizer_act, JonesVector.intensity_scale,
    JonesVector.intensity_linearPolarization]
  ring

/-- An ideal linear polarizer cannot increase squared Jones intensity. -/
lemma linearPolarizer_act_intensity_le (θ : Real.Angle) (J : JonesVector) :
    ((linearPolarizer θ).act J).intensity ≤ J.intensity := by
  rw [linearPolarizer_act_intensity, ← Complex.sq_norm, JonesVector.intensity]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2
  simpa [JonesVector.linearComponent, JonesVector.norm_linearPolarization_components]
    using norm_inner_le_norm (JonesVector.linearPolarization θ).components J.components

end JonesMatrix

end

end Optics
