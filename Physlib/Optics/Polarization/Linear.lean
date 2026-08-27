/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Polarization.Basic

/-!
# Linear Jones polarization states

## i. Overview

This file defines normalized linear-polarization Jones states using `Real.Angle`. The angle is
measured from the first declared Jones coordinate toward the second. Unguarded convention
statement (review only): no observer-dependent clockwise, counterclockwise, or handedness name is
imposed.

The raw Jones representative changes sign after a half-turn, while its squared Jones intensity
and every projector built from it remain unchanged. The analyzer amplitude is the Hermitian inner
product with the selected linear axis.

## ii. Key results

- `JonesVector.linearPolarization`: the normalized Jones state at a real angle.
- `JonesVector.linearComponent`: the complex amplitude along a linear-polarization axis.
- `JonesVector.intensity_linearPolarization`: normalization.
- `JonesVector.linearComponent_linearPolarization`: the signed cosine overlap.
- `JonesVector.linearPolarization_add_pi`: the half-turn global-sign law.
- `JonesVector.ofLinearComponents`: construction in a rotated orthonormal linear basis.

## iii. Table of contents

- A. Linear axes
- B. Analyzer amplitudes
- C. Angle and coordinate regressions
- D. Rotated linear-basis coordinates

## iv. References

The construction uses Mathlib's intrinsic `Real.Angle` trigonometric API and the existing Physlib
Jones conventions.
-/

@[expose] public section

namespace Optics

noncomputable section

namespace JonesVector

/-!

## A. Linear axes
-/

/-- The unit Jones vector linearly polarized at angle `θ` from the first coordinate axis. -/
def linearPolarization (θ : Real.Angle) : JonesVector :=
  ofComponents (Real.Angle.cos θ) (Real.Angle.sin θ)

/-- The first component of a linear-polarization Jones state. -/
@[simp]
lemma linearPolarization_components_zero (θ : Real.Angle) :
    (linearPolarization θ).components 0 = Real.Angle.cos θ := rfl

/-- The second component of a linear-polarization Jones state. -/
@[simp]
lemma linearPolarization_components_one (θ : Real.Angle) :
    (linearPolarization θ).components 1 = Real.Angle.sin θ := rfl

/-- A linear-polarization Jones vector has unit squared Jones intensity. -/
@[simp]
lemma intensity_linearPolarization (θ : Real.Angle) :
    (linearPolarization θ).intensity = 1 := by
  rw [intensity_eq_sum_normSq, Fin.sum_univ_two]
  simp [Complex.normSq_ofReal]
  nlinarith [Real.Angle.cos_sq_add_sin_sq θ]

/-- The component vector of a linear-polarization Jones state has unit norm. -/
@[simp]
lemma norm_linearPolarization_components (θ : Real.Angle) :
    ‖(linearPolarization θ).components‖ = 1 := by
  have h := intensity_linearPolarization θ
  rw [intensity] at h
  nlinarith [norm_nonneg (linearPolarization θ).components]

/-!

## B. Analyzer amplitudes
-/

/-- The complex amplitude of a Jones vector along the linear-polarization axis `θ`. -/
def linearComponent (J : JonesVector) (θ : Real.Angle) : ℂ :=
  inner ℂ (linearPolarization θ).components J.components

/-- Linear-component amplitude is the real-axis dot product with the Jones components. -/
lemma linearComponent_eq (J : JonesVector) (θ : Real.Angle) :
    J.linearComponent θ =
      Real.Angle.cos θ * J.components 0 + Real.Angle.sin θ * J.components 1 := by
  simp only [linearComponent, PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply,
    linearPolarization_components_zero, linearPolarization_components_one]
  simp only [Complex.conj_ofReal]
  ring

/-- The component of one linear-polarization state along another is their angle-difference
cosine. -/
@[simp]
lemma linearComponent_linearPolarization (θ φ : Real.Angle) :
    (linearPolarization φ).linearComponent θ = Real.Angle.cos (φ - θ) := by
  rw [linearComponent_eq]
  simp only [linearPolarization_components_zero, linearPolarization_components_one]
  norm_cast
  rw [sub_eq_add_neg, Real.Angle.cos_add, Real.Angle.cos_neg, Real.Angle.sin_neg]
  ring

/-- Scaling a Jones vector scales each linear-component amplitude by the same scalar. -/
lemma linearComponent_scale (z : ℂ) (J : JonesVector) (θ : Real.Angle) :
    (scale z J).linearComponent θ = z * J.linearComponent θ := by
  simp [linearComponent, scale, inner_smul_right]

/-!

## C. Angle and coordinate regressions
-/

/-- Shifting a linear-polarization angle by `π` changes only the Jones-vector global sign. -/
lemma linearPolarization_add_pi (θ : Real.Angle) :
    linearPolarization (θ + (Real.pi : Real.Angle)) =
      scale (-1) (linearPolarization θ) := by
  ext i
  fin_cases i <;> simp [linearPolarization, scale]

/-- The zero-angle linear-polarization state is the first coordinate state. -/
@[simp]
lemma linearPolarization_zero : linearPolarization 0 = horizontal := by
  ext i
  fin_cases i <;> simp [linearPolarization, horizontal]

/-- The `π / 2` linear-polarization state is the second coordinate state. -/
@[simp]
lemma linearPolarization_pi_div_two :
    linearPolarization ((Real.pi / 2 : ℝ) : Real.Angle) = vertical := by
  ext i
  fin_cases i <;> simp [linearPolarization, vertical]

/-- The `π / 4` linear-polarization state is the equal positive-component state. -/
@[simp]
lemma linearPolarization_pi_div_four :
    linearPolarization ((Real.pi / 4 : ℝ) : Real.Angle) = diagonal := by
  ext i
  fin_cases i <;> simp [linearPolarization, diagonal, unitEqualAmplitude]

/-- The `-π / 4` linear-polarization state is the equal opposite-component state. -/
@[simp]
lemma linearPolarization_neg_pi_div_four :
    linearPolarization ((-Real.pi / 4 : ℝ) : Real.Angle) = antidiagonal := by
  ext i
  fin_cases i
  · change ((Real.cos (-Real.pi / 4) : ℝ) : ℂ) = unitEqualAmplitude
    norm_cast
    rw [show -Real.pi / 4 = -(Real.pi / 4) by ring, Real.cos_neg,
      Real.cos_pi_div_four]
    rfl
  · change ((Real.sin (-Real.pi / 4) : ℝ) : ℂ) = -unitEqualAmplitude
    norm_cast
    rw [show -Real.pi / 4 = -(Real.pi / 4) by ring, Real.sin_neg,
      Real.sin_pi_div_four]
    rfl

/-!

## D. Rotated linear-basis coordinates
-/

/-- Construct a Jones vector from complex amplitudes along the linear axes `axis` and
`axis + π / 2`. -/
def ofLinearComponents (axis : Real.Angle) (axial orthogonal : ℂ) : JonesVector :=
  ofComponents
    (axial * Real.Angle.cos axis - orthogonal * Real.Angle.sin axis)
    (axial * Real.Angle.sin axis + orthogonal * Real.Angle.cos axis)

/-- The first coordinate of a Jones vector constructed in a rotated linear basis. -/
@[simp]
lemma ofLinearComponents_components_zero (axis : Real.Angle) (axial orthogonal : ℂ) :
    (ofLinearComponents axis axial orthogonal).components 0 =
      axial * Real.Angle.cos axis - orthogonal * Real.Angle.sin axis := rfl

/-- The second coordinate of a Jones vector constructed in a rotated linear basis. -/
@[simp]
lemma ofLinearComponents_components_one (axis : Real.Angle) (axial orthogonal : ℂ) :
    (ofLinearComponents axis axial orthogonal).components 1 =
      axial * Real.Angle.sin axis + orthogonal * Real.Angle.cos axis := rfl

/-- Data supported only on the axial rotated coordinate is a scaled linear-polarization state. -/
@[simp]
lemma ofLinearComponents_axial (axis : Real.Angle) (axial : ℂ) :
    ofLinearComponents axis axial 0 = scale axial (linearPolarization axis) := by
  ext i
  fin_cases i <;> simp [ofLinearComponents, scale, linearPolarization]

/-- Data supported only on the orthogonal rotated coordinate is a scaled orthogonal
linear-polarization state. -/
lemma ofLinearComponents_orthogonal (axis : Real.Angle) (orthogonal : ℂ) :
    ofLinearComponents axis 0 orthogonal =
      scale orthogonal
        (linearPolarization (axis + ((Real.pi / 2 : ℝ) : Real.Angle))) := by
  ext i
  fin_cases i <;>
    simp [ofLinearComponents, scale, linearPolarization,
      Real.Angle.cos_add_pi_div_two, Real.Angle.sin_add_pi_div_two]

/-- Extracting the axial component of rotated linear-basis data recovers its axial amplitude. -/
@[simp]
lemma linearComponent_ofLinearComponents (axis : Real.Angle) (axial orthogonal : ℂ) :
    (ofLinearComponents axis axial orthogonal).linearComponent axis = axial := by
  rw [linearComponent_eq]
  simp only [ofLinearComponents_components_zero, ofLinearComponents_components_one]
  have haxis : ((Real.Angle.cos axis : ℂ) ^ 2 +
      (Real.Angle.sin axis : ℂ) ^ 2) = 1 := by
    norm_cast
    exact Real.Angle.cos_sq_add_sin_sq axis
  linear_combination axial * haxis

/-- Extracting the orthogonal component of rotated linear-basis data recovers its orthogonal
amplitude. -/
@[simp]
lemma linearComponent_ofLinearComponents_orthogonal (axis : Real.Angle)
    (axial orthogonal : ℂ) :
    (ofLinearComponents axis axial orthogonal).linearComponent
        (axis + ((Real.pi / 2 : ℝ) : Real.Angle)) = orthogonal := by
  rw [linearComponent_eq]
  simp only [ofLinearComponents_components_zero, ofLinearComponents_components_one]
  simp [Real.Angle.cos_add, Real.Angle.sin_add]
  have haxis : ((Real.Angle.cos axis : ℂ) ^ 2 +
      (Real.Angle.sin axis : ℂ) ^ 2) = 1 := by
    norm_cast
    exact Real.Angle.cos_sq_add_sin_sq axis
  linear_combination orthogonal * haxis

/-- Reconstruct a Jones vector from its amplitudes along an orthonormal pair of linear axes. -/
lemma ofLinearComponents_linearComponents (axis : Real.Angle) (J : JonesVector) :
    ofLinearComponents axis (J.linearComponent axis)
      (J.linearComponent (axis + ((Real.pi / 2 : ℝ) : Real.Angle))) = J := by
  ext i
  fin_cases i <;>
    simp [ofLinearComponents, linearComponent_eq, Real.Angle.cos_add,
      Real.Angle.sin_add]
  · have haxis : ((Real.Angle.cos axis : ℂ) ^ 2 +
        (Real.Angle.sin axis : ℂ) ^ 2) = 1 := by
      norm_cast
      exact Real.Angle.cos_sq_add_sin_sq axis
    linear_combination J.components 0 * haxis
  · have haxis : ((Real.Angle.cos axis : ℂ) ^ 2 +
        (Real.Angle.sin axis : ℂ) ^ 2) = 1 := by
      norm_cast
      exact Real.Angle.cos_sq_add_sin_sq axis
    linear_combination J.components 1 * haxis

/-- Express a linear-polarization state in an arbitrary rotated linear basis. -/
lemma linearPolarization_eq_ofLinearComponents (axis input : Real.Angle) :
    linearPolarization input =
      ofLinearComponents axis (Real.Angle.cos (input - axis))
        (Real.Angle.sin (input - axis)) := by
  have haxis : ((Real.Angle.cos axis : ℂ) ^ 2 +
      (Real.Angle.sin axis : ℂ) ^ 2) = 1 := by
    norm_cast
    exact Real.Angle.cos_sq_add_sin_sq axis
  ext i
  fin_cases i
  · simp [linearPolarization, ofLinearComponents, sub_eq_add_neg,
      Real.Angle.cos_add, Real.Angle.sin_add]
    calc
      (Real.Angle.cos input : ℂ) =
          Real.Angle.cos input * ((Real.Angle.cos axis : ℂ) ^ 2 +
            (Real.Angle.sin axis : ℂ) ^ 2) := by rw [haxis]; ring
      _ = _ := by ring
  · simp [linearPolarization, ofLinearComponents, sub_eq_add_neg,
      Real.Angle.cos_add, Real.Angle.sin_add]
    calc
      (Real.Angle.sin input : ℂ) =
          Real.Angle.sin input * ((Real.Angle.cos axis : ℂ) ^ 2 +
            (Real.Angle.sin axis : ℂ) ^ 2) := by rw [haxis]; ring
      _ = _ := by ring

end JonesVector

end

end Optics
