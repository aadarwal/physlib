/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Polarization.JonesCoherency
public import Physlib.Optics.Polarization.Stokes

/-!
# Jones-derived Stokes coordinates

## i. Overview

This file defines the Stokes data of a coherent Jones vector through its pure coherency matrix. It
therefore connects Jones amplitudes to the same raw and physical Stokes definitions used for
general polarization coherency, rather than introducing a second coordinate calculation.

For Jones components `E₀` and `E₁`, the selected Pauli-positive convention gives
`S₀ = |E₀|² + |E₁|²`, `S₁ = |E₀|² - |E₁|²`,
`S₂ = 2 re (E₀ * conj E₁)`, and `S₃ = -2 im (E₀ * conj E₁)`. The final sign follows from the
already fixed reconstruction identity `C₀₁ = (S₂ - I S₃) / 2`.

## ii. Key results

- `JonesVector.stokes`: Stokes extraction through pure coherency.
- `JonesVector.stokes_scale`: covariance under arbitrary common complex scaling.
- `JonesVector.stokes_phaseShift`: invariance under a common phase shift.
- `JonesVector.stokes_inl_zero` and `JonesVector.stokes_inr_zero`: component squared moduli.
- `JonesVector.stokes_cross_coherence`: the off-diagonal complex coherence identity.
- `JonesVector.stokes_inr_one` and `JonesVector.stokes_inr_two`: the two quadrature coordinates.

## iii. Table of contents

- A. Pure Jones data in Stokes coordinates
- B. Explicit component formulas
- C. Canonical-state checks

## iv. References

The normalized horizontal, vertical, diagonal, antidiagonal, and positive- or negative-`I`
quadrature states have named full-vector checks below. The quadrature names specify only the
relative component factor. No right- or left-circular handedness name is assigned here; that
translation remains subject to the human-checked convention item in `tbd.md`.
-/

@[expose] public section

namespace Optics

open scoped ComplexConjugate

noncomputable section

namespace JonesVector

/-!

## A. Pure Jones data in Stokes coordinates

-/

/-- Extract the Stokes vector of a Jones vector through its pure coherency matrix. -/
noncomputable def stokes (J : JonesVector) : StokesVector :=
  J.coherency.stokes

/-- Jones-derived Stokes data lies in the physical Stokes cone. -/
lemma stokes_isPhysical (J : JonesVector) : J.stokes.IsPhysical :=
  J.coherency.stokes_isPhysical

/-- Stokes intensity of a Jones vector equals its squared Jones intensity. -/
@[simp]
lemma stokes_intensity_eq_intensity (J : JonesVector) :
    J.stokes.intensity = J.intensity := by
  simp [stokes]

/-- Common complex scaling multiplies every Stokes coordinate by the scalar squared modulus. -/
lemma stokes_scale (z : ℂ) (J : JonesVector) :
    (scale z J).stokes = Complex.normSq z • J.stokes := by
  change selfAdjointStokesEquiv (scale z J).coherency.toSelfAdjoint =
    Complex.normSq z • selfAdjointStokesEquiv J.coherency.toSelfAdjoint
  rw [← LinearEquiv.map_smul]
  apply congrArg selfAdjointStokesEquiv
  apply Subtype.ext
  rw [CoherencyMatrix.toSelfAdjoint_val, selfAdjoint.val_smul,
    CoherencyMatrix.toSelfAdjoint_val, coherency_scale_toMatrix]
  ext i j
  simp [Complex.real_smul]

/-- Common unit-modulus scaling leaves Jones-derived Stokes data unchanged. -/
lemma stokes_scale_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) (J : JonesVector) :
    (scale z J).stokes = J.stokes := by
  rw [stokes_scale, ← Complex.sq_norm, hz]
  simp

/-- A common Jones phase shift leaves Jones-derived Stokes data unchanged. -/
@[simp]
lemma stokes_phaseShift (phase : ℝ) (J : JonesVector) :
    (phaseShift phase J).stokes = J.stokes := by
  rw [phaseShift]
  apply stokes_scale_of_norm_eq_one
  exact Complex.norm_exp_ofReal_mul_I phase

/-!

## B. Explicit component formulas

-/

/-- The zeroth Stokes coordinate is the sum of the two component squared moduli. -/
@[simp]
lemma stokes_inl_zero (J : JonesVector) :
    J.stokes (Sum.inl 0) =
      Complex.normSq (J.components 0) + Complex.normSq (J.components 1) := by
  change J.stokes.intensity = _
  rw [stokes_intensity_eq_intensity, intensity_eq_sum_normSq, Fin.sum_univ_two]

/-- The first polarization Stokes coordinate is the difference of the component squared moduli. -/
@[simp]
lemma stokes_inr_zero (J : JonesVector) :
    J.stokes (Sum.inr 0) =
      Complex.normSq (J.components 0) - Complex.normSq (J.components 1) := by
  have hdiag : (J.stokes (Sum.inl 0) + J.stokes (Sum.inr 0)) / 2 =
      Complex.normSq (J.components 0) := by
    apply Complex.ofReal_injective
    calc
      _ = J.stokes.toSelfAdjoint.val 0 0 := by
        simp [StokesVector.toSelfAdjoint_val_eq_matrix]
      _ = J.coherency.toSelfAdjoint.val 0 0 := by
        rw [stokes, PolarizationCoherency.stokes_toSelfAdjoint]
      _ = _ := by simp [Complex.mul_conj]
  rw [stokes_inl_zero] at hdiag
  linarith

/-- The last two Stokes coordinates reconstruct the Jones cross-coherence entry. -/
lemma stokes_cross_coherence (J : JonesVector) :
    ((J.stokes (Sum.inr 1) : ℂ) -
      Complex.I * (J.stokes (Sum.inr 2) : ℂ)) / 2 =
        J.components 0 * star (J.components 1) := by
  calc
    _ = J.stokes.toSelfAdjoint.val 0 1 := by
      simp [StokesVector.toSelfAdjoint_val_eq_matrix]
    _ = J.coherency.toSelfAdjoint.val 0 1 := by
      rw [stokes, PolarizationCoherency.stokes_toSelfAdjoint]
    _ = _ := rfl

/-- The second polarization Stokes coordinate is twice the real cross-coherence. -/
@[simp]
lemma stokes_inr_one (J : JonesVector) :
    J.stokes (Sum.inr 1) =
      2 * (J.components 0 * star (J.components 1)).re := by
  have h := congrArg Complex.re (stokes_cross_coherence J)
  rw [Complex.div_re, Complex.sub_re, Complex.mul_re] at h
  norm_num at h
  rw [Complex.mul_re]
  simp only [Complex.star_def, Complex.conj_re, Complex.conj_im]
  linarith

/-- The third polarization Stokes coordinate is minus twice the imaginary cross-coherence. -/
@[simp]
lemma stokes_inr_two (J : JonesVector) :
    J.stokes (Sum.inr 2) =
      -2 * (J.components 0 * star (J.components 1)).im := by
  have h := congrArg Complex.im (stokes_cross_coherence J)
  rw [Complex.div_im, Complex.sub_im, Complex.mul_im] at h
  norm_num at h
  rw [Complex.mul_im]
  simp only [Complex.star_def, Complex.conj_re, Complex.conj_im]
  linarith

/-!

## C. Canonical-state checks

-/

/-- Horizontal Jones data has unit intensity and positive first polarization coordinate. -/
@[simp]
lemma stokes_horizontal : horizontal.stokes =
    EuclideanSpace.single (Sum.inl 0) 1 + EuclideanSpace.single (Sum.inr 0) 1 := by
  ext μ
  rcases μ with μ | μ
  · fin_cases μ
    simp [horizontal]
  · fin_cases μ <;> simp [horizontal]

/-- Vertical Jones data has unit intensity and negative first polarization coordinate. -/
@[simp]
lemma stokes_vertical : vertical.stokes =
    EuclideanSpace.single (Sum.inl 0) 1 - EuclideanSpace.single (Sum.inr 0) 1 := by
  ext μ
  rcases μ with μ | μ
  · fin_cases μ
    simp [vertical]
  · fin_cases μ <;> simp [vertical]

/-- Diagonal Jones data has unit intensity and positive second polarization coordinate. -/
@[simp]
lemma stokes_diagonal : diagonal.stokes =
    EuclideanSpace.single (Sum.inl 0) 1 + EuclideanSpace.single (Sum.inr 1) 1 := by
  ext μ
  rcases μ with μ | μ
  · fin_cases μ
    simp [diagonal]
    norm_num
  · fin_cases μ <;> simp [diagonal]

/-- Antidiagonal Jones data has unit intensity and negative second polarization coordinate. -/
@[simp]
lemma stokes_antidiagonal : antidiagonal.stokes =
    EuclideanSpace.single (Sum.inl 0) 1 - EuclideanSpace.single (Sum.inr 1) 1 := by
  ext μ
  rcases μ with μ | μ
  · fin_cases μ
    simp [antidiagonal]
    norm_num
  · fin_cases μ <;> simp [antidiagonal]

/-- Positive-`I` quadrature Jones data has unit intensity and positive third coordinate. -/
@[simp]
lemma stokes_plusIQuadrature : plusIQuadrature.stokes =
    EuclideanSpace.single (Sum.inl 0) 1 + EuclideanSpace.single (Sum.inr 2) 1 := by
  ext μ
  rcases μ with μ | μ
  · fin_cases μ
    simp [plusIQuadrature]
    norm_num
  · fin_cases μ <;> simp [plusIQuadrature]

/-- Negative-`I` quadrature Jones data has unit intensity and negative third coordinate. -/
@[simp]
lemma stokes_minusIQuadrature : minusIQuadrature.stokes =
    EuclideanSpace.single (Sum.inl 0) 1 - EuclideanSpace.single (Sum.inr 2) 1 := by
  ext μ
  rcases μ with μ | μ
  · fin_cases μ
    simp [minusIQuadrature]
    norm_num
  · fin_cases μ <;> simp [minusIQuadrature]

end JonesVector

end

end Optics
