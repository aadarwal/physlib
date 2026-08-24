/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Interfaces.PlanarDielectric.FresnelAmplitude
public import Physlib.Optics.Interfaces.PlanarDielectric.SupercriticalPolarization

/-!
# Complex Fresnel amplitudes for positive-normal-decay transmission

## i. Overview

This file extends the lossless planar-dielectric Fresnel calculation from real propagating
normal factors to complex normal factors. It retains the full-vector Jones convention of
`FresnelAmplitude`. For complex normalized normal components `chi_i` and `chi_t`, the scalar
coefficient formulas are

```text
D_s = Y₁ chi_i + Y₂ chi_t,
r_s = (Y₁ chi_i - Y₂ chi_t) / D_s,
t_s = 2 Y₁ chi_i / D_s,
D_p = Y₂ chi_i + Y₁ chi_t,
r_p = (Y₂ chi_i - Y₁ chi_t) / D_p,
t_p = 2 Y₁ chi_i / D_p.
```

The definitions agree exactly with the existing real coefficients after coercion. Their primary
solution lemmas remain branch-neutral and use only the scalar electric and magnetic boundary
equations. Specializing the transmitted factor to `-I * delta`, with a strictly positive real
incident factor, makes both denominators nonzero without a separate assumption.

The later sections connect this algebra to the canonical positive-normal-decay transmitted Jones
carrier. Because boundary amplitudes are referenced to the affine plane's stored point, the
connected transmitted Jones data includes the carrier's exact spatial factor there. No decay
geometry is silently treated as an outgoing-wave or power-flow condition.

## ii. Key results

- `PlanarDielectricInterface.complexSFresnelReflectionCoefficient` and its `p` analogue: complex
  full-vector reflection coefficients.
- `PlanarDielectricInterface.solve_complexSFresnel` and its `p` analogue: the complex scalar
  boundary solutions.
- `PlanarDielectricInterface.complexSFresnelDenominator_ne_zero_of_neg_I_mul`: denominator safety
  on the positive-incident, negative-imaginary transmitted branch.
- `PlanarDielectricInterface.complexSFresnelReflectionCoefficient_norm_of_neg_I_mul` and its `p`
  analogue: unit reflection modulus on that branch.
- `PlanarDielectricInterface.complexSFresnelReflectionCoefficient_phase_of_neg_I_mul` and its `p`
  analogue: the reflection phase as twice a first-quadrant numerator angle.
- `PlanarDielectricInterface.sTotalInternalReflectionPhaseShift_eq_two_arctan` and its `p`
  analogue: the textbook closed phase in the positive-time phasor convention.
- `PlanarDielectricWaveConfiguration.positiveNormalDecay_complexSFresnelReflectionCoefficient_norm`
  and its `p` analogue: unit modulus specialized to the canonical physical decay factor.
- `PlanarDielectricWaveConfiguration.complexFresnel_components_of_referenced_balances`: all four
  boundary-selected complex amplitude laws, including the zero-reflected-wave guard.

## iii. Table of contents

- A. Complex coefficient data
- B. Real-coefficient compatibility
- C. Negative-imaginary denominator safety
- D. Total-internal-reflection modulus and phase
- E. Complex scalar boundary solutions
- F. Physical positive-normal-decay modulus and phase
- G. Hybrid propagating-decay Jones boundary equations
- H. Boundary-selected positive-normal-decay Fresnel amplitudes

## iv. References

The formulas are derived from Physlib's referenced electric and magnetic boundary equations. No
external formal-development source is copied or translated here.
-/

@[expose] public section

namespace Optics

open Electromagnetism

noncomputable section

namespace PlanarDielectricInterface

/-!

## A. Complex coefficient data

-/

/-- The complex full-vector `s` Fresnel denominator `Y₁ chi_i + Y₂ chi_t`. -/
def complexSFresnelDenominator (interface : PlanarDielectricInterface)
    (chi_i chi_t : ℂ) : ℂ :=
  ((interface.negativeMedium.waveImpedance⁻¹ : ℝ) : ℂ) * chi_i +
    ((interface.positiveMedium.waveImpedance⁻¹ : ℝ) : ℂ) * chi_t

/-- The complex full-vector `p` Fresnel denominator `Y₂ chi_i + Y₁ chi_t`. -/
def complexPFresnelDenominator (interface : PlanarDielectricInterface)
    (chi_i chi_t : ℂ) : ℂ :=
  ((interface.positiveMedium.waveImpedance⁻¹ : ℝ) : ℂ) * chi_i +
    ((interface.negativeMedium.waveImpedance⁻¹ : ℝ) : ℂ) * chi_t

/-- The reflected full-vector `s` Jones multiplier for complex normal factors. -/
def complexSFresnelReflectionCoefficient (interface : PlanarDielectricInterface)
    (chi_i chi_t : ℂ) : ℂ :=
  (((interface.negativeMedium.waveImpedance⁻¹ : ℝ) : ℂ) * chi_i -
      ((interface.positiveMedium.waveImpedance⁻¹ : ℝ) : ℂ) * chi_t) /
    interface.complexSFresnelDenominator chi_i chi_t

/-- The transmitted full-vector `s` Jones multiplier for complex normal factors. -/
def complexSFresnelTransmissionCoefficient (interface : PlanarDielectricInterface)
    (chi_i chi_t : ℂ) : ℂ :=
  2 * ((interface.negativeMedium.waveImpedance⁻¹ : ℝ) : ℂ) * chi_i /
    interface.complexSFresnelDenominator chi_i chi_t

/-- The reflected full-vector `p` Jones multiplier for complex normal factors. -/
def complexPFresnelReflectionCoefficient (interface : PlanarDielectricInterface)
    (chi_i chi_t : ℂ) : ℂ :=
  (((interface.positiveMedium.waveImpedance⁻¹ : ℝ) : ℂ) * chi_i -
      ((interface.negativeMedium.waveImpedance⁻¹ : ℝ) : ℂ) * chi_t) /
    interface.complexPFresnelDenominator chi_i chi_t

/-- The transmitted full-vector `p` Jones multiplier for complex normal factors. -/
def complexPFresnelTransmissionCoefficient (interface : PlanarDielectricInterface)
    (chi_i chi_t : ℂ) : ℂ :=
  2 * ((interface.negativeMedium.waveImpedance⁻¹ : ℝ) : ℂ) * chi_i /
    interface.complexPFresnelDenominator chi_i chi_t

/-- The reflected fixed-plane tangential-`p` multiplier for complex normal factors. -/
def complexTangentialPFresnelReflectionCoefficient
    (interface : PlanarDielectricInterface) (chi_i chi_t : ℂ) : ℂ :=
  (((interface.negativeMedium.waveImpedance⁻¹ : ℝ) : ℂ) * chi_t -
      ((interface.positiveMedium.waveImpedance⁻¹ : ℝ) : ℂ) * chi_i) /
    interface.complexPFresnelDenominator chi_i chi_t

/-- The transmitted fixed-plane tangential-`p` multiplier for complex normal factors. -/
def complexTangentialPFresnelTransmissionCoefficient
    (interface : PlanarDielectricInterface) (chi_i chi_t : ℂ) : ℂ :=
  2 * ((interface.negativeMedium.waveImpedance⁻¹ : ℝ) : ℂ) * chi_t /
    interface.complexPFresnelDenominator chi_i chi_t

/-- The complex fixed-plane tangential-`p` reflection coefficient is the negative of the
propagation-oriented full-vector coefficient. -/
lemma complexTangentialPFresnelReflectionCoefficient_eq_neg
    (interface : PlanarDielectricInterface) (chi_i chi_t : ℂ) :
    interface.complexTangentialPFresnelReflectionCoefficient chi_i chi_t =
      -interface.complexPFresnelReflectionCoefficient chi_i chi_t := by
  rw [complexTangentialPFresnelReflectionCoefficient,
    complexPFresnelReflectionCoefficient]
  ring

/-- Tangential projection converts the complex transmitted full-vector `p` coefficient without
division by the incident normal factor. -/
lemma complexTangentialPFresnelTransmissionCoefficient_cross_mul
    (interface : PlanarDielectricInterface) (chi_i chi_t : ℂ) :
    chi_i * interface.complexTangentialPFresnelTransmissionCoefficient chi_i chi_t =
      chi_t * interface.complexPFresnelTransmissionCoefficient chi_i chi_t := by
  rw [complexTangentialPFresnelTransmissionCoefficient,
    complexPFresnelTransmissionCoefficient]
  ring

/-- Away from incident grazing, the complex tangential transmitted `p` coefficient is the
full-vector coefficient multiplied by the transmitted-to-incident normal ratio. -/
lemma complexTangentialPFresnelTransmissionCoefficient_eq_normalRatio_mul
    (interface : PlanarDielectricInterface) {chi_i chi_t : ℂ} (hIncident : chi_i ≠ 0) :
    interface.complexTangentialPFresnelTransmissionCoefficient chi_i chi_t =
      (chi_t / chi_i) * interface.complexPFresnelTransmissionCoefficient chi_i chi_t := by
  calc
    interface.complexTangentialPFresnelTransmissionCoefficient chi_i chi_t =
        chi_i⁻¹ *
          (chi_i * interface.complexTangentialPFresnelTransmissionCoefficient chi_i chi_t) := by
      rw [← mul_assoc, inv_mul_cancel₀ hIncident, one_mul]
    _ = chi_i⁻¹ *
        (chi_t * interface.complexPFresnelTransmissionCoefficient chi_i chi_t) := by
      rw [interface.complexTangentialPFresnelTransmissionCoefficient_cross_mul]
    _ = (chi_t / chi_i) *
        interface.complexPFresnelTransmissionCoefficient chi_i chi_t := by
      rw [div_eq_mul_inv]
      ring

/-- A complex full-vector reflected `p` amplitude law converts to the fixed-plane convention
under the zero-amplitude-or-opposite-normal guard. -/
lemma complexTangentialPFresnelReflectionAmplitude_of_guard
    (interface : PlanarDielectricInterface) {chi_i chi_r chi_t I R : ℂ}
    (hAmplitude : R = interface.complexPFresnelReflectionCoefficient chi_i chi_t * I)
    (hReflection : R = 0 ∨ chi_r = -chi_i) :
    chi_r * R = interface.complexTangentialPFresnelReflectionCoefficient chi_i chi_t *
      (chi_i * I) := by
  rw [interface.complexTangentialPFresnelReflectionCoefficient_eq_neg]
  rcases hReflection with hZero | hNormal
  · rw [hZero] at hAmplitude ⊢
    simp only [mul_zero]
    calc
      0 = -chi_i * (interface.complexPFresnelReflectionCoefficient chi_i chi_t * I) := by
        rw [← hAmplitude]
        simp
      _ = -interface.complexPFresnelReflectionCoefficient chi_i chi_t * (chi_i * I) := by
        ring
  · rw [hAmplitude, hNormal]
    ring

/-- A complex full-vector transmitted `p` amplitude law converts to the fixed-plane convention
without division by the incident normal factor. -/
lemma complexTangentialPFresnelTransmissionAmplitude
    (interface : PlanarDielectricInterface) {chi_i chi_t I T : ℂ}
    (hAmplitude : T = interface.complexPFresnelTransmissionCoefficient chi_i chi_t * I) :
    chi_t * T = interface.complexTangentialPFresnelTransmissionCoefficient chi_i chi_t *
      (chi_i * I) := by
  have hCoefficient :=
    interface.complexTangentialPFresnelTransmissionCoefficient_cross_mul chi_i chi_t
  rw [hAmplitude]
  calc
    chi_t * (interface.complexPFresnelTransmissionCoefficient chi_i chi_t * I) =
        (chi_t * interface.complexPFresnelTransmissionCoefficient chi_i chi_t) * I := by ring
    _ = (chi_i * interface.complexTangentialPFresnelTransmissionCoefficient chi_i chi_t) * I := by
      rw [hCoefficient]
    _ = interface.complexTangentialPFresnelTransmissionCoefficient chi_i chi_t *
        (chi_i * I) := by ring

/-!

## B. Real-coefficient compatibility

-/

/-- The complex `s` denominator restricts to the existing real `s` denominator. -/
@[simp]
lemma complexSFresnelDenominator_ofReal (interface : PlanarDielectricInterface)
    (chi_i chi_t : ℝ) :
    interface.complexSFresnelDenominator (chi_i : ℂ) (chi_t : ℂ) =
      (interface.sFresnelDenominator chi_i chi_t : ℂ) := by
  simp [complexSFresnelDenominator, sFresnelDenominator]

/-- The complex `p` denominator restricts to the existing real `p` denominator. -/
@[simp]
lemma complexPFresnelDenominator_ofReal (interface : PlanarDielectricInterface)
    (chi_i chi_t : ℝ) :
    interface.complexPFresnelDenominator (chi_i : ℂ) (chi_t : ℂ) =
      (interface.pFresnelDenominator chi_i chi_t : ℂ) := by
  simp [complexPFresnelDenominator, pFresnelDenominator]

/-- The complex `s` reflection coefficient restricts to the existing real coefficient. -/
@[simp]
lemma complexSFresnelReflectionCoefficient_ofReal
    (interface : PlanarDielectricInterface) (chi_i chi_t : ℝ) :
    interface.complexSFresnelReflectionCoefficient (chi_i : ℂ) (chi_t : ℂ) =
      (interface.sFresnelReflectionCoefficient chi_i chi_t : ℂ) := by
  simp [complexSFresnelReflectionCoefficient, sFresnelReflectionCoefficient]

/-- The complex `s` transmission coefficient restricts to the existing real coefficient. -/
@[simp]
lemma complexSFresnelTransmissionCoefficient_ofReal
    (interface : PlanarDielectricInterface) (chi_i chi_t : ℝ) :
    interface.complexSFresnelTransmissionCoefficient (chi_i : ℂ) (chi_t : ℂ) =
      (interface.sFresnelTransmissionCoefficient chi_i chi_t : ℂ) := by
  simp [complexSFresnelTransmissionCoefficient, sFresnelTransmissionCoefficient]

/-- The complex `p` reflection coefficient restricts to the existing real coefficient. -/
@[simp]
lemma complexPFresnelReflectionCoefficient_ofReal
    (interface : PlanarDielectricInterface) (chi_i chi_t : ℝ) :
    interface.complexPFresnelReflectionCoefficient (chi_i : ℂ) (chi_t : ℂ) =
      (interface.pFresnelReflectionCoefficient chi_i chi_t : ℂ) := by
  simp [complexPFresnelReflectionCoefficient, pFresnelReflectionCoefficient]

/-- The complex `p` transmission coefficient restricts to the existing real coefficient. -/
@[simp]
lemma complexPFresnelTransmissionCoefficient_ofReal
    (interface : PlanarDielectricInterface) (chi_i chi_t : ℝ) :
    interface.complexPFresnelTransmissionCoefficient (chi_i : ℂ) (chi_t : ℂ) =
      (interface.pFresnelTransmissionCoefficient chi_i chi_t : ℂ) := by
  simp [complexPFresnelTransmissionCoefficient, pFresnelTransmissionCoefficient]

/-- The complex tangential `p` reflection coefficient restricts to the existing real one. -/
@[simp]
lemma complexTangentialPFresnelReflectionCoefficient_ofReal
    (interface : PlanarDielectricInterface) (chi_i chi_t : ℝ) :
    interface.complexTangentialPFresnelReflectionCoefficient (chi_i : ℂ) (chi_t : ℂ) =
      (interface.tangentialPFresnelReflectionCoefficient chi_i chi_t : ℂ) := by
  simp [complexTangentialPFresnelReflectionCoefficient,
    tangentialPFresnelReflectionCoefficient]

/-- The complex tangential `p` transmission coefficient restricts to the existing real one. -/
@[simp]
lemma complexTangentialPFresnelTransmissionCoefficient_ofReal
    (interface : PlanarDielectricInterface) (chi_i chi_t : ℝ) :
    interface.complexTangentialPFresnelTransmissionCoefficient (chi_i : ℂ) (chi_t : ℂ) =
      (interface.tangentialPFresnelTransmissionCoefficient chi_i chi_t : ℂ) := by
  simp [complexTangentialPFresnelTransmissionCoefficient,
    tangentialPFresnelTransmissionCoefficient]

/-!

## C. Negative-imaginary denominator safety

-/

/-- A positive real incident normal factor makes the complex `s` denominator nonzero when the
transmitted normal factor is written `-I * decayRatio`. -/
lemma complexSFresnelDenominator_ne_zero_of_neg_I_mul
    (interface : PlanarDielectricInterface) {chi_i decayRatio : ℝ}
    (hIncident : 0 < chi_i) :
    interface.complexSFresnelDenominator (chi_i : ℂ)
      (-Complex.I * (decayRatio : ℂ)) ≠ 0 := by
  intro hZero
  have hReal := congrArg Complex.re hZero
  simp [complexSFresnelDenominator] at hReal
  have hPositive :
      0 < interface.negativeMedium.waveImpedance⁻¹ * chi_i :=
    mul_pos (inv_pos.mpr interface.negativeMedium.waveImpedance_pos) hIncident
  linarith

/-- A positive real incident normal factor makes the complex `p` denominator nonzero when the
transmitted normal factor is written `-I * decayRatio`. -/
lemma complexPFresnelDenominator_ne_zero_of_neg_I_mul
    (interface : PlanarDielectricInterface) {chi_i decayRatio : ℝ}
    (hIncident : 0 < chi_i) :
    interface.complexPFresnelDenominator (chi_i : ℂ)
      (-Complex.I * (decayRatio : ℂ)) ≠ 0 := by
  intro hZero
  have hReal := congrArg Complex.re hZero
  simp [complexPFresnelDenominator] at hReal
  have hPositive :
      0 < interface.positiveMedium.waveImpedance⁻¹ * chi_i :=
    mul_pos (inv_pos.mpr interface.positiveMedium.waveImpedance_pos) hIncident
  linarith

/-!

## D. Total-internal-reflection modulus and phase

-/

/-- The complex numerator whose quotient by its conjugate is the `s` reflection coefficient for
the transmitted factor `-I * decayRatio`; it lies in the first quadrant when both factors are
positive. -/
def sTotalInternalReflectionPhaseNumerator (interface : PlanarDielectricInterface)
    (chi_i decayRatio : ℝ) : ℂ :=
  (interface.negativeMedium.waveImpedance⁻¹ * chi_i : ℝ) +
    Complex.I * (interface.positiveMedium.waveImpedance⁻¹ * decayRatio : ℝ)

/-- The complex numerator whose quotient by its conjugate is the `p` reflection coefficient for
the transmitted factor `-I * decayRatio`; it lies in the first quadrant when both factors are
positive. -/
def pTotalInternalReflectionPhaseNumerator (interface : PlanarDielectricInterface)
    (chi_i decayRatio : ℝ) : ℂ :=
  (interface.positiveMedium.waveImpedance⁻¹ * chi_i : ℝ) +
    Complex.I * (interface.negativeMedium.waveImpedance⁻¹ * decayRatio : ℝ)

/-- The `s` reflection phase shift, represented modulo `2 * pi` as twice the argument of the
named numerator. Positive incident and decay factors put that numerator in the first quadrant. -/
noncomputable def sTotalInternalReflectionPhaseShift (interface : PlanarDielectricInterface)
    (chi_i decayRatio : ℝ) : Real.Angle :=
  2 • (Complex.arg (interface.sTotalInternalReflectionPhaseNumerator chi_i decayRatio) :
    Real.Angle)

/-- The `p` reflection phase shift, represented modulo `2 * pi` as twice the argument of the
named numerator. Positive incident and decay factors put that numerator in the first quadrant. -/
noncomputable def pTotalInternalReflectionPhaseShift (interface : PlanarDielectricInterface)
    (chi_i decayRatio : ℝ) : Real.Angle :=
  2 • (Complex.arg (interface.pTotalInternalReflectionPhaseNumerator chi_i decayRatio) :
    Real.Angle)

/-- For a transmitted factor written `-I * decayRatio`, the `s` reflection coefficient is a
complex number divided by its conjugate. -/
lemma complexSFresnelReflectionCoefficient_neg_I_mul_eq_div_conj
    (interface : PlanarDielectricInterface) (chi_i decayRatio : ℝ) :
    interface.complexSFresnelReflectionCoefficient (chi_i : ℂ)
      (-Complex.I * (decayRatio : ℂ)) =
      interface.sTotalInternalReflectionPhaseNumerator chi_i decayRatio /
        star (interface.sTotalInternalReflectionPhaseNumerator chi_i decayRatio) := by
  simp only [complexSFresnelReflectionCoefficient, complexSFresnelDenominator,
    sTotalInternalReflectionPhaseNumerator, Complex.star_def, map_add, map_mul,
    Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- For a transmitted factor written `-I * decayRatio`, the `p` reflection coefficient is a
complex number divided by its conjugate. -/
lemma complexPFresnelReflectionCoefficient_neg_I_mul_eq_div_conj
    (interface : PlanarDielectricInterface) (chi_i decayRatio : ℝ) :
    interface.complexPFresnelReflectionCoefficient (chi_i : ℂ)
      (-Complex.I * (decayRatio : ℂ)) =
      interface.pTotalInternalReflectionPhaseNumerator chi_i decayRatio /
        star (interface.pTotalInternalReflectionPhaseNumerator chi_i decayRatio) := by
  simp only [complexPFresnelReflectionCoefficient, complexPFresnelDenominator,
    pTotalInternalReflectionPhaseNumerator, Complex.star_def, map_add, map_mul,
    Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- Positive incident and decay factors place the `s` phase numerator strictly in the first
quadrant. -/
lemma sTotalInternalReflectionPhaseNumerator_arg_mem
    (interface : PlanarDielectricInterface) {chi_i decayRatio : ℝ}
    (hIncident : 0 < chi_i) (hDecay : 0 < decayRatio) :
    Complex.arg (interface.sTotalInternalReflectionPhaseNumerator chi_i decayRatio) ∈
      Set.Ioo 0 (Real.pi / 2) := by
  have hReal : 0 <
      (interface.sTotalInternalReflectionPhaseNumerator chi_i decayRatio).re := by
    simpa [sTotalInternalReflectionPhaseNumerator] using
      mul_pos (inv_pos.mpr interface.negativeMedium.waveImpedance_pos) hIncident
  have hImaginary : 0 <
      (interface.sTotalInternalReflectionPhaseNumerator chi_i decayRatio).im := by
    simpa [sTotalInternalReflectionPhaseNumerator] using
      mul_pos (inv_pos.mpr interface.positiveMedium.waveImpedance_pos) hDecay
  constructor
  · have hNonnegative := Complex.arg_nonneg_iff.mpr hImaginary.le
    exact hNonnegative.lt_of_ne fun hZero ↦ by
      have hImaginaryZero := (Complex.arg_eq_zero_iff.mp hZero.symm).2
      exact hImaginary.ne' hImaginaryZero
  · exact Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hReal)

/-- Positive incident and decay factors place the `p` phase numerator strictly in the first
quadrant. -/
lemma pTotalInternalReflectionPhaseNumerator_arg_mem
    (interface : PlanarDielectricInterface) {chi_i decayRatio : ℝ}
    (hIncident : 0 < chi_i) (hDecay : 0 < decayRatio) :
    Complex.arg (interface.pTotalInternalReflectionPhaseNumerator chi_i decayRatio) ∈
      Set.Ioo 0 (Real.pi / 2) := by
  have hReal : 0 <
      (interface.pTotalInternalReflectionPhaseNumerator chi_i decayRatio).re := by
    simpa [pTotalInternalReflectionPhaseNumerator] using
      mul_pos (inv_pos.mpr interface.positiveMedium.waveImpedance_pos) hIncident
  have hImaginary : 0 <
      (interface.pTotalInternalReflectionPhaseNumerator chi_i decayRatio).im := by
    simpa [pTotalInternalReflectionPhaseNumerator] using
      mul_pos (inv_pos.mpr interface.negativeMedium.waveImpedance_pos) hDecay
  constructor
  · have hNonnegative := Complex.arg_nonneg_iff.mpr hImaginary.le
    exact hNonnegative.lt_of_ne fun hZero ↦ by
      have hImaginaryZero := (Complex.arg_eq_zero_iff.mp hZero.symm).2
      exact hImaginary.ne' hImaginaryZero
  · exact Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hReal)

/-- On the physical positive-factor branch, the `s` numerator argument is the arctangent of the
decay-admittance ratio. -/
lemma sTotalInternalReflectionPhaseNumerator_arg_eq_arctan
    (interface : PlanarDielectricInterface) {chi_i decayRatio : ℝ}
    (hIncident : 0 < chi_i) (hDecay : 0 < decayRatio) :
    Complex.arg (interface.sTotalInternalReflectionPhaseNumerator chi_i decayRatio) =
      Real.arctan
        ((interface.positiveMedium.waveImpedance⁻¹ * decayRatio) /
          (interface.negativeMedium.waveImpedance⁻¹ * chi_i)) := by
  have hArg := interface.sTotalInternalReflectionPhaseNumerator_arg_mem hIncident hDecay
  calc
    Complex.arg (interface.sTotalInternalReflectionPhaseNumerator chi_i decayRatio) =
        Real.arctan
          (Real.tan
            (Complex.arg
              (interface.sTotalInternalReflectionPhaseNumerator chi_i decayRatio))) := by
      symm
      apply Real.arctan_tan
      · exact (neg_neg_of_pos (div_pos Real.pi_pos (by norm_num))).trans hArg.1
      · exact hArg.2
    _ = _ := by
      rw [Complex.tan_arg]
      simp [sTotalInternalReflectionPhaseNumerator]

/-- On the physical positive-factor branch, the `p` numerator argument is the arctangent of the
decay-admittance ratio. -/
lemma pTotalInternalReflectionPhaseNumerator_arg_eq_arctan
    (interface : PlanarDielectricInterface) {chi_i decayRatio : ℝ}
    (hIncident : 0 < chi_i) (hDecay : 0 < decayRatio) :
    Complex.arg (interface.pTotalInternalReflectionPhaseNumerator chi_i decayRatio) =
      Real.arctan
        ((interface.negativeMedium.waveImpedance⁻¹ * decayRatio) /
          (interface.positiveMedium.waveImpedance⁻¹ * chi_i)) := by
  have hArg := interface.pTotalInternalReflectionPhaseNumerator_arg_mem hIncident hDecay
  calc
    Complex.arg (interface.pTotalInternalReflectionPhaseNumerator chi_i decayRatio) =
        Real.arctan
          (Real.tan
            (Complex.arg
              (interface.pTotalInternalReflectionPhaseNumerator chi_i decayRatio))) := by
      symm
      apply Real.arctan_tan
      · exact (neg_neg_of_pos (div_pos Real.pi_pos (by norm_num))).trans hArg.1
      · exact hArg.2
    _ = _ := by
      rw [Complex.tan_arg]
      simp [pTotalInternalReflectionPhaseNumerator]

/-- The physical `s` reflection phase is twice the arctangent of its positive
decay-admittance ratio, as an angle modulo `2 * pi`. -/
lemma sTotalInternalReflectionPhaseShift_eq_two_arctan
    (interface : PlanarDielectricInterface) {chi_i decayRatio : ℝ}
    (hIncident : 0 < chi_i) (hDecay : 0 < decayRatio) :
    interface.sTotalInternalReflectionPhaseShift chi_i decayRatio =
      2 • (Real.arctan
        ((interface.positiveMedium.waveImpedance⁻¹ * decayRatio) /
          (interface.negativeMedium.waveImpedance⁻¹ * chi_i)) : Real.Angle) := by
  rw [sTotalInternalReflectionPhaseShift,
    interface.sTotalInternalReflectionPhaseNumerator_arg_eq_arctan hIncident hDecay]

/-- The physical `p` reflection phase is twice the arctangent of its positive
decay-admittance ratio, as an angle modulo `2 * pi`. -/
lemma pTotalInternalReflectionPhaseShift_eq_two_arctan
    (interface : PlanarDielectricInterface) {chi_i decayRatio : ℝ}
    (hIncident : 0 < chi_i) (hDecay : 0 < decayRatio) :
    interface.pTotalInternalReflectionPhaseShift chi_i decayRatio =
      2 • (Real.arctan
        ((interface.negativeMedium.waveImpedance⁻¹ * decayRatio) /
          (interface.positiveMedium.waveImpedance⁻¹ * chi_i)) : Real.Angle) := by
  rw [pTotalInternalReflectionPhaseShift,
    interface.pTotalInternalReflectionPhaseNumerator_arg_eq_arctan hIncident hDecay]

/-- The complex `s` reflection coefficient has unit modulus for a positive real incident normal
factor and a transmitted factor written `-I * decayRatio`. -/
lemma complexSFresnelReflectionCoefficient_norm_of_neg_I_mul
    (interface : PlanarDielectricInterface) {chi_i decayRatio : ℝ}
    (hIncident : 0 < chi_i) :
    ‖interface.complexSFresnelReflectionCoefficient (chi_i : ℂ)
      (-Complex.I * (decayRatio : ℂ))‖ = 1 := by
  rw [interface.complexSFresnelReflectionCoefficient_neg_I_mul_eq_div_conj,
    Complex.norm_div, norm_star]
  have hNumerator :
      interface.sTotalInternalReflectionPhaseNumerator chi_i decayRatio ≠ 0 := by
    intro hZero
    have hReal := congrArg Complex.re hZero
    simp [sTotalInternalReflectionPhaseNumerator] at hReal
    exact hIncident.ne' hReal
  exact div_self (norm_ne_zero_iff.mpr hNumerator)

/-- The complex `p` reflection coefficient has unit modulus for a positive real incident normal
factor and a transmitted factor written `-I * decayRatio`. -/
lemma complexPFresnelReflectionCoefficient_norm_of_neg_I_mul
    (interface : PlanarDielectricInterface) {chi_i decayRatio : ℝ}
    (hIncident : 0 < chi_i) :
    ‖interface.complexPFresnelReflectionCoefficient (chi_i : ℂ)
      (-Complex.I * (decayRatio : ℂ))‖ = 1 := by
  rw [interface.complexPFresnelReflectionCoefficient_neg_I_mul_eq_div_conj,
    Complex.norm_div, norm_star]
  have hNumerator :
      interface.pTotalInternalReflectionPhaseNumerator chi_i decayRatio ≠ 0 := by
    intro hZero
    have hReal := congrArg Complex.re hZero
    simp [pTotalInternalReflectionPhaseNumerator] at hReal
    exact hIncident.ne' hReal
  exact div_self (norm_ne_zero_iff.mpr hNumerator)

/-- For a transmitted factor written `-I * decayRatio`, the argument of the `s` reflection
coefficient is its named phase shift. -/
lemma complexSFresnelReflectionCoefficient_phase_of_neg_I_mul
    (interface : PlanarDielectricInterface) {chi_i decayRatio : ℝ}
    (hIncident : 0 < chi_i) :
    (Complex.arg (interface.complexSFresnelReflectionCoefficient (chi_i : ℂ)
      (-Complex.I * (decayRatio : ℂ))) : Real.Angle) =
        interface.sTotalInternalReflectionPhaseShift chi_i decayRatio := by
  rw [interface.complexSFresnelReflectionCoefficient_neg_I_mul_eq_div_conj]
  have hNumerator :
      interface.sTotalInternalReflectionPhaseNumerator chi_i decayRatio ≠ 0 := by
    intro hZero
    have hReal := congrArg Complex.re hZero
    simp [sTotalInternalReflectionPhaseNumerator] at hReal
    exact hIncident.ne' hReal
  have hConjugate :
      star (interface.sTotalInternalReflectionPhaseNumerator chi_i decayRatio) ≠ 0 :=
    star_ne_zero.mpr hNumerator
  rw [Complex.arg_div_coe_angle hNumerator hConjugate,
    Complex.star_def,
    Complex.arg_conj_coe_angle]
  simp [sTotalInternalReflectionPhaseShift, two_nsmul]

/-- For a transmitted factor written `-I * decayRatio`, the argument of the `p` reflection
coefficient is its named phase shift. -/
lemma complexPFresnelReflectionCoefficient_phase_of_neg_I_mul
    (interface : PlanarDielectricInterface) {chi_i decayRatio : ℝ}
    (hIncident : 0 < chi_i) :
    (Complex.arg (interface.complexPFresnelReflectionCoefficient (chi_i : ℂ)
      (-Complex.I * (decayRatio : ℂ))) : Real.Angle) =
        interface.pTotalInternalReflectionPhaseShift chi_i decayRatio := by
  rw [interface.complexPFresnelReflectionCoefficient_neg_I_mul_eq_div_conj]
  have hNumerator :
      interface.pTotalInternalReflectionPhaseNumerator chi_i decayRatio ≠ 0 := by
    intro hZero
    have hReal := congrArg Complex.re hZero
    simp [pTotalInternalReflectionPhaseNumerator] at hReal
    exact hIncident.ne' hReal
  have hConjugate :
      star (interface.pTotalInternalReflectionPhaseNumerator chi_i decayRatio) ≠ 0 :=
    star_ne_zero.mpr hNumerator
  rw [Complex.arg_div_coe_angle hNumerator hConjugate,
    Complex.star_def,
    Complex.arg_conj_coe_angle]
  simp [pTotalInternalReflectionPhaseShift, two_nsmul]

/-!

## E. Complex scalar boundary solutions

-/

/-- The full-vector `s` boundary equations determine the complex reflected and transmitted
amplitudes after multiplication by the complex `s` denominator. -/
lemma solve_complexSFresnel_cross_mul (interface : PlanarDielectricInterface)
    {chi_i chi_r chi_t I R T : ℂ}
    (hElectric : T = I + R)
    (hMagnetic :
      ((interface.positiveMedium.waveImpedance⁻¹ : ℝ) : ℂ) * chi_t * T =
        ((interface.negativeMedium.waveImpedance⁻¹ : ℝ) : ℂ) * chi_i * I +
          ((interface.negativeMedium.waveImpedance⁻¹ : ℝ) : ℂ) * chi_r * R)
    (hReflection : R = 0 ∨ chi_r = -chi_i) :
    interface.complexSFresnelDenominator chi_i chi_t * R =
        (((interface.negativeMedium.waveImpedance⁻¹ : ℝ) : ℂ) * chi_i -
          ((interface.positiveMedium.waveImpedance⁻¹ : ℝ) : ℂ) * chi_t) * I ∧
      interface.complexSFresnelDenominator chi_i chi_t * T =
        (2 * ((interface.negativeMedium.waveImpedance⁻¹ : ℝ) : ℂ) * chi_i) * I := by
  rcases hReflection with hZero | hNormal
  · subst R
    simp only [add_zero] at hElectric
    subst T
    simp only [mul_zero, add_zero] at hMagnetic
    constructor <;> simp only [complexSFresnelDenominator]
    · linear_combination hMagnetic
    · linear_combination hMagnetic
  · rw [hNormal, hElectric] at hMagnetic
    have hReflected :
        interface.complexSFresnelDenominator chi_i chi_t * R =
          (((interface.negativeMedium.waveImpedance⁻¹ : ℝ) : ℂ) * chi_i -
            ((interface.positiveMedium.waveImpedance⁻¹ : ℝ) : ℂ) * chi_t) * I := by
      simp only [complexSFresnelDenominator]
      linear_combination hMagnetic
    refine ⟨hReflected, ?_⟩
    rw [hElectric]
    simp only [complexSFresnelDenominator] at hReflected ⊢
    linear_combination hReflected

/-- The full-vector `p` boundary equations determine the complex reflected and transmitted
amplitudes after multiplication by the complex `p` denominator. -/
lemma solve_complexPFresnel_cross_mul (interface : PlanarDielectricInterface)
    {chi_i chi_r chi_t I R T : ℂ}
    (hElectric : chi_t * T = chi_i * I + chi_r * R)
    (hMagnetic :
      ((interface.positiveMedium.waveImpedance⁻¹ : ℝ) : ℂ) * T =
        ((interface.negativeMedium.waveImpedance⁻¹ : ℝ) : ℂ) * I +
          ((interface.negativeMedium.waveImpedance⁻¹ : ℝ) : ℂ) * R)
    (hReflection : R = 0 ∨ chi_r = -chi_i) :
    interface.complexPFresnelDenominator chi_i chi_t * R =
        (((interface.positiveMedium.waveImpedance⁻¹ : ℝ) : ℂ) * chi_i -
          ((interface.negativeMedium.waveImpedance⁻¹ : ℝ) : ℂ) * chi_t) * I ∧
      interface.complexPFresnelDenominator chi_i chi_t * T =
        (2 * ((interface.negativeMedium.waveImpedance⁻¹ : ℝ) : ℂ) * chi_i) * I := by
  rcases hReflection with hZero | hNormal
  · subst R
    simp only [mul_zero, add_zero] at hElectric hMagnetic
    constructor <;> simp only [complexPFresnelDenominator]
    · linear_combination
        ((interface.positiveMedium.waveImpedance⁻¹ : ℝ) : ℂ) * hElectric -
          chi_t * hMagnetic
    · linear_combination
        ((interface.negativeMedium.waveImpedance⁻¹ : ℝ) : ℂ) * hElectric +
          chi_i * hMagnetic
  · rw [hNormal] at hElectric
    have hReflected :
        interface.complexPFresnelDenominator chi_i chi_t * R =
          (((interface.positiveMedium.waveImpedance⁻¹ : ℝ) : ℂ) * chi_i -
            ((interface.negativeMedium.waveImpedance⁻¹ : ℝ) : ℂ) * chi_t) * I := by
      simp only [complexPFresnelDenominator]
      linear_combination
        ((interface.positiveMedium.waveImpedance⁻¹ : ℝ) : ℂ) * hElectric -
          chi_t * hMagnetic
    refine ⟨hReflected, ?_⟩
    simp only [complexPFresnelDenominator] at hElectric hMagnetic hReflected ⊢
    linear_combination
      ((interface.negativeMedium.waveImpedance⁻¹ : ℝ) : ℂ) * hElectric +
        chi_i * hMagnetic

/-- A nonzero complex `s` denominator converts the cross-multiplied boundary solution to the
complex `s` Fresnel coefficients. -/
lemma solve_complexSFresnel (interface : PlanarDielectricInterface)
    {chi_i chi_r chi_t I R T : ℂ}
    (hElectric : T = I + R)
    (hMagnetic :
      ((interface.positiveMedium.waveImpedance⁻¹ : ℝ) : ℂ) * chi_t * T =
        ((interface.negativeMedium.waveImpedance⁻¹ : ℝ) : ℂ) * chi_i * I +
          ((interface.negativeMedium.waveImpedance⁻¹ : ℝ) : ℂ) * chi_r * R)
    (hReflection : R = 0 ∨ chi_r = -chi_i)
    (hDenominator : interface.complexSFresnelDenominator chi_i chi_t ≠ 0) :
    R = interface.complexSFresnelReflectionCoefficient chi_i chi_t * I ∧
      T = interface.complexSFresnelTransmissionCoefficient chi_i chi_t * I := by
  rcases interface.solve_complexSFresnel_cross_mul hElectric hMagnetic hReflection with
    ⟨hReflected, hTransmitted⟩
  constructor
  · have hSolved : R =
        ((((interface.negativeMedium.waveImpedance⁻¹ : ℝ) : ℂ) * chi_i -
          ((interface.positiveMedium.waveImpedance⁻¹ : ℝ) : ℂ) * chi_t) * I) /
            interface.complexSFresnelDenominator chi_i chi_t := by
      apply (eq_div_iff hDenominator).2
      simpa only [mul_comm] using hReflected
    rw [complexSFresnelReflectionCoefficient]
    calc
      R = _ := hSolved
      _ = _ := by ring
  · have hSolved : T =
        ((2 * ((interface.negativeMedium.waveImpedance⁻¹ : ℝ) : ℂ) * chi_i) * I) /
          interface.complexSFresnelDenominator chi_i chi_t := by
      apply (eq_div_iff hDenominator).2
      simpa only [mul_comm] using hTransmitted
    rw [complexSFresnelTransmissionCoefficient]
    calc
      T = _ := hSolved
      _ = _ := by ring

/-- A nonzero complex `p` denominator converts the cross-multiplied boundary solution to the
complex full-vector `p` Fresnel coefficients. -/
lemma solve_complexPFresnel (interface : PlanarDielectricInterface)
    {chi_i chi_r chi_t I R T : ℂ}
    (hElectric : chi_t * T = chi_i * I + chi_r * R)
    (hMagnetic :
      ((interface.positiveMedium.waveImpedance⁻¹ : ℝ) : ℂ) * T =
        ((interface.negativeMedium.waveImpedance⁻¹ : ℝ) : ℂ) * I +
          ((interface.negativeMedium.waveImpedance⁻¹ : ℝ) : ℂ) * R)
    (hReflection : R = 0 ∨ chi_r = -chi_i)
    (hDenominator : interface.complexPFresnelDenominator chi_i chi_t ≠ 0) :
    R = interface.complexPFresnelReflectionCoefficient chi_i chi_t * I ∧
      T = interface.complexPFresnelTransmissionCoefficient chi_i chi_t * I := by
  rcases interface.solve_complexPFresnel_cross_mul hElectric hMagnetic hReflection with
    ⟨hReflected, hTransmitted⟩
  constructor
  · have hSolved : R =
        ((((interface.positiveMedium.waveImpedance⁻¹ : ℝ) : ℂ) * chi_i -
          ((interface.negativeMedium.waveImpedance⁻¹ : ℝ) : ℂ) * chi_t) * I) /
            interface.complexPFresnelDenominator chi_i chi_t := by
      apply (eq_div_iff hDenominator).2
      simpa only [mul_comm] using hReflected
    rw [complexPFresnelReflectionCoefficient]
    calc
      R = _ := hSolved
      _ = _ := by ring
  · have hSolved : T =
        ((2 * ((interface.negativeMedium.waveImpedance⁻¹ : ℝ) : ℂ) * chi_i) * I) /
          interface.complexPFresnelDenominator chi_i chi_t := by
      apply (eq_div_iff hDenominator).2
      simpa only [mul_comm] using hTransmitted
    rw [complexPFresnelTransmissionCoefficient]
    calc
      T = _ := hSolved
      _ = _ := by ring

end PlanarDielectricInterface

namespace PlanarDielectricWaveConfiguration

open ClassicalMechanics Electromagnetism.ThreeDimension Space InnerProductSpace
open Electromagnetism.ThreeDimension.ComplexMonochromaticPlaneWave

/-!

## F. Physical positive-normal-decay modulus and phase

-/

/-- The canonical positive-normal-decay `s` reflection coefficient has unit modulus for a
strictly positive incident normal component. -/
lemma positiveNormalDecay_complexSFresnelReflectionCoefficient_norm
    (configuration : PlanarDielectricWaveConfiguration)
    (hRadicand : configuration.transmittedNormalRadicand < 0)
    {incidentDirection : Space.Direction 3}
    (incidentFrame : PolarizationFrame incidentDirection)
    (hIncidentNormal : 0 <
      configuration.interface.plane.normalComponent incidentFrame.propagationVector) :
    ‖configuration.interface.complexSFresnelReflectionCoefficient
      (configuration.interface.plane.normalComponent incidentFrame.propagationVector : ℂ)
      ((configuration.positiveNormalDecayTransmittedPolarizationFrame
        hRadicand).normalizedWaveVectorNormalComponent configuration.interface.plane)‖ = 1 := by
  rw [configuration.positiveNormalDecayTransmitted_normalizedWaveVectorNormalComponent
    hRadicand]
  exact configuration.interface.complexSFresnelReflectionCoefficient_norm_of_neg_I_mul
    hIncidentNormal

/-- The canonical positive-normal-decay `p` reflection coefficient has unit modulus for a
strictly positive incident normal component. -/
lemma positiveNormalDecay_complexPFresnelReflectionCoefficient_norm
    (configuration : PlanarDielectricWaveConfiguration)
    (hRadicand : configuration.transmittedNormalRadicand < 0)
    {incidentDirection : Space.Direction 3}
    (incidentFrame : PolarizationFrame incidentDirection)
    (hIncidentNormal : 0 <
      configuration.interface.plane.normalComponent incidentFrame.propagationVector) :
    ‖configuration.interface.complexPFresnelReflectionCoefficient
      (configuration.interface.plane.normalComponent incidentFrame.propagationVector : ℂ)
      ((configuration.positiveNormalDecayTransmittedPolarizationFrame
        hRadicand).normalizedWaveVectorNormalComponent configuration.interface.plane)‖ = 1 := by
  rw [configuration.positiveNormalDecayTransmitted_normalizedWaveVectorNormalComponent
    hRadicand]
  exact configuration.interface.complexPFresnelReflectionCoefficient_norm_of_neg_I_mul
    hIncidentNormal

/-- The phase of the canonical positive-normal-decay `s` reflection coefficient is twice the
first-quadrant numerator angle in Physlib's positive-time phasor convention. -/
lemma positiveNormalDecay_complexSFresnelReflectionCoefficient_phase
    (configuration : PlanarDielectricWaveConfiguration)
    (hRadicand : configuration.transmittedNormalRadicand < 0)
    {incidentDirection : Space.Direction 3}
    (incidentFrame : PolarizationFrame incidentDirection)
    (hIncidentNormal : 0 <
      configuration.interface.plane.normalComponent incidentFrame.propagationVector) :
    (Complex.arg (configuration.interface.complexSFresnelReflectionCoefficient
      (configuration.interface.plane.normalComponent incidentFrame.propagationVector : ℂ)
      ((configuration.positiveNormalDecayTransmittedPolarizationFrame
        hRadicand).normalizedWaveVectorNormalComponent configuration.interface.plane)) :
        Real.Angle) =
      configuration.interface.sTotalInternalReflectionPhaseShift
        (configuration.interface.plane.normalComponent incidentFrame.propagationVector)
        (Real.sqrt (-configuration.transmittedNormalRadicand) /
          (configuration.incident.angularFrequency /
            configuration.interface.positiveMedium.waveSpeed)) := by
  rw [configuration.positiveNormalDecayTransmitted_normalizedWaveVectorNormalComponent
    hRadicand]
  exact configuration.interface.complexSFresnelReflectionCoefficient_phase_of_neg_I_mul
    hIncidentNormal

/-- The phase of the canonical positive-normal-decay `p` reflection coefficient is twice the
first-quadrant numerator angle in Physlib's positive-time phasor convention. -/
lemma positiveNormalDecay_complexPFresnelReflectionCoefficient_phase
    (configuration : PlanarDielectricWaveConfiguration)
    (hRadicand : configuration.transmittedNormalRadicand < 0)
    {incidentDirection : Space.Direction 3}
    (incidentFrame : PolarizationFrame incidentDirection)
    (hIncidentNormal : 0 <
      configuration.interface.plane.normalComponent incidentFrame.propagationVector) :
    (Complex.arg (configuration.interface.complexPFresnelReflectionCoefficient
      (configuration.interface.plane.normalComponent incidentFrame.propagationVector : ℂ)
      ((configuration.positiveNormalDecayTransmittedPolarizationFrame
        hRadicand).normalizedWaveVectorNormalComponent configuration.interface.plane)) :
        Real.Angle) =
      configuration.interface.pTotalInternalReflectionPhaseShift
        (configuration.interface.plane.normalComponent incidentFrame.propagationVector)
        (Real.sqrt (-configuration.transmittedNormalRadicand) /
          (configuration.incident.angularFrequency /
            configuration.interface.positiveMedium.waveSpeed)) := by
  rw [configuration.positiveNormalDecayTransmitted_normalizedWaveVectorNormalComponent
    hRadicand]
  exact configuration.interface.complexPFresnelReflectionCoefficient_phase_of_neg_I_mul
    hIncidentNormal

/-!

## G. Hybrid propagating-decay Jones boundary equations

-/

variable {configuration : PlanarDielectricWaveConfiguration}
  {incidentDirection reflectedDirection : Space.Direction 3}
  {incidentFrame : PolarizationFrame incidentDirection}
  {reflectedFrame : PolarizationFrame reflectedDirection}
  {incidentJones reflectedJones transmittedRawJones : JonesVector}

namespace HasReferencedJointElectricBalance

/-- The common `s` coordinate of referenced tangential electric balance for the canonical
positive-normal-decay transmitted carrier. -/
lemma positiveNormalDecay_jones_component_zero
    (h : configuration.HasReferencedJointElectricBalance)
    (hRadicand : configuration.transmittedNormalRadicand < 0)
    (hIncident : IsReferencedMaterialJonesWave configuration.interface.plane
      configuration.interface.negativeMedium configuration.incident incidentFrame incidentJones)
    (hReflected : IsZeroOrReferencedMaterialJonesWave configuration.interface.plane
      configuration.interface.negativeMedium configuration.reflected reflectedFrame reflectedJones)
    (hTransmitted : configuration.transmitted =
      configuration.positiveNormalDecayTransmittedJonesCandidate hRadicand transmittedRawJones)
    (hIncidentAlign : incidentFrame.axis 0 =
      (configuration.positiveNormalDecayTransmittedPolarizationFrame hRadicand).planeFrame.axis 0)
    (hReflectedAlign : reflectedFrame.axis 0 =
      (configuration.positiveNormalDecayTransmittedPolarizationFrame hRadicand).planeFrame.axis 0) :
    (configuration.positiveNormalDecayTransmittedReferencedJones
        transmittedRawJones).components 0 =
      incidentJones.components 0 + reflectedJones.components 0 := by
  have hAmplitude := congrArg Prod.fst h
  simp only [Prod.fst_add] at hAmplitude
  rw [hTransmitted,
    configuration.positiveNormalDecayTransmittedJonesCandidate_referencedTangentialElectricAmplitude
      hRadicand transmittedRawJones,
    hIncident.referencedMediumJointElectricTraceAmplitude_fst_eq_planarFrame
      (configuration.positiveNormalDecayTransmittedPolarizationFrame hRadicand).planeFrame
        hIncidentAlign,
    hReflected.referencedMediumJointElectricTraceAmplitude_fst_eq_planarFrame
      (configuration.positiveNormalDecayTransmittedPolarizationFrame hRadicand).planeFrame
        hReflectedAlign] at hAmplitude
  have hCoordinate := congrArg
    (fun v ↦ ⟪(configuration.positiveNormalDecayTransmittedPolarizationFrame
      hRadicand).planeFrame.complexAxis 0, v⟫_ℂ) hAmplitude
  simpa [PositiveNormalDecayPolarizationFrame.tangentialJones, inner_add_right,
    PolarizationFrame.inner_complexAxis_embedJones] using hCoordinate

/-- The common tangential `p` coordinate of referenced electric balance carries the complex
normalized transmitted normal factor. -/
lemma positiveNormalDecay_jones_component_one
    (h : configuration.HasReferencedJointElectricBalance)
    (hRadicand : configuration.transmittedNormalRadicand < 0)
    (hIncident : IsReferencedMaterialJonesWave configuration.interface.plane
      configuration.interface.negativeMedium configuration.incident incidentFrame incidentJones)
    (hReflected : IsZeroOrReferencedMaterialJonesWave configuration.interface.plane
      configuration.interface.negativeMedium configuration.reflected reflectedFrame reflectedJones)
    (hTransmitted : configuration.transmitted =
      configuration.positiveNormalDecayTransmittedJonesCandidate hRadicand transmittedRawJones)
    (hIncidentAlign : incidentFrame.axis 0 =
      (configuration.positiveNormalDecayTransmittedPolarizationFrame hRadicand).planeFrame.axis 0)
    (hReflectedAlign : reflectedFrame.axis 0 =
      (configuration.positiveNormalDecayTransmittedPolarizationFrame hRadicand).planeFrame.axis 0) :
    (configuration.positiveNormalDecayTransmittedPolarizationFrame
        hRadicand).normalizedWaveVectorNormalComponent configuration.interface.plane *
        (configuration.positiveNormalDecayTransmittedReferencedJones
          transmittedRawJones).components 1 =
      (configuration.interface.plane.normalComponent
        incidentFrame.propagationVector : ℂ) * incidentJones.components 1 +
      (configuration.interface.plane.normalComponent
        reflectedFrame.propagationVector : ℂ) * reflectedJones.components 1 := by
  have hAmplitude := congrArg Prod.fst h
  simp only [Prod.fst_add] at hAmplitude
  rw [hTransmitted,
    configuration.positiveNormalDecayTransmittedJonesCandidate_referencedTangentialElectricAmplitude
      hRadicand transmittedRawJones,
    hIncident.referencedMediumJointElectricTraceAmplitude_fst_eq_planarFrame
      (configuration.positiveNormalDecayTransmittedPolarizationFrame hRadicand).planeFrame
        hIncidentAlign,
    hReflected.referencedMediumJointElectricTraceAmplitude_fst_eq_planarFrame
      (configuration.positiveNormalDecayTransmittedPolarizationFrame hRadicand).planeFrame
        hReflectedAlign] at hAmplitude
  have hCoordinate := congrArg
    (fun v ↦ ⟪(configuration.positiveNormalDecayTransmittedPolarizationFrame
      hRadicand).planeFrame.complexAxis 1, v⟫_ℂ) hAmplitude
  simpa [PositiveNormalDecayPolarizationFrame.tangentialJones, inner_add_right,
    PolarizationFrame.inner_complexAxis_embedJones] using hCoordinate

end HasReferencedJointElectricBalance

namespace HasReferencedTangentialMagneticFieldStrengthBalance

/-- The magnetic boundary equation carried by the `s` coordinate for the canonical
positive-normal-decay transmitted carrier. -/
lemma positiveNormalDecay_jones_component_zero
    (h : configuration.HasReferencedTangentialMagneticFieldStrengthBalance)
    (hRadicand : configuration.transmittedNormalRadicand < 0)
    (hIncident : IsReferencedMaterialJonesWave configuration.interface.plane
      configuration.interface.negativeMedium configuration.incident incidentFrame incidentJones)
    (hReflected : IsZeroOrReferencedMaterialJonesWave configuration.interface.plane
      configuration.interface.negativeMedium configuration.reflected reflectedFrame reflectedJones)
    (hTransmitted : configuration.transmitted =
      configuration.positiveNormalDecayTransmittedJonesCandidate hRadicand transmittedRawJones)
    (hIncidentAlign : incidentFrame.axis 0 =
      (configuration.positiveNormalDecayTransmittedPolarizationFrame hRadicand).planeFrame.axis 0)
    (hReflectedAlign : reflectedFrame.axis 0 =
      (configuration.positiveNormalDecayTransmittedPolarizationFrame hRadicand).planeFrame.axis 0) :
    ((configuration.interface.positiveMedium.waveImpedance⁻¹ : ℝ) : ℂ) *
        (configuration.positiveNormalDecayTransmittedPolarizationFrame
          hRadicand).normalizedWaveVectorNormalComponent configuration.interface.plane *
        (configuration.positiveNormalDecayTransmittedReferencedJones
          transmittedRawJones).components 0 =
      ((configuration.interface.negativeMedium.waveImpedance⁻¹ : ℝ) : ℂ) *
          (configuration.interface.plane.normalComponent
            incidentFrame.propagationVector : ℂ) * incidentJones.components 0 +
        ((configuration.interface.negativeMedium.waveImpedance⁻¹ : ℝ) : ℂ) *
          (configuration.interface.plane.normalComponent
            reflectedFrame.propagationVector : ℂ) * reflectedJones.components 0 := by
  change
    referencedMediumTangentialMagneticFieldStrengthAmplitude configuration.interface.plane
        configuration.interface.positiveMedium configuration.transmitted =
      referencedMediumTangentialMagneticFieldStrengthAmplitude configuration.interface.plane
          configuration.interface.negativeMedium configuration.incident +
        referencedMediumTangentialMagneticFieldStrengthAmplitude configuration.interface.plane
          configuration.interface.negativeMedium configuration.reflected at h
  rw [hTransmitted,
    positiveNormalDecayTransmittedJonesCandidate_referencedTangentialMagneticFieldStrengthAmplitude
      configuration hRadicand transmittedRawJones,
    hIncident.referencedMediumTangentialMagneticFieldStrengthAmplitude_eq_planarFrame
      (configuration.positiveNormalDecayTransmittedPolarizationFrame hRadicand).planeFrame
        hIncidentAlign,
    hReflected.referencedMediumTangentialMagneticFieldStrengthAmplitude_eq_planarFrame
      (configuration.positiveNormalDecayTransmittedPolarizationFrame hRadicand).planeFrame
        hReflectedAlign] at h
  have hCoordinate := congrArg
    (fun v ↦ ⟪(configuration.positiveNormalDecayTransmittedPolarizationFrame
      hRadicand).planeFrame.complexAxis 1, v⟫_ℂ) h
  simpa [inner_add_right, inner_smul_right,
    PolarizationFrame.inner_complexAxis_embedJones, mul_assoc] using hCoordinate

/-- The magnetic boundary equation carried by the `p` coordinate for the canonical
positive-normal-decay transmitted carrier. -/
lemma positiveNormalDecay_jones_component_one
    (h : configuration.HasReferencedTangentialMagneticFieldStrengthBalance)
    (hRadicand : configuration.transmittedNormalRadicand < 0)
    (hIncident : IsReferencedMaterialJonesWave configuration.interface.plane
      configuration.interface.negativeMedium configuration.incident incidentFrame incidentJones)
    (hReflected : IsZeroOrReferencedMaterialJonesWave configuration.interface.plane
      configuration.interface.negativeMedium configuration.reflected reflectedFrame reflectedJones)
    (hTransmitted : configuration.transmitted =
      configuration.positiveNormalDecayTransmittedJonesCandidate hRadicand transmittedRawJones)
    (hIncidentAlign : incidentFrame.axis 0 =
      (configuration.positiveNormalDecayTransmittedPolarizationFrame hRadicand).planeFrame.axis 0)
    (hReflectedAlign : reflectedFrame.axis 0 =
      (configuration.positiveNormalDecayTransmittedPolarizationFrame hRadicand).planeFrame.axis 0) :
    ((configuration.interface.positiveMedium.waveImpedance⁻¹ : ℝ) : ℂ) *
        (configuration.positiveNormalDecayTransmittedReferencedJones
          transmittedRawJones).components 1 =
      ((configuration.interface.negativeMedium.waveImpedance⁻¹ : ℝ) : ℂ) *
          incidentJones.components 1 +
        ((configuration.interface.negativeMedium.waveImpedance⁻¹ : ℝ) : ℂ) *
          reflectedJones.components 1 := by
  change
    referencedMediumTangentialMagneticFieldStrengthAmplitude configuration.interface.plane
        configuration.interface.positiveMedium configuration.transmitted =
      referencedMediumTangentialMagneticFieldStrengthAmplitude configuration.interface.plane
          configuration.interface.negativeMedium configuration.incident +
        referencedMediumTangentialMagneticFieldStrengthAmplitude configuration.interface.plane
          configuration.interface.negativeMedium configuration.reflected at h
  rw [hTransmitted,
    positiveNormalDecayTransmittedJonesCandidate_referencedTangentialMagneticFieldStrengthAmplitude
      configuration hRadicand transmittedRawJones,
    hIncident.referencedMediumTangentialMagneticFieldStrengthAmplitude_eq_planarFrame
      (configuration.positiveNormalDecayTransmittedPolarizationFrame hRadicand).planeFrame
        hIncidentAlign,
    hReflected.referencedMediumTangentialMagneticFieldStrengthAmplitude_eq_planarFrame
      (configuration.positiveNormalDecayTransmittedPolarizationFrame hRadicand).planeFrame
        hReflectedAlign] at h
  have hCoordinate := congrArg
    (fun v ↦ ⟪(configuration.positiveNormalDecayTransmittedPolarizationFrame
      hRadicand).planeFrame.complexAxis 0, v⟫_ℂ) h
  have hNegated :
      -((configuration.interface.positiveMedium.waveImpedance⁻¹ : ℝ) : ℂ) *
          (configuration.positiveNormalDecayTransmittedReferencedJones
            transmittedRawJones).components 1 =
        -((configuration.interface.negativeMedium.waveImpedance⁻¹ : ℝ) : ℂ) *
            incidentJones.components 1 +
          -((configuration.interface.negativeMedium.waveImpedance⁻¹ : ℝ) : ℂ) *
            reflectedJones.components 1 := by
    simpa [inner_add_right, inner_smul_right,
      PolarizationFrame.inner_complexAxis_embedJones] using hCoordinate
  linear_combination -hNegated

end HasReferencedTangentialMagneticFieldStrengthBalance

/-!

## H. Boundary-selected positive-normal-decay Fresnel amplitudes

-/

/-- Referenced electric and magnetic balance select all four complex Fresnel component laws for
the canonical positive-normal-decay transmitted carrier in explicitly aligned Jones frames.

The reflected guard is stated on Jones data, so its zero branch leaves the reflected normal
unrestricted. The wave-level wrapper below also removes the alignment requirement from an
electrically zero reflected dummy frame. -/
lemma complexFresnel_components_of_referenced_balances_of_jones_guard
    (hElectric : configuration.HasReferencedJointElectricBalance)
    (hMagnetic : configuration.HasReferencedTangentialMagneticFieldStrengthBalance)
    (hRadicand : configuration.transmittedNormalRadicand < 0)
    (hIncident : IsReferencedMaterialJonesWave configuration.interface.plane
      configuration.interface.negativeMedium configuration.incident incidentFrame incidentJones)
    (hReflected : IsZeroOrReferencedMaterialJonesWave configuration.interface.plane
      configuration.interface.negativeMedium configuration.reflected reflectedFrame reflectedJones)
    (hTransmitted : configuration.transmitted =
      configuration.positiveNormalDecayTransmittedJonesCandidate hRadicand transmittedRawJones)
    (hIncidentAlign : incidentFrame.axis 0 =
      (configuration.positiveNormalDecayTransmittedPolarizationFrame hRadicand).planeFrame.axis 0)
    (hReflectedAlign : reflectedFrame.axis 0 =
      (configuration.positiveNormalDecayTransmittedPolarizationFrame hRadicand).planeFrame.axis 0)
    (hReflection : reflectedJones.components = 0 ∨
      configuration.interface.plane.normalComponent reflectedFrame.propagationVector =
        -configuration.interface.plane.normalComponent incidentFrame.propagationVector)
    (hIncidentNormal : 0 <
      configuration.interface.plane.normalComponent incidentFrame.propagationVector) :
    reflectedJones.components 0 =
        configuration.interface.complexSFresnelReflectionCoefficient
          (configuration.interface.plane.normalComponent
            incidentFrame.propagationVector : ℂ)
          ((configuration.positiveNormalDecayTransmittedPolarizationFrame
            hRadicand).normalizedWaveVectorNormalComponent configuration.interface.plane) *
          incidentJones.components 0 ∧
      (configuration.positiveNormalDecayTransmittedReferencedJones
        transmittedRawJones).components 0 =
        configuration.interface.complexSFresnelTransmissionCoefficient
          (configuration.interface.plane.normalComponent
            incidentFrame.propagationVector : ℂ)
          ((configuration.positiveNormalDecayTransmittedPolarizationFrame
            hRadicand).normalizedWaveVectorNormalComponent configuration.interface.plane) *
          incidentJones.components 0 ∧
      reflectedJones.components 1 =
        configuration.interface.complexPFresnelReflectionCoefficient
          (configuration.interface.plane.normalComponent
            incidentFrame.propagationVector : ℂ)
          ((configuration.positiveNormalDecayTransmittedPolarizationFrame
            hRadicand).normalizedWaveVectorNormalComponent configuration.interface.plane) *
          incidentJones.components 1 ∧
      (configuration.positiveNormalDecayTransmittedReferencedJones
        transmittedRawJones).components 1 =
        configuration.interface.complexPFresnelTransmissionCoefficient
          (configuration.interface.plane.normalComponent
            incidentFrame.propagationVector : ℂ)
          ((configuration.positiveNormalDecayTransmittedPolarizationFrame
            hRadicand).normalizedWaveVectorNormalComponent configuration.interface.plane) *
          incidentJones.components 1 := by
  have hElectricS :=
    HasReferencedJointElectricBalance.positiveNormalDecay_jones_component_zero hElectric
      hRadicand hIncident hReflected hTransmitted hIncidentAlign hReflectedAlign
  have hElectricP :=
    HasReferencedJointElectricBalance.positiveNormalDecay_jones_component_one hElectric
      hRadicand hIncident hReflected hTransmitted hIncidentAlign hReflectedAlign
  have hMagneticS :=
    HasReferencedTangentialMagneticFieldStrengthBalance.positiveNormalDecay_jones_component_zero
      hMagnetic hRadicand hIncident hReflected hTransmitted hIncidentAlign hReflectedAlign
  have hMagneticP :=
    HasReferencedTangentialMagneticFieldStrengthBalance.positiveNormalDecay_jones_component_one
      hMagnetic hRadicand hIncident hReflected hTransmitted hIncidentAlign hReflectedAlign
  have hReflectionComponent (i : Fin 2) :
      reflectedJones.components i = 0 ∨
        (configuration.interface.plane.normalComponent
          reflectedFrame.propagationVector : ℂ) =
          -(configuration.interface.plane.normalComponent
            incidentFrame.propagationVector : ℂ) := by
    rcases hReflection with hZero | hNormal
    · left
      simpa using congrArg (fun v : EuclideanSpace ℂ (Fin 2) ↦ v i) hZero
    · right
      exact_mod_cast hNormal
  have hSDenominator :
      configuration.interface.complexSFresnelDenominator
        (configuration.interface.plane.normalComponent incidentFrame.propagationVector : ℂ)
        ((configuration.positiveNormalDecayTransmittedPolarizationFrame
          hRadicand).normalizedWaveVectorNormalComponent configuration.interface.plane) ≠ 0 := by
    rw [configuration.positiveNormalDecayTransmitted_normalizedWaveVectorNormalComponent
      hRadicand]
    exact configuration.interface.complexSFresnelDenominator_ne_zero_of_neg_I_mul
      hIncidentNormal
  have hPDenominator :
      configuration.interface.complexPFresnelDenominator
        (configuration.interface.plane.normalComponent incidentFrame.propagationVector : ℂ)
        ((configuration.positiveNormalDecayTransmittedPolarizationFrame
          hRadicand).normalizedWaveVectorNormalComponent configuration.interface.plane) ≠ 0 := by
    rw [configuration.positiveNormalDecayTransmitted_normalizedWaveVectorNormalComponent
      hRadicand]
    exact configuration.interface.complexPFresnelDenominator_ne_zero_of_neg_I_mul
      hIncidentNormal
  rcases configuration.interface.solve_complexSFresnel hElectricS hMagneticS
      (hReflectionComponent 0) hSDenominator with ⟨hReflectedS, hTransmittedS⟩
  rcases configuration.interface.solve_complexPFresnel hElectricP hMagneticP
      (hReflectionComponent 1) hPDenominator with ⟨hReflectedP, hTransmittedP⟩
  exact ⟨hReflectedS, hTransmittedS, hReflectedP, hTransmittedP⟩

/-- The wave-level reflected guard gives the four complex Fresnel component laws while preserving
arbitrary dummy carrier and frame data for an electrically zero reflected wave. -/
lemma complexFresnel_components_of_referenced_balances
    (hElectric : configuration.HasReferencedJointElectricBalance)
    (hMagnetic : configuration.HasReferencedTangentialMagneticFieldStrengthBalance)
    (hRadicand : configuration.transmittedNormalRadicand < 0)
    (hIncident : IsReferencedMaterialJonesWave configuration.interface.plane
      configuration.interface.negativeMedium configuration.incident incidentFrame incidentJones)
    (hReflected : IsZeroOrReferencedMaterialJonesWave configuration.interface.plane
      configuration.interface.negativeMedium configuration.reflected reflectedFrame reflectedJones)
    (hTransmitted : configuration.transmitted =
      configuration.positiveNormalDecayTransmittedJonesCandidate hRadicand transmittedRawJones)
    (hIncidentAlign : incidentFrame.axis 0 =
      (configuration.positiveNormalDecayTransmittedPolarizationFrame hRadicand).planeFrame.axis 0)
    (hReflectedAlign : configuration.reflected.electricAmplitude ≠ 0 →
      reflectedFrame.axis 0 =
        (configuration.positiveNormalDecayTransmittedPolarizationFrame hRadicand).planeFrame.axis 0)
    (hReflection : configuration.reflected.electricAmplitude = 0 ∨
      configuration.interface.plane.normalComponent reflectedFrame.propagationVector =
        -configuration.interface.plane.normalComponent incidentFrame.propagationVector)
    (hIncidentNormal : 0 <
      configuration.interface.plane.normalComponent incidentFrame.propagationVector) :
    reflectedJones.components 0 =
        configuration.interface.complexSFresnelReflectionCoefficient
          (configuration.interface.plane.normalComponent
            incidentFrame.propagationVector : ℂ)
          ((configuration.positiveNormalDecayTransmittedPolarizationFrame
            hRadicand).normalizedWaveVectorNormalComponent configuration.interface.plane) *
          incidentJones.components 0 ∧
      (configuration.positiveNormalDecayTransmittedReferencedJones
        transmittedRawJones).components 0 =
        configuration.interface.complexSFresnelTransmissionCoefficient
          (configuration.interface.plane.normalComponent
            incidentFrame.propagationVector : ℂ)
          ((configuration.positiveNormalDecayTransmittedPolarizationFrame
            hRadicand).normalizedWaveVectorNormalComponent configuration.interface.plane) *
          incidentJones.components 0 ∧
      reflectedJones.components 1 =
        configuration.interface.complexPFresnelReflectionCoefficient
          (configuration.interface.plane.normalComponent
            incidentFrame.propagationVector : ℂ)
          ((configuration.positiveNormalDecayTransmittedPolarizationFrame
            hRadicand).normalizedWaveVectorNormalComponent configuration.interface.plane) *
          incidentJones.components 1 ∧
      (configuration.positiveNormalDecayTransmittedReferencedJones
        transmittedRawJones).components 1 =
        configuration.interface.complexPFresnelTransmissionCoefficient
          (configuration.interface.plane.normalComponent
            incidentFrame.propagationVector : ℂ)
          ((configuration.positiveNormalDecayTransmittedPolarizationFrame
            hRadicand).normalizedWaveVectorNormalComponent configuration.interface.plane) *
          incidentJones.components 1 := by
  by_cases hZero : configuration.reflected.electricAmplitude = 0
  · have hReflectedZero := hReflected.reframe_of_electricAmplitude_eq_zero
      (configuration.positiveNormalDecayTransmittedPolarizationFrame hRadicand).planeFrame hZero
    have hJonesZero := hReflected.components_eq_zero_of_electricAmplitude_eq_zero hZero
    exact complexFresnel_components_of_referenced_balances_of_jones_guard hElectric hMagnetic
      hRadicand hIncident hReflectedZero hTransmitted hIncidentAlign rfl (Or.inl hJonesZero)
        hIncidentNormal
  · have hNormal := hReflection.resolve_left hZero
    exact complexFresnel_components_of_referenced_balances_of_jones_guard hElectric hMagnetic
      hRadicand hIncident hReflected hTransmitted hIncidentAlign (hReflectedAlign hZero)
        (Or.inr hNormal) hIncidentNormal

/-- The boundary-selected complex `p` amplitudes in one fixed interface-plane gauge.

The reflected full-vector coefficient acquires a minus sign, while tangential projection of the
transmitted decay-frame amplitude contributes its complex normalized normal factor. -/
lemma complexFresnel_tangential_p_components_of_referenced_balances
    (hElectric : configuration.HasReferencedJointElectricBalance)
    (hMagnetic : configuration.HasReferencedTangentialMagneticFieldStrengthBalance)
    (hRadicand : configuration.transmittedNormalRadicand < 0)
    (hIncident : IsReferencedMaterialJonesWave configuration.interface.plane
      configuration.interface.negativeMedium configuration.incident incidentFrame incidentJones)
    (hReflected : IsZeroOrReferencedMaterialJonesWave configuration.interface.plane
      configuration.interface.negativeMedium configuration.reflected reflectedFrame reflectedJones)
    (hTransmitted : configuration.transmitted =
      configuration.positiveNormalDecayTransmittedJonesCandidate hRadicand transmittedRawJones)
    (hIncidentAlign : incidentFrame.axis 0 =
      (configuration.positiveNormalDecayTransmittedPolarizationFrame hRadicand).planeFrame.axis 0)
    (hReflectedAlign : configuration.reflected.electricAmplitude ≠ 0 →
      reflectedFrame.axis 0 =
        (configuration.positiveNormalDecayTransmittedPolarizationFrame hRadicand).planeFrame.axis 0)
    (hReflection : configuration.reflected.electricAmplitude = 0 ∨
      configuration.interface.plane.normalComponent reflectedFrame.propagationVector =
        -configuration.interface.plane.normalComponent incidentFrame.propagationVector)
    (hIncidentNormal : 0 <
      configuration.interface.plane.normalComponent incidentFrame.propagationVector) :
    reflectedFrame.normalScaledSecondComponent configuration.interface.plane reflectedJones =
        configuration.interface.complexTangentialPFresnelReflectionCoefficient
          (configuration.interface.plane.normalComponent
            incidentFrame.propagationVector : ℂ)
          ((configuration.positiveNormalDecayTransmittedPolarizationFrame
            hRadicand).normalizedWaveVectorNormalComponent configuration.interface.plane) *
          incidentFrame.normalScaledSecondComponent configuration.interface.plane incidentJones ∧
      (configuration.positiveNormalDecayTransmittedPolarizationFrame
          hRadicand).normalizedWaveVectorNormalComponent configuration.interface.plane *
        (configuration.positiveNormalDecayTransmittedReferencedJones
          transmittedRawJones).components 1 =
        configuration.interface.complexTangentialPFresnelTransmissionCoefficient
          (configuration.interface.plane.normalComponent
            incidentFrame.propagationVector : ℂ)
          ((configuration.positiveNormalDecayTransmittedPolarizationFrame
            hRadicand).normalizedWaveVectorNormalComponent configuration.interface.plane) *
          incidentFrame.normalScaledSecondComponent configuration.interface.plane
            incidentJones := by
  have hSolved := complexFresnel_components_of_referenced_balances hElectric hMagnetic
    hRadicand hIncident hReflected hTransmitted hIncidentAlign hReflectedAlign hReflection
      hIncidentNormal
  have hReflectionP : reflectedJones.components 1 = 0 ∨
      (configuration.interface.plane.normalComponent
        reflectedFrame.propagationVector : ℂ) =
        -(configuration.interface.plane.normalComponent
          incidentFrame.propagationVector : ℂ) := by
    by_cases hZero : configuration.reflected.electricAmplitude = 0
    · left
      have hComponents := hReflected.components_eq_zero_of_electricAmplitude_eq_zero hZero
      simpa using congrArg (fun v : EuclideanSpace ℂ (Fin 2) ↦ v 1) hComponents
    · right
      exact_mod_cast hReflection.resolve_left hZero
  have hReflectedP :=
    configuration.interface.complexTangentialPFresnelReflectionAmplitude_of_guard
      hSolved.2.2.1 hReflectionP
  have hTransmittedP :=
    configuration.interface.complexTangentialPFresnelTransmissionAmplitude hSolved.2.2.2
  constructor
  · simpa [PolarizationFrame.normalScaledSecondComponent] using hReflectedP
  · simpa [PolarizationFrame.normalScaledSecondComponent] using hTransmittedP

/-- Boundary-selected total internal reflection preserves the raw Jones intensity of the
propagating reflected wave.

This is an incident-versus-reflected statement in the common negative medium. It does not treat
the transmitted decay-frame Jones intensity as electromagnetic power. -/
lemma complexFresnel_reflectedJones_intensity_eq_of_referenced_balances
    (hElectric : configuration.HasReferencedJointElectricBalance)
    (hMagnetic : configuration.HasReferencedTangentialMagneticFieldStrengthBalance)
    (hRadicand : configuration.transmittedNormalRadicand < 0)
    (hIncident : IsReferencedMaterialJonesWave configuration.interface.plane
      configuration.interface.negativeMedium configuration.incident incidentFrame incidentJones)
    (hReflected : IsZeroOrReferencedMaterialJonesWave configuration.interface.plane
      configuration.interface.negativeMedium configuration.reflected reflectedFrame reflectedJones)
    (hTransmitted : configuration.transmitted =
      configuration.positiveNormalDecayTransmittedJonesCandidate hRadicand transmittedRawJones)
    (hIncidentAlign : incidentFrame.axis 0 =
      (configuration.positiveNormalDecayTransmittedPolarizationFrame hRadicand).planeFrame.axis 0)
    (hReflectedAlign : configuration.reflected.electricAmplitude ≠ 0 →
      reflectedFrame.axis 0 =
        (configuration.positiveNormalDecayTransmittedPolarizationFrame hRadicand).planeFrame.axis 0)
    (hReflection : configuration.reflected.electricAmplitude = 0 ∨
      configuration.interface.plane.normalComponent reflectedFrame.propagationVector =
        -configuration.interface.plane.normalComponent incidentFrame.propagationVector)
    (hIncidentNormal : 0 <
      configuration.interface.plane.normalComponent incidentFrame.propagationVector) :
    reflectedJones.intensity = incidentJones.intensity := by
  have hSolved := complexFresnel_components_of_referenced_balances hElectric hMagnetic
    hRadicand hIncident hReflected hTransmitted hIncidentAlign hReflectedAlign hReflection
      hIncidentNormal
  have hSNorm := configuration.positiveNormalDecay_complexSFresnelReflectionCoefficient_norm
    hRadicand incidentFrame hIncidentNormal
  have hPNorm := configuration.positiveNormalDecay_complexPFresnelReflectionCoefficient_norm
    hRadicand incidentFrame hIncidentNormal
  have hSNormSq : Complex.normSq
      (configuration.interface.complexSFresnelReflectionCoefficient
        (configuration.interface.plane.normalComponent incidentFrame.propagationVector : ℂ)
        ((configuration.positiveNormalDecayTransmittedPolarizationFrame
          hRadicand).normalizedWaveVectorNormalComponent configuration.interface.plane)) = 1 := by
    rw [Complex.normSq_eq_norm_sq, hSNorm]
    norm_num
  have hPNormSq : Complex.normSq
      (configuration.interface.complexPFresnelReflectionCoefficient
        (configuration.interface.plane.normalComponent incidentFrame.propagationVector : ℂ)
        ((configuration.positiveNormalDecayTransmittedPolarizationFrame
          hRadicand).normalizedWaveVectorNormalComponent configuration.interface.plane)) = 1 := by
    rw [Complex.normSq_eq_norm_sq, hPNorm]
    norm_num
  rw [JonesVector.intensity_eq_sum_normSq, JonesVector.intensity_eq_sum_normSq,
    Fin.sum_univ_two, Fin.sum_univ_two, hSolved.1, hSolved.2.2.1,
    Complex.normSq_mul, Complex.normSq_mul, hSNormSq, hPNormSq]
  norm_num

end PlanarDielectricWaveConfiguration

end

end Optics
