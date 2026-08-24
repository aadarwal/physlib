/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Interfaces.PlanarDielectric.CanonicalIncidence
public import Physlib.Optics.Interfaces.PlanarDielectric.JonesBoundary

/-!
# Fresnel amplitude coefficients for a planar dielectric interface

## i. Overview

This file solves the scalar lossless-dielectric boundary systems that produce the full-vector
Jones convention of `JonesBoundary`. For signed incident, reflected, and transmitted normal
components `chi_i`, `chi_r`, and `chi_t`, the active reflected branch has
`chi_r = -chi_i`. The zero-reflection branch keeps `chi_r` unrestricted because the existing
connector deliberately permits arbitrary carrier data for a zero reflected field.

Writing `Y_j = Z_j⁻¹` for the positive real wave admittance of medium `j`, the denominator values
and coefficients are

```text
D_s = Y₁ chi_i + Y₂ chi_t,
r_s = (Y₁ chi_i - Y₂ chi_t) / D_s,
t_s = 2 Y₁ chi_i / D_s,
D_p = Y₂ chi_i + Y₁ chi_t,
r_p = (Y₂ chi_i - Y₁ chi_t) / D_p,
t_p = 2 Y₁ chi_i / D_p.
```

Here `s` is Jones coordinate zero and `p` is the full electric-vector Jones coordinate one.
Consequently the reflected propagation frame reverses the full-vector `p` sign at normal
incidence, giving `r_p = -r_s` while `t_p = t_s`. These are peak electric-amplitude coefficients,
not fixed-plane tangential-`p` coefficients. The latter convention is also named explicitly:
reflection negates the full-vector coefficient, while transmission changes its numerator from the
incident to the transmitted signed normal component. The conversion is stated without dividing by
the incident normal component and therefore remains algebraically meaningful at grazing incidence.

The primary solution results are cross-multiplied and therefore remain meaningful when a denominator
vanishes. Quotient results require only the matching denominator to be nonzero. Positivity lemmas
derive that condition for strictly positive incident normal component and nonnegative transmitted
normal component. The final results connect the quotient lemmas to the referenced electric and
magnetic equalities and their aligned Jones-wave data. They retain a zero-reflected-field branch
with arbitrary reflected carrier data and require no nonzero incident amplitude. The core result
takes the guarded reflected normal relation explicitly. Its canonical non-normal-incidence wrapper
derives the active relation from phase matching, referenced material data, and explicitly selected
opposite normal signs; no direction follows merely from a wave label. This file states no
irradiance or power law.

## ii. Key results

- `PlanarDielectricInterface.sFresnelDenominator` and
  `PlanarDielectricInterface.pFresnelDenominator`: the two real scalar denominator values.
- `PlanarDielectricInterface.sFresnelReflectionCoefficient` and
  `PlanarDielectricInterface.sFresnelTransmissionCoefficient`: the full-vector `s` coefficients.
- `PlanarDielectricInterface.pFresnelReflectionCoefficient` and
  `PlanarDielectricInterface.pFresnelTransmissionCoefficient`: the full-vector `p` coefficients.
- `PlanarDielectricInterface.tangentialPFresnelReflectionCoefficient` and
  `PlanarDielectricInterface.tangentialPFresnelTransmissionCoefficient`: coefficients for the
  second coordinate in one fixed interface-plane frame.
- `PlanarDielectricInterface.solve_sFresnel_cross_mul` and
  `PlanarDielectricInterface.solve_pFresnel_cross_mul`: guarded denominator-free scalar results.
- `PlanarDielectricInterface.solve_sFresnel` and
  `PlanarDielectricInterface.solve_pFresnel`: quotient forms when the denominator is nonzero.
- `PlanarDielectricWaveConfiguration.fresnel_components_of_referenced_balances_of_jones_guard`:
  the four component formulas from the two referenced equalities and a Jones-zero guard.
- `PlanarDielectricWaveConfiguration.fresnel_components_of_referenced_balances`: the wave-level
  form whose zero branch is stated using the reflected electric amplitude.
- The selected-tangent wrapper
  `fresnel_tangential_components_of_referenced_balances_of_selectedTangentNormalIncidence` gives
  the normal-incidence specialization in one fixed plane frame.
- `PlanarDielectricWaveConfiguration.fresnel_components_of_referenced_balances_of_incidenceFrames`:
  the canonical non-normal-incidence wrapper that derives the common `s`-axis and reflected-normal
  hypotheses while preserving arbitrary zero-reflected carrier data.

## iii. Table of contents

- A. Fresnel denominator values and coefficients
- B. Denominator positivity
- C. Cross-multiplied scalar solutions
- D. Quotient scalar solutions
- E. Normal-incidence signs
- F. Connected Jones boundary solution

## iv. References

The formulas are derived directly from the four scalar boundary equations in `JonesBoundary`.
No external formal-development source is copied or translated here.
-/

@[expose] public section

namespace Optics

open Electromagnetism

noncomputable section

namespace PlanarDielectricInterface

/-!

## A. Fresnel denominator values and coefficients

-/

/-- The real denominator `Y₁ chi_i + Y₂ chi_t` for the full-vector `s` Fresnel coefficients. -/
def sFresnelDenominator (interface : PlanarDielectricInterface)
    (chi_i chi_t : ℝ) : ℝ :=
  interface.negativeMedium.waveImpedance⁻¹ * chi_i +
    interface.positiveMedium.waveImpedance⁻¹ * chi_t

/-- The real denominator `Y₂ chi_i + Y₁ chi_t` for the full-vector `p` Fresnel coefficients. -/
def pFresnelDenominator (interface : PlanarDielectricInterface)
    (chi_i chi_t : ℝ) : ℝ :=
  interface.positiveMedium.waveImpedance⁻¹ * chi_i +
    interface.negativeMedium.waveImpedance⁻¹ * chi_t

/-- The reflected full-vector `s` Jones amplitude divided by the incident `s` amplitude. -/
def sFresnelReflectionCoefficient (interface : PlanarDielectricInterface)
    (chi_i chi_t : ℝ) : ℝ :=
  (interface.negativeMedium.waveImpedance⁻¹ * chi_i -
      interface.positiveMedium.waveImpedance⁻¹ * chi_t) /
    interface.sFresnelDenominator chi_i chi_t

/-- The transmitted full-vector `s` Jones amplitude divided by the incident `s` amplitude. -/
def sFresnelTransmissionCoefficient (interface : PlanarDielectricInterface)
    (chi_i chi_t : ℝ) : ℝ :=
  2 * interface.negativeMedium.waveImpedance⁻¹ * chi_i /
    interface.sFresnelDenominator chi_i chi_t

/-- The reflected full-vector `p` Jones amplitude divided by the incident `p` amplitude.

The propagation-oriented reflected frame gives the sign difference from the familiar
tangential-`p` coefficient. -/
def pFresnelReflectionCoefficient (interface : PlanarDielectricInterface)
    (chi_i chi_t : ℝ) : ℝ :=
  (interface.positiveMedium.waveImpedance⁻¹ * chi_i -
      interface.negativeMedium.waveImpedance⁻¹ * chi_t) /
    interface.pFresnelDenominator chi_i chi_t

/-- The transmitted full-vector `p` Jones amplitude divided by the incident `p` amplitude. -/
def pFresnelTransmissionCoefficient (interface : PlanarDielectricInterface)
    (chi_i chi_t : ℝ) : ℝ :=
  2 * interface.negativeMedium.waveImpedance⁻¹ * chi_i /
    interface.pFresnelDenominator chi_i chi_t

/-- The reflected fixed-plane tangential-`p` amplitude multiplier.

For active reflection, the reflected signed normal is `-chi_i`. Consequently this coefficient is
the negative of the propagation-oriented full-vector `p` reflection coefficient. The definition is
a total algebraic multiplier, not a ratio obtained by dividing actual field amplitudes. -/
def tangentialPFresnelReflectionCoefficient (interface : PlanarDielectricInterface)
    (chi_i chi_t : ℝ) : ℝ :=
  (interface.negativeMedium.waveImpedance⁻¹ * chi_t -
      interface.positiveMedium.waveImpedance⁻¹ * chi_i) /
    interface.pFresnelDenominator chi_i chi_t

/-- The transmitted fixed-plane tangential-`p` amplitude multiplier.

Its numerator contains `chi_t`, because tangential projection converts a transmitted full-vector
`p` component `T` to `chi_t * T`. This total definition performs no division by `chi_i`; converting
it back to a full-vector coefficient requires a nonzero incident normal component. -/
def tangentialPFresnelTransmissionCoefficient (interface : PlanarDielectricInterface)
    (chi_i chi_t : ℝ) : ℝ :=
  2 * interface.negativeMedium.waveImpedance⁻¹ * chi_t /
    interface.pFresnelDenominator chi_i chi_t

/-- The fixed-plane tangential-`p` reflection coefficient is the negative of the full-vector
coefficient. -/
lemma tangentialPFresnelReflectionCoefficient_eq_neg_pFresnelReflectionCoefficient
    (interface : PlanarDielectricInterface) (chi_i chi_t : ℝ) :
    interface.tangentialPFresnelReflectionCoefficient chi_i chi_t =
      -interface.pFresnelReflectionCoefficient chi_i chi_t := by
  rw [tangentialPFresnelReflectionCoefficient, pFresnelReflectionCoefficient]
  ring

/-- Tangential projection converts the transmitted full-vector `p` coefficient without division:
`chi_i * t_p_tangential = chi_t * t_p_full`. -/
lemma tangentialPFresnelTransmissionCoefficient_cross_mul
    (interface : PlanarDielectricInterface) (chi_i chi_t : ℝ) :
    chi_i * interface.tangentialPFresnelTransmissionCoefficient chi_i chi_t =
      chi_t * interface.pFresnelTransmissionCoefficient chi_i chi_t := by
  rw [tangentialPFresnelTransmissionCoefficient, pFresnelTransmissionCoefficient]
  ring

/-- Away from incident grazing, the tangential transmitted `p` coefficient is the full-vector
coefficient multiplied by the transmitted-to-incident signed-normal ratio. -/
lemma tangentialPFresnelTransmissionCoefficient_eq_normalRatio_mul
    (interface : PlanarDielectricInterface) {chi_i chi_t : ℝ} (hIncident : chi_i ≠ 0) :
    interface.tangentialPFresnelTransmissionCoefficient chi_i chi_t =
      (chi_t / chi_i) * interface.pFresnelTransmissionCoefficient chi_i chi_t := by
  calc
    interface.tangentialPFresnelTransmissionCoefficient chi_i chi_t =
        chi_i⁻¹ *
          (chi_i * interface.tangentialPFresnelTransmissionCoefficient chi_i chi_t) := by
      rw [← mul_assoc, inv_mul_cancel₀ hIncident, one_mul]
    _ = chi_i⁻¹ * (chi_t * interface.pFresnelTransmissionCoefficient chi_i chi_t) := by
      rw [interface.tangentialPFresnelTransmissionCoefficient_cross_mul]
    _ = (chi_t / chi_i) * interface.pFresnelTransmissionCoefficient chi_i chi_t := by
      rw [div_eq_mul_inv]
      ring

/-- A full-vector reflected `p` amplitude law converts to the fixed-plane tangential convention
under the same zero-amplitude-or-opposite-normal guard used by the Fresnel solver.

The zero-amplitude branch leaves `chi_r` unrestricted. -/
lemma tangentialPFresnelReflectionAmplitude_of_guard
    (interface : PlanarDielectricInterface) {chi_i chi_r chi_t : ℝ} {I R : ℂ}
    (hAmplitude :
      R = (interface.pFresnelReflectionCoefficient chi_i chi_t : ℂ) * I)
    (hReflection : R = 0 ∨ chi_r = -chi_i) :
    (chi_r : ℂ) * R =
      (interface.tangentialPFresnelReflectionCoefficient chi_i chi_t : ℂ) *
        ((chi_i : ℂ) * I) := by
  have hCoefficient :
      (interface.tangentialPFresnelReflectionCoefficient chi_i chi_t : ℂ) =
        -(interface.pFresnelReflectionCoefficient chi_i chi_t : ℂ) := by
    exact_mod_cast
      interface.tangentialPFresnelReflectionCoefficient_eq_neg_pFresnelReflectionCoefficient
        chi_i chi_t
  rcases hReflection with hZero | hNormal
  · rw [hZero] at hAmplitude ⊢
    simp only [mul_zero] at hAmplitude ⊢
    rw [hCoefficient]
    calc
      0 = -(chi_i : ℂ) *
          ((interface.pFresnelReflectionCoefficient chi_i chi_t : ℂ) * I) := by
        rw [← hAmplitude]
        simp
      _ = -(interface.pFresnelReflectionCoefficient chi_i chi_t : ℂ) *
          ((chi_i : ℂ) * I) := by ring
  · rw [hAmplitude, hNormal, hCoefficient]
    push_cast
    ring

/-- A full-vector transmitted `p` amplitude law converts to the fixed-plane tangential convention
without dividing by the incident signed normal component. -/
lemma tangentialPFresnelTransmissionAmplitude
    (interface : PlanarDielectricInterface) {chi_i chi_t : ℝ} {I T : ℂ}
    (hAmplitude :
      T = (interface.pFresnelTransmissionCoefficient chi_i chi_t : ℂ) * I) :
    (chi_t : ℂ) * T =
      (interface.tangentialPFresnelTransmissionCoefficient chi_i chi_t : ℂ) *
        ((chi_i : ℂ) * I) := by
  have hCoefficient :
      (chi_i : ℂ) *
          (interface.tangentialPFresnelTransmissionCoefficient chi_i chi_t : ℂ) =
      (chi_t : ℂ) * (interface.pFresnelTransmissionCoefficient chi_i chi_t : ℂ) := by
    exact_mod_cast interface.tangentialPFresnelTransmissionCoefficient_cross_mul chi_i chi_t
  rw [hAmplitude]
  calc
    (chi_t : ℂ) *
        ((interface.pFresnelTransmissionCoefficient chi_i chi_t : ℂ) * I) =
      ((chi_t : ℂ) * (interface.pFresnelTransmissionCoefficient chi_i chi_t : ℂ)) * I := by
        ring
    _ = ((chi_i : ℂ) *
        (interface.tangentialPFresnelTransmissionCoefficient chi_i chi_t : ℂ)) * I := by
      rw [hCoefficient]
    _ = (interface.tangentialPFresnelTransmissionCoefficient chi_i chi_t : ℂ) *
        ((chi_i : ℂ) * I) := by ring

/-!

## B. Denominator positivity

-/

/-- The `s` denominator is positive for a strictly positive incident normal component and a
nonnegative transmitted normal component. -/
lemma sFresnelDenominator_pos (interface : PlanarDielectricInterface)
    {chi_i chi_t : ℝ} (hIncident : 0 < chi_i) (hTransmitted : 0 ≤ chi_t) :
    0 < interface.sFresnelDenominator chi_i chi_t := by
  exact add_pos_of_pos_of_nonneg
    (mul_pos (inv_pos.mpr interface.negativeMedium.waveImpedance_pos) hIncident)
    (mul_nonneg (inv_nonneg.mpr interface.positiveMedium.waveImpedance_nonneg) hTransmitted)

/-- The `p` denominator is positive for a strictly positive incident normal component and a
nonnegative transmitted normal component. -/
lemma pFresnelDenominator_pos (interface : PlanarDielectricInterface)
    {chi_i chi_t : ℝ} (hIncident : 0 < chi_i) (hTransmitted : 0 ≤ chi_t) :
    0 < interface.pFresnelDenominator chi_i chi_t := by
  exact add_pos_of_pos_of_nonneg
    (mul_pos (inv_pos.mpr interface.positiveMedium.waveImpedance_pos) hIncident)
    (mul_nonneg (inv_nonneg.mpr interface.negativeMedium.waveImpedance_nonneg) hTransmitted)

/-- The physical-side sign conditions make the `s` denominator nonzero. -/
lemma sFresnelDenominator_ne_zero (interface : PlanarDielectricInterface)
    {chi_i chi_t : ℝ} (hIncident : 0 < chi_i) (hTransmitted : 0 ≤ chi_t) :
    interface.sFresnelDenominator chi_i chi_t ≠ 0 :=
  ne_of_gt (interface.sFresnelDenominator_pos hIncident hTransmitted)

/-- The physical-side sign conditions make the `p` denominator nonzero. -/
lemma pFresnelDenominator_ne_zero (interface : PlanarDielectricInterface)
    {chi_i chi_t : ℝ} (hIncident : 0 < chi_i) (hTransmitted : 0 ≤ chi_t) :
    interface.pFresnelDenominator chi_i chi_t ≠ 0 :=
  ne_of_gt (interface.pFresnelDenominator_pos hIncident hTransmitted)

/-!

## C. Cross-multiplied scalar solutions

-/

/-- The full-vector `s` electric and magnetic scalar boundary equations determine reflected and
transmitted amplitudes after multiplication by the `s` denominator.

The alternative preserves arbitrary reflected normal data when the reflected amplitude is zero.
-/
lemma solve_sFresnel_cross_mul (interface : PlanarDielectricInterface)
    {chi_i chi_r chi_t : ℝ} {I R T : ℂ}
    (hElectric : T = I + R)
    (hMagnetic :
      ((interface.positiveMedium.waveImpedance⁻¹ : ℝ) : ℂ) * (chi_t : ℂ) * T =
        ((interface.negativeMedium.waveImpedance⁻¹ : ℝ) : ℂ) * (chi_i : ℂ) * I +
          ((interface.negativeMedium.waveImpedance⁻¹ : ℝ) : ℂ) * (chi_r : ℂ) * R)
    (hReflection : R = 0 ∨ chi_r = -chi_i) :
    ((interface.sFresnelDenominator chi_i chi_t : ℝ) : ℂ) * R =
        ((interface.negativeMedium.waveImpedance⁻¹ * chi_i -
          interface.positiveMedium.waveImpedance⁻¹ * chi_t : ℝ) : ℂ) * I ∧
      ((interface.sFresnelDenominator chi_i chi_t : ℝ) : ℂ) * T =
        ((2 * interface.negativeMedium.waveImpedance⁻¹ * chi_i : ℝ) : ℂ) * I := by
  rcases hReflection with hZero | hNormal
  · subst R
    simp only [add_zero] at hElectric
    subst T
    simp only [mul_zero, add_zero] at hMagnetic
    constructor <;> push_cast [sFresnelDenominator] at hMagnetic ⊢
    · linear_combination hMagnetic
    · linear_combination hMagnetic
  · rw [hNormal] at hMagnetic
    rw [hElectric] at hMagnetic
    have hReflected :
        ((interface.sFresnelDenominator chi_i chi_t : ℝ) : ℂ) * R =
          ((interface.negativeMedium.waveImpedance⁻¹ * chi_i -
            interface.positiveMedium.waveImpedance⁻¹ * chi_t : ℝ) : ℂ) * I := by
      push_cast [sFresnelDenominator] at hMagnetic ⊢
      linear_combination hMagnetic
    refine ⟨hReflected, ?_⟩
    rw [hElectric]
    push_cast [sFresnelDenominator] at hReflected ⊢
    linear_combination hReflected

/-- The full-vector `p` electric and magnetic scalar boundary equations determine reflected and
transmitted amplitudes after multiplication by the `p` denominator.

The alternative preserves arbitrary reflected normal data when the reflected amplitude is zero.
-/
lemma solve_pFresnel_cross_mul (interface : PlanarDielectricInterface)
    {chi_i chi_r chi_t : ℝ} {I R T : ℂ}
    (hElectric : (chi_t : ℂ) * T = (chi_i : ℂ) * I + (chi_r : ℂ) * R)
    (hMagnetic :
      ((interface.positiveMedium.waveImpedance⁻¹ : ℝ) : ℂ) * T =
        ((interface.negativeMedium.waveImpedance⁻¹ : ℝ) : ℂ) * I +
          ((interface.negativeMedium.waveImpedance⁻¹ : ℝ) : ℂ) * R)
    (hReflection : R = 0 ∨ chi_r = -chi_i) :
    ((interface.pFresnelDenominator chi_i chi_t : ℝ) : ℂ) * R =
        ((interface.positiveMedium.waveImpedance⁻¹ * chi_i -
          interface.negativeMedium.waveImpedance⁻¹ * chi_t : ℝ) : ℂ) * I ∧
      ((interface.pFresnelDenominator chi_i chi_t : ℝ) : ℂ) * T =
        ((2 * interface.negativeMedium.waveImpedance⁻¹ * chi_i : ℝ) : ℂ) * I := by
  rcases hReflection with hZero | hNormal
  · subst R
    simp only [mul_zero, add_zero] at hElectric hMagnetic
    constructor <;> push_cast [pFresnelDenominator] at hElectric hMagnetic ⊢
    · linear_combination
        (interface.positiveMedium.waveImpedance : ℂ)⁻¹ * hElectric -
          (chi_t : ℂ) * hMagnetic
    · linear_combination
        (interface.negativeMedium.waveImpedance : ℂ)⁻¹ * hElectric +
          (chi_i : ℂ) * hMagnetic
  · rw [hNormal] at hElectric
    have hReflected :
        ((interface.pFresnelDenominator chi_i chi_t : ℝ) : ℂ) * R =
          ((interface.positiveMedium.waveImpedance⁻¹ * chi_i -
            interface.negativeMedium.waveImpedance⁻¹ * chi_t : ℝ) : ℂ) * I := by
      push_cast [pFresnelDenominator] at hElectric hMagnetic ⊢
      linear_combination
        (interface.positiveMedium.waveImpedance : ℂ)⁻¹ * hElectric -
          (chi_t : ℂ) * hMagnetic
    refine ⟨hReflected, ?_⟩
    push_cast [pFresnelDenominator] at hElectric hMagnetic ⊢
    linear_combination
      (interface.negativeMedium.waveImpedance : ℂ)⁻¹ * hElectric +
        (chi_i : ℂ) * hMagnetic

/-!

## D. Quotient scalar solutions

-/

/-- When the `s` denominator is nonzero, the scalar boundary equations give the `s` Fresnel
reflection and transmission coefficients. -/
lemma solve_sFresnel (interface : PlanarDielectricInterface)
    {chi_i chi_r chi_t : ℝ} {I R T : ℂ}
    (hElectric : T = I + R)
    (hMagnetic :
      ((interface.positiveMedium.waveImpedance⁻¹ : ℝ) : ℂ) * (chi_t : ℂ) * T =
        ((interface.negativeMedium.waveImpedance⁻¹ : ℝ) : ℂ) * (chi_i : ℂ) * I +
          ((interface.negativeMedium.waveImpedance⁻¹ : ℝ) : ℂ) * (chi_r : ℂ) * R)
    (hReflection : R = 0 ∨ chi_r = -chi_i)
    (hDenominator : interface.sFresnelDenominator chi_i chi_t ≠ 0) :
    R = (interface.sFresnelReflectionCoefficient chi_i chi_t : ℂ) * I ∧
      T = (interface.sFresnelTransmissionCoefficient chi_i chi_t : ℂ) * I := by
  rcases interface.solve_sFresnel_cross_mul hElectric hMagnetic hReflection with
    ⟨hReflected, hTransmitted⟩
  have hDenominatorComplex :
      ((interface.sFresnelDenominator chi_i chi_t : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hDenominator
  constructor
  · have hSolved : R =
        (((interface.negativeMedium.waveImpedance⁻¹ * chi_i -
            interface.positiveMedium.waveImpedance⁻¹ * chi_t : ℝ) : ℂ) * I) /
          (interface.sFresnelDenominator chi_i chi_t : ℂ) := by
      apply (eq_div_iff hDenominatorComplex).2
      simpa only [mul_comm] using hReflected
    rw [sFresnelReflectionCoefficient]
    calc
      R = (((interface.negativeMedium.waveImpedance⁻¹ * chi_i -
          interface.positiveMedium.waveImpedance⁻¹ * chi_t : ℝ) : ℂ) * I) /
          (interface.sFresnelDenominator chi_i chi_t : ℂ) := hSolved
      _ = (((interface.negativeMedium.waveImpedance⁻¹ * chi_i -
          interface.positiveMedium.waveImpedance⁻¹ * chi_t) /
          interface.sFresnelDenominator chi_i chi_t : ℝ) : ℂ) * I := by
        push_cast
        ring
  · have hSolved : T =
        (((2 * interface.negativeMedium.waveImpedance⁻¹ * chi_i : ℝ) : ℂ) * I) /
          (interface.sFresnelDenominator chi_i chi_t : ℂ) := by
      apply (eq_div_iff hDenominatorComplex).2
      simpa only [mul_comm] using hTransmitted
    rw [sFresnelTransmissionCoefficient]
    calc
      T = (((2 * interface.negativeMedium.waveImpedance⁻¹ * chi_i : ℝ) : ℂ) * I) /
          (interface.sFresnelDenominator chi_i chi_t : ℂ) := hSolved
      _ = (((2 * interface.negativeMedium.waveImpedance⁻¹ * chi_i) /
          interface.sFresnelDenominator chi_i chi_t : ℝ) : ℂ) * I := by
        push_cast
        ring

/-- When the `p` denominator is nonzero, the scalar boundary equations give the full-vector `p`
Fresnel reflection and transmission coefficients. -/
lemma solve_pFresnel (interface : PlanarDielectricInterface)
    {chi_i chi_r chi_t : ℝ} {I R T : ℂ}
    (hElectric : (chi_t : ℂ) * T = (chi_i : ℂ) * I + (chi_r : ℂ) * R)
    (hMagnetic :
      ((interface.positiveMedium.waveImpedance⁻¹ : ℝ) : ℂ) * T =
        ((interface.negativeMedium.waveImpedance⁻¹ : ℝ) : ℂ) * I +
          ((interface.negativeMedium.waveImpedance⁻¹ : ℝ) : ℂ) * R)
    (hReflection : R = 0 ∨ chi_r = -chi_i)
    (hDenominator : interface.pFresnelDenominator chi_i chi_t ≠ 0) :
    R = (interface.pFresnelReflectionCoefficient chi_i chi_t : ℂ) * I ∧
      T = (interface.pFresnelTransmissionCoefficient chi_i chi_t : ℂ) * I := by
  rcases interface.solve_pFresnel_cross_mul hElectric hMagnetic hReflection with
    ⟨hReflected, hTransmitted⟩
  have hDenominatorComplex :
      ((interface.pFresnelDenominator chi_i chi_t : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hDenominator
  constructor
  · have hSolved : R =
        (((interface.positiveMedium.waveImpedance⁻¹ * chi_i -
            interface.negativeMedium.waveImpedance⁻¹ * chi_t : ℝ) : ℂ) * I) /
          (interface.pFresnelDenominator chi_i chi_t : ℂ) := by
      apply (eq_div_iff hDenominatorComplex).2
      simpa only [mul_comm] using hReflected
    rw [pFresnelReflectionCoefficient]
    calc
      R = (((interface.positiveMedium.waveImpedance⁻¹ * chi_i -
          interface.negativeMedium.waveImpedance⁻¹ * chi_t : ℝ) : ℂ) * I) /
          (interface.pFresnelDenominator chi_i chi_t : ℂ) := hSolved
      _ = (((interface.positiveMedium.waveImpedance⁻¹ * chi_i -
          interface.negativeMedium.waveImpedance⁻¹ * chi_t) /
          interface.pFresnelDenominator chi_i chi_t : ℝ) : ℂ) * I := by
        push_cast
        ring
  · have hSolved : T =
        (((2 * interface.negativeMedium.waveImpedance⁻¹ * chi_i : ℝ) : ℂ) * I) /
          (interface.pFresnelDenominator chi_i chi_t : ℂ) := by
      apply (eq_div_iff hDenominatorComplex).2
      simpa only [mul_comm] using hTransmitted
    rw [pFresnelTransmissionCoefficient]
    calc
      T = (((2 * interface.negativeMedium.waveImpedance⁻¹ * chi_i : ℝ) : ℂ) * I) /
          (interface.pFresnelDenominator chi_i chi_t : ℂ) := hSolved
      _ = (((2 * interface.negativeMedium.waveImpedance⁻¹ * chi_i) /
          interface.pFresnelDenominator chi_i chi_t : ℝ) : ℂ) * I := by
        push_cast
        ring

/-!

## E. Normal-incidence signs

-/

/-- At normal incidence, the propagation-oriented full-vector `p` reflection coefficient is the
negative of the `s` reflection coefficient. -/
lemma pFresnelReflectionCoefficient_normalIncidence (interface : PlanarDielectricInterface) :
    interface.pFresnelReflectionCoefficient 1 1 =
      -interface.sFresnelReflectionCoefficient 1 1 := by
  have hDenominator :
      interface.negativeMedium.waveImpedance⁻¹ +
          interface.positiveMedium.waveImpedance⁻¹ ≠ 0 := by
    exact ne_of_gt (add_pos
      (inv_pos.mpr interface.negativeMedium.waveImpedance_pos)
      (inv_pos.mpr interface.positiveMedium.waveImpedance_pos))
  simp only [pFresnelReflectionCoefficient, sFresnelReflectionCoefficient,
    pFresnelDenominator, sFresnelDenominator, mul_one]
  field_simp
  ring

/-- At normal incidence, the full-vector `p` and `s` transmission coefficients agree. -/
lemma pFresnelTransmissionCoefficient_normalIncidence (interface : PlanarDielectricInterface) :
    interface.pFresnelTransmissionCoefficient 1 1 =
      interface.sFresnelTransmissionCoefficient 1 1 := by
  simp only [pFresnelTransmissionCoefficient, sFresnelTransmissionCoefficient,
    pFresnelDenominator, sFresnelDenominator, mul_one]
  congr 1
  ring

/-- At normal incidence, the fixed-plane tangential-`p` and `s` reflection coefficients agree. -/
lemma tangentialPFresnelReflectionCoefficient_normalIncidence
    (interface : PlanarDielectricInterface) :
    interface.tangentialPFresnelReflectionCoefficient 1 1 =
      interface.sFresnelReflectionCoefficient 1 1 := by
  rw [interface.tangentialPFresnelReflectionCoefficient_eq_neg_pFresnelReflectionCoefficient,
    interface.pFresnelReflectionCoefficient_normalIncidence]
  ring

/-- At normal incidence, the fixed-plane tangential-`p` and `s` transmission coefficients agree. -/
lemma tangentialPFresnelTransmissionCoefficient_normalIncidence
    (interface : PlanarDielectricInterface) :
    interface.tangentialPFresnelTransmissionCoefficient 1 1 =
      interface.sFresnelTransmissionCoefficient 1 1 := by
  rw [tangentialPFresnelTransmissionCoefficient, sFresnelTransmissionCoefficient,
    pFresnelDenominator, sFresnelDenominator, mul_one]
  congr 1
  ring

end PlanarDielectricInterface

/-!

## F. Connected Jones boundary solution

-/

namespace PlanarDielectricWaveConfiguration

variable {configuration : PlanarDielectricWaveConfiguration}
  {incidentDirection reflectedDirection transmittedDirection : Space.Direction 3}
  {incidentFrame : PolarizationFrame incidentDirection}
  {reflectedFrame : PolarizationFrame reflectedDirection}
  {transmittedFrame : PolarizationFrame transmittedDirection}
  {incidentJones reflectedJones transmittedJones : JonesVector}

/-- The referenced electric and magnetic equalities give all four full-vector Fresnel component
formulas when a zero Jones vector or the reflected-normal sign relation is supplied.

The zero-Jones alternative leaves the reflected frame and carrier normal unrestricted. No
incident Jones component is assumed nonzero; the only division steps use the two stated Fresnel
denominator hypotheses. -/
lemma fresnel_components_of_referenced_balances_of_jones_guard
    (hElectric : configuration.HasReferencedJointElectricBalance)
    (hMagnetic : configuration.HasReferencedTangentialMagneticFieldStrengthBalance)
    (planeFrame : PolarizationFrame configuration.interface.plane.normal)
    (hIncident : IsReferencedMaterialJonesWave configuration.interface.plane
      configuration.interface.negativeMedium configuration.incident incidentFrame incidentJones)
    (hReflected : IsZeroOrReferencedMaterialJonesWave configuration.interface.plane
      configuration.interface.negativeMedium configuration.reflected reflectedFrame reflectedJones)
    (hTransmitted : IsReferencedMaterialJonesWave configuration.interface.plane
      configuration.interface.positiveMedium configuration.transmitted transmittedFrame
        transmittedJones)
    (hIncidentAlign : incidentFrame.axis 0 = planeFrame.axis 0)
    (hReflectedAlign : reflectedFrame.axis 0 = planeFrame.axis 0)
    (hTransmittedAlign : transmittedFrame.axis 0 = planeFrame.axis 0)
    (hReflection : reflectedJones.components = 0 ∨
      configuration.interface.plane.normalComponent reflectedFrame.propagationVector =
        -configuration.interface.plane.normalComponent incidentFrame.propagationVector)
    (hSDenominator : configuration.interface.sFresnelDenominator
      (configuration.interface.plane.normalComponent incidentFrame.propagationVector)
      (configuration.interface.plane.normalComponent transmittedFrame.propagationVector) ≠ 0)
    (hPDenominator : configuration.interface.pFresnelDenominator
      (configuration.interface.plane.normalComponent incidentFrame.propagationVector)
      (configuration.interface.plane.normalComponent transmittedFrame.propagationVector) ≠ 0) :
    reflectedJones.components 0 =
        (configuration.interface.sFresnelReflectionCoefficient
          (configuration.interface.plane.normalComponent incidentFrame.propagationVector)
          (configuration.interface.plane.normalComponent
            transmittedFrame.propagationVector) : ℂ) *
          incidentJones.components 0 ∧
      transmittedJones.components 0 =
        (configuration.interface.sFresnelTransmissionCoefficient
          (configuration.interface.plane.normalComponent incidentFrame.propagationVector)
          (configuration.interface.plane.normalComponent
            transmittedFrame.propagationVector) : ℂ) *
          incidentJones.components 0 ∧
      reflectedJones.components 1 =
        (configuration.interface.pFresnelReflectionCoefficient
          (configuration.interface.plane.normalComponent incidentFrame.propagationVector)
          (configuration.interface.plane.normalComponent
            transmittedFrame.propagationVector) : ℂ) *
          incidentJones.components 1 ∧
      transmittedJones.components 1 =
        (configuration.interface.pFresnelTransmissionCoefficient
          (configuration.interface.plane.normalComponent incidentFrame.propagationVector)
          (configuration.interface.plane.normalComponent
            transmittedFrame.propagationVector) : ℂ) *
          incidentJones.components 1 := by
  have hElectricS := HasReferencedJointElectricBalance.jones_component_zero hElectric planeFrame
    hIncident hReflected hTransmitted hIncidentAlign hReflectedAlign hTransmittedAlign
  have hElectricP := HasReferencedJointElectricBalance.jones_component_one hElectric planeFrame
    hIncident hReflected hTransmitted hIncidentAlign hReflectedAlign hTransmittedAlign
  have hMagneticS := HasReferencedTangentialMagneticFieldStrengthBalance.jones_component_zero
    hMagnetic planeFrame hIncident hReflected hTransmitted hIncidentAlign hReflectedAlign
      hTransmittedAlign
  have hMagneticP := HasReferencedTangentialMagneticFieldStrengthBalance.jones_component_one
    hMagnetic planeFrame hIncident hReflected hTransmitted hIncidentAlign hReflectedAlign
      hTransmittedAlign
  have hReflectionComponent (i : Fin 2) :
      reflectedJones.components i = 0 ∨
        configuration.interface.plane.normalComponent reflectedFrame.propagationVector =
          -configuration.interface.plane.normalComponent incidentFrame.propagationVector := by
    rcases hReflection with hZero | hNormal
    · left
      have hComponent := congrArg (fun v : EuclideanSpace ℂ (Fin 2) ↦ v i) hZero
      simpa using hComponent
    · exact Or.inr hNormal
  rcases configuration.interface.solve_sFresnel hElectricS hMagneticS
      (hReflectionComponent 0) hSDenominator with ⟨hReflectedS, hTransmittedS⟩
  rcases configuration.interface.solve_pFresnel hElectricP hMagneticP
      (hReflectionComponent 1) hPDenominator with ⟨hReflectedP, hTransmittedP⟩
  exact ⟨hReflectedS, hTransmittedS, hReflectedP, hTransmittedP⟩

/-- The wave-level reflected guard gives the four full-vector Fresnel component formulas from the
referenced electric and magnetic equalities.

A zero reflected electric amplitude forces zero reflected Jones data through the guarded material
connector, so its dummy carrier normal remains unrestricted. -/
lemma fresnel_components_of_referenced_balances
    (hElectric : configuration.HasReferencedJointElectricBalance)
    (hMagnetic : configuration.HasReferencedTangentialMagneticFieldStrengthBalance)
    (planeFrame : PolarizationFrame configuration.interface.plane.normal)
    (hIncident : IsReferencedMaterialJonesWave configuration.interface.plane
      configuration.interface.negativeMedium configuration.incident incidentFrame incidentJones)
    (hReflected : IsZeroOrReferencedMaterialJonesWave configuration.interface.plane
      configuration.interface.negativeMedium configuration.reflected reflectedFrame reflectedJones)
    (hTransmitted : IsReferencedMaterialJonesWave configuration.interface.plane
      configuration.interface.positiveMedium configuration.transmitted transmittedFrame
        transmittedJones)
    (hIncidentAlign : incidentFrame.axis 0 = planeFrame.axis 0)
    (hReflectedAlign : reflectedFrame.axis 0 = planeFrame.axis 0)
    (hTransmittedAlign : transmittedFrame.axis 0 = planeFrame.axis 0)
    (hReflection : configuration.reflected.electricAmplitude = 0 ∨
      configuration.interface.plane.normalComponent reflectedFrame.propagationVector =
        -configuration.interface.plane.normalComponent incidentFrame.propagationVector)
    (hSDenominator : configuration.interface.sFresnelDenominator
      (configuration.interface.plane.normalComponent incidentFrame.propagationVector)
      (configuration.interface.plane.normalComponent transmittedFrame.propagationVector) ≠ 0)
    (hPDenominator : configuration.interface.pFresnelDenominator
      (configuration.interface.plane.normalComponent incidentFrame.propagationVector)
      (configuration.interface.plane.normalComponent transmittedFrame.propagationVector) ≠ 0) :
    reflectedJones.components 0 =
        (configuration.interface.sFresnelReflectionCoefficient
          (configuration.interface.plane.normalComponent incidentFrame.propagationVector)
          (configuration.interface.plane.normalComponent
            transmittedFrame.propagationVector) : ℂ) *
          incidentJones.components 0 ∧
      transmittedJones.components 0 =
        (configuration.interface.sFresnelTransmissionCoefficient
          (configuration.interface.plane.normalComponent incidentFrame.propagationVector)
          (configuration.interface.plane.normalComponent
            transmittedFrame.propagationVector) : ℂ) *
          incidentJones.components 0 ∧
      reflectedJones.components 1 =
        (configuration.interface.pFresnelReflectionCoefficient
          (configuration.interface.plane.normalComponent incidentFrame.propagationVector)
          (configuration.interface.plane.normalComponent
            transmittedFrame.propagationVector) : ℂ) *
          incidentJones.components 1 ∧
      transmittedJones.components 1 =
        (configuration.interface.pFresnelTransmissionCoefficient
          (configuration.interface.plane.normalComponent incidentFrame.propagationVector)
          (configuration.interface.plane.normalComponent
            transmittedFrame.propagationVector) : ℂ) *
          incidentJones.components 1 := by
  have hJonesReflection : reflectedJones.components = 0 ∨
      configuration.interface.plane.normalComponent reflectedFrame.propagationVector =
        -configuration.interface.plane.normalComponent incidentFrame.propagationVector :=
    hReflection.imp
      (fun hZero ↦ hReflected.components_eq_zero_of_electricAmplitude_eq_zero hZero) id
  exact fresnel_components_of_referenced_balances_of_jones_guard hElectric hMagnetic planeFrame
    hIncident hReflected hTransmitted hIncidentAlign hReflectedAlign hTransmittedAlign
      hJonesReflection hSDenominator hPDenominator

/-- Selected-tangent normal-incidence frames specialize the four full-vector Fresnel component
laws to incident and transmitted signed normals `(1, 1)` and, in the active reflected branch, a
reflected signed normal of `-1`.

The incident and transmitted frames propagate along the stored positive normal and share the
independently selected first axis of `planeFrame`. The reflected-frame condition is required only
when its electric field is nonzero; a zero field retains arbitrary dummy carrier and frame data. -/
lemma fresnel_components_of_referenced_balances_of_selectedTangentNormalIncidence
    (hElectric : configuration.HasReferencedJointElectricBalance)
    (hMagnetic : configuration.HasReferencedTangentialMagneticFieldStrengthBalance)
    (planeFrame : PolarizationFrame configuration.interface.plane.normal)
    (hIncident : IsReferencedMaterialJonesWave configuration.interface.plane
      configuration.interface.negativeMedium configuration.incident incidentFrame incidentJones)
    (hReflected : IsZeroOrReferencedMaterialJonesWave configuration.interface.plane
      configuration.interface.negativeMedium configuration.reflected reflectedFrame reflectedJones)
    (hTransmitted : IsReferencedMaterialJonesWave configuration.interface.plane
      configuration.interface.positiveMedium configuration.transmitted transmittedFrame
        transmittedJones)
    (hIncidentNormal : incidentFrame.IsSelectedTangentNormalIncidence
      configuration.interface.plane planeFrame .positive)
    (hTransmittedNormal : transmittedFrame.IsSelectedTangentNormalIncidence
      configuration.interface.plane planeFrame .positive)
    (hReflectedNormal : configuration.reflected.electricAmplitude ≠ 0 →
      reflectedFrame.IsSelectedTangentNormalIncidence
        configuration.interface.plane planeFrame .negative) :
    reflectedJones.components 0 =
        (configuration.interface.sFresnelReflectionCoefficient 1 1 : ℂ) *
          incidentJones.components 0 ∧
      transmittedJones.components 0 =
        (configuration.interface.sFresnelTransmissionCoefficient 1 1 : ℂ) *
          incidentJones.components 0 ∧
      reflectedJones.components 1 =
        (configuration.interface.pFresnelReflectionCoefficient 1 1 : ℂ) *
          incidentJones.components 1 ∧
      transmittedJones.components 1 =
        (configuration.interface.pFresnelTransmissionCoefficient 1 1 : ℂ) *
          incidentJones.components 1 := by
  have hIncidentComponent := hIncidentNormal.normalComponent_propagationVector
  have hTransmittedComponent := hTransmittedNormal.normalComponent_propagationVector
  have hSDenominator := configuration.interface.sFresnelDenominator_ne_zero
    (chi_i := 1) (chi_t := 1) (by norm_num) (by norm_num)
  have hPDenominator := configuration.interface.pFresnelDenominator_ne_zero
    (chi_i := 1) (chi_t := 1) (by norm_num) (by norm_num)
  by_cases hZero : configuration.reflected.electricAmplitude = 0
  · have hReflectedZero := hReflected.reframe_of_electricAmplitude_eq_zero planeFrame hZero
    simpa only [hIncidentComponent, hTransmittedComponent,
      Space.OrientedAffineHyperplane.Side.sign_positive] using
      fresnel_components_of_referenced_balances hElectric hMagnetic planeFrame hIncident
        hReflectedZero hTransmitted hIncidentNormal.1 rfl hTransmittedNormal.1 (Or.inl hZero)
          (by simpa only [hIncidentComponent, hTransmittedComponent,
            Space.OrientedAffineHyperplane.Side.sign_positive] using hSDenominator)
          (by simpa only [hIncidentComponent, hTransmittedComponent,
            Space.OrientedAffineHyperplane.Side.sign_positive] using hPDenominator)
  · have hReflectedData := hReflectedNormal hZero
    have hReflectedComponent := hReflectedData.normalComponent_propagationVector
    have hReflection : configuration.interface.plane.normalComponent
          reflectedFrame.propagationVector =
        -configuration.interface.plane.normalComponent incidentFrame.propagationVector := by
      rw [hReflectedComponent, hIncidentComponent]
      norm_num
    simpa only [hIncidentComponent, hTransmittedComponent,
      Space.OrientedAffineHyperplane.Side.sign_positive] using
      fresnel_components_of_referenced_balances hElectric hMagnetic planeFrame hIncident hReflected
        hTransmitted hIncidentNormal.1 hReflectedData.1 hTransmittedNormal.1 (Or.inr hReflection)
          (by simpa only [hIncidentComponent, hTransmittedComponent,
            Space.OrientedAffineHyperplane.Side.sign_positive] using hSDenominator)
          (by simpa only [hIncidentComponent, hTransmittedComponent,
            Space.OrientedAffineHyperplane.Side.sign_positive] using hPDenominator)

/-- At selected-tangent normal incidence, the fixed-plane `p` amplitudes obey the explicitly named
tangential-`p` Fresnel coefficients.

Thus both polarization coordinates are resolved in one common tangent gauge. The reflected
zero-field branch still permits an arbitrary dummy propagation frame. -/
lemma fresnel_tangential_components_of_referenced_balances_of_selectedTangentNormalIncidence
    (hElectric : configuration.HasReferencedJointElectricBalance)
    (hMagnetic : configuration.HasReferencedTangentialMagneticFieldStrengthBalance)
    (planeFrame : PolarizationFrame configuration.interface.plane.normal)
    (hIncident : IsReferencedMaterialJonesWave configuration.interface.plane
      configuration.interface.negativeMedium configuration.incident incidentFrame incidentJones)
    (hReflected : IsZeroOrReferencedMaterialJonesWave configuration.interface.plane
      configuration.interface.negativeMedium configuration.reflected reflectedFrame reflectedJones)
    (hTransmitted : IsReferencedMaterialJonesWave configuration.interface.plane
      configuration.interface.positiveMedium configuration.transmitted transmittedFrame
        transmittedJones)
    (hIncidentNormal : incidentFrame.IsSelectedTangentNormalIncidence
      configuration.interface.plane planeFrame .positive)
    (hTransmittedNormal : transmittedFrame.IsSelectedTangentNormalIncidence
      configuration.interface.plane planeFrame .positive)
    (hReflectedNormal : configuration.reflected.electricAmplitude ≠ 0 →
      reflectedFrame.IsSelectedTangentNormalIncidence
        configuration.interface.plane planeFrame .negative) :
    reflectedJones.components 0 =
        (configuration.interface.sFresnelReflectionCoefficient 1 1 : ℂ) *
          incidentJones.components 0 ∧
      transmittedJones.components 0 =
        (configuration.interface.sFresnelTransmissionCoefficient 1 1 : ℂ) *
          incidentJones.components 0 ∧
      reflectedFrame.normalScaledSecondComponent configuration.interface.plane reflectedJones =
        (configuration.interface.tangentialPFresnelReflectionCoefficient 1 1 : ℂ) *
          incidentFrame.normalScaledSecondComponent configuration.interface.plane incidentJones ∧
      transmittedFrame.normalScaledSecondComponent configuration.interface.plane transmittedJones =
        (configuration.interface.tangentialPFresnelTransmissionCoefficient 1 1 : ℂ) *
          incidentFrame.normalScaledSecondComponent configuration.interface.plane
            incidentJones := by
  have hSolved := fresnel_components_of_referenced_balances_of_selectedTangentNormalIncidence
    hElectric hMagnetic planeFrame hIncident hReflected hTransmitted hIncidentNormal
      hTransmittedNormal hReflectedNormal
  have hIncidentComponent := hIncidentNormal.normalComponent_propagationVector
  have hTransmittedComponent := hTransmittedNormal.normalComponent_propagationVector
  have hReflection : reflectedJones.components 1 = 0 ∨
      configuration.interface.plane.normalComponent reflectedFrame.propagationVector = -1 := by
    by_cases hZero : configuration.reflected.electricAmplitude = 0
    · left
      have hComponents := hReflected.components_eq_zero_of_electricAmplitude_eq_zero hZero
      simpa using congrArg (fun v : EuclideanSpace ℂ (Fin 2) ↦ v 1) hComponents
    · right
      simpa using (hReflectedNormal hZero).normalComponent_propagationVector
  have hReflectedP := configuration.interface.tangentialPFresnelReflectionAmplitude_of_guard
    (chi_i := 1)
    (chi_r := configuration.interface.plane.normalComponent reflectedFrame.propagationVector)
    (chi_t := 1) hSolved.2.2.1 hReflection
  have hTransmittedP := configuration.interface.tangentialPFresnelTransmissionAmplitude
    (chi_i := 1) (chi_t := 1) hSolved.2.2.2
  refine ⟨hSolved.1, hSolved.2.1, ?_, ?_⟩
  · simpa [PolarizationFrame.normalScaledSecondComponent, hIncidentComponent] using hReflectedP
  · simpa [PolarizationFrame.normalScaledSecondComponent, hIncidentComponent,
      hTransmittedComponent] using hTransmittedP

/-- The fixed-frequency boundary equations give all four full-vector Fresnel component formulas
when the propagating frames are the canonical non-normal incidence frames.

The incident frame normal is positive, the transmitted frame normal is nonnegative, and the
active reflected frame normal is explicitly selected negative. The canonical-frame hypotheses
are supplied through the guarded role bundle. Tangential phase matching gives the common `s`
axis; the referenced connector data, phase matching, and opposite normal-sign hypotheses give
exact active reflection. In the zero-reflected
branch, the proof locally represents the zero Jones data in the common plane
frame. The original dummy reflected carrier, direction, frame, and frequency remain unrestricted. -/
lemma fresnel_components_of_referenced_balances_of_incidenceFrames
    (hElectric : configuration.IsFixedFrequencyElectricBoundary)
    (hMagnetic : configuration.HasReferencedTangentialMagneticFieldStrengthBalance)
    (hIncident : IsReferencedMaterialJonesWave configuration.interface.plane
      configuration.interface.negativeMedium configuration.incident incidentFrame incidentJones)
    (hReflected : IsZeroOrReferencedMaterialJonesWave configuration.interface.plane
      configuration.interface.negativeMedium configuration.reflected reflectedFrame reflectedJones)
    (hTransmitted : IsReferencedMaterialJonesWave configuration.interface.plane
      configuration.interface.positiveMedium configuration.transmitted transmittedFrame
        transmittedJones)
    (hFrames : configuration.HasCanonicalNonNormalIncidenceFrames incidentFrame reflectedFrame
      transmittedFrame)
    (hIncidentNormal : 0 <
      configuration.interface.plane.normalComponent incidentFrame.propagationVector)
    (hReflectedNormal : configuration.reflected.electricAmplitude ≠ 0 →
      configuration.interface.plane.normalComponent reflectedFrame.propagationVector < 0)
    (hTransmittedNormal : 0 ≤
      configuration.interface.plane.normalComponent transmittedFrame.propagationVector) :
    reflectedJones.components 0 =
        (configuration.interface.sFresnelReflectionCoefficient
          (configuration.interface.plane.normalComponent incidentFrame.propagationVector)
          (configuration.interface.plane.normalComponent
            transmittedFrame.propagationVector) : ℂ) *
          incidentJones.components 0 ∧
      transmittedJones.components 0 =
        (configuration.interface.sFresnelTransmissionCoefficient
          (configuration.interface.plane.normalComponent incidentFrame.propagationVector)
          (configuration.interface.plane.normalComponent
            transmittedFrame.propagationVector) : ℂ) *
          incidentJones.components 0 ∧
      reflectedJones.components 1 =
        (configuration.interface.pFresnelReflectionCoefficient
          (configuration.interface.plane.normalComponent incidentFrame.propagationVector)
          (configuration.interface.plane.normalComponent
            transmittedFrame.propagationVector) : ℂ) *
          incidentJones.components 1 ∧
      transmittedJones.components 1 =
        (configuration.interface.pFresnelTransmissionCoefficient
          (configuration.interface.plane.normalComponent incidentFrame.propagationVector)
          (configuration.interface.plane.normalComponent
            transmittedFrame.propagationVector) : ℂ) *
          incidentJones.components 1 := by
  have hData := hElectric.1.canonicalIncidenceFrame_data hIncident hReflected hTransmitted
    hFrames hIncidentNormal hReflectedNormal
  rcases hData with
    ⟨planeFrame, hIncidentAlign, hTransmittedAlign, hReflectedData⟩
  have hSDenominator := configuration.interface.sFresnelDenominator_ne_zero
    hIncidentNormal hTransmittedNormal
  have hPDenominator := configuration.interface.pFresnelDenominator_ne_zero
    hIncidentNormal hTransmittedNormal
  by_cases hZero : configuration.reflected.electricAmplitude = 0
  · have hReflectedZero := hReflected.reframe_of_electricAmplitude_eq_zero planeFrame hZero
    exact fresnel_components_of_referenced_balances hElectric.2 hMagnetic planeFrame hIncident
      hReflectedZero hTransmitted hIncidentAlign rfl hTransmittedAlign (Or.inl hZero)
        hSDenominator hPDenominator
  · rcases hReflectedData.resolve_left hZero with ⟨hReflectedAlign, hReflection⟩
    have hNormal : configuration.interface.plane.normalComponent
          reflectedFrame.propagationVector =
        -configuration.interface.plane.normalComponent incidentFrame.propagationVector := by
      rw [hReflection, configuration.interface.plane.normalComponent_vectorReflection]
    exact fresnel_components_of_referenced_balances hElectric.2 hMagnetic planeFrame hIncident
      hReflected hTransmitted hIncidentAlign hReflectedAlign hTransmittedAlign (Or.inr hNormal)
        hSDenominator hPDenominator

end PlanarDielectricWaveConfiguration

end

end Optics
