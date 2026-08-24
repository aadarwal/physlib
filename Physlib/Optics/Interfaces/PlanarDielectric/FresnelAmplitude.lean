/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

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
not tangential-`p` coefficients.

The primary solution results are cross-multiplied and therefore remain meaningful when a denominator
vanishes. Quotient results require only the matching denominator to be nonzero. Positivity lemmas
derive that condition for strictly positive incident normal component and nonnegative transmitted
normal component. The final results connect the quotient lemmas to the referenced electric and
magnetic equalities and their aligned Jones-wave data. They retain a zero-reflected-field branch
with arbitrary reflected carrier data and require no nonzero incident amplitude. The guarded
reflected normal relation remains an explicit premise: this file does not choose a propagation
branch or state an irradiance or power law.

## ii. Key results

- `PlanarDielectricInterface.sFresnelDenominator` and
  `PlanarDielectricInterface.pFresnelDenominator`: the two real scalar denominator values.
- `PlanarDielectricInterface.sFresnelReflectionCoefficient` and
  `PlanarDielectricInterface.sFresnelTransmissionCoefficient`: the full-vector `s` coefficients.
- `PlanarDielectricInterface.pFresnelReflectionCoefficient` and
  `PlanarDielectricInterface.pFresnelTransmissionCoefficient`: the full-vector `p` coefficients.
- `PlanarDielectricInterface.solve_sFresnel_cross_mul` and
  `PlanarDielectricInterface.solve_pFresnel_cross_mul`: guarded denominator-free scalar results.
- `PlanarDielectricInterface.solve_sFresnel` and
  `PlanarDielectricInterface.solve_pFresnel`: quotient forms when the denominator is nonzero.
- `PlanarDielectricWaveConfiguration.fresnel_components_of_referenced_balances_of_jones_guard`:
  the four component formulas from the two referenced equalities and a Jones-zero guard.
- `PlanarDielectricWaveConfiguration.fresnel_components_of_referenced_balances`: the wave-level
  form whose zero branch is stated using the reflected electric amplitude.

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

end PlanarDielectricWaveConfiguration

end

end Optics
