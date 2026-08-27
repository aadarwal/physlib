/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.HarmonicFlux.ReferencedMaterialWave
public import Physlib.Optics.Interfaces.PlanarDielectric.FresnelAmplitude

/-!
# Fresnel normal-flux balance at a planar dielectric interface

## i. Overview

This file turns the real propagating full-vector Fresnel amplitudes into lossless normal-flux
identities. Write `Y_j = Z_j⁻¹`, and let `chi_i > 0` and `chi_t >= 0` be the signed incident and
transmitted normal propagation components; this sign use is pinned by
`jonesBoundaryRegression_incidentNormalComponent`
(`Physlib/Optics/Interfaces/PlanarDielectric/JonesBoundaryRegression.lean:196`) and
`jonesBoundaryRegression_transmittedNormalComponent`
(`Physlib/Optics/Interfaces/PlanarDielectric/JonesBoundaryRegression.lean:214`). The transmission
flux factor is

```text
(Y₂ chi_t) / (Y₁ chi_i).
```

It multiplies the squared transmission amplitude for both polarizations. In particular, the
full-vector `p` coefficient uses the same `Y chi` flux weight as `s`; the `Y / chi` factor belongs
to a tangential-`p` amplitude convention and is not used here.

The primary identities are stronger than normalized `R + T = 1`. Hypothesis-free polynomial
identities are followed by coefficient laws that use division only by the corresponding Fresnel
denominator. They remain valid for zero incident Jones data and use no division by `chi_t`.
Reflectance and transmittance are total real definitions; their nonnegative interpretation and
normalized balance are proved for a positive incident and nonnegative transmitted normal,
retaining transmitted grazing incidence.

The final result consumes the connected referenced electric and magnetic boundary equalities and
identifies the sum of the incident and reflected waves' separate actual one-period mean normal
fluxes with the transmitted wave's mean normal flux at the stored plane point. It is not yet a
statement about the Poynting vector of the combined negative-side field: the cancellation of its
incident-reflected normal interference term is a separate result.

## ii. Key results

- `PlanarDielectricInterface.sFresnel_normalFluxNumerator_identity` and
  `PlanarDielectricInterface.pFresnel_normalFluxNumerator_identity`: denominator-free polynomial
  power identities.
- `PlanarDielectricInterface.sFresnel_normalFluxCoefficient_balance` and
  `PlanarDielectricInterface.pFresnel_normalFluxCoefficient_balance`: unnormalized coefficient
  identities with only the matching denominator assumed nonzero.
- `PlanarDielectricInterface.sFresnelReflectance_add_transmittance` and
  `PlanarDielectricInterface.pFresnelReflectance_add_transmittance`: physical `R + T = 1` laws.
- `PlanarDielectricInterface.jonesIntensity_normalFlux_balance_of_fresnel_components`: arbitrary
  complex Jones-component balance, including elliptical polarization and zero input.
- `PlanarDielectricWaveConfiguration.fresnel_separateWave_normalFlux_balance`: connected actual
  one-period mean normal-flux balance at the stored interface point.
- `PlanarDielectricWaveConfiguration.fresnel_separateWave_normalFlux_balance_of_incidenceFrames`:
  the canonical non-normal-incidence form with a derived common `s` axis and reflection guard.

## iii. Table of contents

- A. Flux factors, reflectance, and transmittance
- B. Denominator-free polynomial identities
- C. Unnormalized coefficient balance
- D. Normalized reflectance and transmittance
- E. Complex amplitudes and arbitrary Jones data
- F. Material irradiance and signed normal flux
- G. Connected separate-wave mean-flux balance

## iv. References

All coefficient parameters are real; their physical propagating interpretation uses the stated
normal-sign hypotheses. The results do not cover complex total-internal-reflection amplitudes,
lossy media, aperture-integrated power, or power-normalized scattering ports. The core connected
theorem accepts an explicit reflected guard, while its canonical-incidence wrapper derives that
guard from explicit direction selection.

-/

@[expose] public section

namespace Optics

open Electromagnetism Electromagnetism.ThreeDimension Space Time
open scoped Interval

noncomputable section

namespace PlanarDielectricInterface

/-!

## A. Flux factors, reflectance, and transmittance

-/

/-- The transmitted-to-incident normal-admittance ratio for real propagating Fresnel power.

Its physical nonnegative interpretation requires a positive incident normal component and a
nonnegative transmitted normal component. -/
def fresnelTransmissionFluxFactor (interface : PlanarDielectricInterface)
    (chi_i chi_t : ℝ) : ℝ :=
  (interface.positiveMedium.waveImpedance⁻¹ * chi_t) /
    (interface.negativeMedium.waveImpedance⁻¹ * chi_i)

/-- The full-vector `s` Fresnel power reflectance. -/
def sFresnelReflectance (interface : PlanarDielectricInterface)
    (chi_i chi_t : ℝ) : ℝ :=
  (interface.sFresnelReflectionCoefficient chi_i chi_t) ^ 2

/-- The full-vector `s` Fresnel power transmittance, including the normal-admittance ratio. -/
def sFresnelTransmittance (interface : PlanarDielectricInterface)
    (chi_i chi_t : ℝ) : ℝ :=
  interface.fresnelTransmissionFluxFactor chi_i chi_t *
    (interface.sFresnelTransmissionCoefficient chi_i chi_t) ^ 2

/-- The full-vector `p` Fresnel power reflectance. -/
def pFresnelReflectance (interface : PlanarDielectricInterface)
    (chi_i chi_t : ℝ) : ℝ :=
  (interface.pFresnelReflectionCoefficient chi_i chi_t) ^ 2

/-- The full-vector `p` Fresnel power transmittance, including the normal-admittance ratio. -/
def pFresnelTransmittance (interface : PlanarDielectricInterface)
    (chi_i chi_t : ℝ) : ℝ :=
  interface.fresnelTransmissionFluxFactor chi_i chi_t *
    (interface.pFresnelTransmissionCoefficient chi_i chi_t) ^ 2

/-- The transmission flux factor is nonnegative on the physical real-propagating branch. -/
lemma fresnelTransmissionFluxFactor_nonneg (interface : PlanarDielectricInterface)
    {chi_i chi_t : ℝ} (hIncident : 0 < chi_i) (hTransmitted : 0 ≤ chi_t) :
    0 ≤ interface.fresnelTransmissionFluxFactor chi_i chi_t := by
  exact div_nonneg
    (mul_nonneg (inv_nonneg.mpr interface.positiveMedium.waveImpedance_nonneg) hTransmitted)
    (mul_nonneg (inv_nonneg.mpr interface.negativeMedium.waveImpedance_nonneg) hIncident.le)

/-- Full-vector `s` reflectance is nonnegative. -/
lemma sFresnelReflectance_nonneg (interface : PlanarDielectricInterface)
    (chi_i chi_t : ℝ) :
    0 ≤ interface.sFresnelReflectance chi_i chi_t :=
  sq_nonneg _

/-- Full-vector `s` transmittance is nonnegative on the physical real-propagating branch. -/
lemma sFresnelTransmittance_nonneg (interface : PlanarDielectricInterface)
    {chi_i chi_t : ℝ} (hIncident : 0 < chi_i) (hTransmitted : 0 ≤ chi_t) :
    0 ≤ interface.sFresnelTransmittance chi_i chi_t := by
  exact mul_nonneg (interface.fresnelTransmissionFluxFactor_nonneg hIncident hTransmitted)
    (sq_nonneg _)

/-- Full-vector `p` reflectance is nonnegative. -/
lemma pFresnelReflectance_nonneg (interface : PlanarDielectricInterface)
    (chi_i chi_t : ℝ) :
    0 ≤ interface.pFresnelReflectance chi_i chi_t :=
  sq_nonneg _

/-- Full-vector `p` transmittance is nonnegative on the physical real-propagating branch. -/
lemma pFresnelTransmittance_nonneg (interface : PlanarDielectricInterface)
    {chi_i chi_t : ℝ} (hIncident : 0 < chi_i) (hTransmitted : 0 ≤ chi_t) :
    0 ≤ interface.pFresnelTransmittance chi_i chi_t := by
  exact mul_nonneg (interface.fresnelTransmissionFluxFactor_nonneg hIncident hTransmitted)
    (sq_nonneg _)

/-!

## B. Denominator-free polynomial identities

-/

/-- The `s` Fresnel numerator expressions satisfy the lossless normal-admittance identity before any
division by the coefficient denominator. -/
lemma sFresnel_normalFluxNumerator_identity (interface : PlanarDielectricInterface)
    (chi_i chi_t : ℝ) :
    interface.negativeMedium.waveImpedance⁻¹ * chi_i *
          (interface.negativeMedium.waveImpedance⁻¹ * chi_i -
            interface.positiveMedium.waveImpedance⁻¹ * chi_t) ^ 2 +
        interface.positiveMedium.waveImpedance⁻¹ * chi_t *
          (2 * interface.negativeMedium.waveImpedance⁻¹ * chi_i) ^ 2 =
      interface.negativeMedium.waveImpedance⁻¹ * chi_i *
        (interface.sFresnelDenominator chi_i chi_t) ^ 2 := by
  rw [sFresnelDenominator]
  ring

/-- The `p` Fresnel numerator expressions satisfy the lossless normal-admittance identity before any
division by the coefficient denominator. -/
lemma pFresnel_normalFluxNumerator_identity (interface : PlanarDielectricInterface)
    (chi_i chi_t : ℝ) :
    interface.negativeMedium.waveImpedance⁻¹ * chi_i *
          (interface.positiveMedium.waveImpedance⁻¹ * chi_i -
            interface.negativeMedium.waveImpedance⁻¹ * chi_t) ^ 2 +
        interface.positiveMedium.waveImpedance⁻¹ * chi_t *
          (2 * interface.negativeMedium.waveImpedance⁻¹ * chi_i) ^ 2 =
      interface.negativeMedium.waveImpedance⁻¹ * chi_i *
        (interface.pFresnelDenominator chi_i chi_t) ^ 2 := by
  rw [pFresnelDenominator]
  ring

/-!

## C. Unnormalized coefficient balance

-/

private lemma weighted_sq_div_balance {A B N M D : ℝ} (hD : D ≠ 0)
    (h : A * N ^ 2 + B * M ^ 2 = A * D ^ 2) :
    A * (N / D) ^ 2 + B * (M / D) ^ 2 = A := by
  field_simp [hD]
  nlinarith [h]

/-- The full-vector `s` coefficients satisfy the unnormalized signed normal-admittance identity.

Only the `s` denominator is required to be nonzero; the result uses no division by the incident
normal component or by an incident field amplitude. -/
lemma sFresnel_normalFluxCoefficient_balance (interface : PlanarDielectricInterface)
    (chi_i chi_t : ℝ) (hDenominator : interface.sFresnelDenominator chi_i chi_t ≠ 0) :
    interface.negativeMedium.waveImpedance⁻¹ * chi_i *
          (interface.sFresnelReflectionCoefficient chi_i chi_t) ^ 2 +
        interface.positiveMedium.waveImpedance⁻¹ * chi_t *
          (interface.sFresnelTransmissionCoefficient chi_i chi_t) ^ 2 =
      interface.negativeMedium.waveImpedance⁻¹ * chi_i := by
  rw [sFresnelReflectionCoefficient, sFresnelTransmissionCoefficient]
  exact weighted_sq_div_balance hDenominator
    (interface.sFresnel_normalFluxNumerator_identity chi_i chi_t)

/-- The full-vector `p` coefficients satisfy the unnormalized signed normal-admittance identity.

Only the `p` denominator is required to be nonzero; the result uses no division by the incident
normal component or by an incident field amplitude. -/
lemma pFresnel_normalFluxCoefficient_balance (interface : PlanarDielectricInterface)
    (chi_i chi_t : ℝ) (hDenominator : interface.pFresnelDenominator chi_i chi_t ≠ 0) :
    interface.negativeMedium.waveImpedance⁻¹ * chi_i *
          (interface.pFresnelReflectionCoefficient chi_i chi_t) ^ 2 +
        interface.positiveMedium.waveImpedance⁻¹ * chi_t *
          (interface.pFresnelTransmissionCoefficient chi_i chi_t) ^ 2 =
      interface.negativeMedium.waveImpedance⁻¹ * chi_i := by
  rw [pFresnelReflectionCoefficient, pFresnelTransmissionCoefficient]
  exact weighted_sq_div_balance hDenominator
    (interface.pFresnel_normalFluxNumerator_identity chi_i chi_t)

/-!

## D. Normalized reflectance and transmittance

-/

private lemma normalize_weighted_sq_balance {A B r t : ℝ} (hA : A ≠ 0)
    (h : A * r ^ 2 + B * t ^ 2 = A) :
    r ^ 2 + (B / A) * t ^ 2 = 1 := by
  field_simp [hA]
  nlinarith [h]

/-- Physical full-vector `s` Fresnel reflectance and transmittance sum to one.

Transmitted grazing incidence is included because `chi_t` is only required to be nonnegative. -/
lemma sFresnelReflectance_add_transmittance (interface : PlanarDielectricInterface)
    {chi_i chi_t : ℝ} (hIncident : 0 < chi_i) (hTransmitted : 0 ≤ chi_t) :
    interface.sFresnelReflectance chi_i chi_t +
      interface.sFresnelTransmittance chi_i chi_t = 1 := by
  have hIncidentWeight :
      interface.negativeMedium.waveImpedance⁻¹ * chi_i ≠ 0 :=
    mul_ne_zero (inv_ne_zero interface.negativeMedium.waveImpedance_ne_zero)
      (ne_of_gt hIncident)
  have hBalance := interface.sFresnel_normalFluxCoefficient_balance chi_i chi_t
    (interface.sFresnelDenominator_ne_zero hIncident hTransmitted)
  exact normalize_weighted_sq_balance hIncidentWeight hBalance

/-- Physical full-vector `p` Fresnel reflectance and transmittance sum to one.

The transmission weight is the same `Y₂ chi_t / (Y₁ chi_i)` factor as for `s`. -/
lemma pFresnelReflectance_add_transmittance (interface : PlanarDielectricInterface)
    {chi_i chi_t : ℝ} (hIncident : 0 < chi_i) (hTransmitted : 0 ≤ chi_t) :
    interface.pFresnelReflectance chi_i chi_t +
      interface.pFresnelTransmittance chi_i chi_t = 1 := by
  have hIncidentWeight :
      interface.negativeMedium.waveImpedance⁻¹ * chi_i ≠ 0 :=
    mul_ne_zero (inv_ne_zero interface.negativeMedium.waveImpedance_ne_zero)
      (ne_of_gt hIncident)
  have hBalance := interface.pFresnel_normalFluxCoefficient_balance chi_i chi_t
    (interface.pFresnelDenominator_ne_zero hIncident hTransmitted)
  exact normalize_weighted_sq_balance hIncidentWeight hBalance

/-!

## E. Complex amplitudes and arbitrary Jones data

-/

/-- The `s` coefficient balance remains valid after multiplication by an arbitrary complex incident
amplitude, including zero. -/
lemma sFresnel_normalFluxNormSq_balance (interface : PlanarDielectricInterface)
    (chi_i chi_t : ℝ) (I : ℂ)
    (hDenominator : interface.sFresnelDenominator chi_i chi_t ≠ 0) :
    interface.negativeMedium.waveImpedance⁻¹ * chi_i *
          Complex.normSq
            ((interface.sFresnelReflectionCoefficient chi_i chi_t : ℂ) * I) +
        interface.positiveMedium.waveImpedance⁻¹ * chi_t *
          Complex.normSq
            ((interface.sFresnelTransmissionCoefficient chi_i chi_t : ℂ) * I) =
      interface.negativeMedium.waveImpedance⁻¹ * chi_i * Complex.normSq I := by
  have hBalance :=
    interface.sFresnel_normalFluxCoefficient_balance chi_i chi_t hDenominator
  simp only [Complex.normSq_mul, Complex.normSq_ofReal]
  linear_combination Complex.normSq I * hBalance

/-- The `p` coefficient balance remains valid after multiplication by an arbitrary complex incident
amplitude, including zero. -/
lemma pFresnel_normalFluxNormSq_balance (interface : PlanarDielectricInterface)
    (chi_i chi_t : ℝ) (I : ℂ)
    (hDenominator : interface.pFresnelDenominator chi_i chi_t ≠ 0) :
    interface.negativeMedium.waveImpedance⁻¹ * chi_i *
          Complex.normSq
            ((interface.pFresnelReflectionCoefficient chi_i chi_t : ℂ) * I) +
        interface.positiveMedium.waveImpedance⁻¹ * chi_t *
          Complex.normSq
            ((interface.pFresnelTransmissionCoefficient chi_i chi_t : ℂ) * I) =
      interface.negativeMedium.waveImpedance⁻¹ * chi_i * Complex.normSq I := by
  have hBalance :=
    interface.pFresnel_normalFluxCoefficient_balance chi_i chi_t hDenominator
  simp only [Complex.normSq_mul, Complex.normSq_ofReal]
  linear_combination Complex.normSq I * hBalance

/-- Fresnel component formulas preserve the normal-admittance-weighted Jones intensity for an
arbitrary complex input polarization.

The two Jones coordinates may have any relative phase, and either may vanish. Each coefficient
denominator must be nonzero. -/
lemma jonesIntensity_normalFlux_balance_of_fresnel_components
    (interface : PlanarDielectricInterface) (chi_i chi_t : ℝ)
    (incidentJones reflectedJones transmittedJones : JonesVector)
    (hReflectedS : reflectedJones.components 0 =
      (interface.sFresnelReflectionCoefficient chi_i chi_t : ℂ) *
        incidentJones.components 0)
    (hTransmittedS : transmittedJones.components 0 =
      (interface.sFresnelTransmissionCoefficient chi_i chi_t : ℂ) *
        incidentJones.components 0)
    (hReflectedP : reflectedJones.components 1 =
      (interface.pFresnelReflectionCoefficient chi_i chi_t : ℂ) *
        incidentJones.components 1)
    (hTransmittedP : transmittedJones.components 1 =
      (interface.pFresnelTransmissionCoefficient chi_i chi_t : ℂ) *
        incidentJones.components 1)
    (hSDenominator : interface.sFresnelDenominator chi_i chi_t ≠ 0)
    (hPDenominator : interface.pFresnelDenominator chi_i chi_t ≠ 0) :
    interface.negativeMedium.waveImpedance⁻¹ * chi_i * reflectedJones.intensity +
        interface.positiveMedium.waveImpedance⁻¹ * chi_t * transmittedJones.intensity =
      interface.negativeMedium.waveImpedance⁻¹ * chi_i * incidentJones.intensity := by
  have hS := interface.sFresnel_normalFluxNormSq_balance chi_i chi_t
    (incidentJones.components 0) hSDenominator
  have hP := interface.pFresnel_normalFluxNormSq_balance chi_i chi_t
    (incidentJones.components 1) hPDenominator
  rw [JonesVector.intensity_eq_sum_normSq, JonesVector.intensity_eq_sum_normSq,
    JonesVector.intensity_eq_sum_normSq, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two,
    hReflectedS, hTransmittedS, hReflectedP, hTransmittedP]
  linear_combination hS + hP

/-!

## F. Material irradiance and signed normal flux

-/

/-- Fresnel component formulas satisfy an incident-normal-weighted material-irradiance identity.

This algebraic form becomes the positive outgoing-flux balance when `0 < chi_i` and
`0 ≤ chi_t`, with the sign assignment pinned by
`jonesBoundaryRegression_incidentNormalComponent`
(`Physlib/Optics/Interfaces/PlanarDielectric/JonesBoundaryRegression.lean:196`),
`jonesBoundaryRegression_transmittedNormalComponent`
(`Physlib/Optics/Interfaces/PlanarDielectric/JonesBoundaryRegression.lean:214`), and
`jonesBoundaryRegression_exact_hasSeparateWaveNormalFluxBalance`
(`Physlib/Optics/Interfaces/PlanarDielectric/FresnelFluxRegression.lean:254`). -/
lemma materialPlaneWaveIrradiance_normalFlux_balance_of_fresnel_components
    (interface : PlanarDielectricInterface) (chi_i chi_t : ℝ)
    (incidentJones reflectedJones transmittedJones : JonesVector)
    (hReflectedS : reflectedJones.components 0 =
      (interface.sFresnelReflectionCoefficient chi_i chi_t : ℂ) *
        incidentJones.components 0)
    (hTransmittedS : transmittedJones.components 0 =
      (interface.sFresnelTransmissionCoefficient chi_i chi_t : ℂ) *
        incidentJones.components 0)
    (hReflectedP : reflectedJones.components 1 =
      (interface.pFresnelReflectionCoefficient chi_i chi_t : ℂ) *
        incidentJones.components 1)
    (hTransmittedP : transmittedJones.components 1 =
      (interface.pFresnelTransmissionCoefficient chi_i chi_t : ℂ) *
        incidentJones.components 1)
    (hSDenominator : interface.sFresnelDenominator chi_i chi_t ≠ 0)
    (hPDenominator : interface.pFresnelDenominator chi_i chi_t ≠ 0) :
    reflectedJones.materialPlaneWaveIrradiance interface.negativeMedium * chi_i +
        transmittedJones.materialPlaneWaveIrradiance interface.positiveMedium * chi_t =
      incidentJones.materialPlaneWaveIrradiance interface.negativeMedium * chi_i := by
  have hIntensity := interface.jonesIntensity_normalFlux_balance_of_fresnel_components
    chi_i chi_t incidentJones reflectedJones transmittedJones hReflectedS hTransmittedS
      hReflectedP hTransmittedP hSDenominator hPDenominator
  rw [JonesVector.materialPlaneWaveIrradiance_eq_half_inv_impedance_mul_intensity,
    JonesVector.materialPlaneWaveIrradiance_eq_half_inv_impedance_mul_intensity,
    JonesVector.materialPlaneWaveIrradiance_eq_half_inv_impedance_mul_intensity]
  linear_combination (1 / 2 : ℝ) * hIntensity

/-- Fresnel component formulas and a zero-or-reflected-normal alternative give signed normal
material irradiance.

If the reflected Jones data vanishes, its normal component remains arbitrary and contributes no
flux. Otherwise its signed normal is the negative of the incident normal; the active sign is
pinned by `jonesBoundaryRegression_incidentNormalComponent`
(`Physlib/Optics/Interfaces/PlanarDielectric/JonesBoundaryRegression.lean:196`),
`jonesBoundaryRegression_reflectedNormalComponent`
(`Physlib/Optics/Interfaces/PlanarDielectric/JonesBoundaryRegression.lean:205`), and
`jonesBoundaryRegression_exact_hasSeparateWaveNormalFluxBalance`
(`Physlib/Optics/Interfaces/PlanarDielectric/FresnelFluxRegression.lean:254`). -/
lemma materialPlaneWaveIrradiance_signedNormalFlux_balance_of_fresnel_components
    (interface : PlanarDielectricInterface) (chi_i chi_r chi_t : ℝ)
    (incidentJones reflectedJones transmittedJones : JonesVector)
    (hReflectedS : reflectedJones.components 0 =
      (interface.sFresnelReflectionCoefficient chi_i chi_t : ℂ) *
        incidentJones.components 0)
    (hTransmittedS : transmittedJones.components 0 =
      (interface.sFresnelTransmissionCoefficient chi_i chi_t : ℂ) *
        incidentJones.components 0)
    (hReflectedP : reflectedJones.components 1 =
      (interface.pFresnelReflectionCoefficient chi_i chi_t : ℂ) *
        incidentJones.components 1)
    (hTransmittedP : transmittedJones.components 1 =
      (interface.pFresnelTransmissionCoefficient chi_i chi_t : ℂ) *
        incidentJones.components 1)
    (hReflection : reflectedJones.components = 0 ∨ chi_r = -chi_i)
    (hSDenominator : interface.sFresnelDenominator chi_i chi_t ≠ 0)
    (hPDenominator : interface.pFresnelDenominator chi_i chi_t ≠ 0) :
    incidentJones.materialPlaneWaveIrradiance interface.negativeMedium * chi_i +
        reflectedJones.materialPlaneWaveIrradiance interface.negativeMedium * chi_r =
      transmittedJones.materialPlaneWaveIrradiance interface.positiveMedium * chi_t := by
  have hOutgoing := interface.materialPlaneWaveIrradiance_normalFlux_balance_of_fresnel_components
    chi_i chi_t incidentJones reflectedJones transmittedJones hReflectedS hTransmittedS
      hReflectedP hTransmittedP hSDenominator hPDenominator
  rcases hReflection with hZero | hNormal
  · have hReflectedIrradiance :
        reflectedJones.materialPlaneWaveIrradiance interface.negativeMedium = 0 := by
      simp [JonesVector.materialPlaneWaveIrradiance, JonesVector.intensity, hZero]
    rw [hReflectedIrradiance] at hOutgoing ⊢
    linarith
  · rw [hNormal]
    linear_combination -hOutgoing

end PlanarDielectricInterface

namespace PlanarDielectricWaveConfiguration

open PlanarDielectricInterface

variable {configuration : PlanarDielectricWaveConfiguration}
  {incidentDirection reflectedDirection transmittedDirection : Space.Direction 3}
  {incidentFrame : PolarizationFrame incidentDirection}
  {reflectedFrame : PolarizationFrame reflectedDirection}
  {transmittedFrame : PolarizationFrame transmittedDirection}
  {incidentJones reflectedJones transmittedJones : JonesVector}

/-!

## G. Connected separate-wave mean-flux balance

-/

/-- The incident-plus-reflected versus transmitted balance of the three separate actual
one-period mean normal fluxes at the stored interface point.

Each carrier is averaged over its own positive-frequency period. This predicate does not assert
that the first two terms equal the normal Poynting flux of their combined fields. -/
def HasSeparateWaveNormalFluxBalance (configuration : PlanarDielectricWaveConfiguration)
    (startTime : Time) : Prop :=
  configuration.interface.plane.normalComponent
        (⨍ time in startTime.val..startTime.val +
            2 * Real.pi / configuration.incident.angularFrequency,
          ThreeDimension.poyntingVector configuration.incident.electricField
            (configuration.incident.magneticFieldStrength
              configuration.interface.negativeMedium)
            (time : Time) configuration.interface.plane.point) +
      configuration.interface.plane.normalComponent
        (⨍ time in startTime.val..startTime.val +
            2 * Real.pi / configuration.reflected.angularFrequency,
          ThreeDimension.poyntingVector configuration.reflected.electricField
            (configuration.reflected.magneticFieldStrength
              configuration.interface.negativeMedium)
            (time : Time) configuration.interface.plane.point) =
    configuration.interface.plane.normalComponent
      (⨍ time in startTime.val..startTime.val +
          2 * Real.pi / configuration.transmitted.angularFrequency,
        ThreeDimension.poyntingVector configuration.transmitted.electricField
          (configuration.transmitted.magneticFieldStrength
            configuration.interface.positiveMedium)
          (time : Time) configuration.interface.plane.point)

/-- The connected referenced boundary equations satisfy the three waves' separate actual
one-period mean normal fluxes at the stored interface point.

The incident normal is positive and the transmitted normal may be grazing. The reflected branch
is either electrically zero, with arbitrary dummy carrier data, or has the opposite signed normal.
Each integral is the actual Poynting vector of the corresponding complex carrier over its own
positive-frequency period. This result does not identify their sum with the Poynting vector of the
combined negative-side field. -/
lemma fresnel_separateWave_normalFlux_balance
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
    (hIncidentNormal : 0 <
      configuration.interface.plane.normalComponent incidentFrame.propagationVector)
    (hTransmittedNormal : 0 ≤
      configuration.interface.plane.normalComponent transmittedFrame.propagationVector)
    (startTime : Time) :
    configuration.HasSeparateWaveNormalFluxBalance startTime := by
  have hSDenominator := configuration.interface.sFresnelDenominator_ne_zero
    hIncidentNormal hTransmittedNormal
  have hPDenominator := configuration.interface.pFresnelDenominator_ne_zero
    hIncidentNormal hTransmittedNormal
  rcases fresnel_components_of_referenced_balances hElectric hMagnetic planeFrame hIncident
      hReflected hTransmitted hIncidentAlign hReflectedAlign hTransmittedAlign hReflection
      hSDenominator hPDenominator with ⟨hReflectedS, hTransmittedS, hReflectedP, hTransmittedP⟩
  have hJonesReflection : reflectedJones.components = 0 ∨
      configuration.interface.plane.normalComponent reflectedFrame.propagationVector =
        -configuration.interface.plane.normalComponent incidentFrame.propagationVector :=
    hReflection.imp
      (fun hZero ↦ hReflected.components_eq_zero_of_electricAmplitude_eq_zero hZero) id
  have hFlux :=
    materialPlaneWaveIrradiance_signedNormalFlux_balance_of_fresnel_components
      configuration.interface
      (configuration.interface.plane.normalComponent incidentFrame.propagationVector)
      (configuration.interface.plane.normalComponent reflectedFrame.propagationVector)
      (configuration.interface.plane.normalComponent transmittedFrame.propagationVector)
      incidentJones reflectedJones transmittedJones hReflectedS hTransmittedS hReflectedP
      hTransmittedP hJonesReflection hSDenominator hPDenominator
  rw [HasSeparateWaveNormalFluxBalance,
    hIncident.normalComponent_intervalAverage_poyntingVector_planePoint,
    hReflected.normalComponent_intervalAverage_poyntingVector_planePoint,
    hTransmitted.normalComponent_intervalAverage_poyntingVector_planePoint]
  exact hFlux

/-- A fixed-frequency boundary with canonical non-normal incidence frames satisfies the three
separate waves' actual one-period mean normal-flux balance.

The canonical-frame hypotheses and tangential phase matching give the common `s` axis. The
referenced connector data, phase matching, and explicit opposite normal-sign hypotheses give exact
active reflection. An electrically zero reflected wave is locally represented by zero Jones data
in the common plane frame, preserving all of its original dummy carrier labels. The incident and
transmitted basis conventions, and conditionally the active-reflected convention, are supplied
through the guarded role bundle. -/
lemma fresnel_separateWave_normalFlux_balance_of_incidenceFrames
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
      configuration.interface.plane.normalComponent transmittedFrame.propagationVector)
    (startTime : Time) :
    configuration.HasSeparateWaveNormalFluxBalance startTime := by
  have hData := hElectric.1.canonicalIncidenceFrame_data hIncident hReflected hTransmitted
    hFrames hIncidentNormal hReflectedNormal
  rcases hData with
    ⟨planeFrame, hIncidentAlign, hTransmittedAlign, hReflectedData⟩
  by_cases hZero : configuration.reflected.electricAmplitude = 0
  · have hReflectedZero := hReflected.reframe_of_electricAmplitude_eq_zero planeFrame hZero
    exact fresnel_separateWave_normalFlux_balance hElectric.2 hMagnetic planeFrame hIncident
      hReflectedZero hTransmitted hIncidentAlign rfl hTransmittedAlign (Or.inl hZero)
        hIncidentNormal hTransmittedNormal startTime
  · rcases hReflectedData.resolve_left hZero with ⟨hReflectedAlign, hReflection⟩
    have hNormal : configuration.interface.plane.normalComponent
          reflectedFrame.propagationVector =
        -configuration.interface.plane.normalComponent incidentFrame.propagationVector := by
      rw [hReflection, configuration.interface.plane.normalComponent_vectorReflection]
    exact fresnel_separateWave_normalFlux_balance hElectric.2 hMagnetic planeFrame hIncident
      hReflected hTransmitted hIncidentAlign hReflectedAlign hTransmittedAlign (Or.inr hNormal)
        hIncidentNormal hTransmittedNormal startTime

end PlanarDielectricWaveConfiguration

end

end Optics
