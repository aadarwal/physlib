/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Interfaces.PlanarDielectric.FresnelAmplitudeRegression
public import Physlib.Optics.Interfaces.PlanarDielectric.FresnelFlux

/-!
# Fresnel normal-flux regressions

## i. Overview

This file checks the Fresnel reflectance, transmittance, arbitrary-Jones, and connected actual-flux
layers against exact rational data. On the existing oblique `3-4-5` interface fixture, the normal
admittance ratio is `3/8` and the two polarization channels give

```text
(R_s, T_s) = (25/121, 96/121),
(R_p, T_p) = (1/25, 24/25).
```

Normal incidence gives `(1/9, 8/9)` for both channels despite the opposite full-vector reflection
signs. At transmitted grazing incidence both channels give `(1, 0)`, including the finite `p`
transmission amplitude whose zero normal-admittance weight removes its normal flux. A matched
interface gives `(0, 1)`.

An input with components `(1, I)` exercises a nontrivial relative phase; the arbitrary-Jones result
establishes the phase-independent law. The existing independently solved nonzero-phase
configuration is finally passed through the connected separate-wave Poynting-flux result, without
using its coefficient-value lemma.

## ii. Key results

- `fresnelFluxRegression_oblique`: exact oblique reflectance and transmittance.
- `fresnelFluxRegression_normalIncidence`: equal `s` and `p` power ratios at normal incidence.
- `fresnelFluxRegression_transmittedGrazing`: unit reflection and zero normal-flux transmittance.
- `fresnelFluxRegression_matchedInterface`: zero reflection and unit transmission.
- `fresnelFluxRegression_quadrature_normalFlux_values`: sentinel for the exact quadrature Jones
  outgoing fluxes.
- `fresnelFluxRegression_zeroReflection_signedNormalFlux`: guarded zero-reflection flux with an
  arbitrary reflected normal.
- `jonesBoundaryRegression_exact_hasSeparateWaveNormalFluxBalance`: the connected actual-wave
  mean-flux regression.

## iii. Table of contents

- A. Exact scalar power ratios
- B. Quadrature Jones normal flux
- C. Connected actual-wave normal flux

## iv. References

These regressions concern separate real propagating wave fluxes. They do not test negative-side
superposition interference, total internal reflection, or power-normalized scattering ports.

-/

@[expose] public section

namespace Optics

open Electromagnetism PlanarDielectricInterface PlanarDielectricWaveConfiguration Time

noncomputable section

/-!

## A. Exact scalar power ratios

-/

/-- The oblique exact fixture has normal-admittance ratio `3/8`, with each polarization's power
ratios summing to one. -/
lemma fresnelFluxRegression_oblique :
    jonesBoundaryRegressionInterface.fresnelTransmissionFluxFactor (4 / 5) (3 / 5) = 3 / 8 ∧
      jonesBoundaryRegressionInterface.sFresnelReflectance (4 / 5) (3 / 5) = 25 / 121 ∧
      jonesBoundaryRegressionInterface.sFresnelTransmittance (4 / 5) (3 / 5) = 96 / 121 ∧
      jonesBoundaryRegressionInterface.pFresnelReflectance (4 / 5) (3 / 5) = 1 / 25 ∧
      jonesBoundaryRegressionInterface.pFresnelTransmittance (4 / 5) (3 / 5) = 24 / 25 := by
  norm_num [fresnelTransmissionFluxFactor, sFresnelReflectance, sFresnelTransmittance,
    pFresnelReflectance, pFresnelTransmittance, sFresnelReflectionCoefficient,
    sFresnelTransmissionCoefficient, pFresnelReflectionCoefficient,
    pFresnelTransmissionCoefficient, sFresnelDenominator, pFresnelDenominator,
    jonesBoundaryRegressionInterface, jonesBoundaryRegression_negativeMedium_waveImpedance_inv,
    jonesBoundaryRegression_positiveMedium_waveImpedance_inv]

/-- With the regression media at normal incidence, both polarization channels have
`(R, T) = (1/9, 8/9)`. -/
lemma fresnelFluxRegression_normalIncidence :
    jonesBoundaryRegressionInterface.fresnelTransmissionFluxFactor 1 1 = 1 / 2 ∧
      jonesBoundaryRegressionInterface.sFresnelReflectance 1 1 = 1 / 9 ∧
      jonesBoundaryRegressionInterface.sFresnelTransmittance 1 1 = 8 / 9 ∧
      jonesBoundaryRegressionInterface.pFresnelReflectance 1 1 = 1 / 9 ∧
      jonesBoundaryRegressionInterface.pFresnelTransmittance 1 1 = 8 / 9 := by
  norm_num [fresnelTransmissionFluxFactor, sFresnelReflectance, sFresnelTransmittance,
    pFresnelReflectance, pFresnelTransmittance, sFresnelReflectionCoefficient,
    sFresnelTransmissionCoefficient, pFresnelReflectionCoefficient,
    pFresnelTransmissionCoefficient, sFresnelDenominator, pFresnelDenominator,
    jonesBoundaryRegressionInterface, jonesBoundaryRegression_negativeMedium_waveImpedance_inv,
    jonesBoundaryRegression_positiveMedium_waveImpedance_inv]

/-- At transmitted grazing incidence, both channels have unit reflectance and zero normal-flux
transmittance even though their electric transmission amplitudes remain finite. -/
lemma fresnelFluxRegression_transmittedGrazing :
    jonesBoundaryRegressionInterface.fresnelTransmissionFluxFactor 1 0 = 0 ∧
      jonesBoundaryRegressionInterface.sFresnelReflectance 1 0 = 1 ∧
      jonesBoundaryRegressionInterface.sFresnelTransmittance 1 0 = 0 ∧
      jonesBoundaryRegressionInterface.pFresnelReflectance 1 0 = 1 ∧
      jonesBoundaryRegressionInterface.pFresnelTransmittance 1 0 = 0 := by
  norm_num [fresnelTransmissionFluxFactor, sFresnelReflectance, sFresnelTransmittance,
    pFresnelReflectance, pFresnelTransmittance, sFresnelReflectionCoefficient,
    sFresnelTransmissionCoefficient, pFresnelReflectionCoefficient,
    pFresnelTransmissionCoefficient, sFresnelDenominator, pFresnelDenominator,
    jonesBoundaryRegressionInterface, jonesBoundaryRegression_negativeMedium_waveImpedance_inv,
    jonesBoundaryRegression_positiveMedium_waveImpedance_inv]

/-- A matched interface at normal incidence has zero reflectance and unit transmittance in both
polarization channels. -/
lemma fresnelFluxRegression_matchedInterface :
    fresnelAmplitudeRegressionMatchedInterface.fresnelTransmissionFluxFactor 1 1 = 1 ∧
      fresnelAmplitudeRegressionMatchedInterface.sFresnelReflectance 1 1 = 0 ∧
      fresnelAmplitudeRegressionMatchedInterface.sFresnelTransmittance 1 1 = 1 ∧
      fresnelAmplitudeRegressionMatchedInterface.pFresnelReflectance 1 1 = 0 ∧
      fresnelAmplitudeRegressionMatchedInterface.pFresnelTransmittance 1 1 = 1 := by
  norm_num [fresnelTransmissionFluxFactor, sFresnelReflectance, sFresnelTransmittance,
    pFresnelReflectance, pFresnelTransmittance, sFresnelReflectionCoefficient,
    sFresnelTransmissionCoefficient, pFresnelReflectionCoefficient,
    pFresnelTransmissionCoefficient, sFresnelDenominator, pFresnelDenominator,
    fresnelAmplitudeRegressionMatchedInterface,
    jonesBoundaryRegression_negativeMedium_waveImpedance_inv]

/-!

## B. Quadrature Jones normal flux

-/

/-- A two-component incident Jones vector with relative quadrature phase. -/
def fresnelFluxRegressionQuadratureIncidentJones : JonesVector :=
  JonesVector.ofComponents 1 Complex.I

/-- The oblique Fresnel-reflected Jones data for the quadrature input. -/
def fresnelFluxRegressionQuadratureReflectedJones : JonesVector :=
  JonesVector.ofComponents (5 / 11) ((-1 / 5) * Complex.I)

/-- The oblique Fresnel-transmitted Jones data for the quadrature input. -/
def fresnelFluxRegressionQuadratureTransmittedJones : JonesVector :=
  JonesVector.ofComponents (16 / 11) ((8 / 5) * Complex.I)

/-- The arbitrary-Jones coefficient result proves the exact quadrature fixture's weighted
intensity balance without assuming either incident component is nonzero. -/
lemma fresnelFluxRegression_quadrature_jonesIntensity_balance :
    jonesBoundaryRegressionNegativeMedium.waveImpedance⁻¹ * (4 / 5) *
          fresnelFluxRegressionQuadratureReflectedJones.intensity +
        jonesBoundaryRegressionPositiveMedium.waveImpedance⁻¹ * (3 / 5) *
          fresnelFluxRegressionQuadratureTransmittedJones.intensity =
      jonesBoundaryRegressionNegativeMedium.waveImpedance⁻¹ * (4 / 5) *
        fresnelFluxRegressionQuadratureIncidentJones.intensity := by
  apply jonesBoundaryRegressionInterface.jonesIntensity_normalFlux_balance_of_fresnel_components
  · norm_num [fresnelFluxRegressionQuadratureReflectedJones,
      fresnelFluxRegressionQuadratureIncidentJones, jonesBoundaryRegressionInterface,
      sFresnelReflectionCoefficient, sFresnelDenominator,
      jonesBoundaryRegression_negativeMedium_waveImpedance_inv,
      jonesBoundaryRegression_positiveMedium_waveImpedance_inv]
  · norm_num [fresnelFluxRegressionQuadratureTransmittedJones,
      fresnelFluxRegressionQuadratureIncidentJones, jonesBoundaryRegressionInterface,
      sFresnelTransmissionCoefficient, sFresnelDenominator,
      jonesBoundaryRegression_negativeMedium_waveImpedance_inv,
      jonesBoundaryRegression_positiveMedium_waveImpedance_inv]
  · norm_num [fresnelFluxRegressionQuadratureReflectedJones,
      fresnelFluxRegressionQuadratureIncidentJones, jonesBoundaryRegressionInterface,
      pFresnelReflectionCoefficient, pFresnelDenominator,
      jonesBoundaryRegression_negativeMedium_waveImpedance_inv,
      jonesBoundaryRegression_positiveMedium_waveImpedance_inv]
  · norm_num [fresnelFluxRegressionQuadratureTransmittedJones,
      fresnelFluxRegressionQuadratureIncidentJones, jonesBoundaryRegressionInterface,
      pFresnelTransmissionCoefficient, pFresnelDenominator,
      jonesBoundaryRegression_negativeMedium_waveImpedance_inv,
      jonesBoundaryRegression_positiveMedium_waveImpedance_inv]
  · exact jonesBoundaryRegressionInterface.sFresnelDenominator_ne_zero
      (by norm_num) (by norm_num)
  · exact jonesBoundaryRegressionInterface.pFresnelDenominator_ne_zero
      (by norm_num) (by norm_num)

/-- The quadrature input has incident normal flux `2`; the reflected and transmitted outgoing
normal fluxes are `746/3025` and `5304/3025`, respectively (sentinel:
`fresnelFluxRegression_quadrature_normalFlux_values`). -/
lemma fresnelFluxRegression_quadrature_normalFlux_values :
    fresnelFluxRegressionQuadratureIncidentJones.materialPlaneWaveIrradiance
          jonesBoundaryRegressionNegativeMedium * (4 / 5) = 2 ∧
      fresnelFluxRegressionQuadratureReflectedJones.materialPlaneWaveIrradiance
          jonesBoundaryRegressionNegativeMedium * (4 / 5) = 746 / 3025 ∧
      fresnelFluxRegressionQuadratureTransmittedJones.materialPlaneWaveIrradiance
          jonesBoundaryRegressionPositiveMedium * (3 / 5) = 5304 / 3025 := by
  rw [JonesVector.materialPlaneWaveIrradiance_eq_half_inv_impedance_mul_intensity,
    JonesVector.materialPlaneWaveIrradiance_eq_half_inv_impedance_mul_intensity,
    JonesVector.materialPlaneWaveIrradiance_eq_half_inv_impedance_mul_intensity,
    JonesVector.intensity_eq_sum_normSq,
    JonesVector.intensity_eq_sum_normSq, JonesVector.intensity_eq_sum_normSq,
    Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [fresnelFluxRegressionQuadratureIncidentJones,
    fresnelFluxRegressionQuadratureReflectedJones,
    fresnelFluxRegressionQuadratureTransmittedJones, JonesVector.ofComponents_zero,
    JonesVector.ofComponents_one, Complex.normSq_one, Complex.normSq_I, Complex.normSq_mul,
    div_eq_mul_inv]
  rw [jonesBoundaryRegression_negativeMedium_waveImpedance_inv,
    jonesBoundaryRegression_positiveMedium_waveImpedance_inv]
  norm_num

/-- A matched interface with zero reflected Jones data keeps the deliberately arbitrary reflected
normal `chi_r = chi_i = 1` and satisfies signed normal-flux balance.

The first conclusion records that this dummy normal does not satisfy the active reflected relation
`chi_r = -chi_i`. -/
lemma fresnelFluxRegression_zeroReflection_signedNormalFlux :
    (1 : ℝ) ≠ -1 ∧
      fresnelFluxRegressionQuadratureIncidentJones.materialPlaneWaveIrradiance
            fresnelAmplitudeRegressionMatchedInterface.negativeMedium * 1 +
          (JonesVector.ofComponents 0 0).materialPlaneWaveIrradiance
            fresnelAmplitudeRegressionMatchedInterface.negativeMedium * 1 =
        fresnelFluxRegressionQuadratureIncidentJones.materialPlaneWaveIrradiance
          fresnelAmplitudeRegressionMatchedInterface.positiveMedium * 1 := by
  rcases fresnelAmplitudeRegression_zeroReflection with
    ⟨hNormal, hReflectedS, hTransmittedS, hReflectedP, hTransmittedP⟩
  refine ⟨hNormal, ?_⟩
  exact
    materialPlaneWaveIrradiance_signedNormalFlux_balance_of_fresnel_components
      fresnelAmplitudeRegressionMatchedInterface
      1 1 1 fresnelFluxRegressionQuadratureIncidentJones (JonesVector.ofComponents 0 0)
      fresnelFluxRegressionQuadratureIncidentJones
      (by rw [hReflectedS]; simp)
      (by rw [hTransmittedS]; simp)
      (by rw [hReflectedP]; simp)
      (by rw [hTransmittedP]; simp)
      (Or.inl (by
        ext i
        fin_cases i <;> rfl))
      (fresnelAmplitudeRegressionMatchedInterface.sFresnelDenominator_ne_zero
        (by norm_num) (by norm_num))
      (fresnelAmplitudeRegressionMatchedInterface.pFresnelDenominator_ne_zero
        (by norm_num) (by norm_num))

/-!

## C. Connected actual-wave normal flux

-/

/-- The independently verified exact wave fixture satisfies the connected separate-wave actual
one-period mean normal-flux law at every period origin. -/
lemma jonesBoundaryRegression_exact_hasSeparateWaveNormalFluxBalance (startTime : Time) :
    HasSeparateWaveNormalFluxBalance
      (jonesBoundaryRegressionConfiguration (5 / 11) (16 / 11) (-1 / 5) (8 / 5))
      startTime := by
  exact fresnel_separateWave_normalFlux_balance
    jonesBoundaryRegression_exact_hasReferencedJointElectricBalance
    jonesBoundaryRegression_exact_hasReferencedTangentialMagneticFieldStrengthBalance
    jonesBoundaryRegressionPlaneFrame
    (jonesBoundaryRegression_incidentWave_isReferencedMaterialJonesWave
      jonesBoundaryRegressionIncidentJones)
    (Or.inr (jonesBoundaryRegression_reflectedWave_isReferencedMaterialJonesWave
      (jonesBoundaryRegressionReflectedJones (5 / 11) (-1 / 5))))
    (jonesBoundaryRegression_transmittedWave_isReferencedMaterialJonesWave
      (jonesBoundaryRegressionTransmittedJones (16 / 11) (8 / 5)))
    (by rfl) (by rfl) (by rfl)
    (Or.inr (by
      dsimp only [jonesBoundaryRegressionConfiguration, jonesBoundaryRegressionInterface]
      rw [jonesBoundaryRegression_incidentNormalComponent,
        jonesBoundaryRegression_reflectedNormalComponent]
      norm_num))
    (by
      dsimp only [jonesBoundaryRegressionConfiguration, jonesBoundaryRegressionInterface]
      rw [jonesBoundaryRegression_incidentNormalComponent]
      norm_num)
    (by
      dsimp only [jonesBoundaryRegressionConfiguration, jonesBoundaryRegressionInterface]
      rw [jonesBoundaryRegression_transmittedNormalComponent]
      norm_num)
    startTime

end

end Optics
