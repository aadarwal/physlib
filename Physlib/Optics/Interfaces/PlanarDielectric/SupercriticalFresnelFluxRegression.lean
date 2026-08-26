/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Interfaces.PlanarDielectric.SupercriticalFresnelFlux
public import Physlib.Optics.Interfaces.PlanarDielectric.SupercriticalFresnelRegression

/-!
# Exact actual-flux regression for total internal reflection

## i. Overview

This file connects the exact unequal-admittance complex Fresnel fixture to actual Poynting flux.
Its negative-side admittance is `2/3`, its incident and reflected signed normal factors are `4/5`
and `-4/5`, and both propagating Jones intensities are two. Their one-period normal mean fluxes
are therefore exactly `8/15` and `-8/15`.

The stored transmitted wave is the canonical positive-normal-decay carrier. Its actual normal
mean flux is zero at every point. Exact phase matching then lets the connected interference API
show that the superposed incident-plus-reflected field also has zero normal mean flux at the stored
interface point.

These statements do not assign propagating irradiance to the decay-frame Jones coordinates. Zero
transmitted normal mean flux also does not mean zero field, zero tangential transport, or pointwise
zero normal Poynting flux.

## ii. Key results

- `supercriticalFresnelFluxRegression_isFixedFrequencyElectricBoundary`: exact phase and electric
  boundary data.
- `supercriticalFresnelFluxRegression_incident_normalFlux` and
  `supercriticalFresnelFluxRegression_reflected_normalFlux`: exact signed propagating fluxes.
- `supercriticalFresnelFluxRegression_transmitted_normalFlux`: zero decay-carrier normal mean flux.
- `supercriticalFresnelFluxRegression_hasSeparateWaveNormalFluxBalance` and
  `supercriticalFresnelFluxRegression_hasSuperposedWaveNormalFluxBalance`: connected actual-flux
  endpoints.
- `supercriticalFresnelFluxRegression_superposed_normalFlux`: exact zero normal mean flux of the
  actual superposed negative-side field.

## iii. Table of contents

- A. Exact fixed-frequency boundary
- B. Exact separate-wave fluxes
- C. Connected actual-flux balances

## iv. References

All propagating fluxes are evaluated at the stored interface point and averaged over the carrier's
own period. The transmitted zero-flux regression holds at every spatial point. No aperture,
whole-plane, outgoing-wave, causal, or modal-power claim is made.

-/

@[expose] public section

namespace Optics

open ClassicalMechanics Electromagnetism Electromagnetism.ThreeDimension Matrix Space Time
open ClassicalMechanics.ComplexWaveVector
open Electromagnetism.ThreeDimension.ComplexMonochromaticPlaneWave
open PlanarDielectricWaveConfiguration
open scoped Interval

noncomputable section

/-!

## A. Exact fixed-frequency boundary

-/

/-- The exact complex total-reflection fixture has the incident frequency and complex tangential
wave-vector projection on the transmitted carrier and on the active reflected carrier. -/
lemma supercriticalFresnelFluxRegression_isElectricPhaseMatched :
    supercriticalFresnelRegressionConfiguration.IsElectricPhaseMatched := by
  refine ⟨⟨?_, ?_⟩, Or.inr ⟨?_, ?_⟩⟩
  · rw [supercriticalFresnelRegression_transmitted_eq_candidate]
    exact positiveNormalDecayTransmittedJonesCandidate_angularFrequency
      supercriticalFresnelRegressionConfiguration
      supercriticalFresnelRegression_configuration_transmittedNormalRadicand_neg
      supercriticalFresnelRegressionTransmittedJones
  · rw [supercriticalFresnelRegression_transmitted_eq_candidate,
      positiveNormalDecayTransmittedJonesCandidate_waveVector,
      hyperplaneTangentialProjection_positiveNormalDecayTransmittedWaveVector]
    rw [show supercriticalFresnelRegressionConfiguration.incident =
        supercriticalFresnelRegressionIncidentWave by rfl,
      supercriticalFresnelRegression_incidentWave_waveVector,
      phaseVector_ofReal, hyperplaneTangentialProjection_ofReal]
  · rfl
  · dsimp only [supercriticalFresnelRegressionConfiguration,
      supercriticalFresnelRegressionInterface]
    rw [supercriticalFresnelRegression_reflectedWave_waveVector,
      supercriticalFresnelRegression_incidentWave_waveVector,
      hyperplaneTangentialProjection_ofReal, hyperplaneTangentialProjection_ofReal]
    ext i
    fin_cases i <;>
      simp [complexDecayRegressionPlane, positiveNormalDecayRegressionDirection,
        OrientedAffineHyperplane.tangentialProjection,
        OrientedAffineHyperplane.normalComponent, OrientedAffineHyperplane.normalVector,
        PiLp.inner_apply, RCLike.inner_apply,
        Matrix.cons_val_two, Matrix.head_cons]

/-- The exact complex total-reflection fixture satisfies the reduced fixed-frequency electric
boundary predicate. -/
lemma supercriticalFresnelFluxRegression_isFixedFrequencyElectricBoundary :
    supercriticalFresnelRegressionConfiguration.IsFixedFrequencyElectricBoundary :=
  ⟨supercriticalFresnelFluxRegression_isElectricPhaseMatched,
    supercriticalFresnelRegression_exact_hasReferencedJointElectricBalance⟩

/-!

## B. Exact separate-wave fluxes

-/

private lemma supercriticalFresnelFluxRegression_incidentConnector :
    IsReferencedMaterialJonesWave
      supercriticalFresnelRegressionConfiguration.interface.plane
      supercriticalFresnelRegressionConfiguration.interface.negativeMedium
      supercriticalFresnelRegressionConfiguration.incident jonesBoundaryRegressionIncidentFrame
      supercriticalFresnelRegressionIncidentJones := by
  simpa only [supercriticalFresnelRegressionConfiguration,
    supercriticalFresnelRegressionInterface] using
      supercriticalFresnelRegression_incident_isReferencedMaterialJonesWave

private lemma supercriticalFresnelFluxRegression_reflectedConnector :
    IsReferencedMaterialJonesWave
      supercriticalFresnelRegressionConfiguration.interface.plane
      supercriticalFresnelRegressionConfiguration.interface.negativeMedium
      supercriticalFresnelRegressionConfiguration.reflected jonesBoundaryRegressionReflectedFrame
      supercriticalFresnelRegressionReflectedJones := by
  simpa only [supercriticalFresnelRegressionConfiguration,
    supercriticalFresnelRegressionInterface] using
      supercriticalFresnelRegression_reflected_isReferencedMaterialJonesWave

private lemma supercriticalFresnelFluxRegression_negativeMedium_waveImpedance_inv :
    supercriticalFresnelRegressionConfiguration.interface.negativeMedium.waveImpedance⁻¹ =
      2 / 3 :=
  supercriticalFresnelRegression_negativeMedium_waveImpedance_inv

/-- The exact incident carrier has actual one-period mean normal flux `8/15` at the stored
interface point. -/
lemma supercriticalFresnelFluxRegression_incident_normalFlux (startTime : Time) :
    supercriticalFresnelRegressionConfiguration.interface.plane.normalComponent
      (⨍ time in startTime.val..startTime.val +
          2 * Real.pi / supercriticalFresnelRegressionConfiguration.incident.angularFrequency,
        poyntingVector supercriticalFresnelRegressionConfiguration.incident.electricField
          (supercriticalFresnelRegressionConfiguration.incident.magneticFieldStrength
            supercriticalFresnelRegressionConfiguration.interface.negativeMedium)
          (time : Time) supercriticalFresnelRegressionConfiguration.interface.plane.point) =
      8 / 15 := by
  have hIncident := supercriticalFresnelFluxRegression_incidentConnector
  rw [hIncident.normalComponent_intervalAverage_poyntingVector_planePoint,
    JonesVector.materialPlaneWaveIrradiance_eq_half_inv_impedance_mul_intensity,
    supercriticalFresnelFluxRegression_negativeMedium_waveImpedance_inv,
    supercriticalFresnelRegression_incidentJones_intensity,
    supercriticalFresnelRegression_incidentNormalComponent]
  norm_num

/-- The exact reflected carrier has actual one-period mean signed normal flux `-8/15` at the
stored interface point. -/
lemma supercriticalFresnelFluxRegression_reflected_normalFlux (startTime : Time) :
    supercriticalFresnelRegressionConfiguration.interface.plane.normalComponent
      (⨍ time in startTime.val..startTime.val +
          2 * Real.pi / supercriticalFresnelRegressionConfiguration.reflected.angularFrequency,
        poyntingVector supercriticalFresnelRegressionConfiguration.reflected.electricField
          (supercriticalFresnelRegressionConfiguration.reflected.magneticFieldStrength
            supercriticalFresnelRegressionConfiguration.interface.negativeMedium)
          (time : Time) supercriticalFresnelRegressionConfiguration.interface.plane.point) =
      -8 / 15 := by
  have hReflected := supercriticalFresnelFluxRegression_reflectedConnector
  rw [hReflected.normalComponent_intervalAverage_poyntingVector_planePoint,
    JonesVector.materialPlaneWaveIrradiance_eq_half_inv_impedance_mul_intensity,
    supercriticalFresnelFluxRegression_negativeMedium_waveImpedance_inv,
    supercriticalFresnelRegression_reflectedJones_intensity,
    supercriticalFresnelRegression_reflectedNormalComponent]
  norm_num

/-- The exact canonical transmitted decay carrier has zero actual one-period mean normal flux at
every spatial point. -/
lemma supercriticalFresnelFluxRegression_transmitted_normalFlux
    (startTime : Time) (x : Space) :
    supercriticalFresnelRegressionConfiguration.interface.plane.normalComponent
      (⨍ time in startTime.val..startTime.val +
          2 * Real.pi / supercriticalFresnelRegressionConfiguration.transmitted.angularFrequency,
        poyntingVector supercriticalFresnelRegressionConfiguration.transmitted.electricField
          (supercriticalFresnelRegressionConfiguration.transmitted.magneticFieldStrength
            supercriticalFresnelRegressionConfiguration.interface.positiveMedium)
          (time : Time) x) = 0 := by
  rw [supercriticalFresnelRegression_transmitted_eq_candidate]
  exact positiveNormalDecayTransmittedJonesCandidate_normalMeanFlux_eq_zero
    supercriticalFresnelRegressionConfiguration
    supercriticalFresnelRegression_configuration_transmittedNormalRadicand_neg
    supercriticalFresnelRegressionTransmittedJones startTime x

/-!

## C. Connected actual-flux balances

-/

private lemma supercriticalFresnelFluxRegression_planeFrame_axis_zero :
    jonesBoundaryRegressionAxisZero =
      complexDecayRegressionPolarizationFrame.planeFrame.axis 0 := by
  rw [PositiveNormalDecayPolarizationFrame.planeFrame_axis_zero]
  symm
  ext i
  fin_cases i <;>
    simp [PositiveNormalDecayPolarizationFrame.realSAxis,
      complexDecayRegressionPolarizationFrame, positiveNormalDecayRegression,
      positiveNormalDecayRegressionTangentialVector,
      PositiveNormalDecayWaveVector.normalVector,
      complexDecayRegressionPlane, positiveNormalDecayRegressionDirection,
      jonesBoundaryRegressionAxisZero, NormedSpace.normalize,
      EuclideanSpace.norm_eq, Fin.sum_univ_three, crossProduct]

private lemma supercriticalFresnelFluxRegression_incidentFrame_align :
    jonesBoundaryRegressionIncidentFrame.axis 0 =
      (positiveNormalDecayTransmittedPolarizationFrame
        supercriticalFresnelRegressionConfiguration
        supercriticalFresnelRegression_configuration_transmittedNormalRadicand_neg).planeFrame.axis
          0 := by
  rw [supercriticalFresnelRegression_configuration_polarizationFrame]
  exact supercriticalFresnelFluxRegression_planeFrame_axis_zero

private lemma supercriticalFresnelFluxRegression_reflectedFrame_align :
    jonesBoundaryRegressionReflectedFrame.axis 0 =
      (positiveNormalDecayTransmittedPolarizationFrame
        supercriticalFresnelRegressionConfiguration
        supercriticalFresnelRegression_configuration_transmittedNormalRadicand_neg).planeFrame.axis
          0 := by
  rw [supercriticalFresnelRegression_configuration_polarizationFrame]
  exact supercriticalFresnelFluxRegression_planeFrame_axis_zero

private lemma supercriticalFresnelFluxRegression_reflectedConnector_guarded :
    IsZeroOrReferencedMaterialJonesWave
      supercriticalFresnelRegressionConfiguration.interface.plane
      supercriticalFresnelRegressionConfiguration.interface.negativeMedium
      supercriticalFresnelRegressionConfiguration.reflected jonesBoundaryRegressionReflectedFrame
      supercriticalFresnelRegressionReflectedJones :=
  Or.inr supercriticalFresnelFluxRegression_reflectedConnector

private lemma supercriticalFresnelFluxRegression_reflection_guard :
    supercriticalFresnelRegressionConfiguration.reflected.electricAmplitude = 0 ∨
      supercriticalFresnelRegressionConfiguration.interface.plane.normalComponent
          jonesBoundaryRegressionReflectedFrame.propagationVector =
        -supercriticalFresnelRegressionConfiguration.interface.plane.normalComponent
          jonesBoundaryRegressionIncidentFrame.propagationVector := by
  right
  rw [supercriticalFresnelRegression_reflectedNormalComponent,
    supercriticalFresnelRegression_incidentNormalComponent]
  norm_num

private lemma supercriticalFresnelFluxRegression_incidentNormal_pos :
    0 < supercriticalFresnelRegressionConfiguration.interface.plane.normalComponent
      jonesBoundaryRegressionIncidentFrame.propagationVector := by
  rw [supercriticalFresnelRegression_incidentNormalComponent]
  norm_num

/-- The exact total-reflection fixture satisfies the existing separate actual-wave normal-flux
balance at every period origin. -/
lemma supercriticalFresnelFluxRegression_hasSeparateWaveNormalFluxBalance (startTime : Time) :
    supercriticalFresnelRegressionConfiguration.HasSeparateWaveNormalFluxBalance startTime := by
  exact complexFresnel_separateWave_normalFlux_balance
    supercriticalFresnelRegression_exact_hasReferencedJointElectricBalance
    supercriticalFresnelRegression_exact_hasReferencedTangentialMagneticFieldStrengthBalance
    supercriticalFresnelRegression_configuration_transmittedNormalRadicand_neg
    supercriticalFresnelFluxRegression_incidentConnector
    supercriticalFresnelFluxRegression_reflectedConnector_guarded
    supercriticalFresnelRegression_transmitted_eq_candidate
    supercriticalFresnelFluxRegression_incidentFrame_align
    (fun _ ↦ supercriticalFresnelFluxRegression_reflectedFrame_align)
    supercriticalFresnelFluxRegression_reflection_guard
    supercriticalFresnelFluxRegression_incidentNormal_pos startTime

/-- The exact total-reflection fixture satisfies the existing actual superposed-wave normal-flux
balance at every period origin. -/
lemma supercriticalFresnelFluxRegression_hasSuperposedWaveNormalFluxBalance (startTime : Time) :
    supercriticalFresnelRegressionConfiguration.HasSuperposedWaveNormalFluxBalance startTime := by
  exact complexFresnel_superposedWave_normalFlux_balance
    supercriticalFresnelFluxRegression_isFixedFrequencyElectricBoundary
    supercriticalFresnelRegression_exact_hasReferencedTangentialMagneticFieldStrengthBalance
    supercriticalFresnelRegression_configuration_transmittedNormalRadicand_neg
    supercriticalFresnelFluxRegression_incidentConnector
    supercriticalFresnelFluxRegression_reflectedConnector_guarded
    supercriticalFresnelRegression_transmitted_eq_candidate
    supercriticalFresnelFluxRegression_incidentFrame_align
    (fun _ ↦ supercriticalFresnelFluxRegression_reflectedFrame_align)
    supercriticalFresnelFluxRegression_reflection_guard
    supercriticalFresnelFluxRegression_incidentNormal_pos startTime

/-- The exact actual superposed incident-plus-reflected field has zero one-period mean Poynting
component along the stored interface normal. -/
lemma supercriticalFresnelFluxRegression_superposed_normalFlux (startTime : Time) :
    supercriticalFresnelRegressionConfiguration.interface.plane.normalComponent
      (⨍ time in startTime.val..startTime.val +
          2 * Real.pi / supercriticalFresnelRegressionConfiguration.incident.angularFrequency,
        poyntingVector
          (supercriticalFresnelRegressionConfiguration.incident.electricField +
            supercriticalFresnelRegressionConfiguration.reflected.electricField)
          (supercriticalFresnelRegressionConfiguration.incident.magneticFieldStrength
              supercriticalFresnelRegressionConfiguration.interface.negativeMedium +
            supercriticalFresnelRegressionConfiguration.reflected.magneticFieldStrength
              supercriticalFresnelRegressionConfiguration.interface.negativeMedium)
          (time : Time) supercriticalFresnelRegressionConfiguration.interface.plane.point) = 0 := by
  exact complexFresnel_superposed_normalFlux_eq_zero
    supercriticalFresnelFluxRegression_isFixedFrequencyElectricBoundary
    supercriticalFresnelRegression_exact_hasReferencedTangentialMagneticFieldStrengthBalance
    supercriticalFresnelRegression_configuration_transmittedNormalRadicand_neg
    supercriticalFresnelFluxRegression_incidentConnector
    supercriticalFresnelFluxRegression_reflectedConnector_guarded
    supercriticalFresnelRegression_transmitted_eq_candidate
    supercriticalFresnelFluxRegression_incidentFrame_align
    (fun _ ↦ supercriticalFresnelFluxRegression_reflectedFrame_align)
    supercriticalFresnelFluxRegression_reflection_guard
    supercriticalFresnelFluxRegression_incidentNormal_pos startTime

end

end Optics
