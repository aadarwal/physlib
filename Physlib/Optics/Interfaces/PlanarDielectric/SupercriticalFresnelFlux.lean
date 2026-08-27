/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Interfaces.PlanarDielectric.FresnelInterference
public import Physlib.Optics.Interfaces.PlanarDielectric.SupercriticalFresnel

/-!
# Normal flux for boundary-selected total internal reflection

## i. Overview

This file connects the boundary-selected complex Fresnel amplitudes on the canonical
positive-normal-decay transmitted branch to actual Poynting-flux statements. The incident and
reflected carriers remain ordinary propagating material Jones waves in the negative-side medium.
Unit reflection modulus first gives equal Jones intensity and hence equal material irradiance.
Together with opposite signed propagation normals, their separate actual one-period normal fluxes
sum to zero; the signs are pinned by `supercriticalFresnelFluxRegression_incident_normalFlux`
(`Physlib/Optics/Interfaces/PlanarDielectric/SupercriticalFresnelFluxRegression.lean:149`) and
`supercriticalFresnelFluxRegression_reflected_normalFlux`
(`Physlib/Optics/Interfaces/PlanarDielectric/SupercriticalFresnelFluxRegression.lean:168`).

The canonical transmitted complex carrier is treated through its Maxwell-qualified harmonic-flux
theorem, not through the propagating Jones irradiance formula. Its actual one-period mean normal
flux is zero at every point, pinned by
`supercriticalFresnelFluxRegression_transmitted_normalFlux`
(`Physlib/Optics/Interfaces/PlanarDielectric/SupercriticalFresnelFluxRegression.lean:187`). These
two results give a separate-wave balance. Pointwise cancellation of incident-reflected normal
interference then shows that the actual superposed negative-side field also has zero one-period
normal flux when the reflected carrier is electrically zero or has the incident frequency.

The result is local to the stored interface point on the propagating side. It does not interpret
the transmitted decay-frame Jones norm as power. Unguarded convention statement (review only): it
does not make the transmitted field a positive-power port or supply outgoing semantics. It supplies
no causal, limiting-absorption, aperture-power, or modal-power semantics either.

## ii. Key results

- `complexFresnel_reflected_materialPlaneWaveIrradiance_eq_of_referenced_balances`: equal
  incident and reflected propagating irradiance.
- `complexFresnel_reflected_normalMeanFlux_eq_neg_incident`: opposite separate actual normal mean
  fluxes.
- `complexFresnel_separateWave_normalFlux_balance`: the three separate actual waves balance.
- `complexFresnel_superposedWave_normalFlux_balance`: equality of the actual superposed and
  transmitted normal mean fluxes, with both sides separately proved zero.
- `complexFresnel_superposed_normalFlux_eq_zero`: zero actual normal mean flux of the superposed
  negative-side field.

## iii. Table of contents

- A. Separate-wave total-reflection flux
- B. Actual superposed-field total-reflection flux

## iv. References

The boundary hypotheses are reduced complex-amplitude balances and referenced carrier connectors.
They are not derived here from integral Maxwell laws. No nonzero incident amplitude is required;
the zero solution remains a valid degenerate case. Unguarded convention statement (review only): a
later named physical-classification layer may add a nonzero incident guard when the phrase "an
incident field is totally reflected" is intended.

-/

@[expose] public section

namespace Optics

open Electromagnetism Electromagnetism.ThreeDimension Matrix Space Time
open scoped Interval

noncomputable section

namespace PlanarDielectricWaveConfiguration

variable {configuration : PlanarDielectricWaveConfiguration}
  {incidentDirection reflectedDirection : Space.Direction 3}
  {incidentFrame : PolarizationFrame incidentDirection}
  {reflectedFrame : PolarizationFrame reflectedDirection}
  {incidentJones reflectedJones transmittedRawJones : JonesVector}

/-!

## A. Separate-wave total-reflection flux

-/

/-- Boundary-selected total internal reflection gives equal material irradiance for the
propagating incident and reflected Jones waves in their common negative-side medium.

This equality concerns local propagating-wave flux density. Unguarded convention statement (review
only): it assigns no irradiance or power meaning to the transmitted decay-frame Jones data. -/
lemma complexFresnel_reflected_materialPlaneWaveIrradiance_eq_of_referenced_balances
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
    reflectedJones.materialPlaneWaveIrradiance configuration.interface.negativeMedium =
      incidentJones.materialPlaneWaveIrradiance configuration.interface.negativeMedium := by
  have hIntensity := complexFresnel_reflectedJones_intensity_eq_of_referenced_balances
    hElectric hMagnetic hRadicand hIncident hReflected hTransmitted hIncidentAlign
      hReflectedAlign hReflection hIncidentNormal
  rw [JonesVector.materialPlaneWaveIrradiance_eq_half_inv_impedance_mul_intensity,
    JonesVector.materialPlaneWaveIrradiance_eq_half_inv_impedance_mul_intensity, hIntensity]

/-- The actual reflected own-period mean Poynting flux is the negative of the incident own-period
mean flux along the stored interface normal; the signs are pinned by
`supercriticalFresnelFluxRegression_incident_normalFlux`
(`Physlib/Optics/Interfaces/PlanarDielectric/SupercriticalFresnelFluxRegression.lean:149`) and
`supercriticalFresnelFluxRegression_reflected_normalFlux`
(`Physlib/Optics/Interfaces/PlanarDielectric/SupercriticalFresnelFluxRegression.lean:168`).

An active reflected wave uses the opposite signed propagation normal. In the zero-field branch,
its arbitrary dummy normal contributes no flux, and equal reflected/incident irradiance forces
the incident flux to vanish as well. -/
lemma complexFresnel_reflected_normalMeanFlux_eq_neg_incident
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
      configuration.interface.plane.normalComponent incidentFrame.propagationVector)
    (startTime : Time) :
    configuration.interface.plane.normalComponent
        (⨍ time in startTime.val..startTime.val +
            2 * Real.pi / configuration.reflected.angularFrequency,
          poyntingVector configuration.reflected.electricField
            (configuration.reflected.magneticFieldStrength
              configuration.interface.negativeMedium)
            (time : Time) configuration.interface.plane.point) =
      -configuration.interface.plane.normalComponent
        (⨍ time in startTime.val..startTime.val +
            2 * Real.pi / configuration.incident.angularFrequency,
          poyntingVector configuration.incident.electricField
            (configuration.incident.magneticFieldStrength
              configuration.interface.negativeMedium)
            (time : Time) configuration.interface.plane.point) := by
  have hIrradiance :=
    complexFresnel_reflected_materialPlaneWaveIrradiance_eq_of_referenced_balances hElectric
      hMagnetic hRadicand hIncident hReflected hTransmitted hIncidentAlign hReflectedAlign
        hReflection hIncidentNormal
  rw [hReflected.normalComponent_intervalAverage_poyntingVector_planePoint,
    hIncident.normalComponent_intervalAverage_poyntingVector_planePoint, ← hIrradiance]
  rcases hReflection with hZero | hNormal
  · have hJonesZero := hReflected.components_eq_zero_of_electricAmplitude_eq_zero hZero
    have hIrradianceZero :
        reflectedJones.materialPlaneWaveIrradiance configuration.interface.negativeMedium = 0 := by
      simp [JonesVector.materialPlaneWaveIrradiance, JonesVector.intensity, hJonesZero]
    rw [hIrradianceZero]
    ring
  · rw [hNormal]
    ring

/-- The boundary-selected positive-normal-decay solution balances the three separate actual
one-period mean normal fluxes: the incident and reflected propagating contributions cancel, and
the transmitted decay carrier has zero normal mean flux. The three values are pinned by
`supercriticalFresnelFluxRegression_incident_normalFlux`
(`Physlib/Optics/Interfaces/PlanarDielectric/SupercriticalFresnelFluxRegression.lean:149`),
`supercriticalFresnelFluxRegression_reflected_normalFlux`
(`Physlib/Optics/Interfaces/PlanarDielectric/SupercriticalFresnelFluxRegression.lean:168`), and
`supercriticalFresnelFluxRegression_transmitted_normalFlux`
(`Physlib/Optics/Interfaces/PlanarDielectric/SupercriticalFresnelFluxRegression.lean:187`). -/
lemma complexFresnel_separateWave_normalFlux_balance
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
      configuration.interface.plane.normalComponent incidentFrame.propagationVector)
    (startTime : Time) :
    configuration.HasSeparateWaveNormalFluxBalance startTime := by
  have hReflectedFlux := complexFresnel_reflected_normalMeanFlux_eq_neg_incident hElectric
    hMagnetic hRadicand hIncident hReflected hTransmitted hIncidentAlign hReflectedAlign hReflection
      hIncidentNormal startTime
  have hPositive := positiveNormalDecayTransmittedJonesCandidate_normalMeanFlux_eq_zero
    configuration hRadicand transmittedRawJones startTime configuration.interface.plane.point
  rw [HasSeparateWaveNormalFluxBalance, hTransmitted, hReflectedFlux, add_neg_cancel, hPositive]

/-!

## B. Actual superposed-field total-reflection flux

-/

/-- The boundary-selected total-reflection solution satisfies the existing actual superposed-wave
normal-flux balance predicate.

Normal interference cancels pointwise. Frequency matching is used only to replace the active
reflected carrier's averaging period; a zero reflected field retains arbitrary dummy frequency and
frame data. -/
lemma complexFresnel_superposedWave_normalFlux_balance
    (hElectric : configuration.IsFixedFrequencyElectricBoundary)
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
      configuration.interface.plane.normalComponent incidentFrame.propagationVector)
    (startTime : Time) :
    configuration.HasSuperposedWaveNormalFluxBalance startTime := by
  let planeFrame :=
    (configuration.positiveNormalDecayTransmittedPolarizationFrame hRadicand).planeFrame
  have hSeparate := complexFresnel_separateWave_normalFlux_balance hElectric.2
    hMagnetic hRadicand hIncident hReflected hTransmitted hIncidentAlign hReflectedAlign hReflection
      hIncidentNormal startTime
  have hFrequency : configuration.reflected.electricAmplitude = 0 ∨
      configuration.reflected.angularFrequency = configuration.incident.angularFrequency :=
    hElectric.1.2.imp id And.left
  have hCombined :
      configuration.interface.plane.normalComponent
          (⨍ time in startTime.val..startTime.val +
              2 * Real.pi / configuration.incident.angularFrequency,
            poyntingVector
              (configuration.incident.electricField + configuration.reflected.electricField)
              (configuration.incident.magneticFieldStrength
                  configuration.interface.negativeMedium +
                configuration.reflected.magneticFieldStrength
                  configuration.interface.negativeMedium)
              (time : Time) configuration.interface.plane.point) =
        configuration.interface.plane.normalComponent
            (⨍ time in startTime.val..startTime.val +
                2 * Real.pi / configuration.incident.angularFrequency,
              poyntingVector configuration.incident.electricField
                (configuration.incident.magneticFieldStrength
                  configuration.interface.negativeMedium)
                (time : Time) configuration.interface.plane.point) +
          configuration.interface.plane.normalComponent
            (⨍ time in startTime.val..startTime.val +
                2 * Real.pi / configuration.reflected.angularFrequency,
              poyntingVector configuration.reflected.electricField
                (configuration.reflected.magneticFieldStrength
                  configuration.interface.negativeMedium)
                (time : Time) configuration.interface.plane.point) := by
    by_cases hZero : configuration.reflected.electricAmplitude = 0
    · have hReflectedZero := hReflected.reframe_of_electricAmplitude_eq_zero planeFrame hZero
      exact incidentReflected_normalComponent_intervalAverage_poyntingVector_add_ownPeriods
        planeFrame hIncident hReflectedZero hIncidentAlign rfl (Or.inl hZero) (Or.inl hZero)
          startTime
    · exact incidentReflected_normalComponent_intervalAverage_poyntingVector_add_ownPeriods
        planeFrame hIncident hReflected hIncidentAlign (hReflectedAlign hZero) hFrequency
          hReflection startTime
  have hTransmittedFrequency :
      configuration.transmitted.angularFrequency = configuration.incident.angularFrequency := by
    rw [hTransmitted]
    exact positiveNormalDecayTransmittedJonesCandidate_angularFrequency configuration hRadicand
      transmittedRawJones
  rw [HasSuperposedWaveNormalFluxBalance, hCombined]
  rw [HasSeparateWaveNormalFluxBalance] at hSeparate
  simpa only [hTransmittedFrequency] using hSeparate

/-- Under fixed-frequency electric phase matching, the actual superposed incident-plus-reflected
field has zero one-period mean Poynting component along the stored interface normal.

This is a corollary of the superposed-wave balance and the independently proved zero normal mean
flux of the canonical transmitted decay carrier. -/
lemma complexFresnel_superposed_normalFlux_eq_zero
    (hElectric : configuration.IsFixedFrequencyElectricBoundary)
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
      configuration.interface.plane.normalComponent incidentFrame.propagationVector)
    (startTime : Time) :
    configuration.interface.plane.normalComponent
      (⨍ time in startTime.val..startTime.val +
          2 * Real.pi / configuration.incident.angularFrequency,
        poyntingVector
          (configuration.incident.electricField + configuration.reflected.electricField)
          (configuration.incident.magneticFieldStrength configuration.interface.negativeMedium +
            configuration.reflected.magneticFieldStrength
              configuration.interface.negativeMedium)
          (time : Time) configuration.interface.plane.point) = 0 := by
  have hBalance := complexFresnel_superposedWave_normalFlux_balance hElectric hMagnetic hRadicand
    hIncident hReflected hTransmitted hIncidentAlign hReflectedAlign hReflection hIncidentNormal
      startTime
  have hPositive := positiveNormalDecayTransmittedJonesCandidate_normalMeanFlux_eq_zero
    configuration hRadicand transmittedRawJones startTime configuration.interface.plane.point
  have hTransmittedFrequency :
      configuration.transmitted.angularFrequency = configuration.incident.angularFrequency := by
    rw [hTransmitted]
    exact positiveNormalDecayTransmittedJonesCandidate_angularFrequency configuration hRadicand
      transmittedRawJones
  rw [HasSuperposedWaveNormalFluxBalance] at hBalance
  rw [← hTransmitted, hTransmittedFrequency] at hPositive
  exact hBalance.trans hPositive

end PlanarDielectricWaveConfiguration

end

end Optics
