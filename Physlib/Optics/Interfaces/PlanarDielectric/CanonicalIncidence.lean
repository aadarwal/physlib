/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Interfaces.PlanarDielectric.PhaseMatchedDispersion
public import Physlib.Optics.Polarization.IncidenceFrame
public import Physlib.Optics.Polarization.ReferencedMaterialWave

/-!
# Canonical incidence data at a planar dielectric interface

## i. Overview

This file connects electric phase matching and real propagating material Jones waves to the
canonical incidence-frame geometry. A strictly positive incident frame normal and a strictly
negative active-reflected frame normal select opposite phase directions. Material dispersion and
phase matching then select hyperplane reflection of the active reflected wave vector. The
referenced-wave connector descends that complex-vector result to exact reflection of the real
frame propagation vector, and hence to the required negated normal component.

For non-normal incidence, canonical incident and transmitted frames share the same `s` axis
because phase matching equates positive scalar multiples of tangential propagation directions.
An active canonical reflected frame shares that axis because hyperplane reflection preserves the
incidence plane. The reflected-frame hypothesis remains conditional on nonzero electric amplitude.
A zero reflected field therefore keeps arbitrary dummy carrier, direction, frame, and frequency
data.

Unguarded convention statement (review only): `HasCanonicalNonNormalIncidenceFrames` packages the
three role-indexed basis conventions without assigning propagation signs from those roles.
Incident and transmitted canonicality are unconditional; reflected canonicality is required only
for an electrically active reflected wave.

The selected normal signs are explicit geometric branch hypotheses. Unguarded convention
statement (review only): they do not follow from the incident or reflected labels and are not
identified here with group velocity, energy flux, or an outgoing radiation condition. At normal
incidence these hypotheses select no unique incidence plane or `s` axis; an independently selected
tangent frame is required.

## ii. Key results

- `.reflected_electricAmplitude_eq_zero_or_propagationVector_eq_vectorReflection`:
  the selected reflected branch descends to the real frame propagation vectors.
- `.reflected_electricAmplitude_eq_zero_or_normalComponent_propagationVector_eq_neg`:
  the reflected normal guard used by the real propagating Fresnel layer.
- `PlanarDielectricWaveConfiguration.HasCanonicalNonNormalIncidenceFrames`: the guarded
  incident/reflected/transmitted canonical `s`/`p` basis convention.
- `IsElectricPhaseMatched.canonicalIncidenceFrame_data`: one interface-plane frame supplies the
  common `s` axis for the incident, transmitted, and active reflected canonical frames.

## iii. Table of contents

- A. Role-specific canonical non-normal frames
- B. Selected reflected propagation branch
- C. Common canonical incidence-frame data

## iv. References

This module combines Physlib's independently implemented phase-matched dispersion, referenced
material-wave, hyperplane-reflection, and incidence-frame APIs. No external formal-development
source is copied or translated here.
-/

@[expose] public section

namespace Optics

open ClassicalMechanics Electromagnetism Electromagnetism.ThreeDimension Space
open ClassicalMechanics.ComplexWaveVector
open Electromagnetism.ThreeDimension.ComplexMonochromaticPlaneWave

noncomputable section

namespace PlanarDielectricWaveConfiguration

/-!

## A. Role-specific canonical non-normal frames

-/

/-- The incident, transmitted, and electrically active reflected propagation frames use the
canonical non-normal incidence `s`/`p` convention of an interface.

This bundle records basis conventions only. Unguarded convention statement (review only): its role
names do not imply propagation signs, phase directions, reflection, material-wave connectivity,
boundary balance, or power flow. The reflected condition is guarded so an electrically zero
reflected wave retains arbitrary dummy carrier, direction, frame, and frequency data. -/
structure HasCanonicalNonNormalIncidenceFrames
    (configuration : PlanarDielectricWaveConfiguration)
    {incidentDirection reflectedDirection transmittedDirection : Space.Direction 3}
    (incidentFrame : PolarizationFrame incidentDirection)
    (reflectedFrame : PolarizationFrame reflectedDirection)
    (transmittedFrame : PolarizationFrame transmittedDirection) : Prop where
  /-- The incident frame uses the canonical non-normal incidence basis convention. -/
  incident : incidentFrame.IsCanonicalNonNormalIncidenceFrame
    configuration.interface.plane.normal
  /-- A nonzero reflected electric field uses the canonical non-normal incidence basis
  convention. -/
  reflected_of_electricAmplitude_ne_zero :
    configuration.reflected.electricAmplitude ≠ 0 →
      reflectedFrame.IsCanonicalNonNormalIncidenceFrame
        configuration.interface.plane.normal
  /-- The transmitted frame uses the canonical non-normal incidence basis convention. -/
  transmitted : transmittedFrame.IsCanonicalNonNormalIncidenceFrame
    configuration.interface.plane.normal

end PlanarDielectricWaveConfiguration

namespace PlanarDielectricWaveConfiguration.IsElectricPhaseMatched

variable {configuration : PlanarDielectricWaveConfiguration}
  {incidentDirection reflectedDirection transmittedDirection : Space.Direction 3}
  {incidentFrame : PolarizationFrame incidentDirection}
  {reflectedFrame : PolarizationFrame reflectedDirection}
  {transmittedFrame : PolarizationFrame transmittedDirection}
  {incidentJones reflectedJones transmittedJones : JonesVector}

/-!

## B. Selected reflected propagation branch

-/

/-- Phase matching, referenced material data, and explicit opposite normal directions give the
zero-reflected alternative or exact reflection of the real frame propagation vector.

The active reflected normal premise selects only a geometric phase branch. The zero branch leaves
all reflected carrier and frame labels unconstrained. -/
lemma reflected_electricAmplitude_eq_zero_or_propagationVector_eq_vectorReflection
    (hPhase : configuration.IsElectricPhaseMatched)
    (hIncident : IsReferencedMaterialJonesWave configuration.interface.plane
      configuration.interface.negativeMedium configuration.incident incidentFrame incidentJones)
    (hReflected : IsZeroOrReferencedMaterialJonesWave configuration.interface.plane
      configuration.interface.negativeMedium configuration.reflected reflectedFrame reflectedJones)
    (hIncidentNormal : 0 <
      configuration.interface.plane.normalComponent incidentFrame.propagationVector)
    (hReflectedNormal : configuration.reflected.electricAmplitude ≠ 0 →
      configuration.interface.plane.normalComponent reflectedFrame.propagationVector < 0) :
    configuration.reflected.electricAmplitude = 0 ∨
      reflectedFrame.propagationVector =
        configuration.interface.plane.vectorReflection incidentFrame.propagationVector := by
  by_cases hZero : configuration.reflected.electricAmplitude = 0
  · exact Or.inl hZero
  · right
    have hReflectedMaterial : IsReferencedMaterialJonesWave configuration.interface.plane
        configuration.interface.negativeMedium configuration.reflected reflectedFrame
          reflectedJones := by
      rcases hReflected with hZeroData | hMaterial
      · exact (hZero hZeroData.1).elim
      · exact hMaterial
    have hIncidentPhase : configuration.incident.waveVector.IsPhaseDirectedInto
        configuration.interface.plane .positive :=
      (hIncident.isPhaseDirectedInto_iff .positive).2 (by
        simpa using hIncidentNormal)
    have hReflectedPhase : configuration.reflected.waveVector.IsPhaseDirectedInto
        configuration.interface.plane .negative :=
      (hReflectedMaterial.isPhaseDirectedInto_iff .negative).2 (by
        simpa using hReflectedNormal hZero)
    have hWaveReflection : configuration.reflected.waveVector =
        hyperplaneReflection configuration.interface.plane
          configuration.incident.waveVector :=
      (reflected_electricAmplitude_eq_zero_or_waveVector_eq_hyperplaneReflection_of_phaseDirections
        hPhase hIncident.isDispersionMatched (fun _ ↦ hReflectedMaterial.isDispersionMatched)
          hIncidentPhase (fun _ ↦ hReflectedPhase)).resolve_left hZero
    have hFrequency : configuration.reflected.angularFrequency =
        configuration.incident.angularFrequency :=
      (hPhase.2.resolve_left hZero).1
    exact hIncident.propagationVector_eq_vectorReflection_of_waveVector_eq
      hReflectedMaterial hFrequency hWaveReflection

/-- The selected reflected propagation branch gives the exact zero-or-negated-normal guard used
by the real propagating Fresnel equations. -/
lemma reflected_electricAmplitude_eq_zero_or_normalComponent_propagationVector_eq_neg
    (hPhase : configuration.IsElectricPhaseMatched)
    (hIncident : IsReferencedMaterialJonesWave configuration.interface.plane
      configuration.interface.negativeMedium configuration.incident incidentFrame incidentJones)
    (hReflected : IsZeroOrReferencedMaterialJonesWave configuration.interface.plane
      configuration.interface.negativeMedium configuration.reflected reflectedFrame reflectedJones)
    (hIncidentNormal : 0 <
      configuration.interface.plane.normalComponent incidentFrame.propagationVector)
    (hReflectedNormal : configuration.reflected.electricAmplitude ≠ 0 →
      configuration.interface.plane.normalComponent reflectedFrame.propagationVector < 0) :
    configuration.reflected.electricAmplitude = 0 ∨
      configuration.interface.plane.normalComponent reflectedFrame.propagationVector =
        -configuration.interface.plane.normalComponent incidentFrame.propagationVector := by
  exact (hPhase.reflected_electricAmplitude_eq_zero_or_propagationVector_eq_vectorReflection
    hIncident hReflected hIncidentNormal hReflectedNormal).imp id (fun hReflection ↦ by
      rw [hReflection, configuration.interface.plane.normalComponent_vectorReflection])

/-!

## C. Common canonical incidence-frame data

-/

/-- Canonical non-normal incident and transmitted frames, together with an active canonical
reflected frame, produce one interface-plane frame with a common `s` axis and the selected
reflected propagation vector.

The reflected canonical-frame premise is conditional so the zero field retains completely
arbitrary dummy frame and carrier labels. No reflected-frame equality is needed unconditionally. -/
lemma canonicalIncidenceFrame_data
    (hPhase : configuration.IsElectricPhaseMatched)
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
      configuration.interface.plane.normalComponent reflectedFrame.propagationVector < 0) :
    ∃ planeFrame : PolarizationFrame configuration.interface.plane.normal,
      incidentFrame.axis 0 = planeFrame.axis 0 ∧
        transmittedFrame.axis 0 = planeFrame.axis 0 ∧
        (configuration.reflected.electricAmplitude = 0 ∨
          reflectedFrame.axis 0 = planeFrame.axis 0 ∧
            reflectedFrame.propagationVector =
              configuration.interface.plane.vectorReflection incidentFrame.propagationVector) := by
  rcases hFrames.incident with ⟨hIncidentNonNormal, hIncidentCanonical⟩
  rcases hFrames.transmitted with ⟨hTransmittedNonNormal, hTransmittedCanonical⟩
  let planeFrame := incidencePlaneFrame configuration.interface.plane incidentDirection
    hIncidentNonNormal
  have hIncidentAlign : incidentFrame.axis 0 = planeFrame.axis 0 := by
    rw [hIncidentCanonical]
    exact incidencePolarizationFrame_axis_zero_eq_incidencePlaneFrame
      configuration.interface.plane incidentDirection hIncidentNonNormal
  have hTangential := hPhase.transmitted_tangentialPhase_attenuation_eq_incident.1
  rw [hTransmitted.waveVector_eq, hIncident.waveVector_eq, phaseVector_ofReal,
    phaseVector_ofReal] at hTangential
  have hCanonicalAxes :=
    incidencePolarizationFrame_axis_zero_eq_of_pos_smul_tangentialProjection_eq
      configuration.interface.plane transmittedDirection incidentDirection
        hTransmittedNonNormal hIncidentNonNormal
        (configuration.transmitted.angularFrequency /
          configuration.interface.positiveMedium.waveSpeed)
        (configuration.incident.angularFrequency /
          configuration.interface.negativeMedium.waveSpeed)
        (div_pos configuration.transmitted.angularFrequency_pos
          configuration.interface.positiveMedium.waveSpeed_pos)
        (div_pos configuration.incident.angularFrequency_pos
          configuration.interface.negativeMedium.waveSpeed_pos)
        hTangential
  have hTransmittedAlign : transmittedFrame.axis 0 = planeFrame.axis 0 := by
    rw [hTransmittedCanonical]
    exact hCanonicalAxes.trans
      (incidencePolarizationFrame_axis_zero_eq_incidencePlaneFrame
        configuration.interface.plane incidentDirection hIncidentNonNormal)
  refine ⟨planeFrame, hIncidentAlign, hTransmittedAlign, ?_⟩
  by_cases hZero : configuration.reflected.electricAmplitude = 0
  · exact Or.inl hZero
  · right
    have hReflection :=
      (hPhase.reflected_electricAmplitude_eq_zero_or_propagationVector_eq_vectorReflection
        hIncident hReflected hIncidentNormal hReflectedNormal).resolve_left hZero
    rcases hFrames.reflected_of_electricAmplitude_ne_zero hZero with
      ⟨hReflectedNonNormal, hCanonical⟩
    have hDirectionReflection : Space.basis.repr reflectedDirection.unit =
        configuration.interface.plane.vectorReflection
          (Space.basis.repr incidentDirection.unit) := by
      simpa only [PolarizationFrame.propagationVector] using hReflection
    have hReflectedAlign : reflectedFrame.axis 0 = planeFrame.axis 0 := by
      rw [hCanonical]
      exact
        incidencePolarizationFrame_axis_zero_eq_incidencePlaneFrame_of_vectorReflection
          configuration.interface.plane incidentDirection reflectedDirection
            hIncidentNonNormal hReflectedNonNormal hDirectionReflection
    exact ⟨hReflectedAlign, hReflection⟩

end PlanarDielectricWaveConfiguration.IsElectricPhaseMatched

end

end Optics
