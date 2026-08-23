/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Interfaces.PlanarDielectric.PhaseMatchedDispersion

/-!
# Angular geometry at a planar dielectric interface

## i. Overview

This file assigns side-relative phase angles to the incident, reflected, and transmitted labels of
a planar dielectric wave configuration. The incident and transmitted phase vectors are measured
from the unit normal into the positive side, while the reflected phase vector is measured from the
unit normal into the negative side. These choices give angles below `π / 2` when separately
supplied phase-direction hypotheses agree with the labels.

The angle definitions are total. In particular, a zero phase vector has angle `π / 2` by Mathlib's
unoriented vector-angle convention. The reflected wave can also have zero electric amplitude and
retain arbitrary dummy wave-vector data. Consequently, the angular reflection result preserves
that zero-amplitude alternative rather than assigning physical meaning to its angle.

For an active reflected wave, common negative-medium dispersion and electric phase matching leave
the incident wave vector or its hyperplane reflection as the algebraic possibilities. Explicit
strict phase directions into opposite sides select the reflection branch, and neutral vector
reflection then proves equality of the incident and reflected phase angles. This is a phase-angle
law. It does not identify phase direction with group velocity, energy flux, a ray, outgoing
behavior, irradiance, or power.

## ii. Key results

- `incidentPhaseAngle`: incident phase angle from the positive-side normal.
- `reflectedPhaseAngle`: reflected phase angle from the negative-side normal.
- `transmittedPhaseAngle`: transmitted phase angle from the positive-side normal.
- `reflectedPhaseAngle_eq_incidentPhaseAngle_of_hyperplaneReflection`: the selected complex
  reflection branch obeys the phase-angle law.
- `reflected_electricAmplitude_eq_zero_or_phaseAngles_eq_of_phaseDirections`:
  phase matching, dispersion, and supplied phase directions give the guarded angular law.

## iii. Table of contents

- A. Label-relative phase angles
- B. Acute-angle ranges from phase direction
- C. Angular law of reflection

## iv. References

The construction specializes Physlib's neutral hyperplane-angle and complex-wave-vector reflection
APIs to the existing planar dielectric configuration. No external formal-development source is
copied or translated here.
-/

@[expose] public section

namespace Optics

open ClassicalMechanics Electromagnetism Electromagnetism.ThreeDimension Space

noncomputable section

namespace PlanarDielectricWaveConfiguration

/-!

## A. Label-relative phase angles

-/

/-- The incident phase-vector angle measured from the unit interface normal into the positive
side.

The choice of side normal is a measurement convention; the incident label alone does not imply
phase direction into that side. A zero phase vector receives the total angle value `π / 2`. -/
noncomputable def incidentPhaseAngle (configuration : PlanarDielectricWaveConfiguration) : ℝ :=
  configuration.incident.waveVector.phaseAngleToSide configuration.interface.plane .positive

/-- The reflected phase-vector angle measured from the unit interface normal into the negative
side.

The choice of side normal is a measurement convention; the reflected label alone does not imply
phase direction into that side. A zero phase vector receives the total angle value `π / 2`, while
a zero-electric-amplitude reflected candidate retains arbitrary dummy wave-vector data. -/
noncomputable def reflectedPhaseAngle (configuration : PlanarDielectricWaveConfiguration) : ℝ :=
  configuration.reflected.waveVector.phaseAngleToSide configuration.interface.plane .negative

/-- The transmitted phase-vector angle measured from the unit interface normal into the positive
side.

The choice of side normal is a measurement convention; the transmitted label alone does not imply
phase direction into that side. A zero phase vector receives the total angle value `π / 2`. -/
noncomputable def transmittedPhaseAngle (configuration : PlanarDielectricWaveConfiguration) : ℝ :=
  configuration.transmitted.waveVector.phaseAngleToSide configuration.interface.plane .positive

/-!

## B. Acute-angle ranges from phase direction

-/

/-- A supplied incident phase direction into the positive side places the incident phase angle in
`[0, π / 2)`. -/
lemma incidentPhaseAngle_mem_Ico_of_isPhaseDirectedInto
    (configuration : PlanarDielectricWaveConfiguration)
    (hDirection : configuration.incident.waveVector.IsPhaseDirectedInto
      configuration.interface.plane .positive) :
    configuration.incidentPhaseAngle ∈ Set.Ico 0 (Real.pi / 2) := by
  simpa only [incidentPhaseAngle] using
    configuration.incident.waveVector.phaseAngleToSide_mem_Ico_of_isPhaseDirectedInto
      configuration.interface.plane .positive hDirection

/-- A supplied reflected phase direction into the negative side places the reflected phase angle
in `[0, π / 2)`. -/
lemma reflectedPhaseAngle_mem_Ico_of_isPhaseDirectedInto
    (configuration : PlanarDielectricWaveConfiguration)
    (hDirection : configuration.reflected.waveVector.IsPhaseDirectedInto
      configuration.interface.plane .negative) :
    configuration.reflectedPhaseAngle ∈ Set.Ico 0 (Real.pi / 2) := by
  simpa only [reflectedPhaseAngle] using
    configuration.reflected.waveVector.phaseAngleToSide_mem_Ico_of_isPhaseDirectedInto
      configuration.interface.plane .negative hDirection

/-- A supplied transmitted phase direction into the positive side places the transmitted phase
angle in `[0, π / 2)`. -/
lemma transmittedPhaseAngle_mem_Ico_of_isPhaseDirectedInto
    (configuration : PlanarDielectricWaveConfiguration)
    (hDirection : configuration.transmitted.waveVector.IsPhaseDirectedInto
      configuration.interface.plane .positive) :
    configuration.transmittedPhaseAngle ∈ Set.Ico 0 (Real.pi / 2) := by
  simpa only [transmittedPhaseAngle] using
    configuration.transmitted.waveVector.phaseAngleToSide_mem_Ico_of_isPhaseDirectedInto
      configuration.interface.plane .positive hDirection

/-!

## C. Angular law of reflection

-/

/-- If the reflected wave vector is the neutral hyperplane reflection of the incident wave vector,
then their phase angles relative to the selected positive- and negative-side normals are equal. -/
lemma reflectedPhaseAngle_eq_incidentPhaseAngle_of_hyperplaneReflection
    (configuration : PlanarDielectricWaveConfiguration)
    (hReflection : configuration.reflected.waveVector =
      ComplexWaveVector.hyperplaneReflection configuration.interface.plane
        configuration.incident.waveVector) :
    configuration.reflectedPhaseAngle = configuration.incidentPhaseAngle := by
  rw [reflectedPhaseAngle, incidentPhaseAngle, hReflection]
  simpa using
    (ComplexWaveVector.phaseAngleToSide_hyperplaneReflection
      configuration.interface.plane .positive configuration.incident.waveVector)

namespace IsElectricPhaseMatched

variable {configuration : PlanarDielectricWaveConfiguration}

/-- Electric phase matching, common negative-medium dispersion, and supplied strict incident and
active-reflected phase directions imply the phase-angle law of reflection, while preserving the
zero-electric-amplitude dummy-label branch.

This result derives neither phase direction from the wave-role labels nor a group-velocity,
energy-flux, outgoing, irradiance, or power statement. -/
lemma reflected_electricAmplitude_eq_zero_or_phaseAngles_eq_of_phaseDirections
    (h : configuration.IsElectricPhaseMatched)
    (hIncidentDispersion : configuration.incident.IsDispersionMatched
      configuration.interface.negativeMedium)
    (hReflectedDispersion : configuration.reflected.electricAmplitude ≠ 0 →
      configuration.reflected.IsDispersionMatched configuration.interface.negativeMedium)
    (hIncidentPhase : configuration.incident.waveVector.IsPhaseDirectedInto
      configuration.interface.plane .positive)
    (hReflectedPhase : configuration.reflected.electricAmplitude ≠ 0 →
      configuration.reflected.waveVector.IsPhaseDirectedInto
        configuration.interface.plane .negative) :
    configuration.reflected.electricAmplitude = 0 ∨
      configuration.reflectedPhaseAngle = configuration.incidentPhaseAngle := by
  rcases
      h.reflected_electricAmplitude_eq_zero_or_waveVector_eq_hyperplaneReflection_of_phaseDirections
        hIncidentDispersion hReflectedDispersion hIncidentPhase hReflectedPhase with
    hZero | hReflection
  · exact Or.inl hZero
  · exact Or.inr
      (configuration.reflectedPhaseAngle_eq_incidentPhaseAngle_of_hyperplaneReflection
        hReflection)

end IsElectricPhaseMatched
end PlanarDielectricWaveConfiguration

end
end Optics
