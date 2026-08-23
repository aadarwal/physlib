/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Interfaces.PlanarDielectric.ElectricLabelMatching

/-!
# Electric boundary activity and tangential-projection conservation

## i. Overview

This file extracts the direct physical consequences of conditional electric label matching at a
planar dielectric boundary. The weakest boundary hypothesis is the two-law electric predicate with
zero free surface charge, together with the exact nonzero incident-exponent joint-electric
aggregate. A full local boundary inherits every result through its electric projection. No common
frequency or wave-vector matching is assumed.

First, the aggregate is equal to the transmitted stored-point-referenced joint electric
coefficient in either reflected branch. Its nonvanishing therefore forces the transmitted electric
amplitude to be nonzero. This makes the transmitted label electrically active, but does not assign
it an outgoing, propagating, on-shell, or positive-power role.

Second, `boundaryExponent_eq_iff` decodes the exponent equalities from label matching. The
transmitted angular frequency and every complex-bilinear wave-vector pairing against a real
tangent displacement equal the incident ones. The same conclusion holds for the reflected wave
unless its electric amplitude is zero; in that branch its frequency and wave vector remain
unconstrained dummy data.

The neutral complex-wave-vector hyperplane API packages those tangent-pairing equalities as exact
equalities of complex tangential projections. These retain both tangential phase and attenuation
information, but do not assert full wave-vector equality or constrain a normal component. This
file proves no Maxwell, material-dispersion, propagation-branch, Snell, Fresnel, irradiance, or
power result. The free surface current remains arbitrary.

## ii. Key results

- `transmitted_electricAmplitude_ne_zero`:
  activity of the transmitted electric label.
- `transmitted_angularFrequency_tangentPairing_eq_incident`:
  transmitted frequency and tangent-pairing conservation.
- `transmitted_angularFrequency_tangentialProjection_eq_incident`:
  transmitted frequency and complex tangential-projection conservation.
- `reflected_electricAmplitude_eq_zero_or_angularFrequency_tangentPairing_eq_incident`:
  the zero-reflection-preserving reflected conservation alternative.
- `reflected_electricAmplitude_eq_zero_or_angularFrequency_tangentialProjection_eq_incident`:
  the corresponding reflected complex tangential-projection alternative.

## iii. Table of contents

- A. Transmitted electric activity
- B. Transmitted conservation
- C. Reflected conservation
- D. Full local boundary wrappers

## iv. References

This module specializes Physlib's electric boundary label-matching theorem and boundary-exponent
characterization. No external formal-development source is copied or translated here.
-/

@[expose] public section

namespace Optics

open ClassicalMechanics Electromagnetism Electromagnetism.ThreeDimension
open Electromagnetism.ThreeDimension.ComplexMonochromaticPlaneWave

noncomputable section

namespace PlanarDielectricWaveConfiguration
namespace IsElectricBoundary

variable {configuration : PlanarDielectricWaveConfiguration}

/-!

## A. Transmitted electric activity

-/

/-- A nonzero incident-key joint-electric aggregate at a local electric boundary forces the
transmitted electric amplitude to be nonzero. -/
lemma transmitted_electricAmplitude_ne_zero
    (h : configuration.IsElectricBoundary 0)
    (hAggregate : configuration.incidentExponentJointElectricAggregate ≠ 0) :
    configuration.transmitted.electricAmplitude ≠ 0 := by
  have hMatching := h.jointElectricBoundaryLabelMatching hAggregate
  have hAggregate_eq :
      configuration.incidentExponentJointElectricAggregate =
        referencedMediumJointElectricTraceAmplitude configuration.interface.plane
          configuration.interface.positiveMedium configuration.transmitted := by
    rcases hMatching.2.1 with hzero | hExponent
    · rw [← referencedMediumJointElectricTraceAmplitude_eq_zero_iff
        configuration.interface.plane configuration.interface.negativeMedium] at hzero
      simpa [incidentExponentJointElectricAggregate, hzero] using hMatching.2.2.symm
    · simpa [incidentExponentJointElectricAggregate, hExponent] using hMatching.2.2.symm
  intro hzero
  apply hAggregate
  rw [hAggregate_eq, referencedMediumJointElectricTraceAmplitude_eq_zero_iff]
  exact hzero

/-!

## B. Transmitted conservation

-/

/-- Conditional electric label matching makes the transmitted angular frequency and every tangent
wave-vector pairing equal to the incident ones. -/
lemma transmitted_angularFrequency_tangentPairing_eq_incident
    (h : configuration.IsElectricBoundary 0)
    (hAggregate : configuration.incidentExponentJointElectricAggregate ≠ 0) :
    configuration.transmitted.angularFrequency = configuration.incident.angularFrequency ∧
      ∀ v : configuration.interface.plane.tangentSubmodule,
        ComplexWaveVector.bilinearDot configuration.transmitted.waveVector
            (ComplexWaveVector.ofReal (v : EuclideanSpace ℝ (Fin 3))) =
          ComplexWaveVector.bilinearDot configuration.incident.waveVector
            (ComplexWaveVector.ofReal (v : EuclideanSpace ℝ (Fin 3))) := by
  exact (boundaryExponent_eq_iff configuration.interface.plane
    configuration.transmitted configuration.incident).mp
      (h.jointElectricBoundaryLabelMatching hAggregate).1

/-- Conditional electric label matching makes the transmitted angular frequency and complex
hyperplane-tangential wave vector equal to the incident ones. -/
lemma transmitted_angularFrequency_tangentialProjection_eq_incident
    (h : configuration.IsElectricBoundary 0)
    (hAggregate : configuration.incidentExponentJointElectricAggregate ≠ 0) :
    configuration.transmitted.angularFrequency = configuration.incident.angularFrequency ∧
      ComplexWaveVector.hyperplaneTangentialProjection configuration.interface.plane
          configuration.transmitted.waveVector =
        ComplexWaveVector.hyperplaneTangentialProjection configuration.interface.plane
          configuration.incident.waveVector := by
  have hConservation := h.transmitted_angularFrequency_tangentPairing_eq_incident hAggregate
  exact ⟨hConservation.1,
    (ComplexWaveVector.hyperplaneTangentialProjection_eq_iff_bilinearDot_eq_on_tangent
      configuration.interface.plane configuration.transmitted.waveVector
        configuration.incident.waveVector).mpr hConservation.2⟩

/-!

## C. Reflected conservation

-/

/-- Conditional electric label matching either leaves a zero-amplitude reflected wave's frequency
and wave vector unconstrained, or makes its angular frequency and every tangent wave-vector pairing
equal to the incident ones. -/
lemma reflected_electricAmplitude_eq_zero_or_angularFrequency_tangentPairing_eq_incident
    (h : configuration.IsElectricBoundary 0)
    (hAggregate : configuration.incidentExponentJointElectricAggregate ≠ 0) :
    configuration.reflected.electricAmplitude = 0 ∨
      (configuration.reflected.angularFrequency = configuration.incident.angularFrequency ∧
        ∀ v : configuration.interface.plane.tangentSubmodule,
          ComplexWaveVector.bilinearDot configuration.reflected.waveVector
              (ComplexWaveVector.ofReal (v : EuclideanSpace ℝ (Fin 3))) =
            ComplexWaveVector.bilinearDot configuration.incident.waveVector
              (ComplexWaveVector.ofReal (v : EuclideanSpace ℝ (Fin 3)))) := by
  rcases (h.jointElectricBoundaryLabelMatching hAggregate).2.1 with hzero | hExponent
  · exact Or.inl hzero
  · exact Or.inr ((boundaryExponent_eq_iff configuration.interface.plane
      configuration.reflected configuration.incident).mp hExponent)

/-- Conditional electric label matching either leaves a zero-amplitude reflected wave's frequency
and wave vector unconstrained, or makes its angular frequency and complex hyperplane-tangential
wave vector equal to the incident ones. -/
lemma reflected_electricAmplitude_eq_zero_or_angularFrequency_tangentialProjection_eq_incident
    (h : configuration.IsElectricBoundary 0)
    (hAggregate : configuration.incidentExponentJointElectricAggregate ≠ 0) :
    configuration.reflected.electricAmplitude = 0 ∨
      (configuration.reflected.angularFrequency = configuration.incident.angularFrequency ∧
        ComplexWaveVector.hyperplaneTangentialProjection configuration.interface.plane
            configuration.reflected.waveVector =
          ComplexWaveVector.hyperplaneTangentialProjection configuration.interface.plane
            configuration.incident.waveVector) := by
  rcases h.reflected_electricAmplitude_eq_zero_or_angularFrequency_tangentPairing_eq_incident
      hAggregate with hzero | hConservation
  · exact Or.inl hzero
  · exact Or.inr ⟨hConservation.1,
      (ComplexWaveVector.hyperplaneTangentialProjection_eq_iff_bilinearDot_eq_on_tangent
        configuration.interface.plane configuration.reflected.waveVector
          configuration.incident.waveVector).mpr hConservation.2⟩

end IsElectricBoundary

namespace IsLocalBoundary

/-!

## D. Full local boundary wrappers

-/

variable {configuration : PlanarDielectricWaveConfiguration}
  {surfaceCurrent : PlanarFreeSurfaceCurrentDensity configuration.interface.plane}

/-- A full zero-free-charge local boundary with a nonzero incident-key aggregate forces the
transmitted electric amplitude to be nonzero. -/
lemma transmitted_electricAmplitude_ne_zero
    (h : configuration.IsLocalBoundary 0 surfaceCurrent)
    (hAggregate : configuration.incidentExponentJointElectricAggregate ≠ 0) :
    configuration.transmitted.electricAmplitude ≠ 0 :=
  h.isElectricBoundary.transmitted_electricAmplitude_ne_zero hAggregate

/-- A full zero-free-charge local boundary inherits transmitted frequency and tangent-pairing
conservation from its electric projection. -/
lemma transmitted_angularFrequency_tangentPairing_eq_incident
    (h : configuration.IsLocalBoundary 0 surfaceCurrent)
    (hAggregate : configuration.incidentExponentJointElectricAggregate ≠ 0) :
    configuration.transmitted.angularFrequency = configuration.incident.angularFrequency ∧
      ∀ v : configuration.interface.plane.tangentSubmodule,
        ComplexWaveVector.bilinearDot configuration.transmitted.waveVector
            (ComplexWaveVector.ofReal (v : EuclideanSpace ℝ (Fin 3))) =
          ComplexWaveVector.bilinearDot configuration.incident.waveVector
            (ComplexWaveVector.ofReal (v : EuclideanSpace ℝ (Fin 3))) :=
  h.isElectricBoundary.transmitted_angularFrequency_tangentPairing_eq_incident hAggregate

/-- A full zero-free-charge local boundary inherits transmitted frequency and tangential-projection
conservation from its electric projection. -/
lemma transmitted_angularFrequency_tangentialProjection_eq_incident
    (h : configuration.IsLocalBoundary 0 surfaceCurrent)
    (hAggregate : configuration.incidentExponentJointElectricAggregate ≠ 0) :
    configuration.transmitted.angularFrequency = configuration.incident.angularFrequency ∧
      ComplexWaveVector.hyperplaneTangentialProjection configuration.interface.plane
          configuration.transmitted.waveVector =
        ComplexWaveVector.hyperplaneTangentialProjection configuration.interface.plane
          configuration.incident.waveVector :=
  h.isElectricBoundary.transmitted_angularFrequency_tangentialProjection_eq_incident hAggregate

/-- A full zero-free-charge local boundary inherits the reflected zero-or-tangent-pairing
conservation alternative from its electric projection. -/
lemma reflected_electricAmplitude_eq_zero_or_angularFrequency_tangentPairing_eq_incident
    (h : configuration.IsLocalBoundary 0 surfaceCurrent)
    (hAggregate : configuration.incidentExponentJointElectricAggregate ≠ 0) :
    configuration.reflected.electricAmplitude = 0 ∨
      (configuration.reflected.angularFrequency = configuration.incident.angularFrequency ∧
        ∀ v : configuration.interface.plane.tangentSubmodule,
          ComplexWaveVector.bilinearDot configuration.reflected.waveVector
              (ComplexWaveVector.ofReal (v : EuclideanSpace ℝ (Fin 3))) =
            ComplexWaveVector.bilinearDot configuration.incident.waveVector
              (ComplexWaveVector.ofReal (v : EuclideanSpace ℝ (Fin 3)))) := by
  let hE := h.isElectricBoundary
  exact hE.reflected_electricAmplitude_eq_zero_or_angularFrequency_tangentPairing_eq_incident
    hAggregate

/-- A full zero-free-charge local boundary inherits the reflected zero-or-tangential-projection
conservation alternative from its electric projection. -/
lemma reflected_electricAmplitude_eq_zero_or_angularFrequency_tangentialProjection_eq_incident
    (h : configuration.IsLocalBoundary 0 surfaceCurrent)
    (hAggregate : configuration.incidentExponentJointElectricAggregate ≠ 0) :
    configuration.reflected.electricAmplitude = 0 ∨
      (configuration.reflected.angularFrequency = configuration.incident.angularFrequency ∧
        ComplexWaveVector.hyperplaneTangentialProjection configuration.interface.plane
            configuration.reflected.waveVector =
          ComplexWaveVector.hyperplaneTangentialProjection configuration.interface.plane
            configuration.incident.waveVector) := by
  let hE := h.isElectricBoundary
  exact hE.reflected_electricAmplitude_eq_zero_or_angularFrequency_tangentialProjection_eq_incident
    hAggregate

end IsLocalBoundary
end PlanarDielectricWaveConfiguration

end
end Optics
