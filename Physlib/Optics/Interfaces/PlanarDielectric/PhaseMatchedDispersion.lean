/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Electromagnetism.ThreeDimension.MonochromaticPlaneWave.ComplexDispersion
public import Physlib.Optics.Interfaces.PlanarDielectric.ElectricFixedFrequency

/-!
# Phase-matched dispersion at a planar dielectric interface

## i. Overview

This file combines the reduced electric phase-matching predicate with independently supplied
complex material-dispersion hypotheses. Phase matching identifies the transmitted frequency and
complex tangential wave-vector projection with the incident data. It identifies the reflected
data only when the reflected electric amplitude is nonzero; the zero-amplitude candidate retains
arbitrary dummy labels.

For transmission, material matching gives the exact squared complex normal component in the
positive-side medium and its difference from the incident squared normal component. For an active
reflected wave, equal frequency, equal tangential projection, and the common negative-side material
shell leave only two possibly coincident algebraic alternatives: the incident vector itself or its
hyperplane reflection. The same-vector root cannot be excluded without a side or outgoing
condition.

These results do not select a square root, define a propagation angle, prove Snell's law, classify
an evanescent branch, or assign energy flux or power. In particular, the phase-matching predicate
is used without its separate electric amplitude-balance predicate.

## ii. Key results

- `transmitted_hyperplaneNormalComponent_sq`: the transmitted normal-root equation in incident
  tangential and frequency data.
- `transmitted_hyperplaneNormalComponent_sq_sub_incident_hyperplaneNormalComponent_sq`:
  the exact two-medium contrast of squared normal components.
- `reflected_electricAmplitude_eq_zero_or_waveVector_eq_or_eq_hyperplaneReflection`: the
  zero-amplitude or two-root reflected alternative.

## iii. Table of contents

- A. Transmitted normal-root equations
- B. Reflected two-root classification

## iv. References

This module combines Physlib's independently implemented complex material shell, neutral
hyperplane reflection, and reduced electric phase-matching APIs. No external formal-development
source is copied or translated here.
-/

@[expose] public section

namespace Optics

open ClassicalMechanics Electromagnetism Electromagnetism.ThreeDimension
open ClassicalMechanics.ComplexWaveVector
open Electromagnetism.ThreeDimension.ComplexMonochromaticPlaneWave

noncomputable section

namespace PlanarDielectricWaveConfiguration
namespace IsElectricPhaseMatched

variable {configuration : PlanarDielectricWaveConfiguration}

/-!

## A. Transmitted normal-root equations

-/

/-- Phase matching and positive-medium material dispersion express the squared transmitted complex
normal component using the incident frequency and complex tangential projection. -/
lemma transmitted_hyperplaneNormalComponent_sq
    (h : configuration.IsElectricPhaseMatched)
    (hTransmittedDispersion : configuration.transmitted.IsDispersionMatched
      configuration.interface.positiveMedium) :
    ComplexWaveVector.hyperplaneNormalComponent configuration.interface.plane
          configuration.transmitted.waveVector ^ 2 =
      ((configuration.interface.positiveMedium.ε *
          configuration.interface.positiveMedium.μ *
          configuration.incident.angularFrequency ^ 2 : ℝ) : ℂ) -
        ComplexWaveVector.bilinearDot
          (ComplexWaveVector.hyperplaneTangentialProjection configuration.interface.plane
            configuration.incident.waveVector)
          (ComplexWaveVector.hyperplaneTangentialProjection configuration.interface.plane
            configuration.incident.waveVector) := by
  simpa only [h.1.1, h.1.2] using
    hTransmittedDispersion.hyperplaneNormalComponent_sq configuration.interface.plane

/-- Under phase matching and material dispersion on both sides, the transmitted-minus-incident
squared complex normal components equal the material contrast times the common frequency square. -/
lemma transmitted_hyperplaneNormalComponent_sq_sub_incident_hyperplaneNormalComponent_sq
    (h : configuration.IsElectricPhaseMatched)
    (hIncidentDispersion : configuration.incident.IsDispersionMatched
      configuration.interface.negativeMedium)
    (hTransmittedDispersion : configuration.transmitted.IsDispersionMatched
      configuration.interface.positiveMedium) :
    ComplexWaveVector.hyperplaneNormalComponent configuration.interface.plane
            configuration.transmitted.waveVector ^ 2 -
        ComplexWaveVector.hyperplaneNormalComponent configuration.interface.plane
          configuration.incident.waveVector ^ 2 =
      (((configuration.interface.positiveMedium.ε *
            configuration.interface.positiveMedium.μ -
          configuration.interface.negativeMedium.ε *
            configuration.interface.negativeMedium.μ) *
          configuration.incident.angularFrequency ^ 2 : ℝ) : ℂ) := by
  rw [hTransmittedDispersion.hyperplaneNormalComponent_sq configuration.interface.plane,
    hIncidentDispersion.hyperplaneNormalComponent_sq configuration.interface.plane,
    h.1.1, h.1.2]
  push_cast
  ring

/-!

## B. Reflected two-root classification

-/

/-- A phase-matched reflected candidate either has zero electric amplitude, keeps the incident wave
vector, or has its hyperplane reflection.

The reflected dispersion premise is conditional so a zero-amplitude candidate retains arbitrary
dummy labels. The same-vector root remains possible until a side or outgoing condition excludes
it. -/
lemma reflected_electricAmplitude_eq_zero_or_waveVector_eq_or_eq_hyperplaneReflection
    (h : configuration.IsElectricPhaseMatched)
    (hIncidentDispersion : configuration.incident.IsDispersionMatched
      configuration.interface.negativeMedium)
    (hReflectedDispersion : configuration.reflected.electricAmplitude ≠ 0 →
      configuration.reflected.IsDispersionMatched configuration.interface.negativeMedium) :
    configuration.reflected.electricAmplitude = 0 ∨
      configuration.reflected.waveVector = configuration.incident.waveVector ∨
        configuration.reflected.waveVector =
          ComplexWaveVector.hyperplaneReflection configuration.interface.plane
            configuration.incident.waveVector := by
  by_cases hReflectedZero : configuration.reflected.electricAmplitude = 0
  · exact Or.inl hReflectedZero
  · right
    have hReflectedMatched := h.2.resolve_left hReflectedZero
    apply
      eq_or_eq_hyperplaneReflection_of_tangentialProjection_eq_of_bilinearDot_self_eq
    · exact hReflectedMatched.2
    · rw [hReflectedDispersion hReflectedZero, hIncidentDispersion, hReflectedMatched.1]

end IsElectricPhaseMatched
end PlanarDielectricWaveConfiguration

end
end Optics
