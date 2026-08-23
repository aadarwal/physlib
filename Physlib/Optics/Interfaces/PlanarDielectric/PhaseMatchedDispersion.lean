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
positive-side medium and its difference from the incident squared normal component. When the
incident tangential attenuation vanishes, this equation becomes an explicitly real radicand built
from the positive-side material data, incident frequency, and squared norm of the incident
tangential phase vector. This hypothesis does not require the incident normal attenuation to
vanish. For an active reflected wave, equal frequency, equal tangential projection, and the common
negative-side material shell leave only two possibly coincident algebraic alternatives: the
incident vector itself or its hyperplane reflection. Strict incident phase direction into the
positive side and strict active reflected phase direction into the negative side exclude the
same-vector root.

The reflected branch result selects an algebraic root only under those explicit phase-direction
hypotheses; it neither derives them from a trace label nor identifies phase direction with group
velocity, energy flux, or outgoing power. These results do not select a transmitted square root,
define a propagation angle, prove Snell's law, or classify an evanescent branch. In particular,
the phase-matching predicate is used without its separate electric amplitude-balance predicate.

## ii. Key results

- `transmitted_hyperplaneNormalComponent_sq`: the transmitted normal-root equation in incident
  tangential and frequency data.
- `transmitted_tangentialPhase_attenuation_eq_incident`: complex phase matching decoded into its
  real tangential phase and attenuation equalities.
- `transmittedNormalRadicand`: the real candidate radicand formed from incident tangential phase
  data and the positive-side medium.
- `transmitted_hyperplaneNormalComponent_sq_eq_transmittedNormalRadicand`: zero incident
  tangential attenuation makes the transmitted normal square equal that embedded real radicand.
- `transmitted_hyperplaneNormalComponent_sq_sub_incident_hyperplaneNormalComponent_sq`:
  the exact two-medium contrast of squared normal components.
- `reflected_electricAmplitude_eq_zero_or_waveVector_eq_or_eq_hyperplaneReflection`: the
  zero-amplitude or two-root reflected alternative.
- `reflected_electricAmplitude_eq_zero_or_waveVector_eq_hyperplaneReflection_of_phaseDirections`:
  strict opposite-side phase directions select the reflected root for an active candidate.

## iii. Table of contents

- A. Transmitted normal-root and real-radicand equations
- B. Reflected two-root classification and phase-directed selection

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

/-!

## A. Transmitted normal-root and real-radicand equations

-/

/-- The real candidate for the squared transmitted normal component when the incident complex
tangential projection has zero attenuation.

This expression alone has no propagation, critical-angle, evanescence, transmitted-root,
side-decay, outgoing, or power meaning. -/
def transmittedNormalRadicand (configuration : PlanarDielectricWaveConfiguration) : ℝ :=
  configuration.interface.positiveMedium.ε *
      configuration.interface.positiveMedium.μ *
      configuration.incident.angularFrequency ^ 2 -
    ‖configuration.interface.plane.tangentialProjection
      configuration.incident.waveVector.phaseVector‖ ^ 2

namespace IsElectricPhaseMatched

variable {configuration : PlanarDielectricWaveConfiguration}

/-- Electric phase matching preserves the real tangential phase and attenuation projections from
the incident wave to the transmitted wave.

These equalities constrain no normal component and assign no propagation role. -/
lemma transmitted_tangentialPhase_attenuation_eq_incident
    (h : configuration.IsElectricPhaseMatched) :
    configuration.interface.plane.tangentialProjection
          configuration.transmitted.waveVector.phaseVector =
        configuration.interface.plane.tangentialProjection
          configuration.incident.waveVector.phaseVector ∧
      configuration.interface.plane.tangentialProjection
          configuration.transmitted.waveVector.attenuationVector =
        configuration.interface.plane.tangentialProjection
          configuration.incident.waveVector.attenuationVector := by
  constructor
  · simpa only [phaseVector_hyperplaneTangentialProjection] using
      congrArg ComplexWaveVector.phaseVector h.1.2
  · simpa only [attenuationVector_hyperplaneTangentialProjection] using
      congrArg ComplexWaveVector.attenuationVector h.1.2

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

/-- If the incident attenuation has zero tangential projection, the squared transmitted normal
component equals the explicitly real transmitted radicand.

The premise does not require zero incident normal attenuation. This result selects no root and
assigns no propagation, critical-angle, evanescence, side-decay, outgoing, or power meaning. -/
lemma transmitted_hyperplaneNormalComponent_sq_eq_transmittedNormalRadicand
    (h : configuration.IsElectricPhaseMatched)
    (hTransmittedDispersion : configuration.transmitted.IsDispersionMatched
      configuration.interface.positiveMedium)
    (hIncidentTangentialAttenuation :
      configuration.interface.plane.tangentialProjection
        configuration.incident.waveVector.attenuationVector = 0) :
    ComplexWaveVector.hyperplaneNormalComponent configuration.interface.plane
          configuration.transmitted.waveVector ^ 2 =
      (configuration.transmittedNormalRadicand : ℂ) := by
  rw [h.transmitted_hyperplaneNormalComponent_sq hTransmittedDispersion]
  have hProjection :
      ComplexWaveVector.hyperplaneTangentialProjection configuration.interface.plane
          configuration.incident.waveVector =
        ComplexWaveVector.ofReal
          (configuration.interface.plane.tangentialProjection
            configuration.incident.waveVector.phaseVector) :=
    hyperplaneTangentialProjection_eq_ofReal_of_tangentialProjection_attenuationVector_eq_zero
      configuration.interface.plane configuration.incident.waveVector
        hIncidentTangentialAttenuation
  rw [hProjection, ComplexWaveVector.bilinearDot_ofReal,
    real_inner_self_eq_norm_sq, transmittedNormalRadicand]
  push_cast
  ring

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

## B. Reflected two-root classification and phase-directed selection

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

/-- Strict incident and active reflected phase directions into opposite geometric sides exclude
the same-vector reflected root.

The incident phase vector is required to point into the positive side, and the active reflected
phase vector into the negative side. The reflected direction and dispersion hypotheses remain
conditional so a zero-amplitude candidate retains arbitrary dummy labels. This selects only the
algebraic hyperplane-reflection branch; it does not derive either phase direction from the trace
labels or identify phase direction with group velocity, energy flux, or outgoing power. -/
lemma reflected_electricAmplitude_eq_zero_or_waveVector_eq_hyperplaneReflection_of_phaseDirections
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
      configuration.reflected.waveVector =
        ComplexWaveVector.hyperplaneReflection configuration.interface.plane
          configuration.incident.waveVector := by
  by_cases hReflectedZero : configuration.reflected.electricAmplitude = 0
  · exact Or.inl hReflectedZero
  · right
    rcases
        h.reflected_electricAmplitude_eq_zero_or_waveVector_eq_or_eq_hyperplaneReflection
          hIncidentDispersion hReflectedDispersion with hZero | hSame | hReflection
    · exact (hReflectedZero hZero).elim
    · have hIncidentNormal :=
        (isPhaseDirectedInto_positive_iff _ _).mp hIncidentPhase
      have hReflectedNormal :=
        (isPhaseDirectedInto_negative_iff _ _).mp
          (hReflectedPhase hReflectedZero)
      rw [hSame] at hReflectedNormal
      exact (not_lt_of_ge hIncidentNormal.le hReflectedNormal).elim
    · exact hReflection

end IsElectricPhaseMatched
end PlanarDielectricWaveConfiguration

end
end Optics
