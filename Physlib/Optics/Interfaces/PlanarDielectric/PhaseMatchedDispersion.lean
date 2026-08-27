/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.ClassicalMechanics.WaveEquation.ComplexWaveVector.NormalRoot
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

The transmitted branch results likewise select a normal root only under a separately supplied
strict phase or attenuation direction into the positive side. At zero radicand the normal root is
unique and no strict direction premise is needed. The attenuation-directed root gives the exact
positive-side exponential factor for the complete transmitted carrier and its ordinary real
electric and magnetic-induction fields. These are global field identities based at an arbitrary
point, not one-sided support conditions. None of these results derives a direction from a trace
label, identifies phase direction with group velocity or power flow, defines a propagation angle,
or proves Snell's law. Unguarded convention statement (review only): they classify no evanescent or
outgoing branch or its power. In particular, the phase-matching predicate is used without its
separate electric amplitude-balance predicate.

## ii. Key results

- `transmitted_hyperplaneNormalComponent_sq`: the transmitted normal-root equation in incident
  tangential and frequency data.
- `transmitted_tangentialPhase_attenuation_eq_incident`: complex phase matching decoded into its
  real tangential phase and attenuation equalities.
- `transmittedNormalRadicand`: the real candidate radicand formed from incident tangential phase
  data and the positive-side medium.
- `hyperplaneNormalComponent_sq_eq_transmittedNormalRadicand_of_tangentialProjection_eq`: the
  branch-neutral vector and material-shell reduction to that radicand.
- `transmitted_hyperplaneNormalComponent_sq_eq_transmittedNormalRadicand`: zero incident
  tangential attenuation makes the transmitted normal square equal that embedded real radicand.
- `transmitted_normalRoot_data_of_isPhaseDirectedInto`: positive-side phase direction selects the
  positive real normal root and forces zero transmitted attenuation.
- `transmitted_normalRoot_data_of_transmittedNormalRadicand_eq_zero`: a zero transmitted radicand
  forces the unique zero normal root and zero transmitted attenuation.
- `transmitted_normalRoot_data_of_isAttenuationDirectedInto`: positive-side attenuation direction
  selects the negative-imaginary normal root.
- `transmitted_electricField_vadd_normalVector_of_isAttenuationDirectedInto`: the selected root
  gives the transmitted electric field its exact positive-side exponential scaling.
- `transmitted_hyperplaneNormalComponent_sq_sub_incident_hyperplaneNormalComponent_sq`:
  the exact two-medium contrast of squared normal components.
- `reflected_electricAmplitude_eq_zero_or_waveVector_eq_or_eq_hyperplaneReflection`: the
  zero-amplitude or two-root reflected alternative.
- `reflected_electricAmplitude_eq_zero_or_waveVector_eq_hyperplaneReflection_of_phaseDirections`:
  strict opposite-side phase directions select the reflected root for an active candidate.

## iii. Table of contents

- A. Transmitted normal-root and real-radicand equations
- B. Direction-selected transmitted normal roots
- C. Reflected two-root classification and phase-directed selection

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

Unguarded convention statement (review only): this expression alone has no propagation,
critical-angle, evanescence, transmitted-root, side-decay, outgoing, or power meaning. -/
def transmittedNormalRadicand (configuration : PlanarDielectricWaveConfiguration) : ℝ :=
  configuration.interface.positiveMedium.ε *
      configuration.interface.positiveMedium.μ *
      configuration.incident.angularFrequency ^ 2 -
    ‖configuration.interface.plane.tangentialProjection
      configuration.incident.waveVector.phaseVector‖ ^ 2

/-- A complex wave vector with the incident tangential projection and the positive-medium shell
has normal square equal to the transmitted normal radicand whenever the incident tangential
attenuation vanishes.

This vector-level reduction selects no normal root or phase/attenuation direction. -/
lemma hyperplaneNormalComponent_sq_eq_transmittedNormalRadicand_of_tangentialProjection_eq
    (configuration : PlanarDielectricWaveConfiguration) (waveVector : ComplexWaveVector 3)
    (hTangential :
      hyperplaneTangentialProjection configuration.interface.plane waveVector =
        hyperplaneTangentialProjection configuration.interface.plane
          configuration.incident.waveVector)
    (hShell : bilinearDot waveVector waveVector =
      ((configuration.interface.positiveMedium.ε *
        configuration.interface.positiveMedium.μ *
        configuration.incident.angularFrequency ^ 2 : ℝ) : ℂ))
    (hIncidentTangentialAttenuation :
      configuration.interface.plane.tangentialProjection
        configuration.incident.waveVector.attenuationVector = 0) :
    hyperplaneNormalComponent configuration.interface.plane waveVector ^ 2 =
      (configuration.transmittedNormalRadicand : ℂ) := by
  have hIncidentProjection :=
    hyperplaneTangentialProjection_eq_ofReal_of_tangentialProjection_attenuationVector_eq_zero
      configuration.interface.plane configuration.incident.waveVector
        hIncidentTangentialAttenuation
  calc
    hyperplaneNormalComponent configuration.interface.plane waveVector ^ 2 =
        ((configuration.interface.positiveMedium.ε *
          configuration.interface.positiveMedium.μ *
          configuration.incident.angularFrequency ^ 2 : ℝ) : ℂ) -
          bilinearDot
            (hyperplaneTangentialProjection configuration.interface.plane waveVector)
            (hyperplaneTangentialProjection configuration.interface.plane waveVector) := by
      rw [← hShell, bilinearDot_self_eq_tangential_add_normal_sq]
      ring
    _ = ((configuration.interface.positiveMedium.ε *
          configuration.interface.positiveMedium.μ *
          configuration.incident.angularFrequency ^ 2 : ℝ) : ℂ) -
          bilinearDot
            (hyperplaneTangentialProjection configuration.interface.plane
              configuration.incident.waveVector)
            (hyperplaneTangentialProjection configuration.interface.plane
              configuration.incident.waveVector) := by
      rw [hTangential]
    _ = (configuration.transmittedNormalRadicand : ℂ) := by
      rw [hIncidentProjection, bilinearDot_ofReal, real_inner_self_eq_norm_sq,
        transmittedNormalRadicand]
      push_cast
      ring

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

The premise does not require zero incident normal attenuation. Unguarded convention statement
(review only): this result selects no root and assigns no propagation, critical-angle,
evanescence, side-decay, outgoing, or power meaning. -/
lemma transmitted_hyperplaneNormalComponent_sq_eq_transmittedNormalRadicand
    (h : configuration.IsElectricPhaseMatched)
    (hTransmittedDispersion : configuration.transmitted.IsDispersionMatched
      configuration.interface.positiveMedium)
    (hIncidentTangentialAttenuation :
      configuration.interface.plane.tangentialProjection
        configuration.incident.waveVector.attenuationVector = 0) :
    ComplexWaveVector.hyperplaneNormalComponent configuration.interface.plane
          configuration.transmitted.waveVector ^ 2 =
      (configuration.transmittedNormalRadicand : ℂ) :=
  configuration.hyperplaneNormalComponent_sq_eq_transmittedNormalRadicand_of_tangentialProjection_eq
    configuration.transmitted.waveVector h.1.2
      (by simpa only [IsDispersionMatched, h.1.1] using hTransmittedDispersion)
        hIncidentTangentialAttenuation

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

## B. Direction-selected transmitted normal roots

-/

/-- Under electric phase matching, zero incident tangential attenuation gives zero transmitted
tangential attenuation.

This statement constrains no normal attenuation component. -/
lemma transmitted_tangentialProjection_attenuationVector_eq_zero
    (h : configuration.IsElectricPhaseMatched)
    (hIncidentTangentialAttenuation :
      configuration.interface.plane.tangentialProjection
        configuration.incident.waveVector.attenuationVector = 0) :
    configuration.interface.plane.tangentialProjection
      configuration.transmitted.waveVector.attenuationVector = 0 :=
  h.transmitted_tangentialPhase_attenuation_eq_incident.2.trans
    hIncidentTangentialAttenuation

/-- If the transmitted phase vector points strictly into the geometric positive side, its real
normal radicand is positive, its whole attenuation vector vanishes, and its normal component is
the positive real square root.

Unguarded convention statement (review only): the direction premise is supplied rather than
derived from the transmitted label, and this algebraic phase-root selection is not a
group-velocity, outgoing, irradiance, or power statement. -/
lemma transmitted_normalRoot_data_of_isPhaseDirectedInto
    (h : configuration.IsElectricPhaseMatched)
    (hTransmittedDispersion : configuration.transmitted.IsDispersionMatched
      configuration.interface.positiveMedium)
    (hIncidentTangentialAttenuation :
      configuration.interface.plane.tangentialProjection
        configuration.incident.waveVector.attenuationVector = 0)
    (hDirection : configuration.transmitted.waveVector.IsPhaseDirectedInto
      configuration.interface.plane .positive) :
    0 < configuration.transmittedNormalRadicand ∧
      configuration.transmitted.waveVector.attenuationVector = 0 ∧
      ComplexWaveVector.hyperplaneNormalComponent configuration.interface.plane
          configuration.transmitted.waveVector =
        (Real.sqrt configuration.transmittedNormalRadicand : ℂ) := by
  have hSquare := h.transmitted_hyperplaneNormalComponent_sq_eq_transmittedNormalRadicand
    hTransmittedDispersion hIncidentTangentialAttenuation
  obtain ⟨hRadicand, hNormalAttenuation, hRoot⟩ :=
    normalRoot_data_of_sq_eq_real_of_isPhaseDirectedInto
      configuration.interface.plane configuration.transmitted.waveVector
        configuration.transmittedNormalRadicand .positive hSquare hDirection
  refine ⟨hRadicand, ?_, ?_⟩
  · calc
      configuration.transmitted.waveVector.attenuationVector =
          configuration.interface.plane.tangentialProjection
              configuration.transmitted.waveVector.attenuationVector +
            configuration.interface.plane.normalComponent
                configuration.transmitted.waveVector.attenuationVector •
              configuration.interface.plane.normalVector :=
        (configuration.interface.plane.tangentialProjection_add_normal _).symm
      _ = 0 := by
        rw [h.transmitted_tangentialProjection_attenuationVector_eq_zero
          hIncidentTangentialAttenuation, hNormalAttenuation]
        simp
  · simpa using hRoot

/-- If the transmitted real normal radicand is zero, the normal root is uniquely zero. Under the
same zero-tangential-attenuation premise, the transmitted attenuation vector also vanishes and
the transmitted phase vector has zero normal component.

This is an algebraic threshold result. Unguarded convention statement (review only): it does not
by itself define a critical angle, a grazing role, an outgoing condition, irradiance, or power. -/
lemma transmitted_normalRoot_data_of_transmittedNormalRadicand_eq_zero
    (h : configuration.IsElectricPhaseMatched)
    (hTransmittedDispersion : configuration.transmitted.IsDispersionMatched
      configuration.interface.positiveMedium)
    (hIncidentTangentialAttenuation :
      configuration.interface.plane.tangentialProjection
        configuration.incident.waveVector.attenuationVector = 0)
    (hRadicand : configuration.transmittedNormalRadicand = 0) :
    configuration.interface.plane.normalComponent
          configuration.transmitted.waveVector.phaseVector = 0 ∧
      configuration.transmitted.waveVector.attenuationVector = 0 ∧
      ComplexWaveVector.hyperplaneNormalComponent configuration.interface.plane
          configuration.transmitted.waveVector = 0 := by
  have hSquare := h.transmitted_hyperplaneNormalComponent_sq_eq_transmittedNormalRadicand
    hTransmittedDispersion hIncidentTangentialAttenuation
  have hRoot :
      ComplexWaveVector.hyperplaneNormalComponent configuration.interface.plane
          configuration.transmitted.waveVector = 0 :=
    normalComponent_eq_zero_of_sq_eq_zero configuration.interface.plane
      configuration.transmitted.waveVector (by simpa [hRadicand] using hSquare)
  have hPhaseNormal :
      configuration.interface.plane.normalComponent
          configuration.transmitted.waveVector.phaseVector = 0 := by
    simpa using congrArg Complex.re hRoot
  have hAttenuationNormal :
      configuration.interface.plane.normalComponent
          configuration.transmitted.waveVector.attenuationVector = 0 := by
    simpa using congrArg Complex.im hRoot
  refine ⟨hPhaseNormal, ?_, hRoot⟩
  calc
    configuration.transmitted.waveVector.attenuationVector =
        configuration.interface.plane.tangentialProjection
            configuration.transmitted.waveVector.attenuationVector +
          configuration.interface.plane.normalComponent
              configuration.transmitted.waveVector.attenuationVector •
            configuration.interface.plane.normalVector :=
      (configuration.interface.plane.tangentialProjection_add_normal _).symm
    _ = 0 := by
      rw [h.transmitted_tangentialProjection_attenuationVector_eq_zero
        hIncidentTangentialAttenuation, hAttenuationNormal]
      simp

/-- If the transmitted attenuation vector points strictly into the geometric positive side, its
real normal radicand is negative, its phase normal component vanishes, and its complex normal
component is the negative-imaginary square root.

For `K = q - I a`, this is the root whose normal attenuation points into the positive side. The
direction premise is supplied rather than derived from the transmitted label. Unguarded convention
statement (review only): the result does not yet assert spatial decay, evanescence, an outgoing
condition, irradiance, or power. -/
lemma transmitted_normalRoot_data_of_isAttenuationDirectedInto
    (h : configuration.IsElectricPhaseMatched)
    (hTransmittedDispersion : configuration.transmitted.IsDispersionMatched
      configuration.interface.positiveMedium)
    (hIncidentTangentialAttenuation :
      configuration.interface.plane.tangentialProjection
        configuration.incident.waveVector.attenuationVector = 0)
    (hDirection : configuration.transmitted.waveVector.IsAttenuationDirectedInto
      configuration.interface.plane .positive) :
    configuration.transmittedNormalRadicand < 0 ∧
      configuration.interface.plane.normalComponent
          configuration.transmitted.waveVector.phaseVector = 0 ∧
      ComplexWaveVector.hyperplaneNormalComponent configuration.interface.plane
          configuration.transmitted.waveVector =
        -Complex.I *
          (Real.sqrt (-configuration.transmittedNormalRadicand) : ℂ) := by
  have hSquare := h.transmitted_hyperplaneNormalComponent_sq_eq_transmittedNormalRadicand
    hTransmittedDispersion hIncidentTangentialAttenuation
  simpa using normalRoot_data_of_sq_eq_real_of_isAttenuationDirectedInto
    configuration.interface.plane configuration.transmitted.waveVector
      configuration.transmittedNormalRadicand .positive hSquare hDirection

/-- The attenuation-directed transmitted root gives the complete carrier its exact
positive-side exponential scaling at the square-root rate.

The base point is arbitrary, the carrier remains globally defined, and negative displacement gives
the inverse growth direction. Unguarded convention statement (review only): this result is neither
a half-space-support condition nor an outgoing, total-internal-reflection, irradiance, or power
statement. -/
lemma transmitted_carrier_vadd_normalVector_of_isAttenuationDirectedInto
    (h : configuration.IsElectricPhaseMatched)
    (hTransmittedDispersion : configuration.transmitted.IsDispersionMatched
      configuration.interface.positiveMedium)
    (hIncidentTangentialAttenuation :
      configuration.interface.plane.tangentialProjection
        configuration.incident.waveVector.attenuationVector = 0)
    (hDirection : configuration.transmitted.waveVector.IsAttenuationDirectedInto
      configuration.interface.plane .positive) (u : ℝ) (t : Time) (x : Space) :
    configuration.transmitted.carrier t
        (u • configuration.interface.plane.normalVector +ᵥ x) =
      (Real.exp
          (-Real.sqrt (-configuration.transmittedNormalRadicand) * u) : ℂ) *
        configuration.transmitted.carrier t x := by
  have hNormal :=
    (h.transmitted_normalRoot_data_of_isAttenuationDirectedInto
      hTransmittedDispersion hIncidentTangentialAttenuation hDirection).2.2
  exact carrier_vadd_normalVector_of_hyperplaneNormalComponent_eq_neg_I_mul
    configuration.transmitted configuration.interface.plane
      (Real.sqrt (-configuration.transmittedNormalRadicand)) hNormal u t x

/-- The attenuation-directed transmitted root gives the ordinary electric field exact
positive-side exponential scaling at the square-root rate. -/
lemma transmitted_electricField_vadd_normalVector_of_isAttenuationDirectedInto
    (h : configuration.IsElectricPhaseMatched)
    (hTransmittedDispersion : configuration.transmitted.IsDispersionMatched
      configuration.interface.positiveMedium)
    (hIncidentTangentialAttenuation :
      configuration.interface.plane.tangentialProjection
        configuration.incident.waveVector.attenuationVector = 0)
    (hDirection : configuration.transmitted.waveVector.IsAttenuationDirectedInto
      configuration.interface.plane .positive) (u : ℝ) (t : Time) (x : Space) :
    configuration.transmitted.electricField t
        (u • configuration.interface.plane.normalVector +ᵥ x) =
      Real.exp (-Real.sqrt (-configuration.transmittedNormalRadicand) * u) •
        configuration.transmitted.electricField t x := by
  have hNormal :=
    (h.transmitted_normalRoot_data_of_isAttenuationDirectedInto
      hTransmittedDispersion hIncidentTangentialAttenuation hDirection).2.2
  exact electricField_vadd_normalVector_of_hyperplaneNormalComponent_eq_neg_I_mul
    configuration.transmitted configuration.interface.plane
      (Real.sqrt (-configuration.transmittedNormalRadicand)) hNormal u t x

/-- The attenuation-directed transmitted root gives the ordinary magnetic induction exact
positive-side exponential scaling at the square-root rate. -/
lemma transmitted_magneticInduction_vadd_normalVector_of_isAttenuationDirectedInto
    (h : configuration.IsElectricPhaseMatched)
    (hTransmittedDispersion : configuration.transmitted.IsDispersionMatched
      configuration.interface.positiveMedium)
    (hIncidentTangentialAttenuation :
      configuration.interface.plane.tangentialProjection
        configuration.incident.waveVector.attenuationVector = 0)
    (hDirection : configuration.transmitted.waveVector.IsAttenuationDirectedInto
      configuration.interface.plane .positive) (u : ℝ) (t : Time) (x : Space) :
    configuration.transmitted.magneticInduction t
        (u • configuration.interface.plane.normalVector +ᵥ x) =
      Real.exp (-Real.sqrt (-configuration.transmittedNormalRadicand) * u) •
        configuration.transmitted.magneticInduction t x := by
  have hNormal :=
    (h.transmitted_normalRoot_data_of_isAttenuationDirectedInto
      hTransmittedDispersion hIncidentTangentialAttenuation hDirection).2.2
  exact magneticInduction_vadd_normalVector_of_hyperplaneNormalComponent_eq_neg_I_mul
    configuration.transmitted configuration.interface.plane
      (Real.sqrt (-configuration.transmittedNormalRadicand)) hNormal u t x

/-!

## C. Reflected two-root classification and phase-directed selection

-/

/-- A phase-matched reflected candidate either has zero electric amplitude, keeps the incident wave
vector, or has its hyperplane reflection.

The reflected dispersion premise is conditional so a zero-amplitude candidate retains arbitrary
dummy labels. Unguarded convention statement (review only): the same-vector root remains possible
until a separately supplied side or outgoing condition excludes it. -/
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
algebraic hyperplane-reflection branch. Unguarded convention statement (review only): it does not
derive either phase direction from the trace labels or identify phase direction with group
velocity, energy flux, or outgoing power. -/
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
