/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Interfaces.PlanarDielectric.SupercriticalTransmission

/-!
# Supercritical transmitted positive-normal-decay carriers

## i. Overview

This file lifts the canonical positive-normal-decay transmitted wave vector to a family of
monochromatic plane-wave carriers indexed by an arbitrary complex electric amplitude. Under
incident negative-medium dispersion, zero whole incident attenuation, and strict
sine-supercritical incidence, fixing that amplitude makes the carrier candidate unique.

When the transmitted normal radicand is negative, the complete complex carrier, ordinary electric
field, and ordinary magnetic induction all have the same exact exponential scaling under
displacement along the stored interface normal. The scaling is inherited from the shared complex
wave vector, so it requires no transversality or Maxwell hypothesis.

These objects are carrier candidates only. Their amplitude may vanish or fail transversality, and
the results do not impose an interface boundary-amplitude equation, one-sided support, Maxwell
equations, an outgoing radiation condition, total internal reflection, a Fresnel coefficient,
irradiance, or power flow.

## ii. Key results

- `positiveNormalDecayTransmittedCandidate`: the arbitrary-amplitude carrier family.
- `IsPositiveNormalDecayTransmittedCandidate`: the exact frequency and wave-vector
  specification.
- `existsUnique_isPositiveNormalDecayTransmittedCandidate_with_electricAmplitude`: uniqueness
  after fixing the otherwise free amplitude.
- `positiveNormalDecayTransmittedCandidate_carrier_vadd_normalVector`: exact exponential carrier
  scaling; the electric and magnetic field results use the same factor.
- `IsElectricPhaseMatched.transmitted_eq_positiveNormalDecayTransmittedCandidate`: identification
  of a supplied phase-matched and attenuation-directed transmitted carrier.

## iii. Table of contents

- A. Arbitrary-amplitude carrier family
- B. Fixed-amplitude existence and uniqueness
- C. Exact positive-normal scaling
- D. Supplied-candidate identification

## iv. References

The construction specializes Physlib's complex plane-wave carrier and positive-normal-decay
APIs. No external formal-development source is copied or translated here.
-/

@[expose] public section

namespace Optics

open ClassicalMechanics Electromagnetism Electromagnetism.ThreeDimension Space
open ClassicalMechanics.ComplexWaveVector
open Electromagnetism.ThreeDimension.ComplexMonochromaticPlaneWave

noncomputable section

namespace PlanarDielectricWaveConfiguration

/-!

## A. Arbitrary-amplitude carrier family

-/

/-- A plane-wave candidate carrying the canonical positive-normal-decay transmitted wave vector
at the incident frequency and an arbitrary supplied electric amplitude.

The amplitude is not determined by an interface boundary equation and may be zero or
nontransverse. -/
noncomputable def positiveNormalDecayTransmittedCandidate
    (configuration : PlanarDielectricWaveConfiguration)
    (electricAmplitude : EuclideanSpace ℂ (Fin 3)) : ComplexMonochromaticPlaneWave where
  angularFrequency := configuration.incident.angularFrequency
  angularFrequency_pos := configuration.incident.angularFrequency_pos
  waveVector := configuration.positiveNormalDecayTransmittedWaveVector
  electricAmplitude := electricAmplitude

/-- A plane-wave candidate has positive-normal-decay transmitted carrier data when its frequency
is the incident frequency and its wave vector satisfies the positive-normal-decay transmitted
specification. Its electric amplitude remains unconstrained. -/
def IsPositiveNormalDecayTransmittedCandidate
    (configuration : PlanarDielectricWaveConfiguration)
    (wave : ComplexMonochromaticPlaneWave) : Prop :=
  wave.angularFrequency = configuration.incident.angularFrequency ∧
    configuration.IsPositiveNormalDecayTransmittedWaveVector wave.waveVector

namespace IsPositiveNormalDecayTransmittedCandidate

variable {configuration : PlanarDielectricWaveConfiguration}
  {wave : ComplexMonochromaticPlaneWave}

/-- A positive-normal-decay candidate supplies the common transmitted frequency and complex
tangential wave-vector data, without constraining the reflected label. -/
lemma phaseMatchData (h : configuration.IsPositiveNormalDecayTransmittedCandidate wave) :
    wave.angularFrequency = configuration.incident.angularFrequency ∧
      hyperplaneTangentialProjection configuration.interface.plane wave.waveVector =
        hyperplaneTangentialProjection configuration.interface.plane
          configuration.incident.waveVector :=
  ⟨h.1, h.2.1⟩

/-- Every positive-normal-decay transmitted candidate is dispersion matched to the positive-side
medium. Its electric amplitude remains arbitrary, and this result supplies neither transversality
nor Maxwell satisfaction. -/
lemma isDispersionMatched (h : configuration.IsPositiveNormalDecayTransmittedCandidate wave) :
    wave.IsDispersionMatched configuration.interface.positiveMedium := by
  rw [IsDispersionMatched, h.1]
  exact h.2.2.1

/-- Every positive-normal-decay transmitted candidate is the canonical family member with its
own electric amplitude. -/
lemma eq_positiveNormalDecayTransmittedCandidate
    (h : configuration.IsPositiveNormalDecayTransmittedCandidate wave) :
    wave = configuration.positiveNormalDecayTransmittedCandidate wave.electricAmplitude := by
  rcases h with ⟨hFrequency, hWaveVector⟩
  have hVector := hWaveVector.eq_positiveNormalDecayTransmittedWaveVector
  cases wave with
  | mk angularFrequency angularFrequency_pos waveVector electricAmplitude =>
      dsimp at hFrequency hVector ⊢
      subst angularFrequency
      subst waveVector
      rfl

end IsPositiveNormalDecayTransmittedCandidate

/-!

## B. Fixed-amplitude existence and uniqueness

-/

/-- Zero incident tangential attenuation and a negative transmitted normal radicand make every
supplied electric amplitude a positive-normal-decay transmitted carrier candidate. -/
lemma positiveNormalDecayTransmittedCandidate_spec_of_radicand_neg
    (configuration : PlanarDielectricWaveConfiguration)
    (electricAmplitude : EuclideanSpace ℂ (Fin 3))
    (hIncidentTangentialAttenuation :
      configuration.interface.plane.tangentialProjection
        configuration.incident.waveVector.attenuationVector = 0)
    (hRadicand : configuration.transmittedNormalRadicand < 0) :
    configuration.IsPositiveNormalDecayTransmittedCandidate
      (configuration.positiveNormalDecayTransmittedCandidate electricAmplitude) := by
  exact ⟨rfl,
    positiveNormalDecayTransmittedWaveVector_spec_of_radicand_neg
      configuration hIncidentTangentialAttenuation hRadicand⟩

/-- Under incident negative-medium dispersion, zero whole incident attenuation, and strict
sine-supercritical incidence, every supplied electric amplitude gives a positive-normal-decay
transmitted carrier candidate. -/
lemma positiveNormalDecayTransmittedCandidate_spec
    (configuration : PlanarDielectricWaveConfiguration)
    (electricAmplitude : EuclideanSpace ℂ (Fin 3))
    (hIncidentDispersion : configuration.incident.IsDispersionMatched
      configuration.interface.negativeMedium)
    (hIncidentAttenuation : configuration.incident.waveVector.attenuationVector = 0)
    (hSupercritical : configuration.IsSupercriticalPhaseIncidence) :
    configuration.IsPositiveNormalDecayTransmittedCandidate
      (configuration.positiveNormalDecayTransmittedCandidate electricAmplitude) := by
  exact ⟨rfl,
    configuration.positiveNormalDecayTransmittedWaveVector_spec
      hIncidentDispersion hIncidentAttenuation hSupercritical⟩

/-- With zero incident tangential attenuation, a negative normal radicand gives a unique
positive-normal-decay carrier candidate after its electric amplitude is fixed. -/
lemma existsUnique_isPositiveNormalDecayTransmittedCandidate_with_electricAmplitude_of_radicand_neg
    (configuration : PlanarDielectricWaveConfiguration)
    (electricAmplitude : EuclideanSpace ℂ (Fin 3))
    (hIncidentTangentialAttenuation :
      configuration.interface.plane.tangentialProjection
        configuration.incident.waveVector.attenuationVector = 0)
    (hRadicand : configuration.transmittedNormalRadicand < 0) :
    ∃! wave,
      configuration.IsPositiveNormalDecayTransmittedCandidate wave ∧
        wave.electricAmplitude = electricAmplitude := by
  refine ⟨configuration.positiveNormalDecayTransmittedCandidate electricAmplitude,
    ⟨positiveNormalDecayTransmittedCandidate_spec_of_radicand_neg
      configuration electricAmplitude hIncidentTangentialAttenuation hRadicand, rfl⟩, ?_⟩
  intro wave hWave
  calc
    wave = configuration.positiveNormalDecayTransmittedCandidate wave.electricAmplitude :=
      hWave.1.eq_positiveNormalDecayTransmittedCandidate
    _ = configuration.positiveNormalDecayTransmittedCandidate electricAmplitude := by rw [hWave.2]

/-- Under incident negative-medium dispersion, zero whole incident attenuation, and strict
sine-supercritical incidence, fixing an electric amplitude gives a unique positive-normal-decay
transmitted carrier candidate. -/
lemma existsUnique_isPositiveNormalDecayTransmittedCandidate_with_electricAmplitude
    (configuration : PlanarDielectricWaveConfiguration)
    (electricAmplitude : EuclideanSpace ℂ (Fin 3))
    (hIncidentDispersion : configuration.incident.IsDispersionMatched
      configuration.interface.negativeMedium)
    (hIncidentAttenuation : configuration.incident.waveVector.attenuationVector = 0)
    (hSupercritical : configuration.IsSupercriticalPhaseIncidence) :
    ∃! wave,
      configuration.IsPositiveNormalDecayTransmittedCandidate wave ∧
        wave.electricAmplitude = electricAmplitude := by
  have hRadicand : configuration.transmittedNormalRadicand < 0 :=
    (configuration.transmittedNormalRadicand_lt_zero_iff_isSupercriticalPhaseIncidence
      hIncidentDispersion hIncidentAttenuation).mpr hSupercritical
  have hIncidentTangentialAttenuation :
      configuration.interface.plane.tangentialProjection
        configuration.incident.waveVector.attenuationVector = 0 := by
    rw [hIncidentAttenuation]
    simp [OrientedAffineHyperplane.tangentialProjection,
      OrientedAffineHyperplane.normalComponent]
  exact
    existsUnique_isPositiveNormalDecayTransmittedCandidate_with_electricAmplitude_of_radicand_neg
      configuration electricAmplitude hIncidentTangentialAttenuation hRadicand

/-!

## C. Exact positive-normal scaling

-/

/-- The canonical carrier constructor stores the wave vector represented by its proof-bearing
positive-normal-decay data. -/
private lemma waveVector_positiveNormalDecayTransmittedCandidate_eq_data
    (configuration : PlanarDielectricWaveConfiguration)
    (electricAmplitude : EuclideanSpace ℂ (Fin 3))
    (hRadicand : configuration.transmittedNormalRadicand < 0) :
    (configuration.positiveNormalDecayTransmittedCandidate electricAmplitude).waveVector =
      (configuration.positiveNormalDecayTransmittedData hRadicand).waveVector := by
  change configuration.positiveNormalDecayTransmittedWaveVector =
    (configuration.positiveNormalDecayTransmittedData hRadicand).waveVector
  exact (configuration.positiveNormalDecayTransmittedData_waveVector hRadicand).symm

/-- The canonical positive-normal-decay candidate's complete carrier has exact exponential
scaling under stored-normal displacement at the square-root decay rate.

The base point is arbitrary, the carrier remains globally defined, and negative displacement
gives growth rather than a one-sided support condition. -/
lemma positiveNormalDecayTransmittedCandidate_carrier_vadd_normalVector
    (configuration : PlanarDielectricWaveConfiguration)
    (electricAmplitude : EuclideanSpace ℂ (Fin 3))
    (hRadicand : configuration.transmittedNormalRadicand < 0)
    (u : ℝ) (t : Time) (x : Space) :
    (configuration.positiveNormalDecayTransmittedCandidate electricAmplitude).carrier t
        (u • configuration.interface.plane.normalVector +ᵥ x) =
      (Real.exp
          (-Real.sqrt (-configuration.transmittedNormalRadicand) * u) : ℂ) *
        (configuration.positiveNormalDecayTransmittedCandidate electricAmplitude).carrier t x := by
  simpa only [configuration.positiveNormalDecayTransmittedData_normalVector hRadicand,
    configuration.positiveNormalDecayTransmittedData_decayRate hRadicand] using
    (configuration.positiveNormalDecayTransmittedCandidate
      electricAmplitude).carrier_vadd_positiveNormalDecay
        (configuration.positiveNormalDecayTransmittedData hRadicand)
          (waveVector_positiveNormalDecayTransmittedCandidate_eq_data
            configuration electricAmplitude hRadicand) u t x

/-- The canonical positive-normal-decay candidate's ordinary electric field has exact exponential
scaling under stored-normal displacement at the square-root decay rate. -/
lemma positiveNormalDecayTransmittedCandidate_electricField_vadd_normalVector
    (configuration : PlanarDielectricWaveConfiguration)
    (electricAmplitude : EuclideanSpace ℂ (Fin 3))
    (hRadicand : configuration.transmittedNormalRadicand < 0)
    (u : ℝ) (t : Time) (x : Space) :
    (configuration.positiveNormalDecayTransmittedCandidate electricAmplitude).electricField t
        (u • configuration.interface.plane.normalVector +ᵥ x) =
      Real.exp (-Real.sqrt (-configuration.transmittedNormalRadicand) * u) •
        (configuration.positiveNormalDecayTransmittedCandidate electricAmplitude).electricField
          t x := by
  simpa only [configuration.positiveNormalDecayTransmittedData_normalVector hRadicand,
    configuration.positiveNormalDecayTransmittedData_decayRate hRadicand] using
    (configuration.positiveNormalDecayTransmittedCandidate
      electricAmplitude).electricField_vadd_positiveNormalDecay
        (configuration.positiveNormalDecayTransmittedData hRadicand)
          (waveVector_positiveNormalDecayTransmittedCandidate_eq_data
            configuration electricAmplitude hRadicand) u t x

/-- The canonical positive-normal-decay candidate's ordinary magnetic induction has exact
exponential scaling under stored-normal displacement at the square-root decay rate. -/
lemma positiveNormalDecayTransmittedCandidate_magneticInduction_vadd_normalVector
    (configuration : PlanarDielectricWaveConfiguration)
    (electricAmplitude : EuclideanSpace ℂ (Fin 3))
    (hRadicand : configuration.transmittedNormalRadicand < 0)
    (u : ℝ) (t : Time) (x : Space) :
    (configuration.positiveNormalDecayTransmittedCandidate electricAmplitude).magneticInduction t
        (u • configuration.interface.plane.normalVector +ᵥ x) =
      Real.exp (-Real.sqrt (-configuration.transmittedNormalRadicand) * u) •
        (configuration.positiveNormalDecayTransmittedCandidate
          electricAmplitude).magneticInduction t x := by
  simpa only [configuration.positiveNormalDecayTransmittedData_normalVector hRadicand,
    configuration.positiveNormalDecayTransmittedData_decayRate hRadicand] using
    (configuration.positiveNormalDecayTransmittedCandidate
      electricAmplitude).magneticInduction_vadd_positiveNormalDecay
        (configuration.positiveNormalDecayTransmittedData hRadicand)
          (waveVector_positiveNormalDecayTransmittedCandidate_eq_data
            configuration electricAmplitude hRadicand) u t x

/-!

## D. Supplied-candidate identification

-/

namespace IsElectricPhaseMatched

variable {configuration : PlanarDielectricWaveConfiguration}

/-- A supplied phase-matched, positive-medium-dispersive transmitted carrier with zero incident
tangential attenuation and positive-side attenuation direction satisfies the
positive-normal-decay transmitted carrier specification. The direction describes only the
attenuation-vector geometry; it supplies no phase, ray, group-velocity, energy-flow, outgoing,
Maxwell, irradiance, or power direction. -/
lemma transmitted_isPositiveNormalDecayTransmittedCandidate
    (h : configuration.IsElectricPhaseMatched)
    (hTransmittedDispersion : configuration.transmitted.IsDispersionMatched
      configuration.interface.positiveMedium)
    (hIncidentTangentialAttenuation :
      configuration.interface.plane.tangentialProjection
        configuration.incident.waveVector.attenuationVector = 0)
    (hDirection : configuration.transmitted.waveVector.IsAttenuationDirectedInto
      configuration.interface.plane .positive) :
    configuration.IsPositiveNormalDecayTransmittedCandidate configuration.transmitted :=
  ⟨h.1.1, h.transmitted_isPositiveNormalDecayTransmittedWaveVector
    hTransmittedDispersion hIncidentTangentialAttenuation hDirection⟩

/-- A supplied phase-matched, positive-medium-dispersive, attenuation-directed transmitted
carrier with zero incident tangential attenuation is the canonical family member with its stored
electric amplitude.

The direction is supplied rather than derived from the transmitted label and has no phase, ray,
group-velocity, energy-flow, outgoing, total-internal-reflection, Maxwell, irradiance, or power-flow
meaning. -/
lemma transmitted_eq_positiveNormalDecayTransmittedCandidate
    (h : configuration.IsElectricPhaseMatched)
    (hTransmittedDispersion : configuration.transmitted.IsDispersionMatched
      configuration.interface.positiveMedium)
    (hIncidentTangentialAttenuation :
      configuration.interface.plane.tangentialProjection
        configuration.incident.waveVector.attenuationVector = 0)
    (hDirection : configuration.transmitted.waveVector.IsAttenuationDirectedInto
      configuration.interface.plane .positive) :
    configuration.transmitted =
      configuration.positiveNormalDecayTransmittedCandidate
        configuration.transmitted.electricAmplitude :=
  (h.transmitted_isPositiveNormalDecayTransmittedCandidate hTransmittedDispersion
    hIncidentTangentialAttenuation hDirection).eq_positiveNormalDecayTransmittedCandidate

end IsElectricPhaseMatched

end PlanarDielectricWaveConfiguration

end
end Optics
