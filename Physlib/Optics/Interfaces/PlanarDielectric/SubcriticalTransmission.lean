/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Interfaces.PlanarDielectric.CriticalAngle

/-!
# Subcritical transmitted phase-root construction

## i. Overview

This file constructs the positive real transmitted normal root at a planar dielectric interface.
The construction keeps the incident tangential phase vector, uses the positive square root of the
transmitted normal radicand, and embeds the resulting real vector into the complex wave-vector
space.

Under negative-medium incident dispersion, zero whole incident attenuation, and strict
sine-subcritical incidence, the construction is the unique complex wave vector with the incident
complex tangential projection, the positive-medium material shell at the incident frequency, zero
attenuation, and phase direction into the geometric positive side. Conversely, existence of such
a vector forces strict sine-subcritical incidence under the same incident hypotheses.

The vector lifts to a plane-wave candidate after an arbitrary electric amplitude is supplied.
Only its frequency and wave vector are determined: the amplitude can vanish or fail
transversality, and no Maxwell, boundary-amplitude, reflected-wave, ray, group-velocity, outgoing,
irradiance, or power statement is made. Positive phase direction is not used as a synonym for any
of those later notions.

## ii. Key results

- `positivePhaseTransmittedWaveVector`: the canonical positive real normal-root construction.
- `IsPositivePhaseTransmittedWaveVector`: the exact carrier-geometry specification.
- `transmittedNormalRadicand_pos_iff_existsUnique_isPositivePhaseTransmittedWaveVector`: the
  weakest radicand-level existence and uniqueness characterization.
- `isSubcriticalPhaseIncidence_iff_existsUnique_isPositivePhaseTransmittedWaveVector`: strict
  sine-subcritical incidence is equivalent to unique existence of the specified wave vector.
- `positivePhaseTransmittedCandidate`: the corresponding arbitrary-amplitude plane-wave family.
- `IsElectricPhaseMatched.transmitted_eq_positivePhaseTransmittedCandidate`: a supplied
  phase-matched and positive-phase-directed transmitted candidate is the canonical family member.

## iii. Table of contents

- A. Positive real transmitted wave vector
- B. Existence and uniqueness below the critical sine threshold
- C. Arbitrary-amplitude plane-wave candidates
- D. Supplied-candidate identification

## iv. References

The construction specializes Physlib's complex wave-vector hyperplane decomposition, material
dispersion shell, and critical-sine threshold APIs. No external formal-development source is
copied or translated here.
-/

@[expose] public section

namespace Optics

open ClassicalMechanics Electromagnetism Electromagnetism.ThreeDimension Space
open ClassicalMechanics.ComplexWaveVector
open Electromagnetism.ThreeDimension.ComplexMonochromaticPlaneWave

noncomputable section

namespace PlanarDielectricWaveConfiguration

/-!

## A. Positive real transmitted wave vector

-/

/-- The canonical positive-phase transmitted wave vector formed from the incident tangential
phase vector and the positive square root of the candidate transmitted normal radicand.

This definition is total. Its positive-root, material-shell, and transmitted-role properties are
proved only under the hypotheses of the subsequent lemmas; in particular, `Real.sqrt` alone does
not prove that the radicand is nonnegative. -/
noncomputable def positivePhaseTransmittedWaveVector
    (configuration : PlanarDielectricWaveConfiguration) : ComplexWaveVector 3 :=
  replaceHyperplaneNormalComponent configuration.interface.plane
    (ofReal configuration.incident.waveVector.phaseVector)
    (Real.sqrt configuration.transmittedNormalRadicand : ℂ)

/-- The canonical construction is the real embedding of the incident tangential phase vector
plus its selected positive normal component. -/
lemma positivePhaseTransmittedWaveVector_eq_ofReal
    (configuration : PlanarDielectricWaveConfiguration) :
    configuration.positivePhaseTransmittedWaveVector =
      ofReal
        (configuration.interface.plane.tangentialProjection
            configuration.incident.waveVector.phaseVector +
          Real.sqrt configuration.transmittedNormalRadicand •
            configuration.interface.plane.normalVector) := by
  simpa [positivePhaseTransmittedWaveVector] using
    replaceHyperplaneNormalComponent_ofReal configuration.interface.plane
      configuration.incident.waveVector.phaseVector
        (Real.sqrt configuration.transmittedNormalRadicand)

/-- The canonical construction has the incident tangential phase vector as its complex
tangential projection. -/
lemma hyperplaneTangentialProjection_positivePhaseTransmittedWaveVector
    (configuration : PlanarDielectricWaveConfiguration) :
    hyperplaneTangentialProjection configuration.interface.plane
        configuration.positivePhaseTransmittedWaveVector =
      ofReal (configuration.interface.plane.tangentialProjection
        configuration.incident.waveVector.phaseVector) := by
  rw [positivePhaseTransmittedWaveVector,
    hyperplaneTangentialProjection_replaceHyperplaneNormalComponent]
  exact hyperplaneTangentialProjection_eq_ofReal_of_tangentialProjection_attenuationVector_eq_zero
    configuration.interface.plane (ofReal configuration.incident.waveVector.phaseVector)
      (by simp [OrientedAffineHyperplane.tangentialProjection,
        OrientedAffineHyperplane.normalComponent])

/-- The canonical construction has the positive square root as its complex normal component. -/
@[simp]
lemma hyperplaneNormalComponent_positivePhaseTransmittedWaveVector
    (configuration : PlanarDielectricWaveConfiguration) :
    hyperplaneNormalComponent configuration.interface.plane
        configuration.positivePhaseTransmittedWaveVector =
      (Real.sqrt configuration.transmittedNormalRadicand : ℂ) := by
  simp [positivePhaseTransmittedWaveVector]

/-- The canonical positive-phase construction has zero whole attenuation. -/
@[simp]
lemma attenuationVector_positivePhaseTransmittedWaveVector
    (configuration : PlanarDielectricWaveConfiguration) :
    configuration.positivePhaseTransmittedWaveVector.attenuationVector = 0 := by
  rw [configuration.positivePhaseTransmittedWaveVector_eq_ofReal]
  exact attenuationVector_ofReal _

/-- A nonnegative transmitted normal radicand puts the canonical construction on the
positive-medium material shell at the incident angular frequency. -/
lemma bilinearDot_positivePhaseTransmittedWaveVector_self
    (configuration : PlanarDielectricWaveConfiguration)
    (hRadicand : 0 ≤ configuration.transmittedNormalRadicand) :
    bilinearDot configuration.positivePhaseTransmittedWaveVector
        configuration.positivePhaseTransmittedWaveVector =
      ((configuration.interface.positiveMedium.ε *
        configuration.interface.positiveMedium.μ *
        configuration.incident.angularFrequency ^ 2 : ℝ) : ℂ) := by
  have hSqrt :
      (Real.sqrt configuration.transmittedNormalRadicand : ℂ) ^ 2 =
        (configuration.transmittedNormalRadicand : ℂ) := by
    norm_cast
    exact Real.sq_sqrt hRadicand
  rw [bilinearDot_self_eq_tangential_add_normal_sq,
    configuration.hyperplaneTangentialProjection_positivePhaseTransmittedWaveVector,
    configuration.hyperplaneNormalComponent_positivePhaseTransmittedWaveVector,
    bilinearDot_ofReal, real_inner_self_eq_norm_sq, hSqrt, transmittedNormalRadicand]
  push_cast
  ring

/-- A strictly positive transmitted normal radicand makes the canonical phase vector point
strictly into the geometric positive side. -/
lemma positivePhaseTransmittedWaveVector_isPhaseDirectedInto
    (configuration : PlanarDielectricWaveConfiguration)
    (hRadicand : 0 < configuration.transmittedNormalRadicand) :
    configuration.positivePhaseTransmittedWaveVector.IsPhaseDirectedInto
      configuration.interface.plane .positive := by
  simp [IsPhaseDirectedInto, Real.sqrt_pos.2 hRadicand]

/-- A complex wave vector realizes positive-phase transmitted carrier geometry when it preserves
the incident complex tangential projection, lies on the positive-medium material shell at the
incident frequency, has zero whole attenuation, and points in phase into the positive side.

The final condition is only a strict phase-normal sign. This predicate assigns no electric
amplitude, transversality, Maxwell, ray, group-velocity, outgoing, irradiance, or power meaning. -/
def IsPositivePhaseTransmittedWaveVector
    (configuration : PlanarDielectricWaveConfiguration)
    (waveVector : ComplexWaveVector 3) : Prop :=
  hyperplaneTangentialProjection configuration.interface.plane waveVector =
      hyperplaneTangentialProjection configuration.interface.plane
        configuration.incident.waveVector ∧
    bilinearDot waveVector waveVector =
      ((configuration.interface.positiveMedium.ε *
        configuration.interface.positiveMedium.μ *
        configuration.incident.angularFrequency ^ 2 : ℝ) : ℂ) ∧
    waveVector.attenuationVector = 0 ∧
    waveVector.IsPhaseDirectedInto configuration.interface.plane .positive

namespace IsPositivePhaseTransmittedWaveVector

variable {configuration : PlanarDielectricWaveConfiguration}
  {waveVector : ComplexWaveVector 3}

/-- A positive-phase transmitted wave-vector specification forces zero incident tangential
attenuation through its common complex tangential projection. -/
lemma incidentTangentialAttenuation_eq_zero
    (h : configuration.IsPositivePhaseTransmittedWaveVector waveVector) :
    configuration.interface.plane.tangentialProjection
      configuration.incident.waveVector.attenuationVector = 0 := by
  have hAttenuation := congrArg ComplexWaveVector.attenuationVector h.1
  rw [attenuationVector_hyperplaneTangentialProjection,
    attenuationVector_hyperplaneTangentialProjection, h.2.2.1] at hAttenuation
  calc
    configuration.interface.plane.tangentialProjection
        configuration.incident.waveVector.attenuationVector =
      configuration.interface.plane.tangentialProjection 0 := hAttenuation.symm
    _ = 0 := by
      simp [OrientedAffineHyperplane.tangentialProjection,
        OrientedAffineHyperplane.normalComponent]

/-- The normal component of every specified positive-phase transmitted wave vector squares to
the real transmitted normal radicand. -/
lemma hyperplaneNormalComponent_sq_eq_transmittedNormalRadicand
    (h : configuration.IsPositivePhaseTransmittedWaveVector waveVector) :
    hyperplaneNormalComponent configuration.interface.plane waveVector ^ 2 =
      (configuration.transmittedNormalRadicand : ℂ) :=
  configuration.hyperplaneNormalComponent_sq_eq_transmittedNormalRadicand_of_tangentialProjection_eq
    waveVector h.1 h.2.1 h.incidentTangentialAttenuation_eq_zero

/-- Every specified positive-phase transmitted wave vector forces a positive radicand and has
the selected positive real normal root. -/
lemma normalRoot_data
    (h : configuration.IsPositivePhaseTransmittedWaveVector waveVector) :
    0 < configuration.transmittedNormalRadicand ∧
      configuration.interface.plane.normalComponent waveVector.attenuationVector = 0 ∧
      hyperplaneNormalComponent configuration.interface.plane waveVector =
        (Real.sqrt configuration.transmittedNormalRadicand : ℂ) := by
  simpa using normalRoot_data_of_sq_eq_real_of_isPhaseDirectedInto
    configuration.interface.plane waveVector configuration.transmittedNormalRadicand
      .positive h.hyperplaneNormalComponent_sq_eq_transmittedNormalRadicand h.2.2.2

/-- Every wave vector satisfying the positive-phase transmitted specification equals the
canonical construction. -/
lemma eq_positivePhaseTransmittedWaveVector
    (h : configuration.IsPositivePhaseTransmittedWaveVector waveVector) :
    waveVector = configuration.positivePhaseTransmittedWaveVector := by
  apply eq_of_hyperplaneTangentialProjection_eq_of_hyperplaneNormalComponent_eq
    configuration.interface.plane
  · calc
      hyperplaneTangentialProjection configuration.interface.plane waveVector =
          hyperplaneTangentialProjection configuration.interface.plane
            configuration.incident.waveVector := h.1
      _ = ofReal (configuration.interface.plane.tangentialProjection
            configuration.incident.waveVector.phaseVector) :=
        hyperplaneTangentialProjection_eq_ofReal_of_tangentialProjection_attenuationVector_eq_zero
          configuration.interface.plane configuration.incident.waveVector
            h.incidentTangentialAttenuation_eq_zero
      _ = hyperplaneTangentialProjection configuration.interface.plane
          configuration.positivePhaseTransmittedWaveVector :=
        configuration.hyperplaneTangentialProjection_positivePhaseTransmittedWaveVector.symm
  · simpa using h.normalRoot_data.2.2

end IsPositivePhaseTransmittedWaveVector

/-!

## B. Existence and uniqueness below the critical sine threshold

-/

/-- Zero incident tangential attenuation and a strictly positive transmitted normal radicand are
the weakest direct hypotheses proving the canonical positive-phase transmitted wave-vector
specification. -/
lemma positivePhaseTransmittedWaveVector_isPositivePhaseTransmittedWaveVector_of_radicand_pos
    (configuration : PlanarDielectricWaveConfiguration)
    (hIncidentTangentialAttenuation :
      configuration.interface.plane.tangentialProjection
        configuration.incident.waveVector.attenuationVector = 0)
    (hRadicand : 0 < configuration.transmittedNormalRadicand) :
    configuration.IsPositivePhaseTransmittedWaveVector
      configuration.positivePhaseTransmittedWaveVector := by
  refine ⟨?_,
    configuration.bilinearDot_positivePhaseTransmittedWaveVector_self hRadicand.le,
    configuration.attenuationVector_positivePhaseTransmittedWaveVector,
    configuration.positivePhaseTransmittedWaveVector_isPhaseDirectedInto hRadicand⟩
  rw [configuration.hyperplaneTangentialProjection_positivePhaseTransmittedWaveVector]
  exact
    (hyperplaneTangentialProjection_eq_ofReal_of_tangentialProjection_attenuationVector_eq_zero
      configuration.interface.plane configuration.incident.waveVector
        hIncidentTangentialAttenuation).symm

/-- Under incident material dispersion, zero whole incident attenuation, and strict
sine-subcritical incidence, the canonical construction satisfies the positive-phase transmitted
wave-vector specification. -/
lemma positivePhaseTransmittedWaveVector_isPositivePhaseTransmittedWaveVector
    (configuration : PlanarDielectricWaveConfiguration)
    (hIncidentDispersion : configuration.incident.IsDispersionMatched
      configuration.interface.negativeMedium)
    (hIncidentAttenuation : configuration.incident.waveVector.attenuationVector = 0)
    (hSubcritical : configuration.IsSubcriticalPhaseIncidence) :
    configuration.IsPositivePhaseTransmittedWaveVector
      configuration.positivePhaseTransmittedWaveVector := by
  have hRadicand : 0 < configuration.transmittedNormalRadicand :=
    (configuration.transmittedNormalRadicand_pos_iff_isSubcriticalPhaseIncidence
      hIncidentDispersion hIncidentAttenuation).mpr hSubcritical
  have hIncidentTangentialAttenuation :
      configuration.interface.plane.tangentialProjection
        configuration.incident.waveVector.attenuationVector = 0 := by
    rw [hIncidentAttenuation]
    simp [OrientedAffineHyperplane.tangentialProjection,
      OrientedAffineHyperplane.normalComponent]
  exact
    positivePhaseTransmittedWaveVector_isPositivePhaseTransmittedWaveVector_of_radicand_pos
      configuration hIncidentTangentialAttenuation hRadicand

/-- With zero incident tangential attenuation, positivity of the transmitted normal radicand is
equivalent to unique existence of the positive-phase transmitted wave vector. -/
lemma transmittedNormalRadicand_pos_iff_existsUnique_isPositivePhaseTransmittedWaveVector
    (configuration : PlanarDielectricWaveConfiguration)
    (hIncidentTangentialAttenuation :
      configuration.interface.plane.tangentialProjection
        configuration.incident.waveVector.attenuationVector = 0) :
    0 < configuration.transmittedNormalRadicand ↔
      ∃! waveVector, configuration.IsPositivePhaseTransmittedWaveVector waveVector := by
  constructor
  · intro hRadicand
    refine ⟨configuration.positivePhaseTransmittedWaveVector,
      positivePhaseTransmittedWaveVector_isPositivePhaseTransmittedWaveVector_of_radicand_pos
        configuration hIncidentTangentialAttenuation hRadicand, ?_⟩
    intro waveVector hWaveVector
    exact hWaveVector.eq_positivePhaseTransmittedWaveVector
  · rintro ⟨waveVector, hWaveVector, -⟩
    exact hWaveVector.normalRoot_data.1

/-- Strict sine-subcritical incidence gives a unique positive-phase transmitted wave vector. -/
lemma existsUnique_isPositivePhaseTransmittedWaveVector
    (configuration : PlanarDielectricWaveConfiguration)
    (hIncidentDispersion : configuration.incident.IsDispersionMatched
      configuration.interface.negativeMedium)
    (hIncidentAttenuation : configuration.incident.waveVector.attenuationVector = 0)
    (hSubcritical : configuration.IsSubcriticalPhaseIncidence) :
    ∃! waveVector, configuration.IsPositivePhaseTransmittedWaveVector waveVector := by
  refine ⟨configuration.positivePhaseTransmittedWaveVector,
    configuration.positivePhaseTransmittedWaveVector_isPositivePhaseTransmittedWaveVector
      hIncidentDispersion hIncidentAttenuation hSubcritical, ?_⟩
  intro waveVector hWaveVector
  exact hWaveVector.eq_positivePhaseTransmittedWaveVector

/-- Under negative-medium incident dispersion and zero whole incident attenuation, strict
sine-subcritical incidence is equivalent to unique existence of the positive-phase transmitted
wave vector. -/
lemma isSubcriticalPhaseIncidence_iff_existsUnique_isPositivePhaseTransmittedWaveVector
    (configuration : PlanarDielectricWaveConfiguration)
    (hIncidentDispersion : configuration.incident.IsDispersionMatched
      configuration.interface.negativeMedium)
    (hIncidentAttenuation : configuration.incident.waveVector.attenuationVector = 0) :
    configuration.IsSubcriticalPhaseIncidence ↔
      ∃! waveVector, configuration.IsPositivePhaseTransmittedWaveVector waveVector := by
  have hIncidentTangentialAttenuation :
      configuration.interface.plane.tangentialProjection
        configuration.incident.waveVector.attenuationVector = 0 := by
    rw [hIncidentAttenuation]
    simp [OrientedAffineHyperplane.tangentialProjection,
      OrientedAffineHyperplane.normalComponent]
  calc
    configuration.IsSubcriticalPhaseIncidence ↔
        0 < configuration.transmittedNormalRadicand :=
      (configuration.transmittedNormalRadicand_pos_iff_isSubcriticalPhaseIncidence
        hIncidentDispersion hIncidentAttenuation).symm
    _ ↔ ∃! waveVector, configuration.IsPositivePhaseTransmittedWaveVector waveVector :=
      transmittedNormalRadicand_pos_iff_existsUnique_isPositivePhaseTransmittedWaveVector
        configuration hIncidentTangentialAttenuation

/-!

## C. Arbitrary-amplitude plane-wave candidates

-/

/-- A plane-wave candidate carrying the canonical positive-phase transmitted wave vector at the
incident frequency and an arbitrary supplied electric amplitude.

The amplitude is not determined by an interface boundary equation and may be zero or
nontransverse. -/
noncomputable def positivePhaseTransmittedCandidate
    (configuration : PlanarDielectricWaveConfiguration)
    (electricAmplitude : EuclideanSpace ℂ (Fin 3)) : ComplexMonochromaticPlaneWave where
  angularFrequency := configuration.incident.angularFrequency
  angularFrequency_pos := configuration.incident.angularFrequency_pos
  waveVector := configuration.positivePhaseTransmittedWaveVector
  electricAmplitude := electricAmplitude

/-- A plane-wave candidate has positive-phase transmitted carrier data when its frequency is the
incident frequency and its wave vector satisfies the positive-phase transmitted specification.
Its electric amplitude remains unconstrained. -/
def IsPositivePhaseTransmittedCandidate
    (configuration : PlanarDielectricWaveConfiguration)
    (wave : ComplexMonochromaticPlaneWave) : Prop :=
  wave.angularFrequency = configuration.incident.angularFrequency ∧
    configuration.IsPositivePhaseTransmittedWaveVector wave.waveVector

namespace IsPositivePhaseTransmittedCandidate

variable {configuration : PlanarDielectricWaveConfiguration}
  {wave : ComplexMonochromaticPlaneWave}

/-- A positive-phase transmitted candidate supplies the common transmitted frequency and complex
tangential wave-vector data, without constraining the reflected label. -/
lemma phaseMatchData (h : configuration.IsPositivePhaseTransmittedCandidate wave) :
    wave.angularFrequency = configuration.incident.angularFrequency ∧
      hyperplaneTangentialProjection configuration.interface.plane wave.waveVector =
        hyperplaneTangentialProjection configuration.interface.plane
          configuration.incident.waveVector :=
  ⟨h.1, h.2.1⟩

/-- Every positive-phase transmitted candidate is dispersion matched to the positive-side
medium. -/
lemma isDispersionMatched (h : configuration.IsPositivePhaseTransmittedCandidate wave) :
    wave.IsDispersionMatched configuration.interface.positiveMedium := by
  rw [IsDispersionMatched, h.1]
  exact h.2.2.1

/-- Every positive-phase transmitted candidate is the canonical family member with its own
electric amplitude. -/
lemma eq_positivePhaseTransmittedCandidate
    (h : configuration.IsPositivePhaseTransmittedCandidate wave) :
    wave = configuration.positivePhaseTransmittedCandidate wave.electricAmplitude := by
  rcases h with ⟨hFrequency, hWaveVector⟩
  have hVector := hWaveVector.eq_positivePhaseTransmittedWaveVector
  cases wave with
  | mk angularFrequency angularFrequency_pos waveVector electricAmplitude =>
      dsimp at hFrequency hVector ⊢
      subst angularFrequency
      subst waveVector
      rfl

end IsPositivePhaseTransmittedCandidate

/-- Under strict sine-subcritical incidence, every supplied electric amplitude gives a
positive-phase transmitted plane-wave candidate. -/
lemma positivePhaseTransmittedCandidate_isPositivePhaseTransmittedCandidate
    (configuration : PlanarDielectricWaveConfiguration)
    (electricAmplitude : EuclideanSpace ℂ (Fin 3))
    (hIncidentDispersion : configuration.incident.IsDispersionMatched
      configuration.interface.negativeMedium)
    (hIncidentAttenuation : configuration.incident.waveVector.attenuationVector = 0)
    (hSubcritical : configuration.IsSubcriticalPhaseIncidence) :
    configuration.IsPositivePhaseTransmittedCandidate
      (configuration.positivePhaseTransmittedCandidate electricAmplitude) := by
  exact ⟨rfl,
    configuration.positivePhaseTransmittedWaveVector_isPositivePhaseTransmittedWaveVector
      hIncidentDispersion hIncidentAttenuation hSubcritical⟩

/-- After an electric amplitude is fixed, strict sine-subcritical incidence gives a unique
positive-phase transmitted plane-wave candidate. -/
lemma existsUnique_isPositivePhaseTransmittedCandidate_with_electricAmplitude
    (configuration : PlanarDielectricWaveConfiguration)
    (electricAmplitude : EuclideanSpace ℂ (Fin 3))
    (hIncidentDispersion : configuration.incident.IsDispersionMatched
      configuration.interface.negativeMedium)
    (hIncidentAttenuation : configuration.incident.waveVector.attenuationVector = 0)
    (hSubcritical : configuration.IsSubcriticalPhaseIncidence) :
    ∃! wave,
      configuration.IsPositivePhaseTransmittedCandidate wave ∧
        wave.electricAmplitude = electricAmplitude := by
  refine ⟨configuration.positivePhaseTransmittedCandidate electricAmplitude,
    ⟨configuration.positivePhaseTransmittedCandidate_isPositivePhaseTransmittedCandidate
      electricAmplitude hIncidentDispersion hIncidentAttenuation hSubcritical, rfl⟩, ?_⟩
  intro wave hWave
  calc
    wave = configuration.positivePhaseTransmittedCandidate wave.electricAmplitude :=
      hWave.1.eq_positivePhaseTransmittedCandidate
    _ = configuration.positivePhaseTransmittedCandidate electricAmplitude := by rw [hWave.2]

/-!

## D. Supplied-candidate identification

-/

namespace IsElectricPhaseMatched

variable {configuration : PlanarDielectricWaveConfiguration}

/-- A supplied phase-matched, positive-medium-dispersive transmitted candidate with zero incident
tangential attenuation and positive-side phase direction satisfies the positive-phase transmitted
wave-vector specification.

The direction is supplied rather than derived from the transmitted label, and this conclusion
has no outgoing or power-flow meaning. -/
lemma transmitted_isPositivePhaseTransmittedWaveVector
    (h : configuration.IsElectricPhaseMatched)
    (hTransmittedDispersion : configuration.transmitted.IsDispersionMatched
      configuration.interface.positiveMedium)
    (hIncidentTangentialAttenuation :
      configuration.interface.plane.tangentialProjection
        configuration.incident.waveVector.attenuationVector = 0)
    (hDirection : configuration.transmitted.waveVector.IsPhaseDirectedInto
      configuration.interface.plane .positive) :
    configuration.IsPositivePhaseTransmittedWaveVector
      configuration.transmitted.waveVector := by
  have hRootData := h.transmitted_normalRoot_data_of_isPhaseDirectedInto
    hTransmittedDispersion hIncidentTangentialAttenuation hDirection
  refine ⟨h.1.2, ?_, hRootData.2.1, hDirection⟩
  simpa only [IsDispersionMatched, h.1.1] using hTransmittedDispersion

/-- A supplied phase-matched, positive-medium-dispersive, positive-phase-directed transmitted
candidate with zero incident tangential attenuation has the canonical positive-phase transmitted
wave vector. -/
lemma transmitted_waveVector_eq_positivePhaseTransmittedWaveVector
    (h : configuration.IsElectricPhaseMatched)
    (hTransmittedDispersion : configuration.transmitted.IsDispersionMatched
      configuration.interface.positiveMedium)
    (hIncidentTangentialAttenuation :
      configuration.interface.plane.tangentialProjection
        configuration.incident.waveVector.attenuationVector = 0)
    (hDirection : configuration.transmitted.waveVector.IsPhaseDirectedInto
      configuration.interface.plane .positive) :
    configuration.transmitted.waveVector =
      configuration.positivePhaseTransmittedWaveVector :=
  (h.transmitted_isPositivePhaseTransmittedWaveVector hTransmittedDispersion
    hIncidentTangentialAttenuation hDirection).eq_positivePhaseTransmittedWaveVector

/-- A supplied phase-matched, positive-medium-dispersive, positive-phase-directed transmitted
candidate with zero incident tangential attenuation is the canonical plane-wave family member
with its stored electric amplitude. -/
lemma transmitted_eq_positivePhaseTransmittedCandidate
    (h : configuration.IsElectricPhaseMatched)
    (hTransmittedDispersion : configuration.transmitted.IsDispersionMatched
      configuration.interface.positiveMedium)
    (hIncidentTangentialAttenuation :
      configuration.interface.plane.tangentialProjection
        configuration.incident.waveVector.attenuationVector = 0)
    (hDirection : configuration.transmitted.waveVector.IsPhaseDirectedInto
      configuration.interface.plane .positive) :
    configuration.transmitted =
      configuration.positivePhaseTransmittedCandidate
        configuration.transmitted.electricAmplitude := by
  apply IsPositivePhaseTransmittedCandidate.eq_positivePhaseTransmittedCandidate
  exact ⟨h.1.1, h.transmitted_isPositivePhaseTransmittedWaveVector
    hTransmittedDispersion hIncidentTangentialAttenuation hDirection⟩

/-- Under incident dispersion and zero whole incident attenuation, a supplied phase-matched,
positive-medium-dispersive, positive-phase-directed transmitted candidate forces strict
sine-subcritical incidence. -/
lemma isSubcriticalPhaseIncidence_of_transmitted_isPhaseDirectedInto
    (h : configuration.IsElectricPhaseMatched)
    (hIncidentDispersion : configuration.incident.IsDispersionMatched
      configuration.interface.negativeMedium)
    (hTransmittedDispersion : configuration.transmitted.IsDispersionMatched
      configuration.interface.positiveMedium)
    (hIncidentAttenuation : configuration.incident.waveVector.attenuationVector = 0)
    (hDirection : configuration.transmitted.waveVector.IsPhaseDirectedInto
      configuration.interface.plane .positive) :
    configuration.IsSubcriticalPhaseIncidence := by
  have hIncidentTangentialAttenuation :
      configuration.interface.plane.tangentialProjection
        configuration.incident.waveVector.attenuationVector = 0 := by
    rw [hIncidentAttenuation]
    simp [OrientedAffineHyperplane.tangentialProjection,
      OrientedAffineHyperplane.normalComponent]
  have hWaveVector := h.transmitted_isPositivePhaseTransmittedWaveVector
    hTransmittedDispersion hIncidentTangentialAttenuation hDirection
  exact (configuration.transmittedNormalRadicand_pos_iff_isSubcriticalPhaseIncidence
    hIncidentDispersion hIncidentAttenuation).mp hWaveVector.normalRoot_data.1

end IsElectricPhaseMatched

end PlanarDielectricWaveConfiguration

end
end Optics
