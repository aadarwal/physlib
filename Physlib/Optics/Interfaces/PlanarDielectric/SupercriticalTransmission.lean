/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Interfaces.PlanarDielectric.CriticalAngle

/-!
# Supercritical transmitted positive-normal decay

## i. Overview

This file constructs the transmitted complex wave-vector branch whose attenuation points along
the stored interface normal into the geometric positive side. The canonical vector keeps the
incident tangential phase data and sets its complex normal component to
`-I * √(-transmittedNormalRadicand)`. For `K = q - I a`, this sign gives positive normal
attenuation and therefore exponential decay under increasing stored-normal displacement when the
radicand is negative. The total formula has only a nonnegative square-root normal attenuation
outside that strict regime.

With zero incident tangential attenuation, a negative transmitted normal radicand is equivalent
to unique existence of a vector with the incident complex tangent, the positive-medium material
shell, purely normal attenuation, and strict positive-side attenuation direction. Under incident
negative-medium dispersion and zero whole incident attenuation, this becomes an exact
sine-supercritical existence and uniqueness characterization.

The resulting vector has the interface-local carrier geometry often associated with an evanescent
branch: its phase vector is tangent, its attenuation vector is a strictly positive multiple of the
normal, and its spatial factor decays to zero with positive-side depth. The carrier remains global,
negative depth gives growth, and none of these facts proves one-sided support, Maxwell equations,
electric transversality, ray or group velocity, an outgoing radiation condition, total internal
reflection, a Fresnel coefficient, irradiance, or power flow.

## ii. Key results

- `positiveNormalDecayTransmittedWaveVector`: the canonical negative-imaginary normal root.
- `IsPositiveNormalDecayTransmittedWaveVector`: the exact tangent, shell, and decay specification.
- `transmittedNormalRadicand_lt_zero_iff_existsUnique_isPositiveNormalDecayTransmittedWaveVector`:
  the weakest radicand-level existence and uniqueness characterization.
- `isSupercriticalPhaseIncidence_iff_existsUnique_isPositiveNormalDecayTransmittedWaveVector`:
  the sine-supercritical specialization.
- `positiveNormalDecayTransmittedData`: a proof-bearing bridge to the neutral positive-normal
  decay and spatial-limit API.
- `IsElectricPhaseMatched.transmitted_waveVector_eq_positiveNormalDecayTransmittedWaveVector`:
  identification of an already supplied attenuation-directed candidate.

## iii. Table of contents

- A. Canonical positive-normal-decay wave vector
- B. Positive-normal decay data and spatial scaling
- C. Existence and uniqueness above the critical sine threshold
- D. Supplied-candidate wave-vector identification

## iv. References

The construction specializes Physlib's complex normal-component replacement, imaginary-root choice,
positive-normal decay data, material shell, and critical-sine threshold APIs. No external formal-
development source is copied or translated here.
-/

@[expose] public section

namespace Optics

open ClassicalMechanics Electromagnetism Electromagnetism.ThreeDimension Space
open ClassicalMechanics.ComplexWaveVector
open Electromagnetism.ThreeDimension.ComplexMonochromaticPlaneWave

noncomputable section

namespace PlanarDielectricWaveConfiguration

/-!

## A. Canonical positive-normal-decay wave vector

-/

/-- The canonical transmitted wave vector with negative-imaginary normal component
`-I * √(-transmittedNormalRadicand)` and the incident tangential phase vector.

This definition is total. Its positive-normal decay, material-shell, and supercritical properties
are proved only under the subsequent nonpositive or negative radicand hypotheses. -/
noncomputable def positiveNormalDecayTransmittedWaveVector
    (configuration : PlanarDielectricWaveConfiguration) : ComplexWaveVector 3 :=
  replaceHyperplaneNormalComponent configuration.interface.plane
    (ofReal configuration.incident.waveVector.phaseVector)
    (-Complex.I *
      (Real.sqrt (-configuration.transmittedNormalRadicand) : ℂ))

/-- The canonical vector is the phase--attenuation representation with incident tangential phase
and nonnegative square-root stored-normal attenuation. -/
lemma positiveNormalDecayTransmittedWaveVector_eq_ofPhaseAttenuation
    (configuration : PlanarDielectricWaveConfiguration) :
    configuration.positiveNormalDecayTransmittedWaveVector =
      ofPhaseAttenuation
        (configuration.interface.plane.tangentialProjection
          configuration.incident.waveVector.phaseVector)
        (Real.sqrt (-configuration.transmittedNormalRadicand) •
          configuration.interface.plane.normalVector) := by
  simpa [positiveNormalDecayTransmittedWaveVector] using
    replaceHyperplaneNormalComponent_ofReal_neg_I_mul configuration.interface.plane
      configuration.incident.waveVector.phaseVector
        (Real.sqrt (-configuration.transmittedNormalRadicand))

/-- The canonical positive-normal-decay vector has the incident tangential phase vector as its
phase vector. -/
@[simp]
lemma phaseVector_positiveNormalDecayTransmittedWaveVector
    (configuration : PlanarDielectricWaveConfiguration) :
    configuration.positiveNormalDecayTransmittedWaveVector.phaseVector =
      configuration.interface.plane.tangentialProjection
        configuration.incident.waveVector.phaseVector := by
  rw [configuration.positiveNormalDecayTransmittedWaveVector_eq_ofPhaseAttenuation]
  simp

/-- The canonical positive-normal-decay vector has attenuation equal to the square-root rate
times the stored normal. -/
@[simp]
lemma attenuationVector_positiveNormalDecayTransmittedWaveVector
    (configuration : PlanarDielectricWaveConfiguration) :
    configuration.positiveNormalDecayTransmittedWaveVector.attenuationVector =
      Real.sqrt (-configuration.transmittedNormalRadicand) •
        configuration.interface.plane.normalVector := by
  rw [configuration.positiveNormalDecayTransmittedWaveVector_eq_ofPhaseAttenuation]
  simp

/-- The canonical positive-normal-decay vector has the incident tangential phase vector as its
complex tangential projection. -/
lemma hyperplaneTangentialProjection_positiveNormalDecayTransmittedWaveVector
    (configuration : PlanarDielectricWaveConfiguration) :
    hyperplaneTangentialProjection configuration.interface.plane
        configuration.positiveNormalDecayTransmittedWaveVector =
      ofReal (configuration.interface.plane.tangentialProjection
        configuration.incident.waveVector.phaseVector) := by
  rw [positiveNormalDecayTransmittedWaveVector,
    hyperplaneTangentialProjection_replaceHyperplaneNormalComponent]
  exact hyperplaneTangentialProjection_eq_ofReal_of_tangentialProjection_attenuationVector_eq_zero
    configuration.interface.plane (ofReal configuration.incident.waveVector.phaseVector)
      (by simp [OrientedAffineHyperplane.tangentialProjection,
        OrientedAffineHyperplane.normalComponent])

/-- The canonical positive-normal-decay vector has the selected negative-imaginary complex normal
component. -/
@[simp]
lemma hyperplaneNormalComponent_positiveNormalDecayTransmittedWaveVector
    (configuration : PlanarDielectricWaveConfiguration) :
    hyperplaneNormalComponent configuration.interface.plane
        configuration.positiveNormalDecayTransmittedWaveVector =
      -Complex.I *
        (Real.sqrt (-configuration.transmittedNormalRadicand) : ℂ) := by
  simp [positiveNormalDecayTransmittedWaveVector]

/-- The canonical positive-normal-decay phase vector is tangent to the interface. -/
lemma normalComponent_phaseVector_positiveNormalDecayTransmittedWaveVector
    (configuration : PlanarDielectricWaveConfiguration) :
    configuration.interface.plane.normalComponent
        configuration.positiveNormalDecayTransmittedWaveVector.phaseVector = 0 := by
  rw [configuration.phaseVector_positiveNormalDecayTransmittedWaveVector]
  exact configuration.interface.plane.normalComponent_tangentialProjection _

/-- The canonical attenuation vector has zero tangential projection. -/
lemma tangentialProjection_attenuationVector_positiveNormalDecayTransmittedWaveVector
    (configuration : PlanarDielectricWaveConfiguration) :
    configuration.interface.plane.tangentialProjection
        configuration.positiveNormalDecayTransmittedWaveVector.attenuationVector = 0 := by
  rw [configuration.attenuationVector_positiveNormalDecayTransmittedWaveVector,
    configuration.interface.plane.tangentialProjection_smul,
    configuration.interface.plane.tangentialProjection_normalVector]
  simp

/-- The canonical attenuation vector has oriented normal component equal to the square-root
normal rate. -/
lemma normalComponent_attenuationVector_positiveNormalDecayTransmittedWaveVector
    (configuration : PlanarDielectricWaveConfiguration) :
    configuration.interface.plane.normalComponent
        configuration.positiveNormalDecayTransmittedWaveVector.attenuationVector =
      Real.sqrt (-configuration.transmittedNormalRadicand) := by
  rw [configuration.attenuationVector_positiveNormalDecayTransmittedWaveVector]
  rw [OrientedAffineHyperplane.normalComponent, real_inner_smul_right,
    configuration.interface.plane.inner_normalVector_self, mul_one]

/-- A nonpositive transmitted normal radicand puts the canonical positive-normal-decay vector on
the positive-medium material shell at the incident angular frequency. -/
lemma bilinearDot_positiveNormalDecayTransmittedWaveVector_self
    (configuration : PlanarDielectricWaveConfiguration)
    (hRadicand : configuration.transmittedNormalRadicand ≤ 0) :
    bilinearDot configuration.positiveNormalDecayTransmittedWaveVector
        configuration.positiveNormalDecayTransmittedWaveVector =
      ((configuration.interface.positiveMedium.ε *
        configuration.interface.positiveMedium.μ *
        configuration.incident.angularFrequency ^ 2 : ℝ) : ℂ) := by
  have hSqrt :
      (Real.sqrt (-configuration.transmittedNormalRadicand) : ℂ) ^ 2 =
        (-configuration.transmittedNormalRadicand : ℂ) := by
    norm_cast
    exact Real.sq_sqrt (neg_nonneg.mpr hRadicand)
  have hNormalSquare :
      (-Complex.I *
          (Real.sqrt (-configuration.transmittedNormalRadicand) : ℂ)) ^ 2 =
        (configuration.transmittedNormalRadicand : ℂ) := by
    rw [mul_pow, hSqrt]
    simp
  rw [bilinearDot_self_eq_tangential_add_normal_sq,
    configuration.hyperplaneTangentialProjection_positiveNormalDecayTransmittedWaveVector,
    configuration.hyperplaneNormalComponent_positiveNormalDecayTransmittedWaveVector,
    bilinearDot_ofReal, real_inner_self_eq_norm_sq, hNormalSquare,
    transmittedNormalRadicand]
  push_cast
  ring

/-- A negative transmitted normal radicand makes the canonical attenuation vector point strictly
into the geometric positive side. -/
lemma positiveNormalDecayTransmittedWaveVector_isAttenuationDirectedInto
    (configuration : PlanarDielectricWaveConfiguration)
    (hRadicand : configuration.transmittedNormalRadicand < 0) :
    configuration.positiveNormalDecayTransmittedWaveVector.IsAttenuationDirectedInto
      configuration.interface.plane .positive := by
  rw [isAttenuationDirectedInto_positive_iff,
    configuration.normalComponent_attenuationVector_positiveNormalDecayTransmittedWaveVector]
  exact Real.sqrt_pos.2 (neg_pos.mpr hRadicand)

/-!

## B. Positive-normal decay data and spatial scaling

-/

/-- Proof-bearing positive-normal decay data for the canonical transmitted vector when its
normal radicand is negative. -/
noncomputable def positiveNormalDecayTransmittedData
    (configuration : PlanarDielectricWaveConfiguration)
    (hRadicand : configuration.transmittedNormalRadicand < 0) :
    PositiveNormalDecayWaveVector configuration.interface.plane.normal where
  tangentialWaveVector := configuration.interface.plane.tangentialProjection
    configuration.incident.waveVector.phaseVector
  tangential := by
    simpa [OrientedAffineHyperplane.normalComponent,
      OrientedAffineHyperplane.normalVector] using
      configuration.interface.plane.normalComponent_tangentialProjection
        configuration.incident.waveVector.phaseVector
  decayRate := Real.sqrt (-configuration.transmittedNormalRadicand)
  decayRate_pos := Real.sqrt_pos.2 (neg_pos.mpr hRadicand)

/-- The neutral decay data uses the interface's stored normal vector. -/
@[simp]
lemma positiveNormalDecayTransmittedData_normalVector
    (configuration : PlanarDielectricWaveConfiguration)
    (hRadicand : configuration.transmittedNormalRadicand < 0) :
    (configuration.positiveNormalDecayTransmittedData hRadicand).normalVector =
      configuration.interface.plane.normalVector := rfl

/-- The neutral decay data has the square-root decay rate. -/
@[simp]
lemma positiveNormalDecayTransmittedData_decayRate
    (configuration : PlanarDielectricWaveConfiguration)
    (hRadicand : configuration.transmittedNormalRadicand < 0) :
    (configuration.positiveNormalDecayTransmittedData hRadicand).decayRate =
      Real.sqrt (-configuration.transmittedNormalRadicand) := rfl

/-- The wave vector represented by the neutral decay data is the canonical transmitted vector. -/
lemma positiveNormalDecayTransmittedData_waveVector
    (configuration : PlanarDielectricWaveConfiguration)
    (hRadicand : configuration.transmittedNormalRadicand < 0) :
    (configuration.positiveNormalDecayTransmittedData hRadicand).waveVector =
      configuration.positiveNormalDecayTransmittedWaveVector := by
  rw [configuration.positiveNormalDecayTransmittedWaveVector_eq_ofPhaseAttenuation]
  rfl

/-- The canonical transmitted spatial factor has exact exponential positive-normal scaling at
the square-root decay rate. -/
lemma positiveNormalDecayTransmittedWaveVector_spatialFactor_vadd_normalVector
    (configuration : PlanarDielectricWaveConfiguration)
    (hRadicand : configuration.transmittedNormalRadicand < 0)
    (u : ℝ) (x : Space) :
    configuration.positiveNormalDecayTransmittedWaveVector.spatialFactor
        (u • configuration.interface.plane.normalVector +ᵥ x) =
      (Real.exp
          (-Real.sqrt (-configuration.transmittedNormalRadicand) * u) : ℂ) *
        configuration.positiveNormalDecayTransmittedWaveVector.spatialFactor x := by
  simpa only [configuration.positiveNormalDecayTransmittedData_normalVector hRadicand,
    configuration.positiveNormalDecayTransmittedData_decayRate hRadicand,
    configuration.positiveNormalDecayTransmittedData_waveVector hRadicand] using
    (configuration.positiveNormalDecayTransmittedData hRadicand).spatialFactor_vadd u x

/-- The canonical transmitted spatial factor tends to zero along increasing positive-side depth.

This is global spatial-factor decay from an arbitrary base point, not one-sided support. -/
lemma positiveNormalDecayTransmittedWaveVector_tendsto_spatialFactor_vadd_normalVector_atTop
    (configuration : PlanarDielectricWaveConfiguration)
    (hRadicand : configuration.transmittedNormalRadicand < 0) (x : Space) :
    Filter.Tendsto
      (fun u : ℝ ↦ configuration.positiveNormalDecayTransmittedWaveVector.spatialFactor
        (u • configuration.interface.plane.normalVector +ᵥ x))
      Filter.atTop (nhds 0) := by
  simpa only [configuration.positiveNormalDecayTransmittedData_normalVector hRadicand,
    configuration.positiveNormalDecayTransmittedData_waveVector hRadicand] using
    (configuration.positiveNormalDecayTransmittedData hRadicand).tendsto_spatialFactor_vadd_atTop x

/-!

## C. Existence and uniqueness above the critical sine threshold

-/

/-- A complex wave vector realizes positive-normal-decay transmitted carrier geometry when it
preserves the incident complex tangential projection, lies on the positive-medium material shell
at the incident frequency, has zero tangential attenuation, and points in attenuation into the
positive side.

The last condition selects a spatial-decay direction only. This predicate assigns no electric
amplitude, transversality, Maxwell, ray, group-velocity, outgoing, total-internal-reflection,
irradiance, or power meaning. -/
def IsPositiveNormalDecayTransmittedWaveVector
    (configuration : PlanarDielectricWaveConfiguration)
    (waveVector : ComplexWaveVector 3) : Prop :=
  hyperplaneTangentialProjection configuration.interface.plane waveVector =
      hyperplaneTangentialProjection configuration.interface.plane
        configuration.incident.waveVector ∧
    bilinearDot waveVector waveVector =
      ((configuration.interface.positiveMedium.ε *
        configuration.interface.positiveMedium.μ *
        configuration.incident.angularFrequency ^ 2 : ℝ) : ℂ) ∧
    configuration.interface.plane.tangentialProjection waveVector.attenuationVector = 0 ∧
    waveVector.IsAttenuationDirectedInto configuration.interface.plane .positive

namespace IsPositiveNormalDecayTransmittedWaveVector

variable {configuration : PlanarDielectricWaveConfiguration}
  {waveVector : ComplexWaveVector 3}

/-- A positive-normal-decay transmitted specification forces zero incident tangential attenuation
through its common complex tangential projection. -/
lemma incidentTangentialAttenuation_eq_zero
    (h : configuration.IsPositiveNormalDecayTransmittedWaveVector waveVector) :
    configuration.interface.plane.tangentialProjection
      configuration.incident.waveVector.attenuationVector = 0 := by
  have hAttenuation := congrArg ComplexWaveVector.attenuationVector h.1
  rw [attenuationVector_hyperplaneTangentialProjection,
    attenuationVector_hyperplaneTangentialProjection, h.2.2.1] at hAttenuation
  exact hAttenuation.symm

/-- The normal component of every specified positive-normal-decay transmitted wave vector squares
to the real transmitted normal radicand. -/
lemma hyperplaneNormalComponent_sq_eq_transmittedNormalRadicand
    (h : configuration.IsPositiveNormalDecayTransmittedWaveVector waveVector) :
    hyperplaneNormalComponent configuration.interface.plane waveVector ^ 2 =
      (configuration.transmittedNormalRadicand : ℂ) :=
  configuration.hyperplaneNormalComponent_sq_eq_transmittedNormalRadicand_of_tangentialProjection_eq
    waveVector h.1 h.2.1 h.incidentTangentialAttenuation_eq_zero

/-- Every specified positive-normal-decay transmitted wave vector forces a negative radicand,
zero phase normal component, and the selected negative-imaginary normal root. -/
lemma normalRoot_data
    (h : configuration.IsPositiveNormalDecayTransmittedWaveVector waveVector) :
    configuration.transmittedNormalRadicand < 0 ∧
      configuration.interface.plane.normalComponent waveVector.phaseVector = 0 ∧
      hyperplaneNormalComponent configuration.interface.plane waveVector =
        -Complex.I *
          (Real.sqrt (-configuration.transmittedNormalRadicand) : ℂ) := by
  simpa using normalRoot_data_of_sq_eq_real_of_isAttenuationDirectedInto
    configuration.interface.plane waveVector configuration.transmittedNormalRadicand
      .positive h.hyperplaneNormalComponent_sq_eq_transmittedNormalRadicand h.2.2.2

/-- Every wave vector satisfying the positive-normal-decay transmitted specification equals the
canonical construction. -/
lemma eq_positiveNormalDecayTransmittedWaveVector
    (h : configuration.IsPositiveNormalDecayTransmittedWaveVector waveVector) :
    waveVector = configuration.positiveNormalDecayTransmittedWaveVector := by
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
          configuration.positiveNormalDecayTransmittedWaveVector :=
        configuration.hyperplaneTangentialProjection_positiveNormalDecayTransmittedWaveVector.symm
  · simpa using h.normalRoot_data.2.2

/-- Every specified positive-normal-decay transmitted wave vector has the canonical tangential
phase vector and positive normal attenuation vector. -/
lemma phaseAttenuation_data
    (h : configuration.IsPositiveNormalDecayTransmittedWaveVector waveVector) :
    waveVector.phaseVector = configuration.interface.plane.tangentialProjection
        configuration.incident.waveVector.phaseVector ∧
      waveVector.attenuationVector =
        Real.sqrt (-configuration.transmittedNormalRadicand) •
          configuration.interface.plane.normalVector := by
  rw [h.eq_positiveNormalDecayTransmittedWaveVector]
  exact ⟨configuration.phaseVector_positiveNormalDecayTransmittedWaveVector,
    configuration.attenuationVector_positiveNormalDecayTransmittedWaveVector⟩

end IsPositiveNormalDecayTransmittedWaveVector

/-- Zero incident tangential attenuation and a negative transmitted normal radicand prove the
canonical positive-normal-decay transmitted wave-vector specification. -/
lemma positiveNormalDecayTransmittedWaveVector_spec_of_radicand_neg
    (configuration : PlanarDielectricWaveConfiguration)
    (hIncidentTangentialAttenuation :
      configuration.interface.plane.tangentialProjection
        configuration.incident.waveVector.attenuationVector = 0)
    (hRadicand : configuration.transmittedNormalRadicand < 0) :
    configuration.IsPositiveNormalDecayTransmittedWaveVector
      configuration.positiveNormalDecayTransmittedWaveVector := by
  refine ⟨?_,
    configuration.bilinearDot_positiveNormalDecayTransmittedWaveVector_self hRadicand.le,
    configuration.tangentialProjection_attenuationVector_positiveNormalDecayTransmittedWaveVector,
    configuration.positiveNormalDecayTransmittedWaveVector_isAttenuationDirectedInto hRadicand⟩
  rw [configuration.hyperplaneTangentialProjection_positiveNormalDecayTransmittedWaveVector]
  exact
    (hyperplaneTangentialProjection_eq_ofReal_of_tangentialProjection_attenuationVector_eq_zero
      configuration.interface.plane configuration.incident.waveVector
        hIncidentTangentialAttenuation).symm

/-- With zero incident tangential attenuation, a negative transmitted normal radicand is
equivalent to unique existence of the positive-normal-decay transmitted wave vector. -/
lemma transmittedNormalRadicand_lt_zero_iff_existsUnique_isPositiveNormalDecayTransmittedWaveVector
    (configuration : PlanarDielectricWaveConfiguration)
    (hIncidentTangentialAttenuation :
      configuration.interface.plane.tangentialProjection
        configuration.incident.waveVector.attenuationVector = 0) :
    configuration.transmittedNormalRadicand < 0 ↔
      ∃! waveVector,
        configuration.IsPositiveNormalDecayTransmittedWaveVector waveVector := by
  constructor
  · intro hRadicand
    refine ⟨configuration.positiveNormalDecayTransmittedWaveVector,
      positiveNormalDecayTransmittedWaveVector_spec_of_radicand_neg
        configuration hIncidentTangentialAttenuation hRadicand, ?_⟩
    intro waveVector hWaveVector
    exact hWaveVector.eq_positiveNormalDecayTransmittedWaveVector
  · rintro ⟨waveVector, hWaveVector, -⟩
    exact hWaveVector.normalRoot_data.1

/-- Under incident material dispersion, zero whole incident attenuation, and strict
sine-supercritical incidence, the canonical construction satisfies the positive-normal-decay
transmitted wave-vector specification. -/
lemma positiveNormalDecayTransmittedWaveVector_spec
    (configuration : PlanarDielectricWaveConfiguration)
    (hIncidentDispersion : configuration.incident.IsDispersionMatched
      configuration.interface.negativeMedium)
    (hIncidentAttenuation : configuration.incident.waveVector.attenuationVector = 0)
    (hSupercritical : configuration.IsSupercriticalPhaseIncidence) :
    configuration.IsPositiveNormalDecayTransmittedWaveVector
      configuration.positiveNormalDecayTransmittedWaveVector := by
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
    positiveNormalDecayTransmittedWaveVector_spec_of_radicand_neg
      configuration hIncidentTangentialAttenuation hRadicand

/-- Strict sine-supercritical incidence gives a unique positive-normal-decay transmitted wave
vector. -/
lemma existsUnique_isPositiveNormalDecayTransmittedWaveVector
    (configuration : PlanarDielectricWaveConfiguration)
    (hIncidentDispersion : configuration.incident.IsDispersionMatched
      configuration.interface.negativeMedium)
    (hIncidentAttenuation : configuration.incident.waveVector.attenuationVector = 0)
    (hSupercritical : configuration.IsSupercriticalPhaseIncidence) :
    ∃! waveVector,
      configuration.IsPositiveNormalDecayTransmittedWaveVector waveVector := by
  refine ⟨configuration.positiveNormalDecayTransmittedWaveVector,
    configuration.positiveNormalDecayTransmittedWaveVector_spec
      hIncidentDispersion hIncidentAttenuation hSupercritical, ?_⟩
  intro waveVector hWaveVector
  exact hWaveVector.eq_positiveNormalDecayTransmittedWaveVector

/-- Under negative-medium incident dispersion and zero whole incident attenuation, strict
sine-supercritical incidence is equivalent to unique existence of the positive-normal-decay
transmitted wave vector. -/
lemma isSupercriticalPhaseIncidence_iff_existsUnique_isPositiveNormalDecayTransmittedWaveVector
    (configuration : PlanarDielectricWaveConfiguration)
    (hIncidentDispersion : configuration.incident.IsDispersionMatched
      configuration.interface.negativeMedium)
    (hIncidentAttenuation : configuration.incident.waveVector.attenuationVector = 0) :
    configuration.IsSupercriticalPhaseIncidence ↔
      ∃! waveVector,
        configuration.IsPositiveNormalDecayTransmittedWaveVector waveVector := by
  have hIncidentTangentialAttenuation :
      configuration.interface.plane.tangentialProjection
        configuration.incident.waveVector.attenuationVector = 0 := by
    rw [hIncidentAttenuation]
    simp [OrientedAffineHyperplane.tangentialProjection,
      OrientedAffineHyperplane.normalComponent]
  calc
    configuration.IsSupercriticalPhaseIncidence ↔
        configuration.transmittedNormalRadicand < 0 :=
      (configuration.transmittedNormalRadicand_lt_zero_iff_isSupercriticalPhaseIncidence
        hIncidentDispersion hIncidentAttenuation).symm
    _ ↔ ∃! waveVector,
        configuration.IsPositiveNormalDecayTransmittedWaveVector waveVector :=
      transmittedNormalRadicand_lt_zero_iff_existsUnique_isPositiveNormalDecayTransmittedWaveVector
        configuration hIncidentTangentialAttenuation

/-!

## D. Supplied-candidate wave-vector identification

-/

namespace IsElectricPhaseMatched

variable {configuration : PlanarDielectricWaveConfiguration}

/-- A supplied phase-matched, positive-medium-dispersive transmitted candidate with zero incident
tangential attenuation and positive-side attenuation direction satisfies the positive-normal-
decay transmitted wave-vector specification.

The direction is supplied rather than derived from the transmitted label and has no outgoing or
power-flow meaning. -/
lemma transmitted_isPositiveNormalDecayTransmittedWaveVector
    (h : configuration.IsElectricPhaseMatched)
    (hTransmittedDispersion : configuration.transmitted.IsDispersionMatched
      configuration.interface.positiveMedium)
    (hIncidentTangentialAttenuation :
      configuration.interface.plane.tangentialProjection
        configuration.incident.waveVector.attenuationVector = 0)
    (hDirection : configuration.transmitted.waveVector.IsAttenuationDirectedInto
      configuration.interface.plane .positive) :
    configuration.IsPositiveNormalDecayTransmittedWaveVector
      configuration.transmitted.waveVector := by
  refine ⟨h.1.2, ?_,
    h.transmitted_tangentialProjection_attenuationVector_eq_zero
      hIncidentTangentialAttenuation, hDirection⟩
  simpa only [IsDispersionMatched, h.1.1] using hTransmittedDispersion

/-- A supplied phase-matched, positive-medium-dispersive, attenuation-directed transmitted
candidate with zero incident tangential attenuation has the canonical positive-normal-decay wave
vector. -/
lemma transmitted_waveVector_eq_positiveNormalDecayTransmittedWaveVector
    (h : configuration.IsElectricPhaseMatched)
    (hTransmittedDispersion : configuration.transmitted.IsDispersionMatched
      configuration.interface.positiveMedium)
    (hIncidentTangentialAttenuation :
      configuration.interface.plane.tangentialProjection
        configuration.incident.waveVector.attenuationVector = 0)
    (hDirection : configuration.transmitted.waveVector.IsAttenuationDirectedInto
      configuration.interface.plane .positive) :
    configuration.transmitted.waveVector =
      configuration.positiveNormalDecayTransmittedWaveVector :=
  (h.transmitted_isPositiveNormalDecayTransmittedWaveVector hTransmittedDispersion
    hIncidentTangentialAttenuation hDirection).eq_positiveNormalDecayTransmittedWaveVector

/-- Under incident dispersion and zero whole incident attenuation, a supplied phase-matched,
positive-medium-dispersive, attenuation-directed transmitted candidate forces strict
sine-supercritical incidence. -/
lemma isSupercriticalPhaseIncidence_of_transmitted_isAttenuationDirectedInto
    (h : configuration.IsElectricPhaseMatched)
    (hIncidentDispersion : configuration.incident.IsDispersionMatched
      configuration.interface.negativeMedium)
    (hTransmittedDispersion : configuration.transmitted.IsDispersionMatched
      configuration.interface.positiveMedium)
    (hIncidentAttenuation : configuration.incident.waveVector.attenuationVector = 0)
    (hDirection : configuration.transmitted.waveVector.IsAttenuationDirectedInto
      configuration.interface.plane .positive) :
    configuration.IsSupercriticalPhaseIncidence := by
  have hIncidentTangentialAttenuation :
      configuration.interface.plane.tangentialProjection
        configuration.incident.waveVector.attenuationVector = 0 := by
    rw [hIncidentAttenuation]
    simp [OrientedAffineHyperplane.tangentialProjection,
      OrientedAffineHyperplane.normalComponent]
  have hWaveVector := h.transmitted_isPositiveNormalDecayTransmittedWaveVector
    hTransmittedDispersion hIncidentTangentialAttenuation hDirection
  exact (configuration.transmittedNormalRadicand_lt_zero_iff_isSupercriticalPhaseIncidence
    hIncidentDispersion hIncidentAttenuation).mp hWaveVector.normalRoot_data.1

end IsElectricPhaseMatched

end PlanarDielectricWaveConfiguration

end
end Optics
