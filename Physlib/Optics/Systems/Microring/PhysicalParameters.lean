/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Systems.Microring.AddDrop
public import Physlib.Optics.Systems.Microring.AllPass

/-!
# Physical parameters for fixed-carrier microrings

## i. Overview

This file separates physical propagation data from the reduced field parameters used by the
all-pass and add-drop microring networks. `PhysicalParameters` stores a round-trip geometric path
length, a power-attenuation coefficient per unit length, an effective index, and a wavelength. Its
field retention and phase lift are

`exp (-alpha * L / 2)` and `2 * pi * n_eff * L / lambda`.

The factor of two is explicit: `powerAttenuation = fieldAttenuation ^ 2`. Likewise,
`IsAmplitudeCoupling` constrains amplitudes by `t ^ 2 + k ^ 2 = 1`, whereas
`IsPowerCoupling` constrains the corresponding power fractions by `T + K = 1`.

The maps to `AllPass.Parameters` and `AddDrop.Parameters` follow the target definitions at
`Physlib/Optics/Systems/Microring/AllPass.lean:81-105` and
`Physlib/Optics/Systems/Microring/AddDropNetwork.lean:80-151`. In particular, add-drop phase is
kept as a real lift and divided between two half arcs before coercion to `Real.Angle`; this fixes
the drop-port reference plane. The drop amplitude is therefore gauge- and reference-plane-
dependent. The all-pass through amplitude is insensitive to the sign of the quadrature cross
coefficient because the response at
`Physlib/Optics/Systems/Microring/AllPass.lean:165-173` contains its square.

This is a nondispersive fixed-carrier parameterization: effective index is held constant. It has
no bending-loss, coupling-length, material, thermal, nonlinear, bandwidth, causality, or group-
delay model. Power means normalized modal power, not electromagnetic power before a Poynting-
normalization bridge. The bridge in
`Physlib/Optics/HarmonicFlux/PropagatingModePower.lean:16-22,60-93` requires a finite,
common-frequency Maxwell family whose measured profiles are pairwise integrable, mutually flux-
orthogonal, and unit normalized. No such hypotheses are inferred here.

## ii. Key results

- `PhysicalParameters.fieldAttenuation_sq`: field retention squares to power retention.
- `PhysicalParameters.roundTripPhaseLift_eq_opticalPathLength`: phase from optical path length.
- `isPowerCoupling_sq_of_isAmplitudeCoupling`: amplitude coefficients square to power fractions.
- `AllPassPhysicalParameters.toParameters`: the physical one-bus parameter map.
- `AddDropPhysicalParameters.toParameters`: the physical two-bus parameter map.
- `AllPassPhysicalParameters.IsValid.toParameters`: N7 validity of the all-pass map.
- `AddDropPhysicalParameters.IsValid.toParameters`: N7 validity of the add-drop map.

## iii. Table of contents

- A. Field and power attenuation
- B. Amplitude and power coupling
- C. Physical propagation parameters
- D. One-bus and two-bus parameter maps

## iv. References

The DATE'14/SysCon'15 parameter audit is summarized in `HOL-CORPUS.md:188-249`; its source-
specific names and port dictionaries belong to the separate microring source bridge. This file
chooses `alpha` to be a power-attenuation coefficient, making the field factor the displayed
half-exponent by definition.
-/

@[expose] public section

namespace Optics

noncomputable section

namespace Microring

/-! ## A. Field and power attenuation -/

/-- A field-amplitude attenuation factor lies in the closed unit interval. -/
def IsFieldAttenuation (fieldFactor : ℝ) : Prop :=
  0 ≤ fieldFactor ∧ fieldFactor ≤ 1

/-- A power attenuation factor lies in the closed unit interval. -/
def IsPowerAttenuation (powerFactor : ℝ) : Prop :=
  0 ≤ powerFactor ∧ powerFactor ≤ 1

/-- Convert a field-amplitude attenuation factor to its power attenuation factor. -/
def fieldToPowerAttenuation (fieldFactor : ℝ) : ℝ :=
  fieldFactor ^ 2

/-- Convert a nonnegative power attenuation factor to its canonical field factor. -/
def powerToFieldAttenuation (powerFactor : ℝ) : ℝ :=
  Real.sqrt powerFactor

/-- Squaring a valid field attenuation produces a valid power attenuation. -/
lemma isPowerAttenuation_fieldToPower {fieldFactor : ℝ}
    (hField : IsFieldAttenuation fieldFactor) :
    IsPowerAttenuation (fieldToPowerAttenuation fieldFactor) := by
  constructor
  · exact sq_nonneg fieldFactor
  · rw [fieldToPowerAttenuation]
    nlinarith [hField.1, hField.2]

/-- The canonical field factor has square equal to its nonnegative power factor. -/
lemma powerToFieldAttenuation_sq {powerFactor : ℝ}
    (hPower : IsPowerAttenuation powerFactor) :
    powerToFieldAttenuation powerFactor ^ 2 = powerFactor := by
  exact Real.sq_sqrt hPower.1

/-- Taking the canonical square root of valid power attenuation gives valid field attenuation. -/
lemma isFieldAttenuation_powerToField {powerFactor : ℝ}
    (hPower : IsPowerAttenuation powerFactor) :
    IsFieldAttenuation (powerToFieldAttenuation powerFactor) := by
  constructor
  · exact Real.sqrt_nonneg powerFactor
  · simpa [powerToFieldAttenuation] using (Real.sqrt_le_one.mpr hPower.2)

/-! ## B. Amplitude and power coupling -/

/-- Ideal coupler amplitudes use nonnegative representatives and `t² + k² = 1`. -/
def IsAmplitudeCoupling (throughAmplitude crossAmplitude : ℝ) : Prop :=
  0 ≤ throughAmplitude ∧ 0 ≤ crossAmplitude ∧
    throughAmplitude ^ 2 + crossAmplitude ^ 2 = 1

/-- Ideal coupler power fractions are nonnegative and sum to one. -/
def IsPowerCoupling (throughPower crossPower : ℝ) : Prop :=
  0 ≤ throughPower ∧ 0 ≤ crossPower ∧ throughPower + crossPower = 1

/-- Squaring ideal amplitude coefficients produces ideal power fractions. -/
lemma isPowerCoupling_sq_of_isAmplitudeCoupling {throughAmplitude crossAmplitude : ℝ}
    (hCoupling : IsAmplitudeCoupling throughAmplitude crossAmplitude) :
    IsPowerCoupling (throughAmplitude ^ 2) (crossAmplitude ^ 2) := by
  exact ⟨sq_nonneg throughAmplitude, sq_nonneg crossAmplitude, hCoupling.2.2⟩

/-- Square roots of ideal power fractions produce canonical ideal amplitudes. -/
lemma isAmplitudeCoupling_sqrt_of_isPowerCoupling {throughPower crossPower : ℝ}
    (hCoupling : IsPowerCoupling throughPower crossPower) :
    IsAmplitudeCoupling (Real.sqrt throughPower) (Real.sqrt crossPower) := by
  refine ⟨Real.sqrt_nonneg throughPower, Real.sqrt_nonneg crossPower, ?_⟩
  rw [Real.sq_sqrt hCoupling.1, Real.sq_sqrt hCoupling.2.1]
  exact hCoupling.2.2

/-- The canonical amplitude conversion recovers both power fractions by explicit squares. -/
lemma sqrt_coupling_squares {throughPower crossPower : ℝ}
    (hCoupling : IsPowerCoupling throughPower crossPower) :
    Real.sqrt throughPower ^ 2 = throughPower ∧
      Real.sqrt crossPower ^ 2 = crossPower :=
  ⟨Real.sq_sqrt hCoupling.1, Real.sq_sqrt hCoupling.2.1⟩

/-- Through and cross field amplitudes for one ideal directional coupler. -/
structure CouplingParameters where
  /-- Same-arm field transmission amplitude. -/
  throughAmplitude : ℝ
  /-- Cross-arm field amplitude before the N7 quadrature phase. -/
  crossAmplitude : ℝ

/-- The N7 directional-coupler parameter selected by physical coupling data. -/
def CouplingParameters.toDirectionalCoupler (p : CouplingParameters) :
    DirectionalCoupler.Parameters where
  throughAmplitude := p.throughAmplitude
  crossAmplitude := p.crossAmplitude

/-- Physical coupling validity is the amplitude, rather than power-fraction, predicate. -/
def CouplingParameters.IsValid (p : CouplingParameters) : Prop :=
  IsAmplitudeCoupling p.throughAmplitude p.crossAmplitude

/-- Valid physical coupling data gives valid N7 directional-coupler parameters. -/
lemma CouplingParameters.IsValid.toDirectionalCoupler {p : CouplingParameters}
    (hp : p.IsValid) : p.toDirectionalCoupler.IsValid := by
  exact hp

/-- The power fractions associated to one physical coupler are the amplitude squares. -/
lemma CouplingParameters.IsValid.isPowerCoupling {p : CouplingParameters}
    (hp : p.IsValid) :
    IsPowerCoupling (p.throughAmplitude ^ 2) (p.crossAmplitude ^ 2) :=
  isPowerCoupling_sq_of_isAmplitudeCoupling hp

/-- The two-coordinate N7 arm mixer selected by physical coupling amplitudes.

This wraps `DirectionalCoupler.mixing` from
`Physlib/Optics/Components/DirectionalCoupler.lean:72-77`; it is the typed arm-mixer view, not
the full four-physical-port component topology.
-/
def CouplingParameters.toTwoPortScattering (p : CouplingParameters) :
    TwoPortScatteringTransform Unit Unit :=
  ({ toModeTransform := DirectionalCoupler.mixing p.toDirectionalCoupler Unit } :
    ScatteringMatrix (Unit ⊕ Unit)).toTwoPortScatteringTransform

/-! ## C. Physical propagation parameters -/

/-- Nondispersive fixed-carrier propagation data for one complete ring circulation. -/
structure PhysicalParameters where
  /-- Geometric path length traversed in one complete circulation. -/
  pathLength : ℝ
  /-- Power-attenuation coefficient per unit path length. -/
  powerAttenuationCoefficient : ℝ
  /-- Constant effective refractive index used at the selected carrier. -/
  effectiveIndex : ℝ
  /-- Vacuum wavelength of the selected carrier. -/
  wavelength : ℝ

/-- Valid physical propagation data has nonnegative length, attenuation, and effective index,
and strictly positive wavelength. -/
def PhysicalParameters.IsValid (p : PhysicalParameters) : Prop :=
  0 ≤ p.pathLength ∧ 0 ≤ p.powerAttenuationCoefficient ∧
    0 ≤ p.effectiveIndex ∧ 0 < p.wavelength

/-- The effective optical path length `n_eff * L` for one complete circulation. -/
def PhysicalParameters.opticalPathLength (p : PhysicalParameters) : ℝ :=
  p.effectiveIndex * p.pathLength

/-- The round-trip power-retention factor `exp (-alpha * L)`. -/
def PhysicalParameters.powerAttenuation (p : PhysicalParameters) : ℝ :=
  Real.exp (-p.powerAttenuationCoefficient * p.pathLength)

/-- The round-trip field-retention factor `exp (-alpha * L / 2)`. -/
def PhysicalParameters.fieldAttenuation (p : PhysicalParameters) : ℝ :=
  Real.exp (-p.powerAttenuationCoefficient * p.pathLength / 2)

/-- The nondispersive propagation constant `2 * pi * n_eff / lambda`. -/
def PhysicalParameters.propagationConstant (p : PhysicalParameters) : ℝ :=
  2 * Real.pi * p.effectiveIndex / p.wavelength

/-- The selected real lift `2 * pi * n_eff * L / lambda` of round-trip phase. -/
def PhysicalParameters.roundTripPhaseLift (p : PhysicalParameters) : ℝ :=
  p.propagationConstant * p.pathLength

/-- Round-trip phase modulo `2 * pi` for the one-bus propagation component. -/
def PhysicalParameters.roundTripPhase (p : PhysicalParameters) : Real.Angle :=
  ((p.roundTripPhaseLift : ℝ) : Real.Angle)

/-- The propagation constant times path length is the declared round-trip phase lift. -/
lemma PhysicalParameters.propagationConstant_mul_pathLength (p : PhysicalParameters) :
    p.propagationConstant * p.pathLength = p.roundTripPhaseLift := rfl

/-- Round-trip phase is `2 * pi` times optical path length divided by wavelength. -/
lemma PhysicalParameters.roundTripPhaseLift_eq_opticalPathLength (p : PhysicalParameters) :
    p.roundTripPhaseLift = 2 * Real.pi * p.opticalPathLength / p.wavelength := by
  rw [PhysicalParameters.roundTripPhaseLift, PhysicalParameters.propagationConstant,
    PhysicalParameters.opticalPathLength]
  ring

/-- The field-retention factor is strictly positive for every real parameter point. -/
lemma PhysicalParameters.fieldAttenuation_pos (p : PhysicalParameters) :
    0 < p.fieldAttenuation := by
  exact Real.exp_pos _

/-- The power-retention factor is strictly positive for every real parameter point. -/
lemma PhysicalParameters.powerAttenuation_pos (p : PhysicalParameters) :
    0 < p.powerAttenuation := by
  exact Real.exp_pos _

/-- The field factor squares exactly to the power factor, exposing the half exponent. -/
lemma PhysicalParameters.fieldAttenuation_sq (p : PhysicalParameters) :
    p.fieldAttenuation ^ 2 = p.powerAttenuation := by
  rw [PhysicalParameters.fieldAttenuation, PhysicalParameters.powerAttenuation, pow_two,
    ← Real.exp_add]
  congr 1
  ring

/-- Valid propagation data produces a valid field attenuation factor. -/
lemma PhysicalParameters.IsValid.isFieldAttenuation {p : PhysicalParameters}
    (hp : p.IsValid) : IsFieldAttenuation p.fieldAttenuation := by
  constructor
  · exact p.fieldAttenuation_pos.le
  · apply Real.exp_le_one_iff.mpr
    nlinarith [mul_nonneg hp.2.1 hp.1]

/-- Valid propagation data produces a valid power attenuation factor. -/
lemma PhysicalParameters.IsValid.isPowerAttenuation {p : PhysicalParameters}
    (hp : p.IsValid) : IsPowerAttenuation p.powerAttenuation := by
  constructor
  · exact p.powerAttenuation_pos.le
  · apply Real.exp_le_one_iff.mpr
    nlinarith [mul_nonneg hp.2.1 hp.1]

/-! ## D. One-bus and two-bus parameter maps -/

/-- Physical data for a one-bus all-pass microring. -/
structure AllPassPhysicalParameters where
  /-- Amplitude coefficients of the bus-ring directional coupler. -/
  coupling : CouplingParameters
  /-- Full-circulation physical propagation data. -/
  propagation : PhysicalParameters

/-- Physical validity for a one-bus ring. -/
def AllPassPhysicalParameters.IsValid (p : AllPassPhysicalParameters) : Prop :=
  p.coupling.IsValid ∧ p.propagation.IsValid

/-- Map one-bus physical data to the S2 all-pass field parameters. -/
def AllPassPhysicalParameters.toParameters (p : AllPassPhysicalParameters) :
    AllPass.Parameters where
  throughAmplitude := p.coupling.throughAmplitude
  crossAmplitude := p.coupling.crossAmplitude
  fieldAttenuation := p.propagation.fieldAttenuation
  roundTripPhase := p.propagation.roundTripPhase

/-- The one-bus map retains amplitudes and uses the derived field attenuation and phase. -/
lemma AllPassPhysicalParameters.toParameters_data (p : AllPassPhysicalParameters) :
    p.toParameters.throughAmplitude = p.coupling.throughAmplitude ∧
      p.toParameters.crossAmplitude = p.coupling.crossAmplitude ∧
      p.toParameters.fieldAttenuation = p.propagation.fieldAttenuation ∧
      p.toParameters.roundTripPhase = p.propagation.roundTripPhase :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Valid one-bus physical data gives valid S2/N7 all-pass parameters. -/
lemma AllPassPhysicalParameters.IsValid.toParameters {p : AllPassPhysicalParameters}
    (hp : p.IsValid) : p.toParameters.IsValid := by
  constructor
  · exact hp.1.toDirectionalCoupler
  · exact hp.2.isFieldAttenuation

/-- Physical data for a two-bus add-drop microring. -/
structure AddDropPhysicalParameters where
  /-- Amplitude coefficients of the input/through coupler. -/
  inputCoupling : CouplingParameters
  /-- Amplitude coefficients of the add/drop coupler. -/
  dropCoupling : CouplingParameters
  /-- Full-circulation physical propagation data shared by the symmetric half arcs. -/
  propagation : PhysicalParameters

/-- Physical validity for a two-bus add-drop ring. -/
def AddDropPhysicalParameters.IsValid (p : AddDropPhysicalParameters) : Prop :=
  p.inputCoupling.IsValid ∧ p.dropCoupling.IsValid ∧ p.propagation.IsValid

/-- Map two-bus physical data to the S2 add-drop field parameters.

The real phase lift is retained because `AddDrop.Parameters.halfArcPhase` divides it by two before
coercion to `Real.Angle`; this is the S2 drop-port reference-plane convention at
`Physlib/Optics/Systems/Microring/AddDropNetwork.lean:116-151`.
-/
def AddDropPhysicalParameters.toParameters (p : AddDropPhysicalParameters) :
    AddDrop.Parameters where
  inputThroughAmplitude := p.inputCoupling.throughAmplitude
  inputCrossAmplitude := p.inputCoupling.crossAmplitude
  dropThroughAmplitude := p.dropCoupling.throughAmplitude
  dropCrossAmplitude := p.dropCoupling.crossAmplitude
  fieldAttenuation := p.propagation.fieldAttenuation
  roundTripPhase := p.propagation.roundTripPhaseLift

/-- The two-bus map retains both couplers and the derived propagation data. -/
lemma AddDropPhysicalParameters.toParameters_data (p : AddDropPhysicalParameters) :
    p.toParameters.inputThroughAmplitude = p.inputCoupling.throughAmplitude ∧
      p.toParameters.inputCrossAmplitude = p.inputCoupling.crossAmplitude ∧
      p.toParameters.dropThroughAmplitude = p.dropCoupling.throughAmplitude ∧
      p.toParameters.dropCrossAmplitude = p.dropCoupling.crossAmplitude ∧
      p.toParameters.fieldAttenuation = p.propagation.fieldAttenuation ∧
      p.toParameters.roundTripPhase = p.propagation.roundTripPhaseLift :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Valid two-bus physical data gives valid S2/N7 add-drop parameters. -/
lemma AddDropPhysicalParameters.IsValid.toParameters {p : AddDropPhysicalParameters}
    (hp : p.IsValid) : p.toParameters.IsValid := by
  have hField := hp.2.2.isFieldAttenuation
  refine ⟨hp.1.toDirectionalCoupler, hp.2.1.toDirectionalCoupler,
    hField.1, hField.2, ?_, ?_⟩
  all_goals
    exact ⟨Real.sqrt_nonneg _, (Real.sqrt_le_one.mpr hField.2)⟩

end Microring

end

end Optics
