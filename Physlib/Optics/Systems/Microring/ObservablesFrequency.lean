/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.ParameterizedResponse
public import Physlib.Optics.Systems.Microring.ObservablesPower

/-!
# Parameterized add-drop response and free spectral range

## i. Overview

This file lifts the explicit add-drop ring to N5F and states frequency observables only through
`ParameterizedNetlist.response` on `responseDomain`. Those definitions and their two gates are at
`Physlib/Optics/Network/ParameterizedResponse.lean:436-472,499-518`. No result uses the totalized
`ParameterizedNetlist.unguardedResponse`.

The stored validity predicate is conservatively the validity of the complete ring at that
frequency for each component label. Thus N5F's componentwise validity domain is exactly the
`AddDrop.Parameters.IsValid` domain, not merely validity of the projected square-root arcs.

Free spectral range is proved under an explicit nondispersive group-index model: group index,
round-trip length, and propagation speed are positive constants, and phase is affine in angular
frequency with constant group delay `n_g L / v`. The result is periodicity of through and drop
powers. No drop-amplitude periodicity is claimed; the symmetric half-arc reference-plane choice is
retained rather than quotienting field phase. The model makes no claim for a
frequency-dependent group index, dispersion, linewidth, quality factor, group delay inferred from
the response, material realization, or validity outside `responseDomain`. The affine frequency
model makes no time-domain or causality inference. It adds no radiation, bend-scattering,
absorption, or other omitted-loss channel, and proves no reciprocity statement.

## ii. Key results

- `AddDrop.parameterizedNetlist_response_through`: pointwise N5F through response.
- `AddDrop.parameterizedNetlist_response_drop`: pointwise N5F drop response.
- `AddDrop.parameterizedNetlist_response_through_power_eq_closedForm`: pointwise power response.
- `AddDrop.NondispersiveGroupIndexModel.angularFSR`: the angular-frequency FSR.
- `AddDrop.NondispersiveGroupIndexModel.frequencyFSR`: the ordinary-frequency FSR.
- `AddDrop.NondispersiveGroupIndexModel.nondispersive_throughPower_periodic`: through power.
- `AddDrop.NondispersiveGroupIndexModel.nondispersive_dropPower_periodic`: drop power.

## iii. Table of contents

- A. N5F parameterized compilation and response
- B. Nondispersive group-index model
- C. Proof-gated free-spectral-range periodicity

## iv. References

The response-domain definition and evaluation theorem are quoted above. The nondispersive model
and its FSR derivation are Physlib-original system declarations.
-/

@[expose] public section

namespace Optics

noncomputable section

namespace AddDrop

/-!
## A. N5F parameterized compilation and response
-/

/-- A parameterized N7 component family obtained from frequency-indexed ring parameters.

Each stored component predicate uses complete-ring validity. This is conservative component data:
it does not assert that one component's physical law depends on other components.
-/
def parameterizedComponents (parametersAt : ℝ → Parameters) :
    ParameterizedComponentFamily ℝ where
  Component := Component
  portFamily := componentPortFamily
  scattering := fun frequency => componentScattering (parametersAt frequency)
  IsValidAt := fun _ frequency => (parametersAt frequency).IsValid

/-- The explicit ring wiring applied uniformly to the parameterized component family. -/
def parameterizedNetlist (parametersAt : ℝ → Parameters) : ParameterizedNetlist ℝ where
  components := parameterizedComponents parametersAt
  Connection := Connection
  connections := connections (parametersAt 0)

/-- Pointwise compilation recovers the fixed-parameter explicit add-drop netlist. -/
lemma parameterizedNetlist_compile (parametersAt : ℝ → Parameters) (frequency : ℝ) :
    (parameterizedNetlist parametersAt).compile frequency = netlist (parametersAt frequency) := by
  rfl

/-- Parameterized aggregate add-drop channels are finite. -/
noncomputable instance parameterizedChannelFintype (parametersAt : ℝ → Parameters) :
    Fintype (parameterizedNetlist parametersAt).Channel := by
  change Fintype (netlist (parametersAt 0)).Channel
  exact channelFintype (parametersAt 0)

/-- Parameterized connected add-drop channels are finite. -/
noncomputable instance parameterizedConnectedChannelFintype (parametersAt : ℝ → Parameters) :
    Fintype (parameterizedNetlist parametersAt).ConnectedChannel := by
  change Fintype (netlist (parametersAt 0)).ConnectedChannel
  exact connectedChannelFintype (parametersAt 0)

/-- N5F response-domain membership is exactly the scalar solve gate together with complete-ring
validity at that frequency. -/
lemma mem_parameterizedNetlist_responseDomain_iff (parametersAt : ℝ → Parameters)
    (frequency : ℝ) :
    frequency ∈ (parameterizedNetlist parametersAt).responseDomain ↔
      (parametersAt frequency).HasNonzeroDenominator ∧ (parametersAt frequency).IsValid := by
  rw [ParameterizedNetlist.mem_responseDomain_iff]
  constructor
  · rintro ⟨hWellPosed, hValid⟩
    constructor
    · change (netlist (parametersAt frequency)).IsWellPosed at hWellPosed
      exact (isWellPosed_iff (parametersAt frequency)).mp hWellPosed
    · exact hValid Component.inputCoupler
  · rintro ⟨hDenominator, hValid⟩
    constructor
    · change (netlist (parametersAt frequency)).IsWellPosed
      exact (isWellPosed_iff (parametersAt frequency)).mpr hDenominator
    · intro component
      exact hValid

/-- The proof-gated pointwise N5F input-to-through response is the N5-derived transfer. -/
lemma parameterizedNetlist_response_through (parametersAt : ℝ → Parameters)
    {frequency : ℝ} (hFrequency :
      frequency ∈ (parameterizedNetlist parametersAt).responseDomain) :
    (parameterizedNetlist parametersAt).response hFrequency
        (Outgoing.mk (throughChannel (parametersAt frequency)))
        (Incident.mk (inputChannel (parametersAt frequency))) =
      throughTransfer (parametersAt frequency) := by
  have hDomain :=
    (mem_parameterizedNetlist_responseDomain_iff parametersAt frequency).mp hFrequency
  change (netlist (parametersAt frequency)).responseTransform hFrequency.1
      (Outgoing.mk (throughChannel (parametersAt frequency)))
      (Incident.mk (inputChannel (parametersAt frequency))) = _
  rw [show hFrequency.1 =
      isWellPosed_of_hasNonzeroDenominator (parametersAt frequency) hDomain.1 from
    Subsingleton.elim _ _]
  exact responseTransform_entry_through_input (parametersAt frequency) hDomain.1

/-- The proof-gated pointwise N5F input-to-drop response is the N5-derived transfer. -/
lemma parameterizedNetlist_response_drop (parametersAt : ℝ → Parameters)
    {frequency : ℝ} (hFrequency :
      frequency ∈ (parameterizedNetlist parametersAt).responseDomain) :
    (parameterizedNetlist parametersAt).response hFrequency
        (Outgoing.mk (dropChannel (parametersAt frequency)))
        (Incident.mk (inputChannel (parametersAt frequency))) =
      dropTransfer (parametersAt frequency) := by
  have hDomain :=
    (mem_parameterizedNetlist_responseDomain_iff parametersAt frequency).mp hFrequency
  change (netlist (parametersAt frequency)).responseTransform hFrequency.1
      (Outgoing.mk (dropChannel (parametersAt frequency)))
      (Incident.mk (inputChannel (parametersAt frequency))) = _
  rw [show hFrequency.1 =
      isWellPosed_of_hasNonzeroDenominator (parametersAt frequency) hDomain.1 from
    Subsingleton.elim _ _]
  exact responseTransform_entry_drop_input (parametersAt frequency) hDomain.1

/-- Squared modulus of the proof-gated pointwise N5F through response is `throughPower`. -/
lemma parameterizedNetlist_response_through_power (parametersAt : ℝ → Parameters)
    {frequency : ℝ} (hFrequency :
      frequency ∈ (parameterizedNetlist parametersAt).responseDomain) :
    Complex.normSq
        ((parameterizedNetlist parametersAt).response hFrequency
          (Outgoing.mk (throughChannel (parametersAt frequency)))
          (Incident.mk (inputChannel (parametersAt frequency)))) =
      throughPower (parametersAt frequency) := by
  rw [parameterizedNetlist_response_through]
  rfl

/-- Squared modulus of the proof-gated pointwise N5F drop response is `dropPower`. -/
lemma parameterizedNetlist_response_drop_power (parametersAt : ℝ → Parameters)
    {frequency : ℝ} (hFrequency :
      frequency ∈ (parameterizedNetlist parametersAt).responseDomain) :
    Complex.normSq
        ((parameterizedNetlist parametersAt).response hFrequency
          (Outgoing.mk (dropChannel (parametersAt frequency)))
          (Incident.mk (inputChannel (parametersAt frequency)))) =
      dropPower (parametersAt frequency) := by
  rw [parameterizedNetlist_response_drop]
  rfl

/-- The proof-gated pointwise N5F through-response power has the exact scalar closed form. -/
lemma parameterizedNetlist_response_through_power_eq_closedForm
    (parametersAt : ℝ → Parameters) {frequency : ℝ}
    (hFrequency : frequency ∈ (parameterizedNetlist parametersAt).responseDomain) :
    Complex.normSq
        ((parameterizedNetlist parametersAt).response hFrequency
          (Outgoing.mk (throughChannel (parametersAt frequency)))
          (Incident.mk (inputChannel (parametersAt frequency)))) =
      (parametersAt frequency).throughPowerNumerator /
        (parametersAt frequency).powerDenominator := by
  have hDomain :=
    (mem_parameterizedNetlist_responseDomain_iff parametersAt frequency).mp hFrequency
  rw [parameterizedNetlist_response_through_power,
    throughPower_eq_closedForm _ hDomain.2.1.isUnitary
      hDomain.2.fieldAttenuation_nonneg hDomain.1]

/-- The proof-gated pointwise N5F drop-response power has the exact scalar closed form. -/
lemma parameterizedNetlist_response_drop_power_eq_closedForm
    (parametersAt : ℝ → Parameters) {frequency : ℝ}
    (hFrequency : frequency ∈ (parameterizedNetlist parametersAt).responseDomain) :
    Complex.normSq
        ((parameterizedNetlist parametersAt).response hFrequency
          (Outgoing.mk (dropChannel (parametersAt frequency)))
          (Incident.mk (inputChannel (parametersAt frequency)))) =
      (parametersAt frequency).dropPowerNumerator /
        (parametersAt frequency).powerDenominator := by
  have hDomain :=
    (mem_parameterizedNetlist_responseDomain_iff parametersAt frequency).mp hFrequency
  rw [parameterizedNetlist_response_drop_power,
    dropPower_eq_closedForm _ hDomain.2.fieldAttenuation_nonneg]

/-!
## B. Nondispersive group-index model
-/

/-- A nondispersive round-trip model with constant group index and affine angular-frequency
phase. -/
structure NondispersiveGroupIndexModel where
  /-- Fixed coupler and attenuation data; its stored phase is the affine phase offset. -/
  base : Parameters
  /-- Constant group index over the frequency interval under consideration. -/
  groupIndex : ℝ
  /-- Complete round-trip geometric path length before multiplication by group index. -/
  roundTripLength : ℝ
  /-- Positive propagation speed used to convert group optical length to delay. -/
  propagationSpeed : ℝ
  /-- The group index is positive. -/
  groupIndex_pos : 0 < groupIndex
  /-- The complete round-trip length is positive. -/
  roundTripLength_pos : 0 < roundTripLength
  /-- The propagation speed is positive. -/
  propagationSpeed_pos : 0 < propagationSpeed

namespace NondispersiveGroupIndexModel

/-- The constant round-trip group delay `n_g L / v`. -/
def groupDelay (model : NondispersiveGroupIndexModel) : ℝ :=
  model.groupIndex * model.roundTripLength / model.propagationSpeed

/-- The group delay is positive under the stored geometric hypotheses. -/
lemma groupDelay_pos (model : NondispersiveGroupIndexModel) : 0 < model.groupDelay :=
  div_pos (mul_pos model.groupIndex_pos model.roundTripLength_pos)
    model.propagationSpeed_pos

/-- The positive group delay is nonzero. -/
lemma groupDelay_ne_zero (model : NondispersiveGroupIndexModel) : model.groupDelay ≠ 0 :=
  model.groupDelay_pos.ne'

/-- The angular-frequency free spectral range `2 pi / tau_g`. -/
def angularFSR (model : NondispersiveGroupIndexModel) : ℝ :=
  2 * Real.pi / model.groupDelay

/-- The angular-frequency FSR is positive. -/
lemma angularFSR_pos (model : NondispersiveGroupIndexModel) : 0 < model.angularFSR :=
  div_pos (mul_pos (by norm_num) Real.pi_pos) model.groupDelay_pos

/-- The angular-frequency FSR in terms of constant group index, path length, and speed. -/
theorem angularFSR_eq (model : NondispersiveGroupIndexModel) :
    model.angularFSR =
      2 * Real.pi * model.propagationSpeed /
        (model.groupIndex * model.roundTripLength) := by
  rw [angularFSR, groupDelay]
  field_simp [model.propagationSpeed_pos.ne', model.groupIndex_pos.ne',
    model.roundTripLength_pos.ne']

/-- The ordinary-frequency free spectral range, obtained from angular FSR by division by
`2 pi`. -/
def frequencyFSR (model : NondispersiveGroupIndexModel) : ℝ :=
  model.angularFSR / (2 * Real.pi)

/-- The ordinary-frequency FSR is positive. -/
lemma frequencyFSR_pos (model : NondispersiveGroupIndexModel) : 0 < model.frequencyFSR :=
  div_pos model.angularFSR_pos (mul_pos (by norm_num) Real.pi_pos)

/-- The ordinary-frequency FSR in the nondispersive group-index model is `v / (n_g L)`. -/
theorem frequencyFSR_eq (model : NondispersiveGroupIndexModel) :
    model.frequencyFSR =
      model.propagationSpeed / (model.groupIndex * model.roundTripLength) := by
  rw [frequencyFSR, model.angularFSR_eq]
  field_simp [Real.pi_ne_zero, model.groupIndex_pos.ne', model.roundTripLength_pos.ne']

/-- Ring parameters at angular frequency `omega`, with only the affine phase changed. -/
def parametersAt (model : NondispersiveGroupIndexModel) (angularFrequency : ℝ) : Parameters :=
  { model.base with
    roundTripPhase := model.base.roundTripPhase + angularFrequency * model.groupDelay }

/-- The N5F ring network induced by the nondispersive parameter law. -/
def network (model : NondispersiveGroupIndexModel) : ParameterizedNetlist ℝ :=
  parameterizedNetlist model.parametersAt

/-- The nondispersive model's aggregate channels are finite. -/
noncomputable instance networkChannelFintype (model : NondispersiveGroupIndexModel) :
    Fintype model.network.Channel := by
  change Fintype (parameterizedNetlist model.parametersAt).Channel
  infer_instance

/-- The nondispersive model's connected channels are finite. -/
noncomputable instance networkConnectedChannelFintype
    (model : NondispersiveGroupIndexModel) : Fintype model.network.ConnectedChannel := by
  change Fintype (parameterizedNetlist model.parametersAt).ConnectedChannel
  infer_instance

/-- One angular FSR advances the affine round-trip phase by exactly `2 pi`. -/
lemma parametersAt_add_angularFSR_roundTripPhase
    (model : NondispersiveGroupIndexModel) (angularFrequency : ℝ) :
    (model.parametersAt (angularFrequency + model.angularFSR)).roundTripPhase =
      (model.parametersAt angularFrequency).roundTripPhase + 2 * Real.pi := by
  rw [parametersAt, parametersAt, angularFSR]
  dsimp only
  field_simp [model.groupDelay_ne_zero]
  ring

/-- One angular FSR leaves the cosine of the round-trip phase unchanged. -/
lemma cos_parametersAt_add_angularFSR (model : NondispersiveGroupIndexModel)
    (angularFrequency : ℝ) :
    Real.cos (model.parametersAt (angularFrequency + model.angularFSR)).roundTripPhase =
      Real.cos (model.parametersAt angularFrequency).roundTripPhase := by
  rw [model.parametersAt_add_angularFSR_roundTripPhase, Real.cos_add_two_pi]

/-- One angular FSR leaves the complete round-trip phase factor unchanged. -/
lemma phaseFactor_parametersAt_add_angularFSR (model : NondispersiveGroupIndexModel)
    (angularFrequency : ℝ) :
    (model.parametersAt (angularFrequency + model.angularFSR)).phaseFactor =
      (model.parametersAt angularFrequency).phaseFactor := by
  rw [Parameters.phaseFactor_eq_cos_sub_sin_mul_I,
    Parameters.phaseFactor_eq_cos_sub_sin_mul_I,
    model.parametersAt_add_angularFSR_roundTripPhase,
    Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- The frequency law changes only phase, so complete-ring validity is frequency-independent. -/
lemma parametersAt_isValid_iff (model : NondispersiveGroupIndexModel)
    (angularFrequency : ℝ) :
    (model.parametersAt angularFrequency).IsValid ↔ model.base.IsValid := by
  rfl

/-- Under nonnegative field attenuation, one angular FSR leaves the complete round-trip
coefficient unchanged. -/
lemma roundTripCoefficient_parametersAt_add_angularFSR
    (model : NondispersiveGroupIndexModel) (angularFrequency : ℝ)
    (hAttenuation : 0 ≤ model.base.fieldAttenuation) :
    (model.parametersAt
        (angularFrequency + model.angularFSR)).roundTripCoefficient =
      (model.parametersAt angularFrequency).roundTripCoefficient := by
  rw [(model.parametersAt
      (angularFrequency + model.angularFSR)).roundTripCoefficient_eq_field_mul_phaseFactor
        (by simpa only [parametersAt] using hAttenuation),
    (model.parametersAt angularFrequency).roundTripCoefficient_eq_field_mul_phaseFactor
      (by simpa only [parametersAt] using hAttenuation),
    model.phaseFactor_parametersAt_add_angularFSR angularFrequency]
  rfl

/-- Under nonnegative field attenuation, one angular FSR leaves the feedback denominator
unchanged. -/
lemma denominator_parametersAt_add_angularFSR
    (model : NondispersiveGroupIndexModel) (angularFrequency : ℝ)
    (hAttenuation : 0 ≤ model.base.fieldAttenuation) :
    (model.parametersAt (angularFrequency + model.angularFSR)).denominator =
      (model.parametersAt angularFrequency).denominator := by
  rw [Parameters.denominator, Parameters.denominator,
    Parameters.loopGain, Parameters.loopGain,
    model.roundTripCoefficient_parametersAt_add_angularFSR angularFrequency hAttenuation]
  rfl

/-- Membership in the physical N5F response domain propagates by one angular FSR. -/
lemma add_angularFSR_mem_responseDomain (model : NondispersiveGroupIndexModel)
    {angularFrequency : ℝ} (hFrequency : angularFrequency ∈ model.network.responseDomain) :
    angularFrequency + model.angularFSR ∈ model.network.responseDomain := by
  unfold network at hFrequency ⊢
  rw [mem_parameterizedNetlist_responseDomain_iff] at hFrequency ⊢
  have hBaseValid :=
    (model.parametersAt_isValid_iff angularFrequency).mp hFrequency.2
  have hAttenuation := hBaseValid.fieldAttenuation_nonneg
  constructor
  · change (model.parametersAt
      (angularFrequency + model.angularFSR)).denominator ≠ 0
    rw [model.denominator_parametersAt_add_angularFSR angularFrequency hAttenuation]
    exact hFrequency.1
  · exact (model.parametersAt_isValid_iff
      (angularFrequency + model.angularFSR)).mpr hBaseValid

/-- One angular FSR leaves the exact closed-form through power unchanged whenever both N5F
physical-response gates hold. -/
lemma throughPower_add_angularFSR (model : NondispersiveGroupIndexModel)
    (angularFrequency : ℝ)
    (hFrequency : angularFrequency ∈ model.network.responseDomain)
    (hNext : angularFrequency + model.angularFSR ∈ model.network.responseDomain) :
    throughPower (model.parametersAt (angularFrequency + model.angularFSR)) =
      throughPower (model.parametersAt angularFrequency) := by
  have hDomain :=
    (mem_parameterizedNetlist_responseDomain_iff model.parametersAt
      angularFrequency).mp hFrequency
  have hNextDomain :=
    (mem_parameterizedNetlist_responseDomain_iff model.parametersAt
      (angularFrequency + model.angularFSR)).mp hNext
  have hCos := model.cos_parametersAt_add_angularFSR angularFrequency
  rw [throughPower_eq_closedForm _ hNextDomain.2.1.isUnitary
      hNextDomain.2.fieldAttenuation_nonneg hNextDomain.1,
    throughPower_eq_closedForm _ hDomain.2.1.isUnitary
      hDomain.2.fieldAttenuation_nonneg hDomain.1]
  rw [Parameters.throughPowerNumerator, Parameters.throughPowerNumerator,
    Parameters.powerDenominator, Parameters.powerDenominator]
  simp only [parametersAt]
  simp only [parametersAt] at hCos
  rw [hCos]

/-- One angular FSR leaves the exact closed-form drop power unchanged whenever both N5F
physical-response gates hold. -/
lemma dropPower_add_angularFSR (model : NondispersiveGroupIndexModel)
    (angularFrequency : ℝ)
    (hFrequency : angularFrequency ∈ model.network.responseDomain)
    (hNext : angularFrequency + model.angularFSR ∈ model.network.responseDomain) :
    dropPower (model.parametersAt (angularFrequency + model.angularFSR)) =
      dropPower (model.parametersAt angularFrequency) := by
  have hDomain :=
    (mem_parameterizedNetlist_responseDomain_iff model.parametersAt
      angularFrequency).mp hFrequency
  have hNextDomain :=
    (mem_parameterizedNetlist_responseDomain_iff model.parametersAt
      (angularFrequency + model.angularFSR)).mp hNext
  have hCos := model.cos_parametersAt_add_angularFSR angularFrequency
  rw [dropPower_eq_closedForm _ hNextDomain.2.fieldAttenuation_nonneg,
    dropPower_eq_closedForm _ hDomain.2.fieldAttenuation_nonneg]
  rw [Parameters.dropPowerNumerator, Parameters.dropPowerNumerator,
    Parameters.powerDenominator, Parameters.powerDenominator]
  simp only [parametersAt]
  simp only [parametersAt] at hCos
  rw [hCos]

/-!
## C. Proof-gated free-spectral-range periodicity
-/

/-- Under the nondispersive group-index hypothesis, the proof-gated N5F through response power is
periodic with angular-frequency period `angularFSR`. -/
theorem nondispersive_throughPower_periodic (model : NondispersiveGroupIndexModel)
    (angularFrequency : ℝ)
    (hFrequency : angularFrequency ∈ model.network.responseDomain)
    (hNext : angularFrequency + model.angularFSR ∈ model.network.responseDomain) :
    Complex.normSq
        (model.network.response hNext
          (Outgoing.mk
            (throughChannel (model.parametersAt
              (angularFrequency + model.angularFSR))))
          (Incident.mk
            (inputChannel (model.parametersAt
              (angularFrequency + model.angularFSR))))) =
      Complex.normSq
        (model.network.response hFrequency
          (Outgoing.mk (throughChannel (model.parametersAt angularFrequency)))
          (Incident.mk (inputChannel (model.parametersAt angularFrequency)))) := by
  unfold network at hFrequency hNext ⊢
  rw [parameterizedNetlist_response_through,
    parameterizedNetlist_response_through]
  simpa only [throughPower] using
    model.throughPower_add_angularFSR angularFrequency hFrequency hNext

/-- Under the nondispersive group-index hypothesis, the proof-gated N5F drop response power is
periodic with angular-frequency period `angularFSR`. No drop-field periodicity is asserted. -/
theorem nondispersive_dropPower_periodic (model : NondispersiveGroupIndexModel)
    (angularFrequency : ℝ)
    (hFrequency : angularFrequency ∈ model.network.responseDomain)
    (hNext : angularFrequency + model.angularFSR ∈ model.network.responseDomain) :
    Complex.normSq
        (model.network.response hNext
          (Outgoing.mk
            (dropChannel (model.parametersAt
              (angularFrequency + model.angularFSR))))
          (Incident.mk
            (inputChannel (model.parametersAt
              (angularFrequency + model.angularFSR))))) =
      Complex.normSq
        (model.network.response hFrequency
          (Outgoing.mk (dropChannel (model.parametersAt angularFrequency)))
          (Incident.mk (inputChannel (model.parametersAt angularFrequency)))) := by
  unfold network at hFrequency hNext ⊢
  rw [parameterizedNetlist_response_drop,
    parameterizedNetlist_response_drop]
  simpa only [dropPower] using
    model.dropPower_add_angularFSR angularFrequency hFrequency hNext

/-- A single physical-domain gate suffices for N5F through-power periodicity because domain
membership itself propagates by one angular FSR. -/
lemma nondispersive_throughPower_periodic_of_mem (model : NondispersiveGroupIndexModel)
    (angularFrequency : ℝ)
    (hFrequency : angularFrequency ∈ model.network.responseDomain) :
    Complex.normSq
        (model.network.response (model.add_angularFSR_mem_responseDomain hFrequency)
          (Outgoing.mk
            (throughChannel (model.parametersAt
              (angularFrequency + model.angularFSR))))
          (Incident.mk
            (inputChannel (model.parametersAt
              (angularFrequency + model.angularFSR))))) =
      Complex.normSq
        (model.network.response hFrequency
          (Outgoing.mk (throughChannel (model.parametersAt angularFrequency)))
          (Incident.mk (inputChannel (model.parametersAt angularFrequency)))) := by
  exact nondispersive_throughPower_periodic model angularFrequency hFrequency
    (model.add_angularFSR_mem_responseDomain hFrequency)

/-- A single physical-domain gate suffices for N5F drop-power periodicity because domain
membership itself propagates by one angular FSR. -/
lemma nondispersive_dropPower_periodic_of_mem (model : NondispersiveGroupIndexModel)
    (angularFrequency : ℝ)
    (hFrequency : angularFrequency ∈ model.network.responseDomain) :
    Complex.normSq
        (model.network.response (model.add_angularFSR_mem_responseDomain hFrequency)
          (Outgoing.mk
            (dropChannel (model.parametersAt
              (angularFrequency + model.angularFSR))))
          (Incident.mk
            (inputChannel (model.parametersAt
              (angularFrequency + model.angularFSR))))) =
      Complex.normSq
        (model.network.response hFrequency
          (Outgoing.mk (dropChannel (model.parametersAt angularFrequency)))
          (Incident.mk (inputChannel (model.parametersAt angularFrequency)))) := by
  exact nondispersive_dropPower_periodic model angularFrequency hFrequency
    (model.add_angularFSR_mem_responseDomain hFrequency)

end NondispersiveGroupIndexModel

end AddDrop

end

end Optics
