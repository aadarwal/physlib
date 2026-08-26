/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Systems.Microring.AllPass

/-!
# Two-port boundary coordinates of the all-pass microring

## i. Overview

The explicit all-pass netlist leaves exactly two physical bus channels exposed: the coupler's
`leftFirst` and `rightFirst` ports. This file proves that exhaustiveness and packages it as a
left-then-right channel equivalence.

The existing N5 derivation treats incidence from the left. Here the same component and routing
equations derive the right-to-left response independently. The two directional formulas coincide
because the selected coupler and propagation models use the same algebraic action in both
directions. No reciprocity or physical time-reversal theorem is inferred from that model choice.

Every response statement retains the exact `Parameters.HasNonzeroDenominator` gate. No chain
pivot, contraction, passivity, losslessness, delay, causality, or region-of-convergence claim is
made here.

## ii. Key results

- `AllPass.twoPortExternalChannelEquiv`: the left/right sum labels exhaust the external boundary.
- `AllPass.leftLoopIncident_eq`: the forward internal circulation solution.
- `AllPass.rightLoopIncident_eq`: the reverse internal circulation solution.
- `AllPass.response_bus_coordinates`: both directional external N5 response laws.
- `AllPass.responseTransform_entry_input_through`: the right-to-left transmission entry.
- `AllPass.responseTransform_entry_input_input` and
  `AllPass.responseTransform_entry_through_through`: the zero-reflection entries.

## iii. Table of contents

- A. External two-port coordinates
- B. Directional circulation equations
- C. Complete bus response

## iv. References

This boundary and reverse-response derivation is Physlib-original. It uses only the component and
wiring equations established in `AllPass.lean`.

-/

@[expose] public section

namespace Optics

noncomputable section

namespace AllPass

/-! ## A. External two-port coordinates -/

/-- The left-then-right sum labels select the input-side and through-side external channels. -/
def twoPortExternalChannel (p : Parameters) :
    Unit ⊕ Unit → (netlist p).ExternalChannel
  | Sum.inl _ => inputChannel p
  | Sum.inr _ => throughChannel p

/-- The two selected external channels are distinct, so the sum labeling is injective. -/
lemma twoPortExternalChannel_injective (p : Parameters) :
    Function.Injective (twoPortExternalChannel p) := by
  rintro (left | right) (left' | right') hEqual
  · cases left
    cases left'
    rfl
  · cases left
    cases right'
    exact (inputChannel_ne_throughChannel p hEqual).elim
  · cases right
    cases left'
    exact (inputChannel_ne_throughChannel p hEqual.symm).elim
  · cases right
    cases right'
    rfl

/-- Every external all-pass channel is one of the two exposed first-arm bus channels. -/
lemma twoPortExternalChannel_surjective (p : Parameters) :
    Function.Surjective (twoPortExternalChannel p) := by
  rintro ⟨⟨⟨component, port⟩, mode⟩, hExternal⟩
  cases component
  · cases port <;> cases mode
    · exact ⟨Sum.inl (), Subtype.ext (by rfl)⟩
    · exfalso
      apply hExternal
      exact ⟨connectedCouplerLeftSecond p, rfl⟩
    · exact ⟨Sum.inr (), Subtype.ext (by rfl)⟩
    · exfalso
      apply hExternal
      exact ⟨connectedCouplerRightSecond p, rfl⟩
  · cases port <;> cases mode
    · exfalso
      apply hExternal
      exact ⟨connectedPropagationLeft p, rfl⟩
    · exfalso
      apply hExternal
      exact ⟨connectedPropagationRight p, rfl⟩

/-- The canonical left-then-right identification of the all-pass external channel family. -/
noncomputable def twoPortExternalChannelEquiv (p : Parameters) :
    Unit ⊕ Unit ≃ (netlist p).ExternalChannel :=
  Equiv.ofBijective (twoPortExternalChannel p)
    ⟨twoPortExternalChannel_injective p, twoPortExternalChannel_surjective p⟩

/-- The left summand is the physical input-side bus channel. -/
@[simp]
lemma twoPortExternalChannelEquiv_apply_inl (p : Parameters) (mode : Unit) :
    twoPortExternalChannelEquiv p (Sum.inl mode) = inputChannel p := rfl

/-- The right summand is the physical through-side bus channel. -/
@[simp]
lemma twoPortExternalChannelEquiv_apply_inr (p : Parameters) (mode : Unit) :
    twoPortExternalChannelEquiv p (Sum.inr mode) = throughChannel p := rfl

/-- A coherent scalar amplitude incident only from the through-side bus channel. -/
def throughIncidentAmplitude (p : Parameters) (amplitude : ℂ) :
    ModeAmplitude (netlist p).ExternalIncident :=
  PiLp.single 2 (Incident.mk (throughChannel p)) amplitude

/-- The through-side excitation has its supplied value at the through channel. -/
@[simp]
lemma throughIncidentAmplitude_apply_through (p : Parameters) (amplitude : ℂ) :
    throughIncidentAmplitude p amplitude (Incident.mk (throughChannel p)) = amplitude := by
  simp [throughIncidentAmplitude]

/-- The through-side excitation vanishes at the input-side channel. -/
@[simp]
lemma throughIncidentAmplitude_apply_input (p : Parameters) (amplitude : ℂ) :
    throughIncidentAmplitude p amplitude (Incident.mk (inputChannel p)) = 0 := by
  rw [throughIncidentAmplitude]
  simp [inputChannel_ne_throughChannel p]

/-- External incident endpoints in typed left/right scattering order.

This is a nominal coordinate relabeling, not a physical time-reversal identification.
-/
noncomputable def twoPortExternalIncidentEquiv (p : Parameters) :
    (netlist p).ExternalIncident ≃ Incident Unit ⊕ Incident Unit :=
  (Incident.relabelEquiv (twoPortExternalChannelEquiv p).symm).trans
    Incident.splitSumEquiv

/-- External outgoing endpoints in typed left/right scattering order.

This is a nominal coordinate relabeling, not a physical time-reversal identification.
-/
noncomputable def twoPortExternalOutgoingEquiv (p : Parameters) :
    (netlist p).ExternalOutgoing ≃ Outgoing Unit ⊕ Outgoing Unit :=
  (Outgoing.relabelEquiv (twoPortExternalChannelEquiv p).symm).trans
    Outgoing.splitSumEquiv

/-! ## B. Directional circulation equations -/

/-- A component-scattering equation implies the local left-bus coupler equation. -/
lemma scatteringEquation_coupler_leftFirst (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident) :
    outgoing (Outgoing.mk (couplerChannel p DirectionalCoupler.Port.leftFirst)) =
      (p.throughAmplitude : ℂ) *
          incident (Incident.mk (couplerChannel p DirectionalCoupler.Port.rightFirst)) +
        DirectionalCoupler.crossCoefficient p.coupler *
          incident (Incident.mk (couplerChannel p DirectionalCoupler.Port.rightSecond)) := by
  have hPhysical := coupler_physicalBehavior_of_scatteringEquation p incident outgoing hScattering
  have hRaw := (DirectionalCoupler.mem_physicalBehavior_iff p.coupler _ _).mp hPhysical
  rw [DirectionalCoupler.mem_behavior_iff,
    DirectionalCoupler.mixing_toLinearMap_apply,
    DirectionalCoupler.mixing_toLinearMap_apply] at hRaw
  exact congrArg (fun amplitude => amplitude (Sum.inl (Outgoing.mk (Sum.inl ())))) hRaw

/-- External readout returns the aggregate input-side bus outgoing coordinate. -/
lemma outputReadout_apply_input (p : Parameters)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex) :
    (netlist p).outputReadout.toLinearMap outgoing (Outgoing.mk (inputChannel p)) =
      outgoing (Outgoing.mk (couplerChannel p DirectionalCoupler.Port.leftFirst)) := by
  rw [FlatNetlist.outputReadout,
    (netlist p).connections.externalOutgoingReadout_apply,
    ModeAmplitude.restrictEmbedding_apply]
  rfl

/-- Solving the left-to-right circulation gives the internal left ring input. -/
lemma leftLoopIncident_eq (p : Parameters) (hDenominator : p.HasNonzeroDenominator)
    (external : ModeAmplitude (netlist p).ExternalIncident)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident)
    (hAssembly : incident =
      (netlist p).connections.incidentAssembly outgoing external) :
    incident (Incident.mk (couplerChannel p DirectionalCoupler.Port.leftSecond)) =
      p.loopCoefficient * DirectionalCoupler.crossCoefficient p.coupler *
          external (Incident.mk (inputChannel p)) / p.denominator := by
  have hInput := congrArg
    (fun state => state (Incident.mk (couplerChannel p DirectionalCoupler.Port.leftFirst)))
    hAssembly
  rw [incidentAssembly_apply_leftFirst] at hInput
  have hCouplerLeft := congrArg
    (fun state => state (Incident.mk (couplerChannel p DirectionalCoupler.Port.leftSecond)))
    hAssembly
  rw [incidentAssembly_apply_coupler_leftSecond,
    scatteringEquation_propagation_right p incident outgoing hScattering] at hCouplerLeft
  have hPropagationLeft := congrArg
    (fun state => state (Incident.mk (propagationChannel p MatchedPropagation.Port.left)))
    hAssembly
  rw [incidentAssembly_apply_propagation_left,
    scatteringEquation_coupler_rightSecond p incident outgoing hScattering,
    hInput] at hPropagationLeft
  apply (eq_div_iff hDenominator).2
  rw [Parameters.denominator, Parameters.loopGain]
  linear_combination hCouplerLeft + p.loopCoefficient * hPropagationLeft

/-- Solving the right-to-left circulation gives the internal right ring input. -/
lemma rightLoopIncident_eq (p : Parameters) (hDenominator : p.HasNonzeroDenominator)
    (external : ModeAmplitude (netlist p).ExternalIncident)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident)
    (hAssembly : incident =
      (netlist p).connections.incidentAssembly outgoing external) :
    incident (Incident.mk (couplerChannel p DirectionalCoupler.Port.rightSecond)) =
      p.loopCoefficient * DirectionalCoupler.crossCoefficient p.coupler *
          external (Incident.mk (throughChannel p)) / p.denominator := by
  have hInput := congrArg
    (fun state => state (Incident.mk (couplerChannel p DirectionalCoupler.Port.rightFirst)))
    hAssembly
  rw [incidentAssembly_apply_rightFirst] at hInput
  have hCouplerRight := congrArg
    (fun state => state (Incident.mk (couplerChannel p DirectionalCoupler.Port.rightSecond)))
    hAssembly
  rw [incidentAssembly_apply_coupler_rightSecond,
    scatteringEquation_propagation_left p incident outgoing hScattering] at hCouplerRight
  have hPropagationRight := congrArg
    (fun state => state (Incident.mk (propagationChannel p MatchedPropagation.Port.right)))
    hAssembly
  rw [incidentAssembly_apply_propagation_right,
    scatteringEquation_coupler_leftSecond p incident outgoing hScattering,
    hInput] at hPropagationRight
  apply (eq_div_iff hDenominator).2
  rw [Parameters.denominator, Parameters.loopGain]
  linear_combination hCouplerRight + p.loopCoefficient * hPropagationRight

/-- Every complete solution returns the left input through the right bus transfer law. -/
lemma scatteringSolution_apply_rightFirst (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator)
    (external : ModeAmplitude (netlist p).ExternalIncident)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident)
    (hAssembly : incident =
      (netlist p).connections.incidentAssembly outgoing external) :
    outgoing (Outgoing.mk (couplerChannel p DirectionalCoupler.Port.rightFirst)) =
      throughTransfer p * external (Incident.mk (inputChannel p)) := by
  have hInput := congrArg
    (fun state => state (Incident.mk (couplerChannel p DirectionalCoupler.Port.leftFirst)))
    hAssembly
  rw [incidentAssembly_apply_leftFirst] at hInput
  rw [scatteringEquation_coupler_rightFirst p incident outgoing hScattering, hInput,
    leftLoopIncident_eq p hDenominator external incident outgoing hScattering hAssembly,
    throughTransfer]
  ring

/-- Every complete solution returns the right input through the left bus transfer law. -/
lemma scatteringSolution_apply_leftFirst (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator)
    (external : ModeAmplitude (netlist p).ExternalIncident)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident)
    (hAssembly : incident =
      (netlist p).connections.incidentAssembly outgoing external) :
    outgoing (Outgoing.mk (couplerChannel p DirectionalCoupler.Port.leftFirst)) =
      throughTransfer p * external (Incident.mk (throughChannel p)) := by
  have hInput := congrArg
    (fun state => state (Incident.mk (couplerChannel p DirectionalCoupler.Port.rightFirst)))
    hAssembly
  rw [incidentAssembly_apply_rightFirst] at hInput
  rw [scatteringEquation_coupler_leftFirst p incident outgoing hScattering, hInput,
    rightLoopIncident_eq p hDenominator external incident outgoing hScattering hAssembly,
    throughTransfer]
  ring

/-! ## C. Complete bus response -/

/-- The proof-gated N5 response obeys both directional bus laws and has zero same-side reflection.

The first equality is the input-side outgoing coordinate; the second is the through-side outgoing
coordinate. Each depends only on incidence from the opposite side.
-/
lemma response_bus_coordinates (p : Parameters) (hDenominator : p.HasNonzeroDenominator)
    (external : ModeAmplitude (netlist p).ExternalIncident) :
    let response := (netlist p).responseTransform
      (isWellPosed_of_hasNonzeroDenominator p hDenominator) |>.toLinearMap external
    response (Outgoing.mk (inputChannel p)) =
        throughTransfer p * external (Incident.mk (throughChannel p)) ∧
      response (Outgoing.mk (throughChannel p)) =
        throughTransfer p * external (Incident.mk (inputChannel p)) := by
  let hWellPosed := isWellPosed_of_hasNonzeroDenominator p hDenominator
  let response := (netlist p).responseTransform hWellPosed |>.toLinearMap external
  have hMember : (external, response) ∈ (netlist p).behavior := by
    rw [← (netlist p).toBehavior_responseTransform hWellPosed,
      ModeTransform.mem_toBehavior_iff_toLinearMap]
  rcases ((netlist p).mem_behavior_iff_equations external response).mp hMember with
    ⟨incident, outgoing, hScattering, hAssembly, hOutput⟩
  have hAssembly' : incident =
      (netlist p).connections.incidentAssembly outgoing external := by
    simpa only [PortConnectionFamily.incidentAssembly] using hAssembly
  have hLeft := scatteringSolution_apply_leftFirst p hDenominator external incident outgoing
    hScattering hAssembly'
  have hRight := scatteringSolution_apply_rightFirst p hDenominator external incident outgoing
    hScattering hAssembly'
  have hReadoutLeft := congrArg (fun state => state (Outgoing.mk (inputChannel p))) hOutput
  have hReadoutRight := congrArg (fun state => state (Outgoing.mk (throughChannel p))) hOutput
  rw [outputReadout_apply_input] at hReadoutLeft
  rw [outputReadout_apply_through] at hReadoutRight
  change response (Outgoing.mk (inputChannel p)) = _ ∧
    response (Outgoing.mk (throughChannel p)) = _
  exact ⟨hReadoutLeft.trans hLeft, hReadoutRight.trans hRight⟩

/-- The proof-gated N5 response has zero input-side reflection. -/
lemma responseTransform_entry_input_input (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) :
    (netlist p).responseTransform (isWellPosed_of_hasNonzeroDenominator p hDenominator)
        (Outgoing.mk (inputChannel p)) (Incident.mk (inputChannel p)) = 0 := by
  have hResponse := (response_bus_coordinates p hDenominator (inputAmplitude p 1)).1
  simpa [inputAmplitude, Matrix.toLpLin_apply,
    (inputChannel_ne_throughChannel p).symm] using hResponse

/-- The proof-gated N5 right-to-left response is the all-pass through transfer. -/
lemma responseTransform_entry_input_through (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) :
    (netlist p).responseTransform (isWellPosed_of_hasNonzeroDenominator p hDenominator)
        (Outgoing.mk (inputChannel p)) (Incident.mk (throughChannel p)) =
      throughTransfer p := by
  have hResponse :=
    (response_bus_coordinates p hDenominator (throughIncidentAmplitude p 1)).1
  simpa [throughIncidentAmplitude, Matrix.toLpLin_apply] using hResponse

/-- The proof-gated N5 response has zero through-side reflection. -/
lemma responseTransform_entry_through_through (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) :
    (netlist p).responseTransform (isWellPosed_of_hasNonzeroDenominator p hDenominator)
        (Outgoing.mk (throughChannel p)) (Incident.mk (throughChannel p)) = 0 := by
  have hResponse :=
    (response_bus_coordinates p hDenominator (throughIncidentAmplitude p 1)).2
  simpa [throughIncidentAmplitude, Matrix.toLpLin_apply,
    inputChannel_ne_throughChannel p] using hResponse

end AllPass

end

end Optics
