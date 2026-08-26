/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.TwoPortChainScattering
public import Physlib.Optics.Systems.DCDR.ZTransformBridge

/-!
# Nominal two-port and chain semantics of the DCDR

## i. Overview

The coherent DCDR netlist has exactly two external N7 channels. This module labels the first
coupler's `leftFirst` endpoint as the nominal left reference plane and the second coupler's
`rightFirst` endpoint as the nominal right reference plane. These labels are algebraic coordinates;
they do not assert physical reference planes or physical time reversal.

The complete forward and reverse N7 equations independently derive all four entries of the
well-posed N5 response. Both nominal reflection entries vanish. Left-to-right transmission is
`transfer p`; right-to-left transmission is separately stated as `transfer p.reverse`. The latter
is the scalar chain pivot. Its nonvanishing is kept separate from N5 well-posedness, analytic ROC
membership, recurrence contraction, and Schur certification.

On the solve and pivot gates, generic N3T conversion supplies the backward-first chain and its
scattering round trip. A downstream common-domain record adds this chain leg to the existing DCDR
causal-Z agreement without deriving any gate from another.

## ii. Key results

- `DCDR.response_nominal_reference_coordinates`: both N5 output coordinates from raw N7 equations.
- `DCDR.packagedNominalTwoPortScattering_eq_nominalTwoPortScatteringTransform`: all four blocks.
- `DCDR.packagedNominalTwoPortScattering_hasBijectiveRightToLeftTransmission_iff`: scalar pivot.
- `DCDR.nominalBackwardFirstChainTransform_eq_matrix`: the explicit backward-first chain.
- `DCDR.nominalBackwardFirstChainTransform_roundTrip`: the generic N3T scattering round trip.
- `DCDR.zChainCrossSemantics_agree`: the DCDR X-01 agreement including the chain leg.

## iii. Table of contents

- A. Nominal external reference-plane coordinates
- B. Complete forward and reverse N5 response
- C. Independent and packaged two-port scattering
- D. Scalar pivot and backward-first chain
- E. Common-domain Z and chain agreement

## iv. References

This nominal two-port and chain presentation is Physlib-original. It makes no claim of physical
reference planes, reciprocity, physical time reversal, physical resonance, coherent--incoherent
equivalence, BIBO stability beyond S4P's gate, normalized-modal or electromagnetic power,
Maxwell time-domain meaning, physical-frequency meaning, or HOL-script semantics.

The scattering-to-chain convention and round trip reuse
`Physlib/Optics/Network/TwoPortChainScattering.lean`.
-/

@[expose] public section

namespace Optics.DCDR

noncomputable section

/-!

## A. Nominal external reference-plane coordinates

-/

/-- The nominal left-then-right labels select the exposed first-arm endpoints.

`Sum.inl` is the first coupler's `leftFirst` endpoint and `Sum.inr` is the second coupler's
`rightFirst` endpoint. The labels are algebraic and do not assert physical reference planes.
-/
def nominalTwoPortExternalChannel (p : Parameters) :
    Unit ⊕ Unit → (netlist p).ExternalChannel
  | Sum.inl _ => inputChannel p
  | Sum.inr _ => outputChannel p

/-- The two nominal external labels are injective. -/
lemma nominalTwoPortExternalChannel_injective (p : Parameters) :
    Function.Injective (nominalTwoPortExternalChannel p) := by
  rintro (left | right) (left' | right') hEqual
  · cases left
    cases left'
    rfl
  · cases left
    cases right'
    exact (inputChannel_ne_outputChannel p hEqual).elim
  · cases right
    cases left'
    exact (inputChannel_ne_outputChannel p hEqual.symm).elim
  · cases right
    cases right'
    rfl

/-- The two nominal labels exhaust the complete external DCDR channel family. -/
lemma nominalTwoPortExternalChannel_surjective (p : Parameters) :
    Function.Surjective (nominalTwoPortExternalChannel p) := by
  intro channel
  rcases externalChannel_eq_input_or_output p channel with rfl | rfl
  · exact ⟨Sum.inl (), rfl⟩
  · exact ⟨Sum.inr (), rfl⟩

/-- The nominal left-then-right equivalence for the two external DCDR channels. -/
noncomputable def nominalTwoPortExternalChannelEquiv (p : Parameters) :
    Unit ⊕ Unit ≃ (netlist p).ExternalChannel :=
  Equiv.ofBijective (nominalTwoPortExternalChannel p)
    ⟨nominalTwoPortExternalChannel_injective p,
      nominalTwoPortExternalChannel_surjective p⟩

/-- The nominal left label is the first coupler's exposed `leftFirst` endpoint. -/
@[simp]
lemma nominalTwoPortExternalChannelEquiv_apply_inl (p : Parameters) (mode : Unit) :
    nominalTwoPortExternalChannelEquiv p (Sum.inl mode) = inputChannel p := rfl

/-- The nominal right label is the second coupler's exposed `rightFirst` endpoint. -/
@[simp]
lemma nominalTwoPortExternalChannelEquiv_apply_inr (p : Parameters) (mode : Unit) :
    nominalTwoPortExternalChannelEquiv p (Sum.inr mode) = outputChannel p := rfl

/-- External incident endpoints in nominal left/right order. -/
noncomputable def nominalTwoPortExternalIncidentEquiv (p : Parameters) :
    (netlist p).ExternalIncident ≃ Incident Unit ⊕ Incident Unit :=
  (Incident.relabelEquiv (nominalTwoPortExternalChannelEquiv p).symm).trans
    Incident.splitSumEquiv

/-- External outgoing endpoints in nominal left/right order. -/
noncomputable def nominalTwoPortExternalOutgoingEquiv (p : Parameters) :
    (netlist p).ExternalOutgoing ≃ Outgoing Unit ⊕ Outgoing Unit :=
  (Outgoing.relabelEquiv (nominalTwoPortExternalChannelEquiv p).symm).trans
    Outgoing.splitSumEquiv

/-- A coherent scalar incident only at the nominal right endpoint. -/
def nominalRightIncidentAmplitude (p : Parameters) (amplitude : ℂ) :
    ModeAmplitude (netlist p).ExternalIncident :=
  PiLp.single 2 (Incident.mk (outputChannel p)) amplitude

/-- The nominal-right excitation has its supplied value at the right endpoint. -/
@[simp]
lemma nominalRightIncidentAmplitude_apply_right (p : Parameters) (amplitude : ℂ) :
    nominalRightIncidentAmplitude p amplitude (Incident.mk (outputChannel p)) = amplitude := by
  simp [nominalRightIncidentAmplitude]

/-- The nominal-right excitation vanishes at the left endpoint. -/
@[simp]
lemma nominalRightIncidentAmplitude_apply_left (p : Parameters) (amplitude : ℂ) :
    nominalRightIncidentAmplitude p amplitude (Incident.mk (inputChannel p)) = 0 := by
  rw [nominalRightIncidentAmplitude]
  simp [inputChannel_ne_outputChannel p]

/-!

## B. Complete forward and reverse N5 response

-/

/-- External readout at the nominal left endpoint is the first coupler's `leftFirst` output. -/
lemma outputReadout_apply_nominalLeft (p : Parameters)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex) :
    (netlist p).outputReadout.toLinearMap outgoing (Outgoing.mk (inputChannel p)) =
      outgoing (Outgoing.mk
        (firstCouplerChannel p DirectionalCoupler.Port.leftFirst)) := by
  rw [FlatNetlist.outputReadout,
    (netlist p).connections.externalOutgoingReadout_apply,
    ModeAmplitude.restrictEmbedding_apply]
  rfl

/-- Raw forward and reverse N7 equations determine both nominal N5 output coordinates.

The nominal-left output depends only on nominal-right incidence through `transfer p.reverse`.
The nominal-right output depends only on nominal-left incidence through `transfer p`.
-/
lemma response_nominal_reference_coordinates (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator)
    (external : ModeAmplitude (netlist p).ExternalIncident) :
    let response := (netlist p).responseTransform
      (isWellPosed_of_hasNonzeroDenominator p hDenominator) |>.toLinearMap external
    response (Outgoing.mk (inputChannel p)) =
        transfer p.reverse * external (Incident.mk (outputChannel p)) ∧
      response (Outgoing.mk (outputChannel p)) =
        transfer p * external (Incident.mk (inputChannel p)) := by
  let hWellPosed := isWellPosed_of_hasNonzeroDenominator p hDenominator
  let response := (netlist p).responseTransform hWellPosed |>.toLinearMap external
  have hMember : (external, response) ∈ (netlist p).behavior := by
    rw [← (netlist p).toBehavior_responseTransform hWellPosed,
      ModeTransform.mem_toBehavior_iff_toLinearMap]
  rcases ((netlist p).mem_behavior_iff_equations external response).mp hMember with
    ⟨incident, outgoing, hScattering, hAssembly, hOutput⟩
  have hAssembly' :
      incident = (netlist p).connections.incidentAssembly outgoing external := by
    simpa only [PortConnectionFamily.incidentAssembly] using hAssembly
  have hForward := forwardEquations_of_netlistEquations p external incident outgoing
    hScattering hAssembly'
  have hReverse := reverseEquations_of_netlistEquations p external incident outgoing
    hScattering hAssembly'
  have hReverseDenominator : p.reverse.HasNonzeroDenominator := by
    simpa [Parameters.HasNonzeroDenominator, Parameters.denominator_reverse] using hDenominator
  have hForwardValue := hForward.output_eq_transfer hDenominator
  have hReverseValue := hReverse.output_eq_transfer hReverseDenominator
  have hReadoutLeft := congrArg
    (fun state => state (Outgoing.mk (inputChannel p))) hOutput
  have hReadoutRight := congrArg
    (fun state => state (Outgoing.mk (outputChannel p))) hOutput
  rw [outputReadout_apply_nominalLeft] at hReadoutLeft
  rw [outputReadout_apply_output] at hReadoutRight
  change response (Outgoing.mk (inputChannel p)) = _ ∧
    response (Outgoing.mk (outputChannel p)) = _
  constructor
  · exact hReadoutLeft.trans (by simpa [reverseState] using hReverseValue)
  · exact hReadoutRight.trans (by simpa [forwardState] using hForwardValue)

/-- The nominal-left N5 reflection entry is zero. -/
lemma responseTransform_entry_nominalLeft_nominalLeft (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) :
    (netlist p).responseTransform (isWellPosed_of_hasNonzeroDenominator p hDenominator)
        (Outgoing.mk (inputChannel p)) (Incident.mk (inputChannel p)) = 0 := by
  have hResponse :=
    (response_nominal_reference_coordinates p hDenominator (inputAmplitude p 1)).1
  simpa [inputAmplitude, Matrix.toLpLin_apply,
    (inputChannel_ne_outputChannel p).symm] using hResponse

/-- The nominal right-to-left N5 entry is the independently stated reverse transmission. -/
lemma responseTransform_entry_nominalLeft_nominalRight (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) :
    (netlist p).responseTransform (isWellPosed_of_hasNonzeroDenominator p hDenominator)
        (Outgoing.mk (inputChannel p)) (Incident.mk (outputChannel p)) =
      transfer p.reverse := by
  have hResponse := (response_nominal_reference_coordinates p hDenominator
    (nominalRightIncidentAmplitude p 1)).1
  simpa [nominalRightIncidentAmplitude, Matrix.toLpLin_apply] using hResponse

/-- The nominal left-to-right N5 entry is the forward transmission. -/
lemma responseTransform_entry_nominalRight_nominalLeft (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) :
    (netlist p).responseTransform (isWellPosed_of_hasNonzeroDenominator p hDenominator)
        (Outgoing.mk (outputChannel p)) (Incident.mk (inputChannel p)) = transfer p := by
  have hResponse :=
    (response_nominal_reference_coordinates p hDenominator (inputAmplitude p 1)).2
  simpa [inputAmplitude, Matrix.toLpLin_apply] using hResponse

/-- The nominal-right N5 reflection entry is zero. -/
lemma responseTransform_entry_nominalRight_nominalRight (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) :
    (netlist p).responseTransform (isWellPosed_of_hasNonzeroDenominator p hDenominator)
        (Outgoing.mk (outputChannel p)) (Incident.mk (outputChannel p)) = 0 := by
  have hResponse := (response_nominal_reference_coordinates p hDenominator
    (nominalRightIncidentAmplitude p 1)).2
  simpa [nominalRightIncidentAmplitude, Matrix.toLpLin_apply,
    inputChannel_ne_outputChannel p] using hResponse

end

end Optics.DCDR
