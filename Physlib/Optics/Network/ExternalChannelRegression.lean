/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.ExternalChannel
public import Physlib.Optics.Network.PartialRoutingRegression

/-!
# Regression tests for external optical channels

## i. Overview

The existing dependent three-port fixture has four connected channels and one external channel.
This file identifies that complement exactly, distinguishes incident injection from outgoing
exposure, tests complex output readout without conjugating the amplitude, and checks the coordinate
and power laws of the expression `C b + E_in u`.

A second valid three-port family gives its unconnected third port an empty mode fiber. Its connected
channel embedding is surjective even though the third physical port is unused. This fixes the
channel-versus-port distinction: an unconnected empty port contributes no external channel.

## ii. Key results

## iii. Table of contents

- A. The sole nonempty external channel
- B. Exact incident injection
- C. Exact outgoing exposure and readout
- D. The assembled `C b + E_in u` incident amplitude
- E. An unconnected port with an empty mode fiber

## iv. References

These are finite normalized-coordinate regressions. The external endpoint transforms supply no
source, termination, detector, electromagnetic normalization, or feedback solution.

-/

@[expose] public section

namespace Optics

noncomputable section

/-!

## A. The sole nonempty external channel

-/

/-- The exposed channel packaged with its proof of external status. -/
abbrev partialRoutingRegressionExternal : partialRoutingRegressionFamily.ExternalChannel :=
  ⟨partialRoutingRegressionExposed, partialRoutingRegression_exposed_not_mem_range⟩

/-- The exposed physical port is not used by the connection family's endpoints. -/
lemma partialRoutingRegression_exposedPort_not_mem_range :
    PartialRoutingRegressionPort.exposed ∉
      Set.range partialRoutingRegressionFamily.endpointEmbedding := by
  rintro ⟨⟨index, endpoint⟩, hPort⟩
  rcases index with ⟨⟩
  cases endpoint <;> cases hPort

/-- The exposed physical port packaged with its proof that it is unconnected. -/
abbrev partialRoutingRegressionUnconnectedExposed :
    partialRoutingRegressionFamily.UnconnectedPort :=
  ⟨.exposed, partialRoutingRegression_exposedPort_not_mem_range⟩

/-- The connected summand of the channel partition retains west zero. -/
lemma externalChannelRegression_partition_connected :
    partialRoutingRegressionFamily.channelPartitionEquiv
        (Sum.inl partialRoutingRegressionConnectedWestZero) =
      partialRoutingRegressionWestZero := rfl

/-- The external summand of the channel partition retains the exposed channel. -/
lemma externalChannelRegression_partition_external :
    partialRoutingRegressionFamily.channelPartitionEquiv
        (Sum.inr partialRoutingRegressionExternal) =
      partialRoutingRegressionExposed := rfl

/-- The channel-to-unconnected-port-mode equivalence exposes the third port and its sole mode. -/
lemma externalChannelRegression_unconnectedPortMode :
    partialRoutingRegressionFamily.externalChannelEquivUnconnectedPortModes
        partialRoutingRegressionExternal =
      ⟨partialRoutingRegressionUnconnectedExposed, ()⟩ := rfl

/-- Every external channel in the nonempty fixture is the exposed channel. -/
lemma externalChannelRegression_external_eq
    (channel : partialRoutingRegressionFamily.ExternalChannel) :
    channel = partialRoutingRegressionExternal := by
  apply Subtype.ext
  rcases channel with ⟨⟨port, mode⟩, hExternal⟩
  cases port
  · exact (hExternal ⟨⟨(), Sum.inl mode⟩, rfl⟩).elim
  · exact (hExternal ⟨⟨(), Sum.inr mode⟩, rfl⟩).elim
  · cases mode
    rfl

/-!

## B. Exact incident injection

-/

/-- The external incident injection has unit gain at the exposed coordinate. -/
lemma externalChannelRegression_injection_entry_exposed :
    partialRoutingRegressionFamily.externalIncidentInjection
        (Incident.mk partialRoutingRegressionExposed)
        (Incident.mk partialRoutingRegressionExternal) = 1 := by
  exact partialRoutingRegressionFamily.externalIncidentInjection_entry_external _

/-- The external incident injection has zero gain into a connected coordinate. -/
lemma externalChannelRegression_injection_entry_connected :
    partialRoutingRegressionFamily.externalIncidentInjection
        (Incident.mk partialRoutingRegressionEastFalse)
        (Incident.mk partialRoutingRegressionExternal) = 0 := by
  change partialRoutingRegressionFamily.externalIncidentInjection
      (Incident.mk (partialRoutingRegressionFamily.channelEmbedding
        partialRoutingRegressionConnectedEastFalse))
      (Incident.mk partialRoutingRegressionExternal) = 0
  exact partialRoutingRegressionFamily.externalIncidentInjection_entry_connected _ _

/-- A genuinely complex external incident amplitude at the exposed channel. -/
def externalChannelRegressionPulse :
    ModeAmplitude (Incident partialRoutingRegressionFamily.ExternalChannel) :=
  PiLp.single 2 (Incident.mk partialRoutingRegressionExternal) (2 + Complex.I)

/-- The complex external amplitude has normalized modal power five. -/
lemma externalChannelRegression_pulse_power : externalChannelRegressionPulse.power = 5 := by
  simp only [ModeAmplitude.power, externalChannelRegressionPulse, PiLp.norm_single]
  rw [Complex.sq_norm]
  norm_num [Complex.normSq]

/-- Injection preserves the complex coefficient at the exposed ambient incident coordinate. -/
lemma externalChannelRegression_injection_apply_exposed :
    partialRoutingRegressionFamily.externalIncidentInjection.toLinearMap
        externalChannelRegressionPulse (Incident.mk partialRoutingRegressionExposed) =
      2 + Complex.I := by
  change partialRoutingRegressionFamily.externalIncidentInjection.toLinearMap
      externalChannelRegressionPulse
        (Incident.mk partialRoutingRegressionExternal.1) = 2 + Complex.I
  rw [partialRoutingRegressionFamily.externalIncidentInjection_apply_external]
  simp [externalChannelRegressionPulse]

/-- Injection has zero amplitude at a connected ambient incident coordinate. -/
lemma externalChannelRegression_injection_apply_connected :
    partialRoutingRegressionFamily.externalIncidentInjection.toLinearMap
        externalChannelRegressionPulse (Incident.mk partialRoutingRegressionEastFalse) = 0 := by
  change partialRoutingRegressionFamily.externalIncidentInjection.toLinearMap
      externalChannelRegressionPulse
        (Incident.mk (partialRoutingRegressionFamily.channelEmbedding
          partialRoutingRegressionConnectedEastFalse)) = 0
  exact partialRoutingRegressionFamily.externalIncidentInjection_apply_connected _ _

/-- Injection preserves the normalized power of the complex external amplitude. -/
lemma externalChannelRegression_injection_power :
    (partialRoutingRegressionFamily.externalIncidentInjection.toLinearMap
      externalChannelRegressionPulse).power = 5 := by
  rw [partialRoutingRegressionFamily.externalIncidentInjection_isPowerPreserving,
    externalChannelRegression_pulse_power]

/-!

## C. Exact outgoing exposure and readout

-/

/-- The external outgoing exposure has unit gain at the exposed coordinate. -/
lemma externalChannelRegression_outgoingInjection_entry_exposed :
    partialRoutingRegressionFamily.externalOutgoingInjection
        (Outgoing.mk partialRoutingRegressionExposed)
        (Outgoing.mk partialRoutingRegressionExternal) = 1 := by
  exact partialRoutingRegressionFamily.externalOutgoingInjection_entry_external _

/-- The external outgoing exposure has zero gain into a connected coordinate. -/
lemma externalChannelRegression_outgoingInjection_entry_connected :
    partialRoutingRegressionFamily.externalOutgoingInjection
        (Outgoing.mk partialRoutingRegressionWestZero)
        (Outgoing.mk partialRoutingRegressionExternal) = 0 := by
  change partialRoutingRegressionFamily.externalOutgoingInjection
      (Outgoing.mk (partialRoutingRegressionFamily.channelEmbedding
        partialRoutingRegressionConnectedWestZero))
      (Outgoing.mk partialRoutingRegressionExternal) = 0
  exact partialRoutingRegressionFamily.externalOutgoingInjection_entry_connected _ _

/-- A genuinely complex external outgoing amplitude used to test exposure and readout. -/
def externalChannelRegressionOutgoingPulse :
    ModeAmplitude (Outgoing partialRoutingRegressionFamily.ExternalChannel) :=
  PiLp.single 2 (Outgoing.mk partialRoutingRegressionExternal) (3 - 2 * Complex.I)

/-- Outgoing exposure preserves the complex coefficient at the ambient external coordinate. -/
lemma externalChannelRegression_outgoingInjection_apply_exposed :
    partialRoutingRegressionFamily.externalOutgoingInjection.toLinearMap
        externalChannelRegressionOutgoingPulse
          (Outgoing.mk partialRoutingRegressionExposed) = 3 - 2 * Complex.I := by
  change partialRoutingRegressionFamily.externalOutgoingInjection.toLinearMap
      externalChannelRegressionOutgoingPulse
        (Outgoing.mk partialRoutingRegressionExternal.1) = 3 - 2 * Complex.I
  rw [partialRoutingRegressionFamily.externalOutgoingInjection_apply_external]
  simp [externalChannelRegressionOutgoingPulse]

/-- Outgoing exposure vanishes at a connected ambient coordinate. -/
lemma externalChannelRegression_outgoingInjection_apply_connected :
    partialRoutingRegressionFamily.externalOutgoingInjection.toLinearMap
        externalChannelRegressionOutgoingPulse
          (Outgoing.mk partialRoutingRegressionWestZero) = 0 := by
  change partialRoutingRegressionFamily.externalOutgoingInjection.toLinearMap
      externalChannelRegressionOutgoingPulse
        (Outgoing.mk (partialRoutingRegressionFamily.channelEmbedding
          partialRoutingRegressionConnectedWestZero)) = 0
  exact partialRoutingRegressionFamily.externalOutgoingInjection_apply_connected _ _

/-- Adjoint readout after exposure returns the exact complex outgoing amplitude, with no complex
conjugation. -/
lemma externalChannelRegression_outgoingReadout_afterInjection :
    partialRoutingRegressionFamily.externalOutgoingReadout.toLinearMap
        (partialRoutingRegressionFamily.externalOutgoingInjection.toLinearMap
          externalChannelRegressionOutgoingPulse) =
      externalChannelRegressionOutgoingPulse := by
  rw [← ModeTransform.toLinearMap_mul_apply,
    partialRoutingRegressionFamily.externalOutgoingReadout_mul_externalOutgoingInjection]
  simp

/-- In particular, output readout retains the coefficient `3 - 2i` rather than conjugating it. -/
lemma externalChannelRegression_outgoingReadout_coefficient :
    partialRoutingRegressionFamily.externalOutgoingReadout.toLinearMap
        (partialRoutingRegressionFamily.externalOutgoingInjection.toLinearMap
          externalChannelRegressionOutgoingPulse)
          (Outgoing.mk partialRoutingRegressionExternal) = 3 - 2 * Complex.I := by
  rw [externalChannelRegression_outgoingReadout_afterInjection]
  simp [externalChannelRegressionOutgoingPulse]

/-- The connected complex pulse included in the ambient outgoing coordinate space. -/
def externalChannelRegressionConnectedOutgoing :
    ModeAmplitude (Outgoing partialRoutingRegressionPortFamily.Channel) :=
  (ModeTransform.zeroExtension
    partialRoutingRegressionFamily.outgoingChannelEmbedding).toLinearMap
      partialRoutingRegressionConnectedPulse

/-- An ambient outgoing amplitude with independent connected and external complex coefficients. -/
def externalChannelRegressionMixedOutgoing :
    ModeAmplitude (Outgoing partialRoutingRegressionPortFamily.Channel) :=
  externalChannelRegressionConnectedOutgoing +
    partialRoutingRegressionFamily.externalOutgoingInjection.toLinearMap
      externalChannelRegressionOutgoingPulse

/-- External output readout rejects the connected ambient outgoing subspace. -/
lemma externalChannelRegression_outgoingReadout_connected_eq_zero :
    partialRoutingRegressionFamily.externalOutgoingReadout.toLinearMap
        externalChannelRegressionConnectedOutgoing = 0 := by
  rw [partialRoutingRegressionFamily.externalOutgoingReadout_apply]
  apply WithLp.ofLp_injective 2
  funext endpoint
  rcases endpoint with ⟨external⟩
  rw [ModeAmplitude.restrictEmbedding_apply]
  apply ModeTransform.zeroExtension_apply_of_not_mem_range
  intro hConnected
  rw [partialRoutingRegressionFamily.outgoing_mk_mem_range_channelEmbedding_iff]
    at hConnected
  exact external.2 hConnected

/-- Readout of a mixed ambient outgoing amplitude keeps only the external coefficient. -/
lemma externalChannelRegression_outgoingReadout_mixed :
    partialRoutingRegressionFamily.externalOutgoingReadout.toLinearMap
        externalChannelRegressionMixedOutgoing =
      externalChannelRegressionOutgoingPulse := by
  rw [externalChannelRegressionMixedOutgoing, map_add,
    externalChannelRegression_outgoingReadout_connected_eq_zero,
    externalChannelRegression_outgoingReadout_afterInjection]
  simp

/-- Routing of the same mixed amplitude keeps the connected coefficient at its exact mate. -/
lemma externalChannelRegression_routing_mixed_connected :
    partialRoutingRegressionFamily.partialRouting.toLinearMap
        externalChannelRegressionMixedOutgoing
          (Incident.mk partialRoutingRegressionEastFalse) = 2 + Complex.I := by
  rw [externalChannelRegressionMixedOutgoing, map_add, PiLp.add_apply]
  change partialRoutingRegressionFamily.partialRouting.toLinearMap
          externalChannelRegressionConnectedOutgoing
          (Incident.mk partialRoutingRegressionEastFalse) +
      partialRoutingRegressionFamily.partialRouting.toLinearMap
          (partialRoutingRegressionFamily.externalOutgoingInjection.toLinearMap
            externalChannelRegressionOutgoingPulse)
          (Incident.mk partialRoutingRegressionEastFalse) = 2 + Complex.I
  have hExternal :
      partialRoutingRegressionFamily.partialRouting.toLinearMap
          (partialRoutingRegressionFamily.externalOutgoingInjection.toLinearMap
            externalChannelRegressionOutgoingPulse) = 0 := by
    rw [← ModeTransform.toLinearMap_mul_apply,
      partialRoutingRegressionFamily.partialRouting_mul_externalOutgoingInjection]
    simp
  rw [hExternal, PiLp.zero_apply, add_zero]
  simpa only [externalChannelRegressionConnectedOutgoing] using
    partialRoutingRegression_connectedPulse_action

/-- Routing of the mixed amplitude still vanishes at the external incident coordinate. -/
lemma externalChannelRegression_routing_mixed_external :
    partialRoutingRegressionFamily.partialRouting.toLinearMap
        externalChannelRegressionMixedOutgoing
          (Incident.mk partialRoutingRegressionExposed) = 0 :=
  partialRoutingRegressionFamily.partialRouting_apply_of_incident_not_mem_range
    externalChannelRegressionMixedOutgoing partialRoutingRegressionExposed
      partialRoutingRegression_exposed_not_mem_range

/-- Internal routing annihilates the complete external outgoing exposure. -/
lemma externalChannelRegression_routing_mul_outgoingInjection :
    partialRoutingRegressionFamily.partialRouting *
      partialRoutingRegressionFamily.externalOutgoingInjection = 0 :=
  partialRoutingRegressionFamily.partialRouting_mul_externalOutgoingInjection

/-- External incident readout annihilates the complete internal-routing range. -/
lemma externalChannelRegression_incidentReadout_mul_routing :
    Matrix.conjTranspose partialRoutingRegressionFamily.externalIncidentInjection *
      partialRoutingRegressionFamily.partialRouting = 0 :=
  partialRoutingRegressionFamily.externalIncidentInjection_conjTranspose_mul_partialRouting

/-- Connected and external outgoing projectors resolve the five ambient coordinates. -/
lemma externalChannelRegression_outgoing_projector_completeness :
    Matrix.conjTranspose partialRoutingRegressionFamily.partialRouting *
        partialRoutingRegressionFamily.partialRouting +
      partialRoutingRegressionFamily.externalOutgoingInjection *
        Matrix.conjTranspose partialRoutingRegressionFamily.externalOutgoingInjection = 1 :=
  PortConnectionFamily.partialRouting_conjTranspose_mul_self_add_externalOutgoingProjector
    partialRoutingRegressionFamily

/-- Connected and external incident projectors resolve the five ambient coordinates. -/
lemma externalChannelRegression_incident_projector_completeness :
    partialRoutingRegressionFamily.partialRouting *
        Matrix.conjTranspose partialRoutingRegressionFamily.partialRouting +
      partialRoutingRegressionFamily.externalIncidentInjection *
        Matrix.conjTranspose partialRoutingRegressionFamily.externalIncidentInjection = 1 :=
  PortConnectionFamily.partialRouting_mul_conjTranspose_add_externalIncidentProjector
    partialRoutingRegressionFamily

/-!

## D. The assembled `C b + E_in u` incident amplitude

-/

/-- A unit external incident amplitude used beside the connected complex amplitude. -/
def externalChannelRegressionUnitPulse :
    ModeAmplitude (Incident partialRoutingRegressionFamily.ExternalChannel) :=
  PiLp.single 2 (Incident.mk partialRoutingRegressionExternal) 1

/-- The external unit amplitude has normalized modal power one. -/
lemma externalChannelRegression_unitPulse_power :
    externalChannelRegressionUnitPulse.power = 1 := by
  simp [ModeAmplitude.power, externalChannelRegressionUnitPulse]

/-- The assembled ambient incident amplitude with a connected complex input and external unit
input. -/
def externalChannelRegressionAssembly :
    ModeAmplitude (Incident partialRoutingRegressionPortFamily.Channel) :=
  partialRoutingRegressionFamily.incidentAssembly
    ((ModeTransform.zeroExtension
      partialRoutingRegressionFamily.outgoingChannelEmbedding).toLinearMap
        partialRoutingRegressionConnectedPulse)
    externalChannelRegressionUnitPulse

/-- The assembled amplitude retains the connected coefficient at east false after routing. -/
lemma externalChannelRegression_assembly_connected :
    externalChannelRegressionAssembly (Incident.mk partialRoutingRegressionEastFalse) =
      2 + Complex.I := by
  rw [externalChannelRegressionAssembly]
  change partialRoutingRegressionFamily.incidentAssembly _ _
      (Incident.mk (partialRoutingRegressionFamily.channelEmbedding
        (partialRoutingRegressionFamily.mateEquiv
          partialRoutingRegressionConnectedWestZero))) = 2 + Complex.I
  rw [partialRoutingRegressionFamily.incidentAssembly_apply_connected]
  change (ModeTransform.zeroExtension
      partialRoutingRegressionFamily.outgoingChannelEmbedding).toLinearMap
        partialRoutingRegressionConnectedPulse
          (partialRoutingRegressionFamily.outgoingChannelEmbedding
            (Outgoing.mk partialRoutingRegressionConnectedWestZero)) = 2 + Complex.I
  rw [ModeTransform.zeroExtension_apply_image]
  simp [partialRoutingRegressionConnectedPulse]

/-- The assembled amplitude retains the external unit coefficient at the exposed coordinate. -/
lemma externalChannelRegression_assembly_external :
    externalChannelRegressionAssembly (Incident.mk partialRoutingRegressionExposed) = 1 := by
  rw [externalChannelRegressionAssembly]
  change partialRoutingRegressionFamily.incidentAssembly
      ((ModeTransform.zeroExtension
        partialRoutingRegressionFamily.outgoingChannelEmbedding).toLinearMap
          partialRoutingRegressionConnectedPulse)
      externalChannelRegressionUnitPulse
        (Incident.mk partialRoutingRegressionExternal.1) = 1
  rw [partialRoutingRegressionFamily.incidentAssembly_apply_external]
  simp [externalChannelRegressionUnitPulse]

/-- The disjoint connected and external parts of the assembled amplitude have total power six. -/
lemma externalChannelRegression_assembly_power :
    externalChannelRegressionAssembly.power = 6 := by
  rw [externalChannelRegressionAssembly,
    partialRoutingRegressionFamily.incidentAssembly_power,
    ← ModeTransform.toLinearMap_restriction,
    ModeTransform.restriction_apply_zeroExtension,
    partialRoutingRegression_connectedPulse_power,
    externalChannelRegression_unitPulse_power]
  norm_num

/-!

## E. An unconnected port with an empty mode fiber

-/

/-- The dependent mode fibers for the empty-exposed-port regression. -/
abbrev externalChannelEmptyMode : PartialRoutingRegressionPort → Type
  | .west => Fin 2
  | .east => Bool
  | .exposed => Empty

instance externalChannelEmptyModeDecidableEq
    (port : PartialRoutingRegressionPort) : DecidableEq (externalChannelEmptyMode port) := by
  cases port <;> infer_instance

instance externalChannelEmptyModeFintype
    (port : PartialRoutingRegressionPort) : Fintype (externalChannelEmptyMode port) := by
  cases port <;> infer_instance

/-- The ambient family whose unconnected third port has no modeled modes. -/
abbrev externalChannelEmptyPortFamily : PortModeFamily where
  Port := PartialRoutingRegressionPort
  Mode := externalChannelEmptyMode

/-- The west-to-east connection in the empty-exposed-port regression. -/
abbrev externalChannelEmptyConnection : PortConnection externalChannelEmptyPortFamily where
  left := .west
  right := .east
  left_ne_right := by decide
  modeEquiv := finTwoEquiv

/-- The valid connection family leaving the empty third port unconnected. -/
abbrev externalChannelEmptyFamily :
    PortConnectionFamily externalChannelEmptyPortFamily Unit where
  connection _ := externalChannelEmptyConnection
  endpointPort_injective := by decide

/-- The empty third port is structurally absent from the connection endpoints. -/
lemma externalChannelEmpty_exposedPort_not_mem_range :
    PartialRoutingRegressionPort.exposed ∉
      Set.range externalChannelEmptyFamily.endpointEmbedding := by
  rintro ⟨⟨index, endpoint⟩, hPort⟩
  rcases index with ⟨⟩
  cases endpoint <;> cases hPort

/-- Every modeled channel is also selected by the connected-channel embedding. -/
lemma externalChannelEmpty_channelEmbedding_surjective :
    Function.Surjective externalChannelEmptyFamily.channelEmbedding := by
  rintro ⟨port, mode⟩
  cases port
  · exact ⟨⟨(), Sum.inl mode⟩, rfl⟩
  · exact ⟨⟨(), Sum.inr mode⟩, rfl⟩
  · exact mode.elim

/-- An unconnected physical port with an empty mode fiber creates no external channel. -/
lemma externalChannelEmpty_isEmpty : IsEmpty externalChannelEmptyFamily.ExternalChannel :=
  ⟨fun channel => channel.2 (externalChannelEmpty_channelEmbedding_surjective channel.1)⟩

end

end Optics
