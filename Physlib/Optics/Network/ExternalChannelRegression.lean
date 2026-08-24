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
This file identifies that complement exactly, tests the incident injection with a genuinely complex
coefficient, and checks the coordinate and power laws of the expression `C b + E u`.

A second valid three-port family gives its unconnected third port an empty mode fiber. Its connected
channel embedding is surjective even though the third physical port is unused. This fixes the
channel-versus-port distinction: an unconnected empty port contributes no external channel.

## ii. Scope

These are finite normalized-coordinate regressions. The external injection supplies no source,
termination, outgoing extraction, electromagnetic normalization, or feedback solution.

## iii. Table of contents

- A. The sole nonempty external channel
- B. Exact incident injection
- C. The assembled `C b + E u` incident amplitude
- D. An unconnected port with an empty mode fiber

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

## C. The assembled `C b + E u` incident amplitude

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

## D. An unconnected port with an empty mode fiber

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
