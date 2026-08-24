/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.PartialRouting

/-!
# External optical channels and incident injection

## i. Overview

A connection family selects the ambient channels that belong to internal routing. This file
defines its external channels as the exact complement of that selected range, proves that connected
and external channels form a complete disjoint partition, and lifts the external inclusion to the
nominal incident endpoint type.

The resulting zero-extension transform is the typed external incident injection `E` in the
algebraic expression `a = C b + E u`, where `C` is ambient partial routing. The coordinate and power
laws below show that `C b` and `E u` have disjoint support in complementary incident coordinates.

## ii. Scope

External status is defined first at the channel level. `UnconnectedPort` separately records the
complement of the endpoint-port range, and external channels are the dependent sum of modeled mode
fibers over those ports. There is no one-channel-per-port identification: an unconnected port with
several modeled modes contributes several external channels, while one with an empty mode fiber
contributes none.

The injection assigns amplitudes to already declared external incident coordinates; it does not
model a source impedance, termination, incoming-wave data, feedback solvability,
electromagnetic power, or an electromagnetic boundary condition. Complement outgoing coordinates
are absent from `C b` because `C` does not route them internally, not because they are absorbed.
Consequently, the modal-power identity below is not a network energy balance.

## iii. Key definitions and results

- `PortConnectionFamily.ExternalChannel`: ambient channels outside the connected range.
- `PortConnectionFamily.channelPartitionEquiv`: connected and external channels exactly partition
  the ambient channel type.
- `PortConnectionFamily.externalChannelEquivUnconnectedPortModes`: external channels are the
  dependent sum of modes over structurally unconnected ports.
- `PortConnectionFamily.externalIncidentInjection`: the typed external incident injection.
- `PortConnectionFamily.incidentAssembly`: the coordinate-level expression `C b + E u`.
- `PortConnectionFamily.incidentAssembly_power`: connected and external modal powers add because
  their incident-coordinate ranges are disjoint.

## iv. Table of contents

- A. The external-channel complement
- B. External incident injection
- C. The assembled incident amplitude

-/

@[expose] public section

namespace Optics

open Matrix
open scoped ComplexConjugate

noncomputable section

universe u v w

namespace PortConnectionFamily

variable {P : PortModeFamily.{u, v}} {ι : Type w} (family : PortConnectionFamily P ι)

/-!

## A. The external-channel complement

-/

/-- The ambient channels not selected by a connection family's connected-channel embedding. -/
abbrev ExternalChannel := (Set.range family.channelEmbedding)ᶜ

/-- The physical ports not selected by any indexed connection endpoint. -/
abbrev UnconnectedPort := (Set.range family.endpointEmbedding)ᶜ

/-- The inclusion of external channels into the ambient physical-channel type. -/
def externalChannelEmbedding : family.ExternalChannel ↪ P.Channel :=
  Function.Embedding.subtype _

/-- The external-channel embedding returns the underlying ambient channel. -/
@[simp]
lemma externalChannelEmbedding_apply (channel : family.ExternalChannel) :
    family.externalChannelEmbedding channel = channel.1 := rfl

/-- An external channel is outside the connected-channel range. -/
lemma externalChannel_not_mem_connectedRange (channel : family.ExternalChannel) :
    channel.1 ∉ Set.range family.channelEmbedding := channel.2

/-- An ambient channel lies in the external embedding exactly when it is not connected. -/
lemma mem_range_externalChannelEmbedding_iff (channel : P.Channel) :
    channel ∈ Set.range family.externalChannelEmbedding ↔
      channel ∉ Set.range family.channelEmbedding := by
  constructor
  · rintro ⟨external, rfl⟩
    exact external.2
  · intro hChannel
    exact ⟨⟨channel, hChannel⟩, rfl⟩

/-- Connected and external channel embeddings have disjoint values. -/
lemma channelEmbedding_ne_externalChannelEmbedding (connected : family.Channel)
    (external : family.ExternalChannel) :
    family.channelEmbedding connected ≠ family.externalChannelEmbedding external := by
  intro hChannel
  apply external.2
  exact ⟨connected, hChannel⟩

/-- External channels are exactly the modeled mode fibers over structurally unconnected ports.

Because the codomain is a dependent sum, an unconnected port contributes one external channel per
declared mode and contributes none when its mode fiber is empty.
-/
def externalChannelEquivUnconnectedPortModes :
    family.ExternalChannel ≃ Σ port : family.UnconnectedPort, P.Mode port.1 where
  toFun channel :=
    ⟨⟨channel.1.1, fun hPort => channel.2
      ((family.channel_mem_range_channelEmbedding_iff channel.1).mpr hPort)⟩,
      channel.1.2⟩
  invFun channel :=
    ⟨⟨channel.1.1, channel.2⟩, fun hChannel => channel.1.2
      ((family.channel_mem_range_channelEmbedding_iff
        ⟨channel.1.1, channel.2⟩).mp hChannel)⟩
  left_inv := by
    rintro ⟨⟨port, mode⟩, hChannel⟩
    rfl
  right_inv := by
    rintro ⟨⟨port, hPort⟩, mode⟩
    rfl

/-- Connected and external channel labels form the complete ambient channel type. -/
noncomputable def channelPartitionEquiv :
    family.Channel ⊕ family.ExternalChannel ≃ P.Channel := by
  classical
  exact
    ((Equiv.ofInjective family.channelEmbedding family.channelEmbedding.injective).sumCongr
      (Equiv.refl family.ExternalChannel)).trans
        (Equiv.Set.sumCompl (Set.range family.channelEmbedding))

/-- The channel partition equivalence includes a connected channel through its embedding. -/
@[simp]
lemma channelPartitionEquiv_apply_inl (channel : family.Channel) :
    family.channelPartitionEquiv (Sum.inl channel) = family.channelEmbedding channel := rfl

/-- The channel partition equivalence includes an external channel through its embedding. -/
@[simp]
lemma channelPartitionEquiv_apply_inr (channel : family.ExternalChannel) :
    family.channelPartitionEquiv (Sum.inr channel) =
      family.externalChannelEmbedding channel := rfl

/-- Applying the inverse partition to an embedded connected channel returns its connected label. -/
@[simp]
lemma channelPartitionEquiv_symm_channelEmbedding (channel : family.Channel) :
    family.channelPartitionEquiv.symm (family.channelEmbedding channel) =
      Sum.inl channel := by
  apply family.channelPartitionEquiv.injective
  simp

/-- Applying the inverse partition to an embedded external channel returns its external label. -/
@[simp]
lemma channelPartitionEquiv_symm_externalChannelEmbedding
    (channel : family.ExternalChannel) :
    family.channelPartitionEquiv.symm channel.1 =
      Sum.inr channel := by
  apply family.channelPartitionEquiv.injective
  simp

/-!

## B. External incident injection

-/

/-- The external-channel embedding lifted to nominal incident endpoint labels. -/
def externalIncidentEmbedding :
    Incident family.ExternalChannel ↪ Incident P.Channel :=
  Incident.relabelEmbedding family.externalChannelEmbedding

/-- An external incident endpoint embeds at its underlying ambient physical channel. -/
@[simp]
lemma externalIncidentEmbedding_apply (channel : family.ExternalChannel) :
    family.externalIncidentEmbedding (Incident.mk channel) =
      Incident.mk channel.1 := rfl

/-- An ambient incident endpoint lies in the external range exactly when its channel is not
connected. -/
lemma incident_mk_mem_range_externalChannelEmbedding_iff (channel : P.Channel) :
    Incident.mk channel ∈ Set.range family.externalIncidentEmbedding ↔
      channel ∉ Set.range family.channelEmbedding := by
  change Incident.mk channel ∈
      Set.range (Incident.relabelEmbedding family.externalChannelEmbedding) ↔ _
  rw [Incident.mk_mem_range_relabelEmbedding_iff,
    family.mem_range_externalChannelEmbedding_iff]

/-- Connected and external incident embeddings have disjoint values. -/
lemma incidentChannelEmbedding_ne_externalIncidentEmbedding
    (connected : Incident family.Channel) (external : Incident family.ExternalChannel) :
    family.incidentChannelEmbedding connected ≠
      family.externalIncidentEmbedding external := by
  intro hEndpoint
  apply external.channel.2
  exact ⟨connected.channel, congrArg Incident.channel hEndpoint⟩

/-- Connected and external incident endpoints exactly partition the ambient incident type. -/
noncomputable def incidentPartitionEquiv :
    Incident family.Channel ⊕ Incident family.ExternalChannel ≃ Incident P.Channel :=
  (Incident.channelEquiv.sumCongr Incident.channelEquiv).trans
    (family.channelPartitionEquiv.trans Incident.channelEquiv.symm)

/-- The incident partition equivalence includes a connected incident endpoint. -/
@[simp]
lemma incidentPartitionEquiv_apply_inl (channel : Incident family.Channel) :
    family.incidentPartitionEquiv (Sum.inl channel) =
      family.incidentChannelEmbedding channel := by
  rcases channel with ⟨channel⟩
  rfl

/-- The incident partition equivalence includes an external incident endpoint. -/
@[simp]
lemma incidentPartitionEquiv_apply_inr (channel : Incident family.ExternalChannel) :
    family.incidentPartitionEquiv (Sum.inr channel) =
      family.externalIncidentEmbedding channel := by
  rcases channel with ⟨channel⟩
  rfl

/-- Extend an external incident amplitude by zero to all ambient incident coordinates.

This is the injection transform `E` in `a = C b + E u`; it supplies no source or termination
physics beyond the declared external amplitude `u`.
-/
def externalIncidentInjection [DecidableEq P.Channel] :
    ModeTransform (Incident family.ExternalChannel) (Incident P.Channel) :=
  ModeTransform.zeroExtension family.externalIncidentEmbedding

/-- External incident injection has a unit entry at every selected external coordinate. -/
@[simp]
lemma externalIncidentInjection_entry_external [DecidableEq P.Channel]
    (channel : family.ExternalChannel) :
    family.externalIncidentInjection (Incident.mk channel.1) (Incident.mk channel) = 1 := by
  simp [externalIncidentInjection]

/-- External incident injection has a zero entry from an external input to a connected ambient
coordinate. -/
lemma externalIncidentInjection_entry_connected [DecidableEq P.Channel]
    (connected : family.Channel) (external : family.ExternalChannel) :
    family.externalIncidentInjection
        (Incident.mk (family.channelEmbedding connected)) (Incident.mk external) = 0 := by
  have hNe : family.externalIncidentEmbedding (Incident.mk external) ≠
      Incident.mk (family.channelEmbedding connected) := by
    intro hChannel
    exact family.channelEmbedding_ne_externalChannelEmbedding connected external
      (congrArg Incident.channel hChannel).symm
  simp only [externalIncidentInjection, ModeTransform.zeroExtension_entry,
    if_neg hNe]

/-- External incident injection recovers the exact amplitude at every external coordinate. -/
@[simp]
lemma externalIncidentInjection_apply_external
    [Fintype family.ExternalChannel] [DecidableEq P.Channel]
    (amplitude : ModeAmplitude (Incident family.ExternalChannel))
    (channel : family.ExternalChannel) :
    family.externalIncidentInjection.toLinearMap amplitude (Incident.mk channel.1) =
      amplitude (Incident.mk channel) := by
  exact ModeTransform.zeroExtension_apply_image family.externalIncidentEmbedding amplitude
    (Incident.mk channel)

/-- External incident injection vanishes at every connected incident coordinate. -/
lemma externalIncidentInjection_apply_connected
    [Fintype family.ExternalChannel] [DecidableEq P.Channel]
    (amplitude : ModeAmplitude (Incident family.ExternalChannel))
    (channel : family.Channel) :
    family.externalIncidentInjection.toLinearMap amplitude
        (Incident.mk (family.channelEmbedding channel)) = 0 := by
  apply ModeTransform.zeroExtension_apply_of_not_mem_range
    family.externalIncidentEmbedding amplitude
  intro hRange
  rw [family.incident_mk_mem_range_externalChannelEmbedding_iff] at hRange
  exact hRange ⟨channel, rfl⟩

/-- External incident injection preserves normalized external modal power. -/
lemma externalIncidentInjection_isPowerPreserving
    [Fintype family.ExternalChannel]
    [Fintype P.Channel] [DecidableEq P.Channel] :
    family.externalIncidentInjection.IsPowerPreserving :=
  ModeTransform.zeroExtension_isPowerPreserving family.externalIncidentEmbedding

/-- External incident injection is an isometry of finite normalized mode-amplitude spaces. -/
lemma externalIncidentInjection_isometry
    [Fintype family.ExternalChannel]
    [Fintype P.Channel] [DecidableEq P.Channel] :
    Isometry family.externalIncidentInjection.toLinearMap :=
  ModeTransform.zeroExtension_isometry family.externalIncidentEmbedding

/-- The input-side Gram matrix of external incident injection is the identity. -/
lemma externalIncidentInjection_conjTranspose_mul_self
    [Fintype P.Channel] [DecidableEq P.Channel] :
    (PortConnectionFamily.externalIncidentInjection family)ᴴ *
      family.externalIncidentInjection = 1 := by
  simpa only [externalIncidentInjection, ModeTransform.zeroExtension_conjTranspose] using
    ModeTransform.restriction_mul_zeroExtension family.externalIncidentEmbedding

/-- The output-side Gram matrix of external incident injection is its ambient range projector. -/
lemma externalIncidentInjection_mul_conjTranspose
    [Fintype family.ExternalChannel] [DecidableEq P.Channel] :
    family.externalIncidentInjection *
        (PortConnectionFamily.externalIncidentInjection family)ᴴ =
      ModeTransform.rangeProjector family.externalIncidentEmbedding := by
  simp only [externalIncidentInjection, ModeTransform.zeroExtension_conjTranspose]
  rfl

/-!

## C. The assembled incident amplitude

-/

/-- The ambient incident amplitude `C b + E u` from internal routing and external injection.

This is only an algebraic right-hand side. It does not assert that a component law supplies `b`,
that a fixed point exists, or that the resulting network is uniquely solvable.
-/
def incidentAssembly [Fintype family.Channel] [DecidableEq family.Channel]
    [Fintype P.Channel] [DecidableEq P.Channel]
    (outgoing : ModeAmplitude (Outgoing P.Channel))
    (external : ModeAmplitude (Incident family.ExternalChannel)) :
    ModeAmplitude (Incident P.Channel) :=
  family.partialRouting.toLinearMap outgoing +
    family.externalIncidentInjection.toLinearMap external

/-- On a connected coordinate, the assembled incident amplitude is the outgoing amplitude after
internal routing and is independent of the external input. -/
lemma incidentAssembly_apply_connected
    [Fintype family.Channel] [DecidableEq family.Channel]
    [Fintype P.Channel] [DecidableEq P.Channel]
    (outgoing : ModeAmplitude (Outgoing P.Channel))
    (external : ModeAmplitude (Incident family.ExternalChannel))
    (channel : family.Channel) :
    family.incidentAssembly outgoing external
        (Incident.mk (family.channelEmbedding (family.mateEquiv channel))) =
      outgoing (Outgoing.mk (family.channelEmbedding channel)) := by
  rw [incidentAssembly, PiLp.add_apply, family.partialRouting_apply_internal,
    family.externalIncidentInjection_apply_connected]
  simp

/-- At a connected incident channel, the assembled amplitude comes from the outgoing amplitude at
the channel's connected mate. -/
@[simp]
lemma incidentAssembly_apply_connected_channel
    [Fintype family.Channel] [DecidableEq family.Channel]
    [Fintype P.Channel] [DecidableEq P.Channel]
    (outgoing : ModeAmplitude (Outgoing P.Channel))
    (external : ModeAmplitude (Incident family.ExternalChannel))
    (channel : family.Channel) :
    family.incidentAssembly outgoing external
        (Incident.mk (family.channelEmbedding channel)) =
      outgoing (Outgoing.mk (family.channelEmbedding (family.mateEquiv channel))) := by
  simpa only [family.mateEquiv_apply_apply] using
    family.incidentAssembly_apply_connected outgoing external (family.mateEquiv channel)

/-- On an external coordinate, the assembled incident amplitude is the exact external input and is
independent of the internal-routing outgoing amplitude. -/
@[simp]
lemma incidentAssembly_apply_external
    [Fintype family.Channel] [DecidableEq family.Channel]
    [Fintype P.Channel] [DecidableEq P.Channel]
    (outgoing : ModeAmplitude (Outgoing P.Channel))
    (external : ModeAmplitude (Incident family.ExternalChannel))
    (channel : family.ExternalChannel) :
    family.incidentAssembly outgoing external (Incident.mk channel.1) =
      external (Incident.mk channel) := by
  rw [incidentAssembly, PiLp.add_apply,
    family.partialRouting_apply_of_incident_not_mem_range outgoing channel.1 channel.2,
    family.externalIncidentInjection_apply_external]
  simp

/-- The assembled incident amplitude is the relabeled direct sum of the connected input after
routing and the external input. -/
lemma incidentAssembly_eq_reindex_directSum
    [Fintype family.Channel] [DecidableEq family.Channel]
    [Fintype P.Channel] [DecidableEq P.Channel]
    (outgoing : ModeAmplitude (Outgoing P.Channel))
    (external : ModeAmplitude (Incident family.ExternalChannel)) :
    family.incidentAssembly outgoing external =
      ModeAmplitude.reindex family.incidentPartitionEquiv
        ((family.idealRouting.toLinearMap
          (outgoing.restrictEmbedding family.outgoingChannelEmbedding)).directSum external) := by
  apply (ModeAmplitude.reindex family.incidentPartitionEquiv.symm).injective
  rw [ModeAmplitude.reindex_symm_reindex]
  apply WithLp.ofLp_injective 2
  funext endpoint
  rcases endpoint with connected | externalChannel
  · rcases connected with ⟨channel⟩
    rw [ModeAmplitude.reindex_apply, Equiv.symm_symm,
      family.incidentPartitionEquiv_apply_inl,
      family.incidentChannelEmbedding_apply,
      family.incidentAssembly_apply_connected_channel]
    change outgoing (Outgoing.mk (family.channelEmbedding (family.mateEquiv channel))) =
      family.idealRouting.toLinearMap
        (outgoing.restrictEmbedding family.outgoingChannelEmbedding) (Incident.mk channel)
    simpa only [family.mateEquiv_apply_apply,
      ModeAmplitude.restrictEmbedding_apply,
      family.outgoingChannelEmbedding_apply] using
        (family.idealRouting_apply
          (outgoing.restrictEmbedding family.outgoingChannelEmbedding)
            (family.mateEquiv channel)).symm
  · rcases externalChannel with ⟨channel⟩
    rw [ModeAmplitude.reindex_apply, Equiv.symm_symm,
      family.incidentPartitionEquiv_apply_inr,
      family.externalIncidentEmbedding_apply,
      family.incidentAssembly_apply_external]
    rfl

/-- The normalized modal power of the assembled incident amplitude is the sum of the power in the
connected restriction of the outgoing amplitude and the external incident amplitude. -/
lemma incidentAssembly_power
    [Fintype family.Channel] [DecidableEq family.Channel]
    [Fintype P.Channel] [DecidableEq P.Channel]
    (outgoing : ModeAmplitude (Outgoing P.Channel))
    (external : ModeAmplitude (Incident family.ExternalChannel)) :
    (family.incidentAssembly outgoing external).power =
      (outgoing.restrictEmbedding family.outgoingChannelEmbedding).power + external.power := by
  rw [family.incidentAssembly_eq_reindex_directSum, ModeAmplitude.power_reindex,
    ModeAmplitude.power_directSum]
  exact congrArg (· + external.power)
    (family.idealRouting_isPowerPreserving
      (outgoing.restrictEmbedding family.outgoingChannelEmbedding))

end PortConnectionFamily

end

end Optics
