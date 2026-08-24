/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Mode.Embedding
public import Physlib.Optics.Network.ConnectionFamily

/-!
# Ambient partial routing for optical connection families

## i. Overview

A proof-carrying connection family defines unit-gain routing on its connected channels. This file
lifts that transform to every channel in the ambient port family: routing sends connected outgoing
coordinates to their mates, while coordinates outside the connected-channel embedding are ignored
on input and zero on output.

The ambient transform is globally passive and preserves power exactly on amplitudes supported on
connected outgoing channels. The exact power-equality characterization records this support
condition rather than describing the transform as globally lossless.

## ii. Scope

An outside-range coordinate is algebraically outside the selected connection subspace. Zero action
on that coordinate does not model a matched termination, absorption, radiation, or any physical
boundary condition. This file does not construct a complementary external-channel type, add an
external excitation, connect components, or solve a feedback equation. Its power statements use
only the finite power-normalized modal convention.

## iii. Key definitions and results

- `PortConnectionFamily.incidentChannelEmbedding` and
  `PortConnectionFamily.outgoingChannelEmbedding`: lift the connected-channel embedding to the
  nominal endpoint types.
- `PortConnectionFamily.partialRouting`: include connected ideal routing in the full ambient
  endpoint spaces.
- `PortConnectionFamily.partialRouting_apply_internal`: exact routing on every connected channel.
- `PortConnectionFamily.partialRouting_conjTranspose_mul_self` and
  `PortConnectionFamily.partialRouting_mul_conjTranspose`: the two Gram matrices are the connected
  outgoing and incident range projectors.
- `PortConnectionFamily.partialRouting_power`: output power is the power of the connected part of
  the input.
- `PortConnectionFamily.partialRouting_power_eq_iff`: ambient power is preserved exactly when all
  complement outgoing coordinates vanish.
- `PortConnectionFamily.partialRouting_isPassive`: ambient partial routing is globally passive.

## iv. Table of contents

- A. Directed connected-channel embeddings
- B. Ambient partial routing entries
- C. Exact amplitude action
- D. Partial-isometry projectors, power, and passivity

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

## A. Directed connected-channel embeddings

-/

/-- The connected-channel embedding lifted to incident endpoint labels. -/
def incidentChannelEmbedding : Incident family.Channel ↪ Incident P.Channel :=
  Incident.relabelEmbedding family.channelEmbedding

/-- The connected-channel embedding lifted to outgoing endpoint labels. -/
def outgoingChannelEmbedding : Outgoing family.Channel ↪ Outgoing P.Channel :=
  Outgoing.relabelEmbedding family.channelEmbedding

/-- A connected incident endpoint embeds at its exact ambient physical channel. -/
@[simp]
lemma incidentChannelEmbedding_apply (channel : family.Channel) :
    family.incidentChannelEmbedding (Incident.mk channel) =
      Incident.mk (family.channelEmbedding channel) := rfl

/-- A connected outgoing endpoint embeds at its exact ambient physical channel. -/
@[simp]
lemma outgoingChannelEmbedding_apply (channel : family.Channel) :
    family.outgoingChannelEmbedding (Outgoing.mk channel) =
      Outgoing.mk (family.channelEmbedding channel) := rfl

/-- An ambient incident endpoint lies in the connected range exactly when its physical channel
does. -/
lemma incident_mk_mem_range_channelEmbedding_iff (channel : P.Channel) :
    Incident.mk channel ∈ Set.range family.incidentChannelEmbedding ↔
      channel ∈ Set.range family.channelEmbedding := by
  exact Incident.mk_mem_range_relabelEmbedding_iff family.channelEmbedding channel

/-- An ambient outgoing endpoint lies in the connected range exactly when its physical channel
does. -/
lemma outgoing_mk_mem_range_channelEmbedding_iff (channel : P.Channel) :
    Outgoing.mk channel ∈ Set.range family.outgoingChannelEmbedding ↔
      channel ∈ Set.range family.channelEmbedding := by
  exact Outgoing.mk_mem_range_relabelEmbedding_iff family.channelEmbedding channel

/-!

## B. Ambient partial routing entries

-/

/-- Include a connection family's ideal routing in its full ambient endpoint spaces.

Outgoing coordinates outside the connected range are ignored and incident coordinates outside the
connected range are zero. This is a sparse algebraic inclusion, not a physical termination law.
-/
def partialRouting [Fintype family.Channel] [DecidableEq family.Channel]
    [DecidableEq P.Channel] : ModeTransform (Outgoing P.Channel) (Incident P.Channel) :=
  family.idealRouting.zeroExtend family.outgoingChannelEmbedding
    family.incidentChannelEmbedding

/-- Ambient partial routing retains every entry of the connected routing block. -/
@[simp]
lemma partialRouting_entry_connected [Fintype family.Channel] [DecidableEq family.Channel]
    [DecidableEq P.Channel] (output input : family.Channel) :
    family.partialRouting (Incident.mk (family.channelEmbedding output))
        (Outgoing.mk (family.channelEmbedding input)) =
      family.idealRouting (Incident.mk output) (Outgoing.mk input) := by
  exact ModeTransform.zeroExtend_entry_image family.idealRouting
    family.outgoingChannelEmbedding family.incidentChannelEmbedding
      (Incident.mk output) (Outgoing.mk input)

/-- Routing sends every connected outgoing channel to its connected mate with unit gain. -/
lemma partialRouting_entry_mate [Fintype family.Channel] [DecidableEq family.Channel]
    [DecidableEq P.Channel] (channel : family.Channel) :
    family.partialRouting
        (Incident.mk (family.channelEmbedding (family.mateEquiv channel)))
        (Outgoing.mk (family.channelEmbedding channel)) = 1 := by
  rw [family.partialRouting_entry_connected]
  exact family.idealRouting_entry_mate channel

/-- An ambient channel outside the connected range gives a zero incident row. -/
lemma partialRouting_entry_of_incident_not_mem_range
    [Fintype family.Channel] [DecidableEq family.Channel] [DecidableEq P.Channel]
    (incident : P.Channel) (hIncident : incident ∉ Set.range family.channelEmbedding)
    (outgoing : Outgoing P.Channel) :
    family.partialRouting (Incident.mk incident) outgoing = 0 := by
  apply ModeTransform.zeroExtend_entry_of_output_not_mem_range family.idealRouting
    family.outgoingChannelEmbedding family.incidentChannelEmbedding
  simpa only [family.incident_mk_mem_range_channelEmbedding_iff]

/-- An ambient channel outside the connected range gives a zero outgoing column. -/
lemma partialRouting_entry_of_outgoing_not_mem_range
    [Fintype family.Channel] [DecidableEq family.Channel] [DecidableEq P.Channel]
    (outgoing : P.Channel) (hOutgoing : outgoing ∉ Set.range family.channelEmbedding)
    (incident : Incident P.Channel) :
    family.partialRouting incident (Outgoing.mk outgoing) = 0 := by
  apply ModeTransform.zeroExtend_entry_of_input_not_mem_range family.idealRouting
    family.outgoingChannelEmbedding family.incidentChannelEmbedding
  simpa only [family.outgoing_mk_mem_range_channelEmbedding_iff]

/-!

## C. Exact amplitude action

-/

/-- Ambient partial routing restricts an arbitrary outgoing amplitude to connected channels,
routes it internally, and extends the incident result by zero. -/
lemma partialRouting_apply [Fintype family.Channel] [DecidableEq family.Channel]
    [Fintype P.Channel] [DecidableEq P.Channel]
    (amplitude : ModeAmplitude (Outgoing P.Channel)) :
    family.partialRouting.toLinearMap amplitude =
      (ModeTransform.zeroExtension family.incidentChannelEmbedding).toLinearMap
        (family.idealRouting.toLinearMap
          (amplitude.restrictEmbedding family.outgoingChannelEmbedding)) := by
  exact ModeTransform.zeroExtend_apply family.idealRouting family.outgoingChannelEmbedding
    family.incidentChannelEmbedding amplitude

/-- Every connected outgoing amplitude reaches its exact ambient incident mate, even when the
ambient input also has complement-coordinate amplitudes. -/
@[simp]
lemma partialRouting_apply_internal [Fintype family.Channel] [DecidableEq family.Channel]
    [Fintype P.Channel] [DecidableEq P.Channel]
    (amplitude : ModeAmplitude (Outgoing P.Channel)) (channel : family.Channel) :
    family.partialRouting.toLinearMap amplitude
        (Incident.mk (family.channelEmbedding (family.mateEquiv channel))) =
      amplitude (Outgoing.mk (family.channelEmbedding channel)) := by
  rw [family.partialRouting_apply]
  change (ModeTransform.zeroExtension family.incidentChannelEmbedding).toLinearMap
      (family.idealRouting.toLinearMap
        (amplitude.restrictEmbedding family.outgoingChannelEmbedding))
        (family.incidentChannelEmbedding (Incident.mk (family.mateEquiv channel))) =
    amplitude (family.outgoingChannelEmbedding (Outgoing.mk channel))
  rw [ModeTransform.zeroExtension_apply_image]
  rw [family.idealRouting_apply]
  rfl

/-- Every ambient incident coordinate outside the connected range has zero output amplitude. -/
lemma partialRouting_apply_of_incident_not_mem_range
    [Fintype family.Channel] [DecidableEq family.Channel]
    [Fintype P.Channel] [DecidableEq P.Channel]
    (amplitude : ModeAmplitude (Outgoing P.Channel)) (channel : P.Channel)
    (hChannel : channel ∉ Set.range family.channelEmbedding) :
    family.partialRouting.toLinearMap amplitude (Incident.mk channel) = 0 := by
  rw [family.partialRouting_apply]
  apply ModeTransform.zeroExtension_apply_of_not_mem_range
  simpa only [family.incident_mk_mem_range_channelEmbedding_iff]

/-- On a zero-extended connected input, ambient partial routing is exactly the zero extension of
connected ideal routing. -/
lemma partialRouting_apply_zeroExtension
    [Fintype family.Channel] [DecidableEq family.Channel]
    [Fintype P.Channel] [DecidableEq P.Channel]
    (amplitude : ModeAmplitude (Outgoing family.Channel)) :
    family.partialRouting.toLinearMap
        ((ModeTransform.zeroExtension family.outgoingChannelEmbedding).toLinearMap amplitude) =
      (ModeTransform.zeroExtension family.incidentChannelEmbedding).toLinearMap
        (family.idealRouting.toLinearMap amplitude) := by
  exact ModeTransform.zeroExtend_apply_zeroExtension family.idealRouting
    family.outgoingChannelEmbedding family.incidentChannelEmbedding amplitude

/-!

## D. Partial-isometry projectors, power, and passivity

-/

/-- The input-side Gram matrix of ambient partial routing is exactly the projector onto connected
outgoing channels. -/
lemma partialRouting_conjTranspose_mul_self
    [Fintype family.Channel] [DecidableEq family.Channel]
    [Fintype P.Channel] [DecidableEq P.Channel] :
    family.partialRoutingᴴ * family.partialRouting =
      ModeTransform.rangeProjector family.outgoingChannelEmbedding := by
  exact ModeTransform.zeroExtend_conjTranspose_mul_self family.idealRouting
    family.outgoingChannelEmbedding family.incidentChannelEmbedding
      (ModeTransform.idealRouting_conjTranspose_mul_self family.mateEquiv)

/-- The output-side Gram matrix of ambient partial routing is exactly the projector onto connected
incident channels. -/
lemma partialRouting_mul_conjTranspose
    [Fintype family.Channel] [DecidableEq family.Channel]
    [Fintype P.Channel] [DecidableEq P.Channel] :
    family.partialRouting * family.partialRoutingᴴ =
      ModeTransform.rangeProjector family.incidentChannelEmbedding := by
  exact ModeTransform.zeroExtend_mul_conjTranspose family.idealRouting
    family.outgoingChannelEmbedding family.incidentChannelEmbedding
      (ModeTransform.idealRouting_mul_conjTranspose family.mateEquiv)

/-- The output power of ambient partial routing is exactly the power in the connected part of the
outgoing input. -/
lemma partialRouting_power [Fintype family.Channel] [DecidableEq family.Channel]
    [Fintype P.Channel] [DecidableEq P.Channel]
    (amplitude : ModeAmplitude (Outgoing P.Channel)) :
    (family.partialRouting.toLinearMap amplitude).power =
      (amplitude.restrictEmbedding family.outgoingChannelEmbedding).power := by
  rw [partialRouting, ModeTransform.zeroExtend_power]
  exact family.idealRouting_isPowerPreserving _

/-- Ambient partial routing preserves the power of a particular amplitude exactly when every
outgoing coordinate outside the connected range has zero amplitude. -/
lemma partialRouting_power_eq_iff [Fintype family.Channel] [DecidableEq family.Channel]
    [Fintype P.Channel] [DecidableEq P.Channel]
    (amplitude : ModeAmplitude (Outgoing P.Channel)) :
    (family.partialRouting.toLinearMap amplitude).power = amplitude.power ↔
      ∀ channel, channel ∉ Set.range family.channelEmbedding →
        amplitude (Outgoing.mk channel) = 0 := by
  rw [family.partialRouting_power,
    ModeAmplitude.power_restrictEmbedding_eq_iff]
  constructor
  · intro hAmplitude channel hChannel
    apply hAmplitude (Outgoing.mk channel)
    simpa only [family.outgoing_mk_mem_range_channelEmbedding_iff]
  · intro hAmplitude endpoint hEndpoint
    rcases endpoint with ⟨channel⟩
    apply hAmplitude channel
    simpa only [family.outgoing_mk_mem_range_channelEmbedding_iff] using hEndpoint

/-- Ambient partial routing is passive on every finite power-normalized mode amplitude. -/
lemma partialRouting_isPassive [Fintype family.Channel] [DecidableEq family.Channel]
    [Fintype P.Channel] [DecidableEq P.Channel] : family.partialRouting.IsPassive := by
  exact family.idealRouting_isPowerPreserving.isPassive.zeroExtend
    family.outgoingChannelEmbedding family.incidentChannelEmbedding

/-- Ambient partial routing preserves the full power of every zero-extended connected input. -/
lemma partialRouting_power_zeroExtension
    [Fintype family.Channel] [DecidableEq family.Channel]
    [Fintype P.Channel] [DecidableEq P.Channel]
    (amplitude : ModeAmplitude (Outgoing family.Channel)) :
    (family.partialRouting.toLinearMap
        ((ModeTransform.zeroExtension family.outgoingChannelEmbedding).toLinearMap
          amplitude)).power = amplitude.power := by
  rw [family.partialRouting_power,
    ← ModeTransform.toLinearMap_restriction,
    ModeTransform.restriction_apply_zeroExtension]

end PortConnectionFamily

end

end Optics
