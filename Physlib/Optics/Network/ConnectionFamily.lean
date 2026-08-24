/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.Port

/-!
# Typed families of optical port connections

## i. Overview

This file assembles local optical port connections into an indexed family. Each indexed end retains
its connection index and whether it is the left or right end. A family stores a proof that the
resulting map to physical ports is injective, so no port can be reused by two connections or form
wire-level fan-out.

The connected channel type retains the connection index and the dependent local mode fiber. Its
embedding into the ambient port-family channels is derived from physical-port uniqueness. The
family mate and ideal routing are assembled blockwise from the existing local mates; they never
pair channels in different connections.

## ii. Scope

This file models only channels at connected ports. It does not construct the complementary
external ports, extend routing by zero to all ambient channels, define components or netlists, or
solve feedback equations. It assigns no splitter behavior, path phase, delay, attenuation,
termination, reciprocity data, or electromagnetic power interpretation.

## iii. Key results

- `PortConnection.endpointPort_injective`: the two ends of one local connection are distinct.
- `PortConnectionFamily.channelEmbedding`: connected dependent channels embed in ambient channels.
- `PortConnectionFamily.mateEquiv`: the blockwise fixed-point-free mate permutation.
- `PortConnectionFamily.idealRouting_entry_of_ne_index`: routing never crosses connection blocks.
- `PortConnectionFamily.idealRouting_apply`: every connected outgoing amplitude reaches its mate.
- `PortConnectionFamily.idealRouting_isPowerPreserving`: connected-channel routing preserves
  normalized modal power.

## iv. Table of contents

- A. Connection ends
- B. Proof-carrying connection families
- C. Connected channels and blockwise mates
- D. Connected-channel ideal routing

-/

@[expose] public section

namespace Optics

noncomputable section

universe u v w

/-!

## A. Connection ends

-/

namespace PortConnection

/-- The two endpoint ends of a local port connection. -/
inductive End
  | left
  | right
  deriving DecidableEq

instance : Fintype End where
  elems := {.left, .right}
  complete := fun endpoint => by cases endpoint <;> decide

/-- The physical port selected by an endpoint occurrence. -/
def endpointPort {P : PortModeFamily.{u, v}} (connection : PortConnection P) :
    End → P.Port
  | .left => connection.left
  | .right => connection.right

/-- The two ends of a local connection select distinct physical ports. -/
lemma endpointPort_injective {P : PortModeFamily.{u, v}} (connection : PortConnection P) :
    Function.Injective connection.endpointPort := by
  intro first second hPort
  cases first <;> cases second
  · rfl
  · exact (connection.left_ne_right hPort).elim
  · exact (connection.left_ne_right hPort.symm).elim
  · rfl

end PortConnection

/-!

## B. Proof-carrying connection families

-/

/-- An indexed family of local port connections in which each physical port occurs at most once.

Finiteness is deliberately absent. Finite-dimensional amplitude operations require it only in
their own statements.
-/
structure PortConnectionFamily (P : PortModeFamily.{u, v}) (ι : Type w) where
  /-- The typed local connection at each family index. -/
  connection : ι → PortConnection P
  /-- No two indexed ends select the same physical port. -/
  endpointPort_injective :
    Function.Injective fun endpoint : ι × PortConnection.End =>
      (connection endpoint.1).endpointPort endpoint.2

namespace PortConnectionFamily

variable {P : PortModeFamily.{u, v}} {ι : Type w} (family : PortConnectionFamily P ι)

/-- The physical port selected by an indexed endpoint occurrence. -/
def endpointPort (endpoint : ι × PortConnection.End) : P.Port :=
  (family.connection endpoint.1).endpointPort endpoint.2

/-- The embedding of indexed ends into physical ports. -/
def endpointEmbedding : ι × PortConnection.End ↪ P.Port where
  toFun := family.endpointPort
  inj' := family.endpointPort_injective

/-- Distinct indexed ends select distinct physical ports. -/
lemma endpointPort_ne_of_ne {first second : ι × PortConnection.End}
    (h : first ≠ second) : family.endpointPort first ≠ family.endpointPort second := by
  exact fun hPort => h (family.endpointPort_injective hPort)

/-!

## C. Connected channels and blockwise mates

-/

/-- The connected channels of a connection family, retaining their connection index. -/
abbrev Channel := Σ index, (family.connection index).LocalChannel

/-- The embedding of one connection's local channels into the family's connected channels. -/
def connectionChannelEmbedding (index : ι) :
    (family.connection index).LocalChannel ↪ family.Channel where
  toFun channel := ⟨index, channel⟩
  inj' := by
    intro first second h
    simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using h

/-- The embedding of all connected dependent channels into the ambient port-family channels. -/
def channelEmbedding : family.Channel ↪ P.Channel where
  toFun channel := (family.connection channel.1).channelEmbedding channel.2
  inj' := by
    rintro ⟨i, modeI⟩ ⟨j, modeJ⟩ hChannel
    rcases modeI with modeI | modeI <;> rcases modeJ with modeJ | modeJ
    · have hEndpoint : (i, PortConnection.End.left) =
          (j, PortConnection.End.left) :=
        family.endpointPort_injective (congrArg Sigma.fst hChannel)
      cases hEndpoint
      cases hChannel
      rfl
    · have hEndpoint : (i, PortConnection.End.left) =
          (j, PortConnection.End.right) :=
        family.endpointPort_injective (congrArg Sigma.fst hChannel)
      cases hEndpoint
    · have hEndpoint : (i, PortConnection.End.right) =
          (j, PortConnection.End.left) :=
        family.endpointPort_injective (congrArg Sigma.fst hChannel)
      cases hEndpoint
    · have hEndpoint : (i, PortConnection.End.right) =
          (j, PortConnection.End.right) :=
        family.endpointPort_injective (congrArg Sigma.fst hChannel)
      cases hEndpoint
      cases hChannel
      rfl

/-- The family channel embedding agrees with the existing local embedding on every block. -/
@[simp]
lemma channelEmbedding_connectionChannelEmbedding (index : ι)
    (channel : (family.connection index).LocalChannel) :
    family.channelEmbedding (family.connectionChannelEmbedding index channel) =
      (family.connection index).channelEmbedding channel := by
  rfl

/-- An ambient channel is selected by the connected-channel embedding exactly when its physical
port is selected by an indexed connection endpoint. -/
lemma channel_mem_range_channelEmbedding_iff (channel : P.Channel) :
    channel ∈ Set.range family.channelEmbedding ↔
      channel.1 ∈ Set.range family.endpointEmbedding := by
  constructor
  · rintro ⟨⟨index, localChannel⟩, hChannel⟩
    rcases localChannel with mode | mode
    · exact ⟨(index, PortConnection.End.left), congrArg Sigma.fst hChannel⟩
    · exact ⟨(index, PortConnection.End.right), congrArg Sigma.fst hChannel⟩
  · rintro ⟨⟨index, endpoint⟩, hPort⟩
    rcases channel with ⟨port, mode⟩
    cases endpoint
    · change (family.connection index).left = port at hPort
      cases hPort
      exact ⟨⟨index, Sum.inl mode⟩, rfl⟩
    · change (family.connection index).right = port at hPort
      cases hPort
      exact ⟨⟨index, Sum.inr mode⟩, rfl⟩

/-- The blockwise mate equivalence of every connected channel in a connection family. -/
def mateEquiv : family.Channel ≃ family.Channel :=
  Equiv.sigmaCongrRight fun index => (family.connection index).mateEquiv

/-- The family mate acts by the existing local mate inside the selected connection block. -/
@[simp]
lemma mateEquiv_connectionChannelEmbedding (index : ι)
    (channel : (family.connection index).LocalChannel) :
    family.mateEquiv (family.connectionChannelEmbedding index channel) =
      family.connectionChannelEmbedding index ((family.connection index).mateEquiv channel) := by
  rfl

/-- Embedding a local channel after taking its mate selects the exact ambient physical channel. -/
lemma channelEmbedding_mateEquiv_connectionChannelEmbedding (index : ι)
    (channel : (family.connection index).LocalChannel) :
    family.channelEmbedding
        (family.mateEquiv (family.connectionChannelEmbedding index channel)) =
      (family.connection index).channelEmbedding
        ((family.connection index).mateEquiv channel) := by
  rw [mateEquiv_connectionChannelEmbedding,
    channelEmbedding_connectionChannelEmbedding]

/-- Taking the family mate twice recovers every connected channel. -/
@[simp]
lemma mateEquiv_apply_apply (channel : family.Channel) :
    family.mateEquiv (family.mateEquiv channel) = channel := by
  rcases channel with ⟨index, channel⟩
  simp [mateEquiv]

/-- The family mate preserves the connection index of every channel. -/
@[simp]
lemma mateEquiv_fst (channel : family.Channel) :
    (family.mateEquiv channel).1 = channel.1 := by
  rcases channel with ⟨index, channel⟩
  rfl

/-- No connected channel in a connection family is its own mate. -/
lemma mateEquiv_ne_self (channel : family.Channel) : family.mateEquiv channel ≠ channel := by
  rcases channel with ⟨index, channel⟩
  intro hMate
  apply (family.connection index).mateEquiv_ne_self channel
  simpa only [mateEquiv, Equiv.sigmaCongrRight_apply, Sigma.mk.inj_iff, heq_eq_eq,
    true_and] using hMate

/-!

## D. Connected-channel ideal routing

-/

/-- The ideal unit-gain routing transform assembled over all connected channel blocks. -/
def idealRouting [DecidableEq family.Channel] :
    ModeTransform (Outgoing family.Channel) (Incident family.Channel) :=
  ModeTransform.idealRouting family.mateEquiv

/-- The routing entry from a connected channel to its family mate is exactly one. -/
@[simp]
lemma idealRouting_entry_mate [DecidableEq family.Channel] (channel : family.Channel) :
    family.idealRouting (Incident.mk (family.mateEquiv channel))
      (Outgoing.mk channel) = 1 := by
  unfold idealRouting
  rw [ModeTransform.idealRouting_entry]
  simp

/-- The routing entry from a connected channel to itself is exactly zero. -/
@[simp]
lemma idealRouting_entry_self [DecidableEq family.Channel] (channel : family.Channel) :
    family.idealRouting (Incident.mk channel) (Outgoing.mk channel) = 0 := by
  unfold idealRouting
  rw [ModeTransform.idealRouting_entry]
  by_cases h : channel = family.mateEquiv channel
  · exact (family.mateEquiv_ne_self channel h.symm).elim
  · simp [h]

/-- Ideal routing has a zero entry between two different connection blocks. -/
lemma idealRouting_entry_of_ne_index [DecidableEq family.Channel] {first second : ι}
    (hIndex : first ≠ second) (input : (family.connection first).LocalChannel)
    (output : (family.connection second).LocalChannel) :
    family.idealRouting
        (Incident.mk (family.connectionChannelEmbedding second output))
        (Outgoing.mk (family.connectionChannelEmbedding first input)) = 0 := by
  have hNot : family.connectionChannelEmbedding second output ≠
      family.connectionChannelEmbedding first ((family.connection first).mateEquiv input) := by
    intro hEqual
    apply hIndex
    exact (congrArg Sigma.fst hEqual).symm
  unfold idealRouting
  rw [ModeTransform.idealRouting_entry]
  simp [hNot]

/-- Connected-channel routing sends every outgoing amplitude to its exact family mate. -/
@[simp]
lemma idealRouting_apply [Fintype family.Channel] [DecidableEq family.Channel]
    (amplitude : ModeAmplitude (Outgoing family.Channel)) (channel : family.Channel) :
    family.idealRouting.toLinearMap amplitude (Incident.mk (family.mateEquiv channel)) =
      amplitude (Outgoing.mk channel) :=
  ModeTransform.idealRouting_apply family.mateEquiv amplitude channel

/-- Ideal routing on all connected channels preserves normalized modal power. -/
lemma idealRouting_isPowerPreserving [Fintype family.Channel] [DecidableEq family.Channel] :
    family.idealRouting.IsPowerPreserving :=
  ModeTransform.idealRouting_isPowerPreserving family.mateEquiv

end PortConnectionFamily

end

end Optics
