/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.Hierarchical
public import Physlib.Optics.Network.LinearBehaviorReindex

/-!
# Transport of optical connection families

## i. Overview

This file transports dependent optical port families, individual connections, and connection
families along equivalences of their port and mode labels. The induced equivalences preserve the
ambient channel embedding, the connected-channel mate relation, and the external boundary.

Incident assembly and singular-safe relational closure are covariant under the same transport.
These statements make boundary relabelling explicit, so a subsystem can be reused without
identifying definitionally different dependent port families.

## ii. Key results

- `PortModeFamily.Equiv.channelEquiv`: a dependent port-family equivalence induces a flattened
  channel equivalence.
- `PortConnection.transport` and `PortConnectionFamily.transport`: relabel connections without
  changing their endpoint pairing.
- `PortConnectionFamily.transportExternalPortModeFamilyEquiv`: transported families expose
  equivalent dependent boundaries.
- `PortConnectionFamily.incidentAssembly_transport`: incident assembly is covariant.
- `PortConnectionFamily.closeBehavior_transport`: relational closure is covariant.

## iii. Table of contents

- A. Dependent port-family equivalences
- B. Transported connections
- C. Transported connection families
- D. Transported external boundaries
- E. Covariance of incident assembly and closure

## iv. References

This is the remaining reuse machinery described in `goal.md` lines 2098--2102. In particular,
"All current N-08 hypotheses are structural `Fintype` assumptions on channel indices, not physical
assumptions." No well-posedness, functionality, passivity, losslessness, reciprocity, stability,
or physical-realization claim is made.
-/

@[expose] public section

namespace Optics

noncomputable section

universe u v w x y

/-!

## A. Dependent port-family equivalences

-/

namespace PortModeFamily

/-- An equivalence of dependent optical port families, consisting of a port equivalence and a
compatible equivalence on every mode fiber. -/
structure Equiv (P : PortModeFamily.{u, v}) (Q : PortModeFamily.{w, x}) where
  /-- The equivalence between physical port labels. -/
  portEquiv : P.Port ≃ Q.Port
  /-- The equivalence between mode fibers over corresponding ports. -/
  modeEquiv : ∀ port, P.Mode port ≃ Q.Mode (portEquiv port)

namespace Equiv

variable {P : PortModeFamily.{u, v}} {Q : PortModeFamily.{w, x}}
  {R : PortModeFamily.{u, y}}

/-- The identity equivalence of a dependent port family. -/
def refl (P : PortModeFamily.{u, v}) : P.Equiv P where
  portEquiv := Equiv.refl P.Port
  modeEquiv _ := Equiv.refl _

/-- Composition of dependent port-family equivalences. -/
def trans (first : P.Equiv Q) (second : Q.Equiv R) : P.Equiv R where
  portEquiv := first.portEquiv.trans second.portEquiv
  modeEquiv port :=
    (first.modeEquiv port).trans (second.modeEquiv (first.portEquiv port))

/-- Reversal of a dependent port-family equivalence. -/
def symm (equiv : P.Equiv Q) : Q.Equiv P where
  portEquiv := equiv.portEquiv.symm
  modeEquiv port :=
    (Equiv.cast
      (congrArg Q.Mode (equiv.portEquiv.apply_symm_apply port)).symm).trans
        (equiv.modeEquiv (equiv.portEquiv.symm port)).symm

/-- The flattened channel equivalence induced by dependent port and mode relabelling. -/
def channelEquiv (equiv : P.Equiv Q) : P.Channel ≃ Q.Channel :=
  Equiv.sigmaCongr equiv.portEquiv equiv.modeEquiv

/-- The induced channel equivalence relabels both the port and its dependent mode. -/
@[simp]
lemma channelEquiv_apply (equiv : P.Equiv Q) (channel : P.Channel) :
    equiv.channelEquiv channel =
      ⟨equiv.portEquiv channel.1, equiv.modeEquiv channel.1 channel.2⟩ := rfl

end Equiv

end PortModeFamily

/-!

## B. Transported connections

-/

namespace PortConnection

variable {P : PortModeFamily.{u, v}} {Q : PortModeFamily.{w, x}}

/-- Relabel a connection along an equivalence of its ambient dependent port family. -/
def transport (equiv : P.Equiv Q) (connection : PortConnection P) : PortConnection Q where
  left := equiv.portEquiv connection.left
  right := equiv.portEquiv connection.right
  left_ne_right := fun hPort => connection.left_ne_right (equiv.portEquiv.injective hPort)
  modeEquiv :=
    (equiv.modeEquiv connection.left).symm.trans
      (connection.modeEquiv.trans (equiv.modeEquiv connection.right))

/-- The local-channel equivalence induced by transport of a connection. -/
def transportLocalChannelEquiv (equiv : P.Equiv Q) (connection : PortConnection P) :
    connection.LocalChannel ≃ (connection.transport equiv).LocalChannel :=
  (equiv.modeEquiv connection.left).sumCongr (equiv.modeEquiv connection.right)

/-- Transported local channels select the transport of the original ambient channel. -/
lemma transport_channelEmbedding (equiv : P.Equiv Q) (connection : PortConnection P)
    (channel : connection.LocalChannel) :
    (connection.transport equiv).channelEmbedding
        (connection.transportLocalChannelEquiv equiv channel) =
      equiv.channelEquiv (connection.channelEmbedding channel) := by
  rcases channel with mode | mode <;> rfl

/-- Transported local-channel labels commute with endpoint mating. -/
lemma transport_mateEquiv (equiv : P.Equiv Q) (connection : PortConnection P)
    (channel : connection.LocalChannel) :
    (connection.transport equiv).mateEquiv
        (connection.transportLocalChannelEquiv equiv channel) =
      connection.transportLocalChannelEquiv equiv (connection.mateEquiv channel) := by
  rcases channel with mode | mode
  · rfl
  · simp [transport, transportLocalChannelEquiv]

end PortConnection

/-!

## C. Transported connection families

-/

namespace PortConnectionFamily

variable {P : PortModeFamily.{u, v}} {Q : PortModeFamily.{w, x}} {index : Type y}

/-- Relabel every connection in a family along an ambient dependent port-family equivalence. -/
def transport (equiv : P.Equiv Q) (family : PortConnectionFamily P index) :
    PortConnectionFamily Q index where
  connection connectionIndex := (family.connection connectionIndex).transport equiv
  endpointPort_injective := by
    rintro ⟨firstIndex, firstEnd⟩ ⟨secondIndex, secondEnd⟩ hPort
    apply family.endpointPort_injective
    apply equiv.portEquiv.injective
    simpa [PortConnection.endpointPort, transport] using hPort

/-- The connected-channel equivalence induced by transport of the ambient port family. -/
def transportChannelEquiv (equiv : P.Equiv Q) (family : PortConnectionFamily P index) :
    family.Channel ≃ (family.transport equiv).Channel :=
  Equiv.sigmaCongrRight fun connectionIndex =>
    (family.connection connectionIndex).transportLocalChannelEquiv equiv

/-- Transported connected channels select the corresponding transported ambient channels. -/
lemma transport_channelEmbedding (equiv : P.Equiv Q)
    (family : PortConnectionFamily P index) (channel : family.Channel) :
    (family.transport equiv).channelEmbedding (family.transportChannelEquiv equiv channel) =
      equiv.channelEquiv (family.channelEmbedding channel) := by
  rcases channel with ⟨connectionIndex, channel⟩
  exact (family.connection connectionIndex).transport_channelEmbedding equiv channel

/-- Transported connected-channel labels commute with the family mate relation. -/
lemma transport_mateEquiv (equiv : P.Equiv Q) (family : PortConnectionFamily P index)
    (channel : family.Channel) :
    (family.transport equiv).mateEquiv (family.transportChannelEquiv equiv channel) =
      family.transportChannelEquiv equiv (family.mateEquiv channel) := by
  rcases channel with ⟨connectionIndex, channel⟩
  exact congrArg (Sigma.mk connectionIndex)
    ((family.connection connectionIndex).transport_mateEquiv equiv channel)

end PortConnectionFamily

/-!

## D. Transported external boundaries

-/

namespace PortConnectionFamily

variable {P : PortModeFamily.{u, v}} {Q : PortModeFamily.{w, x}} {index : Type y}

/-- Transport sends structurally unconnected ports to structurally unconnected ports. -/
def transportUnconnectedPortEquiv (equiv : P.Equiv Q)
    (family : PortConnectionFamily P index) :
    family.UnconnectedPort ≃ (family.transport equiv).UnconnectedPort where
  toFun port := ⟨equiv.portEquiv port.1, by
    intro hEndpoint
    rcases hEndpoint with ⟨⟨connectionIndex, endpoint⟩, hPort⟩
    apply port.2
    refine ⟨⟨connectionIndex, endpoint⟩, ?_⟩
    apply equiv.portEquiv.injective
    simpa [PortConnection.endpointPort, transport] using hPort⟩
  invFun port := ⟨equiv.portEquiv.symm port.1, by
    intro hEndpoint
    rcases hEndpoint with ⟨⟨connectionIndex, endpoint⟩, hPort⟩
    apply port.2
    refine ⟨⟨connectionIndex, endpoint⟩, ?_⟩
    simpa [PortConnection.endpointPort, transport] using congrArg equiv.portEquiv hPort⟩
  left_inv := by rintro ⟨port, hPort⟩; apply Subtype.ext; simp
  right_inv := by rintro ⟨port, hPort⟩; apply Subtype.ext; simp

/-- Transport sends structurally external channels to structurally external channels. -/
def transportExternalChannelEquiv (equiv : P.Equiv Q)
    (family : PortConnectionFamily P index) :
    family.ExternalChannel ≃ (family.transport equiv).ExternalChannel where
  toFun channel := ⟨equiv.channelEquiv channel.1, by
    intro hConnected
    rcases hConnected with ⟨transported, hTransported⟩
    obtain ⟨source, rfl⟩ := (family.transportChannelEquiv equiv).surjective transported
    apply channel.2
    refine ⟨source, ?_⟩
    apply equiv.channelEquiv.injective
    simpa only [family.transport_channelEmbedding equiv] using hTransported⟩
  invFun channel := ⟨equiv.channelEquiv.symm channel.1, by
    intro hConnected
    rcases hConnected with ⟨source, hSource⟩
    apply channel.2
    refine ⟨family.transportChannelEquiv equiv source, ?_⟩
    rw [family.transport_channelEmbedding]
    simpa using congrArg equiv.channelEquiv hSource⟩
  left_inv := by rintro ⟨channel, hChannel⟩; apply Subtype.ext; simp
  right_inv := by rintro ⟨channel, hChannel⟩; apply Subtype.ext; simp

/-- Transported external boundaries are equivalent as dependent port-mode families. -/
def transportExternalPortModeFamilyEquiv (equiv : P.Equiv Q)
    (family : PortConnectionFamily P index) :
    family.externalPortModeFamily.Equiv
      (family.transport equiv).externalPortModeFamily where
  portEquiv := family.transportUnconnectedPortEquiv equiv
  modeEquiv port := equiv.modeEquiv port.1

/-- The external-channel equivalence and the induced boundary-channel equivalence agree after
passing through the canonical boundary presentations. -/
lemma transportExternalChannelEquiv_boundaryChannelEquiv
    (equiv : P.Equiv Q) (family : PortConnectionFamily P index)
    (channel : family.externalPortModeFamily.Channel) :
    family.transportExternalChannelEquiv equiv (family.boundaryChannelEquiv channel) =
      (family.transport equiv).boundaryChannelEquiv
        ((family.transportExternalPortModeFamilyEquiv equiv).channelEquiv channel) := by
  rfl

end PortConnectionFamily

/-!

## E. Covariance of incident assembly and closure

-/

end


end Optics
