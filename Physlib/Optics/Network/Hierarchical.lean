/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.FlatNetlistElimination

/-!
# Hierarchical composition and relational flattening

## i. Overview

A hierarchical network wires components in two stages. An inner connection family closes some of
the component channels into verified subsystems; an outer connection family then wires the
channels those subsystems still expose. This file makes the two stages first-class and shows that
the pair is exactly one flat connection family on the same components.

The boundary of an inner family is itself a typed physical-port family: its ports are the inner
family's structurally unconnected ports and its mode fibers are the ambient mode fibers over those
ports. An outer connection family is then a connection family on that boundary, and each of its
connections lifts to an ambient connection between the same physical ports carrying the same mode
equivalence.

`PortConnectionFamily.append` combines the two stages into a single indexed family on the ambient
port family. Its endpoint-injectivity proof is exactly the statement that the two stages cannot
reuse a physical port: the outer stage only ever selects ports the inner stage left unconnected.
Flattening therefore requires no solvability, invertibility, or well-posedness hypothesis
whatsoever; it is a statement about wiring data alone.

The connected channels of the flattened family are canonically the inner connected channels
together with the outer connected channels, and the channels it leaves external are canonically
the outer family's external channels. Mode fibers and mode equivalences are carried through
unchanged, so no convention is silently renegotiated by flattening.

## ii. Scope

This file supplies the wiring layer of hierarchical composition. It defines no semantics beyond
reusing `FlatNetlist`, asserts no relationship between the hierarchical and flattened relational
behaviors, and packages no child as a functional component. In particular nothing here assumes,
implies, or requires that any child subsystem is well posed, passive, lossless, reciprocal, or
causal, and no reference plane, phase gauge, or port-direction convention is changed: the lifted
outer connections carry the ambient ports and the outer mode equivalences verbatim.

## iii. Key definitions and results

- `PortConnectionFamily.externalPortModeFamily`: the typed boundary port family exposed by a
  connection family.
- `PortConnectionFamily.boundaryChannelEquiv`: boundary channels are exactly external channels.
- `PortConnection.liftBoundary`: an outer connection presented on the ambient ports.
- `PortConnectionFamily.append`: the flattened two-stage connection family, defined without any
  well-posedness hypothesis.
- `PortConnectionFamily.appendChannelEquiv`: flattened connected channels are inner plus outer
  connected channels.
- `PortConnectionFamily.appendUnconnectedPortEquiv` and
  `PortConnectionFamily.appendExternalChannelEquiv`: the flattened network exposes exactly the
  outer family's external ports and channels.
- `HierarchicalNetlist` and `HierarchicalNetlist.flatten`: a two-stage network and its flattened
  netlist.
- `FlatNetlist.packagedScattering`: a proof-gated packaging of a verified subsystem as a single
  scattering component on its own external channels.

## iv. Table of contents

- A. The boundary port family of a connection family
- B. Lifting outer connections to ambient ports
- C. Two-stage wiring and flattening
- D. Flattened connected and external channels
- E. Hierarchical netlists
- F. Packaging a verified subsystem as one component

-/

@[expose] public section

namespace Optics

noncomputable section

universe u v w x

/-!

## A. The boundary port family of a connection family

-/

namespace PortConnectionFamily

variable {P : PortModeFamily.{u, v}} {ι : Type w} (family : PortConnectionFamily P ι)

/-- The typed physical-port family a connection family still exposes.

Its ports are the structurally unconnected ambient ports and its mode fibers are the ambient mode
fibers over those ports. No mode is added, removed, or relabelled.
-/
def externalPortModeFamily : PortModeFamily.{u, v} where
  Port := family.UnconnectedPort
  Mode := fun port => P.Mode port.1

/-- A boundary port is an ambient port left unconnected by the family. -/
lemma externalPortModeFamily_port_not_mem_range
    (port : family.externalPortModeFamily.Port) :
    (port.1 : P.Port) ∉ Set.range family.endpointEmbedding := port.2

/-- Boundary channels are exactly the external channels of the family. -/
def boundaryChannelEquiv :
    family.externalPortModeFamily.Channel ≃ family.ExternalChannel :=
  family.externalChannelEquivUnconnectedPortModes.symm

/-- The ambient channel underlying a boundary channel keeps its port and mode. -/
@[simp]
lemma boundaryChannelEquiv_coe (channel : family.externalPortModeFamily.Channel) :
    ((family.boundaryChannelEquiv channel : family.ExternalChannel) : P.Channel) =
      ⟨channel.1.1, channel.2⟩ := rfl

end PortConnectionFamily

/-!

## B. Lifting outer connections to ambient ports

-/

namespace PortConnection

variable {P : PortModeFamily.{u, v}} {ι : Type w} {family : PortConnectionFamily P ι}

/-- An outer connection between boundary ports, presented between the ambient ports it selects.

The stored mode equivalence is carried through unchanged: lifting renegotiates no mode pairing.
-/
def liftBoundary (connection : PortConnection family.externalPortModeFamily) :
    PortConnection P where
  left := connection.left.1
  right := connection.right.1
  left_ne_right := fun hPort => connection.left_ne_right (Subtype.ext hPort)
  modeEquiv := connection.modeEquiv

/-- Lifting keeps the ambient port underlying the outer left endpoint. -/
@[simp]
lemma liftBoundary_left (connection : PortConnection family.externalPortModeFamily) :
    connection.liftBoundary.left = connection.left.1 := rfl

/-- Lifting keeps the ambient port underlying the outer right endpoint. -/
@[simp]
lemma liftBoundary_right (connection : PortConnection family.externalPortModeFamily) :
    connection.liftBoundary.right = connection.right.1 := rfl

/-- Lifting keeps the stored mode equivalence verbatim. -/
lemma liftBoundary_modeEquiv (connection : PortConnection family.externalPortModeFamily) :
    connection.liftBoundary.modeEquiv = connection.modeEquiv := rfl

/-- Lifting selects the ambient port underlying each outer endpoint. -/
lemma liftBoundary_endpointPort (connection : PortConnection family.externalPortModeFamily)
    (endpoint : PortConnection.End) :
    connection.liftBoundary.endpointPort endpoint =
      (connection.endpointPort endpoint).val := by
  cases endpoint <;> rfl

end PortConnection

/-!

## C. Two-stage wiring and flattening

-/

namespace PortConnectionFamily

variable {P : PortModeFamily.{u, v}} {ι : Type w} {κ : Type x}
variable (inner : PortConnectionFamily P ι)
variable (outer : PortConnectionFamily inner.externalPortModeFamily κ)

/-- The flattened two-stage connection family on the ambient port family.

No solvability, invertibility, or well-posedness hypothesis appears: flattening is a statement
about wiring data. The endpoint-injectivity obligation is discharged because the outer stage only
selects ports the inner stage left unconnected.
-/
def append : PortConnectionFamily P (ι ⊕ κ) where
  connection := Sum.elim inner.connection fun index => (outer.connection index).liftBoundary
  endpointPort_injective := by
    have hOuterNotInner : ∀ (index : κ) (endpoint : PortConnection.End),
        ((outer.connection index).liftBoundary).endpointPort endpoint ∉
          Set.range inner.endpointEmbedding := by
      intro index endpoint
      rw [(outer.connection index).liftBoundary_endpointPort endpoint]
      exact ((outer.connection index).endpointPort endpoint).2
    rintro ⟨firstIndex, firstEnd⟩ ⟨secondIndex, secondEnd⟩ hPort
    rcases firstIndex with firstIndex | firstIndex <;>
      rcases secondIndex with secondIndex | secondIndex
    · have hInner : ((firstIndex, firstEnd) : ι × PortConnection.End) =
          (secondIndex, secondEnd) := inner.endpointPort_injective hPort
      rw [Prod.mk.injEq] at hInner
      rw [hInner.1, hInner.2]
    · exact absurd ⟨(firstIndex, firstEnd), hPort⟩ (hOuterNotInner secondIndex secondEnd)
    · exact absurd ⟨(secondIndex, secondEnd), hPort.symm⟩ (hOuterNotInner firstIndex firstEnd)
    · have hBoundary : (outer.connection firstIndex).endpointPort firstEnd =
          (outer.connection secondIndex).endpointPort secondEnd := by
        apply Subtype.ext
        rw [← (outer.connection firstIndex).liftBoundary_endpointPort firstEnd,
          ← (outer.connection secondIndex).liftBoundary_endpointPort secondEnd]
        exact hPort
      have hOuter : ((firstIndex, firstEnd) : κ × PortConnection.End) =
          (secondIndex, secondEnd) := outer.endpointPort_injective hBoundary
      rw [Prod.mk.injEq] at hOuter
      rw [hOuter.1, hOuter.2]

/-- The flattened family reuses each inner connection unchanged. -/
@[simp]
lemma append_connection_inl (index : ι) :
    (inner.append outer).connection (Sum.inl index) = inner.connection index := rfl

/-- The flattened family reuses each outer connection through its ambient lift. -/
@[simp]
lemma append_connection_inr (index : κ) :
    (inner.append outer).connection (Sum.inr index) =
      (outer.connection index).liftBoundary := rfl

/-- An ambient port selected by the inner stage is selected by the flattened family. -/
lemma mem_range_append_endpointEmbedding_of_inner {port : P.Port}
    (hPort : port ∈ Set.range inner.endpointEmbedding) :
    port ∈ Set.range (inner.append outer).endpointEmbedding := by
  rcases hPort with ⟨⟨index, endpoint⟩, hIndex⟩
  exact ⟨(Sum.inl index, endpoint), hIndex⟩

/-- A boundary port selected by the outer stage is selected by the flattened family. -/
lemma mem_range_append_endpointEmbedding_of_outer {port : inner.UnconnectedPort}
    (hPort : port ∈ Set.range outer.endpointEmbedding) :
    (port : P.Port) ∈ Set.range (inner.append outer).endpointEmbedding := by
  rcases hPort with ⟨⟨index, endpoint⟩, hIndex⟩
  exact ⟨(Sum.inr index, endpoint),
    ((outer.connection index).liftBoundary_endpointPort endpoint).trans (congrArg _ hIndex)⟩

/-- Every port the flattened family selects is selected by exactly one of its two stages. -/
lemma mem_range_append_endpointEmbedding_iff (port : P.Port) :
    port ∈ Set.range (inner.append outer).endpointEmbedding ↔
      port ∈ Set.range inner.endpointEmbedding ∨
        ∃ boundary : inner.UnconnectedPort,
          boundary ∈ Set.range outer.endpointEmbedding ∧ (boundary : P.Port) = port := by
  constructor
  · rintro ⟨⟨index, endpoint⟩, hIndex⟩
    rcases index with index | index
    · exact Or.inl ⟨(index, endpoint), hIndex⟩
    · refine Or.inr ⟨(outer.connection index).endpointPort endpoint,
        ⟨(index, endpoint), rfl⟩, ?_⟩
      rw [← (outer.connection index).liftBoundary_endpointPort endpoint]
      exact hIndex
  · rintro (hInner | ⟨boundary, hBoundary, rfl⟩)
    · exact inner.mem_range_append_endpointEmbedding_of_inner outer hInner
    · exact inner.mem_range_append_endpointEmbedding_of_outer outer hBoundary

/-!

## D. Flattened connected and external channels

-/

/-- The connected channels of the flattened family are the inner connected channels together with
the outer connected channels. -/
def appendChannelEquiv :
    (inner.append outer).Channel ≃ inner.Channel ⊕ outer.Channel where
  toFun := fun channel =>
    match channel with
    | ⟨Sum.inl index, local'⟩ => Sum.inl ⟨index, local'⟩
    | ⟨Sum.inr index, local'⟩ => Sum.inr ⟨index, local'⟩
  invFun := Sum.elim (fun channel => ⟨Sum.inl channel.1, channel.2⟩)
    fun channel => ⟨Sum.inr channel.1, channel.2⟩
  left_inv := by rintro ⟨index | index, local'⟩ <;> rfl
  right_inv := by rintro (⟨index, local'⟩ | ⟨index, local'⟩) <;> rfl

/-- Inner connected channels embed into the flattened family exactly as before. -/
@[simp]
lemma append_channelEmbedding_inl (index : ι)
    (local' : (inner.connection index).LocalChannel) :
    (inner.append outer).channelEmbedding ⟨Sum.inl index, local'⟩ =
      inner.channelEmbedding ⟨index, local'⟩ := rfl

/-- Outer connected channels embed into the flattened family through the inner boundary. -/
lemma append_channelEmbedding_inr (index : κ)
    (local' : (outer.connection index).LocalChannel) :
    (inner.append outer).channelEmbedding ⟨Sum.inr index, local'⟩ =
      ((inner.boundaryChannelEquiv (outer.channelEmbedding ⟨index, local'⟩)
        : inner.ExternalChannel) : P.Channel) := by
  rcases local' with mode | mode <;> rfl

/-- The flattened family leaves unconnected exactly the ports the outer family leaves
unconnected. -/
def appendUnconnectedPortEquiv :
    (inner.append outer).UnconnectedPort ≃ outer.UnconnectedPort where
  toFun := fun port =>
    ⟨⟨port.1, fun hInner => port.2
        (inner.mem_range_append_endpointEmbedding_of_inner outer hInner)⟩,
      fun hOuter => port.2
        (inner.mem_range_append_endpointEmbedding_of_outer outer hOuter)⟩
  invFun := fun port =>
    ⟨port.1.1, by
      show (port.1.1 : P.Port) ∉ Set.range (inner.append outer).endpointEmbedding
      rw [inner.mem_range_append_endpointEmbedding_iff outer]
      rintro (hInner | ⟨boundary, hBoundary, hPort⟩)
      · exact port.1.2 hInner
      · exact port.2 (by rwa [show boundary = port.1 from Subtype.ext hPort] at hBoundary)⟩
  left_inv := by rintro ⟨port, hPort⟩; rfl
  right_inv := by rintro ⟨⟨port, hInner⟩, hOuter⟩; rfl

/-- The flattened family exposes exactly the external channels of the outer family. -/
def appendExternalChannelEquiv :
    (inner.append outer).ExternalChannel ≃ outer.ExternalChannel where
  toFun channel := by
    refine ⟨⟨⟨channel.1.1, ?_⟩, channel.1.2⟩, ?_⟩
    · intro hInner
      exact channel.2
        (((inner.append outer).channel_mem_range_channelEmbedding_iff channel.1).mpr
          (inner.mem_range_append_endpointEmbedding_of_inner outer hInner))
    · intro hOuter
      rw [outer.channel_mem_range_channelEmbedding_iff] at hOuter
      exact channel.2
        (((inner.append outer).channel_mem_range_channelEmbedding_iff channel.1).mpr
          (inner.mem_range_append_endpointEmbedding_of_outer outer hOuter))
  invFun channel := by
    refine ⟨⟨channel.1.1.1, channel.1.2⟩, ?_⟩
    intro hAppend
    rw [(inner.append outer).channel_mem_range_channelEmbedding_iff,
      inner.mem_range_append_endpointEmbedding_iff outer] at hAppend
    rcases hAppend with hInner | ⟨boundary, hBoundary, hPort⟩
    · exact channel.1.1.2 hInner
    · apply channel.2
      rw [outer.channel_mem_range_channelEmbedding_iff]
      rwa [show boundary = channel.1.1 from Subtype.ext hPort] at hBoundary
  left_inv := by rintro ⟨⟨port, mode⟩, hChannel⟩; rfl
  right_inv := by rintro ⟨⟨⟨port, hInner⟩, mode⟩, hOuter⟩; rfl

end PortConnectionFamily

/-!

## E. Hierarchical netlists

-/

-- The universe levels independently track component labels, local ports, local mode fibers, and
-- the two connection stages.
set_option linter.checkUnivs false in
/-- A two-stage network: components, an inner subsystem wiring, and an outer wiring of the
channels the subsystems still expose.

Nothing in this structure assumes that any subsystem is solvable. A hierarchical network is
wiring data, exactly like a flat one.
-/
structure HierarchicalNetlist where
  /-- The indexed fixed-frequency components and their local scattering laws. -/
  components : ScatteringComponentFamily.{u, v, w}
  /-- The type indexing the inner subsystem connections. -/
  InnerConnection : Type x
  /-- The inner subsystem wiring on the aggregate component boundary. -/
  inner : PortConnectionFamily components.aggregatePortModeFamily InnerConnection
  /-- The type indexing the outer connections between subsystem boundaries. -/
  OuterConnection : Type x
  /-- The outer wiring on the channels the inner stage leaves exposed. -/
  outer : PortConnectionFamily inner.externalPortModeFamily OuterConnection

namespace HierarchicalNetlist

variable (netlist : HierarchicalNetlist.{u, v, w, x})

/-- The inner subsystem stage presented as an ordinary flat netlist.

This is the verified-subsystem layer: the same components, wired only by the inner stage.
-/
def innerNetlist : FlatNetlist.{u, v, w, x} where
  components := netlist.components
  Connection := netlist.InnerConnection
  connections := netlist.inner

/-- The flattened netlist: the same components wired by both stages at once.

Flattening takes no well-posedness hypothesis of any kind.
-/
def flatten : FlatNetlist.{u, v, w, x} where
  components := netlist.components
  Connection := netlist.InnerConnection ⊕ netlist.OuterConnection
  connections := netlist.inner.append netlist.outer

/-- Flattening keeps the components untouched. -/
lemma flatten_components : netlist.flatten.components = netlist.components := rfl

/-- Flattening keeps the inner subsystem's components untouched. -/
lemma innerNetlist_components : netlist.innerNetlist.components = netlist.components := rfl

/-- The flattened netlist and the inner subsystem netlist share the ambient channel type. -/
lemma flatten_channel : netlist.flatten.Channel = netlist.innerNetlist.Channel := rfl

/-- The flattened netlist exposes exactly the outer stage's external channels. -/
def flattenExternalChannelEquiv :
    netlist.flatten.ExternalChannel ≃ netlist.outer.ExternalChannel :=
  netlist.inner.appendExternalChannelEquiv netlist.outer

/-- The connected channels of the flattened netlist are the inner ones together with the outer
ones. -/
def flattenConnectedChannelEquiv :
    netlist.flatten.ConnectedChannel ≃
      netlist.innerNetlist.ConnectedChannel ⊕ netlist.outer.Channel :=
  netlist.inner.appendChannelEquiv netlist.outer

end HierarchicalNetlist

/-!

## F. Packaging a verified subsystem as one component

-/

namespace FlatNetlist

variable (netlist : FlatNetlist.{u, v, w, x})
variable [Fintype netlist.Channel] [Fintype netlist.ConnectedChannel]

/-- Classical equality on aggregate channels, kept local to the packaging layer. -/
local instance packagingChannelDecidableEq : DecidableEq netlist.Channel :=
  Classical.decEq _

/-- Classical equality on connected channels, kept local to the packaging layer. -/
local instance packagingConnectedChannelDecidableEq :
    DecidableEq netlist.ConnectedChannel := Classical.decEq _

/-- The external channels of a finite netlist are finite. -/
local instance packagingExternalChannelFintype : Fintype netlist.ExternalChannel := by
  classical
  infer_instance

/-- A well-posed netlist packaged as a single scattering component on its own external channels.

Two separate facts license this packaging and both are visible in the statement. Well-posedness is
a hypothesis, so a subsystem with a multivalued or unsolvable internal state has no functional
packaging at all. The external boundary is already paired: the exposed incident and outgoing
endpoint types are `Incident` and `Outgoing` of the *same* external-channel type, and the pairing
used here is the canonical `Incident.channelEquiv` / `Outgoing.channelEquiv` and nothing else, so
no square port identification is smuggled in.

Packaging asserts no passivity, losslessness, reciprocity, or causality of the subsystem.
-/
def packagedScattering (hWellPosed : netlist.IsWellPosed) :
    ScatteringMatrix netlist.ExternalChannel where
  toModeTransform :=
    (netlist.responseTransform hWellPosed).reindex Incident.channelEquiv Outgoing.channelEquiv

/-- The packaged component's oriented boundary law is exactly the subsystem's external response.

Packaging therefore changes coordinates only by the canonical endpoint-label equivalences.
-/
lemma toOrientedModeTransform_packagedScattering (hWellPosed : netlist.IsWellPosed) :
    (netlist.packagedScattering hWellPosed).toOrientedModeTransform =
      netlist.responseTransform hWellPosed :=
  ModeTransform.reindex_symm_reindex _ _ _

/-- Every entry of the packaged component is the corresponding external response entry. -/
lemma packagedScattering_toModeTransform_apply (hWellPosed : netlist.IsWellPosed)
    (output input : netlist.ExternalChannel) :
    (netlist.packagedScattering hWellPosed).toModeTransform output input =
      netlist.responseTransform hWellPosed (Outgoing.mk output) (Incident.mk input) := rfl

/-- The packaged component reproduces the subsystem's singular-safe relational semantics exactly.

A verified subsystem may therefore be reused as one component without changing what the fully
expanded channel equations say about it.
-/
lemma toBehavior_toOrientedModeTransform_packagedScattering
    (hWellPosed : netlist.IsWellPosed) :
    (netlist.packagedScattering hWellPosed).toOrientedModeTransform.toBehavior =
      netlist.behavior := by
  rw [netlist.toOrientedModeTransform_packagedScattering hWellPosed]
  exact netlist.toBehavior_responseTransform hWellPosed

/-- Subsystem behavior membership is evaluation of the packaged component's boundary law. -/
lemma mem_behavior_iff_packagedScattering (hWellPosed : netlist.IsWellPosed)
    (input : ModeAmplitude netlist.ExternalIncident)
    (output : ModeAmplitude netlist.ExternalOutgoing) :
    (input, output) ∈ netlist.behavior ↔
      output = (netlist.packagedScattering hWellPosed).toOrientedModeTransform.toLinearMap
        input := by
  rw [← netlist.toBehavior_toOrientedModeTransform_packagedScattering hWellPosed,
    ModeTransform.mem_toBehavior_iff_toLinearMap]

end FlatNetlist

end

end Optics
