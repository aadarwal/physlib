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
the component channels into subsystems; an outer connection family then wires the channels those
subsystems still expose. A subsystem here is a grouping of wiring and nothing more: no subsystem
is asserted to be solvable, and the word *verified* is used below only where a well-posedness
proof is actually supplied. This file makes the two stages first-class and shows that the pair is
exactly one flat connection family on the same components.

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

Two further layers are supplied. A child is packaged as a single scattering component *only after*
its well-posedness is proved, on its already-paired external channels. And the singular-safe
relational closure of an abstract oriented boundary behavior by a connection family is made
explicit, with `FlatNetlist.behavior` exhibited as an instance of it; the flattened incident
assembly is then read off stage by stage on inner-connected, outer-connected, and fully external
coordinates.

## ii. Scope

This file supplies the wiring layer of hierarchical composition together with the relational
closure operation and the proof-gated packaging of one child.

Two results the `N5H` contract asks for are deliberately **not** claimed here.

* Equality of hierarchical relational semantics with flattened-netlist semantics (goal.md row
  `N-08`) is not proved. Sections G and H supply the closure operation and the stage-by-stage
  reading of the flattened assembly that such a proof needs, and nothing in this file asserts the
  equality itself.
* Associativity and invariance of `append` for reusing a subsystem are not proved.

Beyond that, nothing here assumes, implies, or requires that any child subsystem is well posed,
passive, lossless, reciprocal, or causal, except in `packagedScattering` and its consequences,
which take well-posedness as an explicit hypothesis and still assert none of the other four. No
reference plane, phase gauge, or port-direction convention is changed: the lifted outer connections
carry the ambient ports and the outer mode equivalences verbatim.

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
- `FlatNetlist.packagedScattering`: a proof-gated packaging of a well-posed subsystem as a single
  scattering component on its own external channels.
- `PortConnectionFamily.closeBehavior` and `PortConnectionFamily.mem_closeBehavior_iff`: the
  singular-safe relational closure of an abstract oriented boundary behavior by a connection
  family, and its three shaped equations.
- `FlatNetlist.behavior_eq_closeBehavior`: a flat netlist's external behavior is that closure
  applied to its assembled component graph.
- `PortConnectionFamily.append_incidentAssembly_apply_inner`, `..._apply_outer`, and
  `..._apply_external`: the flattened incident assembly read off stage by stage.

## iv. Table of contents

- A. The boundary port family of a connection family
- B. Lifting outer connections to ambient ports
- C. Two-stage wiring and flattening
- D. Flattened connected and external channels
- E. Hierarchical netlists
- F. Packaging a well-posed subsystem as one component
- G. Relational closure of an abstract boundary behavior
- H. The flattened incident assembly, stage by stage

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
      ((inner.boundaryChannelEquiv
        (outer.channelEmbedding ⟨index, local'⟩) : inner.ExternalChannel) : P.Channel) := by
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

This is the subsystem layer: the same components, wired only by the inner stage. It is not
asserted to be well posed; that is a separate hypothesis, supplied where `packagedScattering` is
used.
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

## F. Packaging a well-posed subsystem as one component

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

A well-posed subsystem may therefore be reused as one component without changing what the fully
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

/-!

## G. Relational closure of an abstract boundary behavior

-/

namespace PortConnectionFamily

variable {P : PortModeFamily.{u, v}} {ι : Type w} (family : PortConnectionFamily P ι)
variable [Fintype P.Channel] [Fintype family.Channel]

/-- Classical equality on ambient channels, kept local to the relational closure. -/
local instance closureChannelDecidableEq : DecidableEq P.Channel := Classical.decEq _

/-- Classical equality on connected channels, kept local to the relational closure. -/
local instance closureConnectedChannelDecidableEq : DecidableEq family.Channel :=
  Classical.decEq _

/-- The external channels of a finite connection family are finite. -/
local instance closureExternalChannelFintype : Fintype family.ExternalChannel := by
  classical
  infer_instance

/-- The relational form of `a = C b + E_in u` for a connection family.

Internal routing and external injection act independently in parallel, after which algebraic
coherent sum adds their two incident-space outputs. This use of coherent sum is vector addition,
not a physical combiner component.
-/
def incidentAssemblyBehavior :
    LinearBehavior (Outgoing P.Channel ⊕ Incident family.ExternalChannel)
      (Incident P.Channel) :=
  (family.partialRouting.toBehavior.parallel
    family.externalIncidentInjection.toBehavior).series
    (LinearBehavior.coherentSum : LinearBehavior (Incident P.Channel ⊕ Incident P.Channel)
      (Incident P.Channel))

/-- The relational incident assembly is exactly `a = C b + E_in u`. -/
@[simp]
lemma mem_incidentAssemblyBehavior_iff
    (outgoing : ModeAmplitude (Outgoing P.Channel))
    (external : ModeAmplitude (Incident family.ExternalChannel))
    (incident : ModeAmplitude (Incident P.Channel)) :
    (outgoing.directSum external, incident) ∈ family.incidentAssemblyBehavior ↔
      incident = family.incidentAssembly outgoing external := by
  constructor
  · rintro ⟨middle, hParallel, hSum⟩
    rw [LinearBehavior.mem_parallel_iff] at hParallel
    simp only [ModeAmplitude.restrictInl_directSum,
      ModeAmplitude.restrictInr_directSum] at hParallel
    rcases hParallel with ⟨hRouting, hExposure⟩
    change middle.restrictInl = family.partialRouting.toLinearMap outgoing at hRouting
    change middle.restrictInr =
      family.externalIncidentInjection.toLinearMap external at hExposure
    rw [LinearBehavior.mem_coherentSum_iff] at hSum
    rw [hRouting, hExposure] at hSum
    simpa only [PortConnectionFamily.incidentAssembly] using hSum
  · intro hIncident
    refine ⟨(family.partialRouting.toLinearMap outgoing).directSum
      (family.externalIncidentInjection.toLinearMap external), ?_, ?_⟩
    · rw [LinearBehavior.mem_parallel_iff]
      simp only [ModeAmplitude.restrictInl_directSum,
        ModeAmplitude.restrictInr_directSum]
      exact ⟨rfl, rfl⟩
    · rw [LinearBehavior.mem_coherentSum_iff,
        ModeAmplitude.restrictInl_directSum,
        ModeAmplitude.restrictInr_directSum]
      simpa only [PortConnectionFamily.incidentAssembly] using hIncident

/-- Every complete boundary state compatible with an abstract boundary behavior and this
family's return relation. No existence or uniqueness of a state is asserted. -/
def closedSolutionBehavior
    (behavior : LinearBehavior (Incident P.Channel) (Outgoing P.Channel)) :
    LinearBehavior (Incident family.ExternalChannel)
      (Incident P.Channel ⊕ Outgoing P.Channel) :=
  behavior.feedbackSolutions family.incidentAssemblyBehavior

/-- A displayed closed-solution state satisfies exactly the boundary relation and `a = C b + E_in
u`. -/
@[simp]
lemma mem_closedSolutionBehavior_directSum_iff
    (behavior : LinearBehavior (Incident P.Channel) (Outgoing P.Channel))
    (external : ModeAmplitude (Incident family.ExternalChannel))
    (incident : ModeAmplitude (Incident P.Channel))
    (outgoing : ModeAmplitude (Outgoing P.Channel)) :
    (external, incident.directSum outgoing) ∈ family.closedSolutionBehavior behavior ↔
      (incident, outgoing) ∈ behavior ∧
        incident = family.incidentAssembly outgoing external := by
  rw [closedSolutionBehavior, LinearBehavior.mem_feedbackSolutions_directSum_iff,
    family.mem_incidentAssemblyBehavior_iff]

/-- Wiring an abstract oriented boundary behavior by a connection family, singular-safe.

Nothing here assumes that the closed relation is total, single valued, or well posed, and no
inverse is formed. `FlatNetlist.behavior` is the instance of this construction at the assembled
component graph.
-/
def closeBehavior (behavior : LinearBehavior (Incident P.Channel) (Outgoing P.Channel)) :
    LinearBehavior (Incident family.ExternalChannel) (Outgoing family.ExternalChannel) :=
  ((family.closedSolutionBehavior behavior).series
    (LinearBehavior.selectRight :
      LinearBehavior (Incident P.Channel ⊕ Outgoing P.Channel) (Outgoing P.Channel))).series
    family.externalOutgoingReadout.toBehavior

/-- Closure membership is exactly the three shaped equations, with the component law replaced by
an arbitrary boundary relation. -/
lemma mem_closeBehavior_iff
    (behavior : LinearBehavior (Incident P.Channel) (Outgoing P.Channel))
    (input : ModeAmplitude (Incident family.ExternalChannel))
    (output : ModeAmplitude (Outgoing family.ExternalChannel)) :
    (input, output) ∈ family.closeBehavior behavior ↔
      ∃ incident outgoing,
        (incident, outgoing) ∈ behavior ∧
          incident = family.incidentAssembly outgoing input ∧
          output = family.externalOutgoingReadout.toLinearMap outgoing := by
  constructor
  · rintro ⟨outgoing, ⟨state, hSolution, hSelect⟩, hReadout⟩
    rw [LinearBehavior.mem_selectRight_iff] at hSelect
    rw [ModeTransform.mem_toBehavior_iff_toLinearMap] at hReadout
    have hState : state = state.restrictInl.directSum state.restrictInr :=
      (ModeAmplitude.directSum_restrict state).symm
    have hSolution' :
        (input, state.restrictInl.directSum state.restrictInr) ∈
          family.closedSolutionBehavior behavior := by
      rw [← hState]
      exact hSolution
    rcases (family.mem_closedSolutionBehavior_directSum_iff behavior _ _ _).mp hSolution' with
      ⟨hBoundary, hIncident⟩
    refine ⟨state.restrictInl, state.restrictInr, hBoundary, hIncident, ?_⟩
    change outgoing = state.restrictInr at hSelect
    change output = family.externalOutgoingReadout.toLinearMap outgoing at hReadout
    rw [hSelect] at hReadout
    exact hReadout
  · rintro ⟨incident, outgoing, hBoundary, hIncident, hOutput⟩
    refine ⟨outgoing, ⟨incident.directSum outgoing, ?_, ?_⟩, ?_⟩
    · exact (family.mem_closedSolutionBehavior_directSum_iff behavior _ _ _).mpr
        ⟨hBoundary, hIncident⟩
    · rw [LinearBehavior.mem_selectRight_iff, ModeAmplitude.restrictInr_directSum]
    · exact (ModeTransform.mem_toBehavior_iff_toLinearMap _ _ _).mpr hOutput

omit [Fintype P.Channel] in
/-- The family mate of a flattened inner-stage channel is the inner mate. -/
lemma append_mateEquiv_inl {κ : Type x}
    (inner : PortConnectionFamily P ι)
    (outer : PortConnectionFamily inner.externalPortModeFamily κ)
    (index : ι) (local' : (inner.connection index).LocalChannel) :
    (inner.append outer).mateEquiv ⟨Sum.inl index, local'⟩ =
      ⟨Sum.inl index, (inner.connection index).mateEquiv local'⟩ := rfl

omit [Fintype P.Channel] in
/-- The family mate of a flattened outer-stage channel is the outer mate. -/
lemma append_mateEquiv_inr {κ : Type x}
    (inner : PortConnectionFamily P ι)
    (outer : PortConnectionFamily inner.externalPortModeFamily κ)
    (index : κ) (local' : (outer.connection index).LocalChannel) :
    (inner.append outer).mateEquiv ⟨Sum.inr index, local'⟩ =
      ⟨Sum.inr index, (outer.connection index).mateEquiv local'⟩ := by
  rcases local' with mode | mode <;> rfl

end PortConnectionFamily

/-!

## H. The flattened incident assembly, stage by stage

-/

namespace PortConnectionFamily

variable {P : PortModeFamily.{u, v}} {ι : Type w} {κ : Type x}
variable (inner : PortConnectionFamily P ι)
variable (outer : PortConnectionFamily inner.externalPortModeFamily κ)
variable [Fintype P.Channel] [Fintype inner.Channel] [Fintype outer.Channel]

/-- Classical equality on ambient channels, kept local to the two-stage layer. -/
local instance twoStageChannelDecidableEq : DecidableEq P.Channel := Classical.decEq _

/-- The external channels of a finite inner stage are finite. -/
local instance twoStageInnerExternalChannelFintype : Fintype inner.ExternalChannel := by
  classical
  infer_instance

/-- The boundary channels exposed by a finite inner stage are finite. -/
local instance twoStageBoundaryChannelFintype :
    Fintype inner.externalPortModeFamily.Channel :=
  Fintype.ofEquiv _ inner.boundaryChannelEquiv.symm

/-- The connected channels of the flattened family are finite. -/
local instance twoStageAppendChannelFintype : Fintype (inner.append outer).Channel :=
  Fintype.ofEquiv _ (inner.appendChannelEquiv outer).symm

/-- Classical equality on the flattened connected channels. -/
local instance twoStageAppendChannelDecidableEq :
    DecidableEq (inner.append outer).Channel := Classical.decEq _

/-- On an inner-connected coordinate the flattened assembly is the inner stage's own routing.

The outer stage and the external input are invisible there: a subsystem's internal wiring is not
renegotiated by the wiring that reuses the subsystem.
-/
lemma append_incidentAssembly_apply_inner
    (outgoing : ModeAmplitude (Outgoing P.Channel))
    (external : ModeAmplitude (Incident (inner.append outer).ExternalChannel))
    (channel : inner.Channel) :
    (inner.append outer).incidentAssembly outgoing external
        (Incident.mk (inner.channelEmbedding channel)) =
      outgoing (Outgoing.mk (inner.channelEmbedding (inner.mateEquiv channel))) := by
  rcases channel with ⟨index, local'⟩
  rw [← inner.append_channelEmbedding_inl outer index local',
    (inner.append outer).incidentAssembly_apply_connected_channel,
    inner.append_mateEquiv_inl outer, inner.append_channelEmbedding_inl outer]
  rfl

/-- On an outer-connected coordinate the flattened assembly is the outer stage's routing of the
inner stage's boundary amplitudes. -/
lemma append_incidentAssembly_apply_outer
    (outgoing : ModeAmplitude (Outgoing P.Channel))
    (external : ModeAmplitude (Incident (inner.append outer).ExternalChannel))
    (channel : outer.Channel) :
    (inner.append outer).incidentAssembly outgoing external
        (Incident.mk
          ((inner.boundaryChannelEquiv (outer.channelEmbedding channel) :
            inner.ExternalChannel) : P.Channel)) =
      outgoing (Outgoing.mk
        ((inner.boundaryChannelEquiv (outer.channelEmbedding (outer.mateEquiv channel)) :
          inner.ExternalChannel) : P.Channel)) := by
  rcases channel with ⟨index, local'⟩
  rw [← inner.append_channelEmbedding_inr outer index local',
    (inner.append outer).incidentAssembly_apply_connected_channel,
    inner.append_mateEquiv_inr outer]
  exact congrArg (WithLp.ofLp outgoing)
    (congrArg Outgoing.mk
      (inner.append_channelEmbedding_inr outer index
        ((outer.connection index).mateEquiv local')))

/-- On a fully external coordinate the flattened assembly is exactly the external input. -/
lemma append_incidentAssembly_apply_external
    (outgoing : ModeAmplitude (Outgoing P.Channel))
    (external : ModeAmplitude (Incident (inner.append outer).ExternalChannel))
    (channel : (inner.append outer).ExternalChannel) :
    (inner.append outer).incidentAssembly outgoing external (Incident.mk channel.1) =
      external (Incident.mk channel) :=
  (inner.append outer).incidentAssembly_apply_external outgoing external channel

end PortConnectionFamily

namespace FlatNetlist

variable (netlist : FlatNetlist.{u, v, w, x})
variable [Fintype netlist.Channel] [Fintype netlist.ConnectedChannel]

/-- A flat netlist's singular-safe external behavior is the relational closure of its assembled
component graph by its wiring. -/
lemma behavior_eq_closeBehavior :
    netlist.behavior = netlist.connections.closeBehavior netlist.componentBehavior := by
  ext ⟨input, output⟩
  rw [netlist.mem_behavior_iff_componentBehavior,
    netlist.connections.mem_closeBehavior_iff]

end FlatNetlist

end

end Optics
