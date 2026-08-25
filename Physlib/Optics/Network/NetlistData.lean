/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.FlatNetlist

/-!
# Executable finite optical-netlist data

## i. Overview

This file provides the executable input boundary for finite optical scattering networks. A shape
uses natural-number sizes and `Fin` indices for components, ports, and mode fibers. A connection
stores two physical ports and explicit mutually inverse mode maps. Connections are bidirectional;
the existing N4 kernel gives their routed channel ends the nominal `Outgoing → Incident` types.
Mode compatibility is checked from finite data rather than recovered through a noncomputable
equivalence.

`FiniteNetlistData.WellFormed` additionally requires the physical-port map from all connection ends
to be injective. The one condition simultaneously rules out self-wiring, endpoint reuse, and
wire-level fan-out. `FiniteNetlistData.wellFormed` reflects this proposition to a Boolean, and a
successful certificate constructs the existing proof-carrying `FlatNetlist` semantics.
The Boolean is the exhaustive finite decision procedure for that specification, not an independent
oracle; any later optimized checker must be proved equivalent to the same proposition.

## ii. Scope

The checker certifies only finite shape, mutually inverse mode matching, and one-to-one physical
wiring. It does not check component passivity, losslessness, reciprocity, physical realizability,
or feedback solvability. In particular, successful compilation does not imply that `1 - C * S` is
invertible. Connection gains, path phase, and delay remain component data rather than wire data.
There is no directed-wire flag to check: each stored physical connection is bidirectional, while
the direction of every derived channel map is enforced by N4's `Incident` and `Outgoing` types.

The coefficient type is unrestricted at the data boundary. Compilation to the current
complex-valued optics kernel takes an explicit coefficient ring homomorphism. Generic
executable assembly of `S`, `C`, `E_in`, and `E_out`, together with its entrywise soundness, is a
separate layer built on this certified boundary.

## iii. Key definitions and results

- `FiniteNetlistShape`: finite dependent component, port, and mode sizes.
- `FiniteConnectionSpec`: a bidirectional physical-port connection with explicit mode maps in both
  directions.
- `FiniteNetlistData`: local scattering entries and a finite array of connection specifications.
- `FiniteNetlistData.WellFormed`: mutually inverse mode maps and globally unique endpoint ports.
- `FiniteNetlistData.wellFormed_eq_true_iff`: Boolean reflection of the certificate.
- `FiniteNetlistData.toFlatNetlist`: proof-carrying compilation into the N4 relational kernel.
- `FiniteNetlistData.compile?`: checked compilation that rejects malformed finite data.

## iv. Table of contents

- A. Finite netlist shapes
- B. Executable connection and component data
- C. Decidable well-formedness
- D. Compilation to typed flat netlists

-/

@[expose] public section

namespace Optics

/-!

## A. Finite netlist shapes

-/

/-- Natural-number sizes for a finite dependent family of optical components, ports, and modes. -/
structure FiniteNetlistShape where
  /-- The number of component instances. -/
  componentCount : ℕ
  /-- The number of physical ports owned by each component. -/
  portCount : Fin componentCount → ℕ
  /-- The number of modeled modes carried by each physical port. -/
  modeCount : (component : Fin componentCount) → Fin (portCount component) → ℕ

namespace FiniteNetlistShape

variable (shape : FiniteNetlistShape)

/-- The finite component index of a netlist shape. -/
abbrev Component := Fin shape.componentCount

/-- The finite local-port index owned by one component. -/
abbrev LocalPort (component : shape.Component) := Fin (shape.portCount component)

/-- The dependent sum of every component-owned physical port. -/
abbrev Port := Σ component, shape.LocalPort component

/-- The finite mode fiber carried by an aggregate physical port. -/
abbrev Mode (port : shape.Port) := Fin (shape.modeCount port.1 port.2)

/-- The local port and mode family owned by one finite component. -/
def portModeFamily (component : shape.Component) : PortModeFamily where
  Port := shape.LocalPort component
  Mode := fun port => Fin (shape.modeCount component port)

/-- The dependent local-channel type of one finite component. -/
abbrev LocalChannel (component : shape.Component) :=
  (shape.portModeFamily component).Channel

/-- The aggregate physical port and mode family of a finite shape. -/
def aggregatePortModeFamily : PortModeFamily where
  Port := shape.Port
  Mode := shape.Mode

/-- The aggregate channel type of a finite shape. -/
abbrev Channel := shape.aggregatePortModeFamily.Channel

end FiniteNetlistShape

/-!

## B. Executable connection and component data

-/

/-- Executable data for one bidirectional physical connection.

The two mode functions describe both directions of the physical connection; well-formedness
checks that they are mutual inverses before constructing a `PortConnection`.
-/
structure FiniteConnectionSpec (shape : FiniteNetlistShape) where
  /-- The first connected physical port in this presentation. -/
  first : shape.Port
  /-- The second connected physical port in this presentation. -/
  second : shape.Port
  /-- The mode matching from the first port to the second port. -/
  modeMap : shape.Mode first → shape.Mode second
  /-- The proposed inverse mode matching from the second port to the first port. -/
  modeInv : shape.Mode second → shape.Mode first

/-- Finite executable component gains and physical connection data over a coefficient type `R`. -/
structure FiniteNetlistData (R : Type*) where
  /-- The finite dependent component, port, and mode shape. -/
  shape : FiniteNetlistShape
  /-- The local scattering entries of every component. -/
  scattering : (component : shape.Component) →
    Matrix (shape.LocalChannel component) (shape.LocalChannel component) R
  /-- The finite physical connections between component-owned ports. -/
  connections : Array (FiniteConnectionSpec shape)

namespace FiniteNetlistData

variable {R : Type*} (data : FiniteNetlistData R)

/-- The finite index type of stored physical connections. -/
abbrev Connection := Fin data.connections.size

/-- The connection specification selected by a finite connection index. -/
def connection (index : data.Connection) : FiniteConnectionSpec data.shape :=
  data.connections[index]

/-- An indexed left or right endpoint occurrence in the stored connection family. -/
abbrev Endpoint := data.Connection × PortConnection.End

/-- The aggregate physical port selected by an indexed connection endpoint. -/
def endpointPort : data.Endpoint → data.shape.Port
  | (index, .left) => (data.connection index).first
  | (index, .right) => (data.connection index).second

/-!

## C. Decidable well-formedness

-/

/-- Every stored first-to-second mode map has the proposed inverse on its first fiber. -/
def HasLeftInverseModeMaps : Prop :=
  ∀ index mode,
    (data.connection index).modeInv ((data.connection index).modeMap mode) = mode

/-- Every stored first-to-second mode map has the proposed inverse on its second fiber. -/
def HasRightInverseModeMaps : Prop :=
  ∀ index mode,
    (data.connection index).modeMap ((data.connection index).modeInv mode) = mode

/-- No two indexed connection ends select the same aggregate physical port.

This rules out a connection from a port to itself, reuse of a port by two connections, and
wire-level fan-out. Splitters and combiners must instead be supplied as scattering components.
-/
def HasUniqueEndpointPorts : Prop := Function.Injective data.endpointPort

/-- Structural well-formedness of executable finite netlist data. -/
def WellFormed : Prop :=
  data.HasLeftInverseModeMaps ∧
    data.HasRightInverseModeMaps ∧ data.HasUniqueEndpointPorts

instance instDecidableWellFormed : Decidable data.WellFormed := by
  unfold WellFormed HasLeftInverseModeMaps HasRightInverseModeMaps HasUniqueEndpointPorts
  infer_instance

/-- The executable Boolean well-formedness check for finite netlist data. -/
def wellFormed : Bool := decide data.WellFormed

/-- The Boolean checker succeeds exactly for structurally well-formed finite netlist data. -/
lemma wellFormed_eq_true_iff : data.wellFormed = true ↔ data.WellFormed := by
  simp only [wellFormed, decide_eq_true_eq]

/-- The Boolean checker fails exactly for structurally malformed finite netlist data. -/
lemma wellFormed_eq_false_iff : data.wellFormed = false ↔ ¬data.WellFormed := by
  simp only [wellFormed, decide_eq_false_iff_not]

/-- A well-formed connection never selects the same physical port at both of its ends. -/
lemma WellFormed.first_ne_second (h : data.WellFormed) (index : data.Connection) :
    (data.connection index).first ≠ (data.connection index).second := by
  intro hPort
  have hEndpoint : (index, PortConnection.End.left) = (index, PortConnection.End.right) :=
    h.2.2 hPort
  exact PortConnection.End.noConfusion (congrArg Prod.snd hEndpoint)

/-!

## D. Compilation to typed flat netlists

-/

/-- The finite local port and mode family of one component in executable netlist data. -/
def toPortModeFamily (component : data.shape.Component) : PortModeFamily :=
  data.shape.portModeFamily component

section Evaluation

variable [NonAssocSemiring R]

/-- Evaluate executable component entries into the complex-valued scattering-component kernel. -/
def toComponentFamily (evaluate : R →+* ℂ) : ScatteringComponentFamily where
  Component := data.shape.Component
  portFamily := data.toPortModeFamily
  scattering := fun component =>
    ⟨(data.scattering component).map evaluate⟩

/-- Compiled local scattering entries are exactly the evaluated executable coefficients. -/
@[simp]
lemma toComponentFamily_scattering_entry (evaluate : R →+* ℂ)
    (component : data.shape.Component) (output input : data.shape.LocalChannel component) :
    ((data.toComponentFamily evaluate).scattering component).toModeTransform output input =
      evaluate (data.scattering component output input) := rfl

/-- Component compilation retains the shape's exact aggregate physical port and mode family. -/
lemma toComponentFamily_aggregatePortModeFamily (evaluate : R →+* ℂ) :
    (data.toComponentFamily evaluate).aggregatePortModeFamily =
      data.shape.aggregatePortModeFamily := rfl

/-- Compile one certified connection into the typed physical-connection kernel. -/
def toConnection (evaluate : R →+* ℂ) (h : data.WellFormed) (index : data.Connection) :
    PortConnection (data.toComponentFamily evaluate).aggregatePortModeFamily where
  left := (data.connection index).first
  right := (data.connection index).second
  left_ne_right := FiniteNetlistData.WellFormed.first_ne_second data h index
  modeEquiv :=
    { toFun := (data.connection index).modeMap
      invFun := (data.connection index).modeInv
      left_inv := h.1 index
      right_inv := h.2.1 index }

/-- A compiled connection retains the exact stored first physical port. -/
@[simp]
lemma toConnection_left (evaluate : R →+* ℂ) (h : data.WellFormed)
    (index : data.Connection) :
    (data.toConnection evaluate h index).left =
      (data.connection index).first := rfl

/-- A compiled connection retains the exact stored second physical port. -/
@[simp]
lemma toConnection_right (evaluate : R →+* ℂ) (h : data.WellFormed)
    (index : data.Connection) :
    (data.toConnection evaluate h index).right =
      (data.connection index).second := rfl

/-- A compiled connection applies the exact certified first-to-second mode map. -/
@[simp]
lemma toConnection_modeEquiv_apply (evaluate : R →+* ℂ) (h : data.WellFormed)
    (index : data.Connection) (mode : data.shape.Mode (data.connection index).first) :
    (data.toConnection evaluate h index).modeEquiv mode =
      (data.connection index).modeMap mode := rfl

/-- A compiled connection applies the exact certified inverse mode map in reverse. -/
@[simp]
lemma toConnection_modeEquiv_symm_apply (evaluate : R →+* ℂ) (h : data.WellFormed)
    (index : data.Connection) (mode : data.shape.Mode (data.connection index).second) :
    (data.toConnection evaluate h index).modeEquiv.symm mode =
      (data.connection index).modeInv mode := rfl

/-- Compile certified finite connections into a proof-carrying connection family. -/
def toConnectionFamily (evaluate : R →+* ℂ) (h : data.WellFormed) :
    PortConnectionFamily (data.toComponentFamily evaluate).aggregatePortModeFamily
      data.Connection where
  connection := data.toConnection evaluate h
  endpointPort_injective := by
    intro first second hPort
    apply h.2.2
    rcases first with ⟨firstIndex, firstEnd⟩
    rcases second with ⟨secondIndex, secondEnd⟩
    cases firstEnd <;> cases secondEnd <;> exact hPort

/-- Compile certified finite data into the existing singular-safe N4 flat-netlist semantics. -/
def toFlatNetlist (evaluate : R →+* ℂ) (h : data.WellFormed) : FlatNetlist where
  components := data.toComponentFamily evaluate
  Connection := data.Connection
  connections := data.toConnectionFamily evaluate h

/-- Compiled component-indexed local channels retain constructive finite enumeration. -/
instance toComponentFamilyIndexedChannelFintype (evaluate : R →+* ℂ) :
    Fintype (data.toComponentFamily evaluate).IndexedChannel := by
  change Fintype (Σ component : data.shape.Component,
    Σ port : data.shape.LocalPort component, Fin (data.shape.modeCount component port))
  infer_instance

/-- Compiled component-indexed local channels retain constructive decidable equality. -/
instance toComponentFamilyIndexedChannelDecidableEq (evaluate : R →+* ℂ) :
    DecidableEq (data.toComponentFamily evaluate).IndexedChannel := by
  change DecidableEq (Σ component : data.shape.Component,
    Σ port : data.shape.LocalPort component, Fin (data.shape.modeCount component port))
  infer_instance

/-- Compiled aggregate channels retain their constructive finite enumeration. -/
instance toFlatNetlistChannelFintype (evaluate : R →+* ℂ) (h : data.WellFormed) :
    Fintype (data.toFlatNetlist evaluate h).Channel :=
  Fintype.ofEquiv (data.toComponentFamily evaluate).IndexedChannel
    (data.toComponentFamily evaluate).channelEquiv

/-- Compiled aggregate channels retain constructive decidable equality. -/
instance toFlatNetlistChannelDecidableEq (evaluate : R →+* ℂ) (h : data.WellFormed) :
    DecidableEq (data.toFlatNetlist evaluate h).Channel :=
  (data.toComponentFamily evaluate).channelEquiv.symm.decidableEq

/-- Compiled connected channels retain their constructive finite enumeration. -/
instance toFlatNetlistConnectedChannelFintype (evaluate : R →+* ℂ)
    (h : data.WellFormed) : Fintype (data.toFlatNetlist evaluate h).ConnectedChannel := by
  change Fintype (Σ index : data.Connection,
    data.shape.Mode (data.connection index).first ⊕
      data.shape.Mode (data.connection index).second)
  infer_instance

/-- Compiled connected channels retain constructive decidable equality. -/
instance toFlatNetlistConnectedChannelDecidableEq (evaluate : R →+* ℂ)
    (h : data.WellFormed) : DecidableEq (data.toFlatNetlist evaluate h).ConnectedChannel := by
  change DecidableEq (Σ index : data.Connection,
    data.shape.Mode (data.connection index).first ⊕
      data.shape.Mode (data.connection index).second)
  infer_instance

/-- The exact external complement of compiled finite channels remains constructively finite. -/
instance toFlatNetlistExternalChannelFintype (evaluate : R →+* ℂ)
    (h : data.WellFormed) : Fintype (data.toFlatNetlist evaluate h).ExternalChannel := by
  infer_instance

/-- Run the finite checker and compile successful data into the typed N4 flat-netlist kernel. -/
def compile? (evaluate : R →+* ℂ) : Option FlatNetlist :=
  if h : data.WellFormed then some (data.toFlatNetlist evaluate h) else none

/-- Checked compilation succeeds exactly when the executable well-formedness check succeeds. -/
lemma compile?_isSome_eq_wellFormed (evaluate : R →+* ℂ) :
    (data.compile? evaluate).isSome = data.wellFormed := by
  by_cases h : data.WellFormed
  · simp [compile?, wellFormed, h]
  · simp [compile?, wellFormed, h]

end Evaluation

end FiniteNetlistData

end Optics
