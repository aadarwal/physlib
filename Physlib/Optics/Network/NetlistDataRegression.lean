/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.NetlistData

/-!
# Regression tests for executable finite optical-netlist data

## i. Overview

These tests encode a two-component, one-link scattering network entirely as finite executable
data. The positive fixture is accepted by the Boolean checker and compiles to typed N4 component
and connection data. Hostile fixtures separately reject self-wiring, endpoint fan-out, port reuse,
and a non-bijective mode table between unequal finite mode fibers.

## ii. Key results

- `netlistDataRegression_wellFormed`: the valid finite fixture passes the reflected checker.
- `netlistDataRegression_compile?_isSome`: successful checking reaches the typed compiler.
- `netlistDataRegression_twoConnections_wellFormed`: endpoint uniqueness accepts disjoint wires.
- `netlistDataRegression_selfWiring_rejected`: a connection cannot reuse its own port.
- `netlistDataRegression_fanOut_rejected`: two wires cannot share a first endpoint port.
- `netlistDataRegression_targetReuse_rejected`: two wires cannot share a second endpoint port.
- `netlistDataRegression_crossEndReuse_rejected`: reuse is rejected across endpoint presentations.
- `netlistDataRegression_modeMismatch_rejected`: proposed mode maps must be mutual inverses.
- `netlistDataRegression_reverseModeMismatch_rejected`: both inverse laws are checked.
- `netlistDataRegression_nonInverseModeTable_rejected`: equal mode counts alone do not suffice.
- `netlistDataRegression_swapModeTable_wellFormed`: a genuine two-mode permutation is accepted.

## iii. Table of contents

- A. A certified two-component fixture
- B. Exact compiled data
- C. Malformed construction tests

## iv. References

The tests exercise structural certification and the proof-carrying compiler boundary. They do not
yet test generic executable assembly of `S`, `C`, `E_in`, or `E_out`; those matrices belong to the
next compiler layer. The coefficients are exact integers evaluated in `ℂ`, and no inverse or
feedback-solvability assumption is used.

-/

@[expose] public section

namespace Optics

/-!

## A. A certified two-component fixture

-/

/-- Two components, each with one external port and one single-mode link port. -/
def netlistDataRegressionShape : FiniteNetlistShape where
  componentCount := 2
  portCount := fun _ => 2
  modeCount := fun _ _ => 1

/-- The first component index of the executable fixture. -/
def netlistDataRegressionComponentA : netlistDataRegressionShape.Component :=
  ⟨0, by decide⟩

/-- The second component index of the executable fixture. -/
def netlistDataRegressionComponentB : netlistDataRegressionShape.Component :=
  ⟨1, by decide⟩

/-- The external physical port of one fixture component. -/
def netlistDataRegressionExternalPort
    (component : netlistDataRegressionShape.Component) : netlistDataRegressionShape.Port :=
  ⟨component, ⟨0, by simp [netlistDataRegressionShape]⟩⟩

/-- The internal-link physical port of one fixture component. -/
def netlistDataRegressionLinkPort
    (component : netlistDataRegressionShape.Component) : netlistDataRegressionShape.Port :=
  ⟨component, ⟨1, by simp [netlistDataRegressionShape]⟩⟩

/-- The unique modeled mode carried by any port of the valid fixture. -/
def netlistDataRegressionMode (port : netlistDataRegressionShape.Port) :
    netlistDataRegressionShape.Mode port :=
  ⟨0, by simp [netlistDataRegressionShape]⟩

/-- A local channel of the valid fixture assembled from its port and unique mode. -/
def netlistDataRegressionLocalChannel
    (component : netlistDataRegressionShape.Component)
    (port : netlistDataRegressionShape.LocalPort component) :
    netlistDataRegressionShape.LocalChannel component :=
  ⟨port, netlistDataRegressionMode ⟨component, port⟩⟩

/-- Exact asymmetric local scattering entries for the two fixture components.

In local port order `(external, link)`, component A has matrix `[[0, 1], [1, 1]]` and component B
has matrix `[[0, 2], [1, 1]]`.
-/
def netlistDataRegressionScattering
    (component : netlistDataRegressionShape.Component) :
    Matrix (netlistDataRegressionShape.LocalChannel component)
      (netlistDataRegressionShape.LocalChannel component) ℤ :=
  fun output input =>
    if output.1.val = 0 then
      if input.1.val = 0 then 0 else if component.val = 0 then 1 else 2
    else 1

/-- The valid single bidirectional link between the two components' link ports. -/
def netlistDataRegressionConnection : FiniteConnectionSpec netlistDataRegressionShape where
  first := netlistDataRegressionLinkPort netlistDataRegressionComponentA
  second := netlistDataRegressionLinkPort netlistDataRegressionComponentB
  modeMap := fun _ =>
    netlistDataRegressionMode
      (netlistDataRegressionLinkPort netlistDataRegressionComponentB)
  modeInv := fun _ =>
    netlistDataRegressionMode
      (netlistDataRegressionLinkPort netlistDataRegressionComponentA)

/-- The valid executable two-component, one-link netlist fixture. -/
def netlistDataRegression : FiniteNetlistData ℤ where
  shape := netlistDataRegressionShape
  scattering := netlistDataRegressionScattering
  connections := #[netlistDataRegressionConnection]

/-- The valid executable fixture satisfies the structural certificate. -/
lemma netlistDataRegression_wellFormed : netlistDataRegression.WellFormed := by
  decide

/-- The reflected Boolean checker accepts the valid executable fixture. -/
lemma netlistDataRegression_wellFormed_eq_true : netlistDataRegression.wellFormed = true := by
  decide

/-- Integer fixture coefficients evaluated as exact complex numbers. -/
def netlistDataRegressionEvaluate : ℤ →+* ℂ := Int.castRingHom ℂ

/-- The typed N4 netlist compiled from the valid executable fixture. -/
abbrev netlistDataRegressionFlatNetlist : FlatNetlist :=
  netlistDataRegression.toFlatNetlist netlistDataRegressionEvaluate
    netlistDataRegression_wellFormed

/-- The unique connection index of the compiled valid fixture. -/
def netlistDataRegressionConnectionIndex : netlistDataRegressionFlatNetlist.Connection :=
  ⟨0, by decide⟩

/-- Checked compilation reaches a typed flat netlist for the valid fixture. -/
lemma netlistDataRegression_compile?_isSome :
    (netlistDataRegression.compile? netlistDataRegressionEvaluate).isSome = true := by
  rw [FiniteNetlistData.compile?_isSome_eq_wellFormed]
  exact netlistDataRegression_wellFormed_eq_true

/-- A second valid link joining the two formerly external physical ports. -/
def netlistDataRegressionExternalConnection : FiniteConnectionSpec netlistDataRegressionShape where
  first := netlistDataRegressionExternalPort netlistDataRegressionComponentA
  second := netlistDataRegressionExternalPort netlistDataRegressionComponentB
  modeMap := fun _ =>
    netlistDataRegressionMode
      (netlistDataRegressionExternalPort netlistDataRegressionComponentB)
  modeInv := fun _ =>
    netlistDataRegressionMode
      (netlistDataRegressionExternalPort netlistDataRegressionComponentA)

/-- A valid two-link fixture in which all four physical ports occur exactly once. -/
def netlistDataRegressionTwoConnections : FiniteNetlistData ℤ :=
  { netlistDataRegression with
    connections := #[netlistDataRegressionConnection, netlistDataRegressionExternalConnection] }

/-- Endpoint uniqueness accepts multiple connections when all physical ports are disjoint. -/
lemma netlistDataRegression_twoConnections_wellFormed :
    netlistDataRegressionTwoConnections.wellFormed = true := by
  decide

/-!

## B. Exact compiled data

-/

/-- Compiled aggregate channels retain constructive finite enumeration. -/
example : Fintype netlistDataRegressionFlatNetlist.Channel := inferInstance

/-- Compiled aggregate channels retain constructive decidable equality. -/
example : DecidableEq netlistDataRegressionFlatNetlist.Channel := inferInstance

/-- Compiled connected channels retain constructive finite enumeration. -/
example : Fintype netlistDataRegressionFlatNetlist.ConnectedChannel := inferInstance

/-- Compiled connected channels retain constructive decidable equality. -/
example : DecidableEq netlistDataRegressionFlatNetlist.ConnectedChannel := inferInstance

/-- The exact external-channel complement remains constructively finite. -/
example : Fintype netlistDataRegressionFlatNetlist.ExternalChannel := inferInstance

/-- The compiled finite instances make the singular-safe N4 behavior directly available. -/
noncomputable example : LinearBehavior netlistDataRegressionFlatNetlist.ExternalIncident
    netlistDataRegressionFlatNetlist.ExternalOutgoing :=
  netlistDataRegressionFlatNetlist.behavior

/-- Compilation retains the exact first physical port of the stored connection. -/
lemma netlistDataRegression_compiledConnection_left :
    (netlistDataRegressionFlatNetlist.connections.connection
      netlistDataRegressionConnectionIndex).left =
      netlistDataRegressionLinkPort netlistDataRegressionComponentA := rfl

/-- Compilation retains the exact second physical port of the stored connection. -/
lemma netlistDataRegression_compiledConnection_right :
    (netlistDataRegressionFlatNetlist.connections.connection
      netlistDataRegressionConnectionIndex).right =
      netlistDataRegressionLinkPort netlistDataRegressionComponentB := rfl

/-- Compilation uses the certified first-to-second mode table. -/
lemma netlistDataRegression_compiledConnection_modeEquiv :
    (netlistDataRegressionFlatNetlist.connections.connection
      netlistDataRegressionConnectionIndex).modeEquiv
        (netlistDataRegressionMode
          (netlistDataRegressionLinkPort netlistDataRegressionComponentA)) =
      netlistDataRegressionMode
        (netlistDataRegressionLinkPort netlistDataRegressionComponentB) := rfl

/-- Compilation evaluates the asymmetric component-B link-to-external gain exactly. -/
lemma netlistDataRegression_compiledScattering_entry :
    (netlistDataRegressionFlatNetlist.components.scattering
      netlistDataRegressionComponentB).toModeTransform
        (netlistDataRegressionLocalChannel netlistDataRegressionComponentB
          (netlistDataRegressionExternalPort netlistDataRegressionComponentB).2)
        (netlistDataRegressionLocalChannel netlistDataRegressionComponentB
          (netlistDataRegressionLinkPort netlistDataRegressionComponentB).2) = 2 := rfl

/-- Compilation does not transpose component B's external-to-link gain. -/
lemma netlistDataRegression_compiledScattering_transposedEntry :
    (netlistDataRegressionFlatNetlist.components.scattering
      netlistDataRegressionComponentB).toModeTransform
        (netlistDataRegressionLocalChannel netlistDataRegressionComponentB
          (netlistDataRegressionLinkPort netlistDataRegressionComponentB).2)
        (netlistDataRegressionLocalChannel netlistDataRegressionComponentB
          (netlistDataRegressionExternalPort netlistDataRegressionComponentB).2) = 1 := by
  change netlistDataRegressionEvaluate
    (netlistDataRegressionScattering netlistDataRegressionComponentB
      (netlistDataRegressionLocalChannel netlistDataRegressionComponentB
        (netlistDataRegressionLinkPort netlistDataRegressionComponentB).2)
      (netlistDataRegressionLocalChannel netlistDataRegressionComponentB
        (netlistDataRegressionExternalPort netlistDataRegressionComponentB).2)) = 1
  have hOutput :
      (netlistDataRegressionLocalChannel netlistDataRegressionComponentB
        (netlistDataRegressionLinkPort netlistDataRegressionComponentB).2).1.val = 1 := rfl
  simp [netlistDataRegressionScattering, hOutput]

/-- Compilation evaluates component A independently of component B's asymmetric gain. -/
lemma netlistDataRegression_compiledScattering_componentAEntry :
    (netlistDataRegressionFlatNetlist.components.scattering
      netlistDataRegressionComponentA).toModeTransform
        (netlistDataRegressionLocalChannel netlistDataRegressionComponentA
          (netlistDataRegressionExternalPort netlistDataRegressionComponentA).2)
        (netlistDataRegressionLocalChannel netlistDataRegressionComponentA
          (netlistDataRegressionLinkPort netlistDataRegressionComponentA).2) = 1 := by
  change netlistDataRegressionEvaluate
    (netlistDataRegressionScattering netlistDataRegressionComponentA
      (netlistDataRegressionLocalChannel netlistDataRegressionComponentA
        (netlistDataRegressionExternalPort netlistDataRegressionComponentA).2)
      (netlistDataRegressionLocalChannel netlistDataRegressionComponentA
        (netlistDataRegressionLinkPort netlistDataRegressionComponentA).2)) = 1
  have hOutput :
      (netlistDataRegressionLocalChannel netlistDataRegressionComponentA
        (netlistDataRegressionExternalPort netlistDataRegressionComponentA).2).1.val = 0 := rfl
  have hInput :
      (netlistDataRegressionLocalChannel netlistDataRegressionComponentA
        (netlistDataRegressionLinkPort netlistDataRegressionComponentA).2).1.val = 1 := rfl
  have hComponent : netlistDataRegressionComponentA.val = 0 := rfl
  simp [netlistDataRegressionScattering, hOutput, hInput, hComponent]

/-!

## C. Malformed construction tests

-/

/-- A malformed connection that joins A's link port to itself. -/
def netlistDataRegressionSelfConnection : FiniteConnectionSpec netlistDataRegressionShape where
  first := netlistDataRegressionLinkPort netlistDataRegressionComponentA
  second := netlistDataRegressionLinkPort netlistDataRegressionComponentA
  modeMap := fun mode => mode
  modeInv := fun mode => mode

/-- The self-wired hostile fixture. -/
def netlistDataRegressionSelfWiring : FiniteNetlistData ℤ :=
  { netlistDataRegression with connections := #[netlistDataRegressionSelfConnection] }

/-- The executable checker rejects self-wiring. -/
lemma netlistDataRegression_selfWiring_rejected :
    netlistDataRegressionSelfWiring.wellFormed = false := by
  decide

/-- Checked compilation returns no semantic netlist for the self-wired fixture. -/
lemma netlistDataRegression_selfWiring_compile?_eq_none :
    netlistDataRegressionSelfWiring.compile? netlistDataRegressionEvaluate = none := by
  have hMalformed : ¬netlistDataRegressionSelfWiring.WellFormed :=
    (FiniteNetlistData.wellFormed_eq_false_iff _).mp
      netlistDataRegression_selfWiring_rejected
  simp [FiniteNetlistData.compile?, hMalformed]

/-- A second connection that reuses A's link port and reaches B's external port. -/
def netlistDataRegressionFanOutConnection : FiniteConnectionSpec netlistDataRegressionShape where
  first := netlistDataRegressionLinkPort netlistDataRegressionComponentA
  second := netlistDataRegressionExternalPort netlistDataRegressionComponentB
  modeMap := fun _ =>
    netlistDataRegressionMode
      (netlistDataRegressionExternalPort netlistDataRegressionComponentB)
  modeInv := fun _ =>
    netlistDataRegressionMode
      (netlistDataRegressionLinkPort netlistDataRegressionComponentA)

/-- The repeated-first-endpoint fan-out hostile fixture. -/
def netlistDataRegressionFanOut : FiniteNetlistData ℤ :=
  { netlistDataRegression with
    connections := #[netlistDataRegressionConnection, netlistDataRegressionFanOutConnection] }

/-- The executable checker rejects endpoint fan-out. -/
lemma netlistDataRegression_fanOut_rejected :
    netlistDataRegressionFanOut.wellFormed = false := by
  decide

/-- A second connection that reuses B's link port from A's external port. -/
def netlistDataRegressionTargetReuseConnection :
    FiniteConnectionSpec netlistDataRegressionShape where
  first := netlistDataRegressionExternalPort netlistDataRegressionComponentA
  second := netlistDataRegressionLinkPort netlistDataRegressionComponentB
  modeMap := fun _ =>
    netlistDataRegressionMode
      (netlistDataRegressionLinkPort netlistDataRegressionComponentB)
  modeInv := fun _ =>
    netlistDataRegressionMode
      (netlistDataRegressionExternalPort netlistDataRegressionComponentA)

/-- The repeated-second-endpoint hostile fixture. -/
def netlistDataRegressionTargetReuse : FiniteNetlistData ℤ :=
  { netlistDataRegression with
    connections := #[
      netlistDataRegressionConnection,
      netlistDataRegressionTargetReuseConnection] }

/-- The executable checker rejects reuse of an already connected physical port. -/
lemma netlistDataRegression_targetReuse_rejected :
    netlistDataRegressionTargetReuse.wellFormed = false := by
  decide

/-- A second connection that presents A's already used link port as its second endpoint. -/
def netlistDataRegressionCrossEndReuseConnection :
    FiniteConnectionSpec netlistDataRegressionShape where
  first := netlistDataRegressionExternalPort netlistDataRegressionComponentB
  second := netlistDataRegressionLinkPort netlistDataRegressionComponentA
  modeMap := fun _ =>
    netlistDataRegressionMode
      (netlistDataRegressionLinkPort netlistDataRegressionComponentA)
  modeInv := fun _ =>
    netlistDataRegressionMode
      (netlistDataRegressionExternalPort netlistDataRegressionComponentB)

/-- The mixed first-versus-second endpoint-reuse hostile fixture. -/
def netlistDataRegressionCrossEndReuse : FiniteNetlistData ℤ :=
  { netlistDataRegression with
    connections := #[
      netlistDataRegressionConnection,
      netlistDataRegressionCrossEndReuseConnection] }

/-- Endpoint uniqueness rejects reuse across the two endpoint presentations. -/
lemma netlistDataRegression_crossEndReuse_rejected :
    netlistDataRegressionCrossEndReuse.wellFormed = false := by
  decide

/-- Two one-port components whose port mode counts are one and two. -/
def netlistDataRegressionModeMismatchShape : FiniteNetlistShape where
  componentCount := 2
  portCount := fun _ => 1
  modeCount := fun component _ => if component.val = 0 then 1 else 2

/-- A non-bijective table proposed between the unequal one-mode and two-mode fibers. -/
def netlistDataRegressionModeMismatchConnection :
    FiniteConnectionSpec netlistDataRegressionModeMismatchShape where
  first := ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩
  second := ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩
  modeMap := fun _ => ⟨0, by decide⟩
  modeInv := fun _ => ⟨0, by decide⟩

/-- The unequal-mode hostile fixture. -/
def netlistDataRegressionModeMismatch : FiniteNetlistData ℤ where
  shape := netlistDataRegressionModeMismatchShape
  scattering := fun _ _ _ => 0
  connections := #[netlistDataRegressionModeMismatchConnection]

/-- The executable checker rejects mode tables that are not mutually inverse. -/
lemma netlistDataRegression_modeMismatch_rejected :
    netlistDataRegressionModeMismatch.wellFormed = false := by
  decide

/-- The same unequal mode fibers presented from the two-mode port to the one-mode port. -/
def netlistDataRegressionReverseModeMismatchConnection :
    FiniteConnectionSpec netlistDataRegressionModeMismatchShape where
  first := ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩
  second := ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩
  modeMap := fun _ => ⟨0, by decide⟩
  modeInv := fun _ => ⟨0, by decide⟩

/-- The reverse unequal-mode hostile fixture. -/
def netlistDataRegressionReverseModeMismatch : FiniteNetlistData ℤ where
  shape := netlistDataRegressionModeMismatchShape
  scattering := fun _ _ _ => 0
  connections := #[netlistDataRegressionReverseModeMismatchConnection]

/-- The checker tests both mode-table inverse laws, independently of endpoint presentation. -/
lemma netlistDataRegression_reverseModeMismatch_rejected :
    netlistDataRegressionReverseModeMismatch.wellFormed = false := by
  decide

/-- Two one-port components, each carrying exactly two modeled modes. -/
def netlistDataRegressionTwoModeShape : FiniteNetlistShape where
  componentCount := 2
  portCount := fun _ => 1
  modeCount := fun _ _ => 2

/-- The executable transposition of the two labels in `Fin 2`. -/
def netlistDataRegressionSwapMode (mode : Fin 2) : Fin 2 :=
  if mode.val = 0 then ⟨1, by decide⟩ else ⟨0, by decide⟩

/-- An equal-cardinality mode table whose proposed inverse swaps the two modes. -/
def netlistDataRegressionNonInverseModeConnection :
    FiniteConnectionSpec netlistDataRegressionTwoModeShape where
  first := ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩
  second := ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩
  modeMap := fun mode => mode
  modeInv := netlistDataRegressionSwapMode

/-- The equal-cardinality but non-inverse mode-table fixture. -/
def netlistDataRegressionNonInverseModeTable : FiniteNetlistData ℤ where
  shape := netlistDataRegressionTwoModeShape
  scattering := fun _ _ _ => 0
  connections := #[netlistDataRegressionNonInverseModeConnection]

/-- The checker rejects non-inverse mode tables even when both mode counts agree. -/
lemma netlistDataRegression_nonInverseModeTable_rejected :
    netlistDataRegressionNonInverseModeTable.wellFormed = false := by
  decide

/-- A two-mode connection whose forward and inverse tables are both the genuine swap. -/
def netlistDataRegressionSwapModeConnection :
    FiniteConnectionSpec netlistDataRegressionTwoModeShape where
  first := ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩
  second := ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩
  modeMap := netlistDataRegressionSwapMode
  modeInv := netlistDataRegressionSwapMode

/-- The valid equal-cardinality two-mode permutation fixture. -/
def netlistDataRegressionSwapModeTable : FiniteNetlistData ℤ where
  shape := netlistDataRegressionTwoModeShape
  scattering := fun _ _ _ => 0
  connections := #[netlistDataRegressionSwapModeConnection]

/-- The checker accepts an explicitly invertible nontrivial mode permutation. -/
lemma netlistDataRegression_swapModeTable_wellFormed :
    netlistDataRegressionSwapModeTable.wellFormed = true := by
  decide

end Optics
