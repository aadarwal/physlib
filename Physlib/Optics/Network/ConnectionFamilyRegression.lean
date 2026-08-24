/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.ConnectionFamily

/-!
# Regression tests for typed optical connection families

## i. Overview

This file constructs two independent connections whose four ports have genuinely dependent mode
fibers. It checks ambient channel embedding, forward and reverse blockwise mating, exact matched,
self, and cross-block routing entries, arbitrary-amplitude action, and normalized modal power.

Two negative fixtures test the physical-port uniqueness invariant. One assignment reuses a
nonempty port across two otherwise valid local connections. A second assignment reuses a port whose
mode fiber is empty: its aggregate channel map is vacuously injective even though its physical
endpoint map is not. The latter prevents replacing port-level uniqueness with the weaker
channel-level condition.

## ii. Scope

These are connected-channel algebra regressions. They do not define external channels, global
partial routing, components, netlists, feedback, reciprocity, or electromagnetic power.

## iii. Table of contents

- A. A dependent four-port family
- B. Connected-channel embedding and mating
- C. Exact blockwise routing
- D. Reused endpoints
- E. Empty-mode counterexample

-/

@[expose] public section

namespace Optics

noncomputable section

/-!

## A. A dependent four-port family

-/

/-- The four physical ports in the connection-family regression. -/
inductive ConnectionFamilyRegressionPort
  | west
  | east
  | north
  | south
  deriving DecidableEq

instance : Fintype ConnectionFamilyRegressionPort where
  elems := {.west, .east, .north, .south}
  complete := fun port => by cases port <;> decide

/-- The dependent mode fiber at each regression port. -/
abbrev connectionFamilyRegressionMode : ConnectionFamilyRegressionPort → Type
  | .west => Fin 2
  | .east => Bool
  | .north => Fin 2
  | .south => Bool

/-- The dependent port family used by the connection-family regression. -/
abbrev connectionFamilyRegressionPortFamily : PortModeFamily where
  Port := ConnectionFamilyRegressionPort
  Mode := connectionFamilyRegressionMode

/-- The west-to-east local connection in the regression family. -/
abbrev connectionFamilyRegressionWestEast :
    PortConnection connectionFamilyRegressionPortFamily where
  left := .west
  right := .east
  left_ne_right := by decide
  modeEquiv := finTwoEquiv

/-- The opposite-order mode equivalence used by the second regression connection. -/
abbrev connectionFamilyRegressionOppositeModeEquiv : Fin 2 ≃ Bool where
  toFun mode := !(finTwoEquiv mode)
  invFun mode := finTwoEquiv.symm (!mode)
  left_inv := by decide
  right_inv := by decide

/-- The north-to-south local connection in the regression family. -/
abbrev connectionFamilyRegressionNorthSouth :
    PortConnection connectionFamilyRegressionPortFamily where
  left := .north
  right := .south
  left_ne_right := by decide
  modeEquiv := connectionFamilyRegressionOppositeModeEquiv

/-- The two local connections selected by the `Bool` family index. -/
abbrev connectionFamilyRegressionConnection :
    Bool → PortConnection connectionFamilyRegressionPortFamily
  | false => connectionFamilyRegressionWestEast
  | true => connectionFamilyRegressionNorthSouth

/-- A proof-carrying two-connection family with no reused physical port. -/
abbrev connectionFamilyRegressionFamily :
    PortConnectionFamily connectionFamilyRegressionPortFamily Bool where
  connection := connectionFamilyRegressionConnection
  endpointPort_injective := by decide

/-- Each selected local channel block has decidable equality. -/
local instance connectionFamilyRegressionLocalChannelDecidableEq (index : Bool) :
    DecidableEq (connectionFamilyRegressionFamily.connection index).LocalChannel := by
  cases index <;> infer_instance

/-- Each selected local channel block is finite. -/
local instance connectionFamilyRegressionLocalChannelFintype (index : Bool) :
    Fintype (connectionFamilyRegressionFamily.connection index).LocalChannel := by
  cases index <;> infer_instance

/-!

## B. Connected-channel embedding and mating

-/

/-- A west upper mode embeds into the ambient channel with its physical port tag. -/
lemma connectionFamilyRegression_channelEmbedding_west :
    connectionFamilyRegressionFamily.channelEmbedding
        ⟨false, Sum.inl (0 : Fin 2)⟩ =
      ⟨ConnectionFamilyRegressionPort.west, (0 : Fin 2)⟩ := rfl

/-- A south primary mode embeds into the ambient channel with its physical port tag. -/
lemma connectionFamilyRegression_channelEmbedding_south :
    connectionFamilyRegressionFamily.channelEmbedding
        ⟨true, Sum.inr true⟩ =
      ⟨ConnectionFamilyRegressionPort.south, true⟩ := rfl

/-- The forward family mate uses the west-to-east dependent mode equivalence. -/
lemma connectionFamilyRegression_mateEquiv_west :
    connectionFamilyRegressionFamily.mateEquiv
        ⟨false, Sum.inl (0 : Fin 2)⟩ =
      ⟨false, Sum.inr false⟩ := rfl

/-- The reverse family mate uses the inverse south-to-north dependent mode equivalence. -/
lemma connectionFamilyRegression_mateEquiv_south :
    connectionFamilyRegressionFamily.mateEquiv
        ⟨true, Sum.inr true⟩ =
      ⟨true, Sum.inl (0 : Fin 2)⟩ := rfl

/-- Embedding after the reverse family mate selects the exact north-port dependent mode. -/
lemma connectionFamilyRegression_channelEmbedding_mate_south :
    connectionFamilyRegressionFamily.channelEmbedding
        (connectionFamilyRegressionFamily.mateEquiv ⟨true, Sum.inr true⟩) =
      ⟨ConnectionFamilyRegressionPort.north, (0 : Fin 2)⟩ := rfl

/-- Mating twice recovers every connected channel in the regression family. -/
lemma connectionFamilyRegression_mateEquiv_apply_apply
    (channel : connectionFamilyRegressionFamily.Channel) :
    connectionFamilyRegressionFamily.mateEquiv
        (connectionFamilyRegressionFamily.mateEquiv channel) = channel :=
  connectionFamilyRegressionFamily.mateEquiv_apply_apply channel

/-- No connected channel in the regression family is its own mate. -/
lemma connectionFamilyRegression_mateEquiv_ne_self
    (channel : connectionFamilyRegressionFamily.Channel) :
    connectionFamilyRegressionFamily.mateEquiv channel ≠ channel :=
  connectionFamilyRegressionFamily.mateEquiv_ne_self channel

/-!

## C. Exact blockwise routing

-/

/-- The matched west-to-east family-routing entry is exactly one. -/
lemma connectionFamilyRegression_idealRouting_entry_mate :
    connectionFamilyRegressionFamily.idealRouting
        (Incident.mk ⟨false, Sum.inr false⟩)
        (Outgoing.mk ⟨false, Sum.inl (0 : Fin 2)⟩) = 1 := by
  rw [← connectionFamilyRegression_mateEquiv_west]
  exact connectionFamilyRegressionFamily.idealRouting_entry_mate _

/-- The family-routing entry from a connected channel to itself is exactly zero. -/
lemma connectionFamilyRegression_idealRouting_entry_self :
    connectionFamilyRegressionFamily.idealRouting
        (Incident.mk ⟨false, Sum.inl (0 : Fin 2)⟩)
        (Outgoing.mk ⟨false, Sum.inl (0 : Fin 2)⟩) = 0 :=
  connectionFamilyRegressionFamily.idealRouting_entry_self _

/-- Routing has a zero entry from the west-east block into the north-south block. -/
lemma connectionFamilyRegression_idealRouting_entry_cross :
    connectionFamilyRegressionFamily.idealRouting
        (Incident.mk ⟨true, Sum.inr true⟩)
        (Outgoing.mk ⟨false, Sum.inl (0 : Fin 2)⟩) = 0 :=
  connectionFamilyRegressionFamily.idealRouting_entry_of_ne_index (by decide) _ _

/-- An arbitrary west-outgoing upper-mode amplitude reaches the matched east-incident mode. -/
lemma connectionFamilyRegression_idealRouting_apply
    (amplitude : ModeAmplitude (Outgoing connectionFamilyRegressionFamily.Channel)) :
    connectionFamilyRegressionFamily.idealRouting.toLinearMap amplitude
        (Incident.mk ⟨false, Sum.inr false⟩) =
      amplitude (Outgoing.mk ⟨false, Sum.inl (0 : Fin 2)⟩) := by
  rw [← connectionFamilyRegression_mateEquiv_west]
  exact connectionFamilyRegressionFamily.idealRouting_apply amplitude _

/-- Family routing preserves the power of every connected-channel amplitude in the fixture. -/
lemma connectionFamilyRegression_idealRouting_power
    (amplitude : ModeAmplitude (Outgoing connectionFamilyRegressionFamily.Channel)) :
    (connectionFamilyRegressionFamily.idealRouting.toLinearMap amplitude).power =
      amplitude.power :=
  connectionFamilyRegressionFamily.idealRouting_isPowerPreserving amplitude

/-!

## D. Reused endpoints

-/

/-- A second individually valid connection that reuses the east port. -/
abbrev connectionFamilyRegressionEastSouth :
    PortConnection connectionFamilyRegressionPortFamily where
  left := .east
  right := .south
  left_ne_right := by decide
  modeEquiv := Equiv.refl Bool

/-- A raw two-connection assignment that reuses one physical endpoint. -/
abbrev connectionFamilyRegressionOverlappingConnection :
    Bool → PortConnection connectionFamilyRegressionPortFamily
  | false => connectionFamilyRegressionWestEast
  | true => connectionFamilyRegressionEastSouth

/-- The overlapping raw assignment fails the physical endpoint-injectivity requirement. -/
lemma connectionFamilyRegression_overlapping_not_injective :
    ¬Function.Injective fun endpoint : Bool × PortConnection.End =>
      (connectionFamilyRegressionOverlappingConnection endpoint.1).endpointPort endpoint.2 := by
  intro hInjective
  have hEndpoint : (false, PortConnection.End.right) =
      (true, PortConnection.End.left) := hInjective rfl
  have hDistinct : (false, PortConnection.End.right) ≠
      (true, PortConnection.End.left) := by decide
  exact hDistinct hEndpoint

/-!

## E. Empty-mode counterexample

-/

/-- The three physical ports in the empty-mode endpoint-reuse fixture. -/
inductive EmptyModeReuseRegressionPort
  | first
  | shared
  | last
  deriving DecidableEq

instance : Fintype EmptyModeReuseRegressionPort where
  elems := {.first, .shared, .last}
  complete := fun port => by cases port <;> decide

/-- The empty mode fiber at every port in the endpoint-reuse fixture. -/
abbrev emptyModeReuseRegressionMode (_ : EmptyModeReuseRegressionPort) := Empty

/-- The all-empty dependent port family used to test channel-level uniqueness. -/
abbrev emptyModeReuseRegressionPortFamily : PortModeFamily where
  Port := EmptyModeReuseRegressionPort
  Mode := emptyModeReuseRegressionMode

/-- The first-to-shared empty-mode connection. -/
abbrev emptyModeReuseRegressionFirstShared :
    PortConnection emptyModeReuseRegressionPortFamily where
  left := .first
  right := .shared
  left_ne_right := by decide
  modeEquiv := Equiv.refl Empty

/-- The shared-to-last empty-mode connection. -/
abbrev emptyModeReuseRegressionSharedLast :
    PortConnection emptyModeReuseRegressionPortFamily where
  left := .shared
  right := .last
  left_ne_right := by decide
  modeEquiv := Equiv.refl Empty

/-- The raw empty-mode assignment that reuses its shared physical port. -/
abbrev emptyModeReuseRegressionConnection :
    Bool → PortConnection emptyModeReuseRegressionPortFamily
  | false => emptyModeReuseRegressionFirstShared
  | true => emptyModeReuseRegressionSharedLast

/-- The aggregate channel map of the invalid empty-mode assignment. -/
def emptyModeReuseRegressionChannelMap
    (channel : Σ index, (emptyModeReuseRegressionConnection index).LocalChannel) :
    emptyModeReuseRegressionPortFamily.Channel :=
  (emptyModeReuseRegressionConnection channel.1).channelEmbedding channel.2

/-- The empty-mode aggregate channel map is injective only because its domain is empty. -/
lemma emptyModeReuseRegression_channelMap_injective :
    Function.Injective emptyModeReuseRegressionChannelMap := by
  intro first second hChannel
  rcases first with ⟨index, channel⟩
  rcases channel with channel | channel <;> exact channel.elim

/-- Despite its vacuous channel injectivity, the empty-mode assignment reuses a physical port. -/
lemma emptyModeReuseRegression_endpointPort_not_injective :
    ¬Function.Injective fun endpoint : Bool × PortConnection.End =>
      (emptyModeReuseRegressionConnection endpoint.1).endpointPort endpoint.2 := by
  intro hInjective
  have hEndpoint : (false, PortConnection.End.right) =
      (true, PortConnection.End.left) := hInjective rfl
  have hDistinct : (false, PortConnection.End.right) ≠
      (true, PortConnection.End.left) := by decide
  exact hDistinct hEndpoint

end

end Optics
