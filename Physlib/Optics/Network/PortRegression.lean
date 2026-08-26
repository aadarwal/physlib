/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.Port

/-!
# Regression tests for typed optical ports and routing

## i. Overview

This file uses two different port-mode types and a deliberately order-reversing equivalence. The
west modes are `upper` and `lower`, while the east modes are `primary` and `secondary`; the
connection pairs `upper` with `secondary` and `lower` with `primary`. The fixture therefore cannot
definitionally identify the two mode fibers: any common labels must pass through the explicit
equivalence, and identity matching fails the exact endpoint tests.

The regressions check flattening, both mate directions, endpoint-presentation exchange, arbitrary
amplitude routing in both directions, exact routing-matrix entries, and normalized modal power. A
nonsymmetric two-channel scattering matrix separately fixes the incident-to-outgoing adapter's row
and column orientation. Finally, a typed local `C * S` definition and action theorem fix the
incident-space product order required by later network elimination.

## ii. Key results

## iii. Table of contents

- A. A genuinely dependent two-port fixture
- B. Flattening and endpoint mating
- C. Exact ideal routing
- D. Oriented scattering and the local `C * S` seam

## iv. References

These are algebraic finite-mode regressions. They do not claim global endpoint uniqueness,
feedback solvability, path phase, reciprocity, electromagnetic flux, or a physical splitter.

-/

@[expose] public section

namespace Optics

noncomputable section

/-!

## A. A genuinely dependent two-port fixture

-/

/-- The two physical ports in the typed-routing regression. -/
abbrev PortRoutingRegressionPort := Bool

/-- Mode labels available only at the west port. -/
abbrev PortRoutingRegressionWestMode := Fin 2

/-- Mode labels available only at the east port. -/
abbrev PortRoutingRegressionEastMode := Bool

/-- The west port label. -/
abbrev portRoutingRegressionWestPort : PortRoutingRegressionPort := false

/-- The east port label. -/
abbrev portRoutingRegressionEastPort : PortRoutingRegressionPort := true

/-- The west-port upper-mode label. -/
abbrev portRoutingRegressionUpperMode : PortRoutingRegressionWestMode := 0

/-- The west-port lower-mode label. -/
abbrev portRoutingRegressionLowerMode : PortRoutingRegressionWestMode := 1

/-- The east-port primary-mode label. -/
abbrev portRoutingRegressionPrimaryMode : PortRoutingRegressionEastMode := true

/-- The east-port secondary-mode label. -/
abbrev portRoutingRegressionSecondaryMode : PortRoutingRegressionEastMode := false

/-- The regression's dependent mode family. -/
abbrev portRoutingRegressionMode : PortRoutingRegressionPort → Type
  | false => PortRoutingRegressionWestMode
  | true => PortRoutingRegressionEastMode

/-- The regression's typed port family. -/
abbrev portRoutingRegressionFamily : PortModeFamily where
  Port := PortRoutingRegressionPort
  Mode := portRoutingRegressionMode

/-- A deliberately order-reversing equivalence between the distinct mode fibers. -/
abbrev portRoutingRegressionModeEquiv :
    PortRoutingRegressionWestMode ≃ PortRoutingRegressionEastMode :=
  finTwoEquiv

/-- The local connection used by the typed-routing regression. -/
abbrev portRoutingRegressionConnection : PortConnection portRoutingRegressionFamily where
  left := portRoutingRegressionWestPort
  right := portRoutingRegressionEastPort
  left_ne_right := by
    decide
  modeEquiv := portRoutingRegressionModeEquiv

/-- Exchanging the regression connection's presentation retains decidable local-channel
equality. -/
local instance portRoutingRegressionSymmLocalChannelDecidableEq :
    DecidableEq portRoutingRegressionConnection.symm.LocalChannel :=
  portRoutingRegressionConnection.swapLocalChannel.symm.decidableEq

/-- Exchanging the regression connection's presentation retains a finite local-channel family. -/
local instance portRoutingRegressionSymmLocalChannelFintype :
    Fintype portRoutingRegressionConnection.symm.LocalChannel :=
  Fintype.ofEquiv portRoutingRegressionConnection.LocalChannel
    portRoutingRegressionConnection.swapLocalChannel

/-!

## B. Flattening and endpoint mating

-/

/-- The left local channel embeds with its west-port tag. -/
lemma portRoutingRegression_channelEmbedding_left :
    portRoutingRegressionConnection.channelEmbedding
        (Sum.inl portRoutingRegressionUpperMode) =
      ⟨portRoutingRegressionWestPort, portRoutingRegressionUpperMode⟩ := rfl

/-- The right local channel embeds with its east-port tag. -/
lemma portRoutingRegression_channelEmbedding_right :
    portRoutingRegressionConnection.channelEmbedding
        (Sum.inr portRoutingRegressionPrimaryMode) =
      ⟨portRoutingRegressionEastPort, portRoutingRegressionPrimaryMode⟩ := rfl

/-- The forward mate uses the nontrivial west-to-east mode equivalence. -/
lemma portRoutingRegression_mateEquiv_left :
    portRoutingRegressionConnection.mateEquiv
        (Sum.inl portRoutingRegressionUpperMode) =
      Sum.inr portRoutingRegressionSecondaryMode := rfl

/-- The reverse mate uses the inverse east-to-west mode equivalence. -/
lemma portRoutingRegression_mateEquiv_right :
    portRoutingRegressionConnection.mateEquiv
        (Sum.inr portRoutingRegressionPrimaryMode) =
      Sum.inl portRoutingRegressionLowerMode := rfl

/-- Exchanging the endpoint presentation uses the inverse fiber equivalence. -/
lemma portRoutingRegression_symm_mateEquiv_left :
    portRoutingRegressionConnection.symm.mateEquiv
        (Sum.inl portRoutingRegressionPrimaryMode) =
      Sum.inr portRoutingRegressionLowerMode := rfl

/-- Exchanging endpoint presentation and swapping the local label preserves its flattened
channel. -/
lemma portRoutingRegression_symm_channelEmbedding :
    portRoutingRegressionConnection.symm.channelEmbedding
        (portRoutingRegressionConnection.swapLocalChannel
          (Sum.inl portRoutingRegressionUpperMode)) =
      portRoutingRegressionConnection.channelEmbedding
        (Sum.inl portRoutingRegressionUpperMode) :=
  portRoutingRegressionConnection.symm_channelEmbedding_swapLocalChannel _

/-- Mating twice recovers every local channel. -/
lemma portRoutingRegression_mateEquiv_apply_apply
    (channel : portRoutingRegressionConnection.LocalChannel) :
    portRoutingRegressionConnection.mateEquiv
        (portRoutingRegressionConnection.mateEquiv channel) = channel :=
  portRoutingRegressionConnection.mateEquiv_apply_apply channel

/-- No local channel in the fixture is its own mate. -/
lemma portRoutingRegression_mateEquiv_ne_self
    (channel : portRoutingRegressionConnection.LocalChannel) :
    portRoutingRegressionConnection.mateEquiv channel ≠ channel :=
  portRoutingRegressionConnection.mateEquiv_ne_self channel

/-!

## C. Exact ideal routing

-/

/-- The matched left-to-right routing-matrix entry is exactly one. -/
lemma portRoutingRegression_idealRouting_entry_matched :
    portRoutingRegressionConnection.idealRouting
        (Incident.mk (Sum.inr portRoutingRegressionSecondaryMode))
        (Outgoing.mk (Sum.inl portRoutingRegressionUpperMode)) = 1 := by
  unfold PortConnection.idealRouting
  rw [ModeTransform.idealRouting_entry]
  simp [portRoutingRegressionConnection, PortConnection.mateEquiv,
    portRoutingRegressionModeEquiv, portRoutingRegressionUpperMode,
    portRoutingRegressionSecondaryMode, finTwoEquiv]

/-- The entry that would route a local endpoint to itself is exactly zero. -/
lemma portRoutingRegression_idealRouting_entry_self :
    portRoutingRegressionConnection.idealRouting
        (Incident.mk (Sum.inl portRoutingRegressionUpperMode))
        (Outgoing.mk (Sum.inl portRoutingRegressionUpperMode)) = 0 := by
  unfold PortConnection.idealRouting
  rw [ModeTransform.idealRouting_entry]
  simp [portRoutingRegressionConnection, PortConnection.mateEquiv,
    portRoutingRegressionModeEquiv, portRoutingRegressionUpperMode, finTwoEquiv]

/-- An arbitrary west-outgoing upper-mode amplitude appears at the east-incident secondary
mode. -/
lemma portRoutingRegression_idealRouting_left_to_right
    (amplitude : ModeAmplitude (Outgoing portRoutingRegressionConnection.LocalChannel)) :
    portRoutingRegressionConnection.idealRouting.toLinearMap amplitude
        (Incident.mk (Sum.inr portRoutingRegressionSecondaryMode)) =
      amplitude (Outgoing.mk (Sum.inl portRoutingRegressionUpperMode)) := by
  rw [← portRoutingRegression_mateEquiv_left]
  exact portRoutingRegressionConnection.idealRouting_apply amplitude
    (Sum.inl portRoutingRegressionUpperMode)

/-- An arbitrary east-outgoing primary-mode amplitude appears at the west-incident lower mode. -/
lemma portRoutingRegression_idealRouting_right_to_left
    (amplitude : ModeAmplitude (Outgoing portRoutingRegressionConnection.LocalChannel)) :
    portRoutingRegressionConnection.idealRouting.toLinearMap amplitude
        (Incident.mk (Sum.inl portRoutingRegressionLowerMode)) =
      amplitude (Outgoing.mk (Sum.inr portRoutingRegressionPrimaryMode)) := by
  rw [← portRoutingRegression_mateEquiv_right]
  exact portRoutingRegressionConnection.idealRouting_apply amplitude
    (Sum.inr portRoutingRegressionPrimaryMode)

/-- The swapped presentation routes an east-outgoing primary mode to the west-incident lower
mode. -/
lemma portRoutingRegression_symm_idealRouting_left_to_right
    (amplitude :
      ModeAmplitude (Outgoing portRoutingRegressionConnection.symm.LocalChannel)) :
    portRoutingRegressionConnection.symm.idealRouting.toLinearMap amplitude
        (Incident.mk (Sum.inr portRoutingRegressionLowerMode)) =
      amplitude (Outgoing.mk (Sum.inl portRoutingRegressionPrimaryMode)) := by
  convert portRoutingRegressionConnection.symm.idealRouting_apply amplitude
    (portRoutingRegressionConnection.swapLocalChannel
      (Sum.inr portRoutingRegressionPrimaryMode)) using 1 <;> rfl

/-- Relabeling both endpoint wrappers by the local swap recovers routing for the exchanged
presentation. -/
lemma portRoutingRegression_symm_idealRouting_reindex :
    portRoutingRegressionConnection.idealRouting.reindex
        (Outgoing.relabelEquiv portRoutingRegressionConnection.swapLocalChannel)
        (Incident.relabelEquiv portRoutingRegressionConnection.swapLocalChannel) =
      portRoutingRegressionConnection.symm.idealRouting :=
  portRoutingRegressionConnection.symm_idealRouting_reindex_swapLocalChannel

/-- Ideal routing preserves the power of every amplitude in the fixture. -/
lemma portRoutingRegression_idealRouting_power
    (amplitude : ModeAmplitude (Outgoing portRoutingRegressionConnection.LocalChannel)) :
    (portRoutingRegressionConnection.idealRouting.toLinearMap amplitude).power =
      amplitude.power :=
  portRoutingRegressionConnection.idealRouting_isPowerPreserving amplitude

/-!

## D. Oriented scattering and the local `C * S` seam

-/

/-- A nonsymmetric raw scattering matrix used to catch row-column or direction-order errors. -/
def portRoutingRegressionRawScattering : ScatteringMatrix (Fin 2) where
  toModeTransform := !![(1 : ℂ), 2; 3, 4]

/-- The oriented adapter keeps row one, column zero equal to three. -/
lemma portRoutingRegression_toOrientedModeTransform_one_zero :
    portRoutingRegressionRawScattering.toOrientedModeTransform
        (Outgoing.mk 1) (Incident.mk 0) = 3 := by
  rw [ScatteringMatrix.toOrientedModeTransform_apply]
  norm_num [portRoutingRegressionRawScattering]

/-- The oriented adapter keeps row zero, column one equal to two. -/
lemma portRoutingRegression_toOrientedModeTransform_zero_one :
    portRoutingRegressionRawScattering.toOrientedModeTransform
        (Outgoing.mk 0) (Incident.mk 1) = 2 := by
  rw [ScatteringMatrix.toOrientedModeTransform_apply]
  norm_num [portRoutingRegressionRawScattering]

/-- The identity local scattering component used to fix the type of the first round-trip product. -/
def portRoutingRegressionLocalScattering :
    ScatteringMatrix portRoutingRegressionConnection.LocalChannel where
  toModeTransform := 1

/-- The local connection-after-component product is an endomorphism of incident amplitudes. -/
def portRoutingRegressionIncidentRoundTrip :
    ModeTransform (Incident portRoutingRegressionConnection.LocalChannel)
      (Incident portRoutingRegressionConnection.LocalChannel) :=
  portRoutingRegressionConnection.idealRouting *
    portRoutingRegressionLocalScattering.toOrientedModeTransform

/-- The local `C * S` product applies component scattering first and then routes its outgoing
result to the matched incident endpoint. -/
lemma portRoutingRegressionIncidentRoundTrip_apply
    (amplitude : ModeAmplitude (Incident portRoutingRegressionConnection.LocalChannel))
    (channel : portRoutingRegressionConnection.LocalChannel) :
    portRoutingRegressionIncidentRoundTrip.toLinearMap amplitude
        (Incident.mk (portRoutingRegressionConnection.mateEquiv channel)) =
      portRoutingRegressionLocalScattering.toOrientedModeTransform.toLinearMap amplitude
        (Outgoing.mk channel) := by
  unfold portRoutingRegressionIncidentRoundTrip
  exact portRoutingRegressionConnection.idealRouting_mul_toOrientedModeTransform_apply
    portRoutingRegressionLocalScattering amplitude channel

end

end Optics
