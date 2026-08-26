/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.PartialRouting

/-!
# Regression tests for ambient partial routing

## i. Overview

This file connects a two-mode west port to a Boolean-mode east port inside a three-port ambient
family. The third port has one nonempty mode and is not selected by the connection family. The
result is four connected channels inside five ambient channels.

Exact matrix entries distinguish the connected block, a connected entry that is not matched, the
complement incident row, and the complement outgoing column. A unit amplitude on the complement
coordinate is independently shown to have power one and to map to zero, proving that ambient
partial routing is passive but not globally power-preserving. A separate connected amplitude
checks exact preservation on the selected subspace.

## ii. Key results

## iii. Table of contents

- A. A dependent three-port family
- B. Connected and complement channels
- C. Exact ambient routing entries
- D. Omitted-coordinate power witness
- E. Connected-subspace power
- F. Cascade-orientation witness

## iv. References

The complement-coordinate amplitude is excluded from this internal-wiring contribution. Its zero
output does not describe absorption, a matched termination, radiation, or a complete incident-field
boundary condition. All power statements use only normalized finite modal coordinates.

-/

@[expose] public section

namespace Optics

noncomputable section

/-!

## A. A dependent three-port family

-/

/-- The physical ports in the ambient partial-routing regression. -/
inductive PartialRoutingRegressionPort
  | west
  | east
  | exposed
  deriving DecidableEq

instance : Fintype PartialRoutingRegressionPort where
  elems := {.west, .east, .exposed}
  complete := fun port => by cases port <;> decide

/-- The dependent mode fiber at each partial-routing regression port. -/
abbrev partialRoutingRegressionMode : PartialRoutingRegressionPort → Type
  | .west => Fin 2
  | .east => Bool
  | .exposed => Unit

instance partialRoutingRegressionModeDecidableEq
    (port : PartialRoutingRegressionPort) : DecidableEq (partialRoutingRegressionMode port) := by
  cases port <;> infer_instance

instance partialRoutingRegressionModeFintype
    (port : PartialRoutingRegressionPort) : Fintype (partialRoutingRegressionMode port) := by
  cases port <;> infer_instance

/-- The dependent ambient port family in the partial-routing regression. -/
abbrev partialRoutingRegressionPortFamily : PortModeFamily where
  Port := PartialRoutingRegressionPort
  Mode := partialRoutingRegressionMode

/-- The west-to-east connection selected by the regression family. -/
abbrev partialRoutingRegressionWestEast :
    PortConnection partialRoutingRegressionPortFamily where
  left := .west
  right := .east
  left_ne_right := by decide
  modeEquiv := finTwoEquiv

/-- The sole local connection, indexed by `Unit`. -/
abbrev partialRoutingRegressionConnection
    (_ : Unit) : PortConnection partialRoutingRegressionPortFamily :=
  partialRoutingRegressionWestEast

/-- The one-connection family leaves the third physical port unconnected. -/
abbrev partialRoutingRegressionFamily :
    PortConnectionFamily partialRoutingRegressionPortFamily Unit where
  connection := partialRoutingRegressionConnection
  endpointPort_injective := by decide

/-!

## B. Connected and complement channels

-/

/-- The west zero mode as an ambient physical channel. -/
abbrev partialRoutingRegressionWestZero : partialRoutingRegressionPortFamily.Channel :=
  ⟨.west, 0⟩

/-- The west one mode as an ambient physical channel. -/
abbrev partialRoutingRegressionWestOne : partialRoutingRegressionPortFamily.Channel :=
  ⟨.west, 1⟩

/-- The east false mode as an ambient physical channel. -/
abbrev partialRoutingRegressionEastFalse : partialRoutingRegressionPortFamily.Channel :=
  ⟨.east, false⟩

/-- The east true mode as an ambient physical channel. -/
abbrev partialRoutingRegressionEastTrue : partialRoutingRegressionPortFamily.Channel :=
  ⟨.east, true⟩

/-- The sole ambient channel at the unconnected third port. -/
abbrev partialRoutingRegressionExposed : partialRoutingRegressionPortFamily.Channel :=
  ⟨.exposed, ()⟩

/-- The west zero mode in the connected-channel family. -/
abbrev partialRoutingRegressionConnectedWestZero : partialRoutingRegressionFamily.Channel :=
  ⟨(), Sum.inl 0⟩

/-- The west one mode in the connected-channel family. -/
abbrev partialRoutingRegressionConnectedWestOne : partialRoutingRegressionFamily.Channel :=
  ⟨(), Sum.inl 1⟩

/-- The east false mode in the connected-channel family. -/
abbrev partialRoutingRegressionConnectedEastFalse : partialRoutingRegressionFamily.Channel :=
  ⟨(), Sum.inr false⟩

/-- The east true mode in the connected-channel family. -/
abbrev partialRoutingRegressionConnectedEastTrue : partialRoutingRegressionFamily.Channel :=
  ⟨(), Sum.inr true⟩

/-- The connected west zero mode embeds at its exact ambient physical channel. -/
lemma partialRoutingRegression_channelEmbedding_westZero :
    partialRoutingRegressionFamily.channelEmbedding
        partialRoutingRegressionConnectedWestZero = partialRoutingRegressionWestZero := rfl

/-- The connected east false mode embeds at its exact ambient physical channel. -/
lemma partialRoutingRegression_channelEmbedding_eastFalse :
    partialRoutingRegressionFamily.channelEmbedding
        partialRoutingRegressionConnectedEastFalse = partialRoutingRegressionEastFalse := rfl

/-- The family mate routes west zero to east false. -/
lemma partialRoutingRegression_mate_westZero :
    partialRoutingRegressionFamily.mateEquiv
        partialRoutingRegressionConnectedWestZero =
      partialRoutingRegressionConnectedEastFalse := rfl

/-- The family mate routes east true back to west one. -/
lemma partialRoutingRegression_mate_eastTrue :
    partialRoutingRegressionFamily.mateEquiv
        partialRoutingRegressionConnectedEastTrue =
      partialRoutingRegressionConnectedWestOne := rfl

/-- The lifted incident embedding retains the east false physical channel. -/
lemma partialRoutingRegression_incidentChannelEmbedding_eastFalse :
    partialRoutingRegressionFamily.incidentChannelEmbedding
        (Incident.mk partialRoutingRegressionConnectedEastFalse) =
      Incident.mk partialRoutingRegressionEastFalse := rfl

/-- The lifted outgoing embedding retains the west zero physical channel. -/
lemma partialRoutingRegression_outgoingChannelEmbedding_westZero :
    partialRoutingRegressionFamily.outgoingChannelEmbedding
        (Outgoing.mk partialRoutingRegressionConnectedWestZero) =
      Outgoing.mk partialRoutingRegressionWestZero := rfl

/-- The third-port channel is outside the connected-channel embedding. -/
lemma partialRoutingRegression_exposed_not_mem_range :
    partialRoutingRegressionExposed ∉
      Set.range partialRoutingRegressionFamily.channelEmbedding := by
  rintro ⟨channel, hChannel⟩
  rcases channel with ⟨index, channel⟩
  rcases index with ⟨⟩
  rcases channel with mode | mode
  · have hPort : PartialRoutingRegressionPort.west = .exposed :=
      congrArg Sigma.fst hChannel
    cases hPort
  · have hPort : PartialRoutingRegressionPort.east = .exposed :=
      congrArg Sigma.fst hChannel
    cases hPort

/-!

## C. Exact ambient routing entries

-/

/-- Ambient partial routing from west zero reaches east false with unit gain. -/
lemma partialRoutingRegression_entry_westZero_eastFalse :
    partialRoutingRegressionFamily.partialRouting
        (Incident.mk partialRoutingRegressionEastFalse)
        (Outgoing.mk partialRoutingRegressionWestZero) = 1 := by
  change partialRoutingRegressionFamily.partialRouting
      (Incident.mk (partialRoutingRegressionFamily.channelEmbedding
        (partialRoutingRegressionFamily.mateEquiv
          partialRoutingRegressionConnectedWestZero)))
      (Outgoing.mk (partialRoutingRegressionFamily.channelEmbedding
        partialRoutingRegressionConnectedWestZero)) = 1
  exact partialRoutingRegressionFamily.partialRouting_entry_mate _

/-- Ambient partial routing from east true reaches west one with unit gain. -/
lemma partialRoutingRegression_entry_eastTrue_westOne :
    partialRoutingRegressionFamily.partialRouting
        (Incident.mk partialRoutingRegressionWestOne)
        (Outgoing.mk partialRoutingRegressionEastTrue) = 1 := by
  change partialRoutingRegressionFamily.partialRouting
      (Incident.mk (partialRoutingRegressionFamily.channelEmbedding
        (partialRoutingRegressionFamily.mateEquiv
          partialRoutingRegressionConnectedEastTrue)))
      (Outgoing.mk (partialRoutingRegressionFamily.channelEmbedding
        partialRoutingRegressionConnectedEastTrue)) = 1
  exact partialRoutingRegressionFamily.partialRouting_entry_mate _

/-- A connected mode pair that is not matched has a zero routing entry. -/
lemma partialRoutingRegression_entry_unmatched :
    partialRoutingRegressionFamily.partialRouting
        (Incident.mk partialRoutingRegressionEastTrue)
        (Outgoing.mk partialRoutingRegressionWestZero) = 0 := by
  change partialRoutingRegressionFamily.partialRouting
      (Incident.mk (partialRoutingRegressionFamily.channelEmbedding
        partialRoutingRegressionConnectedEastTrue))
      (Outgoing.mk (partialRoutingRegressionFamily.channelEmbedding
        partialRoutingRegressionConnectedWestZero)) = 0
  rw [partialRoutingRegressionFamily.partialRouting_entry_connected]
  change ModeTransform.idealRouting partialRoutingRegressionFamily.mateEquiv
      (Incident.mk partialRoutingRegressionConnectedEastTrue)
        (Outgoing.mk partialRoutingRegressionConnectedWestZero) = 0
  rw [ModeTransform.idealRouting_entry]
  simp [partialRoutingRegression_mate_westZero]

/-- The complement ambient incident coordinate gives a zero routing row. -/
lemma partialRoutingRegression_entry_exposed_row :
    partialRoutingRegressionFamily.partialRouting
        (Incident.mk partialRoutingRegressionExposed)
        (Outgoing.mk partialRoutingRegressionWestZero) = 0 :=
  partialRoutingRegressionFamily.partialRouting_entry_of_incident_not_mem_range
    partialRoutingRegressionExposed partialRoutingRegression_exposed_not_mem_range _

/-- The complement ambient outgoing coordinate gives a zero routing column. -/
lemma partialRoutingRegression_entry_exposed_column :
    partialRoutingRegressionFamily.partialRouting
        (Incident.mk partialRoutingRegressionEastFalse)
        (Outgoing.mk partialRoutingRegressionExposed) = 0 :=
  partialRoutingRegressionFamily.partialRouting_entry_of_outgoing_not_mem_range
    partialRoutingRegressionExposed partialRoutingRegression_exposed_not_mem_range _

/-- The entry between corresponding endpoint wrappers of the same complement channel is zero. -/
lemma partialRoutingRegression_entry_exposed_same_channel :
    partialRoutingRegressionFamily.partialRouting
        (Incident.mk partialRoutingRegressionExposed)
        (Outgoing.mk partialRoutingRegressionExposed) = 0 :=
  partialRoutingRegressionFamily.partialRouting_entry_of_incident_not_mem_range
    partialRoutingRegressionExposed partialRoutingRegression_exposed_not_mem_range _

/-!

## D. Omitted-coordinate power witness

-/

/-- A unit outgoing amplitude supported only on the complement ambient channel. -/
def partialRoutingRegressionExposedPulse :
    ModeAmplitude (Outgoing partialRoutingRegressionPortFamily.Channel) :=
  PiLp.single 2 (Outgoing.mk partialRoutingRegressionExposed) 1

/-- Restriction to connected outgoing channels maps the complement-coordinate amplitude to zero. -/
lemma partialRoutingRegression_restrict_exposedPulse :
    partialRoutingRegressionExposedPulse.restrictEmbedding
        partialRoutingRegressionFamily.outgoingChannelEmbedding = 0 := by
  apply WithLp.ofLp_injective 2
  funext endpoint
  rcases endpoint with ⟨channel⟩
  rw [ModeAmplitude.restrictEmbedding_apply]
  have hNe : Outgoing.mk (partialRoutingRegressionFamily.channelEmbedding channel) ≠
      Outgoing.mk partialRoutingRegressionExposed := by
    intro hChannel
    apply partialRoutingRegression_exposed_not_mem_range
    exact ⟨channel, congrArg Outgoing.channel hChannel⟩
  simp [partialRoutingRegressionExposedPulse, hNe]

/-- The complement-coordinate amplitude has normalized modal power one. -/
lemma partialRoutingRegression_exposedPulse_power :
    partialRoutingRegressionExposedPulse.power = 1 := by
  simp [ModeAmplitude.power, partialRoutingRegressionExposedPulse]

/-- Exact amplitude action maps the complement-coordinate amplitude to zero. -/
lemma partialRoutingRegression_apply_exposedPulse :
    partialRoutingRegressionFamily.partialRouting.toLinearMap
        partialRoutingRegressionExposedPulse = 0 := by
  rw [partialRoutingRegressionFamily.partialRouting_apply,
    partialRoutingRegression_restrict_exposedPulse]
  simp

/-- The complement-coordinate amplitude has zero output power after routing. -/
lemma partialRoutingRegression_exposedPulse_output_power :
    (partialRoutingRegressionFamily.partialRouting.toLinearMap
        partialRoutingRegressionExposedPulse).power = 0 := by
  rw [partialRoutingRegression_apply_exposedPulse]
  simp [ModeAmplitude.power]

/-- The complement-coordinate amplitude proves strict modal-power decrease under ambient partial
routing. -/
lemma partialRoutingRegression_exposedPulse_strict_power_decrease :
    (partialRoutingRegressionFamily.partialRouting.toLinearMap
        partialRoutingRegressionExposedPulse).power <
      partialRoutingRegressionExposedPulse.power := by
  rw [partialRoutingRegression_exposedPulse_output_power,
    partialRoutingRegression_exposedPulse_power]
  norm_num

/-- Ambient partial routing is not globally power-preserving in the fixture. -/
lemma partialRoutingRegression_not_powerPreserving :
    ¬partialRoutingRegressionFamily.partialRouting.IsPowerPreserving := by
  intro hPower
  exact (ne_of_lt partialRoutingRegression_exposedPulse_strict_power_decrease)
    (hPower partialRoutingRegressionExposedPulse)

/-- Ambient partial routing remains globally passive in normalized modal coordinates. -/
lemma partialRoutingRegression_isPassive :
    partialRoutingRegressionFamily.partialRouting.IsPassive :=
  partialRoutingRegressionFamily.partialRouting_isPassive

/-!

## E. Connected-subspace power

-/

/-- A nonzero connected outgoing amplitude with a genuinely complex value. -/
def partialRoutingRegressionConnectedPulse :
    ModeAmplitude (Outgoing partialRoutingRegressionFamily.Channel) :=
  PiLp.single 2 (Outgoing.mk partialRoutingRegressionConnectedWestZero) (2 + Complex.I)

/-- The connected amplitude has normalized modal power five. -/
lemma partialRoutingRegression_connectedPulse_power :
    partialRoutingRegressionConnectedPulse.power = 5 := by
  simp only [ModeAmplitude.power, partialRoutingRegressionConnectedPulse, PiLp.norm_single]
  rw [Complex.sq_norm]
  norm_num [Complex.normSq]

/-- Ambient partial routing preserves the power of the zero-extended connected amplitude. -/
lemma partialRoutingRegression_connectedPulse_output_power :
    (partialRoutingRegressionFamily.partialRouting.toLinearMap
        ((ModeTransform.zeroExtension
          partialRoutingRegressionFamily.outgoingChannelEmbedding).toLinearMap
            partialRoutingRegressionConnectedPulse)).power = 5 := by
  rw [partialRoutingRegressionFamily.partialRouting_power_zeroExtension,
    partialRoutingRegression_connectedPulse_power]

/-- The connected amplitude reaches its ambient mate with its exact complex value. -/
lemma partialRoutingRegression_connectedPulse_action :
    partialRoutingRegressionFamily.partialRouting.toLinearMap
        ((ModeTransform.zeroExtension
          partialRoutingRegressionFamily.outgoingChannelEmbedding).toLinearMap
            partialRoutingRegressionConnectedPulse)
        (Incident.mk partialRoutingRegressionEastFalse) = 2 + Complex.I := by
  change partialRoutingRegressionFamily.partialRouting.toLinearMap
      ((ModeTransform.zeroExtension
        partialRoutingRegressionFamily.outgoingChannelEmbedding).toLinearMap
          partialRoutingRegressionConnectedPulse)
      (Incident.mk (partialRoutingRegressionFamily.channelEmbedding
        (partialRoutingRegressionFamily.mateEquiv
          partialRoutingRegressionConnectedWestZero))) = 2 + Complex.I
  rw [partialRoutingRegressionFamily.partialRouting_apply_internal]
  change (ModeTransform.zeroExtension
      partialRoutingRegressionFamily.outgoingChannelEmbedding).toLinearMap
        partialRoutingRegressionConnectedPulse
        (partialRoutingRegressionFamily.outgoingChannelEmbedding
          (Outgoing.mk partialRoutingRegressionConnectedWestZero)) = 2 + Complex.I
  rw [ModeTransform.zeroExtension_apply_image]
  simp [partialRoutingRegressionConnectedPulse]

/-!

## F. Cascade-orientation witness

-/

/-- An asymmetric one-entry component probe from west-one incident to west-zero outgoing. -/
def partialRoutingRegressionProbe :
    ModeTransform (Incident partialRoutingRegressionPortFamily.Channel)
      (Outgoing partialRoutingRegressionPortFamily.Channel) :=
  Matrix.single (Outgoing.mk partialRoutingRegressionWestZero)
    (Incident.mk partialRoutingRegressionWestOne) (2 + Complex.I)

/-- The incident-space cascade obtained by routing the probe's outgoing amplitude. -/
def partialRoutingRegressionRoundTrip :
    ModeTransform (Incident partialRoutingRegressionPortFamily.Channel)
      (Incident partialRoutingRegressionPortFamily.Channel) :=
  partialRoutingRegressionFamily.partialRouting * partialRoutingRegressionProbe

/-- The `C * S` order sends the probe coefficient from west-one incident to east-false incident. -/
lemma partialRoutingRegression_roundTrip_forward :
    partialRoutingRegressionRoundTrip
        (Incident.mk partialRoutingRegressionEastFalse)
        (Incident.mk partialRoutingRegressionWestOne) = 2 + Complex.I := by
  rw [partialRoutingRegressionRoundTrip, partialRoutingRegressionProbe,
    Matrix.mul_single_apply_same,
    partialRoutingRegression_entry_westZero_eastFalse]
  simp

/-- Reversing the two distinct incident coordinates gives zero, fixing the cascade orientation. -/
lemma partialRoutingRegression_roundTrip_reverse :
    partialRoutingRegressionRoundTrip
        (Incident.mk partialRoutingRegressionWestOne)
        (Incident.mk partialRoutingRegressionEastFalse) = 0 := by
  rw [partialRoutingRegressionRoundTrip, partialRoutingRegressionProbe,
    Matrix.mul_single_apply_of_ne]
  simp

end

end Optics
