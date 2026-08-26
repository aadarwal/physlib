/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.TwoPortSeriesNetlistExternal

/-!
# State coordinates of the canonical two-port series netlist

## i. Overview

This file identifies a left travelling-wave state, a shared middle state, and a right state with
the aggregate incident and outgoing amplitudes of the canonical two-device flat netlist.

## ii. Key results

- `TwoPortSeriesNetlist.aggregateIncident`: the four physical incident-port amplitudes.
- `TwoPortSeriesNetlist.aggregateOutgoing`: the four physical outgoing-port amplitudes.
- `TwoPortSeriesNetlist.externalIncidentEquiv`: the exposed incident-coordinate identification.
- `TwoPortSeriesNetlist.middleStateOfOutgoing`: the shared state recovered from internal outputs.

## iii. Table of contents

- A. Local endpoint coordinates
- B. Aggregate state coordinates

## iv. References

This typed coordinate layer is Physlib-original; no external source is used here.

-/

@[expose] public section

namespace Optics

noncomputable section

universe u

namespace TwoPortSeriesNetlist

variable {left middle right : Type u}

/-!

## A. Local endpoint coordinates

-/

/-- Split algebraic incident channels identified with one component's physical incident ends. -/
def incidentChannelEquiv (left right : Type u) :
    (Incident left ⊕ Incident right) ≃ Incident (portFamily left right).Channel :=
  ((Incident.splitSumEquiv :
      Incident (left ⊕ right) ≃ Incident left ⊕ Incident right).symm).trans
    (Incident.relabelEquiv (channelEquiv left right))

/-- Split algebraic outgoing channels identified with one component's physical outgoing ends. -/
def outgoingChannelEquiv (left right : Type u) :
    (Outgoing left ⊕ Outgoing right) ≃ Outgoing (portFamily left right).Channel :=
  ((Outgoing.splitSumEquiv :
      Outgoing (left ⊕ right) ≃ Outgoing left ⊕ Outgoing right).symm).trans
    (Outgoing.relabelEquiv (channelEquiv left right))

/-- Physical scattering is the typed two-port adapter under the pinned endpoint labels. -/
lemma physicalScattering_toOrientedModeTransform
    (scattering : ScatteringMatrix (left ⊕ right)) :
    (physicalScattering scattering).toOrientedModeTransform =
      scattering.toTwoPortScatteringTransform.reindex
        (incidentChannelEquiv left right) (outgoingChannelEquiv left right) := by
  ext output input
  rcases output with ⟨⟨outputPort, outputMode⟩⟩
  rcases input with ⟨⟨inputPort, inputMode⟩⟩
  cases outputPort <;> cases inputPort <;> rfl

/-- Netlist external incident ends identified with split outer incident channels. -/
def externalIncidentEquiv (first : ScatteringMatrix (left ⊕ middle))
    (second : ScatteringMatrix (middle ⊕ right)) :
    Incident (netlist first second).ExternalChannel ≃ Incident left ⊕ Incident right :=
  (Incident.relabelEquiv (externalChannelEquiv first second).symm).trans
    Incident.splitSumEquiv

/-- Netlist external outgoing ends identified with split outer outgoing channels. -/
def externalOutgoingEquiv (first : ScatteringMatrix (left ⊕ middle))
    (second : ScatteringMatrix (middle ⊕ right)) :
    Outgoing (netlist first second).ExternalChannel ≃ Outgoing left ⊕ Outgoing right :=
  (Outgoing.relabelEquiv (externalChannelEquiv first second).symm).trans
    Outgoing.splitSumEquiv

/-!

## B. Aggregate state coordinates

-/

/-- Aggregate incident amplitudes determined by the three reference-plane states. -/
def aggregateIncident (first : ScatteringMatrix (left ⊕ middle))
    (second : ScatteringMatrix (middle ⊕ right))
    (leftState : BackwardFirstTravellingWaveState left)
    (middleState : BackwardFirstTravellingWaveState middle)
    (rightState : BackwardFirstTravellingWaveState right) :
    ModeAmplitude (netlist first second).IncidentIndex :=
  WithLp.toLp 2 fun
    | ⟨⟨⟨false, Port.left⟩, mode⟩⟩ =>
        leftState (Sum.inr (ForwardWave.mk mode))
    | ⟨⟨⟨false, Port.right⟩, mode⟩⟩ =>
        middleState (Sum.inl (BackwardWave.mk mode))
    | ⟨⟨⟨true, Port.left⟩, mode⟩⟩ =>
        middleState (Sum.inr (ForwardWave.mk mode))
    | ⟨⟨⟨true, Port.right⟩, mode⟩⟩ =>
        rightState (Sum.inl (BackwardWave.mk mode))

/-- Aggregate outgoing amplitudes determined by the three reference-plane states. -/
def aggregateOutgoing (first : ScatteringMatrix (left ⊕ middle))
    (second : ScatteringMatrix (middle ⊕ right))
    (leftState : BackwardFirstTravellingWaveState left)
    (middleState : BackwardFirstTravellingWaveState middle)
    (rightState : BackwardFirstTravellingWaveState right) :
    ModeAmplitude (netlist first second).OutgoingIndex :=
  WithLp.toLp 2 fun
    | ⟨⟨⟨false, Port.left⟩, mode⟩⟩ =>
        leftState (Sum.inl (BackwardWave.mk mode))
    | ⟨⟨⟨false, Port.right⟩, mode⟩⟩ =>
        middleState (Sum.inr (ForwardWave.mk mode))
    | ⟨⟨⟨true, Port.left⟩, mode⟩⟩ =>
        middleState (Sum.inl (BackwardWave.mk mode))
    | ⟨⟨⟨true, Port.right⟩, mode⟩⟩ =>
        rightState (Sum.inr (ForwardWave.mk mode))

/-- Recover the shared backward-first state from the two internal outgoing port amplitudes. -/
def middleStateOfOutgoing (first : ScatteringMatrix (left ⊕ middle))
    (second : ScatteringMatrix (middle ⊕ right))
    (outgoing : ModeAmplitude (netlist first second).OutgoingIndex) :
    BackwardFirstTravellingWaveState middle :=
  WithLp.toLp 2 fun
    | Sum.inl backward =>
        outgoing (Outgoing.mk ⟨⟨true, Port.left⟩, backward.channel⟩)
    | Sum.inr forward =>
        outgoing (Outgoing.mk ⟨⟨false, Port.right⟩, forward.channel⟩)

end TwoPortSeriesNetlist

end

end Optics
