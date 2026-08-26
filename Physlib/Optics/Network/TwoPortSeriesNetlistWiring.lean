/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.TwoPortSeriesNetlistLocal

/-!
# Wiring equations of the canonical two-port series state

## i. Overview

The three-plane aggregate state satisfies the singleton middle connection and exposes exactly its
outer left and right amplitudes. The following reconstruction module proves the converse shape.

## ii. Key results

- `TwoPortSeriesNetlist.aggregateIncident_eq_incidentAssembly`: the middle and input equations.
- `TwoPortSeriesNetlist.externalOutgoingReadout_aggregateOutgoing`: the outer output equation.

## iii. Table of contents

- A. Constructed-state wiring

## iv. References

This typed wiring proof is Physlib-original; no external source is used here.

-/

@[expose] public section

namespace Optics

noncomputable section

universe u

namespace TwoPortSeriesNetlist

variable {left middle right : Type u}

/-!

## A. Constructed-state wiring

-/

/-- The first component's exposed left incident coordinate is supplied by the external input. -/
lemma incidentAssembly_apply_firstLeft
    [Fintype left] [Fintype middle] [Fintype right]
    (first : ScatteringMatrix (left ⊕ middle))
    (second : ScatteringMatrix (middle ⊕ right))
    (outgoing : ModeAmplitude (netlist first second).OutgoingIndex)
    (external : ModeAmplitude (Incident (netlist first second).ExternalChannel))
    (mode : left) :
    (netlist first second).connections.incidentAssembly outgoing external
        (Incident.mk (leftExternalChannel first second mode)) =
      external (Incident.mk (externalChannelEquiv first second (Sum.inl mode))) := by
  exact (netlist first second).connections.incidentAssembly_apply_external outgoing external
    (externalChannelEquiv first second (Sum.inl mode))

/-- The first component's middle incident coordinate is supplied by the second component. -/
lemma incidentAssembly_apply_firstMiddle
    [Fintype left] [Fintype middle] [Fintype right]
    (first : ScatteringMatrix (left ⊕ middle))
    (second : ScatteringMatrix (middle ⊕ right))
    (outgoing : ModeAmplitude (netlist first second).OutgoingIndex)
    (external : ModeAmplitude (Incident (netlist first second).ExternalChannel))
    (mode : middle) :
    (netlist first second).connections.incidentAssembly outgoing external
        (Incident.mk ⟨⟨false, Port.right⟩, mode⟩) =
      outgoing (Outgoing.mk ⟨⟨true, Port.left⟩, mode⟩) := by
  exact (netlist first second).connections.incidentAssembly_apply_connected_channel
    outgoing external ⟨(), Sum.inl mode⟩

/-- The second component's middle incident coordinate is supplied by the first component. -/
lemma incidentAssembly_apply_secondMiddle
    [Fintype left] [Fintype middle] [Fintype right]
    (first : ScatteringMatrix (left ⊕ middle))
    (second : ScatteringMatrix (middle ⊕ right))
    (outgoing : ModeAmplitude (netlist first second).OutgoingIndex)
    (external : ModeAmplitude (Incident (netlist first second).ExternalChannel))
    (mode : middle) :
    (netlist first second).connections.incidentAssembly outgoing external
        (Incident.mk ⟨⟨true, Port.left⟩, mode⟩) =
      outgoing (Outgoing.mk ⟨⟨false, Port.right⟩, mode⟩) := by
  exact (netlist first second).connections.incidentAssembly_apply_connected_channel
    outgoing external ⟨(), Sum.inr mode⟩

/-- The second component's exposed right incident coordinate is supplied by the external input. -/
lemma incidentAssembly_apply_secondRight
    [Fintype left] [Fintype middle] [Fintype right]
    (first : ScatteringMatrix (left ⊕ middle))
    (second : ScatteringMatrix (middle ⊕ right))
    (outgoing : ModeAmplitude (netlist first second).OutgoingIndex)
    (external : ModeAmplitude (Incident (netlist first second).ExternalChannel))
    (mode : right) :
    (netlist first second).connections.incidentAssembly outgoing external
        (Incident.mk (rightExternalChannel first second mode)) =
      external (Incident.mk (externalChannelEquiv first second (Sum.inr mode))) := by
  exact (netlist first second).connections.incidentAssembly_apply_external outgoing external
    (externalChannelEquiv first second (Sum.inr mode))

/-- The aggregate incident state is exactly the singleton middle routing plus the outer input. -/
lemma aggregateIncident_eq_incidentAssembly
    [Fintype left] [Fintype middle] [Fintype right]
    (first : ScatteringMatrix (left ⊕ middle))
    (second : ScatteringMatrix (middle ⊕ right))
    (input : ModeAmplitude (Incident left ⊕ Incident right))
    (output : ModeAmplitude (Outgoing left ⊕ Outgoing right))
    (middleState : BackwardFirstTravellingWaveState middle) :
    let outer := scatteringBackwardFirstLinearEquiv (input, output)
    aggregateIncident first second outer.1 middleState outer.2 =
      (netlist first second).connections.incidentAssembly
        (aggregateOutgoing first second outer.1 middleState outer.2)
        (ModeAmplitude.reindex (externalIncidentEquiv first second).symm input) := by
  dsimp only
  apply WithLp.ofLp_injective 2
  funext index
  rcases index with ⟨⟨⟨component, port⟩, mode⟩⟩
  cases component <;> cases port
  · change left at mode
    change _ = (netlist first second).connections.incidentAssembly _ _
      (Incident.mk (leftExternalChannel first second mode))
    rw [incidentAssembly_apply_firstLeft]
    rfl
  · change middle at mode
    rw [incidentAssembly_apply_firstMiddle]
    rfl
  · change middle at mode
    rw [incidentAssembly_apply_secondMiddle]
    rfl
  · change right at mode
    change _ = (netlist first second).connections.incidentAssembly _ _
      (Incident.mk (rightExternalChannel first second mode))
    rw [incidentAssembly_apply_secondRight]
    rfl

/-- External readout of the aggregate outgoing state is exactly the typed outer output. -/
lemma externalOutgoingReadout_aggregateOutgoing
    [Fintype left] [Fintype middle] [Fintype right]
    (first : ScatteringMatrix (left ⊕ middle))
    (second : ScatteringMatrix (middle ⊕ right))
    (input : ModeAmplitude (Incident left ⊕ Incident right))
    (output : ModeAmplitude (Outgoing left ⊕ Outgoing right))
    (middleState : BackwardFirstTravellingWaveState middle) :
    let outer := scatteringBackwardFirstLinearEquiv (input, output)
    ModeAmplitude.reindex (externalOutgoingEquiv first second).symm output =
      (netlist first second).connections.externalOutgoingReadout.toLinearMap
        (aggregateOutgoing first second outer.1 middleState outer.2) := by
  dsimp only
  rw [(netlist first second).connections.externalOutgoingReadout_apply]
  apply WithLp.ofLp_injective 2
  funext index
  rcases index with ⟨⟨⟨⟨component, port⟩, mode⟩, hExternal⟩⟩
  cases component <;> cases port
  · rfl
  · exact False.elim (hExternal ⟨⟨(), Sum.inl mode⟩, rfl⟩)
  · exact False.elim (hExternal ⟨⟨(), Sum.inr mode⟩, rfl⟩)
  · rfl

end TwoPortSeriesNetlist

end

end Optics
