/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.TwoPortSeriesNetlistWiring

/-!
# Reconstruction of a canonical two-port series state

## i. Overview

The middle-routing and external-readout equations determine the coordinate presentation of every
complete state, without asserting existence or uniqueness of that state.

## ii. Key results

- `TwoPortSeriesNetlist.eq_aggregateState_of_boundaryEquations`: every displayed complete state
  has the canonical three-reference-plane form.

## iii. Table of contents

- A. Boundary coordinates
- B. Complete-state reconstruction

## iv. References

This typed reconstruction is Physlib-original; no external source is used here.

-/

@[expose] public section

namespace Optics

noncomputable section

universe u

namespace TwoPortSeriesNetlist

variable {left middle right : Type u}

/-!

## A. Boundary coordinates

-/

/-- The incident assembly equation fixes the exposed left incident amplitude. -/
lemma incident_apply_left_of_assembly_eq
    [Fintype left] [Fintype middle] [Fintype right]
    (first : ScatteringMatrix (left ⊕ middle))
    (second : ScatteringMatrix (middle ⊕ right))
    (input : ModeAmplitude (Incident left ⊕ Incident right))
    (incident : ModeAmplitude (netlist first second).IncidentIndex)
    (outgoing : ModeAmplitude (netlist first second).OutgoingIndex)
    (hIncident : incident = (netlist first second).connections.incidentAssembly outgoing
      (ModeAmplitude.reindex (externalIncidentEquiv first second).symm input))
    (mode : left) :
    incident (Incident.mk (leftExternalChannel first second mode)) =
      input (Sum.inl (Incident.mk mode)) := by
  have hApply := congrArg
    (fun amplitude => amplitude (Incident.mk (leftExternalChannel first second mode))) hIncident
  rw [incidentAssembly_apply_firstLeft] at hApply
  exact hApply

/-- The incident assembly equation fixes the exposed right incident amplitude. -/
lemma incident_apply_right_of_assembly_eq
    [Fintype left] [Fintype middle] [Fintype right]
    (first : ScatteringMatrix (left ⊕ middle))
    (second : ScatteringMatrix (middle ⊕ right))
    (input : ModeAmplitude (Incident left ⊕ Incident right))
    (incident : ModeAmplitude (netlist first second).IncidentIndex)
    (outgoing : ModeAmplitude (netlist first second).OutgoingIndex)
    (hIncident : incident = (netlist first second).connections.incidentAssembly outgoing
      (ModeAmplitude.reindex (externalIncidentEquiv first second).symm input))
    (mode : right) :
    incident (Incident.mk (rightExternalChannel first second mode)) =
      input (Sum.inr (Incident.mk mode)) := by
  have hApply := congrArg
    (fun amplitude => amplitude (Incident.mk (rightExternalChannel first second mode))) hIncident
  rw [incidentAssembly_apply_secondRight] at hApply
  exact hApply

/-- The external readout equation fixes the exposed left outgoing amplitude. -/
lemma outgoing_apply_left_of_readout_eq
    [Fintype left] [Fintype middle] [Fintype right]
    (first : ScatteringMatrix (left ⊕ middle))
    (second : ScatteringMatrix (middle ⊕ right))
    (output : ModeAmplitude (Outgoing left ⊕ Outgoing right))
    (outgoing : ModeAmplitude (netlist first second).OutgoingIndex)
    (hOutput : ModeAmplitude.reindex (externalOutgoingEquiv first second).symm output =
      (netlist first second).connections.externalOutgoingReadout.toLinearMap outgoing)
    (mode : left) :
    outgoing (Outgoing.mk (leftExternalChannel first second mode)) =
      output (Sum.inl (Outgoing.mk mode)) := by
  rw [(netlist first second).connections.externalOutgoingReadout_apply] at hOutput
  have hApply := congrArg
    (fun amplitude => amplitude
      (Outgoing.mk (externalChannelEquiv first second (Sum.inl mode)))) hOutput
  exact hApply.symm

/-- The external readout equation fixes the exposed right outgoing amplitude. -/
lemma outgoing_apply_right_of_readout_eq
    [Fintype left] [Fintype middle] [Fintype right]
    (first : ScatteringMatrix (left ⊕ middle))
    (second : ScatteringMatrix (middle ⊕ right))
    (output : ModeAmplitude (Outgoing left ⊕ Outgoing right))
    (outgoing : ModeAmplitude (netlist first second).OutgoingIndex)
    (hOutput : ModeAmplitude.reindex (externalOutgoingEquiv first second).symm output =
      (netlist first second).connections.externalOutgoingReadout.toLinearMap outgoing)
    (mode : right) :
    outgoing (Outgoing.mk (rightExternalChannel first second mode)) =
      output (Sum.inr (Outgoing.mk mode)) := by
  rw [(netlist first second).connections.externalOutgoingReadout_apply] at hOutput
  have hApply := congrArg
    (fun amplitude => amplitude
      (Outgoing.mk (externalChannelEquiv first second (Sum.inr mode)))) hOutput
  exact hApply.symm

/-!

## B. Complete-state reconstruction

-/

/-- Every complete state satisfying the middle-routing and external-readout equations is the
aggregate state of its outer scattering data and its two internal outgoing amplitudes. -/
lemma eq_aggregateState_of_boundaryEquations
    [Fintype left] [Fintype middle] [Fintype right]
    (first : ScatteringMatrix (left ⊕ middle))
    (second : ScatteringMatrix (middle ⊕ right))
    (input : ModeAmplitude (Incident left ⊕ Incident right))
    (output : ModeAmplitude (Outgoing left ⊕ Outgoing right))
    (incident : ModeAmplitude (netlist first second).IncidentIndex)
    (outgoing : ModeAmplitude (netlist first second).OutgoingIndex)
    (hIncident : incident = (netlist first second).connections.incidentAssembly outgoing
      (ModeAmplitude.reindex (externalIncidentEquiv first second).symm input))
    (hOutput : ModeAmplitude.reindex (externalOutgoingEquiv first second).symm output =
      (netlist first second).connections.externalOutgoingReadout.toLinearMap outgoing) :
    let outer := scatteringBackwardFirstLinearEquiv (input, output)
    let shared := middleStateOfOutgoing first second outgoing
    incident = aggregateIncident first second outer.1 shared outer.2 ∧
      outgoing = aggregateOutgoing first second outer.1 shared outer.2 := by
  dsimp only
  constructor
  · apply WithLp.ofLp_injective 2
    funext index
    rcases index with ⟨⟨⟨component, port⟩, mode⟩⟩
    cases component <;> cases port
    · change left at mode
      exact incident_apply_left_of_assembly_eq first second input incident outgoing hIncident mode
    · change middle at mode
      have hApply := congrArg
        (fun amplitude => amplitude (Incident.mk ⟨⟨false, Port.right⟩, mode⟩)) hIncident
      rw [incidentAssembly_apply_firstMiddle] at hApply
      exact hApply
    · change middle at mode
      have hApply := congrArg
        (fun amplitude => amplitude (Incident.mk ⟨⟨true, Port.left⟩, mode⟩)) hIncident
      rw [incidentAssembly_apply_secondMiddle] at hApply
      exact hApply
    · change right at mode
      exact incident_apply_right_of_assembly_eq first second input incident outgoing hIncident mode
  · apply WithLp.ofLp_injective 2
    funext index
    rcases index with ⟨⟨⟨component, port⟩, mode⟩⟩
    cases component <;> cases port
    · change left at mode
      exact outgoing_apply_left_of_readout_eq first second output outgoing hOutput mode
    · rfl
    · rfl
    · change right at mode
      exact outgoing_apply_right_of_readout_eq first second output outgoing hOutput mode

end TwoPortSeriesNetlist

end

end Optics
