/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.TwoPortSeriesNetlistState

/-!
# Local component laws of the canonical two-port series state

## i. Overview

The aggregate three-plane state restricts to the first and second physical component boundaries.
This file identifies those restrictions with the typed scattering-coordinate pairs.

## ii. Key results

- `TwoPortSeriesNetlist.firstBoundary_aggregateState`: the first local boundary coordinates.
- `TwoPortSeriesNetlist.secondBoundary_aggregateState`: the second local boundary coordinates.
- `TwoPortSeriesNetlist.aggregateState_mem_componentBehavior_iff`: both component laws at once.

## iii. Table of contents

- A. Local restrictions
- B. Component-law equivalence

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

## A. Local restrictions

-/

/-- Restricting the aggregate state to the first component recovers its scattering pair. -/
lemma firstBoundary_aggregateState
    [Fintype left] [Fintype middle]
    (first : ScatteringMatrix (left ⊕ middle))
    (second : ScatteringMatrix (middle ⊕ right))
    (leftState : BackwardFirstTravellingWaveState left)
    (middleState : BackwardFirstTravellingWaveState middle)
    (rightState : BackwardFirstTravellingWaveState right) :
    ((aggregateIncident first second leftState middleState rightState).restrictEmbedding
        (Incident.relabelEmbedding
          ((netlist first second).components.componentChannelEmbedding false)),
      (aggregateOutgoing first second leftState middleState rightState).restrictEmbedding
        (Outgoing.relabelEmbedding
          ((netlist first second).components.componentChannelEmbedding false))) =
      (ModeAmplitude.reindex (incidentChannelEquiv left middle)
          (scatteringBackwardFirstLinearEquiv.symm (leftState, middleState)).1,
        ModeAmplitude.reindex (outgoingChannelEquiv left middle)
          (scatteringBackwardFirstLinearEquiv.symm (leftState, middleState)).2) := by
  apply Prod.ext
  · apply WithLp.ofLp_injective 2
    funext index
    rcases index with ⟨⟨port, mode⟩⟩
    cases port <;> rfl
  · apply WithLp.ofLp_injective 2
    funext index
    rcases index with ⟨⟨port, mode⟩⟩
    cases port <;> rfl

/-- Restricting the aggregate state to the second component recovers its scattering pair. -/
lemma secondBoundary_aggregateState
    [Fintype middle] [Fintype right]
    (first : ScatteringMatrix (left ⊕ middle))
    (second : ScatteringMatrix (middle ⊕ right))
    (leftState : BackwardFirstTravellingWaveState left)
    (middleState : BackwardFirstTravellingWaveState middle)
    (rightState : BackwardFirstTravellingWaveState right) :
    ((aggregateIncident first second leftState middleState rightState).restrictEmbedding
        (Incident.relabelEmbedding
          ((netlist first second).components.componentChannelEmbedding true)),
      (aggregateOutgoing first second leftState middleState rightState).restrictEmbedding
        (Outgoing.relabelEmbedding
          ((netlist first second).components.componentChannelEmbedding true))) =
      (ModeAmplitude.reindex (incidentChannelEquiv middle right)
          (scatteringBackwardFirstLinearEquiv.symm (middleState, rightState)).1,
        ModeAmplitude.reindex (outgoingChannelEquiv middle right)
          (scatteringBackwardFirstLinearEquiv.symm (middleState, rightState)).2) := by
  apply Prod.ext
  · apply WithLp.ofLp_injective 2
    funext index
    rcases index with ⟨⟨port, mode⟩⟩
    cases port <;> rfl
  · apply WithLp.ofLp_injective 2
    funext index
    rcases index with ⟨⟨port, mode⟩⟩
    cases port <;> rfl

/-!

## B. Component-law equivalence

-/

/-- The aggregate three-plane state satisfies the component graph exactly when its two adjacent
state pairs satisfy the corresponding typed two-port scattering graphs. -/
lemma aggregateState_mem_componentBehavior_iff
    [Fintype left] [DecidableEq left] [Fintype middle] [DecidableEq middle]
    [Fintype right] [DecidableEq right]
    (first : ScatteringMatrix (left ⊕ middle))
    (second : ScatteringMatrix (middle ⊕ right))
    (leftState : BackwardFirstTravellingWaveState left)
    (middleState : BackwardFirstTravellingWaveState middle)
    (rightState : BackwardFirstTravellingWaveState right) :
    (aggregateIncident first second leftState middleState rightState,
        aggregateOutgoing first second leftState middleState rightState) ∈
        (netlist first second).componentBehavior ↔
      scatteringBackwardFirstLinearEquiv.symm (leftState, middleState) ∈
          first.toTwoPortScatteringTransform.toBehavior ∧
        scatteringBackwardFirstLinearEquiv.symm (middleState, rightState) ∈
          second.toTwoPortScatteringTransform.toBehavior := by
  rw [(netlist first second).mem_componentBehavior_iff_forall_component]
  constructor
  · intro hComponents
    constructor
    · have hFirst := hComponents false
      rw [firstBoundary_aggregateState] at hFirst
      change _ ∈ (physicalScattering first).toOrientedModeTransform.toBehavior at hFirst
      rw [physicalScattering_toOrientedModeTransform,
        ModeTransform.toBehavior_reindex, LinearBehavior.mem_reindex_iff] at hFirst
      simpa only [ModeAmplitude.reindex_symm_reindex] using hFirst
    · have hSecond := hComponents true
      rw [secondBoundary_aggregateState] at hSecond
      change _ ∈ (physicalScattering second).toOrientedModeTransform.toBehavior at hSecond
      rw [physicalScattering_toOrientedModeTransform,
        ModeTransform.toBehavior_reindex, LinearBehavior.mem_reindex_iff] at hSecond
      simpa only [ModeAmplitude.reindex_symm_reindex] using hSecond
  · rintro ⟨hFirst, hSecond⟩ component
    cases component
    · rw [firstBoundary_aggregateState]
      change _ ∈ (physicalScattering first).toOrientedModeTransform.toBehavior
      rw [physicalScattering_toOrientedModeTransform,
        ModeTransform.toBehavior_reindex, LinearBehavior.mem_reindex_iff]
      simpa only [ModeAmplitude.reindex_symm_reindex] using hFirst
    · rw [secondBoundary_aggregateState]
      change _ ∈ (physicalScattering second).toOrientedModeTransform.toBehavior
      rw [physicalScattering_toOrientedModeTransform,
        ModeTransform.toBehavior_reindex, LinearBehavior.mem_reindex_iff]
      simpa only [ModeAmplitude.reindex_symm_reindex] using hSecond

end TwoPortSeriesNetlist

end

end Optics
