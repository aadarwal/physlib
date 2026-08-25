/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.TwoPortSeries
public import Physlib.Optics.Network.TwoPortSeriesNetlistReconstruction

/-!
# Typed external behavior of the canonical two-port series netlist

## i. Overview

This file transports the physical component and external channel labels of the canonical
two-device flat netlist back to the typed left/right scattering coordinates used by the
singular-safe Redheffer series relation.

## ii. Key results

- `TwoPortSeriesNetlist.externalBehavior`: the flat netlist behavior in outer scattering labels.
- `TwoPortSeriesNetlist.externalBehavior_eq_redhefferSeriesBehavior`: gate-free agreement with
  relational Redheffer series composition.

## iii. Table of contents

- A. External behavior coordinates

## iv. References

This cross-semantics coordinate layer is Physlib-original; no external source is used here.

-/

@[expose] public section

namespace Optics

noncomputable section

universe u

namespace TwoPortSeriesNetlist

variable {left middle right : Type u}

/-!

## A. External behavior coordinates

-/

/-- The canonical flat-netlist series behavior in typed outer scattering coordinates. -/
def externalBehavior {left middle right : Type u}
    [Fintype left] [Fintype middle] [Fintype right]
    (first : ScatteringMatrix (left ⊕ middle))
    (second : ScatteringMatrix (middle ⊕ right)) : TwoPortScatteringBehavior left right :=
  (netlist first second).behavior.reindex
    (externalIncidentEquiv first second) (externalOutgoingEquiv first second)

/-- The canonical flat-netlist closure equals singular-safe relational Redheffer composition. -/
lemma externalBehavior_eq_redhefferSeriesBehavior
    {left middle right : Type u}
    [Fintype left] [DecidableEq left] [Fintype middle] [DecidableEq middle]
    [Fintype right] [DecidableEq right]
    (first : ScatteringMatrix (left ⊕ middle))
    (second : ScatteringMatrix (middle ⊕ right)) :
    externalBehavior first second =
      first.toTwoPortScatteringTransform.redhefferSeriesBehavior
        second.toTwoPortScatteringTransform := by
  ext state
  rcases state with ⟨input, output⟩
  rw [externalBehavior, LinearBehavior.mem_reindex_iff,
    (netlist first second).mem_behavior_iff_componentBehavior]
  unfold TwoPortScatteringTransform.redhefferSeriesBehavior
  unfold TwoPortScatteringBehavior.redhefferSeries
  rw [BackwardFirstTwoPortBehavior.mem_toScattering_iff,
    LinearBehavior.mem_series_iff]
  simp only [TwoPortScatteringBehavior.mem_toBackwardFirst_iff]
  let outer := scatteringBackwardFirstLinearEquiv (input, output)
  constructor
  · rintro ⟨incident, outgoing, hComponents, hIncident, hOutput⟩
    let shared := middleStateOfOutgoing first second outgoing
    have hShape := eq_aggregateState_of_boundaryEquations first second input output
      incident outgoing hIncident hOutput
    rcases hShape with ⟨hIncidentShape, hOutgoingShape⟩
    rw [hIncidentShape, hOutgoingShape] at hComponents
    exact ⟨shared,
      (aggregateState_mem_componentBehavior_iff first second outer.1 shared outer.2).mp
        hComponents⟩
  · rintro ⟨shared, hFirst, hSecond⟩
    refine ⟨aggregateIncident first second outer.1 shared outer.2,
      aggregateOutgoing first second outer.1 shared outer.2, ?_, ?_, ?_⟩
    · exact (aggregateState_mem_componentBehavior_iff first second outer.1 shared outer.2).mpr
        ⟨hFirst, hSecond⟩
    · exact aggregateIncident_eq_incidentAssembly first second input output shared
    · exact externalOutgoingReadout_aggregateOutgoing first second input output shared

end TwoPortSeriesNetlist

end

end Optics
