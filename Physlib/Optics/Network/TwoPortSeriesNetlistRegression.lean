/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Components.ReflectionlessTwoPort
public import Physlib.Optics.Network.TwoPortSeriesNetlistBehavior
public import Physlib.Optics.Network.TwoPortSeriesRegression

/-!
# Regression tests for the canonical two-port series netlist

## i. Overview

Two actual `ReflectionlessTwoPort` matrices with unequal directional gains are joined by the
canonical physical middle-port connection. The displayed FlatNetlist state is constructed from
the independently hand-expanded relational fixture, without using the X-01 equality theorem.

## ii. Key results

- `TwoPortSeriesNetlistRegression.flatNetlist_member`: raw N5 channel equations accept the same
  two-direction cascade state as relational series composition.
- `TwoPortSeriesNetlistRegression.externalBehavior_member`: the state is visible at the typed
  external boundary.

## iii. Table of contents

- A. Reflectionless component fixtures
- B. Independent flat-netlist state

## iv. References

This cross-semantics fixture is Physlib-original; no external source is used here.

-/

@[expose] public section

namespace Optics

noncomputable section

namespace TwoPortSeriesNetlistRegression

open TwoPortSeriesRegression

/-!

## A. Reflectionless component fixtures

-/

/-- A scalar transform on the singleton mode family. -/
def scalarTransform (gain : ℂ) : ModeTransform Unit Unit := fun _ _ => gain

/-- The first reflectionless component has right-to-left gain two and left-to-right gain three. -/
def first : ScatteringMatrix (Unit ⊕ Unit) :=
  ReflectionlessTwoPort.scattering (scalarTransform 2) (scalarTransform 3)

/-- The second reflectionless component has right-to-left gain five and left-to-right gain seven. -/
def second : ScatteringMatrix (Unit ⊕ Unit) :=
  ReflectionlessTwoPort.scattering (scalarTransform 5) (scalarTransform 7)

/-- The first physical matrix's typed adapter is the independently tested scalar fixture. -/
lemma first_toTwoPortScatteringTransform :
    first.toTwoPortScatteringTransform = reflectionFreeFirst := by
  ext output input
  rcases output with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;>
    rcases input with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;> rfl

/-- The second physical matrix's typed adapter is the independently tested scalar fixture. -/
lemma second_toTwoPortScatteringTransform :
    second.toTwoPortScatteringTransform = reflectionFreeSecond := by
  ext output input
  rcases output with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;>
    rcases input with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;> rfl

/-- The hand-expanded fixture's outer incident amplitude in scattering coordinates. -/
def outerInput : ModeAmplitude (Incident Unit ⊕ Incident Unit) :=
  (scatteringBackwardFirstLinearEquiv.symm (scalarState 130 11, scalarState 13 231)).1

/-- The hand-expanded fixture's outer outgoing amplitude in scattering coordinates. -/
def outerOutput : ModeAmplitude (Outgoing Unit ⊕ Outgoing Unit) :=
  (scatteringBackwardFirstLinearEquiv.symm (scalarState 130 11, scalarState 13 231)).2

/-!

## B. Independent flat-netlist state

-/

/-- The raw canonical FlatNetlist equations accept the hand-expanded reflectionless cascade.

The proof obtains the shared state from the independently expanded relational regression and then
checks the component, routing, injection, and readout equations directly. It does not rewrite by
`externalBehavior_eq_redhefferSeriesBehavior`.
-/
lemma flatNetlist_member :
    (ModeAmplitude.reindex
        (TwoPortSeriesNetlist.externalIncidentEquiv first second).symm outerInput,
      ModeAmplitude.reindex
        (TwoPortSeriesNetlist.externalOutgoingEquiv first second).symm outerOutput) ∈
      (TwoPortSeriesNetlist.netlist first second).behavior := by
  have hRelational := reflectionFree_relational_member
  rw [reflectionFreeFirst.mem_toBackwardFirst_redhefferSeriesBehavior_iff
    reflectionFreeSecond] at hRelational
  rcases hRelational with ⟨shared, hFirst, hSecond⟩
  have hFirstBehavior :
      (scalarState 130 11, shared) ∈ reflectionFreeFirst.toBackwardFirstBehavior :=
    (reflectionFreeFirst.mem_toBackwardFirstBehavior_iff_blockEquations
      (scalarState 130 11) shared).mpr hFirst
  have hSecondBehavior :
      (shared, scalarState 13 231) ∈ reflectionFreeSecond.toBackwardFirstBehavior :=
    (reflectionFreeSecond.mem_toBackwardFirstBehavior_iff_blockEquations
      shared (scalarState 13 231)).mpr hSecond
  have hFirst' :
      scatteringBackwardFirstLinearEquiv.symm (scalarState 130 11, shared) ∈
        first.toTwoPortScatteringTransform.toBehavior := by
    rw [first_toTwoPortScatteringTransform]
    exact (TwoPortScatteringBehavior.mem_toBackwardFirst_iff _ _ _).mp hFirstBehavior
  have hSecond' :
      scatteringBackwardFirstLinearEquiv.symm (shared, scalarState 13 231) ∈
        second.toTwoPortScatteringTransform.toBehavior := by
    rw [second_toTwoPortScatteringTransform]
    exact (TwoPortScatteringBehavior.mem_toBackwardFirst_iff _ _ _).mp hSecondBehavior
  rw [(TwoPortSeriesNetlist.netlist first second).mem_behavior_iff_componentBehavior]
  refine ⟨TwoPortSeriesNetlist.aggregateIncident first second
      (scalarState 130 11) shared (scalarState 13 231),
    TwoPortSeriesNetlist.aggregateOutgoing first second
      (scalarState 130 11) shared (scalarState 13 231), ?_, ?_, ?_⟩
  · exact (TwoPortSeriesNetlist.aggregateState_mem_componentBehavior_iff first second
      (scalarState 130 11) shared (scalarState 13 231)).mpr ⟨hFirst', hSecond'⟩
  · exact TwoPortSeriesNetlist.aggregateIncident_eq_incidentAssembly
      first second outerInput outerOutput shared
  · exact TwoPortSeriesNetlist.externalOutgoingReadout_aggregateOutgoing
      first second outerInput outerOutput shared

/-- The same independently constructed state belongs to the typed external behavior. -/
lemma externalBehavior_member :
    (outerInput, outerOutput) ∈ TwoPortSeriesNetlist.externalBehavior first second := by
  rw [TwoPortSeriesNetlist.externalBehavior, LinearBehavior.mem_reindex_iff]
  exact flatNetlist_member

end TwoPortSeriesNetlistRegression

end

end Optics
