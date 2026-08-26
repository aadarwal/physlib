/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.TwoPortRedhefferRegression
public import Physlib.Optics.Network.TwoPortSeriesNetlistBehavior

/-!
# Singular regression for the chosen canonical two-port series netlist

## i. Overview

A reflective unit-gain internal loop fails the Redheffer matrix-extraction gate but retains two
distinct complete and external relational solutions for zero incident waves.

## ii. Key results

- `TwoPortSeriesNetlistSingularRegression.not_hasBijectiveFeedback`: the pivot gate fails.
- `TwoPortSeriesNetlistSingularRegression.not_isWellPosed`: the FlatNetlist gate fails too.
- `TwoPortSeriesNetlistSingularRegression.externalBehavior_outputs_nonunique`: the chosen
  FlatNetlist builder nevertheless retains both solutions.

## iii. Table of contents

- A. Reflective singular fixtures
- B. Gate-free netlist solutions

## iv. References

This singular cross-semantics fixture is Physlib-original; no external source is used here.

-/

@[expose] public section

namespace Optics

noncomputable section

namespace TwoPortSeriesNetlistSingularRegression

open TwoPortSeriesRegression

/-!

## A. Reflective singular fixtures

-/

/-- A scalar scattering matrix with left-then-right entries `(a, b; c, d)`. -/
def scalarScattering (a b c d : ℂ) : ScatteringMatrix (Unit ⊕ Unit) where
  toModeTransform
    | Sum.inl _, Sum.inl _ => a
    | Sum.inl _, Sum.inr _ => b
    | Sum.inr _, Sum.inl _ => c
    | Sum.inr _, Sum.inr _ => d

/-- The first reflective fixture exposes the loop amplitude at its left output. -/
def first : ScatteringMatrix (Unit ⊕ Unit) := scalarScattering 0 1 0 1

/-- The second reflective fixture closes the unit-gain loop. -/
def second : ScatteringMatrix (Unit ⊕ Unit) := scalarScattering 1 1 0 0

/-- The first physical matrix has the independently tested singular typed adapter. -/
lemma first_toTwoPortScatteringTransform :
    first.toTwoPortScatteringTransform = TwoPortSeriesRegression.singularFirst := by
  ext output input
  rcases output with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;>
    rcases input with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;> rfl

/-- The second physical matrix has the independently tested singular typed adapter. -/
lemma second_toTwoPortScatteringTransform :
    second.toTwoPortScatteringTransform = TwoPortSeriesRegression.singularSecond := by
  ext output input
  rcases output with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;>
    rcases input with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;> rfl

/-- The chosen physical fixture fails the Redheffer matrix-extraction gate. -/
lemma not_hasBijectiveFeedback :
    ¬first.toTwoPortScatteringTransform.HasBijectiveRedhefferFeedback
      second.toTwoPortScatteringTransform := by
  rw [first_toTwoPortScatteringTransform, second_toTwoPortScatteringTransform]
  exact TwoPortRedhefferRegression.singular_not_hasBijectiveFeedback

/-- The zero-input singular fixture's outer outgoing amplitude at loop value `value`. -/
def outerOutput (value : ℂ) : ModeAmplitude (Outgoing Unit ⊕ Outgoing Unit) :=
  (scatteringBackwardFirstLinearEquiv.symm (scalarState value 0, scalarState 0 0)).2

/-- The zero and unit loop values produce distinct typed outer outputs. -/
lemma outerOutput_zero_ne_one : outerOutput 0 ≠ outerOutput 1 := by
  intro hEqual
  have hCoordinate := congrArg
    (fun output => output (Sum.inl (Outgoing.mk ()))) hEqual
  norm_num [outerOutput, scalarState, scalarAmplitude] at hCoordinate

/-!

## B. Gate-free netlist solutions

-/

/-- Every loop amplitude yields a raw FlatNetlist solution with zero external incident waves. -/
lemma flatNetlist_member (value : ℂ) :
    (0, ModeAmplitude.reindex
      (TwoPortSeriesNetlist.externalOutgoingEquiv first second).symm (outerOutput value)) ∈
      (TwoPortSeriesNetlist.netlist first second).behavior := by
  have hRelational := singular_relational_member value
  rw [TwoPortScatteringTransform.mem_toBackwardFirst_redhefferSeriesBehavior_iff]
    at hRelational
  rcases hRelational with ⟨shared, hFirst, hSecond⟩
  have hFirstBehavior :
      (scalarState value 0, shared) ∈
        TwoPortSeriesRegression.singularFirst.toBackwardFirstBehavior :=
    (TwoPortSeriesRegression.singularFirst.mem_toBackwardFirstBehavior_iff_blockEquations
      (scalarState value 0) shared).mpr hFirst
  have hSecondBehavior :
      (shared, scalarState 0 0) ∈
        TwoPortSeriesRegression.singularSecond.toBackwardFirstBehavior :=
    (TwoPortSeriesRegression.singularSecond.mem_toBackwardFirstBehavior_iff_blockEquations
      shared (scalarState 0 0)).mpr hSecond
  have hFirst' : scatteringBackwardFirstLinearEquiv.symm (scalarState value 0, shared) ∈
      first.toTwoPortScatteringTransform.toBehavior := by
    rw [first_toTwoPortScatteringTransform]
    exact (TwoPortScatteringBehavior.mem_toBackwardFirst_iff _ _ _).mp hFirstBehavior
  have hSecond' : scatteringBackwardFirstLinearEquiv.symm (shared, scalarState 0 0) ∈
      second.toTwoPortScatteringTransform.toBehavior := by
    rw [second_toTwoPortScatteringTransform]
    exact (TwoPortScatteringBehavior.mem_toBackwardFirst_iff _ _ _).mp hSecondBehavior
  have hExternalInput :
      (scatteringBackwardFirstLinearEquiv.symm
        (scalarState value 0, scalarState 0 0)).1 = 0 := by
    apply WithLp.ofLp_injective 2
    funext index
    rcases index with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;> rfl
  have hExternalPair :
      (0, outerOutput value) = scatteringBackwardFirstLinearEquiv.symm
        (scalarState value 0, scalarState 0 0) := by
    apply Prod.ext
    · exact hExternalInput.symm
    · rfl
  rw [(TwoPortSeriesNetlist.netlist first second).mem_behavior_iff_componentBehavior]
  refine ⟨TwoPortSeriesNetlist.aggregateIncident first second
      (scalarState value 0) shared (scalarState 0 0),
    TwoPortSeriesNetlist.aggregateOutgoing first second
      (scalarState value 0) shared (scalarState 0 0), ?_, ?_, ?_⟩
  · exact (TwoPortSeriesNetlist.aggregateState_mem_componentBehavior_iff first second
      (scalarState value 0) shared (scalarState 0 0)).mpr ⟨hFirst', hSecond'⟩
  · simpa only [hExternalPair, LinearEquiv.apply_symm_apply, map_zero] using
      TwoPortSeriesNetlist.aggregateIncident_eq_incidentAssembly first second
        (0 : ModeAmplitude (Incident Unit ⊕ Incident Unit)) (outerOutput value) shared
  · simpa only [hExternalPair, LinearEquiv.apply_symm_apply] using
      TwoPortSeriesNetlist.externalOutgoingReadout_aggregateOutgoing first second
        (0 : ModeAmplitude (Incident Unit ⊕ Incident Unit)) (outerOutput value) shared

/-- The chosen FlatNetlist builder is not well posed at the reflective unit loop. -/
lemma not_isWellPosed :
    ¬(TwoPortSeriesNetlist.netlist first second).IsWellPosed := by
  intro hWellPosed
  have hOutputsEqual :=
    ((TwoPortSeriesNetlist.netlist first second).behavior_isFunctional hWellPosed).2
      (flatNetlist_member 0) (flatNetlist_member 1)
  exact outerOutput_zero_ne_one
    ((ModeAmplitude.reindex
      (TwoPortSeriesNetlist.externalOutgoingEquiv first second).symm).injective hOutputsEqual)

/-- The typed external behavior retains two distinct outputs at the singular pivot. -/
lemma externalBehavior_outputs_nonunique :
    (0, outerOutput 0) ∈ TwoPortSeriesNetlist.externalBehavior first second ∧
      (0, outerOutput 1) ∈ TwoPortSeriesNetlist.externalBehavior first second ∧
      outerOutput 0 ≠ outerOutput 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [TwoPortSeriesNetlist.externalBehavior, LinearBehavior.mem_reindex_iff]
    simpa only [map_zero] using flatNetlist_member 0
  · rw [TwoPortSeriesNetlist.externalBehavior, LinearBehavior.mem_reindex_iff]
    simpa only [map_zero] using flatNetlist_member 1
  · exact outerOutput_zero_ne_one

end TwoPortSeriesNetlistSingularRegression

end

end Optics
