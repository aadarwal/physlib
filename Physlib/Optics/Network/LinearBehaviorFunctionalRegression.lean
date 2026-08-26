/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.LinearBehaviorRegression

/-!
# Regression tests for functional linear optical behaviors

## i. Overview

These examples test the proof boundary between an implicit linear behavior and its extracted
linear map. Singular graph behaviors remain functional, while relations that are not total or are
multivalued fail the appropriate predicates. Exact complex gain examples and a nonsymmetric
cascade then check that proof-required extraction preserves graph membership and behavioral series
order.

## ii. Key results

## iii. Table of contents

- A. Predicate boundaries
- B. Concrete graph extraction
- C. Composition and extraction order

## iv. References

The tests concern existence and uniqueness of algebraic outputs only. Being functional does not
imply being injective or invertible, passivity, causality, or physical realizability.

-/

@[expose] public section

namespace Optics

noncomputable section

/-!

## A. Predicate boundaries

-/

/-- The singular zero-transform graph is functional although its linear map is not injective. -/
lemma linearBehaviorFunctionalRegression_zeroTransform_functional_not_injective :
    linearBehaviorRegressionZeroTransform.toBehavior.IsFunctional ∧
      ¬Function.Injective linearBehaviorRegressionZeroTransform.toLinearMap :=
  ⟨ModeTransform.toBehavior_isFunctional _,
    linearBehaviorRegressionZeroTransform_not_injective⟩

/-- The free-output behavior is not total because its nonzero test input is in no pair. -/
lemma linearBehaviorFunctionalRegression_freeOutput_not_isTotal :
    ¬linearBehaviorRegressionFreeOutput.IsTotal := by
  intro hTotal
  rcases hTotal linearBehaviorRegressionUnitPulse with ⟨output, hMember⟩
  have hInput : linearBehaviorRegressionUnitPulse = 0 := by
    simpa [linearBehaviorRegressionFreeOutput] using hMember.1
  exact linearBehaviorRegressionUnitPulse_ne_zero hInput

/-- The free-output behavior is not single-valued because zero input permits two distinct
outputs. -/
lemma linearBehaviorFunctionalRegression_freeOutput_not_isSingleValued :
    ¬linearBehaviorRegressionFreeOutput.IsSingleValued := by
  intro hSingleValued
  have hOutputs : (0 : ModeAmplitude Unit) = linearBehaviorRegressionUnitPulse :=
    hSingleValued linearBehaviorRegressionFreeOutput_zero_zero
      linearBehaviorRegressionFreeOutput_zero_pulse
  exact linearBehaviorRegressionUnitPulse_ne_zero hOutputs.symm

/-- The top behavior is total. -/
lemma linearBehaviorFunctionalRegression_top_isTotal :
    (⊤ : LinearBehavior Unit Unit).IsTotal := by
  intro input
  exact ⟨0, Submodule.mem_top⟩

/-- The top behavior is not single-valued. -/
lemma linearBehaviorFunctionalRegression_top_not_isSingleValued :
    ¬(⊤ : LinearBehavior Unit Unit).IsSingleValued := by
  intro hSingleValued
  have hOutputs : (0 : ModeAmplitude Unit) = linearBehaviorRegressionUnitPulse :=
    hSingleValued (input := 0) (output₁ := 0)
      (output₂ := linearBehaviorRegressionUnitPulse) Submodule.mem_top Submodule.mem_top
  exact linearBehaviorRegressionUnitPulse_ne_zero hOutputs.symm

/-- The bottom behavior is single-valued. -/
lemma linearBehaviorFunctionalRegression_bottom_isSingleValued :
    (⊥ : LinearBehavior Unit Unit).IsSingleValued := by
  intro input output₁ output₂ hOutput₁ hOutput₂
  rw [Submodule.mem_bot] at hOutput₁ hOutput₂
  exact congrArg Prod.snd (hOutput₁.trans hOutput₂.symm)

/-- The bottom behavior is not total. -/
lemma linearBehaviorFunctionalRegression_bottom_not_isTotal :
    ¬(⊥ : LinearBehavior Unit Unit).IsTotal := by
  intro hTotal
  rcases hTotal linearBehaviorRegressionUnitPulse with ⟨output, hMember⟩
  rw [Submodule.mem_bot] at hMember
  apply linearBehaviorRegressionUnitPulse_ne_zero
  simpa using congrArg Prod.fst hMember

/-!

## B. Concrete graph extraction

-/

/-- The complex singleton input used to test graph extraction. -/
def linearBehaviorFunctionalRegressionGainInput : ModeAmplitude Unit :=
  linearBehaviorRegressionUnitAmplitude (3 - Complex.I)

/-- The exact output of gain `2 + I` on the extraction input. -/
def linearBehaviorFunctionalRegressionGainOutput : ModeAmplitude Unit :=
  linearBehaviorRegressionUnitAmplitude (7 + Complex.I)

/-- The exact gain input/output pair is in the original transform behavior. -/
lemma linearBehaviorFunctionalRegression_gain_mem :
    (linearBehaviorFunctionalRegressionGainInput,
        linearBehaviorFunctionalRegressionGainOutput) ∈
      (linearBehaviorRegressionGain (2 + Complex.I)).toBehavior := by
  rw [ModeTransform.mem_toBehavior_iff_toLinearMap]
  calc
    linearBehaviorFunctionalRegressionGainOutput =
        linearBehaviorRegressionUnitAmplitude
          ((2 + Complex.I) * (3 - Complex.I)) := by
      unfold linearBehaviorFunctionalRegressionGainOutput
      congr 1
      ring_nf
      rw [Complex.I_sq]
      ring
    _ = (linearBehaviorRegressionGain (2 + Complex.I)).toLinearMap
        linearBehaviorFunctionalRegressionGainInput := by
      symm
      exact linearBehaviorRegressionGain_action (2 + Complex.I) (3 - Complex.I)

/-- Proof-required extraction preserves the independently checked complex gain action. -/
lemma linearBehaviorFunctionalRegression_gain_toLinearMap_action :
    ((linearBehaviorRegressionGain (2 + Complex.I)).toBehavior.toLinearMap
        (ModeTransform.toBehavior_isFunctional _))
      linearBehaviorFunctionalRegressionGainInput =
        linearBehaviorFunctionalRegressionGainOutput := by
  exact ((LinearBehavior.mem_iff_eq_toLinearMap _ _ _ _).mp
    linearBehaviorFunctionalRegression_gain_mem).symm

/-!

## C. Composition and extraction order

-/

/-- The nonsymmetric regression cascade is functional by series closure. -/
lemma linearBehaviorFunctionalRegression_series_isFunctional :
    (linearBehaviorRegressionFirst.toBehavior.series
      linearBehaviorRegressionSecond.toBehavior).IsFunctional :=
  (ModeTransform.toBehavior_isFunctional linearBehaviorRegressionFirst).series
    (ModeTransform.toBehavior_isFunctional linearBehaviorRegressionSecond)

/-- Extracting the relational cascade returns its exact independently checked forward output. -/
lemma linearBehaviorFunctionalRegression_series_toLinearMap_action :
    ((linearBehaviorRegressionFirst.toBehavior.series
        linearBehaviorRegressionSecond.toBehavior).toLinearMap
      linearBehaviorFunctionalRegression_series_isFunctional)
        linearBehaviorRegressionInput = linearBehaviorRegressionOutput := by
  exact ((LinearBehavior.mem_iff_eq_toLinearMap _ _ _ _).mp
    linearBehaviorRegression_series_mem).symm

/-- Extracting the cascade agrees with applying the second transform after the first. -/
lemma linearBehaviorFunctionalRegression_series_toLinearMap_eq_comp :
    (linearBehaviorRegressionFirst.toBehavior.series
        linearBehaviorRegressionSecond.toBehavior).toLinearMap
      linearBehaviorFunctionalRegression_series_isFunctional =
        linearBehaviorRegressionSecond.toLinearMap.comp
          linearBehaviorRegressionFirst.toLinearMap := by
  calc
    _ = (linearBehaviorRegressionSecond.toBehavior.toLinearMap
          (ModeTransform.toBehavior_isFunctional _)).comp
        (linearBehaviorRegressionFirst.toBehavior.toLinearMap
          (ModeTransform.toBehavior_isFunctional _)) :=
      LinearBehavior.toLinearMap_series _ _ _ _
    _ = linearBehaviorRegressionSecond.toLinearMap.comp
        linearBehaviorRegressionFirst.toLinearMap := by
      rw [ModeTransform.toLinearMap_toBehavior, ModeTransform.toLinearMap_toBehavior]

/-- The extracted forward cascade rejects the distinct reverse-order output. -/
lemma linearBehaviorFunctionalRegression_series_action_ne_reverseOutput :
    ((linearBehaviorRegressionFirst.toBehavior.series
        linearBehaviorRegressionSecond.toBehavior).toLinearMap
      linearBehaviorFunctionalRegression_series_isFunctional)
        linearBehaviorRegressionInput ≠ linearBehaviorRegressionReverseOutput := by
  rw [linearBehaviorFunctionalRegression_series_toLinearMap_action]
  exact linearBehaviorRegression_output_ne_reverseOutput

/-- Re-embedding the extracted cascade recovers the entire relational series behavior. -/
lemma linearBehaviorFunctionalRegression_series_roundTrip :
    LinearBehavior.ofLinearMap
        ((linearBehaviorRegressionFirst.toBehavior.series
            linearBehaviorRegressionSecond.toBehavior).toLinearMap
          linearBehaviorFunctionalRegression_series_isFunctional) =
      linearBehaviorRegressionFirst.toBehavior.series
        linearBehaviorRegressionSecond.toBehavior :=
  LinearBehavior.ofLinearMap_toLinearMap _ _

/-- The independent two-gain parallel regression behavior is functional by parallel closure. -/
lemma linearBehaviorFunctionalRegression_parallel_isFunctional :
    ((linearBehaviorRegressionGain 2).toBehavior.parallel
      (linearBehaviorRegressionGain 3).toBehavior).IsFunctional :=
  (ModeTransform.toBehavior_isFunctional _).parallel
    (ModeTransform.toBehavior_isFunctional _)

/-- Extracting the parallel behavior returns the independently checked two-branch output. -/
lemma linearBehaviorFunctionalRegression_parallel_toLinearMap_action :
    (((linearBehaviorRegressionGain 2).toBehavior.parallel
        (linearBehaviorRegressionGain 3).toBehavior).toLinearMap
      linearBehaviorFunctionalRegression_parallel_isFunctional)
        linearBehaviorRegressionParallelInput =
          linearBehaviorRegressionParallelOutput := by
  exact ((LinearBehavior.mem_iff_eq_toLinearMap _ _ _ _).mp
    linearBehaviorRegression_parallel_mem).symm

/-- The extracted parallel behavior rejects the independently false right-branch output. -/
lemma linearBehaviorFunctionalRegression_parallel_action_ne_wrongOutput :
    (((linearBehaviorRegressionGain 2).toBehavior.parallel
        (linearBehaviorRegressionGain 3).toBehavior).toLinearMap
      linearBehaviorFunctionalRegression_parallel_isFunctional)
        linearBehaviorRegressionParallelInput ≠
          linearBehaviorRegressionParallelWrongOutput := by
  rw [linearBehaviorFunctionalRegression_parallel_toLinearMap_action]
  exact linearBehaviorRegression_parallelOutput_ne_wrongOutput

end

end Optics
