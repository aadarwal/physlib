/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.TwoPortRedhefferBlocks

/-!
# Redheffer formula realizes relational series composition

## i. Overview

This file proves that the proof-gated Redheffer block formula is exactly the singular-safe series
behavior whenever the named feedback pivot is bijective. The proof solves only the internal
backward-wave equation and checks both component laws; the block formula is not taken as the
definition of composition.

Scope:

The result is fixed-frequency complex-linear algebra. It introduces no commutativity,
reciprocity, passivity, losslessness, convergence, or physical-realization assumption.

## ii. Key results

- `TwoPortScatteringTransform.toBehavior_redhefferBlockFormula`: the block formula realizes the
  relational series behavior.

## iii. Table of contents

- A. Internal-equation equivalence
- B. Behavioral realization

## iv. References

This realization proof is Physlib-original; no external source is used here.

-/

@[expose] public section
namespace Optics
noncomputable section
universe u v w
namespace TwoPortScatteringTransform
variable {ι : Type u} {κ : Type v} {μ : Type w}
/-!
## A. Internal-equation equivalence
-/

private lemma redhefferBlockEquations_iff_internalEquations
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype μ] [DecidableEq μ]
    (first : TwoPortScatteringTransform ι κ)
    (second : TwoPortScatteringTransform κ μ)
    (hFeedback : first.HasBijectiveRedhefferFeedback second)
    (leftBackward : ModeAmplitude (BackwardWave ι))
    (leftForward : ModeAmplitude (ForwardWave ι))
    (rightBackward : ModeAmplitude (BackwardWave μ))
    (rightForward : ModeAmplitude (ForwardWave μ)) :
    (leftBackward =
        ModeTransform.toLinearMap (first.leftReflection + first.rightToLeftTransmission *
          first.redhefferFeedbackInverse second hFeedback *
            second.leftReflection * first.leftToRightTransmission) leftForward +
          ModeTransform.toLinearMap (first.rightToLeftTransmission *
            first.redhefferFeedbackInverse second hFeedback *
              second.rightToLeftTransmission) rightBackward ∧
      rightForward =
        ModeTransform.toLinearMap (second.leftToRightTransmission *
          (first.leftToRightTransmission +
          first.rightReflection * first.redhefferFeedbackInverse second hFeedback *
            second.leftReflection * first.leftToRightTransmission)) leftForward +
          ModeTransform.toLinearMap (second.rightReflection +
            second.leftToRightTransmission *
            first.rightReflection * first.redhefferFeedbackInverse second hFeedback *
              second.rightToLeftTransmission) rightBackward) ↔
      ∃ middle : BackwardFirstTravellingWaveState κ,
        (leftBackward = first.leftReflection.toLinearMap leftForward +
            first.rightToLeftTransmission.toLinearMap middle.restrictInl ∧
          middle.restrictInr = first.leftToRightTransmission.toLinearMap leftForward +
            first.rightReflection.toLinearMap middle.restrictInl) ∧
        (middle.restrictInl = second.leftReflection.toLinearMap middle.restrictInr +
            second.rightToLeftTransmission.toLinearMap rightBackward ∧
          rightForward = second.leftToRightTransmission.toLinearMap middle.restrictInr +
            second.rightReflection.toLinearMap rightBackward) := by
  let inverse := first.redhefferFeedbackInverse second hFeedback
  let source := second.leftReflection.toLinearMap
      (first.leftToRightTransmission.toLinearMap leftForward) +
    second.rightToLeftTransmission.toLinearMap rightBackward
  let backward := inverse.toLinearMap source
  let forward := first.leftToRightTransmission.toLinearMap leftForward +
    first.rightReflection.toLinearMap backward
  constructor
  · rintro ⟨hLeft, hRight⟩
    have hPivot : (first.redhefferFeedbackBlock second).toLinearMap backward = source := by
      exact first.redhefferFeedbackBlock_apply_inverse second hFeedback source
    have hBackward : backward = second.leftReflection.toLinearMap forward +
        second.rightToLeftTransmission.toLinearMap rightBackward := by
      rw [first.redhefferFeedbackBlock_apply second] at hPivot
      rw [sub_eq_iff_eq_add] at hPivot
      calc
        backward = source +
            second.leftReflection.toLinearMap
              (first.rightReflection.toLinearMap backward) := hPivot
        _ = second.leftReflection.toLinearMap forward +
            second.rightToLeftTransmission.toLinearMap rightBackward := by
          simp only [forward, source, map_add]
          abel
    refine ⟨backward.directSum forward, ?_⟩
    simp only [ModeAmplitude.restrictInl_directSum, ModeAmplitude.restrictInr_directSum]
    refine ⟨⟨?_, rfl⟩, ⟨hBackward, ?_⟩⟩
    · rw [hLeft]
      simp only [ModeTransform.toLinearMap_mul_apply, backward, inverse, source, map_add,
        LinearMap.add_apply]
      abel_nf
    · rw [hRight]
      simp only [ModeTransform.toLinearMap_mul_apply, forward, backward, inverse, source,
        map_add, LinearMap.add_apply]
      abel_nf
  · rintro ⟨middle, ⟨hLeft, hForward⟩, ⟨hBackward, hRight⟩⟩
    have hPivot : (first.redhefferFeedbackBlock second).toLinearMap middle.restrictInl =
        source := by
      calc
        (first.redhefferFeedbackBlock second).toLinearMap middle.restrictInl =
            middle.restrictInl - second.leftReflection.toLinearMap
              (first.rightReflection.toLinearMap middle.restrictInl) :=
          first.redhefferFeedbackBlock_apply second middle.restrictInl
        _ = (second.leftReflection.toLinearMap middle.restrictInr +
              second.rightToLeftTransmission.toLinearMap rightBackward) -
            second.leftReflection.toLinearMap
              (first.rightReflection.toLinearMap middle.restrictInl) := by
          rw [hBackward]
        _ = source := by
          rw [hForward]
          simp only [source, map_add]
          abel_nf
    have hInternal : middle.restrictInl = backward := by
      change middle.restrictInl =
        (first.redhefferFeedbackInverse second hFeedback).toLinearMap source
      rw [← first.redhefferFeedbackInverse_apply_block second hFeedback middle.restrictInl]
      exact congrArg
        (first.redhefferFeedbackInverse second hFeedback).toLinearMap hPivot
    constructor
    · rw [hLeft, hInternal]
      simp only [ModeTransform.toLinearMap_mul_apply, backward, inverse, source, map_add,
        LinearMap.add_apply]
      abel_nf
    · rw [hRight, hForward, hInternal]
      simp only [ModeTransform.toLinearMap_mul_apply, backward, inverse, source, map_add,
        LinearMap.add_apply]
      abel_nf
/-!
## B. Behavioral realization
-/

/-- The Redheffer block formula has exactly the relational series behavior after backward-first
regrouping. -/
lemma toBackwardFirstBehavior_redhefferBlockFormula
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype μ] [DecidableEq μ]
    (first : TwoPortScatteringTransform ι κ)
    (second : TwoPortScatteringTransform κ μ)
    (hFeedback : first.HasBijectiveRedhefferFeedback second) :
    (first.redhefferBlockFormula second hFeedback).toBackwardFirstBehavior =
      TwoPortScatteringBehavior.toBackwardFirst
        (first.redhefferSeriesBehavior second) := by
  ext ⟨left, right⟩
  rw [mem_toBackwardFirstBehavior_iff_blockEquations,
    first.mem_toBackwardFirst_redhefferSeriesBehavior_iff second left right,
    first.leftReflection_redhefferBlockFormula second hFeedback,
    first.rightToLeftTransmission_redhefferBlockFormula second hFeedback,
    first.leftToRightTransmission_redhefferBlockFormula second hFeedback,
    first.rightReflection_redhefferBlockFormula second hFeedback]
  exact redhefferBlockEquations_iff_internalEquations first second hFeedback
    left.restrictInl left.restrictInr right.restrictInl right.restrictInr

/-- The proof-gated Redheffer block formula realizes the singular-safe relational series behavior
exactly. -/
lemma toBehavior_redhefferBlockFormula
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype μ] [DecidableEq μ]
    (first : TwoPortScatteringTransform ι κ)
    (second : TwoPortScatteringTransform κ μ)
    (hFeedback : first.HasBijectiveRedhefferFeedback second) :
    (first.redhefferBlockFormula second hFeedback).toBehavior =
      first.redhefferSeriesBehavior second := by
  calc
    (first.redhefferBlockFormula second hFeedback).toBehavior =
        BackwardFirstTwoPortBehavior.toScattering
          (first.redhefferBlockFormula second hFeedback).toBackwardFirstBehavior := by
      rw [toBackwardFirstBehavior,
        TwoPortScatteringBehavior.toScattering_toBackwardFirst]
    _ = BackwardFirstTwoPortBehavior.toScattering
        (TwoPortScatteringBehavior.toBackwardFirst
          (first.redhefferSeriesBehavior second)) := by
      rw [first.toBackwardFirstBehavior_redhefferBlockFormula second hFeedback]
    _ = first.redhefferSeriesBehavior second :=
      TwoPortScatteringBehavior.toScattering_toBackwardFirst _

end TwoPortScatteringTransform
end
end Optics
