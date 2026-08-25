/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.TwoPortRedheffer

/-!
# Remaining Redheffer block identities

## i. Overview

This file completes the named block API for the proof-gated Redheffer formula. The lower blocks
retain the exact noncommutative order forced by the internal forward/backward wave types.

Scope:

These are algebraic identities for the declared backward-wave pivot. They make no commutativity,
reciprocity, passivity, losslessness, or physical-realization claim.

## ii. Key results

- `TwoPortScatteringTransform.leftToRightTransmission_redhefferBlockFormula`.
- `TwoPortScatteringTransform.rightReflection_redhefferBlockFormula`.
- `TwoPortScatteringTransform.redhefferFeedbackBlock_apply`.

## iii. Table of contents

- A. Lower Redheffer blocks
- B. Feedback-block action

## iv. References

This typed block API is Physlib-original; no external source is used here.

-/

@[expose] public section

namespace Optics

noncomputable section

universe u v w

namespace TwoPortScatteringTransform

variable {ι : Type u} {κ : Type v} {μ : Type w}

/-!

## A. Lower Redheffer blocks

-/

/-- The Redheffer left-to-right block is
`Tlr₂ * (Tlr₁ + Rr₁ * P⁻¹ * Rl₂ * Tlr₁)`. -/
lemma leftToRightTransmission_redhefferBlockFormula
    [Fintype κ] [DecidableEq κ]
    (first : TwoPortScatteringTransform ι κ)
    (second : TwoPortScatteringTransform κ μ)
    (hFeedback : first.HasBijectiveRedhefferFeedback second) :
    (first.redhefferBlockFormula second hFeedback).leftToRightTransmission =
      second.leftToRightTransmission * (first.leftToRightTransmission +
        first.rightReflection * first.redhefferFeedbackInverse second hFeedback *
          second.leftReflection * first.leftToRightTransmission) := by
  rw [leftToRightTransmission,
    first.toTravellingWaveCoordinates_redhefferBlockFormula second hFeedback]
  exact Matrix.toBlocks_fromBlocks₂₁ _ _ _ _

/-- The Redheffer right-reflection block is
`Rr₂ + Tlr₂ * Rr₁ * P⁻¹ * Trl₂`. -/
lemma rightReflection_redhefferBlockFormula
    [Fintype κ] [DecidableEq κ]
    (first : TwoPortScatteringTransform ι κ)
    (second : TwoPortScatteringTransform κ μ)
    (hFeedback : first.HasBijectiveRedhefferFeedback second) :
    (first.redhefferBlockFormula second hFeedback).rightReflection =
      second.rightReflection + second.leftToRightTransmission *
        first.rightReflection * first.redhefferFeedbackInverse second hFeedback *
          second.rightToLeftTransmission := by
  rw [rightReflection,
    first.toTravellingWaveCoordinates_redhefferBlockFormula second hFeedback]
  exact Matrix.toBlocks_fromBlocks₂₂ _ _ _ _

/-!

## B. Feedback-block action

-/

/-- The named feedback block acts as the identity minus one internal reflection round trip. -/
lemma redhefferFeedbackBlock_apply
    [Fintype κ] [DecidableEq κ]
    (first : TwoPortScatteringTransform ι κ)
    (second : TwoPortScatteringTransform κ μ)
    (backward : ModeAmplitude (BackwardWave κ)) :
    (first.redhefferFeedbackBlock second).toLinearMap backward =
      backward - second.leftReflection.toLinearMap
        (first.rightReflection.toLinearMap backward) := by
  unfold redhefferFeedbackBlock
  change Matrix.toEuclideanLin
      (1 - second.leftReflection * first.rightReflection) backward = _
  rw [map_sub, Matrix.toLpLin_one, LinearMap.sub_apply, LinearMap.id_apply,
    Matrix.toLpLin_mul_same, LinearMap.comp_apply]

end TwoPortScatteringTransform

end


end Optics
