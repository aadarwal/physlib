/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.TwoPortSeries

/-!
# Proof-gated Redheffer block formula

## i. Overview

For two typed scattering transforms connected in series, the internal backward wave satisfies a
feedback equation with operator `1 - Rl₂ * Rr₁`. This file names that exact typed pivot,
requires its bijectivity explicitly, and states the resulting noncommutative four-block Redheffer
formula.

Scope and convention:

Rows and columns of each travelling-wave scattering transform are ordered left then right. The
chosen pivot acts on the internal backward-wave family. Its inverse is proof-gated; no total
matrix inverse, norm-contraction criterion, reciprocity, or commutativity assumption is used.
Bijectivity is a sufficient gate for extracting the external matrix; no converse or minimality
claim about external functionality is made.

## ii. Key results

- `TwoPortScatteringTransform.redhefferFeedbackBlock`: `1 - Rl₂ * Rr₁`.
- `TwoPortScatteringTransform.HasBijectiveRedhefferFeedback`: the exact matrix-extraction gate.
- `TwoPortScatteringTransform.redhefferFeedbackInverse`: the proof-gated pivot inverse.
- `TwoPortScatteringTransform.redhefferBlockFormula`: the typed four-block formula.
- The four named block lemmas expose the exact noncommutative product order.

## iii. Table of contents

- A. Internal feedback pivot
- B. Four-block Redheffer formula

## iv. References

This typed derivation is Physlib-original; no external source is used here.

-/

@[expose] public section

namespace Optics

noncomputable section

universe u v w

namespace TwoPortScatteringTransform

variable {ι : Type u} {κ : Type v} {μ : Type w}

/-!

## A. Internal feedback pivot

-/

/-- The internal backward-wave feedback operator for `first` followed by `second`.

With `Rr₁ : bκ → fκ` and `Rl₂ : fκ → bκ`, the internal equation is
`(1 - Rl₂ * Rr₁) x = Rl₂ * Tlr₁ * aL + Trl₂ * aR`.
-/
def redhefferFeedbackBlock [Fintype κ] [DecidableEq κ]
    (first : TwoPortScatteringTransform ι κ)
    (second : TwoPortScatteringTransform κ μ) :
    ModeTransform (BackwardWave κ) (BackwardWave κ) :=
  1 - second.leftReflection * first.rightReflection

/-- The explicit sufficient solvability gate used to extract the Redheffer scattering matrix from
the singular-safe series behavior. No converse from external functionality is asserted. -/
def HasBijectiveRedhefferFeedback [Fintype κ] [DecidableEq κ]
    (first : TwoPortScatteringTransform ι κ)
    (second : TwoPortScatteringTransform κ μ) : Prop :=
  Function.Bijective (first.redhefferFeedbackBlock second).toLinearMap

/-- The proof-gated inverse of the internal backward-wave feedback operator. -/
noncomputable def redhefferFeedbackInverse
    [Fintype κ] [DecidableEq κ]
    (first : TwoPortScatteringTransform ι κ)
    (second : TwoPortScatteringTransform κ μ)
    (hFeedback : first.HasBijectiveRedhefferFeedback second) :
    ModeTransform (BackwardWave κ) (BackwardWave κ) :=
  (first.redhefferFeedbackBlock second).inverseOfBijective hFeedback

/-- The feedback block applied after its proof-gated inverse is the identity. -/
lemma redhefferFeedbackBlock_apply_inverse
    [Fintype κ] [DecidableEq κ]
    (first : TwoPortScatteringTransform ι κ)
    (second : TwoPortScatteringTransform κ μ)
    (hFeedback : first.HasBijectiveRedhefferFeedback second)
    (amplitude : ModeAmplitude (BackwardWave κ)) :
    (first.redhefferFeedbackBlock second).toLinearMap
        ((first.redhefferFeedbackInverse second hFeedback).toLinearMap amplitude) =
      amplitude :=
  (first.redhefferFeedbackBlock second).apply_inverseOfBijective hFeedback amplitude

/-- The proof-gated inverse applied after the feedback block is the identity. -/
lemma redhefferFeedbackInverse_apply_block
    [Fintype κ] [DecidableEq κ]
    (first : TwoPortScatteringTransform ι κ)
    (second : TwoPortScatteringTransform κ μ)
    (hFeedback : first.HasBijectiveRedhefferFeedback second)
    (amplitude : ModeAmplitude (BackwardWave κ)) :
    (first.redhefferFeedbackInverse second hFeedback).toLinearMap
        ((first.redhefferFeedbackBlock second).toLinearMap amplitude) = amplitude :=
  (first.redhefferFeedbackBlock second).inverseOfBijective_apply hFeedback amplitude

/-!

## B. Four-block Redheffer formula

-/

/-- The Redheffer formula in direction-typed travelling-wave coordinates.

The result orders external inputs as `(aL, aR)` and outputs as `(bL, bR)`. Every product is kept
in its noncommutative, type-correct order.
-/
noncomputable def travellingWaveRedhefferBlockFormula
    [Fintype κ] [DecidableEq κ]
    (first : TwoPortScatteringTransform ι κ)
    (second : TwoPortScatteringTransform κ μ)
    (hFeedback : first.HasBijectiveRedhefferFeedback second) :
    ModeTransform (ForwardWave ι ⊕ BackwardWave μ)
      (BackwardWave ι ⊕ ForwardWave μ) :=
  let inverse := first.redhefferFeedbackInverse second hFeedback
  Matrix.fromBlocks
    (first.leftReflection + first.rightToLeftTransmission * inverse *
      second.leftReflection * first.leftToRightTransmission)
    (first.rightToLeftTransmission * inverse * second.rightToLeftTransmission)
    (second.leftToRightTransmission * (first.leftToRightTransmission +
      first.rightReflection * inverse * second.leftReflection *
        first.leftToRightTransmission))
    (second.rightReflection + second.leftToRightTransmission * first.rightReflection *
      inverse * second.rightToLeftTransmission)

/-- The four-block Redheffer formula relabeled as a typed external scattering transform. -/
noncomputable def redhefferBlockFormula
    [Fintype κ] [DecidableEq κ]
    (first : TwoPortScatteringTransform ι κ)
    (second : TwoPortScatteringTransform κ μ)
    (hFeedback : first.HasBijectiveRedhefferFeedback second) :
    TwoPortScatteringTransform ι μ :=
  (first.travellingWaveRedhefferBlockFormula second hFeedback).reindex
    incidentTravellingWaveEquiv.symm outgoingTravellingWaveEquiv.symm

/-- Returning the typed Redheffer formula to travelling-wave coordinates recovers its exact
four-block matrix. -/
lemma toTravellingWaveCoordinates_redhefferBlockFormula
    [Fintype κ] [DecidableEq κ]
    (first : TwoPortScatteringTransform ι κ)
    (second : TwoPortScatteringTransform κ μ)
    (hFeedback : first.HasBijectiveRedhefferFeedback second) :
    (first.redhefferBlockFormula second hFeedback).toTravellingWaveCoordinates =
      first.travellingWaveRedhefferBlockFormula second hFeedback :=
  ModeTransform.reindex_reindex_symm incidentTravellingWaveEquiv
    outgoingTravellingWaveEquiv
    (first.travellingWaveRedhefferBlockFormula second hFeedback)

/-- The Redheffer left-reflection block is
`Rl₁ + Trl₁ * P⁻¹ * Rl₂ * Tlr₁`. -/
lemma leftReflection_redhefferBlockFormula
    [Fintype κ] [DecidableEq κ]
    (first : TwoPortScatteringTransform ι κ)
    (second : TwoPortScatteringTransform κ μ)
    (hFeedback : first.HasBijectiveRedhefferFeedback second) :
    (first.redhefferBlockFormula second hFeedback).leftReflection =
      first.leftReflection + first.rightToLeftTransmission *
        first.redhefferFeedbackInverse second hFeedback *
          second.leftReflection * first.leftToRightTransmission := by
  rw [leftReflection, first.toTravellingWaveCoordinates_redhefferBlockFormula second hFeedback]
  exact Matrix.toBlocks_fromBlocks₁₁ _ _ _ _

/-- The Redheffer right-to-left block is `Trl₁ * P⁻¹ * Trl₂`. -/
lemma rightToLeftTransmission_redhefferBlockFormula
    [Fintype κ] [DecidableEq κ]
    (first : TwoPortScatteringTransform ι κ)
    (second : TwoPortScatteringTransform κ μ)
    (hFeedback : first.HasBijectiveRedhefferFeedback second) :
    (first.redhefferBlockFormula second hFeedback).rightToLeftTransmission =
      first.rightToLeftTransmission *
        first.redhefferFeedbackInverse second hFeedback *
          second.rightToLeftTransmission := by
  rw [rightToLeftTransmission,
    first.toTravellingWaveCoordinates_redhefferBlockFormula second hFeedback]
  exact Matrix.toBlocks_fromBlocks₁₂ _ _ _ _

end TwoPortScatteringTransform

end

end Optics
