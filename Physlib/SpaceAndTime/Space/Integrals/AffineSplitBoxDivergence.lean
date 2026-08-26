/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.SpaceAndTime.Space.Integrals.AffineBoxLocalDivergence

/-!
# Divergence identities on two interface-split affine boxes

## i. Overview

This file applies the local affine-box divergence theorem separately below and above a shared
carrier face. The two ambient vector fields may be independent. Their carrier values are retained
as an explicit positive-minus-negative face-flux jump.

This is neutral calculus. It does not identify the carrier jump with a sheet charge, assert
continuity across the carrier, construct either one-sided extension, state a Maxwell equation, or
take a shrinking-pillbox limit.

## ii. Key results

- `AffineSplitBoxDivergenceRegularity`: local regularity on both closed half-boxes.
- `affineSplitBoxOuterFlux_eq_bulkDivergence_add_carrierJump`: the outer flux is the sum of the
  two bulk divergence integrals and the retained carrier jump.

## iii. Table of contents

- A. Split-box terms and regularity
- B. Two-half divergence identity

## iv. References

This is neutral calculus infrastructure for the E4b finite-sheet pillbox construction.
-/

@[expose] public section

open Matrix MeasureTheory
open scoped Interval

namespace Space

noncomputable section

/-!
## A. Split-box terms and regularity
-/

/-- Local divergence regularity for independent fields on the negative and positive half-boxes.

The first two coordinate intervals are `[-radius, radius]`. The third-coordinate intervals are
`[-halfThickness, 0]` and `[0, halfThickness]`. -/
structure AffineSplitBoxDivergenceRegularity
    (negativeField positiveField : Space → EuclideanSpace ℝ (Fin 3))
    (center first second third : Space) (radius halfThickness : ℝ)
    (negativeExceptionalSet positiveExceptionalSet : Set (Fin 3 → ℝ)) : Prop where
  /-- Local regularity of the negative-side extension on the closed negative half-box. -/
  negative : AffineBoxDivergenceRegularity negativeField center first second third
    (-radius) (-radius) (-halfThickness) radius radius 0 negativeExceptionalSet
  /-- Local regularity of the positive-side extension on the closed positive half-box. -/
  positive : AffineBoxDivergenceRegularity positiveField center first second third
    (-radius) (-radius) 0 radius radius halfThickness positiveExceptionalSet

/-- The sum of the two signed affine-box divergence integrals. -/
def affineSplitBoxBulkDivergence
    (negativeField positiveField : Space → EuclideanSpace ℝ (Fin 3))
    (center first second third : Space) (radius halfThickness : ℝ) : ℝ :=
  (∫ u in -radius..radius, ∫ v in -radius..radius, ∫ w in -halfThickness..0,
      (∇ ⬝ negativeField) (affineBoxPoint center first second third u v w) *
        inner ℝ (basis.repr first) (basis.repr second ⨯ₑ₃ basis.repr third)) +
    ∫ u in -radius..radius, ∫ v in -radius..radius, ∫ w in 0..halfThickness,
      (∇ ⬝ positiveField) (affineBoxPoint center first second third u v w) *
        inner ℝ (basis.repr first) (basis.repr second ⨯ₑ₃ basis.repr third)

/-- The outward flux through the four lateral faces of the split box. Each cross-interface face
is split into its negative and positive halves. -/
def affineSplitBoxLateralFlux
    (negativeField positiveField : Space → EuclideanSpace ℝ (Fin 3))
    (center first second third : Space) (radius halfThickness : ℝ) : ℝ :=
  (((∫ v in -radius..radius, ∫ w in -halfThickness..0,
          inner ℝ (negativeField
            (affineBoxPoint center first second third radius v w))
            (basis.repr second ⨯ₑ₃ basis.repr third)) -
      ∫ v in -radius..radius, ∫ w in -halfThickness..0,
          inner ℝ (negativeField
            (affineBoxPoint center first second third (-radius) v w))
            (basis.repr second ⨯ₑ₃ basis.repr third)) +
    ((∫ v in -radius..radius, ∫ w in 0..halfThickness,
          inner ℝ (positiveField
            (affineBoxPoint center first second third radius v w))
            (basis.repr second ⨯ₑ₃ basis.repr third)) -
      ∫ v in -radius..radius, ∫ w in 0..halfThickness,
          inner ℝ (positiveField
            (affineBoxPoint center first second third (-radius) v w))
            (basis.repr second ⨯ₑ₃ basis.repr third))) +
    (((∫ u in -radius..radius, ∫ w in -halfThickness..0,
          inner ℝ (negativeField
            (affineBoxPoint center first second third u radius w))
            (basis.repr third ⨯ₑ₃ basis.repr first)) -
      ∫ u in -radius..radius, ∫ w in -halfThickness..0,
          inner ℝ (negativeField
            (affineBoxPoint center first second third u (-radius) w))
            (basis.repr third ⨯ₑ₃ basis.repr first)) +
    ((∫ u in -radius..radius, ∫ w in 0..halfThickness,
          inner ℝ (positiveField
            (affineBoxPoint center first second third u radius w))
            (basis.repr third ⨯ₑ₃ basis.repr first)) -
      ∫ u in -radius..radius, ∫ w in 0..halfThickness,
          inner ℝ (positiveField
            (affineBoxPoint center first second third u (-radius) w))
            (basis.repr third ⨯ₑ₃ basis.repr first)))

/-- The positive top-face flux minus the negative bottom-face flux. -/
def affineSplitBoxPrincipalFlux
    (negativeField positiveField : Space → EuclideanSpace ℝ (Fin 3))
    (center first second third : Space) (radius halfThickness : ℝ) : ℝ :=
  (∫ u in -radius..radius, ∫ v in -radius..radius,
      inner ℝ (positiveField
        (affineBoxPoint center first second third u v halfThickness))
        (basis.repr first ⨯ₑ₃ basis.repr second)) -
    ∫ u in -radius..radius, ∫ v in -radius..radius,
      inner ℝ (negativeField
        (affineBoxPoint center first second third u v (-halfThickness)))
        (basis.repr first ⨯ₑ₃ basis.repr second)

/-- The complete outward flux through the split box, excluding its shared carrier face. -/
def affineSplitBoxOuterFlux
    (negativeField positiveField : Space → EuclideanSpace ℝ (Fin 3))
    (center first second third : Space) (radius halfThickness : ℝ) : ℝ :=
  affineSplitBoxPrincipalFlux negativeField positiveField
      center first second third radius halfThickness +
    affineSplitBoxLateralFlux negativeField positiveField
      center first second third radius halfThickness

/-- The positive-minus-negative flux jump retained on the shared carrier face. -/
def affineSplitBoxCarrierJump
    (negativeField positiveField : Space → EuclideanSpace ℝ (Fin 3))
    (center first second third : Space) (radius : ℝ) : ℝ :=
  (∫ u in -radius..radius, ∫ v in -radius..radius,
      inner ℝ (positiveField (affineBoxPoint center first second third u v 0))
        (basis.repr first ⨯ₑ₃ basis.repr second)) -
    ∫ u in -radius..radius, ∫ v in -radius..radius,
      inner ℝ (negativeField (affineBoxPoint center first second third u v 0))
        (basis.repr first ⨯ₑ₃ basis.repr second)

/-!
## B. Two-half divergence identity
-/

/-- The split box's outer flux equals its two bulk divergence integrals plus the retained
positive-minus-negative carrier-face jump. -/
lemma affineSplitBoxOuterFlux_eq_bulkDivergence_add_carrierJump
    (negativeField positiveField : Space → EuclideanSpace ℝ (Fin 3))
    (center first second third : Space) (radius halfThickness : ℝ)
    (hradius : 0 ≤ radius) (hhalfThickness : 0 ≤ halfThickness)
    (negativeExceptionalSet positiveExceptionalSet : Set (Fin 3 → ℝ))
    (regularity : AffineSplitBoxDivergenceRegularity negativeField positiveField
      center first second third radius halfThickness
      negativeExceptionalSet positiveExceptionalSet) :
    affineSplitBoxOuterFlux negativeField positiveField
        center first second third radius halfThickness =
      affineSplitBoxBulkDivergence negativeField positiveField
          center first second third radius halfThickness +
        affineSplitBoxCarrierJump negativeField positiveField
          center first second third radius := by
  have hNegative := integral3_div_affineBox_of_localRegularity
    negativeField center first second third
    (-radius) (-radius) (-halfThickness) radius radius 0
    (neg_le_self hradius) (neg_le_self hradius)
    (neg_nonpos.mpr hhalfThickness) negativeExceptionalSet regularity.negative
  have hPositive := integral3_div_affineBox_of_localRegularity
    positiveField center first second third
    (-radius) (-radius) 0 radius radius halfThickness
    (neg_le_self hradius) (neg_le_self hradius)
    hhalfThickness positiveExceptionalSet regularity.positive
  unfold affineSplitBoxOuterFlux affineSplitBoxPrincipalFlux
    affineSplitBoxLateralFlux affineSplitBoxBulkDivergence
    affineSplitBoxCarrierJump
  rw [hNegative, hPositive]
  ring

end
end Space
