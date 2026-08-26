/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.SpaceAndTime.Space.Integrals.PlanarRectangleLocalStokes

/-!
# Stokes identities on two interface-split rectangles

## i. Overview

This file applies the local affine-rectangle Stokes theorem separately below and above a shared
carrier. The two ambient fields may be independent. Their carrier values are retained, rather
than cancelled, as an explicit line-integral jump.

The result is neutral calculus. It does not identify the carrier jump with a surface current,
assert continuity across the carrier, or construct either ambient extension from a one-sided
field. Those are explicit downstream electromagnetic premises.

## ii. Key results

- `PlanarSplitRectangleStokesRegularity`: local regularity on both closed half-rectangles.
- `planarSplitRectangleFlux`: the oriented flux of independent vector densities over the two
  half-rectangles.
- `planarSplitRectangleOuterCirculation_eq_curlFlux_add_carrierJump`: the outer circulation is
  the sum of the two bulk curl fluxes and the retained carrier jump.

## iii. Table of contents

- A. Split-rectangle terms and regularity
- B. Two-half Stokes identity

## iv. References

This is neutral calculus infrastructure for the E4b finite-sheet construction.
-/

@[expose] public section

open Matrix MeasureTheory
open scoped Interval

namespace Space

noncomputable section

/-! ## A. Split-rectangle terms and regularity -/

/-- Local Stokes regularity for independent fields on the negative and positive half-rectangles.
The common first-coordinate interval is `[-radius, radius]`; the second-coordinate intervals are
`[-halfThickness, 0]` and `[0, halfThickness]`. -/
structure PlanarSplitRectangleStokesRegularity
    (negativeField positiveField : Space → EuclideanSpace ℝ (Fin 3))
    (center first second : Space) (radius halfThickness : ℝ) : Prop where
  /-- Local regularity of the negative-side extension on the closed negative half-rectangle. -/
  negative : PlanarRectangleStokesRegularity negativeField center first second
    (-radius) (-halfThickness) radius 0
  /-- Local regularity of the positive-side extension on the closed positive half-rectangle. -/
  positive : PlanarRectangleStokesRegularity positiveField center first second
    (-radius) 0 radius halfThickness

/-- The sum of the two oriented vector-density flux integrals on a split rectangle. -/
def planarSplitRectangleFlux
    (negativeDensity positiveDensity : Space → EuclideanSpace ℝ (Fin 3))
    (center first second : Space) (radius halfThickness : ℝ) : ℝ :=
  (∫ u in -radius..radius, ∫ v in -halfThickness..0,
      inner ℝ (negativeDensity (planarRectanglePoint center first second u v))
        (basis.repr second ⨯ₑ₃ basis.repr first)) +
    ∫ u in -radius..radius, ∫ v in 0..halfThickness,
      inner ℝ (positiveDensity (planarRectanglePoint center first second u v))
        (basis.repr second ⨯ₑ₃ basis.repr first)

/-- The sum of the two oriented curl-flux integrals on the split rectangle. -/
def planarSplitRectangleCurlFlux
    (negativeField positiveField : Space → EuclideanSpace ℝ (Fin 3))
    (center first second : Space) (radius halfThickness : ℝ) : ℝ :=
  (∫ u in -radius..radius, ∫ v in -halfThickness..0,
      inner ℝ ((∇ ⨯ negativeField) (planarRectanglePoint center first second u v))
        (basis.repr second ⨯ₑ₃ basis.repr first)) +
    ∫ u in -radius..radius, ∫ v in 0..halfThickness,
      inner ℝ ((∇ ⨯ positiveField) (planarRectanglePoint center first second u v))
        (basis.repr second ⨯ₑ₃ basis.repr first)

/-- The outer circulation of the split rectangle, excluding its shared carrier edge. -/
def planarSplitRectangleOuterCirculation
    (negativeField positiveField : Space → EuclideanSpace ℝ (Fin 3))
    (center first second : Space) (radius halfThickness : ℝ) : ℝ :=
  let positiveLong := ∫ u in -radius..radius,
    inner ℝ (positiveField
      (planarRectanglePoint center first second u halfThickness))
      (basis.repr first)
  let negativeLong := ∫ u in -radius..radius,
    inner ℝ (negativeField
      (planarRectanglePoint center first second u (-halfThickness)))
      (basis.repr first)
  let leftShort :=
    (∫ v in -halfThickness..0,
        inner ℝ (negativeField
          (planarRectanglePoint center first second (-radius) v))
          (basis.repr second)) +
      ∫ v in 0..halfThickness,
        inner ℝ (positiveField
          (planarRectanglePoint center first second (-radius) v))
          (basis.repr second)
  let rightShort :=
    (∫ v in -halfThickness..0,
        inner ℝ (negativeField
          (planarRectanglePoint center first second radius v))
          (basis.repr second)) +
      ∫ v in 0..halfThickness,
        inner ℝ (positiveField
          (planarRectanglePoint center first second radius v))
          (basis.repr second)
  positiveLong - negativeLong + leftShort - rightShort

/-- The positive-minus-negative line-integral jump retained on the shared carrier edge. -/
def planarSplitRectangleCarrierJump
    (negativeField positiveField : Space → EuclideanSpace ℝ (Fin 3))
    (center first second : Space) (radius : ℝ) : ℝ :=
  (∫ u in -radius..radius,
      inner ℝ (positiveField (planarRectanglePoint center first second u 0))
        (basis.repr first)) -
    ∫ u in -radius..radius,
      inner ℝ (negativeField (planarRectanglePoint center first second u 0))
        (basis.repr first)

/-! ## B. Two-half Stokes identity -/

/-- The split rectangle's outer circulation equals its two bulk curl fluxes plus the retained
positive-minus-negative carrier line jump. -/
lemma planarSplitRectangleOuterCirculation_eq_curlFlux_add_carrierJump
    (negativeField positiveField : Space → EuclideanSpace ℝ (Fin 3))
    (center first second : Space) (radius halfThickness : ℝ)
    (regularity : PlanarSplitRectangleStokesRegularity negativeField positiveField
      center first second radius halfThickness) :
    planarSplitRectangleOuterCirculation negativeField positiveField
        center first second radius halfThickness =
      planarSplitRectangleCurlFlux negativeField positiveField
          center first second radius halfThickness +
        planarSplitRectangleCarrierJump negativeField positiveField
          center first second radius := by
  have hNegative := integral2_inner_curl_planarRectangle_of_localRegularity
    negativeField center first second (-radius) (-halfThickness) radius 0
    regularity.negative
  have hPositive := integral2_inner_curl_planarRectangle_of_localRegularity
    positiveField center first second (-radius) 0 radius halfThickness
    regularity.positive
  unfold planarSplitRectangleOuterCirculation planarSplitRectangleCurlFlux
    planarSplitRectangleCarrierJump
  rw [hNegative, hPositive]
  ring

end
end Space
