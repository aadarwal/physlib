/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.SpaceAndTime.Space.Integrals.PlanarSplitRectangleStokes
public import Physlib.SpaceAndTime.Space.Integrals.PlanarThinCell

/-!
# Local Stokes identities on planar thin loops

## i. Overview

This file specializes the local split-rectangle Stokes theorem to the tangent-normal frame of a
`PlanarThinLoopFamily`. Two independent ambient fields are restricted to the two open
half-spaces. Their carrier values are retained as an explicit line jump, while the totalized
open-side samples at the shared endpoint do not affect interval integrals.

The displayed circulation uses exactly `sideLongEdgeAverage` and `shortEdgeAverage`. A companion
result identifies `spanningSurfaceAverage` of independently restricted ambient densities with
the normalized sum of the two affine half-rectangle integrals.

This is neutral calculus. It states no Maxwell equation, sheet-current law, pointwise jump,
time-differentiation interchange, or shrinking-loop limit.

## ii. Key results

- `PlanarThinLoopFamily.AmbientHalfSpanningIntegrable`: both iterated integrability levels for one
  ambient half-surface flux.
- `PlanarThinLoopFamily.circulation_eq_normalized_curlFlux_add_carrierJump`: the normalized
  split-loop Stokes identity.
- `PlanarThinLoopFamily.spanningSurfaceAverage_ofFields_eq_normalized_affineSplitIntegral`:
  the two-sided spanning-surface bridge.

## iii. Table of contents

- A. Thin-loop frame geometry
- B. Ambient half-surface integrability
- C. Open-side integral bridges
- D. Normalized split-loop Stokes identity

## iv. References

This is neutral calculus infrastructure for the E4b finite-sheet premise.
-/

@[expose] public section

open Matrix MeasureTheory
open scoped Interval

namespace Space

noncomputable section

namespace PlanarThinLoopFamily

/-!
## A. Thin-loop frame geometry
-/

/-- The loop tangent, regarded as a direction in the affine-rectangle parameterization. -/
def tangentDirection {plane : OrientedAffineHyperplane 3}
    {tangent : plane.tangentSubmodule}
    (_loop : PlanarThinLoopFamily plane tangent) : Space :=
  basis.repr.symm (tangent : EuclideanSpace ℝ (Fin 3))

/-- The plane normal, regarded as the second affine-rectangle direction. -/
def normalDirection {plane : OrientedAffineHyperplane 3}
    {tangent : plane.tangentSubmodule}
    (_loop : PlanarThinLoopFamily plane tangent) : Space :=
  basis.repr.symm plane.normalVector

/-- The thin-loop affine frame parameterizes the same point as a tangent offset followed by a
signed normal offset. -/
lemma planarRectanglePoint_eq_normalOffsetPoint
    {plane : OrientedAffineHyperplane 3} {tangent : plane.tangentSubmodule}
    (loop : PlanarThinLoopFamily plane tangent) (x : plane.carrier) (u v : ℝ) :
    planarRectanglePoint (x : Space) loop.tangentDirection loop.normalDirection u v =
      plane.normalOffsetPoint x (u • tangent) v := by
  ext i
  simp [planarRectanglePoint, tangentDirection, normalDirection,
    OrientedAffineHyperplane.normalOffsetPoint, basis_repr_symm_apply]
  ring

/-- The oriented affine-rectangle normal is the thin loop's spanning-surface normal. -/
lemma spanningSurfaceNormal
    {plane : OrientedAffineHyperplane 3} {tangent : plane.tangentSubmodule}
    (loop : PlanarThinLoopFamily plane tangent) :
    basis.repr loop.normalDirection ⨯ₑ₃ basis.repr loop.tangentDirection =
      plane.normalVector ⨯ₑ₃ (tangent : EuclideanSpace ℝ (Fin 3)) := by
  rfl

/-!
## B. Ambient half-surface integrability
-/

/-- Both levels of integrability of one ambient half-surface flux in a thin loop.

These are the exact hypotheses needed to distribute sums at both levels of an iterated
half-surface integral. -/
def AmbientHalfSpanningIntegrable
    {plane : OrientedAffineHyperplane 3} {tangent : plane.tangentSubmodule}
    (loop : PlanarThinLoopFamily plane tangent) {P : Type*}
    (density : P → Space → EuclideanSpace ℝ (Fin 3))
    (parameter : P) (x : plane.carrier) (scale : ℕ)
    (lower upper : ℝ) : Prop :=
  (∀ u : ℝ, IntervalIntegrable
      (fun v ↦ inner ℝ (density parameter
        (plane.normalOffsetPoint x (u • tangent) v))
        (plane.normalVector ⨯ₑ₃ (tangent : EuclideanSpace ℝ (Fin 3))))
      volume lower upper) ∧
    IntervalIntegrable
      (fun u ↦ ∫ v in lower..upper,
        inner ℝ (density parameter (plane.normalOffsetPoint x (u • tangent) v))
          (plane.normalVector ⨯ₑ₃ (tangent : EuclideanSpace ℝ (Fin 3))))
      volume (-loop.radius scale) (loop.radius scale)

/-- Ambient half-surface integrability transports to the affine split-rectangle coordinates of
the thin loop. -/
lemma planarSplitRectangleFluxIntegrable
    {plane : OrientedAffineHyperplane 3} {tangent : plane.tangentSubmodule}
    (loop : PlanarThinLoopFamily plane tangent) {P : Type*}
    (negativeDensity positiveDensity : P → Space → EuclideanSpace ℝ (Fin 3))
    (parameter : P) (x : plane.carrier) (scale : ℕ)
    (negativeIntegrable : AmbientHalfSpanningIntegrable loop negativeDensity parameter x scale
      (-(loop.halfThickness scale)) 0)
    (positiveIntegrable : AmbientHalfSpanningIntegrable loop positiveDensity parameter x scale
      0 (loop.halfThickness scale)) :
    PlanarSplitRectangleFluxIntegrable (negativeDensity parameter)
      (positiveDensity parameter) (x : Space) loop.tangentDirection loop.normalDirection
      (loop.radius scale) (loop.halfThickness scale) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u
    apply (negativeIntegrable.1 u).congr
    intro v _
    dsimp only
    rw [loop.planarRectanglePoint_eq_normalOffsetPoint]
    rfl
  · intro u
    apply (positiveIntegrable.1 u).congr
    intro v _
    dsimp only
    rw [loop.planarRectanglePoint_eq_normalOffsetPoint]
    rfl
  · apply negativeIntegrable.2.congr
    intro u _
    apply intervalIntegral.integral_congr
    intro v _
    dsimp only
    rw [loop.planarRectanglePoint_eq_normalOffsetPoint]
    rfl
  · apply positiveIntegrable.2.congr
    intro u _
    apply intervalIntegral.integral_congr
    intro v _
    dsimp only
    rw [loop.planarRectanglePoint_eq_normalOffsetPoint]
    rfl

/-!
## C. Open-side integral bridges
-/

private lemma negativeSideSample_integral_eq_ambient
    {plane : OrientedAffineHyperplane 3}
    {P : Type*}
    (negativeField positiveField : P → Space → EuclideanSpace ℝ (Fin 3))
    (parameter : P) (x : plane.carrier) (offset : plane.tangentSubmodule)
    (direction : EuclideanSpace ℝ (Fin 3)) (halfThickness : ℝ)
    (hhalfThickness : 0 ≤ halfThickness) :
    (∫ v in -halfThickness..0,
      inner ℝ (plane.negativeSideSample
        (OrientedAffineHyperplane.TwoSidedField.ofFields plane
          negativeField positiveField).negative parameter x offset v) direction) =
      ∫ v in -halfThickness..0,
        inner ℝ (negativeField parameter
          (plane.normalOffsetPoint x offset v)) direction := by
  apply intervalIntegral.integral_congr_Ioo_of_le
    (neg_nonpos.mpr hhalfThickness)
  intro v hv
  change inner ℝ
      (plane.negativeSideSample
        (plane.restrictFieldToSide .negative negativeField)
        parameter x offset v) direction =
    inner ℝ (negativeField parameter
      (plane.normalOffsetPoint x offset v)) direction
  rw [plane.negativeSideSample_restrictFieldToSide_of_neg
    negativeField parameter x offset v hv.2]

private lemma positiveSideSample_integral_eq_ambient
    {plane : OrientedAffineHyperplane 3}
    {P : Type*}
    (negativeField positiveField : P → Space → EuclideanSpace ℝ (Fin 3))
    (parameter : P) (x : plane.carrier) (offset : plane.tangentSubmodule)
    (direction : EuclideanSpace ℝ (Fin 3)) (halfThickness : ℝ)
    (hhalfThickness : 0 ≤ halfThickness) :
    (∫ v in 0..halfThickness,
      inner ℝ (plane.positiveSideSample
        (OrientedAffineHyperplane.TwoSidedField.ofFields plane
          negativeField positiveField).positive parameter x offset v) direction) =
      ∫ v in 0..halfThickness,
        inner ℝ (positiveField parameter
          (plane.normalOffsetPoint x offset v)) direction := by
  apply intervalIntegral.integral_congr_Ioo_of_le hhalfThickness
  intro v hv
  change inner ℝ
      (plane.positiveSideSample
        (plane.restrictFieldToSide .positive positiveField)
        parameter x offset v) direction =
    inner ℝ (positiveField parameter
      (plane.normalOffsetPoint x offset v)) direction
  rw [plane.positiveSideSample_restrictFieldToSide_of_pos
    positiveField parameter x offset v hv.1]

private lemma positiveLongEdgeAverage_eq
    {plane : OrientedAffineHyperplane 3} {tangent : plane.tangentSubmodule}
    (loop : PlanarThinLoopFamily plane tangent) {P : Type*}
    (positiveField : P → Space → EuclideanSpace ℝ (Fin 3))
    (parameter : P) (x : plane.carrier) (scale : ℕ) :
    loop.sideLongEdgeAverage .positive
        (plane.restrictFieldToSide .positive positiveField) parameter x scale =
      (2 * loop.radius scale)⁻¹ *
        ∫ u in -loop.radius scale..loop.radius scale,
          inner ℝ (positiveField parameter
            (planarRectanglePoint (x : Space) loop.tangentDirection
              loop.normalDirection u (loop.halfThickness scale)))
            (basis.repr loop.tangentDirection) := by
  unfold PlanarThinLoopFamily.sideLongEdgeAverage normalizedIntervalAverage
  apply congrArg ((2 * loop.radius scale)⁻¹ * ·)
  apply intervalIntegral.integral_congr
  intro u _
  change inner ℝ (positiveField parameter (plane.sidePoint .positive x
      (u • tangent) (loop.halfThickness scale) (loop.halfThickness_pos scale)))
      (tangent : EuclideanSpace ℝ (Fin 3)) =
    inner ℝ (positiveField parameter
      (planarRectanglePoint (x : Space) loop.tangentDirection
        loop.normalDirection u (loop.halfThickness scale))) tangent
  rw [loop.planarRectanglePoint_eq_normalOffsetPoint,
    plane.positiveSidePoint_eq_normalOffsetPoint]

private lemma negativeLongEdgeAverage_eq
    {plane : OrientedAffineHyperplane 3} {tangent : plane.tangentSubmodule}
    (loop : PlanarThinLoopFamily plane tangent) {P : Type*}
    (negativeField : P → Space → EuclideanSpace ℝ (Fin 3))
    (parameter : P) (x : plane.carrier) (scale : ℕ) :
    loop.sideLongEdgeAverage .negative
        (plane.restrictFieldToSide .negative negativeField) parameter x scale =
      (2 * loop.radius scale)⁻¹ *
        ∫ u in -loop.radius scale..loop.radius scale,
          inner ℝ (negativeField parameter
            (planarRectanglePoint (x : Space) loop.tangentDirection
              loop.normalDirection u (-(loop.halfThickness scale))))
            (basis.repr loop.tangentDirection) := by
  unfold PlanarThinLoopFamily.sideLongEdgeAverage normalizedIntervalAverage
  apply congrArg ((2 * loop.radius scale)⁻¹ * ·)
  apply intervalIntegral.integral_congr
  intro u _
  change inner ℝ (negativeField parameter (plane.sidePoint .negative x
      (u • tangent) (loop.halfThickness scale) (loop.halfThickness_pos scale)))
      (tangent : EuclideanSpace ℝ (Fin 3)) =
    inner ℝ (negativeField parameter
      (planarRectanglePoint (x : Space) loop.tangentDirection
        loop.normalDirection u (-(loop.halfThickness scale)))) tangent
  rw [loop.planarRectanglePoint_eq_normalOffsetPoint,
    plane.negativeSidePoint_eq_normalOffsetPoint]

private lemma shortEdgeAverage_eq
    {plane : OrientedAffineHyperplane 3} {tangent : plane.tangentSubmodule}
    (loop : PlanarThinLoopFamily plane tangent) {P : Type*}
    (negativeField positiveField : P → Space → EuclideanSpace ℝ (Fin 3))
    (parameter : P) (x : plane.carrier) (scale : ℕ) :
    loop.shortEdgeAverage
        (OrientedAffineHyperplane.TwoSidedField.ofFields plane
          negativeField positiveField) parameter x scale =
      (2 * loop.radius scale)⁻¹ *
        (((∫ v in -loop.halfThickness scale..0,
              inner ℝ (negativeField parameter
                (planarRectanglePoint (x : Space) loop.tangentDirection
                  loop.normalDirection (-(loop.radius scale)) v))
                (basis.repr loop.normalDirection)) +
            ∫ v in 0..loop.halfThickness scale,
              inner ℝ (positiveField parameter
                (planarRectanglePoint (x : Space) loop.tangentDirection
                  loop.normalDirection (-(loop.radius scale)) v))
                (basis.repr loop.normalDirection)) -
          ((∫ v in -loop.halfThickness scale..0,
              inner ℝ (negativeField parameter
                (planarRectanglePoint (x : Space) loop.tangentDirection
                  loop.normalDirection (loop.radius scale) v))
                (basis.repr loop.normalDirection)) +
            ∫ v in 0..loop.halfThickness scale,
              inner ℝ (positiveField parameter
                (planarRectanglePoint (x : Space) loop.tangentDirection
                  loop.normalDirection (loop.radius scale) v))
                (basis.repr loop.normalDirection))) := by
  let left := -(loop.radius scale) • tangent
  let right := loop.radius scale • tangent
  have hNegativeLeft := negativeSideSample_integral_eq_ambient
    negativeField positiveField parameter x left plane.normalVector
    (loop.halfThickness scale) (loop.halfThickness_pos scale).le
  have hPositiveLeft := positiveSideSample_integral_eq_ambient
    negativeField positiveField parameter x left plane.normalVector
    (loop.halfThickness scale) (loop.halfThickness_pos scale).le
  have hNegativeRight := negativeSideSample_integral_eq_ambient
    negativeField positiveField parameter x right plane.normalVector
    (loop.halfThickness scale) (loop.halfThickness_pos scale).le
  have hPositiveRight := positiveSideSample_integral_eq_ambient
    negativeField positiveField parameter x right plane.normalVector
    (loop.halfThickness scale) (loop.halfThickness_pos scale).le
  unfold PlanarThinLoopFamily.shortEdgeAverage splitNormalIntegral
  dsimp only
  rw [hNegativeLeft, hPositiveLeft, hNegativeRight, hPositiveRight]
  apply congrArg ((2 * loop.radius scale)⁻¹ * ·)
  rw [show basis.repr loop.normalDirection = plane.normalVector by rfl]
  simp only [left, right]
  congr 2 <;>
    apply intervalIntegral.integral_congr <;>
    intro v _ <;>
    dsimp only <;>
    rw [loop.planarRectanglePoint_eq_normalOffsetPoint]

/-!
## D. Normalized split-loop Stokes identity
-/

/-- The normalized principal-plus-short-edge circulation equals the normalized sum of the two
bulk curl-flux integrals and the retained positive-minus-negative carrier-line integral. -/
lemma circulation_eq_normalized_curlFlux_add_carrierJump
    {plane : OrientedAffineHyperplane 3} {tangent : plane.tangentSubmodule}
    (loop : PlanarThinLoopFamily plane tangent) {P : Type*}
    (negativeField positiveField : P → Space → EuclideanSpace ℝ (Fin 3))
    (parameter : P) (x : plane.carrier) (scale : ℕ)
    (regularity : PlanarSplitRectangleStokesRegularity
      (negativeField parameter) (positiveField parameter) (x : Space)
      loop.tangentDirection loop.normalDirection
      (loop.radius scale) (loop.halfThickness scale)) :
    loop.sideLongEdgeAverage .positive
          (plane.restrictFieldToSide .positive positiveField) parameter x scale -
        loop.sideLongEdgeAverage .negative
          (plane.restrictFieldToSide .negative negativeField) parameter x scale +
        loop.shortEdgeAverage
          (OrientedAffineHyperplane.TwoSidedField.ofFields plane
            negativeField positiveField) parameter x scale =
      (2 * loop.radius scale)⁻¹ *
        (planarSplitRectangleCurlFlux (negativeField parameter) (positiveField parameter)
            (x : Space) loop.tangentDirection loop.normalDirection
            (loop.radius scale) (loop.halfThickness scale) +
          planarSplitRectangleCarrierJump (negativeField parameter) (positiveField parameter)
            (x : Space) loop.tangentDirection loop.normalDirection
            (loop.radius scale)) := by
  rw [positiveLongEdgeAverage_eq loop positiveField parameter x scale,
    negativeLongEdgeAverage_eq loop negativeField parameter x scale,
    shortEdgeAverage_eq loop negativeField positiveField parameter x scale]
  have hStokes := planarSplitRectangleOuterCirculation_eq_curlFlux_add_carrierJump
    (negativeField parameter) (positiveField parameter) (x : Space)
    loop.tangentDirection loop.normalDirection
    (loop.radius scale) (loop.halfThickness scale) regularity
  unfold planarSplitRectangleOuterCirculation at hStokes
  dsimp only at hStokes
  rw [← hStokes]
  ring

/-- The two-sided spanning-surface average of independently restricted ambient densities equals
the normalized sum of their two affine half-rectangle flux integrals. -/
lemma spanningSurfaceAverage_ofFields_eq_normalized_affineSplitIntegral
    {plane : OrientedAffineHyperplane 3} {tangent : plane.tangentSubmodule}
    (loop : PlanarThinLoopFamily plane tangent) {P : Type*}
    (negativeDensity positiveDensity : P → Space → EuclideanSpace ℝ (Fin 3))
    (parameter : P) (x : plane.carrier) (scale : ℕ)
    (negativeIntegrable : AmbientHalfSpanningIntegrable loop negativeDensity
      parameter x scale (-(loop.halfThickness scale)) 0)
    (positiveIntegrable : AmbientHalfSpanningIntegrable loop positiveDensity
      parameter x scale 0 (loop.halfThickness scale)) :
    loop.spanningSurfaceAverage
        (OrientedAffineHyperplane.TwoSidedField.ofFields plane
          negativeDensity positiveDensity) parameter x scale =
      (2 * loop.radius scale)⁻¹ *
        ((∫ u in -loop.radius scale..loop.radius scale,
            ∫ v in -loop.halfThickness scale..0,
              inner ℝ (negativeDensity parameter
                (planarRectanglePoint (x : Space) loop.tangentDirection
                  loop.normalDirection u v))
                (basis.repr loop.normalDirection ⨯ₑ₃
                  basis.repr loop.tangentDirection)) +
          ∫ u in -loop.radius scale..loop.radius scale,
            ∫ v in 0..loop.halfThickness scale,
              inner ℝ (positiveDensity parameter
                (planarRectanglePoint (x : Space) loop.tangentDirection
                  loop.normalDirection u v))
                (basis.repr loop.normalDirection ⨯ₑ₃
                  basis.repr loop.tangentDirection)) := by
  let radius := loop.radius scale
  let thickness := loop.halfThickness scale
  let normal := plane.normalVector ⨯ₑ₃
    (tangent : EuclideanSpace ℝ (Fin 3))
  unfold PlanarThinLoopFamily.spanningSurfaceAverage
  apply congrArg ((2 * loop.radius scale)⁻¹ * ·)
  calc
    (∫ u in -radius..radius,
      splitNormalIntegral thickness
        (fun v ↦ inner ℝ (plane.negativeSideSample
          (OrientedAffineHyperplane.TwoSidedField.ofFields plane
            negativeDensity positiveDensity).negative parameter x (u • tangent) v) normal)
        (fun v ↦ inner ℝ (plane.positiveSideSample
          (OrientedAffineHyperplane.TwoSidedField.ofFields plane
            negativeDensity positiveDensity).positive parameter x (u • tangent) v) normal)) =
      ∫ u in -radius..radius,
        (∫ v in -thickness..0,
          inner ℝ (negativeDensity parameter
            (plane.normalOffsetPoint x (u • tangent) v)) normal) +
        ∫ v in 0..thickness,
          inner ℝ (positiveDensity parameter
            (plane.normalOffsetPoint x (u • tangent) v)) normal := by
      apply intervalIntegral.integral_congr
      intro u _
      change splitNormalIntegral thickness
          (fun v ↦ inner ℝ (plane.negativeSideSample
            (OrientedAffineHyperplane.TwoSidedField.ofFields plane
              negativeDensity positiveDensity).negative parameter x (u • tangent) v) normal)
          (fun v ↦ inner ℝ (plane.positiveSideSample
            (OrientedAffineHyperplane.TwoSidedField.ofFields plane
              negativeDensity positiveDensity).positive parameter x (u • tangent) v) normal) =
        (∫ v in -thickness..0,
          inner ℝ (negativeDensity parameter
            (plane.normalOffsetPoint x (u • tangent) v)) normal) +
        ∫ v in 0..thickness,
          inner ℝ (positiveDensity parameter
            (plane.normalOffsetPoint x (u • tangent) v)) normal
      unfold splitNormalIntegral
      rw [negativeSideSample_integral_eq_ambient
          negativeDensity positiveDensity parameter x (u • tangent) normal thickness
          (loop.halfThickness_pos scale).le,
        positiveSideSample_integral_eq_ambient
          negativeDensity positiveDensity parameter x (u • tangent) normal thickness
          (loop.halfThickness_pos scale).le]
    _ = (∫ u in -radius..radius, ∫ v in -thickness..0,
          inner ℝ (negativeDensity parameter
            (plane.normalOffsetPoint x (u • tangent) v)) normal) +
        ∫ u in -radius..radius, ∫ v in 0..thickness,
          inner ℝ (positiveDensity parameter
            (plane.normalOffsetPoint x (u • tangent) v)) normal :=
      intervalIntegral.integral_add negativeIntegrable.2 positiveIntegrable.2
    _ = _ := by
      congr 1
      · apply intervalIntegral.integral_congr
        intro u _
        apply intervalIntegral.integral_congr
        intro v _
        change inner ℝ (negativeDensity parameter
            (plane.normalOffsetPoint x (u • tangent) v)) normal =
          inner ℝ (negativeDensity parameter
            (planarRectanglePoint (x : Space) loop.tangentDirection
              loop.normalDirection u v))
            (basis.repr loop.normalDirection ⨯ₑ₃ basis.repr loop.tangentDirection)
        rw [loop.spanningSurfaceNormal,
          loop.planarRectanglePoint_eq_normalOffsetPoint]
      · apply intervalIntegral.integral_congr
        intro u _
        apply intervalIntegral.integral_congr
        intro v _
        change inner ℝ (positiveDensity parameter
            (plane.normalOffsetPoint x (u • tangent) v)) normal =
          inner ℝ (positiveDensity parameter
            (planarRectanglePoint (x : Space) loop.tangentDirection
              loop.normalDirection u v))
            (basis.repr loop.normalDirection ⨯ₑ₃ basis.repr loop.tangentDirection)
        rw [loop.spanningSurfaceNormal,
          loop.planarRectanglePoint_eq_normalOffsetPoint]

end PlanarThinLoopFamily

end
end Space
