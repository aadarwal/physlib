/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.SpaceAndTime.Space.Integrals.ThinCellLimit
public import Physlib.SpaceAndTime.Space.OrientedAffineHyperplaneCrossProduct
public import Physlib.SpaceAndTime.Space.OrientedAffineHyperplaneTrace
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Planar thin-loop and pillbox averages

## i. Overview

This file gives explicit shrinking planar cell geometry and the normalized principal averages used
by thin-loop and pillbox arguments. A side sample is genuinely a point of the selected open
half-space. A boundary sample remains in the carrier. Long-edge averages pair a side field with a
chosen tangent direction. Short-edge and lateral-face terms sample genuine two-sided bulk fields
off the carrier. Face averages use that tangent and its oriented quarter-turn
`normalVector cross tangent`; their physical area Jacobian cancels in the normalized average.

The file does not state Stokes, divergence, or Maxwell laws. It also does not prove that the
averages converge to one-sided traces: that requires uniform thin-cell control stronger than a
pointwise trace and is therefore an explicit hypothesis in the electromagnetic consumer.

## ii. Key results

- `OrientedAffineHyperplane.tangentPoint`: a carrier point displaced tangentially.
- `OrientedAffineHyperplane.sidePoint`: a positive-distance sample in one open half-space.
- `OrientedAffineHyperplane.quarterTurnTangent`: the oriented in-plane quarter-turn.
- `PlanarThinLoopFamily.sideLongEdgeAverage`: an actual normalized long-edge integral.
- `PlanarThinLoopFamily.shortEdgeAverage`: the two normalized short-edge integrals.
- `PlanarThinLoopFamily.spanningSurfaceAverage`: a normalized thin-rectangle flux integral.
- `PlanarPillboxFamily.sideFaceAverage`: an actual normalized principal-face integral.
- `PlanarPillboxFamily.lateralFaceAverage`: the four normalized lateral-face integrals.
- `PlanarPillboxFamily.volumeAverage`: an actual normalized thin-box integral.

## iii. Table of contents

- A. Normalized interval and square averages
- A.1. Integrability of iterated cell integrals
- B. Planar sample geometry
- C. Thin-loop families
- D. Pillbox families

## iv. References

This is neutral geometry and integration infrastructure for the E4b Maxwell boundary derivation.
-/

@[expose] public section

open Filter
open Matrix
open scoped Interval

namespace Space

noncomputable section

/-! ## A. Normalized interval and square averages -/

/-- The interval integral over `[-radius, radius]`, divided by its signed length `2 * radius`.

The definition is total at `radius = 0`; thin-cell families separately require positive radii. -/
def normalizedIntervalAverage (radius : ℝ) (f : ℝ → ℝ) : ℝ :=
  (2 * radius)⁻¹ * ∫ u in -radius..radius, f u

/-- The iterated normalized square average over `[-radius, radius]²`. -/
def normalizedSquareAverage (radius : ℝ) (f : ℝ → ℝ → ℝ) : ℝ :=
  normalizedIntervalAverage radius fun u ↦ normalizedIntervalAverage radius (f u)

/-- Integrate over a rectangle with half-length `radius` and half-thickness `halfThickness`, then
divide by the principal length `2 * radius`. -/
def normalizedThinRectangleIntegral (radius halfThickness : ℝ)
    (f : ℝ → ℝ → ℝ) : ℝ :=
  (2 * radius)⁻¹ * ∫ u in -radius..radius, ∫ v in -halfThickness..halfThickness, f u v

/-- Integrate over a box with square half-width `radius` and normal half-thickness
`halfThickness`, then divide by the principal-face area `(2 * radius) ^ 2`. -/
def normalizedThinBoxIntegral (radius halfThickness : ℝ)
    (f : ℝ → ℝ → ℝ → ℝ) : ℝ :=
  ((2 * radius) ^ 2)⁻¹ *
    ∫ u in -radius..radius,
      ∫ v in -radius..radius, ∫ w in -halfThickness..halfThickness, f u v w

/-- Sum the negative- and positive-half interval integrals without assigning either integrand to
the shared endpoint. -/
def splitNormalIntegral (halfThickness : ℝ) (negative positive : ℝ → ℝ) : ℝ :=
  (∫ w in -halfThickness..0, negative w) + ∫ w in 0..halfThickness, positive w

/-! ### A.1. Integrability of iterated cell integrals -/

/-- Integrability on the symmetric interval used by a normalized cell average. -/
def SymmetricIntervalIntegrable (radius : ℝ) (f : ℝ → ℝ) : Prop :=
  IntervalIntegrable f MeasureTheory.volume (-radius) radius

/-- Integrability on both open-side halves of a normal interval. -/
def SplitNormalIntegrable (halfThickness : ℝ)
    (negative positive : ℝ → ℝ) : Prop :=
  IntervalIntegrable negative MeasureTheory.volume (-halfThickness) 0 ∧
  IntervalIntegrable positive MeasureTheory.volume 0 halfThickness

/-- Integrability of both levels of an iterated symmetric-square integral. -/
def IteratedSquareIntegrable (radius : ℝ) (f : ℝ → ℝ → ℝ) : Prop :=
  (∀ u, SymmetricIntervalIntegrable radius (f u)) ∧
  SymmetricIntervalIntegrable radius
    (fun u ↦ normalizedIntervalAverage radius (f u))

/-- Integrability of a rectangle whose normal integral is split across the carrier. -/
def SplitRectangleIntegrable (radius halfThickness : ℝ)
    (negative positive : ℝ → ℝ → ℝ) : Prop :=
  (∀ u, SplitNormalIntegrable halfThickness (negative u) (positive u)) ∧
  SymmetricIntervalIntegrable radius fun u ↦
    splitNormalIntegral halfThickness (negative u) (positive u)

/-- Integrability of all three levels of a box whose normal integral is split across the
carrier. -/
def SplitBoxIntegrable (radius halfThickness : ℝ)
    (negative positive : ℝ → ℝ → ℝ → ℝ) : Prop :=
  (∀ u v, SplitNormalIntegrable halfThickness (negative u v) (positive u v)) ∧
  (∀ u, SymmetricIntervalIntegrable radius fun v ↦
    splitNormalIntegral halfThickness (negative u v) (positive u v)) ∧
  SymmetricIntervalIntegrable radius fun u ↦
    ∫ v in -radius..radius,
      splitNormalIntegral halfThickness (negative u v) (positive u v)

namespace OrientedAffineHyperplane

/-! ## B. Planar sample geometry -/

/-- An ambient point displaced tangentially from a carrier point and then by a signed amount
along the stored normal. Positive offsets lie on the positive side and negative offsets on the
negative side. -/
def normalOffsetPoint {d : ℕ} (plane : OrientedAffineHyperplane d) (x : plane.carrier)
    (offset : plane.tangentSubmodule) (height : ℝ) : Space d :=
  ((offset : EuclideanSpace ℝ (Fin d)) + height • plane.normalVector) +ᵥ (x : Space d)

/-- The signed normal coordinate of `normalOffsetPoint` is its signed height. -/
@[simp]
lemma signedNormalCoordinate_normalOffsetPoint {d : ℕ}
    (plane : OrientedAffineHyperplane d) (x : plane.carrier)
    (offset : plane.tangentSubmodule) (height : ℝ) :
    plane.signedNormalCoordinate (plane.normalOffsetPoint x offset height) = height := by
  rw [normalOffsetPoint, plane.signedNormalCoordinate_vadd,
    (plane.mem_carrier (x : Space d)).mp x.property, add_zero,
    normalComponent, inner_add_right, inner_smul_right,
    (plane.mem_tangentSubmodule offset).mp offset.property,
    zero_add, plane.inner_normalVector_self, mul_one]

/-- Sample a negative-side field at a signed negative normal height.

The totalized value is zero when the height is not strictly negative. In thin-cell integrals this
function is used only on `[-h, 0]`; the endpoint convention is made explicit rather than assigning
a carrier point to the open-half-space field. -/
def negativeSideSample {d : ℕ} {P V : Type*} [Zero V]
    (plane : OrientedAffineHyperplane d) (field : plane.SideField .negative P V)
    (parameter : P) (x : plane.carrier) (offset : plane.tangentSubmodule)
    (height : ℝ) : V :=
  if hHeight : height < 0 then
    field parameter ⟨plane.normalOffsetPoint x offset height, by
      change 0 < -plane.signedNormalCoordinate (plane.normalOffsetPoint x offset height)
      rw [plane.signedNormalCoordinate_normalOffsetPoint]
      linarith⟩
  else 0

/-- Sample a positive-side field at a signed positive normal height.

The totalized value is zero when the height is not strictly positive. In thin-cell integrals this
function is used only on `[0, h]`, with the carrier endpoint treated separately from both bulk
sides. -/
def positiveSideSample {d : ℕ} {P V : Type*} [Zero V]
    (plane : OrientedAffineHyperplane d) (field : plane.SideField .positive P V)
    (parameter : P) (x : plane.carrier) (offset : plane.tangentSubmodule)
    (height : ℝ) : V :=
  if hHeight : 0 < height then
    field parameter ⟨plane.normalOffsetPoint x offset height, by
      change 0 < plane.signedNormalCoordinate (plane.normalOffsetPoint x offset height)
      simpa using hHeight⟩
  else 0

/-- A carrier point displaced by a bundled tangent vector remains in the carrier. -/
def tangentPoint {d : ℕ} (plane : OrientedAffineHyperplane d) (x : plane.carrier)
    (offset : plane.tangentSubmodule) : plane.carrier :=
  ⟨(offset : EuclideanSpace ℝ (Fin d)) +ᵥ (x : Space d), by
    rw [plane.mem_carrier, plane.signedNormalCoordinate_vadd,
      (plane.mem_carrier (x : Space d)).mp x.property, add_zero]
    exact (plane.mem_tangentSubmodule offset).mp offset.property⟩

/-- A tangentially displaced carrier point, moved a positive distance into one selected side. -/
def sidePoint {d : ℕ} (plane : OrientedAffineHyperplane d) (side : Side)
    (x : plane.carrier) (offset : plane.tangentSubmodule) (height : ℝ)
    (hHeight : 0 < height) : plane.openHalfSpace side :=
  ⟨((offset : EuclideanSpace ℝ (Fin d)) + height • plane.sideNormalVector side) +ᵥ
      (x : Space d), by
    change 0 < side.sign * plane.signedNormalCoordinate
      (((offset : EuclideanSpace ℝ (Fin d)) + height • plane.sideNormalVector side) +ᵥ
        (x : Space d))
    rw [plane.signedNormalCoordinate_vadd,
      (plane.mem_carrier (x : Space d)).mp x.property, add_zero,
      normalComponent, inner_add_right, inner_smul_right]
    have hOffset : inner ℝ plane.normalVector
        (offset : EuclideanSpace ℝ (Fin d)) = 0 :=
      (plane.mem_tangentSubmodule offset).mp offset.property
    rw [hOffset, zero_add]
    change 0 < side.sign * (height * plane.normalComponent (plane.sideNormalVector side))
    rw [plane.normalComponent_sideNormalVector]
    nlinarith [side.sign_sq]⟩

/-- The oriented in-plane quarter-turn of a bundled tangent vector. -/
def quarterTurnTangent (plane : OrientedAffineHyperplane 3)
    (tangent : plane.tangentSubmodule) : plane.tangentSubmodule :=
  ⟨plane.normalVector ⨯ₑ₃ (tangent : EuclideanSpace ℝ (Fin 3)), by
    change plane.normalComponent
      (plane.normalVector ⨯ₑ₃ (tangent : EuclideanSpace ℝ (Fin 3))) = 0
    exact Space.inner_self_cross plane.normalVector tangent⟩

/-- The oriented in-plane quarter-turn preserves the norm of a tangent vector. -/
lemma norm_quarterTurnTangent (plane : OrientedAffineHyperplane 3)
    (tangent : plane.tangentSubmodule) :
    ‖(plane.quarterTurnTangent tangent : EuclideanSpace ℝ (Fin 3))‖ =
      ‖(tangent : EuclideanSpace ℝ (Fin 3))‖ :=
  plane.norm_normalVector_cross_of_isTangent tangent
    ((plane.mem_tangentSubmodule tangent).mp tangent.property)

/-- For a unit tangent, the tangent crossed with its oriented quarter-turn is the stored normal. -/
lemma tangent_cross_quarterTurnTangent_of_norm_eq_one
    (plane : OrientedAffineHyperplane 3) (tangent : plane.tangentSubmodule)
    (hNorm : ‖(tangent : EuclideanSpace ℝ (Fin 3))‖ = 1) :
    (tangent : EuclideanSpace ℝ (Fin 3)) ⨯ₑ₃
        (plane.quarterTurnTangent tangent : EuclideanSpace ℝ (Fin 3)) =
      plane.normalVector := by
  change (tangent : EuclideanSpace ℝ (Fin 3)) ⨯ₑ₃
      (plane.normalVector ⨯ₑ₃ (tangent : EuclideanSpace ℝ (Fin 3))) =
    plane.normalVector
  rw [Space.cross_cross_eq_smul_sub_smul', real_inner_self_eq_norm_sq, hNorm,
    one_pow, one_smul,
    (plane.mem_tangentSubmodule tangent).mp tangent.property, zero_smul, sub_zero]

end OrientedAffineHyperplane

/-! ## C. Thin-loop families -/

/-- Positive shrinking planar-cell scales whose thickness vanishes relative to their principal
radius. The aspect-ratio condition is the geometric gate used to kill normalized short-edge and
lateral-face contributions under local boundedness. -/
structure PlanarThinScale where
  /-- Half-width or half-length of the principal face or edge. -/
  radius : ℕ → ℝ
  /-- Normal half-thickness of the cell. -/
  halfThickness : ℕ → ℝ
  /-- Every principal radius is positive. -/
  radius_pos : ∀ scale, 0 < radius scale
  /-- Every half-thickness is positive. -/
  halfThickness_pos : ∀ scale, 0 < halfThickness scale
  /-- The principal radius shrinks to zero. -/
  radius_tendsto_zero : Tendsto radius atTop (nhds 0)
  /-- The half-thickness shrinks to zero. -/
  halfThickness_tendsto_zero : Tendsto halfThickness atTop (nhds 0)
  /-- The cell becomes thin relative to its principal radius. -/
  halfThickness_div_radius_tendsto_zero :
    Tendsto (fun scale ↦ halfThickness scale / radius scale) atTop (nhds 0)

/-- A sequence of planar thin loops shrinking to one carrier point along a fixed tangent
direction. -/
structure PlanarThinLoopFamily (plane : OrientedAffineHyperplane 3)
    (tangent : plane.tangentSubmodule) extends PlanarThinScale

namespace PlanarThinLoopFamily

/-- The normalized principal-edge integral of a selected-side vector field, oriented along the
stored tangent direction. -/
def sideLongEdgeAverage {plane : OrientedAffineHyperplane 3}
    {tangent : plane.tangentSubmodule} (loop : PlanarThinLoopFamily plane tangent)
    (side : OrientedAffineHyperplane.Side)
    {P : Type*} (field : plane.SideField side P (EuclideanSpace ℝ (Fin 3)))
    (parameter : P) (x : plane.carrier) (scale : ℕ) : ℝ :=
  normalizedIntervalAverage (loop.radius scale) fun u ↦
    inner ℝ
      (field parameter
        (plane.sidePoint side x (u • tangent) (loop.halfThickness scale)
          (loop.halfThickness_pos scale)))
      (tangent : EuclideanSpace ℝ (Fin 3))

/-- The normalized boundary-line integral of a tangent vector source against the oriented
spanning-surface normal `normalVector cross tangent`. -/
def surfaceLineAverage {plane : OrientedAffineHyperplane 3}
    {tangent : plane.tangentSubmodule} (loop : PlanarThinLoopFamily plane tangent)
    {P : Type*} (source : plane.BoundaryField P plane.tangentSubmodule)
    (parameter : P) (x : plane.carrier) (scale : ℕ) : ℝ :=
  normalizedIntervalAverage (loop.radius scale) fun u ↦
    inner ℝ
      (source parameter (plane.tangentPoint x (u • tangent)) :
        EuclideanSpace ℝ (Fin 3))
      (plane.normalVector ⨯ₑ₃ (tangent : EuclideanSpace ℝ (Fin 3)))

/-- The normalized circulation along the two short edges of the thin loop.

The positive-`tangent` endpoint is traversed from the positive side to the negative side, and the
negative-`tangent` endpoint is traversed in the opposite direction. This is the orientation for
which the long-edge contribution is positive-side minus negative-side. -/
def shortEdgeAverage {plane : OrientedAffineHyperplane 3}
    {tangent : plane.tangentSubmodule} (loop : PlanarThinLoopFamily plane tangent)
    {P : Type*} (field : plane.TwoSidedField P (EuclideanSpace ℝ (Fin 3)))
    (parameter : P) (x : plane.carrier) (scale : ℕ) : ℝ :=
  let left := -(loop.radius scale) • tangent
  let right := loop.radius scale • tangent
  (2 * loop.radius scale)⁻¹ *
    (splitNormalIntegral (loop.halfThickness scale)
        (fun v ↦ inner ℝ (plane.negativeSideSample field.negative parameter x left v)
          plane.normalVector)
        (fun v ↦ inner ℝ (plane.positiveSideSample field.positive parameter x left v)
          plane.normalVector) -
      splitNormalIntegral (loop.halfThickness scale)
        (fun v ↦ inner ℝ (plane.negativeSideSample field.negative parameter x right v)
          plane.normalVector)
        (fun v ↦ inner ℝ (plane.positiveSideSample field.positive parameter x right v)
          plane.normalVector))

/-- The normalized flux of a two-sided bulk vector density through the thin loop's spanning
rectangle, oriented by `normalVector cross tangent`. -/
def spanningSurfaceAverage {plane : OrientedAffineHyperplane 3}
    {tangent : plane.tangentSubmodule} (loop : PlanarThinLoopFamily plane tangent)
    {P : Type*} (density : plane.TwoSidedField P (EuclideanSpace ℝ (Fin 3)))
    (parameter : P) (x : plane.carrier) (scale : ℕ) : ℝ :=
  (2 * loop.radius scale)⁻¹ *
    ∫ u in -loop.radius scale..loop.radius scale,
      splitNormalIntegral (loop.halfThickness scale)
        (fun v ↦ inner ℝ
          (plane.negativeSideSample density.negative parameter x (u • tangent) v)
          (plane.normalVector ⨯ₑ₃ (tangent : EuclideanSpace ℝ (Fin 3))))
        (fun v ↦ inner ℝ
          (plane.positiveSideSample density.positive parameter x (u • tangent) v)
          (plane.normalVector ⨯ₑ₃ (tangent : EuclideanSpace ℝ (Fin 3))))

/-- Integrability of a selected-side principal long-edge pullback. -/
def SideLongEdgeIntegrable {plane : OrientedAffineHyperplane 3}
    {tangent : plane.tangentSubmodule} (loop : PlanarThinLoopFamily plane tangent)
    (side : OrientedAffineHyperplane.Side)
    {P : Type*} (field : plane.SideField side P (EuclideanSpace ℝ (Fin 3)))
    (parameter : P) (x : plane.carrier) (scale : ℕ) : Prop :=
  SymmetricIntervalIntegrable (loop.radius scale) fun u ↦
    inner ℝ
      (field parameter
        (plane.sidePoint side x (u • tangent) (loop.halfThickness scale)
          (loop.halfThickness_pos scale)))
      (tangent : EuclideanSpace ℝ (Fin 3))

/-- Integrability of a boundary-line surface-current pullback. -/
def SurfaceLineIntegrable {plane : OrientedAffineHyperplane 3}
    {tangent : plane.tangentSubmodule} (loop : PlanarThinLoopFamily plane tangent)
    {P : Type*} (source : plane.BoundaryField P plane.tangentSubmodule)
    (parameter : P) (x : plane.carrier) (scale : ℕ) : Prop :=
  SymmetricIntervalIntegrable (loop.radius scale) fun u ↦
    inner ℝ
      (source parameter (plane.tangentPoint x (u • tangent)) :
        EuclideanSpace ℝ (Fin 3))
      (plane.normalVector ⨯ₑ₃ (tangent : EuclideanSpace ℝ (Fin 3)))

/-- Integrability of all four half-pullbacks forming the two short-edge integrals. -/
def ShortEdgesIntegrable {plane : OrientedAffineHyperplane 3}
    {tangent : plane.tangentSubmodule} (loop : PlanarThinLoopFamily plane tangent)
    {P : Type*} (field : plane.TwoSidedField P (EuclideanSpace ℝ (Fin 3)))
    (parameter : P) (x : plane.carrier) (scale : ℕ) : Prop :=
  let left := -(loop.radius scale) • tangent
  let right := loop.radius scale • tangent
  SplitNormalIntegrable (loop.halfThickness scale)
      (fun v ↦ inner ℝ (plane.negativeSideSample field.negative parameter x left v)
        plane.normalVector)
      (fun v ↦ inner ℝ (plane.positiveSideSample field.positive parameter x left v)
        plane.normalVector) ∧
    SplitNormalIntegrable (loop.halfThickness scale)
      (fun v ↦ inner ℝ (plane.negativeSideSample field.negative parameter x right v)
        plane.normalVector)
      (fun v ↦ inner ℝ (plane.positiveSideSample field.positive parameter x right v)
        plane.normalVector)

/-- Integrability of the split two-sided pullback on a thin loop's spanning rectangle. -/
def SpanningSurfaceIntegrable {plane : OrientedAffineHyperplane 3}
    {tangent : plane.tangentSubmodule} (loop : PlanarThinLoopFamily plane tangent)
    {P : Type*} (density : plane.TwoSidedField P (EuclideanSpace ℝ (Fin 3)))
    (parameter : P) (x : plane.carrier) (scale : ℕ) : Prop :=
  SplitRectangleIntegrable (loop.radius scale) (loop.halfThickness scale)
    (fun u v ↦ inner ℝ
      (plane.negativeSideSample density.negative parameter x (u • tangent) v)
      (plane.normalVector ⨯ₑ₃ (tangent : EuclideanSpace ℝ (Fin 3))))
    (fun u v ↦ inner ℝ
      (plane.positiveSideSample density.positive parameter x (u • tangent) v)
      (plane.normalVector ⨯ₑ₃ (tangent : EuclideanSpace ℝ (Fin 3))))

end PlanarThinLoopFamily

/-! ## D. Pillbox families -/

/-- A sequence of planar pillboxes shrinking to one carrier point. The stored unit tangent and its
oriented quarter-turn parameterize the principal faces. -/
structure PlanarPillboxFamily (plane : OrientedAffineHyperplane 3) extends PlanarThinScale where
  /-- A selected unit tangent direction used to parameterize both principal faces. -/
  tangent : plane.tangentSubmodule
  /-- The selected tangent has unit norm. -/
  tangent_norm : ‖(tangent : EuclideanSpace ℝ (Fin 3))‖ = 1

namespace PlanarPillboxFamily

/-- The normalized principal-face flux average of a selected-side vector field against the stored
negative-to-positive normal. -/
def sideFaceAverage {plane : OrientedAffineHyperplane 3}
    (pillbox : PlanarPillboxFamily plane)
    (side : OrientedAffineHyperplane.Side)
    {P : Type*} (field : plane.SideField side P (EuclideanSpace ℝ (Fin 3)))
    (parameter : P) (x : plane.carrier) (scale : ℕ) : ℝ :=
  normalizedSquareAverage (pillbox.radius scale) fun u v ↦
    inner ℝ plane.normalVector
      (field parameter
        (plane.sidePoint side x
          (u • pillbox.tangent + v • plane.quarterTurnTangent pillbox.tangent)
          (pillbox.halfThickness scale) (pillbox.halfThickness_pos scale)))

/-- The normalized boundary-face average of a scalar surface source. -/
def surfaceFaceAverage {plane : OrientedAffineHyperplane 3}
    (pillbox : PlanarPillboxFamily plane)
    {P : Type*} (source : plane.BoundaryField P ℝ)
    (parameter : P) (x : plane.carrier) (scale : ℕ) : ℝ :=
  normalizedSquareAverage (pillbox.radius scale) fun u v ↦
    source parameter
      (plane.tangentPoint x
        (u • pillbox.tangent + v • plane.quarterTurnTangent pillbox.tangent))

/-- The normalized outward flux through the four lateral faces of a pillbox.

The first pair has outward normals `±tangent`; the second has outward normals
`±(normalVector cross tangent)`. Each cross-interface face is split at the carrier into one
negative-side and one positive-side integral. -/
def lateralFaceAverage {plane : OrientedAffineHyperplane 3}
    (pillbox : PlanarPillboxFamily plane)
    {P : Type*} (field : plane.TwoSidedField P (EuclideanSpace ℝ (Fin 3)))
    (parameter : P) (x : plane.carrier) (scale : ℕ) : ℝ :=
  let radius := pillbox.radius scale
  let thickness := pillbox.halfThickness scale
  let tangent := (pillbox.tangent : EuclideanSpace ℝ (Fin 3))
  let quarterTurn :=
    (plane.quarterTurnTangent pillbox.tangent : EuclideanSpace ℝ (Fin 3))
  let splitFlux (offset : plane.tangentSubmodule)
      (normal : EuclideanSpace ℝ (Fin 3)) :=
    splitNormalIntegral thickness
      (fun w ↦ inner ℝ
        (plane.negativeSideSample field.negative parameter x offset w) normal)
      (fun w ↦ inner ℝ
        (plane.positiveSideSample field.positive parameter x offset w) normal)
  ((2 * radius) ^ 2)⁻¹ *
    (((∫ v in -radius..radius,
          splitFlux
            (radius • pillbox.tangent + v • plane.quarterTurnTangent pillbox.tangent)
            tangent) -
        ∫ v in -radius..radius,
          splitFlux
            (-(radius) • pillbox.tangent + v • plane.quarterTurnTangent pillbox.tangent)
            tangent) +
      (∫ u in -radius..radius,
          splitFlux
            (u • pillbox.tangent + radius • plane.quarterTurnTangent pillbox.tangent)
            quarterTurn) -
        ∫ u in -radius..radius,
          splitFlux
            (u • pillbox.tangent + -(radius) • plane.quarterTurnTangent pillbox.tangent)
            quarterTurn)

/-- The normalized integral of a two-sided scalar density over the pillbox volume. -/
def volumeAverage {plane : OrientedAffineHyperplane 3}
    (pillbox : PlanarPillboxFamily plane) {P : Type*}
    (density : plane.TwoSidedField P ℝ) (parameter : P)
    (x : plane.carrier) (scale : ℕ) : ℝ :=
  ((2 * pillbox.radius scale) ^ 2)⁻¹ *
    ∫ u in -pillbox.radius scale..pillbox.radius scale,
      ∫ v in -pillbox.radius scale..pillbox.radius scale,
        splitNormalIntegral (pillbox.halfThickness scale)
          (plane.negativeSideSample density.negative parameter x
            (u • pillbox.tangent + v • plane.quarterTurnTangent pillbox.tangent))
          (plane.positiveSideSample density.positive parameter x
            (u • pillbox.tangent + v • plane.quarterTurnTangent pillbox.tangent))

/-- Integrability of both levels of one selected-side principal-face pullback. -/
def SideFaceIntegrable {plane : OrientedAffineHyperplane 3}
    (pillbox : PlanarPillboxFamily plane) (side : OrientedAffineHyperplane.Side)
    {P : Type*} (field : plane.SideField side P (EuclideanSpace ℝ (Fin 3)))
    (parameter : P) (x : plane.carrier) (scale : ℕ) : Prop :=
  IteratedSquareIntegrable (pillbox.radius scale) fun u v ↦
    inner ℝ plane.normalVector
      (field parameter
        (plane.sidePoint side x
          (u • pillbox.tangent + v • plane.quarterTurnTangent pillbox.tangent)
          (pillbox.halfThickness scale) (pillbox.halfThickness_pos scale)))

/-- Integrability of both levels of a boundary-face surface-charge pullback. -/
def SurfaceFaceIntegrable {plane : OrientedAffineHyperplane 3}
    (pillbox : PlanarPillboxFamily plane) {P : Type*}
    (source : plane.BoundaryField P ℝ) (parameter : P)
    (x : plane.carrier) (scale : ℕ) : Prop :=
  IteratedSquareIntegrable (pillbox.radius scale) fun u v ↦
    source parameter
      (plane.tangentPoint x
        (u • pillbox.tangent + v • plane.quarterTurnTangent pillbox.tangent))

/-- Integrability of every split pullback on the four lateral pillbox faces. -/
def LateralFacesIntegrable {plane : OrientedAffineHyperplane 3}
    (pillbox : PlanarPillboxFamily plane)
    {P : Type*} (field : plane.TwoSidedField P (EuclideanSpace ℝ (Fin 3)))
    (parameter : P) (x : plane.carrier) (scale : ℕ) : Prop :=
  let radius := pillbox.radius scale
  let thickness := pillbox.halfThickness scale
  let tangent := (pillbox.tangent : EuclideanSpace ℝ (Fin 3))
  let quarterTurn :=
    (plane.quarterTurnTangent pillbox.tangent : EuclideanSpace ℝ (Fin 3))
  let splitFace (offset : ℝ → plane.tangentSubmodule)
      (normal : EuclideanSpace ℝ (Fin 3)) :=
    SplitRectangleIntegrable radius thickness
      (fun u w ↦ inner ℝ
        (plane.negativeSideSample field.negative parameter x (offset u) w) normal)
      (fun u w ↦ inner ℝ
        (plane.positiveSideSample field.positive parameter x (offset u) w) normal)
  splitFace
      (fun v ↦ radius • pillbox.tangent +
        v • plane.quarterTurnTangent pillbox.tangent) tangent ∧
    splitFace
      (fun v ↦ -(radius) • pillbox.tangent +
        v • plane.quarterTurnTangent pillbox.tangent) tangent ∧
    splitFace
      (fun u ↦ u • pillbox.tangent +
        radius • plane.quarterTurnTangent pillbox.tangent) quarterTurn ∧
    splitFace
      (fun u ↦ u • pillbox.tangent +
        -(radius) • plane.quarterTurnTangent pillbox.tangent) quarterTurn

/-- Integrability of every level of a split two-sided pillbox-volume pullback. -/
def VolumeIntegrable {plane : OrientedAffineHyperplane 3}
    (pillbox : PlanarPillboxFamily plane) {P : Type*}
    (density : plane.TwoSidedField P ℝ) (parameter : P)
    (x : plane.carrier) (scale : ℕ) : Prop :=
  SplitBoxIntegrable (pillbox.radius scale) (pillbox.halfThickness scale)
    (fun u v w ↦ plane.negativeSideSample density.negative parameter x
      (u • pillbox.tangent + v • plane.quarterTurnTangent pillbox.tangent) w)
    (fun u v w ↦ plane.positiveSideSample density.positive parameter x
      (u • pillbox.tangent + v • plane.quarterTurnTangent pillbox.tangent) w)

end PlanarPillboxFamily

end
end Space
