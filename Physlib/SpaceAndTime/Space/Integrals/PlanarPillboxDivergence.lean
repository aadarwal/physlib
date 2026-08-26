/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.SpaceAndTime.Space.Integrals.AffineSplitBoxDivergence
public import Physlib.SpaceAndTime.Space.Integrals.PlanarThinCell

/-!
# Local divergence identities on planar pillboxes

## i. Overview

This file specializes the local split affine-box divergence theorem to the oriented orthonormal
frame carried by a `PlanarPillboxFamily`. Two independent ambient fields are restricted to the
negative and positive open half-spaces. Their values at the carrier are retained only by the
explicit carrier-face term; the open-side samples remain zero-totalized at the shared endpoint,
whose value does not affect an interval integral.

The resulting identity has exactly the normalized principal- and lateral-face terms used by the
thin-cell API. It is neutral calculus: it does not state a Maxwell equation, identify the carrier
jump with a surface charge, assert a pointwise jump, or take a shrinking-pillbox limit.

## ii. Key results

- `PlanarPillboxFamily.AmbientHalfLateralIntegrable`: integrability of the four ambient half-face
  fluxes needed to regroup negative- and positive-side integrals.
- `PlanarPillboxFamily.DivergenceRegularity`: local split-box regularity and half-face
  integrability for one pillbox.
- `PlanarPillboxFamily.flux_eq_normalized_bulkDivergence_add_carrierJump`: the normalized
  split-pillbox divergence identity.

## iii. Table of contents

- A. Pillbox frame geometry
- B. Ambient half-face integrability
- C. Open-side integral bridges
- D. Normalized split-pillbox divergence

## iv. References

This is neutral calculus infrastructure for the E4b finite-sheet premise.
-/

@[expose] public section

open Matrix MeasureTheory
open scoped Interval

namespace Space

noncomputable section

namespace PlanarPillboxFamily

/-! ## A. Pillbox frame geometry -/

/-- The pillbox tangent, regarded as a direction in the affine-box parameterization. -/
def tangentDirection {plane : OrientedAffineHyperplane 3}
    (pillbox : PlanarPillboxFamily plane) : Space :=
  basis.repr.symm (pillbox.tangent : EuclideanSpace ℝ (Fin 3))

/-- The oriented in-plane quarter-turn, regarded as an affine-box direction. -/
def quarterTurnDirection {plane : OrientedAffineHyperplane 3}
    (pillbox : PlanarPillboxFamily plane) : Space :=
  basis.repr.symm
    (plane.quarterTurnTangent pillbox.tangent : EuclideanSpace ℝ (Fin 3))

/-- The plane's negative-to-positive normal, regarded as an affine-box direction. -/
def normalDirection {plane : OrientedAffineHyperplane 3}
    (_pillbox : PlanarPillboxFamily plane) : Space :=
  basis.repr.symm plane.normalVector

/-- The pillbox affine frame parameterizes the same point as a tangential offset followed by a
signed normal offset. -/
lemma affineBoxPoint_eq_normalOffsetPoint {plane : OrientedAffineHyperplane 3}
    (pillbox : PlanarPillboxFamily plane) (x : plane.carrier) (u v w : ℝ) :
    affineBoxPoint (x : Space) pillbox.tangentDirection pillbox.quarterTurnDirection
        pillbox.normalDirection u v w =
      plane.normalOffsetPoint x
        (u • pillbox.tangent + v • plane.quarterTurnTangent pillbox.tangent) w := by
  ext i
  simp [affineBoxPoint, tangentDirection, quarterTurnDirection, normalDirection,
    OrientedAffineHyperplane.normalOffsetPoint, basis_repr_symm_apply]
  ring

/-- The positive selected-side point is the positive signed normal-offset point. -/
lemma positiveSidePoint_eq_normalOffsetPoint {plane : OrientedAffineHyperplane 3}
    (x : plane.carrier) (offset : plane.tangentSubmodule) (height : ℝ)
    (hheight : 0 < height) :
    (plane.sidePoint .positive x offset height hheight : Space) =
      plane.normalOffsetPoint x offset height := by
  ext i
  simp [OrientedAffineHyperplane.sidePoint,
    OrientedAffineHyperplane.normalOffsetPoint]

/-- The negative selected-side point is the negative signed normal-offset point. -/
lemma negativeSidePoint_eq_normalOffsetPoint {plane : OrientedAffineHyperplane 3}
    (x : plane.carrier) (offset : plane.tangentSubmodule) (height : ℝ)
    (hheight : 0 < height) :
    (plane.sidePoint .negative x offset height hheight : Space) =
      plane.normalOffsetPoint x offset (-height) := by
  ext i
  simp [OrientedAffineHyperplane.sidePoint,
    OrientedAffineHyperplane.normalOffsetPoint]

/-- The quarter-turn crossed with the normal recovers the original tangent. -/
lemma quarterTurnTangent_cross_normalVector {plane : OrientedAffineHyperplane 3}
    (tangent : plane.tangentSubmodule) :
    (plane.quarterTurnTangent tangent : EuclideanSpace ℝ (Fin 3)) ⨯ₑ₃
        plane.normalVector = tangent := by
  change (plane.normalVector ⨯ₑ₃ (tangent : EuclideanSpace ℝ (Fin 3))) ⨯ₑ₃
      plane.normalVector = tangent
  rw [Space.cross_cross_eq_smul_sub_smul, plane.inner_normalVector_self, one_smul]
  have hTangent : inner ℝ (tangent : EuclideanSpace ℝ (Fin 3))
      plane.normalVector = 0 := by
    rw [real_inner_comm]
    exact (plane.mem_tangentSubmodule tangent).mp tangent.property
  rw [hTangent, zero_smul, sub_zero]

/-- The first affine-box face cofactor is the pillbox tangent. -/
lemma firstFaceNormal {plane : OrientedAffineHyperplane 3}
    (pillbox : PlanarPillboxFamily plane) :
    basis.repr pillbox.quarterTurnDirection ⨯ₑ₃ basis.repr pillbox.normalDirection =
      pillbox.tangent := by
  change (plane.quarterTurnTangent pillbox.tangent : EuclideanSpace ℝ (Fin 3)) ⨯ₑ₃
    plane.normalVector = pillbox.tangent
  exact quarterTurnTangent_cross_normalVector pillbox.tangent

/-- The second affine-box face cofactor is the oriented quarter-turn. -/
lemma secondFaceNormal {plane : OrientedAffineHyperplane 3}
    (pillbox : PlanarPillboxFamily plane) :
    basis.repr pillbox.normalDirection ⨯ₑ₃ basis.repr pillbox.tangentDirection =
      plane.quarterTurnTangent pillbox.tangent := by
  rfl

/-- The principal affine-box face cofactor is the stored plane normal. -/
lemma principalFaceNormal {plane : OrientedAffineHyperplane 3}
    (pillbox : PlanarPillboxFamily plane) :
    basis.repr pillbox.tangentDirection ⨯ₑ₃
        basis.repr pillbox.quarterTurnDirection = plane.normalVector := by
  change (pillbox.tangent : EuclideanSpace ℝ (Fin 3)) ⨯ₑ₃
    (plane.quarterTurnTangent pillbox.tangent : EuclideanSpace ℝ (Fin 3)) =
      plane.normalVector
  exact plane.tangent_cross_quarterTurnTangent_of_norm_eq_one
    pillbox.tangent pillbox.tangent_norm

/-! ## B. Ambient half-face integrability -/

/-- Outer-variable integrability of the four lateral half-face fluxes of one ambient field.

The normal interval `[lower, upper]` selects one closed half of the pillbox. These hypotheses are
exactly what is needed to distribute an outer interval integral over the negative-plus-positive
split; they make no assertion about Maxwell equations or the carrier value. -/
structure AmbientHalfLateralIntegrable {plane : OrientedAffineHyperplane 3}
    (pillbox : PlanarPillboxFamily plane) {P : Type*}
    (field : P → Space → EuclideanSpace ℝ (Fin 3))
    (parameter : P) (x : plane.carrier) (scale : ℕ)
    (lower upper : ℝ) : Prop where
  /-- Integrability of the positive-tangent lateral half-face flux. -/
  firstUpper : IntervalIntegrable
    (fun v ↦ ∫ w in lower..upper,
      inner ℝ (field parameter (plane.normalOffsetPoint x
        (pillbox.radius scale • pillbox.tangent +
          v • plane.quarterTurnTangent pillbox.tangent) w))
        (pillbox.tangent : EuclideanSpace ℝ (Fin 3)))
    volume (-pillbox.radius scale) (pillbox.radius scale)
  /-- Integrability of the negative-tangent lateral half-face flux. -/
  firstLower : IntervalIntegrable
    (fun v ↦ ∫ w in lower..upper,
      inner ℝ (field parameter (plane.normalOffsetPoint x
        (-(pillbox.radius scale) • pillbox.tangent +
          v • plane.quarterTurnTangent pillbox.tangent) w))
        (pillbox.tangent : EuclideanSpace ℝ (Fin 3)))
    volume (-pillbox.radius scale) (pillbox.radius scale)
  /-- Integrability of the positive-quarter-turn lateral half-face flux. -/
  secondUpper : IntervalIntegrable
    (fun u ↦ ∫ w in lower..upper,
      inner ℝ (field parameter (plane.normalOffsetPoint x
        (u • pillbox.tangent +
          pillbox.radius scale • plane.quarterTurnTangent pillbox.tangent) w))
        (plane.quarterTurnTangent pillbox.tangent : EuclideanSpace ℝ (Fin 3)))
    volume (-pillbox.radius scale) (pillbox.radius scale)
  /-- Integrability of the negative-quarter-turn lateral half-face flux. -/
  secondLower : IntervalIntegrable
    (fun u ↦ ∫ w in lower..upper,
      inner ℝ (field parameter (plane.normalOffsetPoint x
        (u • pillbox.tangent +
          -(pillbox.radius scale) • plane.quarterTurnTangent pillbox.tangent) w))
        (plane.quarterTurnTangent pillbox.tangent : EuclideanSpace ℝ (Fin 3)))
    volume (-pillbox.radius scale) (pillbox.radius scale)

/-- Local split-box regularity and the half-face integrability needed to express its outer flux
through `PlanarPillboxFamily.lateralFaceAverage`. -/
structure DivergenceRegularity {plane : OrientedAffineHyperplane 3}
    (pillbox : PlanarPillboxFamily plane) {P : Type*}
    (negativeField positiveField : P → Space → EuclideanSpace ℝ (Fin 3))
    (parameter : P) (x : plane.carrier) (scale : ℕ)
    (negativeExceptionalSet positiveExceptionalSet : Set (Fin 3 → ℝ)) : Prop where
  /-- Local divergence regularity on the two closed half-boxes. -/
  calculus : AffineSplitBoxDivergenceRegularity
    (negativeField parameter) (positiveField parameter) (x : Space)
    pillbox.tangentDirection pillbox.quarterTurnDirection pillbox.normalDirection
    (pillbox.radius scale) (pillbox.halfThickness scale)
    negativeExceptionalSet positiveExceptionalSet
  /-- Integrability of the four negative-side lateral half-face fluxes. -/
  negativeLateral : AmbientHalfLateralIntegrable pillbox negativeField parameter x scale
    (-(pillbox.halfThickness scale)) 0
  /-- Integrability of the four positive-side lateral half-face fluxes. -/
  positiveLateral : AmbientHalfLateralIntegrable pillbox positiveField parameter x scale
    0 (pillbox.halfThickness scale)

/-! ## C. Open-side integral bridges -/

private lemma normalizedSquareAverage_eq_normalized_iteratedIntegral
    (radius : ℝ) (f : ℝ → ℝ → ℝ) :
    normalizedSquareAverage radius f =
      ((2 * radius) ^ 2)⁻¹ *
        ∫ u in -radius..radius, ∫ v in -radius..radius, f u v := by
  unfold normalizedSquareAverage normalizedIntervalAverage
  rw [intervalIntegral.integral_const_mul]
  ring

private lemma negativeSideSample_integral_eq_ambient
    {plane : OrientedAffineHyperplane 3} {P : Type*}
    (negativeField positiveField : P → Space → EuclideanSpace ℝ (Fin 3))
    (parameter : P) (x : plane.carrier) (offset : plane.tangentSubmodule)
    (normal : EuclideanSpace ℝ (Fin 3)) (halfThickness : ℝ)
    (hhalfThickness : 0 ≤ halfThickness) :
    (∫ w in -halfThickness..0,
      inner ℝ (plane.negativeSideSample
        (OrientedAffineHyperplane.TwoSidedField.ofFields plane
          negativeField positiveField).negative parameter x offset w) normal) =
      ∫ w in -halfThickness..0,
        inner ℝ (negativeField parameter
          (plane.normalOffsetPoint x offset w)) normal := by
  apply intervalIntegral.integral_congr_Ioo_of_le
    (neg_nonpos.mpr hhalfThickness)
  intro w hw
  simp [OrientedAffineHyperplane.negativeSideSample, hw.2,
    OrientedAffineHyperplane.TwoSidedField.ofFields,
    OrientedAffineHyperplane.restrictFieldToSide]

private lemma positiveSideSample_integral_eq_ambient
    {plane : OrientedAffineHyperplane 3} {P : Type*}
    (negativeField positiveField : P → Space → EuclideanSpace ℝ (Fin 3))
    (parameter : P) (x : plane.carrier) (offset : plane.tangentSubmodule)
    (normal : EuclideanSpace ℝ (Fin 3)) (halfThickness : ℝ)
    (hhalfThickness : 0 ≤ halfThickness) :
    (∫ w in 0..halfThickness,
      inner ℝ (plane.positiveSideSample
        (OrientedAffineHyperplane.TwoSidedField.ofFields plane
          negativeField positiveField).positive parameter x offset w) normal) =
      ∫ w in 0..halfThickness,
        inner ℝ (positiveField parameter
          (plane.normalOffsetPoint x offset w)) normal := by
  apply intervalIntegral.integral_congr_Ioo_of_le hhalfThickness
  intro w hw
  simp [OrientedAffineHyperplane.positiveSideSample, hw.1,
    OrientedAffineHyperplane.TwoSidedField.ofFields,
    OrientedAffineHyperplane.restrictFieldToSide]

private lemma outerSplitIntegral_eq_add
    {plane : OrientedAffineHyperplane 3} {P : Type*}
    (negativeField positiveField : P → Space → EuclideanSpace ℝ (Fin 3))
    (parameter : P) (x : plane.carrier) (offset : ℝ → plane.tangentSubmodule)
    (normal : EuclideanSpace ℝ (Fin 3)) (radius halfThickness : ℝ)
    (hhalfThickness : 0 ≤ halfThickness)
    (hnegative : IntervalIntegrable
      (fun u ↦ ∫ w in -halfThickness..0,
        inner ℝ (negativeField parameter
          (plane.normalOffsetPoint x (offset u) w)) normal)
      volume (-radius) radius)
    (hpositive : IntervalIntegrable
      (fun u ↦ ∫ w in 0..halfThickness,
        inner ℝ (positiveField parameter
          (plane.normalOffsetPoint x (offset u) w)) normal)
      volume (-radius) radius) :
    (∫ u in -radius..radius,
      splitNormalIntegral halfThickness
        (fun w ↦ inner ℝ (plane.negativeSideSample
          (OrientedAffineHyperplane.TwoSidedField.ofFields plane
            negativeField positiveField).negative parameter x (offset u) w) normal)
        (fun w ↦ inner ℝ (plane.positiveSideSample
          (OrientedAffineHyperplane.TwoSidedField.ofFields plane
            negativeField positiveField).positive parameter x (offset u) w) normal)) =
      (∫ u in -radius..radius, ∫ w in -halfThickness..0,
        inner ℝ (negativeField parameter
          (plane.normalOffsetPoint x (offset u) w)) normal) +
      ∫ u in -radius..radius, ∫ w in 0..halfThickness,
        inner ℝ (positiveField parameter
          (plane.normalOffsetPoint x (offset u) w)) normal := by
  calc
    _ = ∫ u in -radius..radius,
        (∫ w in -halfThickness..0,
          inner ℝ (negativeField parameter
            (plane.normalOffsetPoint x (offset u) w)) normal) +
        ∫ w in 0..halfThickness,
          inner ℝ (positiveField parameter
            (plane.normalOffsetPoint x (offset u) w)) normal := by
      apply intervalIntegral.integral_congr
      intro u _
      change splitNormalIntegral halfThickness
          (fun w ↦ inner ℝ (plane.negativeSideSample
            (OrientedAffineHyperplane.TwoSidedField.ofFields plane
              negativeField positiveField).negative parameter x (offset u) w) normal)
          (fun w ↦ inner ℝ (plane.positiveSideSample
            (OrientedAffineHyperplane.TwoSidedField.ofFields plane
              negativeField positiveField).positive parameter x (offset u) w) normal) =
        (∫ w in -halfThickness..0,
          inner ℝ (negativeField parameter
            (plane.normalOffsetPoint x (offset u) w)) normal) +
        ∫ w in 0..halfThickness,
          inner ℝ (positiveField parameter
            (plane.normalOffsetPoint x (offset u) w)) normal
      unfold splitNormalIntegral
      rw [negativeSideSample_integral_eq_ambient negativeField positiveField
          parameter x (offset u) normal halfThickness hhalfThickness,
        positiveSideSample_integral_eq_ambient negativeField positiveField
          parameter x (offset u) normal halfThickness hhalfThickness]
    _ = _ := intervalIntegral.integral_add hnegative hpositive

private lemma outerSplitIntegral_eq_affine
    {plane : OrientedAffineHyperplane 3} {P : Type*}
    (negativeField positiveField : P → Space → EuclideanSpace ℝ (Fin 3))
    (parameter : P) (x : plane.carrier) (offset : ℝ → plane.tangentSubmodule)
    (normal : EuclideanSpace ℝ (Fin 3)) (point : ℝ → ℝ → Space)
    (cofactor : EuclideanSpace ℝ (Fin 3)) (radius halfThickness : ℝ)
    (hhalfThickness : 0 ≤ halfThickness)
    (hpoint : ∀ u w, plane.normalOffsetPoint x (offset u) w = point u w)
    (hnormal : normal = cofactor)
    (hnegative : IntervalIntegrable
      (fun u ↦ ∫ w in -halfThickness..0,
        inner ℝ (negativeField parameter
          (plane.normalOffsetPoint x (offset u) w)) normal)
      volume (-radius) radius)
    (hpositive : IntervalIntegrable
      (fun u ↦ ∫ w in 0..halfThickness,
        inner ℝ (positiveField parameter
          (plane.normalOffsetPoint x (offset u) w)) normal)
      volume (-radius) radius) :
    (∫ u in -radius..radius,
      splitNormalIntegral halfThickness
        (fun w ↦ inner ℝ (plane.negativeSideSample
          (OrientedAffineHyperplane.TwoSidedField.ofFields plane
            negativeField positiveField).negative parameter x (offset u) w) normal)
        (fun w ↦ inner ℝ (plane.positiveSideSample
          (OrientedAffineHyperplane.TwoSidedField.ofFields plane
            negativeField positiveField).positive parameter x (offset u) w) normal)) =
      (∫ u in -radius..radius, ∫ w in -halfThickness..0,
        inner ℝ (negativeField parameter (point u w)) cofactor) +
      ∫ u in -radius..radius, ∫ w in 0..halfThickness,
        inner ℝ (positiveField parameter (point u w)) cofactor := by
  simpa only [hpoint, hnormal] using
    outerSplitIntegral_eq_add negativeField positiveField parameter x offset normal
      radius halfThickness hhalfThickness hnegative hpositive

private lemma positiveSideFaceAverage_eq
    {plane : OrientedAffineHyperplane 3} (pillbox : PlanarPillboxFamily plane)
    {P : Type*} (positiveField : P → Space → EuclideanSpace ℝ (Fin 3))
    (parameter : P) (x : plane.carrier) (scale : ℕ) :
    pillbox.sideFaceAverage .positive
        (plane.restrictFieldToSide .positive positiveField) parameter x scale =
      ((2 * pillbox.radius scale) ^ 2)⁻¹ *
        ∫ u in -pillbox.radius scale..pillbox.radius scale,
          ∫ v in -pillbox.radius scale..pillbox.radius scale,
            inner ℝ (positiveField parameter
              (affineBoxPoint (x : Space) pillbox.tangentDirection
                pillbox.quarterTurnDirection pillbox.normalDirection u v
                (pillbox.halfThickness scale))) plane.normalVector := by
  rw [PlanarPillboxFamily.sideFaceAverage,
    normalizedSquareAverage_eq_normalized_iteratedIntegral]
  apply congrArg (((2 * pillbox.radius scale) ^ 2)⁻¹ * ·)
  apply intervalIntegral.integral_congr
  intro u _
  apply intervalIntegral.integral_congr
  intro v _
  change inner ℝ plane.normalVector
      (positiveField parameter (plane.sidePoint .positive x
        (u • pillbox.tangent + v • plane.quarterTurnTangent pillbox.tangent)
        (pillbox.halfThickness scale) (pillbox.halfThickness_pos scale))) =
    inner ℝ (positiveField parameter
      (affineBoxPoint (x : Space) pillbox.tangentDirection
        pillbox.quarterTurnDirection pillbox.normalDirection u v
        (pillbox.halfThickness scale))) plane.normalVector
  rw [real_inner_comm, pillbox.affineBoxPoint_eq_normalOffsetPoint,
    positiveSidePoint_eq_normalOffsetPoint]

private lemma negativeSideFaceAverage_eq
    {plane : OrientedAffineHyperplane 3} (pillbox : PlanarPillboxFamily plane)
    {P : Type*} (negativeField : P → Space → EuclideanSpace ℝ (Fin 3))
    (parameter : P) (x : plane.carrier) (scale : ℕ) :
    pillbox.sideFaceAverage .negative
        (plane.restrictFieldToSide .negative negativeField) parameter x scale =
      ((2 * pillbox.radius scale) ^ 2)⁻¹ *
        ∫ u in -pillbox.radius scale..pillbox.radius scale,
          ∫ v in -pillbox.radius scale..pillbox.radius scale,
            inner ℝ (negativeField parameter
              (affineBoxPoint (x : Space) pillbox.tangentDirection
                pillbox.quarterTurnDirection pillbox.normalDirection u v
                (-(pillbox.halfThickness scale)))) plane.normalVector := by
  rw [PlanarPillboxFamily.sideFaceAverage,
    normalizedSquareAverage_eq_normalized_iteratedIntegral]
  apply congrArg (((2 * pillbox.radius scale) ^ 2)⁻¹ * ·)
  apply intervalIntegral.integral_congr
  intro u _
  apply intervalIntegral.integral_congr
  intro v _
  change inner ℝ plane.normalVector
      (negativeField parameter (plane.sidePoint .negative x
        (u • pillbox.tangent + v • plane.quarterTurnTangent pillbox.tangent)
        (pillbox.halfThickness scale) (pillbox.halfThickness_pos scale))) =
    inner ℝ (negativeField parameter
      (affineBoxPoint (x : Space) pillbox.tangentDirection
        pillbox.quarterTurnDirection pillbox.normalDirection u v
        (-(pillbox.halfThickness scale)))) plane.normalVector
  rw [real_inner_comm, pillbox.affineBoxPoint_eq_normalOffsetPoint,
    negativeSidePoint_eq_normalOffsetPoint]

private lemma lateralFaceAverage_eq_normalized_affineSplitBoxLateralFlux
    {plane : OrientedAffineHyperplane 3} (pillbox : PlanarPillboxFamily plane)
    {P : Type*}
    (negativeField positiveField : P → Space → EuclideanSpace ℝ (Fin 3))
    (parameter : P) (x : plane.carrier) (scale : ℕ)
    (negativeIntegrable : AmbientHalfLateralIntegrable pillbox negativeField
      parameter x scale (-(pillbox.halfThickness scale)) 0)
    (positiveIntegrable : AmbientHalfLateralIntegrable pillbox positiveField
      parameter x scale 0 (pillbox.halfThickness scale)) :
    pillbox.lateralFaceAverage
        (OrientedAffineHyperplane.TwoSidedField.ofFields plane
          negativeField positiveField) parameter x scale =
      ((2 * pillbox.radius scale) ^ 2)⁻¹ *
        affineSplitBoxLateralFlux (negativeField parameter) (positiveField parameter)
          (x : Space) pillbox.tangentDirection pillbox.quarterTurnDirection
          pillbox.normalDirection (pillbox.radius scale) (pillbox.halfThickness scale) := by
  let radius := pillbox.radius scale
  let thickness := pillbox.halfThickness scale
  let tangent := (pillbox.tangent : EuclideanSpace ℝ (Fin 3))
  let quarterTurn :=
    (plane.quarterTurnTangent pillbox.tangent : EuclideanSpace ℝ (Fin 3))
  have hFirstUpper := outerSplitIntegral_eq_affine negativeField positiveField
    parameter x
    (fun v ↦ radius • pillbox.tangent + v • plane.quarterTurnTangent pillbox.tangent)
    tangent
    (fun v w ↦ affineBoxPoint (x : Space) pillbox.tangentDirection
      pillbox.quarterTurnDirection pillbox.normalDirection radius v w)
    (basis.repr pillbox.quarterTurnDirection ⨯ₑ₃ basis.repr pillbox.normalDirection)
    radius thickness (pillbox.halfThickness_pos scale).le
    (fun v w ↦ (pillbox.affineBoxPoint_eq_normalOffsetPoint x radius v w).symm)
    pillbox.firstFaceNormal.symm negativeIntegrable.firstUpper positiveIntegrable.firstUpper
  have hFirstLower := outerSplitIntegral_eq_affine negativeField positiveField
    parameter x
    (fun v ↦ -radius • pillbox.tangent + v • plane.quarterTurnTangent pillbox.tangent)
    tangent
    (fun v w ↦ affineBoxPoint (x : Space) pillbox.tangentDirection
      pillbox.quarterTurnDirection pillbox.normalDirection (-radius) v w)
    (basis.repr pillbox.quarterTurnDirection ⨯ₑ₃ basis.repr pillbox.normalDirection)
    radius thickness (pillbox.halfThickness_pos scale).le
    (fun v w ↦ (pillbox.affineBoxPoint_eq_normalOffsetPoint x (-radius) v w).symm)
    pillbox.firstFaceNormal.symm negativeIntegrable.firstLower positiveIntegrable.firstLower
  have hSecondUpper := outerSplitIntegral_eq_affine negativeField positiveField
    parameter x
    (fun u ↦ u • pillbox.tangent + radius • plane.quarterTurnTangent pillbox.tangent)
    quarterTurn
    (fun u w ↦ affineBoxPoint (x : Space) pillbox.tangentDirection
      pillbox.quarterTurnDirection pillbox.normalDirection u radius w)
    (basis.repr pillbox.normalDirection ⨯ₑ₃ basis.repr pillbox.tangentDirection)
    radius thickness (pillbox.halfThickness_pos scale).le
    (fun u w ↦ (pillbox.affineBoxPoint_eq_normalOffsetPoint x u radius w).symm)
    pillbox.secondFaceNormal.symm negativeIntegrable.secondUpper
    positiveIntegrable.secondUpper
  have hSecondLower := outerSplitIntegral_eq_affine negativeField positiveField
    parameter x
    (fun u ↦ u • pillbox.tangent + -radius • plane.quarterTurnTangent pillbox.tangent)
    quarterTurn
    (fun u w ↦ affineBoxPoint (x : Space) pillbox.tangentDirection
      pillbox.quarterTurnDirection pillbox.normalDirection u (-radius) w)
    (basis.repr pillbox.normalDirection ⨯ₑ₃ basis.repr pillbox.tangentDirection)
    radius thickness (pillbox.halfThickness_pos scale).le
    (fun u w ↦ (pillbox.affineBoxPoint_eq_normalOffsetPoint x u (-radius) w).symm)
    pillbox.secondFaceNormal.symm negativeIntegrable.secondLower
    positiveIntegrable.secondLower
  unfold PlanarPillboxFamily.lateralFaceAverage affineSplitBoxLateralFlux
  dsimp only
  rw [hFirstUpper, hFirstLower, hSecondUpper, hSecondLower]
  ring

/-! ## D. Normalized split-pillbox divergence -/

/-- The normalized principal-plus-lateral pillbox flux equals the normalized sum of bulk
divergence and the retained positive-minus-negative carrier-face flux.

The open-side field in the displayed lateral term is obtained by restricting the two ambient
fields. No carrier value is assigned to either open-side field. -/
lemma flux_eq_normalized_bulkDivergence_add_carrierJump
    {plane : OrientedAffineHyperplane 3} (pillbox : PlanarPillboxFamily plane)
    {P : Type*}
    (negativeField positiveField : P → Space → EuclideanSpace ℝ (Fin 3))
    (parameter : P) (x : plane.carrier) (scale : ℕ)
    (negativeExceptionalSet positiveExceptionalSet : Set (Fin 3 → ℝ))
    (regularity : DivergenceRegularity pillbox negativeField positiveField
      parameter x scale negativeExceptionalSet positiveExceptionalSet) :
    pillbox.sideFaceAverage .positive
          (plane.restrictFieldToSide .positive positiveField) parameter x scale -
        pillbox.sideFaceAverage .negative
          (plane.restrictFieldToSide .negative negativeField) parameter x scale +
        pillbox.lateralFaceAverage
          (OrientedAffineHyperplane.TwoSidedField.ofFields plane
            negativeField positiveField) parameter x scale =
      ((2 * pillbox.radius scale) ^ 2)⁻¹ *
        (affineSplitBoxBulkDivergence (negativeField parameter) (positiveField parameter)
            (x : Space) pillbox.tangentDirection pillbox.quarterTurnDirection
            pillbox.normalDirection (pillbox.radius scale) (pillbox.halfThickness scale) +
          affineSplitBoxCarrierJump (negativeField parameter) (positiveField parameter)
            (x : Space) pillbox.tangentDirection pillbox.quarterTurnDirection
            pillbox.normalDirection (pillbox.radius scale)) := by
  rw [positiveSideFaceAverage_eq pillbox positiveField parameter x scale,
    negativeSideFaceAverage_eq pillbox negativeField parameter x scale,
    lateralFaceAverage_eq_normalized_affineSplitBoxLateralFlux pillbox
      negativeField positiveField parameter x scale
      regularity.negativeLateral regularity.positiveLateral]
  have hDivergence :=
    affineSplitBoxOuterFlux_eq_bulkDivergence_add_carrierJump
      (negativeField parameter) (positiveField parameter) (x : Space)
      pillbox.tangentDirection pillbox.quarterTurnDirection pillbox.normalDirection
      (pillbox.radius scale) (pillbox.halfThickness scale)
      (pillbox.radius_pos scale).le (pillbox.halfThickness_pos scale).le
      negativeExceptionalSet positiveExceptionalSet regularity.calculus
  unfold affineSplitBoxOuterFlux affineSplitBoxPrincipalFlux at hDivergence
  rw [pillbox.principalFaceNormal] at hDivergence
  rw [← hDivergence]
  ring

end PlanarPillboxFamily

end
end Space
