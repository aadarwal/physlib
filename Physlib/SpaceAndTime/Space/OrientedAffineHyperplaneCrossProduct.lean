/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.SpaceAndTime.Space.CrossProduct
public import Physlib.SpaceAndTime.Space.OrientedAffineHyperplane

/-!
# Cross products with oriented affine hyperplane geometry

## i. Overview

This file connects three-dimensional cross products to the dimension-generic oriented affine
hyperplane API. Crossing first by the stored normal discards the normal part of a vector, so it is
unchanged by tangential projection or reflection across the tangent plane.

## ii. Key results

- `OrientedAffineHyperplane.normalVector_cross_tangentialProjection`: normal crossing depends only
  on the tangential projection.
- `OrientedAffineHyperplane.normalVector_cross_vectorReflection`: tangent-plane reflection
  preserves normal crossing.
- `OrientedAffineHyperplane.norm_normalVector_cross_of_isTangent`: crossing a
  tangent vector by the unit normal preserves its norm.
- `OrientedAffineHyperplane.normalVector_cross_normalize_normalVector_cross`: the normalized
  normal cross tangent axis has the expected in-plane quarter-turn.

## iii. Table of contents

- A. Normal cross products

## iv. References

These results combine Physlib's independently implemented cross-product and oriented-hyperplane
APIs. No external formal-development source is copied or translated here.
-/

@[expose] public section

namespace Space

open Matrix

noncomputable section

namespace OrientedAffineHyperplane

/-!

## A. Normal cross products

-/

/-- Crossing first by the oriented normal discards a vector's normal component. -/
lemma normalVector_cross_tangentialProjection
    (plane : OrientedAffineHyperplane 3) (v : EuclideanSpace ℝ (Fin 3)) :
    plane.normalVector ⨯ₑ₃ plane.tangentialProjection v = plane.normalVector ⨯ₑ₃ v := by
  rw [OrientedAffineHyperplane.tangentialProjection]
  ext i
  fin_cases i <;>
    simp [crossProduct, OrientedAffineHyperplane.normalVector] <;>
    ring

/-- Reflection across the tangent plane preserves crossing first by the oriented normal. -/
lemma normalVector_cross_vectorReflection
    (plane : OrientedAffineHyperplane 3) (v : EuclideanSpace ℝ (Fin 3)) :
    plane.normalVector ⨯ₑ₃ plane.vectorReflection v = plane.normalVector ⨯ₑ₃ v := by
  rw [← plane.normalVector_cross_tangentialProjection (plane.vectorReflection v),
    plane.tangentialProjection_vectorReflection,
    plane.normalVector_cross_tangentialProjection]

/-- Crossing a tangent vector by the oriented unit normal preserves its Euclidean norm. -/
lemma norm_normalVector_cross_of_isTangent
    (plane : OrientedAffineHyperplane 3) (v : EuclideanSpace ℝ (Fin 3))
    (hTangent : plane.IsTangent v) :
    ‖plane.normalVector ⨯ₑ₃ v‖ = ‖v‖ := by
  change inner ℝ plane.normalVector v = 0 at hTangent
  have hSquare : ‖plane.normalVector ⨯ₑ₃ v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, Space.inner_cross_cross,
      plane.inner_normalVector_self, real_inner_self_eq_norm_sq]
    simp [hTangent]
  nlinarith [norm_nonneg (plane.normalVector ⨯ₑ₃ v), norm_nonneg v]

/-- Crossing the normal with the normalized `normal × tangent` axis gives the negative
normalized tangent direction. -/
lemma normalVector_cross_normalize_normalVector_cross
    (plane : OrientedAffineHyperplane 3) (v : EuclideanSpace ℝ (Fin 3))
    (hTangent : plane.IsTangent v) :
    plane.normalVector ⨯ₑ₃ NormedSpace.normalize (plane.normalVector ⨯ₑ₃ v) =
      -NormedSpace.normalize v := by
  change inner ℝ plane.normalVector v = 0 at hTangent
  rw [NormedSpace.normalize, NormedSpace.normalize, Space.cross_smul,
    plane.norm_normalVector_cross_of_isTangent v hTangent,
    Space.cross_cross_eq_smul_sub_smul', hTangent,
    plane.inner_normalVector_self]
  simp

/-- Crossing a nonzero tangent vector with the normalized `normal × tangent` axis gives its
norm times the oriented normal. -/
lemma tangent_cross_normalize_normalVector_cross
    (plane : OrientedAffineHyperplane 3) (v : EuclideanSpace ℝ (Fin 3))
    (hv : v ≠ 0) (hTangent : plane.IsTangent v) :
    v ⨯ₑ₃ NormedSpace.normalize (plane.normalVector ⨯ₑ₃ v) =
      ‖v‖ • plane.normalVector := by
  change inner ℝ plane.normalVector v = 0 at hTangent
  rw [NormedSpace.normalize, Space.cross_smul,
    plane.norm_normalVector_cross_of_isTangent v hTangent,
    Space.cross_cross_eq_smul_sub_smul', real_inner_self_eq_norm_sq,
    hTangent, zero_smul, sub_zero, smul_smul]
  congr 1
  field_simp [norm_ne_zero_iff.mpr hv]

end OrientedAffineHyperplane

end

end Space
