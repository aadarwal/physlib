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

end OrientedAffineHyperplane

end

end Space
