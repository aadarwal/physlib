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
- `OrientedAffineHyperplane.normalVector_cross_eq_of_tangent_pairings`: oriented tangent
  pairings determine a normal cross product.

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

/-- Oriented tangent pairings determine the cross product of a vector jump with the stored normal.

The hypothesis is the scalar form produced by an Ampere thin loop directed along `tangent`: the
field jump pairs with the loop direction exactly as the tangent surface current pairs with the
oriented spanning-surface normal `normalVector cross tangent`. -/
lemma normalVector_cross_eq_of_tangent_pairings
    (plane : OrientedAffineHyperplane 3)
    (fieldJump surfaceCurrent : EuclideanSpace ℝ (Fin 3))
    (hCurrent : plane.IsTangent surfaceCurrent)
    (hPairing : ∀ tangent : plane.tangentSubmodule,
      inner ℝ fieldJump (tangent : EuclideanSpace ℝ (Fin 3)) =
        inner ℝ surfaceCurrent
          (plane.normalVector ⨯ₑ₃ (tangent : EuclideanSpace ℝ (Fin 3)))) :
    plane.normalVector ⨯ₑ₃ fieldJump = surfaceCurrent := by
  have hCrossTangent : plane.IsTangent (plane.normalVector ⨯ₑ₃ fieldJump) := by
    exact Space.inner_self_cross plane.normalVector fieldJump
  have hPair : ∀ tangent : plane.tangentSubmodule,
      inner ℝ (plane.normalVector ⨯ₑ₃ fieldJump)
          (tangent : EuclideanSpace ℝ (Fin 3)) =
        inner ℝ surfaceCurrent (tangent : EuclideanSpace ℝ (Fin 3)) := by
    intro tangent
    let rotated : plane.tangentSubmodule :=
      ⟨-(plane.normalVector ⨯ₑ₃ (tangent : EuclideanSpace ℝ (Fin 3))), by
        change plane.normalComponent
          (-(plane.normalVector ⨯ₑ₃ (tangent : EuclideanSpace ℝ (Fin 3)))) = 0
        rw [normalComponent, inner_neg_right, Space.inner_self_cross, neg_zero]⟩
    have hTangent : inner ℝ plane.normalVector
        (tangent : EuclideanSpace ℝ (Fin 3)) = 0 :=
      ((plane.mem_tangentSubmodule tangent).mp tangent.property)
    have hRotated : inner ℝ plane.normalVector
        (rotated : EuclideanSpace ℝ (Fin 3)) = 0 :=
      ((plane.mem_tangentSubmodule rotated).mp rotated.property)
    have hRotate :
        plane.normalVector ⨯ₑ₃ (rotated : EuclideanSpace ℝ (Fin 3)) = tangent := by
      change plane.normalVector ⨯ₑ₃
        (-(plane.normalVector ⨯ₑ₃ (tangent : EuclideanSpace ℝ (Fin 3)))) = tangent
      rw [← neg_one_smul ℝ, Space.cross_smul,
        Space.cross_cross_eq_smul_sub_smul', plane.inner_normalVector_self,
        hTangent, one_smul, zero_smul]
      simp
    calc
      inner ℝ (plane.normalVector ⨯ₑ₃ fieldJump)
          (tangent : EuclideanSpace ℝ (Fin 3)) =
          inner ℝ (plane.normalVector ⨯ₑ₃ fieldJump)
            (plane.normalVector ⨯ₑ₃ (rotated : EuclideanSpace ℝ (Fin 3))) := by
              rw [hRotate]
      _ = inner ℝ fieldJump (rotated : EuclideanSpace ℝ (Fin 3)) := by
        rw [Space.inner_cross_cross, plane.inner_normalVector_self,
          hRotated, one_mul]
        simp
      _ = inner ℝ surfaceCurrent
          (plane.normalVector ⨯ₑ₃ (rotated : EuclideanSpace ℝ (Fin 3))) := hPairing rotated
      _ = inner ℝ surfaceCurrent (tangent : EuclideanSpace ℝ (Fin 3)) := by rw [hRotate]
  have hProjection :=
    (plane.tangentialProjection_eq_iff_inner_eq_on_tangent
      (plane.normalVector ⨯ₑ₃ fieldJump) surfaceCurrent).mpr hPair
  simpa only [plane.tangentialProjection_eq_self_of_isTangent _ hCrossTangent,
    plane.tangentialProjection_eq_self_of_isTangent _ hCurrent] using hProjection

end OrientedAffineHyperplane

end

end Space
