/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Mathematics.Distribution.CoordinateSplit

/-!
# Coordinate hyperplane geometry

## i. Overview

This file supplies the normal and tangential embeddings associated with a selected Euclidean
coordinate, together with the affine normal lines used by hyperplane distributions.

## ii. Key results

- `Distribution.coordinateHyperplaneEmbeddingLI`: tangential-coordinate insertion.
- `Distribution.coordinateNormalEmbeddingLI`: selected normal-coordinate insertion.
- `Distribution.coordinateNormalLine_isometry`: isometry of each affine normal line.

## iii. Table of contents

- A. Coordinate embeddings and normal lines

## iv. References

This is neutral Euclidean geometry.
-/

@[expose] public section

open MeasureTheory SchwartzMap
open scoped SchwartzMap

namespace Physlib
namespace Distribution

noncomputable section

/-!
## A. Coordinate embeddings and normal lines
-/

/-- The insertion of the zero `i`th coordinate into Euclidean space. -/
def coordinateHyperplaneEmbedding (d : ℕ) (i : Fin d.succ)
    (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d.succ) :=
  (coordinateSplit d i).symm (0, x)

lemma norm_coordinateHyperplaneEmbedding (d : ℕ) (i : Fin d.succ)
    (x : EuclideanSpace ℝ (Fin d)) :
    ‖coordinateHyperplaneEmbedding d i x‖ = ‖x‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  simp only [PiLp.norm_sq_eq_of_L2, coordinateHyperplaneEmbedding]
  rw [Fin.sum_univ_succAbove _ i]
  simp [coordinateSplit_symm_apply_self, coordinateSplit_symm_apply_succAbove]

/-- The zero-coordinate insertion as a linear isometry. -/
def coordinateHyperplaneEmbeddingLI (d : ℕ) (i : Fin d.succ) :
    EuclideanSpace ℝ (Fin d) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d.succ) where
  toFun := coordinateHyperplaneEmbedding d i
  map_add' x y := by
    ext j
    rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
    · simp [coordinateHyperplaneEmbedding]
    · simp [coordinateHyperplaneEmbedding]
  map_smul' c x := by
    ext j
    rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
    · simp [coordinateHyperplaneEmbedding]
    · simp [coordinateHyperplaneEmbedding]
  norm_map' := norm_coordinateHyperplaneEmbedding d i

@[simp]
lemma coordinateHyperplaneEmbedding_zero (d : ℕ) (i : Fin d.succ) :
    coordinateHyperplaneEmbedding d i 0 = 0 := by
  change (coordinateHyperplaneEmbeddingLI d i) 0 = 0
  exact map_zero _

/-- The insertion of a scalar into the selected coordinate, with every retained coordinate
zero. -/
def coordinateNormalEmbedding (d : ℕ) (i : Fin d.succ) (r : ℝ) :
    EuclideanSpace ℝ (Fin d.succ) :=
  (coordinateSplit d i).symm (r, 0)

lemma norm_coordinateNormalEmbedding (d : ℕ) (i : Fin d.succ) (r : ℝ) :
    ‖coordinateNormalEmbedding d i r‖ = ‖r‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  simp only [PiLp.norm_sq_eq_of_L2, coordinateNormalEmbedding]
  rw [Fin.sum_univ_succAbove _ i]
  simp [coordinateSplit_symm_apply_self, coordinateSplit_symm_apply_succAbove]

/-- The selected coordinate insertion as a linear isometry. -/
def coordinateNormalEmbeddingLI (d : ℕ) (i : Fin d.succ) :
    ℝ →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d.succ) where
  toFun := coordinateNormalEmbedding d i
  map_add' r s := by
    ext j
    rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
    · simp [coordinateNormalEmbedding]
    · simp [coordinateNormalEmbedding]
  map_smul' c r := by
    ext j
    rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
    · simp [coordinateNormalEmbedding]
    · simp [coordinateNormalEmbedding]
  norm_map' := norm_coordinateNormalEmbedding d i

@[simp]
lemma coordinateNormalEmbedding_zero (d : ℕ) (i : Fin d.succ) :
    coordinateNormalEmbedding d i 0 = 0 := by
  change (coordinateNormalEmbeddingLI d i) 0 = 0
  exact map_zero _

/-- The coordinate split reconstructs as the sum of its normal and hyperplane insertions. -/
lemma coordinateSplit_symm_eq_add (d : ℕ) (i : Fin d.succ) (r : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    (coordinateSplit d i).symm (r, x) =
      coordinateNormalEmbedding d i r + coordinateHyperplaneEmbedding d i x := by
  ext j
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
  · simp [coordinateNormalEmbedding, coordinateHyperplaneEmbedding]
  · simp [coordinateNormalEmbedding, coordinateHyperplaneEmbedding]

/-- The affine line through a retained-coordinate point in the selected normal direction. -/
def coordinateNormalLine (d : ℕ) (i : Fin d.succ)
    (x : EuclideanSpace ℝ (Fin d)) (r : ℝ) : EuclideanSpace ℝ (Fin d.succ) :=
  coordinateNormalEmbedding d i r + coordinateHyperplaneEmbedding d i x

lemma coordinateNormalLine_eq_split_symm (d : ℕ) (i : Fin d.succ)
    (x : EuclideanSpace ℝ (Fin d)) (r : ℝ) :
    coordinateNormalLine d i x r = (coordinateSplit d i).symm (r, x) :=
  (coordinateSplit_symm_eq_add d i r x).symm

@[simp]
lemma fderiv_coordinateNormalLine_apply (d : ℕ) (i : Fin d.succ)
    (x : EuclideanSpace ℝ (Fin d)) (r s : ℝ) :
    fderiv ℝ (coordinateNormalLine d i x) r s = coordinateNormalEmbedding d i s := by
  change fderiv ℝ
    (fun t => (coordinateNormalEmbeddingLI d i).toContinuousLinearMap t +
      coordinateHyperplaneEmbedding d i x) r s =
      (coordinateNormalEmbeddingLI d i) s
  rw [fderiv_add_const, ContinuousLinearMap.fderiv]
  rfl

/-- Every selected-coordinate normal line is an isometric embedding of the real line. -/
lemma coordinateNormalLine_isometry (d : ℕ) (i : Fin d.succ)
    (x : EuclideanSpace ℝ (Fin d)) :
    Isometry (coordinateNormalLine d i x) := by
  apply Isometry.of_dist_eq
  intro r s
  change dist
    ((coordinateNormalEmbeddingLI d i) r + coordinateHyperplaneEmbedding d i x)
    ((coordinateNormalEmbeddingLI d i) s + coordinateHyperplaneEmbedding d i x) = dist r s
  rw [dist_add_right]
  exact (coordinateNormalEmbeddingLI d i).isometry.dist_eq r s

end
end Distribution
end Physlib
