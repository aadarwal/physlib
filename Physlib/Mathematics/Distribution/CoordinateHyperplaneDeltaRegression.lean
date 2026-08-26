/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Mathematics.Distribution.CoordinateHyperplaneDelta
public import Physlib.Mathematics.InnerProductSpace.Gaussian

/-!
# Coordinate-hyperplane pushforward regression tests

## i. Overview

This file checks the coefficient and selected-coordinate orientation of a tangential point source
pushed onto a coordinate hyperplane. The fixture expands the pushforward definition directly. It
does not use the production point-source transport lemma.

## ii. Key results

- `coordinateHyperplanePushforwardRegression_selected_apply`: the selected hyperplane preserves
  the point-source coefficient.
- `coordinateHyperplanePushforwardRegression_wrongCoordinate_ne`: changing the selected
  coordinate changes the pushed-forward distribution.

## iii. Table of contents

- A. Anisotropic two-dimensional point-source fixture
- B. Direct coefficient and coordinate sentinels

## iv. References

This is neutral distribution theory. It assumes no electromagnetic boundary law or surface-source
model.
-/

@[expose] public section

open SchwartzMap
open scoped SchwartzMap

namespace Physlib
namespace Distribution

noncomputable section

/-!
## A. Anisotropic two-dimensional point-source fixture
-/

/-- The first ambient coordinate selected by the pushforward regression. -/
def coordinateHyperplanePushforwardRegressionSelected : Fin 2 := 0

/-- The other ambient coordinate used by the orientation sentinel. -/
def coordinateHyperplanePushforwardRegressionOther : Fin 2 := 1

/-- The nonzero point of the one-dimensional tangential hyperplane. -/
def coordinateHyperplanePushforwardRegressionPoint : EuclideanSpace ℝ (Fin 1) :=
  coordinateNormalEmbedding 0 (Fin.last 0) 1

/-- The ambient point obtained by inserting zero in the selected coordinate. -/
def coordinateHyperplanePushforwardRegressionCenter : EuclideanSpace ℝ (Fin 2) :=
  coordinateHyperplaneEmbedding 1 coordinateHyperplanePushforwardRegressionSelected
    coordinateHyperplanePushforwardRegressionPoint

/-- A Gaussian centered on the selected embedded point, hence anisotropic with respect to swapping
the two coordinate hyperplanes while retaining the same tangential point. -/
def coordinateHyperplanePushforwardRegressionTest : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ :=
  InnerProductSpace.gaussian ℝ
    (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin 2)))
    coordinateHyperplanePushforwardRegressionCenter

/-- A tangential point source with a nonunit coefficient. -/
def coordinateHyperplanePushforwardRegressionSource :
    (EuclideanSpace ℝ (Fin 1)) →d[ℝ] ℝ :=
  Distribution.diracDelta' ℝ coordinateHyperplanePushforwardRegressionPoint 7

private lemma coordinateHyperplanePushforwardRegression_test_at_center :
    coordinateHyperplanePushforwardRegressionTest
      coordinateHyperplanePushforwardRegressionCenter = 1 := by
  simp [coordinateHyperplanePushforwardRegressionTest, InnerProductSpace.gaussian_apply]

private lemma coordinateHyperplanePushforwardRegression_wrong_point_selected_coordinate :
    coordinateHyperplaneEmbedding 1 coordinateHyperplanePushforwardRegressionOther
        coordinateHyperplanePushforwardRegressionPoint
        coordinateHyperplanePushforwardRegressionSelected = 1 := by
  have hindex : coordinateHyperplanePushforwardRegressionSelected =
      coordinateHyperplanePushforwardRegressionOther.succAbove (Fin.last 0) := by
    decide
  rw [hindex, coordinateHyperplaneEmbedding,
    coordinateSplit_symm_apply_succAbove]
  simp [coordinateHyperplanePushforwardRegressionPoint, coordinateNormalEmbedding]

private lemma coordinateHyperplanePushforwardRegression_center_selected_coordinate :
    coordinateHyperplanePushforwardRegressionCenter
        coordinateHyperplanePushforwardRegressionSelected = 0 := by
  simp [coordinateHyperplanePushforwardRegressionCenter,
    coordinateHyperplanePushforwardRegressionSelected,
    coordinateHyperplaneEmbedding]

private lemma coordinateHyperplanePushforwardRegression_wrong_point_ne_center :
    coordinateHyperplaneEmbedding 1 coordinateHyperplanePushforwardRegressionOther
        coordinateHyperplanePushforwardRegressionPoint ≠
      coordinateHyperplanePushforwardRegressionCenter := by
  intro h
  have hcoord := congrArg
    (fun x : EuclideanSpace ℝ (Fin 2) =>
      x coordinateHyperplanePushforwardRegressionSelected) h
  rw [coordinateHyperplanePushforwardRegression_wrong_point_selected_coordinate,
    coordinateHyperplanePushforwardRegression_center_selected_coordinate] at hcoord
  norm_num at hcoord

private lemma coordinateHyperplanePushforwardRegression_test_wrong_ne_one :
    coordinateHyperplanePushforwardRegressionTest
        (coordinateHyperplaneEmbedding 1 coordinateHyperplanePushforwardRegressionOther
          coordinateHyperplanePushforwardRegressionPoint) ≠ 1 := by
  rw [coordinateHyperplanePushforwardRegressionTest, InnerProductSpace.gaussian_apply]
  simp only [ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.refl_apply]
  change Real.exp (-2⁻¹ * ‖coordinateHyperplaneEmbedding 1
      coordinateHyperplanePushforwardRegressionOther
      coordinateHyperplanePushforwardRegressionPoint -
      coordinateHyperplanePushforwardRegressionCenter‖ ^ 2) ≠ 1
  have hne : coordinateHyperplaneEmbedding 1
      coordinateHyperplanePushforwardRegressionOther
      coordinateHyperplanePushforwardRegressionPoint -
      coordinateHyperplanePushforwardRegressionCenter ≠ 0 :=
    sub_ne_zero.mpr coordinateHyperplanePushforwardRegression_wrong_point_ne_center
  have hnorm : 0 < ‖coordinateHyperplaneEmbedding 1
      coordinateHyperplanePushforwardRegressionOther
      coordinateHyperplanePushforwardRegressionPoint -
      coordinateHyperplanePushforwardRegressionCenter‖ := norm_pos_iff.mpr hne
  exact ne_of_lt (Real.exp_lt_one_iff.mpr
    (mul_neg_of_neg_of_pos (by norm_num) (pow_pos hnorm 2)))

/-!
## B. Direct coefficient and coordinate sentinels
-/

/-- Direct expansion shows that the selected-coordinate pushforward retains the source
coefficient. This proof does not invoke the production point-source transport result. -/
lemma coordinateHyperplanePushforwardRegression_selected_apply :
    coordinateHyperplanePushforward 1 coordinateHyperplanePushforwardRegressionSelected
        coordinateHyperplanePushforwardRegressionSource
        coordinateHyperplanePushforwardRegressionTest = 7 := by
  rw [coordinateHyperplanePushforward, ContinuousLinearMap.comp_apply,
    coordinateHyperplanePushforwardRegressionSource, Distribution.diracDelta'_apply,
    coordinateHyperplaneRestriction_apply]
  rw [show coordinateHyperplaneEmbedding 1 coordinateHyperplanePushforwardRegressionSelected
      coordinateHyperplanePushforwardRegressionPoint =
    coordinateHyperplanePushforwardRegressionCenter by rfl]
  rw [coordinateHyperplanePushforwardRegression_test_at_center]
  norm_num

/-- The same tangential source and test function do not produce the selected coefficient after a
coordinate swap. -/
lemma coordinateHyperplanePushforwardRegression_other_apply_ne :
    coordinateHyperplanePushforward 1 coordinateHyperplanePushforwardRegressionOther
        coordinateHyperplanePushforwardRegressionSource
        coordinateHyperplanePushforwardRegressionTest ≠ 7 := by
  rw [coordinateHyperplanePushforward, ContinuousLinearMap.comp_apply,
    coordinateHyperplanePushforwardRegressionSource, Distribution.diracDelta'_apply,
    coordinateHyperplaneRestriction_apply]
  intro h
  apply coordinateHyperplanePushforwardRegression_test_wrong_ne_one
  simp only [smul_eq_mul] at h
  nlinarith

/-- The selected and other coordinate pushforwards are distinct distributions. -/
lemma coordinateHyperplanePushforwardRegression_wrongCoordinate_ne :
    coordinateHyperplanePushforward 1 coordinateHyperplanePushforwardRegressionSelected
        coordinateHyperplanePushforwardRegressionSource ≠
      coordinateHyperplanePushforward 1 coordinateHyperplanePushforwardRegressionOther
        coordinateHyperplanePushforwardRegressionSource := by
  intro h
  have happly := congrArg
    (fun u => u coordinateHyperplanePushforwardRegressionTest) h
  rw [coordinateHyperplanePushforwardRegression_selected_apply] at happly
  exact coordinateHyperplanePushforwardRegression_other_apply_ne happly.symm

end
end Distribution
end Physlib
