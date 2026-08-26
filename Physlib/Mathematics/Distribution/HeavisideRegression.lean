/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Mathematics.Distribution.Heaviside
public import Physlib.Mathematics.InnerProductSpace.Gaussian

/-!
# Coordinate Heaviside regression tests

## i. Overview

This file checks the normalization and orientation of the distributional derivative of the
one-dimensional positive-half-line Heaviside distribution on a standard Gaussian test function.

## ii. Key results

- `heavisideRegression_positiveNormal`: the positive normal derivative evaluates to `1`.
- `heavisideRegression_negativeNormal`: reversing the normal changes the value to `-1`.

## iii. Table of contents

- A. One-dimensional Gaussian fixture
- B. Boundary normalization and orientation sentinels

## iv. References

This is a regression for neutral distribution theory. It assumes no electromagnetic boundary law.
-/

@[expose] public section

open MeasureTheory SchwartzMap
open scoped SchwartzMap

namespace Physlib
namespace Distribution

noncomputable section

/-!
## A. One-dimensional Gaussian fixture
-/

/-- The unnormalized standard Gaussian used to test the one-dimensional Heaviside derivative. -/
def heavisideRegressionGaussian : SchwartzMap (EuclideanSpace ℝ (Fin 1)) ℝ :=
  InnerProductSpace.stdGaussian (EuclideanSpace ℝ (Fin 1)) ℝ

@[simp]
lemma heavisideRegressionGaussian_apply_zero : heavisideRegressionGaussian 0 = 1 := by
  simp [heavisideRegressionGaussian, InnerProductSpace.gaussian_apply]

/-!
## B. Boundary normalization and orientation sentinels
-/

lemma heavisideRegression_hyperplaneDelta :
    coordinateHyperplaneDelta 0 (Fin.last 0) heavisideRegressionGaussian = 1 := by
  rw [coordinateHyperplaneDelta_zero_apply]
  exact heavisideRegressionGaussian_apply_zero

lemma heavisideRegression_positiveNormal :
    fderivD ℝ (heavisideStep 0) heavisideRegressionGaussian
        (coordinateNormalEmbedding 0 (Fin.last 0) 1) = 1 := by
  rw [fderivD_heavisideStep_last_apply]
  exact heavisideRegression_hyperplaneDelta

lemma heavisideRegression_negativeNormal :
    fderivD ℝ (heavisideStep 0) heavisideRegressionGaussian
        (coordinateNormalEmbedding 0 (Fin.last 0) (-1)) = -1 := by
  have hnormal : coordinateNormalEmbedding 0 (Fin.last 0) (-1) =
      -coordinateNormalEmbedding 0 (Fin.last 0) 1 := by
    change (coordinateNormalEmbeddingLI 0 (Fin.last 0)) (-1) =
      -(coordinateNormalEmbeddingLI 0 (Fin.last 0)) 1
    rw [map_neg]
  rw [hnormal, map_neg, heavisideRegression_positiveNormal]

end
end Distribution
end Physlib
