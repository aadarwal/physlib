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

This file independently checks the normalization and sign of the distributional derivative of the
one-dimensional positive-half-line Heaviside distribution on a standard Gaussian test function.
It expands the derivative and half-space integral directly instead of using the production
Heaviside-to-boundary-delta identification.

## ii. Key results

- `heavisideRegression_positiveNormal`: the positive normal derivative evaluates to `1`.
- `heavisideRegression_negativeNormal`: reversing the normal changes the value to `-1`.

## iii. Table of contents

- A. One-dimensional Gaussian fixture
- B. Boundary normalization and orientation sentinels

## iv. References

This is a regression for neutral distribution theory. It assumes no electromagnetic boundary law.
Because the ambient space is one-dimensional, the fixture guards normalization and normal reversal,
not selection among multiple coordinate axes.
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

/-- The independently defined coordinate-hyperplane delta evaluates the fixture to `1`. -/
lemma heavisideRegression_hyperplaneDelta :
    coordinateHyperplaneDelta 0 (Fin.last 0) heavisideRegressionGaussian = 1 := by
  rw [coordinateHyperplaneDelta_zero_apply]
  exact heavisideRegressionGaussian_apply_zero

/-- Direct expansion of the Gaussian normal derivative over the positive half-space gives `-1`.
This proof deliberately avoids every Heaviside-to-delta identification and the packaged
normal-line half-FTC lemma. -/
private lemma heavisideRegression_raw_halfSpaceDerivative :
    ∫ y in {y : EuclideanSpace ℝ (Fin 1) | 0 < y (Fin.last 0)},
        fderiv ℝ heavisideRegressionGaussian y
          (coordinateNormalEmbedding 0 (Fin.last 0) 1) = -1 := by
  let i : Fin 1 := Fin.last 0
  let normal : EuclideanSpace ℝ (Fin 1) := coordinateNormalEmbedding 0 i 1
  let e : ℝ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 1) :=
    (coordinateNormalEmbeddingLI 0 i).toLinearIsometryEquiv (by simp)
  let line : SchwartzMap ℝ ℝ :=
    coordinateNormalLineRestriction 0 i 0 heavisideRegressionGaussian
  have hePreimage :
      e ⁻¹' {y : EuclideanSpace ℝ (Fin 1) | 0 < y i} = Set.Ioi (0 : ℝ) := by
    ext r
    change 0 < coordinateNormalEmbedding 0 i r i ↔ 0 < r
    simp [coordinateNormalEmbedding]
  have hChange :
      ∫ y in {y : EuclideanSpace ℝ (Fin 1) | 0 < y i},
          fderiv ℝ heavisideRegressionGaussian y normal =
        ∫ r in Set.Ioi (0 : ℝ),
          fderiv ℝ heavisideRegressionGaussian (e r) normal := by
    have h := e.measurePreserving.setIntegral_preimage_emb
      e.toHomeomorph.measurableEmbedding
      (fun y => fderiv ℝ heavisideRegressionGaussian y normal)
      {y : EuclideanSpace ℝ (Fin 1) | 0 < y i}
    simpa only [hePreimage] using h.symm
  rw [show Fin.last 0 = i by rfl, show coordinateNormalEmbedding 0 i 1 = normal by rfl,
    hChange]
  calc
    _ = ∫ r in Set.Ioi (0 : ℝ), deriv line r := by
      congr 1
      funext r
      have hline : DifferentiableAt ℝ (coordinateNormalLine 0 i 0) r := by
        change DifferentiableAt ℝ
          (fun t => (coordinateNormalEmbeddingLI 0 i).toContinuousLinearMap t +
            coordinateHyperplaneEmbedding 0 i 0) r
        fun_prop
      rw [show e r = coordinateNormalEmbedding 0 i r by rfl]
      rw [show coordinateNormalEmbedding 0 i r = coordinateNormalLine 0 i 0 r by
        simp [coordinateNormalLine]]
      change fderiv ℝ heavisideRegressionGaussian (coordinateNormalLine 0 i 0 r) normal =
        deriv (fun t => heavisideRegressionGaussian (coordinateNormalLine 0 i 0 t)) r
      rw [← fderiv_apply_one_eq_deriv,
        fderiv_fun_comp _ heavisideRegressionGaussian.differentiableAt hline]
      simp only [ContinuousLinearMap.comp_apply]
      rw [fderiv_coordinateNormalLine_apply]
    _ = -line 0 := by
      rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
        (f := fun r => line r) (m := 0)]
      · simp
      · exact ContinuousAt.continuousWithinAt (by fun_prop)
      · exact fun r _ => DifferentiableAt.hasDerivAt (by fun_prop)
      · exact (integrable ((SchwartzMap.derivCLM ℝ ℝ) line)).integrableOn
      · exact Filter.Tendsto.mono_left line.toZeroAtInfty.zero_at_infty'
          atTop_le_cocompact
    _ = -1 := by
      simp [line, coordinateNormalLine, heavisideRegressionGaussian_apply_zero]

/-- Direct expansion gives `1` for differentiation into the positive half-space. -/
lemma heavisideRegression_positiveNormal :
    fderivD ℝ (heavisideStep 0) heavisideRegressionGaussian
        (coordinateNormalEmbedding 0 (Fin.last 0) 1) = 1 := by
  rw [fderivD_apply, heavisideStep_apply]
  simp only [SchwartzMap.evalCLM_apply_apply, SchwartzMap.fderivCLM_apply]
  change -(∫ y in {y : EuclideanSpace ℝ (Fin 1) | 0 < y (Fin.last 0)},
      fderiv ℝ heavisideRegressionGaussian y
        (coordinateNormalEmbedding 0 (Fin.last 0) 1)) = 1
  rw [heavisideRegression_raw_halfSpaceDerivative]
  norm_num

/-- Direct expansion gives `-1` after reversing the selected normal direction. -/
lemma heavisideRegression_negativeNormal :
    fderivD ℝ (heavisideStep 0) heavisideRegressionGaussian
        (coordinateNormalEmbedding 0 (Fin.last 0) (-1)) = -1 := by
  have hnormal : coordinateNormalEmbedding 0 (Fin.last 0) (-1) =
      -coordinateNormalEmbedding 0 (Fin.last 0) 1 := by
    change (coordinateNormalEmbeddingLI 0 (Fin.last 0)) (-1) =
      -(coordinateNormalEmbeddingLI 0 (Fin.last 0)) 1
    rw [map_neg]
  rw [fderivD_apply, heavisideStep_apply]
  simp only [SchwartzMap.evalCLM_apply_apply, SchwartzMap.fderivCLM_apply]
  change -(∫ y in {y : EuclideanSpace ℝ (Fin 1) | 0 < y (Fin.last 0)},
      fderiv ℝ heavisideRegressionGaussian y
        (coordinateNormalEmbedding 0 (Fin.last 0) (-1))) = -1
  rw [hnormal]
  simp only [map_neg, MeasureTheory.integral_neg]
  rw [heavisideRegression_raw_halfSpaceDerivative]
  norm_num

end
end Distribution
end Physlib
