/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Mathematics.Distribution.Heaviside
public import Physlib.Mathematics.InnerProductSpace.Gaussian
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# Coordinate Heaviside regression tests

## i. Overview

This file independently checks the normalization and sign of the distributional derivative of a
positive-coordinate Heaviside distribution on Gaussian test functions. The one-dimensional
fixture pins normal orientation. A two-dimensional fixture selects the first rather than last
coordinate, and an asymmetric weighted Gaussian makes a coordinate swap observable. The proofs
expand the derivative, half-space integral, and boundary integral directly instead of using the
production Heaviside-to-boundary-delta identification.

## ii. Key results

- `heavisideRegression_positiveNormal`: the positive normal derivative evaluates to `1`.
- `heavisideRegression_negativeNormal`: reversing the normal changes the value to `-1`.
- `coordinateHeavisideRegression_derivative_eq_boundary`: direct derivative and boundary
  computations agree for a selected coordinate that is not the last coordinate.
- `coordinateHeavisideRegression_hyperplaneDelta`: the selected first-coordinate boundary mass.
- `coordinateHeavisideRegression_wrongCoordinate_ne`: the other coordinate gives a different
  value on the weighted fixture.

## iii. Table of contents

- A. One-dimensional Gaussian fixture
- B. Boundary normalization and orientation sentinels
- C. Selected-coordinate sentinels

## iv. References

This is a regression for neutral distribution theory. It assumes no electromagnetic boundary law,
weak field, or surface source.
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

/-!
## C. Selected-coordinate sentinels
-/

/-- The two-dimensional Gaussian used to test a selected coordinate other than the last one. -/
def coordinateHeavisideRegressionGaussian :
    SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ :=
  InnerProductSpace.stdGaussian (EuclideanSpace ℝ (Fin 2)) ℝ

/-- The first ambient coordinate selected by the two-dimensional regression. -/
def coordinateHeavisideRegressionSelected : Fin 2 := 0

/-- The nonselected second ambient coordinate used by the swap sentinel. -/
def coordinateHeavisideRegressionOther : Fin 2 := 1

/-- A coordinate-asymmetric Schwartz map: the square of the selected coordinate times the
standard Gaussian. -/
def coordinateHeavisideRegressionWeightedGaussian :
    SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ :=
  SchwartzMap.smulLeftCLM ℝ
    ((fun x : EuclideanSpace ℝ (Fin 2) ↦
      x coordinateHeavisideRegressionSelected) ^ 2)
    coordinateHeavisideRegressionGaussian

@[simp]
lemma coordinateHeavisideRegressionWeightedGaussian_apply
    (x : EuclideanSpace ℝ (Fin 2)) :
    coordinateHeavisideRegressionWeightedGaussian x =
      (x coordinateHeavisideRegressionSelected) ^ 2 *
        coordinateHeavisideRegressionGaussian x := by
  have hcoordinate : Function.HasTemperateGrowth
      (fun y : EuclideanSpace ℝ (Fin 2) =>
        y coordinateHeavisideRegressionSelected) := by
    exact (PiLp.proj (p := 2) (β := fun _ : Fin 2 => ℝ)
      coordinateHeavisideRegressionSelected).hasTemperateGrowth
  have hweight := hcoordinate.pow 2
  rw [coordinateHeavisideRegressionWeightedGaussian]
  simpa [Pi.pow_apply, smul_eq_mul] using
    (SchwartzMap.smulLeftCLM_apply_apply hweight
      coordinateHeavisideRegressionGaussian x)

private lemma coordinateHeavisideRegression_raw_boundaryIntegral :
    (∫ x : EuclideanSpace ℝ (Fin 1), coordinateHeavisideRegressionGaussian
        (coordinateHyperplaneEmbedding 1 coordinateHeavisideRegressionSelected x)) =
      (2 * Real.pi) ^ (1 / 2 : ℝ) := by
  simp only [coordinateHeavisideRegressionGaussian, InnerProductSpace.gaussian_apply,
    sub_zero, ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.refl_apply,
    norm_coordinateHyperplaneEmbedding]
  simpa [coordinateHeavisideRegressionSelected, mul_comm] using
    (GaussianFourier.integral_rexp_neg_mul_sq_norm
      (V := EuclideanSpace ℝ (Fin 1)) (b := (2 : ℝ)⁻¹) (by positivity))

private lemma coordinateHeavisideRegression_raw_normalLineIntegral
    (x : EuclideanSpace ℝ (Fin 1)) :
    ∫ r in Set.Ioi (0 : ℝ),
        fderiv ℝ coordinateHeavisideRegressionGaussian
          (coordinateNormalLine 1 coordinateHeavisideRegressionSelected x r)
          (coordinateNormalEmbedding 1 coordinateHeavisideRegressionSelected 1) =
      -coordinateHeavisideRegressionGaussian
        (coordinateHyperplaneEmbedding 1 coordinateHeavisideRegressionSelected x) := by
  let line : SchwartzMap ℝ ℝ :=
    coordinateNormalLineRestriction 1 coordinateHeavisideRegressionSelected x
      coordinateHeavisideRegressionGaussian
  calc
    _ = ∫ r in Set.Ioi (0 : ℝ), deriv line r := by
      congr 1
      funext r
      have hline : DifferentiableAt ℝ
          (coordinateNormalLine 1 coordinateHeavisideRegressionSelected x) r := by
        let i : Fin 2 := coordinateHeavisideRegressionSelected
        change DifferentiableAt ℝ (coordinateNormalLine 1 i x) r
        change DifferentiableAt ℝ
          (fun t => (coordinateNormalEmbeddingLI 1 i).toContinuousLinearMap t +
            coordinateHyperplaneEmbedding 1 i x) r
        fun_prop
      change fderiv ℝ coordinateHeavisideRegressionGaussian
          (coordinateNormalLine 1 coordinateHeavisideRegressionSelected x r)
          (coordinateNormalEmbedding 1 coordinateHeavisideRegressionSelected 1) =
        deriv (fun t => coordinateHeavisideRegressionGaussian
          (coordinateNormalLine 1 coordinateHeavisideRegressionSelected x t)) r
      rw [← fderiv_apply_one_eq_deriv,
        fderiv_fun_comp _ coordinateHeavisideRegressionGaussian.differentiableAt hline]
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
    _ = _ := by
      simp [line, coordinateNormalLine]

private lemma coordinateHeavisideRegression_raw_halfSpaceDerivative :
    ∫ y in {y : EuclideanSpace ℝ (Fin 2) |
        0 < y coordinateHeavisideRegressionSelected},
      fderiv ℝ coordinateHeavisideRegressionGaussian y
        (coordinateNormalEmbedding 1 coordinateHeavisideRegressionSelected 1) =
      -((2 * Real.pi) ^ (1 / 2 : ℝ)) := by
  let normal : EuclideanSpace ℝ (Fin 2) :=
    coordinateNormalEmbedding 1 coordinateHeavisideRegressionSelected 1
  let g : ℝ × EuclideanSpace ℝ (Fin 1) → ℝ := fun p =>
    fderiv ℝ coordinateHeavisideRegressionGaussian
      (coordinateNormalLine 1 coordinateHeavisideRegressionSelected p.2 p.1) normal
  have hsplit := coordinateSplit_measurePreserving 1
    coordinateHeavisideRegressionSelected
  have hcomp :=
    (hsplit.symm.integrable_comp_emb
        (coordinateSplit 1 coordinateHeavisideRegressionSelected).symm.measurableEmbedding).mpr
      (integrable_fderiv_coordinateNormal 1 coordinateHeavisideRegressionSelected
        coordinateHeavisideRegressionGaussian)
  rw [Measure.volume_eq_prod] at hcomp
  have hgProd : Integrable g
      ((volume : Measure ℝ).prod (volume : Measure (EuclideanSpace ℝ (Fin 1)))) := by
    refine hcomp.congr ?_
    filter_upwards with p
    simp only [g, normal, Function.comp_apply, coordinateNormalLine_eq_split_symm]
  have hChange :
      (∫ y in {y : EuclideanSpace ℝ (Fin 2) |
          0 < y coordinateHeavisideRegressionSelected},
        fderiv ℝ coordinateHeavisideRegressionGaussian y normal) =
        ∫ p in {p : ℝ × EuclideanSpace ℝ (Fin 1) | 0 < p.1}, g p := by
    have h := hsplit.setIntegral_preimage_emb
        (coordinateSplit 1 coordinateHeavisideRegressionSelected).measurableEmbedding g
        {p : ℝ × EuclideanSpace ℝ (Fin 1) | 0 < p.1}
    simpa [g, coordinateNormalLine_eq_split_symm] using h
  have hFubini :
      (∫ p in {p : ℝ × EuclideanSpace ℝ (Fin 1) | 0 < p.1}, g p) =
        ∫ x : EuclideanSpace ℝ (Fin 1), ∫ r in Set.Ioi (0 : ℝ), g (r, x) := by
    have hset : {p : ℝ × EuclideanSpace ℝ (Fin 1) | 0 < p.1} =
        Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (EuclideanSpace ℝ (Fin 1))) := by
      ext p
      simp
    rw [hset, Measure.volume_eq_prod]
    calc
      _ = ∫ p : EuclideanSpace ℝ (Fin 1) × ℝ in
          Set.univ ×ˢ Set.Ioi (0 : ℝ), g p.swap
          ∂((volume : Measure (EuclideanSpace ℝ (Fin 1))).prod (volume : Measure ℝ)) := by
        exact (MeasureTheory.setIntegral_prod_swap
          (Set.Ioi (0 : ℝ)) (Set.univ : Set (EuclideanSpace ℝ (Fin 1))) g).symm
      _ = _ := by
        rw [MeasureTheory.setIntegral_prod]
        · simp
        · exact hgProd.integrableOn.swap
  rw [show coordinateNormalEmbedding 1 coordinateHeavisideRegressionSelected 1 = normal by rfl,
    hChange, hFubini]
  simp_rw [g, normal, coordinateHeavisideRegression_raw_normalLineIntegral]
  rw [integral_neg, coordinateHeavisideRegression_raw_boundaryIntegral]

/-- Direct expansion of the selected-coordinate distributional derivative gives the same exact
Gaussian mass as the independently expanded boundary integral. -/
lemma coordinateHeavisideRegression_positiveNormal :
    fderivD ℝ
        (coordinateHeavisideStep 1 coordinateHeavisideRegressionSelected)
        coordinateHeavisideRegressionGaussian
        (coordinateNormalEmbedding 1 coordinateHeavisideRegressionSelected 1) =
      (2 * Real.pi) ^ (1 / 2 : ℝ) := by
  rw [fderivD_apply, coordinateHeavisideStep_apply]
  simp only [SchwartzMap.evalCLM_apply_apply, SchwartzMap.fderivCLM_apply]
  change -(∫ y in {y : EuclideanSpace ℝ (Fin 2) |
      0 < y coordinateHeavisideRegressionSelected},
    fderiv ℝ coordinateHeavisideRegressionGaussian y
      (coordinateNormalEmbedding 1 coordinateHeavisideRegressionSelected 1)) = _
  rw [coordinateHeavisideRegression_raw_halfSpaceDerivative]
  simp

/-- Direct boundary integration on the selected first-coordinate hyperplane gives the exact
one-dimensional Gaussian mass. This does not use a Heaviside derivative identification. -/
lemma coordinateHeavisideRegression_hyperplaneDelta :
    coordinateHyperplaneDelta 1 coordinateHeavisideRegressionSelected
        coordinateHeavisideRegressionGaussian =
      (2 * Real.pi) ^ (1 / 2 : ℝ) := by
  rw [coordinateHyperplaneDelta_apply,
    coordinateHeavisideRegression_raw_boundaryIntegral]

/-- The raw derivative and boundary calculations agree without using the production
Heaviside-to-boundary identification. -/
lemma coordinateHeavisideRegression_derivative_eq_boundary :
    fderivD ℝ
        (coordinateHeavisideStep 1 coordinateHeavisideRegressionSelected)
        coordinateHeavisideRegressionGaussian
        (coordinateNormalEmbedding 1 coordinateHeavisideRegressionSelected 1) =
      coordinateHyperplaneDelta 1 coordinateHeavisideRegressionSelected
        coordinateHeavisideRegressionGaussian := by
  rw [coordinateHeavisideRegression_positiveNormal,
    coordinateHeavisideRegression_hyperplaneDelta]

/-- The weighted fixture vanishes identically on the selected first-coordinate hyperplane. -/
lemma coordinateHeavisideRegression_weighted_selected_eq_zero :
    coordinateHyperplaneDelta 1 coordinateHeavisideRegressionSelected
      coordinateHeavisideRegressionWeightedGaussian = 0 := by
  rw [coordinateHyperplaneDelta_apply]
  simp_rw [coordinateHeavisideRegressionWeightedGaussian_apply]
  simp [coordinateHeavisideRegressionSelected, coordinateHyperplaneEmbedding]

/-- The same weighted fixture has strictly positive boundary mass on the other coordinate
hyperplane. This makes replacing the selected coordinate by the last coordinate fail. -/
lemma coordinateHeavisideRegression_weighted_other_pos :
    0 < coordinateHyperplaneDelta 1 coordinateHeavisideRegressionOther
      coordinateHeavisideRegressionWeightedGaussian := by
  rw [coordinateHyperplaneDelta_apply]
  let restricted : SchwartzMap (EuclideanSpace ℝ (Fin 1)) ℝ :=
    coordinateHyperplaneRestriction 1 coordinateHeavisideRegressionOther
      coordinateHeavisideRegressionWeightedGaussian
  change 0 < ∫ x, restricted x
  apply integral_pos_of_integrable_nonneg_nonzero restricted.continuous (integrable restricted)
  · intro x
    change 0 ≤ coordinateHeavisideRegressionWeightedGaussian
      (coordinateHyperplaneEmbedding 1 coordinateHeavisideRegressionOther x)
    rw [coordinateHeavisideRegressionWeightedGaussian_apply]
    apply mul_nonneg (sq_nonneg _)
    rw [coordinateHeavisideRegressionGaussian, InnerProductSpace.gaussian_apply]
    exact Real.exp_nonneg _
  · let one : EuclideanSpace ℝ (Fin 1) := coordinateNormalEmbedding 0 (Fin.last 0) 1
    show restricted one ≠ 0
    change coordinateHeavisideRegressionWeightedGaussian
      (coordinateHyperplaneEmbedding 1 coordinateHeavisideRegressionOther one) ≠ 0
    rw [coordinateHeavisideRegressionWeightedGaussian_apply]
    apply mul_ne_zero
    · have hindex : coordinateHeavisideRegressionSelected =
          coordinateHeavisideRegressionOther.succAbove (Fin.last 0) := by
          decide
      rw [hindex, coordinateHyperplaneEmbedding,
        coordinateSplit_symm_apply_succAbove]
      simp [one, coordinateNormalEmbedding]
    · simp [coordinateHeavisideRegressionGaussian, InnerProductSpace.gaussian_apply]

/-- The selected and other coordinate hyperplanes are distinguished by the weighted fixture. -/
lemma coordinateHeavisideRegression_wrongCoordinate_ne :
    coordinateHyperplaneDelta 1 coordinateHeavisideRegressionSelected
        coordinateHeavisideRegressionWeightedGaussian ≠
      coordinateHyperplaneDelta 1 coordinateHeavisideRegressionOther
        coordinateHeavisideRegressionWeightedGaussian := by
  rw [coordinateHeavisideRegression_weighted_selected_eq_zero]
  exact ne_of_lt coordinateHeavisideRegression_weighted_other_pos

end
end Distribution
end Physlib
