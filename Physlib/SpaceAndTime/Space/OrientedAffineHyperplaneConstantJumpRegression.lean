/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Mathematics.InnerProductSpace.Gaussian
public import Physlib.SpaceAndTime.Space.OrientedAffineHyperplaneConstantJump

/-!
# Regression for a constant coordinate-hyperplane jump

## i. Overview

This file independently expands the sidewise distributional derivative and the transported sheet
on a one-dimensional Gaussian fixture. Both have value `7`; reversing the derivative direction
has value `-7`. A coordinate-asymmetric two-dimensional fixture separately distinguishes the
selected and swapped hyperplanes.

The value anchors do not use the production realization or derivative-identification lemmas.

## ii. Key results

- `constantJumpRegression_raw_positiveDerivative`: direct half-line calculus gives `7`.
- `constantJumpRegression_raw_sheet`: direct boundary evaluation gives `7`.
- `constantJumpRegression_raw_agreement`: the independently expanded values agree.
- `constantJumpRegression_raw_negativeDerivative`: normal reversal gives `-7`.
- `constantJumpRegression_wrongCoordinate_ne`: the selected and swapped sheets differ.

## iii. Table of contents

- A. One-dimensional sign fixture
- B. Two-dimensional coordinate fixture

## iv. References

This is a regression for neutral distribution theory. It does not state an electromagnetic jump
law or derive a finite-sheet premise.
-/

@[expose] public section

open MeasureTheory SchwartzMap

namespace Space

noncomputable section

/-!
## A. One-dimensional sign fixture
-/

/-- The positive coordinate index in one-dimensional space. -/
def constantJumpRegressionIndex : Fin 1 := Fin.last 0

/-- The standard spatial Gaussian used by the sign fixture. -/
def constantJumpRegressionGaussian : SchwartzMap (Space 1) ℝ :=
  InnerProductSpace.stdGaussian (Space 1) ℝ

@[simp]
lemma constantJumpRegressionGaussian_apply_zero : constantJumpRegressionGaussian 0 = 1 := by
  simp [constantJumpRegressionGaussian, InnerProductSpace.gaussian_apply]

/-- Pull the one-dimensional spatial Gaussian back along the coordinate isometry. -/
def constantJumpRegressionLine : SchwartzMap ℝ ℝ :=
  SchwartzMap.compCLMOfAntilipschitz ℝ
    Space.oneEquiv.symm.toContinuousLinearMap.hasTemperateGrowth
    Space.oneEquiv.symm.isometry.antilipschitz constantJumpRegressionGaussian

@[simp]
lemma constantJumpRegressionLine_apply (r : ℝ) :
    constantJumpRegressionLine r = constantJumpRegressionGaussian (Space.oneEquiv.symm r) :=
  rfl

private lemma constantJumpRegression_oneEquiv_symm_one :
    Space.oneEquiv.symm 1 = Space.basis constantJumpRegressionIndex := by
  ext i
  fin_cases i
  simp [constantJumpRegressionIndex, Space.oneEquiv_symm_apply]

/-- Direct change of variables and one-dimensional FTC give the raw positive-half-space normal
derivative integral. -/
private lemma constantJumpRegression_raw_halfSpaceDerivative :
    ∫ x in {x : Space 1 | 0 < x constantJumpRegressionIndex},
        fderiv ℝ constantJumpRegressionGaussian x
          (Space.basis constantJumpRegressionIndex) = -1 := by
  let e : ℝ ≃ₗᵢ[ℝ] Space 1 := Space.oneEquiv.symm
  have hePreimage :
      e ⁻¹' {x : Space 1 | 0 < x constantJumpRegressionIndex} = Set.Ioi (0 : ℝ) := by
    ext r
    change 0 < Space.oneEquiv.symm r constantJumpRegressionIndex ↔ 0 < r
    simp [Space.oneEquiv_symm_apply]
  have hChange :
      (∫ x in {x : Space 1 | 0 < x constantJumpRegressionIndex},
          fderiv ℝ constantJumpRegressionGaussian x
            (Space.basis constantJumpRegressionIndex)) =
        ∫ r in Set.Ioi (0 : ℝ),
          fderiv ℝ constantJumpRegressionGaussian (e r)
            (Space.basis constantJumpRegressionIndex) := by
    have h := e.measurePreserving.setIntegral_preimage_emb
      e.toHomeomorph.measurableEmbedding
      (fun x => fderiv ℝ constantJumpRegressionGaussian x
        (Space.basis constantJumpRegressionIndex))
      {x : Space 1 | 0 < x constantJumpRegressionIndex}
    simpa only [hePreimage] using h.symm
  rw [hChange]
  calc
    _ = ∫ r in Set.Ioi (0 : ℝ), _root_.deriv constantJumpRegressionLine r := by
      congr 1
      funext r
      change fderiv ℝ constantJumpRegressionGaussian (Space.oneEquiv.symm r)
          (Space.basis constantJumpRegressionIndex) =
        _root_.deriv (fun t => constantJumpRegressionGaussian (Space.oneEquiv.symm t)) r
      rw [← fderiv_apply_one_eq_deriv]
      conv_rhs =>
        rw [fderiv_fun_comp _ constantJumpRegressionGaussian.differentiableAt (by fun_prop)]
      simp only [ContinuousLinearMap.comp_apply]
      have heFderiv :
          fderiv ℝ (Space.oneEquiv.symm : ℝ → Space 1) r 1 =
            Space.basis constantJumpRegressionIndex := by
        change fderiv ℝ Space.oneEquiv.symm.toContinuousLinearMap r 1 = _
        rw [ContinuousLinearMap.fderiv]
        exact constantJumpRegression_oneEquiv_symm_one
      rw [heFderiv]
    _ = -constantJumpRegressionLine 0 := by
      rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
        (f := fun r => constantJumpRegressionLine r) (m := 0)]
      · simp
      · exact ContinuousAt.continuousWithinAt (by fun_prop)
      · exact fun r _ => DifferentiableAt.hasDerivAt (by fun_prop)
      · exact (integrable ((SchwartzMap.derivCLM ℝ ℝ)
          constantJumpRegressionLine)).integrableOn
      · exact Filter.Tendsto.mono_left
          constantJumpRegressionLine.toZeroAtInfty.zero_at_infty' atTop_le_cocompact
    _ = -1 := by
      simp [constantJumpRegressionLine]

/-- Direct expansion of the sidewise relation and distributional derivative gives `7`. -/
lemma constantJumpRegression_raw_positiveDerivative :
    distDeriv constantJumpRegressionIndex
        (OrientedAffineHyperplane.distOfSidewiseFunction
          (OrientedAffineHyperplane.coordinateHyperplane constantJumpRegressionIndex)
            (OrientedAffineHyperplane.coordinatePositiveConstantField (7 : ℝ))
            (OrientedAffineHyperplane.coordinatePositiveConstantField_isDistBounded 7))
        constantJumpRegressionGaussian = 7 := by
  rw [distDeriv_apply, Physlib.Distribution.fderivD_apply,
    OrientedAffineHyperplane.distOfSidewiseFunction_apply]
  simp only [SchwartzMap.evalCLM_apply_apply, SchwartzMap.fderivCLM_apply,
    OrientedAffineHyperplane.coordinatePositiveConstantField, smul_eq_mul,
    mul_zero, integral_zero, zero_add]
  simp only [OrientedAffineHyperplane.openHalfSpace,
    OrientedAffineHyperplane.Side.sign_positive, one_mul,
    OrientedAffineHyperplane.signedNormalCoordinate_coordinateHyperplane]
  change -(∫ x in {x : Space 1 | 0 < x constantJumpRegressionIndex},
      fderiv ℝ constantJumpRegressionGaussian x
        (Space.basis constantJumpRegressionIndex) * 7) = 7
  rw [integral_mul_const, constantJumpRegression_raw_halfSpaceDerivative]
  norm_num

/-- Direct expansion of the transported coefficient sheet gives `7`. -/
lemma constantJumpRegression_raw_sheet :
    coordinateHyperplaneSheet 0 constantJumpRegressionIndex (7 : ℝ)
        constantJumpRegressionGaussian = 7 := by
  rw [coordinateHyperplaneSheet, ContinuousLinearMap.smulRight_apply,
    coordinateHyperplaneDeltaDistribution, distributionOfEuclideanCoordinates_apply]
  rw [show constantJumpRegressionIndex = Fin.last 0 by rfl,
    Physlib.Distribution.coordinateHyperplaneDelta_zero_apply]
  simp [basisCoordinateSchwartz, constantJumpRegressionGaussian,
    InnerProductSpace.gaussian_apply]

/-- The independently expanded derivative and sheet values agree. -/
lemma constantJumpRegression_raw_agreement :
    distDeriv constantJumpRegressionIndex
        (OrientedAffineHyperplane.distOfSidewiseFunction
          (OrientedAffineHyperplane.coordinateHyperplane constantJumpRegressionIndex)
            (OrientedAffineHyperplane.coordinatePositiveConstantField (7 : ℝ))
            (OrientedAffineHyperplane.coordinatePositiveConstantField_isDistBounded 7))
        constantJumpRegressionGaussian =
      coordinateHyperplaneSheet 0 constantJumpRegressionIndex (7 : ℝ)
        constantJumpRegressionGaussian := by
  rw [constantJumpRegression_raw_positiveDerivative, constantJumpRegression_raw_sheet]

/-- Direct expansion after reversing the derivative direction gives `-7`. -/
lemma constantJumpRegression_raw_negativeDerivative :
    Physlib.Distribution.fderivD ℝ
        (OrientedAffineHyperplane.distOfSidewiseFunction
          (OrientedAffineHyperplane.coordinateHyperplane constantJumpRegressionIndex)
            (OrientedAffineHyperplane.coordinatePositiveConstantField (7 : ℝ))
            (OrientedAffineHyperplane.coordinatePositiveConstantField_isDistBounded 7))
        constantJumpRegressionGaussian (-Space.basis constantJumpRegressionIndex) = -7 := by
  rw [Physlib.Distribution.fderivD_apply,
    OrientedAffineHyperplane.distOfSidewiseFunction_apply]
  simp only [SchwartzMap.evalCLM_apply_apply, SchwartzMap.fderivCLM_apply,
    OrientedAffineHyperplane.coordinatePositiveConstantField, map_neg, smul_eq_mul,
    mul_zero, integral_zero, zero_add]
  simp only [OrientedAffineHyperplane.openHalfSpace,
    OrientedAffineHyperplane.Side.sign_positive, one_mul,
    OrientedAffineHyperplane.signedNormalCoordinate_coordinateHyperplane]
  have hintegrand :
      (fun x : Space 1 =>
        -(fderiv ℝ constantJumpRegressionGaussian x
          (Space.basis constantJumpRegressionIndex)) * 7) =
        fun x => -(fderiv ℝ constantJumpRegressionGaussian x
          (Space.basis constantJumpRegressionIndex) * 7) := by
    funext x
    ring
  rw [hintegrand, integral_neg, neg_neg, integral_mul_const,
    constantJumpRegression_raw_halfSpaceDerivative]
  norm_num

/-!
## B. Two-dimensional coordinate fixture
-/

/-- The selected first coordinate of the two-dimensional fixture. -/
def constantJumpRegressionSelected : Fin 2 := 0

/-- The nonselected second coordinate of the two-dimensional fixture. -/
def constantJumpRegressionOther : Fin 2 := 1

/-- The standard Gaussian on two-dimensional space. -/
def constantJumpRegressionGaussianTwo : SchwartzMap (Space 2) ℝ :=
  InnerProductSpace.stdGaussian (Space 2) ℝ

/-- A coordinate-asymmetric test: the square of the selected coordinate times the standard
Gaussian. -/
def constantJumpRegressionWeightedGaussian : SchwartzMap (Space 2) ℝ :=
  SchwartzMap.smulLeftCLM ℝ
    ((fun x : Space 2 => x constantJumpRegressionSelected) ^ 2)
    constantJumpRegressionGaussianTwo

@[simp]
lemma constantJumpRegressionWeightedGaussian_apply (x : Space 2) :
    constantJumpRegressionWeightedGaussian x =
      (x constantJumpRegressionSelected) ^ 2 * constantJumpRegressionGaussianTwo x := by
  have hcoordinate : Function.HasTemperateGrowth
      (fun y : Space 2 => y constantJumpRegressionSelected) := by
    simpa [Space.coordCLM_apply, Space.coord_apply] using
      (Space.coordCLM constantJumpRegressionSelected).hasTemperateGrowth
  have hweight := hcoordinate.pow 2
  rw [constantJumpRegressionWeightedGaussian]
  simpa [Pi.pow_apply, smul_eq_mul] using
    (SchwartzMap.smulLeftCLM_apply_apply hweight constantJumpRegressionGaussianTwo x)

/-- Direct expansion shows that the weighted test vanishes on the selected coordinate sheet. -/
lemma constantJumpRegression_selectedSheet_eq_zero :
    coordinateHyperplaneSheet 1 constantJumpRegressionSelected (7 : ℝ)
        constantJumpRegressionWeightedGaussian = 0 := by
  rw [coordinateHyperplaneSheet, ContinuousLinearMap.smulRight_apply,
    coordinateHyperplaneDeltaDistribution, distributionOfEuclideanCoordinates_apply,
    Physlib.Distribution.coordinateHyperplaneDelta_apply]
  simp_rw [basisCoordinateSchwartz_apply, constantJumpRegressionWeightedGaussian_apply]
  simp [constantJumpRegressionSelected,
    Physlib.Distribution.coordinateHyperplaneEmbedding]

/-- Direct expansion gives strictly positive mass on the swapped coordinate sheet. -/
lemma constantJumpRegression_otherSheet_pos :
    0 < coordinateHyperplaneSheet 1 constantJumpRegressionOther (7 : ℝ)
      constantJumpRegressionWeightedGaussian := by
  rw [coordinateHyperplaneSheet, ContinuousLinearMap.smulRight_apply,
    coordinateHyperplaneDeltaDistribution, distributionOfEuclideanCoordinates_apply,
    Physlib.Distribution.coordinateHyperplaneDelta_apply, smul_eq_mul]
  apply mul_pos
  · let restricted : SchwartzMap (EuclideanSpace ℝ (Fin 1)) ℝ :=
      Physlib.Distribution.coordinateHyperplaneRestriction 1 constantJumpRegressionOther
        (basisCoordinateSchwartz 2 constantJumpRegressionWeightedGaussian)
    change 0 < ∫ x, restricted x
    apply integral_pos_of_integrable_nonneg_nonzero restricted.continuous
      (integrable restricted)
    · intro x
      change 0 ≤ constantJumpRegressionWeightedGaussian
        (Space.basis.repr.symm
          (Physlib.Distribution.coordinateHyperplaneEmbedding 1
            constantJumpRegressionOther x))
      rw [constantJumpRegressionWeightedGaussian_apply]
      apply mul_nonneg (sq_nonneg _)
      rw [constantJumpRegressionGaussianTwo, InnerProductSpace.gaussian_apply]
      exact Real.exp_nonneg _
    · let one : EuclideanSpace ℝ (Fin 1) :=
        Physlib.Distribution.coordinateNormalEmbedding 0 (Fin.last 0) 1
      show restricted one ≠ 0
      change constantJumpRegressionWeightedGaussian
        (Space.basis.repr.symm
          (Physlib.Distribution.coordinateHyperplaneEmbedding 1
            constantJumpRegressionOther one)) ≠ 0
      rw [constantJumpRegressionWeightedGaussian_apply]
      apply mul_ne_zero
      · have hindex : constantJumpRegressionSelected =
            constantJumpRegressionOther.succAbove (Fin.last 0) := by
            decide
        rw [Space.basis_repr_symm_apply, hindex,
          Physlib.Distribution.coordinateHyperplaneEmbedding,
          Physlib.Distribution.coordinateSplit_symm_apply_succAbove]
        simp [one, Physlib.Distribution.coordinateNormalEmbedding]
      · simp [constantJumpRegressionGaussianTwo, InnerProductSpace.gaussian_apply]
  · norm_num

/-- The asymmetric fixture rejects replacing the selected coordinate sheet by the other one. -/
lemma constantJumpRegression_wrongCoordinate_ne :
    coordinateHyperplaneSheet 1 constantJumpRegressionSelected (7 : ℝ)
        constantJumpRegressionWeightedGaussian ≠
      coordinateHyperplaneSheet 1 constantJumpRegressionOther (7 : ℝ)
        constantJumpRegressionWeightedGaussian := by
  rw [constantJumpRegression_selectedSheet_eq_zero]
  exact ne_of_lt constantJumpRegression_otherSheet_pos

end
end Space
