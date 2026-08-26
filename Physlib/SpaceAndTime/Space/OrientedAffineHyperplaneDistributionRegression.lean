/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.SpaceAndTime.Space.OrientedAffineHyperplaneDistribution

/-!
# Regression tests for sidewise function distributions

## i. Overview

A one-dimensional bump is supported strictly on the positive side of the coordinate hyperplane.
Direct expansion of the defining indicators gives a positive value when the nonzero field is
assigned to that side and zero when the same field is assigned to the negative side. This pins the
side choice independently of the production application lemma.

## ii. Key results

- `sidewiseDistributionRegression_positive_pos`: the positive-side field has positive action.
- `sidewiseDistributionRegression_wrongSide_eq_zero`: moving the same field to the negative side
  makes its action on the positive-supported test vanish.
- `sidewiseDistributionRegression_positive_ne_wrongSide`: the hostile side exchange changes the
  distribution value.

## iii. Table of contents

- A. Coordinate fixture
- B. Direct sidewise evaluation

## iv. References

This is an algebraic and analytic regression for neutral distribution infrastructure. It does not
state a boundary jump or electromagnetic interface law.
-/

@[expose] public section

open MeasureTheory SchwartzMap

namespace Space

noncomputable section

/-!
## A. Coordinate fixture
-/

/-- The positive coordinate direction in one-dimensional space. -/
def sidewiseDistributionRegressionNormal : Direction 1 where
  unit := ⟨![(1 : ℝ)]⟩
  norm := by
    rw [Space.norm_eq]
    simp

/-- The oriented point hyperplane at the origin, with positive side `x > 0`. -/
def sidewiseDistributionRegressionPlane : OrientedAffineHyperplane 1 where
  point := 0
  normal := sidewiseDistributionRegressionNormal

/-- The center of the positive-side bump test. -/
def sidewiseDistributionRegressionCenter : Space 1 :=
  ⟨![(2 : ℝ)]⟩

/-- A smooth bump whose support is the radius-one ball around coordinate `2`. -/
def sidewiseDistributionRegressionBump :
    ContDiffBump sidewiseDistributionRegressionCenter where
  rIn := 1 / 2
  rOut := 1
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The compactly supported bump bundled as a Schwartz test. -/
def sidewiseDistributionRegressionTest : SchwartzMap (Space 1) ℝ :=
  sidewiseDistributionRegressionBump.hasCompactSupport.toSchwartzMap
    sidewiseDistributionRegressionBump.contDiff

@[simp]
lemma sidewiseDistributionRegressionTest_apply (x : Space 1) :
    sidewiseDistributionRegressionTest x = sidewiseDistributionRegressionBump x :=
  rfl

/-- The fixture plane's signed normal coordinate is its unique spatial coordinate. -/
lemma sidewiseDistributionRegression_signedNormalCoordinate (x : Space 1) :
    sidewiseDistributionRegressionPlane.signedNormalCoordinate x = x 0 := by
  simp [OrientedAffineHyperplane.signedNormalCoordinate,
    OrientedAffineHyperplane.normalVector, sidewiseDistributionRegressionPlane,
    sidewiseDistributionRegressionNormal, PiLp.inner_apply,
    RCLike.inner_apply, Space.basis_repr_apply]

/-- The bump test is supported strictly in the positive open half-space. -/
lemma sidewiseDistributionRegression_support_subset_positive :
    Function.support sidewiseDistributionRegressionTest ⊆
      sidewiseDistributionRegressionPlane.openHalfSpace .positive := by
  intro x hx
  have hball : x ∈ Metric.ball sidewiseDistributionRegressionCenter 1 := by
    change x ∈ Function.support (sidewiseDistributionRegressionBump : Space 1 → ℝ) at hx
    rw [sidewiseDistributionRegressionBump.support_eq] at hx
    simpa [sidewiseDistributionRegressionBump] using hx
  have hdist : dist x sidewiseDistributionRegressionCenter < 1 :=
    Metric.mem_ball.mp hball
  rw [Space.dist_eq_norm, Space.norm_eq, Fin.sum_univ_one] at hdist
  simp only [sidewiseDistributionRegressionCenter, Space.sub_apply,
    Matrix.cons_val_fin_one,
    Real.sqrt_sq_eq_abs] at hdist
  change 0 < OrientedAffineHyperplane.Side.positive.sign *
    sidewiseDistributionRegressionPlane.signedNormalCoordinate x
  rw [sidewiseDistributionRegression_signedNormalCoordinate]
  simp only [OrientedAffineHyperplane.Side.sign_positive, one_mul]
  linarith [(abs_lt.mp hdist).1]

/-- The bump test has strictly positive total integral. -/
lemma sidewiseDistributionRegression_integral_pos :
    0 < ∫ x : Space 1, sidewiseDistributionRegressionTest x := by
  apply integral_pos_of_integrable_nonneg_nonzero
    sidewiseDistributionRegressionTest.continuous
    (integrable sidewiseDistributionRegressionTest)
  · intro x
    exact sidewiseDistributionRegressionBump.nonneg
  · show sidewiseDistributionRegressionTest sidewiseDistributionRegressionCenter ≠ 0
    rw [sidewiseDistributionRegressionTest_apply]
    exact ne_of_gt (sidewiseDistributionRegressionBump.pos_of_mem_ball
      (Metric.mem_ball_self sidewiseDistributionRegressionBump.rOut_pos))

/-- Restricting the bump integral to the positive half-space does not change it. -/
lemma sidewiseDistributionRegression_integral_positive_eq :
    (∫ x in sidewiseDistributionRegressionPlane.openHalfSpace .positive,
        sidewiseDistributionRegressionTest x) =
      ∫ x : Space 1, sidewiseDistributionRegressionTest x := by
  rw [← MeasureTheory.integral_indicator
    (sidewiseDistributionRegressionPlane.measurableSet_openHalfSpace .positive)]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ sidewiseDistributionRegressionPlane.openHalfSpace .positive
  · simp [Set.indicator_of_mem hx]
  · have hsupport : x ∉ Function.support sidewiseDistributionRegressionTest := by
      intro h
      exact hx (sidewiseDistributionRegression_support_subset_positive h)
    rw [Set.indicator_of_notMem hx, Function.notMem_support.mp hsupport]

/-- The bump integral over the negative half-space vanishes. -/
lemma sidewiseDistributionRegression_integral_negative_eq_zero :
    (∫ x in sidewiseDistributionRegressionPlane.openHalfSpace .negative,
        sidewiseDistributionRegressionTest x) = 0 := by
  calc
    (∫ x in sidewiseDistributionRegressionPlane.openHalfSpace .negative,
        sidewiseDistributionRegressionTest x) =
        ∫ x in sidewiseDistributionRegressionPlane.openHalfSpace .negative, (0 : ℝ) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem
        (sidewiseDistributionRegressionPlane.measurableSet_openHalfSpace .negative)]
        with x hx
      have hnotPositive :
          x ∉ sidewiseDistributionRegressionPlane.openHalfSpace .positive := by
        change 0 < OrientedAffineHyperplane.Side.negative.sign *
          sidewiseDistributionRegressionPlane.signedNormalCoordinate x at hx
        change ¬ 0 < OrientedAffineHyperplane.Side.positive.sign *
          sidewiseDistributionRegressionPlane.signedNormalCoordinate x
        rw [sidewiseDistributionRegression_signedNormalCoordinate] at hx ⊢
        simp only [OrientedAffineHyperplane.Side.sign_negative, neg_one_mul,
          OrientedAffineHyperplane.Side.sign_positive, one_mul] at hx ⊢
        linarith
      apply Function.notMem_support.mp
      intro hsupport
      exact hnotPositive (sidewiseDistributionRegression_support_subset_positive hsupport)
    _ = 0 := by simp

/-!
## B. Direct sidewise evaluation
-/

/-- A scalar field equal to seven on the positive side and zero on the negative side. -/
def sidewiseDistributionRegressionPositiveField :
    OrientedAffineHyperplane.Side → Space 1 → ℝ
  | .negative, _ => 0
  | .positive, _ => 7

/-- A hostile field obtained by assigning the same nonzero value to the negative side. -/
def sidewiseDistributionRegressionWrongSideField :
    OrientedAffineHyperplane.Side → Space 1 → ℝ
  | .negative, _ => 7
  | .positive, _ => 0

/-- Each constant side of the positive-field fixture is distribution bounded. -/
lemma sidewiseDistributionRegressionPositiveField_isDistBounded :
    ∀ side, IsDistBounded (sidewiseDistributionRegressionPositiveField side) := by
  intro side
  cases side
  · change IsDistBounded (fun _ : Space 1 => (0 : ℝ))
    fun_prop
  · change IsDistBounded (fun _ : Space 1 => (7 : ℝ))
    fun_prop

/-- Each constant side of the hostile wrong-side fixture is distribution bounded. -/
lemma sidewiseDistributionRegressionWrongSideField_isDistBounded :
    ∀ side, IsDistBounded (sidewiseDistributionRegressionWrongSideField side) := by
  intro side
  cases side
  · change IsDistBounded (fun _ : Space 1 => (7 : ℝ))
    fun_prop
  · change IsDistBounded (fun _ : Space 1 => (0 : ℝ))
    fun_prop

/-- Direct expansion gives positive action when the nonzero field occupies the positive side. -/
lemma sidewiseDistributionRegression_positive_pos :
    0 < sidewiseDistributionRegressionPlane.distOfSidewiseFunction
      sidewiseDistributionRegressionPositiveField
      sidewiseDistributionRegressionPositiveField_isDistBounded
      sidewiseDistributionRegressionTest := by
  rw [OrientedAffineHyperplane.distOfSidewiseFunction, _root_.add_apply,
    distOfFunctionOn, distOfFunctionOn, distOfFunction_apply, distOfFunction_apply]
  change 0 <
    (∫ x, sidewiseDistributionRegressionTest x •
      (sidewiseDistributionRegressionPlane.openHalfSpace .negative).indicator
        (fun _ => (0 : ℝ)) x) +
    ∫ x, sidewiseDistributionRegressionTest x •
      (sidewiseDistributionRegressionPlane.openHalfSpace .positive).indicator
        (fun _ => (7 : ℝ)) x
  simp only [Set.indicator_zero, smul_zero, integral_zero, zero_add]
  rw [show (∫ x, sidewiseDistributionRegressionTest x •
      (sidewiseDistributionRegressionPlane.openHalfSpace .positive).indicator
        (fun _ => (7 : ℝ)) x) =
      7 * ∫ x in sidewiseDistributionRegressionPlane.openHalfSpace .positive,
        sidewiseDistributionRegressionTest x by
    rw [← MeasureTheory.integral_indicator
      (sidewiseDistributionRegressionPlane.measurableSet_openHalfSpace .positive),
      ← MeasureTheory.integral_const_mul]
    congr 1
    funext x
    by_cases hx : x ∈ sidewiseDistributionRegressionPlane.openHalfSpace .positive
    · simp [Set.indicator_of_mem hx, mul_comm]
    · simp [Set.indicator_of_notMem hx]]
  rw [sidewiseDistributionRegression_integral_positive_eq]
  exact mul_pos (by norm_num) sidewiseDistributionRegression_integral_pos

/-- Direct expansion gives zero when the same nonzero field is assigned to the negative side. -/
lemma sidewiseDistributionRegression_wrongSide_eq_zero :
    sidewiseDistributionRegressionPlane.distOfSidewiseFunction
      sidewiseDistributionRegressionWrongSideField
      sidewiseDistributionRegressionWrongSideField_isDistBounded
      sidewiseDistributionRegressionTest = 0 := by
  rw [OrientedAffineHyperplane.distOfSidewiseFunction, _root_.add_apply,
    distOfFunctionOn, distOfFunctionOn, distOfFunction_apply, distOfFunction_apply]
  change
    (∫ x, sidewiseDistributionRegressionTest x •
      (sidewiseDistributionRegressionPlane.openHalfSpace .negative).indicator
        (fun _ => (7 : ℝ)) x) +
    (∫ x, sidewiseDistributionRegressionTest x •
      (sidewiseDistributionRegressionPlane.openHalfSpace .positive).indicator
        (fun _ => (0 : ℝ)) x) = 0
  simp only [Set.indicator_zero, smul_zero, integral_zero, add_zero]
  rw [show (∫ x, sidewiseDistributionRegressionTest x •
      (sidewiseDistributionRegressionPlane.openHalfSpace .negative).indicator
        (fun _ => (7 : ℝ)) x) =
      7 * ∫ x in sidewiseDistributionRegressionPlane.openHalfSpace .negative,
        sidewiseDistributionRegressionTest x by
    rw [← MeasureTheory.integral_indicator
      (sidewiseDistributionRegressionPlane.measurableSet_openHalfSpace .negative),
      ← MeasureTheory.integral_const_mul]
    congr 1
    funext x
    by_cases hx : x ∈ sidewiseDistributionRegressionPlane.openHalfSpace .negative
    · simp [Set.indicator_of_mem hx, mul_comm]
    · simp [Set.indicator_of_notMem hx]]
  rw [sidewiseDistributionRegression_integral_negative_eq_zero, mul_zero]

/-- Exchanging the positive and negative side assignments changes the distribution value. -/
lemma sidewiseDistributionRegression_positive_ne_wrongSide :
    sidewiseDistributionRegressionPlane.distOfSidewiseFunction
        sidewiseDistributionRegressionPositiveField
        sidewiseDistributionRegressionPositiveField_isDistBounded
        sidewiseDistributionRegressionTest ≠
      sidewiseDistributionRegressionPlane.distOfSidewiseFunction
        sidewiseDistributionRegressionWrongSideField
        sidewiseDistributionRegressionWrongSideField_isDistBounded
        sidewiseDistributionRegressionTest := by
  rw [sidewiseDistributionRegression_wrongSide_eq_zero]
  exact ne_of_gt sidewiseDistributionRegression_positive_pos

end
end Space
