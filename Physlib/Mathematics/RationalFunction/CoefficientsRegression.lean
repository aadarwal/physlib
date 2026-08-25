/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Mathematics.RationalFunction.Coefficients

/-!
# Regression tests for executable rational-function coefficients

## i. Overview

These tests pin list normalization, constant-term-first Horner evaluation, rejection of a zero
stored denominator, and guarded agreement with Mathlib's canonical rational-function evaluation.
A canceled fraction distinguishes the conservative stored-denominator guard from canonical
regularity. At a genuine pole, Mathlib's total rational-function evaluation returns algebraic zero;
the failed guard records that this value has no certified point-evaluation interpretation here.

## ii. Scope

The tests concern exact algebraic representation and point evaluation. They attach no frequency
units, analytic continuation, causality, stability, or physical response interpretation.

## iii. Table of contents

- A. Normalized polynomial lists
- B. Unreduced rational fractions
- C. Guarded evaluation

-/

@[expose] public section

namespace Physlib

/-!

## A. Normalized polynomial lists

-/

/-- A little-endian polynomial whose redundant high-degree zeros are removed. -/
def coefficientsRegressionPolynomial : PolynomialCoefficients ℚ :=
  PolynomialCoefficients.ofList [1, 2, 0, 0]

/-- Normalization removes every trailing coefficient zero. -/
lemma coefficientsRegression_normalized :
    coefficientsRegressionPolynomial.coefficients = [1, 2] := by
  decide

/-- An all-zero input list normalizes to the unique empty zero presentation. -/
lemma coefficientsRegression_allZero :
    (PolynomialCoefficients.ofList [0, 0] : PolynomialCoefficients ℚ).coefficients = [] := by
  decide

/-- A little-endian order sentinel representing `1 - 2q²`. -/
def coefficientsRegressionLittleEndian : PolynomialCoefficients ℚ :=
  PolynomialCoefficients.ofList [1, 0, -2]

/-- The order-sentinel polynomial is already normalized. -/
lemma coefficientsRegression_littleEndian_coefficients :
    coefficientsRegressionLittleEndian.coefficients = [1, 0, -2] := by
  decide

/-- Horner evaluation reads `[1, 0, -2]` as `1 - 2q²`, not the reversed polynomial. -/
lemma coefficientsRegression_littleEndian :
    coefficientsRegressionLittleEndian.eval (RingHom.id ℚ) 2 = -7 := by
  unfold PolynomialCoefficients.eval
  rw [coefficientsRegression_littleEndian_coefficients]
  norm_num

/-!

## B. Unreduced rational fractions

-/

/-- The unreduced fraction `(q² - 1) / (q - 1)`. -/
def coefficientsRegressionCanceled : RationalCoefficients ℚ :=
  (RationalCoefficients.ofLists? [-1, 0, 1] [-1, 1]).get (by decide)

/-- The genuine-pole fraction `1 / (q - 1)`. -/
def coefficientsRegressionPole : RationalCoefficients ℚ :=
  (RationalCoefficients.ofLists? [1] [-1, 1]).get (by decide)

/-- The canceled fixture retains its normalized numerator list. -/
lemma coefficientsRegression_canceled_numerator :
    coefficientsRegressionCanceled.numerator.coefficients = [-1, 0, 1] := by
  decide

/-- The canceled fixture retains its normalized denominator list. -/
lemma coefficientsRegression_canceled_denominator :
    coefficientsRegressionCanceled.denominator.coefficients = [-1, 1] := by
  decide

/-- The genuine-pole fixture has the same stored denominator. -/
lemma coefficientsRegression_pole_denominator :
    coefficientsRegressionPole.denominator.coefficients = [-1, 1] := by
  decide

/-- The genuine-pole fixture has unit stored numerator. -/
lemma coefficientsRegression_pole_numerator :
    coefficientsRegressionPole.numerator.coefficients = [1] := by
  decide

/-- The genuine-pole fixture denotes exactly `1 / (q - 1)` as a rational function. -/
lemma coefficientsRegression_pole_toRatFunc :
    coefficientsRegressionPole.toRatFunc =
      RatFunc.mk 1 (Polynomial.X - 1) := by
  unfold RationalCoefficients.toRatFunc PolynomialCoefficients.toPolynomial
  rw [coefficientsRegression_pole_numerator, coefficientsRegression_pole_denominator]
  simp only [List.foldr_cons, List.foldr_nil]
  congr 1
  · simp
  · simp [sub_eq_add_neg, add_comm]

/-- Canonical rational-function interpretation cancels the stored common factor exactly. -/
lemma coefficientsRegression_canceled_toRatFunc :
    coefficientsRegressionCanceled.toRatFunc =
      algebraMap (Polynomial ℚ) (RatFunc ℚ) (Polynomial.X + 1) := by
  rw [RationalCoefficients.toRatFunc]
  apply (RatFunc.mk_eq_mk
    coefficientsRegressionCanceled.denominator_toPolynomial_ne_zero (by simp)).2
  unfold PolynomialCoefficients.toPolynomial
  rw [coefficientsRegression_canceled_numerator,
    coefficientsRegression_canceled_denominator]
  simp only [List.foldr_cons, List.foldr_nil]
  rw [Algebra.algebraMap_self_apply]
  norm_num
  ring

/-- The constructor rejects an empty denominator after normalization. -/
lemma coefficientsRegression_rejectsEmptyDenominator :
    RationalCoefficients.ofLists? (K := ℚ) [1] [] = none := by
  decide

/-- The constructor also rejects a nonempty list that normalizes to the zero polynomial. -/
lemma coefficientsRegression_rejectsZeroDenominator :
    RationalCoefficients.ofLists? (K := ℚ) [1] [0, 0] = none := by
  decide

/-!

## C. Guarded evaluation

-/

/-- The canceled presentation deliberately fails the stored guard at its removable zero. -/
lemma coefficientsRegression_canceled_guard_fails :
    ¬coefficientsRegressionCanceled.StoredDenominatorNonzeroAt (RingHom.id ℚ) 1 := by
  unfold RationalCoefficients.StoredDenominatorNonzeroAt PolynomialCoefficients.eval
  rw [coefficientsRegression_canceled_denominator]
  norm_num

/-- The genuine pole also fails the stored guard at `q = 1`. -/
lemma coefficientsRegression_pole_guard_fails :
    ¬coefficientsRegressionPole.StoredDenominatorNonzeroAt (RingHom.id ℚ) 1 := by
  unfold RationalCoefficients.StoredDenominatorNonzeroAt PolynomialCoefficients.eval
  rw [coefficientsRegression_pole_denominator]
  norm_num

/-- Canonical evaluation sees the removable stored zero and returns the reduced value two. -/
lemma coefficientsRegression_canceled_ratFunc_eval_one :
    RatFunc.eval (RingHom.id ℚ) 1 coefficientsRegressionCanceled.toRatFunc = 2 := by
  rw [coefficientsRegression_canceled_toRatFunc, RatFunc.eval_algebraMap]
  norm_num

/-- Total rational-function evaluation returns algebraic zero at the genuine pole. -/
lemma coefficientsRegression_pole_ratFunc_eval_one :
    RatFunc.eval (RingHom.id ℚ) 1 coefficientsRegressionPole.toRatFunc = 0 := by
  classical
  let _ : DecidableEq ℚ := Classical.decEq ℚ
  rw [coefficientsRegression_pole_toRatFunc, RatFunc.mk_eq_div]
  apply RatFunc.eval_eq_zero_of_eval₂_denom_eq_zero
  have hDenominator : (Polynomial.X - (1 : Polynomial ℚ)) ≠ 0 := by
    simpa using Polynomial.X_sub_C_ne_zero (1 : ℚ)
  rw [RatFunc.denom_div (1 : Polynomial ℚ) hDenominator]
  simp

/-- The canceled presentation satisfies its stored guard away from the common zero. -/
lemma coefficientsRegression_canceled_guard_two :
    coefficientsRegressionCanceled.StoredDenominatorNonzeroAt (RingHom.id ℚ) 2 := by
  unfold RationalCoefficients.StoredDenominatorNonzeroAt PolynomialCoefficients.eval
  rw [coefficientsRegression_canceled_denominator]
  norm_num

/-- Away from the canceled factor, direct executable evaluation gives the expected value. -/
lemma coefficientsRegression_canceled_evalAt_two :
    coefficientsRegressionCanceled.evalAt (RingHom.id ℚ) 2 = 3 := by
  unfold RationalCoefficients.evalAt PolynomialCoefficients.eval
  rw [coefficientsRegression_canceled_numerator,
    coefficientsRegression_canceled_denominator]
  norm_num

/-- Guarded canonical evaluation agrees with executable evaluation at `q = 2`. -/
lemma coefficientsRegression_canceled_ratFunc_eval_two :
    RatFunc.eval (RingHom.id ℚ) 2 coefficientsRegressionCanceled.toRatFunc = 3 := by
  have hGuard :
      coefficientsRegressionCanceled.StoredDenominatorNonzeroAt (RingHom.id ℚ) 2 := by
    exact coefficientsRegression_canceled_guard_two
  rw [coefficientsRegressionCanceled.ratFunc_eval_eq_evalAt (RingHom.id ℚ) 2 hGuard]
  exact coefficientsRegression_canceled_evalAt_two

/-- Evaluation on the regular-at-point subring preserves addition for guarded coefficients. -/
lemma coefficientsRegression_regularAt_add :
    let regular := coefficientsRegressionCanceled.toRegularAt (RingHom.id ℚ) 2
      coefficientsRegression_canceled_guard_two
    RationalFunction.evalRegularAt (RingHom.id ℚ) 2 (regular + regular) = 6 := by
  dsimp only
  rw [map_add, RationalCoefficients.evalRegularAt_toRegularAt,
    coefficientsRegression_canceled_evalAt_two]
  norm_num

/-- Evaluation on the regular-at-point subring also preserves multiplication. -/
lemma coefficientsRegression_regularAt_mul :
    let regular := coefficientsRegressionCanceled.toRegularAt (RingHom.id ℚ) 2
      coefficientsRegression_canceled_guard_two
    RationalFunction.evalRegularAt (RingHom.id ℚ) 2 (regular * regular) = 9 := by
  dsimp only
  rw [map_mul, RationalCoefficients.evalRegularAt_toRegularAt,
    coefficientsRegression_canceled_evalAt_two]
  norm_num

end Physlib
