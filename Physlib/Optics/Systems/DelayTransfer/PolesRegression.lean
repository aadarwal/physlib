/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Systems.DelayTransfer.Poles

/-!
# Regression tests for candidate and actual poles

## i. Overview

The raw response `(q - 1) / (q - 1)` has an internal candidate at `q = 1`, but its reduced
response is `1 / 1` and has no transfer-function pole. The common factor is recorded explicitly,
and the fixture proves both membership in the candidate set and nonmembership in the actual set.

This is a load-bearing negative regression. Any future theorem that makes every candidate an
actual pole without a no-cancellation or observability hypothesis fails on this fixture.

## ii. Key results

- `cancellationRegression_candidate_not_actual`: `q = 1` is candidate but not actual.
- `cancellationRegression_not_noPoleCancellation`: the explicit criterion correctly fails.
- `cancellationRegression_not_candidatePoles_subset_actualPoles`: the ungated converse is false.

## iii. Table of contents

- A. A completely cancelled linear factor

## iv. References and non-claims

This regression implements the cancellation counterexample required by `goal.md` section H.4
S4P. It is algebraic and source-neutral. The candidate is not called a physical resonance, and no
network reachability, observability, stability, frequency, or dispersion claim is made.
-/

@[expose] public section

namespace Optics.DelayTransfer

noncomputable section

open Polynomial

/-!

## A. A completely cancelled linear factor

-/

/-- The reduced constant response left after complete linear cancellation. -/
def cancellationRegressionReduced : ReducedRationalResponse where
  numerator := 1
  denominator := 1
  numerator_ne_zero := one_ne_zero
  denominator_ne_zero := one_ne_zero
  isCoprime := isCoprime_one_left

/-- The raw response `(q - 1) / (q - 1)` reduced to `1 / 1`. -/
def cancellationRegression : RationalReduction where
  rawNumerator := Polynomial.X - Polynomial.C 1
  rawDenominator := Polynomial.X - Polynomial.C 1
  cancelledFactor := Polynomial.X - Polynomial.C 1
  reduced := cancellationRegressionReduced
  cancelledFactor_ne_zero := Polynomial.X_sub_C_ne_zero 1
  rawNumerator_eq := by simp [cancellationRegressionReduced]
  rawDenominator_eq := by simp [cancellationRegressionReduced]

/-- The point `q = 1` is an unreduced candidate but not an actual transfer pole. -/
lemma cancellationRegression_candidate_not_actual :
    (1 : ℂ) ∈ cancellationRegression.candidatePoles ∧
      (1 : ℂ) ∉ cancellationRegression.actualPoles := by
  constructor <;>
    simp [RationalReduction.candidatePoles, RationalReduction.actualPoles,
      ReducedRationalResponse.poles, cancellationRegression,
      cancellationRegressionReduced]

/-- The cancelled linear factor violates the explicit no-cancellation criterion. -/
lemma cancellationRegression_not_noPoleCancellation :
    ¬ cancellationRegression.NoPoleCancellation := by
  intro hNoCancellation
  exact hNoCancellation 1 (by simp [cancellationRegression])

/-- Without the no-cancellation criterion, candidate poles need not be actual poles. -/
lemma cancellationRegression_not_candidatePoles_subset_actualPoles :
    ¬ cancellationRegression.candidatePoles ⊆ cancellationRegression.actualPoles := by
  intro hSubset
  exact cancellationRegression_candidate_not_actual.2
    (hSubset cancellationRegression_candidate_not_actual.1)

end

end Optics.DelayTransfer
