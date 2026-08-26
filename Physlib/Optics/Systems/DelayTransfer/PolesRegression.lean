/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Systems.DelayTransfer.Poles

/-!
# Regression tests for abstract polynomial cancellation

## i. Overview

The abstract raw quotient `(q - 1) / (q - 1)` has a raw denominator root at `q = 1`, but its
reduced quotient is `1 / 1` and has no reduced denominator root. The common factor is explicit,
making this a fixture-bearing check of the polynomial-reduction schema. It is not a netlist or an
internal-singularity example.

## ii. Key results

- `cancellationRegression_raw_root_not_reduced`: `q = 1` disappears after reduction.
- `cancellationRegression_not_noPoleCancellation`: the pointwise criterion fails at `q = 1`.
- `cancellationRegression_not_rawRoots_subset_reducedPoles`: the ungated converse is false.

## iii. Table of contents

- A. A completely cancelled linear factor

## iv. References and non-claims

This regression is algebraic and source-neutral. It checks only an abstract polynomial quotient;
it does not exhibit a singular internal operator or a cancelled network response. A genuine
singular-but-cancelled netlist fixture remains future work after symbolic response elimination.
No network reachability, observability, stability, frequency, or dispersion claim is made.
-/

@[expose] public section

namespace Optics.DelayTransfer

noncomputable section

open Polynomial

/-!

## A. A completely cancelled linear factor

-/

/-- The reduced constant quotient left after complete linear cancellation. -/
def cancellationRegressionReduced : ReducedRationalResponse where
  numerator := 1
  denominator := 1
  numerator_ne_zero := one_ne_zero
  denominator_ne_zero := one_ne_zero
  isCoprime := isCoprime_one_left

/-- The raw quotient `(q - 1) / (q - 1)` reduced to `1 / 1`. -/
def cancellationRegression : RationalReduction where
  rawNumerator := Polynomial.X - Polynomial.C 1
  rawDenominator := Polynomial.X - Polynomial.C 1
  cancelledFactor := Polynomial.X - Polynomial.C 1
  reduced := cancellationRegressionReduced
  cancelledFactor_ne_zero := Polynomial.X_sub_C_ne_zero 1
  rawNumerator_eq := by simp [cancellationRegressionReduced]
  rawDenominator_eq := by simp [cancellationRegressionReduced]

/-- The point `q = 1` is a raw denominator root but not a reduced denominator root. -/
lemma cancellationRegression_raw_root_not_reduced :
    (1 : ℂ) ∈ cancellationRegression.rawDenominatorRoots ∧
      (1 : ℂ) ∉ cancellationRegression.reducedPoles := by
  constructor <;>
    simp [RationalReduction.rawDenominatorRoots, RationalReduction.reducedPoles,
      ReducedRationalResponse.poles, cancellationRegression,
      cancellationRegressionReduced]

/-- The cancelled linear factor violates the explicit no-cancellation criterion. -/
lemma cancellationRegression_not_noPoleCancellation :
    ¬ cancellationRegression.NoPoleCancellation 1 := by
  intro hNoCancellation
  exact hNoCancellation (by simp [cancellationRegression])

/-- Without the no-cancellation criterion, raw roots need not remain reduced roots. -/
lemma cancellationRegression_not_rawRoots_subset_reducedPoles :
    ¬ cancellationRegression.rawDenominatorRoots ⊆ cancellationRegression.reducedPoles := by
  intro hSubset
  exact cancellationRegression_raw_root_not_reduced.2
    (hSubset cancellationRegression_raw_root_not_reduced.1)

end

end Optics.DelayTransfer
