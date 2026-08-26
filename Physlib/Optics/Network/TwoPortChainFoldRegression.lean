/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.TwoPortChainFold
public import Physlib.Optics.Network.TwoPortChainRegression

/-!
# Regression tests for finite backward-first chain folds

## i. Overview

The two nonsymmetric matrices from the independent two-port chain regression are folded in
input-to-output list order. Direct entry expansion gives one for the implemented fold and seven
for the reversed product, so the fixture would fail if the list orientation were reversed.

## ii. Key results

- `twoPortChainFoldRegression_fold_entry`: the later-on-the-left fold has leading entry one.
- `twoPortChainFoldRegression_reverse_entry`: the reversed product has leading entry seven.
- `twoPortChainFoldRegression_ne_reverse`: the two ordered products are unequal.

## iii. Table of contents

- A. Asymmetric two-element fold

## iv. References

This is a Physlib-original algebraic fixture. It makes no ring, propagation, termination,
passivity, reciprocity, causality, source-parity, or electromagnetic claim.

-/

@[expose] public section

namespace Optics

noncomputable section

/-!

## A. Asymmetric two-element fold

-/

/-- The asymmetric two-element input-to-output chain list. -/
def twoPortChainFoldRegressionList :
    List (BackwardFirstChainTransform Unit Unit) :=
  [twoPortChainRegressionFirst, twoPortChainRegressionSecond]

/-- Direct expansion of the fold gives leading entry one. -/
lemma twoPortChainFoldRegression_fold_entry :
    BackwardFirstChainTransform.fold twoPortChainFoldRegressionList
        (Sum.inl (BackwardWave.mk ())) (Sum.inl (BackwardWave.mk ())) = 1 := by
  norm_num [twoPortChainFoldRegressionList, BackwardFirstChainTransform.fold,
    Matrix.mul_apply, twoPortChainRegressionFirst, twoPortChainRegressionSecond,
    Fintype.sum_sum_type, BackwardWave.fintype_card, ForwardWave.fintype_card]

/-- Direct expansion of the reversed product gives leading entry seven. -/
lemma twoPortChainFoldRegression_reverse_entry :
    (twoPortChainRegressionFirst * twoPortChainRegressionSecond)
        (Sum.inl (BackwardWave.mk ())) (Sum.inl (BackwardWave.mk ())) = 7 := by
  norm_num [Matrix.mul_apply, twoPortChainRegressionFirst,
    twoPortChainRegressionSecond, Fintype.sum_sum_type,
    BackwardWave.fintype_card, ForwardWave.fintype_card]

/-- The finite fold is not the reversed matrix product. -/
lemma twoPortChainFoldRegression_ne_reverse :
    BackwardFirstChainTransform.fold twoPortChainFoldRegressionList ≠
      twoPortChainRegressionFirst * twoPortChainRegressionSecond := by
  intro hReverse
  have hEntry := congrFun
    (congrFun hReverse (Sum.inl (BackwardWave.mk ())))
      (Sum.inl (BackwardWave.mk ()))
  rw [twoPortChainFoldRegression_fold_entry,
    twoPortChainFoldRegression_reverse_entry] at hEntry
  norm_num at hEntry

end

end Optics
