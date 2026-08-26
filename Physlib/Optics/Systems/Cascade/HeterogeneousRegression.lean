/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Systems.Cascade.Heterogeneous

/-!
# Regression tests for heterogeneous DATE microring cascades

## i. Overview

Two arbitrary DATE stages are expanded entry by entry. The hand matrix below is written directly
from DATE's four ring entries and the two signed continuity factors. It does not call the
production stage product, the generic fold agreement theorem, or the heterogeneous cascade
theorem. Four independent entry lemmas compare it with the production two-stage composition.

The first stage is input-side and the second stage is output-side, so every hand expression uses
the second stage on the left. The separate asymmetric neutral regression in
`Physlib/Optics/Network/TwoPortChainFoldRegression.lean` rejects the reverse order mechanically.

## ii. Key results

- `dateCascadeRegressionHandProduct`: the hand-expanded two-ring DATE product.
- `dateCascadeRegression_twoRing_inl_inl` and the other three entry lemmas: all four matrix
  coordinates agree without using the H-03 headline theorem.

## iii. Table of contents

- A. Hand-expanded two-ring product

## iv. References and non-claims

DATE'14 Defs. 6--7 and Thm. 3 are summarized at `HOL-CORPUS.md:201-203`. This algebraic fixture
makes no quadruple-ring, lattice, termination, Sylvester, Chebyshev, resonance, dispersion,
bending-loss, causality, passivity, reciprocity, or electromagnetic-power claim. It exercises the
totalized matrices and therefore needs no pivot hypothesis; relational meaning remains gated by
the production theorem.
-/

@[expose] public section

namespace Optics

noncomputable section

namespace MicroringCascade

open MicroringSourceBridge

/-!

## A. Hand-expanded two-ring product

-/

/-- The two-stage DATE product expanded directly from the ring and continuity entries.

The first argument is input-side and the second is output-side. No production matrix fold or
stage-composition definition occurs on the right-hand side.
-/
def dateCascadeRegressionHandProduct (first second : DateCascadeStage) :
    BackwardFirstChainTransform Unit Unit
  | Sum.inl _, Sum.inl _ =>
      (second.backwardContinuityFactor * (1 / dateForwardTransfer second.ring)) *
          (first.backwardContinuityFactor * (1 / dateForwardTransfer first.ring)) +
        (second.backwardContinuityFactor *
            (-dateBackwardTransfer second.ring / dateForwardTransfer second.ring)) *
          (first.forwardContinuityFactor *
            (dateBackwardTransfer first.ring / dateForwardTransfer first.ring))
  | Sum.inl _, Sum.inr _ =>
      (second.backwardContinuityFactor * (1 / dateForwardTransfer second.ring)) *
          (first.backwardContinuityFactor *
            (-dateBackwardTransfer first.ring / dateForwardTransfer first.ring)) +
        (second.backwardContinuityFactor *
            (-dateBackwardTransfer second.ring / dateForwardTransfer second.ring)) *
          (first.forwardContinuityFactor *
            ((dateForwardTransfer first.ring ^ 2 - dateBackwardTransfer first.ring ^ 2) /
              dateForwardTransfer first.ring))
  | Sum.inr _, Sum.inl _ =>
      (second.forwardContinuityFactor *
          (dateBackwardTransfer second.ring / dateForwardTransfer second.ring)) *
          (first.backwardContinuityFactor * (1 / dateForwardTransfer first.ring)) +
        (second.forwardContinuityFactor *
            ((dateForwardTransfer second.ring ^ 2 - dateBackwardTransfer second.ring ^ 2) /
              dateForwardTransfer second.ring)) *
          (first.forwardContinuityFactor *
            (dateBackwardTransfer first.ring / dateForwardTransfer first.ring))
  | Sum.inr _, Sum.inr _ =>
      (second.forwardContinuityFactor *
          (dateBackwardTransfer second.ring / dateForwardTransfer second.ring)) *
          (first.backwardContinuityFactor *
            (-dateBackwardTransfer first.ring / dateForwardTransfer first.ring)) +
        (second.forwardContinuityFactor *
            ((dateForwardTransfer second.ring ^ 2 - dateBackwardTransfer second.ring ^ 2) /
              dateForwardTransfer second.ring)) *
          (first.forwardContinuityFactor *
            ((dateForwardTransfer first.ring ^ 2 - dateBackwardTransfer first.ring ^ 2) /
              dateForwardTransfer first.ring))

/-- The hand-expanded two-ring backward-to-backward entry agrees with the production product. -/
lemma dateCascadeRegression_twoRing_inl_inl (first second : DateCascadeStage) :
    dateCascadeComposition [first, second]
        (Sum.inl (BackwardWave.mk ())) (Sum.inl (BackwardWave.mk ())) =
      dateCascadeRegressionHandProduct first second
        (Sum.inl (BackwardWave.mk ())) (Sum.inl (BackwardWave.mk ())) := by
  simp [dateCascadeComposition, BackwardFirstChainTransform.fold,
    DateCascadeStage.compositionMatrix, DateCascadeStage.continuityChainMatrix,
    dateCascadeRegressionHandProduct, Matrix.mul_apply, Fintype.sum_sum_type]
  simp_rw [← BackwardWave.channelEquiv.symm.sum_comp,
    ← ForwardWave.channelEquiv.symm.sum_comp]
  simp [dateFourPortBackwardFirstChainMatrix]

/-- The hand-expanded two-ring forward-to-backward entry agrees with the production product. -/
lemma dateCascadeRegression_twoRing_inl_inr (first second : DateCascadeStage) :
    dateCascadeComposition [first, second]
        (Sum.inl (BackwardWave.mk ())) (Sum.inr (ForwardWave.mk ())) =
      dateCascadeRegressionHandProduct first second
        (Sum.inl (BackwardWave.mk ())) (Sum.inr (ForwardWave.mk ())) := by
  simp [dateCascadeComposition, BackwardFirstChainTransform.fold,
    DateCascadeStage.compositionMatrix, DateCascadeStage.continuityChainMatrix,
    dateCascadeRegressionHandProduct, Matrix.mul_apply, Fintype.sum_sum_type]
  simp_rw [← BackwardWave.channelEquiv.symm.sum_comp,
    ← ForwardWave.channelEquiv.symm.sum_comp]
  simp [dateFourPortBackwardFirstChainMatrix]

/-- The hand-expanded two-ring backward-to-forward entry agrees with the production product. -/
lemma dateCascadeRegression_twoRing_inr_inl (first second : DateCascadeStage) :
    dateCascadeComposition [first, second]
        (Sum.inr (ForwardWave.mk ())) (Sum.inl (BackwardWave.mk ())) =
      dateCascadeRegressionHandProduct first second
        (Sum.inr (ForwardWave.mk ())) (Sum.inl (BackwardWave.mk ())) := by
  simp [dateCascadeComposition, BackwardFirstChainTransform.fold,
    DateCascadeStage.compositionMatrix, DateCascadeStage.continuityChainMatrix,
    dateCascadeRegressionHandProduct, Matrix.mul_apply, Fintype.sum_sum_type]
  simp_rw [← BackwardWave.channelEquiv.symm.sum_comp,
    ← ForwardWave.channelEquiv.symm.sum_comp]
  simp [dateFourPortBackwardFirstChainMatrix]

/-- The hand-expanded two-ring forward-to-forward entry agrees with the production product. -/
lemma dateCascadeRegression_twoRing_inr_inr (first second : DateCascadeStage) :
    dateCascadeComposition [first, second]
        (Sum.inr (ForwardWave.mk ())) (Sum.inr (ForwardWave.mk ())) =
      dateCascadeRegressionHandProduct first second
        (Sum.inr (ForwardWave.mk ())) (Sum.inr (ForwardWave.mk ())) := by
  simp [dateCascadeComposition, BackwardFirstChainTransform.fold,
    DateCascadeStage.compositionMatrix, DateCascadeStage.continuityChainMatrix,
    dateCascadeRegressionHandProduct, Matrix.mul_apply, Fintype.sum_sum_type]
  simp_rw [← BackwardWave.channelEquiv.symm.sum_comp,
    ← ForwardWave.channelEquiv.symm.sum_comp]
  simp [dateFourPortBackwardFirstChainMatrix]

end MicroringCascade

end

end Optics
