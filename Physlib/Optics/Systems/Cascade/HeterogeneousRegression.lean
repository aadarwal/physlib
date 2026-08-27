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

An additional quarter-turn fixture expands the carrier exponential itself. It pins DATE's
backward continuity factor to `I` and its forward factor to `-I`, then carries the backward sign
through a two-stage composition entry.

The first stage is input-side and the second stage is output-side, so every hand expression uses
the second stage on the left. The separate asymmetric neutral regression in
`Physlib/Optics/Network/TwoPortChainFoldRegression.lean` rejects the reverse order mechanically.

## ii. Key results

- `dateCascadeRegressionHandProduct`: the hand-expanded two-ring DATE product.
- `dateCascadeRegression_twoRing_inl_inl` and the other three entry lemmas: all four matrix
  coordinates agree without using the H-03 headline theorem.
- `dateCascadeRegression_quarterTurn_signedContinuity`: the opposite DATE phase signs at `pi/2`.
- `dateCascadeRegression_quarterTurn_then_zero_inl_inl`: the pinned backward sign in a product.

## iii. Table of contents

- A. Hand-expanded two-ring product
- B. Signed-phase sentinel

## iv. References
This algebraic fixture makes no quadruple-ring, lattice, termination, Sylvester, Chebyshev,
resonance, dispersion, bending-loss, causality, passivity, reciprocity, or electromagnetic-power
claim. It exercises the totalized matrices and therefore needs no pivot hypothesis; relational
meaning remains gated by the production theorem.

DATE'14 Defs. 6--7 and Thm. 3 are summarized at `HOL-CORPUS.md:201-203`.
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

/-!

## B. Signed-phase sentinel

-/

/-- Exact DATE data used by the signed-continuity sentinel. -/
def dateCascadeRegressionQuarterTurnRing : DateParameters where
  reflectivity := -1
  transmissivity := 0
  couplingLength := 1
  powerAttenuationCoefficient := 0
  wavelength := 4
  effectiveIndex := 1

/-- A stage whose DATE bus phase is a positive quarter turn. -/
def dateCascadeRegressionQuarterTurnStage : DateCascadeStage where
  ring := dateCascadeRegressionQuarterTurnRing
  busLength := 1

/-- The same DATE ring with a zero following bus phase. -/
def dateCascadeRegressionZeroBusStage : DateCascadeStage where
  ring := dateCascadeRegressionQuarterTurnRing
  busLength := 0

/-- Direct parameter expansion gives the quarter-turn bus phase `pi / 2`. -/
lemma dateCascadeRegression_quarterTurn_busPhase :
    dateCascadeRegressionQuarterTurnStage.busPhase = Real.pi / 2 := by
  norm_num [dateCascadeRegressionQuarterTurnStage, DateCascadeStage.busPhase,
    dateCascadeRegressionQuarterTurnRing]
  ring

/-- At bus phase `pi / 2`, DATE continuity is `I` backward and `-I` forward.

The proof expands the fixed-carrier exponential to its trigonometric primitives. The paired
statement fails if the two continuity definitions are swapped or if the explicit negation in the
backward factor is dropped.
-/
lemma dateCascadeRegression_quarterTurn_signedContinuity :
    dateCascadeRegressionQuarterTurnStage.backwardContinuityFactor = Complex.I ∧
      dateCascadeRegressionQuarterTurnStage.forwardContinuityFactor = -Complex.I := by
  rw [DateCascadeStage.backwardContinuityFactor,
    DateCascadeStage.forwardContinuityFactor,
    dateCascadeRegression_quarterTurn_busPhase]
  constructor <;>
    simp [MatchedPropagation.carrierPhaseFactor, Real.Angle.toCircle_coe,
      Circle.coe_exp, Complex.exp_mul_I]

/-- The sentinel ring has unit field attenuation. -/
lemma dateCascadeRegression_quarterTurnRing_fieldAttenuation :
    dateCascadeRegressionQuarterTurnRing.fieldAttenuation = 1 := by
  norm_num [dateCascadeRegressionQuarterTurnRing, DateParameters.fieldAttenuation]

/-- The sentinel ring's internal phase factor is `-I`. -/
lemma dateCascadeRegression_quarterTurnRing_phaseFactor :
    dateCascadeRegressionQuarterTurnRing.phaseFactor = -Complex.I := by
  have hPhase : dateCascadeRegressionQuarterTurnRing.roundTripPhase = Real.pi / 2 := by
    norm_num [dateCascadeRegressionQuarterTurnRing, DateParameters.roundTripPhase]
    ring
  rw [DateParameters.phaseFactor, hPhase]
  simp [MatchedPropagation.carrierPhaseFactor,
    Real.Angle.toCircle_coe, Circle.coe_exp, Complex.exp_mul_I]

/-- The sentinel ring's DATE quotient denominator is `1 + I`. -/
lemma dateCascadeRegression_quarterTurnRing_denominator :
    dateCascadeRegressionQuarterTurnRing.denominator = 1 + Complex.I := by
  rw [DateParameters.denominator,
    dateCascadeRegression_quarterTurnRing_fieldAttenuation,
    dateCascadeRegression_quarterTurnRing_phaseFactor]
  norm_num [dateCascadeRegressionQuarterTurnRing]

/-- The sentinel ring has exact forward transfer one. -/
lemma dateCascadeRegression_quarterTurnRing_forwardTransfer :
    dateForwardTransfer dateCascadeRegressionQuarterTurnRing = 1 := by
  rw [dateForwardTransfer,
    dateCascadeRegression_quarterTurnRing_fieldAttenuation,
    dateCascadeRegression_quarterTurnRing_phaseFactor,
    dateCascadeRegression_quarterTurnRing_denominator]
  norm_num [dateCascadeRegressionQuarterTurnRing]
  intro hZero
  have hReal := congrArg Complex.re hZero
  norm_num at hReal

/-- The sentinel ring has exact backward transfer zero. -/
lemma dateCascadeRegression_quarterTurnRing_backwardTransfer :
    dateBackwardTransfer dateCascadeRegressionQuarterTurnRing = 0 := by
  simp [dateBackwardTransfer, dateCascadeRegressionQuarterTurnRing]

/-- The comparison stage's zero bus has unit backward continuity. -/
lemma dateCascadeRegression_zeroBus_backwardContinuity :
    dateCascadeRegressionZeroBusStage.backwardContinuityFactor = 1 := by
  simp [DateCascadeStage.backwardContinuityFactor, DateCascadeStage.busPhase,
    dateCascadeRegressionZeroBusStage, dateCascadeRegressionQuarterTurnRing,
    MatchedPropagation.carrierPhaseFactor]

/-- A quarter-turn stage followed by a zero-bus stage has backward entry `I`.

The proof consumes `dateCascadeRegression_quarterTurn_signedContinuity`; hence this entry fails if
the continuity factors are swapped or if the backward factor's explicit negation is dropped.
-/
lemma dateCascadeRegression_quarterTurn_then_zero_inl_inl :
    dateCascadeComposition
        [dateCascadeRegressionQuarterTurnStage, dateCascadeRegressionZeroBusStage]
        (Sum.inl (BackwardWave.mk ())) (Sum.inl (BackwardWave.mk ())) = Complex.I := by
  rw [dateCascadeRegression_twoRing_inl_inl]
  simp only [dateCascadeRegressionHandProduct]
  rw [dateCascadeRegression_zeroBus_backwardContinuity,
    dateCascadeRegression_quarterTurn_signedContinuity.1,
    show dateCascadeRegressionZeroBusStage.ring =
      dateCascadeRegressionQuarterTurnRing by rfl,
    show dateCascadeRegressionQuarterTurnStage.ring =
      dateCascadeRegressionQuarterTurnRing by rfl,
    dateCascadeRegression_quarterTurnRing_forwardTransfer,
    dateCascadeRegression_quarterTurnRing_backwardTransfer]
  ring

end MicroringCascade

end

end Optics
