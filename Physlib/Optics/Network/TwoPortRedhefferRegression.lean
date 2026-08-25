/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.TwoPortRedhefferStar

/-!
# Regression tests for the Redheffer star product

## i. Overview

A scalar reflective fixture pins all four Redheffer blocks with a nontrivial feedback inverse.
A second fixture pins a zero feedback pivot and the consequent failure of the matrix-extraction
gate; the underlying relational API remains available without that gate.

Scope:

These are exact algebraic sentinels. They make no physical passivity, losslessness, reciprocity,
causality, or material-realization claim.

## ii. Key results

- The reflective fixture has feedback pivot `-1` and star blocks `(-13, -21, -55, -141)`.
- The singular fixture has a zero pivot and cannot construct a proof-gated star matrix.
- `TwoPortSeriesRegression` separately tests the gate-free relation at both regular and singular
  pivots.

## iii. Table of contents

- A. Scalar block fixture
- B. Singular pivot fixture

## iv. References

These fixtures are Physlib-original and use no external source.

-/

@[expose] public section

namespace Optics

noncomputable section

namespace TwoPortRedhefferRegression

/-!

## A. Scalar block fixture

-/

/-- A scalar two-port transform with travelling-wave block entries `(a, b; c, d)`. -/
def scalarTwoPort (a b c d : ℂ) : TwoPortScatteringTransform Unit Unit
  | Sum.inl _, Sum.inl _ => a
  | Sum.inl _, Sum.inr _ => b
  | Sum.inr _, Sum.inl _ => c
  | Sum.inr _, Sum.inr _ => d

/-- The first reflective scalar fixture has blocks `(2, 3; 5, 2)`. -/
def first : TwoPortScatteringTransform Unit Unit :=
  scalarTwoPort 2 3 5 2

/-- The second reflective scalar fixture has blocks `(1, 7; 11, 13)`. -/
def second : TwoPortScatteringTransform Unit Unit :=
  scalarTwoPort 1 7 11 13

@[simp]
lemma scalarTwoPort_leftReflection (a b c d : ℂ) :
    (scalarTwoPort a b c d).leftReflection ⟨()⟩ ⟨()⟩ = a := rfl

@[simp]
lemma scalarTwoPort_rightToLeftTransmission (a b c d : ℂ) :
    (scalarTwoPort a b c d).rightToLeftTransmission ⟨()⟩ ⟨()⟩ = b := rfl

@[simp]
lemma scalarTwoPort_leftToRightTransmission (a b c d : ℂ) :
    (scalarTwoPort a b c d).leftToRightTransmission ⟨()⟩ ⟨()⟩ = c := rfl

@[simp]
lemma scalarTwoPort_rightReflection (a b c d : ℂ) :
    (scalarTwoPort a b c d).rightReflection ⟨()⟩ ⟨()⟩ = d := rfl

/-- The reflective fixture's internal feedback block is exactly negative identity. -/
lemma feedbackBlock_eq_neg_one :
    first.redhefferFeedbackBlock second =
      -(1 : ModeTransform (BackwardWave Unit) (BackwardWave Unit)) := by
  ext ⟨output⟩ ⟨input⟩
  cases output
  cases input
  norm_num [TwoPortScatteringTransform.redhefferFeedbackBlock, first, second,
    scalarTwoPort, Matrix.mul_apply, ← ForwardWave.channelEquiv.symm.sum_comp]

/-- The scalar reflective fixture satisfies the explicit Redheffer pivot gate. -/
lemma hasBijectiveFeedback : first.HasBijectiveRedhefferFeedback second := by
  rw [TwoPortScatteringTransform.HasBijectiveRedhefferFeedback,
    feedbackBlock_eq_neg_one,
    ModeTransform.toLinearMap_bijective_iff_isUnit]
  simp

/-- The proof-gated feedback inverse is also negative identity. -/
lemma feedbackInverse_eq_neg_one :
    first.redhefferFeedbackInverse second hasBijectiveFeedback =
      -(1 : ModeTransform (BackwardWave Unit) (BackwardWave Unit)) := by
  have hMul := (first.redhefferFeedbackBlock second).mul_inverseOfBijective
    hasBijectiveFeedback
  change first.redhefferFeedbackBlock second *
      first.redhefferFeedbackInverse second hasBijectiveFeedback = 1 at hMul
  rw [feedbackBlock_eq_neg_one] at hMul
  have hNeg : -(first.redhefferFeedbackInverse second hasBijectiveFeedback) = 1 := by
    simpa using hMul
  exact neg_eq_iff_eq_neg.mp hNeg

/-- The star product has left-reflection entry `-13`. -/
lemma redhefferStar_leftReflection :
    (first.redhefferStar second hasBijectiveFeedback).leftReflection ⟨()⟩ ⟨()⟩ = -13 := by
  rw [first.redhefferStar_eq_blockFormula,
    first.leftReflection_redhefferBlockFormula, feedbackInverse_eq_neg_one]
  norm_num [first, second, scalarTwoPort, Matrix.mul_apply,
    ← BackwardWave.channelEquiv.symm.sum_comp,
    ← ForwardWave.channelEquiv.symm.sum_comp]

/-- The star product has right-to-left transmission entry `-21`. -/
lemma redhefferStar_rightToLeftTransmission :
    (first.redhefferStar second hasBijectiveFeedback).rightToLeftTransmission
        ⟨()⟩ ⟨()⟩ = -21 := by
  rw [first.redhefferStar_eq_blockFormula,
    first.rightToLeftTransmission_redhefferBlockFormula, feedbackInverse_eq_neg_one]
  norm_num [first, second, scalarTwoPort, Matrix.mul_apply,
    ← BackwardWave.channelEquiv.symm.sum_comp,
    ← ForwardWave.channelEquiv.symm.sum_comp]

/-- The star product has left-to-right transmission entry `-55`. -/
lemma redhefferStar_leftToRightTransmission :
    (first.redhefferStar second hasBijectiveFeedback).leftToRightTransmission
        ⟨()⟩ ⟨()⟩ = -55 := by
  rw [first.redhefferStar_eq_blockFormula,
    first.leftToRightTransmission_redhefferBlockFormula, feedbackInverse_eq_neg_one]
  norm_num [first, second, scalarTwoPort, Matrix.mul_apply,
    ← BackwardWave.channelEquiv.symm.sum_comp,
    ← ForwardWave.channelEquiv.symm.sum_comp]

/-- The star product has right-reflection entry `-141`. -/
lemma redhefferStar_rightReflection :
    (first.redhefferStar second hasBijectiveFeedback).rightReflection ⟨()⟩ ⟨()⟩ = -141 := by
  rw [first.redhefferStar_eq_blockFormula,
    first.rightReflection_redhefferBlockFormula, feedbackInverse_eq_neg_one]
  norm_num [first, second, scalarTwoPort, Matrix.mul_apply,
    ← BackwardWave.channelEquiv.symm.sum_comp,
    ← ForwardWave.channelEquiv.symm.sum_comp]

/-!

## B. Singular pivot fixture

-/

/-- The first singular fixture exposes its internal backward wave at the left output. -/
def singularFirst : TwoPortScatteringTransform Unit Unit :=
  scalarTwoPort 0 1 0 1

/-- The second singular fixture closes a unit-gain loop and accepts a right incident source. -/
def singularSecond : TwoPortScatteringTransform Unit Unit :=
  scalarTwoPort 1 1 0 0

/-- The singular fixture's feedback block is zero. -/
lemma singular_feedbackBlock_eq_zero :
    singularFirst.redhefferFeedbackBlock singularSecond = 0 := by
  ext ⟨output⟩ ⟨input⟩
  cases output
  cases input
  norm_num [TwoPortScatteringTransform.redhefferFeedbackBlock, singularFirst,
    singularSecond, scalarTwoPort, Matrix.mul_apply,
    ← ForwardWave.channelEquiv.symm.sum_comp]

/-- The singular fixture fails the Redheffer matrix-extraction gate. -/
lemma singular_not_hasBijectiveFeedback :
    ¬singularFirst.HasBijectiveRedhefferFeedback singularSecond := by
  rw [TwoPortScatteringTransform.HasBijectiveRedhefferFeedback,
    singular_feedbackBlock_eq_zero]
  intro hBijective
  let pulse : ModeAmplitude (BackwardWave Unit) := WithLp.toLp 2 fun _ => 1
  have hApply : (0 : ModeTransform (BackwardWave Unit) (BackwardWave Unit)).toLinearMap pulse =
      (0 : ModeTransform (BackwardWave Unit) (BackwardWave Unit)).toLinearMap 0 := by simp
  have hPulse := hBijective.1 hApply
  have := congrArg (fun amplitude => amplitude ⟨()⟩) hPulse
  norm_num [pulse] at this

end TwoPortRedhefferRegression

end


end Optics
