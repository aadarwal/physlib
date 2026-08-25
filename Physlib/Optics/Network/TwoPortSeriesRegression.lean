/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.TwoPortSeries

/-!
# Regression tests for singular-safe two-port series behavior

## i. Overview

Scalar fixtures exercise the relational composition directly, without invoking the Redheffer
block formula. A reflection-free fixture pins both directional product orders. A unit-gain loop
then exhibits two outputs for the same zero incident waves, showing that the relation survives a
singular feedback pivot.

Scope:

These are exact algebraic sentinels. They make no functionality, matrix-extraction, passivity,
losslessness, reciprocity, causality, or material-realization claim.

## ii. Key results

- `reflectionFree_relational_member` pins right-to-left gain `2 * 5` and left-to-right gain
  `7 * 3` through the exposed middle state.
- `singular_relational_outputs_nonunique` pins nonuniqueness at zero incident waves.

## iii. Table of contents

- A. Scalar action
- B. Reflection-free relation
- C. Singular relation

## iv. References

These fixtures are Physlib-original and use no external source.

-/

@[expose] public section

namespace Optics

noncomputable section

namespace TwoPortSeriesRegression

/-!

## A. Scalar action

-/

/-- A scalar two-port transform with travelling-wave blocks `(a, b; c, d)`. -/
def scalarTwoPort (a b c d : ℂ) : TwoPortScatteringTransform Unit Unit
  | Sum.inl _, Sum.inl _ => a
  | Sum.inl _, Sum.inr _ => b
  | Sum.inr _, Sum.inl _ => c
  | Sum.inr _, Sum.inr _ => d

/-- A constant scalar amplitude on an arbitrary regression mode family. -/
def scalarAmplitude {ι : Type*} (value : ℂ) : ModeAmplitude ι :=
  WithLp.toLp 2 fun _ => value

/-- A scalar backward-first state with independently specified entries. -/
def scalarState (backward forward : ℂ) : BackwardFirstTravellingWaveState Unit :=
  (scalarAmplitude backward : ModeAmplitude (BackwardWave Unit)).directSum
    (scalarAmplitude forward : ModeAmplitude (ForwardWave Unit))

/-- The left-reflection block acts by scalar multiplication. -/
@[simp]
lemma scalarTwoPort_leftReflection_apply (a b c d x : ℂ) :
    ((scalarTwoPort a b c d).leftReflection.toLinearMap
      (scalarAmplitude x : ModeAmplitude (ForwardWave Unit))) (BackwardWave.mk ()) = a * x := by
  simp only [ModeTransform.toLinearMap, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    scalarAmplitude]
  rw [← ForwardWave.channelEquiv.symm.sum_comp]
  simp [scalarTwoPort]

/-- The right-to-left block acts by scalar multiplication. -/
@[simp]
lemma scalarTwoPort_rightToLeftTransmission_apply (a b c d x : ℂ) :
    ((scalarTwoPort a b c d).rightToLeftTransmission.toLinearMap
      (scalarAmplitude x : ModeAmplitude (BackwardWave Unit))) (BackwardWave.mk ()) = b * x := by
  simp only [ModeTransform.toLinearMap, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    scalarAmplitude]
  rw [← BackwardWave.channelEquiv.symm.sum_comp]
  simp [scalarTwoPort]

/-- The left-to-right block acts by scalar multiplication. -/
@[simp]
lemma scalarTwoPort_leftToRightTransmission_apply (a b c d x : ℂ) :
    ((scalarTwoPort a b c d).leftToRightTransmission.toLinearMap
      (scalarAmplitude x : ModeAmplitude (ForwardWave Unit))) (ForwardWave.mk ()) = c * x := by
  simp only [ModeTransform.toLinearMap, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    scalarAmplitude]
  rw [← ForwardWave.channelEquiv.symm.sum_comp]
  simp [scalarTwoPort]

/-- The right-reflection block acts by scalar multiplication. -/
@[simp]
lemma scalarTwoPort_rightReflection_apply (a b c d x : ℂ) :
    ((scalarTwoPort a b c d).rightReflection.toLinearMap
      (scalarAmplitude x : ModeAmplitude (BackwardWave Unit))) (ForwardWave.mk ()) = d * x := by
  simp only [ModeTransform.toLinearMap, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    scalarAmplitude]
  rw [← BackwardWave.channelEquiv.symm.sum_comp]
  simp [scalarTwoPort]

/-!

## B. Reflection-free relation

-/

/-- The first reflection-free fixture has directional gains two and three. -/
def reflectionFreeFirst : TwoPortScatteringTransform Unit Unit := scalarTwoPort 0 2 3 0

/-- The second reflection-free fixture has directional gains five and seven. -/
def reflectionFreeSecond : TwoPortScatteringTransform Unit Unit := scalarTwoPort 0 5 7 0

/-- Direct relational membership pins both ordered transmission products. -/
lemma reflectionFree_relational_member :
    (scalarState 130 11, scalarState 13 231) ∈
      TwoPortScatteringBehavior.toBackwardFirst
        (reflectionFreeFirst.redhefferSeriesBehavior reflectionFreeSecond) := by
  rw [reflectionFreeFirst.mem_toBackwardFirst_redhefferSeriesBehavior_iff
    reflectionFreeSecond]
  refine ⟨scalarState 65 33, ?_⟩
  simp only [scalarState, ModeAmplitude.restrictInl_directSum,
    ModeAmplitude.restrictInr_directSum]
  apply And.intro <;> apply And.intro <;>
    apply WithLp.ofLp_injective 2 <;> funext index
  all_goals
    rcases index with ⟨⟨⟩⟩
    norm_num [scalarAmplitude, reflectionFreeFirst, reflectionFreeSecond, scalarTwoPort,
      Matrix.mulVec, dotProduct, ← ForwardWave.channelEquiv.symm.sum_comp,
      ← BackwardWave.channelEquiv.symm.sum_comp]

/-!

## C. Singular relation

-/

/-- The first singular fixture exposes the loop amplitude at the left output. -/
def singularFirst : TwoPortScatteringTransform Unit Unit := scalarTwoPort 0 1 0 1

/-- The second singular fixture closes the unit-gain loop. -/
def singularSecond : TwoPortScatteringTransform Unit Unit := scalarTwoPort 1 1 0 0

/-- Every loop amplitude gives a relational solution with zero incident waves. -/
lemma singular_relational_member (value : ℂ) :
    (scalarState value 0, scalarState 0 0) ∈
      TwoPortScatteringBehavior.toBackwardFirst
        (singularFirst.redhefferSeriesBehavior singularSecond) := by
  rw [singularFirst.mem_toBackwardFirst_redhefferSeriesBehavior_iff singularSecond]
  refine ⟨scalarState value value, ?_⟩
  simp only [scalarState, ModeAmplitude.restrictInl_directSum,
    ModeAmplitude.restrictInr_directSum]
  apply And.intro <;> apply And.intro <;>
    apply WithLp.ofLp_injective 2 <;> funext index
  all_goals
    rcases index with ⟨⟨⟩⟩
    norm_num [scalarAmplitude, singularFirst, singularSecond, scalarTwoPort,
      Matrix.mulVec, dotProduct,
      ← ForwardWave.channelEquiv.symm.sum_comp,
      ← BackwardWave.channelEquiv.symm.sum_comp]

/-- Zero incident waves admit two different outgoing states at the singular pivot. -/
lemma singular_relational_outputs_nonunique :
    (scalarState 0 0, scalarState 0 0) ∈
        TwoPortScatteringBehavior.toBackwardFirst
          (singularFirst.redhefferSeriesBehavior singularSecond) ∧
      (scalarState 1 0, scalarState 0 0) ∈
        TwoPortScatteringBehavior.toBackwardFirst
          (singularFirst.redhefferSeriesBehavior singularSecond) ∧
      scalarState 0 0 ≠ scalarState 1 0 := by
  refine ⟨singular_relational_member 0, singular_relational_member 1, ?_⟩
  intro hEqual
  have hCoordinate := congrArg
    (fun state : BackwardFirstTravellingWaveState Unit =>
      state (Sum.inl (BackwardWave.mk ()))) hEqual
  norm_num [scalarState, scalarAmplitude] at hCoordinate

end TwoPortSeriesRegression

end


end Optics
