/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.TwoPortTermination

/-!
# Regression tests for relational two-port termination

## i. Overview

An identity backward-first device is terminated by the scalar return law `aR = 2 bR`. Its exact
four-wave solution pins the load orientation, and a reversed-law candidate is rejected. A second,
asymmetric device gives three distinct output waves and pins the complete output order
`(bL, (aR, bR))`.

## ii. Key results

## iii. Table of contents

- A. Loaded identity behavior
- B. Asymmetric complete-solution order
- C. Reversed-orientation rejection

## iv. References

The scalar return law is an algebraic orientation sentinel. It makes no passivity, losslessness,
impedance, absorption, or physical-load claim.

-/

@[expose] public section

namespace Optics

noncomputable section

/-!

## A. Loaded identity behavior

-/

/-- A constant scalar amplitude on an arbitrary regression channel family. -/
def twoPortTerminationRegressionAmplitude {ι : Type*} (value : ℂ) : ModeAmplitude ι :=
  WithLp.toLp 2 fun _ => value

/-- A constant-entry mode transform used to assemble scalar relational fixtures. -/
def twoPortTerminationRegressionScalarBlock {ι κ : Type*} (value : ℂ) : ModeTransform ι κ :=
  fun _ _ => value

/-- The scalar right-return transform `aR = 2 bR`. -/
def twoPortTerminationRegressionDoubleReturn : RightLoadTransform Unit :=
  twoPortTerminationRegressionScalarBlock 2

/-- The scalar return transform doubles the unique forward-wave coordinate. -/
lemma twoPortTerminationRegressionDoubleReturn_action
    (amplitude : ModeAmplitude (ForwardWave Unit)) :
    twoPortTerminationRegressionDoubleReturn.toLinearMap amplitude =
      (twoPortTerminationRegressionAmplitude
        (2 * amplitude (ForwardWave.mk ())) : ModeAmplitude (BackwardWave Unit)) := by
  apply WithLp.ofLp_injective 2
  funext index
  rcases index with ⟨⟨⟩⟩
  simp only [ModeTransform.toLinearMap, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    twoPortTerminationRegressionAmplitude]
  rw [← ForwardWave.channelEquiv.symm.sum_comp]
  simp [twoPortTerminationRegressionDoubleReturn, twoPortTerminationRegressionScalarBlock]

/-- The incident amplitude three for the relational termination fixture. -/
def twoPortTerminationRegressionLeftIncident : ModeAmplitude (ForwardWave Unit) :=
  twoPortTerminationRegressionAmplitude 3

/-- The reflected amplitude six for the relational termination fixture. -/
def twoPortTerminationRegressionLeftBackward : ModeAmplitude (BackwardWave Unit) :=
  twoPortTerminationRegressionAmplitude 6

/-- The returned right amplitude six for the relational termination fixture. -/
def twoPortTerminationRegressionRightBackward : ModeAmplitude (BackwardWave Unit) :=
  twoPortTerminationRegressionAmplitude 6

/-- The forward right amplitude three for the relational termination fixture. -/
def twoPortTerminationRegressionRightForward : ModeAmplitude (ForwardWave Unit) :=
  twoPortTerminationRegressionAmplitude 3

/-- The complete wave tuple satisfies the identity device and the return law `aR = 2 bR`. -/
lemma twoPortTerminationRegression_completeSolution_mem :
    (twoPortTerminationRegressionLeftIncident,
        twoPortTerminationRegressionLeftBackward.directSum
          (twoPortTerminationRegressionRightBackward.directSum
            twoPortTerminationRegressionRightForward)) ∈
      BackwardFirstTwoPortBehavior.terminateRight
        (LinearBehavior.identity : BackwardFirstTwoPortBehavior Unit Unit)
        (RightLoadBehavior.ofReflection twoPortTerminationRegressionDoubleReturn) := by
  rw [BackwardFirstTwoPortBehavior.mem_terminateRight_directSum_iff,
    LinearBehavior.mem_identity_iff, RightLoadBehavior.mem_ofReflection_iff,
    twoPortTerminationRegressionDoubleReturn_action]
  constructor
  · rfl
  · apply WithLp.ofLp_injective 2
    funext index
    rcases index with ⟨⟨⟩⟩
    norm_num [twoPortTerminationRegressionRightBackward,
      twoPortTerminationRegressionRightForward, twoPortTerminationRegressionAmplitude]

/-!

## B. Asymmetric complete-solution order

-/

/-- A diagonal device with equations `aR = 2 bL` and `bR = 3 aL`. -/
def twoPortTerminationRegressionAsymmetricDevice :
    ModeTransform (BackwardWave Unit ⊕ ForwardWave Unit)
      (BackwardWave Unit ⊕ ForwardWave Unit) :=
  (twoPortTerminationRegressionScalarBlock 2 :
    ModeTransform (BackwardWave Unit) (BackwardWave Unit)).directSum
      (twoPortTerminationRegressionScalarBlock 3 :
        ModeTransform (ForwardWave Unit) (ForwardWave Unit))

/-- The scalar right-return transform `aR = 4 bR` for the asymmetric fixture. -/
def twoPortTerminationRegressionQuadrupleReturn : RightLoadTransform Unit :=
  twoPortTerminationRegressionScalarBlock 4

/-- The incident amplitude one for the asymmetric tuple-order fixture. -/
def twoPortTerminationRegressionAsymmetricLeftIncident : ModeAmplitude (ForwardWave Unit) :=
  twoPortTerminationRegressionAmplitude 1

/-- The reflected amplitude six for the asymmetric tuple-order fixture. -/
def twoPortTerminationRegressionAsymmetricLeftBackward : ModeAmplitude (BackwardWave Unit) :=
  twoPortTerminationRegressionAmplitude 6

/-- The returned amplitude twelve for the asymmetric tuple-order fixture. -/
def twoPortTerminationRegressionAsymmetricRightBackward : ModeAmplitude (BackwardWave Unit) :=
  twoPortTerminationRegressionAmplitude 12

/-- The forward amplitude three for the asymmetric tuple-order fixture. -/
def twoPortTerminationRegressionAsymmetricRightForward : ModeAmplitude (ForwardWave Unit) :=
  twoPortTerminationRegressionAmplitude 3

/-- The asymmetric diagonal device maps `(bL, aL) = (6, 1)` to `(aR, bR) = (12, 3)`. -/
lemma twoPortTerminationRegressionAsymmetricDevice_action :
    twoPortTerminationRegressionAsymmetricDevice.toLinearMap
        (twoPortTerminationRegressionAsymmetricLeftBackward.directSum
          twoPortTerminationRegressionAsymmetricLeftIncident) =
      twoPortTerminationRegressionAsymmetricRightBackward.directSum
        twoPortTerminationRegressionAsymmetricRightForward := by
  rw [twoPortTerminationRegressionAsymmetricDevice, ModeTransform.directSum_apply]
  apply WithLp.ofLp_injective 2
  funext index
  rcases index with index | index
  · rcases index with ⟨⟨⟩⟩
    norm_num [ModeTransform.toLinearMap, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
      twoPortTerminationRegressionScalarBlock, twoPortTerminationRegressionAmplitude,
      twoPortTerminationRegressionAsymmetricLeftBackward,
      twoPortTerminationRegressionAsymmetricRightBackward]
  · rcases index with ⟨⟨⟩⟩
    norm_num [ModeTransform.toLinearMap, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
      twoPortTerminationRegressionScalarBlock, twoPortTerminationRegressionAmplitude,
      twoPortTerminationRegressionAsymmetricLeftIncident,
      twoPortTerminationRegressionAsymmetricRightForward]

/-- The return transform maps the fixture's forward amplitude three to backward amplitude twelve. -/
lemma twoPortTerminationRegressionQuadrupleReturn_action :
    twoPortTerminationRegressionQuadrupleReturn.toLinearMap
        twoPortTerminationRegressionAsymmetricRightForward =
      twoPortTerminationRegressionAsymmetricRightBackward := by
  apply WithLp.ofLp_injective 2
  funext index
  rcases index with ⟨⟨⟩⟩
  norm_num [ModeTransform.toLinearMap, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    twoPortTerminationRegressionQuadrupleReturn, twoPortTerminationRegressionScalarBlock,
    twoPortTerminationRegressionAmplitude,
    twoPortTerminationRegressionAsymmetricRightForward,
    twoPortTerminationRegressionAsymmetricRightBackward]

/-- The three distinct unknown waves occupy the declared order `(bL, (aR, bR))`. -/
lemma twoPortTerminationRegression_asymmetricCompleteSolution_mem :
    (twoPortTerminationRegressionAsymmetricLeftIncident,
        twoPortTerminationRegressionAsymmetricLeftBackward.directSum
          (twoPortTerminationRegressionAsymmetricRightBackward.directSum
            twoPortTerminationRegressionAsymmetricRightForward)) ∈
      BackwardFirstTwoPortBehavior.terminateRight
        twoPortTerminationRegressionAsymmetricDevice.toBehavior
        (RightLoadBehavior.ofReflection twoPortTerminationRegressionQuadrupleReturn) := by
  rw [BackwardFirstTwoPortBehavior.mem_terminateRight_directSum_iff,
    ModeTransform.mem_toBehavior_iff_toLinearMap, RightLoadBehavior.mem_ofReflection_iff]
  exact ⟨twoPortTerminationRegressionAsymmetricDevice_action.symm,
    twoPortTerminationRegressionQuadrupleReturn_action.symm⟩

/-- Swapping the distinct `bL` and `aR` amplitudes does not preserve complete-solution
membership. -/
lemma twoPortTerminationRegression_swappedCompleteSolution_not_mem :
    (twoPortTerminationRegressionAsymmetricLeftIncident,
        twoPortTerminationRegressionAsymmetricRightBackward.directSum
          (twoPortTerminationRegressionAsymmetricLeftBackward.directSum
            twoPortTerminationRegressionAsymmetricRightForward)) ∉
      BackwardFirstTwoPortBehavior.terminateRight
        twoPortTerminationRegressionAsymmetricDevice.toBehavior
        (RightLoadBehavior.ofReflection twoPortTerminationRegressionQuadrupleReturn) := by
  intro hMember
  have hLoad := (BackwardFirstTwoPortBehavior.mem_terminateRight_directSum_iff
    twoPortTerminationRegressionAsymmetricDevice.toBehavior
    (RightLoadBehavior.ofReflection twoPortTerminationRegressionQuadrupleReturn)
    twoPortTerminationRegressionAsymmetricLeftIncident
    twoPortTerminationRegressionAsymmetricRightBackward
    twoPortTerminationRegressionAsymmetricLeftBackward
    twoPortTerminationRegressionAsymmetricRightForward).mp hMember |>.2
  rw [RightLoadBehavior.mem_ofReflection_iff] at hLoad
  have hCoordinate := congrArg
    (fun amplitude : ModeAmplitude (BackwardWave Unit) =>
      amplitude (BackwardWave.mk ())) hLoad
  norm_num [ModeTransform.toLinearMap, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    twoPortTerminationRegressionQuadrupleReturn, twoPortTerminationRegressionScalarBlock,
    twoPortTerminationRegressionAmplitude,
    twoPortTerminationRegressionAsymmetricLeftBackward,
    twoPortTerminationRegressionAsymmetricRightForward] at hCoordinate

/-!

## C. Reversed-orientation rejection

-/

/-- The reversed equation `bR = 2 aR` would suggest the incorrect return amplitude `3 / 2`. -/
def twoPortTerminationRegressionReversedRightBackward : ModeAmplitude (BackwardWave Unit) :=
  twoPortTerminationRegressionAmplitude (3 / 2)

/-- The reversed-law candidate is not a solution of the declared load orientation `aR = 2 bR`. -/
lemma twoPortTerminationRegression_reversedSolution_not_mem :
    (twoPortTerminationRegressionLeftIncident,
        twoPortTerminationRegressionReversedRightBackward.directSum
          (twoPortTerminationRegressionReversedRightBackward.directSum
            twoPortTerminationRegressionRightForward)) ∉
      BackwardFirstTwoPortBehavior.terminateRight
        (LinearBehavior.identity : BackwardFirstTwoPortBehavior Unit Unit)
        (RightLoadBehavior.ofReflection twoPortTerminationRegressionDoubleReturn) := by
  intro hMember
  have hLoad := (BackwardFirstTwoPortBehavior.mem_terminateRight_directSum_iff
    (LinearBehavior.identity : BackwardFirstTwoPortBehavior Unit Unit)
    (RightLoadBehavior.ofReflection twoPortTerminationRegressionDoubleReturn)
    twoPortTerminationRegressionLeftIncident
    twoPortTerminationRegressionReversedRightBackward
    twoPortTerminationRegressionReversedRightBackward
    twoPortTerminationRegressionRightForward).mp hMember |>.2
  rw [RightLoadBehavior.mem_ofReflection_iff,
    twoPortTerminationRegressionDoubleReturn_action] at hLoad
  have hCoordinate := congrArg
    (fun amplitude : ModeAmplitude (BackwardWave Unit) =>
      amplitude (BackwardWave.mk ())) hLoad
  norm_num [twoPortTerminationRegressionReversedRightBackward,
    twoPortTerminationRegressionRightForward, twoPortTerminationRegressionAmplitude] at hCoordinate

end

end Optics
