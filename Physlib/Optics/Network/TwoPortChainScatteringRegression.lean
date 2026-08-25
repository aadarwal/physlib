/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.TwoPortChainScattering
public import Physlib.Optics.Network.TwoPortScatteringChainRegression

/-!
# Regression tests for two-port chain-to-scattering conversion

## i. Overview

The singular full scattering fixture converts to a chain transform and back exactly, pinning every
reverse-formula sign and block placement. A two-mode round trip guards noncommutative block order.
A singular chain with a bijective leading block shows that full-chain invertibility is unnecessary,
while a chain with zero leading block and nonzero off-diagonal blocks has no scattering view.

## ii. Scope

These are fixed-frequency algebraic orientation sentinels. They make no losslessness, passivity,
reciprocity, causality, or physical-realization claim.

## iii. Table of contents

- A. Exact scalar scattering-chain-scattering round trip
- B. Noncommutative round trip
- C. Singular chain with a valid scattering pivot
- D. Wrong-pivot negative case

-/

@[expose] public section

namespace Optics

noncomputable section

/-!

## A. Exact scalar scattering-chain-scattering round trip

-/

/-- The chain transform derived from the singular scalar scattering fixture. -/
def twoPortChainScatteringRegressionChain : BackwardFirstChainTransform Unit Unit :=
  twoPortScatteringChainRegressionScattering.toBackwardFirstChainTransform
    twoPortScatteringChainRegression_hasBijectiveRightToLeftTransmission

/-- The derived scalar chain has the automatically transported bijective leading block. -/
lemma twoPortChainScatteringRegression_hasBijectiveLeadingBlock :
    twoPortChainScatteringRegressionChain.HasBijectiveLeadingBlock :=
  TwoPortScatteringTransform.hasBijectiveLeadingBlock_toBackwardFirstChainTransform
    twoPortScatteringChainRegressionScattering
    twoPortScatteringChainRegression_hasBijectiveRightToLeftTransmission

/-- The scalar scattering-chain-scattering conversion is an exact matrix round trip. -/
lemma twoPortChainScatteringRegression_roundTrip :
    twoPortChainScatteringRegressionChain.toTwoPortScatteringTransform
        twoPortChainScatteringRegression_hasBijectiveLeadingBlock =
      twoPortScatteringChainRegressionScattering :=
  TwoPortScatteringTransform.toTwoPortScatteringTransform_toBackwardFirstChainTransform
    twoPortScatteringChainRegressionScattering
    twoPortScatteringChainRegression_hasBijectiveRightToLeftTransmission
    twoPortChainScatteringRegression_hasBijectiveLeadingBlock

/-- Reverse conversion recovers the left-reflection entry two. -/
lemma twoPortChainScatteringRegression_leftReflection_entry :
    (twoPortChainScatteringRegressionChain.toTwoPortScatteringTransform
      twoPortChainScatteringRegression_hasBijectiveLeadingBlock).leftReflection
        (BackwardWave.mk ()) (ForwardWave.mk ()) = 2 := by
  rw [twoPortChainScatteringRegression_roundTrip]
  exact twoPortScatteringChainRegression_leftReflection_entry

/-- Reverse conversion recovers the right-to-left transmission entry `I`. -/
lemma twoPortChainScatteringRegression_rightToLeftTransmission_entry :
    (twoPortChainScatteringRegressionChain.toTwoPortScatteringTransform
      twoPortChainScatteringRegression_hasBijectiveLeadingBlock).rightToLeftTransmission
        (BackwardWave.mk ()) (BackwardWave.mk ()) = Complex.I := by
  rw [twoPortChainScatteringRegression_roundTrip]
  exact twoPortScatteringChainRegression_rightToLeftTransmission_entry

/-- Reverse conversion recovers the left-to-right transmission entry `-6 I`. -/
lemma twoPortChainScatteringRegression_leftToRightTransmission_entry :
    (twoPortChainScatteringRegressionChain.toTwoPortScatteringTransform
      twoPortChainScatteringRegression_hasBijectiveLeadingBlock).leftToRightTransmission
        (ForwardWave.mk ()) (ForwardWave.mk ()) = -6 * Complex.I := by
  rw [twoPortChainScatteringRegression_roundTrip]
  exact twoPortScatteringChainRegression_leftToRightTransmission_entry

/-- Reverse conversion recovers the right-reflection entry three. -/
lemma twoPortChainScatteringRegression_rightReflection_entry :
    (twoPortChainScatteringRegressionChain.toTwoPortScatteringTransform
      twoPortChainScatteringRegression_hasBijectiveLeadingBlock).rightReflection
        (ForwardWave.mk ()) (BackwardWave.mk ()) = 3 := by
  rw [twoPortChainScatteringRegression_roundTrip]
  exact twoPortScatteringChainRegression_rightReflection_entry

/-!

## B. Noncommutative round trip

-/

/-- The chain transform derived from the two-mode noncommuting scattering fixture. -/
def twoPortChainScatteringRegressionNoncommutingChain :
    BackwardFirstChainTransform (Fin 2) (Fin 2) :=
  twoPortScatteringChainRegressionNoncommuting.toBackwardFirstChainTransform
    twoPortScatteringChainRegressionNoncommuting_hasBijectiveRightToLeftTransmission

/-- The noncommuting chain has the transported bijective leading block. -/
lemma twoPortChainScatteringRegressionNoncommuting_hasBijectiveLeadingBlock :
    twoPortChainScatteringRegressionNoncommutingChain.HasBijectiveLeadingBlock :=
  TwoPortScatteringTransform.hasBijectiveLeadingBlock_toBackwardFirstChainTransform
    twoPortScatteringChainRegressionNoncommuting
    twoPortScatteringChainRegressionNoncommuting_hasBijectiveRightToLeftTransmission

/-- The noncommuting chain has identity leading block. -/
lemma twoPortChainScatteringRegressionNoncommuting_leadingBlock :
    twoPortChainScatteringRegressionNoncommutingChain.leadingBlock = 1 := by
  rw [twoPortChainScatteringRegressionNoncommutingChain,
    TwoPortScatteringTransform.toBackwardFirstChainTransform_eq_blockFormula]
  unfold TwoPortScatteringTransform.backwardFirstChainBlockFormula
  rw [twoPortScatteringChainRegressionNoncommuting_transmissionInverse]
  exact Matrix.toBlocks_fromBlocks₁₁ _ _ _ _

/-- The noncommuting chain has upper-right block `-Rl`. -/
lemma twoPortChainScatteringRegressionNoncommuting_upperRightBlock :
    twoPortChainScatteringRegressionNoncommutingChain.upperRightBlock =
      -twoPortScatteringChainRegressionLeftReflection := by
  change twoPortChainScatteringRegressionNoncommutingChain.toBlocks₁₂ = _
  rw [twoPortChainScatteringRegressionNoncommutingChain,
    TwoPortScatteringTransform.toBackwardFirstChainTransform_eq_blockFormula]
  unfold TwoPortScatteringTransform.backwardFirstChainBlockFormula
  rw [Matrix.toBlocks_fromBlocks₁₂,
    twoPortScatteringChainRegressionNoncommuting_transmissionInverse,
    twoPortScatteringChainRegressionNoncommuting_leftReflection, Matrix.one_mul]

/-- The noncommuting chain has lower-left block `Rr`. -/
lemma twoPortChainScatteringRegressionNoncommuting_lowerLeftBlock :
    twoPortChainScatteringRegressionNoncommutingChain.lowerLeftBlock =
      twoPortScatteringChainRegressionRightReflection := by
  change twoPortChainScatteringRegressionNoncommutingChain.toBlocks₂₁ = _
  rw [twoPortChainScatteringRegressionNoncommutingChain,
    TwoPortScatteringTransform.toBackwardFirstChainTransform_eq_blockFormula]
  unfold TwoPortScatteringTransform.backwardFirstChainBlockFormula
  rw [Matrix.toBlocks_fromBlocks₂₁,
    twoPortScatteringChainRegressionNoncommuting_transmissionInverse,
    twoPortScatteringChainRegressionNoncommuting_rightReflection, Matrix.mul_one]

/-- The noncommuting chain has lower-right block `-Rr * Rl`. -/
lemma twoPortChainScatteringRegressionNoncommuting_lowerRightBlock :
    twoPortChainScatteringRegressionNoncommutingChain.lowerRightBlock =
      -(twoPortScatteringChainRegressionRightReflection *
        twoPortScatteringChainRegressionLeftReflection) := by
  change twoPortChainScatteringRegressionNoncommutingChain.toBlocks₂₂ = _
  rw [twoPortChainScatteringRegressionNoncommutingChain,
    TwoPortScatteringTransform.toBackwardFirstChainTransform_eq_blockFormula]
  unfold TwoPortScatteringTransform.backwardFirstChainBlockFormula
  rw [Matrix.toBlocks_fromBlocks₂₂,
    twoPortScatteringChainRegressionNoncommuting_transmissionInverse,
    twoPortScatteringChainRegressionNoncommuting_leftToRightTransmission,
    twoPortScatteringChainRegressionNoncommuting_leftReflection,
    twoPortScatteringChainRegressionNoncommuting_rightReflection,
    Matrix.mul_one, zero_sub]

/-- The inverse of the noncommuting chain's identity leading block is identity. -/
lemma twoPortChainScatteringRegressionNoncommuting_leadingBlockInverse :
    twoPortChainScatteringRegressionNoncommutingChain.leadingBlockInverse
        twoPortChainScatteringRegressionNoncommuting_hasBijectiveLeadingBlock = 1 := by
  apply Matrix.toEuclideanLin.injective
  apply LinearMap.ext
  intro amplitude
  have hInverse :=
    twoPortChainScatteringRegressionNoncommutingChain.inverse_apply_leadingBlock
      twoPortChainScatteringRegressionNoncommuting_hasBijectiveLeadingBlock amplitude
  rw [twoPortChainScatteringRegressionNoncommuting_leadingBlock] at hInverse
  simpa only [ModeTransform.toLinearMap, Matrix.toLpLin_one,
    LinearMap.id_apply] using hInverse

/-- The two-mode scattering-chain-scattering conversion is an exact matrix round trip. -/
lemma twoPortChainScatteringRegressionNoncommuting_roundTrip :
    twoPortChainScatteringRegressionNoncommutingChain.toTwoPortScatteringTransform
        twoPortChainScatteringRegressionNoncommuting_hasBijectiveLeadingBlock =
      twoPortScatteringChainRegressionNoncommuting :=
  TwoPortScatteringTransform.toTwoPortScatteringTransform_toBackwardFirstChainTransform
    twoPortScatteringChainRegressionNoncommuting
    twoPortScatteringChainRegressionNoncommuting_hasBijectiveRightToLeftTransmission
    twoPortChainScatteringRegressionNoncommuting_hasBijectiveLeadingBlock

/-- The noncommutative reverse formula cancels its lower-left scattering block exactly. -/
lemma twoPortChainScatteringRegressionNoncommuting_leftToRightTransmission :
    TwoPortScatteringTransform.leftToRightTransmission
        (twoPortChainScatteringRegressionNoncommutingChain.toTwoPortScatteringTransform
          twoPortChainScatteringRegressionNoncommuting_hasBijectiveLeadingBlock) = 0 := by
  rw [BackwardFirstChainTransform.toTwoPortScatteringTransform_eq_blockFormula,
    BackwardFirstChainTransform.leftToRightTransmission_scatteringBlockFormula,
    twoPortChainScatteringRegressionNoncommuting_lowerRightBlock,
    twoPortChainScatteringRegressionNoncommuting_lowerLeftBlock,
    twoPortChainScatteringRegressionNoncommuting_leadingBlockInverse,
    twoPortChainScatteringRegressionNoncommuting_upperRightBlock]
  simp

/-- The incorrectly reversed raw Schur product has upper-left entry six instead of zero. -/
lemma twoPortChainScatteringRegressionNoncommuting_reversedSchur_entry :
    (-(twoPortScatteringChainRegressionRightReflectionRaw *
        twoPortScatteringChainRegressionLeftReflectionRaw) -
      (-twoPortScatteringChainRegressionLeftReflectionRaw) *
        twoPortScatteringChainRegressionRightReflectionRaw) 0 0 = 6 := by
  norm_num [Matrix.mul_apply, twoPortScatteringChainRegressionLeftReflectionRaw,
    twoPortScatteringChainRegressionRightReflectionRaw]

/-!

## C. Singular chain with a valid scattering pivot

-/

/-- A singular backward-first chain with identity leading block and every other block zero. -/
def twoPortChainScatteringRegressionSingular : BackwardFirstChainTransform Unit Unit :=
  Matrix.fromBlocks 1 0 0 0

/-- The singular chain has identity leading block. -/
lemma twoPortChainScatteringRegressionSingular_leadingBlock :
    twoPortChainScatteringRegressionSingular.leadingBlock = 1 := by
  exact Matrix.toBlocks_fromBlocks₁₁ _ _ _ _

/-- The singular chain has a bijective leading block. -/
lemma twoPortChainScatteringRegressionSingular_hasBijectiveLeadingBlock :
    twoPortChainScatteringRegressionSingular.HasBijectiveLeadingBlock := by
  rw [BackwardFirstChainTransform.HasBijectiveLeadingBlock,
    twoPortChainScatteringRegressionSingular_leadingBlock]
  constructor
  · intro first second hEqual
    simpa only [ModeTransform.toLinearMap, Matrix.toLpLin_one,
      LinearMap.id_apply] using hEqual
  · intro amplitude
    exact ⟨amplitude, by
      simp only [ModeTransform.toLinearMap, Matrix.toLpLin_one,
        LinearMap.id_apply]⟩

/-- The proof-selected inverse of the singular chain's identity leading block is identity. -/
lemma twoPortChainScatteringRegressionSingular_leadingBlockInverse :
    twoPortChainScatteringRegressionSingular.leadingBlockInverse
        twoPortChainScatteringRegressionSingular_hasBijectiveLeadingBlock = 1 := by
  apply Matrix.toEuclideanLin.injective
  apply LinearMap.ext
  intro amplitude
  have hInverse := twoPortChainScatteringRegressionSingular.inverse_apply_leadingBlock
    twoPortChainScatteringRegressionSingular_hasBijectiveLeadingBlock amplitude
  rw [twoPortChainScatteringRegressionSingular_leadingBlock] at hInverse
  simpa only [ModeTransform.toLinearMap, Matrix.toLpLin_one,
    LinearMap.id_apply] using hInverse

/-- The explicit reverse formula gives unit right-to-left transmission for the singular chain. -/
lemma twoPortChainScatteringRegressionSingular_rightToLeftTransmission :
    (twoPortChainScatteringRegressionSingular.toTwoPortScatteringTransform
      twoPortChainScatteringRegressionSingular_hasBijectiveLeadingBlock).rightToLeftTransmission =
        1 := by
  rw [BackwardFirstChainTransform.toTwoPortScatteringTransform_eq_blockFormula,
    BackwardFirstChainTransform.rightToLeftTransmission_scatteringBlockFormula,
    twoPortChainScatteringRegressionSingular_leadingBlockInverse]

/-- A nonzero vector supported on the discarded forward coordinate of the singular chain. -/
def twoPortChainScatteringRegressionSingularKernelInput :
    BackwardFirstTravellingWaveState Unit :=
  (0 : ModeAmplitude (BackwardWave Unit)).directSum
    (twoPortScatteringChainRegressionAmplitude 1 : ModeAmplitude (ForwardWave Unit))

/-- The singular chain sends its kernel sentinel to zero. -/
lemma twoPortChainScatteringRegressionSingular_kernel_action :
    twoPortChainScatteringRegressionSingular.toLinearMap
      twoPortChainScatteringRegressionSingularKernelInput = 0 := by
  change ModeTransform.toLinearMap
      (Matrix.fromBlocks 1 0 0 0 : BackwardFirstChainTransform Unit Unit)
      ((0 : ModeAmplitude (BackwardWave Unit)).directSum
        (twoPortScatteringChainRegressionAmplitude 1 : ModeAmplitude (ForwardWave Unit))) = 0
  rw [ModeTransform.fromBlocks_apply]
  apply WithLp.ofLp_injective 2
  funext index
  rcases index with index | index <;> simp

/-- The singular-chain kernel sentinel is nonzero. -/
lemma twoPortChainScatteringRegressionSingularKernelInput_ne_zero :
    twoPortChainScatteringRegressionSingularKernelInput ≠ 0 := by
  intro hZero
  have hCoordinate := congrArg
    (fun amplitude : BackwardFirstTravellingWaveState Unit =>
      amplitude (Sum.inr (ForwardWave.mk ()))) hZero
  norm_num [twoPortChainScatteringRegressionSingularKernelInput,
    twoPortScatteringChainRegressionAmplitude] at hCoordinate

/-- A bijective leading block does not require the complete chain transform to be injective. -/
lemma twoPortChainScatteringRegressionSingular_not_injective :
    ¬Function.Injective twoPortChainScatteringRegressionSingular.toLinearMap := by
  intro hInjective
  apply twoPortChainScatteringRegressionSingularKernelInput_ne_zero
  apply hInjective
  rw [twoPortChainScatteringRegressionSingular_kernel_action, map_zero]

/-- Reverse conversion transports the singular chain's valid pivot to its scattering transform. -/
lemma twoPortChainScatteringRegressionSingular_hasBijectiveRightToLeftTransmission :
    TwoPortScatteringTransform.HasBijectiveRightToLeftTransmission
      (twoPortChainScatteringRegressionSingular.toTwoPortScatteringTransform
        twoPortChainScatteringRegressionSingular_hasBijectiveLeadingBlock) :=
  BackwardFirstChainTransform.hasBijectiveRightToLeftTransmission_toTwoPortScatteringTransform
    twoPortChainScatteringRegressionSingular
    twoPortChainScatteringRegressionSingular_hasBijectiveLeadingBlock

/-- The singular chain still completes an exact chain-scattering-chain round trip. -/
lemma twoPortChainScatteringRegressionSingular_roundTrip :
    TwoPortScatteringTransform.toBackwardFirstChainTransform
        (twoPortChainScatteringRegressionSingular.toTwoPortScatteringTransform
          twoPortChainScatteringRegressionSingular_hasBijectiveLeadingBlock)
        twoPortChainScatteringRegressionSingular_hasBijectiveRightToLeftTransmission =
      twoPortChainScatteringRegressionSingular :=
  BackwardFirstChainTransform.toBackwardFirstChainTransform_toTwoPortScatteringTransform
    twoPortChainScatteringRegressionSingular
    twoPortChainScatteringRegressionSingular_hasBijectiveLeadingBlock _

/-!

## D. Wrong-pivot negative case

-/

/-- A singleton transform from forward-wave to backward-wave coordinates with unit entry. -/
def twoPortChainScatteringRegressionForwardToBackward :
    ModeTransform (ForwardWave Unit) (BackwardWave Unit) :=
  fun _ _ => 1

/-- A singleton transform from backward-wave to forward-wave coordinates with unit entry. -/
def twoPortChainScatteringRegressionBackwardToForward :
    ModeTransform (BackwardWave Unit) (ForwardWave Unit) :=
  fun _ _ => 1

/-- A chain with zero leading block and unit off-diagonal blocks. -/
def twoPortChainScatteringRegressionWrongPivot : BackwardFirstChainTransform Unit Unit :=
  Matrix.fromBlocks 0 twoPortChainScatteringRegressionForwardToBackward
    twoPortChainScatteringRegressionBackwardToForward 0

/-- The wrong-pivot fixture has zero leading block. -/
lemma twoPortChainScatteringRegressionWrongPivot_leadingBlock :
    twoPortChainScatteringRegressionWrongPivot.leadingBlock = 0 := by
  exact Matrix.toBlocks_fromBlocks₁₁ _ _ _ _

/-- The upper-right block is nonzero even though the required leading block vanishes. -/
lemma twoPortChainScatteringRegressionWrongPivot_upperRight_entry :
    twoPortChainScatteringRegressionWrongPivot.upperRightBlock
      (BackwardWave.mk ()) (ForwardWave.mk ()) = 1 := by
  rfl

/-- The lower-left block is nonzero even though the required leading block vanishes. -/
lemma twoPortChainScatteringRegressionWrongPivot_lowerLeft_entry :
    twoPortChainScatteringRegressionWrongPivot.lowerLeftBlock
      (ForwardWave.mk ()) (BackwardWave.mk ()) = 1 := by
  rfl

/-- The singleton forward-to-backward block preserves its unique amplitude coordinate. -/
lemma twoPortChainScatteringRegressionForwardToBackward_action
    (amplitude : ModeAmplitude (ForwardWave Unit)) :
    twoPortChainScatteringRegressionForwardToBackward.toLinearMap amplitude =
      twoPortScatteringChainRegressionAmplitude (amplitude (ForwardWave.mk ())) := by
  apply WithLp.ofLp_injective 2
  funext index
  rcases index with ⟨⟨⟩⟩
  simp only [ModeTransform.toLinearMap, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    twoPortScatteringChainRegressionAmplitude]
  rw [← ForwardWave.channelEquiv.symm.sum_comp]
  simp [twoPortChainScatteringRegressionForwardToBackward]

/-- The singleton backward-to-forward block preserves its unique amplitude coordinate. -/
lemma twoPortChainScatteringRegressionBackwardToForward_action
    (amplitude : ModeAmplitude (BackwardWave Unit)) :
    twoPortChainScatteringRegressionBackwardToForward.toLinearMap amplitude =
      twoPortScatteringChainRegressionAmplitude (amplitude (BackwardWave.mk ())) := by
  apply WithLp.ofLp_injective 2
  funext index
  rcases index with ⟨⟨⟩⟩
  simp only [ModeTransform.toLinearMap, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    twoPortScatteringChainRegressionAmplitude]
  rw [← BackwardWave.channelEquiv.symm.sum_comp]
  simp [twoPortChainScatteringRegressionBackwardToForward]

/-- The wrong-pivot chain exchanges its unique backward and forward coordinates. -/
lemma twoPortChainScatteringRegressionWrongPivot_action
    (backward : ModeAmplitude (BackwardWave Unit))
    (forward : ModeAmplitude (ForwardWave Unit)) :
    twoPortChainScatteringRegressionWrongPivot.toLinearMap
        (backward.directSum forward) =
      (twoPortScatteringChainRegressionAmplitude (forward (ForwardWave.mk ())) :
          ModeAmplitude (BackwardWave Unit)).directSum
        (twoPortScatteringChainRegressionAmplitude (backward (BackwardWave.mk ())) :
          ModeAmplitude (ForwardWave Unit)) := by
  change ModeTransform.toLinearMap
      (Matrix.fromBlocks 0 twoPortChainScatteringRegressionForwardToBackward
        twoPortChainScatteringRegressionBackwardToForward 0 :
        BackwardFirstChainTransform Unit Unit) (backward.directSum forward) = _
  rw [ModeTransform.fromBlocks_apply,
    twoPortChainScatteringRegressionForwardToBackward_action,
    twoPortChainScatteringRegressionBackwardToForward_action]
  simp

/-- The complete wrong-pivot chain transform is bijective even though its leading block is zero. -/
lemma twoPortChainScatteringRegressionWrongPivot_bijective :
    Function.Bijective twoPortChainScatteringRegressionWrongPivot.toLinearMap := by
  constructor
  · intro first second hEqual
    rw [← first.directSum_restrict, ← second.directSum_restrict,
      twoPortChainScatteringRegressionWrongPivot_action,
      twoPortChainScatteringRegressionWrongPivot_action] at hEqual
    have hBackwardOutput := congrArg ModeAmplitude.restrictInl hEqual
    have hForwardOutput := congrArg ModeAmplitude.restrictInr hEqual
    have hForwardCoordinate := congrArg
      (fun amplitude : ModeAmplitude (BackwardWave Unit) =>
        amplitude (BackwardWave.mk ())) hBackwardOutput
    have hBackwardCoordinate := congrArg
      (fun amplitude : ModeAmplitude (ForwardWave Unit) =>
        amplitude (ForwardWave.mk ())) hForwardOutput
    have hBackward : first.restrictInl = second.restrictInl := by
      apply WithLp.ofLp_injective 2
      funext index
      rcases index with ⟨⟨⟩⟩
      exact hBackwardCoordinate
    have hForward : first.restrictInr = second.restrictInr := by
      apply WithLp.ofLp_injective 2
      funext index
      rcases index with ⟨⟨⟩⟩
      exact hForwardCoordinate
    rw [← first.directSum_restrict, ← second.directSum_restrict, hBackward, hForward]
  · intro output
    let backward := (twoPortScatteringChainRegressionAmplitude
      (output.restrictInr (ForwardWave.mk ())) : ModeAmplitude (BackwardWave Unit))
    let forward := (twoPortScatteringChainRegressionAmplitude
      (output.restrictInl (BackwardWave.mk ())) : ModeAmplitude (ForwardWave Unit))
    refine ⟨backward.directSum forward, ?_⟩
    rw [twoPortChainScatteringRegressionWrongPivot_action]
    apply WithLp.ofLp_injective 2
    funext index
    rcases index with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;> rfl

/-- The wrong-pivot fixture does not have a bijective leading block. -/
lemma twoPortChainScatteringRegressionWrongPivot_not_hasBijectiveLeadingBlock :
    ¬twoPortChainScatteringRegressionWrongPivot.HasBijectiveLeadingBlock := by
  intro hLeading
  let target :=
    (twoPortScatteringChainRegressionAmplitude 1 : ModeAmplitude (BackwardWave Unit))
  rcases hLeading.2 target with ⟨input, hInput⟩
  rw [twoPortChainScatteringRegressionWrongPivot_leadingBlock] at hInput
  have hCoordinate := congrArg
    (fun amplitude : ModeAmplitude (BackwardWave Unit) =>
      amplitude (BackwardWave.mk ())) hInput
  simp only [ModeTransform.toLinearMap, Matrix.toLpLin_apply, Matrix.mulVec,
    dotProduct] at hCoordinate
  rw [← BackwardWave.channelEquiv.symm.sum_comp] at hCoordinate
  simp only [Matrix.zero_apply, zero_mul, Finset.sum_const_zero] at hCoordinate
  change (0 : ℂ) = target (BackwardWave.mk ()) at hCoordinate
  change (0 : ℂ) = 1 at hCoordinate
  norm_num at hCoordinate

/-- The wrong-pivot chain graph is not a functional incident-to-outgoing scattering behavior. -/
lemma twoPortChainScatteringRegressionWrongPivot_not_hasScatteringView :
    ¬twoPortChainScatteringRegressionWrongPivot.HasScatteringView := by
  rw [BackwardFirstChainTransform.hasScatteringView_iff_hasBijectiveLeadingBlock]
  exact twoPortChainScatteringRegressionWrongPivot_not_hasBijectiveLeadingBlock

end

end Optics
