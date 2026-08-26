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

The singular full scattering fixture converts to a chain transform and back exactly. Independent
literal scalar and two-mode chain fixtures exercise every chain-to-scattering sign, block placement,
and the noncommuting Schur-product order. A singular chain with a bijective leading block shows that
full-chain invertibility is unnecessary, while a chain with zero leading block and nonzero
off-diagonal blocks has no scattering view.

## ii. Key results

## iii. Table of contents

- A. Exact scalar scattering-chain-scattering round trip
- B. Independent scalar chain-to-scattering formula
- C. Noncommutative round trip
- D. Independent non-cancelling chain-to-scattering formula
- E. Singular chain with a valid scattering pivot
- F. Wrong-pivot negative case

## iv. References

These are fixed-frequency algebraic orientation sentinels. They make no losslessness, passivity,
reciprocity, causality, or physical-realization claim.

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

## B. Independent scalar chain-to-scattering formula

-/

/-- The literal scalar chain `[[−I, 2I], [−3I, 0]]`, independently of conversion. -/
def twoPortChainScatteringRegressionLiteralChain : BackwardFirstChainTransform Unit Unit
  | Sum.inl _, Sum.inl _ => -Complex.I
  | Sum.inl _, Sum.inr _ => 2 * Complex.I
  | Sum.inr _, Sum.inl _ => -3 * Complex.I
  | Sum.inr _, Sum.inr _ => 0

/-- The literal scalar chain has leading-block entry `-I`. -/
lemma twoPortChainScatteringRegressionLiteral_leadingBlock_entry :
    twoPortChainScatteringRegressionLiteralChain.leadingBlock
      (BackwardWave.mk ()) (BackwardWave.mk ()) = -Complex.I := by
  rfl

/-- The literal scalar chain has upper-right entry `2 I`. -/
lemma twoPortChainScatteringRegressionLiteral_upperRightBlock_entry :
    twoPortChainScatteringRegressionLiteralChain.upperRightBlock
      (BackwardWave.mk ()) (ForwardWave.mk ()) = 2 * Complex.I := by
  rfl

/-- The literal scalar chain has lower-left entry `-3 I`. -/
lemma twoPortChainScatteringRegressionLiteral_lowerLeftBlock_entry :
    twoPortChainScatteringRegressionLiteralChain.lowerLeftBlock
      (ForwardWave.mk ()) (BackwardWave.mk ()) = -3 * Complex.I := by
  rfl

/-- The literal scalar chain has zero lower-right entry. -/
lemma twoPortChainScatteringRegressionLiteral_lowerRightBlock_entry :
    twoPortChainScatteringRegressionLiteralChain.lowerRightBlock
      (ForwardWave.mk ()) (ForwardWave.mk ()) = 0 := by
  rfl

/-- The literal scalar chain's leading block acts by multiplication by `-I`. -/
lemma twoPortChainScatteringRegressionLiteral_leadingBlock_action
    (amplitude : ModeAmplitude (BackwardWave Unit)) :
    twoPortChainScatteringRegressionLiteralChain.leadingBlock.toLinearMap amplitude =
      twoPortScatteringChainRegressionAmplitude
        (-Complex.I * amplitude (BackwardWave.mk ())) := by
  apply WithLp.ofLp_injective 2
  funext index
  rcases index with ⟨⟨⟩⟩
  simp only [ModeTransform.toLinearMap, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    twoPortScatteringChainRegressionAmplitude]
  rw [← BackwardWave.channelEquiv.symm.sum_comp]
  simp [twoPortChainScatteringRegressionLiteralChain,
    BackwardFirstChainTransform.leadingBlock, Matrix.toBlocks₁₁]

/-- The literal scalar chain has a bijective leading block, proved without forward conversion. -/
lemma twoPortChainScatteringRegressionLiteral_hasBijectiveLeadingBlock :
    twoPortChainScatteringRegressionLiteralChain.HasBijectiveLeadingBlock := by
  constructor
  · intro first second hEqual
    apply WithLp.ofLp_injective 2
    funext index
    rcases index with ⟨⟨⟩⟩
    have hCoordinate := congrArg
      (fun amplitude : ModeAmplitude (BackwardWave Unit) =>
        amplitude (BackwardWave.mk ())) hEqual
    rw [twoPortChainScatteringRegressionLiteral_leadingBlock_action,
      twoPortChainScatteringRegressionLiteral_leadingBlock_action] at hCoordinate
    exact mul_left_cancel₀ (neg_ne_zero.mpr Complex.I_ne_zero) hCoordinate
  · intro output
    refine ⟨twoPortScatteringChainRegressionAmplitude
      (Complex.I * output (BackwardWave.mk ())), ?_⟩
    rw [twoPortChainScatteringRegressionLiteral_leadingBlock_action]
    apply WithLp.ofLp_injective 2
    funext index
    rcases index with ⟨⟨⟩⟩
    change -Complex.I * (Complex.I * output (BackwardWave.mk ())) =
      output (BackwardWave.mk ())
    calc
      -Complex.I * (Complex.I * output (BackwardWave.mk ())) =
          -(Complex.I * Complex.I) * output (BackwardWave.mk ()) := by ring
      _ = output (BackwardWave.mk ()) := by rw [Complex.I_mul_I]; ring

/-- The explicit inverse of the literal scalar chain's leading block. -/
def twoPortChainScatteringRegressionLiteralLeadingInverse :
    ModeTransform (BackwardWave Unit) (BackwardWave Unit) :=
  fun _ _ => Complex.I

/-- The explicit scalar inverse acts by multiplication by `I`. -/
lemma twoPortChainScatteringRegressionLiteralLeadingInverse_action
    (amplitude : ModeAmplitude (BackwardWave Unit)) :
    twoPortChainScatteringRegressionLiteralLeadingInverse.toLinearMap amplitude =
      twoPortScatteringChainRegressionAmplitude
        (Complex.I * amplitude (BackwardWave.mk ())) := by
  apply WithLp.ofLp_injective 2
  funext index
  rcases index with ⟨⟨⟩⟩
  simp only [ModeTransform.toLinearMap, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    twoPortScatteringChainRegressionAmplitude]
  rw [← BackwardWave.channelEquiv.symm.sum_comp]
  simp [twoPortChainScatteringRegressionLiteralLeadingInverse]

/-- The proof-selected inverse of the literal leading block is the explicit scalar `I`. -/
lemma twoPortChainScatteringRegressionLiteral_leadingBlockInverse :
    twoPortChainScatteringRegressionLiteralChain.leadingBlockInverse
        twoPortChainScatteringRegressionLiteral_hasBijectiveLeadingBlock =
      twoPortChainScatteringRegressionLiteralLeadingInverse := by
  apply Matrix.toEuclideanLin.injective
  apply LinearMap.ext
  intro amplitude
  apply twoPortChainScatteringRegressionLiteral_hasBijectiveLeadingBlock.1
  calc
    twoPortChainScatteringRegressionLiteralChain.leadingBlock.toLinearMap
        ((twoPortChainScatteringRegressionLiteralChain.leadingBlockInverse
          twoPortChainScatteringRegressionLiteral_hasBijectiveLeadingBlock).toLinearMap
            amplitude) = amplitude :=
      BackwardFirstChainTransform.leadingBlock_apply_inverse _ _ _
    _ = twoPortChainScatteringRegressionLiteralChain.leadingBlock.toLinearMap
        (twoPortChainScatteringRegressionLiteralLeadingInverse.toLinearMap amplitude) := by
      rw [twoPortChainScatteringRegressionLiteralLeadingInverse_action,
        twoPortChainScatteringRegressionLiteral_leadingBlock_action]
      apply WithLp.ofLp_injective 2
      funext index
      rcases index with ⟨⟨⟩⟩
      change amplitude (BackwardWave.mk ()) =
        -Complex.I * (Complex.I * amplitude (BackwardWave.mk ()))
      calc
        amplitude (BackwardWave.mk ()) =
            -(Complex.I * Complex.I) * amplitude (BackwardWave.mk ()) := by
          rw [Complex.I_mul_I]
          ring
        _ = -Complex.I * (Complex.I * amplitude (BackwardWave.mk ())) := by ring

/-- The literal chain-to-scattering formula has left-reflection entry two. -/
lemma twoPortChainScatteringRegressionLiteral_leftReflection_entry :
    (twoPortChainScatteringRegressionLiteralChain.toTwoPortScatteringTransform
      twoPortChainScatteringRegressionLiteral_hasBijectiveLeadingBlock).leftReflection
        (BackwardWave.mk ()) (ForwardWave.mk ()) = 2 := by
  rw [BackwardFirstChainTransform.toTwoPortScatteringTransform_eq_blockFormula,
    BackwardFirstChainTransform.leftReflection_scatteringBlockFormula,
    twoPortChainScatteringRegressionLiteral_leadingBlockInverse]
  simp [Matrix.mul_apply, twoPortChainScatteringRegressionLiteralChain,
    twoPortChainScatteringRegressionLiteralLeadingInverse,
    BackwardFirstChainTransform.upperRightBlock, Matrix.toBlocks₁₂,
    ← BackwardWave.channelEquiv.symm.sum_comp]
  calc
    -(Complex.I * (2 * Complex.I)) = -(2 * (Complex.I * Complex.I)) := by ring
    _ = 2 := by rw [Complex.I_mul_I]; ring

/-- The literal chain-to-scattering formula has right-to-left transmission entry `I`. -/
lemma twoPortChainScatteringRegressionLiteral_rightToLeftTransmission_entry :
    (twoPortChainScatteringRegressionLiteralChain.toTwoPortScatteringTransform
      twoPortChainScatteringRegressionLiteral_hasBijectiveLeadingBlock).rightToLeftTransmission
        (BackwardWave.mk ()) (BackwardWave.mk ()) = Complex.I := by
  rw [BackwardFirstChainTransform.toTwoPortScatteringTransform_eq_blockFormula,
    BackwardFirstChainTransform.rightToLeftTransmission_scatteringBlockFormula,
    twoPortChainScatteringRegressionLiteral_leadingBlockInverse]
  rfl

/-- The literal chain-to-scattering formula has left-to-right transmission entry `-6 I`. -/
lemma twoPortChainScatteringRegressionLiteral_leftToRightTransmission_entry :
    (twoPortChainScatteringRegressionLiteralChain.toTwoPortScatteringTransform
      twoPortChainScatteringRegressionLiteral_hasBijectiveLeadingBlock).leftToRightTransmission
        (ForwardWave.mk ()) (ForwardWave.mk ()) = -6 * Complex.I := by
  rw [BackwardFirstChainTransform.toTwoPortScatteringTransform_eq_blockFormula,
    BackwardFirstChainTransform.leftToRightTransmission_scatteringBlockFormula,
    twoPortChainScatteringRegressionLiteral_leadingBlockInverse]
  simp [Matrix.mul_apply, twoPortChainScatteringRegressionLiteralChain,
    twoPortChainScatteringRegressionLiteralLeadingInverse,
    BackwardFirstChainTransform.upperRightBlock,
    BackwardFirstChainTransform.lowerLeftBlock,
    BackwardFirstChainTransform.lowerRightBlock, Matrix.toBlocks₁₂,
    Matrix.toBlocks₂₁, Matrix.toBlocks₂₂,
    ← BackwardWave.channelEquiv.symm.sum_comp]
  calc
    3 * Complex.I * Complex.I * (2 * Complex.I) =
        6 * (Complex.I * Complex.I) * Complex.I := by ring
    _ = -(6 * Complex.I) := by rw [Complex.I_mul_I]; ring

/-- The literal chain-to-scattering formula has right-reflection entry three. -/
lemma twoPortChainScatteringRegressionLiteral_rightReflection_entry :
    (twoPortChainScatteringRegressionLiteralChain.toTwoPortScatteringTransform
      twoPortChainScatteringRegressionLiteral_hasBijectiveLeadingBlock).rightReflection
        (ForwardWave.mk ()) (BackwardWave.mk ()) = 3 := by
  rw [BackwardFirstChainTransform.toTwoPortScatteringTransform_eq_blockFormula,
    BackwardFirstChainTransform.rightReflection_scatteringBlockFormula,
    twoPortChainScatteringRegressionLiteral_leadingBlockInverse]
  simp [Matrix.mul_apply, twoPortChainScatteringRegressionLiteralChain,
    twoPortChainScatteringRegressionLiteralLeadingInverse,
    BackwardFirstChainTransform.lowerLeftBlock, Matrix.toBlocks₂₁,
    ← BackwardWave.channelEquiv.symm.sum_comp]
  calc
    -(3 * Complex.I * Complex.I) = -(3 * (Complex.I * Complex.I)) := by ring
    _ = 3 := by rw [Complex.I_mul_I]; ring

/-!

## C. Noncommutative round trip

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

## D. Independent non-cancelling chain-to-scattering formula

-/

/-- An independent two-mode chain `[[1, A], [B, 0]]` with noncommuting shear blocks. -/
def twoPortChainScatteringRegressionNoncancelling :
    BackwardFirstChainTransform (Fin 2) (Fin 2) :=
  Matrix.fromBlocks 1 twoPortScatteringChainRegressionLeftReflection
    twoPortScatteringChainRegressionRightReflection 0

/-- The independent two-mode chain has identity leading block. -/
lemma twoPortChainScatteringRegressionNoncancelling_leadingBlock :
    twoPortChainScatteringRegressionNoncancelling.leadingBlock = 1 := by
  exact Matrix.toBlocks_fromBlocks₁₁ _ _ _ _

/-- The independent two-mode chain has upper-right shear `A`. -/
lemma twoPortChainScatteringRegressionNoncancelling_upperRightBlock :
    twoPortChainScatteringRegressionNoncancelling.upperRightBlock =
      twoPortScatteringChainRegressionLeftReflection := by
  exact Matrix.toBlocks_fromBlocks₁₂ _ _ _ _

/-- The independent two-mode chain has lower-left shear `B`. -/
lemma twoPortChainScatteringRegressionNoncancelling_lowerLeftBlock :
    twoPortChainScatteringRegressionNoncancelling.lowerLeftBlock =
      twoPortScatteringChainRegressionRightReflection := by
  exact Matrix.toBlocks_fromBlocks₂₁ _ _ _ _

/-- The independent two-mode chain has zero lower-right block. -/
lemma twoPortChainScatteringRegressionNoncancelling_lowerRightBlock :
    twoPortChainScatteringRegressionNoncancelling.lowerRightBlock = 0 := by
  exact Matrix.toBlocks_fromBlocks₂₂ _ _ _ _

/-- The independent two-mode chain has a bijective leading block. -/
lemma twoPortChainScatteringRegressionNoncancelling_hasBijectiveLeadingBlock :
    twoPortChainScatteringRegressionNoncancelling.HasBijectiveLeadingBlock := by
  rw [BackwardFirstChainTransform.HasBijectiveLeadingBlock,
    twoPortChainScatteringRegressionNoncancelling_leadingBlock]
  constructor
  · intro first second hEqual
    simpa only [ModeTransform.toLinearMap, Matrix.toLpLin_one,
      LinearMap.id_apply] using hEqual
  · intro amplitude
    exact ⟨amplitude, by
      simp only [ModeTransform.toLinearMap, Matrix.toLpLin_one,
        LinearMap.id_apply]⟩

/-- The inverse of the independent chain's identity leading block is identity. -/
lemma twoPortChainScatteringRegressionNoncancelling_leadingBlockInverse :
    twoPortChainScatteringRegressionNoncancelling.leadingBlockInverse
        twoPortChainScatteringRegressionNoncancelling_hasBijectiveLeadingBlock = 1 := by
  apply Matrix.toEuclideanLin.injective
  apply LinearMap.ext
  intro amplitude
  have hInverse := twoPortChainScatteringRegressionNoncancelling.inverse_apply_leadingBlock
    twoPortChainScatteringRegressionNoncancelling_hasBijectiveLeadingBlock amplitude
  rw [twoPortChainScatteringRegressionNoncancelling_leadingBlock] at hInverse
  simpa only [ModeTransform.toLinearMap, Matrix.toLpLin_one,
    LinearMap.id_apply] using hInverse

/-- The non-cancelling formula has off-diagonal left-reflection entry `-2`. -/
lemma twoPortChainScatteringRegressionNoncancelling_leftReflection_entry :
    (twoPortChainScatteringRegressionNoncancelling.toTwoPortScatteringTransform
      twoPortChainScatteringRegressionNoncancelling_hasBijectiveLeadingBlock).leftReflection
        (BackwardWave.mk 0) (ForwardWave.mk 1) = -2 := by
  rw [BackwardFirstChainTransform.toTwoPortScatteringTransform_eq_blockFormula,
    BackwardFirstChainTransform.leftReflection_scatteringBlockFormula,
    twoPortChainScatteringRegressionNoncancelling_leadingBlockInverse,
    twoPortChainScatteringRegressionNoncancelling_upperRightBlock, Matrix.one_mul]
  norm_num [twoPortScatteringChainRegressionLeftReflection,
    twoPortScatteringChainRegressionLeftReflectionRaw]

/-- The non-cancelling formula places the leading-block inverse in right-to-left transmission. -/
lemma twoPortChainScatteringRegressionNoncancelling_rightToLeftTransmission_entry :
    TwoPortScatteringTransform.rightToLeftTransmission
        (twoPortChainScatteringRegressionNoncancelling.toTwoPortScatteringTransform
          twoPortChainScatteringRegressionNoncancelling_hasBijectiveLeadingBlock)
          (BackwardWave.mk 1) (BackwardWave.mk 1) = 1 := by
  rw [BackwardFirstChainTransform.toTwoPortScatteringTransform_eq_blockFormula,
    BackwardFirstChainTransform.rightToLeftTransmission_scatteringBlockFormula,
    twoPortChainScatteringRegressionNoncancelling_leadingBlockInverse]
  rfl

/-- The ordered Schur block `-B A` has lower-right entry `-7`. -/
lemma twoPortChainScatteringRegressionNoncancelling_leftToRightTransmission_entry :
    TwoPortScatteringTransform.leftToRightTransmission
        (twoPortChainScatteringRegressionNoncancelling.toTwoPortScatteringTransform
          twoPortChainScatteringRegressionNoncancelling_hasBijectiveLeadingBlock)
          (ForwardWave.mk 1) (ForwardWave.mk 1) = -7 := by
  rw [BackwardFirstChainTransform.toTwoPortScatteringTransform_eq_blockFormula,
    BackwardFirstChainTransform.leftToRightTransmission_scatteringBlockFormula,
    twoPortChainScatteringRegressionNoncancelling_lowerRightBlock,
    twoPortChainScatteringRegressionNoncancelling_lowerLeftBlock,
    twoPortChainScatteringRegressionNoncancelling_leadingBlockInverse,
    twoPortChainScatteringRegressionNoncancelling_upperRightBlock,
    Matrix.mul_one, zero_sub, Matrix.neg_apply, Matrix.mul_apply]
  rw [← BackwardWave.channelEquiv.symm.sum_comp]
  norm_num [twoPortScatteringChainRegressionLeftReflection,
    twoPortScatteringChainRegressionLeftReflectionRaw,
    twoPortScatteringChainRegressionRightReflection,
    twoPortScatteringChainRegressionRightReflectionRaw]

/-- The non-cancelling formula places `B` in the right-reflection block. -/
lemma twoPortChainScatteringRegressionNoncancelling_rightReflection_entry :
    (twoPortChainScatteringRegressionNoncancelling.toTwoPortScatteringTransform
      twoPortChainScatteringRegressionNoncancelling_hasBijectiveLeadingBlock).rightReflection
        (ForwardWave.mk 1) (BackwardWave.mk 0) = 3 := by
  rw [BackwardFirstChainTransform.toTwoPortScatteringTransform_eq_blockFormula,
    BackwardFirstChainTransform.rightReflection_scatteringBlockFormula,
    twoPortChainScatteringRegressionNoncancelling_lowerLeftBlock,
    twoPortChainScatteringRegressionNoncancelling_leadingBlockInverse, Matrix.mul_one]
  norm_num [twoPortScatteringChainRegressionRightReflection,
    twoPortScatteringChainRegressionRightReflectionRaw]

/-- Reversing the two raw shear factors gives lower-right entry `-1`. -/
lemma twoPortChainScatteringRegressionNoncancelling_wrongOrder_entry :
    (-(twoPortScatteringChainRegressionLeftReflectionRaw *
      twoPortScatteringChainRegressionRightReflectionRaw)) 1 1 = -1 := by
  norm_num [Matrix.mul_apply, twoPortScatteringChainRegressionLeftReflectionRaw,
    twoPortScatteringChainRegressionRightReflectionRaw]

/-- The ordered Schur entry is not the value produced by the wrong raw factor order. -/
lemma twoPortChainScatteringRegressionNoncancelling_leftToRightTransmission_ne_wrongOrder :
    TwoPortScatteringTransform.leftToRightTransmission
        (twoPortChainScatteringRegressionNoncancelling.toTwoPortScatteringTransform
          twoPortChainScatteringRegressionNoncancelling_hasBijectiveLeadingBlock)
          (ForwardWave.mk 1) (ForwardWave.mk 1) ≠
      (-(twoPortScatteringChainRegressionLeftReflectionRaw *
        twoPortScatteringChainRegressionRightReflectionRaw)) 1 1 := by
  rw [twoPortChainScatteringRegressionNoncancelling_leftToRightTransmission_entry,
    twoPortChainScatteringRegressionNoncancelling_wrongOrder_entry]
  norm_num

/-!

## E. Singular chain with a valid scattering pivot

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

/-- The one-way singular fixture has zero left reflection. -/
lemma twoPortChainScatteringRegressionSingular_leftReflection :
    (twoPortChainScatteringRegressionSingular.toTwoPortScatteringTransform
      twoPortChainScatteringRegressionSingular_hasBijectiveLeadingBlock).leftReflection = 0 := by
  rw [BackwardFirstChainTransform.toTwoPortScatteringTransform_eq_blockFormula,
    BackwardFirstChainTransform.leftReflection_scatteringBlockFormula,
    twoPortChainScatteringRegressionSingular_leadingBlockInverse]
  change -(1 * (Matrix.fromBlocks 1 0 0 0).toBlocks₁₂) = 0
  rw [Matrix.toBlocks_fromBlocks₁₂, Matrix.mul_zero, neg_zero]

/-- The one-way singular fixture has zero left-to-right transmission. -/
lemma twoPortChainScatteringRegressionSingular_leftToRightTransmission :
    TwoPortScatteringTransform.leftToRightTransmission
        (twoPortChainScatteringRegressionSingular.toTwoPortScatteringTransform
          twoPortChainScatteringRegressionSingular_hasBijectiveLeadingBlock) = 0 := by
  rw [BackwardFirstChainTransform.toTwoPortScatteringTransform_eq_blockFormula,
    BackwardFirstChainTransform.leftToRightTransmission_scatteringBlockFormula,
    twoPortChainScatteringRegressionSingular_leadingBlockInverse]
  change (Matrix.fromBlocks 1 0 0 0).toBlocks₂₂ -
    (Matrix.fromBlocks 1 0 0 0).toBlocks₂₁ * 1 *
      (Matrix.fromBlocks 1 0 0 0).toBlocks₁₂ = 0
  rw [Matrix.toBlocks_fromBlocks₂₂, Matrix.toBlocks_fromBlocks₂₁,
    Matrix.toBlocks_fromBlocks₁₂, Matrix.zero_mul, Matrix.zero_mul, sub_zero]

/-- The one-way singular fixture has zero right reflection. -/
lemma twoPortChainScatteringRegressionSingular_rightReflection :
    (twoPortChainScatteringRegressionSingular.toTwoPortScatteringTransform
      twoPortChainScatteringRegressionSingular_hasBijectiveLeadingBlock).rightReflection = 0 := by
  rw [BackwardFirstChainTransform.toTwoPortScatteringTransform_eq_blockFormula,
    BackwardFirstChainTransform.rightReflection_scatteringBlockFormula,
    twoPortChainScatteringRegressionSingular_leadingBlockInverse]
  change (Matrix.fromBlocks 1 0 0 0).toBlocks₂₁ * 1 = 0
  rw [Matrix.toBlocks_fromBlocks₂₁, Matrix.zero_mul]

/-- A second direct proof of the singular fixture's leading-block gate. -/
lemma twoPortChainScatteringRegressionSingular_hasBijectiveLeadingBlockAlternative :
    twoPortChainScatteringRegressionSingular.HasBijectiveLeadingBlock := by
  rw [BackwardFirstChainTransform.HasBijectiveLeadingBlock,
    twoPortChainScatteringRegressionSingular_leadingBlock]
  exact ⟨fun _ _ hEqual => by
    simpa only [ModeTransform.toLinearMap, Matrix.toLpLin_one,
      LinearMap.id_apply] using hEqual,
    fun amplitude => ⟨amplitude, by
      simp only [ModeTransform.toLinearMap, Matrix.toLpLin_one,
        LinearMap.id_apply]⟩⟩

/-- Chain-to-scattering extraction is insensitive to the chosen proof of its pivot gate. -/
lemma twoPortChainScatteringRegressionSingular_proofIrrelevance :
    twoPortChainScatteringRegressionSingular.toTwoPortScatteringTransform
        twoPortChainScatteringRegressionSingular_hasBijectiveLeadingBlock =
      twoPortChainScatteringRegressionSingular.toTwoPortScatteringTransform
        twoPortChainScatteringRegressionSingular_hasBijectiveLeadingBlockAlternative := by
  rfl

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

/-- The formula-derived unit transmission block has a direct bijectivity proof. -/
lemma twoPortChainScatteringRegressionSingular_hasBijectiveTransmissionDirect :
    TwoPortScatteringTransform.HasBijectiveRightToLeftTransmission
      (twoPortChainScatteringRegressionSingular.toTwoPortScatteringTransform
        twoPortChainScatteringRegressionSingular_hasBijectiveLeadingBlock) := by
  rw [TwoPortScatteringTransform.HasBijectiveRightToLeftTransmission,
    twoPortChainScatteringRegressionSingular_rightToLeftTransmission]
  constructor
  · intro first second hEqual
    simpa only [ModeTransform.toLinearMap, Matrix.toLpLin_one,
      LinearMap.id_apply] using hEqual
  · intro amplitude
    exact ⟨amplitude, by
      simp only [ModeTransform.toLinearMap, Matrix.toLpLin_one,
        LinearMap.id_apply]⟩

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

/-- The singular matrix round trip accepts an independently proved transported pivot gate. -/
lemma twoPortChainScatteringRegressionSingular_roundTrip_directPivot :
    TwoPortScatteringTransform.toBackwardFirstChainTransform
        (twoPortChainScatteringRegressionSingular.toTwoPortScatteringTransform
          twoPortChainScatteringRegressionSingular_hasBijectiveLeadingBlock)
        twoPortChainScatteringRegressionSingular_hasBijectiveTransmissionDirect =
      twoPortChainScatteringRegressionSingular :=
  BackwardFirstChainTransform.toBackwardFirstChainTransform_toTwoPortScatteringTransform
    twoPortChainScatteringRegressionSingular
    twoPortChainScatteringRegressionSingular_hasBijectiveLeadingBlock _

/-!

## F. Wrong-pivot negative case

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

/-- The tempting but incorrect upper-right pivot is the singleton identity across wave labels. -/
lemma twoPortChainScatteringRegressionWrongPivot_upperRightBlock :
    twoPortChainScatteringRegressionWrongPivot.upperRightBlock =
      twoPortChainScatteringRegressionForwardToBackward := by
  exact Matrix.toBlocks_fromBlocks₁₂ _ _ _ _

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

/-- The tempting upper-right block is bijective even though it is not the scattering pivot. -/
lemma twoPortChainScatteringRegressionWrongPivot_upperRight_bijective :
    Function.Bijective
      twoPortChainScatteringRegressionWrongPivot.upperRightBlock.toLinearMap := by
  rw [twoPortChainScatteringRegressionWrongPivot_upperRightBlock]
  constructor
  · intro first second hEqual
    rw [twoPortChainScatteringRegressionForwardToBackward_action,
      twoPortChainScatteringRegressionForwardToBackward_action] at hEqual
    apply WithLp.ofLp_injective 2
    funext index
    rcases index with ⟨⟨⟩⟩
    exact congrArg
      (fun amplitude : ModeAmplitude (BackwardWave Unit) =>
        amplitude (BackwardWave.mk ())) hEqual
  · intro output
    let input := (twoPortScatteringChainRegressionAmplitude
      (output (BackwardWave.mk ())) : ModeAmplitude (ForwardWave Unit))
    refine ⟨input, ?_⟩
    rw [twoPortChainScatteringRegressionForwardToBackward_action]
    apply WithLp.ofLp_injective 2
    funext index
    rcases index with ⟨⟨⟩⟩
    rfl

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

/-- Incident data `(aL, aR) = (0, 1)` for which the wrong-pivot chain has no output. -/
def twoPortChainScatteringRegressionWrongPivotImpossibleIncident :
    ModeAmplitude (Incident Unit ⊕ Incident Unit) :=
  (scatteringBackwardFirstLinearEquiv.symm
    ((0 : ModeAmplitude (BackwardWave Unit)).directSum
        (0 : ModeAmplitude (ForwardWave Unit)),
      (twoPortScatteringChainRegressionAmplitude 1 : ModeAmplitude (BackwardWave Unit)).directSum
        (0 : ModeAmplitude (ForwardWave Unit)))).1

/-- The wrong-pivot chain is not total: incident data `(0, 1)` admit no outgoing state. -/
lemma twoPortChainScatteringRegressionWrongPivot_impossibleIncident
    (outgoing : ModeAmplitude (Outgoing Unit ⊕ Outgoing Unit)) :
    (twoPortChainScatteringRegressionWrongPivotImpossibleIncident, outgoing) ∉
      twoPortChainScatteringRegressionWrongPivot.toScatteringBehavior := by
  intro hMember
  let states := scatteringBackwardFirstLinearEquiv
    (twoPortChainScatteringRegressionWrongPivotImpossibleIncident, outgoing)
  have hBlocks :=
    (twoPortChainScatteringRegressionWrongPivot.mem_toScatteringBehavior_iff_blockEquations
      twoPortChainScatteringRegressionWrongPivotImpossibleIncident outgoing).mp hMember
  change states.2.restrictInl =
      twoPortChainScatteringRegressionWrongPivot.leadingBlock.toLinearMap
          states.1.restrictInl +
        twoPortChainScatteringRegressionWrongPivot.upperRightBlock.toLinearMap
          states.1.restrictInr ∧ _ at hBlocks
  have hLeftForward : states.1.restrictInr = 0 := by
    apply WithLp.ofLp_injective 2
    funext ⟨channel⟩
    rfl
  have hRightBackward : states.2.restrictInl =
      (twoPortScatteringChainRegressionAmplitude 1 : ModeAmplitude (BackwardWave Unit)) := by
    apply WithLp.ofLp_injective 2
    funext ⟨channel⟩
    rfl
  rw [hRightBackward, hLeftForward, map_zero, add_zero] at hBlocks
  have hCoordinate := congrArg
    (fun amplitude : ModeAmplitude (BackwardWave Unit) =>
      amplitude (BackwardWave.mk ())) hBlocks.1
  rw [twoPortChainScatteringRegressionWrongPivot_leadingBlock] at hCoordinate
  simp only [ModeTransform.toLinearMap, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    twoPortScatteringChainRegressionAmplitude] at hCoordinate
  rw [← BackwardWave.channelEquiv.symm.sum_comp] at hCoordinate
  norm_num at hCoordinate

/-- The explicit impossible incident state proves that the wrong-pivot scattering view is not
total, independently of the abstract pivot criterion. -/
lemma twoPortChainScatteringRegressionWrongPivot_not_total :
    ¬twoPortChainScatteringRegressionWrongPivot.toScatteringBehavior.IsTotal := by
  intro hTotal
  rcases hTotal twoPortChainScatteringRegressionWrongPivotImpossibleIncident with
    ⟨outgoing, hMember⟩
  exact twoPortChainScatteringRegressionWrongPivot_impossibleIncident outgoing hMember

/-- The wrong-pivot chain graph is not a functional incident-to-outgoing scattering behavior. -/
lemma twoPortChainScatteringRegressionWrongPivot_not_hasScatteringView :
    ¬twoPortChainScatteringRegressionWrongPivot.HasScatteringView := by
  intro hView
  exact twoPortChainScatteringRegressionWrongPivot_not_total hView.1

end

end Optics
