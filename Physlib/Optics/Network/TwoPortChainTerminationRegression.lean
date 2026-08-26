/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.TwoPortChainTermination
public import Physlib.Optics.Network.TwoPortTerminationRegression

/-!
# Regression tests for right-terminated chain transforms

## i. Overview

The scalar chain `[[2, 3], [5, 7]]` is terminated first by the nonzero return law
`aR = (1 / 3) bR` and then by zero return. The loaded response is exactly `bL = -2 aL` and
`bR = -3 aL`; the zero-return response is `bL = -(3 / 2) aL` and `bR = -(1 / 2) aL`.

These values pin the load orientation, both pivot subtraction signs, and the distinction between
the terminated forward response and the opposite transmission block `K₁₁⁻¹`. The chain has
determinant `-1`, so its zero-return forward response is not `1 / K₁₁`.

## ii. Key results

## iii. Table of contents

- A. Loaded scalar response
- B. Zero-return response and scattering agreement
- C. Well-posed rectangular pivot without surjectivity
- D. Singular loaded relation without a response transform
- E. Noncommuting two-mode loaded response

## iv. References

The fixtures are exact fixed-frequency algebra. They make no passivity, losslessness, impedance,
absorption, causality, or physical-load claim.

-/

@[expose] public section

namespace Optics

noncomputable section

/-!

## A. Loaded scalar response

-/

/-- The scalar chain `[[2, 3], [5, 7]]`. -/
def twoPortChainTerminationRegressionChain : BackwardFirstChainTransform Unit Unit :=
  Matrix.fromBlocks
    (twoPortTerminationRegressionScalarBlock 2)
    (twoPortTerminationRegressionScalarBlock 3)
    (twoPortTerminationRegressionScalarBlock 5)
    (twoPortTerminationRegressionScalarBlock 7)

/-- The nonzero scalar return transform `Γ = 1 / 3`. -/
def twoPortChainTerminationRegressionLoad : RightLoadTransform Unit :=
  twoPortTerminationRegressionScalarBlock (1 / 3)

/-- The loaded termination pivot is the singleton matrix with entry `1 / 3`. -/
lemma twoPortChainTerminationRegression_pivot :
    twoPortChainTerminationRegressionChain.rightTerminationPivot
        twoPortChainTerminationRegressionLoad =
      (twoPortTerminationRegressionScalarBlock (1 / 3) :
        ModeTransform (BackwardWave Unit) (BackwardWave Unit)) := by
  ext output input
  rcases output with ⟨⟨⟩⟩
  rcases input with ⟨⟨⟩⟩
  simp [BackwardFirstChainTransform.rightTerminationPivot,
    twoPortChainTerminationRegressionChain, twoPortChainTerminationRegressionLoad,
    twoPortTerminationRegressionScalarBlock, Matrix.mul_apply]
  norm_num

/-- The loaded incident block is the singleton matrix with entry `-2 / 3`. -/
lemma twoPortChainTerminationRegression_incidentBlock :
    twoPortChainTerminationRegressionChain.rightTerminationIncidentBlock
        twoPortChainTerminationRegressionLoad =
      (twoPortTerminationRegressionScalarBlock (-2 / 3) :
        ModeTransform (ForwardWave Unit) (BackwardWave Unit)) := by
  ext output input
  rcases output with ⟨⟨⟩⟩
  rcases input with ⟨⟨⟩⟩
  simp [BackwardFirstChainTransform.rightTerminationIncidentBlock,
    twoPortChainTerminationRegressionChain, twoPortChainTerminationRegressionLoad,
    twoPortTerminationRegressionScalarBlock, Matrix.mul_apply]
  norm_num

/-- The singleton loaded pivot acts by multiplication by `1 / 3`. -/
lemma twoPortChainTerminationRegression_pivot_action
    (amplitude : ModeAmplitude (BackwardWave Unit)) :
    (twoPortChainTerminationRegressionChain.rightTerminationPivot
      twoPortChainTerminationRegressionLoad).toLinearMap amplitude =
      (twoPortTerminationRegressionAmplitude
        ((1 / 3) * amplitude (BackwardWave.mk ())) :
          ModeAmplitude (BackwardWave Unit)) := by
  rw [twoPortChainTerminationRegression_pivot]
  apply WithLp.ofLp_injective 2
  funext index
  rcases index with ⟨⟨⟩⟩
  simp only [ModeTransform.toLinearMap, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    twoPortTerminationRegressionAmplitude]
  rw [← BackwardWave.channelEquiv.symm.sum_comp]
  simp [twoPortTerminationRegressionScalarBlock]

/-- The loaded termination pivot is bijective. -/
lemma twoPortChainTerminationRegression_hasBijectivePivot :
    twoPortChainTerminationRegressionChain.HasBijectiveRightTerminationPivot
      twoPortChainTerminationRegressionLoad := by
  constructor
  · intro first second hEqual
    rw [twoPortChainTerminationRegression_pivot_action,
      twoPortChainTerminationRegression_pivot_action] at hEqual
    have hCoordinate := congrArg
      (fun amplitude : ModeAmplitude (BackwardWave Unit) =>
        amplitude (BackwardWave.mk ())) hEqual
    change (1 / 3 : ℂ) * first (BackwardWave.mk ()) =
      (1 / 3 : ℂ) * second (BackwardWave.mk ()) at hCoordinate
    apply WithLp.ofLp_injective 2
    funext index
    rcases index with ⟨⟨⟩⟩
    exact mul_left_cancel₀ (by norm_num : (1 / 3 : ℂ) ≠ 0) hCoordinate
  · intro output
    refine ⟨(twoPortTerminationRegressionAmplitude
      (3 * output (BackwardWave.mk ())) : ModeAmplitude (BackwardWave Unit)), ?_⟩
    rw [twoPortChainTerminationRegression_pivot_action]
    apply WithLp.ofLp_injective 2
    funext index
    rcases index with ⟨⟨⟩⟩
    change (1 / 3 : ℂ) * (3 * output (BackwardWave.mk ())) =
      output (BackwardWave.mk ())
    ring

/-- The inverse loaded pivot has singleton entry three. -/
lemma twoPortChainTerminationRegression_pivotInverse_entry :
    (twoPortChainTerminationRegressionChain.rightTerminationPivotInverse
      twoPortChainTerminationRegressionLoad
      twoPortChainTerminationRegression_hasBijectivePivot)
        (BackwardWave.mk ()) (BackwardWave.mk ()) = 3 := by
  let unitAmplitude :=
    (twoPortTerminationRegressionAmplitude 1 : ModeAmplitude (BackwardWave Unit))
  have hInverse :=
    twoPortChainTerminationRegressionChain.rightTerminationPivot_apply_inverse
      twoPortChainTerminationRegressionLoad
      twoPortChainTerminationRegression_hasBijectivePivot unitAmplitude
  rw [twoPortChainTerminationRegression_pivot_action] at hInverse
  have hCoordinate := congrArg
    (fun amplitude : ModeAmplitude (BackwardWave Unit) =>
      amplitude (BackwardWave.mk ())) hInverse
  simp only [ModeTransform.toLinearMap, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    twoPortTerminationRegressionAmplitude] at hCoordinate
  rw [← BackwardWave.channelEquiv.symm.sum_comp] at hCoordinate
  simp only [Finset.univ_unique, Finset.sum_singleton] at hCoordinate
  change (1 / 3 : ℂ) *
    ((twoPortChainTerminationRegressionChain.rightTerminationPivotInverse
      twoPortChainTerminationRegressionLoad
      twoPortChainTerminationRegression_hasBijectivePivot)
        (BackwardWave.mk ()) (BackwardWave.mk ()) * 1) = 1 at hCoordinate
  norm_num at hCoordinate
  linear_combination 3 * hCoordinate

/-- The explicit loaded reflection formula has singleton entry `-2`. -/
lemma twoPortChainTerminationRegression_reflectionFormula_entry :
    (twoPortChainTerminationRegressionChain.rightTerminatedReflectionBlockFormula
      twoPortChainTerminationRegressionLoad
      twoPortChainTerminationRegression_hasBijectivePivot)
        (BackwardWave.mk ()) (ForwardWave.mk ()) = -2 := by
  rw [BackwardFirstChainTransform.rightTerminatedReflectionBlockFormula,
    Matrix.mul_apply]
  rw [← BackwardWave.channelEquiv.symm.sum_comp]
  simp [twoPortChainTerminationRegression_pivotInverse_entry,
    twoPortChainTerminationRegression_incidentBlock,
    twoPortTerminationRegressionScalarBlock]
  norm_num

/-- The behavior-derived loaded reflection transform has singleton entry `-2`. -/
lemma twoPortChainTerminationRegression_reflection_entry :
    (twoPortChainTerminationRegressionChain.rightTerminatedReflectionTransform
      twoPortChainTerminationRegressionLoad
      twoPortChainTerminationRegression_hasBijectivePivot)
        (BackwardWave.mk ()) (ForwardWave.mk ()) = -2 := by
  rw [twoPortChainTerminationRegressionChain.rightTerminatedReflectionTransform_eq_blockFormula]
  exact twoPortChainTerminationRegression_reflectionFormula_entry

/-- The scalar chain's lower-left block has entry five. -/
lemma twoPortChainTerminationRegression_lowerLeft_entry :
    twoPortChainTerminationRegressionChain.lowerLeftBlock
      (ForwardWave.mk ()) (BackwardWave.mk ()) = 5 := by
  simp [twoPortChainTerminationRegressionChain,
    twoPortTerminationRegressionScalarBlock]

/-- The scalar chain's lower-right block has entry seven. -/
lemma twoPortChainTerminationRegression_lowerRight_entry :
    twoPortChainTerminationRegressionChain.lowerRightBlock
      (ForwardWave.mk ()) (ForwardWave.mk ()) = 7 := by
  simp [twoPortChainTerminationRegressionChain,
    twoPortTerminationRegressionScalarBlock]

/-- The behavior-derived loaded forward transform has singleton entry `-3`. -/
lemma twoPortChainTerminationRegression_transmission_entry :
    (twoPortChainTerminationRegressionChain.rightTerminatedTransmissionTransform
      twoPortChainTerminationRegressionLoad
      twoPortChainTerminationRegression_hasBijectivePivot)
        (ForwardWave.mk ()) (ForwardWave.mk ()) = -3 := by
  rw [twoPortChainTerminationRegressionChain.rightTerminatedTransmissionTransform_eq_blockFormula,
    BackwardFirstChainTransform.rightTerminatedTransmissionBlockFormula, Matrix.add_apply,
    Matrix.mul_apply]
  rw [← BackwardWave.channelEquiv.symm.sum_comp]
  simp [twoPortChainTerminationRegression_lowerLeft_entry,
    twoPortChainTerminationRegression_reflectionFormula_entry,
    twoPortChainTerminationRegression_lowerRight_entry]
  norm_num

/-!

## B. Zero-return response and scattering agreement

-/

/-- The scalar chain's leading block has entry two. -/
lemma twoPortChainTerminationRegression_leadingBlock_entry :
    twoPortChainTerminationRegressionChain.leadingBlock
      (BackwardWave.mk ()) (BackwardWave.mk ()) = 2 := by
  simp [twoPortChainTerminationRegressionChain,
    twoPortTerminationRegressionScalarBlock]

/-- The scalar chain's upper-right block has entry three. -/
lemma twoPortChainTerminationRegression_upperRight_entry :
    twoPortChainTerminationRegressionChain.upperRightBlock
      (BackwardWave.mk ()) (ForwardWave.mk ()) = 3 := by
  simp [twoPortChainTerminationRegressionChain,
    twoPortTerminationRegressionScalarBlock]

/-- The scalar chain's leading block acts by multiplication by two. -/
lemma twoPortChainTerminationRegression_leadingBlock_action
    (amplitude : ModeAmplitude (BackwardWave Unit)) :
    twoPortChainTerminationRegressionChain.leadingBlock.toLinearMap amplitude =
      (twoPortTerminationRegressionAmplitude
        (2 * amplitude (BackwardWave.mk ())) : ModeAmplitude (BackwardWave Unit)) := by
  apply WithLp.ofLp_injective 2
  funext index
  rcases index with ⟨⟨⟩⟩
  simp only [ModeTransform.toLinearMap, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    twoPortTerminationRegressionAmplitude]
  rw [← BackwardWave.channelEquiv.symm.sum_comp]
  simp [twoPortChainTerminationRegression_leadingBlock_entry]

/-- The scalar chain has a bijective leading block. -/
lemma twoPortChainTerminationRegression_hasBijectiveLeadingBlock :
    twoPortChainTerminationRegressionChain.HasBijectiveLeadingBlock := by
  constructor
  · intro first second hEqual
    rw [twoPortChainTerminationRegression_leadingBlock_action,
      twoPortChainTerminationRegression_leadingBlock_action] at hEqual
    have hCoordinate := congrArg
      (fun amplitude : ModeAmplitude (BackwardWave Unit) =>
        amplitude (BackwardWave.mk ())) hEqual
    change (2 : ℂ) * first (BackwardWave.mk ()) =
      (2 : ℂ) * second (BackwardWave.mk ()) at hCoordinate
    apply WithLp.ofLp_injective 2
    funext index
    rcases index with ⟨⟨⟩⟩
    exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) hCoordinate
  · intro output
    refine ⟨(twoPortTerminationRegressionAmplitude
      ((1 / 2) * output (BackwardWave.mk ())) : ModeAmplitude (BackwardWave Unit)), ?_⟩
    rw [twoPortChainTerminationRegression_leadingBlock_action]
    apply WithLp.ofLp_injective 2
    funext index
    rcases index with ⟨⟨⟩⟩
    change (2 : ℂ) * ((1 / 2) * output (BackwardWave.mk ())) =
      output (BackwardWave.mk ())
    ring

/-- The canonical zero-return pivot hypothesis for the scalar chain. -/
lemma twoPortChainTerminationRegression_hasBijectiveZeroReturnPivot :
    twoPortChainTerminationRegressionChain.HasBijectiveRightTerminationPivot
      (0 : RightLoadTransform Unit) :=
  twoPortChainTerminationRegressionChain.hasBijectiveRightTerminationPivot_zero
    twoPortChainTerminationRegression_hasBijectiveLeadingBlock

/-- The inverse leading block has singleton entry `1 / 2`. -/
lemma twoPortChainTerminationRegression_leadingBlockInverse_entry :
    (twoPortChainTerminationRegressionChain.leadingBlockInverse
      twoPortChainTerminationRegression_hasBijectiveLeadingBlock)
        (BackwardWave.mk ()) (BackwardWave.mk ()) = 1 / 2 := by
  let unitAmplitude :=
    (twoPortTerminationRegressionAmplitude 1 : ModeAmplitude (BackwardWave Unit))
  have hInverse := twoPortChainTerminationRegressionChain.leadingBlock_apply_inverse
    twoPortChainTerminationRegression_hasBijectiveLeadingBlock unitAmplitude
  rw [twoPortChainTerminationRegression_leadingBlock_action] at hInverse
  have hCoordinate := congrArg
    (fun amplitude : ModeAmplitude (BackwardWave Unit) =>
      amplitude (BackwardWave.mk ())) hInverse
  simp only [ModeTransform.toLinearMap, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    twoPortTerminationRegressionAmplitude] at hCoordinate
  rw [← BackwardWave.channelEquiv.symm.sum_comp] at hCoordinate
  simp only [Finset.univ_unique, Finset.sum_singleton] at hCoordinate
  change (2 : ℂ) *
    (twoPortChainTerminationRegressionChain.leadingBlockInverse
      twoPortChainTerminationRegression_hasBijectiveLeadingBlock
        (BackwardWave.mk ()) (BackwardWave.mk ()) * 1) = 1 at hCoordinate
  norm_num at hCoordinate
  linear_combination (1 / 2) * hCoordinate

/-- The inverse zero-return pivot has singleton entry `1 / 2`. -/
lemma twoPortChainTerminationRegression_zeroPivotInverse_entry :
    (twoPortChainTerminationRegressionChain.rightTerminationPivotInverse 0
      twoPortChainTerminationRegression_hasBijectiveZeroReturnPivot)
        (BackwardWave.mk ()) (BackwardWave.mk ()) = 1 / 2 := by
  rw [twoPortChainTerminationRegressionChain.rightTerminationPivotInverse_zero
    twoPortChainTerminationRegression_hasBijectiveLeadingBlock]
  exact twoPortChainTerminationRegression_leadingBlockInverse_entry

/-- The zero-return reflected response has singleton entry `-3 / 2`. -/
lemma twoPortChainTerminationRegression_zeroReflection_entry :
    (twoPortChainTerminationRegressionChain.rightTerminatedReflectionTransform 0
      twoPortChainTerminationRegression_hasBijectiveZeroReturnPivot)
        (BackwardWave.mk ()) (ForwardWave.mk ()) = -3 / 2 := by
  rw [twoPortChainTerminationRegressionChain.rightTerminatedReflectionTransform_eq_blockFormula,
    twoPortChainTerminationRegressionChain.rightTerminatedReflectionBlockFormula_zero
      twoPortChainTerminationRegression_hasBijectiveLeadingBlock]
  change -((twoPortChainTerminationRegressionChain.leadingBlockInverse
    twoPortChainTerminationRegression_hasBijectiveLeadingBlock *
      twoPortChainTerminationRegressionChain.upperRightBlock)
        (BackwardWave.mk ()) (ForwardWave.mk ())) = -3 / 2
  rw [Matrix.mul_apply]
  rw [← BackwardWave.channelEquiv.symm.sum_comp]
  simp [twoPortChainTerminationRegression_leadingBlockInverse_entry,
    twoPortChainTerminationRegression_upperRight_entry]
  norm_num

/-- The zero-return forward response has singleton entry `-1 / 2`. -/
lemma twoPortChainTerminationRegression_zeroTransmission_entry :
    (twoPortChainTerminationRegressionChain.rightTerminatedTransmissionTransform 0
      twoPortChainTerminationRegression_hasBijectiveZeroReturnPivot)
        (ForwardWave.mk ()) (ForwardWave.mk ()) = -1 / 2 := by
  rw [twoPortChainTerminationRegressionChain.rightTerminatedTransmissionTransform_eq_blockFormula,
    twoPortChainTerminationRegressionChain.rightTerminatedTransmissionBlockFormula_zero
      twoPortChainTerminationRegression_hasBijectiveLeadingBlock]
  change twoPortChainTerminationRegressionChain.lowerRightBlock
      (ForwardWave.mk ()) (ForwardWave.mk ()) -
    (twoPortChainTerminationRegressionChain.lowerLeftBlock *
        twoPortChainTerminationRegressionChain.leadingBlockInverse
          twoPortChainTerminationRegression_hasBijectiveLeadingBlock *
      twoPortChainTerminationRegressionChain.upperRightBlock)
        (ForwardWave.mk ()) (ForwardWave.mk ()) = -1 / 2
  rw [twoPortChainTerminationRegression_lowerRight_entry, Matrix.mul_apply,
    ← BackwardWave.channelEquiv.symm.sum_comp]
  simp only [Finset.univ_unique, Finset.sum_singleton]
  rw [Matrix.mul_apply, ← BackwardWave.channelEquiv.symm.sum_comp]
  simp only [Finset.univ_unique, Finset.sum_singleton]
  rw [twoPortChainTerminationRegression_lowerLeft_entry,
    twoPortChainTerminationRegression_leadingBlockInverse_entry,
    twoPortChainTerminationRegression_upperRight_entry]
  norm_num

/-- The zero-return forward response is not the opposite transmission value `1 / K₁₁`. -/
lemma twoPortChainTerminationRegression_zeroTransmission_ne_inverseLeading :
    (twoPortChainTerminationRegressionChain.rightTerminatedTransmissionTransform 0
      twoPortChainTerminationRegression_hasBijectiveZeroReturnPivot)
        (ForwardWave.mk ()) (ForwardWave.mk ()) ≠ 1 / 2 := by
  rw [twoPortChainTerminationRegression_zeroTransmission_entry]
  norm_num

/-- Zero-return reflection agrees with the left-reflection block of chain-to-scattering
conversion. -/
lemma twoPortChainTerminationRegression_zeroReflection_eq_scattering :
    twoPortChainTerminationRegressionChain.rightTerminatedReflectionTransform 0
        twoPortChainTerminationRegression_hasBijectiveZeroReturnPivot =
      (twoPortChainTerminationRegressionChain.toTwoPortScatteringTransform
        twoPortChainTerminationRegression_hasBijectiveLeadingBlock).leftReflection :=
  twoPortChainTerminationRegressionChain.rightTerminatedReflectionTransform_zero_eq_leftReflection
    twoPortChainTerminationRegression_hasBijectiveLeadingBlock
    twoPortChainTerminationRegression_hasBijectiveZeroReturnPivot

/-- Zero-return forward response agrees with the left-to-right block of chain-to-scattering
conversion. -/
lemma twoPortChainTerminationRegression_zeroTransmission_eq_scattering :
    twoPortChainTerminationRegressionChain.rightTerminatedTransmissionTransform 0
        twoPortChainTerminationRegression_hasBijectiveZeroReturnPivot =
      (twoPortChainTerminationRegressionChain.toTwoPortScatteringTransform
        twoPortChainTerminationRegression_hasBijectiveLeadingBlock).leftToRightTransmission :=
  BackwardFirstChainTransform.rightTerminatedTransmissionTransform_zero_eq_leftToRightTransmission
    twoPortChainTerminationRegressionChain
    twoPortChainTerminationRegression_hasBijectiveLeadingBlock
    twoPortChainTerminationRegression_hasBijectiveZeroReturnPivot

/-!

## C. Well-posed rectangular pivot without surjectivity

-/

/-- The one-column embedding into the zero coordinate of two right backward modes. -/
def twoPortChainTerminationRegressionRectangularLeading :
    ModeTransform (BackwardWave Unit) (BackwardWave (Fin 2)) :=
  fun output _ => if output.channel = 0 then 1 else 0

/-- The same one-column embedding from the left forward mode. -/
def twoPortChainTerminationRegressionRectangularIncident :
    ModeTransform (ForwardWave Unit) (BackwardWave (Fin 2)) :=
  fun output _ => if output.channel = 0 then 1 else 0

/-- A rectangular chain whose zero-return pivot and incident block have the same one-dimensional
range inside two right backward modes. -/
def twoPortChainTerminationRegressionRectangularChain :
    BackwardFirstChainTransform Unit (Fin 2) :=
  Matrix.fromBlocks twoPortChainTerminationRegressionRectangularLeading
    (-twoPortChainTerminationRegressionRectangularIncident) 0 0

/-- The two-coordinate output of the rectangular embedding. -/
def twoPortChainTerminationRegressionRectangularOutput (value : ℂ) :
    ModeAmplitude (BackwardWave (Fin 2)) :=
  WithLp.toLp 2 fun output => if output.channel = 0 then value else 0

/-- The rectangular leading block acts by embedding the singleton coordinate at index zero. -/
lemma twoPortChainTerminationRegressionRectangularLeading_action
    (amplitude : ModeAmplitude (BackwardWave Unit)) :
    twoPortChainTerminationRegressionRectangularLeading.toLinearMap amplitude =
      twoPortChainTerminationRegressionRectangularOutput
        (amplitude (BackwardWave.mk ())) := by
  apply WithLp.ofLp_injective 2
  funext output
  rcases output with ⟨output⟩
  simp only [ModeTransform.toLinearMap, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    twoPortChainTerminationRegressionRectangularOutput]
  rw [← BackwardWave.channelEquiv.symm.sum_comp]
  simp [twoPortChainTerminationRegressionRectangularLeading]

/-- The rectangular incident embedding has the same coordinate action. -/
lemma twoPortChainTerminationRegressionRectangularIncident_action
    (amplitude : ModeAmplitude (ForwardWave Unit)) :
    twoPortChainTerminationRegressionRectangularIncident.toLinearMap amplitude =
      twoPortChainTerminationRegressionRectangularOutput
        (amplitude (ForwardWave.mk ())) := by
  apply WithLp.ofLp_injective 2
  funext output
  rcases output with ⟨output⟩
  simp only [ModeTransform.toLinearMap, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    twoPortChainTerminationRegressionRectangularOutput]
  rw [← ForwardWave.channelEquiv.symm.sum_comp]
  simp [twoPortChainTerminationRegressionRectangularIncident]

/-- The zero-return pivot of the rectangular chain is its one-column leading embedding. -/
lemma twoPortChainTerminationRegressionRectangular_pivot :
    twoPortChainTerminationRegressionRectangularChain.rightTerminationPivot
        (0 : RightLoadTransform (Fin 2)) =
      twoPortChainTerminationRegressionRectangularLeading := by
  rw [BackwardFirstChainTransform.rightTerminationPivot_zero]
  exact Matrix.toBlocks_fromBlocks₁₁ _ _ _ _

/-- The zero-return incident block of the rectangular chain is the matching embedding. -/
lemma twoPortChainTerminationRegressionRectangular_incidentBlock :
    twoPortChainTerminationRegressionRectangularChain.rightTerminationIncidentBlock
        (0 : RightLoadTransform (Fin 2)) =
      twoPortChainTerminationRegressionRectangularIncident := by
  rw [BackwardFirstChainTransform.rightTerminationIncidentBlock_zero]
  change -twoPortChainTerminationRegressionRectangularChain.toBlocks₁₂ = _
  rw [twoPortChainTerminationRegressionRectangularChain]
  simp only [Matrix.toBlocks_fromBlocks₁₂, neg_neg]

/-- The rectangular termination pivot is injective. -/
lemma twoPortChainTerminationRegressionRectangular_pivot_injective :
    Function.Injective
      (twoPortChainTerminationRegressionRectangularChain.rightTerminationPivot
        (0 : RightLoadTransform (Fin 2))).toLinearMap := by
  intro first second hEqual
  rw [twoPortChainTerminationRegressionRectangular_pivot,
    twoPortChainTerminationRegressionRectangularLeading_action,
    twoPortChainTerminationRegressionRectangularLeading_action] at hEqual
  have hCoordinate := congrArg
    (fun amplitude : ModeAmplitude (BackwardWave (Fin 2)) =>
      amplitude (BackwardWave.mk 0)) hEqual
  change first (BackwardWave.mk ()) = second (BackwardWave.mk ()) at hCoordinate
  apply WithLp.ofLp_injective 2
  funext input
  rcases input with ⟨⟨⟩⟩
  exact hCoordinate

/-- Every rectangular incident forcing is solved by copying its singleton coordinate to `bL`. -/
lemma twoPortChainTerminationRegressionRectangular_pivot_solvable
    (leftIncident : ModeAmplitude (ForwardWave Unit)) :
    ∃ leftBackward : ModeAmplitude (BackwardWave Unit),
      (twoPortChainTerminationRegressionRectangularChain.rightTerminationPivot
          (0 : RightLoadTransform (Fin 2))).toLinearMap leftBackward =
        (twoPortChainTerminationRegressionRectangularChain.rightTerminationIncidentBlock
          (0 : RightLoadTransform (Fin 2))).toLinearMap leftIncident := by
  refine ⟨(twoPortTerminationRegressionAmplitude
    (leftIncident (ForwardWave.mk ())) : ModeAmplitude (BackwardWave Unit)), ?_⟩
  rw [twoPortChainTerminationRegressionRectangular_pivot,
    twoPortChainTerminationRegressionRectangular_incidentBlock,
    twoPortChainTerminationRegressionRectangularLeading_action,
    twoPortChainTerminationRegressionRectangularIncident_action]
  rfl

/-- The rectangular zero-return termination is well posed although its pivot is not surjective. -/
lemma twoPortChainTerminationRegressionRectangular_wellPosed :
    twoPortChainTerminationRegressionRectangularChain.HasWellPosedRightTermination
      (0 : RightLoadTransform (Fin 2)) := by
  apply (BackwardFirstChainTransform.hasWellPosedRightTermination_iff_pivot_injective_and_solvable
      twoPortChainTerminationRegressionRectangularChain 0).mpr
  exact ⟨twoPortChainTerminationRegressionRectangular_pivot_injective,
    twoPortChainTerminationRegressionRectangular_pivot_solvable⟩

/-- A target supported at right backward index one is outside the rectangular pivot range. -/
def twoPortChainTerminationRegressionRectangularMissingTarget :
    ModeAmplitude (BackwardWave (Fin 2)) :=
  WithLp.toLp 2 fun output => if output.channel = 1 then 1 else 0

/-- The rectangular termination pivot is not surjective. -/
lemma twoPortChainTerminationRegressionRectangular_pivot_not_surjective :
    ¬Function.Surjective
      (twoPortChainTerminationRegressionRectangularChain.rightTerminationPivot
        (0 : RightLoadTransform (Fin 2))).toLinearMap := by
  intro hSurjective
  rcases hSurjective twoPortChainTerminationRegressionRectangularMissingTarget with
    ⟨input, hInput⟩
  rw [twoPortChainTerminationRegressionRectangular_pivot,
    twoPortChainTerminationRegressionRectangularLeading_action] at hInput
  have hCoordinate := congrArg
    (fun amplitude : ModeAmplitude (BackwardWave (Fin 2)) =>
      amplitude (BackwardWave.mk 1)) hInput
  norm_num [twoPortChainTerminationRegressionRectangularOutput,
    twoPortChainTerminationRegressionRectangularMissingTarget] at hCoordinate

/-- Well-posedness of the rectangular termination does not imply pivot bijectivity. -/
lemma twoPortChainTerminationRegressionRectangular_not_hasBijectivePivot :
    ¬twoPortChainTerminationRegressionRectangularChain.HasBijectiveRightTerminationPivot
      (0 : RightLoadTransform (Fin 2)) := by
  intro hBijective
  exact twoPortChainTerminationRegressionRectangular_pivot_not_surjective hBijective.2

/-- Exact well-posedness extracts the singleton identity reflection even though the rectangular
pivot is not surjective. -/
lemma twoPortChainTerminationRegressionRectangular_reflection_entry :
    (twoPortChainTerminationRegressionRectangularChain.rightTerminatedReflectionTransformOfWellPosed
        0
        twoPortChainTerminationRegressionRectangular_wellPosed)
          (BackwardWave.mk ()) (ForwardWave.mk ()) = 1 := by
  let incident :=
    (twoPortTerminationRegressionAmplitude 1 : ModeAmplitude (ForwardWave Unit))
  let response :=
    twoPortChainTerminationRegressionRectangularChain.rightTerminatedReflectionTransformOfWellPosed
      0 twoPortChainTerminationRegressionRectangular_wellPosed
  have hGraph : (incident, response.toLinearMap incident) ∈ response.toBehavior := by
    rw [ModeTransform.mem_toBehavior_iff_toLinearMap]
  dsimp only [response] at hGraph
  rw [BackwardFirstChainTransform.toBehavior_rightTerminatedReflectionTransformOfWellPosed,
    BackwardFirstChainTransform.mem_rightTerminatedReflectionBehavior_iff_pivotEquation,
    twoPortChainTerminationRegressionRectangular_pivot,
    twoPortChainTerminationRegressionRectangular_incidentBlock,
    twoPortChainTerminationRegressionRectangularLeading_action,
    twoPortChainTerminationRegressionRectangularIncident_action] at hGraph
  have hCoordinate := congrArg
    (fun amplitude : ModeAmplitude (BackwardWave (Fin 2)) =>
      amplitude (BackwardWave.mk 0)) hGraph
  change response.toLinearMap incident (BackwardWave.mk ()) =
    incident (ForwardWave.mk ()) at hCoordinate
  simp only [ModeTransform.toLinearMap, Matrix.toLpLin_apply, Matrix.mulVec,
    dotProduct] at hCoordinate
  rw [← ForwardWave.channelEquiv.symm.sum_comp] at hCoordinate
  simpa [response, incident, twoPortTerminationRegressionAmplitude] using hCoordinate

/-- Exact well-posedness extracts zero forward response for the rectangular fixture without a
bijective-pivot proof. -/
lemma twoPortChainTerminationRegressionRectangular_transmission_eq_zero :
    BackwardFirstChainTransform.rightTerminatedTransmissionTransformOfWellPosed
        twoPortChainTerminationRegressionRectangularChain 0
          twoPortChainTerminationRegressionRectangular_wellPosed = 0 := by
  let response :=
    BackwardFirstChainTransform.rightTerminatedTransmissionTransformOfWellPosed
      twoPortChainTerminationRegressionRectangularChain 0
        twoPortChainTerminationRegressionRectangular_wellPosed
  ext output input
  rcases input with ⟨⟨⟩⟩
  let incident :=
    (twoPortTerminationRegressionAmplitude 1 : ModeAmplitude (ForwardWave Unit))
  have hGraph : (incident, response.toLinearMap incident) ∈ response.toBehavior := by
    rw [ModeTransform.mem_toBehavior_iff_toLinearMap]
  dsimp only [response] at hGraph
  rw [BackwardFirstChainTransform.toBehavior_rightTerminatedTransmissionTransformOfWellPosed,
    BackwardFirstChainTransform.mem_rightTerminatedTransmissionBehavior_iff_pivotEquation]
      at hGraph
  rcases hGraph with ⟨leftBackward, _, hForward⟩
  have hZero : response.toLinearMap incident = 0 := by
    simpa [response, twoPortChainTerminationRegressionRectangularChain] using hForward
  have hCoordinate := congrArg
    (fun amplitude : ModeAmplitude (ForwardWave (Fin 2)) => amplitude output) hZero
  simp only [ModeTransform.toLinearMap, Matrix.toLpLin_apply, Matrix.mulVec,
    dotProduct] at hCoordinate
  rw [← ForwardWave.channelEquiv.symm.sum_comp] at hCoordinate
  simpa [response, incident, twoPortTerminationRegressionAmplitude] using hCoordinate

/-!

## D. Singular loaded relation without a response transform

-/

/-- The scalar chain `[[1, 1], [1, 0]]` whose unit-return pivot vanishes. -/
def twoPortChainTerminationRegressionZeroPivotChain : BackwardFirstChainTransform Unit Unit :=
  Matrix.fromBlocks
    (twoPortTerminationRegressionScalarBlock 1)
    (twoPortTerminationRegressionScalarBlock 1)
    (twoPortTerminationRegressionScalarBlock 1) 0

/-- The unit right-return transform for the singular relation fixture. -/
def twoPortChainTerminationRegressionUnitReturn : RightLoadTransform Unit :=
  twoPortTerminationRegressionScalarBlock 1

/-- The singular fixture's loaded pivot is zero. -/
lemma twoPortChainTerminationRegressionSingular_pivot :
    twoPortChainTerminationRegressionZeroPivotChain.rightTerminationPivot
        twoPortChainTerminationRegressionUnitReturn = 0 := by
  ext output input
  rcases output with ⟨⟨⟩⟩
  rcases input with ⟨⟨⟩⟩
  simp [BackwardFirstChainTransform.rightTerminationPivot,
    twoPortChainTerminationRegressionZeroPivotChain,
    twoPortChainTerminationRegressionUnitReturn,
    twoPortTerminationRegressionScalarBlock, Matrix.mul_apply]

/-- The singular fixture's incident block is scalar `-1`. -/
lemma twoPortChainTerminationRegressionSingular_incidentBlock :
    twoPortChainTerminationRegressionZeroPivotChain.rightTerminationIncidentBlock
        twoPortChainTerminationRegressionUnitReturn =
      (twoPortTerminationRegressionScalarBlock (-1) :
        ModeTransform (ForwardWave Unit) (BackwardWave Unit)) := by
  ext output input
  rcases output with ⟨⟨⟩⟩
  rcases input with ⟨⟨⟩⟩
  simp [BackwardFirstChainTransform.rightTerminationIncidentBlock,
    twoPortChainTerminationRegressionZeroPivotChain,
    twoPortChainTerminationRegressionUnitReturn,
    twoPortTerminationRegressionScalarBlock]

/-- The singular incident block negates the unique left incident coordinate. -/
lemma twoPortChainTerminationRegressionSingular_incidentBlock_action
    (amplitude : ModeAmplitude (ForwardWave Unit)) :
    (twoPortChainTerminationRegressionZeroPivotChain.rightTerminationIncidentBlock
      twoPortChainTerminationRegressionUnitReturn).toLinearMap amplitude =
      (twoPortTerminationRegressionAmplitude
        (-amplitude (ForwardWave.mk ())) : ModeAmplitude (BackwardWave Unit)) := by
  rw [twoPortChainTerminationRegressionSingular_incidentBlock]
  apply WithLp.ofLp_injective 2
  funext output
  rcases output with ⟨⟨⟩⟩
  simp only [ModeTransform.toLinearMap, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    twoPortTerminationRegressionAmplitude]
  rw [← ForwardWave.channelEquiv.symm.sum_comp]
  simp [twoPortTerminationRegressionScalarBlock]

/-- The singular loaded relation is not total: a unit incident wave has no pivot solution. -/
lemma twoPortChainTerminationRegressionSingular_not_isTotal :
    ¬(twoPortChainTerminationRegressionZeroPivotChain.rightTerminationBehavior
      twoPortChainTerminationRegressionUnitReturn).IsTotal := by
  intro hTotal
  have hSolvable :=
    (BackwardFirstChainTransform.isTotal_rightTerminationBehavior_iff_pivot_solvable
      twoPortChainTerminationRegressionZeroPivotChain
      twoPortChainTerminationRegressionUnitReturn).mp hTotal
  let unitIncident :=
    (twoPortTerminationRegressionAmplitude 1 : ModeAmplitude (ForwardWave Unit))
  rcases hSolvable unitIncident with ⟨leftBackward, hPivot⟩
  rw [twoPortChainTerminationRegressionSingular_pivot,
    twoPortChainTerminationRegressionSingular_incidentBlock_action] at hPivot
  have hCoordinate := congrArg
    (fun amplitude : ModeAmplitude (BackwardWave Unit) =>
      amplitude (BackwardWave.mk ())) hPivot
  norm_num [ModeTransform.toLinearMap, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    unitIncident, twoPortTerminationRegressionAmplitude] at hCoordinate

/-- The singular loaded relation is not single-valued: its zero pivot leaves `bL` free at zero
incident forcing. -/
lemma twoPortChainTerminationRegressionSingular_not_isSingleValued :
    ¬(twoPortChainTerminationRegressionZeroPivotChain.rightTerminationBehavior
      twoPortChainTerminationRegressionUnitReturn).IsSingleValued := by
  rw [BackwardFirstChainTransform.isSingleValued_rightTerminationBehavior_iff_pivot_injective]
  intro hInjective
  let unitBackward :=
    (twoPortTerminationRegressionAmplitude 1 : ModeAmplitude (BackwardWave Unit))
  have hEqual :
      (twoPortChainTerminationRegressionZeroPivotChain.rightTerminationPivot
        twoPortChainTerminationRegressionUnitReturn).toLinearMap unitBackward =
      (twoPortChainTerminationRegressionZeroPivotChain.rightTerminationPivot
        twoPortChainTerminationRegressionUnitReturn).toLinearMap 0 := by
    rw [twoPortChainTerminationRegressionSingular_pivot]
    simp
  have hZero := hInjective hEqual
  have hCoordinate := congrArg
    (fun amplitude : ModeAmplitude (BackwardWave Unit) =>
      amplitude (BackwardWave.mk ())) hZero
  norm_num [unitBackward, twoPortTerminationRegressionAmplitude] at hCoordinate

/-- The singular loaded relation has no well-posed response transform. -/
lemma twoPortChainTerminationRegressionSingular_not_wellPosed :
    ¬twoPortChainTerminationRegressionZeroPivotChain.HasWellPosedRightTermination
      twoPortChainTerminationRegressionUnitReturn := by
  intro hWellPosed
  exact twoPortChainTerminationRegressionSingular_not_isTotal hWellPosed.1

/-!

## E. Noncommuting two-mode loaded response

-/

/-- The leading block `2 I` of the noncommuting fixture. -/
def twoPortChainTerminationRegressionNoncommutingLeading :
    ModeTransform (BackwardWave (Fin 2)) (BackwardWave (Fin 2)) :=
  fun output input => if output.channel = input.channel then 2 else 0

/-- The upper-right block `I` of the noncommuting fixture. -/
def twoPortChainTerminationRegressionNoncommutingUpperRight :
    ModeTransform (ForwardWave (Fin 2)) (BackwardWave (Fin 2)) :=
  fun output input => if output.channel = input.channel then 1 else 0

/-- The lower-left block `E₂₁` of the noncommuting fixture. -/
def twoPortChainTerminationRegressionNoncommutingLowerLeft :
    ModeTransform (BackwardWave (Fin 2)) (ForwardWave (Fin 2)) :=
  fun output input => if output.channel = 1 ∧ input.channel = 0 then 1 else 0

/-- The lower-right block `I` of the noncommuting fixture. -/
def twoPortChainTerminationRegressionNoncommutingLowerRight :
    ModeTransform (ForwardWave (Fin 2)) (ForwardWave (Fin 2)) :=
  fun output input => if output.channel = input.channel then 1 else 0

/-- The right-return block `E₁₂` of the noncommuting fixture. -/
def twoPortChainTerminationRegressionNoncommutingLoad : RightLoadTransform (Fin 2) :=
  fun output input => if output.channel = 0 ∧ input.channel = 1 then 1 else 0

/-- The two-mode chain assembled from `A = 2 I`, `B = I`, `C = E₂₁`, and `D = I`. -/
def twoPortChainTerminationRegressionNoncommutingChain :
    BackwardFirstChainTransform (Fin 2) (Fin 2) :=
  Matrix.fromBlocks twoPortChainTerminationRegressionNoncommutingLeading
    twoPortChainTerminationRegressionNoncommutingUpperRight
    twoPortChainTerminationRegressionNoncommutingLowerLeft
    twoPortChainTerminationRegressionNoncommutingLowerRight

/-- The expected pivot `diag(1, 2)` of the noncommuting fixture. -/
def twoPortChainTerminationRegressionNoncommutingPivot :
    ModeTransform (BackwardWave (Fin 2)) (BackwardWave (Fin 2)) :=
  fun output input =>
    if output.channel = input.channel then
      if output.channel = 0 then 1 else 2
    else 0

/-- The expected inverse pivot `diag(1, 1 / 2)`. -/
def twoPortChainTerminationRegressionNoncommutingPivotInverse :
    ModeTransform (BackwardWave (Fin 2)) (BackwardWave (Fin 2)) :=
  fun output input =>
    if output.channel = input.channel then
      if output.channel = 0 then 1 else 1 / 2
    else 0

/-- The expected incident block `E₁₂ - I` of the noncommuting fixture. -/
def twoPortChainTerminationRegressionNoncommutingIncident :
    ModeTransform (ForwardWave (Fin 2)) (BackwardWave (Fin 2)) :=
  fun output input =>
    if output.channel = 0 ∧ input.channel = 1 then 1
    else if output.channel = input.channel then -1 else 0

/-- The expected loaded reflection matrix `[[-1, 1], [0, -1/2]]`. -/
def twoPortChainTerminationRegressionNoncommutingReflection :
    ModeTransform (ForwardWave (Fin 2)) (BackwardWave (Fin 2)) :=
  fun output input =>
    if output.channel = 0 ∧ input.channel = 0 then -1
    else if output.channel = 0 ∧ input.channel = 1 then 1
    else if output.channel = 1 ∧ input.channel = 1 then -1 / 2
    else 0

/-- The expected loaded forward matrix `[[1, 0], [-1, 2]]`. -/
def twoPortChainTerminationRegressionNoncommutingTransmission :
    ModeTransform (ForwardWave (Fin 2)) (ForwardWave (Fin 2)) :=
  fun output input =>
    if output.channel = 0 ∧ input.channel = 0 then 1
    else if output.channel = 1 ∧ input.channel = 0 then -1
    else if output.channel = 1 ∧ input.channel = 1 then 2
    else 0

/-- The two-mode termination pivot is exactly `diag(1, 2)`. -/
lemma twoPortChainTerminationRegressionNoncommuting_pivot :
    twoPortChainTerminationRegressionNoncommutingChain.rightTerminationPivot
        twoPortChainTerminationRegressionNoncommutingLoad =
      twoPortChainTerminationRegressionNoncommutingPivot := by
  ext output input
  rcases output with ⟨output⟩
  rcases input with ⟨input⟩
  fin_cases output <;> fin_cases input <;>
    norm_num [BackwardFirstChainTransform.rightTerminationPivot,
      twoPortChainTerminationRegressionNoncommutingChain,
      twoPortChainTerminationRegressionNoncommutingLeading,
      twoPortChainTerminationRegressionNoncommutingLowerLeft,
      twoPortChainTerminationRegressionNoncommutingLoad,
      twoPortChainTerminationRegressionNoncommutingPivot, Matrix.mul_apply,
      ← ForwardWave.channelEquiv.symm.sum_comp, Fin.sum_univ_two]

/-- The two-mode incident block is exactly `E₁₂ - I`. -/
lemma twoPortChainTerminationRegressionNoncommuting_incidentBlock :
    twoPortChainTerminationRegressionNoncommutingChain.rightTerminationIncidentBlock
        twoPortChainTerminationRegressionNoncommutingLoad =
      twoPortChainTerminationRegressionNoncommutingIncident := by
  ext output input
  rcases output with ⟨output⟩
  rcases input with ⟨input⟩
  fin_cases output <;> fin_cases input <;>
    simp [BackwardFirstChainTransform.rightTerminationIncidentBlock,
      twoPortChainTerminationRegressionNoncommutingChain,
      twoPortChainTerminationRegressionNoncommutingUpperRight,
      twoPortChainTerminationRegressionNoncommutingLowerRight,
      twoPortChainTerminationRegressionNoncommutingLoad,
      twoPortChainTerminationRegressionNoncommutingIncident, Matrix.mul_apply,
      ← ForwardWave.channelEquiv.symm.sum_comp, Fin.sum_univ_two]

/-- The proposed diagonal inverse is a left inverse of the two-mode pivot. -/
lemma twoPortChainTerminationRegressionNoncommuting_inverse_mul_pivot :
    twoPortChainTerminationRegressionNoncommutingPivotInverse *
        twoPortChainTerminationRegressionNoncommutingPivot = 1 := by
  ext output input
  rcases output with ⟨output⟩
  rcases input with ⟨input⟩
  fin_cases output <;> fin_cases input <;>
    norm_num [twoPortChainTerminationRegressionNoncommutingPivotInverse,
      twoPortChainTerminationRegressionNoncommutingPivot, Matrix.mul_apply,
      ← BackwardWave.channelEquiv.symm.sum_comp, Fin.sum_univ_two]

/-- The proposed diagonal inverse is a right inverse of the two-mode pivot. -/
lemma twoPortChainTerminationRegressionNoncommuting_pivot_mul_inverse :
    twoPortChainTerminationRegressionNoncommutingPivot *
        twoPortChainTerminationRegressionNoncommutingPivotInverse = 1 := by
  ext output input
  rcases output with ⟨output⟩
  rcases input with ⟨input⟩
  fin_cases output <;> fin_cases input <;>
    norm_num [twoPortChainTerminationRegressionNoncommutingPivotInverse,
      twoPortChainTerminationRegressionNoncommutingPivot, Matrix.mul_apply,
      ← BackwardWave.channelEquiv.symm.sum_comp, Fin.sum_univ_two]

/-- The noncommuting two-mode termination pivot is bijective. -/
lemma twoPortChainTerminationRegressionNoncommuting_hasBijectivePivot :
    twoPortChainTerminationRegressionNoncommutingChain.HasBijectiveRightTerminationPivot
      twoPortChainTerminationRegressionNoncommutingLoad := by
  rw [BackwardFirstChainTransform.HasBijectiveRightTerminationPivot,
    twoPortChainTerminationRegressionNoncommuting_pivot]
  constructor
  · intro first second hEqual
    have hMapped := congrArg
      twoPortChainTerminationRegressionNoncommutingPivotInverse.toLinearMap hEqual
    simpa only [← ModeTransform.toLinearMap_mul_apply,
      twoPortChainTerminationRegressionNoncommuting_inverse_mul_pivot,
      ModeTransform.toLinearMap, Matrix.toLpLin_one, LinearMap.id_apply] using hMapped
  · intro output
    refine ⟨twoPortChainTerminationRegressionNoncommutingPivotInverse.toLinearMap output, ?_⟩
    rw [← ModeTransform.toLinearMap_mul_apply,
      twoPortChainTerminationRegressionNoncommuting_pivot_mul_inverse]
    simp only [ModeTransform.toLinearMap, Matrix.toLpLin_one, LinearMap.id_apply]

/-- The inverse constructed from pivot bijectivity is the expected diagonal matrix. -/
lemma twoPortChainTerminationRegressionNoncommuting_pivotInverse :
    twoPortChainTerminationRegressionNoncommutingChain.rightTerminationPivotInverse
        twoPortChainTerminationRegressionNoncommutingLoad
        twoPortChainTerminationRegressionNoncommuting_hasBijectivePivot =
      twoPortChainTerminationRegressionNoncommutingPivotInverse := by
  apply Matrix.toEuclideanLin.injective
  apply LinearMap.ext
  intro amplitude
  apply twoPortChainTerminationRegressionNoncommuting_hasBijectivePivot.1
  calc
    (twoPortChainTerminationRegressionNoncommutingChain.rightTerminationPivot
        twoPortChainTerminationRegressionNoncommutingLoad).toLinearMap
        ((twoPortChainTerminationRegressionNoncommutingChain.rightTerminationPivotInverse
          twoPortChainTerminationRegressionNoncommutingLoad
          twoPortChainTerminationRegressionNoncommuting_hasBijectivePivot).toLinearMap
            amplitude) = amplitude :=
      twoPortChainTerminationRegressionNoncommutingChain.rightTerminationPivot_apply_inverse
        twoPortChainTerminationRegressionNoncommutingLoad
        twoPortChainTerminationRegressionNoncommuting_hasBijectivePivot amplitude
    _ = (twoPortChainTerminationRegressionNoncommutingChain.rightTerminationPivot
        twoPortChainTerminationRegressionNoncommutingLoad).toLinearMap
          (twoPortChainTerminationRegressionNoncommutingPivotInverse.toLinearMap amplitude) := by
      rw [twoPortChainTerminationRegressionNoncommuting_pivot,
        ← ModeTransform.toLinearMap_mul_apply,
        twoPortChainTerminationRegressionNoncommuting_pivot_mul_inverse]
      simp only [ModeTransform.toLinearMap, Matrix.toLpLin_one, LinearMap.id_apply]

/-- The explicit noncommuting reflection formula has the expected ordered product. -/
lemma twoPortChainTerminationRegressionNoncommuting_reflectionFormula :
    twoPortChainTerminationRegressionNoncommutingChain.rightTerminatedReflectionBlockFormula
        twoPortChainTerminationRegressionNoncommutingLoad
        twoPortChainTerminationRegressionNoncommuting_hasBijectivePivot =
      twoPortChainTerminationRegressionNoncommutingReflection := by
  rw [BackwardFirstChainTransform.rightTerminatedReflectionBlockFormula,
    twoPortChainTerminationRegressionNoncommuting_pivotInverse,
    twoPortChainTerminationRegressionNoncommuting_incidentBlock]
  ext output input
  rcases output with ⟨output⟩
  rcases input with ⟨input⟩
  fin_cases output <;> fin_cases input <;>
    norm_num [twoPortChainTerminationRegressionNoncommutingPivotInverse,
      twoPortChainTerminationRegressionNoncommutingIncident,
      twoPortChainTerminationRegressionNoncommutingReflection, Matrix.mul_apply,
      ← BackwardWave.channelEquiv.symm.sum_comp, Fin.sum_univ_two]

/-- The behavior-derived noncommuting reflection transform has the expected matrix. -/
lemma twoPortChainTerminationRegressionNoncommuting_reflection :
    twoPortChainTerminationRegressionNoncommutingChain.rightTerminatedReflectionTransform
        twoPortChainTerminationRegressionNoncommutingLoad
        twoPortChainTerminationRegressionNoncommuting_hasBijectivePivot =
      twoPortChainTerminationRegressionNoncommutingReflection := by
  rw [BackwardFirstChainTransform.rightTerminatedReflectionTransform_eq_blockFormula]
  exact twoPortChainTerminationRegressionNoncommuting_reflectionFormula

/-- The behavior-derived noncommuting forward transform has the expected matrix. -/
lemma twoPortChainTerminationRegressionNoncommuting_transmission :
    twoPortChainTerminationRegressionNoncommutingChain.rightTerminatedTransmissionTransform
        twoPortChainTerminationRegressionNoncommutingLoad
        twoPortChainTerminationRegressionNoncommuting_hasBijectivePivot =
      twoPortChainTerminationRegressionNoncommutingTransmission := by
  rw [BackwardFirstChainTransform.rightTerminatedTransmissionTransform_eq_blockFormula,
    BackwardFirstChainTransform.rightTerminatedTransmissionBlockFormula,
    twoPortChainTerminationRegressionNoncommuting_reflectionFormula]
  ext output input
  rcases output with ⟨output⟩
  rcases input with ⟨input⟩
  fin_cases output <;> fin_cases input <;>
    norm_num [twoPortChainTerminationRegressionNoncommutingChain,
      twoPortChainTerminationRegressionNoncommutingLowerLeft,
      twoPortChainTerminationRegressionNoncommutingLowerRight,
      twoPortChainTerminationRegressionNoncommutingReflection,
      twoPortChainTerminationRegressionNoncommutingTransmission, Matrix.mul_apply,
      ← BackwardWave.channelEquiv.symm.sum_comp, Fin.sum_univ_two]

/-- The lower-right reflection entry records the inverse scaling of the second pivot coordinate. -/
lemma twoPortChainTerminationRegressionNoncommuting_reflection_lowerRight_entry :
    (twoPortChainTerminationRegressionNoncommutingChain.rightTerminatedReflectionTransform
      twoPortChainTerminationRegressionNoncommutingLoad
      twoPortChainTerminationRegressionNoncommuting_hasBijectivePivot)
        (BackwardWave.mk 1) (ForwardWave.mk 1) = -1 / 2 := by
  rw [twoPortChainTerminationRegressionNoncommuting_reflection]
  simp [twoPortChainTerminationRegressionNoncommutingReflection]

/-- The upper-right reflection entry is one; right multiplication by the pivot inverse would give
`1 / 2`, so this pins the order `P⁻¹ Q`. -/
lemma twoPortChainTerminationRegressionNoncommuting_reflection_upperRight_entry :
    (twoPortChainTerminationRegressionNoncommutingChain.rightTerminatedReflectionTransform
      twoPortChainTerminationRegressionNoncommutingLoad
      twoPortChainTerminationRegressionNoncommuting_hasBijectivePivot)
        (BackwardWave.mk 0) (ForwardWave.mk 1) = 1 := by
  rw [twoPortChainTerminationRegressionNoncommuting_reflection]
  simp [twoPortChainTerminationRegressionNoncommutingReflection]

/-- The lower-left forward entry is `-1`, pinning the ordered product `K₂₁ RΓ`. -/
lemma twoPortChainTerminationRegressionNoncommuting_transmission_lowerLeft_entry :
    (twoPortChainTerminationRegressionNoncommutingChain.rightTerminatedTransmissionTransform
      twoPortChainTerminationRegressionNoncommutingLoad
      twoPortChainTerminationRegressionNoncommuting_hasBijectivePivot)
        (ForwardWave.mk 1) (ForwardWave.mk 0) = -1 := by
  rw [twoPortChainTerminationRegressionNoncommuting_transmission]
  simp [twoPortChainTerminationRegressionNoncommutingTransmission]

end

end Optics
