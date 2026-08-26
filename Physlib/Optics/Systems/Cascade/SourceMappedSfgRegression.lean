/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Systems.Cascade.SourceMappedSfg
public import Physlib.Optics.Systems.Microring.AddDropRegression

/-!
# Regression anchors for the stagewise SFG-TR'14 dictionary

## i. Overview

This file evaluates the composed source dictionary directly at two exact `3-4-5` add-drop
fixtures. At zero phase the principal square root selects Physlib's first half arc and both give
`-32/91`. At a half turn it selects the opposite square-root branch: the source composition gives
`-32*I/109`, while the N7/N5 drop transfer gives `32*I/109`.

## ii. Key results

- `sourceMappedSfgRegression_zeroPhase_transfer`: direct positive-branch evaluation.
- `sourceMappedSfgRegression_halfTurn_transfer`: direct opposite-branch evaluation.
- `sourceMappedSfgRegression_halfTurn_transfer_ne_dropTransfer`: a failing branch fixture.

## iii. Table of contents

- A. Principal-root evaluations
- B. Direct transfer anchors
- C. Branch-gate negative control

## iv. References and non-claims

The fixtures come from `Physlib/Optics/Systems/Microring/AddDropRegression.lean:62-69,402-409`.
The anchors unfold the composed dictionary and source quotient; they do not invoke either
comparison lemma in `SourceMappedSfg`. They test branch sensitivity, not a physically connected
two-stage cascade. No power or source-parity claim beyond the already audited SFG-TR bridge is
made.
-/

@[expose] public section

namespace Optics

noncomputable section

open scoped ComplexOrder

namespace MicroringCascade

open MicroringSourceBridge

/-! ## A. Principal-root evaluations -/

/-- The principal complex square root of the positive quarter is the positive half. -/
lemma sourceMappedSfgRegression_sqrt_quarter :
    Complex.sqrt (1 / 4 : ℂ) = 1 / 2 := by
  have hRealSqrt : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
    apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2
    norm_num
  have hNonnegative : (0 : ℂ) ≤ 1 / 4 := by
    norm_num [Complex.nonneg_iff]
  calc
    Complex.sqrt (1 / 4) = (Real.sqrt (1 / 4 : ℝ) : ℂ) := by
      rw [Complex.sqrt_of_nonneg hNonnegative]
      norm_num
    _ = 1 / 2 := by rw [hRealSqrt]; norm_num

/-- The principal complex square root of the negative quarter is the positive imaginary half. -/
lemma sourceMappedSfgRegression_sqrt_neg_quarter :
    Complex.sqrt (-1 / 4 : ℂ) = Complex.I / 2 := by
  have hNonnegative : (0 : ℂ) ≤ 1 / 4 := by
    norm_num [Complex.nonneg_iff]
  rw [show (-1 / 4 : ℂ) = -(1 / 4) by ring,
    Complex.sqrt_neg_of_nonneg hNonnegative,
    sourceMappedSfgRegression_sqrt_quarter]
  ring

/-! ## B. Direct transfer anchors -/

/-- Direct source-quotient expansion at zero phase gives `-32/91`. -/
lemma sourceMappedSfgRegression_zeroPhase_transfer :
    sfgAddDropStageTransfer AddDrop.addDropRegressionResonanceParameters = -32 / 91 := by
  rw [sfgAddDropStageTransfer, Function.comp_apply, sfgAddDropTransfer]
  simp only [SfgParameters.ofAddDrop]
  rw [AddDrop.addDropRegression_resonance_roundTripCoefficient,
    sourceMappedSfgRegression_sqrt_quarter]
  norm_num [AddDrop.addDropRegressionResonanceParameters]

/-- Direct source-quotient expansion at a half turn gives the opposite-branch value
`-32*I/109`. -/
lemma sourceMappedSfgRegression_halfTurn_transfer :
    sfgAddDropStageTransfer AddDrop.addDropRegressionAntiresonanceParameters =
      -32 * Complex.I / 109 := by
  rw [sfgAddDropStageTransfer, Function.comp_apply, sfgAddDropTransfer]
  simp only [SfgParameters.ofAddDrop]
  rw [AddDrop.addDropRegression_antiresonance_roundTripCoefficient,
    sourceMappedSfgRegression_sqrt_neg_quarter]
  norm_num [AddDrop.addDropRegressionAntiresonanceParameters]
  ring

/-- The two concrete source transfers remain visibly ordered in a stage list. -/
lemma sourceMappedSfgRegression_twoStage_list :
    sfgAddDropStageTransfers
        [AddDrop.addDropRegressionResonanceParameters,
          AddDrop.addDropRegressionAntiresonanceParameters] =
      [-32 / 91, -32 * Complex.I / 109] := by
  simp [sfgAddDropStageTransfers,
    sourceMappedSfgRegression_zeroPhase_transfer,
    sourceMappedSfgRegression_halfTurn_transfer]

/-! ## C. Branch-gate negative control -/

/-- The zero-phase fixture inhabits the principal-root/selected-half-arc comparison gate. -/
lemma sourceMappedSfgRegression_zeroPhase_rootGate :
    Complex.sqrt AddDrop.addDropRegressionResonanceParameters.roundTripCoefficient =
      AddDrop.addDropRegressionResonanceParameters.firstArcCoefficient := by
  rw [AddDrop.addDropRegression_resonance_roundTripCoefficient,
    AddDrop.addDropRegression_resonance_firstArcCoefficient,
    sourceMappedSfgRegression_sqrt_quarter]

/-- At a half turn, the principal root and Physlib's selected first half arc differ. -/
lemma sourceMappedSfgRegression_halfTurn_not_rootGate :
    Complex.sqrt AddDrop.addDropRegressionAntiresonanceParameters.roundTripCoefficient ≠
      AddDrop.addDropRegressionAntiresonanceParameters.firstArcCoefficient := by
  rw [AddDrop.addDropRegression_antiresonance_roundTripCoefficient,
    AddDrop.addDropRegression_antiresonance_firstArcCoefficient,
    sourceMappedSfgRegression_sqrt_neg_quarter]
  intro hEqual
  have hImaginary := congrArg Complex.im hEqual
  norm_num at hImaginary

/-- The source composition is false as an N7/N5 drop-transfer equality when the root gate fails. -/
lemma sourceMappedSfgRegression_halfTurn_transfer_ne_dropTransfer :
    sfgAddDropStageTransfer AddDrop.addDropRegressionAntiresonanceParameters ≠
      AddDrop.dropTransfer AddDrop.addDropRegressionAntiresonanceParameters := by
  rw [sourceMappedSfgRegression_halfTurn_transfer,
    AddDrop.addDropRegression_antiresonance_dropTransfer]
  intro hEqual
  have hImaginary := congrArg Complex.im hEqual
  norm_num at hImaginary

end MicroringCascade

end

end Optics
