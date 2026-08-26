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
`-32*I/109`, while the totalized algebraic drop transfer gives `32*I/109`.

At the zero-phase point, a separate equality connects the direct source evaluation to the
existing raw-N5 response anchor. A denominator-zero fixture then shows that both scalar
quotients remain totalized while the raw N5 feedback operator has a displayed nonzero kernel.

## ii. Key results

- `sourceMappedSfgRegression_zeroPhase_transfer`: direct positive-branch evaluation.
- `sourceMappedSfgRegression_zeroPhase_transfer_eq_rawN5`: equality with the raw N5 response.
- `sourceMappedSfgRegression_halfTurn_transfer`: direct opposite-branch evaluation.
- `sourceMappedSfgRegression_halfTurn_transfer_ne_dropTransfer`: a failing branch fixture.
- `sourceMappedSfgRegressionSingular_not_isWellPosed`: raw feedback-kernel failure.

## iii. Table of contents

- A. Principal-root evaluations
- B. Direct transfer anchors
- C. Independent raw-N5 anchor
- D. Branch-gate negative control
- E. Denominator-zero control

## iv. References and non-claims

The fixtures come from `Physlib/Optics/Systems/Microring/AddDropRegression.lean:62-69,402-409`.
The anchors unfold the composed dictionary and source quotient; they do not invoke either
comparison lemma in `SourceMappedSfg`. They test branch sensitivity, not a physically connected
two-stage cascade. No power or source-parity claim beyond the already audited SFG-TR bridge is
made. The singular parameters are not asserted valid, passive, lossless, or reciprocal.
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

/-! ## C. Independent raw-N5 anchor -/

/-- The directly evaluated source quotient equals the independently eliminated N5 response
entry at the zero-phase point.

The N5 equality used on the right is proved from raw scattering, routing, and readout equations at
`Physlib/Optics/Systems/Microring/AddDropRegression.lean:267-344`. Neither comparison lemma in
`SourceMappedSfg` occurs in this proof.
-/
lemma sourceMappedSfgRegression_zeroPhase_transfer_eq_rawN5 :
    sfgAddDropStageTransfer AddDrop.addDropRegressionResonanceParameters =
      (AddDrop.netlist AddDrop.addDropRegressionResonanceParameters).responseTransform
        AddDrop.addDropRegression_resonance_isWellPosed
        (Outgoing.mk
          (AddDrop.dropChannel AddDrop.addDropRegressionResonanceParameters))
        (Incident.mk
          (AddDrop.inputChannel AddDrop.addDropRegressionResonanceParameters)) := by
  rw [sourceMappedSfgRegression_zeroPhase_transfer,
    AddDrop.addDropRegression_resonance_responseTransform_entry_drop]

/-! ## D. Branch-gate negative control -/

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

/-- The source composition is false as an algebraic drop-transfer equality when the root gate
fails. The compared object is the totalized scalar `dropTransfer`, not an N5 response entry. -/
lemma sourceMappedSfgRegression_halfTurn_transfer_ne_dropTransfer :
    sfgAddDropStageTransfer AddDrop.addDropRegressionAntiresonanceParameters ≠
      AddDrop.dropTransfer AddDrop.addDropRegressionAntiresonanceParameters := by
  rw [sourceMappedSfgRegression_halfTurn_transfer,
    AddDrop.addDropRegression_antiresonance_dropTransfer]
  intro hEqual
  have hImaginary := congrArg Complex.im hEqual
  norm_num at hImaginary

/-! ## E. Denominator-zero control -/

/-- Exact zero-denominator add-drop data with nonzero cross coefficients and unit arc factors. -/
def sourceMappedSfgRegressionSingularParameters : AddDrop.Parameters where
  inputThroughAmplitude := 1
  inputCrossAmplitude := 1
  dropThroughAmplitude := 1
  dropCrossAmplitude := 1
  fieldAttenuation := 1
  roundTripPhase := 0

/-- Direct arc expansion gives two unit propagation coefficients at the singular point. -/
lemma sourceMappedSfgRegressionSingular_arcCoefficients :
    sourceMappedSfgRegressionSingularParameters.firstArcCoefficient = 1 ∧
      sourceMappedSfgRegressionSingularParameters.secondArcCoefficient = 1 := by
  constructor <;>
    norm_num [sourceMappedSfgRegressionSingularParameters,
      AddDrop.Parameters.firstArcCoefficient,
      AddDrop.Parameters.secondArcCoefficient,
      AddDrop.Parameters.firstPropagation,
      AddDrop.Parameters.secondPropagation,
      AddDrop.Parameters.halfArcAttenuation,
      AddDrop.Parameters.halfArcPhase,
      MatchedPropagation.transmissionCoefficient,
      MatchedPropagation.carrierPhaseFactor]

/-- The two unit arcs give unit round-trip coefficient at the singular point. -/
lemma sourceMappedSfgRegressionSingular_roundTripCoefficient :
    sourceMappedSfgRegressionSingularParameters.roundTripCoefficient = 1 := by
  rw [AddDrop.Parameters.roundTripCoefficient,
    sourceMappedSfgRegressionSingular_arcCoefficients.1,
    sourceMappedSfgRegressionSingular_arcCoefficients.2]
  norm_num

/-- Direct expansion gives a zero circulation denominator. -/
lemma sourceMappedSfgRegressionSingular_denominator :
    sourceMappedSfgRegressionSingularParameters.denominator = 0 := by
  rw [AddDrop.Parameters.denominator, AddDrop.Parameters.loopGain,
    sourceMappedSfgRegressionSingular_roundTripCoefficient]
  norm_num [sourceMappedSfgRegressionSingularParameters]

/-- The named scalar solve gate fails directly at the zero denominator. -/
lemma sourceMappedSfgRegressionSingular_not_hasNonzeroDenominator :
    ¬sourceMappedSfgRegressionSingularParameters.HasNonzeroDenominator := by
  rw [AddDrop.Parameters.HasNonzeroDenominator,
    sourceMappedSfgRegressionSingular_denominator]
  simp

/-- The source principal root still agrees with the selected half arc at the singular point. -/
lemma sourceMappedSfgRegressionSingular_rootGate :
    Complex.sqrt sourceMappedSfgRegressionSingularParameters.roundTripCoefficient =
      sourceMappedSfgRegressionSingularParameters.firstArcCoefficient := by
  rw [sourceMappedSfgRegressionSingular_roundTripCoefficient,
    sourceMappedSfgRegressionSingular_arcCoefficients.1]
  simp

/-- SFG-TR's quotient remains totalized and evaluates to zero at the zero denominator. -/
lemma sourceMappedSfgRegressionSingular_sfgTransfer :
    sfgAddDropStageTransfer sourceMappedSfgRegressionSingularParameters = 0 := by
  rw [sfgAddDropStageTransfer, Function.comp_apply, sfgAddDropTransfer]
  simp only [SfgParameters.ofAddDrop]
  rw [sourceMappedSfgRegressionSingular_roundTripCoefficient]
  norm_num [sourceMappedSfgRegressionSingularParameters]

/-- Physlib's algebraic drop quotient remains totalized and evaluates to zero at the same point. -/
lemma sourceMappedSfgRegressionSingular_dropTransfer :
    AddDrop.dropTransfer sourceMappedSfgRegressionSingularParameters = 0 := by
  rw [AddDrop.dropTransfer,
    sourceMappedSfgRegressionSingular_arcCoefficients.1,
    sourceMappedSfgRegressionSingular_denominator]
  simp

/-- The displayed nonzero circulation state lies in the raw N5 feedback kernel. -/
lemma sourceMappedSfgRegressionSingular_feedbackKernel :
    (AddDrop.netlist sourceMappedSfgRegressionSingularParameters).feedbackOperator.toLinearMap
        (AddDrop.singularIncident sourceMappedSfgRegressionSingularParameters) = 0 := by
  exact AddDrop.singularIncident_feedbackOperator_eq_zero
    sourceMappedSfgRegressionSingularParameters
    sourceMappedSfgRegressionSingular_denominator

/-- The singular N5 netlist is not well posed, proved from its raw nonzero feedback-kernel
witness rather than the production well-posedness equivalence. -/
lemma sourceMappedSfgRegressionSingular_not_isWellPosed :
    ¬(AddDrop.netlist sourceMappedSfgRegressionSingularParameters).IsWellPosed := by
  rw [FlatNetlist.isWellPosed_iff_feedbackOperator_injective]
  intro hInjective
  apply AddDrop.singularIncident_ne_zero sourceMappedSfgRegressionSingularParameters
  apply hInjective
  rw [sourceMappedSfgRegressionSingular_feedbackKernel, map_zero]

end MicroringCascade

end

end Optics
