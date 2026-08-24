/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.RectangularBehavior

/-!
# Regression tests for rectangular linear optical behaviors

## i. Overview

These examples test algebraic copy, coherent sum, branch selection, and weighted split-combine
behaviors on singleton mode families. Unequal complex branch data distinguish left from right and
direct coefficients from conjugated coefficients. A three-four-five coefficient pair gives a
split followed by combine that is the identity, while the reverse order is a nonidentity
idempotent with a displayed nonzero kernel.

The tests establish component actions directly from membership equations before invoking the
generic composition laws. They also check output uniqueness or reject a plausible wrong output
for the elementary graph behaviors.

## ii. Scope

These are fixed-frequency complex-amplitude regressions. Copy is an explicit algebraic component,
not wire fan-out, a passive splitter, or quantum cloning. Coherent cancellation does not by itself
identify a physical absorption mechanism, and branch selection is not a termination model.

## iii. Table of contents

- A. Singleton and two-branch fixtures
- B. Copy, coherent sum, and selection
- C. Weighted one-sided inverse
- D. Reverse-order idempotent and kernel
- E. Modal-power sentinels

-/

@[expose] public section

namespace Optics

noncomputable section

/-!

## A. Singleton and two-branch fixtures

-/

/-- A singleton-mode amplitude carrying the displayed complex scalar. -/
def rectangularBehaviorRegressionUnitAmplitude (value : ℂ) : ModeAmplitude Unit :=
  WithLp.toLp 2 fun _ => value

/-- The singleton fixture evaluates to its defining scalar. -/
@[simp]
lemma rectangularBehaviorRegressionUnitAmplitude_apply (value : ℂ) :
    rectangularBehaviorRegressionUnitAmplitude value () = value := rfl

/-- A two-branch amplitude with independently displayed singleton coordinates. -/
def rectangularBehaviorRegressionPairAmplitude (left right : ℂ) :
    ModeAmplitude (Unit ⊕ Unit) :=
  (rectangularBehaviorRegressionUnitAmplitude left).directSum
    (rectangularBehaviorRegressionUnitAmplitude right)

/-- The left restriction of a pair fixture is its first singleton amplitude. -/
@[simp]
lemma rectangularBehaviorRegressionPairAmplitude_restrictInl (left right : ℂ) :
    (rectangularBehaviorRegressionPairAmplitude left right).restrictInl =
      rectangularBehaviorRegressionUnitAmplitude left := rfl

/-- The right restriction of a pair fixture is its second singleton amplitude. -/
@[simp]
lemma rectangularBehaviorRegressionPairAmplitude_restrictInr (left right : ℂ) :
    (rectangularBehaviorRegressionPairAmplitude left right).restrictInr =
      rectangularBehaviorRegressionUnitAmplitude right := rfl

/-!

## B. Copy, coherent sum, and selection

-/

/-- The unequal complex amplitude used by the copy regression. -/
def rectangularBehaviorRegressionCopyInput : ModeAmplitude Unit :=
  rectangularBehaviorRegressionUnitAmplitude (2 + Complex.I)

/-- The exact equal-branch output of algebraic copy. -/
def rectangularBehaviorRegressionCopyOutput : ModeAmplitude (Unit ⊕ Unit) :=
  rectangularBehaviorRegressionPairAmplitude (2 + Complex.I) (2 + Complex.I)

/-- A plausible but incorrect copy output with the imaginary part reversed on the right. -/
def rectangularBehaviorRegressionCopyWrongOutput : ModeAmplitude (Unit ⊕ Unit) :=
  rectangularBehaviorRegressionPairAmplitude (2 + Complex.I) (2 - Complex.I)

/-- Algebraic copy produces the exact equal-branch fixture. -/
lemma rectangularBehaviorRegression_copy_mem :
    (rectangularBehaviorRegressionCopyInput, rectangularBehaviorRegressionCopyOutput) ∈
      (LinearBehavior.copy : LinearBehavior Unit (Unit ⊕ Unit)) := by
  rw [LinearBehavior.mem_copy_iff]
  rfl

/-- Every copy output at the regression input equals the exact fixture. -/
lemma rectangularBehaviorRegression_copy_output_eq (candidate : ModeAmplitude (Unit ⊕ Unit))
    (hCandidate : (rectangularBehaviorRegressionCopyInput, candidate) ∈
      (LinearBehavior.copy : LinearBehavior Unit (Unit ⊕ Unit))) :
    candidate = rectangularBehaviorRegressionCopyOutput := by
  rw [LinearBehavior.mem_copy_iff] at hCandidate
  exact hCandidate

/-- The wrong right-branch phase makes the false copy fixture fail membership. -/
lemma rectangularBehaviorRegression_copy_wrong_not_mem :
    (rectangularBehaviorRegressionCopyInput, rectangularBehaviorRegressionCopyWrongOutput) ∉
      (LinearBehavior.copy : LinearBehavior Unit (Unit ⊕ Unit)) := by
  intro hWrong
  have hOutput := rectangularBehaviorRegression_copy_output_eq _ hWrong
  have hRight := congrArg
    (fun amplitude : ModeAmplitude (Unit ⊕ Unit) => amplitude (Sum.inr ())) hOutput
  norm_num [rectangularBehaviorRegressionCopyOutput,
    rectangularBehaviorRegressionCopyWrongOutput,
    rectangularBehaviorRegressionPairAmplitude] at hRight
  have hImag := congrArg Complex.im hRight
  norm_num at hImag

/-- The unequal two-branch input for coherent addition. -/
def rectangularBehaviorRegressionSumInput : ModeAmplitude (Unit ⊕ Unit) :=
  rectangularBehaviorRegressionPairAmplitude (2 + 3 * Complex.I) (-2 + Complex.I)

/-- The exact coherent output of the unequal two-branch input. -/
def rectangularBehaviorRegressionSumOutput : ModeAmplitude Unit :=
  rectangularBehaviorRegressionUnitAmplitude (4 * Complex.I)

/-- A two-branch fixture whose coherent sum cancels exactly. -/
def rectangularBehaviorRegressionCancellationInput : ModeAmplitude (Unit ⊕ Unit) :=
  rectangularBehaviorRegressionPairAmplitude (2 + 3 * Complex.I) (-2 - 3 * Complex.I)

/-- Coherent sum adds complex amplitudes, producing the exact quadrature output. -/
lemma rectangularBehaviorRegression_sum_mem :
    (rectangularBehaviorRegressionSumInput, rectangularBehaviorRegressionSumOutput) ∈
      (LinearBehavior.coherentSum : LinearBehavior (Unit ⊕ Unit) Unit) := by
  rw [LinearBehavior.mem_coherentSum_iff]
  apply WithLp.ofLp_injective 2
  funext mode
  rcases mode with ⟨⟩
  norm_num [rectangularBehaviorRegressionSumInput, rectangularBehaviorRegressionSumOutput,
    rectangularBehaviorRegressionPairAmplitude, rectangularBehaviorRegressionUnitAmplitude]
  ring

/-- Opposite complex branch amplitudes cancel to zero under coherent sum. -/
lemma rectangularBehaviorRegression_cancellation_mem :
    (rectangularBehaviorRegressionCancellationInput, (0 : ModeAmplitude Unit)) ∈
      (LinearBehavior.coherentSum : LinearBehavior (Unit ⊕ Unit) Unit) := by
  rw [LinearBehavior.mem_coherentSum_iff]
  apply WithLp.ofLp_injective 2
  funext mode
  rcases mode with ⟨⟩
  norm_num [rectangularBehaviorRegressionCancellationInput,
    rectangularBehaviorRegressionPairAmplitude, rectangularBehaviorRegressionUnitAmplitude]

/-- A nonzero output cannot satisfy the cancellation input's coherent-sum behavior. -/
lemma rectangularBehaviorRegression_cancellation_nonzero_not_mem :
    (rectangularBehaviorRegressionCancellationInput,
        rectangularBehaviorRegressionUnitAmplitude 1) ∉
      (LinearBehavior.coherentSum : LinearBehavior (Unit ⊕ Unit) Unit) := by
  intro hWrong
  rw [LinearBehavior.mem_coherentSum_iff] at hWrong
  have hUnit := congrArg (fun amplitude : ModeAmplitude Unit => amplitude ()) hWrong
  norm_num [rectangularBehaviorRegressionCancellationInput,
    rectangularBehaviorRegressionPairAmplitude,
    rectangularBehaviorRegressionUnitAmplitude] at hUnit

/-- The unequal complex branch input used to test selector orientation. -/
def rectangularBehaviorRegressionSelectInput : ModeAmplitude (Unit ⊕ Unit) :=
  rectangularBehaviorRegressionPairAmplitude (2 + 3 * Complex.I) (-1 + 4 * Complex.I)

/-- Left selection returns exactly the first complex branch. -/
lemma rectangularBehaviorRegression_selectLeft_mem :
    (rectangularBehaviorRegressionSelectInput,
        rectangularBehaviorRegressionUnitAmplitude (2 + 3 * Complex.I)) ∈
      (LinearBehavior.selectLeft : LinearBehavior (Unit ⊕ Unit) Unit) := by
  simp [rectangularBehaviorRegressionSelectInput]

/-- Right selection returns exactly the second complex branch. -/
lemma rectangularBehaviorRegression_selectRight_mem :
    (rectangularBehaviorRegressionSelectInput,
        rectangularBehaviorRegressionUnitAmplitude (-1 + 4 * Complex.I)) ∈
      (LinearBehavior.selectRight : LinearBehavior (Unit ⊕ Unit) Unit) := by
  simp [rectangularBehaviorRegressionSelectInput]

/-- Left selection rejects the right branch value. -/
lemma rectangularBehaviorRegression_selectLeft_wrong_not_mem :
    (rectangularBehaviorRegressionSelectInput,
        rectangularBehaviorRegressionUnitAmplitude (-1 + 4 * Complex.I)) ∉
      (LinearBehavior.selectLeft : LinearBehavior (Unit ⊕ Unit) Unit) := by
  intro hWrong
  rw [LinearBehavior.mem_selectLeft_iff] at hWrong
  have hUnit := congrArg (fun amplitude : ModeAmplitude Unit => amplitude ()) hWrong
  norm_num [rectangularBehaviorRegressionSelectInput,
    rectangularBehaviorRegressionUnitAmplitude] at hUnit
  have hReal := congrArg Complex.re hUnit
  norm_num at hReal

/-- Right selection rejects the left branch value. -/
lemma rectangularBehaviorRegression_selectRight_wrong_not_mem :
    (rectangularBehaviorRegressionSelectInput,
        rectangularBehaviorRegressionUnitAmplitude (2 + 3 * Complex.I)) ∉
      (LinearBehavior.selectRight : LinearBehavior (Unit ⊕ Unit) Unit) := by
  intro hWrong
  rw [LinearBehavior.mem_selectRight_iff] at hWrong
  have hUnit := congrArg (fun amplitude : ModeAmplitude Unit => amplitude ()) hWrong
  norm_num [rectangularBehaviorRegressionSelectInput,
    rectangularBehaviorRegressionUnitAmplitude] at hUnit
  have hReal := congrArg Complex.re hUnit
  norm_num at hReal

/-!

## C. Weighted one-sided inverse

-/

/-- The left coefficient in the three-four-five regression pair. -/
def rectangularBehaviorRegressionLeftWeight : ℂ := 3 / 5

/-- The right coefficient in the three-four-five regression pair. -/
def rectangularBehaviorRegressionRightWeight : ℂ := 4 / 5

/-- The independent complex input for the weighted split-combine regression. -/
def rectangularBehaviorRegressionWeightedInput : ModeAmplitude Unit :=
  rectangularBehaviorRegressionUnitAmplitude (5 + 5 * Complex.I)

/-- The exact two-branch result of weighted splitting. -/
def rectangularBehaviorRegressionWeightedMiddle : ModeAmplitude (Unit ⊕ Unit) :=
  rectangularBehaviorRegressionPairAmplitude (3 + 3 * Complex.I) (4 + 4 * Complex.I)

/-- Weighted split independently produces the expected three and four branches. -/
lemma rectangularBehaviorRegression_weightedSplit_mem :
    (rectangularBehaviorRegressionWeightedInput,
        rectangularBehaviorRegressionWeightedMiddle) ∈
      LinearBehavior.weightedSplit rectangularBehaviorRegressionLeftWeight
        rectangularBehaviorRegressionRightWeight := by
  rw [LinearBehavior.mem_weightedSplit_iff]
  apply WithLp.ofLp_injective 2
  funext mode
  rcases mode with mode | mode
  · rcases mode with ⟨⟩
    norm_num [rectangularBehaviorRegressionWeightedInput,
      rectangularBehaviorRegressionWeightedMiddle,
      rectangularBehaviorRegressionLeftWeight,
      rectangularBehaviorRegressionPairAmplitude,
      rectangularBehaviorRegressionUnitAmplitude]
    ring
  · rcases mode with ⟨⟩
    norm_num [rectangularBehaviorRegressionWeightedInput,
      rectangularBehaviorRegressionWeightedMiddle,
      rectangularBehaviorRegressionRightWeight,
      rectangularBehaviorRegressionPairAmplitude,
      rectangularBehaviorRegressionUnitAmplitude]
    ring

/-- Weighted combine independently reconstructs the original complex input. -/
lemma rectangularBehaviorRegression_weightedCombine_mem :
    (rectangularBehaviorRegressionWeightedMiddle,
        rectangularBehaviorRegressionWeightedInput) ∈
      LinearBehavior.weightedCombine rectangularBehaviorRegressionLeftWeight
        rectangularBehaviorRegressionRightWeight := by
  rw [LinearBehavior.mem_weightedCombine_iff]
  apply WithLp.ofLp_injective 2
  funext mode
  rcases mode with ⟨⟩
  norm_num [rectangularBehaviorRegressionWeightedInput,
    rectangularBehaviorRegressionWeightedMiddle,
    rectangularBehaviorRegressionLeftWeight, rectangularBehaviorRegressionRightWeight,
    rectangularBehaviorRegressionPairAmplitude,
    rectangularBehaviorRegressionUnitAmplitude]
  ring

/-- A complex input that detects conjugation of a weighted-split coefficient. -/
def rectangularBehaviorRegressionPhaseSplitInput : ModeAmplitude Unit :=
  rectangularBehaviorRegressionUnitAmplitude (1 + Complex.I)

/-- The direct, unconjugated weighted-split output for weights two and `I`. -/
def rectangularBehaviorRegressionPhaseSplitOutput : ModeAmplitude (Unit ⊕ Unit) :=
  rectangularBehaviorRegressionPairAmplitude (2 + 2 * Complex.I) (-1 + Complex.I)

/-- The false split output obtained by conjugating the second coefficient. -/
def rectangularBehaviorRegressionPhaseSplitWrongOutput : ModeAmplitude (Unit ⊕ Unit) :=
  rectangularBehaviorRegressionPairAmplitude (2 + 2 * Complex.I) (1 - Complex.I)

/-- Complex weighted split uses its displayed coefficients without implicit conjugation. -/
lemma rectangularBehaviorRegression_phase_split_mem :
    (rectangularBehaviorRegressionPhaseSplitInput,
        rectangularBehaviorRegressionPhaseSplitOutput) ∈
      LinearBehavior.weightedSplit 2 Complex.I := by
  rw [LinearBehavior.mem_weightedSplit_iff]
  apply WithLp.ofLp_injective 2
  funext mode
  rcases mode with mode | mode
  · rcases mode with ⟨⟩
    norm_num [rectangularBehaviorRegressionPhaseSplitInput,
      rectangularBehaviorRegressionPhaseSplitOutput,
      rectangularBehaviorRegressionPairAmplitude,
      rectangularBehaviorRegressionUnitAmplitude]
    ring
  · rcases mode with ⟨⟩
    norm_num [rectangularBehaviorRegressionPhaseSplitInput,
      rectangularBehaviorRegressionPhaseSplitOutput,
      rectangularBehaviorRegressionPairAmplitude,
      rectangularBehaviorRegressionUnitAmplitude]
    apply Complex.ext <;> norm_num

/-- The output from conjugating the second coefficient does not satisfy direct weighted split. -/
lemma rectangularBehaviorRegression_phase_split_conjugated_not_mem :
    (rectangularBehaviorRegressionPhaseSplitInput,
        rectangularBehaviorRegressionPhaseSplitWrongOutput) ∉
      LinearBehavior.weightedSplit 2 Complex.I := by
  intro hWrong
  rw [LinearBehavior.mem_weightedSplit_iff] at hWrong
  have hRight := congrArg
    (fun amplitude : ModeAmplitude (Unit ⊕ Unit) => amplitude (Sum.inr ())) hWrong
  norm_num [rectangularBehaviorRegressionPhaseSplitInput,
    rectangularBehaviorRegressionPhaseSplitWrongOutput,
    rectangularBehaviorRegressionPairAmplitude,
    rectangularBehaviorRegressionUnitAmplitude] at hRight
  have hReal := congrArg Complex.re hRight
  norm_num at hReal

/-- An unequal complex two-branch input that detects coefficient conjugation mistakes. -/
def rectangularBehaviorRegressionPhaseCombineInput : ModeAmplitude (Unit ⊕ Unit) :=
  rectangularBehaviorRegressionPairAmplitude (1 + Complex.I) (2 - Complex.I)

/-- The direct, unconjugated result for weights two and `I`. -/
def rectangularBehaviorRegressionPhaseCombineOutput : ModeAmplitude Unit :=
  rectangularBehaviorRegressionUnitAmplitude (3 + 4 * Complex.I)

/-- Complex weighted combine uses its displayed coefficients without implicit conjugation. -/
lemma rectangularBehaviorRegression_phase_combine_mem :
    (rectangularBehaviorRegressionPhaseCombineInput,
        rectangularBehaviorRegressionPhaseCombineOutput) ∈
      LinearBehavior.weightedCombine 2 Complex.I := by
  rw [LinearBehavior.mem_weightedCombine_iff]
  apply WithLp.ofLp_injective 2
  funext mode
  rcases mode with ⟨⟩
  norm_num [rectangularBehaviorRegressionPhaseCombineInput,
    rectangularBehaviorRegressionPhaseCombineOutput,
    rectangularBehaviorRegressionPairAmplitude,
    rectangularBehaviorRegressionUnitAmplitude]
  apply Complex.ext <;> norm_num

/-- The value obtained by conjugating the second coefficient does not satisfy direct weighted
combine. -/
lemma rectangularBehaviorRegression_phase_combine_conjugated_not_mem :
    (rectangularBehaviorRegressionPhaseCombineInput,
        rectangularBehaviorRegressionUnitAmplitude 1) ∉
      LinearBehavior.weightedCombine 2 Complex.I := by
  intro hWrong
  rw [LinearBehavior.mem_weightedCombine_iff] at hWrong
  have hUnit := congrArg (fun amplitude : ModeAmplitude Unit => amplitude ()) hWrong
  norm_num [rectangularBehaviorRegressionPhaseCombineInput,
    rectangularBehaviorRegressionPairAmplitude,
    rectangularBehaviorRegressionUnitAmplitude] at hUnit
  have hReal := congrArg Complex.re hUnit
  norm_num at hReal

/-- The complete three-four-five split-then-combine behavior is the identity. -/
lemma rectangularBehaviorRegression_split_combine_eq_identity :
    (LinearBehavior.weightedSplit rectangularBehaviorRegressionLeftWeight
        rectangularBehaviorRegressionRightWeight).series
      (LinearBehavior.weightedCombine rectangularBehaviorRegressionLeftWeight
        rectangularBehaviorRegressionRightWeight) =
      (LinearBehavior.identity : LinearBehavior Unit Unit) := by
  apply LinearBehavior.weightedSplit_series_weightedCombine_eq_identity
  norm_num [rectangularBehaviorRegressionLeftWeight,
    rectangularBehaviorRegressionRightWeight]

/-!

## D. Reverse-order idempotent and kernel

-/

/-- Weighted combine followed by weighted split in the reverse of the identity order. -/
def rectangularBehaviorRegressionProjector :
    LinearBehavior (Unit ⊕ Unit) (Unit ⊕ Unit) :=
  (LinearBehavior.weightedCombine rectangularBehaviorRegressionLeftWeight
    rectangularBehaviorRegressionRightWeight).series
  (LinearBehavior.weightedSplit rectangularBehaviorRegressionLeftWeight
    rectangularBehaviorRegressionRightWeight)

/-- A two-branch input that the reverse-order behavior changes. -/
def rectangularBehaviorRegressionProjectorInput : ModeAmplitude (Unit ⊕ Unit) :=
  rectangularBehaviorRegressionPairAmplitude 5 0

/-- The singleton intermediate obtained by combining the changed input. -/
def rectangularBehaviorRegressionProjectorMiddle : ModeAmplitude Unit :=
  rectangularBehaviorRegressionUnitAmplitude 3

/-- The exact changed output of the reverse-order behavior. -/
def rectangularBehaviorRegressionProjectorOutput : ModeAmplitude (Unit ⊕ Unit) :=
  rectangularBehaviorRegressionPairAmplitude (9 / 5) (12 / 5)

/-- Combining the changed input produces exactly the singleton value three. -/
lemma rectangularBehaviorRegression_projector_combine_mem :
    (rectangularBehaviorRegressionProjectorInput,
        rectangularBehaviorRegressionProjectorMiddle) ∈
      LinearBehavior.weightedCombine rectangularBehaviorRegressionLeftWeight
        rectangularBehaviorRegressionRightWeight := by
  rw [LinearBehavior.mem_weightedCombine_iff]
  apply WithLp.ofLp_injective 2
  funext mode
  rcases mode with ⟨⟩
  norm_num [rectangularBehaviorRegressionProjectorInput,
    rectangularBehaviorRegressionProjectorMiddle,
    rectangularBehaviorRegressionLeftWeight, rectangularBehaviorRegressionRightWeight,
    rectangularBehaviorRegressionPairAmplitude,
    rectangularBehaviorRegressionUnitAmplitude]

/-- Splitting the singleton value three produces the exact reverse-order output. -/
lemma rectangularBehaviorRegression_projector_split_mem :
    (rectangularBehaviorRegressionProjectorMiddle,
        rectangularBehaviorRegressionProjectorOutput) ∈
      LinearBehavior.weightedSplit rectangularBehaviorRegressionLeftWeight
        rectangularBehaviorRegressionRightWeight := by
  rw [LinearBehavior.mem_weightedSplit_iff]
  apply WithLp.ofLp_injective 2
  funext mode
  rcases mode with mode | mode
  · rcases mode with ⟨⟩
    norm_num [rectangularBehaviorRegressionProjectorMiddle,
      rectangularBehaviorRegressionProjectorOutput,
      rectangularBehaviorRegressionLeftWeight,
      rectangularBehaviorRegressionPairAmplitude,
      rectangularBehaviorRegressionUnitAmplitude]
  · rcases mode with ⟨⟩
    norm_num [rectangularBehaviorRegressionProjectorMiddle,
      rectangularBehaviorRegressionProjectorOutput,
      rectangularBehaviorRegressionRightWeight,
      rectangularBehaviorRegressionPairAmplitude,
      rectangularBehaviorRegressionUnitAmplitude]

/-- The reverse-order behavior maps the displayed input to a different exact output. -/
lemma rectangularBehaviorRegression_projector_mem :
    (rectangularBehaviorRegressionProjectorInput,
        rectangularBehaviorRegressionProjectorOutput) ∈
      rectangularBehaviorRegressionProjector := by
  exact ⟨rectangularBehaviorRegressionProjectorMiddle,
    rectangularBehaviorRegression_projector_combine_mem,
    rectangularBehaviorRegression_projector_split_mem⟩

/-- The displayed reverse-order output differs from its input. -/
lemma rectangularBehaviorRegression_projector_output_ne_input :
    rectangularBehaviorRegressionProjectorOutput ≠
      rectangularBehaviorRegressionProjectorInput := by
  intro hOutput
  have hLeft := congrArg
    (fun amplitude : ModeAmplitude (Unit ⊕ Unit) => amplitude (Sum.inl ())) hOutput
  norm_num [rectangularBehaviorRegressionProjectorOutput,
    rectangularBehaviorRegressionProjectorInput,
    rectangularBehaviorRegressionPairAmplitude] at hLeft

/-- The reverse-order behavior is not the identity behavior. -/
lemma rectangularBehaviorRegression_projector_ne_identity :
    rectangularBehaviorRegressionProjector ≠
      (LinearBehavior.identity : LinearBehavior (Unit ⊕ Unit) (Unit ⊕ Unit)) := by
  intro hBehavior
  have hMember := rectangularBehaviorRegression_projector_mem
  rw [hBehavior, LinearBehavior.mem_identity_iff] at hMember
  exact rectangularBehaviorRegression_projector_output_ne_input hMember

/-- The exact reverse-order output is a fixed point of the same behavior. -/
lemma rectangularBehaviorRegression_projector_output_mem :
    (rectangularBehaviorRegressionProjectorOutput,
        rectangularBehaviorRegressionProjectorOutput) ∈
      rectangularBehaviorRegressionProjector := by
  refine ⟨rectangularBehaviorRegressionProjectorMiddle, ?_,
    rectangularBehaviorRegression_projector_split_mem⟩
  rw [LinearBehavior.mem_weightedCombine_iff]
  apply WithLp.ofLp_injective 2
  funext mode
  rcases mode with ⟨⟩
  norm_num [rectangularBehaviorRegressionProjectorOutput,
    rectangularBehaviorRegressionProjectorMiddle,
    rectangularBehaviorRegressionLeftWeight, rectangularBehaviorRegressionRightWeight,
    rectangularBehaviorRegressionPairAmplitude,
    rectangularBehaviorRegressionUnitAmplitude]

/-- The concrete reverse-order behavior is idempotent. -/
lemma rectangularBehaviorRegression_projector_idempotent :
    rectangularBehaviorRegressionProjector.series rectangularBehaviorRegressionProjector =
      rectangularBehaviorRegressionProjector := by
  apply LinearBehavior.weightedCombine_series_weightedSplit_idempotent
  norm_num [rectangularBehaviorRegressionLeftWeight,
    rectangularBehaviorRegressionRightWeight]

/-- A nonzero two-branch input in the weighted-combine kernel. -/
def rectangularBehaviorRegressionKernelInput : ModeAmplitude (Unit ⊕ Unit) :=
  rectangularBehaviorRegressionPairAmplitude 4 (-3)

/-- The displayed kernel input is nonzero. -/
lemma rectangularBehaviorRegressionKernelInput_ne_zero :
    rectangularBehaviorRegressionKernelInput ≠ 0 := by
  intro hInput
  have hLeft := congrArg
    (fun amplitude : ModeAmplitude (Unit ⊕ Unit) => amplitude (Sum.inl ())) hInput
  norm_num [rectangularBehaviorRegressionKernelInput,
    rectangularBehaviorRegressionPairAmplitude] at hLeft

/-- Weighted combine maps the displayed nonzero kernel input to zero. -/
lemma rectangularBehaviorRegression_kernel_combine_mem :
    (rectangularBehaviorRegressionKernelInput, (0 : ModeAmplitude Unit)) ∈
      LinearBehavior.weightedCombine rectangularBehaviorRegressionLeftWeight
        rectangularBehaviorRegressionRightWeight := by
  rw [LinearBehavior.mem_weightedCombine_iff]
  apply WithLp.ofLp_injective 2
  funext mode
  rcases mode with ⟨⟩
  norm_num [rectangularBehaviorRegressionKernelInput,
    rectangularBehaviorRegressionLeftWeight, rectangularBehaviorRegressionRightWeight,
    rectangularBehaviorRegressionPairAmplitude,
    rectangularBehaviorRegressionUnitAmplitude]

/-- The reverse-order behavior maps the displayed nonzero kernel input to zero. -/
lemma rectangularBehaviorRegression_kernel_projector_mem :
    (rectangularBehaviorRegressionKernelInput, (0 : ModeAmplitude (Unit ⊕ Unit))) ∈
      rectangularBehaviorRegressionProjector := by
  exact ⟨0, rectangularBehaviorRegression_kernel_combine_mem,
    (LinearBehavior.weightedSplit rectangularBehaviorRegressionLeftWeight
      rectangularBehaviorRegressionRightWeight).zero_mem⟩

/-!

## E. Modal-power sentinels

-/

/-- The modal power of a singleton fixture is the squared modulus of its scalar. -/
lemma rectangularBehaviorRegressionUnitAmplitude_power (value : ℂ) :
    (rectangularBehaviorRegressionUnitAmplitude value).power = Complex.normSq value := by
  rw [ModeAmplitude.power_eq_sum_normSq]
  simp [rectangularBehaviorRegressionUnitAmplitude]

/-- The modal power of a pair fixture is the sum of the two scalar squared moduli. -/
lemma rectangularBehaviorRegressionPairAmplitude_power (left right : ℂ) :
    (rectangularBehaviorRegressionPairAmplitude left right).power =
      Complex.normSq left + Complex.normSq right := by
  rw [rectangularBehaviorRegressionPairAmplitude, ModeAmplitude.power_directSum,
    rectangularBehaviorRegressionUnitAmplitude_power,
    rectangularBehaviorRegressionUnitAmplitude_power]

/-- The unequal complex copy input has modal power five. -/
lemma rectangularBehaviorRegression_copy_input_power :
    rectangularBehaviorRegressionCopyInput.power = 5 := by
  rw [rectangularBehaviorRegressionCopyInput,
    rectangularBehaviorRegressionUnitAmplitude_power]
  norm_num [Complex.normSq_apply]

/-- Algebraic copy sends input power five to output power ten. -/
lemma rectangularBehaviorRegression_copy_output_power :
    rectangularBehaviorRegressionCopyOutput.power = 10 := by
  rw [rectangularBehaviorRegressionCopyOutput,
    rectangularBehaviorRegressionPairAmplitude_power]
  norm_num [Complex.normSq_apply]

/-- The weighted complex regression input has modal power fifty. -/
lemma rectangularBehaviorRegression_weighted_input_power :
    rectangularBehaviorRegressionWeightedInput.power = 50 := by
  rw [rectangularBehaviorRegressionWeightedInput,
    rectangularBehaviorRegressionUnitAmplitude_power]
  norm_num [Complex.normSq_apply]

/-- The normalized three-four-five split preserves the concrete input's modal power. -/
lemma rectangularBehaviorRegression_weighted_middle_power :
    rectangularBehaviorRegressionWeightedMiddle.power =
      rectangularBehaviorRegressionWeightedInput.power := by
  rw [rectangularBehaviorRegressionWeightedMiddle,
    rectangularBehaviorRegressionPairAmplitude_power,
    rectangularBehaviorRegression_weighted_input_power]
  norm_num [Complex.normSq_apply]

/-- Equal singleton branches used to test coherent-sum enhancement. -/
def rectangularBehaviorRegressionEqualSumInput : ModeAmplitude (Unit ⊕ Unit) :=
  rectangularBehaviorRegressionPairAmplitude 1 1

/-- The exact doubled amplitude produced by equal coherent branches. -/
def rectangularBehaviorRegressionEqualSumOutput : ModeAmplitude Unit :=
  rectangularBehaviorRegressionUnitAmplitude 2

/-- Equal branches add coherently to amplitude two. -/
lemma rectangularBehaviorRegression_equal_sum_mem :
    (rectangularBehaviorRegressionEqualSumInput,
        rectangularBehaviorRegressionEqualSumOutput) ∈
      (LinearBehavior.coherentSum : LinearBehavior (Unit ⊕ Unit) Unit) := by
  rw [LinearBehavior.mem_coherentSum_iff]
  apply WithLp.ofLp_injective 2
  funext mode
  rcases mode with ⟨⟩
  norm_num [rectangularBehaviorRegressionEqualSumInput,
    rectangularBehaviorRegressionEqualSumOutput,
    rectangularBehaviorRegressionPairAmplitude,
    rectangularBehaviorRegressionUnitAmplitude]

/-- The two equal input branches have total modal power two. -/
lemma rectangularBehaviorRegression_equal_sum_input_power :
    rectangularBehaviorRegressionEqualSumInput.power = 2 := by
  rw [rectangularBehaviorRegressionEqualSumInput,
    rectangularBehaviorRegressionPairAmplitude_power]
  norm_num

/-- Coherent addition of equal branches produces output modal power four. -/
lemma rectangularBehaviorRegression_equal_sum_output_power :
    rectangularBehaviorRegressionEqualSumOutput.power = 4 := by
  rw [rectangularBehaviorRegressionEqualSumOutput,
    rectangularBehaviorRegressionUnitAmplitude_power]
  norm_num

/-- The displayed cancellation input has nonzero modal power twenty-six. -/
lemma rectangularBehaviorRegression_cancellation_input_power :
    rectangularBehaviorRegressionCancellationInput.power = 26 := by
  rw [rectangularBehaviorRegressionCancellationInput,
    rectangularBehaviorRegressionPairAmplitude_power]
  norm_num [Complex.normSq_apply]

end

end Optics
