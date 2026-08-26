/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.LinearBehavior

/-!
# Regression tests for implicit linear optical behaviors

## i. Overview

These examples distinguish relational optical behaviors from ordinary linear maps and check the
orientation of series and parallel composition. Two nonsymmetric transforms act on an independent
complex input, so reversing their order changes the exact output. A separate behavior permits
multiple outputs for one input and therefore cannot be the graph of any linear map.

The parallel example uses gain two, gain three, and complex branch amplitudes. It checks that
parallel composition leaves the two branches independent: it does not duplicate or sum an input,
and it does not swap the branches.

## ii. Key results

## iii. Table of contents

- A. A nonsymmetric series cascade
- B. Singular and multivalued behaviors
- C. Independent parallel branches

## iv. References

These are algebraic, fixed-frequency regressions. Their amplitudes are not electromagnetic field
solutions, and no passivity, losslessness, causality, or physical realization is stated.

-/

@[expose] public section

namespace Optics

noncomputable section

/-!

## A. A nonsymmetric series cascade

-/

/-- A two-mode amplitude with independently specified coordinates. -/
def linearBehaviorRegressionBoolAmplitude (falseValue trueValue : ℂ) : ModeAmplitude Bool :=
  WithLp.toLp 2 fun
    | false => falseValue
    | true => trueValue

/-- The false coordinate of the regression amplitude is its first argument. -/
@[simp]
lemma linearBehaviorRegressionBoolAmplitude_false (falseValue trueValue : ℂ) :
    linearBehaviorRegressionBoolAmplitude falseValue trueValue false = falseValue := rfl

/-- The true coordinate of the regression amplitude is its second argument. -/
@[simp]
lemma linearBehaviorRegressionBoolAmplitude_true (falseValue trueValue : ℂ) :
    linearBehaviorRegressionBoolAmplitude falseValue trueValue true = trueValue := rfl

/-- The first nonsymmetric transform in the regression cascade. -/
def linearBehaviorRegressionFirst : ModeTransform Bool Bool
  | false, false => 1
  | false, true => 2
  | true, false => 0
  | true, true => 1

/-- The second nonsymmetric transform in the regression cascade. -/
def linearBehaviorRegressionSecond : ModeTransform Bool Bool
  | false, false => 1
  | false, true => 0
  | true, false => 3
  | true, true => 1

/-- The independent complex input to the regression cascade. -/
def linearBehaviorRegressionInput : ModeAmplitude Bool :=
  linearBehaviorRegressionBoolAmplitude 1 Complex.I

/-- The exact intermediate amplitude after the first transform. -/
def linearBehaviorRegressionMiddle : ModeAmplitude Bool :=
  linearBehaviorRegressionBoolAmplitude (1 + 2 * Complex.I) Complex.I

/-- The exact output when the first transform acts before the second. -/
def linearBehaviorRegressionOutput : ModeAmplitude Bool :=
  linearBehaviorRegressionBoolAmplitude (1 + 2 * Complex.I) (3 + 7 * Complex.I)

/-- The intermediate amplitude obtained by applying the second transform first. -/
def linearBehaviorRegressionReverseMiddle : ModeAmplitude Bool :=
  linearBehaviorRegressionBoolAmplitude 1 (3 + Complex.I)

/-- The distinct output obtained by reversing the transform order. -/
def linearBehaviorRegressionReverseOutput : ModeAmplitude Bool :=
  linearBehaviorRegressionBoolAmplitude (7 + 2 * Complex.I) (3 + Complex.I)

/-- The first transform produces the stated intermediate amplitude. -/
lemma linearBehaviorRegression_first_action :
    linearBehaviorRegressionFirst.toLinearMap linearBehaviorRegressionInput =
      linearBehaviorRegressionMiddle := by
  apply WithLp.ofLp_injective 2
  funext mode
  cases mode <;>
    norm_num [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
      linearBehaviorRegressionFirst, linearBehaviorRegressionInput,
      linearBehaviorRegressionMiddle, linearBehaviorRegressionBoolAmplitude,
      Fintype.sum_bool]
  all_goals ring

/-- The second transform maps the intermediate amplitude to the stated cascade output. -/
lemma linearBehaviorRegression_second_action :
    linearBehaviorRegressionSecond.toLinearMap linearBehaviorRegressionMiddle =
      linearBehaviorRegressionOutput := by
  apply WithLp.ofLp_injective 2
  funext mode
  cases mode <;>
    norm_num [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
      linearBehaviorRegressionSecond, linearBehaviorRegressionMiddle,
      linearBehaviorRegressionOutput, linearBehaviorRegressionBoolAmplitude,
      Fintype.sum_bool]
  ring

/-- Applying the second transform first produces the reverse intermediate amplitude. -/
lemma linearBehaviorRegression_second_first_action :
    linearBehaviorRegressionSecond.toLinearMap linearBehaviorRegressionInput =
      linearBehaviorRegressionReverseMiddle := by
  apply WithLp.ofLp_injective 2
  funext mode
  cases mode <;>
    norm_num [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
      linearBehaviorRegressionSecond, linearBehaviorRegressionInput,
      linearBehaviorRegressionReverseMiddle, linearBehaviorRegressionBoolAmplitude,
      Fintype.sum_bool]
  all_goals ring

/-- Applying the first transform second produces the reverse-order output. -/
lemma linearBehaviorRegression_first_second_action :
    linearBehaviorRegressionFirst.toLinearMap linearBehaviorRegressionReverseMiddle =
      linearBehaviorRegressionReverseOutput := by
  apply WithLp.ofLp_injective 2
  funext mode
  cases mode <;>
    norm_num [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
      linearBehaviorRegressionFirst, linearBehaviorRegressionReverseMiddle,
      linearBehaviorRegressionReverseOutput, linearBehaviorRegressionBoolAmplitude,
      Fintype.sum_bool]
  ring

/-- The forward cascade output is not equal to the reverse cascade output. -/
lemma linearBehaviorRegression_output_ne_reverseOutput :
    linearBehaviorRegressionOutput ≠ linearBehaviorRegressionReverseOutput := by
  intro hOutput
  have hTrue := congrArg (fun amplitude : ModeAmplitude Bool => amplitude true) hOutput
  norm_num [linearBehaviorRegressionOutput, linearBehaviorRegressionReverseOutput,
    linearBehaviorRegressionBoolAmplitude] at hTrue

/-- The concrete intermediate pair is in the first transform's graph behavior. -/
lemma linearBehaviorRegression_first_graph :
    (linearBehaviorRegressionInput, linearBehaviorRegressionMiddle) ∈
      linearBehaviorRegressionFirst.toBehavior := by
  change linearBehaviorRegressionMiddle =
    linearBehaviorRegressionFirst.toLinearMap linearBehaviorRegressionInput
  exact linearBehaviorRegression_first_action.symm

/-- The concrete output pair is in the second transform's graph behavior. -/
lemma linearBehaviorRegression_second_graph :
    (linearBehaviorRegressionMiddle, linearBehaviorRegressionOutput) ∈
      linearBehaviorRegressionSecond.toBehavior := by
  change linearBehaviorRegressionOutput =
    linearBehaviorRegressionSecond.toLinearMap linearBehaviorRegressionMiddle
  exact linearBehaviorRegression_second_action.symm

/-- The exact input and output satisfy the relational series composition. -/
lemma linearBehaviorRegression_series_mem :
    (linearBehaviorRegressionInput, linearBehaviorRegressionOutput) ∈
      linearBehaviorRegressionFirst.toBehavior.series
        linearBehaviorRegressionSecond.toBehavior := by
  exact ⟨linearBehaviorRegressionMiddle, linearBehaviorRegression_first_graph,
    linearBehaviorRegression_second_graph⟩

/-- The concrete series behavior has a unique output at the regression input. -/
lemma linearBehaviorRegression_series_output_eq (candidate : ModeAmplitude Bool)
    (hCandidate : (linearBehaviorRegressionInput, candidate) ∈
      linearBehaviorRegressionFirst.toBehavior.series
        linearBehaviorRegressionSecond.toBehavior) :
    candidate = linearBehaviorRegressionOutput := by
  rcases hCandidate with ⟨middle, hFirst, hSecond⟩
  change middle =
    linearBehaviorRegressionFirst.toLinearMap linearBehaviorRegressionInput at hFirst
  change candidate = linearBehaviorRegressionSecond.toLinearMap middle at hSecond
  calc
    candidate = linearBehaviorRegressionSecond.toLinearMap middle := hSecond
    _ = linearBehaviorRegressionSecond.toLinearMap linearBehaviorRegressionMiddle := by
      rw [hFirst, linearBehaviorRegression_first_action]
    _ = linearBehaviorRegressionOutput := linearBehaviorRegression_second_action

/-- The reverse-order output does not satisfy the forward series behavior. -/
lemma linearBehaviorRegression_reverseOutput_not_mem_series :
    (linearBehaviorRegressionInput, linearBehaviorRegressionReverseOutput) ∉
      linearBehaviorRegressionFirst.toBehavior.series
        linearBehaviorRegressionSecond.toBehavior := by
  intro hReverse
  exact linearBehaviorRegression_output_ne_reverseOutput
    (linearBehaviorRegression_series_output_eq _ hReverse).symm

/-- The product matrix independently produces the exact forward-cascade output. -/
lemma linearBehaviorRegression_mul_action :
    ModeTransform.toLinearMap
        (linearBehaviorRegressionSecond * linearBehaviorRegressionFirst)
      linearBehaviorRegressionInput = linearBehaviorRegressionOutput := by
  simpa only [ModeTransform.toLinearMap, Matrix.toLpLin_mul_same, LinearMap.comp_apply,
    linearBehaviorRegression_first_action] using linearBehaviorRegression_second_action

/-- The independently checked matrix product is in its graph behavior. -/
lemma linearBehaviorRegression_mul_graph :
    (linearBehaviorRegressionInput, linearBehaviorRegressionOutput) ∈
      ModeTransform.toBehavior
        (linearBehaviorRegressionSecond * linearBehaviorRegressionFirst) := by
  rw [ModeTransform.mem_toBehavior_iff_toLinearMap]
  exact linearBehaviorRegression_mul_action.symm

/-- The concrete relational cascade equals the product-transform graph as a whole behavior. -/
lemma linearBehaviorRegression_series_eq_mul :
    linearBehaviorRegressionFirst.toBehavior.series
        linearBehaviorRegressionSecond.toBehavior =
      ModeTransform.toBehavior
        (linearBehaviorRegressionSecond * linearBehaviorRegressionFirst) :=
  ModeTransform.toBehavior_mul _ _

/-!

## B. Singular and multivalued behaviors

-/

/-- A nonzero regression amplitude on the singleton mode family. -/
def linearBehaviorRegressionUnitPulse : ModeAmplitude Unit :=
  WithLp.toLp 2 fun _ => 1

/-- The singleton regression amplitude is nonzero. -/
lemma linearBehaviorRegressionUnitPulse_ne_zero :
    linearBehaviorRegressionUnitPulse ≠ 0 := by
  intro hPulse
  have hUnit := congrArg (fun amplitude : ModeAmplitude Unit => amplitude ()) hPulse
  norm_num [linearBehaviorRegressionUnitPulse] at hUnit

/-- The singular zero transform on the singleton mode family. -/
def linearBehaviorRegressionZeroTransform : ModeTransform Unit Unit :=
  0

/-- The zero transform maps the nonzero singleton amplitude to zero. -/
lemma linearBehaviorRegressionZeroTransform_pulse :
    linearBehaviorRegressionZeroTransform.toLinearMap
        linearBehaviorRegressionUnitPulse = 0 := by
  simp [linearBehaviorRegressionZeroTransform]

/-- A singular transform still induces a total, single-valued graph behavior. -/
lemma linearBehaviorRegressionZeroTransform_graph :
    (linearBehaviorRegressionUnitPulse, (0 : ModeAmplitude Unit)) ∈
      linearBehaviorRegressionZeroTransform.toBehavior := by
  rw [ModeTransform.mem_toBehavior_iff_toLinearMap]
  exact linearBehaviorRegressionZeroTransform_pulse.symm

/-- The zero transform's bundled linear map is not injective. -/
lemma linearBehaviorRegressionZeroTransform_not_injective :
    ¬Function.Injective linearBehaviorRegressionZeroTransform.toLinearMap := by
  intro hInjective
  apply linearBehaviorRegressionUnitPulse_ne_zero
  apply hInjective
  simp [linearBehaviorRegressionZeroTransform]

/-- A linear behavior that requires zero input and permits every output. -/
def linearBehaviorRegressionFreeOutput : LinearBehavior Unit Unit :=
  (⊥ : Submodule ℂ (ModeAmplitude Unit)).prod ⊤

/-- Zero input and zero output satisfy the free-output behavior. -/
lemma linearBehaviorRegressionFreeOutput_zero_zero :
    ((0 : ModeAmplitude Unit), (0 : ModeAmplitude Unit)) ∈
      linearBehaviorRegressionFreeOutput := by
  simp [linearBehaviorRegressionFreeOutput]

/-- Zero input and a nonzero singleton output both satisfy the free-output behavior. -/
lemma linearBehaviorRegressionFreeOutput_zero_pulse :
    ((0 : ModeAmplitude Unit), linearBehaviorRegressionUnitPulse) ∈
      linearBehaviorRegressionFreeOutput := by
  simp [linearBehaviorRegressionFreeOutput]

/-- The free-output behavior cannot be the graph of any complex-linear map. -/
lemma linearBehaviorRegressionFreeOutput_ne_ofLinearMap
    (map : ModeAmplitude Unit →ₗ[ℂ] ModeAmplitude Unit) :
    linearBehaviorRegressionFreeOutput ≠ LinearBehavior.ofLinearMap map := by
  intro hBehavior
  have hMember : ((0 : ModeAmplitude Unit), linearBehaviorRegressionUnitPulse) ∈
      LinearBehavior.ofLinearMap map := by
    rw [← hBehavior]
    exact linearBehaviorRegressionFreeOutput_zero_pulse
  rw [LinearBehavior.mem_ofLinearMap_iff, map_zero] at hMember
  exact linearBehaviorRegressionUnitPulse_ne_zero hMember

/-!

## C. Independent parallel branches

-/

/-- A scalar amplitude on the singleton mode family. -/
def linearBehaviorRegressionUnitAmplitude (value : ℂ) : ModeAmplitude Unit :=
  WithLp.toLp 2 fun _ => value

/-- A scalar-gain transform on the singleton mode family. -/
def linearBehaviorRegressionGain (gain : ℂ) : ModeTransform Unit Unit :=
  fun _ _ => gain

/-- A singleton scalar-gain transform multiplies its amplitude by the gain. -/
lemma linearBehaviorRegressionGain_action (gain value : ℂ) :
    (linearBehaviorRegressionGain gain).toLinearMap
        (linearBehaviorRegressionUnitAmplitude value) =
      linearBehaviorRegressionUnitAmplitude (gain * value) := by
  apply WithLp.ofLp_injective 2
  funext mode
  rcases mode with ⟨⟩
  simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    linearBehaviorRegressionGain, linearBehaviorRegressionUnitAmplitude]

/-- The two independent input branches carry amplitudes one and `I`. -/
def linearBehaviorRegressionParallelInput : ModeAmplitude (Unit ⊕ Unit) :=
  (linearBehaviorRegressionUnitAmplitude 1).directSum
    (linearBehaviorRegressionUnitAmplitude Complex.I)

/-- Gain two and gain three produce independent outputs two and `3I`. -/
def linearBehaviorRegressionParallelOutput : ModeAmplitude (Unit ⊕ Unit) :=
  (linearBehaviorRegressionUnitAmplitude 2).directSum
    (linearBehaviorRegressionUnitAmplitude (3 * Complex.I))

/-- A false output retaining gain two on the right branch. -/
def linearBehaviorRegressionParallelWrongOutput : ModeAmplitude (Unit ⊕ Unit) :=
  (linearBehaviorRegressionUnitAmplitude 2).directSum
    (linearBehaviorRegressionUnitAmplitude (2 * Complex.I))

/-- The concrete two-branch amplitudes satisfy relational parallel composition. -/
lemma linearBehaviorRegression_parallel_mem :
    (linearBehaviorRegressionParallelInput, linearBehaviorRegressionParallelOutput) ∈
      (linearBehaviorRegressionGain 2).toBehavior.parallel
        (linearBehaviorRegressionGain 3).toBehavior := by
  rw [LinearBehavior.mem_parallel_iff]
  constructor
  · change linearBehaviorRegressionUnitAmplitude 2 =
      (linearBehaviorRegressionGain 2).toLinearMap
        (linearBehaviorRegressionUnitAmplitude 1)
    simpa using (linearBehaviorRegressionGain_action (2 : ℂ) 1).symm
  · change linearBehaviorRegressionUnitAmplitude (3 * Complex.I) =
      (linearBehaviorRegressionGain 3).toLinearMap
        (linearBehaviorRegressionUnitAmplitude Complex.I)
    exact (linearBehaviorRegressionGain_action (3 : ℂ) Complex.I).symm

/-- Every output satisfying the concrete parallel behavior has both expected branch amplitudes. -/
lemma linearBehaviorRegression_parallel_output_eq (candidate : ModeAmplitude (Unit ⊕ Unit))
    (hCandidate : (linearBehaviorRegressionParallelInput, candidate) ∈
      (linearBehaviorRegressionGain 2).toBehavior.parallel
        (linearBehaviorRegressionGain 3).toBehavior) :
    candidate = linearBehaviorRegressionParallelOutput := by
  rw [LinearBehavior.mem_parallel_iff] at hCandidate
  rcases hCandidate with ⟨hLeft, hRight⟩
  rw [ModeTransform.mem_toBehavior_iff_toLinearMap] at hLeft hRight
  have hLeftOutput : candidate.restrictInl = linearBehaviorRegressionUnitAmplitude 2 := by
    calc
      candidate.restrictInl = (linearBehaviorRegressionGain 2).toLinearMap
          (linearBehaviorRegressionUnitAmplitude 1) := by
        simpa [linearBehaviorRegressionParallelInput] using hLeft
      _ = linearBehaviorRegressionUnitAmplitude (2 * 1) :=
        linearBehaviorRegressionGain_action 2 1
      _ = linearBehaviorRegressionUnitAmplitude 2 := by norm_num
  have hRightOutput : candidate.restrictInr =
      linearBehaviorRegressionUnitAmplitude (3 * Complex.I) := by
    calc
      candidate.restrictInr = (linearBehaviorRegressionGain 3).toLinearMap
          (linearBehaviorRegressionUnitAmplitude Complex.I) := by
        simpa [linearBehaviorRegressionParallelInput] using hRight
      _ = linearBehaviorRegressionUnitAmplitude (3 * Complex.I) :=
        linearBehaviorRegressionGain_action 3 Complex.I
  calc
    candidate = candidate.restrictInl.directSum candidate.restrictInr :=
      (ModeAmplitude.directSum_restrict candidate).symm
    _ = linearBehaviorRegressionParallelOutput := by
      rw [hLeftOutput, hRightOutput]
      rfl

/-- The expected parallel output is not equal to the false right-branch output. -/
lemma linearBehaviorRegression_parallelOutput_ne_wrongOutput :
    linearBehaviorRegressionParallelOutput ≠
      linearBehaviorRegressionParallelWrongOutput := by
  intro hOutput
  have hRight := congrArg
    (fun amplitude : ModeAmplitude (Unit ⊕ Unit) => amplitude (Sum.inr ())) hOutput
  norm_num [linearBehaviorRegressionParallelOutput,
    linearBehaviorRegressionParallelWrongOutput,
    linearBehaviorRegressionUnitAmplitude] at hRight

/-- The false right-branch output does not satisfy the concrete parallel behavior. -/
lemma linearBehaviorRegression_wrongOutput_not_mem_parallel :
    (linearBehaviorRegressionParallelInput, linearBehaviorRegressionParallelWrongOutput) ∉
      (linearBehaviorRegressionGain 2).toBehavior.parallel
        (linearBehaviorRegressionGain 3).toBehavior := by
  intro hWrong
  exact linearBehaviorRegression_parallelOutput_ne_wrongOutput
    (linearBehaviorRegression_parallel_output_eq _ hWrong).symm

/-- The block-diagonal transform independently produces the exact parallel output. -/
lemma linearBehaviorRegression_directSum_action :
    ((linearBehaviorRegressionGain 2).directSum
        (linearBehaviorRegressionGain 3)).toLinearMap
      linearBehaviorRegressionParallelInput = linearBehaviorRegressionParallelOutput := by
  calc
    ((linearBehaviorRegressionGain 2).directSum
        (linearBehaviorRegressionGain 3)).toLinearMap
        linearBehaviorRegressionParallelInput =
      ((linearBehaviorRegressionGain 2).toLinearMap
        (linearBehaviorRegressionUnitAmplitude 1)).directSum
          ((linearBehaviorRegressionGain 3).toLinearMap
            (linearBehaviorRegressionUnitAmplitude Complex.I)) := by
      exact ModeTransform.directSum_apply _ _ _ _
    _ = linearBehaviorRegressionParallelOutput := by
      rw [linearBehaviorRegressionGain_action, linearBehaviorRegressionGain_action]
      norm_num [linearBehaviorRegressionParallelOutput]

/-- The independently checked block-diagonal action is in its graph behavior. -/
lemma linearBehaviorRegression_directSum_graph :
    (linearBehaviorRegressionParallelInput, linearBehaviorRegressionParallelOutput) ∈
      ((linearBehaviorRegressionGain 2).directSum
        (linearBehaviorRegressionGain 3)).toBehavior := by
  rw [ModeTransform.mem_toBehavior_iff_toLinearMap]
  exact linearBehaviorRegression_directSum_action.symm

/-- The concrete relational parallel composition equals the block-diagonal graph behavior. -/
lemma linearBehaviorRegression_parallel_eq_directSum :
    (linearBehaviorRegressionGain 2).toBehavior.parallel
        (linearBehaviorRegressionGain 3).toBehavior =
      ((linearBehaviorRegressionGain 2).directSum
        (linearBehaviorRegressionGain 3)).toBehavior :=
  ModeTransform.toBehavior_directSum _ _

end

end Optics
