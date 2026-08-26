/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.LinearBehaviorConservation

/-!
# Rectangular conservation regression

## i. Overview

This regression uses a genuinely rectangular `Fin 1 → Fin 2` splitter. At the concrete input
amplitude `1`, the positive output is `(3/5, 4/5)`, so its modal power is
`9/25 + 16/25 = 1`. The matrix action, relation membership, and all three powers are expanded from
finite sums and `Complex.normSq`, without using a conservation-classification or covariance lemma.

The same input is fed to a hostile duplicated-output transform whose output is `(4/5, 4/5)` and
whose power is `32/25`. That exact member rejects relational passivity by the false inequality
`32/25 ≤ 1`. Thus a duplicated output channel or a mistaken square-boundary identification can
make the regression fail.

The input and output index families cannot be equivalent because their finite cardinalities are
one and two. The conservation predicate therefore cannot be relying on a hidden time-reversal or
incident/outgoing pairing.

## ii. Key results

- `linearBehaviorConservationRegression_splitter_mem`: primitive membership of the
  `(3/5, 4/5)` output.
- `linearBehaviorConservationRegression_input_power` and
  `linearBehaviorConservationRegression_splitter_output_power`: the exact positive powers.
- `linearBehaviorConservationRegression_splitter_isPowerPreserving`: direct relation-level
  classification without the transform/behavior iff under test.
- `linearBehaviorConservationRegression_no_boundary_equiv`: `Fin 1` and `Fin 2` are not
  equivalent.
- `linearBehaviorConservationRegression_hostile_output_power`: the duplicated output has power
  `32/25`.
- `linearBehaviorConservationRegression_hostile_not_isPassive`: the hostile relation is rejected
  by its concrete member.

## iii. Table of contents

- A. Rectangular splitter primitives
- B. Primitive membership and power anchors
- C. Direct relational classification
- D. No boundary pairing
- E. Hostile duplicated-output sentinel

## iv. References

All quantities in this regression are squared norms of algebraic modal amplitudes. They are not
electromagnetic power or energy statements, and no time-reversal, scattering, physical-port,
reciprocity, reference-plane, propagation, or physical losslessness interpretation is asserted.

This is fail-capable evidence for ledger row N-09, whose failure mode is a false square-port
identification. The positive and hostile anchors do not invoke
`ModeTransform.toBehavior_isPassive_iff`,
`ModeTransform.toBehavior_isPowerPreserving_iff`, any relabel/rephase covariance lemma, or any
FlatNetlist conservation lift.
-/

@[expose] public section

namespace Optics

noncomputable section

/-!
## A. Rectangular splitter primitives
-/

/-- The singleton input amplitude, with its only coordinate equal to one. -/
def linearBehaviorConservationRegressionInput : ModeAmplitude (Fin 1) :=
  WithLp.toLp 2 fun _ => 1

/-- The rectangular three-four-five splitter matrix from one input mode to two output modes. -/
def linearBehaviorConservationRegressionSplitter : ModeTransform (Fin 1) (Fin 2) :=
  fun output _ => if output = 0 then (3 : ℂ) / 5 else (4 : ℂ) / 5

/-- The graph relation of the rectangular three-four-five splitter. -/
def linearBehaviorConservationRegressionSplitterBehavior :
    LinearBehavior (Fin 1) (Fin 2) :=
  linearBehaviorConservationRegressionSplitter.toBehavior

/-- The hand-expanded positive output, with coordinates exactly `3/5` and `4/5`. -/
def linearBehaviorConservationRegressionOutput : ModeAmplitude (Fin 2) :=
  WithLp.toLp 2 fun output => if output = 0 then (3 : ℂ) / 5 else (4 : ℂ) / 5

/-- The splitter action on an arbitrary singleton input, expanded directly from matrix
multiplication. -/
lemma linearBehaviorConservationRegression_splitter_apply
    (input : ModeAmplitude (Fin 1)) :
    linearBehaviorConservationRegressionSplitter.toLinearMap input =
      WithLp.toLp 2 fun output =>
        (if output = 0 then (3 : ℂ) / 5 else (4 : ℂ) / 5) * input 0 := by
  apply WithLp.ofLp_injective 2
  funext output
  fin_cases output <;>
    rw [Matrix.ofLp_toLpLin, Matrix.toLin'_apply, Matrix.mulVec, dotProduct] <;>
    norm_num [linearBehaviorConservationRegressionSplitter]

/-!
## B. Primitive membership and power anchors
-/

/-- The hand-expanded output records the two distinct positive coordinates `3/5` and `4/5`. -/
lemma linearBehaviorConservationRegression_output_coordinates :
    linearBehaviorConservationRegressionOutput 0 = (3 : ℂ) / 5 ∧
      linearBehaviorConservationRegressionOutput 1 = (4 : ℂ) / 5 := by
  norm_num [linearBehaviorConservationRegressionOutput]

/-- The concrete singleton input and hand-expanded output satisfy the splitter graph, independently
of every conservation-classification and covariance lemma under test. -/
lemma linearBehaviorConservationRegression_splitter_mem :
    (linearBehaviorConservationRegressionInput,
        linearBehaviorConservationRegressionOutput) ∈
      linearBehaviorConservationRegressionSplitterBehavior := by
  rw [linearBehaviorConservationRegressionSplitterBehavior,
    ModeTransform.mem_toBehavior_iff_toLinearMap,
    linearBehaviorConservationRegression_splitter_apply]
  apply WithLp.ofLp_injective 2
  funext output
  fin_cases output <;>
    norm_num [linearBehaviorConservationRegressionInput,
      linearBehaviorConservationRegressionOutput]

/-- The concrete singleton input has normalized modal power exactly one. -/
lemma linearBehaviorConservationRegression_input_power :
    linearBehaviorConservationRegressionInput.power = 1 := by
  rw [ModeAmplitude.power_eq_sum_normSq, Fin.sum_univ_one]
  norm_num [linearBehaviorConservationRegressionInput, Complex.normSq_apply]

/-- The concrete `(3/5, 4/5)` output has normalized modal power
`9/25 + 16/25 = 1`. -/
lemma linearBehaviorConservationRegression_splitter_output_power :
    linearBehaviorConservationRegressionOutput.power = 1 := by
  rw [ModeAmplitude.power_eq_sum_normSq, Fin.sum_univ_two]
  norm_num [linearBehaviorConservationRegressionOutput, Complex.normSq_apply]

/-- The concrete positive member has exactly equal input and output modal powers. -/
lemma linearBehaviorConservationRegression_positive_power_agreement :
    linearBehaviorConservationRegressionOutput.power =
      linearBehaviorConservationRegressionInput.power := by
  rw [linearBehaviorConservationRegression_splitter_output_power,
    linearBehaviorConservationRegression_input_power]

/-!
## C. Direct relational classification
-/

/-- The rectangular splitter preserves normalized modal power for every singleton input, proved
from the primitive matrix action and the three-four-five identity. -/
lemma linearBehaviorConservationRegression_splitter_power
    (input : ModeAmplitude (Fin 1)) :
    (linearBehaviorConservationRegressionSplitter.toLinearMap input).power = input.power := by
  rw [linearBehaviorConservationRegression_splitter_apply,
    ModeAmplitude.power_eq_sum_normSq, ModeAmplitude.power_eq_sum_normSq,
    Fin.sum_univ_two, Fin.sum_univ_one]
  change Complex.normSq (((3 : ℂ) / 5) * input 0) +
      Complex.normSq (((4 : ℂ) / 5) * input 0) = Complex.normSq (input 0)
  rw [Complex.normSq_mul, Complex.normSq_mul]
  norm_num [Complex.normSq_apply]
  ring

/-- The positive rectangular relation is power-preserving, proved directly from membership and the
primitive power calculation rather than the transform/behavior classification iff. -/
lemma linearBehaviorConservationRegression_splitter_isPowerPreserving :
    linearBehaviorConservationRegressionSplitterBehavior.IsPowerPreserving := by
  intro input output hMember
  rw [linearBehaviorConservationRegressionSplitterBehavior,
    ModeTransform.mem_toBehavior_iff_toLinearMap] at hMember
  rw [hMember]
  exact linearBehaviorConservationRegression_splitter_power input

/-!
## D. No boundary pairing
-/

/-- The one-channel input boundary and two-channel output boundary admit no equivalence. -/
lemma linearBehaviorConservationRegression_no_boundary_equiv :
    ¬Nonempty (Fin 1 ≃ Fin 2) := by
  rintro ⟨boundaryEquiv⟩
  have hCard := Fintype.card_congr boundaryEquiv
  norm_num at hCard

/-!
## E. Hostile duplicated-output sentinel
-/

/-- The hostile rectangular transform duplicates the `4/5` branch onto both output channels. -/
def linearBehaviorConservationRegressionHostile : ModeTransform (Fin 1) (Fin 2) :=
  fun _ _ => (4 : ℂ) / 5

/-- The graph relation of the hostile duplicated-output transform. -/
def linearBehaviorConservationRegressionHostileBehavior :
    LinearBehavior (Fin 1) (Fin 2) :=
  linearBehaviorConservationRegressionHostile.toBehavior

/-- The hostile hand-expanded output has coordinates `(4/5, 4/5)`. -/
def linearBehaviorConservationRegressionHostileOutput : ModeAmplitude (Fin 2) :=
  WithLp.toLp 2 fun _ => (4 : ℂ) / 5

/-- The hostile hand-expanded output records `4/5` on both distinct output coordinates. -/
lemma linearBehaviorConservationRegression_hostile_output_coordinates :
    linearBehaviorConservationRegressionHostileOutput 0 = (4 : ℂ) / 5 ∧
      linearBehaviorConservationRegressionHostileOutput 1 = (4 : ℂ) / 5 := by
  norm_num [linearBehaviorConservationRegressionHostileOutput]

/-- The singleton input and duplicated output satisfy the hostile graph by primitive matrix
multiplication. -/
lemma linearBehaviorConservationRegression_hostile_mem :
    (linearBehaviorConservationRegressionInput,
        linearBehaviorConservationRegressionHostileOutput) ∈
      linearBehaviorConservationRegressionHostileBehavior := by
  rw [linearBehaviorConservationRegressionHostileBehavior,
    ModeTransform.mem_toBehavior_iff_toLinearMap]
  apply WithLp.ofLp_injective 2
  funext output
  fin_cases output <;>
    rw [Matrix.ofLp_toLpLin, Matrix.toLin'_apply, Matrix.mulVec, dotProduct] <;>
    norm_num [linearBehaviorConservationRegressionHostile,
      linearBehaviorConservationRegressionInput,
      linearBehaviorConservationRegressionHostileOutput]

/-- The duplicated `(4/5, 4/5)` output has normalized modal power exactly `32/25`. -/
lemma linearBehaviorConservationRegression_hostile_output_power :
    linearBehaviorConservationRegressionHostileOutput.power = 32 / 25 := by
  rw [ModeAmplitude.power_eq_sum_normSq, Fin.sum_univ_two]
  norm_num [linearBehaviorConservationRegressionHostileOutput,
    Complex.normSq_apply]

/-- The hostile member strictly increases modal power from `1` to `32/25`. -/
lemma linearBehaviorConservationRegression_hostile_power_gt_input :
    linearBehaviorConservationRegressionInput.power <
      linearBehaviorConservationRegressionHostileOutput.power := by
  rw [linearBehaviorConservationRegression_input_power,
    linearBehaviorConservationRegression_hostile_output_power]
  norm_num

/-- The hostile duplicated-output relation is not passive: its concrete member would require the
false inequality `32/25 ≤ 1`. -/
lemma linearBehaviorConservationRegression_hostile_not_isPassive :
    ¬linearBehaviorConservationRegressionHostileBehavior.IsPassive := by
  intro hPassive
  have hBound := hPassive linearBehaviorConservationRegression_hostile_mem
  rw [linearBehaviorConservationRegression_input_power,
    linearBehaviorConservationRegression_hostile_output_power] at hBound
  norm_num at hBound

end

end Optics
