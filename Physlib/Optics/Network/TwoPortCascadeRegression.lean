/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.TwoPortCascade

/-!
# Regression tests for reflection-free two-port cascade

## i. Overview

Two `Fin 2` transmission blocks are chosen not to commute. Their reflection-free series cascade
has left-to-right block `B * A`, with lower-right entry `7`; the reversed product has entry `1`.

Scope:

The fixture tests matrix order only. It makes no passivity, losslessness, reciprocity, causality,
or physical-realization claim.

## ii. Key results

- `twoPortCascadeRegression_ordered_entry` and
  `twoPortCascadeRegression_ne_reversed_product` pin the later-on-the-left cascade order.

## iii. Table of contents

- A. Noncommuting transmission blocks
- B. Ordered cascade

## iv. References

This fixture is Physlib-original and uses no external source.

-/

@[expose] public section

namespace Optics

noncomputable section

namespace TwoPortCascadeRegression

/-!

## A. Noncommuting transmission blocks

-/

/-- Build a typed `Fin 2` two-port transform from four raw block matrices. -/
def ofBlocks (a b c d : ModeTransform (Fin 2) (Fin 2)) :
    TwoPortScatteringTransform (Fin 2) (Fin 2)
  | Sum.inl output, Sum.inl input => a output.channel input.channel
  | Sum.inl output, Sum.inr input => b output.channel input.channel
  | Sum.inr output, Sum.inl input => c output.channel input.channel
  | Sum.inr output, Sum.inr input => d output.channel input.channel

/-- The first left-to-right transmission block. -/
def firstTransmission : ModeTransform (Fin 2) (Fin 2) := !![1, 2; 0, 1]

/-- The second left-to-right transmission block. -/
def secondTransmission : ModeTransform (Fin 2) (Fin 2) := !![1, 0; 3, 1]

/-- The first fixture has no reflection and transmits left-to-right by `A`. -/
def first : TwoPortScatteringTransform (Fin 2) (Fin 2) :=
  ofBlocks 0 1 firstTransmission 0

/-- The second fixture has no reflection and transmits left-to-right by `B`. -/
def second : TwoPortScatteringTransform (Fin 2) (Fin 2) :=
  ofBlocks 0 1 secondTransmission 0

/-- The first fixture has zero right reflection. -/
lemma first_rightReflection_eq_zero : first.rightReflection = 0 := by
  ext ⟨output⟩ ⟨input⟩
  rfl

/-- The second fixture has zero left reflection. -/
lemma second_leftReflection_eq_zero : second.leftReflection = 0 := by
  ext ⟨output⟩ ⟨input⟩
  rfl

/-!

## B. Ordered cascade

-/

/-- The reflection-free cascade places the later transmission block on the left. -/
lemma twoPortCascadeRegression_ordered_entry :
    (first.reflectionFreeSeriesCascade second first_rightReflection_eq_zero
      second_leftReflection_eq_zero).leftToRightTransmission ⟨1⟩ ⟨1⟩ = 7 := by
  rw [first.leftToRightTransmission_reflectionFreeSeriesCascade second]
  norm_num [first, second, firstTransmission, secondTransmission, ofBlocks,
    Matrix.mul_apply, ← ForwardWave.channelEquiv.symm.sum_comp, Fin.sum_univ_two]

/-- Reversing the noncommuting transmission order changes the pinned lower-right entry. -/
lemma twoPortCascadeRegression_ne_reversed_product :
    (first.reflectionFreeSeriesCascade second first_rightReflection_eq_zero
        second_leftReflection_eq_zero).leftToRightTransmission ≠
      first.leftToRightTransmission * second.leftToRightTransmission := by
  intro hEqual
  have hEntry := congrFun (congrFun hEqual ⟨1⟩) ⟨1⟩
  rw [twoPortCascadeRegression_ordered_entry] at hEntry
  norm_num [first, second, firstTransmission, secondTransmission, ofBlocks,
    Matrix.mul_apply, ← ForwardWave.channelEquiv.symm.sum_comp,
    Fin.sum_univ_two] at hEntry

end TwoPortCascadeRegression

end


end Optics
