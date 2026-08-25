/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Components.ReflectionlessTwoPort

/-!
# Regression tests for reflectionless two-port realization

## i. Overview

The heterogeneous fixture has a singleton left family and a two-mode right family. Its unequal
directional row and column act on nonzero inputs from both sides. Exact independent-behavior and
typed-scattering results therefore pin endpoint wrappers, upper-right versus lower-left block
placement, local mode order, and graph realization without a dimension-collapsing symmetry.

## ii. Key results

- `reflectionlessTwoPortRectangular_outputMap`: exact independent directional output.
- `reflectionlessTwoPortRectangular_mem`: direct independent-behavior membership.
- `reflectionlessTwoPortRectangular_scattering_action`: exact typed scattering realization.
- `reflectionlessTwoPortRectangular_realized_mem`: concrete realized-graph membership.
- `reflectionlessTwoPortRectangular_wrong_not_mem`: wrong local mode order is rejected.

## iii. Table of contents

- A. Heterogeneous fixture
- B. Independent behavior
- C. Scattering realization

## iv. References

These are source-neutral regression fixtures for the Physlib-original algebraic constructor.
-/

@[expose] public section

namespace Optics

noncomputable section

namespace ReflectionlessTwoPort

/-!

## A. Heterogeneous fixture

-/

/-- A two-mode-to-single-mode right-to-left transform with unequal row entries. -/
def reflectionlessTwoPortRectangularRightToLeft : ModeTransform (Fin 2) Unit :=
  fun _ input => if input = 0 then 2 else 3

/-- A single-mode-to-two-mode left-to-right transform with unequal column entries. -/
def reflectionlessTwoPortRectangularLeftToRight : ModeTransform Unit (Fin 2) :=
  fun output _ => if output = 0 then 5 else 7

/-- An input with nonzero amplitudes on both sides of the rectangular fixture. -/
def reflectionlessTwoPortRectangularIncident :
    ModeAmplitude (Incident Unit ⊕ Incident (Fin 2)) :=
  WithLp.toLp 2 fun
    | Sum.inl _ => 11
    | Sum.inr ⟨mode⟩ => if mode = 0 then 13 else 17

/-- The expected rectangular output: `2 * 13 + 3 * 17 = 77` on the left and
`(5 * 11, 7 * 11) = (55, 77)` on the right. -/
def reflectionlessTwoPortRectangularOutgoing :
    ModeAmplitude (Outgoing Unit ⊕ Outgoing (Fin 2)) :=
  WithLp.toLp 2 fun
    | Sum.inl _ => 77
    | Sum.inr ⟨mode⟩ => if mode = 0 then 55 else 77

/-- A false output obtained by exchanging the two right-hand local modes. -/
def reflectionlessTwoPortRectangularWrongOutgoing :
    ModeAmplitude (Outgoing Unit ⊕ Outgoing (Fin 2)) :=
  WithLp.toLp 2 fun
    | Sum.inl _ => 77
    | Sum.inr ⟨mode⟩ => if mode = 0 then 77 else 55

/-- The rectangular right-to-left transform computes its unequal row action. -/
lemma reflectionlessTwoPortRectangularRightToLeft_apply
    (amplitude : ModeAmplitude (Fin 2)) :
    reflectionlessTwoPortRectangularRightToLeft.toLinearMap amplitude =
      WithLp.toLp 2 (fun _ : Unit => 2 * amplitude 0 + 3 * amplitude 1) := by
  apply WithLp.ofLp_injective 2
  funext output
  rcases output with ⟨⟩
  simp [ModeTransform.toLinearMap, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    reflectionlessTwoPortRectangularRightToLeft, Fin.sum_univ_two]

/-- The rectangular left-to-right transform computes its unequal column action. -/
lemma reflectionlessTwoPortRectangularLeftToRight_apply
    (amplitude : ModeAmplitude Unit) :
    reflectionlessTwoPortRectangularLeftToRight.toLinearMap amplitude =
      WithLp.toLp 2 fun output : Fin 2 =>
        if output = 0 then 5 * amplitude () else 7 * amplitude () := by
  apply WithLp.ofLp_injective 2
  funext output
  fin_cases output <;>
    simp [ModeTransform.toLinearMap, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
      reflectionlessTwoPortRectangularLeftToRight]

/-!

## B. Independent behavior

-/

/-- The independent rectangular law places both unequal directional actions correctly. -/
lemma reflectionlessTwoPortRectangular_outputMap :
    outputMap reflectionlessTwoPortRectangularRightToLeft
        reflectionlessTwoPortRectangularLeftToRight
        reflectionlessTwoPortRectangularIncident =
      reflectionlessTwoPortRectangularOutgoing := by
  rw [outputMap_apply, reflectionlessTwoPortRectangularRightToLeft_apply,
    reflectionlessTwoPortRectangularLeftToRight_apply]
  apply WithLp.ofLp_injective 2
  funext endpoint
  rcases endpoint with endpoint | endpoint
  · rcases endpoint with ⟨⟨⟩⟩
    norm_num [reflectionlessTwoPortRectangularIncident,
      reflectionlessTwoPortRectangularOutgoing, ModeAmplitude.directSum]
  · rcases endpoint with ⟨mode⟩
    fin_cases mode <;>
      norm_num [reflectionlessTwoPortRectangularIncident,
        reflectionlessTwoPortRectangularOutgoing, ModeAmplitude.directSum]

/-- The rectangular fixture belongs directly to its independent behavioral specification. -/
lemma reflectionlessTwoPortRectangular_mem :
    (reflectionlessTwoPortRectangularIncident,
      reflectionlessTwoPortRectangularOutgoing) ∈
        behavior reflectionlessTwoPortRectangularRightToLeft
          reflectionlessTwoPortRectangularLeftToRight := by
  rw [mem_behavior_iff]
  simpa only [outputMap_apply] using reflectionlessTwoPortRectangular_outputMap.symm

/-- Exchanging the two right-hand local modes violates the independent behavior. -/
lemma reflectionlessTwoPortRectangular_wrong_not_mem :
    (reflectionlessTwoPortRectangularIncident,
      reflectionlessTwoPortRectangularWrongOutgoing) ∉
        behavior reflectionlessTwoPortRectangularRightToLeft
          reflectionlessTwoPortRectangularLeftToRight := by
  intro hWrong
  rw [mem_behavior_iff] at hWrong
  have hExpected :
      ((ModeAmplitude.reindex Outgoing.channelEquiv.symm
          (reflectionlessTwoPortRectangularRightToLeft.toLinearMap
            (ModeAmplitude.reindex Incident.channelEquiv
              reflectionlessTwoPortRectangularIncident.restrictInr))).directSum
        (ModeAmplitude.reindex Outgoing.channelEquiv.symm
          (reflectionlessTwoPortRectangularLeftToRight.toLinearMap
            (ModeAmplitude.reindex Incident.channelEquiv
              reflectionlessTwoPortRectangularIncident.restrictInl)))) =
        reflectionlessTwoPortRectangularOutgoing := by
    simpa only [outputMap_apply] using reflectionlessTwoPortRectangular_outputMap
  have hWrongOutput := hWrong.trans hExpected
  have hMode := congrArg
    (fun amplitude : ModeAmplitude (Outgoing Unit ⊕ Outgoing (Fin 2)) =>
      amplitude (Sum.inr (Outgoing.mk 0))) hWrongOutput
  norm_num [reflectionlessTwoPortRectangularWrongOutgoing,
    reflectionlessTwoPortRectangularOutgoing] at hMode

/-!

## C. Scattering realization

-/

/-- The typed scattering realization produces the exact heterogeneous output. -/
lemma reflectionlessTwoPortRectangular_scattering_action :
    (scattering reflectionlessTwoPortRectangularRightToLeft
      reflectionlessTwoPortRectangularLeftToRight).toTwoPortScatteringTransform.toLinearMap
        reflectionlessTwoPortRectangularIncident =
      reflectionlessTwoPortRectangularOutgoing := by
  rw [scattering_toTwoPortScatteringTransform_toLinearMap_apply]
  exact reflectionlessTwoPortRectangular_outputMap

/-- The exact heterogeneous state belongs to the realized scattering graph. -/
lemma reflectionlessTwoPortRectangular_realized_mem :
    (reflectionlessTwoPortRectangularIncident,
      reflectionlessTwoPortRectangularOutgoing) ∈
        (scattering reflectionlessTwoPortRectangularRightToLeft
          reflectionlessTwoPortRectangularLeftToRight).toTwoPortScatteringBehavior := by
  rw [ScatteringMatrix.toTwoPortScatteringBehavior,
    ModeTransform.mem_toBehavior_iff_toLinearMap]
  exact reflectionlessTwoPortRectangular_scattering_action.symm

end ReflectionlessTwoPort

end

end Optics
