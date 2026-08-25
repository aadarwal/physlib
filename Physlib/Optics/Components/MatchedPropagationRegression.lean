/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Components.MatchedPropagation

/-!
# Regression tests for fixed-carrier matched propagation

## i. Overview

The two-mode fixture has amplitude transmission `1 / 2` and carrier path phase `π / 2`, so its
complex coefficient is exactly `-I / 2`. Nonzero incident amplitudes occupy different modes on
the two sides. The expected output therefore pins all three independent convention choices:

- the negative fixed-carrier phase sign;
- transmission to the opposite side rather than same-side reflection; and
- preservation of the local mode label.

Membership is checked directly through the independent behavioral equations. The typed scattering
action is evaluated separately, and its exact result is then placed in the realized graph. Two
hostile outputs reject the opposite phase sign and same-side routing.

## ii. Key results

- `matchedPropagationRegression_transmissionCoefficient`: the phase convention gives `-I / 2`.
- `matchedPropagationRegression_mem`: direct membership in the independent behavior.
- `matchedPropagationRegression_wrongPhase_not_mem`: the opposite phase sign is rejected.
- `matchedPropagationRegression_sameSide_not_mem`: same-side routing is rejected.
- `matchedPropagationRegression_scattering_action`: exact typed-scattering action.
- `matchedPropagationRegression_realized_mem`: concrete membership in the realized graph.

## iii. Table of contents

- A. Hostile two-mode fixture
- B. Independent behavioral equations
- C. Scattering realization

## iv. References

This is an exact source-neutral regression for the Physlib-original component law.
-/

@[expose] public section

namespace Optics

noncomputable section

namespace MatchedPropagation

/-!

## A. Hostile two-mode fixture

-/

/-- Half-amplitude transmission with a positive quarter-turn carrier path phase. -/
def matchedPropagationRegressionParameters : Parameters where
  amplitudeTransmission := 1 / 2
  carrierPathPhase := ((Real.pi / 2 : ℝ) : Real.Angle)

/-- The hostile fixture satisfies the reduced component's parameter-validity predicate. -/
lemma matchedPropagationRegressionParameters_isValid :
    matchedPropagationRegressionParameters.IsValid := by
  constructor <;> norm_num [matchedPropagationRegressionParameters, Parameters.IsValid]

/-- The fixed-carrier sign convention gives the exact coefficient `-I / 2`. -/
lemma matchedPropagationRegression_transmissionCoefficient :
    transmissionCoefficient matchedPropagationRegressionParameters = -Complex.I / 2 := by
  simp [matchedPropagationRegressionParameters, transmissionCoefficient, carrierPhaseFactor,
    Real.Angle.toCircle_coe, Circle.coe_exp]
  ring

/-- Nonzero incident data on different local modes of the two sides. -/
def matchedPropagationRegressionIncident :
    ModeAmplitude (Incident (Fin 2) ⊕ Incident (Fin 2)) :=
  WithLp.toLp 2 fun
    | Sum.inl ⟨mode⟩ => if mode = 0 then 2 + 4 * Complex.I else 0
    | Sum.inr ⟨mode⟩ => if mode = 0 then 0 else 6 - 2 * Complex.I

/-- The expected crossed-side output under multiplication by `-I / 2`. -/
def matchedPropagationRegressionOutgoing :
    ModeAmplitude (Outgoing (Fin 2) ⊕ Outgoing (Fin 2)) :=
  WithLp.toLp 2 fun
    | Sum.inl ⟨mode⟩ => if mode = 0 then 0 else -1 - 3 * Complex.I
    | Sum.inr ⟨mode⟩ => if mode = 0 then 2 - Complex.I else 0

/-- The false output obtained from the opposite carrier-phase sign. -/
def matchedPropagationRegressionWrongPhase :
    ModeAmplitude (Outgoing (Fin 2) ⊕ Outgoing (Fin 2)) :=
  WithLp.toLp 2 fun
    | Sum.inl ⟨mode⟩ => if mode = 0 then 0 else 1 + 3 * Complex.I
    | Sum.inr ⟨mode⟩ => if mode = 0 then -2 + Complex.I else 0

/-- The false output obtained by transmitting on the same side rather than crossing the ports. -/
def matchedPropagationRegressionSameSide :
    ModeAmplitude (Outgoing (Fin 2) ⊕ Outgoing (Fin 2)) :=
  WithLp.toLp 2 fun
    | Sum.inl ⟨mode⟩ => if mode = 0 then 2 - Complex.I else 0
    | Sum.inr ⟨mode⟩ => if mode = 0 then 0 else -1 - 3 * Complex.I

/-!

## B. Independent behavioral equations

-/

/-- The exact state belongs directly to the independent directional behavior. -/
lemma matchedPropagationRegression_mem :
    (matchedPropagationRegressionIncident, matchedPropagationRegressionOutgoing) ∈
      behavior matchedPropagationRegressionParameters := by
  rw [mem_behavior_iff, matchedPropagationRegression_transmissionCoefficient]
  apply WithLp.ofLp_injective 2
  funext endpoint
  rcases endpoint with endpoint | endpoint <;>
    rcases endpoint with ⟨mode⟩ <;> fin_cases mode <;>
    norm_num [matchedPropagationRegressionIncident, matchedPropagationRegressionOutgoing,
      ModeAmplitude.directSum, ModeAmplitude.reindex_apply] <;>
    apply Complex.ext <;> norm_num

/-- The independent behavior rejects the opposite carrier-phase sign. -/
lemma matchedPropagationRegression_wrongPhase_not_mem :
    (matchedPropagationRegressionIncident, matchedPropagationRegressionWrongPhase) ∉
      behavior matchedPropagationRegressionParameters := by
  intro hWrong
  rw [mem_behavior_iff, matchedPropagationRegression_transmissionCoefficient] at hWrong
  have hMode := congrArg
    (fun amplitude : ModeAmplitude (Outgoing (Fin 2) ⊕ Outgoing (Fin 2)) =>
      amplitude (Sum.inr (Outgoing.mk 0))) hWrong
  simp only [ModeAmplitude.directSum_apply_inr, ModeAmplitude.reindex_apply,
    Equiv.symm_symm, Outgoing.channelEquiv_apply] at hMode
  have hReal := congrArg Complex.re hMode
  norm_num [matchedPropagationRegressionIncident, matchedPropagationRegressionWrongPhase] at hReal

/-- The independent behavior rejects same-side routing. -/
lemma matchedPropagationRegression_sameSide_not_mem :
    (matchedPropagationRegressionIncident, matchedPropagationRegressionSameSide) ∉
      behavior matchedPropagationRegressionParameters := by
  intro hWrong
  rw [mem_behavior_iff, matchedPropagationRegression_transmissionCoefficient] at hWrong
  have hMode := congrArg
    (fun amplitude : ModeAmplitude (Outgoing (Fin 2) ⊕ Outgoing (Fin 2)) =>
      amplitude (Sum.inl (Outgoing.mk 0))) hWrong
  simp only [ModeAmplitude.directSum_apply_inl, ModeAmplitude.reindex_apply,
    Equiv.symm_symm, Outgoing.channelEquiv_apply] at hMode
  have hReal := congrArg Complex.re hMode
  norm_num [matchedPropagationRegressionIncident, matchedPropagationRegressionSameSide] at hReal

/-!

## C. Scattering realization

-/

/-- The typed scattering realization produces the exact crossed-side, mode-preserving output. -/
lemma matchedPropagationRegression_scattering_action :
    ModeTransform.toLinearMap
        (ScatteringMatrix.toTwoPortScatteringTransform
          (scattering matchedPropagationRegressionParameters (Fin 2)))
        matchedPropagationRegressionIncident =
      matchedPropagationRegressionOutgoing := by
  rw [scattering_toTwoPortScatteringTransform_toLinearMap_apply,
    matchedPropagationRegression_transmissionCoefficient]
  apply WithLp.ofLp_injective 2
  funext endpoint
  rcases endpoint with endpoint | endpoint <;>
    rcases endpoint with ⟨mode⟩ <;> fin_cases mode <;>
    norm_num [matchedPropagationRegressionIncident, matchedPropagationRegressionOutgoing,
      ModeAmplitude.directSum, ModeAmplitude.reindex_apply] <;>
    apply Complex.ext <;> norm_num

/-- The exact state belongs to the realized typed-scattering graph. -/
lemma matchedPropagationRegression_realized_mem :
    (matchedPropagationRegressionIncident, matchedPropagationRegressionOutgoing) ∈
      (scattering matchedPropagationRegressionParameters (Fin 2)).toTwoPortScatteringBehavior := by
  rw [ScatteringMatrix.toTwoPortScatteringBehavior,
    ModeTransform.mem_toBehavior_iff_toLinearMap,
    matchedPropagationRegression_scattering_action]

end MatchedPropagation

end

end Optics
