/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Components.DirectionalCoupler

/-!
# Regression tests for the algebraic directional coupler

## i. Overview

The exact `3–4–5` fixture uses through amplitude `3 / 5`, cross amplitude `4 / 5`, and nonzero
data on both arms of both longitudinal sides. Its expected result pins the `-I` cross phase,
through/cross placement, opposite-side routing, and coherent two-input addition. Membership is
checked through the independent behavior; the typed scattering action is evaluated separately.

Directly defined hostile outputs reject the opposite cross phase and same-side routing. The
fixture remains on algebraic nested-sum labels; physical four-port ownership is tested only in the
later physical layer.

## ii. Key results

- `directionalCouplerRegression_mem`: direct independent-behavior membership.
- `directionalCouplerRegression_wrongPhase_not_mem`: rejection of the opposite cross phase.
- `directionalCouplerRegression_sameSide_not_mem`: rejection of same-side routing.
- `directionalCouplerRegression_scattering_action`: exact typed-scattering action.
- `directionalCouplerRegression_realized_mem`: concrete realized-graph membership.

## iii. Table of contents

- A. Exact nested-sum fixture
- B. Independent behavior and hostile outputs
- C. Scattering realization

## iv. References

This is a source-neutral regression for the Physlib-original algebraic component law.
-/

@[expose] public section

namespace Optics

noncomputable section

namespace DirectionalCoupler

/-!
## A. Exact nested-sum fixture
-//-- The normalized `3–4–5` through/cross amplitude pair. -/
def directionalCouplerRegressionParameters : Parameters where
  throughAmplitude := 3 / 5
  crossAmplitude := 4 / 5
/-- Nonzero incident amplitudes on both arms of both longitudinal sides. -/
def directionalCouplerRegressionIncident :
    ModeAmplitude (Incident (Unit ⊕ Unit) ⊕ Incident (Unit ⊕ Unit)) :=
  WithLp.toLp 2 fun
    | Sum.inl ⟨Sum.inl ()⟩ => 1
    | Sum.inl ⟨Sum.inr ()⟩ => 2
    | Sum.inr ⟨Sum.inl ()⟩ => 3
    | Sum.inr ⟨Sum.inr ()⟩ => 4
/-- Returning the left incident side to raw arm labels gives amplitudes one and two. -/
lemma directionalCouplerRegressionIncident_left :
    ModeAmplitude.reindex Incident.channelEquiv
        directionalCouplerRegressionIncident.restrictInl =
      WithLp.toLp 2 (fun | Sum.inl () => 1 | Sum.inr () => 2) := by
  apply WithLp.ofLp_injective 2
  funext channel
  rcases channel with ⟨⟩ | ⟨⟩ <;> rfl
/-- Returning the right incident side to raw arm labels gives amplitudes three and four. -/
lemma directionalCouplerRegressionIncident_right :
    ModeAmplitude.reindex Incident.channelEquiv
        directionalCouplerRegressionIncident.restrictInr =
      WithLp.toLp 2 (fun | Sum.inl () => 3 | Sum.inr () => 4) := by
  apply WithLp.ofLp_injective 2
  funext channel
  rcases channel with ⟨⟩ | ⟨⟩ <;> rfl

/-- The exact opposite-side output under the pinned negative-quadrature mixer. -/
def directionalCouplerRegressionOutgoing :
    ModeAmplitude (Outgoing (Unit ⊕ Unit) ⊕ Outgoing (Unit ⊕ Unit)) :=
  WithLp.toLp 2 fun
    | Sum.inl ⟨Sum.inl ()⟩ => (9 - 16 * Complex.I) / 5
    | Sum.inl ⟨Sum.inr ()⟩ => (12 - 12 * Complex.I) / 5
    | Sum.inr ⟨Sum.inl ()⟩ => (3 - 8 * Complex.I) / 5
    | Sum.inr ⟨Sum.inr ()⟩ => (6 - 4 * Complex.I) / 5

/-- The false output obtained by reversing the declared cross-phase sign. -/
def directionalCouplerRegressionWrongPhase :
    ModeAmplitude (Outgoing (Unit ⊕ Unit) ⊕ Outgoing (Unit ⊕ Unit)) :=
  WithLp.toLp 2 fun
    | Sum.inl ⟨Sum.inl ()⟩ => (9 + 16 * Complex.I) / 5
    | Sum.inl ⟨Sum.inr ()⟩ => (12 + 12 * Complex.I) / 5
    | Sum.inr ⟨Sum.inl ()⟩ => (3 + 8 * Complex.I) / 5
    | Sum.inr ⟨Sum.inr ()⟩ => (6 + 4 * Complex.I) / 5

/-- The false output obtained by mixing each incident pair back onto the same side. -/
def directionalCouplerRegressionSameSide :
    ModeAmplitude (Outgoing (Unit ⊕ Unit) ⊕ Outgoing (Unit ⊕ Unit)) :=
  WithLp.toLp 2 fun
    | Sum.inl ⟨Sum.inl ()⟩ => (3 - 8 * Complex.I) / 5
    | Sum.inl ⟨Sum.inr ()⟩ => (6 - 4 * Complex.I) / 5
    | Sum.inr ⟨Sum.inl ()⟩ => (9 - 16 * Complex.I) / 5
    | Sum.inr ⟨Sum.inr ()⟩ => (12 - 12 * Complex.I) / 5

/-!
## B. Independent behavior and hostile outputs
-/

/-- The exact state satisfies the independently declared directional mixing equations. -/
lemma directionalCouplerRegression_mem :
    (directionalCouplerRegressionIncident, directionalCouplerRegressionOutgoing) ∈
      behavior directionalCouplerRegressionParameters := by
  rw [mem_behavior_iff, directionalCouplerRegressionIncident_right,
    directionalCouplerRegressionIncident_left, mixing_toLinearMap_apply,
    mixing_toLinearMap_apply]
  apply WithLp.ofLp_injective 2
  funext endpoint
  rcases endpoint with endpoint | endpoint <;>
    rcases endpoint with ⟨channel⟩ <;>
    rcases channel with ⟨⟩ | ⟨⟩ <;>
    norm_num [directionalCouplerRegressionParameters, crossCoefficient,
      directionalCouplerRegressionOutgoing,
      ModeAmplitude.directSum, ModeAmplitude.restrictInl,
      ModeAmplitude.restrictInr] <;>
    apply Complex.ext <;> norm_num

/-- The independent behavior rejects the opposite cross-phase sign. -/
lemma directionalCouplerRegression_wrongPhase_not_mem :
    (directionalCouplerRegressionIncident, directionalCouplerRegressionWrongPhase) ∉
      behavior directionalCouplerRegressionParameters := by
  intro hWrong
  rw [mem_behavior_iff, directionalCouplerRegressionIncident_right,
    directionalCouplerRegressionIncident_left, mixing_toLinearMap_apply,
    mixing_toLinearMap_apply] at hWrong
  have hCoordinate := congrArg
    (fun output => output (Sum.inr (Outgoing.mk (Sum.inl ())))) hWrong
  simp only [ModeAmplitude.directSum_apply_inr,
    ModeAmplitude.reindex_apply, Equiv.symm_symm,
    Outgoing.channelEquiv_apply] at hCoordinate
  have hImaginary := congrArg Complex.im hCoordinate
  norm_num [directionalCouplerRegressionParameters, crossCoefficient,
    directionalCouplerRegressionWrongPhase, ModeAmplitude.restrictInl,
    ModeAmplitude.restrictInr] at hImaginary

/-- The independent behavior rejects same-side routing. -/
lemma directionalCouplerRegression_sameSide_not_mem :
    (directionalCouplerRegressionIncident, directionalCouplerRegressionSameSide) ∉
      behavior directionalCouplerRegressionParameters := by
  intro hWrong
  rw [mem_behavior_iff, directionalCouplerRegressionIncident_right,
    directionalCouplerRegressionIncident_left, mixing_toLinearMap_apply,
    mixing_toLinearMap_apply] at hWrong
  have hCoordinate := congrArg
    (fun output => output (Sum.inl (Outgoing.mk (Sum.inl ())))) hWrong
  simp only [ModeAmplitude.directSum_apply_inl,
    ModeAmplitude.reindex_apply, Equiv.symm_symm,
    Outgoing.channelEquiv_apply] at hCoordinate
  have hReal := congrArg Complex.re hCoordinate
  norm_num [directionalCouplerRegressionParameters, crossCoefficient,
    directionalCouplerRegressionSameSide, ModeAmplitude.restrictInl,
    ModeAmplitude.restrictInr] at hReal

/-!
## C. Scattering realization
-/

/-- The typed scattering realization produces the exact opposite-side mixed output. -/
lemma directionalCouplerRegression_scattering_action :
    ModeTransform.toLinearMap
        (ScatteringMatrix.toTwoPortScatteringTransform
          (scattering directionalCouplerRegressionParameters Unit))
        directionalCouplerRegressionIncident =
      directionalCouplerRegressionOutgoing := by
  rw [scattering_toTwoPortScatteringTransform_toLinearMap_apply,
    ReflectionlessTwoPort.outputMap_apply,
    directionalCouplerRegressionIncident_right,
    directionalCouplerRegressionIncident_left, mixing_toLinearMap_apply,
    mixing_toLinearMap_apply]
  apply WithLp.ofLp_injective 2
  funext endpoint
  rcases endpoint with endpoint | endpoint <;>
    rcases endpoint with ⟨channel⟩ <;>
    rcases channel with ⟨⟩ | ⟨⟩ <;>
    norm_num [directionalCouplerRegressionParameters, crossCoefficient,
      directionalCouplerRegressionOutgoing,
      ModeAmplitude.directSum, ModeAmplitude.restrictInl,
      ModeAmplitude.restrictInr] <;>
    apply Complex.ext <;> norm_num

/-- The exact state belongs to the separately realized typed-scattering graph. -/
lemma directionalCouplerRegression_realized_mem :
    (directionalCouplerRegressionIncident, directionalCouplerRegressionOutgoing) ∈
      (scattering directionalCouplerRegressionParameters Unit).toTwoPortScatteringBehavior := by
  rw [ScatteringMatrix.toTwoPortScatteringBehavior,
    ModeTransform.mem_toBehavior_iff_toLinearMap,
    directionalCouplerRegression_scattering_action]

end DirectionalCoupler
end
end Optics
