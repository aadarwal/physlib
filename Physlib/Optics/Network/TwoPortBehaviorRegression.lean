/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.TwoPortBehavior

/-!
# Regression tests for travelling-wave two-port behaviors

## i. Overview

Four distinct non-real scalar amplitudes pin the backward-first regrouping of scattering data:
incident `(aL, aR)` and outgoing `(bL, bR)` become left state `(bL, aL)` and right state
`(aR, bR)`. A perfect-through scattering map becomes the identity backward-first behavior. A zero
scattering map then shows that scattering functionality need not survive this regrouping: the right
incident wave remains unconstrained when both outgoing waves vanish.

## ii. Key results

## iii. Table of contents

- A. Backward-first scattering regrouping
- B. Scattering functionality under regrouping

## iv. References

These are algebraic fixed-frequency fixtures. Their scalar coordinates do not carry a field,
power, passivity, reciprocity, propagation-phase, termination, or physical-realization claim.

-/

@[expose] public section

namespace Optics

noncomputable section

/-!

## A. Backward-first scattering regrouping

-/

/-- A constant scalar amplitude on an arbitrary mode family. -/
def twoPortBehaviorRegressionScalarAmplitude {ι : Type*} (value : ℂ) : ModeAmplitude ι :=
  WithLp.toLp 2 fun _ => value

/-- A backward-first two-wave state with independently specified scalar coordinates. -/
def twoPortBehaviorRegressionState (backward forward : ℂ) :
    BackwardFirstTravellingWaveState Unit :=
  (twoPortBehaviorRegressionScalarAmplitude backward : ModeAmplitude (BackwardWave Unit)).directSum
    (twoPortBehaviorRegressionScalarAmplitude forward : ModeAmplitude (ForwardWave Unit))

/-- The backward coordinate of the scalar regression state. -/
@[simp]
lemma twoPortBehaviorRegressionState_backward (backward forward : ℂ) :
    twoPortBehaviorRegressionState backward forward (Sum.inl (BackwardWave.mk ())) =
      backward := rfl

/-- The forward coordinate of the scalar regression state. -/
@[simp]
lemma twoPortBehaviorRegressionState_forward (backward forward : ℂ) :
    twoPortBehaviorRegressionState backward forward (Sum.inr (ForwardWave.mk ())) =
      forward := rfl

/-- Distinct left and right incident amplitudes `(aL, aR)`. -/
def twoPortBehaviorRegressionIncident : ModeAmplitude (Incident Unit ⊕ Incident Unit) :=
  (twoPortBehaviorRegressionScalarAmplitude (1 + Complex.I) :
    ModeAmplitude (Incident Unit)).directSum
    (twoPortBehaviorRegressionScalarAmplitude (2 - Complex.I) :
      ModeAmplitude (Incident Unit))

/-- Distinct left and right outgoing amplitudes `(bL, bR)`. -/
def twoPortBehaviorRegressionOutgoing : ModeAmplitude (Outgoing Unit ⊕ Outgoing Unit) :=
  (twoPortBehaviorRegressionScalarAmplitude (3 + 2 * Complex.I) :
    ModeAmplitude (Outgoing Unit)).directSum
    (twoPortBehaviorRegressionScalarAmplitude (4 - 3 * Complex.I) :
      ModeAmplitude (Outgoing Unit))

/-- The expected backward-first left state `(bL, aL)`. -/
def twoPortBehaviorRegressionLeftState : BackwardFirstTravellingWaveState Unit :=
  twoPortBehaviorRegressionState (3 + 2 * Complex.I) (1 + Complex.I)

/-- The expected backward-first right state `(aR, bR)`. -/
def twoPortBehaviorRegressionRightState : BackwardFirstTravellingWaveState Unit :=
  twoPortBehaviorRegressionState (2 - Complex.I) (4 - 3 * Complex.I)

/-- Scattering coordinates regroup to the exact backward-first left and right states. -/
lemma twoPortBehaviorRegression_scattering_regrouping :
    scatteringBackwardFirstLinearEquiv
        (twoPortBehaviorRegressionIncident, twoPortBehaviorRegressionOutgoing) =
      (twoPortBehaviorRegressionLeftState, twoPortBehaviorRegressionRightState) := by
  apply Prod.ext <;>
    apply WithLp.ofLp_injective 2 <;>
    funext index <;>
    rcases index with ⟨index⟩ | ⟨index⟩ <;>
    rfl

/-- Ungrouping the exact backward-first states recovers the original scattering coordinates. -/
lemma twoPortBehaviorRegression_scattering_ungrouping :
    scatteringBackwardFirstLinearEquiv.symm
        (twoPortBehaviorRegressionLeftState, twoPortBehaviorRegressionRightState) =
      (twoPortBehaviorRegressionIncident, twoPortBehaviorRegressionOutgoing) := by
  apply Prod.ext <;>
    apply WithLp.ofLp_injective 2 <;>
    funext index <;>
    rcases index with ⟨index⟩ | ⟨index⟩ <;>
    rfl

/-!

## B. Scattering functionality under regrouping

-/

/-- The perfect-through scattering map: each incident wave exits at the opposite boundary. -/
def twoPortBehaviorRegressionPerfectThroughMap :
    ModeAmplitude (Incident Unit ⊕ Incident Unit) →ₗ[ℂ]
      ModeAmplitude (Outgoing Unit ⊕ Outgoing Unit) where
  toFun incident := WithLp.toLp 2 fun
    | Sum.inl outgoing => incident (Sum.inr (Incident.mk outgoing.channel))
    | Sum.inr outgoing => incident (Sum.inl (Incident.mk outgoing.channel))
  map_add' first second := by
    apply WithLp.ofLp_injective 2
    funext index
    rcases index with ⟨index⟩ | ⟨index⟩ <;> rfl
  map_smul' scalar incident := by
    apply WithLp.ofLp_injective 2
    funext index
    rcases index with ⟨index⟩ | ⟨index⟩ <;> rfl

/-- The perfect-through map presented as a scattering-coordinate behavior. -/
def twoPortBehaviorRegressionPerfectThrough : TwoPortScatteringBehavior Unit Unit :=
  LinearBehavior.ofLinearMap twoPortBehaviorRegressionPerfectThroughMap

/-- Regrouping perfect-through scattering gives the identity backward-first behavior. -/
lemma twoPortBehaviorRegressionPerfectThrough_toBackwardFirst :
    twoPortBehaviorRegressionPerfectThrough.toBackwardFirst =
      (LinearBehavior.identity : BackwardFirstTwoPortBehavior Unit Unit) := by
  ext ⟨left, right⟩
  rw [TwoPortScatteringBehavior.mem_toBackwardFirst_iff]
  unfold twoPortBehaviorRegressionPerfectThrough
  rw [LinearBehavior.mem_ofLinearMap_iff, LinearBehavior.mem_identity_iff]
  constructor
  · intro hThrough
    apply WithLp.ofLp_injective 2
    funext index
    rcases index with ⟨index⟩ | ⟨index⟩
    · have hBackward := congrArg
        (fun outgoing : ModeAmplitude (Outgoing Unit ⊕ Outgoing Unit) =>
          outgoing (Sum.inl (Outgoing.mk index.channel))) hThrough
      exact hBackward.symm
    · have hForward := congrArg
        (fun outgoing : ModeAmplitude (Outgoing Unit ⊕ Outgoing Unit) =>
          outgoing (Sum.inr (Outgoing.mk index.channel))) hThrough
      exact hForward
  · rintro rfl
    apply WithLp.ofLp_injective 2
    funext index
    rcases index with ⟨index⟩ | ⟨index⟩ <;>
      rfl

/-- The graph of the zero scattering map on the two scalar port coordinates. -/
def twoPortBehaviorRegressionZeroScattering : TwoPortScatteringBehavior Unit Unit :=
  LinearBehavior.ofLinearMap 0

/-- The zero scattering relation is functional in incident-to-outgoing coordinates. -/
lemma twoPortBehaviorRegressionZeroScattering_isFunctional :
    twoPortBehaviorRegressionZeroScattering.IsFunctional :=
  LinearBehavior.isFunctional_ofLinearMap 0

/-- A nonzero right-incident, zero-right-outgoing state used to expose chain multivaluedness. -/
def twoPortBehaviorRegressionFreeRightIncident : BackwardFirstTravellingWaveState Unit :=
  twoPortBehaviorRegressionState 1 0

/-- The zero left and right states satisfy the regrouped zero scattering behavior. -/
lemma twoPortBehaviorRegressionZeroScattering_zero_mem :
    (0, 0) ∈ twoPortBehaviorRegressionZeroScattering.toBackwardFirst := by
  rw [TwoPortScatteringBehavior.mem_toBackwardFirst_iff]
  unfold twoPortBehaviorRegressionZeroScattering
  rw [LinearBehavior.mem_ofLinearMap_iff]
  change (scatteringBackwardFirstLinearEquiv.symm (0, 0)).2 = 0
  apply WithLp.ofLp_injective 2
  funext index
  rcases index with ⟨index⟩ | ⟨index⟩ <;>
    rfl

/-- Keeping the left state zero while choosing a nonzero right-incident wave also satisfies the
regrouped zero scattering behavior. -/
lemma twoPortBehaviorRegressionZeroScattering_freeRightIncident_mem :
    (0, twoPortBehaviorRegressionFreeRightIncident) ∈
      twoPortBehaviorRegressionZeroScattering.toBackwardFirst := by
  rw [TwoPortScatteringBehavior.mem_toBackwardFirst_iff]
  unfold twoPortBehaviorRegressionZeroScattering
  rw [LinearBehavior.mem_ofLinearMap_iff]
  change (scatteringBackwardFirstLinearEquiv.symm
    (0, twoPortBehaviorRegressionFreeRightIncident)).2 = 0
  apply WithLp.ofLp_injective 2
  funext index
  rcases index with ⟨index⟩ | ⟨index⟩ <;>
    rfl

/-- The free-right-incident state is not the zero right state. -/
lemma twoPortBehaviorRegressionFreeRightIncident_ne_zero :
    twoPortBehaviorRegressionFreeRightIncident ≠ 0 := by
  intro hState
  have hBackward := congrArg
    (fun state : BackwardFirstTravellingWaveState Unit =>
      state (Sum.inl (BackwardWave.mk ()))) hState
  norm_num [twoPortBehaviorRegressionFreeRightIncident, twoPortBehaviorRegressionState,
    twoPortBehaviorRegressionScalarAmplitude] at hBackward

/-- A functional scattering graph can become multivalued after backward-first regrouping. -/
lemma twoPortBehaviorRegressionZeroScattering_not_backwardFirstSingleValued :
    ¬twoPortBehaviorRegressionZeroScattering.toBackwardFirst.IsSingleValued := by
  intro hSingleValued
  exact twoPortBehaviorRegressionFreeRightIncident_ne_zero
    (hSingleValued twoPortBehaviorRegressionZeroScattering_freeRightIncident_mem
      twoPortBehaviorRegressionZeroScattering_zero_mem)

end

end Optics
