/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Components.ReflectionlessTwoPortPower

/-!
# Regression tests for reflectionless two-port modal power

## i. Overview

The phase-only fixture uses independent unit-modulus directional coefficients `I` and
`(3 + 4I) / 5`, whose directional composition is not identity. Exact behavior and power results
therefore guard the fact that losslessness requires each direction to preserve modal power, not
an inverse-pair condition.

A separate modal-amplitude-gain-two fixture gives a concrete full-component input whose output
power is four times its input power, independently ruling out passivity.

## ii. Key results

- `reflectionlessTwoPortPhase_outputMap`: exact non-inverse phase action.
- `reflectionlessTwoPortPhase_directional_mul_ne_one`: the directional transforms are not inverse.
- `reflectionlessTwoPortPhase_isLossless`: independent phases give a lossless component.
- `reflectionlessTwoPortPhase_outgoing_power`: behavior-level decomposition plus phase power
  preservation gives exact input-output power equality.
- `reflectionlessTwoPortGainTwo_not_isPassive`: a concrete component-level nonpassivity witness.

## iii. Table of contents

- A. Independent phase fixture
- B. Lossless power classification
- C. Passivity-violating gain fixture

## iv. References

These are source-neutral regression fixtures for Physlib's normalized-modal-power definitions.
-/

@[expose] public section

namespace Optics

noncomputable section

namespace ReflectionlessTwoPort

/-!

## A. Independent phase fixture

-/

/-- The phase-only right-to-left singleton transmission with coefficient `I`. -/
def reflectionlessTwoPortPhaseRightToLeft : ModeTransform Unit Unit :=
  Complex.I • (1 : ModeTransform Unit Unit)

/-- The independent phase-only left-to-right coefficient `(3 + 4I) / 5`. -/
def reflectionlessTwoPortPhaseLeftToRight : ModeTransform Unit Unit :=
  ((3 + 4 * Complex.I) / 5) • (1 : ModeTransform Unit Unit)

/-- Unequal complex incident amplitudes on the left and right ports. -/
def reflectionlessTwoPortPhaseIncident :
    ModeAmplitude (Incident Unit ⊕ Incident Unit) :=
  WithLp.toLp 2 fun
    | Sum.inl _ => 2 + Complex.I
    | Sum.inr _ => 3 - 2 * Complex.I

/-- The expected output under the two independent phase coefficients. -/
def reflectionlessTwoPortPhaseOutgoing :
    ModeAmplitude (Outgoing Unit ⊕ Outgoing Unit) :=
  WithLp.toLp 2 fun
    | Sum.inl _ => 2 + 3 * Complex.I
    | Sum.inr _ => (2 + 11 * Complex.I) / 5

/-- The right-to-left phase transform multiplies every amplitude by `I`. -/
lemma reflectionlessTwoPortPhaseRightToLeft_apply (amplitude : ModeAmplitude Unit) :
    reflectionlessTwoPortPhaseRightToLeft.toLinearMap amplitude =
      Complex.I • amplitude := by
  apply WithLp.ofLp_injective 2
  funext mode
  rcases mode with ⟨⟩
  simp [reflectionlessTwoPortPhaseRightToLeft]

/-- The left-to-right phase transform multiplies every amplitude by `(3 + 4I) / 5`. -/
lemma reflectionlessTwoPortPhaseLeftToRight_apply (amplitude : ModeAmplitude Unit) :
    reflectionlessTwoPortPhaseLeftToRight.toLinearMap amplitude =
      ((3 + 4 * Complex.I) / 5) • amplitude := by
  apply WithLp.ofLp_injective 2
  funext mode
  rcases mode with ⟨⟩
  simp [reflectionlessTwoPortPhaseLeftToRight]

/-- The independent behavior produces the exact two-phase output. -/
lemma reflectionlessTwoPortPhase_outputMap :
    outputMap reflectionlessTwoPortPhaseRightToLeft
        reflectionlessTwoPortPhaseLeftToRight reflectionlessTwoPortPhaseIncident =
      reflectionlessTwoPortPhaseOutgoing := by
  rw [outputMap_apply, reflectionlessTwoPortPhaseRightToLeft_apply,
    reflectionlessTwoPortPhaseLeftToRight_apply]
  apply WithLp.ofLp_injective 2
  funext endpoint
  rcases endpoint with endpoint | endpoint
  · rcases endpoint with ⟨⟨⟩⟩
    norm_num [reflectionlessTwoPortPhaseIncident, reflectionlessTwoPortPhaseOutgoing,
      ModeAmplitude.directSum]
    calc
      Complex.I * (3 - 2 * Complex.I) =
          3 * Complex.I - 2 * (Complex.I * Complex.I) := by ring
      _ = 2 + 3 * Complex.I := by rw [Complex.I_mul_I]; ring
  · rcases endpoint with ⟨⟨⟩⟩
    norm_num [reflectionlessTwoPortPhaseIncident, reflectionlessTwoPortPhaseOutgoing,
      ModeAmplitude.directSum]
    rw [Complex.ext_iff]
    constructor <;> norm_num

/-- The exact phase fixture belongs directly to its independent behavior. -/
lemma reflectionlessTwoPortPhase_mem :
    (reflectionlessTwoPortPhaseIncident, reflectionlessTwoPortPhaseOutgoing) ∈
      behavior reflectionlessTwoPortPhaseRightToLeft
        reflectionlessTwoPortPhaseLeftToRight := by
  rw [mem_behavior_iff]
  simpa only [outputMap_apply] using reflectionlessTwoPortPhase_outputMap.symm

/-- The two directional phase transforms are not inverse: their composition is not identity. -/
lemma reflectionlessTwoPortPhase_directional_mul_ne_one :
    reflectionlessTwoPortPhaseLeftToRight * reflectionlessTwoPortPhaseRightToLeft ≠
      (1 : ModeTransform Unit Unit) := by
  intro hIdentity
  have hEntry := congrArg (fun transform : ModeTransform Unit Unit => transform () ()) hIdentity
  simp [reflectionlessTwoPortPhaseLeftToRight, reflectionlessTwoPortPhaseRightToLeft,
    Matrix.mul_apply] at hEntry
  have hReal := congrArg Complex.re hEntry
  norm_num at hReal

/-!

## B. Lossless power classification

-/

/-- The right-to-left phase transform preserves normalized modal power. -/
lemma reflectionlessTwoPortPhaseRightToLeft_isPowerPreserving :
    reflectionlessTwoPortPhaseRightToLeft.IsPowerPreserving := by
  intro amplitude
  rw [reflectionlessTwoPortPhaseRightToLeft_apply, ModeAmplitude.power_smul]
  simp

/-- The left-to-right phase transform preserves normalized modal power. -/
lemma reflectionlessTwoPortPhaseLeftToRight_isPowerPreserving :
    reflectionlessTwoPortPhaseLeftToRight.IsPowerPreserving := by
  intro amplitude
  rw [reflectionlessTwoPortPhaseLeftToRight_apply, ModeAmplitude.power_smul]
  have hNorm : Complex.normSq ((3 + 4 * Complex.I) / 5) = 1 := by
    norm_num [Complex.normSq]
  rw [hNorm, one_mul]

/-- The two independent phase directions make the modeled two-port scattering matrix lossless. -/
lemma reflectionlessTwoPortPhase_isLossless :
    (scattering reflectionlessTwoPortPhaseRightToLeft
      reflectionlessTwoPortPhaseLeftToRight).IsLossless :=
  (scattering_isLossless_iff _ _).mpr
    ⟨reflectionlessTwoPortPhaseRightToLeft_isPowerPreserving,
      reflectionlessTwoPortPhaseLeftToRight_isPowerPreserving⟩

/-- The phase fixture's incident normalized modal power is eighteen. -/
lemma reflectionlessTwoPortPhase_incident_power :
    reflectionlessTwoPortPhaseIncident.power = 18 := by
  rw [ModeAmplitude.power_eq_sum_normSq, Fintype.sum_sum_type]
  norm_num [reflectionlessTwoPortPhaseIncident, Complex.normSq]
  have hCard : Fintype.card (Incident Unit) = 1 := by
    simpa using Fintype.card_congr (Incident.channelEquiv : Incident Unit ≃ Unit)
  rw [hCard]
  norm_num

/-- The behavior-level decomposition and phase power preservation give output power eighteen. -/
lemma reflectionlessTwoPortPhase_outgoing_power :
    reflectionlessTwoPortPhaseOutgoing.power = 18 := by
  calc
    reflectionlessTwoPortPhaseOutgoing.power =
        (reflectionlessTwoPortPhaseRightToLeft.toLinearMap
          (ModeAmplitude.reindex Incident.channelEquiv
            reflectionlessTwoPortPhaseIncident.restrictInr)).power +
        (reflectionlessTwoPortPhaseLeftToRight.toLinearMap
          (ModeAmplitude.reindex Incident.channelEquiv
            reflectionlessTwoPortPhaseIncident.restrictInl)).power :=
      behavior_output_power _ _ reflectionlessTwoPortPhase_mem
    _ = (ModeAmplitude.reindex Incident.channelEquiv
            reflectionlessTwoPortPhaseIncident.restrictInr).power +
          (ModeAmplitude.reindex Incident.channelEquiv
            reflectionlessTwoPortPhaseIncident.restrictInl).power := by
      rw [reflectionlessTwoPortPhaseRightToLeft_isPowerPreserving,
        reflectionlessTwoPortPhaseLeftToRight_isPowerPreserving]
    _ = reflectionlessTwoPortPhaseIncident.power := by
      rw [ModeAmplitude.power_reindex, ModeAmplitude.power_reindex, add_comm,
        ← ModeAmplitude.power_directSum]
      exact congrArg ModeAmplitude.power
        (ModeAmplitude.directSum_restrict reflectionlessTwoPortPhaseIncident)
    _ = 18 := reflectionlessTwoPortPhase_incident_power

/-!

## C. Passivity-violating gain fixture

-/

/-- A singleton transform with modal-amplitude gain two. -/
def reflectionlessTwoPortGainTwo : ModeTransform Unit Unit :=
  (2 : ℂ) • (1 : ModeTransform Unit Unit)

/-- The gain-two transform doubles every singleton amplitude. -/
lemma reflectionlessTwoPortGainTwo_apply (amplitude : ModeAmplitude Unit) :
    reflectionlessTwoPortGainTwo.toLinearMap amplitude = (2 : ℂ) • amplitude := by
  apply WithLp.ofLp_injective 2
  funext mode
  rcases mode with ⟨⟩
  simp [reflectionlessTwoPortGainTwo]

/-- The model with modal-amplitude gain two has a concrete input on which output power exceeds
input power, so it is not passive. -/
lemma reflectionlessTwoPortGainTwo_not_isPassive :
    ¬(scattering reflectionlessTwoPortGainTwo
      (1 : ModeTransform Unit Unit)).toModeTransform.IsPassive := by
  intro hPassive
  let pulse : ModeAmplitude Unit := WithLp.toLp 2 fun _ => 1
  have hApplied := hPassive ((0 : ModeAmplitude Unit).directSum pulse)
  rw [power_scattering_toLinearMap_apply, reflectionlessTwoPortGainTwo_apply,
    ModeAmplitude.power_smul, ModeAmplitude.power_directSum] at hApplied
  have hPulse : pulse.power = 1 := by
    rw [ModeAmplitude.power_eq_sum_normSq]
    simp [pulse, Complex.normSq]
  rw [hPulse] at hApplied
  norm_num [ModeAmplitude.power, Complex.normSq] at hApplied

end ReflectionlessTwoPort

end

end Optics
