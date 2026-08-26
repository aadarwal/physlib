/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Components.MatchedPropagationPhysicalPower
public import Physlib.Optics.Components.MatchedPropagationPhysicalRegression
public import Physlib.Optics.Components.MatchedPropagationPowerRegression

/-!
# Physical-port normalized-modal-power regressions for matched propagation

## i. Overview

The exact physical-port fixture has incident and outgoing normalized modal powers `60` and `15`,
so the pinned channel presentation preserves the algebraic quarter-power law. The regression also
transports the passive, non-lossless, and unit-amplitude lossless classification boundaries to the
public physical scattering matrix.

These statements use only Physlib's finite normalized-mode convention. Physical-port ownership
supplies neither an electromagnetic power normalization nor completeness of omitted loss or
radiation channels.

## ii. Key results

- `matchedPropagationPhysicalPowerRegression_behavior_power`: physical-port normalized-modal
  quarter-power law.
- `matchedPropagationPhysicalPowerRegression_not_isLossless`: the half-amplitude physical component
  is not lossless.
- `matchedPropagationPhysicalPowerRegression_unitPhase_isLossless`: the unit-amplitude physical
  component is lossless.
- `matchedPropagationPhysicalPowerRegression_gainTwo_not_isPassive`: an explicit physical pulse
  witnesses gain-two nonpassivity.

## iii. Table of contents

- A. Exact physical-coordinate power
- B. Physical classification boundaries

## iv. References

This is a source-neutral coordinate-invariance regression.

-/

@[expose] public section

namespace Optics

noncomputable section

namespace MatchedPropagation

/-!

## A. Exact physical-coordinate power

-/

/-- The physical incident fixture retains total normalized modal power `60`. -/
lemma matchedPropagationPhysicalPowerRegression_incident_power :
    matchedPropagationPhysicalRegressionIncident.power = 60 := by
  rw [matchedPropagationPhysicalRegressionIncident, ModeAmplitude.power_reindex]
  rw [show matchedPropagationRegressionIncident.power =
      matchedPropagationRegressionIncident.restrictInl.power +
        matchedPropagationRegressionIncident.restrictInr.power by
    rw [← ModeAmplitude.power_directSum, ModeAmplitude.directSum_restrict]]
  rw [← ModeAmplitude.power_reindex Incident.channelEquiv,
    ← ModeAmplitude.power_reindex Incident.channelEquiv,
    ModeAmplitude.power_eq_sum_normSq, ModeAmplitude.power_eq_sum_normSq,
    Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [matchedPropagationRegressionIncident, ModeAmplitude.reindex_apply,
    Incident.channelEquiv_symm_apply]
  norm_num [Complex.normSq]

/-- The physical outgoing fixture retains total normalized modal power `15`. -/
lemma matchedPropagationPhysicalPowerRegression_outgoing_power :
    matchedPropagationPhysicalRegressionOutgoing.power = 15 := by
  rw [matchedPropagationPhysicalRegressionOutgoing, ModeAmplitude.power_reindex]
  rw [show matchedPropagationRegressionOutgoing.power =
      matchedPropagationRegressionOutgoing.restrictInl.power +
        matchedPropagationRegressionOutgoing.restrictInr.power by
    rw [← ModeAmplitude.power_directSum, ModeAmplitude.directSum_restrict]]
  rw [← ModeAmplitude.power_reindex Outgoing.channelEquiv,
    ← ModeAmplitude.power_reindex Outgoing.channelEquiv,
    ModeAmplitude.power_eq_sum_normSq, ModeAmplitude.power_eq_sum_normSq,
    Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [matchedPropagationRegressionOutgoing, ModeAmplitude.reindex_apply,
    Outgoing.channelEquiv_symm_apply]
  norm_num [Complex.normSq]

/-- The independent physical behavior has the exact pinned quarter-power result. -/
lemma matchedPropagationPhysicalPowerRegression_behavior_power :
    matchedPropagationPhysicalRegressionOutgoing.power =
      (1 / 2 : ℝ) ^ 2 * matchedPropagationPhysicalRegressionIncident.power := by
  simpa [matchedPropagationRegressionParameters] using
    physicalBehavior_output_power matchedPropagationRegressionParameters
      matchedPropagationPhysicalRegression_mem

/-!

## B. Physical classification boundaries

-/

/-- The half-amplitude physical scattering component is passive. -/
lemma matchedPropagationPhysicalPowerRegression_isPassive :
    ModeTransform.IsPassive
      (ScatteringMatrix.toModeTransform
        (physicalScattering matchedPropagationRegressionParameters (Fin 2))) :=
  physicalScattering_isPassive matchedPropagationRegressionParameters
    matchedPropagationRegressionParameters_isValid

/-- The concrete half-amplitude physical scattering component is not lossless. -/
lemma matchedPropagationPhysicalPowerRegression_not_isLossless :
    ¬(physicalScattering matchedPropagationRegressionParameters (Fin 2)).IsLossless := by
  intro hLossless
  have hPowerPreserving :=
    (ScatteringMatrix.isLossless_iff_toOrientedModeTransform_isPowerPreserving
      (physicalScattering matchedPropagationRegressionParameters (Fin 2))).mp hLossless
  have hPower := hPowerPreserving matchedPropagationPhysicalRegressionIncident
  rw [matchedPropagationPhysicalRegression_scattering_action,
    matchedPropagationPhysicalPowerRegression_incident_power,
    matchedPropagationPhysicalPowerRegression_outgoing_power] at hPower
  norm_num at hPower

/-- Unit amplitude remains lossless after transport to the owned physical ports. -/
lemma matchedPropagationPhysicalPowerRegression_unitPhase_isLossless :
    (physicalScattering matchedPropagationPowerRegressionUnitPhase Unit).IsLossless := by
  exact physicalScattering_isLossless matchedPropagationPowerRegressionUnitPhase rfl

/-- A unit physical pulse entering from the right port of the gain-two fixture. -/
def matchedPropagationPhysicalPowerRegressionGainTwoInput :
    ModeAmplitude ((portFamily Unit).Channel) :=
  WithLp.toLp 2 fun
    | ⟨Port.left, ()⟩ => 0
    | ⟨Port.right, ()⟩ => 1

/-- The gain-two physical pulse is zero at the left port. -/
lemma matchedPropagationPhysicalPowerRegression_gainTwoInput_left :
    matchedPropagationPhysicalPowerRegressionGainTwoInput ⟨Port.left, ()⟩ = 0 := rfl

/-- The gain-two physical pulse is one at the right port. -/
lemma matchedPropagationPhysicalPowerRegression_gainTwoInput_right :
    matchedPropagationPhysicalPowerRegressionGainTwoInput ⟨Port.right, ()⟩ = 1 := rfl

/-- The explicit physical gain-two pulse has output power four and input power one. -/
lemma matchedPropagationPhysicalPowerRegression_gainTwo_not_isPassive :
    ¬ModeTransform.IsPassive
      (ScatteringMatrix.toModeTransform
        (physicalScattering matchedPropagationPowerRegressionGainTwo Unit)) := by
  intro hPassive
  let pulse : ModeAmplitude Unit := WithLp.toLp 2 fun _ => 1
  have hInput : matchedPropagationPhysicalPowerRegressionGainTwoInput =
      ModeAmplitude.reindex (channelEquiv Unit)
        ((0 : ModeAmplitude Unit).directSum pulse) := by
    apply WithLp.ofLp_injective 2
    funext channel
    rcases channel with ⟨port, ⟨⟩⟩
    cases port <;> rfl
  have hApplied := hPassive matchedPropagationPhysicalPowerRegressionGainTwoInput
  rw [hInput, physicalScattering, ScatteringMatrix.toModeTransform_reindex,
    ModeTransform.toLinearMap_reindex_apply,
    ModeAmplitude.power_reindex, ModeAmplitude.power_reindex,
    power_scattering_toLinearMap_apply, ModeAmplitude.power_directSum] at hApplied
  have hPulse : pulse.power = 1 := by
    rw [ModeAmplitude.power_eq_sum_normSq]
    norm_num [pulse, Complex.normSq]
  rw [hPulse] at hApplied
  norm_num [matchedPropagationPowerRegressionGainTwo, ModeAmplitude.power] at hApplied

end MatchedPropagation

end

end Optics
