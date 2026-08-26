/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Components.DirectionalCouplerPower
public import Physlib.Optics.Components.DirectionalCouplerRegression

/-!
# Regression tests for directional-coupler modal power

## i. Overview

The exact `3–4–5` fixture has unit power factor and preserves the independently computed input
power `30`. A second fixture with through and cross amplitudes both one has power factor two; a
concrete complete scattering input then produces output power two from input power one. Together
these tests pin both the unitary boundary and a genuine component-level passivity failure.

## ii. Key results

- `directionalCouplerPowerRegression_isValid`: the exact `3–4–5` parameters are canonical.
- `directionalCouplerPowerRegression_behavior_power`: exact behavior-level power preservation.
- `directionalCouplerPowerRegression_isLossless`: the modeled two-port scattering matrix is
  lossless.
- `directionalCouplerPowerRegression_gain_not_isPassive`: an explicit full input violates
  passivity at power factor two.

## iii. Table of contents

- A. Unitary `3–4–5` fixture
- B. Power-gain hostile fixture

## iv. References

This is an exact source-neutral regression for normalized modal power.
-/

@[expose] public section

namespace Optics

noncomputable section

namespace DirectionalCoupler

/-!
## A. Unitary `3–4–5` fixture
-/

/-- The exact coupler parameters satisfy the canonical ideal-coupler predicate. -/
lemma directionalCouplerPowerRegression_isValid :
    directionalCouplerRegressionParameters.IsValid := by
  constructor
  · norm_num [directionalCouplerRegressionParameters]
  · constructor
    · norm_num [directionalCouplerRegressionParameters]
    · norm_num [Parameters.IsUnitary, Parameters.powerFactor,
        directionalCouplerRegressionParameters]

/-- The exact incident fixture has normalized modal power `30`. -/
lemma directionalCouplerPowerRegression_incident_power :
    directionalCouplerRegressionIncident.power = 30 := by
  rw [show directionalCouplerRegressionIncident.power =
      directionalCouplerRegressionIncident.restrictInl.power +
        directionalCouplerRegressionIncident.restrictInr.power by
    rw [← ModeAmplitude.power_directSum, ModeAmplitude.directSum_restrict]]
  rw [← ModeAmplitude.power_reindex Incident.channelEquiv,
    ← ModeAmplitude.power_reindex Incident.channelEquiv,
    ModeAmplitude.power_eq_sum_normSq, ModeAmplitude.power_eq_sum_normSq,
    Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [directionalCouplerRegressionIncident, ModeAmplitude.reindex_apply,
    Incident.channelEquiv_symm_apply]
  norm_num [Complex.normSq]

/-- The exact outgoing fixture also has normalized modal power `30`. -/
lemma directionalCouplerPowerRegression_outgoing_power :
    directionalCouplerRegressionOutgoing.power = 30 := by
  rw [show directionalCouplerRegressionOutgoing.power =
      directionalCouplerRegressionOutgoing.restrictInl.power +
        directionalCouplerRegressionOutgoing.restrictInr.power by
    rw [← ModeAmplitude.power_directSum, ModeAmplitude.directSum_restrict]]
  rw [← ModeAmplitude.power_reindex Outgoing.channelEquiv,
    ← ModeAmplitude.power_reindex Outgoing.channelEquiv,
    ModeAmplitude.power_eq_sum_normSq, ModeAmplitude.power_eq_sum_normSq,
    Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [directionalCouplerRegressionOutgoing, ModeAmplitude.reindex_apply,
    Outgoing.channelEquiv_symm_apply]
  norm_num [Complex.normSq]

/-- The independent behavior-level identity gives exact power preservation. -/
lemma directionalCouplerPowerRegression_behavior_power :
    directionalCouplerRegressionOutgoing.power =
      directionalCouplerRegressionIncident.power := by
  have hPower := behavior_output_power directionalCouplerRegressionParameters
    directionalCouplerRegression_mem
  rw [Parameters.powerFactor] at hPower
  norm_num [directionalCouplerRegressionParameters] at hPower
  exact hPower

/-- The exact unitary fixture gives a lossless modeled two-port scattering matrix. -/
lemma directionalCouplerPowerRegression_isLossless :
    (scattering directionalCouplerRegressionParameters Unit).IsLossless :=
  scattering_isLossless directionalCouplerRegressionParameters
    directionalCouplerPowerRegression_isValid.isUnitary

/-!
## B. Power-gain hostile fixture
-/

/-- Through and cross amplitudes both one give power factor two. -/
def directionalCouplerPowerRegressionGain : Parameters where
  throughAmplitude := 1
  crossAmplitude := 1

/-- The gain fixture is not power-bounded. -/
lemma directionalCouplerPowerRegression_gain_not_isPowerBounded :
    ¬directionalCouplerPowerRegressionGain.IsPowerBounded := by
  norm_num [Parameters.IsPowerBounded, Parameters.powerFactor,
    directionalCouplerPowerRegressionGain]

/-- A unit pulse on the first arm and zero on the second. -/
def directionalCouplerPowerRegressionPulse : ModeAmplitude (Unit ⊕ Unit) :=
  WithLp.toLp 2 fun
    | Sum.inl () => 1
    | Sum.inr () => 0

/-- The hostile pulse has input power one. -/
lemma directionalCouplerPowerRegression_pulse_power :
    directionalCouplerPowerRegressionPulse.power = 1 := by
  rw [ModeAmplitude.power_eq_sum_normSq, Fintype.sum_sum_type]
  norm_num [directionalCouplerPowerRegressionPulse, Complex.normSq]

/-- The independently specified mixer output for the gain-two pulse. -/
def directionalCouplerPowerRegressionMixedPulse : ModeAmplitude (Unit ⊕ Unit) :=
  WithLp.toLp 2 fun
    | Sum.inl () => 1
    | Sum.inr () => -Complex.I

/-- Direct mixer evaluation sends the gain-two pulse to `(1, -I)`. -/
lemma directionalCouplerPowerRegression_mixing_action :
    (mixing directionalCouplerPowerRegressionGain Unit).toLinearMap
        directionalCouplerPowerRegressionPulse =
      directionalCouplerPowerRegressionMixedPulse := by
  rw [mixing_toLinearMap_apply]
  apply WithLp.ofLp_injective 2
  funext channel
  rcases channel with ⟨⟩ | ⟨⟩ <;>
    norm_num [directionalCouplerPowerRegressionGain,
      directionalCouplerPowerRegressionPulse,
      directionalCouplerPowerRegressionMixedPulse, crossCoefficient,
      ModeAmplitude.directSum]

/-- The independently evaluated gain output has power two. -/
lemma directionalCouplerPowerRegression_mixed_power :
    ((mixing directionalCouplerPowerRegressionGain Unit).toLinearMap
      directionalCouplerPowerRegressionPulse).power = 2 := by
  rw [directionalCouplerPowerRegression_mixing_action,
    ModeAmplitude.power_eq_sum_normSq, Fintype.sum_sum_type]
  norm_num [directionalCouplerPowerRegressionMixedPulse, Complex.normSq]

/-- A complete scattering input with only the left-side pulse has total power one. -/
def directionalCouplerPowerRegressionCompleteInput :
    ModeAmplitude ((Unit ⊕ Unit) ⊕ (Unit ⊕ Unit)) :=
  directionalCouplerPowerRegressionPulse.directSum 0

/-- The complete scattering input has total normalized modal power one. -/
lemma directionalCouplerPowerRegression_completeInput_power :
    directionalCouplerPowerRegressionCompleteInput.power = 1 := by
  rw [directionalCouplerPowerRegressionCompleteInput, ModeAmplitude.power_directSum,
    directionalCouplerPowerRegression_pulse_power]
  norm_num [ModeAmplitude.power]

/-- The modeled scattering matrix sends the complete unit input to output power two. -/
lemma directionalCouplerPowerRegression_scatteringOutput_power :
    ((scattering directionalCouplerPowerRegressionGain Unit).toModeTransform.toLinearMap
      directionalCouplerPowerRegressionCompleteInput).power = 2 := by
  rw [directionalCouplerPowerRegressionCompleteInput, scattering_toLinearMap_apply,
    ModeAmplitude.power_directSum, directionalCouplerPowerRegression_mixed_power]
  norm_num [ModeAmplitude.power]

/-- The explicit full scattering input witnesses failure of passivity at power factor two. -/
lemma directionalCouplerPowerRegression_gain_not_isPassive :
    ¬(scattering directionalCouplerPowerRegressionGain Unit).toModeTransform.IsPassive := by
  intro hPassive
  have hApplied := hPassive directionalCouplerPowerRegressionCompleteInput
  rw [directionalCouplerPowerRegression_scatteringOutput_power,
    directionalCouplerPowerRegression_completeInput_power] at hApplied
  norm_num at hApplied

end DirectionalCoupler

end

end Optics
