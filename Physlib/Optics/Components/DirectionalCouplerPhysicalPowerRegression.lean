/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Components.DirectionalCouplerPhysicalPower
public import Physlib.Optics.Components.DirectionalCouplerPhysicalRegression
public import Physlib.Optics.Components.DirectionalCouplerPowerRegression

/-!
# Physical-port normalized-modal-power regressions for directional coupling

## i. Overview

The four-port presentation of the exact `3–4–5` fixture retains raw input and output normalized
modal power `30`, and its independently transported behavior proves the same equality. A directly
defined unit pulse at `leftFirst` then transports the power-factor-two passivity failure to the
physical scattering matrix.

These statements use only Physlib's finite normalized-mode convention. Physical-port ownership
supplies neither an electromagnetic power normalization nor completeness of omitted loss or
radiation channels.

## ii. Key results

- `directionalCouplerPhysicalPowerRegression_behavior_power`: physical-port normalized-modal-power
  preservation.
- `directionalCouplerPhysicalPowerRegression_isLossless`: the unitary physical fixture is lossless.
- `directionalCouplerPhysicalPowerRegression_gain_not_isPassive`: a physical pulse witnesses
  failure of passivity at power factor two.

## iii. Table of contents

- A. Exact physical-port normalized-modal-power preservation
- B. Physical power-gain witness

## iv. References

This is a source-neutral coordinate-invariance regression.
-/

@[expose] public section

namespace Optics

noncomputable section

namespace DirectionalCoupler

/-! ## A. Exact physical power preservation -/

/-- The physical incident fixture has normalized modal power `30`. -/
lemma directionalCouplerPhysicalPowerRegression_incident_power :
    directionalCouplerPhysicalRegressionIncident.power = 30 := by
  rw [directionalCouplerPhysicalRegressionIncident, ModeAmplitude.power_reindex,
    directionalCouplerPowerRegression_incident_power]

/-- The physical outgoing fixture has normalized modal power `30`. -/
lemma directionalCouplerPhysicalPowerRegression_outgoing_power :
    directionalCouplerPhysicalRegressionOutgoing.power = 30 := by
  rw [directionalCouplerPhysicalRegressionOutgoing, ModeAmplitude.power_reindex,
    directionalCouplerPowerRegression_outgoing_power]

/-- The independently transported physical behavior preserves exact normalized modal power. -/
lemma directionalCouplerPhysicalPowerRegression_behavior_power :
    directionalCouplerPhysicalRegressionOutgoing.power =
      directionalCouplerPhysicalRegressionIncident.power := by
  have hPower := physicalBehavior_output_power directionalCouplerRegressionParameters
    directionalCouplerPhysicalRegression_mem
  rw [Parameters.powerFactor] at hPower
  norm_num [directionalCouplerRegressionParameters] at hPower
  exact hPower

/-- The exact four-port physical scattering fixture is lossless. -/
lemma directionalCouplerPhysicalPowerRegression_isLossless :
    (physicalScattering directionalCouplerRegressionParameters Unit).IsLossless :=
  physicalScattering_isLossless directionalCouplerRegressionParameters
    directionalCouplerPowerRegression_isValid.isUnitary

/-! ## B. Physical power-gain witness -/

/-- A unit physical pulse entering the first arm from the left side. -/
def directionalCouplerPhysicalPowerRegressionGainInput :
    ModeAmplitude ((portFamily Unit).Channel) :=
  WithLp.toLp 2 fun
    | ⟨Port.leftFirst, ()⟩ => 1
    | ⟨Port.leftSecond, ()⟩ => 0
    | ⟨Port.rightFirst, ()⟩ => 0
    | ⟨Port.rightSecond, ()⟩ => 0

/-- The explicit physical pulse is the channel transport of the raw complete input. -/
lemma directionalCouplerPhysicalPowerRegression_gainInput_eq_reindex :
    directionalCouplerPhysicalPowerRegressionGainInput =
      ModeAmplitude.reindex (channelEquiv Unit)
        directionalCouplerPowerRegressionCompleteInput := by
  apply WithLp.ofLp_injective 2
  funext channel
  rcases channel with ⟨port, ⟨⟩⟩
  cases port <;> rfl

/-- The explicit physical gain input has normalized modal power one. -/
lemma directionalCouplerPhysicalPowerRegression_gainInput_power :
    directionalCouplerPhysicalPowerRegressionGainInput.power = 1 := by
  rw [directionalCouplerPhysicalPowerRegression_gainInput_eq_reindex,
    ModeAmplitude.power_reindex, directionalCouplerPowerRegressionCompleteInput,
    ModeAmplitude.power_directSum, directionalCouplerPowerRegression_pulse_power]
  norm_num [ModeAmplitude.power]

/-- The physical gain fixture sends the explicit unit input to output power two. -/
lemma directionalCouplerPhysicalPowerRegression_gainOutput_power :
    (ModeTransform.toLinearMap
      (ScatteringMatrix.toModeTransform
        (physicalScattering directionalCouplerPowerRegressionGain Unit))
      directionalCouplerPhysicalPowerRegressionGainInput).power = 2 := by
  rw [directionalCouplerPhysicalPowerRegression_gainInput_eq_reindex,
    physicalScattering, ScatteringMatrix.toModeTransform_reindex,
    ModeTransform.toLinearMap_reindex_apply, ModeAmplitude.power_reindex,
    directionalCouplerPowerRegressionCompleteInput, scattering_toLinearMap_apply,
    ModeAmplitude.power_directSum, directionalCouplerPowerRegression_mixed_power]
  norm_num [ModeAmplitude.power]

/-- The explicit physical pulse witnesses failure of passivity at power factor two. -/
lemma directionalCouplerPhysicalPowerRegression_gain_not_isPassive :
    ¬ModeTransform.IsPassive
      (ScatteringMatrix.toModeTransform
        (physicalScattering directionalCouplerPowerRegressionGain Unit)) := by
  intro hPassive
  have hApplied := hPassive directionalCouplerPhysicalPowerRegressionGainInput
  rw [directionalCouplerPhysicalPowerRegression_gainOutput_power,
    directionalCouplerPhysicalPowerRegression_gainInput_power] at hApplied
  norm_num at hApplied

end DirectionalCoupler

end

end Optics
