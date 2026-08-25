/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Components.MatchedPropagationPower
public import Physlib.Optics.Components.MatchedPropagationRegression

/-!
# Regression tests for matched-propagation modal power

## i. Overview

The half-amplitude, quarter-turn fixture is evaluated on a singleton mode from each side. Its
incident normalized modal power is `60`, while its output power is `15`. Thus the fixture pins the
distinction between amplitude transmission `1 / 2` and retained power `1 / 4` independently of the
generic classification proof.

The exact state is checked against the independent behavior. A concrete mismatch rules out
losslessness. The generic classifier covers every phase; this regression exercises a nonzero
quarter-turn phase. Amplitude gain two is outside the validity domain and violates passivity.

## ii. Key results

- `matchedPropagationPowerRegression_behavior_power`: behavior-level quarter-power law.
- `matchedPropagationPowerRegression_not_isLossless`: explicit losslessness failure.
- `matchedPropagationPowerRegression_unitPhase_isLossless`: the unit-amplitude quarter-turn
  fixture is lossless.

## iii. Table of contents

- A. Half-amplitude power fixture
- B. Classification boundaries

## iv. References

This is an exact source-neutral regression for normalized modal power.
-/

@[expose] public section

namespace Optics

noncomputable section

namespace MatchedPropagation

/-!

## A. Half-amplitude power fixture

-/

/-- The left incident singleton amplitude, with power `20`. -/
def matchedPropagationPowerRegressionLeft : ModeAmplitude Unit :=
  WithLp.toLp 2 fun _ => 2 + 4 * Complex.I

/-- The right incident singleton amplitude, with power `40`. -/
def matchedPropagationPowerRegressionRight : ModeAmplitude Unit :=
  WithLp.toLp 2 fun _ => 6 - 2 * Complex.I

/-- The left outgoing singleton amplitude after multiplication by `-I / 2`. -/
def matchedPropagationPowerRegressionLeftOutgoing : ModeAmplitude Unit :=
  WithLp.toLp 2 fun _ => -1 - 3 * Complex.I

/-- The right outgoing singleton amplitude after multiplication by `-I / 2`. -/
def matchedPropagationPowerRegressionRightOutgoing : ModeAmplitude Unit :=
  WithLp.toLp 2 fun _ => 2 - Complex.I

/-- The typed incident state assembled from the two raw side amplitudes. -/
def matchedPropagationPowerRegressionIncident :
    ModeAmplitude (Incident Unit ⊕ Incident Unit) :=
  (ModeAmplitude.reindex Incident.channelEquiv.symm
    matchedPropagationPowerRegressionLeft).directSum
  (ModeAmplitude.reindex Incident.channelEquiv.symm
    matchedPropagationPowerRegressionRight)

/-- The typed outgoing state assembled from the two exact transmitted amplitudes. -/
def matchedPropagationPowerRegressionOutgoing :
    ModeAmplitude (Outgoing Unit ⊕ Outgoing Unit) :=
  (ModeAmplitude.reindex Outgoing.channelEquiv.symm
    matchedPropagationPowerRegressionLeftOutgoing).directSum
  (ModeAmplitude.reindex Outgoing.channelEquiv.symm
    matchedPropagationPowerRegressionRightOutgoing)

/-- The exact singleton state belongs directly to the independent behavior. -/
lemma matchedPropagationPowerRegression_mem :
    (matchedPropagationPowerRegressionIncident,
      matchedPropagationPowerRegressionOutgoing) ∈
        behavior matchedPropagationRegressionParameters := by
  rw [mem_behavior_iff, matchedPropagationRegression_transmissionCoefficient]
  apply WithLp.ofLp_injective 2
  funext endpoint
  rcases endpoint with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;>
    norm_num [matchedPropagationPowerRegressionIncident,
      matchedPropagationPowerRegressionOutgoing, matchedPropagationPowerRegressionLeft,
      matchedPropagationPowerRegressionRight, matchedPropagationPowerRegressionLeftOutgoing,
      matchedPropagationPowerRegressionRightOutgoing, ModeAmplitude.directSum] <;>
    apply Complex.ext <;> norm_num

/-- Total incident normalized modal power is `60`. -/
lemma matchedPropagationPowerRegression_incident_power :
    matchedPropagationPowerRegressionIncident.power = 60 := by
  rw [matchedPropagationPowerRegressionIncident, ModeAmplitude.power_directSum,
    ModeAmplitude.power_reindex, ModeAmplitude.power_reindex]
  rw [ModeAmplitude.power_eq_sum_normSq, ModeAmplitude.power_eq_sum_normSq]
  norm_num [matchedPropagationPowerRegressionLeft, matchedPropagationPowerRegressionRight,
    Complex.normSq]

/-- Total outgoing normalized modal power is `15`, one quarter of the input. -/
lemma matchedPropagationPowerRegression_outgoing_power :
    matchedPropagationPowerRegressionOutgoing.power = 15 := by
  rw [matchedPropagationPowerRegressionOutgoing, ModeAmplitude.power_directSum,
    ModeAmplitude.power_reindex, ModeAmplitude.power_reindex]
  rw [ModeAmplitude.power_eq_sum_normSq, ModeAmplitude.power_eq_sum_normSq]
  norm_num [matchedPropagationPowerRegressionLeftOutgoing,
    matchedPropagationPowerRegressionRightOutgoing, Complex.normSq]

/-- The independent behavior's exact power law gives the pinned quarter-power result. -/
lemma matchedPropagationPowerRegression_behavior_power :
    matchedPropagationPowerRegressionOutgoing.power =
      (1 / 2 : ℝ) ^ 2 * matchedPropagationPowerRegressionIncident.power := by
  simpa [matchedPropagationRegressionParameters] using
    behavior_output_power matchedPropagationRegressionParameters
      matchedPropagationPowerRegression_mem

/-- The realized scattering component is passive under the fixture's valid parameters. -/
lemma matchedPropagationPowerRegression_isPassive :
    (scattering matchedPropagationRegressionParameters (Fin 2)).toModeTransform.IsPassive :=
  scattering_isPassive matchedPropagationRegressionParameters
    matchedPropagationRegressionParameters_isValid

/-- The concrete `60` to `15` power loss rules out modal losslessness. -/
lemma matchedPropagationPowerRegression_not_isLossless :
    ¬(scattering matchedPropagationRegressionParameters Unit).IsLossless := by
  intro hLossless
  have hPower := hLossless.isPowerPreserving
    (matchedPropagationPowerRegressionLeft.directSum
      matchedPropagationPowerRegressionRight)
  rw [power_scattering_toLinearMap_apply, ModeAmplitude.power_directSum,
    ModeAmplitude.power_eq_sum_normSq, ModeAmplitude.power_eq_sum_normSq] at hPower
  norm_num [matchedPropagationRegressionParameters, matchedPropagationPowerRegressionLeft,
    matchedPropagationPowerRegressionRight, Complex.normSq] at hPower

/-!

## B. Classification boundaries

-/

/-- Unit amplitude with a positive quarter-turn carrier phase. -/
def matchedPropagationPowerRegressionUnitPhase : Parameters where
  amplitudeTransmission := 1
  carrierPathPhase := ((Real.pi / 2 : ℝ) : Real.Angle)

/-- Unit amplitude transmission is lossless despite its nonzero carrier path phase. -/
lemma matchedPropagationPowerRegression_unitPhase_isLossless :
    (scattering matchedPropagationPowerRegressionUnitPhase Unit).IsLossless := by
  exact scattering_isLossless matchedPropagationPowerRegressionUnitPhase rfl

/-- Amplitude gain two at zero carrier phase. -/
def matchedPropagationPowerRegressionGainTwo : Parameters where
  amplitudeTransmission := 2
  carrierPathPhase := 0

/-- Gain two is outside the reduced component's passive parameter domain. -/
lemma matchedPropagationPowerRegression_gainTwo_not_isValid :
    ¬matchedPropagationPowerRegressionGainTwo.IsValid := by
  norm_num [matchedPropagationPowerRegressionGainTwo, Parameters.IsValid]

/-- Gain two has a concrete singleton input on which output power exceeds input power. -/
lemma matchedPropagationPowerRegression_gainTwo_not_isPassive :
    ¬(scattering matchedPropagationPowerRegressionGainTwo Unit).toModeTransform.IsPassive := by
  intro hPassive
  let pulse : ModeAmplitude Unit := WithLp.toLp 2 fun _ => 1
  have hApplied := hPassive ((0 : ModeAmplitude Unit).directSum pulse)
  rw [power_scattering_toLinearMap_apply, ModeAmplitude.power_directSum] at hApplied
  have hPulse : pulse.power = 1 := by
    rw [ModeAmplitude.power_eq_sum_normSq]
    norm_num [pulse, Complex.normSq]
  rw [hPulse] at hApplied
  norm_num [matchedPropagationPowerRegressionGainTwo, ModeAmplitude.power] at hApplied

end MatchedPropagation

end

end Optics
