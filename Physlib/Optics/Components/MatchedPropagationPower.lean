/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Components.MatchedPropagation
public import Physlib.Optics.Components.ReflectionlessTwoPortPower

/-!
# Modal-power classification of fixed-carrier matched propagation

## i. Overview

This file proves the exact normalized-modal-power law for `MatchedPropagation`. If the retained
amplitude factor is `a`, output power is `a²` times incident power; the carrier path phase has unit
modulus and drops out. The result is first proved for the independently stated behavior and then
for its scattering realization.

A valid parameter pair, with `0 ≤ a ≤ 1`, gives a passive modeled scattering component. Unit
amplitude transmission gives a lossless one. These classifications concern only the complete
finite channel family declared by this model and Physlib's normalized modal power. They do not
establish electromagnetic normalization, material absorption, impedance matching, reciprocity,
or completeness of physical loss channels.

## ii. Key results

- `MatchedPropagation.normSq_transmissionCoefficient`: the coefficient norm square is `a²`.
- `MatchedPropagation.behavior_output_power`: specification-level power scaling.
- `MatchedPropagation.power_scattering_toLinearMap_apply`: realized power scaling.
- `MatchedPropagation.scattering_isPassive`: validity implies modal passivity.
- `MatchedPropagation.scattering_isLossless`: unit amplitude implies modal losslessness.

## iii. Table of contents

- A. Coefficient and scalar-transform power
- B. Behavior and scattering power
- C. Passivity and losslessness

## iv. References

These modal-power results are Physlib-original and source-neutral.
-/

@[expose] public section

namespace Optics

noncomputable section

universe u

namespace MatchedPropagation

/-!

## A. Coefficient and scalar-transform power

-/

/-- The fixed-carrier phase factor has unit squared modulus. -/
lemma normSq_carrierPhaseFactor (phase : Real.Angle) :
    Complex.normSq (carrierPhaseFactor phase) = 1 := by
  simp [carrierPhaseFactor]

/-- The squared modulus of the transmission coefficient is the square of its real amplitude
factor. -/
lemma normSq_transmissionCoefficient (p : Parameters) :
    Complex.normSq (transmissionCoefficient p) = p.amplitudeTransmission ^ 2 := by
  rw [transmissionCoefficient, Complex.normSq_mul, Complex.normSq_ofReal,
    normSq_carrierPhaseFactor]
  ring

/-- Scalar transmission scales normalized modal power by the squared amplitude factor. -/
lemma power_transmission_toLinearMap_apply [Fintype ι] [DecidableEq ι] (p : Parameters)
    (amplitude : ModeAmplitude ι) :
    ((transmission p ι).toLinearMap amplitude).power =
      p.amplitudeTransmission ^ 2 * amplitude.power := by
  rw [transmission_toLinearMap_apply, ModeAmplitude.power_smul,
    normSq_transmissionCoefficient]

/-!

## B. Behavior and scattering power

-/

/-- Every state in the independent behavior has output power equal to `a²` times its incident
power. -/
lemma behavior_output_power [Fintype ι] [DecidableEq ι] (p : Parameters)
    {incident : ModeAmplitude (Incident ι ⊕ Incident ι)}
    {outgoing : ModeAmplitude (Outgoing ι ⊕ Outgoing ι)}
    (hMember : (incident, outgoing) ∈ behavior p) :
    outgoing.power = p.amplitudeTransmission ^ 2 * incident.power := by
  change (incident, outgoing) ∈
    ReflectionlessTwoPort.behavior (transmission p ι) (transmission p ι) at hMember
  have hPower := ReflectionlessTwoPort.behavior_output_power
    (transmission p ι) (transmission p ι) hMember
  rw [power_transmission_toLinearMap_apply,
    power_transmission_toLinearMap_apply] at hPower
  have hIncident :
      (ModeAmplitude.reindex Incident.channelEquiv incident.restrictInl).power +
          (ModeAmplitude.reindex Incident.channelEquiv incident.restrictInr).power =
        incident.power := by
    rw [ModeAmplitude.power_reindex, ModeAmplitude.power_reindex,
      ← ModeAmplitude.power_directSum]
    exact congrArg ModeAmplitude.power (ModeAmplitude.directSum_restrict incident)
  rw [hPower, ← hIncident]
  ring

/-- The realized scattering action scales total normalized modal power by `a²`. -/
lemma power_scattering_toLinearMap_apply [Fintype ι] [DecidableEq ι] (p : Parameters)
    (left right : ModeAmplitude ι) :
    ((scattering p ι).toModeTransform.toLinearMap (left.directSum right)).power =
      p.amplitudeTransmission ^ 2 * (left.power + right.power) := by
  rw [scattering_toLinearMap_apply, ModeAmplitude.power_directSum,
    ModeAmplitude.power_smul, ModeAmplitude.power_smul,
    normSq_transmissionCoefficient]
  ring

/-!

## C. Passivity and losslessness

-/

/-- A valid amplitude factor makes the scalar directional transmission passive. -/
lemma transmission_isPassive [Fintype ι] [DecidableEq ι] (p : Parameters)
    (hp : p.IsValid) : (transmission p ι).IsPassive := by
  intro amplitude
  rw [power_transmission_toLinearMap_apply]
  have hsq : p.amplitudeTransmission ^ 2 ≤ 1 := by
    nlinarith [hp.1, hp.2]
  nlinarith [ModeAmplitude.power_nonneg amplitude]

/-- Unit amplitude transmission makes the scalar directional transform power-preserving. -/
lemma transmission_isPowerPreserving [Fintype ι] [DecidableEq ι] (p : Parameters)
    (hUnit : p.amplitudeTransmission = 1) :
    (transmission p ι).IsPowerPreserving := by
  intro amplitude
  rw [power_transmission_toLinearMap_apply, hUnit]
  norm_num

/-- A valid fixed-carrier matched-propagation component is passive in normalized modal power. -/
lemma scattering_isPassive [Fintype ι] [DecidableEq ι] (p : Parameters)
    (hp : p.IsValid) : (scattering p ι).toModeTransform.IsPassive := by
  exact ReflectionlessTwoPort.scattering_isPassive
    (transmission_isPassive p hp) (transmission_isPassive p hp)

/-- Unit amplitude transmission makes the fixed-carrier matched-propagation scattering matrix
lossless in normalized modal power. -/
lemma scattering_isLossless [Fintype ι] [DecidableEq ι] (p : Parameters)
    (hUnit : p.amplitudeTransmission = 1) : (scattering p ι).IsLossless := by
  exact ReflectionlessTwoPort.scattering_isLossless
    (transmission_isPowerPreserving p hUnit) (transmission_isPowerPreserving p hUnit)

end MatchedPropagation

end

end Optics
