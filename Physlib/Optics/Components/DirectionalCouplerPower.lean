/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Components.DirectionalCoupler
public import Physlib.Optics.Components.ReflectionlessTwoPortPower

/-!
# Modal power for the algebraic directional coupler

## i. Overview

This file proves the exact normalized-modal-power law of the real-quadrature mixer. The sum of its
two output modal powers is `t² + k²` times the summed input modal power; the cross terms cancel
because the declared cross coefficient is `-I * k`. Consequently `t² + k² ≤ 1` gives passivity
and equality to one gives power preservation and losslessness of the modeled reflectionless
scattering matrix.

`Parameters.IsValid` additionally chooses nonnegative through and cross amplitudes. Those signs
are a canonical parameter convention, not a mathematical requirement for unitarity. These remain
normalized finite-mode statements, with no electromagnetic normalization, reciprocity, material,
bandwidth, delay, or omitted-channel completeness claim.

## ii. Key results

- `DirectionalCoupler.power_mixing_toLinearMap_apply`: exact mixer power scaling.
- `DirectionalCoupler.behavior_output_power`: specification-level component power scaling.
- `DirectionalCoupler.scattering_isPassive`: power-bounded parameters imply passivity.
- `DirectionalCoupler.scattering_isLossless`: unitary parameters imply losslessness.

## iii. Table of contents

- A. Power constraints and the two-coordinate identity
- B. Mixer and component power classification

## iv. References

These normalized-modal-power results are Physlib-original and source-neutral.
-/

@[expose] public section

namespace Optics

noncomputable section

namespace DirectionalCoupler

/-!
## A. Power constraints and the two-coordinate identity
-/

/-- The common normalized-modal-power factor `t² + k²` of the two-arm mixer. -/
def Parameters.powerFactor (p : Parameters) : ℝ :=
  p.throughAmplitude ^ 2 + p.crossAmplitude ^ 2

/-- The coupler parameters do not amplify normalized modal power. -/
def Parameters.IsPowerBounded (p : Parameters) : Prop :=
  p.powerFactor ≤ 1

/-- The two-arm mixing parameters satisfy the exact unitary normalization. -/
def Parameters.IsUnitary (p : Parameters) : Prop :=
  p.powerFactor = 1

/-- Canonical ideal-coupler parameters use nonnegative amplitudes and unitary normalization. -/
def Parameters.IsValid (p : Parameters) : Prop :=
  0 ≤ p.throughAmplitude ∧ 0 ≤ p.crossAmplitude ∧ p.IsUnitary

/-- Valid ideal-coupler parameters satisfy the unitary normalization. -/
lemma Parameters.IsValid.isUnitary {p : Parameters} (hp : p.IsValid) : p.IsUnitary :=
  hp.2.2

/-- Unitary parameters are power-bounded. -/
lemma Parameters.IsUnitary.isPowerBounded {p : Parameters} (hp : p.IsUnitary) :
    p.IsPowerBounded := by
  rw [Parameters.IsPowerBounded, hp]

/-- The quadrature cross terms cancel in the squared moduli of the two mixed coordinates. -/
lemma normSq_mixing_pair (p : Parameters) (first second : ℂ) :
    Complex.normSq ((p.throughAmplitude : ℂ) * first + crossCoefficient p * second) +
        Complex.normSq (crossCoefficient p * first +
          (p.throughAmplitude : ℂ) * second) =
      p.powerFactor * (Complex.normSq first + Complex.normSq second) := by
  simp [crossCoefficient, Parameters.powerFactor, Complex.normSq_apply]
  ring

/-!
## B. Mixer and component power classification
-/

/-- The two-arm mixer scales total normalized modal power by exactly `t² + k²`. -/
lemma power_mixing_toLinearMap_apply [Fintype ι] [DecidableEq ι] (p : Parameters)
    (input : ModeAmplitude (ι ⊕ ι)) :
    ((mixing p ι).toLinearMap input).power = p.powerFactor * input.power := by
  let first := input.restrictInl
  let second := input.restrictInr
  calc
    ((mixing p ι).toLinearMap input).power =
        (((p.throughAmplitude : ℂ) • first + crossCoefficient p • second).power +
          (crossCoefficient p • first +
            (p.throughAmplitude : ℂ) • second).power) := by
      rw [mixing_toLinearMap_apply, ModeAmplitude.power_directSum]
    _ = p.powerFactor * (first.power + second.power) := by
      simp only [ModeAmplitude.power_eq_sum_normSq]
      change
        (∑ i, Complex.normSq
          ((p.throughAmplitude : ℂ) * first i + crossCoefficient p * second i)) +
            (∑ i, Complex.normSq
              (crossCoefficient p * first i +
                (p.throughAmplitude : ℂ) * second i)) =
          p.powerFactor *
            ((∑ i, Complex.normSq (first i)) + ∑ i, Complex.normSq (second i))
      rw [← Finset.sum_add_distrib]
      simp_rw [normSq_mixing_pair]
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ = p.powerFactor * input.power := by
      congr 1
      rw [← ModeAmplitude.power_directSum]
      exact congrArg ModeAmplitude.power (ModeAmplitude.directSum_restrict input)

/-- Every state in the independent coupler behavior obeys the exact power-factor law. -/
lemma behavior_output_power [Fintype ι] [DecidableEq ι] (p : Parameters)
    {incident : ModeAmplitude (Incident (ι ⊕ ι) ⊕ Incident (ι ⊕ ι))}
    {outgoing : ModeAmplitude (Outgoing (ι ⊕ ι) ⊕ Outgoing (ι ⊕ ι))}
    (hMember : (incident, outgoing) ∈ behavior p) :
    outgoing.power = p.powerFactor * incident.power := by
  have hPower := ReflectionlessTwoPort.behavior_output_power
    (mixing p ι) (mixing p ι) hMember
  rw [power_mixing_toLinearMap_apply, power_mixing_toLinearMap_apply] at hPower
  rw [hPower, ModeAmplitude.power_reindex, ModeAmplitude.power_reindex]
  calc
    p.powerFactor * incident.restrictInr.power +
        p.powerFactor * incident.restrictInl.power =
      p.powerFactor * (incident.restrictInl.power + incident.restrictInr.power) := by ring
    _ = p.powerFactor * incident.power := by
      congr 1
      rw [← ModeAmplitude.power_directSum]
      exact congrArg ModeAmplitude.power (ModeAmplitude.directSum_restrict incident)

/-- Power-bounded parameters make the two-arm mixer passive. -/
lemma mixing_isPassive [Fintype ι] [DecidableEq ι] (p : Parameters)
    (hp : p.IsPowerBounded) : (mixing p ι).IsPassive := by
  intro input
  rw [power_mixing_toLinearMap_apply]
  change p.powerFactor ≤ 1 at hp
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right hp (ModeAmplitude.power_nonneg input)

/-- Unitary parameters make the two-arm mixer power-preserving. -/
lemma mixing_isPowerPreserving [Fintype ι] [DecidableEq ι] (p : Parameters)
    (hp : p.IsUnitary) : (mixing p ι).IsPowerPreserving := by
  intro input
  rw [power_mixing_toLinearMap_apply, hp, one_mul]

/-- Power-bounded parameters make the complete reflectionless coupler scattering law passive. -/
lemma scattering_isPassive [Fintype ι] [DecidableEq ι] (p : Parameters)
    (hp : p.IsPowerBounded) : (scattering p ι).toModeTransform.IsPassive :=
  ReflectionlessTwoPort.scattering_isPassive
    (mixing_isPassive p hp) (mixing_isPassive p hp)

/-- Unitary parameters make the complete reflectionless coupler scattering law lossless. -/
lemma scattering_isLossless [Fintype ι] [DecidableEq ι] (p : Parameters)
    (hp : p.IsUnitary) : (scattering p ι).IsLossless :=
  ReflectionlessTwoPort.scattering_isLossless
    (mixing_isPowerPreserving p hp) (mixing_isPowerPreserving p hp)

end DirectionalCoupler

end

end Optics
