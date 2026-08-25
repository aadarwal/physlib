/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Components.ReflectionlessTwoPort

/-!
# Modal-power classification of reflectionless two-ports

## i. Overview

This file classifies the algebraic reflectionless two-port constructor using the normalized modal
power from `Mode.Basic`. It first derives the exact output-power decomposition from the independent
behavior. It then proves that the realized scattering matrix is passive, respectively lossless,
exactly when both declared directional transmissions are passive, respectively power-preserving.

These are modal statements for the modeled channel families. They do not prove electromagnetic
normalization, impedance matching, reciprocity, material realization, or completeness of physical
loss channels.

## ii. Key results

- `ReflectionlessTwoPort.behavior_output_power`: exact specification-level power decomposition.
- `ReflectionlessTwoPort.power_scattering_toLinearMap_apply`: realized power decomposition.
- `ReflectionlessTwoPort.scattering_isPassive_iff`: exact passivity classification.
- `ReflectionlessTwoPort.scattering_isLossless_iff`: exact losslessness classification.

## iii. Table of contents

- A. Output-power decomposition
- B. Passivity and losslessness

## iv. References

These modal-power classifications are Physlib-original and source-neutral.
-/

@[expose] public section

namespace Optics

noncomputable section

universe u v

namespace ReflectionlessTwoPort

variable {ι : Type u} {κ : Type v}

/-!

## A. Output-power decomposition

-/

/-- The independent behavior's output power is the sum of its two transmitted powers. -/
lemma behavior_output_power [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (rightToLeft : ModeTransform κ ι)
    (leftToRight : ModeTransform ι κ)
    {incident : ModeAmplitude (Incident ι ⊕ Incident κ)}
    {outgoing : ModeAmplitude (Outgoing ι ⊕ Outgoing κ)}
    (hMember : (incident, outgoing) ∈ behavior rightToLeft leftToRight) :
    outgoing.power =
      (rightToLeft.toLinearMap
          (ModeAmplitude.reindex Incident.channelEquiv incident.restrictInr)).power +
        (leftToRight.toLinearMap
          (ModeAmplitude.reindex Incident.channelEquiv incident.restrictInl)).power := by
  rw [mem_behavior_iff] at hMember
  rw [hMember, ModeAmplitude.power_directSum, ModeAmplitude.power_reindex,
    ModeAmplitude.power_reindex]

/-- The realized output power is the sum of the two directional transmitted powers. -/
lemma power_scattering_toLinearMap_apply [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (rightToLeft : ModeTransform κ ι)
    (leftToRight : ModeTransform ι κ) (left : ModeAmplitude ι)
    (right : ModeAmplitude κ) :
    ((scattering rightToLeft leftToRight).toModeTransform.toLinearMap
        (left.directSum right)).power =
      (rightToLeft.toLinearMap right).power +
        (leftToRight.toLinearMap left).power := by
  rw [scattering_toLinearMap_apply, ModeAmplitude.power_directSum]

/-!

## B. Passivity and losslessness

-/

/-- Passive directional transmissions realize a passive reflectionless component. -/
lemma scattering_isPassive [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] {rightToLeft : ModeTransform κ ι}
    {leftToRight : ModeTransform ι κ} (hRightToLeft : rightToLeft.IsPassive)
    (hLeftToRight : leftToRight.IsPassive) :
    (scattering rightToLeft leftToRight).toModeTransform.IsPassive := by
  intro input
  let left := input.restrictInl
  let right := input.restrictInr
  calc
    ((scattering rightToLeft leftToRight).toModeTransform.toLinearMap input).power =
        (rightToLeft.toLinearMap right).power +
          (leftToRight.toLinearMap left).power := by
      rw [show input = left.directSum right by
        change input = input.restrictInl.directSum input.restrictInr
        exact (ModeAmplitude.directSum_restrict input).symm]
      exact power_scattering_toLinearMap_apply rightToLeft leftToRight left right
    _ ≤ right.power + left.power :=
      add_le_add (hRightToLeft right) (hLeftToRight left)
    _ = left.power + right.power := add_comm _ _
    _ = input.power := by
      rw [← ModeAmplitude.power_directSum]
      change (input.restrictInl.directSum input.restrictInr).power = input.power
      exact congrArg ModeAmplitude.power (ModeAmplitude.directSum_restrict input)

/-- A reflectionless scattering component is passive exactly when both directional
transmissions are passive. -/
lemma scattering_isPassive_iff [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (rightToLeft : ModeTransform κ ι)
    (leftToRight : ModeTransform ι κ) :
    (scattering rightToLeft leftToRight).toModeTransform.IsPassive ↔
      rightToLeft.IsPassive ∧ leftToRight.IsPassive := by
  constructor
  · intro hPassive
    constructor
    · intro right
      have hApplied := hPassive ((0 : ModeAmplitude ι).directSum right)
      rw [power_scattering_toLinearMap_apply, ModeAmplitude.power_directSum] at hApplied
      simpa [ModeAmplitude.power] using hApplied
    · intro left
      have hApplied := hPassive (left.directSum (0 : ModeAmplitude κ))
      rw [power_scattering_toLinearMap_apply, ModeAmplitude.power_directSum] at hApplied
      simpa [ModeAmplitude.power] using hApplied
  · rintro ⟨hRightToLeft, hLeftToRight⟩
    exact scattering_isPassive hRightToLeft hLeftToRight

/-- Power-preserving directional transmissions realize a lossless scattering component. -/
lemma scattering_isLossless [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] {rightToLeft : ModeTransform κ ι}
    {leftToRight : ModeTransform ι κ}
    (hRightToLeft : rightToLeft.IsPowerPreserving)
    (hLeftToRight : leftToRight.IsPowerPreserving) :
    (scattering rightToLeft leftToRight).IsLossless := by
  rw [ScatteringMatrix.isLossless_iff_isPowerPreserving]
  intro input
  let left := input.restrictInl
  let right := input.restrictInr
  calc
    ((scattering rightToLeft leftToRight).toModeTransform.toLinearMap input).power =
        (rightToLeft.toLinearMap right).power +
          (leftToRight.toLinearMap left).power := by
      rw [show input = left.directSum right by
        change input = input.restrictInl.directSum input.restrictInr
        exact (ModeAmplitude.directSum_restrict input).symm]
      exact power_scattering_toLinearMap_apply rightToLeft leftToRight left right
    _ = right.power + left.power := by
      rw [hRightToLeft right, hLeftToRight left]
    _ = left.power + right.power := add_comm _ _
    _ = input.power := by
      rw [← ModeAmplitude.power_directSum]
      change (input.restrictInl.directSum input.restrictInr).power = input.power
      exact congrArg ModeAmplitude.power (ModeAmplitude.directSum_restrict input)

/-- A reflectionless scattering component is lossless exactly when both directional
transmissions preserve power. -/
lemma scattering_isLossless_iff [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (rightToLeft : ModeTransform κ ι)
    (leftToRight : ModeTransform ι κ) :
    (scattering rightToLeft leftToRight).IsLossless ↔
      rightToLeft.IsPowerPreserving ∧ leftToRight.IsPowerPreserving := by
  constructor
  · intro hLossless
    have hPower := hLossless.isPowerPreserving
    constructor
    · intro right
      have hApplied := hPower ((0 : ModeAmplitude ι).directSum right)
      rw [power_scattering_toLinearMap_apply, ModeAmplitude.power_directSum] at hApplied
      simpa [ModeAmplitude.power] using hApplied
    · intro left
      have hApplied := hPower (left.directSum (0 : ModeAmplitude κ))
      rw [power_scattering_toLinearMap_apply, ModeAmplitude.power_directSum] at hApplied
      simpa [ModeAmplitude.power] using hApplied
  · rintro ⟨hRightToLeft, hLeftToRight⟩
    exact scattering_isLossless hRightToLeft hLeftToRight

end ReflectionlessTwoPort

end

end Optics
