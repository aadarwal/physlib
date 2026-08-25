/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.RectangularBehavior
public import Physlib.Optics.Network.TwoPortBehavior

/-!
# Relational right termination of a two-port behavior

## i. Overview

A right load relates the forward wave `bR` arriving from a two-port device to the backward wave
`aR` returning from the load. This file imposes that relation on a backward-first two-port
behavior without assuming that either the device or the load is functional.

The terminated behavior retains the complete solution `(bL, aR, bR)`. Consequently, its
well-posedness means uniqueness of every unknown wave, including the internal wave `aR` at the
device-load interface. Left reflection and forward transmission to the right termination plane
are derived as relational projections of that complete solution.

## ii. Scope

These are fixed-frequency complex-linear semantics. A zero-reflection load is only the algebraic
relation `aR = 0`; no impedance matching, absorption, passivity, causality, or electromagnetic
realization is inferred. The projected forward wave `bR` is transmission to the declared right
termination plane, not transmission through the load.

## iii. Key definitions and results

- `RightLoadBehavior`: a relation from the wave arriving at a right load to the returning wave.
- `BackwardFirstTwoPortBehavior.terminateRight`: the complete relational terminated solution.
- `BackwardFirstTwoPortBehavior.HasWellPosedRightTermination`: functionality of that solution.
- `BackwardFirstTwoPortBehavior.rightTerminatedReflectionBehavior` and
  `BackwardFirstTwoPortBehavior.rightTerminatedTransmissionBehavior`: external projections.
- `BackwardFirstTwoPortBehavior.rightTerminatedReflectionTransform` and
  `BackwardFirstTwoPortBehavior.rightTerminatedTransmissionTransform`: proof-gated matrices.

## iv. Table of contents

- A. Right-load and complete-solution behaviors
- B. Reflection and transmission projections
- C. Proof-gated response transforms

-/

@[expose] public section

namespace Optics

noncomputable section

universe u v

/-!

## A. Right-load and complete-solution behaviors

-/

/-- A relation from the forward wave `bR` arriving at a right load to the backward wave `aR`
returning toward the two-port device. -/
abbrev RightLoadBehavior (κ : Type v) :=
  LinearBehavior (ForwardWave κ) (BackwardWave κ)

/-- A finite-mode reflection transform mapping the wave `bR` arriving at a right load to the
returning wave `aR`. -/
abbrev RightLoadTransform (κ : Type v) :=
  ModeTransform (ForwardWave κ) (BackwardWave κ)

/-- The output-channel family for a complete right-terminated solution, ordered as
`(bL, (aR, bR))`. -/
abbrev RightTerminatedSolutionChannel (ι : Type u) (κ : Type v) :=
  BackwardWave ι ⊕ (BackwardWave κ ⊕ ForwardWave κ)

/-- A relation from the left incident wave `aL` to the complete terminated solution
`(bL, (aR, bR))`. -/
abbrev RightTerminatedSolutionBehavior (ι : Type u) (κ : Type v) :=
  LinearBehavior (ForwardWave ι) (RightTerminatedSolutionChannel ι κ)

namespace RightLoadBehavior

variable {κ : Type v}

/-- The graph behavior of a finite-mode right-load reflection transform. -/
def ofReflection [Fintype κ] (reflection : RightLoadTransform κ) : RightLoadBehavior κ :=
  reflection.toBehavior

/-- A right-load reflection graph imposes `aR = Γ bR`. -/
lemma mem_ofReflection_iff [Fintype κ] [DecidableEq κ]
    (reflection : RightLoadTransform κ) (forward : ModeAmplitude (ForwardWave κ))
    (backward : ModeAmplitude (BackwardWave κ)) :
    (forward, backward) ∈ ofReflection reflection ↔
      backward = reflection.toLinearMap forward :=
  ModeTransform.mem_toBehavior_iff_toLinearMap reflection forward backward

/-- The algebraic right-load relation `aR = 0` for every arriving wave `bR`.

This definition alone makes no impedance-matching or absorption claim.
-/
def zeroReflection : RightLoadBehavior κ :=
  LinearBehavior.ofLinearMap 0

/-- Membership in the zero-reflection load means that the returning wave vanishes. -/
@[simp]
lemma mem_zeroReflection_iff (forward : ModeAmplitude (ForwardWave κ))
    (backward : ModeAmplitude (BackwardWave κ)) :
    (forward, backward) ∈ (zeroReflection : RightLoadBehavior κ) ↔ backward = 0 := by
  simp [zeroReflection]

/-- The zero-reflection relation is the graph of the zero reflection transform. -/
@[simp]
lemma ofReflection_zero [Fintype κ] :
    ofReflection (0 : RightLoadTransform κ) = zeroReflection := by
  classical
  ext pair
  rcases pair with ⟨forward, backward⟩
  simp [mem_ofReflection_iff]

end RightLoadBehavior

namespace BackwardFirstTwoPortBehavior

variable {ι : Type u} {κ : Type v}

/-- The linear coordinate map from a terminated solution to the device's left and right states. -/
def rightTerminationDeviceStateMap :
    (ModeAmplitude (ForwardWave ι) ×
        ModeAmplitude (RightTerminatedSolutionChannel ι κ)) →ₗ[ℂ]
      (BackwardFirstTravellingWaveState ι × BackwardFirstTravellingWaveState κ) where
  toFun pair :=
    (pair.2.restrictInl.directSum pair.1,
      pair.2.restrictInr.restrictInl.directSum pair.2.restrictInr.restrictInr)
  map_add' first second := by
    apply Prod.ext
    · apply WithLp.ofLp_injective 2
      funext index
      rcases index with index | index <;> rfl
    · apply WithLp.ofLp_injective 2
      funext index
      rcases index with index | index <;> rfl
  map_smul' scalar pair := by
    apply Prod.ext
    · apply WithLp.ofLp_injective 2
      funext index
      rcases index with index | index <;> rfl
    · apply WithLp.ofLp_injective 2
      funext index
      rcases index with index | index <;> rfl

/-- The linear coordinate map from a terminated solution to the load pair `(bR, aR)`. -/
def rightTerminationLoadStateMap :
    (ModeAmplitude (ForwardWave ι) ×
        ModeAmplitude (RightTerminatedSolutionChannel ι κ)) →ₗ[ℂ]
      (ModeAmplitude (ForwardWave κ) × ModeAmplitude (BackwardWave κ)) where
  toFun pair := (pair.2.restrictInr.restrictInr, pair.2.restrictInr.restrictInl)
  map_add' first second := by
    apply Prod.ext <;> apply WithLp.ofLp_injective 2 <;> funext index <;> rfl
  map_smul' scalar pair := by
    apply Prod.ext <;> apply WithLp.ofLp_injective 2 <;> funext index <;> rfl

/-- Impose a right-load relation on a backward-first two-port behavior.

For left incident wave `aL`, the output stores the complete solution `(bL, (aR, bR))`. Membership
requires the device relation between `(bL, aL)` and `(aR, bR)`, together with the load relation
from `bR` to `aR`.
-/
def terminateRight (device : BackwardFirstTwoPortBehavior ι κ)
    (load : RightLoadBehavior κ) : RightTerminatedSolutionBehavior ι κ :=
  device.comap rightTerminationDeviceStateMap ⊓
    load.comap rightTerminationLoadStateMap

/-- Membership in a right-terminated behavior is exactly the device equation together with the
right-load constraint `(bR, aR) ∈ load`. -/
@[simp]
lemma mem_terminateRight_iff (device : BackwardFirstTwoPortBehavior ι κ)
    (load : RightLoadBehavior κ) (leftIncident : ModeAmplitude (ForwardWave ι))
    (solution : ModeAmplitude (RightTerminatedSolutionChannel ι κ)) :
    (leftIncident, solution) ∈ device.terminateRight load ↔
      (solution.restrictInl.directSum leftIncident, solution.restrictInr.restrictInl.directSum
          solution.restrictInr.restrictInr) ∈ device ∧
        (solution.restrictInr.restrictInr, solution.restrictInr.restrictInl) ∈ load := by
  simp only [terminateRight, Submodule.mem_inf, Submodule.mem_comap]
  rfl

/-- Explicit four-wave membership for a right-terminated behavior. -/
lemma mem_terminateRight_directSum_iff (device : BackwardFirstTwoPortBehavior ι κ)
    (load : RightLoadBehavior κ) (leftIncident : ModeAmplitude (ForwardWave ι))
    (leftBackward : ModeAmplitude (BackwardWave ι))
    (rightBackward : ModeAmplitude (BackwardWave κ))
    (rightForward : ModeAmplitude (ForwardWave κ)) :
    (leftIncident, leftBackward.directSum (rightBackward.directSum rightForward)) ∈
        device.terminateRight load ↔
      (leftBackward.directSum leftIncident, rightBackward.directSum rightForward) ∈ device ∧
        (rightForward, rightBackward) ∈ load := by
  rw [mem_terminateRight_iff]
  rfl

/-- A right termination is well posed when every left incident wave determines exactly one
complete solution `(bL, aR, bR)`. -/
abbrev HasWellPosedRightTermination (device : BackwardFirstTwoPortBehavior ι κ)
    (load : RightLoadBehavior κ) : Prop :=
  (device.terminateRight load).IsFunctional

/-!

## B. Reflection and transmission projections

-/

/-- The left-reflected-wave relation obtained by projecting a complete right-terminated
solution. -/
def rightTerminatedReflectionBehavior (device : BackwardFirstTwoPortBehavior ι κ)
    (load : RightLoadBehavior κ) : LinearBehavior (ForwardWave ι) (BackwardWave ι) :=
  (device.terminateRight load).series
    (LinearBehavior.selectLeft :
      LinearBehavior (RightTerminatedSolutionChannel ι κ) (BackwardWave ι))

/-- The forward-wave relation at the right termination plane, obtained by projecting a complete
right-terminated solution. -/
def rightTerminatedTransmissionBehavior (device : BackwardFirstTwoPortBehavior ι κ)
    (load : RightLoadBehavior κ) : LinearBehavior (ForwardWave ι) (ForwardWave κ) :=
  ((device.terminateRight load).series
      (LinearBehavior.selectRight : LinearBehavior (RightTerminatedSolutionChannel ι κ)
        (BackwardWave κ ⊕ ForwardWave κ))).series
    (LinearBehavior.selectRight :
      LinearBehavior (BackwardWave κ ⊕ ForwardWave κ) (ForwardWave κ))

/-- Reflection-projection membership exposes the two right-plane waves hidden by the projection. -/
lemma mem_rightTerminatedReflectionBehavior_iff
    (device : BackwardFirstTwoPortBehavior ι κ) (load : RightLoadBehavior κ)
    (leftIncident : ModeAmplitude (ForwardWave ι))
    (leftBackward : ModeAmplitude (BackwardWave ι)) :
    (leftIncident, leftBackward) ∈ device.rightTerminatedReflectionBehavior load ↔
      ∃ rightBackward : ModeAmplitude (BackwardWave κ),
        ∃ rightForward : ModeAmplitude (ForwardWave κ),
          (leftBackward.directSum leftIncident, rightBackward.directSum rightForward) ∈ device ∧
            (rightForward, rightBackward) ∈ load := by
  rw [rightTerminatedReflectionBehavior, LinearBehavior.mem_series_iff]
  constructor
  · rintro ⟨solution, hSolution, hProjection⟩
    rw [LinearBehavior.mem_selectLeft_iff] at hProjection
    refine ⟨solution.restrictInr.restrictInl, solution.restrictInr.restrictInr, ?_⟩
    rw [hProjection]
    exact (device.mem_terminateRight_iff load leftIncident solution).mp hSolution
  · rintro ⟨rightBackward, rightForward, hDevice, hLoad⟩
    refine ⟨leftBackward.directSum (rightBackward.directSum rightForward), ?_, by simp⟩
    exact (device.mem_terminateRight_directSum_iff load leftIncident leftBackward
      rightBackward rightForward).mpr ⟨hDevice, hLoad⟩

/-- Transmission-projection membership exposes the left-reflected and right-returned waves hidden
by the projection. -/
lemma mem_rightTerminatedTransmissionBehavior_iff
    (device : BackwardFirstTwoPortBehavior ι κ) (load : RightLoadBehavior κ)
    (leftIncident : ModeAmplitude (ForwardWave ι))
    (rightForward : ModeAmplitude (ForwardWave κ)) :
    (leftIncident, rightForward) ∈ device.rightTerminatedTransmissionBehavior load ↔
      ∃ leftBackward : ModeAmplitude (BackwardWave ι),
        ∃ rightBackward : ModeAmplitude (BackwardWave κ),
          (leftBackward.directSum leftIncident, rightBackward.directSum rightForward) ∈ device ∧
            (rightForward, rightBackward) ∈ load := by
  rw [rightTerminatedTransmissionBehavior, LinearBehavior.mem_series_iff]
  constructor
  · rintro ⟨rightState, ⟨solution, hSolution, hRightState⟩, hProjection⟩
    rw [LinearBehavior.mem_selectRight_iff] at hRightState hProjection
    change rightState = solution.restrictInr at hRightState
    rw [hRightState] at hProjection
    refine ⟨solution.restrictInl, solution.restrictInr.restrictInl, ?_⟩
    rw [hProjection]
    exact (device.mem_terminateRight_iff load leftIncident solution).mp hSolution
  · rintro ⟨leftBackward, rightBackward, hDevice, hLoad⟩
    refine ⟨rightBackward.directSum rightForward, ?_, by simp⟩
    refine ⟨leftBackward.directSum (rightBackward.directSum rightForward), ?_, by simp⟩
    exact (device.mem_terminateRight_directSum_iff load leftIncident leftBackward
      rightBackward rightForward).mpr ⟨hDevice, hLoad⟩

/-- A well-posed complete right termination has a functional left-reflection projection. -/
lemma rightTerminatedReflectionBehavior_isFunctional
    (device : BackwardFirstTwoPortBehavior ι κ) (load : RightLoadBehavior κ)
    (hWellPosed : device.HasWellPosedRightTermination load) :
    (device.rightTerminatedReflectionBehavior load).IsFunctional :=
  hWellPosed.series
    (LinearBehavior.isFunctional_ofLinearMap ModeAmplitude.restrictInlLinearMap)

/-- A well-posed complete right termination has a functional forward-transmission projection. -/
lemma rightTerminatedTransmissionBehavior_isFunctional
    (device : BackwardFirstTwoPortBehavior ι κ) (load : RightLoadBehavior κ)
    (hWellPosed : device.HasWellPosedRightTermination load) :
    (device.rightTerminatedTransmissionBehavior load).IsFunctional :=
  (hWellPosed.series
    (LinearBehavior.isFunctional_ofLinearMap ModeAmplitude.restrictInrLinearMap)).series
      (LinearBehavior.isFunctional_ofLinearMap ModeAmplitude.restrictInrLinearMap)

/-!

## C. Proof-gated response transforms

-/

/-- The left-reflection transform extracted from a well-posed right termination. -/
noncomputable def rightTerminatedReflectionTransform [Fintype ι] [DecidableEq ι]
    (device : BackwardFirstTwoPortBehavior ι κ) (load : RightLoadBehavior κ)
    (hWellPosed : device.HasWellPosedRightTermination load) :
    ModeTransform (ForwardWave ι) (BackwardWave ι) :=
  (device.rightTerminatedReflectionBehavior load).toModeTransform
    (device.rightTerminatedReflectionBehavior_isFunctional load hWellPosed)

/-- The extracted reflection transform reconstructs the projected reflection behavior. -/
@[simp]
lemma toBehavior_rightTerminatedReflectionTransform [Fintype ι] [DecidableEq ι]
    (device : BackwardFirstTwoPortBehavior ι κ) (load : RightLoadBehavior κ)
    (hWellPosed : device.HasWellPosedRightTermination load) :
    (device.rightTerminatedReflectionTransform load hWellPosed).toBehavior =
      device.rightTerminatedReflectionBehavior load :=
  LinearBehavior.toBehavior_toModeTransform _ _

/-- The forward-transmission transform to the right termination plane, extracted from a
well-posed right termination. -/
noncomputable def rightTerminatedTransmissionTransform [Fintype ι] [DecidableEq ι]
    (device : BackwardFirstTwoPortBehavior ι κ) (load : RightLoadBehavior κ)
    (hWellPosed : device.HasWellPosedRightTermination load) :
    ModeTransform (ForwardWave ι) (ForwardWave κ) :=
  (device.rightTerminatedTransmissionBehavior load).toModeTransform
    (device.rightTerminatedTransmissionBehavior_isFunctional load hWellPosed)

/-- The extracted transmission transform reconstructs the projected transmission behavior. -/
@[simp]
lemma toBehavior_rightTerminatedTransmissionTransform [Fintype ι] [DecidableEq ι]
    (device : BackwardFirstTwoPortBehavior ι κ) (load : RightLoadBehavior κ)
    (hWellPosed : device.HasWellPosedRightTermination load) :
    (device.rightTerminatedTransmissionTransform load hWellPosed).toBehavior =
      device.rightTerminatedTransmissionBehavior load :=
  LinearBehavior.toBehavior_toModeTransform _ _

end BackwardFirstTwoPortBehavior

end

end Optics
