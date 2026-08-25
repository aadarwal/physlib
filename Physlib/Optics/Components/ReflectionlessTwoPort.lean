/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.TwoPortScattering

/-!
# Reflectionless two-port scattering components

## i. Overview

This file gives a reflectionless two-port component an independent amplitude-level behavior and a
scattering-matrix realization. The two transmission transforms may have different mode families
and need not be inverses. In scattering coordinates the specification is

`bL = T_rl aR` and `bR = T_lr aL`.

The realized matrix has zero reflection blocks and the two declared transmission blocks. Exact
graph equality proves that the matrix realizes the behavioral specification. Modal-power
classification is provided separately in `ReflectionlessTwoPortPower`.

Reflectionless here is only a zero-reflection component law. It does not assert impedance
matching, reciprocity, a propagation model, a material realization, or absence of omitted loss
channels.

## ii. Key results

- `ReflectionlessTwoPort.outputMap`: independent amplitude-level transmission law.
- `ReflectionlessTwoPort.behavior`: graph behavior of that law.
- `ReflectionlessTwoPort.scattering`: the zero-reflection block scattering matrix.
- `ReflectionlessTwoPort.scattering_realizes_behavior`: exact graph realization.

## iii. Table of contents

- A. Independent behavioral specification
- B. Scattering realization

## iv. References

This algebraic constructor is Physlib-original. It is not a formalization of a named component law
from the surveyed HOL optics corpus.
-/

@[expose] public section

namespace Optics

noncomputable section

universe u v

namespace ReflectionlessTwoPort

variable {ι : Type u} {κ : Type v}

/-!

## A. Independent behavioral specification

-/

/-- The amplitude-level output law of a reflectionless two-port component.

The first output is the right-to-left transmission applied to the right incident amplitude. The
second output is the left-to-right transmission applied to the left incident amplitude. Endpoint
wrappers are removed before the declared transforms act and restored afterwards.
-/
def outputMap [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (rightToLeft : ModeTransform κ ι) (leftToRight : ModeTransform ι κ) :
    ModeAmplitude (Incident ι ⊕ Incident κ) →ₗ[ℂ]
      ModeAmplitude (Outgoing ι ⊕ Outgoing κ) :=
  let leftIncident :=
    (ModeAmplitude.reindex
      (Incident.channelEquiv : Incident ι ≃ ι)).toLinearEquiv.toLinearMap.comp
      (ModeAmplitude.restrictInlLinearMap :
        ModeAmplitude (Incident ι ⊕ Incident κ) →ₗ[ℂ] ModeAmplitude (Incident ι))
  let rightIncident :=
    (ModeAmplitude.reindex
      (Incident.channelEquiv : Incident κ ≃ κ)).toLinearEquiv.toLinearMap.comp
      (ModeAmplitude.restrictInrLinearMap :
        ModeAmplitude (Incident ι ⊕ Incident κ) →ₗ[ℂ] ModeAmplitude (Incident κ))
  let leftOutgoing :=
    (ModeAmplitude.reindex
      (Outgoing.channelEquiv.symm : ι ≃ Outgoing ι)).toLinearEquiv.toLinearMap
  let rightOutgoing :=
    (ModeAmplitude.reindex
      (Outgoing.channelEquiv.symm : κ ≃ Outgoing κ)).toLinearEquiv.toLinearMap
  ModeAmplitude.directSumLinearEquiv.toLinearMap.comp
    ((leftOutgoing.comp (rightToLeft.toLinearMap.comp rightIncident)).prod
      (rightOutgoing.comp (leftToRight.toLinearMap.comp leftIncident)))

/-- The independent output law applies the two transmissions in the declared directions. -/
lemma outputMap_apply [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (rightToLeft : ModeTransform κ ι) (leftToRight : ModeTransform ι κ)
    (incident : ModeAmplitude (Incident ι ⊕ Incident κ)) :
    outputMap rightToLeft leftToRight incident =
      (ModeAmplitude.reindex Outgoing.channelEquiv.symm
          (rightToLeft.toLinearMap
            (ModeAmplitude.reindex Incident.channelEquiv incident.restrictInr))).directSum
        (ModeAmplitude.reindex Outgoing.channelEquiv.symm
          (leftToRight.toLinearMap
            (ModeAmplitude.reindex Incident.channelEquiv incident.restrictInl))) := by
  rfl

/-- The reflectionless two-port behavior specified independently at the amplitude level. -/
def behavior [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (rightToLeft : ModeTransform κ ι) (leftToRight : ModeTransform ι κ) :
    TwoPortScatteringBehavior ι κ :=
  LinearBehavior.ofLinearMap (outputMap rightToLeft leftToRight)

/-- Behavior membership is exactly the pair of declared directional transmission laws. -/
@[simp]
lemma mem_behavior_iff [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (rightToLeft : ModeTransform κ ι) (leftToRight : ModeTransform ι κ)
    (incident : ModeAmplitude (Incident ι ⊕ Incident κ))
    (outgoing : ModeAmplitude (Outgoing ι ⊕ Outgoing κ)) :
    (incident, outgoing) ∈ behavior rightToLeft leftToRight ↔
      outgoing =
        (ModeAmplitude.reindex Outgoing.channelEquiv.symm
            (rightToLeft.toLinearMap
              (ModeAmplitude.reindex Incident.channelEquiv incident.restrictInr))).directSum
          (ModeAmplitude.reindex Outgoing.channelEquiv.symm
            (leftToRight.toLinearMap
              (ModeAmplitude.reindex Incident.channelEquiv incident.restrictInl))) := by
  rw [behavior, LinearBehavior.mem_ofLinearMap_iff, outputMap_apply]

/-!

## B. Scattering realization

-/

/-- The scattering realization with zero reflection blocks and the declared transmissions.

Rows and columns are ordered left then right. Thus the upper-right block is right-to-left
transmission and the lower-left block is left-to-right transmission.
-/
def scattering (rightToLeft : ModeTransform κ ι) (leftToRight : ModeTransform ι κ) :
    ScatteringMatrix (ι ⊕ κ) where
  toModeTransform := Matrix.fromBlocks 0 rightToLeft leftToRight 0

/-- The scattering realization acts by the two directional transmission equations. -/
lemma scattering_toLinearMap_apply [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (rightToLeft : ModeTransform κ ι)
    (leftToRight : ModeTransform ι κ) (left : ModeAmplitude ι)
    (right : ModeAmplitude κ) :
    (scattering rightToLeft leftToRight).toModeTransform.toLinearMap
        (left.directSum right) =
      (rightToLeft.toLinearMap right).directSum
        (leftToRight.toLinearMap left) := by
  change ModeTransform.toLinearMap (Matrix.fromBlocks 0 rightToLeft leftToRight 0)
      (left.directSum right) = _
  rw [ModeTransform.fromBlocks_apply]
  simp

/-- The typed scattering adapter of the realized matrix acts by the independent output map. -/
lemma scattering_toTwoPortScatteringTransform_toLinearMap_apply
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (rightToLeft : ModeTransform κ ι) (leftToRight : ModeTransform ι κ)
    (incident : ModeAmplitude (Incident ι ⊕ Incident κ)) :
    (scattering rightToLeft leftToRight).toTwoPortScatteringTransform.toLinearMap incident =
      outputMap rightToLeft leftToRight incident := by
  rw [ScatteringMatrix.toLinearMap_toTwoPortScatteringTransform_eq,
    ScatteringMatrix.toLinearMap_toOrientedModeTransform]
  have hIncident :
      ModeAmplitude.reindex Incident.channelEquiv
          (ModeAmplitude.reindex Incident.splitSumEquiv.symm incident) =
        (ModeAmplitude.reindex Incident.channelEquiv incident.restrictInl).directSum
          (ModeAmplitude.reindex Incident.channelEquiv incident.restrictInr) := by
    apply WithLp.ofLp_injective 2
    funext channel
    rcases channel with channel | channel <;> rfl
  rw [hIncident, scattering_toLinearMap_apply, outputMap_apply]
  apply WithLp.ofLp_injective 2
  funext endpoint
  rcases endpoint with endpoint | endpoint
  · rcases endpoint with ⟨channel⟩
    rfl
  · rcases endpoint with ⟨channel⟩
    rfl

/-- The block scattering matrix realizes the independent reflectionless behavior exactly. -/
lemma scattering_realizes_behavior [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (rightToLeft : ModeTransform κ ι)
    (leftToRight : ModeTransform ι κ) :
    (scattering rightToLeft leftToRight).toTwoPortScatteringBehavior =
      behavior rightToLeft leftToRight := by
  ext ⟨incident, outgoing⟩
  rw [ScatteringMatrix.toTwoPortScatteringBehavior,
    ModeTransform.mem_toBehavior_iff_toLinearMap, mem_behavior_iff,
    scattering_toTwoPortScatteringTransform_toLinearMap_apply]
  simp only [outputMap_apply]

end ReflectionlessTwoPort

end

end Optics
