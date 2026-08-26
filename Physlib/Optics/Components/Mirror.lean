/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.LinearBehavior
public import Physlib.Optics.Network.Port

/-!
# Algebraic one-port phase mirror

## i. Overview

This file specifies a mirror as a one-port fixed-carrier scattering law. Every mode incident on the
single modeled port is returned on the corresponding outgoing channel with one declared complex
reflection coefficient. The behavior is stated independently at the amplitude level before the
scattering matrix is constructed and proved to realize it.

`Parameters.IsUnitPhase` records the exact unit-modulus condition needed for algebraic modal-power
preservation. It is a condition on the reduced coefficient, not a material, coating, boundary, or
electromagnetic derivation. The model supplies no propagation distance, reference-plane shift,
time reversal, reciprocity, bandwidth, causality, dispersion, or omitted-channel completeness.

## ii. Key results

- `Mirror.reflection`: the same-mode scalar reflection transform.
- `Mirror.behavior`: the independent one-port phase law.
- `Mirror.scattering`: the one-port scattering realization.
- `Mirror.scattering_realizes_behavior`: exact realization of the independent behavior.
- `Mirror.scattering_isLossless`: a unit-phase coefficient preserves algebraic modal power.

## iii. Table of contents

- A. Reflection coefficient and mode transform
- B. Independent behavioral specification
- C. Scattering realization and unit-phase classification

## iv. References

This reduced one-port mirror is Physlib-original and source-neutral. Its modal-power result is
squared-amplitude bookkeeping, not electromagnetic power. No reciprocity, time reversal,
reverse-incidence Maxwell law, modal completeness, propagation, causality, dispersion, or
physical realization is asserted.
-/

@[expose] public section

namespace Optics

noncomputable section

universe u

namespace Mirror

/-!
## A. Reflection coefficient and mode transform
-/

/-- The complex reflection coefficient of the fixed-carrier one-port mirror. -/
structure Parameters where
  /-- The same-mode coefficient from the incident endpoint to the outgoing endpoint. -/
  reflectionCoefficient : ℂ

/-- The mirror coefficient has unit squared modulus. -/
def Parameters.IsUnitPhase (p : Parameters) : Prop :=
  Complex.normSq p.reflectionCoefficient = 1

/-- The scalar same-mode reflection transform. -/
def reflection (p : Parameters) (mode : Type u) : ModeTransform mode mode := by
  classical
  exact p.reflectionCoefficient • 1

/-- The reflection transform multiplies every modal amplitude by its coefficient. -/
lemma reflection_toLinearMap_apply [Fintype ι] [DecidableEq ι] (p : Parameters)
    (amplitude : ModeAmplitude ι) :
    (reflection p ι).toLinearMap amplitude = p.reflectionCoefficient • amplitude := by
  classical
  have hReflection : reflection p ι =
      p.reflectionCoefficient • (1 : ModeTransform ι ι) := by
    ext output input
    by_cases h : output = input <;> simp [reflection, h]
  rw [hReflection]
  simp only [ModeTransform.toLinearMap, Matrix.toEuclideanLin, map_smul,
    Matrix.toLpLin_one, LinearMap.smul_apply, LinearMap.id_apply]

/-!
## B. Independent behavioral specification
-/

/-- The independently specified incident-to-outgoing map of the one-port mirror.

This definition states coefficient-times-corresponding-mode directly. It does not use the matrix
`reflection` or the scattering realization.
-/
def outputMap [Fintype ι] (p : Parameters) :
    ModeAmplitude (Incident ι) →ₗ[ℂ] ModeAmplitude (Outgoing ι) :=
  (ModeAmplitude.reindex
      (Outgoing.channelEquiv.symm : ι ≃ Outgoing ι)).toLinearEquiv.toLinearMap.comp
    ((p.reflectionCoefficient •
        (LinearMap.id : ModeAmplitude ι →ₗ[ℂ] ModeAmplitude ι)).comp
      (ModeAmplitude.reindex
        (Incident.channelEquiv : Incident ι ≃ ι)).toLinearEquiv.toLinearMap)

/-- The independent output law removes endpoint wrappers, reflects, and restores them. -/
lemma outputMap_apply [Fintype ι] (p : Parameters)
    (incident : ModeAmplitude (Incident ι)) :
    outputMap p incident =
      ModeAmplitude.reindex Outgoing.channelEquiv.symm
        (p.reflectionCoefficient •
          ModeAmplitude.reindex Incident.channelEquiv incident) := by
  rfl

/-- The independent one-port mirror behavior. -/
def behavior [Fintype ι] (p : Parameters) :
    LinearBehavior (Incident ι) (Outgoing ι) :=
  LinearBehavior.ofLinearMap (outputMap p)

/-- Behavior membership is exactly the independently declared reflection equation. -/
@[simp]
lemma mem_behavior_iff [Fintype ι] (p : Parameters)
    (incident : ModeAmplitude (Incident ι))
    (outgoing : ModeAmplitude (Outgoing ι)) :
    (incident, outgoing) ∈ behavior p ↔
      outgoing = ModeAmplitude.reindex Outgoing.channelEquiv.symm
        (p.reflectionCoefficient •
          ModeAmplitude.reindex Incident.channelEquiv incident) := by
  rw [behavior, LinearBehavior.mem_ofLinearMap_iff, outputMap_apply]

/-!
## C. Scattering realization and unit-phase classification
-/

/-- The scattering realization of the one-port reflection law. -/
def scattering (p : Parameters) (mode : Type u) : ScatteringMatrix mode where
  toModeTransform := reflection p mode

/-- The scattering transform multiplies every modal amplitude by the reflection coefficient. -/
lemma scattering_toLinearMap_apply [Fintype ι] [DecidableEq ι] (p : Parameters)
    (amplitude : ModeAmplitude ι) :
    (scattering p ι).toModeTransform.toLinearMap amplitude =
      p.reflectionCoefficient • amplitude :=
  reflection_toLinearMap_apply p amplitude

/-- The scattering matrix realizes the independently specified mirror behavior exactly. -/
lemma scattering_realizes_behavior [Fintype ι] [DecidableEq ι] (p : Parameters) :
    (scattering p ι).toOrientedModeTransform.toBehavior = behavior p := by
  ext ⟨incident, outgoing⟩
  rw [ModeTransform.mem_toBehavior_iff_toLinearMap, mem_behavior_iff,
    ScatteringMatrix.toLinearMap_toOrientedModeTransform]
  rw [scattering_toLinearMap_apply]

/-- A unit-phase reflection coefficient makes the one-port scattering matrix lossless. -/
lemma scattering_isLossless [Fintype ι] [DecidableEq ι] (p : Parameters)
    (hp : p.IsUnitPhase) : (scattering p ι).IsLossless := by
  rw [ScatteringMatrix.isLossless_iff_isPowerPreserving]
  intro amplitude
  rw [scattering_toLinearMap_apply, ModeAmplitude.power_smul]
  change Complex.normSq p.reflectionCoefficient = 1 at hp
  rw [hp, one_mul]

end Mirror

end

end Optics
