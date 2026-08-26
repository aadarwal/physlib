/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.LinearBehavior
public import Physlib.Optics.Network.Port

/-!
# Algebraic two-channel beam splitter

## i. Overview

This file specifies a fixed-carrier beam splitter directly on two optical channels. Its real
through and cross amplitudes `t` and `k` use the declared matrix

`[[t, -I * k], [-I * k, t]]`.

The incident-to-outgoing behavior is stated independently as an amplitude-level linear map before
the scattering matrix is constructed. Exact graph equality then proves that the scattering matrix
realizes that specification. This component is not an alias of `DirectionalCoupler`: it has its
own parameters, behavior, scattering law, and unitary classification, and it mixes one pair of
incident channels rather than embedding a mixer in a reflectionless longitudinal four-port law.

The negative-quadrature cross phase is declared model data. It is not derived from reciprocity,
time reversal, a material interface, or propagation. This algebraic law asserts no geometry,
bandwidth, causality, electromagnetic normalization, or physical realization.

## ii. Key results

- `BeamSplitter.mixing`: the declared two-channel transform.
- `BeamSplitter.behavior`: the independent incident-to-outgoing behavior.
- `BeamSplitter.scattering`: the scattering realization.
- `BeamSplitter.scattering_realizes_behavior`: exact realization of the independent behavior.
- `BeamSplitter.scattering_isLossless`: unitary parameters give algebraic modal losslessness.

## iii. Table of contents

- A. Parameters and two-channel mixing
- B. Independent behavioral specification
- C. Scattering realization and unitary classification

## iv. References

This reusable component law is Physlib-original and source-neutral. `ModeAmplitude.power` is
squared-amplitude bookkeeping; its use here is not an electromagnetic-power claim.
-/

@[expose] public section

namespace Optics

noncomputable section

universe u

namespace BeamSplitter

/-!
## A. Parameters and two-channel mixing
-/

/-- Real through and cross amplitudes of the algebraic beam splitter. -/
structure Parameters where
  /-- The same-channel through amplitude. -/
  throughAmplitude : ℝ
  /-- The other-channel cross amplitude before the declared quadrature phase. -/
  crossAmplitude : ℝ

/-- The common normalized-modal-power factor `t² + k²`. -/
def Parameters.powerFactor (p : Parameters) : ℝ :=
  p.throughAmplitude ^ 2 + p.crossAmplitude ^ 2

/-- The exact unitary normalization of the beam-splitter parameters. -/
def Parameters.IsUnitary (p : Parameters) : Prop :=
  p.powerFactor = 1

/-- Canonical ideal parameters use nonnegative amplitudes and unitary normalization. -/
def Parameters.IsValid (p : Parameters) : Prop :=
  0 ≤ p.throughAmplitude ∧ 0 ≤ p.crossAmplitude ∧ p.IsUnitary

/-- Canonically valid parameters satisfy the exact unitary normalization. -/
lemma Parameters.IsValid.isUnitary {p : Parameters} (hp : p.IsValid) : p.IsUnitary :=
  hp.2.2

/-- The cross-channel coefficient with the pinned negative-quadrature phase. -/
def crossCoefficient (p : Parameters) : ℂ :=
  -Complex.I * (p.crossAmplitude : ℂ)

/-- The beam-splitter matrix `[[t, -I*k], [-I*k, t]]`. -/
def mixing (p : Parameters) (mode : Type u) : ModeTransform (mode ⊕ mode) (mode ⊕ mode) := by
  classical
  exact Matrix.fromBlocks
    ((p.throughAmplitude : ℂ) • 1) (crossCoefficient p • 1)
    (crossCoefficient p • 1) ((p.throughAmplitude : ℂ) • 1)

/-- The mixer applies the declared through and cross coefficients in the pinned channel order. -/
lemma mixing_toLinearMap_apply [Fintype ι] [DecidableEq ι] (p : Parameters)
    (input : ModeAmplitude (ι ⊕ ι)) :
    (mixing p ι).toLinearMap input =
      ((p.throughAmplitude : ℂ) • input.restrictInl +
          crossCoefficient p • input.restrictInr).directSum
        (crossCoefficient p • input.restrictInl +
          (p.throughAmplitude : ℂ) • input.restrictInr) := by
  classical
  conv_lhs => rw [← ModeAmplitude.directSum_restrict input]
  have hMixing : mixing p ι = Matrix.fromBlocks
      ((p.throughAmplitude : ℂ) • (1 : ModeTransform ι ι))
      (crossCoefficient p • (1 : ModeTransform ι ι))
      (crossCoefficient p • (1 : ModeTransform ι ι))
      ((p.throughAmplitude : ℂ) • (1 : ModeTransform ι ι)) := by
    ext output input
    rcases output with output | output <;> rcases input with input | input <;>
      simp [mixing] <;>
      (left; by_cases h : output = input <;> simp [Matrix.one_apply, h])
  rw [hMixing, ModeTransform.fromBlocks_apply]
  simp only [ModeTransform.toLinearMap, Matrix.toEuclideanLin, map_smul,
    Matrix.toLpLin_one, LinearMap.smul_apply, LinearMap.id_apply]

/-!
## B. Independent behavioral specification
-/

/-- The independently specified endpoint output map of the beam splitter.

This definition states the two through/cross equations directly. It does not use the matrix
`mixing` or the scattering realization.
-/
def outputMap [Fintype ι] [DecidableEq ι] (p : Parameters) :
    ModeAmplitude (Incident (ι ⊕ ι)) →ₗ[ℂ]
      ModeAmplitude (Outgoing (ι ⊕ ι)) :=
  let rawIncident :=
    (ModeAmplitude.reindex
      (Incident.channelEquiv : Incident (ι ⊕ ι) ≃ ι ⊕ ι)).toLinearEquiv.toLinearMap
  let firstIncident :=
    (ModeAmplitude.restrictInlLinearMap :
      ModeAmplitude (ι ⊕ ι) →ₗ[ℂ] ModeAmplitude ι).comp rawIncident
  let secondIncident :=
    (ModeAmplitude.restrictInrLinearMap :
      ModeAmplitude (ι ⊕ ι) →ₗ[ℂ] ModeAmplitude ι).comp rawIncident
  let firstOutgoing :=
    (p.throughAmplitude : ℂ) • firstIncident +
      (-Complex.I * (p.crossAmplitude : ℂ)) • secondIncident
  let secondOutgoing :=
    (-Complex.I * (p.crossAmplitude : ℂ)) • firstIncident +
      (p.throughAmplitude : ℂ) • secondIncident
  (ModeAmplitude.reindex
      (Outgoing.channelEquiv.symm :
        (ι ⊕ ι) ≃ Outgoing (ι ⊕ ι))).toLinearEquiv.toLinearMap.comp
    (ModeAmplitude.directSumLinearEquiv.toLinearMap.comp
      (firstOutgoing.prod secondOutgoing))

/-- The independent output map removes endpoint wrappers, mixes, and restores them. -/
lemma outputMap_apply [Fintype ι] [DecidableEq ι] (p : Parameters)
    (incident : ModeAmplitude (Incident (ι ⊕ ι))) :
    outputMap p incident =
      ModeAmplitude.reindex Outgoing.channelEquiv.symm
        (((p.throughAmplitude : ℂ) •
            (ModeAmplitude.reindex Incident.channelEquiv incident).restrictInl +
          (-Complex.I * (p.crossAmplitude : ℂ)) •
            (ModeAmplitude.reindex Incident.channelEquiv incident).restrictInr).directSum
        ((-Complex.I * (p.crossAmplitude : ℂ)) •
            (ModeAmplitude.reindex Incident.channelEquiv incident).restrictInl +
          (p.throughAmplitude : ℂ) •
            (ModeAmplitude.reindex Incident.channelEquiv incident).restrictInr)) := by
  rfl

/-- The independent beam-splitter behavior, defined before its scattering realization. -/
def behavior [Fintype ι] [DecidableEq ι] (p : Parameters) :
    LinearBehavior (Incident (ι ⊕ ι)) (Outgoing (ι ⊕ ι)) :=
  LinearBehavior.ofLinearMap (outputMap p)

/-- Behavior membership is exactly the independently declared output equation. -/
@[simp]
lemma mem_behavior_iff [Fintype ι] [DecidableEq ι] (p : Parameters)
    (incident : ModeAmplitude (Incident (ι ⊕ ι)))
    (outgoing : ModeAmplitude (Outgoing (ι ⊕ ι))) :
    (incident, outgoing) ∈ behavior p ↔
      outgoing =
        ModeAmplitude.reindex Outgoing.channelEquiv.symm
          (((p.throughAmplitude : ℂ) •
              (ModeAmplitude.reindex Incident.channelEquiv incident).restrictInl +
            (-Complex.I * (p.crossAmplitude : ℂ)) •
              (ModeAmplitude.reindex Incident.channelEquiv incident).restrictInr).directSum
          ((-Complex.I * (p.crossAmplitude : ℂ)) •
              (ModeAmplitude.reindex Incident.channelEquiv incident).restrictInl +
            (p.throughAmplitude : ℂ) •
              (ModeAmplitude.reindex Incident.channelEquiv incident).restrictInr)) := by
  rw [behavior, LinearBehavior.mem_ofLinearMap_iff, outputMap_apply]

/-!
## C. Scattering realization and unitary classification
-/

/-- The scattering realization of the declared two-channel mixer. -/
def scattering (p : Parameters) (mode : Type u) : ScatteringMatrix (mode ⊕ mode) where
  toModeTransform := mixing p mode

/-- The scattering matrix acts by the declared two-channel mixing law. -/
lemma scattering_toLinearMap_apply [Fintype ι] [DecidableEq ι] (p : Parameters)
    (input : ModeAmplitude (ι ⊕ ι)) :
    (scattering p ι).toModeTransform.toLinearMap input =
      ((p.throughAmplitude : ℂ) • input.restrictInl +
          crossCoefficient p • input.restrictInr).directSum
        (crossCoefficient p • input.restrictInl +
          (p.throughAmplitude : ℂ) • input.restrictInr) :=
  mixing_toLinearMap_apply p input

/-- The scattering matrix realizes the independently specified behavior exactly. -/
lemma scattering_realizes_behavior [Fintype ι] [DecidableEq ι] (p : Parameters) :
    (scattering p ι).toOrientedModeTransform.toBehavior = behavior p := by
  ext ⟨incident, outgoing⟩
  rw [ModeTransform.mem_toBehavior_iff_toLinearMap, mem_behavior_iff,
    ScatteringMatrix.toLinearMap_toOrientedModeTransform,
    scattering_toLinearMap_apply, crossCoefficient]
  rfl

/-- The quadrature cross terms cancel in the squared moduli of the two mixed coordinates. -/
lemma normSq_mixing_pair (p : Parameters) (first second : ℂ) :
    Complex.normSq ((p.throughAmplitude : ℂ) * first + crossCoefficient p * second) +
        Complex.normSq (crossCoefficient p * first +
          (p.throughAmplitude : ℂ) * second) =
      p.powerFactor * (Complex.normSq first + Complex.normSq second) := by
  simp [crossCoefficient, Parameters.powerFactor, Complex.normSq_apply]
  ring

/-- The beam-splitter mixer scales modal power by exactly `t² + k²`. -/
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

/-- Unitary parameters make the mixer preserve normalized modal power. -/
lemma mixing_isPowerPreserving [Fintype ι] [DecidableEq ι] (p : Parameters)
    (hp : p.IsUnitary) : (mixing p ι).IsPowerPreserving := by
  intro input
  rw [power_mixing_toLinearMap_apply, hp, one_mul]

/-- Unitary parameters make the algebraic scattering matrix lossless. -/
lemma scattering_isLossless [Fintype ι] [DecidableEq ι] (p : Parameters)
    (hp : p.IsUnitary) : (scattering p ι).IsLossless := by
  rw [ScatteringMatrix.isLossless_iff_isPowerPreserving]
  exact mixing_isPowerPreserving p hp

end BeamSplitter

end

end Optics
