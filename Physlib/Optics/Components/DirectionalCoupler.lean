/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Components.ReflectionlessTwoPort

/-!
# Algebraic directional-coupler core

## i. Overview

This file specifies a fixed-carrier two-arm mixer with real through amplitude `t`, real cross
amplitude `k`, and the pinned complex matrix

`[[t, -I * k], [-I * k, t]]`.

Two copies of this mixer form a reflectionless two-side, two-arm nested-sum scattering law. The
right-side incident pair determines the left-side outgoing pair, and conversely. The behavior is
stated independently before the scattering matrix is constructed and proved to be its exact graph.

Using the same mixer in both longitudinal directions is model data, not a reciprocity theorem. The
`-I` cross phase is a declared coordinate convention, not a consequence of the positive-time
phasor convention. This source-neutral algebraic layer claims no physical ports, coupling length,
bandwidth, delay, material realization, electromagnetic normalization, or quantum behavior.
Physical-port ownership and normalized-modal-power classification are separate stacked layers.

## ii. Key results

- `DirectionalCoupler.mixing`: the two-arm through/cross transform.
- `DirectionalCoupler.mixing_toLinearMap_apply`: its exact coupled action.
- `DirectionalCoupler.behavior`: the independent bidirectional law.
- `DirectionalCoupler.scattering`: its reflectionless nested-sum realization.
- `DirectionalCoupler.scattering_realizes_behavior`: exact graph realization.

## iii. Table of contents

- A. Parameters and two-arm mixing
- B. Independent behavior and scattering realization

## iv. References

This reusable component law is Physlib-original. Comparison with scalar coupler coefficients in
DATE 2014 and SysCon 2015 remains a separately human-audited bridge.
-/

@[expose] public section

namespace Optics

noncomputable section

universe u

namespace DirectionalCoupler

/-! ## A. Parameters and two-arm mixing -/

/-- Real through/cross modal-amplitude parameters of the algebraic coupler. -/
structure Parameters where
  /-- The same-arm through amplitude. -/
  throughAmplitude : ℝ
  /-- The other-arm cross amplitude before the declared quadrature phase. -/
  crossAmplitude : ℝ

/-- The cross-arm coefficient with the pinned negative-quadrature phase. -/
def crossCoefficient (p : Parameters) : ℂ :=
  -Complex.I * (p.crossAmplitude : ℂ)

/-- The two-arm mixer `[[t, -I*k], [-I*k, t]]`, with rows indexing output arms. -/
def mixing (p : Parameters) (mode : Type u) : ModeTransform (mode ⊕ mode) (mode ⊕ mode) := by
  classical
  exact Matrix.fromBlocks
    ((p.throughAmplitude : ℂ) • 1) (crossCoefficient p • 1)
    (crossCoefficient p • 1) ((p.throughAmplitude : ℂ) • 1)

/-- The mixer applies the declared through and cross coefficients in the pinned arm order. -/
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

/-! ## B. Independent behavior and scattering realization -/

/-- The independent reflectionless bidirectional coupler behavior. -/
def behavior [Fintype ι] [DecidableEq ι] (p : Parameters) :
    TwoPortScatteringBehavior (ι ⊕ ι) (ι ⊕ ι) :=
  ReflectionlessTwoPort.behavior (mixing p ι) (mixing p ι)

/-- Behavior membership is exactly the pair of declared opposite-side mixing equations. -/
@[simp]
lemma mem_behavior_iff [Fintype ι] [DecidableEq ι] (p : Parameters)
    (incident : ModeAmplitude (Incident (ι ⊕ ι) ⊕ Incident (ι ⊕ ι)))
    (outgoing : ModeAmplitude (Outgoing (ι ⊕ ι) ⊕ Outgoing (ι ⊕ ι))) :
    (incident, outgoing) ∈ behavior p ↔
      outgoing =
        (ModeAmplitude.reindex Outgoing.channelEquiv.symm
          ((mixing p ι).toLinearMap
            (ModeAmplitude.reindex Incident.channelEquiv incident.restrictInr))).directSum
        (ModeAmplitude.reindex Outgoing.channelEquiv.symm
          ((mixing p ι).toLinearMap
            (ModeAmplitude.reindex Incident.channelEquiv incident.restrictInl))) := by
  rw [behavior, ReflectionlessTwoPort.mem_behavior_iff]

/-- The zero-reflection two-side, two-arm nested-sum scattering realization of the mixer. -/
def scattering (p : Parameters) (mode : Type u) :
    ScatteringMatrix ((mode ⊕ mode) ⊕ (mode ⊕ mode)) :=
  ReflectionlessTwoPort.scattering (mixing p mode) (mixing p mode)

/-- The scattering realization crosses the longitudinal sides and mixes the two arms. -/
lemma scattering_toLinearMap_apply [Fintype ι] [DecidableEq ι] (p : Parameters)
    (left right : ModeAmplitude (ι ⊕ ι)) :
    (scattering p ι).toModeTransform.toLinearMap (left.directSum right) =
      ((mixing p ι).toLinearMap right).directSum
        ((mixing p ι).toLinearMap left) := by
  exact ReflectionlessTwoPort.scattering_toLinearMap_apply _ _ _ _

/-- The typed scattering adapter applies the independently declared bidirectional output law. -/
lemma scattering_toTwoPortScatteringTransform_toLinearMap_apply
    [Fintype ι] [DecidableEq ι] (p : Parameters)
    (incident : ModeAmplitude (Incident (ι ⊕ ι) ⊕ Incident (ι ⊕ ι))) :
    (scattering p ι).toTwoPortScatteringTransform.toLinearMap incident =
      ReflectionlessTwoPort.outputMap (mixing p ι) (mixing p ι) incident := by
  exact
    ReflectionlessTwoPort.scattering_toTwoPortScatteringTransform_toLinearMap_apply
      _ _ _

/-- The scattering matrix realizes the independently specified coupler behavior exactly. -/
lemma scattering_realizes_behavior [Fintype ι] [DecidableEq ι] (p : Parameters) :
    (scattering p ι).toTwoPortScatteringBehavior = behavior p := by
  exact ReflectionlessTwoPort.scattering_realizes_behavior (mixing p ι) (mixing p ι)

end DirectionalCoupler

end

end Optics
