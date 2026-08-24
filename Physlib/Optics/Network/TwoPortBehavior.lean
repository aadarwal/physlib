/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.LinearBehavior
public import Physlib.Optics.Network.Port

/-!
# Travelling-wave two-port behaviors

## i. Overview

A two-port law involves four travelling waves: one in each direction at each of two oriented
reference planes. This file keeps that law relational. Its chosen internal state order is backward
wave first and forward wave second, where backward means toward the declared left port and forward
means toward the declared right port. A two-port behavior relates the complete state at the left
reference plane to the complete state at the right reference plane.

Scattering coordinates group the same four waves differently, as left/right incident amplitudes
followed by left/right outgoing amplitudes. `TwoPortScatteringBehavior.toBackwardFirst` performs
only this reversible regrouping. It does not solve an equation or assume that either view is
functional.

## ii. Scope

These are fixed-frequency complex-linear semantics. The reference-plane orientation and state
ordering are explicit, but no phase convention, propagation segment, termination, passivity,
reciprocity, causality, or electromagnetic realization is supplied. In particular, this file does
not infer chain functionality from a scattering matrix and introduces no block inverse. Those
results require the relevant transmission-block hypothesis.

Using the same underlying label type for both directions supplies only a bookkeeping correspondence
between coordinate families. It does not assert that opposite directions are physical time-reversal
partners.

Here “two-port” means two reference planes carrying four travelling waves. It is not the
separately named internal-ring two-port model used in some integrated-photonics sources.

## iii. Key definitions and results

- `BackwardFirstTravellingWaveState`: backward and forward amplitudes at one reference plane.
- `BackwardFirstTwoPortBehavior`: a relation between left and right travelling-wave states.
- `TwoPortScatteringBehavior`: the same physical variables grouped as incident and outgoing data.
- `TwoPortScatteringBehavior.toBackwardFirst`: reversible backward-first regrouping.

## iv. Table of contents

- A. Travelling-wave states and two-port relations
- B. Scattering-coordinate regrouping

-/

@[expose] public section

namespace Optics

noncomputable section

universe u v

/-!

## A. Travelling-wave states and two-port relations

-/

/-- A channel carrying a wave in the declared right-to-left direction. -/
@[ext]
structure BackwardWave (ι : Type u) where
  /-- The underlying transverse-mode label. -/
  channel : ι
  deriving DecidableEq, Fintype

/-- A channel carrying a wave in the declared left-to-right direction. -/
@[ext]
structure ForwardWave (ι : Type u) where
  /-- The underlying transverse-mode label. -/
  channel : ι
  deriving DecidableEq, Fintype

namespace BackwardWave

/-- The canonical equivalence from backward-wave channels to their transverse-mode labels. -/
def channelEquiv {ι : Type u} : BackwardWave ι ≃ ι where
  toFun := BackwardWave.channel
  invFun := BackwardWave.mk
  left_inv := by intro channel; cases channel; rfl
  right_inv := by intro channel; rfl

/-- The backward-wave equivalence exposes the underlying channel label. -/
@[simp]
lemma channelEquiv_apply {ι : Type u} (channel : BackwardWave ι) :
    channelEquiv channel = channel.channel := rfl

/-- The inverse backward-wave equivalence wraps an underlying channel label. -/
@[simp]
lemma channelEquiv_symm_apply {ι : Type u} (channel : ι) :
    channelEquiv.symm channel = ⟨channel⟩ := rfl

/-- An equivalence of transverse-mode labels lifted to backward-wave channels. -/
def relabelEquiv {ι : Type u} {κ : Type v} (equiv : ι ≃ κ) :
    BackwardWave ι ≃ BackwardWave κ :=
  channelEquiv.trans (equiv.trans channelEquiv.symm)

/-- Relabeling a backward-wave channel relabels its underlying transverse mode. -/
@[simp]
lemma relabelEquiv_apply {ι : Type u} {κ : Type v} (equiv : ι ≃ κ) (channel : ι) :
    relabelEquiv equiv ⟨channel⟩ = ⟨equiv channel⟩ := rfl

/-- Backward-wave channel wrapping preserves finite cardinality. -/
@[simp]
lemma fintype_card {ι : Type u} [Fintype ι] :
    Fintype.card (BackwardWave ι) = Fintype.card ι :=
  Fintype.card_congr channelEquiv

end BackwardWave

namespace ForwardWave

/-- The canonical equivalence from forward-wave channels to their transverse-mode labels. -/
def channelEquiv {ι : Type u} : ForwardWave ι ≃ ι where
  toFun := ForwardWave.channel
  invFun := ForwardWave.mk
  left_inv := by intro channel; cases channel; rfl
  right_inv := by intro channel; rfl

/-- The forward-wave equivalence exposes the underlying channel label. -/
@[simp]
lemma channelEquiv_apply {ι : Type u} (channel : ForwardWave ι) :
    channelEquiv channel = channel.channel := rfl

/-- The inverse forward-wave equivalence wraps an underlying channel label. -/
@[simp]
lemma channelEquiv_symm_apply {ι : Type u} (channel : ι) :
    channelEquiv.symm channel = ⟨channel⟩ := rfl

/-- An equivalence of transverse-mode labels lifted to forward-wave channels. -/
def relabelEquiv {ι : Type u} {κ : Type v} (equiv : ι ≃ κ) :
    ForwardWave ι ≃ ForwardWave κ :=
  channelEquiv.trans (equiv.trans channelEquiv.symm)

/-- Relabeling a forward-wave channel relabels its underlying transverse mode. -/
@[simp]
lemma relabelEquiv_apply {ι : Type u} {κ : Type v} (equiv : ι ≃ κ) (channel : ι) :
    relabelEquiv equiv ⟨channel⟩ = ⟨equiv channel⟩ := rfl

/-- Forward-wave channel wrapping preserves finite cardinality. -/
@[simp]
lemma fintype_card {ι : Type u} [Fintype ι] :
    Fintype.card (ForwardWave ι) = Fintype.card ι :=
  Fintype.card_congr channelEquiv

end ForwardWave

/-- The travelling-wave amplitudes at one oriented reference plane.

The left summand travels in the declared right-to-left direction and the right summand in the
declared left-to-right direction. Thus the state order is backward wave first and forward wave
second.
-/
abbrev BackwardFirstTravellingWaveState (ι : Type u) :=
  ModeAmplitude (BackwardWave ι ⊕ ForwardWave ι)

/-- A complex-linear relation between travelling-wave states at left and right reference planes.

This relation need not determine either state as a function of the other.
-/
abbrev BackwardFirstTwoPortBehavior (ι : Type u) (κ : Type v) :=
  LinearBehavior (BackwardWave ι ⊕ ForwardWave ι) (BackwardWave κ ⊕ ForwardWave κ)

/-- A two-port relation in scattering coordinates.

The input is the direct sum of left and right incident amplitudes. The output is the direct sum of
left and right outgoing amplitudes. This view need not be functional.
-/
abbrev TwoPortScatteringBehavior (ι : Type u) (κ : Type v) :=
  LinearBehavior (Incident ι ⊕ Incident κ) (Outgoing ι ⊕ Outgoing κ)

/-!

## B. Scattering-coordinate regrouping

-/

/-- The linear equivalence between scattering coordinates and backward-first reference-plane
states.

For incident data `(aL, aR)` and outgoing data `(bL, bR)`, the result is the left state
`(bL, aL)` and right state `(aR, bR)`. This is a coordinate permutation, not an input-output
solution.
-/
def scatteringBackwardFirstLinearEquiv {ι : Type u} {κ : Type v} :
    (ModeAmplitude (Incident ι ⊕ Incident κ) ×
      ModeAmplitude (Outgoing ι ⊕ Outgoing κ)) ≃ₗ[ℂ]
      (BackwardFirstTravellingWaveState ι × BackwardFirstTravellingWaveState κ) where
  toFun waves :=
    (WithLp.toLp 2 fun
        | Sum.inl backward => waves.2 (Sum.inl (Outgoing.mk backward.channel))
        | Sum.inr forward => waves.1 (Sum.inl (Incident.mk forward.channel)),
      WithLp.toLp 2 fun
        | Sum.inl backward => waves.1 (Sum.inr (Incident.mk backward.channel))
        | Sum.inr forward => waves.2 (Sum.inr (Outgoing.mk forward.channel)))
  invFun states :=
    (WithLp.toLp 2 fun
        | Sum.inl incident => states.1 (Sum.inr (ForwardWave.mk incident.channel))
        | Sum.inr incident => states.2 (Sum.inl (BackwardWave.mk incident.channel)),
      WithLp.toLp 2 fun
        | Sum.inl outgoing => states.1 (Sum.inl (BackwardWave.mk outgoing.channel))
        | Sum.inr outgoing => states.2 (Sum.inr (ForwardWave.mk outgoing.channel)))
  left_inv waves := by
    apply Prod.ext
    · apply WithLp.ofLp_injective 2
      funext index
      rcases index with ⟨index⟩ | ⟨index⟩ <;> rfl
    · apply WithLp.ofLp_injective 2
      funext index
      rcases index with ⟨index⟩ | ⟨index⟩ <;> rfl
  right_inv states := by
    apply Prod.ext
    · apply WithLp.ofLp_injective 2
      funext index
      rcases index with ⟨index⟩ | ⟨index⟩ <;> rfl
    · apply WithLp.ofLp_injective 2
      funext index
      rcases index with ⟨index⟩ | ⟨index⟩ <;> rfl
  map_add' first second := by
    apply Prod.ext
    · apply WithLp.ofLp_injective 2
      funext index
      rcases index with index | index <;> rfl
    · apply WithLp.ofLp_injective 2
      funext index
      rcases index with index | index <;> rfl
  map_smul' scalar waves := by
    apply Prod.ext
    · apply WithLp.ofLp_injective 2
      funext index
      rcases index with index | index <;> rfl
    · apply WithLp.ofLp_injective 2
      funext index
      rcases index with index | index <;> rfl

/-- Scattering coordinates regroup as left `(bL, aL)` and right `(aR, bR)` states. -/
@[simp]
lemma scatteringBackwardFirstLinearEquiv_apply {ι : Type u} {κ : Type v}
    (waves : ModeAmplitude (Incident ι ⊕ Incident κ) ×
      ModeAmplitude (Outgoing ι ⊕ Outgoing κ)) :
    scatteringBackwardFirstLinearEquiv waves =
      (WithLp.toLp 2 fun
          | Sum.inl backward => waves.2 (Sum.inl (Outgoing.mk backward.channel))
          | Sum.inr forward => waves.1 (Sum.inl (Incident.mk forward.channel)),
        WithLp.toLp 2 fun
          | Sum.inl backward => waves.1 (Sum.inr (Incident.mk backward.channel))
          | Sum.inr forward => waves.2 (Sum.inr (Outgoing.mk forward.channel))) := rfl

/-- Backward-first states ungroup as incident `(aL, aR)` and outgoing `(bL, bR)` data. -/
@[simp]
lemma scatteringBackwardFirstLinearEquiv_symm_apply {ι : Type u} {κ : Type v}
    (states : BackwardFirstTravellingWaveState ι × BackwardFirstTravellingWaveState κ) :
    scatteringBackwardFirstLinearEquiv.symm states =
      (WithLp.toLp 2 fun
          | Sum.inl incident => states.1 (Sum.inr (ForwardWave.mk incident.channel))
          | Sum.inr incident => states.2 (Sum.inl (BackwardWave.mk incident.channel)),
        WithLp.toLp 2 fun
          | Sum.inl outgoing => states.1 (Sum.inl (BackwardWave.mk outgoing.channel))
          | Sum.inr outgoing => states.2 (Sum.inr (ForwardWave.mk outgoing.channel))) := rfl

namespace TwoPortScatteringBehavior

variable {ι : Type u} {κ : Type v}

/-- Regroup a scattering-coordinate relation as a backward-first two-port behavior. -/
def toBackwardFirst (behavior : TwoPortScatteringBehavior ι κ) :
    BackwardFirstTwoPortBehavior ι κ :=
  behavior.map scatteringBackwardFirstLinearEquiv.toLinearMap

/-- Membership after scattering-coordinate regrouping is membership of the corresponding incident
and outgoing amplitudes in the original relation. -/
@[simp]
lemma mem_toBackwardFirst_iff (behavior : TwoPortScatteringBehavior ι κ)
    (left : BackwardFirstTravellingWaveState ι)
    (right : BackwardFirstTravellingWaveState κ) :
    (left, right) ∈ behavior.toBackwardFirst ↔
      scatteringBackwardFirstLinearEquiv.symm (left, right) ∈ behavior := by
  simp only [toBackwardFirst, Submodule.mem_map_equiv]

end TwoPortScatteringBehavior

namespace BackwardFirstTwoPortBehavior

variable {ι : Type u} {κ : Type v}

/-- Regroup a backward-first two-port relation as incident and outgoing scattering data. -/
def toScattering (behavior : BackwardFirstTwoPortBehavior ι κ) :
    TwoPortScatteringBehavior ι κ :=
  behavior.map scatteringBackwardFirstLinearEquiv.symm.toLinearMap

/-- Membership after scattering regrouping is membership of the corresponding backward-first
left and right states in the original relation. -/
@[simp]
lemma mem_toScattering_iff (behavior : BackwardFirstTwoPortBehavior ι κ)
    (incident : ModeAmplitude (Incident ι ⊕ Incident κ))
    (outgoing : ModeAmplitude (Outgoing ι ⊕ Outgoing κ)) :
    (incident, outgoing) ∈ behavior.toScattering ↔
      scatteringBackwardFirstLinearEquiv (incident, outgoing) ∈ behavior := by
  simp only [toScattering, Submodule.mem_map_equiv, LinearEquiv.symm_symm]

end BackwardFirstTwoPortBehavior

namespace TwoPortScatteringBehavior

variable {ι : Type u} {κ : Type v}

/-- Regrouping a scattering behavior to backward-first states and back changes no behavior. -/
@[simp]
lemma toScattering_toBackwardFirst (behavior : TwoPortScatteringBehavior ι κ) :
    behavior.toBackwardFirst.toScattering = behavior := by
  unfold BackwardFirstTwoPortBehavior.toScattering TwoPortScatteringBehavior.toBackwardFirst
  exact (Submodule.map_symm_eq_iff scatteringBackwardFirstLinearEquiv).mpr rfl

end TwoPortScatteringBehavior

namespace BackwardFirstTwoPortBehavior

variable {ι : Type u} {κ : Type v}

/-- Regrouping a backward-first behavior to scattering data and back changes no behavior. -/
@[simp]
lemma toBackwardFirst_toScattering (behavior : BackwardFirstTwoPortBehavior ι κ) :
    behavior.toScattering.toBackwardFirst = behavior := by
  unfold toScattering TwoPortScatteringBehavior.toBackwardFirst
  exact (Submodule.map_symm_eq_iff scatteringBackwardFirstLinearEquiv).mp rfl

end BackwardFirstTwoPortBehavior

end

end Optics
