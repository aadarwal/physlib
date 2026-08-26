/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.TwoPortBehavior

/-!
# Typed two-port scattering transforms

## i. Overview

A `ScatteringMatrix (ι ⊕ κ)` uses one sum of raw channel labels, whereas a two-port behavior uses
separately wrapped left and right incident and outgoing channel families. This file supplies the
canonical adapter between those presentations. It changes only index labels: every matrix entry
and the induced graph behavior are preserved.

## ii. Key results

- `TwoPortScatteringTransform`: a transform from left/right incident channels to left/right
  outgoing channels.
- `TwoPortScatteringTransform.ofOriented`: split combined endpoint labels without changing a
  transform.
- `ScatteringMatrix.toTwoPortScatteringTransform`: the canonical typed two-port adapter.
- `ScatteringMatrix.toTwoPortScatteringBehavior`: its graph behavior.
- `ScatteringMatrix.mem_toTwoPortScatteringBehavior_iff`: behavior-level agreement with the
  oriented scattering transform.

## iii. Table of contents

- A. Typed two-port scattering adapter
- B. Agreement of graph behaviors

## iv. References

The binary sum records the declared left/right port order. The adapter does not select propagation
directions, pair time-reversed modes, infer a chain view, or impose losslessness, reciprocity,
passivity, or transmission-block invertibility.

-/

@[expose] public section

namespace Optics

noncomputable section

universe u v

/-!

## A. Typed two-port scattering adapter

-/

/-- A two-port scattering transform with separately typed left/right incident and outgoing ends. -/
abbrev TwoPortScatteringTransform (ι : Type u) (κ : Type v) :=
  ModeTransform (Incident ι ⊕ Incident κ) (Outgoing ι ⊕ Outgoing κ)

namespace TwoPortScatteringTransform

/-- Split the combined incident and outgoing labels of an oriented transform into ordered left and
right endpoint families. -/
def ofOriented {ι : Type u} {κ : Type v}
    (transform : ModeTransform (Incident (ι ⊕ κ)) (Outgoing (ι ⊕ κ))) :
    TwoPortScatteringTransform ι κ :=
  transform.reindex Incident.splitSumEquiv Outgoing.splitSumEquiv

/-- Recombining the endpoint labels of a split oriented transform recovers the original
transform. -/
@[simp]
lemma reindex_symm_ofOriented {ι : Type u} {κ : Type v}
    (transform : ModeTransform (Incident (ι ⊕ κ)) (Outgoing (ι ⊕ κ))) :
    (ofOriented transform).reindex Incident.splitSumEquiv.symm
        Outgoing.splitSumEquiv.symm = transform :=
  ModeTransform.reindex_symm_reindex Incident.splitSumEquiv Outgoing.splitSumEquiv transform

end TwoPortScatteringTransform

/-- Relabel a scattering matrix on a sum of channels as a typed two-port scattering transform.

The left summand is the declared left port and the right summand is the declared right port. This
is a pure coordinate adapter; it neither permutes scattering roles nor solves for chain variables.
-/
def ScatteringMatrix.toTwoPortScatteringTransform {ι : Type u} {κ : Type v}
    (scattering : ScatteringMatrix (ι ⊕ κ)) : TwoPortScatteringTransform ι κ :=
  TwoPortScatteringTransform.ofOriented scattering.toOrientedModeTransform

/-- The typed two-port adapter evaluates the oriented transform at the recombined endpoint
labels. -/
lemma ScatteringMatrix.toTwoPortScatteringTransform_apply {ι : Type u} {κ : Type v}
    (scattering : ScatteringMatrix (ι ⊕ κ))
    (output : Outgoing ι ⊕ Outgoing κ) (input : Incident ι ⊕ Incident κ) :
    scattering.toTwoPortScatteringTransform output input =
      scattering.toOrientedModeTransform (Outgoing.splitSumEquiv.symm output)
        (Incident.splitSumEquiv.symm input) := rfl

/-- The typed two-port adapter retains the left-reflection entries. -/
@[simp]
lemma ScatteringMatrix.toTwoPortScatteringTransform_apply_inl_inl
    {ι : Type u} {κ : Type v} (scattering : ScatteringMatrix (ι ⊕ κ))
    (output input : ι) :
    scattering.toTwoPortScatteringTransform (Sum.inl ⟨output⟩) (Sum.inl ⟨input⟩) =
      scattering.toModeTransform (Sum.inl output) (Sum.inl input) := rfl

/-- The typed two-port adapter retains the right-to-left transmission entries. -/
@[simp]
lemma ScatteringMatrix.toTwoPortScatteringTransform_apply_inl_inr
    {ι : Type u} {κ : Type v} (scattering : ScatteringMatrix (ι ⊕ κ))
    (output : ι) (input : κ) :
    scattering.toTwoPortScatteringTransform (Sum.inl ⟨output⟩) (Sum.inr ⟨input⟩) =
      scattering.toModeTransform (Sum.inl output) (Sum.inr input) := rfl

/-- The typed two-port adapter retains the left-to-right transmission entries. -/
@[simp]
lemma ScatteringMatrix.toTwoPortScatteringTransform_apply_inr_inl
    {ι : Type u} {κ : Type v} (scattering : ScatteringMatrix (ι ⊕ κ))
    (output : κ) (input : ι) :
    scattering.toTwoPortScatteringTransform (Sum.inr ⟨output⟩) (Sum.inl ⟨input⟩) =
      scattering.toModeTransform (Sum.inr output) (Sum.inl input) := rfl

/-- The typed two-port adapter retains the right-reflection entries. -/
@[simp]
lemma ScatteringMatrix.toTwoPortScatteringTransform_apply_inr_inr
    {ι : Type u} {κ : Type v} (scattering : ScatteringMatrix (ι ⊕ κ))
    (output input : κ) :
    scattering.toTwoPortScatteringTransform (Sum.inr ⟨output⟩) (Sum.inr ⟨input⟩) =
      scattering.toModeTransform (Sum.inr output) (Sum.inr input) := rfl

/-- The typed adapter commutes with relabeling a combined incident amplitude into separate left and
right endpoint families. -/
lemma ScatteringMatrix.toLinearMap_toTwoPortScatteringTransform_apply
    {ι : Type u} {κ : Type v} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (scattering : ScatteringMatrix (ι ⊕ κ))
    (amplitude : ModeAmplitude (Incident (ι ⊕ κ))) :
    scattering.toTwoPortScatteringTransform.toLinearMap
        (ModeAmplitude.reindex Incident.splitSumEquiv amplitude) =
      ModeAmplitude.reindex Outgoing.splitSumEquiv
        (scattering.toOrientedModeTransform.toLinearMap amplitude) :=
  ModeTransform.toLinearMap_reindex_apply Incident.splitSumEquiv Outgoing.splitSumEquiv
    scattering.toOrientedModeTransform amplitude

/-- The typed two-port adapter acts by returning incident amplitudes to the combined endpoint
family, applying the oriented scattering transform, and redistributing the outgoing amplitudes. -/
lemma ScatteringMatrix.toLinearMap_toTwoPortScatteringTransform_eq
    {ι : Type u} {κ : Type v} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (scattering : ScatteringMatrix (ι ⊕ κ))
    (amplitude : ModeAmplitude (Incident ι ⊕ Incident κ)) :
    scattering.toTwoPortScatteringTransform.toLinearMap amplitude =
      ModeAmplitude.reindex Outgoing.splitSumEquiv
        (scattering.toOrientedModeTransform.toLinearMap
          (ModeAmplitude.reindex Incident.splitSumEquiv.symm amplitude)) :=
  ModeTransform.toLinearMap_reindex_eq Incident.splitSumEquiv Outgoing.splitSumEquiv
    scattering.toOrientedModeTransform amplitude

/-- Losslessness of a scattering matrix is preserved and reflected by the typed two-port
adapter. -/
lemma ScatteringMatrix.isLossless_iff_toTwoPortScatteringTransform_isPowerPreserving
    {ι : Type u} {κ : Type v} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (scattering : ScatteringMatrix (ι ⊕ κ)) :
    scattering.IsLossless ↔ scattering.toTwoPortScatteringTransform.IsPowerPreserving := by
  rw [ScatteringMatrix.isLossless_iff_toOrientedModeTransform_isPowerPreserving]
  exact (ModeTransform.isPowerPreserving_reindex_iff Incident.splitSumEquiv
    Outgoing.splitSumEquiv scattering.toOrientedModeTransform).symm

/-!

## B. Agreement of graph behaviors

-/

/-- The scattering behavior induced by the canonical typed two-port adapter. -/
def ScatteringMatrix.toTwoPortScatteringBehavior {ι : Type u} {κ : Type v}
    [Fintype ι] [Fintype κ] (scattering : ScatteringMatrix (ι ⊕ κ)) :
    TwoPortScatteringBehavior ι κ :=
  scattering.toTwoPortScatteringTransform.toBehavior

/-- A pair belongs to the typed two-port scattering behavior exactly when the oriented transform
maps the recombined incident amplitude to the recombined outgoing amplitude. -/
lemma ScatteringMatrix.mem_toTwoPortScatteringBehavior_iff
    {ι : Type u} {κ : Type v} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (scattering : ScatteringMatrix (ι ⊕ κ))
    (incident : ModeAmplitude (Incident ι ⊕ Incident κ))
    (outgoing : ModeAmplitude (Outgoing ι ⊕ Outgoing κ)) :
    (incident, outgoing) ∈ scattering.toTwoPortScatteringBehavior ↔
      outgoing = ModeAmplitude.reindex Outgoing.splitSumEquiv
        (scattering.toOrientedModeTransform.toLinearMap
          (ModeAmplitude.reindex Incident.splitSumEquiv.symm incident)) := by
  rw [ScatteringMatrix.toTwoPortScatteringBehavior,
    ModeTransform.mem_toBehavior_iff_toLinearMap,
    ScatteringMatrix.toLinearMap_toTwoPortScatteringTransform_eq]

end

end Optics
