/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Mode.Reindex

/-!
# Typed optical ports and ideal routing

## i. Overview

This file introduces the type boundary between optical components and the connections that join
them. A port family has a possibly dependent mode type over each port, and its flattened channel
type is their dependent sum. Incident and outgoing channel ends are deliberately distinct wrapper
types: component scattering maps incident amplitudes to outgoing amplitudes, while a connection
routes outgoing amplitudes back to incident amplitudes.

Equivalences and embeddings of underlying channel labels lift separately to both nominal endpoint
types, preserving the boundary while supporting later ambient routing.

A local connection connects two distinct ports by an explicit equivalence between their mode fibers.
Its local channel labels form a binary sum. The induced mate equivalence swaps the two ends, is an
involution, and has no fixed point. Ideal unit-gain routing is the identity mode transform relabeled
along that mate equivalence, so its exact endpoint action and modal-power preservation follow from
the existing convention-free reindexing API.

## ii. Scope

This file models one local bidirectional connection. It does not yet assemble finite connection
families, enforce global endpoint uniqueness, expose external channels, or solve feedback
equations. It adds no path phase, delay, attenuation, non-unit gain, reference-plane transport,
reciprocity data, time-reversal pairing, fan-out, termination, or physical Poynting-flux
interpretation. Splitters and combiners are components rather than one-to-many connections.

## iii. Key results

- `Incident.splitSumEquiv` and `Outgoing.splitSumEquiv`: distribute directed endpoint wrappers over
  a binary sum of channel families.
- `Incident.relabelEmbedding` and `Outgoing.relabelEmbedding`: lift a channel embedding without
  erasing the nominal endpoint type.
- `PortConnection.channelEmbedding`: embeds both local mode fibers in the flattened channel type.
- `PortConnection.symm` and `PortConnection.swapLocalChannel`: exchange endpoint presentation
  without changing the flattened connection.
- `PortConnection.mateEquiv`: swaps the two connected channel families using the supplied mode
  equivalence.
- `PortConnection.mateEquiv_apply_apply`: mating twice recovers the original local channel.
- `PortConnection.mateEquiv_ne_self`: a connection never mates a local channel to itself.
- `ScatteringMatrix.toOrientedModeTransform`: exposes the component boundary as incident to
  outgoing amplitudes.
- `ModeTransform.idealRouting`: unit-gain routing from outgoing to incident amplitudes.
- `ModeTransform.idealRouting_apply`: routing preserves the amplitude at the matched endpoint.
- `ModeTransform.idealRouting_isPowerPreserving`: ideal routing preserves normalized modal power.
- `ModeTransform.idealRouting_conjTranspose_mul_self` and
  `ModeTransform.idealRouting_mul_conjTranspose`: both ideal-routing Gram matrices are identities.
- `ModeTransform.idealRouting_reindex`: routing is covariant under endpoint relabeling.
- `PortConnection.idealRouting_mul_toOrientedModeTransform_apply`: the local `C * S` product has
  the intended incident-space action order.

## iv. Table of contents

- A. Port families and directed channel ends
- B. Local bidirectional connections
- C. Typed scattering boundary
- D. Ideal unit-gain routing

-/

@[expose] public section

namespace Optics

open Matrix
open scoped ComplexConjugate

noncomputable section

universe u v w x

/-!

## A. Port families and directed channel ends

-/

-- The two universe levels are intentional: port labels and mode fibers are independent types.
set_option linter.checkUnivs false in
/-- A family of optical mode labels indexed by physical ports.

Finiteness is deliberately absent: only later finite-dimensional amplitude operations require it.
-/
structure PortModeFamily where
  /-- The type of physical ports. -/
  Port : Type u
  /-- The type of mode labels available at each physical port. -/
  Mode : Port → Type v

namespace PortModeFamily

/-- The flattened dependent channel type of a port family. -/
abbrev Channel (P : PortModeFamily.{u, v}) := Σ port, P.Mode port

end PortModeFamily

/-- An incident channel end, kept nominally distinct from an outgoing channel end. -/
@[ext]
structure Incident (ι : Type u) where
  /-- The underlying channel label. -/
  channel : ι
  deriving DecidableEq, Fintype

/-- An outgoing channel end, kept nominally distinct from an incident channel end. -/
@[ext]
structure Outgoing (ι : Type u) where
  /-- The underlying channel label. -/
  channel : ι
  deriving DecidableEq, Fintype

namespace Incident

/-- Lift an explicitly supplied finite channel enumeration to incident endpoint labels. -/
@[instance_reducible]
def fintypeOf {ι : Type u} (fintype : Fintype ι) : Fintype (Incident ι) := by
  letI := fintype
  infer_instance

/-- The canonical equivalence from incident channel ends to their underlying labels. -/
def channelEquiv {ι : Type u} : Incident ι ≃ ι where
  toFun := Incident.channel
  invFun := Incident.mk
  left_inv := by intro i; cases i; rfl
  right_inv := by intro i; rfl

/-- The incident-end equivalence exposes the underlying channel label. -/
@[simp]
lemma channelEquiv_apply {ι : Type u} (i : Incident ι) : channelEquiv i = i.channel := rfl

/-- The inverse incident-end equivalence wraps an underlying channel label. -/
@[simp]
lemma channelEquiv_symm_apply {ι : Type u} (i : ι) : channelEquiv.symm i = ⟨i⟩ := rfl

/-- An equivalence of underlying labels lifted to incident channel ends. -/
def relabelEquiv {ι : Type u} {κ : Type v} (e : ι ≃ κ) : Incident ι ≃ Incident κ :=
  channelEquiv.trans (e.trans channelEquiv.symm)

/-- Relabeling an incident endpoint relabels its underlying channel. -/
@[simp]
lemma relabelEquiv_apply {ι : Type u} {κ : Type v} (e : ι ≃ κ) (i : ι) :
    relabelEquiv e (Incident.mk i) = Incident.mk (e i) := rfl

/-- The canonical equivalence distributing incident channel ends over a binary sum. -/
def splitSumEquiv {ι : Type u} {κ : Type v} :
    Incident (ι ⊕ κ) ≃ Incident ι ⊕ Incident κ :=
  channelEquiv.trans (channelEquiv.symm.sumCongr channelEquiv.symm)

/-- Distributing incident ends sends a left channel to the left family. -/
@[simp]
lemma splitSumEquiv_apply_inl {ι : Type u} {κ : Type v} (i : ι) :
    (splitSumEquiv : Incident (ι ⊕ κ) ≃ Incident ι ⊕ Incident κ) ⟨Sum.inl i⟩ =
      Sum.inl ⟨i⟩ := rfl

/-- Distributing incident ends sends a right channel to the right family. -/
@[simp]
lemma splitSumEquiv_apply_inr {ι : Type u} {κ : Type v} (i : κ) :
    (splitSumEquiv : Incident (ι ⊕ κ) ≃ Incident ι ⊕ Incident κ) ⟨Sum.inr i⟩ =
      Sum.inr ⟨i⟩ := rfl

/-- Recombining a left incident family wraps its channel in the left summand. -/
@[simp]
lemma splitSumEquiv_symm_apply_inl {ι : Type u} {κ : Type v} (i : Incident ι) :
    (splitSumEquiv : Incident (ι ⊕ κ) ≃ Incident ι ⊕ Incident κ).symm (Sum.inl i) =
      ⟨Sum.inl i.channel⟩ := by
  cases i
  rfl

/-- Recombining a right incident family wraps its channel in the right summand. -/
@[simp]
lemma splitSumEquiv_symm_apply_inr {ι : Type u} {κ : Type v} (i : Incident κ) :
    (splitSumEquiv : Incident (ι ⊕ κ) ≃ Incident ι ⊕ Incident κ).symm (Sum.inr i) =
      ⟨Sum.inr i.channel⟩ := by
  cases i
  rfl

/-- An embedding of underlying labels lifted to incident channel ends. -/
def relabelEmbedding {ι : Type u} {κ : Type v} (embedding : ι ↪ κ) :
    Incident ι ↪ Incident κ where
  toFun endpoint := Incident.mk (embedding endpoint.channel)
  inj' := by
    intro first second hEndpoint
    apply Incident.ext
    exact embedding.injective (congrArg Incident.channel hEndpoint)

/-- Lifting an embedding to incident ends maps the wrapped underlying label. -/
@[simp]
lemma relabelEmbedding_apply {ι : Type u} {κ : Type v} (embedding : ι ↪ κ) (i : ι) :
    relabelEmbedding embedding (Incident.mk i) = Incident.mk (embedding i) := rfl

/-- An incident endpoint is selected by a lifted embedding exactly when its channel is selected by
the underlying embedding. -/
lemma mk_mem_range_relabelEmbedding_iff {ι : Type u} {κ : Type v}
    (embedding : ι ↪ κ) (i : κ) :
    Incident.mk i ∈ Set.range (relabelEmbedding embedding) ↔ i ∈ Set.range embedding := by
  constructor
  · rintro ⟨endpoint, hEndpoint⟩
    exact ⟨endpoint.channel, congrArg Incident.channel hEndpoint⟩
  · rintro ⟨channel, rfl⟩
    exact ⟨Incident.mk channel, rfl⟩

end Incident

namespace Outgoing

/-- Lift an explicitly supplied finite channel enumeration to outgoing endpoint labels. -/
@[instance_reducible]
def fintypeOf {ι : Type u} (fintype : Fintype ι) : Fintype (Outgoing ι) := by
  letI := fintype
  infer_instance

/-- The canonical equivalence from outgoing channel ends to their underlying labels. -/
def channelEquiv {ι : Type u} : Outgoing ι ≃ ι where
  toFun := Outgoing.channel
  invFun := Outgoing.mk
  left_inv := by intro i; cases i; rfl
  right_inv := by intro i; rfl

/-- The outgoing-end equivalence exposes the underlying channel label. -/
@[simp]
lemma channelEquiv_apply {ι : Type u} (i : Outgoing ι) : channelEquiv i = i.channel := rfl

/-- The inverse outgoing-end equivalence wraps an underlying channel label. -/
@[simp]
lemma channelEquiv_symm_apply {ι : Type u} (i : ι) : channelEquiv.symm i = ⟨i⟩ := rfl

/-- An equivalence of underlying labels lifted to outgoing channel ends. -/
def relabelEquiv {ι : Type u} {κ : Type v} (e : ι ≃ κ) : Outgoing ι ≃ Outgoing κ :=
  channelEquiv.trans (e.trans channelEquiv.symm)

/-- Relabeling an outgoing endpoint relabels its underlying channel. -/
@[simp]
lemma relabelEquiv_apply {ι : Type u} {κ : Type v} (e : ι ≃ κ) (i : ι) :
    relabelEquiv e (Outgoing.mk i) = Outgoing.mk (e i) := rfl

/-- The canonical equivalence distributing outgoing channel ends over a binary sum. -/
def splitSumEquiv {ι : Type u} {κ : Type v} :
    Outgoing (ι ⊕ κ) ≃ Outgoing ι ⊕ Outgoing κ :=
  channelEquiv.trans (channelEquiv.symm.sumCongr channelEquiv.symm)

/-- Distributing outgoing ends sends a left channel to the left family. -/
@[simp]
lemma splitSumEquiv_apply_inl {ι : Type u} {κ : Type v} (i : ι) :
    (splitSumEquiv : Outgoing (ι ⊕ κ) ≃ Outgoing ι ⊕ Outgoing κ) ⟨Sum.inl i⟩ =
      Sum.inl ⟨i⟩ := rfl

/-- Distributing outgoing ends sends a right channel to the right family. -/
@[simp]
lemma splitSumEquiv_apply_inr {ι : Type u} {κ : Type v} (i : κ) :
    (splitSumEquiv : Outgoing (ι ⊕ κ) ≃ Outgoing ι ⊕ Outgoing κ) ⟨Sum.inr i⟩ =
      Sum.inr ⟨i⟩ := rfl

/-- Recombining a left outgoing family wraps its channel in the left summand. -/
@[simp]
lemma splitSumEquiv_symm_apply_inl {ι : Type u} {κ : Type v} (i : Outgoing ι) :
    (splitSumEquiv : Outgoing (ι ⊕ κ) ≃ Outgoing ι ⊕ Outgoing κ).symm (Sum.inl i) =
      ⟨Sum.inl i.channel⟩ := by
  cases i
  rfl

/-- Recombining a right outgoing family wraps its channel in the right summand. -/
@[simp]
lemma splitSumEquiv_symm_apply_inr {ι : Type u} {κ : Type v} (i : Outgoing κ) :
    (splitSumEquiv : Outgoing (ι ⊕ κ) ≃ Outgoing ι ⊕ Outgoing κ).symm (Sum.inr i) =
      ⟨Sum.inr i.channel⟩ := by
  cases i
  rfl

/-- An embedding of underlying labels lifted to outgoing channel ends. -/
def relabelEmbedding {ι : Type u} {κ : Type v} (embedding : ι ↪ κ) :
    Outgoing ι ↪ Outgoing κ where
  toFun endpoint := Outgoing.mk (embedding endpoint.channel)
  inj' := by
    intro first second hEndpoint
    apply Outgoing.ext
    exact embedding.injective (congrArg Outgoing.channel hEndpoint)

/-- Lifting an embedding to outgoing ends maps the wrapped underlying label. -/
@[simp]
lemma relabelEmbedding_apply {ι : Type u} {κ : Type v} (embedding : ι ↪ κ) (i : ι) :
    relabelEmbedding embedding (Outgoing.mk i) = Outgoing.mk (embedding i) := rfl

/-- An outgoing endpoint is selected by a lifted embedding exactly when its channel is selected by
the underlying embedding. -/
lemma mk_mem_range_relabelEmbedding_iff {ι : Type u} {κ : Type v}
    (embedding : ι ↪ κ) (i : κ) :
    Outgoing.mk i ∈ Set.range (relabelEmbedding embedding) ↔ i ∈ Set.range embedding := by
  constructor
  · rintro ⟨endpoint, hEndpoint⟩
    exact ⟨endpoint.channel, congrArg Outgoing.channel hEndpoint⟩
  · rintro ⟨channel, rfl⟩
    exact ⟨Outgoing.mk channel, rfl⟩

end Outgoing

/-- An underlying channel equivalence lifted from outgoing ends to incident ends.

This is typed connection data, not a pairing of time-reversed physical modes.
-/
def outgoingToIncidentEquiv {ι : Type u} {κ : Type v} (e : ι ≃ κ) :
    Outgoing ι ≃ Incident κ :=
  Outgoing.channelEquiv.trans (e.trans Incident.channelEquiv.symm)

/-- Lifting a channel equivalence maps an outgoing endpoint to the matching incident endpoint. -/
@[simp]
lemma outgoingToIncidentEquiv_apply {ι : Type u} {κ : Type v} (e : ι ≃ κ) (i : ι) :
    outgoingToIncidentEquiv e (Outgoing.mk i) = Incident.mk (e i) := rfl

/-- The inverse lifted equivalence maps an incident endpoint back to the matching outgoing
endpoint. -/
@[simp]
lemma outgoingToIncidentEquiv_symm_apply {ι : Type u} {κ : Type v} (e : ι ≃ κ) (i : κ) :
    (outgoingToIncidentEquiv e).symm (Incident.mk i) = Outgoing.mk (e.symm i) := rfl

/-!

## B. Local bidirectional connections

-/

/-- A bidirectional local connection between two distinct ports.

The mode equivalence states exactly which mode at the left port is paired with each mode at the
right port. No phase or propagation law is stored in this topological connection. -/
structure PortConnection (P : PortModeFamily.{u, v}) where
  /-- The first endpoint port. -/
  left : P.Port
  /-- The second endpoint port. -/
  right : P.Port
  /-- A connection cannot join a port to itself. -/
  left_ne_right : left ≠ right
  /-- The compatible one-to-one matching between the endpoint mode fibers. -/
  modeEquiv : P.Mode left ≃ P.Mode right

namespace PortConnection

variable {P : PortModeFamily.{u, v}} (connection : PortConnection P)

/-- The same physical connection presented with its two endpoints exchanged. -/
def symm : PortConnection P where
  left := connection.right
  right := connection.left
  left_ne_right := connection.left_ne_right.symm
  modeEquiv := connection.modeEquiv.symm

/-- Exchanging the endpoints of a connection twice recovers its original presentation. -/
@[simp]
lemma symm_symm : connection.symm.symm = connection := by
  cases connection
  rfl

/-- The disjoint local channel labels at the two endpoints of a connection. -/
abbrev LocalChannel := P.Mode connection.left ⊕ P.Mode connection.right

/-- The local-channel relabeling induced by exchanging a connection's endpoint presentation. -/
def swapLocalChannel : connection.LocalChannel ≃ connection.symm.LocalChannel :=
  Equiv.sumComm _ _

/-- Exchanging endpoint presentation sends a left local channel to the right summand. -/
@[simp]
lemma swapLocalChannel_inl (mode : P.Mode connection.left) :
    connection.swapLocalChannel (Sum.inl mode) = Sum.inr mode := rfl

/-- Exchanging endpoint presentation sends a right local channel to the left summand. -/
@[simp]
lemma swapLocalChannel_inr (mode : P.Mode connection.right) :
    connection.swapLocalChannel (Sum.inr mode) = Sum.inl mode := rfl

/-- The injection of a connection's two local mode fibers into the flattened port-family
channels. -/
def channelEmbedding : connection.LocalChannel ↪ P.Channel where
  toFun
    | Sum.inl mode => ⟨connection.left, mode⟩
    | Sum.inr mode => ⟨connection.right, mode⟩
  inj' := by
    intro x y hxy
    rcases x with x | x <;> rcases y with y | y
    · cases hxy
      rfl
    · exact (connection.left_ne_right (congrArg Sigma.fst hxy)).elim
    · exact (connection.left_ne_right (congrArg Sigma.fst hxy).symm).elim
    · cases hxy
      rfl

/-- The local-channel embedding sends a left mode to the corresponding flattened channel. -/
@[simp]
lemma channelEmbedding_inl (mode : P.Mode connection.left) :
    connection.channelEmbedding (Sum.inl mode) = ⟨connection.left, mode⟩ := rfl

/-- The local-channel embedding sends a right mode to the corresponding flattened channel. -/
@[simp]
lemma channelEmbedding_inr (mode : P.Mode connection.right) :
    connection.channelEmbedding (Sum.inr mode) = ⟨connection.right, mode⟩ := rfl

/-- Exchanging endpoint presentation does not change the flattened channel selected by a local
label. -/
lemma symm_channelEmbedding_swapLocalChannel (channel : connection.LocalChannel) :
    connection.symm.channelEmbedding (connection.swapLocalChannel channel) =
      connection.channelEmbedding channel := by
  rcases channel with mode | mode <;> rfl

/-- The endpoint-mate equivalence induced by a bidirectional connection.

It sends a left mode to its matched right mode and a right mode back along the inverse matching.
-/
def mateEquiv : connection.LocalChannel ≃ connection.LocalChannel where
  toFun
    | Sum.inl mode => Sum.inr (connection.modeEquiv mode)
    | Sum.inr mode => Sum.inl (connection.modeEquiv.symm mode)
  invFun
    | Sum.inl mode => Sum.inr (connection.modeEquiv mode)
    | Sum.inr mode => Sum.inl (connection.modeEquiv.symm mode)
  left_inv := by
    intro channel
    rcases channel with mode | mode <;> simp
  right_inv := by
    intro channel
    rcases channel with mode | mode <;> simp

/-- The mate of a left channel is its mode-equivalent right channel. -/
@[simp]
lemma mateEquiv_inl (mode : P.Mode connection.left) :
    connection.mateEquiv (Sum.inl mode) = Sum.inr (connection.modeEquiv mode) := rfl

/-- The mate of a right channel is its inverse-mode-equivalent left channel. -/
@[simp]
lemma mateEquiv_inr (mode : P.Mode connection.right) :
    connection.mateEquiv (Sum.inr mode) = Sum.inl (connection.modeEquiv.symm mode) := rfl

/-- Taking the endpoint mate twice recovers the original local channel. -/
@[simp]
lemma mateEquiv_apply_apply (channel : connection.LocalChannel) :
    connection.mateEquiv (connection.mateEquiv channel) = channel := by
  rcases channel with mode | mode <;> simp

/-- Endpoint mating is independent of which endpoint is presented first. -/
lemma swapLocalChannel_mateEquiv (channel : connection.LocalChannel) :
    connection.swapLocalChannel (connection.mateEquiv channel) =
      connection.symm.mateEquiv (connection.swapLocalChannel channel) := by
  rcases channel with mode | mode <;> rfl

/-- No local channel is its own mate. -/
lemma mateEquiv_ne_self (channel : connection.LocalChannel) :
    connection.mateEquiv channel ≠ channel := by
  rcases channel with mode | mode <;> simp

end PortConnection

/-!

## C. Typed scattering boundary

-/

/-- The component-oriented transform underlying a scattering matrix.

This canonical adapter makes the matrix's physically distinct incident domain and outgoing
codomain explicit without giving the wrapped scattering matrix an ordinary cascade operation. -/
def ScatteringMatrix.toOrientedModeTransform {ι : Type u} (scattering : ScatteringMatrix ι) :
    ModeTransform (Incident ι) (Outgoing ι) :=
  scattering.toModeTransform.reindex Incident.channelEquiv.symm Outgoing.channelEquiv.symm

/-- The oriented scattering adapter retains every entry of the underlying scattering matrix. -/
@[simp]
lemma ScatteringMatrix.toOrientedModeTransform_apply {ι : Type u}
    (scattering : ScatteringMatrix ι) (output input : ι) :
    scattering.toOrientedModeTransform (Outgoing.mk output) (Incident.mk input) =
      scattering.toModeTransform output input := rfl

/-- The oriented scattering adapter acts by removing incident wrappers, applying the underlying
transform, and wrapping the resulting outgoing labels. -/
lemma ScatteringMatrix.toLinearMap_toOrientedModeTransform {ι : Type u}
    [Fintype ι] [DecidableEq ι] (scattering : ScatteringMatrix ι)
    (amplitude : ModeAmplitude (Incident ι)) :
    scattering.toOrientedModeTransform.toLinearMap amplitude =
      ModeAmplitude.reindex Outgoing.channelEquiv.symm
        (scattering.toModeTransform.toLinearMap
          (ModeAmplitude.reindex Incident.channelEquiv amplitude)) := by
  simpa only [ScatteringMatrix.toOrientedModeTransform, Equiv.symm_symm] using
    ModeTransform.toLinearMap_reindex_eq Incident.channelEquiv.symm
      Outgoing.channelEquiv.symm scattering.toModeTransform amplitude

/-- A scattering matrix is lossless exactly when its oriented transform preserves normalized
modal power. -/
lemma ScatteringMatrix.isLossless_iff_toOrientedModeTransform_isPowerPreserving
    {ι : Type u} [Fintype ι] [DecidableEq ι] (scattering : ScatteringMatrix ι) :
    scattering.IsLossless ↔ scattering.toOrientedModeTransform.IsPowerPreserving := by
  rw [ScatteringMatrix.isLossless_iff_isPowerPreserving]
  exact (ModeTransform.isPowerPreserving_reindex_iff Incident.channelEquiv.symm
    Outgoing.channelEquiv.symm scattering.toModeTransform).symm

/-!

## D. Ideal unit-gain routing

-/

/-- The unit-gain routing transform induced by an equivalence of underlying channel labels.

The transform has the network orientation `Outgoing → Incident`; it is not a component scattering
matrix and therefore does not inherit component composition semantics. -/
def ModeTransform.idealRouting {ι : Type u} {κ : Type v} [DecidableEq ι] (e : ι ≃ κ) :
    ModeTransform (Outgoing ι) (Incident κ) :=
  (1 : ModeTransform (Outgoing ι) (Outgoing ι)).reindex (Equiv.refl _)
    (outgoingToIncidentEquiv e)

/-- The ideal-routing matrix has unit gain precisely at the channel selected by the equivalence. -/
@[simp]
lemma ModeTransform.idealRouting_entry {ι : Type u} {κ : Type v} [DecidableEq ι]
    [DecidableEq κ] (e : ι ≃ κ)
    (output : Incident κ) (input : Outgoing ι) :
    ModeTransform.idealRouting e output input =
      if output = outgoingToIncidentEquiv e input then (1 : ℂ) else 0 := by
  classical
  by_cases hMatched : output = outgoingToIncidentEquiv e input
  · subst output
    simp [ModeTransform.idealRouting, Matrix.one_apply]
  · have hOld : (outgoingToIncidentEquiv e).symm output ≠ input := by
      intro hEqual
      apply hMatched
      rw [← hEqual]
      simp
    simp [ModeTransform.idealRouting, Matrix.one_apply, hMatched, hOld]

/-- Ideal routing acts by isometric relabeling of outgoing amplitudes as incident amplitudes. -/
lemma ModeTransform.toLinearMap_idealRouting {ι : Type u} {κ : Type v}
    [Fintype ι] [DecidableEq ι] [Fintype κ] (e : ι ≃ κ)
    (amplitude : ModeAmplitude (Outgoing ι)) :
    (ModeTransform.idealRouting e).toLinearMap amplitude =
      ModeAmplitude.reindex (outgoingToIncidentEquiv e) amplitude := by
  rw [ModeTransform.idealRouting, ModeTransform.toLinearMap_reindex_eq]
  have hRefl :
      ModeAmplitude.reindex (Equiv.refl (Outgoing ι)).symm amplitude = amplitude := by
    ext input
    rfl
  rw [hRefl]
  unfold ModeTransform.toLinearMap
  unfold Matrix.toEuclideanLin
  have hOne :
      (Matrix.toLpLin 2 2) (1 : ModeTransform (Outgoing ι) (Outgoing ι)) =
        LinearMap.id := Matrix.toLpLin_one (R := ℂ) (n := Outgoing ι) 2
  have hOneApply := congrArg
    (fun linearMap : ModeAmplitude (Outgoing ι) →ₗ[ℂ] ModeAmplitude (Outgoing ι) ↦
      linearMap amplitude) hOne
  simp only [LinearMap.id_apply] at hOneApply
  rw [hOneApply]

/-- Ideal routing preserves the amplitude at every matched channel endpoint. -/
@[simp]
lemma ModeTransform.idealRouting_apply {ι : Type u} {κ : Type v}
    [Fintype ι] [DecidableEq ι] [Fintype κ] (e : ι ≃ κ)
    (amplitude : ModeAmplitude (Outgoing ι)) (channel : ι) :
    (ModeTransform.idealRouting e).toLinearMap amplitude (Incident.mk (e channel)) =
      amplitude (Outgoing.mk channel) := by
  rw [ModeTransform.toLinearMap_idealRouting, ModeAmplitude.reindex_apply]
  simp

/-- Ideal unit-gain routing preserves normalized modal power. -/
lemma ModeTransform.idealRouting_isPowerPreserving {ι : Type u} {κ : Type v}
    [Fintype ι] [DecidableEq ι] [Fintype κ] (e : ι ≃ κ) :
    (ModeTransform.idealRouting e).IsPowerPreserving := by
  intro amplitude
  rw [ModeTransform.toLinearMap_idealRouting, ModeAmplitude.power_reindex]

/-- The input-side Gram matrix of ideal routing is the identity. -/
lemma ModeTransform.idealRouting_conjTranspose_mul_self {ι : Type u} {κ : Type v}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) :
    (ModeTransform.idealRouting e)ᴴ * ModeTransform.idealRouting e = 1 := by
  exact (ModeTransform.isPowerPreserving_iff_conjTranspose_mul_self
    (ModeTransform.idealRouting e)).mp (ModeTransform.idealRouting_isPowerPreserving e)

/-- The output-side Gram matrix of ideal routing is the identity. -/
lemma ModeTransform.idealRouting_mul_conjTranspose {ι : Type u} {κ : Type v}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) :
    ModeTransform.idealRouting e * (ModeTransform.idealRouting e)ᴴ = 1 := by
  exact (Matrix.mul_eq_one_comm_of_equiv (outgoingToIncidentEquiv e)).mp
    (ModeTransform.idealRouting_conjTranspose_mul_self e)

/-- Relabeling both endpoint types of ideal routing conjugates its underlying channel
equivalence. -/
lemma ModeTransform.idealRouting_reindex {ι : Type u} {κ : Type v} {μ : Type w} {ν : Type x}
    [DecidableEq ι] [DecidableEq μ] (e : ι ≃ κ) (eIn : ι ≃ μ) (eOut : κ ≃ ν) :
    (ModeTransform.idealRouting e).reindex (Outgoing.relabelEquiv eIn)
        (Incident.relabelEquiv eOut) =
      ModeTransform.idealRouting (eIn.symm.trans (e.trans eOut)) := by
  ext output input
  by_cases hMatched :
      Outgoing.mk (eIn (e.symm (eOut.symm output.channel))) = input
  · simp [ModeTransform.idealRouting, Matrix.one_apply, Incident.relabelEquiv,
      Outgoing.relabelEquiv, outgoingToIncidentEquiv, hMatched]
    have hChannel := congrArg Outgoing.channel hMatched
    simpa using congrArg eIn.symm hChannel
  · simp [ModeTransform.idealRouting, Matrix.one_apply, Incident.relabelEquiv,
      Outgoing.relabelEquiv, outgoingToIncidentEquiv, hMatched]
    intro hOld
    apply hMatched
    apply Outgoing.ext
    simpa using congrArg eIn hOld

namespace PortConnection

variable {P : PortModeFamily.{u, v}} (connection : PortConnection P)

/-- The ideal routing transform of a local port connection. -/
def idealRouting [DecidableEq connection.LocalChannel] :
    ModeTransform (Outgoing connection.LocalChannel) (Incident connection.LocalChannel) :=
  ModeTransform.idealRouting connection.mateEquiv

/-- Exchanging endpoint presentation and relabeling both endpoint wrappers leaves ideal routing
unchanged. -/
lemma symm_idealRouting_reindex_swapLocalChannel [DecidableEq connection.LocalChannel]
    [DecidableEq connection.symm.LocalChannel] :
    connection.idealRouting.reindex (Outgoing.relabelEquiv connection.swapLocalChannel)
        (Incident.relabelEquiv connection.swapLocalChannel) =
      connection.symm.idealRouting := by
  unfold idealRouting
  rw [ModeTransform.idealRouting_reindex]
  congr 1
  ext channel
  rcases channel with mode | mode <;> rfl

/-- A connection routes each outgoing local amplitude to the incident amplitude at its mate. -/
@[simp]
lemma idealRouting_apply [Fintype connection.LocalChannel]
    [DecidableEq connection.LocalChannel]
    (amplitude : ModeAmplitude (Outgoing connection.LocalChannel))
    (channel : connection.LocalChannel) :
    connection.idealRouting.toLinearMap amplitude
        (Incident.mk (connection.mateEquiv channel)) = amplitude (Outgoing.mk channel) :=
  ModeTransform.idealRouting_apply connection.mateEquiv amplitude channel

/-- The ideal routing transform of a finite local connection preserves normalized modal power.

This uses the bijection between the two ends of one local connection. A later global routing
operator that is zero outside its selected channel embedding is a partial isometry; it preserves
power globally only when no ambient channel lies outside that embedding.
-/
lemma idealRouting_isPowerPreserving [Fintype connection.LocalChannel]
    [DecidableEq connection.LocalChannel] :
    connection.idealRouting.IsPowerPreserving :=
  ModeTransform.idealRouting_isPowerPreserving connection.mateEquiv

/-- In the incident-space product `C * S`, the oriented scattering transform acts first and the
connection routes its outgoing result to the incident endpoint selected by the mate.

This fixes the multiplication order used by later network equations without defining feedback or
asserting that the internal equation is solvable. Here the scattering matrix describes a component
whose full local boundary is closed by this connection; connection families and external channels
belong to the global connection layer. -/
lemma idealRouting_mul_toOrientedModeTransform_apply
    [Fintype connection.LocalChannel] [DecidableEq connection.LocalChannel]
    (scattering : ScatteringMatrix connection.LocalChannel)
    (amplitude : ModeAmplitude (Incident connection.LocalChannel))
    (channel : connection.LocalChannel) :
    ModeTransform.toLinearMap
        (connection.idealRouting * scattering.toOrientedModeTransform :
          ModeTransform (Incident connection.LocalChannel)
            (Incident connection.LocalChannel)) amplitude
      (Incident.mk (connection.mateEquiv channel)) =
      scattering.toOrientedModeTransform.toLinearMap amplitude (Outgoing.mk channel) := by
  simpa only [ModeTransform.toLinearMap, Matrix.toLpLin_mul_same, LinearMap.comp_apply] using
    connection.idealRouting_apply
      (scattering.toOrientedModeTransform.toLinearMap amplitude) channel

end PortConnection

end

end Optics
