/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Mode.Rephase
public import Physlib.Optics.Network.Port

/-!
# Pairing-aware reciprocity metadata

## i. Overview

This file records the convention data needed to state reciprocity for a power-normalized optical
scattering matrix. A `ChannelPairing` is supplied data from incident channel ends to outgoing
channel ends. It is not inferred from a shared label type and, by itself, is not called time
reversal. The nominal pairing merely preserves the underlying channel label.

The rows of `ScatteringMatrix.pairedMatrix` are transported through the supplied pairing before
`Matrix.IsSymm` is applied. `ScatteringMatrix.IsReciprocal` therefore means transpose symmetry in
paired, power-normalized scattering coordinates, not Hermitian symmetry.

A `ReferencePlaneShift` carries two unit-phase gauges and the designated inverse-paired law. Its
paired matrix transforms as `D * A * D`. More generally, a gauge preserves paired symmetry for
every paired-symmetric matrix exactly when its pairing factor is constant. The exact condition
includes nonidentity pairings and is strictly broader than the designated reference-plane law.

`TimeReversalRealization` is only a proof bundle for four predicates supplied by a component. It
does not manufacture physical mode, plane-point, normalization, or frame data, and this module
provides no instance.

## ii. Key results

- `ChannelPairing` and `nominalPairing`: supplied and label-preserving endpoint pairings.
- `ScatteringMatrix.pairedMatrix` and `ScatteringMatrix.IsReciprocal`: the typed predicate.
- `ScatteringMatrix.isReciprocal_reindex_iff`: relabeling covariance.
- `ReferencePlaneShift`: the designated inverse-paired phase convention.
- `ScatteringMatrix.pairedMatrix_rephase_referencePlaneShift_eq_D_mul_D`: the reference-plane
  congruence formula.
- `ScatteringMatrix.isReciprocal_rephase_tauInversePaired`: inverse-paired sufficiency.
- `ScatteringMatrix.rephase_preserves_pairedIsSymm_iff_constant`: the exact general criterion.
- `TimeReversalRealization`: component-owned proof obligations over a supplied pairing.

## iii. Table of contents

- A. Supplied channel pairings
- B. Paired scattering matrices
- C. Relabeling covariance
- D. Reference-plane rephasing
- E. Physical realization obligations

## iv. References

The convention is fixed by `scratchpad/lanes/decisions/decision-L6.md`, Revision 4, and the
paste-ready C-07--C-09 record in
`scratchpad/lanes/decisions/registry-draft-A1.md`, Revision 4. It implements the N2b package at
`goal.md:1966-1974` of registered base `b8ef3236`; the decision gate is checked at
`goal.md:2744-2745`.

`ChannelPairing` alone is a label permutation, not a time-reversal claim. A
`ReferencePlaneShift` is a same-port inverse-paired convention and is distinct from
`PortConnectionFamily.IsMatchedGauge`, which is a routed-mate condition. No identification
between them is made.

Reciprocity here is transpose symmetry only in paired, power-normalized `ScatteringMatrix`
coordinates. No statement asserts losslessness, passivity, raw Jones or Fresnel reciprocity,
reverse-incidence Maxwell physics, a component realization, propagation distance, delay,
electromagnetic power, measurement, or physical realization. Independent endpoint gauges remain
legal coordinate changes but are not called reference-plane shifts.
-/

@[expose] public section

namespace Optics

noncomputable section

universe u v

/-!
## A. Supplied channel pairings
-/

/-- A supplied equivalence from incident channel ends to outgoing channel ends.

This is label-level convention data only. It is not inferred from the channel type and is not, by
itself, a physical time-reversal realization.
-/
abbrev ChannelPairing (channel : Type u) := Incident channel ≃ Outgoing channel

/-- The nominal pairing preserves the underlying incident/outgoing channel label. -/
def nominalPairing {channel : Type u} : ChannelPairing channel :=
  Incident.channelEquiv.trans Outgoing.channelEquiv.symm

/-- The nominal pairing wraps the same underlying label as an outgoing channel end. -/
@[simp]
lemma nominalPairing_apply {channel : Type u} (label : channel) :
    nominalPairing (Incident.mk label) = Outgoing.mk label := rfl

namespace ChannelPairing

/-- Transport a channel pairing along an equivalence of underlying channel labels. -/
def reindex {channel : Type u} {newChannel : Type v} (equiv : channel ≃ newChannel)
    (pairing : ChannelPairing channel) : ChannelPairing newChannel :=
  (Incident.relabelEquiv equiv).symm.trans
    (pairing.trans (Outgoing.relabelEquiv equiv))

/-- A transported pairing applies the old pairing at the corresponding old channel label. -/
@[simp]
lemma reindex_apply {channel : Type u} {newChannel : Type v}
    (equiv : channel ≃ newChannel) (pairing : ChannelPairing channel)
    (label : newChannel) :
    pairing.reindex equiv (Incident.mk label) =
      Outgoing.mk
        (equiv ((pairing (Incident.mk (equiv.symm label))).channel)) := by
  apply Outgoing.ext
  simp [reindex, Incident.relabelEquiv, Outgoing.relabelEquiv]

/-- Transporting the nominal pairing leaves it nominal on the new labels. -/
lemma reindex_nominalPairing {channel : Type u} {newChannel : Type v}
    (equiv : channel ≃ newChannel) :
    (nominalPairing : ChannelPairing channel).reindex equiv = nominalPairing := by
  ext label
  rcases label with ⟨label⟩
  simp

end ChannelPairing

/-!
## B. Paired scattering matrices
-/

namespace ScatteringMatrix

/-- Transport outgoing rows through a supplied pairing before comparing them with incident
columns. -/
def pairedMatrix {channel : Type u} (scattering : ScatteringMatrix channel)
    (pairing : ChannelPairing channel) : Matrix channel channel ℂ :=
  fun output input =>
    scattering.toModeTransform (pairing (Incident.mk output)).channel input

/-- A paired-matrix entry is the scattering coefficient at the paired outgoing row. -/
@[simp]
lemma pairedMatrix_apply {channel : Type u} (scattering : ScatteringMatrix channel)
    (pairing : ChannelPairing channel) (output input : channel) :
    scattering.pairedMatrix pairing output input =
      scattering.toModeTransform (pairing (Incident.mk output)).channel input := rfl

/-- A scattering matrix is reciprocal for a supplied pairing when its paired matrix is symmetric.
-/
def IsReciprocal {channel : Type u} (scattering : ScatteringMatrix channel)
    (pairing : ChannelPairing channel) : Prop :=
  (scattering.pairedMatrix pairing).IsSymm

/-- Pairing-aware reciprocity is the entrywise transpose-symmetry relation. -/
lemma isReciprocal_iff {channel : Type u} (scattering : ScatteringMatrix channel)
    (pairing : ChannelPairing channel) :
    scattering.IsReciprocal pairing ↔
      ∀ first second,
        scattering.pairedMatrix pairing first second =
          scattering.pairedMatrix pairing second first := by
  rw [IsReciprocal, Matrix.IsSymm.ext_iff]
  constructor <;> intro h first second
  · exact h second first
  · exact h second first

/-- Under the nominal pairing, the paired matrix is the underlying scattering transform. -/
@[simp]
lemma pairedMatrix_nominalPairing {channel : Type u}
    (scattering : ScatteringMatrix channel) :
    scattering.pairedMatrix nominalPairing = scattering.toModeTransform := rfl

/-- Nominal reciprocity is ordinary transpose symmetry of the underlying scattering transform. -/
lemma isReciprocal_nominalPairing_iff {channel : Type u}
    (scattering : ScatteringMatrix channel) :
    scattering.IsReciprocal nominalPairing ↔ scattering.toModeTransform.IsSymm := by
  rfl

/-!
## C. Relabeling covariance
-/

/-- Relabeling a scattering matrix and its pairing relabels the paired matrix on both indices. -/
lemma pairedMatrix_reindex {channel : Type u} {newChannel : Type v}
    (equiv : channel ≃ newChannel) (scattering : ScatteringMatrix channel)
    (pairing : ChannelPairing channel) :
    (scattering.reindex equiv).pairedMatrix (pairing.reindex equiv) =
      (scattering.pairedMatrix pairing).reindex equiv equiv := by
  ext output input
  simp only [pairedMatrix_apply, ScatteringMatrix.toModeTransform_reindex,
    ModeTransform.reindex_apply, ChannelPairing.reindex_apply,
    Equiv.symm_apply_apply, Matrix.reindex_apply, Matrix.submatrix_apply]

/-- Relabeling the scattering coordinates and the supplied pairing preserves and reflects
reciprocity. -/
lemma isReciprocal_reindex_iff {channel : Type u} {newChannel : Type v}
    (equiv : channel ≃ newChannel) (scattering : ScatteringMatrix channel)
    (pairing : ChannelPairing channel) :
    (scattering.reindex equiv).IsReciprocal (pairing.reindex equiv) ↔
      scattering.IsReciprocal pairing := by
  change
    ((scattering.reindex equiv).pairedMatrix (pairing.reindex equiv)).IsSymm ↔
      (scattering.pairedMatrix pairing).IsSymm
  rw [pairedMatrix_reindex, Matrix.isSymm_reindex_iff]

end ScatteringMatrix

/-!
## D. Reference-plane rephasing
-/

/-- A pairing-aware reference-plane shift consists of incident and outgoing phase gauges related
by the designated inverse-paired law. -/
structure ReferencePlaneShift {channel : Type u} (pairing : ChannelPairing channel) where
  /-- The phase change on incident channel coordinates. -/
  incidentGauge : ModePhaseGauge channel
  /-- The phase change on outgoing channel coordinates. -/
  outgoingGauge : ModePhaseGauge channel
  /-- A paired outgoing coordinate carries the inverse incident phase. -/
  inverse_paired : ∀ label,
    outgoingGauge (pairing (Incident.mk label)).channel = (incidentGauge label)⁻¹

namespace ScatteringMatrix

/-- General rephasing changes a paired entry by the paired output phase and inverse input phase. -/
@[simp]
lemma pairedMatrix_rephase_apply {channel : Type u} (scattering : ScatteringMatrix channel)
    (pairing : ChannelPairing channel) (incidentGauge outgoingGauge : ModePhaseGauge channel)
    (output input : channel) :
    (scattering.rephase incidentGauge outgoingGauge).pairedMatrix pairing output input =
      (outgoingGauge (pairing (Incident.mk output)).channel : ℂ) *
        scattering.pairedMatrix pairing output input *
          (incidentGauge input : ℂ)⁻¹ := rfl

/-- A reference-plane shift acts on a paired matrix by the same inverse incident diagonal on both
sides. -/
lemma pairedMatrix_rephase_referencePlaneShift_eq_D_mul_D
    {channel : Type u} [Fintype channel] [DecidableEq channel]
    (scattering : ScatteringMatrix channel) (pairing : ChannelPairing channel)
    (shift : ReferencePlaneShift pairing) :
    (scattering.rephase shift.incidentGauge shift.outgoingGauge).pairedMatrix pairing =
      Matrix.diagonal (fun label => (shift.incidentGauge label : ℂ)⁻¹) *
        scattering.pairedMatrix pairing *
          Matrix.diagonal (fun label => (shift.incidentGauge label : ℂ)⁻¹) := by
  ext output input
  rw [pairedMatrix_rephase_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [shift.inverse_paired output]
  simp only [Circle.coe_inv]

/-- For the nominal pairing, a reference-plane shift is the usual `D * S * D` congruence. -/
lemma rephase_referencePlaneShift_eq_D_S_D
    {channel : Type u} [Fintype channel] [DecidableEq channel]
    (scattering : ScatteringMatrix channel)
    (shift : ReferencePlaneShift (nominalPairing : ChannelPairing channel)) :
    (scattering.rephase shift.incidentGauge shift.outgoingGauge).toModeTransform =
      Matrix.diagonal (fun label => (shift.incidentGauge label : ℂ)⁻¹) *
        scattering.toModeTransform *
          Matrix.diagonal (fun label => (shift.incidentGauge label : ℂ)⁻¹) := by
  simpa only [pairedMatrix_nominalPairing] using
    scattering.pairedMatrix_rephase_referencePlaneShift_eq_D_mul_D nominalPairing shift

/-- The designated inverse-paired gauge law preserves pairing-aware reciprocity. -/
lemma isReciprocal_rephase_tauInversePaired {channel : Type u}
    (scattering : ScatteringMatrix channel) (pairing : ChannelPairing channel)
    (incidentGauge outgoingGauge : ModePhaseGauge channel)
    (hInversePaired : ∀ label,
      outgoingGauge (pairing (Incident.mk label)).channel = (incidentGauge label)⁻¹)
    (hReciprocal : scattering.IsReciprocal pairing) :
    (scattering.rephase incidentGauge outgoingGauge).IsReciprocal pairing := by
  rw [isReciprocal_iff] at hReciprocal ⊢
  intro first second
  rw [pairedMatrix_rephase_apply, pairedMatrix_rephase_apply,
    hInversePaired first, hInversePaired second, hReciprocal first second]
  simp only [Circle.coe_inv]
  ring

/-- Rephasing preserves every paired-symmetric scattering matrix exactly when the product of the
paired output phase and incident phase is constant across channel labels. -/
lemma rephase_preserves_pairedIsSymm_iff_constant {channel : Type u}
    (pairing : ChannelPairing channel) (incidentGauge outgoingGauge : ModePhaseGauge channel) :
    (∀ scattering : ScatteringMatrix channel,
        (scattering.pairedMatrix pairing).IsSymm →
          ((scattering.rephase incidentGauge outgoingGauge).pairedMatrix pairing).IsSymm) ↔
      ∀ first second,
        (outgoingGauge (pairing (Incident.mk first)).channel : ℂ) *
            (incidentGauge first : ℂ) =
          (outgoingGauge (pairing (Incident.mk second)).channel : ℂ) *
            (incidentGauge second : ℂ) := by
  constructor
  · intro hPreserves first second
    let allOnes : ScatteringMatrix channel :=
      { toModeTransform := fun _ _ => 1 }
    have hAllOnes : (allOnes.pairedMatrix pairing).IsSymm := by
      apply Matrix.IsSymm.ext
      intro output input
      rfl
    have hRephased := Matrix.IsSymm.apply (hPreserves allOnes hAllOnes) second first
    change
      (outgoingGauge (pairing (Incident.mk first)).channel : ℂ) * 1 *
          (incidentGauge second : ℂ)⁻¹ =
        (outgoingGauge (pairing (Incident.mk second)).channel : ℂ) * 1 *
          (incidentGauge first : ℂ)⁻¹ at hRephased
    field_simp [Circle.coe_ne_zero] at hRephased
    have hCross :
        (outgoingGauge (pairing (Incident.mk first)).channel : ℂ) *
            (incidentGauge first : ℂ) =
          (incidentGauge second : ℂ) *
            (outgoingGauge (pairing (Incident.mk second)).channel : ℂ) := by
      simpa only [mul_one] using hRephased
    exact hCross.trans (mul_comm _ _)
  · intro hConstant scattering hSymmetric
    apply Matrix.IsSymm.ext
    intro first second
    have hPhase :
        (outgoingGauge (pairing (Incident.mk first)).channel : ℂ) *
            (incidentGauge second : ℂ)⁻¹ =
          (outgoingGauge (pairing (Incident.mk second)).channel : ℂ) *
            (incidentGauge first : ℂ)⁻¹ := by
      calc
        (outgoingGauge (pairing (Incident.mk first)).channel : ℂ) *
              (incidentGauge second : ℂ)⁻¹ =
            ((outgoingGauge (pairing (Incident.mk first)).channel : ℂ) *
                (incidentGauge first : ℂ)) *
              ((incidentGauge first : ℂ)⁻¹ *
                (incidentGauge second : ℂ)⁻¹) := by
                  field_simp [Circle.coe_ne_zero]
        _ = ((outgoingGauge (pairing (Incident.mk second)).channel : ℂ) *
                (incidentGauge second : ℂ)) *
              ((incidentGauge first : ℂ)⁻¹ *
                (incidentGauge second : ℂ)⁻¹) := by
                  rw [hConstant first second]
        _ = (outgoingGauge (pairing (Incident.mk second)).channel : ℂ) *
              (incidentGauge first : ℂ)⁻¹ := by
                field_simp [Circle.coe_ne_zero]
    rw [pairedMatrix_rephase_apply, pairedMatrix_rephase_apply]
    have hEntry := Matrix.IsSymm.apply hSymmetric first second
    calc
      (outgoingGauge (pairing (Incident.mk second)).channel : ℂ) *
            scattering.pairedMatrix pairing second first *
              (incidentGauge first : ℂ)⁻¹ =
          ((outgoingGauge (pairing (Incident.mk second)).channel : ℂ) *
              (incidentGauge first : ℂ)⁻¹) *
            scattering.pairedMatrix pairing second first := by ring
      _ = ((outgoingGauge (pairing (Incident.mk first)).channel : ℂ) *
              (incidentGauge second : ℂ)⁻¹) *
            scattering.pairedMatrix pairing second first := by rw [hPhase]
      _ = ((outgoingGauge (pairing (Incident.mk first)).channel : ℂ) *
              (incidentGauge second : ℂ)⁻¹) *
            scattering.pairedMatrix pairing first second := by rw [hEntry]
      _ = (outgoingGauge (pairing (Incident.mk first)).channel : ℂ) *
            scattering.pairedMatrix pairing first second *
              (incidentGauge second : ℂ)⁻¹ := by ring

end ScatteringMatrix

/-!
## E. Physical realization obligations
-/

/-- Proof-bearing component obligations for calling a supplied channel pairing a physical
time-reversal realization.

The four predicates are supplied by a component because neutral channel labels contain no carrier,
frame, stored plane point, or modal normalization data. Under C-07, a concrete frame-transport
predicate records `(e₀, e₁, k) ↦ (e₀, -e₁, -k)` and
`(J₀, J₁) ↦ (conj J₀, -conj J₁)`, including any component-owned orthogonal sign correction.
-/
structure TimeReversalRealization {channel : Type u} (pairing : ChannelPairing channel)
    (SameTransverseMode SameReferencePlane EqualPowerNormalization ExactFrameTransport :
      Incident channel → Outgoing channel → Prop) : Prop where
  /-- Every paired end satisfies the component's transverse-mode relation. -/
  same_transverse_mode : ∀ incident, SameTransverseMode incident (pairing incident)
  /-- Every paired end is referenced to the same component-owned plane point. -/
  same_reference_plane : ∀ incident, SameReferencePlane incident (pairing incident)
  /-- Every paired end has the component's equal power-normalization proof. -/
  equal_power_normalization :
    ∀ incident, EqualPowerNormalization incident (pairing incident)
  /-- Every paired end satisfies the component's exact direction/frame transport relation. -/
  exact_frame_transport : ∀ incident, ExactFrameTransport incident (pairing incident)

end

end Optics
