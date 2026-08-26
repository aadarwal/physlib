/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Components.BeamSplitter
public import Physlib.Optics.Network.ScatteringComponentFamily

/-!
# Component-owned physical ports for the beam splitter

## i. Overview

This file gives `BeamSplitter` two component-owned optical ports. Each port carries a separately
tagged copy of the declared mode family, and `channelEquiv` pins the algebraic first/second channel
order to the physical `first`/`second` port order by construction.

The independent behavior and scattering matrix are transported separately and proved to have the
same graph. `componentFamily` is a direct singleton `ScatteringComponentFamily` whose stored port
family and scattering law are definitionally the component-owned objects; callers perform no
post-hoc port identification.

This coordinate and ownership layer adds no reciprocity, time reversal, propagation, reference
plane, geometry, material, causality, dispersion, electromagnetic normalization, or physical
realization claim.

## ii. Key results

- `BeamSplitter.portFamily`: the two owned physical ports.
- `BeamSplitter.channelEquiv`: the pinned algebraic-to-physical channel order.
- `BeamSplitter.physicalBehavior`: the independent law in physical endpoint labels.
- `BeamSplitter.physicalScattering`: the physical-channel scattering matrix.
- `BeamSplitter.physicalScattering_realizes_physicalBehavior`: exact graph realization.
- `BeamSplitter.componentFamily`: direct consumption by `ScatteringComponentFamily`.

## iii. Table of contents

- A. Physical ports and pinned channel coordinates
- B. Transported behavior and scattering realization
- C. Direct component-family witness

## iv. References

This physical-port presentation is Physlib-original and source-neutral. Its losslessness result is
only squared-amplitude modal bookkeeping, not electromagnetic power. No reciprocity, time
reversal, reverse-incidence Maxwell law, modal completeness, propagation, causality, dispersion,
or physical realization is asserted.
-/

@[expose] public section

namespace Optics

noncomputable section

universe u

namespace BeamSplitter

/-!
## A. Physical ports and pinned channel coordinates
-/

/-- The two independently wireable optical ports of the beam splitter. -/
inductive Port
  | first
  | second
  deriving DecidableEq

/-- The two beam-splitter ports form a finite family. -/
instance : Fintype Port where
  elems := {Port.first, Port.second}
  complete port := by
    cases port <;> simp

/-- The component-owned physical ports, with the declared mode family at each port. -/
def portFamily (mode : Type u) : PortModeFamily.{0, u} where
  Port := Port
  Mode := fun _ => mode

/-- The pinned equivalence from algebraic channel order to component-owned physical channels. -/
def channelEquiv (mode : Type u) : (mode ⊕ mode) ≃ (portFamily mode).Channel where
  toFun
    | Sum.inl value => ⟨Port.first, value⟩
    | Sum.inr value => ⟨Port.second, value⟩
  invFun
    | ⟨Port.first, value⟩ => Sum.inl value
    | ⟨Port.second, value⟩ => Sum.inr value
  left_inv := by
    intro channel
    rcases channel with value | value <;> rfl
  right_inv := by
    rintro ⟨port, value⟩
    cases port <;> rfl

/-- Physical beam-splitter channels are finite through the pinned equivalence. -/
noncomputable instance channelFintype [Fintype ι] : Fintype ((portFamily ι).Channel) :=
  Fintype.ofEquiv (ι ⊕ ι) (channelEquiv ι)

/-- Physical beam-splitter channels have decidable equality in pinned coordinates. -/
instance channelDecidableEq [DecidableEq ι] :
    DecidableEq ((portFamily ι).Channel) :=
  (channelEquiv ι).symm.decidableEq

/-- The first algebraic channel is the first owned physical-port channel. -/
@[simp]
lemma channelEquiv_apply_first (value : ι) :
    channelEquiv ι (Sum.inl value) = ⟨Port.first, value⟩ := rfl

/-- The second algebraic channel is the second owned physical-port channel. -/
@[simp]
lemma channelEquiv_apply_second (value : ι) :
    channelEquiv ι (Sum.inr value) = ⟨Port.second, value⟩ := rfl

/-- The pinned incident-end equivalence to component-owned physical channels. -/
def incidentChannelEquiv (mode : Type u) :
    Incident (mode ⊕ mode) ≃ Incident ((portFamily mode).Channel) :=
  Incident.relabelEquiv (channelEquiv mode)

/-- The pinned outgoing-end equivalence to component-owned physical channels. -/
def outgoingChannelEquiv (mode : Type u) :
    Outgoing (mode ⊕ mode) ≃ Outgoing ((portFamily mode).Channel) :=
  Outgoing.relabelEquiv (channelEquiv mode)

/-- The first raw incident endpoint becomes the first owned physical endpoint. -/
@[simp]
lemma incidentChannelEquiv_apply_first (value : ι) :
    incidentChannelEquiv ι (Incident.mk (Sum.inl value)) =
      Incident.mk ⟨Port.first, value⟩ := rfl

/-- The second raw incident endpoint becomes the second owned physical endpoint. -/
@[simp]
lemma incidentChannelEquiv_apply_second (value : ι) :
    incidentChannelEquiv ι (Incident.mk (Sum.inr value)) =
      Incident.mk ⟨Port.second, value⟩ := rfl

/-- The first raw outgoing endpoint becomes the first owned physical endpoint. -/
@[simp]
lemma outgoingChannelEquiv_apply_first (value : ι) :
    outgoingChannelEquiv ι (Outgoing.mk (Sum.inl value)) =
      Outgoing.mk ⟨Port.first, value⟩ := rfl

/-- The second raw outgoing endpoint becomes the second owned physical endpoint. -/
@[simp]
lemma outgoingChannelEquiv_apply_second (value : ι) :
    outgoingChannelEquiv ι (Outgoing.mk (Sum.inr value)) =
      Outgoing.mk ⟨Port.second, value⟩ := rfl

/-!
## B. Transported behavior and scattering realization
-/

/-- The independently specified beam-splitter law in component-owned endpoint labels. -/
def physicalBehavior [Fintype ι] [DecidableEq ι] (p : Parameters) :
    LinearBehavior (Incident ((portFamily ι).Channel))
      (Outgoing ((portFamily ι).Channel)) :=
  (behavior p).reindex (incidentChannelEquiv ι) (outgoingChannelEquiv ι)

/-- Physical behavior membership is membership in the pinned algebraic coordinates. -/
@[simp]
lemma mem_physicalBehavior_iff [Fintype ι] [DecidableEq ι] (p : Parameters)
    (incident : ModeAmplitude (Incident ((portFamily ι).Channel)))
    (outgoing : ModeAmplitude (Outgoing ((portFamily ι).Channel))) :
    (incident, outgoing) ∈ physicalBehavior p ↔
      (ModeAmplitude.reindex (incidentChannelEquiv ι).symm incident,
        ModeAmplitude.reindex (outgoingChannelEquiv ι).symm outgoing) ∈ behavior p := by
  rw [physicalBehavior, LinearBehavior.mem_reindex_iff]

/-- The beam-splitter scattering matrix in component-owned physical channel labels. -/
def physicalScattering (p : Parameters) (mode : Type u) :
    ScatteringMatrix ((portFamily mode).Channel) :=
  (scattering p mode).reindex (channelEquiv mode)

/-- The physical scattering adapter is the raw adapter in the pinned endpoint coordinates. -/
lemma physicalScattering_toOrientedModeTransform (p : Parameters) (mode : Type u) :
    (physicalScattering p mode).toOrientedModeTransform =
      (scattering p mode).toOrientedModeTransform.reindex
        (incidentChannelEquiv mode) (outgoingChannelEquiv mode) := by
  ext output input
  rcases output with ⟨⟨outputPort, outputMode⟩⟩
  rcases input with ⟨⟨inputPort, inputMode⟩⟩
  cases outputPort <;> cases inputPort <;> rfl

/-- Physical scattering realizes the independently transported physical behavior exactly. -/
lemma physicalScattering_realizes_physicalBehavior [Fintype ι] [DecidableEq ι]
    (p : Parameters) :
    (physicalScattering p ι).toOrientedModeTransform.toBehavior = physicalBehavior p := by
  rw [physicalScattering_toOrientedModeTransform, ModeTransform.toBehavior_reindex]
  rw [scattering_realizes_behavior]
  rfl

/-- Unitary parameters make the physical scattering presentation lossless. -/
lemma physicalScattering_isLossless [Fintype ι] [DecidableEq ι] (p : Parameters)
    (hp : p.IsUnitary) : (physicalScattering p ι).IsLossless :=
  (ScatteringMatrix.isLossless_reindex_iff (channelEquiv ι) (scattering p ι)).mpr
    (scattering_isLossless p hp)

/-!
## C. Direct component-family witness
-/

/-- The beam splitter as a singleton scattering-component family with owned physical ports. -/
def componentFamily (p : Parameters) (mode : Type u) : ScatteringComponentFamily where
  Component := Unit
  portFamily := fun _ => portFamily mode
  scattering := fun _ => physicalScattering p mode

/-- The singleton witness stores the beam splitter's owned physical-port family definitionally. -/
@[simp]
lemma componentFamily_portFamily (p : Parameters) (mode : Type u) :
    (componentFamily p mode).portFamily () = portFamily mode := rfl

/-- The singleton witness stores the physical scattering law definitionally. -/
@[simp]
lemma componentFamily_scattering (p : Parameters) (mode : Type u) :
    (componentFamily p mode).scattering () = physicalScattering p mode := rfl

end BeamSplitter

end

end Optics
