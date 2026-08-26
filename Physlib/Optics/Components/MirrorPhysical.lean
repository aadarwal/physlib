/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Components.Mirror
public import Physlib.Optics.Network.ScatteringComponentFamily

/-!
# Component-owned physical port for the one-port mirror

## i. Overview

This file gives `Mirror` one component-owned physical surface port. The port carries the declared
mode family, and `channelEquiv` pins every raw mode to the corresponding channel at that owned port
by construction.

The independent behavior and scattering matrix are transported separately and proved to have the
same graph. `componentFamily` is a direct singleton `ScatteringComponentFamily` whose stored port
family and scattering law are definitionally the mirror-owned objects.

This coordinate and ownership layer adds no coating, interface, reciprocity, time reversal,
propagation, reference-plane, geometry, causality, dispersion, electromagnetic normalization, or
physical-realization claim.

## ii. Key results

- `Mirror.portFamily`: the owned surface port and its mode fiber.
- `Mirror.channelEquiv`: the pinned raw-to-physical channel equivalence.
- `Mirror.physicalBehavior`: the independent law in physical endpoint labels.
- `Mirror.physicalScattering`: the physical-channel scattering matrix.
- `Mirror.physicalScattering_realizes_physicalBehavior`: exact graph realization.
- `Mirror.componentFamily`: direct consumption by `ScatteringComponentFamily`.

## iii. Table of contents

- A. Physical port and pinned channel coordinates
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

namespace Mirror

/-!
## A. Physical port and pinned channel coordinates
-/

/-- The independently wireable reflecting surface port. -/
inductive Port
  | surface
  deriving DecidableEq

/-- The one mirror port forms a finite family. -/
instance : Fintype Port where
  elems := {Port.surface}
  complete port := by
    cases port
    simp

/-- The component-owned surface port carrying the declared mode family. -/
def portFamily (mode : Type u) : PortModeFamily.{0, u} where
  Port := Port
  Mode := fun _ => mode

/-- The pinned equivalence from raw modes to channels at the owned surface port. -/
def channelEquiv (mode : Type u) : mode ≃ (portFamily mode).Channel where
  toFun value := ⟨Port.surface, value⟩
  invFun
    | ⟨Port.surface, value⟩ => value
  left_inv := by
    intro value
    rfl
  right_inv := by
    rintro ⟨port, value⟩
    cases port
    rfl

/-- Physical mirror channels are finite through the pinned equivalence. -/
noncomputable instance channelFintype [Fintype ι] : Fintype ((portFamily ι).Channel) :=
  Fintype.ofEquiv ι (channelEquiv ι)

/-- Physical mirror channels have decidable equality in pinned coordinates. -/
instance channelDecidableEq [DecidableEq ι] :
    DecidableEq ((portFamily ι).Channel) :=
  (channelEquiv ι).symm.decidableEq

/-- A raw mode is the corresponding channel at the owned surface port. -/
@[simp]
lemma channelEquiv_apply (value : ι) :
    channelEquiv ι value = ⟨Port.surface, value⟩ := rfl

/-- The pinned incident-end equivalence to the owned surface port. -/
def incidentChannelEquiv (mode : Type u) :
    Incident mode ≃ Incident ((portFamily mode).Channel) :=
  Incident.relabelEquiv (channelEquiv mode)

/-- The pinned outgoing-end equivalence to the owned surface port. -/
def outgoingChannelEquiv (mode : Type u) :
    Outgoing mode ≃ Outgoing ((portFamily mode).Channel) :=
  Outgoing.relabelEquiv (channelEquiv mode)

/-- A raw incident mode becomes the corresponding owned surface endpoint. -/
@[simp]
lemma incidentChannelEquiv_apply (value : ι) :
    incidentChannelEquiv ι (Incident.mk value) =
      Incident.mk ⟨Port.surface, value⟩ := rfl

/-- A raw outgoing mode becomes the corresponding owned surface endpoint. -/
@[simp]
lemma outgoingChannelEquiv_apply (value : ι) :
    outgoingChannelEquiv ι (Outgoing.mk value) =
      Outgoing.mk ⟨Port.surface, value⟩ := rfl

/-!
## B. Transported behavior and scattering realization
-/

/-- The independently specified mirror law in component-owned endpoint labels. -/
def physicalBehavior [Fintype ι] [DecidableEq ι] (p : Parameters) :
    LinearBehavior (Incident ((portFamily ι).Channel))
      (Outgoing ((portFamily ι).Channel)) :=
  (behavior p).reindex (incidentChannelEquiv ι) (outgoingChannelEquiv ι)

/-- Physical behavior membership is membership in the pinned raw-mode coordinates. -/
@[simp]
lemma mem_physicalBehavior_iff [Fintype ι] [DecidableEq ι] (p : Parameters)
    (incident : ModeAmplitude (Incident ((portFamily ι).Channel)))
    (outgoing : ModeAmplitude (Outgoing ((portFamily ι).Channel))) :
    (incident, outgoing) ∈ physicalBehavior p ↔
      (ModeAmplitude.reindex (incidentChannelEquiv ι).symm incident,
        ModeAmplitude.reindex (outgoingChannelEquiv ι).symm outgoing) ∈ behavior p := by
  rw [physicalBehavior, LinearBehavior.mem_reindex_iff]

/-- The mirror scattering matrix in component-owned physical channel labels. -/
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
  cases outputPort
  cases inputPort
  rfl

/-- Physical scattering realizes the independently transported mirror behavior exactly. -/
lemma physicalScattering_realizes_physicalBehavior [Fintype ι] [DecidableEq ι]
    (p : Parameters) :
    (physicalScattering p ι).toOrientedModeTransform.toBehavior = physicalBehavior p := by
  rw [physicalScattering_toOrientedModeTransform, ModeTransform.toBehavior_reindex]
  rw [scattering_realizes_behavior]
  rfl

/-- A unit-phase coefficient makes the physical mirror presentation lossless. -/
lemma physicalScattering_isLossless [Fintype ι] [DecidableEq ι] (p : Parameters)
    (hp : p.IsUnitPhase) : (physicalScattering p ι).IsLossless :=
  (ScatteringMatrix.isLossless_reindex_iff (channelEquiv ι) (scattering p ι)).mpr
    (scattering_isLossless p hp)

/-!
## C. Direct component-family witness
-/

/-- The mirror as a singleton scattering-component family with its owned surface port. -/
def componentFamily (p : Parameters) (mode : Type u) : ScatteringComponentFamily where
  Component := Unit
  portFamily := fun _ => portFamily mode
  scattering := fun _ => physicalScattering p mode

/-- The singleton witness stores the mirror's owned physical-port family definitionally. -/
@[simp]
lemma componentFamily_portFamily (p : Parameters) (mode : Type u) :
    (componentFamily p mode).portFamily () = portFamily mode := rfl

/-- The singleton witness stores the physical mirror scattering law definitionally. -/
@[simp]
lemma componentFamily_scattering (p : Parameters) (mode : Type u) :
    (componentFamily p mode).scattering () = physicalScattering p mode := rfl

end Mirror

end

end Optics
