/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Components.DirectionalCoupler

/-!
# Physical-port presentation of the directional coupler

## i. Overview

This file gives the algebraic two-side, two-arm coupler four independently wireable physical
ports. Each port carries a separately tagged copy of the declared mode family. `channelEquiv`
pins the raw nested-sum order to `leftFirst`, `leftSecond`, `rightFirst`, `rightSecond`.

The independent behavior and the scattering matrix are transported separately along the endpoint
and channel equivalences, then proved to have the same graph. Thus a downstream component family
can own four ports rather than hiding the two arms as modes of only one port on each side.

This is a coordinate and ownership layer. It adds no reciprocity, propagation, delay, geometry,
material, electromagnetic normalization, or power-completeness claim.

## ii. Key results

- `DirectionalCoupler.portFamily`: four independently wireable physical ports.
- `DirectionalCoupler.channelEquiv`: the pinned raw-to-physical channel order.
- `DirectionalCoupler.physicalBehavior`: the independent law in physical endpoint labels.
- `DirectionalCoupler.physicalScattering`: the physical-channel scattering matrix.
- `DirectionalCoupler.physicalScattering_realizes_physicalBehavior`: exact graph realization.

## iii. Table of contents

- A. Physical ports and channel coordinates
- B. Transported behavior and scattering realization

## iv. References

This physical-port presentation is Physlib-original and source-neutral.
-/

@[expose] public section

namespace Optics

noncomputable section

universe u

namespace DirectionalCoupler

/-! ## A. Physical ports and channel coordinates -/

/-- The four independently wireable ports of a co-directional two-arm coupler. -/
inductive Port
  | leftFirst
  | leftSecond
  | rightFirst
  | rightSecond
  deriving DecidableEq

/-- The four physical directional-coupler ports form a finite family. -/
instance : Fintype Port where
  elems := {Port.leftFirst, Port.leftSecond, Port.rightFirst, Port.rightSecond}
  complete port := by
    cases port <;> simp

/-- The physical port family, with the same declared mode family copied at every port. -/
def portFamily (mode : Type u) : PortModeFamily.{0, u} where
  Port := Port
  Mode := fun _ => mode

/-- The pinned ordering from nested side/arm labels to flattened physical channels. -/
def channelEquiv (mode : Type u) :
    ((mode ⊕ mode) ⊕ (mode ⊕ mode)) ≃ (portFamily mode).Channel where
  toFun
    | Sum.inl (Sum.inl value) => ⟨Port.leftFirst, value⟩
    | Sum.inl (Sum.inr value) => ⟨Port.leftSecond, value⟩
    | Sum.inr (Sum.inl value) => ⟨Port.rightFirst, value⟩
    | Sum.inr (Sum.inr value) => ⟨Port.rightSecond, value⟩
  invFun
    | ⟨Port.leftFirst, value⟩ => Sum.inl (Sum.inl value)
    | ⟨Port.leftSecond, value⟩ => Sum.inl (Sum.inr value)
    | ⟨Port.rightFirst, value⟩ => Sum.inr (Sum.inl value)
    | ⟨Port.rightSecond, value⟩ => Sum.inr (Sum.inr value)
  left_inv := by
    intro channel
    rcases channel with (value | value) | (value | value) <;> rfl
  right_inv := by
    rintro ⟨port, value⟩
    cases port <;> rfl

/-- Flattened physical channels are finite through the pinned side/arm equivalence. -/
noncomputable instance channelFintype [Fintype ι] : Fintype ((portFamily ι).Channel) :=
  Fintype.ofEquiv ((ι ⊕ ι) ⊕ (ι ⊕ ι)) (channelEquiv ι)

/-- Flattened physical channels have decidable equality through their pinned coordinates. -/
instance channelDecidableEq [DecidableEq ι] :
    DecidableEq ((portFamily ι).Channel) :=
  (channelEquiv ι).symm.decidableEq

/-- The first raw left-arm channel is the corresponding physical port channel. -/
@[simp]
lemma channelEquiv_apply_leftFirst (value : ι) :
    channelEquiv ι (Sum.inl (Sum.inl value)) = ⟨Port.leftFirst, value⟩ := rfl

/-- The second raw left-arm channel is the corresponding physical port channel. -/
@[simp]
lemma channelEquiv_apply_leftSecond (value : ι) :
    channelEquiv ι (Sum.inl (Sum.inr value)) = ⟨Port.leftSecond, value⟩ := rfl

/-- The first raw right-arm channel is the corresponding physical port channel. -/
@[simp]
lemma channelEquiv_apply_rightFirst (value : ι) :
    channelEquiv ι (Sum.inr (Sum.inl value)) = ⟨Port.rightFirst, value⟩ := rfl

/-- The second raw right-arm channel is the corresponding physical port channel. -/
@[simp]
lemma channelEquiv_apply_rightSecond (value : ι) :
    channelEquiv ι (Sum.inr (Sum.inr value)) = ⟨Port.rightSecond, value⟩ := rfl

/-- The endpoint equivalence from split incident coordinates to physical incident channels. -/
def incidentChannelEquiv (mode : Type u) :
    (Incident (mode ⊕ mode) ⊕ Incident (mode ⊕ mode)) ≃
      Incident ((portFamily mode).Channel) :=
  ((Incident.splitSumEquiv :
      Incident ((mode ⊕ mode) ⊕ (mode ⊕ mode)) ≃
        Incident (mode ⊕ mode) ⊕ Incident (mode ⊕ mode)).symm).trans
    (Incident.relabelEquiv (channelEquiv mode))

/-- The endpoint equivalence from split outgoing coordinates to physical outgoing channels. -/
def outgoingChannelEquiv (mode : Type u) :
    (Outgoing (mode ⊕ mode) ⊕ Outgoing (mode ⊕ mode)) ≃
      Outgoing ((portFamily mode).Channel) :=
  ((Outgoing.splitSumEquiv :
      Outgoing ((mode ⊕ mode) ⊕ (mode ⊕ mode)) ≃
        Outgoing (mode ⊕ mode) ⊕ Outgoing (mode ⊕ mode)).symm).trans
    (Outgoing.relabelEquiv (channelEquiv mode))

/-! ## B. Transported behavior and scattering realization -/

/-- The independent directional-coupler behavior in owned physical endpoint labels. -/
def physicalBehavior [Fintype ι] [DecidableEq ι] (p : Parameters) :
    LinearBehavior (Incident ((portFamily ι).Channel))
      (Outgoing ((portFamily ι).Channel)) :=
  (behavior p).reindex (incidentChannelEquiv ι) (outgoingChannelEquiv ι)

/-- Membership in the physical behavior is membership in the pinned nested-sum coordinates. -/
@[simp]
lemma mem_physicalBehavior_iff [Fintype ι] [DecidableEq ι] (p : Parameters)
    (incident : ModeAmplitude (Incident ((portFamily ι).Channel)))
    (outgoing : ModeAmplitude (Outgoing ((portFamily ι).Channel))) :
    (incident, outgoing) ∈ physicalBehavior p ↔
      (ModeAmplitude.reindex (incidentChannelEquiv ι).symm incident,
        ModeAmplitude.reindex (outgoingChannelEquiv ι).symm outgoing) ∈ behavior p := by
  rw [physicalBehavior, LinearBehavior.mem_reindex_iff]

/-- The directional-coupler scattering matrix in owned physical channel labels. -/
def physicalScattering (p : Parameters) (mode : Type u) :
    ScatteringMatrix ((portFamily mode).Channel) :=
  (scattering p mode).reindex (channelEquiv mode)

/-- The physical scattering adapter is the raw adapter in the pinned endpoint coordinates. -/
lemma physicalScattering_toOrientedModeTransform (p : Parameters) (mode : Type u) :
    (physicalScattering p mode).toOrientedModeTransform =
      (scattering p mode).toTwoPortScatteringTransform.reindex
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
  change LinearBehavior.reindex (incidentChannelEquiv ι) (outgoingChannelEquiv ι)
      (scattering p ι).toTwoPortScatteringBehavior = physicalBehavior p
  rw [scattering_realizes_behavior]
  rfl

end DirectionalCoupler

end

end Optics
