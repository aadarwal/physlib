/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Components.MatchedPropagation

/-!
# Physical-port presentation of fixed-carrier matched propagation

## i. Overview

This file equips the algebraic `MatchedPropagation` law with two component-owned physical ports.
The left and right ports each carry the declared mode family, and `channelEquiv` proves that the
algebraic `left ⊕ right` order is exactly the flattened physical-channel order used by the network
API.

The independent split-endpoint behavior is transported to physical incident and outgoing channel
ends. The scattering matrix is transported separately, and an oriented-transform equality proves
that the physical scattering graph realizes the transported behavior. Thus callers do not choose
their own left/right relabeling when inserting this component into a `ScatteringComponentFamily`.

This is only a coordinate and ownership layer. It adds no propagation, power, matching,
reciprocity, delay, material, or completeness claim beyond `MatchedPropagation`.

## ii. Key results

- `MatchedPropagation.portFamily`: the two owned physical ports and their mode fibers.
- `MatchedPropagation.channelEquiv`: the pinned algebraic-to-physical channel ordering.
- `MatchedPropagation.physicalBehavior`: the independent law in physical endpoint labels.
- `MatchedPropagation.physicalScattering`: the scattering law in physical channel labels.
- `MatchedPropagation.physicalScattering_realizes_physicalBehavior`: exact graph realization.

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

namespace MatchedPropagation

/-!

## A. Physical ports and channel coordinates

-/

/-- The two physical reference-plane ports of a matched-propagation component. -/
inductive Port
  | left
  | right
  deriving DecidableEq

/-- The two physical matched-propagation ports form a finite family. -/
instance : Fintype Port where
  elems := {Port.left, Port.right}
  complete port := by
    cases port <;> simp

/-- The matched-propagation physical-port family, with the same mode fiber at both ports. -/
def portFamily (ι : Type u) : PortModeFamily.{0, u} where
  Port := Port
  Mode := fun _ => ι

/-- The pinned ordering from algebraic left/right channels to flattened physical channels. -/
def channelEquiv (ι : Type u) : ι ⊕ ι ≃ (portFamily ι).Channel where
  toFun
    | Sum.inl mode => ⟨Port.left, mode⟩
    | Sum.inr mode => ⟨Port.right, mode⟩
  invFun
    | ⟨Port.left, mode⟩ => Sum.inl mode
    | ⟨Port.right, mode⟩ => Sum.inr mode
  left_inv := by
    intro channel
    rcases channel with mode | mode <;> rfl
  right_inv := by
    rintro ⟨port, mode⟩
    cases port <;> rfl

/-- Flattened physical channels are finite through the pinned left/right equivalence. -/
noncomputable instance channelFintype [Fintype ι] : Fintype ((portFamily ι).Channel) :=
  Fintype.ofEquiv (ι ⊕ ι) (channelEquiv ι)

/-- Flattened physical channels have decidable equality through their pinned coordinates. -/
instance channelDecidableEq [DecidableEq ι] :
    DecidableEq ((portFamily ι).Channel) :=
  (channelEquiv ι).symm.decidableEq

/-- A left algebraic channel is the corresponding physical left-port channel. -/
@[simp]
lemma channelEquiv_apply_inl (mode : ι) :
    channelEquiv ι (Sum.inl mode) = ⟨Port.left, mode⟩ := rfl

/-- A right algebraic channel is the corresponding physical right-port channel. -/
@[simp]
lemma channelEquiv_apply_inr (mode : ι) :
    channelEquiv ι (Sum.inr mode) = ⟨Port.right, mode⟩ := rfl

/-- The endpoint equivalence from split incident coordinates to physical incident channels. -/
def incidentChannelEquiv (ι : Type u) :
    (Incident ι ⊕ Incident ι) ≃ Incident ((portFamily ι).Channel) :=
  ((Incident.splitSumEquiv :
      Incident (ι ⊕ ι) ≃ Incident ι ⊕ Incident ι).symm).trans
    (Incident.relabelEquiv (channelEquiv ι))

/-- The endpoint equivalence from split outgoing coordinates to physical outgoing channels. -/
def outgoingChannelEquiv (ι : Type u) :
    (Outgoing ι ⊕ Outgoing ι) ≃ Outgoing ((portFamily ι).Channel) :=
  ((Outgoing.splitSumEquiv :
      Outgoing (ι ⊕ ι) ≃ Outgoing ι ⊕ Outgoing ι).symm).trans
    (Outgoing.relabelEquiv (channelEquiv ι))

/-- The left split incident endpoint is the owned physical left endpoint. -/
@[simp]
lemma incidentChannelEquiv_apply_inl (mode : ι) :
    incidentChannelEquiv ι (Sum.inl (Incident.mk mode)) = Incident.mk ⟨Port.left, mode⟩ := rfl
/-- The right split incident endpoint is the owned physical right endpoint. -/
@[simp]
lemma incidentChannelEquiv_apply_inr (mode : ι) :
    incidentChannelEquiv ι (Sum.inr (Incident.mk mode)) = Incident.mk ⟨Port.right, mode⟩ := rfl
/-- The left split outgoing endpoint is the owned physical left endpoint. -/
@[simp]
lemma outgoingChannelEquiv_apply_inl (mode : ι) :
    outgoingChannelEquiv ι (Sum.inl (Outgoing.mk mode)) = Outgoing.mk ⟨Port.left, mode⟩ := rfl
/-- The right split outgoing endpoint is the owned physical right endpoint. -/
@[simp]
lemma outgoingChannelEquiv_apply_inr (mode : ι) :
    outgoingChannelEquiv ι (Sum.inr (Outgoing.mk mode)) = Outgoing.mk ⟨Port.right, mode⟩ := rfl

/-!

## B. Transported behavior and scattering realization

-/

/-- The independent matched-propagation behavior in component-owned physical endpoint labels. -/
def physicalBehavior [Fintype ι] [DecidableEq ι] (p : Parameters) :
    LinearBehavior (Incident ((portFamily ι).Channel))
      (Outgoing ((portFamily ι).Channel)) :=
  (behavior p).reindex (incidentChannelEquiv ι) (outgoingChannelEquiv ι)

/-- Physical behavior membership is membership after returning to the pinned split coordinates. -/
@[simp]
lemma mem_physicalBehavior_iff [Fintype ι] [DecidableEq ι] (p : Parameters)
    (incident : ModeAmplitude (Incident ((portFamily ι).Channel)))
    (outgoing : ModeAmplitude (Outgoing ((portFamily ι).Channel))) :
    (incident, outgoing) ∈ physicalBehavior p ↔
      (ModeAmplitude.reindex (incidentChannelEquiv ι).symm incident,
        ModeAmplitude.reindex (outgoingChannelEquiv ι).symm outgoing) ∈ behavior p := by
  rw [physicalBehavior, LinearBehavior.mem_reindex_iff]

/-- The matched-propagation scattering matrix in component-owned physical channel labels. -/
def physicalScattering (p : Parameters) (ι : Type u) :
    ScatteringMatrix ((portFamily ι).Channel) :=
  (scattering p ι).reindex (channelEquiv ι)

/-- The physical scattering adapter is the typed two-port adapter in the pinned endpoint labels. -/
lemma physicalScattering_toOrientedModeTransform (p : Parameters) (ι : Type u) :
    (physicalScattering p ι).toOrientedModeTransform =
      (scattering p ι).toTwoPortScatteringTransform.reindex
        (incidentChannelEquiv ι) (outgoingChannelEquiv ι) := by
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

end MatchedPropagation

end

end Optics
