/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Interfaces.PlanarDielectric.FresnelScattering
public import Physlib.Optics.Network.ScatteringComponentFamily

/-!
# Component-owned ports for the polarized Fresnel scattering kernels

## i. Overview

This file gives the registered s- and p-polarized Fresnel kernels two component-owned side ports.
Each port carries distinct `s` and `p` modes. `channelEquiv` pins the raw kernel ordering: the left
summand is s polarization, the right summand is p polarization, and coordinate `0`/`1` is the
negative/positive side. The two registered kernels are combined only by block-diagonal parallel
composition and then transported to these owned channels.

The angle convention is the one already fixed in `AngularGeometry.lean`: incident and transmitted
angles are measured from the positive-side normal (`AngularGeometry.lean:88-89,105-106`), while
the reflected angle is measured from the negative-side normal (`AngularGeometry.lean:97-98`). The
present algebraic kernel carries only `chi_i` and `chi_t`; it does not redefine those angles.

The p entries use Physlib's fork-declared full-electric-vector convention. At normal incidence
`r_p = -r_s` and `t_p = t_s`; some literature instead orients the reflected p basis so the
reflection signs agree. This package preserves the registered full-vector coefficients and does
not force a cross-convention match.

## ii. Key results

- `PlanarDielectricInterface.portFamily`: the owned negative- and positive-side ports.
- `PlanarDielectricInterface.channelEquiv`: the pinned side/polarization channel equivalence.
- `PlanarDielectricInterface.polarizedScattering`: parallel registered s/p kernels.
- `PlanarDielectricInterface.physicalBehavior`: the kernel graph in owned endpoint labels.
- `PlanarDielectricInterface.physicalScattering`: the kernel in owned channel labels.
- `PlanarDielectricInterface.physicalScattering_realizes_physicalBehavior`: exact realization.
- `PlanarDielectricInterface.componentFamily`: direct `ScatteringComponentFamily` consumption.

## iii. Table of contents

- A. Owned sides and pinned polarization coordinates
- B. Registered-kernel behavior and scattering realization
- C. Direct component-family witness

## iv. References

This file packages the algebraic completion from `FresnelScattering.lean`; it does not upgrade that
completion to a reverse-incidence Maxwell derivation or an E6 physical bidirectional interface.
Its losslessness result is normalized squared-amplitude bookkeeping, not electromagnetic power.
No reciprocity, time reversal, reference-plane law, modal completeness, propagation, causality,
dispersion, observer convention, or physical realization is asserted. The typed reciprocity
predicate and its reference-plane convention belong to a separate development.
-/

@[expose] public section

namespace Optics

noncomputable section

namespace PlanarDielectricInterface

/-!
## A. Owned sides and pinned polarization coordinates
-/

/-- The two independently wireable geometric sides of the interface component. -/
inductive Port
  | negativeSide
  | positiveSide
  deriving DecidableEq

/-- The two interface side ports form a finite family. -/
instance : Fintype Port where
  elems := {Port.negativeSide, Port.positiveSide}
  complete port := by
    cases port <;> simp

/-- The two polarization labels carried independently at each side port. -/
inductive PolarizationMode
  | s
  | p
  deriving DecidableEq

/-- The two interface polarization labels form a finite mode fiber. -/
instance : Fintype PolarizationMode where
  elems := {PolarizationMode.s, PolarizationMode.p}
  complete mode := by
    cases mode <;> simp

/-- The component-owned side ports, each carrying s and p polarization modes. -/
def portFamily : PortModeFamily where
  Port := Port
  Mode := fun _ => PolarizationMode

/-- The registered kernel side order: coordinate zero is negative and one is positive. -/
def sideEquiv : Fin 2 ≃ Port where
  toFun := Fin.cases Port.negativeSide fun _ => Port.positiveSide
  invFun
    | Port.negativeSide => 0
    | Port.positiveSide => 1
  left_inv := by
    intro side
    fin_cases side <;> rfl
  right_inv := by
    intro side
    cases side <;> rfl

/-- The pinned raw order `s negative/positive`, then `p negative/positive`, as owned channels. -/
def channelEquiv : (Fin 2 ⊕ Fin 2) ≃ portFamily.Channel where
  toFun
    | Sum.inl side => ⟨sideEquiv side, PolarizationMode.s⟩
    | Sum.inr side => ⟨sideEquiv side, PolarizationMode.p⟩
  invFun
    | ⟨side, PolarizationMode.s⟩ => Sum.inl (sideEquiv.symm side)
    | ⟨side, PolarizationMode.p⟩ => Sum.inr (sideEquiv.symm side)
  left_inv := by
    intro channel
    rcases channel with side | side <;> simp
  right_inv := by
    rintro ⟨side, mode⟩
    cases mode <;> simp

/-- Owned interface channels are finite through the pinned side/polarization equivalence. -/
noncomputable instance channelFintype : Fintype portFamily.Channel :=
  Fintype.ofEquiv (Fin 2 ⊕ Fin 2) channelEquiv

/-- Owned interface channels have decidable equality in pinned coordinates. -/
instance channelDecidableEq : DecidableEq portFamily.Channel :=
  channelEquiv.symm.decidableEq

/-- Raw s/negative is the owned negative-side s channel. -/
@[simp]
lemma channelEquiv_apply_s_negative :
    channelEquiv (Sum.inl 0) = ⟨Port.negativeSide, PolarizationMode.s⟩ := rfl

/-- Raw s/positive is the owned positive-side s channel. -/
@[simp]
lemma channelEquiv_apply_s_positive :
    channelEquiv (Sum.inl 1) = ⟨Port.positiveSide, PolarizationMode.s⟩ := rfl

/-- Raw p/negative is the owned negative-side p channel. -/
@[simp]
lemma channelEquiv_apply_p_negative :
    channelEquiv (Sum.inr 0) = ⟨Port.negativeSide, PolarizationMode.p⟩ := rfl

/-- Raw p/positive is the owned positive-side p channel. -/
@[simp]
lemma channelEquiv_apply_p_positive :
    channelEquiv (Sum.inr 1) = ⟨Port.positiveSide, PolarizationMode.p⟩ := rfl

/-- The pinned incident-end equivalence to the owned side/polarization channels. -/
def incidentChannelEquiv :
    Incident (Fin 2 ⊕ Fin 2) ≃ Incident portFamily.Channel :=
  Incident.relabelEquiv channelEquiv

/-- The pinned outgoing-end equivalence to the owned side/polarization channels. -/
def outgoingChannelEquiv :
    Outgoing (Fin 2 ⊕ Fin 2) ≃ Outgoing portFamily.Channel :=
  Outgoing.relabelEquiv channelEquiv

/-!
## B. Registered-kernel behavior and scattering realization
-/

/-- The registered s and p Fresnel kernels in independent parallel polarization blocks. -/
def polarizedScattering (interface : PlanarDielectricInterface) (chi_i chi_t : ℝ) :
    ScatteringMatrix (Fin 2 ⊕ Fin 2) :=
  (interface.sFresnelScatteringKernel chi_i chi_t).directSum
    (interface.pFresnelScatteringKernel chi_i chi_t)

/-- The parallel registered-kernel action with nominal incident and outgoing endpoints. -/
def outputMap (interface : PlanarDielectricInterface) (chi_i chi_t : ℝ) :
    ModeAmplitude (Incident (Fin 2 ⊕ Fin 2)) →ₗ[ℂ]
      ModeAmplitude (Outgoing (Fin 2 ⊕ Fin 2)) :=
  (ModeAmplitude.reindex
      (Outgoing.channelEquiv.symm :
        (Fin 2 ⊕ Fin 2) ≃ Outgoing (Fin 2 ⊕ Fin 2))).toLinearEquiv.toLinearMap.comp
    ((polarizedScattering interface chi_i chi_t).toModeTransform.toLinearMap.comp
      (ModeAmplitude.reindex
        (Incident.channelEquiv :
          Incident (Fin 2 ⊕ Fin 2) ≃ Fin 2 ⊕ Fin 2)).toLinearEquiv.toLinearMap)

/-- The registered polarized-kernel graph before physical-channel relabeling. -/
def behavior (interface : PlanarDielectricInterface) (chi_i chi_t : ℝ) :
    LinearBehavior (Incident (Fin 2 ⊕ Fin 2)) (Outgoing (Fin 2 ⊕ Fin 2)) :=
  LinearBehavior.ofLinearMap (outputMap interface chi_i chi_t)

/-- Raw behavior membership is exactly the endpoint-wrapped polarized-kernel action. -/
@[simp]
lemma mem_behavior_iff (interface : PlanarDielectricInterface) (chi_i chi_t : ℝ)
    (incident : ModeAmplitude (Incident (Fin 2 ⊕ Fin 2)))
    (outgoing : ModeAmplitude (Outgoing (Fin 2 ⊕ Fin 2))) :
    (incident, outgoing) ∈ behavior interface chi_i chi_t ↔
      outgoing = ModeAmplitude.reindex Outgoing.channelEquiv.symm
        ((polarizedScattering interface chi_i chi_t).toModeTransform.toLinearMap
          (ModeAmplitude.reindex Incident.channelEquiv incident)) := by
  rfl

/-- The parallel registered Fresnel kernels realize their endpoint behavior exactly. -/
lemma polarizedScattering_realizes_behavior (interface : PlanarDielectricInterface)
    (chi_i chi_t : ℝ) :
    (polarizedScattering interface chi_i chi_t).toOrientedModeTransform.toBehavior =
      behavior interface chi_i chi_t := by
  ext ⟨incident, outgoing⟩
  rw [ModeTransform.mem_toBehavior_iff_toLinearMap, mem_behavior_iff,
    ScatteringMatrix.toLinearMap_toOrientedModeTransform]

/-- The registered polarized-kernel behavior in component-owned endpoint labels. -/
def physicalBehavior (interface : PlanarDielectricInterface) (chi_i chi_t : ℝ) :
    LinearBehavior (Incident portFamily.Channel) (Outgoing portFamily.Channel) :=
  (behavior interface chi_i chi_t).reindex incidentChannelEquiv outgoingChannelEquiv

/-- Physical behavior membership is kernel behavior membership in pinned raw coordinates. -/
@[simp]
lemma mem_physicalBehavior_iff (interface : PlanarDielectricInterface) (chi_i chi_t : ℝ)
    (incident : ModeAmplitude (Incident portFamily.Channel))
    (outgoing : ModeAmplitude (Outgoing portFamily.Channel)) :
    (incident, outgoing) ∈ physicalBehavior interface chi_i chi_t ↔
      (ModeAmplitude.reindex incidentChannelEquiv.symm incident,
        ModeAmplitude.reindex outgoingChannelEquiv.symm outgoing) ∈
          behavior interface chi_i chi_t := by
  rw [physicalBehavior, LinearBehavior.mem_reindex_iff]

/-- The polarized Fresnel kernels in component-owned side/polarization labels. -/
def physicalScattering (interface : PlanarDielectricInterface) (chi_i chi_t : ℝ) :
    ScatteringMatrix portFamily.Channel :=
  (polarizedScattering interface chi_i chi_t).reindex channelEquiv

/-- Physical scattering is the polarized kernel in the pinned endpoint coordinates. -/
lemma physicalScattering_toOrientedModeTransform (interface : PlanarDielectricInterface)
    (chi_i chi_t : ℝ) :
    (physicalScattering interface chi_i chi_t).toOrientedModeTransform =
      (polarizedScattering interface chi_i chi_t).toOrientedModeTransform.reindex
        incidentChannelEquiv outgoingChannelEquiv := by
  ext output input
  rcases output with ⟨⟨outputPort, outputMode⟩⟩
  rcases input with ⟨⟨inputPort, inputMode⟩⟩
  cases outputPort <;> cases outputMode <;>
    cases inputPort <;> cases inputMode <;> rfl

/-- Physical scattering realizes the transported registered-kernel behavior exactly. -/
lemma physicalScattering_realizes_physicalBehavior
    (interface : PlanarDielectricInterface) (chi_i chi_t : ℝ) :
    (physicalScattering interface chi_i chi_t).toOrientedModeTransform.toBehavior =
      physicalBehavior interface chi_i chi_t := by
  rw [physicalScattering_toOrientedModeTransform, ModeTransform.toBehavior_reindex]
  rw [polarizedScattering_realizes_behavior]
  rfl

/-- Positive propagating normal factors give algebraic losslessness in owned labels. -/
lemma physicalScattering_isLossless (interface : PlanarDielectricInterface)
    {chi_i chi_t : ℝ} (hIncident : 0 < chi_i) (hTransmitted : 0 < chi_t) :
    (physicalScattering interface chi_i chi_t).IsLossless := by
  apply (ScatteringMatrix.isLossless_reindex_iff channelEquiv
    (polarizedScattering interface chi_i chi_t)).mpr
  exact (interface.sFresnelScatteringKernel_isLossless hIncident hTransmitted).directSum
    (interface.pFresnelScatteringKernel_isLossless hIncident hTransmitted)

/-!
## C. Direct component-family witness
-/

/-- The polarized interface as a singleton family with owned side/polarization channels. -/
def componentFamily (interface : PlanarDielectricInterface) (chi_i chi_t : ℝ) :
    ScatteringComponentFamily where
  Component := Unit
  portFamily := fun _ => portFamily
  scattering := fun _ => physicalScattering interface chi_i chi_t

/-- The singleton witness stores the interface-owned port family definitionally. -/
@[simp]
lemma componentFamily_portFamily (interface : PlanarDielectricInterface)
    (chi_i chi_t : ℝ) :
    (componentFamily interface chi_i chi_t).portFamily () = portFamily := rfl

/-- The singleton witness stores the physical polarized scattering law definitionally. -/
@[simp]
lemma componentFamily_scattering (interface : PlanarDielectricInterface)
    (chi_i chi_t : ℝ) :
    (componentFamily interface chi_i chi_t).scattering () =
      physicalScattering interface chi_i chi_t := rfl

end PlanarDielectricInterface

end

end Optics
