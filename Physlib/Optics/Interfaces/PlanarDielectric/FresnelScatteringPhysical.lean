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
negative/positive side. This is the ordering declared by
`FresnelScattering.lean:83-95,145-161`. The two registered kernels are combined only by
block-diagonal parallel composition and then transported to these owned channels.

The angle convention is the one already fixed in `AngularGeometry.lean`: incident and transmitted
angles are measured from the positive-side normal (`AngularGeometry.lean:88-89,105-106`), while
the reflected angle is measured from the negative-side normal (`AngularGeometry.lean:97-98`). The
present algebraic kernel carries only `chi_i` and `chi_t`; it does not redefine those angles.

The p entries use Physlib's fork-declared full-electric-vector convention
(`FresnelAmplitude.lean:135-149`). At normal incidence `r_p = -r_s` and `t_p = t_s`; some
literature instead orients the reflected p basis so the reflection signs agree. This package
preserves the registered full-vector coefficients and does not force a cross-convention match.

## ii. Key results

- `PlanarDielectricInterface.portFamily`: the owned negative- and positive-side ports.
- `PlanarDielectricInterface.channelEquiv`: the pinned side/polarization channel equivalence.
- `PlanarDielectricInterface.endpointOutput`: the four independent s/p side equations.
- `PlanarDielectricInterface.polarizedScattering`: parallel registered s/p kernels.
- `PlanarDielectricInterface.physicalBehavior`: the kernel graph in owned endpoint labels.
- `PlanarDielectricInterface.physicalScattering`: the kernel in owned channel labels.
- `PlanarDielectricInterface.physicalScattering_realizes_physicalBehavior`: exact realization.
- `PlanarDielectricInterface.componentFamily`: direct `ScatteringComponentFamily` consumption.

## iii. Table of contents

- A. Owned sides and pinned polarization coordinates
- B. Independent endpoint behavior and scattering realization
- C. Direct component-family witness

## iv. References

This file packages the algebraic completion from `FresnelScattering.lean`; it does not upgrade that
completion to a reverse-incidence Maxwell derivation or an E6 physical bidirectional interface.
Its losslessness result is normalized squared-amplitude bookkeeping, not electromagnetic power.
No reciprocity, time reversal, reference-plane law, modal completeness, propagation, causality,
dispersion, observer convention, measurement, or physical realization is asserted. No `tau`
pairing is defined or inferred. The typed reciprocity predicate and its reference-plane convention
belong to a separate development.
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
    cases side <;> cases mode <;> rfl

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
## B. Independent endpoint behavior and scattering realization
-/

/-- One polarization's independent two-side endpoint map.

The definition states reflection/transmission coordinates directly and does not use a scattering
matrix or a Fresnel kernel.
-/
def sideOutputMap (reflection normalizedTransmission : ℝ) :
    ModeAmplitude (Fin 2) →ₗ[ℂ] ModeAmplitude (Fin 2) :=
  Matrix.toEuclideanLin !![
    (reflection : ℂ), (normalizedTransmission : ℂ);
    (normalizedTransmission : ℂ), -(reflection : ℂ)]

/-- The independent two-side map satisfies its two displayed endpoint equations. -/
lemma sideOutputMap_apply (reflection normalizedTransmission : ℝ)
    (input : ModeAmplitude (Fin 2)) :
    sideOutputMap reflection normalizedTransmission input =
      WithLp.toLp 2 ![
        (reflection : ℂ) * input 0 + (normalizedTransmission : ℂ) * input 1,
        (normalizedTransmission : ℂ) * input 0 - (reflection : ℂ) * input 1] := by
  apply WithLp.ofLp_injective 2
  funext output
  fin_cases output <;>
    simp [sideOutputMap, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, sub_eq_add_neg]

/-- The four independently specified s/p side-coordinate endpoint equations.

The s block precedes the p block, and within each block coordinate zero is the negative side. The
coefficients are the registered Fresnel coefficient primitives and their registered flux
normalization. No scattering matrix occurs in this definition.
-/
def endpointOutput (interface : PlanarDielectricInterface) (chi_i chi_t : ℝ)
    (input : ModeAmplitude (Fin 2 ⊕ Fin 2)) : ModeAmplitude (Fin 2 ⊕ Fin 2) :=
  let flux := interface.fresnelTransmissionFluxFactor chi_i chi_t
  let sReflection := interface.sFresnelReflectionCoefficient chi_i chi_t
  let sTransmission := powerNormalizedFresnelTransmissionCoefficient flux
    (interface.sFresnelTransmissionCoefficient chi_i chi_t)
  let pReflection := interface.pFresnelReflectionCoefficient chi_i chi_t
  let pTransmission := powerNormalizedFresnelTransmissionCoefficient flux
    (interface.pFresnelTransmissionCoefficient chi_i chi_t)
  (WithLp.toLp 2 ![
    (sReflection : ℂ) * input (Sum.inl 0) +
      (sTransmission : ℂ) * input (Sum.inl 1),
    (sTransmission : ℂ) * input (Sum.inl 0) -
      (sReflection : ℂ) * input (Sum.inl 1)]).directSum
    (WithLp.toLp 2 ![
      (pReflection : ℂ) * input (Sum.inr 0) +
        (pTransmission : ℂ) * input (Sum.inr 1),
      (pTransmission : ℂ) * input (Sum.inr 0) -
        (pReflection : ℂ) * input (Sum.inr 1)])

/-- The independent endpoint-equation map with nominal incident and outgoing wrappers. -/
def outputMap (interface : PlanarDielectricInterface) (chi_i chi_t : ℝ) :
    ModeAmplitude (Incident (Fin 2 ⊕ Fin 2)) →ₗ[ℂ]
      ModeAmplitude (Outgoing (Fin 2 ⊕ Fin 2)) :=
  let rawIncident :=
    (ModeAmplitude.reindex
      (Incident.channelEquiv :
        Incident (Fin 2 ⊕ Fin 2) ≃ Fin 2 ⊕ Fin 2)).toLinearEquiv.toLinearMap
  let sIncident :=
    (ModeAmplitude.restrictInlLinearMap :
      ModeAmplitude (Fin 2 ⊕ Fin 2) →ₗ[ℂ] ModeAmplitude (Fin 2)).comp rawIncident
  let pIncident :=
    (ModeAmplitude.restrictInrLinearMap :
      ModeAmplitude (Fin 2 ⊕ Fin 2) →ₗ[ℂ] ModeAmplitude (Fin 2)).comp rawIncident
  let flux := interface.fresnelTransmissionFluxFactor chi_i chi_t
  let sOutput :=
    (sideOutputMap (interface.sFresnelReflectionCoefficient chi_i chi_t)
      (powerNormalizedFresnelTransmissionCoefficient flux
        (interface.sFresnelTransmissionCoefficient chi_i chi_t))).comp sIncident
  let pOutput :=
    (sideOutputMap (interface.pFresnelReflectionCoefficient chi_i chi_t)
      (powerNormalizedFresnelTransmissionCoefficient flux
        (interface.pFresnelTransmissionCoefficient chi_i chi_t))).comp pIncident
  (ModeAmplitude.reindex
      (Outgoing.channelEquiv.symm :
        (Fin 2 ⊕ Fin 2) ≃ Outgoing (Fin 2 ⊕ Fin 2))).toLinearEquiv.toLinearMap.comp
    (ModeAmplitude.directSumLinearEquiv.toLinearMap.comp
      (sOutput.prod pOutput))

/-- The independent endpoint map evaluates to the four declared side equations. -/
lemma outputMap_apply (interface : PlanarDielectricInterface) (chi_i chi_t : ℝ)
    (incident : ModeAmplitude (Incident (Fin 2 ⊕ Fin 2))) :
    outputMap interface chi_i chi_t incident =
      ModeAmplitude.reindex Outgoing.channelEquiv.symm
        (endpointOutput interface chi_i chi_t
          (ModeAmplitude.reindex Incident.channelEquiv incident)) := by
  change ModeAmplitude.reindex Outgoing.channelEquiv.symm
      ((sideOutputMap _ _
          (ModeAmplitude.reindex Incident.channelEquiv incident).restrictInl).directSum
        (sideOutputMap _ _
          (ModeAmplitude.reindex Incident.channelEquiv incident).restrictInr)) = _
  rw [sideOutputMap_apply, sideOutputMap_apply]
  rfl

/-- The independent four-equation behavior before physical-channel relabeling. -/
def behavior (interface : PlanarDielectricInterface) (chi_i chi_t : ℝ) :
    LinearBehavior (Incident (Fin 2 ⊕ Fin 2)) (Outgoing (Fin 2 ⊕ Fin 2)) :=
  LinearBehavior.ofLinearMap (outputMap interface chi_i chi_t)

/-- Raw behavior membership is exactly the four independent endpoint equations. -/
@[simp]
lemma mem_behavior_iff (interface : PlanarDielectricInterface) (chi_i chi_t : ℝ)
    (incident : ModeAmplitude (Incident (Fin 2 ⊕ Fin 2)))
    (outgoing : ModeAmplitude (Outgoing (Fin 2 ⊕ Fin 2))) :
    (incident, outgoing) ∈ behavior interface chi_i chi_t ↔
      outgoing = ModeAmplitude.reindex Outgoing.channelEquiv.symm
        (endpointOutput interface chi_i chi_t
          (ModeAmplitude.reindex Incident.channelEquiv incident)) := by
  rw [behavior, LinearBehavior.mem_ofLinearMap_iff, outputMap_apply]

/-- The registered s and p Fresnel kernels in independent parallel polarization blocks. -/
def polarizedScattering (interface : PlanarDielectricInterface) (chi_i chi_t : ℝ) :
    ScatteringMatrix (Fin 2 ⊕ Fin 2) :=
  (interface.sFresnelScatteringKernel chi_i chi_t).directSum
    (interface.pFresnelScatteringKernel chi_i chi_t)

/-- The direct-sum kernel action satisfies the independently stated four endpoint equations. -/
lemma polarizedScattering_toLinearMap_apply (interface : PlanarDielectricInterface)
    (chi_i chi_t : ℝ) (input : ModeAmplitude (Fin 2 ⊕ Fin 2)) :
    (polarizedScattering interface chi_i chi_t).toModeTransform.toLinearMap input =
      endpointOutput interface chi_i chi_t input := by
  rw [← ModeAmplitude.directSum_restrict input, polarizedScattering,
    ModeTransform.directSum_apply, sFresnelScatteringKernel,
    pFresnelScatteringKernel, scalarFresnelScatteringKernel_toLinearMap_apply,
    scalarFresnelScatteringKernel_toLinearMap_apply]
  rfl

/-- The parallel registered kernels realize the independent four-equation behavior exactly. -/
lemma polarizedScattering_realizes_behavior (interface : PlanarDielectricInterface)
    (chi_i chi_t : ℝ) :
    (polarizedScattering interface chi_i chi_t).toOrientedModeTransform.toBehavior =
      behavior interface chi_i chi_t := by
  ext ⟨incident, outgoing⟩
  rw [ModeTransform.mem_toBehavior_iff_toLinearMap, mem_behavior_iff,
    ScatteringMatrix.toLinearMap_toOrientedModeTransform,
    polarizedScattering_toLinearMap_apply]

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
