/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.ScatteringComponentFamily
public import Physlib.Optics.Polarization.Basic

/-!
# Component-owned physical port for Jones polarization scattering

## i. Overview

This file presents any registered `JonesMatrix` as a one-port scattering component. The component
owns one aperture port with the existing two Jones coordinates as its mode fiber. `channelEquiv`
pins coordinate `0` and coordinate `1` to that owned port without assigning new polarization
names or changing the registered Jones convention.

The behavior transports `JonesMatrix.act` (`Polarization/Basic.lean:390-396`) through incident and
outgoing endpoint wrappers. The scattering adapter stores the same registered Jones entries and is
proved to realize that behavior exactly. `componentFamily` is a direct singleton
`ScatteringComponentFamily`, so no downstream caller supplies a post-hoc port identification.

Physlib's `Phasor.realize` is the positive-time convention
`Re (z exp (I * carrierPhase))` (`Polarization/Basic.lean:66-70`). The registered
`JonesVector.plusIQuadrature` has second component `I` times the first
(`Polarization/Basic.lean:363-367`). Under the binding C-02 receiver/optics observer convention it
is the right-circular state. This package adds no handedness alias, alters no convention, and
manufactures no propagation direction from Jones data.

## ii. Key results

- `JonesMatrix.portFamily`: the owned aperture and its two Jones-coordinate modes.
- `JonesMatrix.channelEquiv`: the pinned Jones-coordinate channel equivalence.
- `JonesMatrix.physicalBehavior`: the registered Jones action in owned endpoint labels.
- `JonesMatrix.physicalScattering`: the Jones matrix in owned channel labels.
- `JonesMatrix.physicalScattering_realizes_physicalBehavior`: exact graph realization.
- `JonesMatrix.componentFamily`: direct consumption by `ScatteringComponentFamily`.

## iii. Table of contents

- A. Owned aperture and pinned Jones coordinates
- B. Jones action and scattering realization
- C. Direct component-family witness

## iv. References

This is a coordinate and ownership adapter for the registered Jones primitives. Its unitarity
result is squared raw-Jones-amplitude bookkeeping, not electromagnetic power or a physical
losslessness claim. No reciprocity, time reversal, reverse-incidence Maxwell law, modal
completeness, propagation, reference-plane, causality, dispersion, or physical realization is
asserted.
-/

@[expose] public section

namespace Optics

noncomputable section

namespace JonesMatrix

/-!
## A. Owned aperture and pinned Jones coordinates
-/

/-- The independently wireable aperture of a Jones polarization component. -/
inductive Port
  | aperture
  deriving DecidableEq

/-- The single Jones aperture forms a finite port family. -/
instance : Fintype Port where
  elems := {Port.aperture}
  complete port := by
    cases port
    simp

/-- The component-owned aperture carrying the two registered Jones coordinates. -/
def portFamily : PortModeFamily where
  Port := Port
  Mode := fun _ => Fin 2

/-- The pinned equivalence from Jones coordinates to owned aperture channels. -/
def channelEquiv : Fin 2 ≃ portFamily.Channel where
  toFun coordinate := ⟨Port.aperture, coordinate⟩
  invFun
    | ⟨Port.aperture, coordinate⟩ => coordinate
  left_inv := by
    intro coordinate
    rfl
  right_inv := by
    rintro ⟨port, coordinate⟩
    cases port
    rfl

/-- The owned Jones channel family is finite through its pinned coordinate equivalence. -/
noncomputable instance channelFintype : Fintype portFamily.Channel :=
  Fintype.ofEquiv (Fin 2) channelEquiv

/-- Owned Jones channels have decidable equality in pinned coordinates. -/
instance channelDecidableEq : DecidableEq portFamily.Channel :=
  channelEquiv.symm.decidableEq

/-- A Jones coordinate becomes the corresponding mode at the owned aperture. -/
@[simp]
lemma channelEquiv_apply (coordinate : Fin 2) :
    channelEquiv coordinate = ⟨Port.aperture, coordinate⟩ := rfl

/-- The pinned incident-end equivalence to the owned aperture. -/
def incidentChannelEquiv : Incident (Fin 2) ≃ Incident portFamily.Channel :=
  Incident.relabelEquiv channelEquiv

/-- The pinned outgoing-end equivalence to the owned aperture. -/
def outgoingChannelEquiv : Outgoing (Fin 2) ≃ Outgoing portFamily.Channel :=
  Outgoing.relabelEquiv channelEquiv

/-- A raw incident Jones coordinate becomes the matching aperture endpoint. -/
@[simp]
lemma incidentChannelEquiv_apply (coordinate : Fin 2) :
    incidentChannelEquiv (Incident.mk coordinate) =
      Incident.mk ⟨Port.aperture, coordinate⟩ := rfl

/-- A raw outgoing Jones coordinate becomes the matching aperture endpoint. -/
@[simp]
lemma outgoingChannelEquiv_apply (coordinate : Fin 2) :
    outgoingChannelEquiv (Outgoing.mk coordinate) =
      Outgoing.mk ⟨Port.aperture, coordinate⟩ := rfl

/-!
## B. Jones action and scattering realization
-/

/-- The registered Jones action, with nominal incident and outgoing endpoint types. -/
def outputMap (matrix : JonesMatrix) :
    ModeAmplitude (Incident (Fin 2)) →ₗ[ℂ] ModeAmplitude (Outgoing (Fin 2)) :=
  (ModeAmplitude.reindex
      (Outgoing.channelEquiv.symm : Fin 2 ≃ Outgoing (Fin 2))).toLinearEquiv.toLinearMap.comp
    ((Matrix.toEuclideanLin matrix.entries).comp
      (ModeAmplitude.reindex
        (Incident.channelEquiv : Incident (Fin 2) ≃ Fin 2)).toLinearEquiv.toLinearMap)

/-- Endpoint unwrapping makes `outputMap` exactly the registered `JonesMatrix.act`. -/
lemma outputMap_apply (matrix : JonesMatrix)
    (incident : ModeAmplitude (Incident (Fin 2))) :
    outputMap matrix incident =
      ModeAmplitude.reindex Outgoing.channelEquiv.symm
        (matrix.act ⟨ModeAmplitude.reindex Incident.channelEquiv incident⟩).components := by
  rfl

/-- The registered Jones action as an oriented endpoint behavior. -/
def behavior (matrix : JonesMatrix) :
    LinearBehavior (Incident (Fin 2)) (Outgoing (Fin 2)) :=
  LinearBehavior.ofLinearMap (outputMap matrix)

/-- Behavior membership is exactly the endpoint-wrapped registered Jones action. -/
@[simp]
lemma mem_behavior_iff (matrix : JonesMatrix)
    (incident : ModeAmplitude (Incident (Fin 2)))
    (outgoing : ModeAmplitude (Outgoing (Fin 2))) :
    (incident, outgoing) ∈ behavior matrix ↔
      outgoing = ModeAmplitude.reindex Outgoing.channelEquiv.symm
        (matrix.act ⟨ModeAmplitude.reindex Incident.channelEquiv incident⟩).components := by
  rw [behavior, LinearBehavior.mem_ofLinearMap_iff, outputMap_apply]

/-- A registered Jones matrix viewed as a scattering matrix on its two raw coordinates. -/
def scattering (matrix : JonesMatrix) : ScatteringMatrix (Fin 2) where
  toModeTransform := matrix.entries

/-- The scattering adapter realizes the registered Jones action exactly. -/
lemma scattering_realizes_behavior (matrix : JonesMatrix) :
    (scattering matrix).toOrientedModeTransform.toBehavior = behavior matrix := by
  ext ⟨incident, outgoing⟩
  rw [ModeTransform.mem_toBehavior_iff_toLinearMap, mem_behavior_iff,
    ScatteringMatrix.toLinearMap_toOrientedModeTransform]
  rfl

/-- The registered Jones behavior in component-owned endpoint labels. -/
def physicalBehavior (matrix : JonesMatrix) :
    LinearBehavior (Incident portFamily.Channel) (Outgoing portFamily.Channel) :=
  (behavior matrix).reindex incidentChannelEquiv outgoingChannelEquiv

/-- Physical behavior membership is registered Jones behavior membership in pinned coordinates. -/
@[simp]
lemma mem_physicalBehavior_iff (matrix : JonesMatrix)
    (incident : ModeAmplitude (Incident portFamily.Channel))
    (outgoing : ModeAmplitude (Outgoing portFamily.Channel)) :
    (incident, outgoing) ∈ physicalBehavior matrix ↔
      (ModeAmplitude.reindex incidentChannelEquiv.symm incident,
        ModeAmplitude.reindex outgoingChannelEquiv.symm outgoing) ∈ behavior matrix := by
  rw [physicalBehavior, LinearBehavior.mem_reindex_iff]

/-- The registered Jones matrix in component-owned aperture-channel labels. -/
def physicalScattering (matrix : JonesMatrix) : ScatteringMatrix portFamily.Channel :=
  (scattering matrix).reindex channelEquiv

/-- The physical scattering adapter is the Jones adapter in pinned endpoint coordinates. -/
lemma physicalScattering_toOrientedModeTransform (matrix : JonesMatrix) :
    (physicalScattering matrix).toOrientedModeTransform =
      (scattering matrix).toOrientedModeTransform.reindex
        incidentChannelEquiv outgoingChannelEquiv := by
  ext output input
  rcases output with ⟨⟨outputPort, outputMode⟩⟩
  rcases input with ⟨⟨inputPort, inputMode⟩⟩
  cases outputPort
  cases inputPort
  rfl

/-- Physical scattering realizes the transported registered Jones behavior exactly. -/
lemma physicalScattering_realizes_physicalBehavior (matrix : JonesMatrix) :
    (physicalScattering matrix).toOrientedModeTransform.toBehavior =
      physicalBehavior matrix := by
  rw [physicalScattering_toOrientedModeTransform, ModeTransform.toBehavior_reindex]
  rw [scattering_realizes_behavior]
  rfl

/-- A unitary Jones matrix gives algebraic squared-amplitude losslessness after relabeling. -/
lemma physicalScattering_isLossless (matrix : JonesMatrix) (hMatrix : matrix.IsUnitary) :
    (physicalScattering matrix).IsLossless := by
  apply (ScatteringMatrix.isLossless_reindex_iff channelEquiv (scattering matrix)).mpr
  exact hMatrix

/-!
## C. Direct component-family witness
-/

/-- A Jones matrix as a singleton scattering-component family with its owned aperture. -/
def componentFamily (matrix : JonesMatrix) : ScatteringComponentFamily where
  Component := Unit
  portFamily := fun _ => portFamily
  scattering := fun _ => physicalScattering matrix

/-- The singleton witness stores the owned Jones port family definitionally. -/
@[simp]
lemma componentFamily_portFamily (matrix : JonesMatrix) :
    (componentFamily matrix).portFamily () = portFamily := rfl

/-- The singleton witness stores the physical Jones scattering law definitionally. -/
@[simp]
lemma componentFamily_scattering (matrix : JonesMatrix) :
    (componentFamily matrix).scattering () = physicalScattering matrix := rfl

end JonesMatrix

end

end Optics
