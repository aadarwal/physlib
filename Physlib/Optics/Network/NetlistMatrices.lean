/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.NetlistData

/-!
# Executable matrices for certified finite optical netlists

## i. Overview

This file compiles certified finite-netlist data directly to the four shaped coefficient matrices
of the N4 network equations. Component blocks give `S`, stored bidirectional physical connections
give the unit-gain return matrix `C`, and the exact complement of their channel image gives the
incident and outgoing exposure matrices `E_in` and `E_out`.

All four constructions are executable over a coefficient type with distinguished zero and one.
Mapping coefficients into
`ℂ` agrees entrywise with the transforms derived independently by the singular-safe `FlatNetlist`
kernel. The equality proof is extensional, so it does not identify the constructive equality
decisions used here with the kernel's local classical decisions.

## ii. Key results

- `FiniteNetlistData.scatteringMatrix`: executable block-diagonal component matrix `S`.
- `FiniteNetlistData.routingMatrix`: executable ambient return matrix `C`.
- `FiniteNetlistData.inputExposureMatrix`: executable external incident injection `E_in`.
- `FiniteNetlistData.inputExposureMatrix_mulVec_external`: exact executable boundary injection.
- `FiniteNetlistData.outputExposureMatrix`: executable external outgoing exposure `E_out`.
- `FiniteNetlistData.outputReadoutMatrix_eq_transpose`: readout is exactly `E_outᵀ`.
- `FiniteNetlistData.feedbackMatrix`: the executable implicit operator `1 - C * S`.
- `FiniteNetlistData.feedbackMatrixInTypedCoordinates_eq_feedbackOperator`: evaluated feedback is
  exactly N4's typed implicit operator.
- `FiniteNetlistData.mem_toFlatNetlist_behavior_iff_matrixEquations`: evaluated executable
  equations are exactly the compiled singular-safe external relation.

## iii. Table of contents

- A. Executable connected and external channel indices
- B. Shaped coefficient matrices
- C. Soundness with respect to the typed N4 kernel

## iv. References

The matrices encode component action, topology, and boundary exposure only. They do not invert the
feedback operator, decide a determinant, assert unique solvability, or assign gain, phase, delay,
passivity, losslessness, or reciprocity to a physical wire. The output exposure is kept distinct
from its coordinate readout.

-/

@[expose] public section

namespace Optics

/-!

## A. Executable connected and external channel indices

-/

namespace FiniteNetlistShape

variable (shape : FiniteNetlistShape)

/-- The component-indexed sum of all local channels in a finite netlist shape. -/
abbrev IndexedChannel := Σ component, shape.LocalChannel component

/-- Reassociate a component-indexed local channel as an aggregate physical channel. -/
def indexedChannelEquiv : shape.IndexedChannel ≃ shape.Channel where
  toFun := fun ⟨component, ⟨port, mode⟩⟩ => ⟨⟨component, port⟩, mode⟩
  invFun := fun ⟨⟨component, port⟩, mode⟩ => ⟨component, ⟨port, mode⟩⟩
  left_inv := by
    rintro ⟨component, ⟨port, mode⟩⟩
    rfl
  right_inv := by
    rintro ⟨⟨component, port⟩, mode⟩
    rfl

end FiniteNetlistShape

namespace FiniteNetlistData

variable {R : Type*} (data : FiniteNetlistData R)

/-- The executable dependent sum of all stored connection-local channels. -/
abbrev ConnectedChannel := Σ index : data.Connection,
  data.shape.Mode (data.connection index).first ⊕
    data.shape.Mode (data.connection index).second

/-- Aggregate finite-data channels have a constructive finite enumeration. -/
local instance channelFintype : Fintype data.shape.Channel := by
  letI : Fintype data.shape.IndexedChannel := by
    change Fintype (Σ component : data.shape.Component,
      Σ port : data.shape.LocalPort component,
        Fin (data.shape.modeCount component port))
    infer_instance
  exact Fintype.ofEquiv data.shape.IndexedChannel data.shape.indexedChannelEquiv

/-- Aggregate finite-data channels have constructive decidable equality. -/
local instance channelDecidableEq : DecidableEq data.shape.Channel := by
  letI : DecidableEq data.shape.IndexedChannel := by
    change DecidableEq (Σ component : data.shape.Component,
      Σ port : data.shape.LocalPort component,
        Fin (data.shape.modeCount component port))
    infer_instance
  exact data.shape.indexedChannelEquiv.symm.decidableEq

/-- Stored connection-local channels have a constructive finite enumeration. -/
local instance connectedChannelFintype : Fintype data.ConnectedChannel := by
  change Fintype (Σ index : data.Connection,
    data.shape.Mode (data.connection index).first ⊕
      data.shape.Mode (data.connection index).second)
  infer_instance

/-- Stored connection-local channels have constructive decidable equality. -/
local instance connectedChannelDecidableEq : DecidableEq data.ConnectedChannel := by
  change DecidableEq (Σ index : data.Connection,
    data.shape.Mode (data.connection index).first ⊕
      data.shape.Mode (data.connection index).second)
  infer_instance

/-- Map a stored connection-local channel to its aggregate physical channel.

The map is total on unchecked data. A `WellFormed` certificate later proves that it is the
injective embedding used by the N4 kernel.
-/
def connectedChannelMap : data.ConnectedChannel → data.shape.Channel
  | ⟨index, Sum.inl mode⟩ => ⟨(data.connection index).first, mode⟩
  | ⟨index, Sum.inr mode⟩ => ⟨(data.connection index).second, mode⟩

/-- Apply the stored forward or inverse mode table to obtain a connection-local mate.

The function is total on unchecked data. Its involutive equivalence law is supplied only after
the two stored tables pass the `WellFormed` inverse checks.
-/
def mate : data.ConnectedChannel → data.ConnectedChannel
  | ⟨index, Sum.inl mode⟩ =>
      ⟨index, Sum.inr ((data.connection index).modeMap mode)⟩
  | ⟨index, Sum.inr mode⟩ =>
      ⟨index, Sum.inl ((data.connection index).modeInv mode)⟩

/-- A well-formed stored channel map is the embedding used by typed N4 compilation. -/
def connectedChannelEmbedding (h : data.WellFormed) :
    data.ConnectedChannel ↪ data.shape.Channel where
  toFun := data.connectedChannelMap
  inj' := by
    rintro ⟨first, firstMode⟩ ⟨second, secondMode⟩ hChannel
    rcases firstMode with firstMode | firstMode <;>
      rcases secondMode with secondMode | secondMode
    · have hEndpoint : (first, PortConnection.End.left) =
          (second, PortConnection.End.left) :=
        h.2.2 (congrArg Sigma.fst hChannel)
      cases hEndpoint
      cases hChannel
      rfl
    · have hEndpoint : (first, PortConnection.End.left) =
          (second, PortConnection.End.right) :=
        h.2.2 (congrArg Sigma.fst hChannel)
      cases hEndpoint
    · have hEndpoint : (first, PortConnection.End.right) =
          (second, PortConnection.End.left) :=
        h.2.2 (congrArg Sigma.fst hChannel)
      cases hEndpoint
    · have hEndpoint : (first, PortConnection.End.right) =
          (second, PortConnection.End.right) :=
        h.2.2 (congrArg Sigma.fst hChannel)
      cases hEndpoint
      cases hChannel
      rfl

/-- The executable external channels are the complement of the stored connected-channel image. -/
abbrev ExternalChannel := (Set.range data.connectedChannelMap)ᶜ

/-!

## B. Shaped coefficient matrices

-/

section Matrices

variable [Zero R] [One R]

/-- The block-diagonal component matrix before aggregate-channel reassociation. -/
def indexedScatteringMatrix :
    Matrix data.shape.IndexedChannel data.shape.IndexedChannel R :=
  Matrix.blockDiagonal' data.scattering

/-- The executable aggregate component matrix `S : A_in → A_out`. -/
def scatteringMatrix :
    Matrix (Outgoing data.shape.Channel) (Incident data.shape.Channel) R :=
  Matrix.reindex
    (data.shape.indexedChannelEquiv.trans Outgoing.channelEquiv.symm)
    (data.shape.indexedChannelEquiv.trans Incident.channelEquiv.symm)
    data.indexedScatteringMatrix

/-- The executable ambient return matrix `C : A_out → A_in`.

An entry is one exactly when a stored connected channel supplies the outgoing coordinate and its
stored mate supplies the incident coordinate.
-/
def routingMatrix :
    Matrix (Incident data.shape.Channel) (Outgoing data.shape.Channel) R :=
  fun incident outgoing =>
    if ∃ channel : data.ConnectedChannel,
        data.connectedChannelMap channel = outgoing.channel ∧
          data.connectedChannelMap (data.mate channel) = incident.channel
    then 1 else 0

/-- The executable external incident injection `E_in : U → A_in`. -/
def inputExposureMatrix :
    Matrix (Incident data.shape.Channel) (Incident data.ExternalChannel) R :=
  fun incident external => if incident.channel = external.channel.1 then 1 else 0

/-- The executable external outgoing exposure `E_out : Y → A_out`. -/
def outputExposureMatrix :
    Matrix (Outgoing data.shape.Channel) (Outgoing data.ExternalChannel) R :=
  fun outgoing external => if outgoing.channel = external.channel.1 then 1 else 0

/-- The executable external outgoing coordinate readout. -/
def outputReadoutMatrix :
    Matrix (Outgoing data.ExternalChannel) (Outgoing data.shape.Channel) R :=
  fun external outgoing => if outgoing.channel = external.channel.1 then 1 else 0

/-- Executable output readout is the transpose of executable output exposure. -/
lemma outputReadoutMatrix_eq_transpose :
    data.outputReadoutMatrix = data.outputExposureMatrix.transpose := by
  rfl

end Matrices

section Feedback

variable [Ring R]

/-- The executable implicit feedback matrix `1 - C * S`, without an inverse or solvability claim. -/
def feedbackMatrix :
    Matrix (Incident data.shape.Channel) (Incident data.shape.Channel) R :=
  1 - data.routingMatrix * data.scatteringMatrix

end Feedback

/-!

## C. Soundness with respect to the typed N4 kernel

-/

section MatrixEntries

variable [Zero R]

/-- A raw diagonal component block is exactly its stored local scattering matrix. -/
@[simp]
lemma scatteringMatrix_entry_same (component : data.shape.Component)
    (output input : data.shape.LocalChannel component) :
    data.scatteringMatrix
        (Outgoing.mk (data.shape.indexedChannelEquiv ⟨component, output⟩))
        (Incident.mk (data.shape.indexedChannelEquiv ⟨component, input⟩)) =
      data.scattering component output input := by
  exact Matrix.blockDiagonal'_apply_eq data.scattering component output input

/-- Raw scattering has no direct entry between two different component blocks. -/
lemma scatteringMatrix_entry_of_ne {first second : data.shape.Component}
    (hComponent : first ≠ second) (output : data.shape.LocalChannel first)
    (input : data.shape.LocalChannel second) :
    data.scatteringMatrix
        (Outgoing.mk (data.shape.indexedChannelEquiv ⟨first, output⟩))
        (Incident.mk (data.shape.indexedChannelEquiv ⟨second, input⟩)) = 0 := by
  exact Matrix.blockDiagonal'_apply_ne data.scattering output input hComponent

variable [One R]

/-- Raw routing has unit gain from every stored channel to its stored mate. -/
@[simp]
lemma routingMatrix_entry_mate (channel : data.ConnectedChannel) :
    data.routingMatrix
        (Incident.mk (data.connectedChannelMap (data.mate channel)))
        (Outgoing.mk (data.connectedChannelMap channel)) = 1 := by
  simp only [routingMatrix]
  rw [if_pos ⟨channel, rfl, rfl⟩]

/-- Raw external incident injection has a unit entry on its selected ambient coordinate. -/
@[simp]
lemma inputExposureMatrix_entry (external : data.ExternalChannel) :
    data.inputExposureMatrix (Incident.mk external.1) (Incident.mk external) = 1 := by
  simp [inputExposureMatrix]

end MatrixEntries

section Soundness

variable [Semiring R]

/-- Raw input exposure injects an external amplitude at its underlying ambient coordinate. -/
lemma inputExposureMatrix_mulVec_external [Fintype data.ExternalChannel]
    (input : Incident data.ExternalChannel → R) (external : data.ExternalChannel) :
    Matrix.mulVec data.inputExposureMatrix input (Incident.mk external.1) =
      input (Incident.mk external) := by
  classical
  simp only [Matrix.mulVec, dotProduct, inputExposureMatrix, ite_mul, one_mul, zero_mul]
  let selected : Incident data.ExternalChannel := Incident.mk external
  calc
    (∑ other, if external.1 = other.channel.1 then input other else 0) =
        if external.1 = selected.channel.1 then input selected else 0 := by
      apply Fintype.sum_eq_single selected
      intro other hOther
      rw [if_neg]
      intro hChannel
      apply hOther
      cases other
      cases external
      simp_all [selected]
    _ = input (Incident.mk external) := by simp [selected]

/-- Raw input exposure vanishes at every stored connected ambient coordinate. -/
lemma inputExposureMatrix_mulVec_connected [Fintype data.ExternalChannel]
    (input : Incident data.ExternalChannel → R) (channel : data.ConnectedChannel) :
    Matrix.mulVec data.inputExposureMatrix input
        (Incident.mk (data.connectedChannelMap channel)) = 0 := by
  classical
  simp only [Matrix.mulVec, dotProduct, inputExposureMatrix, ite_mul, one_mul, zero_mul]
  apply Finset.sum_eq_zero
  intro external _
  rw [if_neg]
  intro hChannel
  exact external.channel.2 ⟨channel, hChannel⟩

/-- Raw external outgoing exposure has a unit entry on its selected ambient coordinate. -/
@[simp]
lemma outputExposureMatrix_entry (external : data.ExternalChannel) :
    data.outputExposureMatrix (Outgoing.mk external.1) (Outgoing.mk external) = 1 := by
  simp [outputExposureMatrix]

/-- Raw external outgoing readout selects its exact ambient coordinate. -/
@[simp]
lemma outputReadoutMatrix_entry (external : data.ExternalChannel) :
    data.outputReadoutMatrix (Outgoing.mk external) (Outgoing.mk external.1) = 1 := by
  simp [outputReadoutMatrix]

/-- Raw output readout acts by selecting the ambient coordinate underlying an external channel. -/
lemma outputReadoutMatrix_mulVec (outgoing : Outgoing data.shape.Channel → R)
    (external : data.ExternalChannel) :
    Matrix.mulVec data.outputReadoutMatrix outgoing (Outgoing.mk external) =
      outgoing (Outgoing.mk external.1) := by
  classical
  simp only [Matrix.mulVec, dotProduct, outputReadoutMatrix, ite_mul, one_mul, zero_mul]
  let selected : Outgoing data.shape.Channel := Outgoing.mk external.1
  calc
    (∑ other, if other.channel = external.1 then outgoing other else 0) =
        if selected.channel = external.1 then outgoing selected else 0 := by
      apply Fintype.sum_eq_single selected
      intro other hOther
      rw [if_neg]
      intro hChannel
      apply hOther
      cases other
      simp_all [selected]
    _ = outgoing (Outgoing.mk external.1) := by simp [selected]

/-- Certified netlist compilation uses the raw connected-channel map on every stored channel. -/
@[simp]
lemma toFlatNetlist_channelEmbedding (evaluate : R →+* ℂ) (h : data.WellFormed)
    (channel : data.ConnectedChannel) :
    (data.toFlatNetlist evaluate h).connections.channelEmbedding channel =
      data.connectedChannelMap channel := by
  rcases channel with ⟨index, mode | mode⟩ <;> rfl

/-- Certified netlist compilation selects exactly the raw connected-channel image. -/
lemma range_toFlatNetlist_channelEmbedding_eq (evaluate : R →+* ℂ)
    (h : data.WellFormed) :
    Set.range (data.toFlatNetlist evaluate h).connections.channelEmbedding =
      Set.range data.connectedChannelMap := by
  ext channel
  constructor
  · rintro ⟨connected, rfl⟩
    exact ⟨connected, (data.toFlatNetlist_channelEmbedding evaluate h connected).symm⟩
  · rintro ⟨connected, rfl⟩
    exact ⟨connected, data.toFlatNetlist_channelEmbedding evaluate h connected⟩

/-- Raw and typed external channels differ only by proofs of the same complement predicate. -/
def externalChannelEquiv (evaluate : R →+* ℂ) (h : data.WellFormed) :
    data.ExternalChannel ≃ (data.toFlatNetlist evaluate h).ExternalChannel :=
  Equiv.subtypeEquivRight fun channel => by
    change channel ∉ Set.range data.connectedChannelMap ↔
      channel ∉ Set.range (data.toFlatNetlist evaluate h).connections.channelEmbedding
    rw [data.range_toFlatNetlist_channelEmbedding_eq evaluate h]
    rfl

/-- External-channel relabeling preserves the underlying aggregate physical channel. -/
@[simp]
lemma externalChannelEquiv_val (evaluate : R →+* ℂ) (h : data.WellFormed)
    (channel : data.ExternalChannel) :
    (data.externalChannelEquiv evaluate h channel).1 = channel.1 := rfl

/-- Raw and compiled aggregate channels have the same physical labels. -/
def channelEquiv (evaluate : R →+* ℂ) (h : data.WellFormed) :
    data.shape.Channel ≃ (data.toFlatNetlist evaluate h).Channel where
  toFun := id
  invFun := id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- Aggregate-channel compilation preserves every physical channel definitionally. -/
@[simp]
lemma channelEquiv_apply (evaluate : R →+* ℂ) (h : data.WellFormed)
    (channel : data.shape.Channel) :
    data.channelEquiv evaluate h channel = channel := rfl

/-- The compiled incident index with the compiler's constructive channel enumeration fixed. -/
@[instance_reducible]
def compiledIncidentFintype (evaluate : R →+* ℂ) (h : data.WellFormed) :
    Fintype (data.toFlatNetlist evaluate h).IncidentIndex := by
  letI : Fintype (data.toFlatNetlist evaluate h).Channel :=
    data.toFlatNetlistChannelFintype evaluate h
  infer_instance

/-- The compiled outgoing index with the compiler's constructive channel enumeration fixed. -/
@[instance_reducible]
def compiledOutgoingFintype (evaluate : R →+* ℂ) (h : data.WellFormed) :
    Fintype (data.toFlatNetlist evaluate h).OutgoingIndex := by
  letI : Fintype (data.toFlatNetlist evaluate h).Channel :=
    data.toFlatNetlistChannelFintype evaluate h
  infer_instance

/-- The compiled external incident index with the exact-complement enumeration fixed. -/
@[instance_reducible]
def compiledExternalIncidentFintype (evaluate : R →+* ℂ)
    (h : data.WellFormed) :
    Fintype (data.toFlatNetlist evaluate h).ExternalIncident := by
  letI : Fintype (data.toFlatNetlist evaluate h).ExternalChannel :=
    data.toFlatNetlistExternalChannelFintype evaluate h
  infer_instance

/-- Evaluate and relabel raw component scattering into the typed aggregate coordinates. -/
def scatteringMatrixInTypedCoordinates (evaluate : R →+* ℂ)
    (h : data.WellFormed) :
    ModeTransform (data.toFlatNetlist evaluate h).IncidentIndex
      (data.toFlatNetlist evaluate h).OutgoingIndex :=
  Matrix.reindex
    (Outgoing.relabelEquiv (data.channelEquiv evaluate h))
    (Incident.relabelEquiv (data.channelEquiv evaluate h))
    (data.scatteringMatrix.map evaluate)

/-- Evaluate and relabel raw unit-gain routing into the typed aggregate coordinates. -/
def routingMatrixInTypedCoordinates (evaluate : R →+* ℂ)
    (h : data.WellFormed) :
    ModeTransform (data.toFlatNetlist evaluate h).OutgoingIndex
      (data.toFlatNetlist evaluate h).IncidentIndex :=
  Matrix.reindex
    (Incident.relabelEquiv (data.channelEquiv evaluate h))
    (Outgoing.relabelEquiv (data.channelEquiv evaluate h))
    (data.routingMatrix.map evaluate)

/-- Evaluate and relabel raw incident exposure into the typed external coordinates. -/
def inputExposureMatrixInTypedCoordinates (evaluate : R →+* ℂ)
    (h : data.WellFormed) :
    ModeTransform (data.toFlatNetlist evaluate h).ExternalIncident
      (data.toFlatNetlist evaluate h).IncidentIndex :=
  Matrix.reindex
    (Incident.relabelEquiv (data.channelEquiv evaluate h))
    (Incident.relabelEquiv (data.externalChannelEquiv evaluate h))
    (data.inputExposureMatrix.map evaluate)

/-- Evaluate and relabel raw outgoing exposure into the typed external coordinates. -/
def outputExposureMatrixInTypedCoordinates (evaluate : R →+* ℂ)
    (h : data.WellFormed) :
    ModeTransform (data.toFlatNetlist evaluate h).ExternalOutgoing
      (data.toFlatNetlist evaluate h).OutgoingIndex :=
  Matrix.reindex
    (Outgoing.relabelEquiv (data.channelEquiv evaluate h))
    (Outgoing.relabelEquiv (data.externalChannelEquiv evaluate h))
    (data.outputExposureMatrix.map evaluate)

/-- Evaluate and relabel raw outgoing readout into the typed external coordinates. -/
def outputReadoutMatrixInTypedCoordinates (evaluate : R →+* ℂ)
    (h : data.WellFormed) :
    ModeTransform (data.toFlatNetlist evaluate h).OutgoingIndex
      (data.toFlatNetlist evaluate h).ExternalOutgoing :=
  Matrix.reindex
    (Outgoing.relabelEquiv (data.externalChannelEquiv evaluate h))
    (Outgoing.relabelEquiv (data.channelEquiv evaluate h))
    (data.outputReadoutMatrix.map evaluate)

/-- Certified netlist compilation retains each raw local-channel embedding. -/
@[simp]
lemma toFlatNetlist_componentChannelEmbedding (evaluate : R →+* ℂ)
    (h : data.WellFormed) (component : data.shape.Component)
    (channel : data.shape.LocalChannel component) :
    (data.toFlatNetlist evaluate h).components.componentChannelEmbedding component channel =
      data.shape.indexedChannelEquiv ⟨component, channel⟩ := rfl

/-- Certified netlist compilation evaluates each stored local scattering entry. -/
@[simp]
lemma toFlatNetlist_scattering_entry (evaluate : R →+* ℂ)
    (h : data.WellFormed) (component : data.shape.Component)
    (output input : data.shape.LocalChannel component) :
    ((data.toFlatNetlist evaluate h).components.scattering component).toModeTransform
        output input = evaluate (data.scattering component output input) := rfl

/-- Certified channel embedding after mating is the raw map after the raw mate table. -/
@[simp]
lemma toFlatNetlist_channelEmbedding_mate (evaluate : R →+* ℂ)
    (h : data.WellFormed) (channel : data.ConnectedChannel) :
    (data.toFlatNetlist evaluate h).connections.channelEmbedding
        ((data.toFlatNetlist evaluate h).connections.mateEquiv channel) =
      data.connectedChannelMap (data.mate channel) := by
  rcases channel with ⟨index, mode | mode⟩ <;> rfl

/-- Certified N4 scattering evaluates one raw diagonal component entry exactly. -/
lemma toFlatNetlist_scatteringTransform_entry_same (evaluate : R →+* ℂ)
    (h : data.WellFormed) (component : data.shape.Component)
    (output input : data.shape.LocalChannel component) :
    (data.toFlatNetlist evaluate h).scatteringTransform
        (Outgoing.mk (data.shape.indexedChannelEquiv ⟨component, output⟩))
      (Incident.mk (data.shape.indexedChannelEquiv ⟨component, input⟩)) =
      evaluate (data.scattering component output input) := by
  simpa only [data.toFlatNetlist_componentChannelEmbedding evaluate h,
    data.toFlatNetlist_scattering_entry evaluate h] using
    (data.toFlatNetlist evaluate h).scatteringTransform_entry_same component output input

/-- Certified N4 scattering has no evaluated entry between distinct raw component blocks. -/
lemma toFlatNetlist_scatteringTransform_entry_of_ne (evaluate : R →+* ℂ)
    (h : data.WellFormed) {first second : data.shape.Component}
    (hComponent : first ≠ second) (output : data.shape.LocalChannel first)
    (input : data.shape.LocalChannel second) :
    (data.toFlatNetlist evaluate h).scatteringTransform
        (Outgoing.mk (data.shape.indexedChannelEquiv ⟨first, output⟩))
      (Incident.mk (data.shape.indexedChannelEquiv ⟨second, input⟩)) = 0 := by
  simpa only [data.toFlatNetlist_componentChannelEmbedding evaluate h] using
    (data.toFlatNetlist evaluate h).scatteringTransform_entry_of_ne
      hComponent output input

/-- Evaluating the raw block-diagonal matrix gives exactly the N4 component transform. -/
private lemma scatteringMatrix_map_eq_scatteringTransform (evaluate : R →+* ℂ)
    (h : data.WellFormed) :
    data.scatteringMatrix.map evaluate =
      (data.toFlatNetlist evaluate h).scatteringTransform := by
  ext output input
  obtain ⟨⟨outputComponent, output⟩, rfl⟩ :=
    (data.shape.indexedChannelEquiv.trans Outgoing.channelEquiv.symm).surjective output
  obtain ⟨⟨inputComponent, input⟩, rfl⟩ :=
    (data.shape.indexedChannelEquiv.trans Incident.channelEquiv.symm).surjective input
  simp only [Equiv.trans_apply, Outgoing.channelEquiv_symm_apply,
    Incident.channelEquiv_symm_apply, Matrix.map_apply]
  by_cases hComponent : outputComponent = inputComponent
  · subst inputComponent
    rw [data.scatteringMatrix_entry_same]
    exact (data.toFlatNetlist_scatteringTransform_entry_same evaluate h
      outputComponent output input).symm
  · rw [data.scatteringMatrix_entry_of_ne hComponent, map_zero]
    exact (data.toFlatNetlist_scatteringTransform_entry_of_ne evaluate h
      hComponent output input).symm

/-- A compiled connected routing column agrees with the raw stored mate entry. -/
lemma toFlatNetlist_routingTransform_connected_column (evaluate : R →+* ℂ)
    (h : data.WellFormed) (incident : data.shape.Channel)
    (channel : data.ConnectedChannel) :
    (data.toFlatNetlist evaluate h).routingTransform (Incident.mk incident)
        (Outgoing.mk (data.connectedChannelMap channel)) =
      if incident = data.connectedChannelMap (data.mate channel) then 1 else 0 := by
  rw [← data.toFlatNetlist_channelEmbedding evaluate h channel]
  have hMate := data.toFlatNetlist_channelEmbedding_mate evaluate h channel
  by_cases hMatched : incident = data.connectedChannelMap (data.mate channel)
  · rw [if_pos hMatched]
    subst incident
    rw [← hMate]
    exact (data.toFlatNetlist evaluate h).routingTransform_entry_mate channel
  · rw [if_neg hMatched]
    apply FlatNetlist.routingTransform_entry_connected_column_of_ne
    exact fun hEqual => hMatched (hEqual.trans hMate)

/-- A raw external outgoing coordinate gives a zero column in compiled routing. -/
lemma toFlatNetlist_routingTransform_of_outgoing_not_mem_range
    (evaluate : R →+* ℂ) (h : data.WellFormed) (outgoing : data.shape.Channel)
    (hOutgoing : outgoing ∉ Set.range data.connectedChannelMap)
    (incident : Incident data.shape.Channel) :
    (data.toFlatNetlist evaluate h).routingTransform incident
        (Outgoing.mk outgoing) = 0 := by
  apply FlatNetlist.routingTransform_entry_of_outgoing_not_mem_range
  intro hMember
  apply hOutgoing
  rw [← data.range_toFlatNetlist_channelEmbedding_eq evaluate h]
  exact hMember

/-- Evaluating raw unit-gain routing gives exactly the N4 partial-routing transform. -/
private lemma routingMatrix_map_eq_routingTransform (evaluate : R →+* ℂ)
    (h : data.WellFormed) :
    data.routingMatrix.map evaluate =
      (data.toFlatNetlist evaluate h).routingTransform := by
  ext incident outgoing
  rcases incident with ⟨incident⟩
  rcases outgoing with ⟨outgoing⟩
  simp only [Matrix.map_apply, routingMatrix]
  by_cases hOutgoing : ∃ channel, data.connectedChannelMap channel = outgoing
  · rcases hOutgoing with ⟨channel, rfl⟩
    by_cases hMate : data.connectedChannelMap (data.mate channel) = incident
    · rw [if_pos ⟨channel, rfl, hMate⟩, map_one]
      rw [← data.toFlatNetlist_channelEmbedding evaluate h channel]
      subst incident
      rw [← data.toFlatNetlist_channelEmbedding_mate evaluate h channel]
      exact ((data.toFlatNetlist evaluate h).routingTransform_entry_mate channel).symm
    · have hNoWitness : ¬ ∃ candidate,
          data.connectedChannelMap candidate = data.connectedChannelMap channel ∧
            data.connectedChannelMap (data.mate candidate) = incident := by
        rintro ⟨candidate, hCandidate, hCandidateMate⟩
        have hEqual : candidate = channel :=
          (data.connectedChannelEmbedding h).injective hCandidate
        exact hMate (hEqual ▸ hCandidateMate)
      rw [if_neg hNoWitness, map_zero]
      rw [← data.toFlatNetlist_channelEmbedding evaluate h channel]
      symm
      apply FlatNetlist.routingTransform_entry_connected_column_of_ne
      intro hEqual
      apply hMate
      exact (hEqual.trans
        (data.toFlatNetlist_channelEmbedding_mate evaluate h channel)).symm
  · have hNoWitness : ¬ ∃ channel,
        data.connectedChannelMap channel = outgoing ∧
          data.connectedChannelMap (data.mate channel) = incident := by
      rintro ⟨channel, hChannel, -⟩
      exact hOutgoing ⟨channel, hChannel⟩
    rw [if_neg hNoWitness, map_zero]
    symm
    apply FlatNetlist.routingTransform_entry_of_outgoing_not_mem_range
    rintro ⟨channel, hChannel⟩
    apply hOutgoing
    exact ⟨channel,
      (data.toFlatNetlist_channelEmbedding evaluate h channel).symm.trans hChannel⟩

/-- Relabeled raw component scattering is exactly the N4 component transform. -/
lemma scatteringMatrixInTypedCoordinates_eq_scatteringTransform (evaluate : R →+* ℂ)
    (h : data.WellFormed) :
    data.scatteringMatrixInTypedCoordinates evaluate h =
      (data.toFlatNetlist evaluate h).scatteringTransform := by
  ext ⟨outgoing⟩ ⟨incident⟩
  change evaluate (data.scatteringMatrix (Outgoing.mk outgoing) (Incident.mk incident)) =
    (data.toFlatNetlist evaluate h).scatteringTransform
      (Outgoing.mk outgoing) (Incident.mk incident)
  exact congrFun (congrFun
    (data.scatteringMatrix_map_eq_scatteringTransform evaluate h) (Outgoing.mk outgoing))
    (Incident.mk incident)

/-- Relabeled raw unit-gain routing is exactly the N4 partial-routing transform. -/
lemma routingMatrixInTypedCoordinates_eq_routingTransform (evaluate : R →+* ℂ)
    (h : data.WellFormed) :
    data.routingMatrixInTypedCoordinates evaluate h =
      (data.toFlatNetlist evaluate h).routingTransform := by
  ext ⟨incident⟩ ⟨outgoing⟩
  change evaluate (data.routingMatrix (Incident.mk incident) (Outgoing.mk outgoing)) =
    (data.toFlatNetlist evaluate h).routingTransform
      (Incident.mk incident) (Outgoing.mk outgoing)
  exact congrFun (congrFun
    (data.routingMatrix_map_eq_routingTransform evaluate h) (Incident.mk incident))
    (Outgoing.mk outgoing)

/-- Relabeled raw incident exposure is exactly the N4 external-input transform. -/
lemma inputExposureMatrixInTypedCoordinates_eq_inputExposure (evaluate : R →+* ℂ)
    (h : data.WellFormed) :
    data.inputExposureMatrixInTypedCoordinates evaluate h =
      (data.toFlatNetlist evaluate h).inputExposure := by
  ext incident external
  obtain ⟨incident, rfl⟩ :=
    (Incident.relabelEquiv (data.channelEquiv evaluate h)).surjective incident
  obtain ⟨external, rfl⟩ :=
    (Incident.relabelEquiv (data.externalChannelEquiv evaluate h)).surjective external
  rcases incident with ⟨incident⟩
  rcases external with ⟨external⟩
  simp only [inputExposureMatrixInTypedCoordinates, Matrix.reindex_apply,
    Matrix.submatrix_apply, Matrix.map_apply, Equiv.symm_apply_apply]
  by_cases hChannel : incident = external.1
  · subst incident
    rw [inputExposureMatrix, if_pos rfl, map_one]
    simpa only [Incident.relabelEquiv_apply, data.channelEquiv_apply evaluate h,
      data.externalChannelEquiv_val evaluate h] using
      ((data.toFlatNetlist evaluate h).inputExposure_entry_external
        (data.externalChannelEquiv evaluate h external)).symm
  · rw [inputExposureMatrix, if_neg hChannel, map_zero]
    have hTyped : data.channelEquiv evaluate h incident ≠
        (data.externalChannelEquiv evaluate h external).1 := by
      intro hEqual
      apply hChannel
      apply (data.channelEquiv evaluate h).injective
      exact hEqual.trans (by rfl)
    simpa only [Incident.relabelEquiv_apply] using
      ((data.toFlatNetlist evaluate h).inputExposure_entry_of_ne
        (data.channelEquiv evaluate h incident)
        (data.externalChannelEquiv evaluate h external) hTyped).symm

/-- Relabeled raw outgoing exposure is exactly the N4 external-output exposure. -/
lemma outputExposureMatrixInTypedCoordinates_eq_outputExposure (evaluate : R →+* ℂ)
    (h : data.WellFormed) :
    data.outputExposureMatrixInTypedCoordinates evaluate h =
      (data.toFlatNetlist evaluate h).outputExposure := by
  ext outgoing external
  obtain ⟨outgoing, rfl⟩ :=
    (Outgoing.relabelEquiv (data.channelEquiv evaluate h)).surjective outgoing
  obtain ⟨external, rfl⟩ :=
    (Outgoing.relabelEquiv (data.externalChannelEquiv evaluate h)).surjective external
  rcases outgoing with ⟨outgoing⟩
  rcases external with ⟨external⟩
  simp only [outputExposureMatrixInTypedCoordinates, Matrix.reindex_apply,
    Matrix.submatrix_apply, Matrix.map_apply, Equiv.symm_apply_apply]
  by_cases hChannel : outgoing = external.1
  · subst outgoing
    rw [outputExposureMatrix, if_pos rfl, map_one]
    simpa only [Outgoing.relabelEquiv_apply, data.channelEquiv_apply evaluate h,
      data.externalChannelEquiv_val evaluate h] using
      ((data.toFlatNetlist evaluate h).outputExposure_entry_external
        (data.externalChannelEquiv evaluate h external)).symm
  · rw [outputExposureMatrix, if_neg hChannel, map_zero]
    have hTyped : data.channelEquiv evaluate h outgoing ≠
        (data.externalChannelEquiv evaluate h external).1 := by
      intro hEqual
      apply hChannel
      apply (data.channelEquiv evaluate h).injective
      exact hEqual.trans (by rfl)
    simpa only [Outgoing.relabelEquiv_apply] using
      ((data.toFlatNetlist evaluate h).outputExposure_entry_of_ne
        (data.channelEquiv evaluate h outgoing)
        (data.externalChannelEquiv evaluate h external) hTyped).symm

/-- Relabeled raw outgoing readout is exactly the N4 external-output readout. -/
lemma outputReadoutMatrixInTypedCoordinates_eq_outputReadout (evaluate : R →+* ℂ)
    (h : data.WellFormed) :
    data.outputReadoutMatrixInTypedCoordinates evaluate h =
      (data.toFlatNetlist evaluate h).outputReadout := by
  ext external outgoing
  obtain ⟨external, rfl⟩ :=
    (Outgoing.relabelEquiv (data.externalChannelEquiv evaluate h)).surjective external
  obtain ⟨outgoing, rfl⟩ :=
    (Outgoing.relabelEquiv (data.channelEquiv evaluate h)).surjective outgoing
  rcases external with ⟨external⟩
  rcases outgoing with ⟨outgoing⟩
  simp only [outputReadoutMatrixInTypedCoordinates, Matrix.reindex_apply,
    Matrix.submatrix_apply, Matrix.map_apply, Equiv.symm_apply_apply]
  by_cases hChannel : outgoing = external.1
  · subst outgoing
    rw [outputReadoutMatrix, if_pos rfl, map_one]
    simpa only [Outgoing.relabelEquiv_apply, data.channelEquiv_apply evaluate h,
      data.externalChannelEquiv_val evaluate h] using
      ((data.toFlatNetlist evaluate h).outputReadout_entry_external
        (data.externalChannelEquiv evaluate h external)).symm
  · rw [outputReadoutMatrix, if_neg hChannel, map_zero]
    have hTyped : data.channelEquiv evaluate h outgoing ≠
        (data.externalChannelEquiv evaluate h external).1 := by
      intro hEqual
      apply hChannel
      apply (data.channelEquiv evaluate h).injective
      exact hEqual.trans (by rfl)
    simpa only [Outgoing.relabelEquiv_apply] using
      ((data.toFlatNetlist evaluate h).outputReadout_entry_of_ne
        (data.externalChannelEquiv evaluate h external)
        (data.channelEquiv evaluate h outgoing) hTyped).symm

end Soundness

section FeedbackSoundness

variable [Ring R]

/-- Evaluate and relabel the raw implicit feedback matrix into typed incident coordinates. -/
def feedbackMatrixInTypedCoordinates (evaluate : R →+* ℂ) (h : data.WellFormed) :
    ModeTransform (data.toFlatNetlist evaluate h).IncidentIndex
      (data.toFlatNetlist evaluate h).IncidentIndex :=
  Matrix.reindex
    (Incident.relabelEquiv (data.channelEquiv evaluate h))
    (Incident.relabelEquiv (data.channelEquiv evaluate h))
    (data.feedbackMatrix.map evaluate)

/-- Evaluated executable feedback is exactly N4's typed operator `1 - C * S`. -/
lemma feedbackMatrixInTypedCoordinates_eq_feedbackOperator (evaluate : R →+* ℂ)
    (h : data.WellFormed) :
    data.feedbackMatrixInTypedCoordinates evaluate h =
      (data.toFlatNetlist evaluate h).feedbackOperator := by
  unfold feedbackMatrixInTypedCoordinates feedbackMatrix FlatNetlist.feedbackOperator
  have hDecEq : (data.toFlatNetlist evaluate h).channelDecidableEq =
      data.toFlatNetlistChannelDecidableEq evaluate h := Subsingleton.elim _ _
  have hConnectedDecEq : (data.toFlatNetlist evaluate h).connectedChannelDecidableEq =
      data.toFlatNetlistConnectedChannelDecidableEq evaluate h := Subsingleton.elim _ _
  rw [hDecEq, hConnectedDecEq]
  let incidentEquiv := Incident.relabelEquiv (data.channelEquiv evaluate h)
  let outgoingEquiv := Outgoing.relabelEquiv (data.channelEquiv evaluate h)
  change Matrix.reindex incidentEquiv incidentEquiv
      ((1 - data.routingMatrix * data.scatteringMatrix).map evaluate) =
    1 - (data.toFlatNetlist evaluate h).routingTransform *
      (data.toFlatNetlist evaluate h).scatteringTransform
  rw [Matrix.map_sub evaluate (fun first second => evaluate.map_sub first second),
    Matrix.map_one evaluate evaluate.map_zero evaluate.map_one, Matrix.map_mul]
  change (Matrix.reindexLinearEquiv ℂ ℂ incidentEquiv incidentEquiv)
      (1 - data.routingMatrix.map evaluate * data.scatteringMatrix.map evaluate) = _
  rw [map_sub, Matrix.reindexLinearEquiv_one, ← Matrix.reindexLinearEquiv_mul ℂ ℂ
    incidentEquiv outgoingEquiv incidentEquiv]
  change 1 - data.routingMatrixInTypedCoordinates evaluate h *
      data.scatteringMatrixInTypedCoordinates evaluate h = _
  rw [data.routingMatrixInTypedCoordinates_eq_routingTransform evaluate h,
    data.scatteringMatrixInTypedCoordinates_eq_scatteringTransform evaluate h]

end FeedbackSoundness

section SemanticSoundness

variable [Semiring R]

/-- The evaluated executable matrices state exactly the three relational N4 network equations.

In particular, this theorem connects raw finite input data to the singular-safe external behavior;
it does not require the implicit feedback equation to have a unique solution.
-/
lemma mem_toFlatNetlist_behavior_iff_matrixEquations (evaluate : R →+* ℂ)
    (h : data.WellFormed)
    (input : ModeAmplitude (data.toFlatNetlist evaluate h).ExternalIncident)
    (output : ModeAmplitude (data.toFlatNetlist evaluate h).ExternalOutgoing) :
    (input, output) ∈ (data.toFlatNetlist evaluate h).behavior ↔
      ∃ incident : ModeAmplitude (data.toFlatNetlist evaluate h).IncidentIndex,
        ∃ outgoing : ModeAmplitude (data.toFlatNetlist evaluate h).OutgoingIndex,
        WithLp.ofLp outgoing = ModeTransform.mulVecWith
            (data.compiledIncidentFintype evaluate h)
            (data.scatteringMatrixInTypedCoordinates evaluate h) (WithLp.ofLp incident) ∧
          WithLp.ofLp incident =
              ModeTransform.mulVecWith (data.compiledOutgoingFintype evaluate h)
                  (data.routingMatrixInTypedCoordinates evaluate h)
                  (WithLp.ofLp outgoing) +
                ModeTransform.mulVecWith
                  (data.compiledExternalIncidentFintype evaluate h)
                  (data.inputExposureMatrixInTypedCoordinates evaluate h)
                  (WithLp.ofLp input) ∧
          WithLp.ofLp output = ModeTransform.mulVecWith
            (data.compiledOutgoingFintype evaluate h)
            (data.outputReadoutMatrixInTypedCoordinates evaluate h) (WithLp.ofLp outgoing) := by
  rw [(data.toFlatNetlist evaluate h).mem_behavior_iff_matrixEquations
    (data.compiledIncidentFintype evaluate h)
    (data.compiledOutgoingFintype evaluate h)
    (data.compiledExternalIncidentFintype evaluate h)
    (data.toFlatNetlistConnectedChannelDecidableEq evaluate h)
    (data.toFlatNetlistChannelDecidableEq evaluate h)]
  rw [data.scatteringMatrixInTypedCoordinates_eq_scatteringTransform evaluate h,
    data.routingMatrixInTypedCoordinates_eq_routingTransform evaluate h,
    data.inputExposureMatrixInTypedCoordinates_eq_inputExposure evaluate h,
    data.outputReadoutMatrixInTypedCoordinates_eq_outputReadout evaluate h]

end SemanticSoundness

end FiniteNetlistData

end Optics
