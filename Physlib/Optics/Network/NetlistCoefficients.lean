/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Mathematics.RationalFunction.Coefficients
public import Physlib.Optics.Network.NetlistMatrices

/-!
# Rational coefficients for certified finite optical netlists

## i. Overview

This file connects the executable coefficient-list layer to the N4C finite-netlist matrix compiler.
`FiniteNetlistData.mapGains` is natural for all five structural matrices and, for a ring
homomorphism, for the implicit feedback matrix `1 - C * S`.

A netlist with executable `RationalCoefficients K` gains has two exact views. `toRatFuncData`
interprets every gain in the field `RatFunc K`. `evaluateAt` evaluates the stored lists directly in
a target field. When every stored denominator is nonzero at the selected point, the intermediate
`regularAtData` lives in the subring on which `RatFunc.eval` is a ring homomorphism. Consequently
evaluation commutes not only with component assembly, but also with the multiplication and
subtraction forming `1 - C * S`.

## ii. Key results

- `FiniteNetlistData.mapGains`: coefficient-only mapping, defined in `NetlistData`.
- `FiniteNetlistData.feedbackMatrix_mapGains`: compiler naturality for `1 - C * S`.
- `FiniteNetlistData.StoredDenominatorsNonzeroAt`: guard for every stored local gain.
- `FiniteNetlistData.toRatFuncData`: exact field-valued symbolic netlist data.
- `FiniteNetlistData.evaluateAt`: direct executable evaluation of every gain.
- `FiniteNetlistData.feedbackMatrix_evalAt`: guarded evaluation commutes with `1 - C * S`.

## iii. Table of contents

- A. Naturality of executable netlist matrices
- B. Rational-function and point-evaluated netlist data
- C. Guarded compilation commutation

## iv. References

The denominator guard concerns component gains only. It neither asserts nor decides invertibility
of the feedback matrix, unique solvability, a determinant condition, or a physical response domain.
The symbolic backend is univariate in one formal variable. A stored canceled factor is still a
required denominator and therefore conservatively excludes its zero from the guarded commutation
theorems until an executable reduction algorithm is supplied.

-/

@[expose] public section

namespace Optics

open Physlib

universe u

namespace FiniteNetlistData

attribute [local instance] channelFintype channelDecidableEq
  connectedChannelFintype connectedChannelDecidableEq

/-!

## A. Naturality of executable netlist matrices

-/

section MatrixNaturality

variable {R S : Type u}
variable (data : FiniteNetlistData R)

/-- Mapping local gains commutes with dependent block-diagonal component assembly. -/
lemma indexedScatteringMatrix_mapGains [Zero R] [Zero S]
    (map : R → S) (hZero : map 0 = 0) :
    (data.mapGains map).indexedScatteringMatrix = data.indexedScatteringMatrix.map map := by
  unfold indexedScatteringMatrix
  exact (Matrix.blockDiagonal'_map data.scattering map hZero).symm

/-- Mapping local gains commutes with aggregate scattering-matrix assembly. -/
lemma scatteringMatrix_mapGains [Zero R] [Zero S]
    (map : R → S) (hZero : map 0 = 0) :
    (data.mapGains map).scatteringMatrix = data.scatteringMatrix.map map := by
  unfold scatteringMatrix
  rw [data.indexedScatteringMatrix_mapGains map hZero]
  rfl

/-- Changing local gains preserves the raw connected-channel map. -/
@[simp]
lemma connectedChannelMap_mapGains (map : R → S)
    (channel : (data.mapGains map).ConnectedChannel) :
    (data.mapGains map).connectedChannelMap channel =
      data.connectedChannelMap channel := by
  rcases channel with ⟨index, mode | mode⟩ <;> rfl

/-- Changing local gains preserves the raw connected-channel mate involution. -/
@[simp]
lemma mate_mapGains (map : R → S) (channel : (data.mapGains map).ConnectedChannel) :
    (data.mapGains map).mate channel = data.mate channel := by
  rcases channel with ⟨index, mode | mode⟩ <;> rfl

/-- The canonical coefficient-independent equivalence of connected-channel indices. -/
def connectedChannelEquivMapGains (map : R → S) :
    data.ConnectedChannel ≃ (data.mapGains map).ConnectedChannel where
  toFun
    | ⟨index, Sum.inl mode⟩ => ⟨index, Sum.inl mode⟩
    | ⟨index, Sum.inr mode⟩ => ⟨index, Sum.inr mode⟩
  invFun
    | ⟨index, Sum.inl mode⟩ => ⟨index, Sum.inl mode⟩
    | ⟨index, Sum.inr mode⟩ => ⟨index, Sum.inr mode⟩
  left_inv := by rintro ⟨index, mode | mode⟩ <;> rfl
  right_inv := by rintro ⟨index, mode | mode⟩ <;> rfl

/-- Mapping gains preserves the ambient channel selected by a connected-channel index. -/
lemma connectedChannelMap_connectedChannelEquivMapGains (map : R → S)
    (channel : data.ConnectedChannel) :
    (data.mapGains map).connectedChannelMap
        (data.connectedChannelEquivMapGains map channel) =
      data.connectedChannelMap channel := by
  rcases channel with ⟨index, mode | mode⟩ <;> rfl

/-- Mapping gains conjugates the connected-channel mate map by the canonical equivalence. -/
lemma mate_connectedChannelEquivMapGains (map : R → S)
    (channel : data.ConnectedChannel) :
    (data.mapGains map).mate (data.connectedChannelEquivMapGains map channel) =
      data.connectedChannelEquivMapGains map (data.mate channel) := by
  rcases channel with ⟨index, mode | mode⟩ <;> rfl

/-- Mapping gains preserves the exact set of connected ambient channels. -/
lemma range_connectedChannelMap_mapGains (map : R → S) :
    Set.range (data.mapGains map).connectedChannelMap =
      Set.range data.connectedChannelMap := by
  ext ambient
  constructor
  · rintro ⟨channel, hChannel⟩
    obtain ⟨oldChannel, rfl⟩ :=
      (data.connectedChannelEquivMapGains map).surjective channel
    exact ⟨oldChannel,
      (data.connectedChannelMap_connectedChannelEquivMapGains map oldChannel).symm.trans
        hChannel⟩
  · rintro ⟨channel, hChannel⟩
    exact ⟨data.connectedChannelEquivMapGains map channel,
      (data.connectedChannelMap_connectedChannelEquivMapGains map channel).trans hChannel⟩

/-- The canonical external-channel equivalence after changing only local gains. -/
def externalChannelEquivMapGains (map : R → S) :
    data.ExternalChannel ≃ (data.mapGains map).ExternalChannel :=
  Equiv.subtypeEquivRight fun ambient => by
    change ambient ∉ Set.range data.connectedChannelMap ↔
      ambient ∉ Set.range (data.mapGains map).connectedChannelMap
    rw [data.range_connectedChannelMap_mapGains map]

/-- Gain mapping changes only an external channel's complement proof. -/
@[simp]
lemma externalChannelEquivMapGains_val (map : R → S)
    (channel : data.ExternalChannel) :
    (data.externalChannelEquivMapGains map channel).1 = channel.1 := rfl

/-- Inverse gain-mapping transport also preserves the underlying ambient channel. -/
@[simp]
lemma externalChannelEquivMapGains_symm_val (map : R → S)
    (channel : (data.mapGains map).ExternalChannel) :
    ((data.externalChannelEquivMapGains map).symm channel).1 = channel.1 := rfl

/-- A zero-and-one-preserving map commutes with executable mate routing. -/
lemma routingMatrix_mapGains [Zero R] [One R] [Zero S] [One S]
    (map : R → S) (hZero : map 0 = 0) (hOne : map 1 = 1) :
    (data.mapGains map).routingMatrix = data.routingMatrix.map map := by
  classical
  let lhs : Matrix (Incident data.shape.Channel) (Outgoing data.shape.Channel) S :=
    (data.mapGains map).routingMatrix
  let rhs : Matrix (Incident data.shape.Channel) (Outgoing data.shape.Channel) S :=
    data.routingMatrix.map map
  suffices hStable : lhs = rhs by exact hStable
  ext incident outgoing
  let mappedRouted : Prop :=
    ∃ channel : (data.mapGains map).ConnectedChannel,
      (data.mapGains map).connectedChannelMap channel = outgoing.channel ∧
        (data.mapGains map).connectedChannelMap ((data.mapGains map).mate channel) =
          incident.channel
  let routed : Prop := ∃ channel : data.ConnectedChannel,
    data.connectedChannelMap channel = outgoing.channel ∧
      data.connectedChannelMap (data.mate channel) = incident.channel
  change lhs incident outgoing = rhs incident outgoing
  simp only [lhs, rhs, routingMatrix, Matrix.map_apply]
  have hRoutedIff : mappedRouted ↔ routed := by
    constructor
    · rintro ⟨channel, hOutgoing, hIncident⟩
      obtain ⟨oldChannel, rfl⟩ :=
        (data.connectedChannelEquivMapGains map).surjective channel
      refine ⟨oldChannel, ?_, ?_⟩
      · simpa only [connectedChannelMap_connectedChannelEquivMapGains] using hOutgoing
      · simpa only [mate_connectedChannelEquivMapGains,
          connectedChannelMap_connectedChannelEquivMapGains] using hIncident
    · rintro ⟨channel, hOutgoing, hIncident⟩
      refine ⟨data.connectedChannelEquivMapGains map channel, ?_, ?_⟩
      · simpa only [connectedChannelMap_connectedChannelEquivMapGains] using hOutgoing
      · simpa only [mate_connectedChannelEquivMapGains,
          connectedChannelMap_connectedChannelEquivMapGains] using hIncident
  by_cases hRouted : routed
  · rw [if_pos (hRoutedIff.mpr hRouted), if_pos hRouted, hOne]
  · rw [if_neg (fun hMapped => hRouted (hRoutedIff.mp hMapped)),
      if_neg hRouted, hZero]

/-- A zero-and-one-preserving map commutes with external incident exposure. -/
lemma inputExposureMatrix_mapGains [Zero R] [One R] [Zero S] [One S]
    (map : R → S) (hZero : map 0 = 0) (hOne : map 1 = 1) :
    (data.mapGains map).inputExposureMatrix =
      Matrix.reindex (Equiv.refl _)
        (Incident.relabelEquiv (data.externalChannelEquivMapGains map))
        (data.inputExposureMatrix.map map) := by
  ext incident external
  rcases incident with ⟨incident⟩
  rcases external with ⟨external⟩
  simp only [inputExposureMatrix, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.map_apply, Equiv.refl_symm, Equiv.refl_apply]
  have hExternal :
      (((Incident.relabelEquiv (data.externalChannelEquivMapGains map)).symm
        (Incident.mk external)).channel).1 = external.1 := by
    change ((data.externalChannelEquivMapGains map).symm external).1 = external.1
    exact data.externalChannelEquivMapGains_symm_val map external
  rw [hExternal]
  by_cases hChannel : incident = external.1
  · rw [if_pos hChannel, if_pos hChannel, hOne]
  · rw [if_neg hChannel, if_neg hChannel, hZero]

/-- A zero-and-one-preserving map commutes with external outgoing exposure. -/
lemma outputExposureMatrix_mapGains [Zero R] [One R] [Zero S] [One S]
    (map : R → S) (hZero : map 0 = 0) (hOne : map 1 = 1) :
    (data.mapGains map).outputExposureMatrix =
      Matrix.reindex (Equiv.refl _)
        (Outgoing.relabelEquiv (data.externalChannelEquivMapGains map))
        (data.outputExposureMatrix.map map) := by
  ext outgoing external
  rcases outgoing with ⟨outgoing⟩
  rcases external with ⟨external⟩
  simp only [outputExposureMatrix, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.map_apply, Equiv.refl_symm, Equiv.refl_apply]
  have hExternal :
      (((Outgoing.relabelEquiv (data.externalChannelEquivMapGains map)).symm
        (Outgoing.mk external)).channel).1 = external.1 := by
    change ((data.externalChannelEquivMapGains map).symm external).1 = external.1
    exact data.externalChannelEquivMapGains_symm_val map external
  rw [hExternal]
  by_cases hChannel : outgoing = external.1
  · rw [if_pos hChannel, if_pos hChannel, hOne]
  · rw [if_neg hChannel, if_neg hChannel, hZero]

/-- A zero-and-one-preserving map commutes with external outgoing readout. -/
lemma outputReadoutMatrix_mapGains [Zero R] [One R] [Zero S] [One S]
    (map : R → S) (hZero : map 0 = 0) (hOne : map 1 = 1) :
    (data.mapGains map).outputReadoutMatrix =
      Matrix.reindex (Outgoing.relabelEquiv (data.externalChannelEquivMapGains map))
        (Equiv.refl _) (data.outputReadoutMatrix.map map) := by
  ext external outgoing
  rcases external with ⟨external⟩
  rcases outgoing with ⟨outgoing⟩
  simp only [outputReadoutMatrix, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.map_apply, Equiv.refl_symm, Equiv.refl_apply]
  have hExternal :
      (((Outgoing.relabelEquiv (data.externalChannelEquivMapGains map)).symm
        (Outgoing.mk external)).channel).1 = external.1 := by
    change ((data.externalChannelEquivMapGains map).symm external).1 = external.1
    exact data.externalChannelEquivMapGains_symm_val map external
  rw [hExternal]
  by_cases hChannel : outgoing = external.1
  · rw [if_pos hChannel, if_pos hChannel, hOne]
  · rw [if_neg hChannel, if_neg hChannel, hZero]

end MatrixNaturality

section FeedbackNaturality

variable {R S : Type u} [Ring R] [Ring S]
variable (data : FiniteNetlistData R)

/-- A ring homomorphism commutes with formation of the implicit matrix `1 - C * S`. -/
lemma feedbackMatrix_mapGains (map : R →+* S) :
    (data.mapGains map).feedbackMatrix = data.feedbackMatrix.map map := by
  classical
  unfold feedbackMatrix
  rw [Matrix.map_sub map map.map_sub, Matrix.map_one map map.map_zero map.map_one,
    Matrix.map_mul, ← data.routingMatrix_mapGains map map.map_zero map.map_one,
    ← data.scatteringMatrix_mapGains map map.map_zero]

end FeedbackNaturality

/-!

## B. Rational-function and point-evaluated netlist data

-/

section RationalData

variable {K L : Type u} [Field K] [Field L] [DecidableEq K]
variable (data : FiniteNetlistData (RationalCoefficients K))

/-- Every stored component-gain denominator is nonzero at the selected point. -/
def StoredDenominatorsNonzeroAt (f : K →+* L) (point : L) : Prop :=
  ∀ component output input,
    (data.scattering component output input).StoredDenominatorNonzeroAt f point

/-- The finite stored-denominator guard is constructively decidable over a decidable target. -/
instance [DecidableEq L] (f : K →+* L) (point : L) :
    Decidable (data.StoredDenominatorsNonzeroAt f point) := by
  unfold StoredDenominatorsNonzeroAt
  letI localChannelFintype (component : data.shape.Component) :
      Fintype (data.shape.LocalChannel component) := by
    change Fintype (Σ port : Fin (data.shape.portCount component),
      Fin (data.shape.modeCount component port))
    infer_instance
  letI decideInputs (component : data.shape.Component)
      (output : data.shape.LocalChannel component) :
      Decidable (∀ input,
        (data.scattering component output input).StoredDenominatorNonzeroAt f point) :=
    Fintype.decidableForallFintype
  letI decideOutputs (component : data.shape.Component) :
      Decidable (∀ output input,
        (data.scattering component output input).StoredDenominatorNonzeroAt f point) :=
    Fintype.decidableForallFintype
  exact Fintype.decidableForallFintype

/-- Interpret every executable gain in the univariate rational-function field. -/
@[reducible]
noncomputable def toRatFuncData : FiniteNetlistData (RatFunc K) :=
  data.mapGains RationalCoefficients.toRatFunc

/-- Evaluate every stored numerator and denominator by total field division at one point. -/
@[reducible]
def evaluateAt (f : K →+* L) (point : L) : FiniteNetlistData L :=
  data.mapGains fun gain => gain.evalAt f point

/-- Lift every guarded gain to the subring of rational functions regular at the point. -/
@[reducible]
noncomputable def regularAtData (f : K →+* L) (point : L)
    (h : data.StoredDenominatorsNonzeroAt f point) :
    FiniteNetlistData (RationalFunction.regularAt f point) where
  shape := data.shape
  scattering := fun component output input =>
    (data.scattering component output input).toRegularAt f point
      (h component output input)
  connections := data.connections

@[simp]
lemma regularAtData_scattering (f : K →+* L) (point : L)
    (h : data.StoredDenominatorsNonzeroAt f point)
    (component : data.shape.Component) (output input : data.shape.LocalChannel component) :
    (data.regularAtData f point h).scattering component output input =
      (data.scattering component output input).toRegularAt f point
        (h component output input) := rfl

/-- Forgetting regularity from the guarded data recovers the exact `RatFunc` interpretation. -/
lemma regularAtData_map_subtype (f : K →+* L) (point : L)
    (h : data.StoredDenominatorsNonzeroAt f point) :
    (data.regularAtData f point h).mapGains
        (RationalFunction.regularAt f point).subtype =
      data.toRatFuncData := by
  cases data
  rfl

/-- Evaluating the guarded subring data recovers direct executable list evaluation. -/
lemma regularAtData_map_evalRegularAt (f : K →+* L) (point : L)
    (h : data.StoredDenominatorsNonzeroAt f point) :
    (data.regularAtData f point h).mapGains
        (RationalFunction.evalRegularAt f point) =
      data.evaluateAt f point := by
  cases data with
  | mk shape scattering connections =>
      simp only [regularAtData, evaluateAt, mapGains]
      congr 1
      funext component output input
      exact RationalCoefficients.evalRegularAt_toRegularAt f point
        (scattering component output input) (h component output input)

/-- Canonical external-channel transport from symbolic data to point-evaluated data. -/
noncomputable def externalChannelEquivEvaluation (f : K →+* L) (point : L) :
    data.toRatFuncData.ExternalChannel ≃ (data.evaluateAt f point).ExternalChannel :=
  (data.externalChannelEquivMapGains RationalCoefficients.toRatFunc).symm.trans
    (data.externalChannelEquivMapGains fun gain => gain.evalAt f point)

/-- Symbolic-to-evaluated external transport preserves the underlying ambient channel. -/
@[simp]
lemma externalChannelEquivEvaluation_val (f : K →+* L) (point : L)
    (channel : data.toRatFuncData.ExternalChannel) :
    (data.externalChannelEquivEvaluation f point channel).1 = channel.1 := rfl

/-- Inverse evaluation transport preserves the underlying ambient channel. -/
@[simp]
lemma externalChannelEquivEvaluation_symm_val (f : K →+* L) (point : L)
    (channel : (data.evaluateAt f point).ExternalChannel) :
    ((data.externalChannelEquivEvaluation f point).symm channel).1 = channel.1 := rfl

end RationalData

/-!

## C. Guarded compilation commutation

-/

section GuardedCommutation

variable {K L : Type u} [Field K] [Field L] [DecidableEq K]
variable (data : FiniteNetlistData (RationalCoefficients K))
variable (f : K →+* L) (point : L)

/-- The component denominator guard extends to every entry of the assembled scattering matrix. -/
lemma scatteringMatrix_storedDenominatorNonzeroAt
    (h : data.StoredDenominatorsNonzeroAt f point)
    (output : Outgoing data.shape.Channel) (input : Incident data.shape.Channel) :
    (data.scatteringMatrix output input).StoredDenominatorNonzeroAt f point := by
  obtain ⟨⟨outputComponent, output⟩, rfl⟩ :=
    (data.shape.indexedChannelEquiv.trans Outgoing.channelEquiv.symm).surjective output
  obtain ⟨⟨inputComponent, input⟩, rfl⟩ :=
    (data.shape.indexedChannelEquiv.trans Incident.channelEquiv.symm).surjective input
  simp only [Equiv.trans_apply, Outgoing.channelEquiv_symm_apply,
    Incident.channelEquiv_symm_apply]
  by_cases hComponent : outputComponent = inputComponent
  · subst inputComponent
    rw [data.scatteringMatrix_entry_same]
    exact h outputComponent output input
  · rw [data.scatteringMatrix_entry_of_ne hComponent]
    exact RationalCoefficients.storedDenominatorNonzeroAt_zero f point

/-- Guarded evaluation commutes with block-diagonal scattering assembly. -/
lemma scatteringMatrix_evalAt (h : data.StoredDenominatorsNonzeroAt f point) :
    data.toRatFuncData.scatteringMatrix.map (RatFunc.eval f point) =
      (data.evaluateAt f point).scatteringMatrix := by
  unfold toRatFuncData evaluateAt
  rw [data.scatteringMatrix_mapGains _ RationalCoefficients.toRatFunc_zero,
    data.scatteringMatrix_mapGains _ (RationalCoefficients.evalAt_zero f point)]
  ext output input
  exact RationalCoefficients.ratFunc_eval_eq_evalAt f point _
    (data.scatteringMatrix_storedDenominatorNonzeroAt f point h output input)

/-- Rational-function evaluation commutes with unit-gain mate routing without a denominator
guard. -/
lemma routingMatrix_evalAt :
    data.toRatFuncData.routingMatrix.map (RatFunc.eval f point) =
      (data.evaluateAt f point).routingMatrix := by
  unfold toRatFuncData evaluateAt
  rw [data.routingMatrix_mapGains _ RationalCoefficients.toRatFunc_zero
      RationalCoefficients.toRatFunc_one,
    data.routingMatrix_mapGains _ (RationalCoefficients.evalAt_zero f point)
      (RationalCoefficients.evalAt_one f point)]
  ext incident outgoing
  simp only [Matrix.map_apply, routingMatrix]
  split <;> simp

/-- Rational-function evaluation commutes with external incident exposure. -/
lemma inputExposureMatrix_evalAt :
    (data.evaluateAt f point).inputExposureMatrix =
      Matrix.reindex (Equiv.refl _)
        (Incident.relabelEquiv (data.externalChannelEquivEvaluation f point))
        (data.toRatFuncData.inputExposureMatrix.map (RatFunc.eval f point)) := by
  ext incident external
  rcases incident with ⟨incident⟩
  rcases external with ⟨external⟩
  simp only [inputExposureMatrix, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.map_apply, Equiv.refl_symm, Equiv.refl_apply]
  have hExternal :
      (((Incident.relabelEquiv (data.externalChannelEquivEvaluation f point)).symm
        (Incident.mk external)).channel).1 = external.1 := by
    change ((data.externalChannelEquivEvaluation f point).symm external).1 = external.1
    exact data.externalChannelEquivEvaluation_symm_val f point external
  rw [hExternal]
  by_cases hChannel : incident = external.1 <;> simp [hChannel]

/-- Rational-function evaluation commutes with external outgoing exposure. -/
lemma outputExposureMatrix_evalAt :
    (data.evaluateAt f point).outputExposureMatrix =
      Matrix.reindex (Equiv.refl _)
        (Outgoing.relabelEquiv (data.externalChannelEquivEvaluation f point))
        (data.toRatFuncData.outputExposureMatrix.map (RatFunc.eval f point)) := by
  ext outgoing external
  rcases outgoing with ⟨outgoing⟩
  rcases external with ⟨external⟩
  simp only [outputExposureMatrix, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.map_apply, Equiv.refl_symm, Equiv.refl_apply]
  have hExternal :
      (((Outgoing.relabelEquiv (data.externalChannelEquivEvaluation f point)).symm
        (Outgoing.mk external)).channel).1 = external.1 := by
    change ((data.externalChannelEquivEvaluation f point).symm external).1 = external.1
    exact data.externalChannelEquivEvaluation_symm_val f point external
  rw [hExternal]
  by_cases hChannel : outgoing = external.1 <;> simp [hChannel]

/-- Rational-function evaluation commutes with external outgoing readout. -/
lemma outputReadoutMatrix_evalAt :
    (data.evaluateAt f point).outputReadoutMatrix =
      Matrix.reindex (Outgoing.relabelEquiv (data.externalChannelEquivEvaluation f point))
        (Equiv.refl _)
        (data.toRatFuncData.outputReadoutMatrix.map (RatFunc.eval f point)) := by
  ext external outgoing
  rcases external with ⟨external⟩
  rcases outgoing with ⟨outgoing⟩
  simp only [outputReadoutMatrix, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.map_apply, Equiv.refl_symm, Equiv.refl_apply]
  have hExternal :
      (((Outgoing.relabelEquiv (data.externalChannelEquivEvaluation f point)).symm
        (Outgoing.mk external)).channel).1 = external.1 := by
    change ((data.externalChannelEquivEvaluation f point).symm external).1 = external.1
    exact data.externalChannelEquivEvaluation_symm_val f point external
  rw [hExternal]
  by_cases hChannel : outgoing = external.1 <;> simp [hChannel]

private lemma regularAtData_scatteringMatrix_map_subtype
    (h : data.StoredDenominatorsNonzeroAt f point) :
    ((data.regularAtData f point h).scatteringMatrix.map
        (RationalFunction.regularAt f point).subtype :
      Matrix (Outgoing data.shape.Channel) (Incident data.shape.Channel) (RatFunc K)) =
      data.toRatFuncData.scatteringMatrix := by
  ext output input
  obtain ⟨⟨outputComponent, output⟩, rfl⟩ :=
    (data.shape.indexedChannelEquiv.trans Outgoing.channelEquiv.symm).surjective output
  obtain ⟨⟨inputComponent, input⟩, rfl⟩ :=
    (data.shape.indexedChannelEquiv.trans Incident.channelEquiv.symm).surjective input
  simp only [Equiv.trans_apply, Outgoing.channelEquiv_symm_apply,
    Incident.channelEquiv_symm_apply, Matrix.map_apply]
  by_cases hComponent : outputComponent = inputComponent
  · subst inputComponent
    rw [(data.regularAtData f point h).scatteringMatrix_entry_same,
      data.toRatFuncData.scatteringMatrix_entry_same]
    rfl
  · rw [(data.regularAtData f point h).scatteringMatrix_entry_of_ne hComponent,
      data.toRatFuncData.scatteringMatrix_entry_of_ne hComponent, map_zero]

private lemma regularAtData_scatteringMatrix_map_evalRegularAt
    (h : data.StoredDenominatorsNonzeroAt f point) :
    ((data.regularAtData f point h).scatteringMatrix.map
        (RationalFunction.evalRegularAt f point) :
      Matrix (Outgoing data.shape.Channel) (Incident data.shape.Channel) L) =
      (data.evaluateAt f point).scatteringMatrix := by
  ext output input
  obtain ⟨⟨outputComponent, output⟩, rfl⟩ :=
    (data.shape.indexedChannelEquiv.trans Outgoing.channelEquiv.symm).surjective output
  obtain ⟨⟨inputComponent, input⟩, rfl⟩ :=
    (data.shape.indexedChannelEquiv.trans Incident.channelEquiv.symm).surjective input
  simp only [Equiv.trans_apply, Outgoing.channelEquiv_symm_apply,
    Incident.channelEquiv_symm_apply, Matrix.map_apply]
  by_cases hComponent : outputComponent = inputComponent
  · subst inputComponent
    rw [(data.regularAtData f point h).scatteringMatrix_entry_same,
      (data.evaluateAt f point).scatteringMatrix_entry_same]
    exact RationalCoefficients.evalRegularAt_toRegularAt f point
      (data.scattering outputComponent output input) (h outputComponent output input)
  · rw [(data.regularAtData f point h).scatteringMatrix_entry_of_ne hComponent,
      (data.evaluateAt f point).scatteringMatrix_entry_of_ne hComponent, map_zero]

/-- The coefficient-independent mate-routing matrix valued in the regular-at-point subring. -/
private noncomputable def regularRoutingMatrix :
    Matrix (Incident data.shape.Channel) (Outgoing data.shape.Channel)
      (RationalFunction.regularAt f point) :=
  fun incident outgoing =>
    if ∃ channel : data.ConnectedChannel,
        data.connectedChannelMap channel = outgoing.channel ∧
          data.connectedChannelMap (data.mate channel) = incident.channel
    then 1 else 0

private lemma regularRoutingMatrix_map_subtype :
    (data.regularRoutingMatrix f point).map
        (RationalFunction.regularAt f point).subtype =
      data.toRatFuncData.routingMatrix := by
  unfold toRatFuncData
  rw [data.routingMatrix_mapGains _ RationalCoefficients.toRatFunc_zero
    RationalCoefficients.toRatFunc_one]
  ext incident outgoing
  simp only [regularRoutingMatrix, Matrix.map_apply, routingMatrix]
  split <;> simp

private lemma regularRoutingMatrix_map_evalRegularAt :
    (data.regularRoutingMatrix f point).map
        (RationalFunction.evalRegularAt f point) =
      (data.evaluateAt f point).routingMatrix := by
  unfold evaluateAt
  rw [data.routingMatrix_mapGains _ (RationalCoefficients.evalAt_zero f point)
    (RationalCoefficients.evalAt_one f point)]
  ext incident outgoing
  simp only [regularRoutingMatrix, Matrix.map_apply, routingMatrix]
  split <;> simp

/-- Guarded rational-function evaluation commutes with the implicit matrix
`1 - C * S`.

This theorem has no inverse, determinant, or unique-solvability hypothesis. In particular, a
feedback matrix may remain singular at every guarded point.
-/
lemma feedbackMatrix_evalAt (h : data.StoredDenominatorsNonzeroAt f point) :
    data.toRatFuncData.feedbackMatrix.map (RatFunc.eval f point) =
      (data.evaluateAt f point).feedbackMatrix := by
  let regularFeedback :
      Matrix (Incident data.shape.Channel) (Incident data.shape.Channel)
        (RationalFunction.regularAt f point) :=
    1 - data.regularRoutingMatrix f point *
      (data.regularAtData f point h).scatteringMatrix
  have hSymbolic :
      (regularFeedback.map (RationalFunction.regularAt f point).subtype :
        Matrix (Incident data.shape.Channel) (Incident data.shape.Channel) (RatFunc K)) =
      data.toRatFuncData.feedbackMatrix := by
    simp only [regularFeedback]
    unfold feedbackMatrix
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.map_mul, data.regularRoutingMatrix_map_subtype f point,
      data.regularAtData_scatteringMatrix_map_subtype f point h]
  have hEvaluated :
      (regularFeedback.map (RationalFunction.evalRegularAt f point) :
        Matrix (Incident data.shape.Channel) (Incident data.shape.Channel) L) =
      (data.evaluateAt f point).feedbackMatrix := by
    simp only [regularFeedback]
    unfold feedbackMatrix
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.map_mul, data.regularRoutingMatrix_map_evalRegularAt f point,
      data.regularAtData_scatteringMatrix_map_evalRegularAt f point h]
  change
    (data.toRatFuncData.feedbackMatrix.map (RatFunc.eval f point) :
      Matrix (Incident data.shape.Channel) (Incident data.shape.Channel) L) =
      (data.evaluateAt f point).feedbackMatrix
  rw [← hSymbolic, ← hEvaluated]
  ext incident input
  rfl

end GuardedCommutation

end FiniteNetlistData

end Optics
