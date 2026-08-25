/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.FlatNetlist

/-!
# Regression tests for singular-safe flat scattering netlists

## i. Overview

Two two-port components share one internal connection. Their remaining ports form a two-channel
external boundary. Exact coordinate laws pin component scattering, mate routing, external
injection, and output readout in one connected construction.

The component matrices are individually invertible, but the closed feedback equation is singular.
At zero external input the netlist admits a one-parameter family of complete states and distinct
external outputs. A second external input has no solution. These witnesses ensure that flat-netlist
semantics remains a linear relation and does not silently invert the feedback operator.

## ii. Scope

The coefficients are algebraic sentinels. Component invertibility is used only to show that it is
not sufficient for network well-posedness. No passivity, losslessness, reciprocity, causality,
electromagnetic normalization, or executable solver is claimed.

## iii. Table of contents

- A. A two-component shared-link netlist
- B. Exact component and boundary equations
- C. A singular family of solutions
- D. An external input with no solution

-/

@[expose] public section

namespace Optics

noncomputable section

/-!

## A. A two-component shared-link netlist

-/

/-- Each regression component has one external port and one internal-link port, each carrying one
mode. `false` names the external port and `true` names the link port. -/
abbrev flatNetlistRegressionPortFamily : PortModeFamily where
  Port := Bool
  Mode := fun _ => Unit

/-- Boolean component and port labels use the same classical equality witness as assembled
scattering. -/
local instance flatNetlistRegressionBoolDecidableEq : DecidableEq Bool :=
  Classical.decEq _

/-- The two singular-fixture component laws. In local `[external, link]` order they are
`[[0, 1], [1, 1]]` and `[[0, 2], [1, 1]]`. -/
def flatNetlistRegressionScattering
    (component : Bool) : ScatteringMatrix flatNetlistRegressionPortFamily.Channel where
  toModeTransform := fun output input =>
    match component, output.1, input.1 with
    | false, false, false => 0
    | false, false, true => 1
    | false, true, false => 1
    | false, true, true => 1
    | true, false, false => 0
    | true, false, true => 2
    | true, true, false => 1
    | true, true, true => 1

/-- The two component instances before wiring. -/
abbrev flatNetlistRegressionComponents : ScatteringComponentFamily where
  Component := Bool
  portFamily := fun _ => flatNetlistRegressionPortFamily
  scattering := flatNetlistRegressionScattering

/-- Every local component-channel family in the regression is finite. -/
local instance flatNetlistRegressionLocalChannelFintype (component : Bool) :
    Fintype (flatNetlistRegressionComponents.portFamily component).Channel := by
  change Fintype (Σ _ : Bool, Unit)
  infer_instance

/-- Every local component-channel family in the regression has decidable equality. -/
local instance flatNetlistRegressionLocalChannelDecidableEq (component : Bool) :
    DecidableEq (flatNetlistRegressionComponents.portFamily component).Channel := by
  classical
  exact Classical.decEq _

/-- Explicit inverses of the two local component matrices. -/
def flatNetlistRegressionInverseScattering (component : Bool) :
    ModeTransform flatNetlistRegressionPortFamily.Channel
      flatNetlistRegressionPortFamily.Channel := fun output input =>
  match component, output.1, input.1 with
  | false, false, false => -1
  | false, false, true => 1
  | false, true, false => 1
  | false, true, true => 0
  | true, false, false => -(1 / 2)
  | true, false, true => 1
  | true, true, false => 1 / 2
  | true, true, true => 0

/-- Each local component matrix has the displayed two-sided inverse, even though the assembled
feedback loop below is singular. -/
lemma flatNetlistRegression_scattering_twoSidedInverse (component : Bool) :
    (flatNetlistRegressionScattering component).toModeTransform *
          flatNetlistRegressionInverseScattering component = 1 ∧
      flatNetlistRegressionInverseScattering component *
          (flatNetlistRegressionScattering component).toModeTransform = 1 := by
  constructor
  · ext output input
    rw [Matrix.mul_apply]
    rcases output with ⟨outputPort, outputMode⟩
    rcases input with ⟨inputPort, inputMode⟩
    cases component <;> cases outputPort <;> cases outputMode <;>
      cases inputPort <;> cases inputMode
    all_goals
      simp [Fintype.sum_sigma,
        flatNetlistRegressionScattering, flatNetlistRegressionInverseScattering]
  · ext output input
    rw [Matrix.mul_apply]
    rcases output with ⟨outputPort, outputMode⟩
    rcases input with ⟨inputPort, inputMode⟩
    cases component <;> cases outputPort <;> cases outputMode <;>
      cases inputPort <;> cases inputMode
    all_goals
      simp [Fintype.sum_sigma,
        flatNetlistRegressionScattering, flatNetlistRegressionInverseScattering]

/-- Aggregate channels are finite through the canonical component-channel reassociation. -/
local instance flatNetlistRegressionAggregateChannelFintype :
  Fintype flatNetlistRegressionComponents.aggregatePortModeFamily.Channel :=
  Fintype.ofEquiv flatNetlistRegressionComponents.IndexedChannel
    flatNetlistRegressionComponents.channelEquiv

/-- Aggregate channels have decidable equality. -/
local instance flatNetlistRegressionAggregateChannelDecidableEq :
    DecidableEq flatNetlistRegressionComponents.aggregatePortModeFamily.Channel :=
  Classical.decEq _

/-- The external port of the first component. -/
abbrev flatNetlistRegressionPortAExternal :
    flatNetlistRegressionComponents.aggregatePortModeFamily.Port := ⟨false, false⟩

/-- The link port of the first component. -/
abbrev flatNetlistRegressionPortALink :
    flatNetlistRegressionComponents.aggregatePortModeFamily.Port := ⟨false, true⟩

/-- The external port of the second component. -/
abbrev flatNetlistRegressionPortBExternal :
    flatNetlistRegressionComponents.aggregatePortModeFamily.Port := ⟨true, false⟩

/-- The link port of the second component. -/
abbrev flatNetlistRegressionPortBLink :
    flatNetlistRegressionComponents.aggregatePortModeFamily.Port := ⟨true, true⟩

/-- The sole internal connection joins the two link ports. -/
abbrev flatNetlistRegressionConnection :
    PortConnection flatNetlistRegressionComponents.aggregatePortModeFamily where
  left := flatNetlistRegressionPortALink
  right := flatNetlistRegressionPortBLink
  left_ne_right := by
    intro hPort
    exact Bool.noConfusion (congrArg Sigma.fst hPort)
  modeEquiv := Equiv.refl Unit

/-- The proof-carrying singleton connection family. -/
abbrev flatNetlistRegressionConnections :
    PortConnectionFamily flatNetlistRegressionComponents.aggregatePortModeFamily Unit where
  connection := fun _ => flatNetlistRegressionConnection
  endpointPort_injective := by
    rintro ⟨firstIndex, firstEnd⟩ ⟨secondIndex, secondEnd⟩ hPort
    cases firstIndex
    cases secondIndex
    cases firstEnd <;> cases secondEnd
    · rfl
    · exact Bool.noConfusion (congrArg Sigma.fst hPort)
    · exact Bool.noConfusion (congrArg Sigma.fst hPort)
    · rfl

/-- The singular two-component flat netlist. -/
abbrev flatNetlistRegression : FlatNetlist where
  components := flatNetlistRegressionComponents
  Connection := Unit
  connections := flatNetlistRegressionConnections

/-- The two selected link channels are finite. -/
local instance flatNetlistRegressionConnectedChannelFintype :
    Fintype flatNetlistRegression.ConnectedChannel := by
  change Fintype (Σ _ : Unit, Unit ⊕ Unit)
  infer_instance

/-- The two selected link channels have decidable equality. -/
local instance flatNetlistRegressionConnectedChannelDecidableEq :
    DecidableEq flatNetlistRegression.ConnectedChannel :=
  Classical.decEq _

/-- The complementary external-channel family is finite. -/
local instance flatNetlistRegressionExternalChannelFintype :
    Fintype flatNetlistRegression.ExternalChannel :=
  Fintype.ofFinite _

/-- The first external ambient channel. -/
abbrev flatNetlistRegressionAExternal : flatNetlistRegression.Channel :=
  ⟨flatNetlistRegressionPortAExternal, ()⟩

/-- The first internal-link ambient channel. -/
abbrev flatNetlistRegressionALink : flatNetlistRegression.Channel :=
  ⟨flatNetlistRegressionPortALink, ()⟩

/-- The second external ambient channel. -/
abbrev flatNetlistRegressionBExternal : flatNetlistRegression.Channel :=
  ⟨flatNetlistRegressionPortBExternal, ()⟩

/-- The second internal-link ambient channel. -/
abbrev flatNetlistRegressionBLink : flatNetlistRegression.Channel :=
  ⟨flatNetlistRegressionPortBLink, ()⟩

/-- The first link channel in the connection family's dependent channel type. -/
abbrev flatNetlistRegressionConnectedA : flatNetlistRegression.ConnectedChannel :=
  ⟨(), Sum.inl ()⟩

/-- The second link channel in the connection family's dependent channel type. -/
abbrev flatNetlistRegressionConnectedB : flatNetlistRegression.ConnectedChannel :=
  ⟨(), Sum.inr ()⟩

/-- The first external ambient channel is outside the internal connection range. -/
lemma flatNetlistRegression_aExternal_not_mem_range :
    flatNetlistRegressionAExternal ∉
      Set.range flatNetlistRegression.connections.channelEmbedding := by
  rintro ⟨channel, hChannel⟩
  rcases channel with ⟨index, channel⟩
  rcases index with ⟨⟩
  rcases channel with mode | mode <;> cases mode
  · have hPort := congrArg (fun selected => selected.1.2) hChannel
    exact Bool.noConfusion hPort
  · have hComponent := congrArg (fun selected => selected.1.1) hChannel
    exact Bool.noConfusion hComponent

/-- The second external ambient channel is outside the internal connection range. -/
lemma flatNetlistRegression_bExternal_not_mem_range :
    flatNetlistRegressionBExternal ∉
      Set.range flatNetlistRegression.connections.channelEmbedding := by
  rintro ⟨channel, hChannel⟩
  rcases channel with ⟨index, channel⟩
  rcases index with ⟨⟩
  rcases channel with mode | mode <;> cases mode
  · have hComponent := congrArg (fun selected => selected.1.1) hChannel
    exact Bool.noConfusion hComponent
  · have hPort := congrArg (fun selected => selected.1.2) hChannel
    exact Bool.noConfusion hPort

/-- The packaged first external channel. -/
abbrev flatNetlistRegressionExternalA : flatNetlistRegression.ExternalChannel :=
  ⟨flatNetlistRegressionAExternal, flatNetlistRegression_aExternal_not_mem_range⟩

/-- The packaged second external channel. -/
abbrev flatNetlistRegressionExternalB : flatNetlistRegression.ExternalChannel :=
  ⟨flatNetlistRegressionBExternal, flatNetlistRegression_bExternal_not_mem_range⟩

/-!

## B. Exact component and boundary equations

-/

/-- The first component's link output is its external incident amplitude plus its link incident
amplitude. -/
lemma flatNetlistRegression_scattering_apply_aLink
    (incident : ModeAmplitude flatNetlistRegression.IncidentIndex) :
    flatNetlistRegression.scatteringTransform.toLinearMap incident
        (Outgoing.mk flatNetlistRegressionALink) =
      incident (Incident.mk flatNetlistRegressionAExternal) +
        incident (Incident.mk flatNetlistRegressionALink) := by
  classical
  rw [FlatNetlist.scatteringTransform, FlatNetlist.scatteringMatrix,
    ScatteringMatrix.toLinearMap_toOrientedModeTransform,
    ModeAmplitude.reindex_apply]
  simp only [Equiv.symm_symm, Outgoing.channelEquiv_apply]
  change flatNetlistRegressionComponents.assembledScatteringMatrix.toModeTransform.toLinearMap
      (ModeAmplitude.reindex Incident.channelEquiv incident)
        (flatNetlistRegressionComponents.componentChannelEmbedding false ⟨true, ()⟩) = _
  rw [flatNetlistRegressionComponents.assembledScatteringMatrix_apply_component]
  rw [Matrix.ofLp_toLpLin, Matrix.toLin'_apply]
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sigma, Fintype.sum_bool,
    Fintype.sum_unique, flatNetlistRegressionScattering,
    ModeAmplitude.restrictEmbedding_apply, ModeAmplitude.reindex_apply]
  change 1 * incident (Incident.mk flatNetlistRegressionALink) +
      1 * incident (Incident.mk flatNetlistRegressionAExternal) = _
  ring

/-- The second component's link output is its external incident amplitude plus its link incident
amplitude. -/
lemma flatNetlistRegression_scattering_apply_bLink
    (incident : ModeAmplitude flatNetlistRegression.IncidentIndex) :
    flatNetlistRegression.scatteringTransform.toLinearMap incident
        (Outgoing.mk flatNetlistRegressionBLink) =
      incident (Incident.mk flatNetlistRegressionBExternal) +
        incident (Incident.mk flatNetlistRegressionBLink) := by
  classical
  rw [FlatNetlist.scatteringTransform, FlatNetlist.scatteringMatrix,
    ScatteringMatrix.toLinearMap_toOrientedModeTransform,
    ModeAmplitude.reindex_apply]
  simp only [Equiv.symm_symm, Outgoing.channelEquiv_apply]
  change flatNetlistRegressionComponents.assembledScatteringMatrix.toModeTransform.toLinearMap
      (ModeAmplitude.reindex Incident.channelEquiv incident)
        (flatNetlistRegressionComponents.componentChannelEmbedding true ⟨true, ()⟩) = _
  rw [flatNetlistRegressionComponents.assembledScatteringMatrix_apply_component]
  rw [Matrix.ofLp_toLpLin, Matrix.toLin'_apply]
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sigma, Fintype.sum_bool,
    Fintype.sum_unique, flatNetlistRegressionScattering,
    ModeAmplitude.restrictEmbedding_apply, ModeAmplitude.reindex_apply]
  change 1 * incident (Incident.mk flatNetlistRegressionBLink) +
      1 * incident (Incident.mk flatNetlistRegressionBExternal) = _
  ring

/-- The first component's external output is its link incident amplitude. -/
lemma flatNetlistRegression_scattering_apply_aExternal
    (incident : ModeAmplitude flatNetlistRegression.IncidentIndex) :
    flatNetlistRegression.scatteringTransform.toLinearMap incident
        (Outgoing.mk flatNetlistRegressionAExternal) =
      incident (Incident.mk flatNetlistRegressionALink) := by
  classical
  rw [FlatNetlist.scatteringTransform, FlatNetlist.scatteringMatrix,
    ScatteringMatrix.toLinearMap_toOrientedModeTransform,
    ModeAmplitude.reindex_apply]
  simp only [Equiv.symm_symm, Outgoing.channelEquiv_apply]
  change flatNetlistRegressionComponents.assembledScatteringMatrix.toModeTransform.toLinearMap
      (ModeAmplitude.reindex Incident.channelEquiv incident)
        (flatNetlistRegressionComponents.componentChannelEmbedding false ⟨false, ()⟩) = _
  rw [flatNetlistRegressionComponents.assembledScatteringMatrix_apply_component]
  rw [Matrix.ofLp_toLpLin, Matrix.toLin'_apply]
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sigma, Fintype.sum_bool,
    Fintype.sum_unique, flatNetlistRegressionScattering,
    ModeAmplitude.restrictEmbedding_apply, ModeAmplitude.reindex_apply]
  change 1 * incident (Incident.mk flatNetlistRegressionALink) +
      0 * incident (Incident.mk flatNetlistRegressionAExternal) = _
  ring

/-- The second component's external output is twice its link incident amplitude. -/
lemma flatNetlistRegression_scattering_apply_bExternal
    (incident : ModeAmplitude flatNetlistRegression.IncidentIndex) :
    flatNetlistRegression.scatteringTransform.toLinearMap incident
        (Outgoing.mk flatNetlistRegressionBExternal) =
      2 * incident (Incident.mk flatNetlistRegressionBLink) := by
  classical
  rw [FlatNetlist.scatteringTransform, FlatNetlist.scatteringMatrix,
    ScatteringMatrix.toLinearMap_toOrientedModeTransform,
    ModeAmplitude.reindex_apply]
  simp only [Equiv.symm_symm, Outgoing.channelEquiv_apply]
  change flatNetlistRegressionComponents.assembledScatteringMatrix.toModeTransform.toLinearMap
      (ModeAmplitude.reindex Incident.channelEquiv incident)
        (flatNetlistRegressionComponents.componentChannelEmbedding true ⟨false, ()⟩) = _
  rw [flatNetlistRegressionComponents.assembledScatteringMatrix_apply_component]
  rw [Matrix.ofLp_toLpLin, Matrix.toLin'_apply]
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sigma, Fintype.sum_bool,
    Fintype.sum_unique, flatNetlistRegressionScattering,
    ModeAmplitude.restrictEmbedding_apply, ModeAmplitude.reindex_apply]
  change 2 * incident (Incident.mk flatNetlistRegressionBLink) +
      0 * incident (Incident.mk flatNetlistRegressionBExternal) = _
  ring

/-- At the first link input, incident assembly routes the second link output. -/
lemma flatNetlistRegression_incidentAssembly_apply_aLink
    (outgoing : ModeAmplitude flatNetlistRegression.OutgoingIndex)
    (input : ModeAmplitude flatNetlistRegression.ExternalIncident) :
    flatNetlistRegression.connections.incidentAssembly outgoing input
        (Incident.mk flatNetlistRegressionALink) =
      outgoing (Outgoing.mk flatNetlistRegressionBLink) := by
  exact flatNetlistRegression.connections.incidentAssembly_apply_connected_channel
    outgoing input flatNetlistRegressionConnectedA

/-- At the second link input, incident assembly routes the first link output. -/
lemma flatNetlistRegression_incidentAssembly_apply_bLink
    (outgoing : ModeAmplitude flatNetlistRegression.OutgoingIndex)
    (input : ModeAmplitude flatNetlistRegression.ExternalIncident) :
    flatNetlistRegression.connections.incidentAssembly outgoing input
        (Incident.mk flatNetlistRegressionBLink) =
      outgoing (Outgoing.mk flatNetlistRegressionALink) := by
  exact flatNetlistRegression.connections.incidentAssembly_apply_connected_channel
    outgoing input flatNetlistRegressionConnectedB

/-- At the first external input, incident assembly returns the exact supplied coordinate. -/
lemma flatNetlistRegression_incidentAssembly_apply_aExternal
    (outgoing : ModeAmplitude flatNetlistRegression.OutgoingIndex)
    (input : ModeAmplitude flatNetlistRegression.ExternalIncident) :
    flatNetlistRegression.connections.incidentAssembly outgoing input
        (Incident.mk flatNetlistRegressionAExternal) =
      input (Incident.mk flatNetlistRegressionExternalA) := by
  exact flatNetlistRegression.connections.incidentAssembly_apply_external
    outgoing input flatNetlistRegressionExternalA

/-- At the second external input, incident assembly returns the exact supplied coordinate. -/
lemma flatNetlistRegression_incidentAssembly_apply_bExternal
    (outgoing : ModeAmplitude flatNetlistRegression.OutgoingIndex)
    (input : ModeAmplitude flatNetlistRegression.ExternalIncident) :
    flatNetlistRegression.connections.incidentAssembly outgoing input
        (Incident.mk flatNetlistRegressionBExternal) =
      input (Incident.mk flatNetlistRegressionExternalB) := by
  exact flatNetlistRegression.connections.incidentAssembly_apply_external
    outgoing input flatNetlistRegressionExternalB

/-!

## C. A singular family of solutions

-/

/-- The zero-input incident state with common internal amplitude `t`. -/
def flatNetlistRegressionIncident (t : ℂ) :
    ModeAmplitude flatNetlistRegression.IncidentIndex :=
  WithLp.toLp 2 fun endpoint => if endpoint.channel.1.2 then t else 0

/-- The corresponding outgoing state: `(t, t)` on the first component and `(2t, t)` on the
second. -/
def flatNetlistRegressionOutgoing (t : ℂ) :
    ModeAmplitude flatNetlistRegression.OutgoingIndex :=
  WithLp.toLp 2 fun endpoint =>
    match endpoint.channel.1.1, endpoint.channel.1.2 with
    | false, _ => t
    | true, false => 2 * t
    | true, true => t

/-- Component scattering maps every displayed incident state to its displayed outgoing state. -/
lemma flatNetlistRegression_scattering_action (t : ℂ) :
    flatNetlistRegression.scatteringTransform.toLinearMap
        (flatNetlistRegressionIncident t) =
      flatNetlistRegressionOutgoing t := by
  apply WithLp.ofLp_injective 2
  funext endpoint
  rcases endpoint with ⟨⟨⟨component, port⟩, mode⟩⟩
  cases component <;> cases port <;> cases mode
  · rw [flatNetlistRegression_scattering_apply_aExternal]
    simp [flatNetlistRegressionIncident, flatNetlistRegressionOutgoing]
  · rw [flatNetlistRegression_scattering_apply_aLink]
    simp [flatNetlistRegressionIncident, flatNetlistRegressionOutgoing]
  · rw [flatNetlistRegression_scattering_apply_bExternal]
    simp [flatNetlistRegressionIncident, flatNetlistRegressionOutgoing]
  · rw [flatNetlistRegression_scattering_apply_bLink]
    simp [flatNetlistRegressionIncident, flatNetlistRegressionOutgoing]

/-- Mate routing and zero external injection reconstruct every displayed incident state. -/
lemma flatNetlistRegression_incidentAssembly_zero (t : ℂ) :
    flatNetlistRegressionIncident t =
      flatNetlistRegression.connections.incidentAssembly
        (flatNetlistRegressionOutgoing t) 0 := by
  apply WithLp.ofLp_injective 2
  funext endpoint
  rcases endpoint with ⟨⟨⟨component, port⟩, mode⟩⟩
  cases component <;> cases port <;> cases mode
  · rw [flatNetlistRegression_incidentAssembly_apply_aExternal]
    simp [flatNetlistRegressionIncident]
  · rw [flatNetlistRegression_incidentAssembly_apply_aLink]
    simp [flatNetlistRegressionIncident, flatNetlistRegressionOutgoing]
  · rw [flatNetlistRegression_incidentAssembly_apply_bExternal]
    simp [flatNetlistRegressionIncident]
  · rw [flatNetlistRegression_incidentAssembly_apply_bLink]
    simp [flatNetlistRegressionIncident, flatNetlistRegressionOutgoing]

/-- Every complex `t` gives a complete zero-input solution of the singular feedback loop. -/
lemma flatNetlistRegression_solution (t : ℂ) :
    ((0 : ModeAmplitude flatNetlistRegression.ExternalIncident),
        (flatNetlistRegressionIncident t).directSum
          (flatNetlistRegressionOutgoing t)) ∈
      flatNetlistRegression.solutionBehavior := by
  rw [flatNetlistRegression.mem_solutionBehavior_directSum_iff]
  exact ⟨(flatNetlistRegression.mem_componentBehavior_iff _ _).mpr
      (flatNetlistRegression_scattering_action t).symm,
    flatNetlistRegression_incidentAssembly_zero t⟩

/-- The zero and unit-parameter complete solution states are distinct. -/
lemma flatNetlistRegression_solutionState_zero_ne_one :
    (flatNetlistRegressionIncident 0).directSum (flatNetlistRegressionOutgoing 0) ≠
      (flatNetlistRegressionIncident 1).directSum (flatNetlistRegressionOutgoing 1) := by
  intro hState
  have hCoordinate := congrArg
    (fun state => state (Sum.inl (Incident.mk flatNetlistRegressionALink))) hState
  simp [flatNetlistRegressionIncident] at hCoordinate

/-- The complete solution relation is multivalued at zero external input. -/
lemma flatNetlistRegression_solutionBehavior_not_singleValued :
    ¬flatNetlistRegression.solutionBehavior.IsSingleValued := by
  intro hSingleValued
  exact flatNetlistRegression_solutionState_zero_ne_one
    (hSingleValued (flatNetlistRegression_solution 0) (flatNetlistRegression_solution 1))

/-- The exact external output associated with parameter `t`, obtained through the netlist's
derived readout. -/
def flatNetlistRegressionOutput (t : ℂ) :
    ModeAmplitude flatNetlistRegression.ExternalOutgoing :=
  flatNetlistRegression.outputReadout.toLinearMap (flatNetlistRegressionOutgoing t)

/-- Every displayed zero-input solution projects to its corresponding external output. -/
lemma flatNetlistRegression_behavior_member (t : ℂ) :
    ((0 : ModeAmplitude flatNetlistRegression.ExternalIncident),
        flatNetlistRegressionOutput t) ∈ flatNetlistRegression.behavior := by
  rw [flatNetlistRegression.mem_behavior_iff_componentBehavior]
  exact ⟨flatNetlistRegressionIncident t, flatNetlistRegressionOutgoing t,
    (flatNetlistRegression.mem_componentBehavior_iff _ _).mpr
      (flatNetlistRegression_scattering_action t).symm,
    flatNetlistRegression_incidentAssembly_zero t, rfl⟩

/-- Readout exposes the first component's external outgoing coordinate as `t`. -/
lemma flatNetlistRegression_output_apply_aExternal (t : ℂ) :
    flatNetlistRegressionOutput t (Outgoing.mk flatNetlistRegressionExternalA) = t := by
  rw [flatNetlistRegressionOutput,
    FlatNetlist.outputReadout,
    flatNetlistRegression.connections.externalOutgoingReadout_apply,
    ModeAmplitude.restrictEmbedding_apply]
  rfl

/-- Readout exposes the second component's external outgoing coordinate as `2t`. -/
lemma flatNetlistRegression_output_apply_bExternal (t : ℂ) :
    flatNetlistRegressionOutput t (Outgoing.mk flatNetlistRegressionExternalB) = 2 * t := by
  rw [flatNetlistRegressionOutput,
    FlatNetlist.outputReadout,
    flatNetlistRegression.connections.externalOutgoingReadout_apply,
    ModeAmplitude.restrictEmbedding_apply]
  rfl

/-- The zero and unit-parameter external outputs are distinct (`(0, 0)` versus `(1, 2)`). -/
lemma flatNetlistRegression_output_zero_ne_one :
    flatNetlistRegressionOutput 0 ≠ flatNetlistRegressionOutput 1 := by
  intro hOutput
  have hCoordinate := congrArg
    (fun output => output (Outgoing.mk flatNetlistRegressionExternalA)) hOutput
  rw [flatNetlistRegression_output_apply_aExternal,
    flatNetlistRegression_output_apply_aExternal] at hCoordinate
  norm_num at hCoordinate

/-- Projecting the singular solutions leaves the external behavior multivalued. -/
lemma flatNetlistRegression_behavior_not_singleValued :
    ¬flatNetlistRegression.behavior.IsSingleValued := by
  intro hSingleValued
  exact flatNetlistRegression_output_zero_ne_one
    (hSingleValued (flatNetlistRegression_behavior_member 0)
      (flatNetlistRegression_behavior_member 1))

/-- The unit-parameter incident state is nonzero. -/
lemma flatNetlistRegressionIncident_one_ne_zero :
    flatNetlistRegressionIncident 1 ≠ 0 := by
  intro hIncident
  have hCoordinate := congrArg
    (fun incident => incident (Incident.mk flatNetlistRegressionALink)) hIncident
  simp [flatNetlistRegressionIncident] at hCoordinate

/-- The feedback operator sends the unit-parameter incident state to zero. -/
lemma flatNetlistRegression_feedbackOperator_kernel :
    flatNetlistRegression.feedbackOperator.toLinearMap
        (flatNetlistRegressionIncident 1) = 0 := by
  have hFeedback :=
    (flatNetlistRegression.mem_solutionBehavior_directSum_iff_scattering_feedbackEquation
      (0 : ModeAmplitude flatNetlistRegression.ExternalIncident)
      (flatNetlistRegressionIncident 1) (flatNetlistRegressionOutgoing 1)).mp
        (flatNetlistRegression_solution 1) |>.2
  simpa using hFeedback

/-- The nonzero kernel witness makes the feedback operator noninjective. -/
lemma flatNetlistRegression_feedbackOperator_not_injective :
    ¬Function.Injective flatNetlistRegression.feedbackOperator.toLinearMap := by
  intro hInjective
  apply flatNetlistRegressionIncident_one_ne_zero
  apply hInjective
  simpa using flatNetlistRegression_feedbackOperator_kernel

/-!

## D. An external input with no solution

-/

/-- The hostile external input is one on the first external channel and zero on the second. -/
def flatNetlistRegressionBadInput :
    ModeAmplitude flatNetlistRegression.ExternalIncident :=
  PiLp.single 2 (Incident.mk flatNetlistRegressionExternalA) 1

/-- The hostile input has the expected first coordinate. -/
lemma flatNetlistRegression_badInput_apply_aExternal :
    flatNetlistRegressionBadInput (Incident.mk flatNetlistRegressionExternalA) = 1 := by
  simp [flatNetlistRegressionBadInput]

/-- The hostile input has zero at the second external coordinate. -/
lemma flatNetlistRegression_badInput_apply_bExternal :
    flatNetlistRegressionBadInput (Incident.mk flatNetlistRegressionExternalB) = 0 := by
  have hNe : (Incident.mk flatNetlistRegressionExternalB) ≠
      Incident.mk flatNetlistRegressionExternalA := by
    intro h
    have hComponent := congrArg (fun endpoint => endpoint.channel.1.1.1) h
    cases hComponent
  simp [flatNetlistRegressionBadInput, hNe]

/-- No complete solution exists for the hostile input. -/
lemma flatNetlistRegression_badInput_no_solution :
    ¬∃ state,
      (flatNetlistRegressionBadInput, state) ∈ flatNetlistRegression.solutionBehavior := by
  rintro ⟨state, hState⟩
  let incident := state.restrictInl
  let outgoing := state.restrictInr
  have hStateEq : state = incident.directSum outgoing :=
    (ModeAmplitude.directSum_restrict state).symm
  have hSolution :
      (flatNetlistRegressionBadInput, incident.directSum outgoing) ∈
        flatNetlistRegression.solutionBehavior := by
    rw [← hStateEq]
    exact hState
  rcases (flatNetlistRegression.mem_solutionBehavior_directSum_iff
    flatNetlistRegressionBadInput incident outgoing).mp hSolution with
    ⟨hComponent, hIncident⟩
  have hScattering :=
    (flatNetlistRegression.mem_componentBehavior_iff incident outgoing).mp hComponent
  have hAExternal := congrArg
    (fun amplitude => amplitude (Incident.mk flatNetlistRegressionAExternal)) hIncident
  have hALink := congrArg
    (fun amplitude => amplitude (Incident.mk flatNetlistRegressionALink)) hIncident
  have hBExternal := congrArg
    (fun amplitude => amplitude (Incident.mk flatNetlistRegressionBExternal)) hIncident
  have hBLink := congrArg
    (fun amplitude => amplitude (Incident.mk flatNetlistRegressionBLink)) hIncident
  rw [flatNetlistRegression_incidentAssembly_apply_aExternal,
    flatNetlistRegression_badInput_apply_aExternal] at hAExternal
  rw [flatNetlistRegression_incidentAssembly_apply_aLink] at hALink
  rw [flatNetlistRegression_incidentAssembly_apply_bExternal,
    flatNetlistRegression_badInput_apply_bExternal] at hBExternal
  rw [flatNetlistRegression_incidentAssembly_apply_bLink] at hBLink
  have hScatteringALink := congrArg
    (fun amplitude => amplitude (Outgoing.mk flatNetlistRegressionALink)) hScattering
  have hScatteringBLink := congrArg
    (fun amplitude => amplitude (Outgoing.mk flatNetlistRegressionBLink)) hScattering
  rw [flatNetlistRegression_scattering_apply_aLink] at hScatteringALink
  rw [flatNetlistRegression_scattering_apply_bLink] at hScatteringBLink
  rw [hAExternal] at hScatteringALink
  rw [hBExternal, zero_add] at hScatteringBLink
  rw [hScatteringALink] at hBLink
  rw [hScatteringBLink] at hALink
  have hImpossible : (1 : ℂ) = 0 := by
    linear_combination -hALink - hBLink
  exact one_ne_zero hImpossible

/-- The complete solution behavior is not total. -/
lemma flatNetlistRegression_solutionBehavior_not_total :
    ¬flatNetlistRegression.solutionBehavior.IsTotal := by
  intro hTotal
  exact flatNetlistRegression_badInput_no_solution
    (hTotal flatNetlistRegressionBadInput)

/-- No external output is related to the hostile input. -/
lemma flatNetlistRegression_badInput_not_mem_behavior
    (output : ModeAmplitude flatNetlistRegression.ExternalOutgoing) :
    (flatNetlistRegressionBadInput, output) ∉ flatNetlistRegression.behavior := by
  intro hBehavior
  rcases (flatNetlistRegression.mem_behavior_iff_componentBehavior _ _).mp hBehavior with
    ⟨incident, outgoing, hComponent, hIncident, hOutput⟩
  apply flatNetlistRegression_badInput_no_solution
  refine ⟨incident.directSum outgoing, ?_⟩
  exact (flatNetlistRegression.mem_solutionBehavior_directSum_iff _ _ _).mpr
    ⟨hComponent, hIncident⟩

/-- The projected external behavior is not total. -/
lemma flatNetlistRegression_behavior_not_total :
    ¬flatNetlistRegression.behavior.IsTotal := by
  intro hTotal
  rcases hTotal flatNetlistRegressionBadInput with ⟨output, hOutput⟩
  exact flatNetlistRegression_badInput_not_mem_behavior output hOutput

end

end Optics
