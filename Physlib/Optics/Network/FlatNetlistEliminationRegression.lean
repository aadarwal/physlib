/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.FlatNetlistElimination
public import Physlib.Optics.Network.FlatNetlistRegression

/-!
# Regression tests for well-posed flat-netlist elimination

## i. Overview

Two two-port components reuse the shared-link topology of the singular flat-netlist regression.
Their nonreal, nonsymmetric coefficients make the feedback operator invertible and give a fully
coupled external response. Exact matrices pin the inverse gate, the order
`E_outᴴ * S * (1 - C * S)⁻¹ * E_in`, each intermediate solution block, and agreement with the
complete relational semantics.

The pre-existing singular shared-link fixture remains a negative control: it has a nonzero
homogeneous feedback state and an external input with no solution, so it is not well posed.

## ii. Scope

The coefficients are hostile algebraic sentinels, not passive or physically normalized optical
components. Invertibility is proved without a contraction hypothesis. The regression does not
claim losslessness, reciprocity, causality, or frequency-domain realizability.

## iii. Table of contents

- A. A well-posed noncommuting shared-link netlist
- B. Exact feedback inverse and well-posedness
- C. Complete solution and external response
- D. Singular negative control
- E. Wiring-presentation invariance

-/

@[expose] public section

namespace Optics

noncomputable section

/-!

## A. A well-posed noncommuting shared-link netlist

-/

/-- The well-posed fixture component matrices. In local `[external, link]` order they are
`[[1, 4], [2, I]]` and `[[I, 2], [3, I]]`. -/
def flatNetlistEliminationRegressionScattering
    (component : Bool) : ScatteringMatrix flatNetlistRegressionPortFamily.Channel where
  toModeTransform := fun output input =>
    match component, output.1, input.1 with
    | false, false, false => 1
    | false, false, true => 4
    | false, true, false => 2
    | false, true, true => Complex.I
    | true, false, false => Complex.I
    | true, false, true => 2
    | true, true, false => 3
    | true, true, true => Complex.I

/-- The two well-posed fixture components before wiring. -/
abbrev flatNetlistEliminationRegressionComponents : ScatteringComponentFamily where
  Component := Bool
  portFamily := fun _ => flatNetlistRegressionPortFamily
  scattering := flatNetlistEliminationRegressionScattering

/-- The well-posed fixture reuses the exact one-link connection topology of the singular fixture. -/
abbrev flatNetlistEliminationRegression : FlatNetlist where
  components := flatNetlistEliminationRegressionComponents
  Connection := Unit
  connections := flatNetlistRegressionConnections

/-- Aggregate channels in the well-posed fixture are finite. -/
local instance flatNetlistEliminationRegressionChannelFintype :
    Fintype flatNetlistEliminationRegression.Channel := by
  change Fintype (Σ _ : (Σ _ : Bool, Bool), Unit)
  infer_instance

/-- Aggregate channels in the well-posed fixture have decidable equality. -/
local instance flatNetlistEliminationRegressionChannelDecidableEq :
    DecidableEq flatNetlistEliminationRegression.Channel := Classical.decEq _

/-- Connected channels in the well-posed fixture are finite. -/
local instance flatNetlistEliminationRegressionConnectedChannelFintype :
    Fintype flatNetlistEliminationRegression.ConnectedChannel := by
  change Fintype (Σ _ : Unit, Unit ⊕ Unit)
  infer_instance

/-- Connected channels in the well-posed fixture have decidable equality. -/
local instance flatNetlistEliminationRegressionConnectedChannelDecidableEq :
    DecidableEq flatNetlistEliminationRegression.ConnectedChannel := Classical.decEq _

/-- External channels in the well-posed fixture are finite. -/
local instance flatNetlistEliminationRegressionExternalChannelFintype :
    Fintype flatNetlistEliminationRegression.ExternalChannel :=
  Fintype.ofFinite _

/-- The first external ambient channel of the well-posed fixture. -/
abbrev flatNetlistEliminationRegressionAExternal :
    flatNetlistEliminationRegression.Channel :=
  ⟨flatNetlistRegressionPortAExternal, ()⟩

/-- The first internal-link ambient channel of the well-posed fixture. -/
abbrev flatNetlistEliminationRegressionALink :
    flatNetlistEliminationRegression.Channel :=
  ⟨flatNetlistRegressionPortALink, ()⟩

/-- The second external ambient channel of the well-posed fixture. -/
abbrev flatNetlistEliminationRegressionBExternal :
    flatNetlistEliminationRegression.Channel :=
  ⟨flatNetlistRegressionPortBExternal, ()⟩

/-- The second internal-link ambient channel of the well-posed fixture. -/
abbrev flatNetlistEliminationRegressionBLink :
    flatNetlistEliminationRegression.Channel :=
  ⟨flatNetlistRegressionPortBLink, ()⟩

/-- Equality of concrete aggregate channels is equality of their component and port tags. -/
@[simp]
lemma flatNetlistEliminationRegression_channel_eq_iff
    (firstComponent firstPort secondComponent secondPort : Bool) :
    ((⟨⟨firstComponent, firstPort⟩, ()⟩ :
        flatNetlistEliminationRegression.Channel) =
      ⟨⟨secondComponent, secondPort⟩, ()⟩) ↔
        firstComponent = secondComponent ∧ firstPort = secondPort := by
  constructor
  · intro hChannel
    exact ⟨congrArg (fun channel => channel.1.1) hChannel,
      congrArg (fun channel => channel.1.2) hChannel⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- The first connected link channel in the well-posed fixture. -/
abbrev flatNetlistEliminationRegressionConnectedA :
    flatNetlistEliminationRegression.ConnectedChannel :=
  flatNetlistRegressionConnectedA

/-- The second connected link channel in the well-posed fixture. -/
abbrev flatNetlistEliminationRegressionConnectedB :
    flatNetlistEliminationRegression.ConnectedChannel :=
  flatNetlistRegressionConnectedB

/-- The first external ambient channel is outside the internal connection range. -/
lemma flatNetlistEliminationRegression_aExternal_not_mem_range :
    flatNetlistEliminationRegressionAExternal ∉
      Set.range flatNetlistEliminationRegression.connections.channelEmbedding := by
  rintro ⟨channel, hChannel⟩
  rcases channel with ⟨index, channel⟩
  rcases index with ⟨⟩
  rcases channel with mode | mode <;> cases mode
  · have hPort := congrArg (fun selected => selected.1.2) hChannel
    exact Bool.noConfusion hPort
  · have hComponent := congrArg (fun selected => selected.1.1) hChannel
    exact Bool.noConfusion hComponent

/-- The second external ambient channel is outside the internal connection range. -/
lemma flatNetlistEliminationRegression_bExternal_not_mem_range :
    flatNetlistEliminationRegressionBExternal ∉
      Set.range flatNetlistEliminationRegression.connections.channelEmbedding := by
  rintro ⟨channel, hChannel⟩
  rcases channel with ⟨index, channel⟩
  rcases index with ⟨⟩
  rcases channel with mode | mode <;> cases mode
  · have hComponent := congrArg (fun selected => selected.1.1) hChannel
    exact Bool.noConfusion hComponent
  · have hPort := congrArg (fun selected => selected.1.2) hChannel
    exact Bool.noConfusion hPort

/-- The packaged first external channel of the well-posed fixture. -/
abbrev flatNetlistEliminationRegressionExternalA :
    flatNetlistEliminationRegression.ExternalChannel :=
  ⟨flatNetlistEliminationRegressionAExternal,
    flatNetlistEliminationRegression_aExternal_not_mem_range⟩

/-- The packaged second external channel of the well-posed fixture. -/
abbrev flatNetlistEliminationRegressionExternalB :
    flatNetlistEliminationRegression.ExternalChannel :=
  ⟨flatNetlistEliminationRegressionBExternal,
    flatNetlistEliminationRegression_bExternal_not_mem_range⟩

/-- The first connected channel embeds as the first component's link channel. -/
lemma flatNetlistEliminationRegression_channelEmbedding_connectedA :
    flatNetlistEliminationRegression.connections.channelEmbedding
        flatNetlistEliminationRegressionConnectedA =
      flatNetlistEliminationRegressionALink := rfl

/-- The second connected channel embeds as the second component's link channel. -/
lemma flatNetlistEliminationRegression_channelEmbedding_connectedB :
    flatNetlistEliminationRegression.connections.channelEmbedding
        flatNetlistEliminationRegressionConnectedB =
      flatNetlistEliminationRegressionBLink := rfl

/-- The mate of the first connected endpoint is the second connected endpoint. -/
@[simp]
lemma flatNetlistEliminationRegression_mate_connectedA :
    flatNetlistEliminationRegression.connections.mateEquiv
        flatNetlistEliminationRegressionConnectedA =
      flatNetlistEliminationRegressionConnectedB := rfl

/-- The mate of the second connected endpoint is the first connected endpoint. -/
@[simp]
lemma flatNetlistEliminationRegression_mate_connectedB :
    flatNetlistEliminationRegression.connections.mateEquiv
        flatNetlistEliminationRegressionConnectedB =
      flatNetlistEliminationRegressionConnectedA := rfl

/-- Every exposed channel is one of the two declared external endpoints. -/
lemma flatNetlistEliminationRegression_external_eq_a_or_b
    (channel : flatNetlistEliminationRegression.ExternalChannel) :
    channel = flatNetlistEliminationRegressionExternalA ∨
      channel = flatNetlistEliminationRegressionExternalB := by
  rcases channel with ⟨⟨⟨component, port⟩, mode⟩, hExternal⟩
  change (flatNetlistEliminationRegression.components.portFamily component).Mode port at mode
  cases component <;> cases port <;> cases mode
  · left
    apply Subtype.ext
    rfl
  · exfalso
    exact hExternal ⟨flatNetlistEliminationRegressionConnectedA,
      flatNetlistEliminationRegression_channelEmbedding_connectedA⟩
  · right
    apply Subtype.ext
    rfl
  · exfalso
    exact hExternal ⟨flatNetlistEliminationRegressionConnectedB,
      flatNetlistEliminationRegression_channelEmbedding_connectedB⟩

/-- Incident exposure embeds the first external label at its ambient channel. -/
@[simp]
lemma flatNetlistEliminationRegression_externalIncidentEmbedding_a :
    flatNetlistEliminationRegression.connections.externalIncidentEmbedding
        (Incident.mk flatNetlistEliminationRegressionExternalA) =
      Incident.mk flatNetlistEliminationRegressionAExternal := rfl

/-- Incident exposure embeds the second external label at its ambient channel. -/
@[simp]
lemma flatNetlistEliminationRegression_externalIncidentEmbedding_b :
    flatNetlistEliminationRegression.connections.externalIncidentEmbedding
        (Incident.mk flatNetlistEliminationRegressionExternalB) =
      Incident.mk flatNetlistEliminationRegressionBExternal := rfl

/-- Outgoing readout embeds the first external label at its ambient channel. -/
@[simp]
lemma flatNetlistEliminationRegression_externalOutgoingEmbedding_a :
    flatNetlistEliminationRegression.connections.externalOutgoingEmbedding
        (Outgoing.mk flatNetlistEliminationRegressionExternalA) =
      Outgoing.mk flatNetlistEliminationRegressionAExternal := rfl

/-- Outgoing readout embeds the second external label at its ambient channel. -/
@[simp]
lemma flatNetlistEliminationRegression_externalOutgoingEmbedding_b :
    flatNetlistEliminationRegression.connections.externalOutgoingEmbedding
        (Outgoing.mk flatNetlistEliminationRegressionExternalB) =
      Outgoing.mk flatNetlistEliminationRegressionBExternal := rfl

/-- The exact feedback matrix in aggregate order `(A.ext, A.link, B.ext, B.link)`. -/
def flatNetlistEliminationRegressionFeedback :
    ModeTransform flatNetlistEliminationRegression.IncidentIndex
      flatNetlistEliminationRegression.IncidentIndex := fun output input =>
  match output.channel.1.1, output.channel.1.2, input.channel.1.1, input.channel.1.2 with
  | false, false, false, false => 1
  | false, true, false, true => 1
  | false, true, true, false => -3
  | false, true, true, true => -Complex.I
  | true, false, true, false => 1
  | true, true, false, false => -2
  | true, true, false, true => -Complex.I
  | true, true, true, true => 1
  | _, _, _, _ => 0

/-- The displayed inverse feedback matrix in the same aggregate order. -/
def flatNetlistEliminationRegressionInverse :
    ModeTransform flatNetlistEliminationRegression.IncidentIndex
      flatNetlistEliminationRegression.IncidentIndex := fun output input =>
  match output.channel.1.1, output.channel.1.2, input.channel.1.1, input.channel.1.2 with
  | false, false, false, false => 1
  | false, true, false, false => Complex.I
  | false, true, false, true => 1 / 2
  | false, true, true, false => 3 / 2
  | false, true, true, true => Complex.I / 2
  | true, false, true, false => 1
  | true, true, false, false => 1
  | true, true, false, true => Complex.I / 2
  | true, true, true, false => 3 * Complex.I / 2
  | true, true, true, true => 1 / 2
  | _, _, _, _ => 0

/-- The expected external response in exposed order `(A.ext, B.ext)`. -/
def flatNetlistEliminationRegressionResponse :
    ModeTransform flatNetlistEliminationRegression.ExternalIncident
      flatNetlistEliminationRegression.ExternalOutgoing := fun output input =>
  match output.channel.1.1.1, input.channel.1.1.1 with
  | false, false => 1 + 4 * Complex.I
  | false, true => 6
  | true, false => 2
  | true, true => 4 * Complex.I

/-- The explicit assembled component transform in aggregate endpoint coordinates. -/
def flatNetlistEliminationRegressionScatteringTransform :
    ModeTransform flatNetlistEliminationRegression.IncidentIndex
      flatNetlistEliminationRegression.OutgoingIndex := fun output input =>
  match output.channel.1.1, output.channel.1.2, input.channel.1.1, input.channel.1.2 with
  | false, false, false, false => 1
  | false, false, false, true => 4
  | false, true, false, false => 2
  | false, true, false, true => Complex.I
  | true, false, true, false => Complex.I
  | true, false, true, true => 2
  | true, true, true, false => 3
  | true, true, true, true => Complex.I
  | _, _, _, _ => 0

/-- The explicit partial-routing transform, exchanging only the two link endpoints. -/
def flatNetlistEliminationRegressionRoutingTransform :
    ModeTransform flatNetlistEliminationRegression.OutgoingIndex
      flatNetlistEliminationRegression.IncidentIndex := fun incident outgoing =>
  match incident.channel.1.1, incident.channel.1.2,
      outgoing.channel.1.1, outgoing.channel.1.2 with
  | false, true, true, true => 1
  | true, true, false, true => 1
  | _, _, _, _ => 0

/-- The explicit injection of the two exposed incident coordinates into the aggregate boundary. -/
def flatNetlistEliminationRegressionInputExposure :
    ModeTransform flatNetlistEliminationRegression.ExternalIncident
      flatNetlistEliminationRegression.IncidentIndex := fun incident external =>
  match incident.channel.1.1, incident.channel.1.2, external.channel.1.1.1 with
  | false, false, false => 1
  | true, false, true => 1
  | _, _, _ => 0

/-- The explicit readout of the two exposed outgoing coordinates from the aggregate boundary. -/
def flatNetlistEliminationRegressionOutputReadout :
    ModeTransform flatNetlistEliminationRegression.OutgoingIndex
      flatNetlistEliminationRegression.ExternalOutgoing := fun external outgoing =>
  match external.channel.1.1.1, outgoing.channel.1.1, outgoing.channel.1.2 with
  | false, false, false => 1
  | true, true, false => 1
  | _, _, _ => 0

/-- The explicit solved incident block `F⁻¹ E_in` for the two exposed inputs. -/
def flatNetlistEliminationRegressionIncidentSolution :
    ModeTransform flatNetlistEliminationRegression.ExternalIncident
      flatNetlistEliminationRegression.IncidentIndex := fun incident external =>
  match incident.channel.1.1, incident.channel.1.2, external.channel.1.1.1 with
  | false, false, false => 1
  | false, true, false => Complex.I
  | false, true, true => 3 / 2
  | true, false, true => 1
  | true, true, false => 1
  | true, true, true => 3 * Complex.I / 2
  | _, _, _ => 0

/-- The explicit solved outgoing block `S F⁻¹ E_in` for the two exposed inputs. -/
def flatNetlistEliminationRegressionOutgoingSolution :
    ModeTransform flatNetlistEliminationRegression.ExternalIncident
      flatNetlistEliminationRegression.OutgoingIndex := fun outgoing external =>
  match outgoing.channel.1.1, outgoing.channel.1.2, external.channel.1.1.1 with
  | false, false, false => 1 + 4 * Complex.I
  | false, false, true => 6
  | false, true, false => 1
  | false, true, true => 3 * Complex.I / 2
  | true, false, false => 2
  | true, false, true => 4 * Complex.I
  | true, true, false => Complex.I
  | true, true, true => 3 / 2

/-!

## B. Exact feedback inverse and well-posedness

-/

/-- Component assembly recovers the explicit block-diagonal transform. -/
lemma flatNetlistEliminationRegression_scatteringTransform_eq :
    flatNetlistEliminationRegression.scatteringTransform =
      flatNetlistEliminationRegressionScatteringTransform := by
  classical
  ext output input
  rcases output with ⟨⟨⟨outputComponent, outputPort⟩, outputMode⟩⟩
  rcases input with ⟨⟨⟨inputComponent, inputPort⟩, inputMode⟩⟩
  change (flatNetlistEliminationRegression.components.portFamily
    outputComponent).Mode outputPort at outputMode
  change (flatNetlistEliminationRegression.components.portFamily
    inputComponent).Mode inputPort at inputMode
  rw [show (⟨⟨outputComponent, outputPort⟩, outputMode⟩ :
      flatNetlistEliminationRegression.Channel) =
        flatNetlistEliminationRegression.components.componentChannelEmbedding
          outputComponent ⟨outputPort, outputMode⟩ by rfl,
    show (⟨⟨inputComponent, inputPort⟩, inputMode⟩ :
      flatNetlistEliminationRegression.Channel) =
        flatNetlistEliminationRegression.components.componentChannelEmbedding
          inputComponent ⟨inputPort, inputMode⟩ by rfl]
  cases outputComponent <;> cases outputPort <;> cases outputMode <;>
    cases inputComponent <;> cases inputPort <;> cases inputMode
  all_goals first
    | rw [flatNetlistEliminationRegression.scatteringTransform_entry_same]
      rfl
    | rw [flatNetlistEliminationRegression.scatteringTransform_entry_of_ne
        (by decide)]
      rfl

/-- The derived partial routing recovers the explicit link-exchange transform. -/
lemma flatNetlistEliminationRegression_routingTransform_eq :
    flatNetlistEliminationRegression.routingTransform =
      flatNetlistEliminationRegressionRoutingTransform := by
  classical
  ext incident outgoing
  rcases incident with ⟨incident⟩
  rcases outgoing with ⟨outgoing⟩
  by_cases hOutgoingA : outgoing = flatNetlistEliminationRegressionALink
  · subst outgoing
    rw [← flatNetlistEliminationRegression_channelEmbedding_connectedA,
      flatNetlistEliminationRegression.routingTransform_entry_connected_column,
      flatNetlistEliminationRegression_mate_connectedA,
      flatNetlistEliminationRegression_channelEmbedding_connectedB,
      flatNetlistEliminationRegression_channelEmbedding_connectedA]
    by_cases hIncident : incident = flatNetlistEliminationRegressionBLink
    · subst incident
      simp [flatNetlistEliminationRegressionRoutingTransform,
        flatNetlistEliminationRegressionBLink]
    · rw [if_neg hIncident]
      rcases incident with ⟨⟨incidentComponent, incidentPort⟩, incidentMode⟩
      change (flatNetlistEliminationRegression.components.portFamily
        incidentComponent).Mode incidentPort at incidentMode
      cases incidentComponent <;> cases incidentPort <;> cases incidentMode
      all_goals first
        | rfl
        | exact (hIncident rfl).elim
  · by_cases hOutgoingB : outgoing = flatNetlistEliminationRegressionBLink
    · subst outgoing
      rw [← flatNetlistEliminationRegression_channelEmbedding_connectedB,
        flatNetlistEliminationRegression.routingTransform_entry_connected_column,
        flatNetlistEliminationRegression_mate_connectedB,
        flatNetlistEliminationRegression_channelEmbedding_connectedA,
        flatNetlistEliminationRegression_channelEmbedding_connectedB]
      by_cases hIncident : incident = flatNetlistEliminationRegressionALink
      · subst incident
        simp [flatNetlistEliminationRegressionRoutingTransform,
          flatNetlistEliminationRegressionALink]
      · rw [if_neg hIncident]
        rcases incident with ⟨⟨incidentComponent, incidentPort⟩, incidentMode⟩
        change (flatNetlistEliminationRegression.components.portFamily
          incidentComponent).Mode incidentPort at incidentMode
        cases incidentComponent <;> cases incidentPort <;> cases incidentMode
        all_goals first
          | rfl
          | exact (hIncident rfl).elim
    · have hNotRange : outgoing ∉
          Set.range flatNetlistEliminationRegression.connections.channelEmbedding := by
        rintro ⟨connected, hConnected⟩
        rcases connected with ⟨index, channel⟩
        rcases index with ⟨⟩
        rcases channel with mode | mode <;> cases mode
        · exact hOutgoingA hConnected.symm
        · exact hOutgoingB hConnected.symm
      rw [flatNetlistEliminationRegression.routingTransform_entry_of_outgoing_not_mem_range
        outgoing hNotRange]
      rcases incident with ⟨⟨incidentComponent, incidentPort⟩, incidentMode⟩
      rcases outgoing with ⟨⟨outgoingComponent, outgoingPort⟩, outgoingMode⟩
      change (flatNetlistEliminationRegression.components.portFamily
        incidentComponent).Mode incidentPort at incidentMode
      change (flatNetlistEliminationRegression.components.portFamily
        outgoingComponent).Mode outgoingPort at outgoingMode
      cases incidentComponent <;> cases incidentPort <;> cases incidentMode <;>
        cases outgoingComponent <;> cases outgoingPort <;> cases outgoingMode <;>
          simp [flatNetlistEliminationRegressionRoutingTransform,
            flatNetlistEliminationRegressionALink,
            flatNetlistEliminationRegressionBLink] at hOutgoingA hOutgoingB ⊢

/-- The derived incident exposure is the displayed coordinate injection. -/
lemma flatNetlistEliminationRegression_inputExposure_eq :
    flatNetlistEliminationRegression.inputExposure =
      flatNetlistEliminationRegressionInputExposure := by
  classical
  ext incident external
  rcases incident with ⟨incident⟩
  rcases external with ⟨external⟩
  rcases flatNetlistEliminationRegression_external_eq_a_or_b external with
    rfl | rfl
  · by_cases hIncident : incident = flatNetlistEliminationRegressionExternalA.1
    · subst incident
      simpa [flatNetlistEliminationRegressionInputExposure,
        flatNetlistEliminationRegressionExternalA,
        flatNetlistEliminationRegressionAExternal,
        flatNetlistRegressionPortAExternal] using
          flatNetlistEliminationRegression.inputExposure_entry_external
            flatNetlistEliminationRegressionExternalA
    · rw [flatNetlistEliminationRegression.inputExposure_entry_of_ne
        incident flatNetlistEliminationRegressionExternalA hIncident]
      rcases incident with ⟨⟨component, port⟩, mode⟩
      change (flatNetlistEliminationRegression.components.portFamily component).Mode port at mode
      cases component <;> cases port <;> cases mode
      all_goals
        simp [flatNetlistEliminationRegressionInputExposure,
          flatNetlistEliminationRegressionAExternal,
          flatNetlistRegressionPortAExternal] at hIncident ⊢
  · by_cases hIncident : incident = flatNetlistEliminationRegressionExternalB.1
    · subst incident
      simpa [flatNetlistEliminationRegressionInputExposure,
        flatNetlistEliminationRegressionExternalB,
        flatNetlistEliminationRegressionBExternal,
        flatNetlistRegressionPortBExternal] using
          flatNetlistEliminationRegression.inputExposure_entry_external
            flatNetlistEliminationRegressionExternalB
    · rw [flatNetlistEliminationRegression.inputExposure_entry_of_ne
        incident flatNetlistEliminationRegressionExternalB hIncident]
      rcases incident with ⟨⟨component, port⟩, mode⟩
      change (flatNetlistEliminationRegression.components.portFamily component).Mode port at mode
      cases component <;> cases port <;> cases mode
      all_goals
        simp [flatNetlistEliminationRegressionInputExposure,
          flatNetlistEliminationRegressionBExternal,
          flatNetlistRegressionPortBExternal] at hIncident ⊢

/-- The derived outgoing readout is the displayed coordinate restriction. -/
lemma flatNetlistEliminationRegression_outputReadout_eq :
    flatNetlistEliminationRegression.outputReadout =
      flatNetlistEliminationRegressionOutputReadout := by
  classical
  ext external outgoing
  rcases external with ⟨external⟩
  rcases outgoing with ⟨outgoing⟩
  rcases flatNetlistEliminationRegression_external_eq_a_or_b external with
    rfl | rfl
  · by_cases hOutgoing : outgoing = flatNetlistEliminationRegressionExternalA.1
    · subst outgoing
      simpa [flatNetlistEliminationRegressionOutputReadout,
        flatNetlistEliminationRegressionExternalA,
        flatNetlistEliminationRegressionAExternal,
        flatNetlistRegressionPortAExternal] using
          flatNetlistEliminationRegression.outputReadout_entry_external
            flatNetlistEliminationRegressionExternalA
    · rw [flatNetlistEliminationRegression.outputReadout_entry_of_ne
        flatNetlistEliminationRegressionExternalA outgoing hOutgoing]
      rcases outgoing with ⟨⟨component, port⟩, mode⟩
      change (flatNetlistEliminationRegression.components.portFamily component).Mode port at mode
      cases component <;> cases port <;> cases mode
      all_goals
        simp [flatNetlistEliminationRegressionOutputReadout,
          flatNetlistEliminationRegressionAExternal,
          flatNetlistRegressionPortAExternal] at hOutgoing ⊢
  · by_cases hOutgoing : outgoing = flatNetlistEliminationRegressionExternalB.1
    · subst outgoing
      simpa [flatNetlistEliminationRegressionOutputReadout,
        flatNetlistEliminationRegressionExternalB,
        flatNetlistEliminationRegressionBExternal,
        flatNetlistRegressionPortBExternal] using
          flatNetlistEliminationRegression.outputReadout_entry_external
            flatNetlistEliminationRegressionExternalB
    · rw [flatNetlistEliminationRegression.outputReadout_entry_of_ne
        flatNetlistEliminationRegressionExternalB outgoing hOutgoing]
      rcases outgoing with ⟨⟨component, port⟩, mode⟩
      change (flatNetlistEliminationRegression.components.portFamily component).Mode port at mode
      cases component <;> cases port <;> cases mode
      all_goals
        simp [flatNetlistEliminationRegressionOutputReadout,
          flatNetlistEliminationRegressionBExternal,
          flatNetlistRegressionPortBExternal] at hOutgoing ⊢

/-- The derived feedback operator has the displayed sparse matrix. -/
lemma flatNetlistEliminationRegression_feedbackOperator_eq :
    flatNetlistEliminationRegression.feedbackOperator =
      flatNetlistEliminationRegressionFeedback := by
  rw [FlatNetlist.feedbackOperator,
    flatNetlistEliminationRegression_routingTransform_eq,
    flatNetlistEliminationRegression_scatteringTransform_eq]
  ext output input
  by_cases hOutputInput : output = input
  all_goals
  rw [Matrix.sub_apply, Matrix.mul_apply,
    Fintype.sum_equiv
      (Outgoing.channelEquiv.trans
        flatNetlistEliminationRegression.components.channelEquiv.symm)
      (fun middle => flatNetlistEliminationRegressionRoutingTransform output middle *
        flatNetlistEliminationRegressionScatteringTransform middle input)
      (fun indexed =>
        flatNetlistEliminationRegressionRoutingTransform output
            (Outgoing.mk (flatNetlistEliminationRegression.components.channelEquiv indexed)) *
          flatNetlistEliminationRegressionScatteringTransform
            (Outgoing.mk (flatNetlistEliminationRegression.components.channelEquiv indexed)) input)
      (by intro x; cases x; rfl)]
  rcases output with ⟨outputChannel⟩
  rcases input with ⟨inputChannel⟩
  simp only [Incident.mk.injEq] at hOutputInput
  rcases outputChannel with ⟨⟨outputComponent, outputPort⟩, outputMode⟩
  rcases inputChannel with ⟨⟨inputComponent, inputPort⟩, inputMode⟩
  cases outputComponent <;> cases outputPort <;> cases outputMode <;>
    cases inputComponent <;> cases inputPort <;> cases inputMode
  all_goals
    simp [Matrix.one_apply, hOutputInput, Fintype.sum_sigma,
      ScatteringComponentFamily.channelEquiv,
      flatNetlistEliminationRegressionRoutingTransform,
      flatNetlistEliminationRegressionScatteringTransform,
      flatNetlistEliminationRegressionFeedback]
  all_goals try cases hOutputInput

/-- The displayed feedback matrix followed by its displayed inverse is the identity. -/
lemma flatNetlistEliminationRegression_feedback_mul_inverse :
    flatNetlistEliminationRegressionFeedback *
        flatNetlistEliminationRegressionInverse = 1 := by
  ext output input
  by_cases hOutputInput : output = input
  all_goals
  rw [Matrix.mul_apply]
  rw [Fintype.sum_equiv
    (Incident.channelEquiv.trans
      flatNetlistEliminationRegression.components.channelEquiv.symm)
    (fun middle => flatNetlistEliminationRegressionFeedback output middle *
      flatNetlistEliminationRegressionInverse middle input)
    (fun indexed => flatNetlistEliminationRegressionFeedback output
        (Incident.mk (flatNetlistEliminationRegression.components.channelEquiv indexed)) *
      flatNetlistEliminationRegressionInverse
        (Incident.mk (flatNetlistEliminationRegression.components.channelEquiv indexed)) input)
    (by intro x; cases x; rfl)]
  rcases output with ⟨outputChannel⟩
  rcases input with ⟨inputChannel⟩
  simp only [Incident.mk.injEq] at hOutputInput
  rcases outputChannel with ⟨⟨outputComponent, outputPort⟩, outputMode⟩
  rcases inputChannel with ⟨⟨inputComponent, inputPort⟩, inputMode⟩
  cases outputComponent <;> cases outputPort <;> cases outputMode <;>
    cases inputComponent <;> cases inputPort <;> cases inputMode
  all_goals
    simp [Matrix.one_apply, hOutputInput, Fintype.sum_sigma,
      ScatteringComponentFamily.channelEquiv,
      flatNetlistEliminationRegressionFeedback,
      flatNetlistEliminationRegressionInverse]
  all_goals try cases hOutputInput
  all_goals try exact (hOutputInput rfl).elim
  all_goals ring_nf
  all_goals rw [Complex.I_sq]
  all_goals ring

/-- The displayed inverse followed by the displayed feedback matrix is the identity. -/
lemma flatNetlistEliminationRegression_inverse_mul_feedback :
    flatNetlistEliminationRegressionInverse *
        flatNetlistEliminationRegressionFeedback = 1 := by
  ext output input
  by_cases hOutputInput : output = input
  all_goals
  rw [Matrix.mul_apply]
  rw [Fintype.sum_equiv
    (Incident.channelEquiv.trans
      flatNetlistEliminationRegression.components.channelEquiv.symm)
    (fun middle => flatNetlistEliminationRegressionInverse output middle *
      flatNetlistEliminationRegressionFeedback middle input)
    (fun indexed => flatNetlistEliminationRegressionInverse output
        (Incident.mk (flatNetlistEliminationRegression.components.channelEquiv indexed)) *
      flatNetlistEliminationRegressionFeedback
        (Incident.mk (flatNetlistEliminationRegression.components.channelEquiv indexed)) input)
    (by intro x; cases x; rfl)]
  rcases output with ⟨outputChannel⟩
  rcases input with ⟨inputChannel⟩
  simp only [Incident.mk.injEq] at hOutputInput
  rcases outputChannel with ⟨⟨outputComponent, outputPort⟩, outputMode⟩
  rcases inputChannel with ⟨⟨inputComponent, inputPort⟩, inputMode⟩
  cases outputComponent <;> cases outputPort <;> cases outputMode <;>
    cases inputComponent <;> cases inputPort <;> cases inputMode
  all_goals
    simp [Matrix.one_apply, hOutputInput, Fintype.sum_sigma,
      ScatteringComponentFamily.channelEquiv,
      flatNetlistEliminationRegressionFeedback,
      flatNetlistEliminationRegressionInverse]
  all_goals try cases hOutputInput
  all_goals try exact (hOutputInput rfl).elim
  all_goals ring_nf
  all_goals rw [Complex.I_sq]
  all_goals ring

/-- The hostile shared-link fixture is well posed without any contraction assumption. -/
lemma flatNetlistEliminationRegression_isWellPosed :
    flatNetlistEliminationRegression.IsWellPosed := by
  apply flatNetlistEliminationRegression.isWellPosed_iff_feedbackOperator_injective.mpr
  intro first second hEqual
  have hMapped := congrArg
    flatNetlistEliminationRegressionInverse.toLinearMap hEqual
  simpa only [← ModeTransform.toLinearMap_mul_apply,
    flatNetlistEliminationRegression_feedbackOperator_eq,
    flatNetlistEliminationRegression_inverse_mul_feedback,
    ModeTransform.toLinearMap, Matrix.toLpLin_one, LinearMap.id_apply] using hMapped

/-- The proof-gated inverse is exactly the displayed inverse matrix. -/
lemma flatNetlistEliminationRegression_feedbackInverse_eq :
    flatNetlistEliminationRegression.feedbackInverse
        flatNetlistEliminationRegression_isWellPosed =
      flatNetlistEliminationRegressionInverse := by
  calc
    flatNetlistEliminationRegression.feedbackInverse
          flatNetlistEliminationRegression_isWellPosed =
        flatNetlistEliminationRegression.feedbackInverse
            flatNetlistEliminationRegression_isWellPosed * 1 :=
      (Matrix.mul_one _).symm
    _ = flatNetlistEliminationRegression.feedbackInverse
          flatNetlistEliminationRegression_isWellPosed *
            (flatNetlistEliminationRegressionFeedback *
              flatNetlistEliminationRegressionInverse) := by
      rw [flatNetlistEliminationRegression_feedback_mul_inverse]
    _ = (flatNetlistEliminationRegression.feedbackInverse
            flatNetlistEliminationRegression_isWellPosed *
          flatNetlistEliminationRegression.feedbackOperator) *
            flatNetlistEliminationRegressionInverse := by
      rw [flatNetlistEliminationRegression_feedbackOperator_eq, Matrix.mul_assoc]
    _ = flatNetlistEliminationRegressionInverse := by
      rw [flatNetlistEliminationRegression.feedbackInverse_mul_feedbackOperator,
        Matrix.one_mul]

/-!

## C. Complete solution and external response

-/

/-- The displayed feedback inverse and exposure give the displayed incident solution block. -/
lemma flatNetlistEliminationRegression_inverse_mul_inputExposure :
    flatNetlistEliminationRegressionInverse *
        flatNetlistEliminationRegressionInputExposure =
      flatNetlistEliminationRegressionIncidentSolution := by
  ext incident external
  rcases incident with ⟨⟨⟨component, port⟩, mode⟩⟩
  change (flatNetlistEliminationRegression.components.portFamily component).Mode port at mode
  rcases external with ⟨external⟩
  rcases flatNetlistEliminationRegression_external_eq_a_or_b external with
    rfl | rfl
  all_goals
    cases component <;> cases port <;> cases mode
  all_goals
    rw [Matrix.mul_apply, ← (flatNetlistEliminationRegression.components.channelEquiv.trans
      Incident.channelEquiv.symm).sum_comp]
  all_goals
    simp [Fintype.sum_sigma, ScatteringComponentFamily.channelEquiv,
      flatNetlistEliminationRegressionInverse,
      flatNetlistEliminationRegressionInputExposure,
      flatNetlistEliminationRegressionIncidentSolution]

/-- Component scattering sends the incident solution block to the displayed outgoing block. -/
lemma flatNetlistEliminationRegression_scattering_mul_incidentSolution :
    flatNetlistEliminationRegressionScatteringTransform *
        flatNetlistEliminationRegressionIncidentSolution =
      flatNetlistEliminationRegressionOutgoingSolution := by
  ext outgoing external
  rcases outgoing with ⟨⟨⟨component, port⟩, mode⟩⟩
  change (flatNetlistEliminationRegression.components.portFamily component).Mode port at mode
  rcases external with ⟨external⟩
  rcases flatNetlistEliminationRegression_external_eq_a_or_b external with
    rfl | rfl
  all_goals
    cases component <;> cases port <;> cases mode
  all_goals
    rw [Matrix.mul_apply, ← (flatNetlistEliminationRegression.components.channelEquiv.trans
      Incident.channelEquiv.symm).sum_comp]
  all_goals
    simp [Fintype.sum_sigma, ScatteringComponentFamily.channelEquiv,
      flatNetlistEliminationRegressionScatteringTransform,
      flatNetlistEliminationRegressionIncidentSolution,
      flatNetlistEliminationRegressionOutgoingSolution]
  all_goals ring_nf
  all_goals rw [Complex.I_sq]
  all_goals ring

/-- External readout selects the displayed two-by-two response from the outgoing solution. -/
lemma flatNetlistEliminationRegression_outputReadout_mul_outgoingSolution :
    flatNetlistEliminationRegressionOutputReadout *
        flatNetlistEliminationRegressionOutgoingSolution =
      flatNetlistEliminationRegressionResponse := by
  ext output input
  rcases output with ⟨output⟩
  rcases input with ⟨input⟩
  rcases flatNetlistEliminationRegression_external_eq_a_or_b output with
    rfl | rfl <;>
    rcases flatNetlistEliminationRegression_external_eq_a_or_b input with
      rfl | rfl
  all_goals
    rw [Matrix.mul_apply, ← (flatNetlistEliminationRegression.components.channelEquiv.trans
      Outgoing.channelEquiv.symm).sum_comp]
  all_goals
    simp [Fintype.sum_sigma, ScatteringComponentFamily.channelEquiv,
      flatNetlistEliminationRegressionOutputReadout,
      flatNetlistEliminationRegressionOutgoingSolution,
      flatNetlistEliminationRegressionResponse]

/-- The exact well-posed external response pins every entry of the four-factor formula. -/
lemma flatNetlistEliminationRegression_responseTransform_eq :
    flatNetlistEliminationRegression.responseTransform
        flatNetlistEliminationRegression_isWellPosed =
      flatNetlistEliminationRegressionResponse := by
  rw [flatNetlistEliminationRegression.responseTransform_eq_blockFormula,
    flatNetlistEliminationRegression.responseBlockFormula_eq,
    flatNetlistEliminationRegression_outputReadout_eq,
    flatNetlistEliminationRegression_feedbackInverse_eq,
    flatNetlistEliminationRegression_scatteringTransform_eq,
    flatNetlistEliminationRegression_inputExposure_eq]
  simp only [Matrix.mul_assoc,
    flatNetlistEliminationRegression_inverse_mul_inputExposure,
    flatNetlistEliminationRegression_scattering_mul_incidentSolution,
    flatNetlistEliminationRegression_outputReadout_mul_outgoingSolution]

/-- The response is asymmetric and therefore detects a transposed external transfer matrix. -/
lemma flatNetlistEliminationRegression_response_asymmetric :
    flatNetlistEliminationRegressionResponse
        (Outgoing.mk flatNetlistEliminationRegressionExternalB)
        (Incident.mk flatNetlistEliminationRegressionExternalA) ≠
      flatNetlistEliminationRegressionResponse
        (Outgoing.mk flatNetlistEliminationRegressionExternalA)
        (Incident.mk flatNetlistEliminationRegressionExternalB) := by
  norm_num [flatNetlistEliminationRegressionResponse]

/-!

## D. Singular negative control

-/

/-- Aggregate channels in the singular negative control are finite. -/
local instance flatNetlistRegressionChannelFintypeForElimination :
    Fintype flatNetlistRegression.Channel :=
  Fintype.ofEquiv flatNetlistRegressionComponents.IndexedChannel
    flatNetlistRegressionComponents.channelEquiv

/-- Connected channels in the singular negative control are finite. -/
local instance flatNetlistRegressionConnectedChannelFintypeForElimination :
    Fintype flatNetlistRegression.ConnectedChannel := by
  change Fintype (Σ _ : Unit, Unit ⊕ Unit)
  infer_instance

/-- The original shared-link fixture is not well posed because its feedback operator has a
nonzero homogeneous kernel state. -/
lemma flatNetlistRegression_not_isWellPosed : ¬flatNetlistRegression.IsWellPosed := by
  rw [flatNetlistRegression.isWellPosed_iff_feedbackOperator_injective]
  exact flatNetlistRegression_feedbackOperator_not_injective

/-!

## E. Wiring-presentation invariance

-/

/-- Endpoint-exchanged connected channels in the well-posed fixture are finite. -/
local instance flatNetlistEliminationRegressionSymmConnectedChannelFintype :
    Fintype flatNetlistEliminationRegression.connections.symm.Channel := by
  change Fintype (Σ _ : Unit, Unit ⊕ Unit)
  infer_instance

/-- Endpoint-exchanged connected channels in the singular fixture are finite. -/
local instance flatNetlistRegressionSymmConnectedChannelFintype :
    Fintype flatNetlistRegression.connections.symm.Channel := by
  change Fintype (Σ _ : Unit, Unit ⊕ Unit)
  infer_instance

/-- Exchanging the presentation of the well-posed fixture's link preserves well-posedness. -/
lemma flatNetlistEliminationRegression_symmConnections_isWellPosed :
    flatNetlistEliminationRegression.symmConnections.IsWellPosed :=
  (flatNetlistEliminationRegression.isWellPosed_withConnections_iff
    flatNetlistEliminationRegression.connections.symm
    (PortConnectionFamily.WiringEquiv.ofSymm
      flatNetlistEliminationRegression.connections)).mpr
        flatNetlistEliminationRegression_isWellPosed

/-- The response of the endpoint-exchanged fixture is the same exact response under the canonical
external relabelling. -/
lemma flatNetlistEliminationRegression_responseTransform_symmConnections :
    flatNetlistEliminationRegression.symmConnections.responseTransform
        flatNetlistEliminationRegression_symmConnections_isWellPosed =
      flatNetlistEliminationRegressionResponse.reindex
        (PortConnectionFamily.WiringEquiv.externalIncidentEquiv
          (PortConnectionFamily.WiringEquiv.ofSymm
            flatNetlistEliminationRegression.connections))
        (PortConnectionFamily.WiringEquiv.externalOutgoingEquiv
          (PortConnectionFamily.WiringEquiv.ofSymm
            flatNetlistEliminationRegression.connections)) := by
  rw [flatNetlistEliminationRegression.responseTransform_withConnections
    flatNetlistEliminationRegression.connections.symm
    (PortConnectionFamily.WiringEquiv.ofSymm
      flatNetlistEliminationRegression.connections)
    flatNetlistEliminationRegression_symmConnections_isWellPosed
    flatNetlistEliminationRegression_isWellPosed,
    flatNetlistEliminationRegression_responseTransform_eq]

/-- Exchanging the presentation of the singular fixture's link cannot create well-posedness. -/
lemma flatNetlistRegression_symmConnections_not_isWellPosed :
    ¬flatNetlistRegression.symmConnections.IsWellPosed := by
  rw [flatNetlistRegression.isWellPosed_withConnections_iff
    flatNetlistRegression.connections.symm
    (PortConnectionFamily.WiringEquiv.ofSymm flatNetlistRegression.connections)]
  exact flatNetlistRegression_not_isWellPosed

end

end Optics
