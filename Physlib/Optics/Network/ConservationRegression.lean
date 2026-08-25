/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.Coherency
public import Physlib.Optics.Network.FlatNetlistEliminationRegression

/-!
# Regression tests for conservation under interconnection

## i. Overview

Two reflectionless two-port components are wired through one internal link. Each component matrix
is unitary in its own right, with the second carrying a quarter-turn phase so that a transposed or
conjugated convention is detectable. The fixture reuses the shared-link topology of the existing
flat-netlist regressions and adds the two conservation checks required by row `N-03`.

The first check proves that the complete external scattering matrix is unitary *from* component
unitarity, through `FlatNetlist.externalScatteringMatrix_isLossless_of_components_isLossless`,
without ever inspecting the external response. The second check independently pins every entry of
that response to a hand-computed value and confirms the unit column powers by arithmetic, so a
wrong-but-unitary response cannot pass.

The incoherent check exhibits two decorrelated contributions whose output powers add exactly, with
no interference term, and shows the same two contributions taken coherently differ by a nonzero
amount, so the vanishing of the cross terms is a consequence of the decorrelation hypothesis
rather than of the fixture being degenerate.

## ii. Scope

These are exact algebraic fixtures at one frequency. Nothing here claims that the components are
physically realizable devices, that the modal power convention has been normalized to
electromagnetic flux, or that the fixture is reciprocal.

## iii. Table of contents

- A. A lossless shared-link cascade
- B. Component unitarity
- C. Exact feedback inverse and well-posedness
- D. System losslessness from component unitarity
- E. The hand-computed external response
- F. Coherent and decorrelated two-input power

-/

@[expose] public section

namespace Optics

open scoped ComplexConjugate ComplexOrder

noncomputable section

/-!

## A. A lossless shared-link cascade

-/

/-- The two lossless fixture component matrices. In local `[external, link]` order they are
`[[0, 1], [1, 0]]` and `[[0, I], [I, 0]]`: each is a reflectionless unit-transmission two port,
the second with a quarter-turn transmitted phase. -/
def conservationRegressionScattering
    (component : Bool) : ScatteringMatrix flatNetlistRegressionPortFamily.Channel where
  toModeTransform := fun output input =>
    match component, output.1, input.1 with
    | false, false, false => 0
    | false, false, true => 1
    | false, true, false => 1
    | false, true, true => 0
    | true, false, false => 0
    | true, false, true => Complex.I
    | true, true, false => Complex.I
    | true, true, true => 0

/-- The two lossless fixture components before wiring. -/
abbrev conservationRegressionComponents : ScatteringComponentFamily where
  Component := Bool
  portFamily := fun _ => flatNetlistRegressionPortFamily
  scattering := conservationRegressionScattering

/-- The lossless fixture reuses the exact one-link connection topology of the earlier
regressions. -/
abbrev conservationRegression : FlatNetlist where
  components := conservationRegressionComponents
  Connection := Unit
  connections := flatNetlistRegressionConnections

/-- Every local component-channel family in the lossless fixture is finite. -/
local instance conservationRegressionLocalChannelFintype (component : Bool) :
    Fintype (conservationRegressionComponents.portFamily component).Channel := by
  change Fintype (Σ _ : Bool, Unit)
  infer_instance

/-- Every local component-channel family in the lossless fixture has decidable equality. -/
local instance conservationRegressionLocalChannelDecidableEq (component : Bool) :
    DecidableEq (conservationRegressionComponents.portFamily component).Channel :=
  Classical.decEq _

/-- Aggregate channels in the lossless fixture are finite. -/
local instance conservationRegressionChannelFintype :
    Fintype conservationRegression.Channel := by
  change Fintype (Σ _ : (Σ _ : Bool, Bool), Unit)
  infer_instance

/-- Aggregate channels in the lossless fixture have decidable equality. -/
local instance conservationRegressionChannelDecidableEq :
    DecidableEq conservationRegression.Channel := Classical.decEq _

/-- Connected channels in the lossless fixture are finite. -/
local instance conservationRegressionConnectedChannelFintype :
    Fintype conservationRegression.ConnectedChannel := by
  change Fintype (Σ _ : Unit, Unit ⊕ Unit)
  infer_instance

/-- Connected channels in the lossless fixture have decidable equality. -/
local instance conservationRegressionConnectedChannelDecidableEq :
    DecidableEq conservationRegression.ConnectedChannel := Classical.decEq _

/-- External channels in the lossless fixture are finite. -/
local instance conservationRegressionExternalChannelFintype :
    Fintype conservationRegression.ExternalChannel := by
  classical
  infer_instance

/-- The first external ambient channel of the lossless fixture. -/
abbrev conservationRegressionAExternal : conservationRegression.Channel :=
  ⟨flatNetlistRegressionPortAExternal, ()⟩

/-- The first internal-link ambient channel of the lossless fixture. -/
abbrev conservationRegressionALink : conservationRegression.Channel :=
  ⟨flatNetlistRegressionPortALink, ()⟩

/-- The second external ambient channel of the lossless fixture. -/
abbrev conservationRegressionBExternal : conservationRegression.Channel :=
  ⟨flatNetlistRegressionPortBExternal, ()⟩

/-- The second internal-link ambient channel of the lossless fixture. -/
abbrev conservationRegressionBLink : conservationRegression.Channel :=
  ⟨flatNetlistRegressionPortBLink, ()⟩

/-- The first connected link channel in the lossless fixture. -/
abbrev conservationRegressionConnectedA : conservationRegression.ConnectedChannel :=
  flatNetlistRegressionConnectedA

/-- The second connected link channel in the lossless fixture. -/
abbrev conservationRegressionConnectedB : conservationRegression.ConnectedChannel :=
  flatNetlistRegressionConnectedB

/-- The first external ambient channel is outside the internal connection range. -/
lemma conservationRegression_aExternal_not_mem_range :
    conservationRegressionAExternal ∉
      Set.range conservationRegression.connections.channelEmbedding := by
  rintro ⟨channel, hChannel⟩
  rcases channel with ⟨index, channel⟩
  rcases index with ⟨⟩
  rcases channel with mode | mode <;> cases mode
  · have hPort := congrArg (fun selected => selected.1.2) hChannel
    exact Bool.noConfusion hPort
  · have hComponent := congrArg (fun selected => selected.1.1) hChannel
    exact Bool.noConfusion hComponent

/-- The second external ambient channel is outside the internal connection range. -/
lemma conservationRegression_bExternal_not_mem_range :
    conservationRegressionBExternal ∉
      Set.range conservationRegression.connections.channelEmbedding := by
  rintro ⟨channel, hChannel⟩
  rcases channel with ⟨index, channel⟩
  rcases index with ⟨⟩
  rcases channel with mode | mode <;> cases mode
  · have hComponent := congrArg (fun selected => selected.1.1) hChannel
    exact Bool.noConfusion hComponent
  · have hPort := congrArg (fun selected => selected.1.2) hChannel
    exact Bool.noConfusion hPort

/-- The packaged first external channel of the lossless fixture. -/
abbrev conservationRegressionExternalA : conservationRegression.ExternalChannel :=
  ⟨conservationRegressionAExternal, conservationRegression_aExternal_not_mem_range⟩

/-- The packaged second external channel of the lossless fixture. -/
abbrev conservationRegressionExternalB : conservationRegression.ExternalChannel :=
  ⟨conservationRegressionBExternal, conservationRegression_bExternal_not_mem_range⟩

/-- The first connected channel embeds as the first component's link channel. -/
lemma conservationRegression_channelEmbedding_connectedA :
    conservationRegression.connections.channelEmbedding conservationRegressionConnectedA =
      conservationRegressionALink := rfl

/-- The second connected channel embeds as the second component's link channel. -/
lemma conservationRegression_channelEmbedding_connectedB :
    conservationRegression.connections.channelEmbedding conservationRegressionConnectedB =
      conservationRegressionBLink := rfl

/-- The mate of the first connected endpoint is the second connected endpoint. -/
@[simp]
lemma conservationRegression_mate_connectedA :
    conservationRegression.connections.mateEquiv conservationRegressionConnectedA =
      conservationRegressionConnectedB := rfl

/-- The mate of the second connected endpoint is the first connected endpoint. -/
@[simp]
lemma conservationRegression_mate_connectedB :
    conservationRegression.connections.mateEquiv conservationRegressionConnectedB =
      conservationRegressionConnectedA := rfl

/-- Every exposed channel is one of the two declared external endpoints. -/
lemma conservationRegression_external_eq_a_or_b
    (channel : conservationRegression.ExternalChannel) :
    channel = conservationRegressionExternalA ∨ channel = conservationRegressionExternalB := by
  rcases channel with ⟨⟨⟨component, port⟩, mode⟩, hExternal⟩
  change (conservationRegression.components.portFamily component).Mode port at mode
  cases component <;> cases port <;> cases mode
  · left
    apply Subtype.ext
    rfl
  · exfalso
    exact hExternal ⟨conservationRegressionConnectedA,
      conservationRegression_channelEmbedding_connectedA⟩
  · right
    apply Subtype.ext
    rfl
  · exfalso
    exact hExternal ⟨conservationRegressionConnectedB,
      conservationRegression_channelEmbedding_connectedB⟩

/-!

## B. Component unitarity

-/

/-- Each fixture component matrix is unitary, hence lossless. -/
lemma conservationRegressionScattering_isLossless
    (component : conservationRegression.components.Component) :
    (conservationRegression.components.scattering component).IsLossless := by
  rw [ScatteringMatrix.IsLossless, Matrix.mem_unitaryGroup_iff',
    Matrix.star_eq_conjTranspose]
  ext output input
  rw [Matrix.mul_apply]
  rcases output with ⟨outputPort, outputMode⟩
  rcases input with ⟨inputPort, inputMode⟩
  cases component <;> cases outputPort <;> cases outputMode <;>
    cases inputPort <;> cases inputMode
  all_goals
    simp [Fintype.sum_sigma, Matrix.conjTranspose, Matrix.transpose, Matrix.of_apply,
      conservationRegressionScattering]

/-!

## C. Exact feedback inverse and well-posedness

-/

/-- The explicit assembled component transform in aggregate endpoint coordinates. -/
def conservationRegressionScatteringTransform :
    ModeTransform conservationRegression.IncidentIndex
      conservationRegression.OutgoingIndex := fun output input =>
  match output.channel.1.1, output.channel.1.2, input.channel.1.1, input.channel.1.2 with
  | false, false, false, true => 1
  | false, true, false, false => 1
  | true, false, true, true => Complex.I
  | true, true, true, false => Complex.I
  | _, _, _, _ => 0

/-- The explicit partial-routing transform, exchanging only the two link endpoints. -/
def conservationRegressionRoutingTransform :
    ModeTransform conservationRegression.OutgoingIndex
      conservationRegression.IncidentIndex := fun incident outgoing =>
  match incident.channel.1.1, incident.channel.1.2,
      outgoing.channel.1.1, outgoing.channel.1.2 with
  | false, true, true, true => 1
  | true, true, false, true => 1
  | _, _, _, _ => 0

/-- The explicit injection of the two exposed incident coordinates into the aggregate boundary. -/
def conservationRegressionInputExposure :
    ModeTransform conservationRegression.ExternalIncident
      conservationRegression.IncidentIndex := fun incident external =>
  match incident.channel.1.1, incident.channel.1.2, external.channel.1.1.1 with
  | false, false, false => 1
  | true, false, true => 1
  | _, _, _ => 0

/-- The explicit readout of the two exposed outgoing coordinates from the aggregate boundary. -/
def conservationRegressionOutputReadout :
    ModeTransform conservationRegression.OutgoingIndex
      conservationRegression.ExternalOutgoing := fun external outgoing =>
  match external.channel.1.1.1, outgoing.channel.1.1, outgoing.channel.1.2 with
  | false, false, false => 1
  | true, true, false => 1
  | _, _, _ => 0

/-- The exact feedback matrix `1 - C * S` in aggregate order `(A.ext, A.link, B.ext, B.link)`. -/
def conservationRegressionFeedback :
    ModeTransform conservationRegression.IncidentIndex
      conservationRegression.IncidentIndex := fun output input =>
  match output.channel.1.1, output.channel.1.2, input.channel.1.1, input.channel.1.2 with
  | false, false, false, false => 1
  | false, true, false, true => 1
  | false, true, true, false => -Complex.I
  | true, false, true, false => 1
  | true, true, true, true => 1
  | true, true, false, false => -1
  | _, _, _, _ => 0

/-- The displayed inverse feedback matrix `1 + C * S` in the same aggregate order. -/
def conservationRegressionInverse :
    ModeTransform conservationRegression.IncidentIndex
      conservationRegression.IncidentIndex := fun output input =>
  match output.channel.1.1, output.channel.1.2, input.channel.1.1, input.channel.1.2 with
  | false, false, false, false => 1
  | false, true, false, true => 1
  | false, true, true, false => Complex.I
  | true, false, true, false => 1
  | true, true, true, true => 1
  | true, true, false, false => 1
  | _, _, _, _ => 0

/-- The explicit solved incident block `F⁻¹ E_in` for the two exposed inputs. -/
def conservationRegressionIncidentSolution :
    ModeTransform conservationRegression.ExternalIncident
      conservationRegression.IncidentIndex := fun incident external =>
  match incident.channel.1.1, incident.channel.1.2, external.channel.1.1.1 with
  | false, false, false => 1
  | false, true, true => Complex.I
  | true, false, true => 1
  | true, true, false => 1
  | _, _, _ => 0

/-- The explicit solved outgoing block `S F⁻¹ E_in` for the two exposed inputs. -/
def conservationRegressionOutgoingSolution :
    ModeTransform conservationRegression.ExternalIncident
      conservationRegression.OutgoingIndex := fun outgoing external =>
  match outgoing.channel.1.1, outgoing.channel.1.2, external.channel.1.1.1 with
  | false, false, true => Complex.I
  | false, true, false => 1
  | true, false, false => Complex.I
  | true, true, true => Complex.I
  | _, _, _ => 0

/-- The expected external response in exposed order `(A.ext, B.ext)`, namely `[[0, I], [I, 0]]`. -/
def conservationRegressionResponse :
    ModeTransform conservationRegression.ExternalIncident
      conservationRegression.ExternalOutgoing := fun output input =>
  match output.channel.1.1.1, input.channel.1.1.1 with
  | false, false => 0
  | false, true => Complex.I
  | true, false => Complex.I
  | true, true => 0

/-- Component assembly recovers the explicit block-diagonal transform. -/
lemma conservationRegression_scatteringTransform_eq :
    conservationRegression.scatteringTransform =
      conservationRegressionScatteringTransform := by
  classical
  ext output input
  rcases output with ⟨⟨⟨outputComponent, outputPort⟩, outputMode⟩⟩
  rcases input with ⟨⟨⟨inputComponent, inputPort⟩, inputMode⟩⟩
  change (conservationRegression.components.portFamily
    outputComponent).Mode outputPort at outputMode
  change (conservationRegression.components.portFamily
    inputComponent).Mode inputPort at inputMode
  rw [show (⟨⟨outputComponent, outputPort⟩, outputMode⟩ : conservationRegression.Channel) =
        conservationRegression.components.componentChannelEmbedding
          outputComponent ⟨outputPort, outputMode⟩ by rfl,
    show (⟨⟨inputComponent, inputPort⟩, inputMode⟩ : conservationRegression.Channel) =
        conservationRegression.components.componentChannelEmbedding
          inputComponent ⟨inputPort, inputMode⟩ by rfl]
  cases outputComponent <;> cases outputPort <;> cases outputMode <;>
    cases inputComponent <;> cases inputPort <;> cases inputMode
  all_goals first
    | rw [conservationRegression.scatteringTransform_entry_same]
      rfl
    | rw [conservationRegression.scatteringTransform_entry_of_ne (by decide)]
      rfl

/-- The derived partial routing recovers the explicit link-exchange transform. -/
lemma conservationRegression_routingTransform_eq :
    conservationRegression.routingTransform = conservationRegressionRoutingTransform := by
  classical
  ext incident outgoing
  rcases incident with ⟨incident⟩
  rcases outgoing with ⟨outgoing⟩
  by_cases hOutgoingA : outgoing = conservationRegressionALink
  · subst outgoing
    rw [← conservationRegression_channelEmbedding_connectedA,
      conservationRegression.routingTransform_entry_connected_column,
      conservationRegression_mate_connectedA,
      conservationRegression_channelEmbedding_connectedB,
      conservationRegression_channelEmbedding_connectedA]
    by_cases hIncident : incident = conservationRegressionBLink
    · subst incident
      simp [conservationRegressionRoutingTransform, conservationRegressionBLink]
    · rw [if_neg hIncident]
      rcases incident with ⟨⟨incidentComponent, incidentPort⟩, incidentMode⟩
      change (conservationRegression.components.portFamily
        incidentComponent).Mode incidentPort at incidentMode
      cases incidentComponent <;> cases incidentPort <;> cases incidentMode
      all_goals first
        | rfl
        | exact (hIncident rfl).elim
  · by_cases hOutgoingB : outgoing = conservationRegressionBLink
    · subst outgoing
      rw [← conservationRegression_channelEmbedding_connectedB,
        conservationRegression.routingTransform_entry_connected_column,
        conservationRegression_mate_connectedB,
        conservationRegression_channelEmbedding_connectedA,
        conservationRegression_channelEmbedding_connectedB]
      by_cases hIncident : incident = conservationRegressionALink
      · subst incident
        simp [conservationRegressionRoutingTransform, conservationRegressionALink]
      · rw [if_neg hIncident]
        rcases incident with ⟨⟨incidentComponent, incidentPort⟩, incidentMode⟩
        change (conservationRegression.components.portFamily
          incidentComponent).Mode incidentPort at incidentMode
        cases incidentComponent <;> cases incidentPort <;> cases incidentMode
        all_goals first
          | rfl
          | exact (hIncident rfl).elim
    · have hNotRange : outgoing ∉
          Set.range conservationRegression.connections.channelEmbedding := by
        rintro ⟨connected, hConnected⟩
        rcases connected with ⟨index, channel⟩
        rcases index with ⟨⟩
        rcases channel with mode | mode <;> cases mode
        · exact hOutgoingA hConnected.symm
        · exact hOutgoingB hConnected.symm
      rw [conservationRegression.routingTransform_entry_of_outgoing_not_mem_range
        outgoing hNotRange]
      rcases incident with ⟨⟨incidentComponent, incidentPort⟩, incidentMode⟩
      rcases outgoing with ⟨⟨outgoingComponent, outgoingPort⟩, outgoingMode⟩
      change (conservationRegression.components.portFamily
        incidentComponent).Mode incidentPort at incidentMode
      change (conservationRegression.components.portFamily
        outgoingComponent).Mode outgoingPort at outgoingMode
      cases incidentComponent <;> cases incidentPort <;> cases incidentMode <;>
        cases outgoingComponent <;> cases outgoingPort <;> cases outgoingMode <;>
          simp [conservationRegressionRoutingTransform, conservationRegressionALink,
            conservationRegressionBLink] at hOutgoingA hOutgoingB ⊢

/-- The derived incident exposure is the displayed coordinate injection. -/
lemma conservationRegression_inputExposure_eq :
    conservationRegression.inputExposure = conservationRegressionInputExposure := by
  classical
  ext incident external
  rcases incident with ⟨incident⟩
  rcases external with ⟨external⟩
  rcases conservationRegression_external_eq_a_or_b external with rfl | rfl
  · by_cases hIncident : incident = conservationRegressionExternalA.1
    · subst incident
      simpa [conservationRegressionInputExposure, conservationRegressionExternalA,
        conservationRegressionAExternal, flatNetlistRegressionPortAExternal] using
          conservationRegression.inputExposure_entry_external conservationRegressionExternalA
    · rw [conservationRegression.inputExposure_entry_of_ne
        incident conservationRegressionExternalA hIncident]
      rcases incident with ⟨⟨component, port⟩, mode⟩
      change (conservationRegression.components.portFamily component).Mode port at mode
      cases component <;> cases port <;> cases mode
      all_goals
        simp [conservationRegressionInputExposure, conservationRegressionAExternal,
          flatNetlistRegressionPortAExternal] at hIncident ⊢
  · by_cases hIncident : incident = conservationRegressionExternalB.1
    · subst incident
      simpa [conservationRegressionInputExposure, conservationRegressionExternalB,
        conservationRegressionBExternal, flatNetlistRegressionPortBExternal] using
          conservationRegression.inputExposure_entry_external conservationRegressionExternalB
    · rw [conservationRegression.inputExposure_entry_of_ne
        incident conservationRegressionExternalB hIncident]
      rcases incident with ⟨⟨component, port⟩, mode⟩
      change (conservationRegression.components.portFamily component).Mode port at mode
      cases component <;> cases port <;> cases mode
      all_goals
        simp [conservationRegressionInputExposure, conservationRegressionBExternal,
          flatNetlistRegressionPortBExternal] at hIncident ⊢

/-- The derived outgoing readout is the displayed coordinate restriction. -/
lemma conservationRegression_outputReadout_eq :
    conservationRegression.outputReadout = conservationRegressionOutputReadout := by
  classical
  ext external outgoing
  rcases external with ⟨external⟩
  rcases outgoing with ⟨outgoing⟩
  rcases conservationRegression_external_eq_a_or_b external with rfl | rfl
  · by_cases hOutgoing : outgoing = conservationRegressionExternalA.1
    · subst outgoing
      simpa [conservationRegressionOutputReadout, conservationRegressionExternalA,
        conservationRegressionAExternal, flatNetlistRegressionPortAExternal] using
          conservationRegression.outputReadout_entry_external conservationRegressionExternalA
    · rw [conservationRegression.outputReadout_entry_of_ne
        conservationRegressionExternalA outgoing hOutgoing]
      rcases outgoing with ⟨⟨component, port⟩, mode⟩
      change (conservationRegression.components.portFamily component).Mode port at mode
      cases component <;> cases port <;> cases mode
      all_goals
        simp [conservationRegressionOutputReadout, conservationRegressionAExternal,
          flatNetlistRegressionPortAExternal] at hOutgoing ⊢
  · by_cases hOutgoing : outgoing = conservationRegressionExternalB.1
    · subst outgoing
      simpa [conservationRegressionOutputReadout, conservationRegressionExternalB,
        conservationRegressionBExternal, flatNetlistRegressionPortBExternal] using
          conservationRegression.outputReadout_entry_external conservationRegressionExternalB
    · rw [conservationRegression.outputReadout_entry_of_ne
        conservationRegressionExternalB outgoing hOutgoing]
      rcases outgoing with ⟨⟨component, port⟩, mode⟩
      change (conservationRegression.components.portFamily component).Mode port at mode
      cases component <;> cases port <;> cases mode
      all_goals
        simp [conservationRegressionOutputReadout, conservationRegressionBExternal,
          flatNetlistRegressionPortBExternal] at hOutgoing ⊢

/-- The derived feedback operator has the displayed sparse matrix. -/
lemma conservationRegression_feedbackOperator_eq :
    conservationRegression.feedbackOperator = conservationRegressionFeedback := by
  rw [FlatNetlist.feedbackOperator, conservationRegression_routingTransform_eq,
    conservationRegression_scatteringTransform_eq]
  ext output input
  by_cases hOutputInput : output = input
  all_goals
  rw [Matrix.sub_apply, Matrix.mul_apply,
    Fintype.sum_equiv
      (Outgoing.channelEquiv.trans conservationRegression.components.channelEquiv.symm)
      (fun middle => conservationRegressionRoutingTransform output middle *
        conservationRegressionScatteringTransform middle input)
      (fun indexed =>
        conservationRegressionRoutingTransform output
            (Outgoing.mk (conservationRegression.components.channelEquiv indexed)) *
          conservationRegressionScatteringTransform
            (Outgoing.mk (conservationRegression.components.channelEquiv indexed)) input)
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
      conservationRegressionRoutingTransform,
      conservationRegressionScatteringTransform,
      conservationRegressionFeedback]
  all_goals try cases hOutputInput

/-- The displayed feedback matrix followed by its displayed inverse is the identity. -/
lemma conservationRegression_feedback_mul_inverse :
    conservationRegressionFeedback * conservationRegressionInverse = 1 := by
  ext output input
  by_cases hOutputInput : output = input
  all_goals
  rw [Matrix.mul_apply]
  rw [Fintype.sum_equiv
    (Incident.channelEquiv.trans conservationRegression.components.channelEquiv.symm)
    (fun middle => conservationRegressionFeedback output middle *
      conservationRegressionInverse middle input)
    (fun indexed => conservationRegressionFeedback output
        (Incident.mk (conservationRegression.components.channelEquiv indexed)) *
      conservationRegressionInverse
        (Incident.mk (conservationRegression.components.channelEquiv indexed)) input)
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
      conservationRegressionFeedback, conservationRegressionInverse]
  all_goals try cases hOutputInput

/-- The displayed inverse followed by the displayed feedback matrix is the identity. -/
lemma conservationRegression_inverse_mul_feedback :
    conservationRegressionInverse * conservationRegressionFeedback = 1 := by
  ext output input
  by_cases hOutputInput : output = input
  all_goals
  rw [Matrix.mul_apply]
  rw [Fintype.sum_equiv
    (Incident.channelEquiv.trans conservationRegression.components.channelEquiv.symm)
    (fun middle => conservationRegressionInverse output middle *
      conservationRegressionFeedback middle input)
    (fun indexed => conservationRegressionInverse output
        (Incident.mk (conservationRegression.components.channelEquiv indexed)) *
      conservationRegressionFeedback
        (Incident.mk (conservationRegression.components.channelEquiv indexed)) input)
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
      conservationRegressionFeedback, conservationRegressionInverse]
  all_goals try cases hOutputInput

/-- The lossless shared-link fixture is well posed. -/
lemma conservationRegression_isWellPosed : conservationRegression.IsWellPosed := by
  apply conservationRegression.isWellPosed_iff_feedbackOperator_injective.mpr
  intro first second hEqual
  have hMapped := congrArg conservationRegressionInverse.toLinearMap hEqual
  simpa only [← ModeTransform.toLinearMap_mul_apply,
    conservationRegression_feedbackOperator_eq,
    conservationRegression_inverse_mul_feedback,
    ModeTransform.toLinearMap, Matrix.toLpLin_one, LinearMap.id_apply] using hMapped

/-- The proof-gated inverse is exactly the displayed inverse matrix. -/
lemma conservationRegression_feedbackInverse_eq :
    conservationRegression.feedbackInverse conservationRegression_isWellPosed =
      conservationRegressionInverse := by
  calc
    conservationRegression.feedbackInverse conservationRegression_isWellPosed =
        conservationRegression.feedbackInverse conservationRegression_isWellPosed * 1 :=
      (Matrix.mul_one _).symm
    _ = conservationRegression.feedbackInverse conservationRegression_isWellPosed *
          (conservationRegressionFeedback * conservationRegressionInverse) := by
      rw [conservationRegression_feedback_mul_inverse]
    _ = (conservationRegression.feedbackInverse conservationRegression_isWellPosed *
          conservationRegression.feedbackOperator) * conservationRegressionInverse := by
      rw [conservationRegression_feedbackOperator_eq, Matrix.mul_assoc]
    _ = conservationRegressionInverse := by
      rw [conservationRegression.feedbackInverse_mul_feedbackOperator, Matrix.one_mul]

/-!

## D. System losslessness from component unitarity

-/

/-- The assembled component law of the fixture preserves normalized modal power. -/
lemma conservationRegression_scatteringTransform_isPowerPreserving :
    conservationRegression.scatteringTransform.IsPowerPreserving :=
  conservationRegression.scatteringTransform_isPowerPreserving_of_components_isLossless
    conservationRegressionScattering_isLossless

/-- The complete external response of the fixture preserves power. -/
lemma conservationRegression_responseTransform_isPowerPreserving :
    (conservationRegression.responseTransform
      conservationRegression_isWellPosed).IsPowerPreserving :=
  conservationRegression.responseTransform_isPowerPreserving_of_components_isLossless
    conservationRegression_isWellPosed conservationRegressionScattering_isLossless

/-- Row `N-03`: the complete external scattering matrix of the lossless cascade is unitary,
proved from component unitarity and wiring validity alone. -/
lemma conservationRegression_externalScatteringMatrix_isLossless :
    (conservationRegression.externalScatteringMatrix
      conservationRegression_isWellPosed).IsLossless :=
  conservationRegression.externalScatteringMatrix_isLossless_of_components_isLossless
    conservationRegression_isWellPosed conservationRegressionScattering_isLossless

/-!

## E. The hand-computed external response

-/

/-- The displayed feedback inverse and exposure give the displayed incident solution block. -/
lemma conservationRegression_inverse_mul_inputExposure :
    conservationRegressionInverse * conservationRegressionInputExposure =
      conservationRegressionIncidentSolution := by
  ext incident external
  rcases incident with ⟨⟨⟨component, port⟩, mode⟩⟩
  change (conservationRegression.components.portFamily component).Mode port at mode
  rcases external with ⟨external⟩
  rcases conservationRegression_external_eq_a_or_b external with rfl | rfl
  all_goals
    cases component <;> cases port <;> cases mode
  all_goals
    rw [Matrix.mul_apply, ← (conservationRegression.components.channelEquiv.trans
      Incident.channelEquiv.symm).sum_comp]
  all_goals
    simp [Fintype.sum_sigma, ScatteringComponentFamily.channelEquiv,
      conservationRegressionInverse, conservationRegressionInputExposure,
      conservationRegressionIncidentSolution]

/-- Component scattering sends the incident solution block to the displayed outgoing block. -/
lemma conservationRegression_scattering_mul_incidentSolution :
    conservationRegressionScatteringTransform * conservationRegressionIncidentSolution =
      conservationRegressionOutgoingSolution := by
  ext outgoing external
  rcases outgoing with ⟨⟨⟨component, port⟩, mode⟩⟩
  change (conservationRegression.components.portFamily component).Mode port at mode
  rcases external with ⟨external⟩
  rcases conservationRegression_external_eq_a_or_b external with rfl | rfl
  all_goals
    cases component <;> cases port <;> cases mode
  all_goals
    rw [Matrix.mul_apply, ← (conservationRegression.components.channelEquiv.trans
      Incident.channelEquiv.symm).sum_comp]
  all_goals
    simp [Fintype.sum_sigma, ScatteringComponentFamily.channelEquiv,
      conservationRegressionScatteringTransform, conservationRegressionIncidentSolution,
      conservationRegressionOutgoingSolution]

/-- External readout selects the displayed two-by-two response from the outgoing solution. -/
lemma conservationRegression_outputReadout_mul_outgoingSolution :
    conservationRegressionOutputReadout * conservationRegressionOutgoingSolution =
      conservationRegressionResponse := by
  ext output input
  rcases output with ⟨output⟩
  rcases input with ⟨input⟩
  rcases conservationRegression_external_eq_a_or_b output with rfl | rfl <;>
    rcases conservationRegression_external_eq_a_or_b input with rfl | rfl
  all_goals
    rw [Matrix.mul_apply, ← (conservationRegression.components.channelEquiv.trans
      Outgoing.channelEquiv.symm).sum_comp]
  all_goals
    simp [Fintype.sum_sigma, ScatteringComponentFamily.channelEquiv,
      conservationRegressionOutputReadout, conservationRegressionOutgoingSolution,
      conservationRegressionResponse]

/-- The exact external response of the lossless cascade is the hand-computed `[[0, I], [I, 0]]`. -/
lemma conservationRegression_responseTransform_eq :
    conservationRegression.responseTransform conservationRegression_isWellPosed =
      conservationRegressionResponse := by
  rw [conservationRegression.responseTransform_eq_blockFormula,
    conservationRegression.responseBlockFormula_eq,
    conservationRegression_outputReadout_eq,
    conservationRegression_feedbackInverse_eq,
    conservationRegression_scatteringTransform_eq,
    conservationRegression_inputExposure_eq]
  simp only [Matrix.mul_assoc, conservationRegression_inverse_mul_inputExposure,
    conservationRegression_scattering_mul_incidentSolution,
    conservationRegression_outputReadout_mul_outgoingSolution]

/-- The first exposed column of the hand-computed response carries exactly unit power. -/
lemma conservationRegressionResponse_column_a_power :
    Complex.normSq (conservationRegressionResponse
        (Outgoing.mk conservationRegressionExternalA)
        (Incident.mk conservationRegressionExternalA)) +
      Complex.normSq (conservationRegressionResponse
        (Outgoing.mk conservationRegressionExternalB)
        (Incident.mk conservationRegressionExternalA)) = 1 := by
  norm_num [conservationRegressionResponse]

/-- The second exposed column of the hand-computed response carries exactly unit power. -/
lemma conservationRegressionResponse_column_b_power :
    Complex.normSq (conservationRegressionResponse
        (Outgoing.mk conservationRegressionExternalA)
        (Incident.mk conservationRegressionExternalB)) +
      Complex.normSq (conservationRegressionResponse
        (Outgoing.mk conservationRegressionExternalB)
        (Incident.mk conservationRegressionExternalB)) = 1 := by
  norm_num [conservationRegressionResponse]

/-- The cascade is a pure exchange with a quarter-turn phase, so a dropped or conjugated
transmission phase is detected. -/
lemma conservationRegressionResponse_cross_entries :
    conservationRegressionResponse (Outgoing.mk conservationRegressionExternalA)
        (Incident.mk conservationRegressionExternalB) = Complex.I ∧
      conservationRegressionResponse (Outgoing.mk conservationRegressionExternalB)
        (Incident.mk conservationRegressionExternalA) = Complex.I :=
  ⟨rfl, rfl⟩

/-!

## F. Coherent and decorrelated two-input power

-/

/-- Two decorrelated external contributions have exactly additive total output power, and the
lossless cascade returns the sum of their input powers. -/
lemma conservationRegression_incoherentSum_trace
    (first second : ModeAmplitude conservationRegression.ExternalIncident) :
    (conservationRegression.responseCoherency conservationRegression_isWellPosed
        ((CoherencyMatrix.ofAmplitude first).incoherentSum
          (CoherencyMatrix.ofAmplitude second))).trace = first.power + second.power := by
  rw [conservationRegression.responseCoherency_trace_of_isPowerPreserving
      conservationRegression_isWellPosed
      conservationRegression_scatteringTransform_isPowerPreserving,
    CoherencyMatrix.incoherentSum_trace, CoherencyMatrix.ofAmplitude_trace,
    CoherencyMatrix.ofAmplitude_trace]

/-- Decorrelated contributions have exactly additive output power in every external channel: no
interference cross term survives. -/
lemma conservationRegression_incoherentSum_channelPower
    (first second : ModeAmplitude conservationRegression.ExternalIncident)
    (channel : conservationRegression.ExternalOutgoing) :
    (conservationRegression.responseCoherency conservationRegression_isWellPosed
          ((CoherencyMatrix.ofAmplitude first).incoherentSum
            (CoherencyMatrix.ofAmplitude second))).channelPower channel =
      (conservationRegression.responseCoherency conservationRegression_isWellPosed
          (CoherencyMatrix.ofAmplitude first)).channelPower channel +
        (conservationRegression.responseCoherency conservationRegression_isWellPosed
          (CoherencyMatrix.ofAmplitude second)).channelPower channel :=
  CoherencyMatrix.channelPower_map_incoherentSum _ _ _ channel

/-- The decorrelated result is not vacuous: the same two contributions taken coherently give a
strictly larger total output power whenever the contribution is nonzero. -/
lemma conservationRegression_coherent_ne_incoherentSum
    (amplitude : ModeAmplitude conservationRegression.ExternalIncident)
    (hAmplitude : amplitude ≠ 0) :
    (conservationRegression.responseCoherency conservationRegression_isWellPosed
        (CoherencyMatrix.ofAmplitude (amplitude + amplitude))).trace ≠
      (conservationRegression.responseCoherency conservationRegression_isWellPosed
        ((CoherencyMatrix.ofAmplitude amplitude).incoherentSum
          (CoherencyMatrix.ofAmplitude amplitude))).trace := by
  rw [conservationRegression.responseCoherency_trace_of_isPowerPreserving
      conservationRegression_isWellPosed
      conservationRegression_scatteringTransform_isPowerPreserving,
    conservationRegression_incoherentSum_trace, CoherencyMatrix.ofAmplitude_trace]
  have hDouble : amplitude + amplitude = (2 : ℂ) • amplitude := (two_smul ℂ amplitude).symm
  have hPositive : 0 < amplitude.power :=
    lt_of_le_of_ne amplitude.power_nonneg
      (fun hZero => hAmplitude ((ModeAmplitude.power_eq_zero_iff amplitude).mp hZero.symm))
  rw [hDouble, ModeAmplitude.power_smul]
  simp only [Complex.normSq_ofNat]
  intro hEqual
  linarith

end

end Optics
