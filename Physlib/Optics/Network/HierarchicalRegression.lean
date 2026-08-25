/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.Hierarchical

/-!
# Regression tests for hierarchical flattening

## i. Overview

A three-component chain is wired in two stages. The inner stage joins the first component's link
port to the second component's link port. The inner netlist retains all three components, while
its wiring connects a two-component subgraph and leaves a nontrivial boundary. The outer stage
then wires the second component's remaining boundary port to the third component, leaving exactly
two channels external: one on the first component and one on the third.

Every component is reflectionless with distinct forward and backward transmissions. Flattened
solutions force the forward sentinel

```text
y(output) = 165 * u(input)
```

The non-unit, nonreciprocal component coefficients keep the wiring order visible: a
subsystem-boundary or port-lift error that attached the outer connection to the wrong boundary port
would change the forced product.

## ii. Key results

The coefficients are exact algebraic sentinels, not passive, lossless, reciprocal, causal, or
normalized optical components. Nothing here asserts well-posedness of either stage; the memberships
proved below are memberships in singular-safe relations.

The fixture proves the hand-expanded pair satisfies both the flattened netlist equations and the
outer closure equations. Its forcing law and negative control detect a subsystem-boundary or
port-lift error. Together these results provide concrete evidence for `goal.md` I.3 row `N-08`.

## iii. Table of contents

- A. A three-component two-stage fixture
- B. The exact hand-computed solution state
- C. Membership in the flattened netlist's own channel equations
- D. The inner subsystem's own semantics
- E. Membership in the outer closure of the inner subsystem's behavior
- F. A forced coefficient and the mis-lifted-port negative control

## iv. References

The general semantic statement is `HierarchicalNetlist.flatten_behavior_eq` in
`Physlib.Optics.Network.Hierarchical`. The proofs here deliberately do not use that theorem: the
fixture independently checks the channel-level construction to catch an error in the theorem's
wiring setup or port lift.

-/

@[expose] public section

namespace Optics

noncomputable section

/-!

## A. A three-component two-stage fixture

-/

/-- The three components of the hierarchical fixture.

`inputStage` carries one external channel, `outputStage` carries the other, and `linkStage` is
interior to the flattened network: the inner stage reaches it and the outer stage leaves it.
-/
inductive HierarchicalRegressionComponent
  | inputStage
  | linkStage
  | outputStage
  deriving DecidableEq

/-- The fixture has exactly three components. -/
instance : Fintype HierarchicalRegressionComponent where
  elems := {.inputStage, .linkStage, .outputStage}
  complete := fun component => by cases component <;> decide

/-- Each fixture component has one outward port and one link port, each carrying one mode. -/
abbrev hierarchicalRegressionPortFamily : PortModeFamily where
  Port := Bool
  Mode := fun _ => Unit

/-- The fixture component matrices.

In local `[outward, link]` port order they are `[[0, 2], [3, 0]]`, `[[0, 5], [7, 0]]`, and
`[[0, 11], [13, 0]]`: reflectionless, with distinct forward and backward transmissions.
-/
def hierarchicalRegressionScattering (component : HierarchicalRegressionComponent) :
    ScatteringMatrix hierarchicalRegressionPortFamily.Channel where
  toModeTransform := fun output input =>
    match component, output.1, input.1 with
    | .inputStage, false, true => 2
    | .inputStage, true, false => 3
    | .linkStage, false, true => 5
    | .linkStage, true, false => 7
    | .outputStage, false, true => 11
    | .outputStage, true, false => 13
    | _, _, _ => 0

/-- The three fixture components before any wiring. -/
abbrev hierarchicalRegressionComponents : ScatteringComponentFamily where
  Component := HierarchicalRegressionComponent
  portFamily := fun _ => hierarchicalRegressionPortFamily
  scattering := hierarchicalRegressionScattering

/-- The inner stage's single connection joins the first two components' link ports. -/
abbrev hierarchicalRegressionInnerConnection :
    PortConnection hierarchicalRegressionComponents.aggregatePortModeFamily where
  left := ⟨.inputStage, true⟩
  right := ⟨.linkStage, true⟩
  left_ne_right := by
    intro hPort
    exact HierarchicalRegressionComponent.noConfusion (congrArg Sigma.fst hPort)
  modeEquiv := Equiv.refl Unit

/-- The proof-carrying inner connection family. -/
abbrev hierarchicalRegressionInner :
    PortConnectionFamily hierarchicalRegressionComponents.aggregatePortModeFamily Unit where
  connection := fun _ => hierarchicalRegressionInnerConnection
  endpointPort_injective := by
    rintro ⟨firstIndex, firstEnd⟩ ⟨secondIndex, secondEnd⟩ hPort
    cases firstIndex
    cases secondIndex
    cases firstEnd <;> cases secondEnd
    · rfl
    · exact HierarchicalRegressionComponent.noConfusion (congrArg Sigma.fst hPort)
    · exact HierarchicalRegressionComponent.noConfusion (congrArg Sigma.fst hPort)
    · rfl

/-- The second component's remaining port is left unconnected by the inner stage. -/
lemma hierarchicalRegression_linkOutward_unconnected :
    (⟨.linkStage, false⟩ : hierarchicalRegressionComponents.aggregatePortModeFamily.Port) ∉
      Set.range hierarchicalRegressionInner.endpointEmbedding := by
  rintro ⟨⟨index, endpoint⟩, hPort⟩
  cases index
  cases endpoint
  · exact HierarchicalRegressionComponent.noConfusion (congrArg Sigma.fst hPort)
  · exact Bool.noConfusion (congrArg (fun port => port.2) hPort)

/-- The third component's link port is left unconnected by the inner stage. -/
lemma hierarchicalRegression_outputLink_unconnected :
    (⟨.outputStage, true⟩ : hierarchicalRegressionComponents.aggregatePortModeFamily.Port) ∉
      Set.range hierarchicalRegressionInner.endpointEmbedding := by
  rintro ⟨⟨index, endpoint⟩, hPort⟩
  cases index
  cases endpoint <;>
    exact HierarchicalRegressionComponent.noConfusion (congrArg Sigma.fst hPort)

/-- The second component's outward port, as a boundary port of the inner stage. -/
abbrev hierarchicalRegressionLinkBoundary :
    hierarchicalRegressionInner.externalPortModeFamily.Port :=
  ⟨⟨.linkStage, false⟩, hierarchicalRegression_linkOutward_unconnected⟩

/-- The third component's link port, as a boundary port of the inner stage. -/
abbrev hierarchicalRegressionOutputBoundary :
    hierarchicalRegressionInner.externalPortModeFamily.Port :=
  ⟨⟨.outputStage, true⟩, hierarchicalRegression_outputLink_unconnected⟩

/-- The outer stage's single connection joins those two boundary ports. -/
abbrev hierarchicalRegressionOuterConnection :
    PortConnection hierarchicalRegressionInner.externalPortModeFamily where
  left := hierarchicalRegressionLinkBoundary
  right := hierarchicalRegressionOutputBoundary
  left_ne_right := by
    intro hPort
    exact HierarchicalRegressionComponent.noConfusion
      (congrArg (fun port => (Subtype.val port).1) hPort)
  modeEquiv := Equiv.refl Unit

/-- The proof-carrying outer connection family. -/
abbrev hierarchicalRegressionOuter :
    PortConnectionFamily hierarchicalRegressionInner.externalPortModeFamily Unit where
  connection := fun _ => hierarchicalRegressionOuterConnection
  endpointPort_injective := by
    rintro ⟨firstIndex, firstEnd⟩ ⟨secondIndex, secondEnd⟩ hPort
    cases firstIndex
    cases secondIndex
    cases firstEnd <;> cases secondEnd
    · rfl
    · exact HierarchicalRegressionComponent.noConfusion
        (congrArg (fun port => (Subtype.val port).1) hPort)
    · exact HierarchicalRegressionComponent.noConfusion
        (congrArg (fun port => (Subtype.val port).1) hPort)
    · rfl

/-- The two-stage fixture network. -/
abbrev hierarchicalRegression : HierarchicalNetlist where
  components := hierarchicalRegressionComponents
  InnerConnection := Unit
  inner := hierarchicalRegressionInner
  OuterConnection := Unit
  outer := hierarchicalRegressionOuter

/-- The component-family spelling is the canonical ambient channel type within this fixture. -/
abbrev HierarchicalRegressionChannel :=
  hierarchicalRegressionComponents.aggregatePortModeFamily.Channel

/-- The appended-family spelling is the canonical flattened connection family within this
fixture. -/
abbrev hierarchicalRegressionFlattenConnections :=
  hierarchicalRegressionInner.append hierarchicalRegressionOuter

/-- The fixture component type uses classical equality in assembled matrix expressions. -/
local instance hierarchicalRegressionComponentDecidableEq :
    DecidableEq HierarchicalRegressionComponent := Classical.decEq _

/-- Aggregate channels are finite in the fixture's canonical spelling. -/
local instance hierarchicalRegressionAggregateChannelFintype :
    Fintype HierarchicalRegressionChannel := by
  change Fintype (Σ _ : (Σ _ : HierarchicalRegressionComponent, Bool), Unit)
  infer_instance

/-- Aggregate channels have classical equality in the fixture's canonical spelling. -/
local instance hierarchicalRegressionAggregateChannelDecidableEq :
    DecidableEq HierarchicalRegressionChannel := Classical.decEq _

/-- The flattened-netlist channel spelling uses the canonical ambient enumeration. -/
local instance hierarchicalRegressionFlattenChannelFintype :
    Fintype hierarchicalRegression.flatten.Channel :=
  hierarchicalRegressionAggregateChannelFintype

/-- The flattened-netlist channel spelling uses the canonical ambient equality decision. -/
local instance hierarchicalRegressionFlattenChannelDecidableEq :
    DecidableEq hierarchicalRegression.flatten.Channel :=
  hierarchicalRegressionAggregateChannelDecidableEq

/-- Connected channels of the flattened fixture are finite in the appended-family spelling. -/
local instance hierarchicalRegressionAppendChannelFintype :
    Fintype hierarchicalRegressionFlattenConnections.Channel := by
  change Fintype (Σ _ : Unit ⊕ Unit, Unit ⊕ Unit)
  infer_instance

/-- Classical equality on the flattened two-stage family's connected channels. -/
local instance hierarchicalRegressionAppendChannelDecidableEq :
    DecidableEq hierarchicalRegressionFlattenConnections.Channel :=
  Classical.decEq _

/-- The flattened two-stage family's external channels are finite. -/
local instance hierarchicalRegressionAppendExternalFintype :
    Fintype hierarchicalRegressionFlattenConnections.ExternalChannel := Fintype.ofFinite _

/-- The flattened-netlist connected spelling uses the appended-family enumeration. -/
local instance hierarchicalRegressionFlattenConnectedChannelFintype :
    Fintype hierarchicalRegression.flatten.connections.Channel :=
  hierarchicalRegressionAppendChannelFintype

/-- The flattened-netlist connected spelling uses the appended-family equality decision. -/
local instance hierarchicalRegressionFlattenConnectedChannelDecidableEq :
    DecidableEq hierarchicalRegression.flatten.connections.Channel :=
  hierarchicalRegressionAppendChannelDecidableEq

/-- The flattened-netlist external spelling uses the appended-family enumeration. -/
local instance hierarchicalRegressionFlattenExternalChannelFintype :
    Fintype hierarchicalRegression.flatten.ExternalChannel :=
  hierarchicalRegressionAppendExternalFintype

/-- Each component's local channels are finite. -/
local instance hierarchicalRegressionLocalChannelFintype
    (component : HierarchicalRegressionComponent) :
    Fintype (hierarchicalRegressionComponents.portFamily component).Channel := by
  change Fintype (Σ _ : Bool, Unit)
  infer_instance

/-- The flattened component spelling uses the concrete three-element enumeration. -/
local instance hierarchicalRegressionFlattenComponentFintype :
    Fintype hierarchicalRegression.flatten.components.Component := by
  change Fintype HierarchicalRegressionComponent
  infer_instance

/-- The flattened component spelling uses the same classical equality decision. -/
local instance hierarchicalRegressionFlattenComponentDecidableEq :
    DecidableEq hierarchicalRegression.flatten.components.Component :=
  hierarchicalRegressionComponentDecidableEq

/-- Each local channel is finite in the flattened-component spelling. -/
local instance hierarchicalRegressionFlattenLocalChannelFintype
    (component : hierarchicalRegression.flatten.components.Component) :
    Fintype (hierarchicalRegression.flatten.components.portFamily component).Channel := by
  change Fintype (Σ _ : Bool, Unit)
  infer_instance

/-!

## B. The exact hand-computed solution state

-/

/-- The first component's outward ambient channel. -/
abbrev hierarchicalRegressionInputChannel : HierarchicalRegressionChannel :=
  ⟨⟨.inputStage, false⟩, ()⟩

/-- The third component's outward ambient channel. -/
abbrev hierarchicalRegressionOutputChannel : HierarchicalRegressionChannel :=
  ⟨⟨.outputStage, false⟩, ()⟩

/-- The first component's inner-link ambient channel. -/
abbrev hierarchicalRegressionInputLinkChannel : HierarchicalRegressionChannel :=
  ⟨⟨.inputStage, true⟩, ()⟩

/-- The second component's outward ambient channel. -/
abbrev hierarchicalRegressionLinkOutwardChannel : HierarchicalRegressionChannel :=
  ⟨⟨.linkStage, false⟩, ()⟩

/-- The second component's inner-link ambient channel. -/
abbrev hierarchicalRegressionLinkLinkChannel : HierarchicalRegressionChannel :=
  ⟨⟨.linkStage, true⟩, ()⟩

/-- The third component's link ambient channel. -/
abbrev hierarchicalRegressionOutputLinkChannel : HierarchicalRegressionChannel :=
  ⟨⟨.outputStage, true⟩, ()⟩

/-- The first component's outward channel is left external by both stages. -/
lemma hierarchicalRegression_inputChannel_external :
    hierarchicalRegressionInputChannel ∉
      Set.range hierarchicalRegressionFlattenConnections.channelEmbedding := by
  rintro ⟨⟨index, local'⟩, hChannel⟩
  rcases index with index | index
  · cases index
    rcases local' with mode | mode <;> cases mode
    · exact Bool.noConfusion (congrArg (fun channel => channel.1.2) hChannel)
    · exact HierarchicalRegressionComponent.noConfusion
        (congrArg (fun channel => channel.1.1) hChannel)
  · cases index
    rcases local' with mode | mode <;> cases mode <;>
      exact HierarchicalRegressionComponent.noConfusion
        (congrArg (fun channel => channel.1.1) hChannel)

/-- The third component's outward channel is left external by both stages. -/
lemma hierarchicalRegression_outputChannel_external :
    hierarchicalRegressionOutputChannel ∉
      Set.range hierarchicalRegressionFlattenConnections.channelEmbedding := by
  rintro ⟨⟨index, local'⟩, hChannel⟩
  rcases index with index | index
  · cases index
    rcases local' with mode | mode <;> cases mode <;>
      exact HierarchicalRegressionComponent.noConfusion
        (congrArg (fun channel => channel.1.1) hChannel)
  · cases index
    rcases local' with mode | mode <;> cases mode
    · exact HierarchicalRegressionComponent.noConfusion
        (congrArg (fun channel => channel.1.1) hChannel)
    · exact Bool.noConfusion (congrArg (fun channel => channel.1.2) hChannel)

/-- The packaged external channel carrying the drive. -/
abbrev hierarchicalRegressionExternalInput :
    hierarchicalRegressionFlattenConnections.ExternalChannel :=
  ⟨hierarchicalRegressionInputChannel, hierarchicalRegression_inputChannel_external⟩

/-- The packaged external channel carrying the response. -/
abbrev hierarchicalRegressionExternalOutput :
    hierarchicalRegressionFlattenConnections.ExternalChannel :=
  ⟨hierarchicalRegressionOutputChannel, hierarchicalRegression_outputChannel_external⟩

/-- The hand-computed ambient incident state for unit drive on the input-stage channel.

Reading the chain forward: the drive enters at the first component, crosses the inner connection
with gain `3`, and crosses the outer connection with a further gain `5`.
-/
def hierarchicalRegressionIncidentState :
    ModeAmplitude (Incident HierarchicalRegressionChannel) :=
  WithLp.toLp 2 fun endpoint =>
    match endpoint.channel.1.1, endpoint.channel.1.2 with
    | .inputStage, false => 1
    | .linkStage, true => 3
    | .outputStage, true => 15
    | _, _ => 0

/-- The hand-computed ambient outgoing state for the same drive. -/
def hierarchicalRegressionOutgoingState :
    ModeAmplitude (Outgoing HierarchicalRegressionChannel) :=
  WithLp.toLp 2 fun endpoint =>
    match endpoint.channel.1.1, endpoint.channel.1.2 with
    | .inputStage, true => 3
    | .linkStage, false => 15
    | .outputStage, false => 165
    | _, _ => 0

/-- Unit drive on the input-stage external channel and nothing on the other. -/
def hierarchicalRegressionInput :
    ModeAmplitude (Incident hierarchicalRegressionFlattenConnections.ExternalChannel) :=
  WithLp.toLp 2 fun endpoint =>
    match endpoint.channel.1.1.1 with
    | .inputStage => 1
    | _ => 0

/-- The hand-computed external response to that drive: `165` on the output-stage channel. -/
def hierarchicalRegressionOutput :
    ModeAmplitude (Outgoing hierarchicalRegressionFlattenConnections.ExternalChannel) :=
  WithLp.toLp 2 fun endpoint =>
    match endpoint.channel.1.1.1 with
    | .outputStage => 165
    | _ => 0

/-- Every exposed channel of the flattened fixture is one of its two declared external
endpoints. -/
lemma hierarchicalRegression_external_eq_input_or_output
    (channel : hierarchicalRegressionFlattenConnections.ExternalChannel) :
    channel = hierarchicalRegressionExternalInput ∨
      channel = hierarchicalRegressionExternalOutput := by
  rcases channel with ⟨⟨⟨component, port⟩, mode⟩, hChannel⟩
  cases component <;> cases port <;> cases mode
  · exact Or.inl rfl
  · exact absurd ⟨⟨Sum.inl (), Sum.inl ()⟩, rfl⟩ hChannel
  · exact absurd ⟨⟨Sum.inr (), Sum.inl ()⟩, rfl⟩ hChannel
  · exact absurd ⟨⟨Sum.inl (), Sum.inr ()⟩, rfl⟩ hChannel
  · exact Or.inr rfl
  · exact absurd ⟨⟨Sum.inr (), Sum.inr ()⟩, rfl⟩ hChannel

/-!

## C. Membership in the flattened netlist's own channel equations

-/

/-- Component channel embedding in the fixture keeps the component tag, port, and mode. -/
@[simp]
lemma hierarchicalRegression_componentChannelEmbedding
    (component : HierarchicalRegressionComponent) (port : Bool) :
    hierarchicalRegressionComponents.componentChannelEmbedding component
        ⟨port, ()⟩ = ⟨⟨component, port⟩, ()⟩ := rfl

/-- The flattened family's first inner connected channel embeds at the first component's link. -/
@[simp]
lemma hierarchicalRegression_flatten_embed_innerLeft :
    hierarchicalRegressionInner.channelEmbedding ⟨(), Sum.inl ()⟩ =
      (⟨⟨.inputStage, true⟩, ()⟩ : HierarchicalRegressionChannel) := rfl

/-- The flattened family's second inner connected channel embeds at the second component's
link. -/
@[simp]
lemma hierarchicalRegression_flatten_embed_innerRight :
    hierarchicalRegressionInner.channelEmbedding ⟨(), Sum.inr ()⟩ =
      (⟨⟨.linkStage, true⟩, ()⟩ : HierarchicalRegressionChannel) := rfl

/-- The appended-family spelling of the flattened inner left embedding. -/
lemma hierarchicalRegression_flatten_embed_innerLeft_append :
    hierarchicalRegressionFlattenConnections.channelEmbedding
        ⟨Sum.inl (), Sum.inl ()⟩ =
      (⟨⟨.inputStage, true⟩, ()⟩ : HierarchicalRegressionChannel) := rfl

/-- The appended-family spelling of the flattened inner right embedding. -/
lemma hierarchicalRegression_flatten_embed_innerRight_append :
    hierarchicalRegressionFlattenConnections.channelEmbedding
        ⟨Sum.inl (), Sum.inr ()⟩ =
      (⟨⟨.linkStage, true⟩, ()⟩ : HierarchicalRegressionChannel) := rfl

/-- The flattened family's first outer connected channel embeds at the second component's outward
port. -/
@[simp]
lemma hierarchicalRegression_flatten_embed_outerLeft :
    hierarchicalRegressionFlattenConnections.channelEmbedding
        ⟨Sum.inr (), Sum.inl ()⟩ =
      (⟨⟨.linkStage, false⟩, ()⟩ : HierarchicalRegressionChannel) := rfl

/-- The flattened family's second outer connected channel embeds at the third component's link. -/
@[simp]
lemma hierarchicalRegression_flatten_embed_outerRight :
    hierarchicalRegressionFlattenConnections.channelEmbedding
        ⟨Sum.inr (), Sum.inr ()⟩ =
      (⟨⟨.outputStage, true⟩, ()⟩ : HierarchicalRegressionChannel) := rfl

/-- Mates in the flattened family exchange the two ends of each connection. -/
@[simp]
lemma hierarchicalRegression_flatten_mate_innerLeft :
    hierarchicalRegressionFlattenConnections.mateEquiv ⟨Sum.inl (), Sum.inl ()⟩ =
      ⟨Sum.inl (), Sum.inr ()⟩ := rfl

/-- Mates in the flattened family exchange the two ends of each connection. -/
@[simp]
lemma hierarchicalRegression_flatten_mate_innerRight :
    hierarchicalRegressionFlattenConnections.mateEquiv ⟨Sum.inl (), Sum.inr ()⟩ =
      ⟨Sum.inl (), Sum.inl ()⟩ := rfl

/-- Mates in the flattened family exchange the two ends of each connection. -/
@[simp]
lemma hierarchicalRegression_flatten_mate_outerLeft :
    hierarchicalRegressionFlattenConnections.mateEquiv ⟨Sum.inr (), Sum.inl ()⟩ =
      ⟨Sum.inr (), Sum.inr ()⟩ := rfl

/-- Mates in the flattened family exchange the two ends of each connection. -/
@[simp]
lemma hierarchicalRegression_flatten_mate_outerRight :
    hierarchicalRegressionFlattenConnections.mateEquiv ⟨Sum.inr (), Sum.inr ()⟩ =
      ⟨Sum.inr (), Sum.inl ()⟩ := rfl

/-- The hand-computed state satisfies every component's own boundary law. -/
lemma hierarchicalRegression_mem_componentBehavior :
    (hierarchicalRegressionIncidentState, hierarchicalRegressionOutgoingState) ∈
      hierarchicalRegression.flatten.componentBehavior := by
  classical
  apply (hierarchicalRegression.flatten.mem_componentBehavior_iff_forall_component
    hierarchicalRegressionIncidentState hierarchicalRegressionOutgoingState).2
  intro component
  let canonicalComponent : HierarchicalRegressionComponent := component
  change
    (hierarchicalRegressionIncidentState.restrictEmbedding
        (Incident.relabelEmbedding
          (hierarchicalRegressionComponents.componentChannelEmbedding canonicalComponent)),
      hierarchicalRegressionOutgoingState.restrictEmbedding
        (Outgoing.relabelEmbedding
          (hierarchicalRegressionComponents.componentChannelEmbedding canonicalComponent))) ∈
      (hierarchicalRegressionScattering canonicalComponent).toOrientedModeTransform.toBehavior
  rw [ModeTransform.mem_toBehavior_iff_toLinearMap,
    ScatteringMatrix.toLinearMap_toOrientedModeTransform]
  apply WithLp.ofLp_injective 2
  funext localChannel
  rcases localChannel with ⟨port, mode⟩
  rw [ModeAmplitude.reindex_apply]
  simp only [Equiv.symm_symm, Outgoing.channelEquiv_apply,
    ModeAmplitude.restrictEmbedding_apply]
  rw [Matrix.ofLp_toLpLin, Matrix.toLin'_apply]
  cases canonicalComponent <;> cases port <;> cases mode
  all_goals
    simp [ModeAmplitude.reindex_apply, Matrix.mulVec, dotProduct,
      Fintype.sum_sigma,
      hierarchicalRegressionScattering, ModeAmplitude.restrictEmbedding_apply,
      hierarchicalRegressionIncidentState, hierarchicalRegressionOutgoingState]
  · change (0 : ℂ) = 2 * 0
    norm_num
  · change (3 : ℂ) = 3 * 1
    norm_num
  · change (15 : ℂ) = 5 * 3
    norm_num
  · change (0 : ℂ) = 7 * 0
    norm_num
  · change (165 : ℂ) = 11 * 15
    norm_num
  · change (0 : ℂ) = 13 * 0
    norm_num

/-- The hand-computed state satisfies the flattened netlist's incident assembly `a = C b + E_in u`
at every ambient coordinate, connected and external alike. -/
lemma hierarchicalRegression_incidentAssembly :
    hierarchicalRegressionIncidentState =
      hierarchicalRegression.flatten.connections.incidentAssembly
        hierarchicalRegressionOutgoingState hierarchicalRegressionInput := by
  classical
  change hierarchicalRegressionIncidentState =
    hierarchicalRegressionFlattenConnections.incidentAssembly
      hierarchicalRegressionOutgoingState hierarchicalRegressionInput
  apply WithLp.ofLp_injective 2
  funext endpoint
  rcases endpoint with ⟨⟨⟨component, port⟩, mode⟩⟩
  cases component <;> cases port <;> cases mode
  · rw [hierarchicalRegressionFlattenConnections.incidentAssembly_apply_external
      hierarchicalRegressionOutgoingState hierarchicalRegressionInput
      hierarchicalRegressionExternalInput]
    simp [hierarchicalRegressionIncidentState, hierarchicalRegressionInput]
  · rw [show (⟨⟨HierarchicalRegressionComponent.inputStage, true⟩, ()⟩ :
        HierarchicalRegressionChannel) =
          hierarchicalRegressionFlattenConnections.channelEmbedding
            ⟨Sum.inl (), Sum.inl ()⟩ from rfl,
      hierarchicalRegressionFlattenConnections.incidentAssembly_apply_connected_channel
        hierarchicalRegressionOutgoingState hierarchicalRegressionInput ⟨Sum.inl (), Sum.inl ()⟩]
    rw [hierarchicalRegression_flatten_mate_innerLeft,
      hierarchicalRegression_flatten_embed_innerLeft_append,
      hierarchicalRegression_flatten_embed_innerRight_append]
    simp [hierarchicalRegressionIncidentState, hierarchicalRegressionOutgoingState]
  · rw [show (⟨⟨HierarchicalRegressionComponent.linkStage, false⟩, ()⟩ :
        HierarchicalRegressionChannel) =
          hierarchicalRegressionFlattenConnections.channelEmbedding
            ⟨Sum.inr (), Sum.inl ()⟩ from rfl,
      hierarchicalRegressionFlattenConnections.incidentAssembly_apply_connected_channel
        hierarchicalRegressionOutgoingState hierarchicalRegressionInput ⟨Sum.inr (), Sum.inl ()⟩]
    rw [hierarchicalRegression_flatten_mate_outerLeft,
      hierarchicalRegression_flatten_embed_outerLeft,
      hierarchicalRegression_flatten_embed_outerRight]
    simp [hierarchicalRegressionIncidentState, hierarchicalRegressionOutgoingState]
  · rw [show (⟨⟨HierarchicalRegressionComponent.linkStage, true⟩, ()⟩ :
        HierarchicalRegressionChannel) =
          hierarchicalRegressionFlattenConnections.channelEmbedding
            ⟨Sum.inl (), Sum.inr ()⟩ from rfl,
      hierarchicalRegressionFlattenConnections.incidentAssembly_apply_connected_channel
        hierarchicalRegressionOutgoingState hierarchicalRegressionInput ⟨Sum.inl (), Sum.inr ()⟩]
    rw [hierarchicalRegression_flatten_mate_innerRight,
      hierarchicalRegression_flatten_embed_innerRight_append,
      hierarchicalRegression_flatten_embed_innerLeft_append]
    simp [hierarchicalRegressionIncidentState, hierarchicalRegressionOutgoingState]
  · rw [hierarchicalRegressionFlattenConnections.incidentAssembly_apply_external
      hierarchicalRegressionOutgoingState hierarchicalRegressionInput
      hierarchicalRegressionExternalOutput]
    simp [hierarchicalRegressionIncidentState, hierarchicalRegressionInput]
  · rw [show (⟨⟨HierarchicalRegressionComponent.outputStage, true⟩, ()⟩ :
        HierarchicalRegressionChannel) =
          hierarchicalRegressionFlattenConnections.channelEmbedding
            ⟨Sum.inr (), Sum.inr ()⟩ from rfl,
      hierarchicalRegressionFlattenConnections.incidentAssembly_apply_connected_channel
        hierarchicalRegressionOutgoingState hierarchicalRegressionInput ⟨Sum.inr (), Sum.inr ()⟩]
    rw [hierarchicalRegression_flatten_mate_outerRight,
      hierarchicalRegression_flatten_embed_outerRight,
      hierarchicalRegression_flatten_embed_outerLeft]
    simp [hierarchicalRegressionIncidentState, hierarchicalRegressionOutgoingState]

/-- External readout of the hand-computed outgoing state is the hand-computed response. -/
lemma hierarchicalRegression_outputReadout :
    hierarchicalRegressionOutput =
      hierarchicalRegression.flatten.outputReadout.toLinearMap
        hierarchicalRegressionOutgoingState := by
  classical
  change hierarchicalRegressionOutput =
    hierarchicalRegressionFlattenConnections.externalOutgoingReadout.toLinearMap
      hierarchicalRegressionOutgoingState
  rw [PortConnectionFamily.externalOutgoingReadout_apply]
  apply WithLp.ofLp_injective 2
  funext endpoint
  rcases endpoint with ⟨channel⟩
  rw [ModeAmplitude.restrictEmbedding_apply,
    PortConnectionFamily.externalOutgoingEmbedding_apply]
  rcases hierarchicalRegression_external_eq_input_or_output channel with rfl | rfl <;>
    simp [hierarchicalRegressionOutput, hierarchicalRegressionOutgoingState]

/-- **The flattened netlist admits the hand-computed pair**, proved from its own three channel
equations and not from any hierarchical theorem. -/
lemma hierarchicalRegression_mem_flatten_behavior :
    (hierarchicalRegressionInput, hierarchicalRegressionOutput) ∈
      hierarchicalRegression.flatten.behavior := by
  classical
  exact (hierarchicalRegression.flatten.mem_behavior_iff_componentBehavior
    hierarchicalRegressionInput hierarchicalRegressionOutput).2
      ⟨hierarchicalRegressionIncidentState, hierarchicalRegressionOutgoingState,
        hierarchicalRegression_mem_componentBehavior,
        hierarchicalRegression_incidentAssembly,
        hierarchicalRegression_outputReadout⟩

/-!

## D. The inner subsystem's own semantics

-/

/-- The one-connection channel shape shared by the two stages is finite. -/
local instance hierarchicalRegressionStageChannelFintype :
    Fintype (Σ _ : Unit, Unit ⊕ Unit) := inferInstance

/-- The one-connection channel shape shared by the two stages has classical equality. -/
local instance hierarchicalRegressionStageChannelDecidableEq :
    DecidableEq (Σ _ : Unit, Unit ⊕ Unit) := Classical.decEq _

/-- The inner connected-channel spelling uses the shared stage enumeration. -/
local instance hierarchicalRegressionInnerChannelFintype :
    Fintype hierarchicalRegressionInner.Channel :=
  hierarchicalRegressionStageChannelFintype

/-- The inner connected-channel spelling uses the shared stage equality decision. -/
local instance hierarchicalRegressionInnerChannelDecidableEq :
    DecidableEq hierarchicalRegressionInner.Channel :=
  hierarchicalRegressionStageChannelDecidableEq

/-- The outer connected-channel spelling uses the shared stage enumeration. -/
local instance hierarchicalRegressionOuterChannelFintype :
    Fintype hierarchicalRegressionOuter.Channel :=
  hierarchicalRegressionStageChannelFintype

/-- The outer connected-channel spelling uses the shared stage equality decision. -/
local instance hierarchicalRegressionOuterChannelDecidableEq :
    DecidableEq hierarchicalRegressionOuter.Channel :=
  hierarchicalRegressionStageChannelDecidableEq

/-- The inner stage's external channels are finite. -/
local instance hierarchicalRegressionInnerExternalFintype :
    Fintype hierarchicalRegressionInner.ExternalChannel := Fintype.ofFinite _

/-- The inner-netlist ambient spelling uses the canonical aggregate enumeration. -/
local instance hierarchicalRegressionInnerNetlistChannelFintype :
    Fintype hierarchicalRegression.innerNetlist.Channel :=
  hierarchicalRegressionAggregateChannelFintype

/-- The inner-netlist ambient spelling uses the canonical aggregate equality decision. -/
local instance hierarchicalRegressionInnerNetlistChannelDecidableEq :
    DecidableEq hierarchicalRegression.innerNetlist.Channel :=
  hierarchicalRegressionAggregateChannelDecidableEq

/-- The inner-netlist connected spelling uses the inner-stage enumeration. -/
local instance hierarchicalRegressionInnerNetlistConnectedFintype :
    Fintype hierarchicalRegression.innerNetlist.ConnectedChannel :=
  hierarchicalRegressionInnerChannelFintype

/-- The inner-netlist connected spelling uses the inner-stage equality decision. -/
local instance hierarchicalRegressionInnerNetlistConnectedDecidableEq :
    DecidableEq hierarchicalRegression.innerNetlist.ConnectedChannel :=
  hierarchicalRegressionInnerChannelDecidableEq

/-- The inner-netlist external spelling uses the inner-stage enumeration. -/
local instance hierarchicalRegressionInnerNetlistExternalFintype :
    Fintype hierarchicalRegression.innerNetlist.ExternalChannel :=
  hierarchicalRegressionInnerExternalFintype

/-- The inner stage's connected channels embed at the two link channels. -/
@[simp]
lemma hierarchicalRegression_inner_embed_left :
    hierarchicalRegressionInner.channelEmbedding ⟨(), Sum.inl ()⟩ =
      (⟨⟨.inputStage, true⟩, ()⟩ :
        hierarchicalRegressionComponents.aggregatePortModeFamily.Channel) := rfl

/-- The inner stage's connected channels embed at the two link channels. -/
@[simp]
lemma hierarchicalRegression_inner_embed_right :
    hierarchicalRegressionInner.channelEmbedding ⟨(), Sum.inr ()⟩ =
      (⟨⟨.linkStage, true⟩, ()⟩ :
        hierarchicalRegressionComponents.aggregatePortModeFamily.Channel) := rfl

/-- Mates in the inner stage exchange the two ends of its connection. -/
@[simp]
lemma hierarchicalRegression_inner_mate_left :
    hierarchicalRegressionInner.mateEquiv ⟨(), Sum.inl ()⟩ = ⟨(), Sum.inr ()⟩ := rfl

/-- Mates in the inner stage exchange the two ends of its connection. -/
@[simp]
lemma hierarchicalRegression_inner_mate_right :
    hierarchicalRegressionInner.mateEquiv ⟨(), Sum.inr ()⟩ = ⟨(), Sum.inl ()⟩ := rfl

/-- The inner stage connects exactly the two link channels. -/
lemma hierarchicalRegression_inner_channelEmbedding_eq
    (channel : hierarchicalRegressionInner.Channel) :
    hierarchicalRegressionInner.channelEmbedding channel =
        (⟨⟨.inputStage, true⟩, ()⟩ :
          hierarchicalRegressionComponents.aggregatePortModeFamily.Channel) ∨
      hierarchicalRegressionInner.channelEmbedding channel =
        (⟨⟨.linkStage, true⟩, ()⟩ :
          hierarchicalRegressionComponents.aggregatePortModeFamily.Channel) := by
  rcases channel with ⟨index, local'⟩
  cases index
  rcases local' with mode | mode <;> cases mode
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The first component's outward channel is left external by the inner stage. -/
lemma hierarchicalRegression_inner_inputOutward_external :
    (⟨⟨.inputStage, false⟩, ()⟩ :
        hierarchicalRegressionComponents.aggregatePortModeFamily.Channel) ∉
      Set.range hierarchicalRegressionInner.channelEmbedding := by
  rintro ⟨channel, hChannel⟩
  rcases hierarchicalRegression_inner_channelEmbedding_eq channel with hEq | hEq <;>
    rw [hEq] at hChannel
  · exact Bool.noConfusion (congrArg (fun c => c.1.2) hChannel)
  · exact HierarchicalRegressionComponent.noConfusion (congrArg (fun c => c.1.1) hChannel)

/-- The second component's outward channel is left external by the inner stage. -/
lemma hierarchicalRegression_inner_linkOutward_external :
    (⟨⟨.linkStage, false⟩, ()⟩ :
        hierarchicalRegressionComponents.aggregatePortModeFamily.Channel) ∉
      Set.range hierarchicalRegressionInner.channelEmbedding := by
  rintro ⟨channel, hChannel⟩
  rcases hierarchicalRegression_inner_channelEmbedding_eq channel with hEq | hEq <;>
    rw [hEq] at hChannel
  · exact HierarchicalRegressionComponent.noConfusion (congrArg (fun c => c.1.1) hChannel)
  · exact Bool.noConfusion (congrArg (fun c => c.1.2) hChannel)

/-- The third component's outward channel is left external by the inner stage. -/
lemma hierarchicalRegression_inner_outputOutward_external :
    (⟨⟨.outputStage, false⟩, ()⟩ :
        hierarchicalRegressionComponents.aggregatePortModeFamily.Channel) ∉
      Set.range hierarchicalRegressionInner.channelEmbedding := by
  rintro ⟨channel, hChannel⟩
  rcases hierarchicalRegression_inner_channelEmbedding_eq channel with hEq | hEq <;>
    exact HierarchicalRegressionComponent.noConfusion
      (congrArg (fun c => c.1.1) (hEq ▸ hChannel))

/-- The third component's link channel is left external by the inner stage. -/
lemma hierarchicalRegression_inner_outputLink_external :
    (⟨⟨.outputStage, true⟩, ()⟩ :
        hierarchicalRegressionComponents.aggregatePortModeFamily.Channel) ∉
      Set.range hierarchicalRegressionInner.channelEmbedding := by
  rintro ⟨channel, hChannel⟩
  rcases hierarchicalRegression_inner_channelEmbedding_eq channel with hEq | hEq <;>
    exact HierarchicalRegressionComponent.noConfusion
      (congrArg (fun c => c.1.1) (hEq ▸ hChannel))

/-- The first component's outward channel, packaged as an inner external channel. -/
abbrev hierarchicalRegressionInnerInputExternal :
    hierarchicalRegressionInner.ExternalChannel :=
  ⟨⟨⟨.inputStage, false⟩, ()⟩, hierarchicalRegression_inner_inputOutward_external⟩

/-- The second component's outward channel, packaged as an inner external channel. -/
abbrev hierarchicalRegressionInnerLinkExternal :
    hierarchicalRegressionInner.ExternalChannel :=
  ⟨⟨⟨.linkStage, false⟩, ()⟩, hierarchicalRegression_inner_linkOutward_external⟩

/-- The third component's outward channel, packaged as an inner external channel. -/
abbrev hierarchicalRegressionInnerOutputExternal :
    hierarchicalRegressionInner.ExternalChannel :=
  ⟨⟨⟨.outputStage, false⟩, ()⟩, hierarchicalRegression_inner_outputOutward_external⟩

/-- The third component's link channel, packaged as an inner external channel. -/
abbrev hierarchicalRegressionInnerOutputLinkExternal :
    hierarchicalRegressionInner.ExternalChannel :=
  ⟨⟨⟨.outputStage, true⟩, ()⟩, hierarchicalRegression_inner_outputLink_external⟩

/-- The inner stage's external incident amplitudes for the same drive. -/
def hierarchicalRegressionInnerIncident :
    ModeAmplitude (Incident hierarchicalRegressionInner.ExternalChannel) :=
  WithLp.toLp 2 fun endpoint =>
    match endpoint.channel.1.1.1, endpoint.channel.1.1.2 with
    | .inputStage, false => 1
    | .outputStage, true => 15
    | _, _ => 0

/-- The inner stage's external outgoing amplitudes for the same drive. -/
def hierarchicalRegressionInnerOutgoing :
    ModeAmplitude (Outgoing hierarchicalRegressionInner.ExternalChannel) :=
  WithLp.toLp 2 fun endpoint =>
    match endpoint.channel.1.1.1, endpoint.channel.1.1.2 with
    | .linkStage, false => 15
    | .outputStage, false => 165
    | _, _ => 0

/-- The same ambient state satisfies the inner subsystem's own incident assembly. -/
lemma hierarchicalRegression_inner_incidentAssembly :
    hierarchicalRegressionIncidentState =
      hierarchicalRegressionInner.incidentAssembly
        hierarchicalRegressionOutgoingState hierarchicalRegressionInnerIncident := by
  classical
  apply WithLp.ofLp_injective 2
  funext endpoint
  rcases endpoint with ⟨⟨⟨component, port⟩, mode⟩⟩
  cases component <;> cases port <;> cases mode
  · rw [hierarchicalRegressionInner.incidentAssembly_apply_external
      hierarchicalRegressionOutgoingState hierarchicalRegressionInnerIncident
      hierarchicalRegressionInnerInputExternal]
    simp [hierarchicalRegressionIncidentState, hierarchicalRegressionInnerIncident]
  · rw [show (⟨⟨HierarchicalRegressionComponent.inputStage, true⟩, ()⟩ :
        hierarchicalRegressionComponents.aggregatePortModeFamily.Channel) =
          hierarchicalRegressionInner.channelEmbedding ⟨(), Sum.inl ()⟩ from rfl,
      hierarchicalRegressionInner.incidentAssembly_apply_connected_channel
        hierarchicalRegressionOutgoingState hierarchicalRegressionInnerIncident
        ⟨(), Sum.inl ()⟩]
    rw [hierarchicalRegression_inner_mate_left,
      hierarchicalRegression_inner_embed_left,
      hierarchicalRegression_inner_embed_right]
    simp [hierarchicalRegressionIncidentState, hierarchicalRegressionOutgoingState]
  · rw [hierarchicalRegressionInner.incidentAssembly_apply_external
      hierarchicalRegressionOutgoingState hierarchicalRegressionInnerIncident
      hierarchicalRegressionInnerLinkExternal]
    simp [hierarchicalRegressionIncidentState, hierarchicalRegressionInnerIncident]
  · rw [show (⟨⟨HierarchicalRegressionComponent.linkStage, true⟩, ()⟩ :
        hierarchicalRegressionComponents.aggregatePortModeFamily.Channel) =
          hierarchicalRegressionInner.channelEmbedding ⟨(), Sum.inr ()⟩ from rfl,
      hierarchicalRegressionInner.incidentAssembly_apply_connected_channel
        hierarchicalRegressionOutgoingState hierarchicalRegressionInnerIncident
        ⟨(), Sum.inr ()⟩]
    rw [hierarchicalRegression_inner_mate_right,
      hierarchicalRegression_inner_embed_right,
      hierarchicalRegression_inner_embed_left]
    simp [hierarchicalRegressionIncidentState, hierarchicalRegressionOutgoingState]
  · rw [hierarchicalRegressionInner.incidentAssembly_apply_external
      hierarchicalRegressionOutgoingState hierarchicalRegressionInnerIncident
      hierarchicalRegressionInnerOutputExternal]
    simp [hierarchicalRegressionIncidentState, hierarchicalRegressionInnerIncident]
  · rw [hierarchicalRegressionInner.incidentAssembly_apply_external
      hierarchicalRegressionOutgoingState hierarchicalRegressionInnerIncident
      hierarchicalRegressionInnerOutputLinkExternal]
    simp [hierarchicalRegressionIncidentState, hierarchicalRegressionInnerIncident]

/-- Every channel the inner stage exposes is one of its four declared external endpoints. -/
lemma hierarchicalRegression_inner_external_cases
    (channel : hierarchicalRegressionInner.ExternalChannel) :
    channel = hierarchicalRegressionInnerInputExternal ∨
      channel = hierarchicalRegressionInnerLinkExternal ∨
        channel = hierarchicalRegressionInnerOutputExternal ∨
          channel = hierarchicalRegressionInnerOutputLinkExternal := by
  rcases channel with ⟨⟨⟨component, port⟩, mode⟩, hChannel⟩
  cases component <;> cases port <;> cases mode
  · exact Or.inl rfl
  · exact absurd ⟨⟨(), Sum.inl ()⟩, rfl⟩ hChannel
  · exact Or.inr (Or.inl rfl)
  · exact absurd ⟨⟨(), Sum.inr ()⟩, rfl⟩ hChannel
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))

/-- The inner stage's external readout of the ambient outgoing state is its boundary outgoing
amplitude. -/
lemma hierarchicalRegression_inner_outputReadout :
    hierarchicalRegressionInnerOutgoing =
      hierarchicalRegressionInner.externalOutgoingReadout.toLinearMap
        hierarchicalRegressionOutgoingState := by
  classical
  rw [PortConnectionFamily.externalOutgoingReadout_apply]
  apply WithLp.ofLp_injective 2
  funext endpoint
  rcases endpoint with ⟨channel⟩
  rw [ModeAmplitude.restrictEmbedding_apply,
    PortConnectionFamily.externalOutgoingEmbedding_apply]
  rcases hierarchicalRegression_inner_external_cases channel with
    rfl | rfl | rfl | rfl <;>
    simp [hierarchicalRegressionInnerOutgoing, hierarchicalRegressionOutgoingState]

/-- **The inner subsystem netlist admits the hand-computed boundary pair**, proved from its own
three channel equations. -/
lemma hierarchicalRegression_mem_innerNetlist_behavior :
    (hierarchicalRegressionInnerIncident, hierarchicalRegressionInnerOutgoing) ∈
      hierarchicalRegression.innerNetlist.behavior := by
  classical
  exact (hierarchicalRegression.innerNetlist.mem_behavior_iff_componentBehavior
    hierarchicalRegressionInnerIncident hierarchicalRegressionInnerOutgoing).2
      ⟨hierarchicalRegressionIncidentState, hierarchicalRegressionOutgoingState,
        hierarchicalRegression_mem_componentBehavior,
        hierarchicalRegression_inner_incidentAssembly,
        hierarchicalRegression_inner_outputReadout⟩

/-!

## E. Membership in the outer closure of the inner subsystem's behavior

-/

/-- Classical equality on the boundary channels exposed by the inner stage. -/
local instance hierarchicalRegressionBoundaryChannelDecidableEq :
    DecidableEq hierarchicalRegressionInner.externalPortModeFamily.Channel := Classical.decEq _

/-- The boundary channels exposed by the inner stage are finite. -/
local instance hierarchicalRegressionBoundaryChannelFintype :
    Fintype hierarchicalRegressionInner.externalPortModeFamily.Channel :=
  Fintype.ofEquiv _ hierarchicalRegressionInner.boundaryChannelEquiv.symm

/-- The outer stage's external channels are finite. -/
local instance hierarchicalRegressionOuterExternalFintype :
    Fintype hierarchicalRegressionOuter.ExternalChannel := Fintype.ofFinite _

/-- The first component's outward port is left unconnected by the inner stage. -/
lemma hierarchicalRegression_inputOutward_unconnectedPort :
    (⟨.inputStage, false⟩ : hierarchicalRegressionComponents.aggregatePortModeFamily.Port) ∉
      Set.range hierarchicalRegressionInner.endpointEmbedding := by
  rintro ⟨⟨index, endpoint⟩, hPort⟩
  cases index
  cases endpoint
  · exact Bool.noConfusion (congrArg (fun port => port.2) hPort)
  · exact HierarchicalRegressionComponent.noConfusion (congrArg Sigma.fst hPort)

/-- The third component's outward port is left unconnected by the inner stage. -/
lemma hierarchicalRegression_outputOutward_unconnectedPort :
    (⟨.outputStage, false⟩ : hierarchicalRegressionComponents.aggregatePortModeFamily.Port) ∉
      Set.range hierarchicalRegressionInner.endpointEmbedding := by
  rintro ⟨⟨index, endpoint⟩, hPort⟩
  cases index
  cases endpoint <;>
    exact HierarchicalRegressionComponent.noConfusion (congrArg Sigma.fst hPort)

/-- The first component's outward port, as a boundary port of the inner stage. -/
abbrev hierarchicalRegressionInputBoundary :
    hierarchicalRegressionInner.externalPortModeFamily.Port :=
  ⟨⟨.inputStage, false⟩, hierarchicalRegression_inputOutward_unconnectedPort⟩

/-- The third component's outward port, as a boundary port of the inner stage. -/
abbrev hierarchicalRegressionOutputOutwardBoundary :
    hierarchicalRegressionInner.externalPortModeFamily.Port :=
  ⟨⟨.outputStage, false⟩, hierarchicalRegression_outputOutward_unconnectedPort⟩

/-- The outer stage's connected channels embed at the two boundary channels. -/
@[simp]
lemma hierarchicalRegression_outer_embed_left :
    hierarchicalRegressionOuter.channelEmbedding ⟨(), Sum.inl ()⟩ =
      (⟨hierarchicalRegressionLinkBoundary, ()⟩ :
        hierarchicalRegressionInner.externalPortModeFamily.Channel) := rfl

/-- The outer stage's connected channels embed at the two boundary channels. -/
@[simp]
lemma hierarchicalRegression_outer_embed_right :
    hierarchicalRegressionOuter.channelEmbedding ⟨(), Sum.inr ()⟩ =
      (⟨hierarchicalRegressionOutputBoundary, ()⟩ :
        hierarchicalRegressionInner.externalPortModeFamily.Channel) := rfl

/-- Mates in the outer stage exchange the two ends of its connection. -/
@[simp]
lemma hierarchicalRegression_outer_mate_left :
    hierarchicalRegressionOuter.mateEquiv ⟨(), Sum.inl ()⟩ = ⟨(), Sum.inr ()⟩ := rfl

/-- Mates in the outer stage exchange the two ends of its connection. -/
@[simp]
lemma hierarchicalRegression_outer_mate_right :
    hierarchicalRegressionOuter.mateEquiv ⟨(), Sum.inr ()⟩ = ⟨(), Sum.inl ()⟩ := rfl

/-- The outer stage connects exactly the two boundary channels it declares. -/
lemma hierarchicalRegression_outer_channelEmbedding_eq
    (channel : hierarchicalRegressionOuter.Channel) :
    hierarchicalRegressionOuter.channelEmbedding channel =
        (⟨hierarchicalRegressionLinkBoundary, ()⟩ :
          hierarchicalRegressionInner.externalPortModeFamily.Channel) ∨
      hierarchicalRegressionOuter.channelEmbedding channel =
        (⟨hierarchicalRegressionOutputBoundary, ()⟩ :
          hierarchicalRegressionInner.externalPortModeFamily.Channel) := by
  rcases channel with ⟨index, local'⟩
  cases index
  rcases local' with mode | mode <;> cases mode
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The first component's boundary channel is left external by the outer stage. -/
lemma hierarchicalRegression_outer_inputBoundary_external :
    (⟨hierarchicalRegressionInputBoundary, ()⟩ :
        hierarchicalRegressionInner.externalPortModeFamily.Channel) ∉
      Set.range hierarchicalRegressionOuter.channelEmbedding := by
  rintro ⟨channel, hChannel⟩
  rcases hierarchicalRegression_outer_channelEmbedding_eq channel with hEq | hEq <;>
    exact HierarchicalRegressionComponent.noConfusion
      (congrArg (fun boundary => boundary.1.1.1) (hEq ▸ hChannel))

/-- The third component's outward boundary channel is left external by the outer stage. -/
lemma hierarchicalRegression_outer_outputBoundary_external :
    (⟨hierarchicalRegressionOutputOutwardBoundary, ()⟩ :
        hierarchicalRegressionInner.externalPortModeFamily.Channel) ∉
      Set.range hierarchicalRegressionOuter.channelEmbedding := by
  rintro ⟨channel, hChannel⟩
  rcases hierarchicalRegression_outer_channelEmbedding_eq channel with hEq | hEq
  · exact HierarchicalRegressionComponent.noConfusion
      (congrArg (fun boundary => boundary.1.1.1) (hEq ▸ hChannel))
  · exact Bool.noConfusion
      (congrArg (fun boundary => boundary.1.1.2) (hEq ▸ hChannel))

/-- The drive channel, packaged as an external channel of the outer stage. -/
abbrev hierarchicalRegressionOuterInputExternal :
    hierarchicalRegressionOuter.ExternalChannel :=
  ⟨⟨hierarchicalRegressionInputBoundary, ()⟩,
    hierarchicalRegression_outer_inputBoundary_external⟩

/-- The response channel, packaged as an external channel of the outer stage. -/
abbrev hierarchicalRegressionOuterOutputExternal :
    hierarchicalRegressionOuter.ExternalChannel :=
  ⟨⟨hierarchicalRegressionOutputOutwardBoundary, ()⟩,
    hierarchicalRegression_outer_outputBoundary_external⟩

/-- Every channel the outer stage exposes is one of its two declared external endpoints. -/
lemma hierarchicalRegression_outer_external_cases
    (channel : hierarchicalRegressionOuter.ExternalChannel) :
    channel = hierarchicalRegressionOuterInputExternal ∨
      channel = hierarchicalRegressionOuterOutputExternal := by
  rcases channel with ⟨⟨⟨⟨component, port⟩, hPort⟩, mode⟩, hChannel⟩
  cases component <;> cases port <;> cases mode
  · exact Or.inl rfl
  · exact absurd (hPort ⟨((), PortConnection.End.left), rfl⟩) not_false
  · exact absurd ⟨⟨(), Sum.inl ()⟩, rfl⟩ hChannel
  · exact absurd (hPort ⟨((), PortConnection.End.right), rfl⟩) not_false
  · exact Or.inr rfl
  · exact absurd ⟨⟨(), Sum.inr ()⟩, rfl⟩ hChannel

/-- The inner boundary incident amplitudes in the outer stage's coordinates. -/
def hierarchicalRegressionBoundaryIncident :
    ModeAmplitude (Incident hierarchicalRegressionInner.externalPortModeFamily.Channel) :=
  WithLp.toLp 2 fun endpoint =>
    match endpoint.channel.1.1.1, endpoint.channel.1.1.2 with
    | .inputStage, false => 1
    | .outputStage, true => 15
    | _, _ => 0

/-- The inner boundary outgoing amplitudes in the outer stage's coordinates. -/
def hierarchicalRegressionBoundaryOutgoing :
    ModeAmplitude (Outgoing hierarchicalRegressionInner.externalPortModeFamily.Channel) :=
  WithLp.toLp 2 fun endpoint =>
    match endpoint.channel.1.1.1, endpoint.channel.1.1.2 with
    | .linkStage, false => 15
    | .outputStage, false => 165
    | _, _ => 0

/-- The drive in the outer stage's external coordinates. -/
def hierarchicalRegressionOuterInput :
    ModeAmplitude (Incident hierarchicalRegressionOuter.ExternalChannel) :=
  WithLp.toLp 2 fun endpoint =>
    match endpoint.channel.1.1.1.1 with
    | .inputStage => 1
    | _ => 0

/-- The response in the outer stage's external coordinates. -/
def hierarchicalRegressionOuterOutput :
    ModeAmplitude (Outgoing hierarchicalRegressionOuter.ExternalChannel) :=
  WithLp.toLp 2 fun endpoint =>
    match endpoint.channel.1.1.1.1 with
    | .outputStage => 165
    | _ => 0

/-- Relabelling the flattened drive into the outer-stage coordinates gives the hand-expanded
outer drive. -/
lemma hierarchicalRegression_outerInput_reindex :
    ModeAmplitude.reindex
        (Incident.relabelEquiv
          (hierarchicalRegressionInner.appendExternalChannelEquiv
            hierarchicalRegressionOuter))
        hierarchicalRegressionInput =
      hierarchicalRegressionOuterInput := by
  apply WithLp.ofLp_injective 2
  funext endpoint
  rfl

/-- Relabelling the flattened response into the outer-stage coordinates gives the hand-expanded
outer response. -/
lemma hierarchicalRegression_outerOutput_reindex :
    ModeAmplitude.reindex
        (Outgoing.relabelEquiv
          (hierarchicalRegressionInner.appendExternalChannelEquiv
            hierarchicalRegressionOuter))
        hierarchicalRegressionOutput =
      hierarchicalRegressionOuterOutput := by
  apply WithLp.ofLp_injective 2
  funext endpoint
  rfl

/-- Returning the hand-expanded boundary incident state to the inner external coordinates gives
the hand-expanded inner incident state. -/
lemma hierarchicalRegression_boundaryIncident_reindex :
    ModeAmplitude.reindex
        (Incident.relabelEquiv hierarchicalRegressionInner.boundaryChannelEquiv.symm).symm
        hierarchicalRegressionBoundaryIncident =
      hierarchicalRegressionInnerIncident := by
  apply WithLp.ofLp_injective 2
  funext endpoint
  rcases endpoint with ⟨channel⟩
  rcases hierarchicalRegression_inner_external_cases channel with
    rfl | rfl | rfl | rfl <;>
    simp [ModeAmplitude.reindex_apply, PortConnectionFamily.boundaryChannelEquiv,
      PortConnectionFamily.externalChannelEquivUnconnectedPortModes,
      hierarchicalRegressionBoundaryIncident, hierarchicalRegressionInnerIncident] <;>
    rfl

/-- Returning the hand-expanded boundary outgoing state to the inner external coordinates gives
the hand-expanded inner outgoing state. -/
lemma hierarchicalRegression_boundaryOutgoing_reindex :
    ModeAmplitude.reindex
        (Outgoing.relabelEquiv hierarchicalRegressionInner.boundaryChannelEquiv.symm).symm
        hierarchicalRegressionBoundaryOutgoing =
      hierarchicalRegressionInnerOutgoing := by
  apply WithLp.ofLp_injective 2
  funext endpoint
  rcases endpoint with ⟨channel⟩
  rcases hierarchicalRegression_inner_external_cases channel with
    rfl | rfl | rfl | rfl <;>
    simp [ModeAmplitude.reindex_apply, PortConnectionFamily.boundaryChannelEquiv,
      PortConnectionFamily.externalChannelEquivUnconnectedPortModes,
      hierarchicalRegressionBoundaryOutgoing, hierarchicalRegressionInnerOutgoing] <;>
    rfl

/-- The outer stage's own incident assembly holds at every boundary coordinate. -/
lemma hierarchicalRegression_outer_incidentAssembly :
    hierarchicalRegressionBoundaryIncident =
      hierarchicalRegressionOuter.incidentAssembly
        hierarchicalRegressionBoundaryOutgoing hierarchicalRegressionOuterInput := by
  classical
  apply WithLp.ofLp_injective 2
  funext endpoint
  rcases endpoint with ⟨⟨⟨⟨component, port⟩, hPort⟩, mode⟩⟩
  cases component <;> cases port <;> cases mode
  · rw [hierarchicalRegressionOuter.incidentAssembly_apply_external
      hierarchicalRegressionBoundaryOutgoing hierarchicalRegressionOuterInput
      hierarchicalRegressionOuterInputExternal]
    simp [hierarchicalRegressionBoundaryIncident, hierarchicalRegressionOuterInput]
  · exact absurd (hPort ⟨((), PortConnection.End.left), rfl⟩) not_false
  · rw [show (⟨⟨⟨HierarchicalRegressionComponent.linkStage, false⟩, hPort⟩, ()⟩ :
        hierarchicalRegressionInner.externalPortModeFamily.Channel) =
          hierarchicalRegressionOuter.channelEmbedding ⟨(), Sum.inl ()⟩ from rfl,
      hierarchicalRegressionOuter.incidentAssembly_apply_connected_channel
        hierarchicalRegressionBoundaryOutgoing hierarchicalRegressionOuterInput
        ⟨(), Sum.inl ()⟩]
    rw [hierarchicalRegression_outer_mate_left,
      hierarchicalRegression_outer_embed_left,
      hierarchicalRegression_outer_embed_right]
    simp [hierarchicalRegressionBoundaryIncident, hierarchicalRegressionBoundaryOutgoing]
  · exact absurd (hPort ⟨((), PortConnection.End.right), rfl⟩) not_false
  · rw [hierarchicalRegressionOuter.incidentAssembly_apply_external
      hierarchicalRegressionBoundaryOutgoing hierarchicalRegressionOuterInput
      hierarchicalRegressionOuterOutputExternal]
    simp [hierarchicalRegressionBoundaryIncident, hierarchicalRegressionOuterInput]
  · rw [show (⟨⟨⟨HierarchicalRegressionComponent.outputStage, true⟩, hPort⟩, ()⟩ :
        hierarchicalRegressionInner.externalPortModeFamily.Channel) =
          hierarchicalRegressionOuter.channelEmbedding ⟨(), Sum.inr ()⟩ from rfl,
      hierarchicalRegressionOuter.incidentAssembly_apply_connected_channel
        hierarchicalRegressionBoundaryOutgoing hierarchicalRegressionOuterInput
        ⟨(), Sum.inr ()⟩]
    rw [hierarchicalRegression_outer_mate_right,
      hierarchicalRegression_outer_embed_right,
      hierarchicalRegression_outer_embed_left]
    simp [hierarchicalRegressionBoundaryIncident, hierarchicalRegressionBoundaryOutgoing]

/-- The outer stage's external readout of the boundary outgoing amplitudes is the response. -/
lemma hierarchicalRegression_outer_outputReadout :
    hierarchicalRegressionOuterOutput =
      hierarchicalRegressionOuter.externalOutgoingReadout.toLinearMap
        hierarchicalRegressionBoundaryOutgoing := by
  classical
  rw [PortConnectionFamily.externalOutgoingReadout_apply]
  apply WithLp.ofLp_injective 2
  funext endpoint
  rcases endpoint with ⟨channel⟩
  rw [ModeAmplitude.restrictEmbedding_apply,
    PortConnectionFamily.externalOutgoingEmbedding_apply]
  rcases hierarchicalRegression_outer_external_cases channel with rfl | rfl <;>
    simp [hierarchicalRegressionOuterOutput, hierarchicalRegressionBoundaryOutgoing]

/-- **The outer closure of the inner subsystem's own behavior admits the same pair**, proved from
the closure's three membership equations and the inner netlist's own semantics, not from any
flattening theorem. -/
lemma hierarchicalRegression_mem_outerClosure :
    (ModeAmplitude.reindex
        (Incident.relabelEquiv
          (hierarchicalRegressionInner.appendExternalChannelEquiv
            hierarchicalRegressionOuter))
        hierarchicalRegressionInput,
      ModeAmplitude.reindex
        (Outgoing.relabelEquiv
          (hierarchicalRegressionInner.appendExternalChannelEquiv
            hierarchicalRegressionOuter))
        hierarchicalRegressionOutput) ∈
      hierarchicalRegressionOuter.closeBehavior
        (hierarchicalRegression.innerNetlist.behavior.reindex
          (Incident.relabelEquiv hierarchicalRegressionInner.boundaryChannelEquiv.symm)
          (Outgoing.relabelEquiv hierarchicalRegressionInner.boundaryChannelEquiv.symm)) := by
  classical
  rw [hierarchicalRegression_outerInput_reindex,
    hierarchicalRegression_outerOutput_reindex]
  let innerBehavior :
      LinearBehavior (Incident hierarchicalRegressionInner.ExternalChannel)
        (Outgoing hierarchicalRegressionInner.ExternalChannel) :=
    hierarchicalRegression.innerNetlist.behavior
  change (hierarchicalRegressionOuterInput, hierarchicalRegressionOuterOutput) ∈
    hierarchicalRegressionOuter.closeBehavior
      (innerBehavior.reindex
        (Incident.relabelEquiv hierarchicalRegressionInner.boundaryChannelEquiv.symm)
        (Outgoing.relabelEquiv hierarchicalRegressionInner.boundaryChannelEquiv.symm))
  rw [PortConnectionFamily.mem_closeBehavior_iff]
  refine ⟨hierarchicalRegressionBoundaryIncident, hierarchicalRegressionBoundaryOutgoing,
    ?_, hierarchicalRegression_outer_incidentAssembly,
    hierarchicalRegression_outer_outputReadout⟩
  rw [LinearBehavior.mem_reindex_iff,
    hierarchicalRegression_boundaryIncident_reindex,
    hierarchicalRegression_boundaryOutgoing_reindex]
  exact hierarchicalRegression_mem_innerNetlist_behavior

/-!

## F. A forced coefficient and the mis-lifted-port negative control

-/

/-- The flattened fixture's assembled scattering transform is the component-family transform in
the fixture's canonical ambient coordinates. -/
lemma hierarchicalRegression_scatteringTransform_eq :
    hierarchicalRegressionComponents.assembledScatteringMatrix.toOrientedModeTransform =
      hierarchicalRegression.flatten.scatteringTransform := by
  unfold FlatNetlist.scatteringTransform FlatNetlist.scatteringMatrix
  rfl

/-- The first component sends its outward incident amplitude to its link output with gain `3`. -/
lemma hierarchicalRegression_scattering_apply_inputLink
    (incident : ModeAmplitude (Incident HierarchicalRegressionChannel)) :
    hierarchicalRegressionComponents.assembledScatteringMatrix.toOrientedModeTransform.toLinearMap
        incident (Outgoing.mk hierarchicalRegressionInputLinkChannel) =
      3 * incident (Incident.mk hierarchicalRegressionInputChannel) := by
  classical
  rw [ScatteringMatrix.toLinearMap_toOrientedModeTransform,
    ModeAmplitude.reindex_apply]
  simp only [Equiv.symm_symm, Outgoing.channelEquiv_apply]
  change
    hierarchicalRegressionComponents.assembledScatteringMatrix.toModeTransform.toLinearMap
        (ModeAmplitude.reindex Incident.channelEquiv incident)
          (hierarchicalRegressionComponents.componentChannelEmbedding
            .inputStage ⟨true, ()⟩) = _
  rw [hierarchicalRegressionComponents.assembledScatteringMatrix_apply_component,
    Matrix.ofLp_toLpLin, Matrix.toLin'_apply]
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sigma,
    hierarchicalRegressionScattering,
    ModeAmplitude.restrictEmbedding_apply, ModeAmplitude.reindex_apply]
  change incident (Incident.mk hierarchicalRegressionInputChannel) =
    incident (Incident.mk hierarchicalRegressionInputChannel)
  rfl

/-- The second component sends its link incident amplitude outward with gain `5`. -/
lemma hierarchicalRegression_scattering_apply_linkOutward
    (incident : ModeAmplitude (Incident HierarchicalRegressionChannel)) :
    hierarchicalRegressionComponents.assembledScatteringMatrix.toOrientedModeTransform.toLinearMap
        incident (Outgoing.mk hierarchicalRegressionLinkOutwardChannel) =
      5 * incident (Incident.mk hierarchicalRegressionLinkLinkChannel) := by
  classical
  rw [ScatteringMatrix.toLinearMap_toOrientedModeTransform,
    ModeAmplitude.reindex_apply]
  simp only [Equiv.symm_symm, Outgoing.channelEquiv_apply]
  change
    hierarchicalRegressionComponents.assembledScatteringMatrix.toModeTransform.toLinearMap
        (ModeAmplitude.reindex Incident.channelEquiv incident)
          (hierarchicalRegressionComponents.componentChannelEmbedding
            .linkStage ⟨false, ()⟩) = _
  rw [hierarchicalRegressionComponents.assembledScatteringMatrix_apply_component,
    Matrix.ofLp_toLpLin, Matrix.toLin'_apply]
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sigma,
    hierarchicalRegressionScattering,
    ModeAmplitude.restrictEmbedding_apply, ModeAmplitude.reindex_apply]
  change incident (Incident.mk hierarchicalRegressionLinkLinkChannel) =
    incident (Incident.mk hierarchicalRegressionLinkLinkChannel)
  rfl

/-- The third component sends its link incident amplitude outward with gain `11`. -/
lemma hierarchicalRegression_scattering_apply_output
    (incident : ModeAmplitude (Incident HierarchicalRegressionChannel)) :
    hierarchicalRegressionComponents.assembledScatteringMatrix.toOrientedModeTransform.toLinearMap
        incident (Outgoing.mk hierarchicalRegressionOutputChannel) =
      11 * incident (Incident.mk hierarchicalRegressionOutputLinkChannel) := by
  classical
  rw [ScatteringMatrix.toLinearMap_toOrientedModeTransform,
    ModeAmplitude.reindex_apply]
  simp only [Equiv.symm_symm, Outgoing.channelEquiv_apply]
  change
    hierarchicalRegressionComponents.assembledScatteringMatrix.toModeTransform.toLinearMap
        (ModeAmplitude.reindex Incident.channelEquiv incident)
          (hierarchicalRegressionComponents.componentChannelEmbedding
            .outputStage ⟨false, ()⟩) = _
  rw [hierarchicalRegressionComponents.assembledScatteringMatrix_apply_component,
    Matrix.ofLp_toLpLin, Matrix.toLin'_apply]
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sigma,
    hierarchicalRegressionScattering,
    ModeAmplitude.restrictEmbedding_apply, ModeAmplitude.reindex_apply]
  change incident (Incident.mk hierarchicalRegressionOutputLinkChannel) =
    incident (Incident.mk hierarchicalRegressionOutputLinkChannel)
  rfl

/-- At the input channel, flattened incident assembly returns the external drive. -/
lemma hierarchicalRegression_incidentAssembly_apply_input
    (outgoing : ModeAmplitude (Outgoing HierarchicalRegressionChannel))
    (input : ModeAmplitude
      (Incident hierarchicalRegressionFlattenConnections.ExternalChannel)) :
    hierarchicalRegressionFlattenConnections.incidentAssembly outgoing input
        (Incident.mk hierarchicalRegressionInputChannel) =
      input (Incident.mk hierarchicalRegressionExternalInput) := by
  rw [hierarchicalRegressionFlattenConnections.incidentAssembly_apply_external
    outgoing input hierarchicalRegressionExternalInput]

/-- At the second component's link input, flattened incident assembly routes the first
component's link output. -/
lemma hierarchicalRegression_incidentAssembly_apply_linkLink
    (outgoing : ModeAmplitude (Outgoing HierarchicalRegressionChannel))
    (input : ModeAmplitude
      (Incident hierarchicalRegressionFlattenConnections.ExternalChannel)) :
    hierarchicalRegressionFlattenConnections.incidentAssembly outgoing input
        (Incident.mk hierarchicalRegressionLinkLinkChannel) =
      outgoing (Outgoing.mk hierarchicalRegressionInputLinkChannel) := by
  rw [show hierarchicalRegressionLinkLinkChannel =
      hierarchicalRegressionFlattenConnections.channelEmbedding
        ⟨Sum.inl (), Sum.inr ()⟩ from rfl,
    hierarchicalRegressionFlattenConnections.incidentAssembly_apply_connected_channel
      outgoing input ⟨Sum.inl (), Sum.inr ()⟩,
    hierarchicalRegression_flatten_mate_innerRight,
    hierarchicalRegression_flatten_embed_innerLeft_append]

/-- At the third component's link input, flattened incident assembly performs the outer-stage
port lift and routes the second component's outward output. -/
lemma hierarchicalRegression_incidentAssembly_apply_outputLink
    (outgoing : ModeAmplitude (Outgoing HierarchicalRegressionChannel))
    (input : ModeAmplitude
      (Incident hierarchicalRegressionFlattenConnections.ExternalChannel)) :
    hierarchicalRegressionFlattenConnections.incidentAssembly outgoing input
        (Incident.mk hierarchicalRegressionOutputLinkChannel) =
      outgoing (Outgoing.mk hierarchicalRegressionLinkOutwardChannel) := by
  rw [show hierarchicalRegressionOutputLinkChannel =
      hierarchicalRegressionFlattenConnections.channelEmbedding
        ⟨Sum.inr (), Sum.inr ()⟩ from rfl,
    hierarchicalRegressionFlattenConnections.incidentAssembly_apply_connected_channel
      outgoing input ⟨Sum.inr (), Sum.inr ()⟩,
    hierarchicalRegression_flatten_mate_outerRight,
    hierarchicalRegression_flatten_embed_outerLeft]

/-- Flattened external readout returns the third component's outward output on the response
channel. -/
lemma hierarchicalRegression_outputReadout_apply_output
    (outgoing : ModeAmplitude (Outgoing HierarchicalRegressionChannel)) :
    hierarchicalRegressionFlattenConnections.externalOutgoingReadout.toLinearMap outgoing
        (Outgoing.mk hierarchicalRegressionExternalOutput) =
      outgoing (Outgoing.mk hierarchicalRegressionOutputChannel) := by
  rw [PortConnectionFamily.externalOutgoingReadout_apply,
    ModeAmplitude.restrictEmbedding_apply,
    PortConnectionFamily.externalOutgoingEmbedding_apply]

/-- The component laws and the flattened incident assembly propagate the input through all
three distinct forward gains. -/
lemma hierarchicalRegression_forward_chain
    (incident : ModeAmplitude (Incident HierarchicalRegressionChannel))
    (outgoing : ModeAmplitude (Outgoing HierarchicalRegressionChannel))
    (input : ModeAmplitude
      (Incident hierarchicalRegressionFlattenConnections.ExternalChannel))
    (hScattering : outgoing =
      ModeTransform.toLinearMap
        hierarchicalRegressionComponents.assembledScatteringMatrix.toOrientedModeTransform
        incident)
    (hIncident : incident =
      hierarchicalRegressionFlattenConnections.incidentAssembly outgoing input) :
    outgoing (Outgoing.mk hierarchicalRegressionOutputChannel) =
      165 * input (Incident.mk hierarchicalRegressionExternalInput) := by
  have hInputLink := congrArg
    (fun amplitude => amplitude (Outgoing.mk hierarchicalRegressionInputLinkChannel))
    hScattering
  have hLinkOutward := congrArg
    (fun amplitude => amplitude (Outgoing.mk hierarchicalRegressionLinkOutwardChannel))
    hScattering
  have hOutput := congrArg
    (fun amplitude => amplitude (Outgoing.mk hierarchicalRegressionOutputChannel))
    hScattering
  rw [hierarchicalRegression_scattering_apply_inputLink] at hInputLink
  rw [hierarchicalRegression_scattering_apply_linkOutward] at hLinkOutward
  rw [hierarchicalRegression_scattering_apply_output] at hOutput
  calc
    outgoing (Outgoing.mk hierarchicalRegressionOutputChannel) =
        11 * incident (Incident.mk hierarchicalRegressionOutputLinkChannel) := hOutput
    _ = 11 * outgoing (Outgoing.mk hierarchicalRegressionLinkOutwardChannel) := by
      rw [hIncident, hierarchicalRegression_incidentAssembly_apply_outputLink]
    _ = 11 * (5 * incident (Incident.mk hierarchicalRegressionLinkLinkChannel)) := by
      rw [hLinkOutward]
    _ = 11 * (5 * outgoing (Outgoing.mk hierarchicalRegressionInputLinkChannel)) := by
      rw [hIncident, hierarchicalRegression_incidentAssembly_apply_linkLink]
    _ = 11 * (5 * (3 * incident (Incident.mk hierarchicalRegressionInputChannel))) := by
      rw [hInputLink]
    _ = 165 * input (Incident.mk hierarchicalRegressionExternalInput) := by
      rw [hIncident, hierarchicalRegression_incidentAssembly_apply_input]
      ring

/-- Every flattened solution forces the forward coefficient
`y(output) = 165 * u(input)`. -/
lemma hierarchicalRegression_flatten_output_forced
    (input : ModeAmplitude (Incident hierarchicalRegressionFlattenConnections.ExternalChannel))
    (output : ModeAmplitude
      (Outgoing hierarchicalRegressionFlattenConnections.ExternalChannel))
    (hBehavior : (input, output) ∈ hierarchicalRegression.flatten.behavior) :
    output (Outgoing.mk hierarchicalRegressionExternalOutput) =
      165 * input (Incident.mk hierarchicalRegressionExternalInput) := by
  classical
  rcases (hierarchicalRegression.flatten.mem_behavior_iff_componentBehavior
    input output).1 hBehavior with
    ⟨incident, outgoing, hComponent, hIncident, hOutput⟩
  have hScattering :=
    (hierarchicalRegression.flatten.mem_componentBehavior_iff incident outgoing).1 hComponent
  let canonicalIncident : ModeAmplitude (Incident HierarchicalRegressionChannel) := incident
  let canonicalOutgoing : ModeAmplitude (Outgoing HierarchicalRegressionChannel) := outgoing
  have hCanonicalScattering :
      canonicalOutgoing =
        ModeTransform.toLinearMap
          hierarchicalRegressionComponents.assembledScatteringMatrix.toOrientedModeTransform
          canonicalIncident := by
    rw [hierarchicalRegression_scatteringTransform_eq]
    exact hScattering
  have hCanonicalIncident :
      canonicalIncident =
        hierarchicalRegressionFlattenConnections.incidentAssembly canonicalOutgoing input :=
    hIncident
  have hCanonicalOutput :
      output =
        hierarchicalRegressionFlattenConnections.externalOutgoingReadout.toLinearMap
          canonicalOutgoing :=
    hOutput
  calc
    output (Outgoing.mk hierarchicalRegressionExternalOutput) =
        canonicalOutgoing (Outgoing.mk hierarchicalRegressionOutputChannel) := by
      rw [hCanonicalOutput, hierarchicalRegression_outputReadout_apply_output]
    _ = 165 * input (Incident.mk hierarchicalRegressionExternalInput) :=
      hierarchicalRegression_forward_chain canonicalIncident canonicalOutgoing input
        hCanonicalScattering hCanonicalIncident

/-- The deliberately mis-lifted response puts `165` on the input-stage output channel instead of
the output-stage output channel. -/
def hierarchicalRegressionMisLiftedOutput :
    ModeAmplitude (Outgoing hierarchicalRegressionFlattenConnections.ExternalChannel) :=
  WithLp.toLp 2 fun endpoint =>
    match endpoint.channel.1.1.1 with
    | .inputStage => 165
    | _ => 0

/-- The mis-lifted response is rejected by the flattened behavior. -/
lemma hierarchicalRegression_misLifted_not_mem_flatten_behavior :
    (hierarchicalRegressionInput, hierarchicalRegressionMisLiftedOutput) ∉
      hierarchicalRegression.flatten.behavior := by
  intro hBehavior
  have hForced := hierarchicalRegression_flatten_output_forced
    hierarchicalRegressionInput hierarchicalRegressionMisLiftedOutput hBehavior
  norm_num [hierarchicalRegressionInput, hierarchicalRegressionMisLiftedOutput] at hForced

end

end Optics
