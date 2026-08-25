/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.FlatNetlistRegression
public import Physlib.Optics.Network.WiringInvariance

/-!
# Regression tests for flat-netlist wiring invariance

## i. Overview

The singular two-component flat-netlist fixture is presented in two different ways. The first
exchanges the left/right presentation of its internal connection. The second changes the
connection index type from `Unit` to `Fin 1`. Exact channel, routing, solution, and external-output
sentinels verify that both presentations retain the same physical wiring.

The transported netlists remain multivalued at zero input and have no solution for the hostile
input. These checks make the invariance result exercise relational semantics directly: neither
fixture admits an inverse-based or unique-solution shortcut.

## ii. Scope

The scalar component coefficients remain algebraic sentinels. The tests establish wiring
presentation invariance only; they make no passivity, losslessness, reciprocity, causality, or
electromagnetic-normalization claim. A non-involutive index-direction sentinel requires a future
fixture with at least three connections.

## iii. Table of contents

- A. Shared finite instances
- B. Endpoint-presentation exchange
- C. Connection-index type change

-/

@[expose] public section

namespace Optics

noncomputable section

/-!

## A. Shared finite instances

-/

/-- Each local component-channel family in the singular fixture is finite. -/
local instance wiringInvarianceRegressionLocalChannelFintype (component : Bool) :
    Fintype (flatNetlistRegressionComponents.portFamily component).Channel := by
  change Fintype (Σ _ : Bool, Unit)
  infer_instance

/-- The singular fixture's ambient channel family is finite. -/
local instance wiringInvarianceRegressionChannelFintype :
    Fintype flatNetlistRegression.Channel :=
  Fintype.ofEquiv flatNetlistRegressionComponents.IndexedChannel
    flatNetlistRegressionComponents.channelEquiv

/-- The singular fixture's ambient channels have decidable equality. -/
local instance wiringInvarianceRegressionChannelDecidableEq :
    DecidableEq flatNetlistRegression.Channel :=
  Classical.decEq _

/-- The singular fixture's original connected-channel family is finite. -/
local instance wiringInvarianceRegressionConnectedFintype :
    Fintype flatNetlistRegression.ConnectedChannel := by
  change Fintype (Σ _ : Unit, Unit ⊕ Unit)
  infer_instance

/-- The original connected-channel presentation has decidable equality. -/
local instance wiringInvarianceRegressionConnectedDecidableEq :
    DecidableEq flatNetlistRegression.ConnectedChannel :=
  Classical.decEq _

/-- The singular fixture's original external-channel family is finite. -/
local instance wiringInvarianceRegressionExternalFintype :
    Fintype flatNetlistRegression.ExternalChannel := by
  classical
  exact Fintype.ofFinite _

/-!

## B. Endpoint-presentation exchange

-/

/-- The singular fixture with its sole connection presented in the opposite endpoint order. -/
abbrev wiringInvarianceRegressionSymmNetlist : FlatNetlist :=
  flatNetlistRegression.symmConnections

/-- The wiring equivalence induced by exchanging the sole connection's endpoints. -/
abbrev wiringInvarianceRegressionSymm :
    PortConnectionFamily.WiringEquiv flatNetlistRegression.connections
      wiringInvarianceRegressionSymmNetlist.connections :=
  PortConnectionFamily.WiringEquiv.ofSymm flatNetlistRegression.connections

/-- The endpoint-exchanged fixture's connected-channel family is finite. -/
local instance wiringInvarianceRegressionSymmConnectedFintype :
    Fintype wiringInvarianceRegressionSymmNetlist.ConnectedChannel :=
  Fintype.ofEquiv flatNetlistRegression.ConnectedChannel
    wiringInvarianceRegressionSymm.toEquiv

/-- The endpoint-exchanged connected channels have decidable equality. -/
local instance wiringInvarianceRegressionSymmConnectedDecidableEq :
    DecidableEq wiringInvarianceRegressionSymmNetlist.ConnectedChannel :=
  Classical.decEq _

/-- The endpoint-exchanged fixture's external-channel family is finite. -/
local instance wiringInvarianceRegressionSymmExternalFintype :
    Fintype wiringInvarianceRegressionSymmNetlist.ExternalChannel :=
  Fintype.ofEquiv flatNetlistRegression.ExternalChannel
    wiringInvarianceRegressionSymm.externalChannelEquiv

/-- Endpoint exchange sends the old first-end label to the new second-end label. -/
lemma wiringInvarianceRegression_symm_channelEquiv_aLink :
    wiringInvarianceRegressionSymm.toEquiv flatNetlistRegressionConnectedA =
      (⟨(), Sum.inr ()⟩ : wiringInvarianceRegressionSymmNetlist.ConnectedChannel) := rfl

/-- The new second-end label still embeds at the first component's physical link channel. -/
lemma wiringInvarianceRegression_symm_channelEmbedding_aLink :
    wiringInvarianceRegressionSymmNetlist.connections.channelEmbedding
        ⟨(), Sum.inr ()⟩ =
      flatNetlistRegressionALink := rfl

/-- Endpoint presentation exchange leaves the ambient routing matrix literally unchanged. -/
lemma wiringInvarianceRegression_symm_routingTransform :
    wiringInvarianceRegressionSymmNetlist.routingTransform =
      flatNetlistRegression.routingTransform :=
  FlatNetlist.routingTransform_withConnections
    flatNetlistRegression.connections.symm wiringInvarianceRegressionSymm

/-- The exchanged presentation still routes the second link output into the first link input. -/
lemma wiringInvarianceRegression_symm_routing_entry_mate :
    wiringInvarianceRegressionSymmNetlist.routingTransform
        (Incident.mk flatNetlistRegressionALink)
        (Outgoing.mk flatNetlistRegressionBLink) = 1 := by
  rw [wiringInvarianceRegression_symm_routingTransform]
  exact flatNetlistRegression.connections.partialRouting_entry_mate
    flatNetlistRegressionConnectedB

/-- The exchanged presentation still has no self-routing entry at the first link. -/
lemma wiringInvarianceRegression_symm_routing_entry_self :
    wiringInvarianceRegressionSymmNetlist.routingTransform
        (Incident.mk flatNetlistRegressionALink)
        (Outgoing.mk flatNetlistRegressionALink) = 0 := by
  rw [wiringInvarianceRegression_symm_routingTransform]
  change flatNetlistRegression.connections.partialRouting
      (Incident.mk
        (flatNetlistRegression.connections.channelEmbedding
          flatNetlistRegressionConnectedA))
      (Outgoing.mk
        (flatNetlistRegression.connections.channelEmbedding
          flatNetlistRegressionConnectedA)) = 0
  rw [flatNetlistRegression.connections.partialRouting_entry_connected]
  exact flatNetlistRegression.connections.idealRouting_entry_self
    flatNetlistRegressionConnectedA

/-- The canonically transported first external channel of the exchanged presentation. -/
abbrev wiringInvarianceRegressionSymmExternalA :
    wiringInvarianceRegressionSymmNetlist.ExternalChannel :=
  wiringInvarianceRegressionSymm.externalChannelEquiv flatNetlistRegressionExternalA

/-- The canonically transported second external channel of the exchanged presentation. -/
abbrev wiringInvarianceRegressionSymmExternalB :
    wiringInvarianceRegressionSymmNetlist.ExternalChannel :=
  wiringInvarianceRegressionSymm.externalChannelEquiv flatNetlistRegressionExternalB

/-- The transported external output of the endpoint-exchanged fixture. -/
def wiringInvarianceRegressionSymmOutput (t : ℂ) :
    ModeAmplitude wiringInvarianceRegressionSymmNetlist.ExternalOutgoing :=
  ModeAmplitude.reindex wiringInvarianceRegressionSymm.externalOutgoingEquiv
    (flatNetlistRegressionOutput t)

/-- Every singular zero-input solution transports to the endpoint-exchanged fixture. -/
lemma wiringInvarianceRegression_symm_solution (t : ℂ) :
    (ModeAmplitude.reindex wiringInvarianceRegressionSymm.externalIncidentEquiv 0,
        (flatNetlistRegressionIncident t).directSum
          (flatNetlistRegressionOutgoing t)) ∈
      wiringInvarianceRegressionSymmNetlist.solutionBehavior :=
  (FlatNetlist.mem_solutionBehavior_withConnections_iff
    flatNetlistRegression.connections.symm wiringInvarianceRegressionSymm
      0 (flatNetlistRegressionIncident t) (flatNetlistRegressionOutgoing t)).mpr
        (flatNetlistRegression_solution t)

/-- Every singular external behavior member transports to the endpoint-exchanged fixture. -/
lemma wiringInvarianceRegression_symm_behavior_member (t : ℂ) :
    (ModeAmplitude.reindex wiringInvarianceRegressionSymm.externalIncidentEquiv 0,
        wiringInvarianceRegressionSymmOutput t) ∈
      wiringInvarianceRegressionSymmNetlist.behavior :=
  (FlatNetlist.mem_behavior_withConnections_iff
    flatNetlistRegression.connections.symm wiringInvarianceRegressionSymm
      0 (flatNetlistRegressionOutput t)).mpr
        (flatNetlistRegression_behavior_member t)

/-- For `t = 2 + I`, the transported first external output remains `2 + I`. -/
lemma wiringInvarianceRegression_symm_output_aExternal :
    wiringInvarianceRegressionSymmOutput (2 + Complex.I)
        (Outgoing.mk wiringInvarianceRegressionSymmExternalA) =
      2 + Complex.I := by
  rw [wiringInvarianceRegressionSymmOutput, ModeAmplitude.reindex_apply]
  change flatNetlistRegressionOutput (2 + Complex.I)
      (wiringInvarianceRegressionSymm.externalOutgoingEquiv.symm
        (wiringInvarianceRegressionSymm.externalOutgoingEquiv
          (Outgoing.mk flatNetlistRegressionExternalA))) = _
  rw [Equiv.symm_apply_apply,
    flatNetlistRegression_output_apply_aExternal]

/-- For `t = 2 + I`, the transported second external output remains `4 + 2I`. -/
lemma wiringInvarianceRegression_symm_output_bExternal :
    wiringInvarianceRegressionSymmOutput (2 + Complex.I)
        (Outgoing.mk wiringInvarianceRegressionSymmExternalB) =
      4 + 2 * Complex.I := by
  rw [wiringInvarianceRegressionSymmOutput, ModeAmplitude.reindex_apply]
  change flatNetlistRegressionOutput (2 + Complex.I)
      (wiringInvarianceRegressionSymm.externalOutgoingEquiv.symm
        (wiringInvarianceRegressionSymm.externalOutgoingEquiv
          (Outgoing.mk flatNetlistRegressionExternalB))) = _
  rw [Equiv.symm_apply_apply,
    flatNetlistRegression_output_apply_bExternal]
  ring

/-- Endpoint exchange preserves multivaluedness of the complete singular solution relation. -/
lemma wiringInvarianceRegression_symm_solutionBehavior_not_singleValued :
    ¬wiringInvarianceRegressionSymmNetlist.solutionBehavior.IsSingleValued := by
  intro hSingleValued
  apply flatNetlistRegression_solutionState_zero_ne_one
  exact hSingleValued (wiringInvarianceRegression_symm_solution 0)
    (wiringInvarianceRegression_symm_solution 1)

/-- Endpoint exchange preserves multivaluedness of the singular external behavior. -/
lemma wiringInvarianceRegression_symm_behavior_not_singleValued :
    ¬wiringInvarianceRegressionSymmNetlist.behavior.IsSingleValued := by
  intro hSingleValued
  apply flatNetlistRegression_output_zero_ne_one
  apply (ModeAmplitude.reindex
    wiringInvarianceRegressionSymm.externalOutgoingEquiv).injective
  exact hSingleValued (wiringInvarianceRegression_symm_behavior_member 0)
    (wiringInvarianceRegression_symm_behavior_member 1)

/-- Endpoint exchange preserves failure of totality for the complete solution relation. -/
lemma wiringInvarianceRegression_symm_solutionBehavior_not_total :
    ¬wiringInvarianceRegressionSymmNetlist.solutionBehavior.IsTotal := by
  intro hTotal
  let newInput := ModeAmplitude.reindex
    wiringInvarianceRegressionSymm.externalIncidentEquiv flatNetlistRegressionBadInput
  rcases hTotal newInput with ⟨state, hState⟩
  let incident := state.restrictInl
  let outgoing := state.restrictInr
  have hStateEq : state = incident.directSum outgoing :=
    (ModeAmplitude.directSum_restrict state).symm
  apply flatNetlistRegression_badInput_no_solution
  refine ⟨incident.directSum outgoing, ?_⟩
  apply (FlatNetlist.mem_solutionBehavior_withConnections_iff
    flatNetlistRegression.connections.symm wiringInvarianceRegressionSymm
      flatNetlistRegressionBadInput incident outgoing).mp
  rw [← hStateEq]
  exact hState

/-- Endpoint exchange preserves failure of totality for the projected external behavior. -/
lemma wiringInvarianceRegression_symm_behavior_not_total :
    ¬wiringInvarianceRegressionSymmNetlist.behavior.IsTotal := by
  intro hTotal
  let newInput := ModeAmplitude.reindex
    wiringInvarianceRegressionSymm.externalIncidentEquiv flatNetlistRegressionBadInput
  rcases hTotal newInput with ⟨newOutput, hOutput⟩
  let oldOutput := ModeAmplitude.reindex
    wiringInvarianceRegressionSymm.externalOutgoingEquiv.symm newOutput
  apply flatNetlistRegression_badInput_not_mem_behavior oldOutput
  rw [FlatNetlist.behavior_withConnections
    flatNetlistRegression.connections.symm wiringInvarianceRegressionSymm,
    LinearBehavior.mem_reindex_iff] at hOutput
  simpa only [newInput, oldOutput, ModeAmplitude.reindex_symm_reindex] using hOutput

/-!

## C. Connection-index type change

-/

/-- The singleton index equivalence used to replace `Unit` by `Fin 1`. -/
abbrev wiringInvarianceRegressionIndexEquiv : Unit ≃ Fin 1 :=
  finOneEquiv.symm

/-- The singular fixture with its connection indexed by `Fin 1`. -/
abbrev wiringInvarianceRegressionReindexedNetlist : FlatNetlist :=
  flatNetlistRegression.reindexConnections wiringInvarianceRegressionIndexEquiv

/-- The wiring equivalence induced by the singleton connection-index change. -/
abbrev wiringInvarianceRegressionReindex :
    PortConnectionFamily.WiringEquiv flatNetlistRegression.connections
      wiringInvarianceRegressionReindexedNetlist.connections :=
  PortConnectionFamily.WiringEquiv.ofReindex flatNetlistRegression.connections
    wiringInvarianceRegressionIndexEquiv

/-- The reindexed fixture's connected-channel family is finite. -/
local instance wiringInvarianceRegressionReindexedConnectedFintype :
    Fintype wiringInvarianceRegressionReindexedNetlist.ConnectedChannel :=
  Fintype.ofEquiv flatNetlistRegression.ConnectedChannel
    wiringInvarianceRegressionReindex.toEquiv

/-- The `Fin 1`-indexed connected channels have decidable equality. -/
local instance wiringInvarianceRegressionReindexedConnectedDecidableEq :
    DecidableEq wiringInvarianceRegressionReindexedNetlist.ConnectedChannel :=
  Classical.decEq _

/-- The reindexed fixture's external-channel family is finite. -/
local instance wiringInvarianceRegressionReindexedExternalFintype :
    Fintype wiringInvarianceRegressionReindexedNetlist.ExternalChannel :=
  Fintype.ofEquiv flatNetlistRegression.ExternalChannel
    wiringInvarianceRegressionReindex.externalChannelEquiv

/-- The old first link label becomes the corresponding `Fin 1`-indexed label. -/
lemma wiringInvarianceRegression_reindex_channelEquiv_aLink :
    wiringInvarianceRegressionReindex.toEquiv flatNetlistRegressionConnectedA =
      (⟨0, Sum.inl ()⟩ :
        wiringInvarianceRegressionReindexedNetlist.ConnectedChannel) := by
  rfl

/-- The `Fin 1`-indexed first link still embeds at the same ambient physical channel. -/
lemma wiringInvarianceRegression_reindex_channelEmbedding_aLink :
    wiringInvarianceRegressionReindexedNetlist.connections.channelEmbedding
        ⟨0, Sum.inl ()⟩ =
      flatNetlistRegressionALink := rfl

/-- Changing the singleton index type leaves the ambient routing matrix literally unchanged. -/
lemma wiringInvarianceRegression_reindex_routingTransform :
    wiringInvarianceRegressionReindexedNetlist.routingTransform =
      flatNetlistRegression.routingTransform :=
  FlatNetlist.routingTransform_withConnections
    (flatNetlistRegression.connections.reindex wiringInvarianceRegressionIndexEquiv)
      wiringInvarianceRegressionReindex

/-- A nonreal singular solution transports across the connection-index type change. -/
lemma wiringInvarianceRegression_reindex_solution :
    (ModeAmplitude.reindex wiringInvarianceRegressionReindex.externalIncidentEquiv 0,
        (flatNetlistRegressionIncident (2 + Complex.I)).directSum
          (flatNetlistRegressionOutgoing (2 + Complex.I))) ∈
      wiringInvarianceRegressionReindexedNetlist.solutionBehavior :=
  (FlatNetlist.mem_solutionBehavior_withConnections_iff
    (flatNetlistRegression.connections.reindex wiringInvarianceRegressionIndexEquiv)
      wiringInvarianceRegressionReindex 0
        (flatNetlistRegressionIncident (2 + Complex.I))
        (flatNetlistRegressionOutgoing (2 + Complex.I))).mpr
          (flatNetlistRegression_solution (2 + Complex.I))

/-- The hostile input still has no complete solution after changing the index type. -/
lemma wiringInvarianceRegression_reindex_badInput_no_solution :
    ¬∃ state,
      (ModeAmplitude.reindex wiringInvarianceRegressionReindex.externalIncidentEquiv
          flatNetlistRegressionBadInput,
        state) ∈ wiringInvarianceRegressionReindexedNetlist.solutionBehavior := by
  rintro ⟨state, hState⟩
  let incident := state.restrictInl
  let outgoing := state.restrictInr
  have hStateEq : state = incident.directSum outgoing :=
    (ModeAmplitude.directSum_restrict state).symm
  apply flatNetlistRegression_badInput_no_solution
  refine ⟨incident.directSum outgoing, ?_⟩
  apply (FlatNetlist.mem_solutionBehavior_withConnections_iff
    (flatNetlistRegression.connections.reindex wiringInvarianceRegressionIndexEquiv)
      wiringInvarianceRegressionReindex flatNetlistRegressionBadInput incident outgoing).mp
  rw [← hStateEq]
  exact hState

end

end Optics
