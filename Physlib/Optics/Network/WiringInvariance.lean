/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.FlatNetlist

/-!
# Invariance of optical netlists under wiring presentation changes

## i. Overview

Two connection families on the same ambient port family describe the same physical wiring when a
connected-channel equivalence preserves both the ambient channel embedding and the mate relation.
This criterion includes connection-index relabelling and exchange of every connection's endpoint
presentation.

The ambient partial-routing matrix is literally unchanged by such a presentation change. External
channel types are different subtypes of the same ambient channel family, so their amplitudes and
behaviors are instead transported along a canonical equivalence that preserves the underlying
ambient channel.

## ii. Key results

- `PortConnectionFamily.WiringEquiv`: equivalence of connected labels preserving physical wiring.
- `PortConnectionFamily.WiringEquiv.ofReindex`: index relabelling preserves wiring.
- `PortConnectionFamily.WiringEquiv.ofSymm`: endpoint-presentation exchange preserves wiring.
- `PortConnectionFamily.WiringEquiv.partialRouting_eq`: ambient routing is literally invariant.
- `FlatNetlist.behavior_withConnections`: external behavior changes only by canonical relabelling.

## iii. Table of contents

- A. Wiring-preserving connected-channel equivalences
- B. Connected and external channel invariance
- C. Derived boundary-map invariance
- D. Flat-netlist invariance

## iv. References

This file fixes the ambient port family. Reordering components changes that family and requires a
separate covariance theorem. A mode phase gauge changes transform entries and is also covariance,
not wiring invariance. No inverse, determinant, functionality, existence, or uniqueness hypothesis
is used: the results apply unchanged to partial and multivalued network behaviors.

-/

@[expose] public section

namespace Optics

noncomputable section

universe u v w x y

namespace PortConnectionFamily

variable {P : PortModeFamily.{u, v}} {ι : Type w} {ι' : Type x}
  (family : PortConnectionFamily P ι) (family' : PortConnectionFamily P ι')

/-!

## A. Wiring-preserving connected-channel equivalences

-/

/-- An equivalence of connected-channel labels that preserves their ambient channels and mates.

Both families live on the same ambient port family. The two compatibility laws say that only the
presentation of the wiring changes, not which ambient channels are connected or how they pair.
-/
structure WiringEquiv where
  /-- The relabelling between the two dependent connected-channel families. -/
  toEquiv : family.Channel ≃ family'.Channel
  /-- Relabelled connected channels select the same ambient physical channels. -/
  channelEmbedding_apply :
    ∀ channel, family'.channelEmbedding (toEquiv channel) = family.channelEmbedding channel
  /-- Relabelling commutes with the fixed-point-free mate permutations. -/
  mateEquiv_apply :
    ∀ channel,
      family'.mateEquiv (toEquiv channel) = toEquiv (family.mateEquiv channel)

namespace WiringEquiv

variable {family : PortConnectionFamily P ι}
  {family' : PortConnectionFamily P ι'}

/-- Reversing a wiring equivalence preserves both compatibility laws. -/
def symm (wiring : WiringEquiv family family') : WiringEquiv family' family where
  toEquiv := wiring.toEquiv.symm
  channelEmbedding_apply channel := by
    simpa using
      (wiring.channelEmbedding_apply (wiring.toEquiv.symm channel)).symm
  mateEquiv_apply channel := by
    apply wiring.toEquiv.injective
    simpa using
      (wiring.mateEquiv_apply (wiring.toEquiv.symm channel)).symm

/-- The dependent connected-channel equivalence induced by connection-index relabelling. -/
def reindexChannelEquiv (family : PortConnectionFamily P ι) (e : ι ≃ ι') :
    family.Channel ≃ (family.reindex e).Channel :=
  (Equiv.sigmaCongrLeft
      (β := fun index => (family.connection index).LocalChannel) e.symm :
    (family.reindex e).Channel ≃ family.Channel).symm

/-- Connection-index relabelling preserves the physical wiring. -/
def ofReindex (family : PortConnectionFamily P ι) (e : ι ≃ ι') :
    WiringEquiv family (family.reindex e) := by
  let backward : WiringEquiv (family.reindex e) family :=
    { toEquiv := (reindexChannelEquiv family e).symm
      channelEmbedding_apply := by
        rintro ⟨index, channel⟩
        rfl
      mateEquiv_apply := by
        rintro ⟨index, channel⟩
        change family.mateEquiv
            ((reindexChannelEquiv family e).symm ⟨index, channel⟩) =
          (reindexChannelEquiv family e).symm
            ((family.reindex e).mateEquiv ⟨index, channel⟩)
        rfl }
  exact backward.symm

/-- Exchanging every connection's endpoint presentation preserves the physical wiring. -/
def ofSymm (family : PortConnectionFamily P ι) : WiringEquiv family family.symm where
  toEquiv :=
    (Equiv.sigmaCongrRight fun index =>
      (family.connection index).swapLocalChannel :
        family.Channel ≃ family.symm.Channel)
  channelEmbedding_apply := by
    rintro ⟨index, channel⟩
    exact (family.connection index).symm_channelEmbedding_swapLocalChannel channel
  mateEquiv_apply := by
    rintro ⟨index, channel⟩
    exact congrArg (fun localChannel => Sigma.mk index localChannel)
      ((family.connection index).swapLocalChannel_mateEquiv channel).symm

/-!

## B. Connected and external channel invariance

-/

/-- Wiring-equivalent families select exactly the same set of ambient channels. -/
lemma range_channelEmbedding_eq (wiring : WiringEquiv family family') :
    Set.range family'.channelEmbedding = Set.range family.channelEmbedding := by
  ext ambient
  constructor
  · rintro ⟨channel, hChannel⟩
    obtain ⟨oldChannel, hOldChannel⟩ :=
      (PortConnectionFamily.WiringEquiv.toEquiv wiring).surjective channel
    subst channel
    exact ⟨oldChannel,
      (PortConnectionFamily.WiringEquiv.channelEmbedding_apply wiring oldChannel).symm.trans
        hChannel⟩
  · rintro ⟨channel, hChannel⟩
    exact ⟨PortConnectionFamily.WiringEquiv.toEquiv wiring channel,
      (PortConnectionFamily.WiringEquiv.channelEmbedding_apply wiring channel).trans
        hChannel⟩

/-- The canonical equivalence between the two external-channel subtypes.

It changes only the proof that an ambient channel is external; its underlying ambient channel is
definitionally unchanged.
-/
def externalChannelEquiv (wiring : WiringEquiv family family') :
    family.ExternalChannel ≃ family'.ExternalChannel :=
  Equiv.subtypeEquivRight fun ambient => by
    change ambient ∉ Set.range family.channelEmbedding ↔
      ambient ∉ Set.range family'.channelEmbedding
    rw [range_channelEmbedding_eq wiring]

/-- Canonical external-channel transport preserves the underlying ambient channel. -/
@[simp]
lemma externalChannelEquiv_val (wiring : WiringEquiv family family')
    (channel : family.ExternalChannel) :
    (externalChannelEquiv wiring channel).1 = channel.1 := rfl

/-- The canonical external-channel equivalence lifted to incident endpoint labels. -/
def externalIncidentEquiv (wiring : WiringEquiv family family') :
    Incident family.ExternalChannel ≃ Incident family'.ExternalChannel :=
  Incident.relabelEquiv (externalChannelEquiv wiring)

/-- The canonical external-channel equivalence lifted to outgoing endpoint labels. -/
def externalOutgoingEquiv (wiring : WiringEquiv family family') :
    Outgoing family.ExternalChannel ≃ Outgoing family'.ExternalChannel :=
  Outgoing.relabelEquiv (externalChannelEquiv wiring)

/-- Ideal connected routing changes covariantly under the connected-channel relabelling. -/
lemma idealRouting_eq_reindex (wiring : WiringEquiv family family')
    [DecidableEq family.Channel]
    [DecidableEq family'.Channel] :
    family'.idealRouting =
      family.idealRouting.reindex
        (Outgoing.relabelEquiv
          (PortConnectionFamily.WiringEquiv.toEquiv wiring))
        (Incident.relabelEquiv
          (PortConnectionFamily.WiringEquiv.toEquiv wiring)) := by
  have hMate :
      (PortConnectionFamily.WiringEquiv.toEquiv wiring).symm.trans
          (family.mateEquiv.trans
            (PortConnectionFamily.WiringEquiv.toEquiv wiring)) =
        family'.mateEquiv := by
    apply Equiv.ext
    intro channel
    obtain ⟨oldChannel, rfl⟩ :=
      (PortConnectionFamily.WiringEquiv.toEquiv wiring).surjective channel
    simpa using
      (PortConnectionFamily.WiringEquiv.mateEquiv_apply wiring oldChannel).symm
  unfold PortConnectionFamily.idealRouting
  rw [ModeTransform.idealRouting_reindex, hMate]

/-- Wiring-equivalent presentations have the same ambient routing entry between any two selected
connected channels. -/
lemma partialRouting_entry_connected_eq (wiring : WiringEquiv family family')
    [Fintype family.Channel] [DecidableEq family.Channel]
    [Fintype family'.Channel] [DecidableEq family'.Channel] [DecidableEq P.Channel]
    (incidentChannel outgoingChannel : family.Channel) :
    family'.partialRouting
          (Incident.mk (family.channelEmbedding incidentChannel))
          (Outgoing.mk (family.channelEmbedding outgoingChannel)) =
      family.partialRouting
        (Incident.mk (family.channelEmbedding incidentChannel))
        (Outgoing.mk (family.channelEmbedding outgoingChannel)) := by
  have hIdeal := congrArg
    (fun transform =>
      transform
        (Incident.mk
          (PortConnectionFamily.WiringEquiv.toEquiv wiring incidentChannel))
        (Outgoing.mk
          (PortConnectionFamily.WiringEquiv.toEquiv wiring outgoingChannel)))
    (idealRouting_eq_reindex wiring)
  calc
    family'.partialRouting
          (Incident.mk (family.channelEmbedding incidentChannel))
          (Outgoing.mk (family.channelEmbedding outgoingChannel)) =
        family'.partialRouting
          (Incident.mk
            (family'.channelEmbedding
              (PortConnectionFamily.WiringEquiv.toEquiv wiring incidentChannel)))
          (Outgoing.mk
            (family'.channelEmbedding
              (PortConnectionFamily.WiringEquiv.toEquiv wiring outgoingChannel))) := by
              rw [PortConnectionFamily.WiringEquiv.channelEmbedding_apply,
                PortConnectionFamily.WiringEquiv.channelEmbedding_apply]
    _ = family'.idealRouting
          (Incident.mk
            (PortConnectionFamily.WiringEquiv.toEquiv wiring incidentChannel))
          (Outgoing.mk
            (PortConnectionFamily.WiringEquiv.toEquiv wiring outgoingChannel)) := by
            rw [family'.partialRouting_entry_connected]
    _ = family.idealRouting (Incident.mk incidentChannel)
          (Outgoing.mk outgoingChannel) := by
            simpa only [ModeTransform.reindex_apply,
              ← Incident.relabelEquiv_apply,
              ← Outgoing.relabelEquiv_apply, Equiv.symm_apply_apply] using hIdeal
    _ = family.partialRouting
          (Incident.mk (family.channelEmbedding incidentChannel))
          (Outgoing.mk (family.channelEmbedding outgoingChannel)) := by
            rw [family.partialRouting_entry_connected]

/-- The ambient partial-routing matrix is literally unchanged by a wiring presentation change. -/
lemma partialRouting_eq (wiring : WiringEquiv family family')
    [Fintype family.Channel] [DecidableEq family.Channel]
    [Fintype family'.Channel] [DecidableEq family'.Channel] [DecidableEq P.Channel] :
    family'.partialRouting = family.partialRouting := by
  ext incident outgoing
  rcases incident with ⟨incident⟩
  rcases outgoing with ⟨outgoing⟩
  by_cases hIncident : incident ∈ Set.range family.channelEmbedding
  · rcases hIncident with ⟨incidentChannel, rfl⟩
    by_cases hOutgoing : outgoing ∈ Set.range family.channelEmbedding
    · rcases hOutgoing with ⟨outgoingChannel, rfl⟩
      exact partialRouting_entry_connected_eq wiring incidentChannel outgoingChannel
    · have hOutgoing' :
          outgoing ∉ Set.range family'.channelEmbedding := by
        simpa only [range_channelEmbedding_eq wiring] using hOutgoing
      rw [family'.partialRouting_entry_of_outgoing_not_mem_range outgoing hOutgoing',
        family.partialRouting_entry_of_outgoing_not_mem_range outgoing hOutgoing]
  · have hIncident' : incident ∉ Set.range family'.channelEmbedding := by
      simpa only [range_channelEmbedding_eq wiring] using hIncident
    rw [family'.partialRouting_entry_of_incident_not_mem_range incident hIncident',
      family.partialRouting_entry_of_incident_not_mem_range incident hIncident]

/-!

## C. Derived boundary-map invariance

-/

/-- External incident injection changes covariantly under the canonical external relabelling. -/
lemma externalIncidentInjection_eq (wiring : WiringEquiv family family')
    [DecidableEq P.Channel] :
    family'.externalIncidentInjection =
      family.externalIncidentInjection.reindex
        (Incident.relabelEquiv (externalChannelEquiv wiring)) (Equiv.refl _) := by
  ext ambient external
  rcases ambient with ⟨ambient⟩
  rcases external with ⟨external⟩
  simp only [PortConnectionFamily.externalIncidentInjection,
    ModeTransform.zeroExtension_entry, ModeTransform.reindex_apply,
    Equiv.refl_symm, Equiv.refl_apply]
  rfl

/-- External outgoing exposure changes covariantly under the canonical external relabelling. -/
lemma externalOutgoingInjection_eq (wiring : WiringEquiv family family')
    [DecidableEq P.Channel] :
    family'.externalOutgoingInjection =
      family.externalOutgoingInjection.reindex
        (Outgoing.relabelEquiv (externalChannelEquiv wiring)) (Equiv.refl _) := by
  ext ambient external
  rcases ambient with ⟨ambient⟩
  rcases external with ⟨external⟩
  simp only [PortConnectionFamily.externalOutgoingInjection,
    ModeTransform.zeroExtension_entry, ModeTransform.reindex_apply,
    Equiv.refl_symm, Equiv.refl_apply]
  rfl

/-- External outgoing readout changes covariantly under the canonical external relabelling. -/
lemma externalOutgoingReadout_eq (wiring : WiringEquiv family family')
    [DecidableEq P.Channel] :
    family'.externalOutgoingReadout =
      family.externalOutgoingReadout.reindex (Equiv.refl _)
        (Outgoing.relabelEquiv (externalChannelEquiv wiring)) := by
  ext external ambient
  rcases external with ⟨external⟩
  rcases ambient with ⟨ambient⟩
  simp only [PortConnectionFamily.externalOutgoingReadout,
    ModeTransform.restriction_entry, ModeTransform.reindex_apply,
    Equiv.refl_symm, Equiv.refl_apply]
  rfl

/-- Incident assembly is unchanged after relabelling the external input canonically. -/
lemma incidentAssembly_reindex (wiring : WiringEquiv family family')
    [Fintype family.Channel] [DecidableEq family.Channel]
    [Fintype family'.Channel] [DecidableEq family'.Channel]
    [Fintype family.ExternalChannel] [Fintype family'.ExternalChannel]
    [Fintype P.Channel] [DecidableEq P.Channel]
    (outgoing : ModeAmplitude (Outgoing P.Channel))
    (external : ModeAmplitude (Incident family.ExternalChannel)) :
    family'.incidentAssembly outgoing
        (ModeAmplitude.reindex
          (Incident.relabelEquiv (externalChannelEquiv wiring)) external) =
      family.incidentAssembly outgoing external := by
  classical
  apply WithLp.ofLp_injective 2
  funext incident
  rcases incident with ⟨incident⟩
  by_cases hIncident : incident ∈ Set.range family.channelEmbedding
  · rcases hIncident with ⟨channel, rfl⟩
    calc
      family'.incidentAssembly outgoing
            (ModeAmplitude.reindex
              (Incident.relabelEquiv (externalChannelEquiv wiring)) external)
            (Incident.mk (family.channelEmbedding channel)) =
          family'.incidentAssembly outgoing
            (ModeAmplitude.reindex
              (Incident.relabelEquiv (externalChannelEquiv wiring)) external)
            (Incident.mk
              (family'.channelEmbedding
                (PortConnectionFamily.WiringEquiv.toEquiv wiring channel))) := by
                  rw [PortConnectionFamily.WiringEquiv.channelEmbedding_apply]
      _ = outgoing
            (Outgoing.mk
              (family'.channelEmbedding
                (family'.mateEquiv
                  (PortConnectionFamily.WiringEquiv.toEquiv wiring channel)))) := by
            rw [family'.incidentAssembly_apply_connected_channel]
      _ = outgoing
            (Outgoing.mk
              (family.channelEmbedding (family.mateEquiv channel))) := by
            rw [PortConnectionFamily.WiringEquiv.mateEquiv_apply,
              PortConnectionFamily.WiringEquiv.channelEmbedding_apply]
      _ = family.incidentAssembly outgoing external
            (Incident.mk (family.channelEmbedding channel)) := by
            rw [family.incidentAssembly_apply_connected_channel]
  · let externalChannel : family.ExternalChannel := ⟨incident, hIncident⟩
    let externalChannel' : family'.ExternalChannel :=
      externalChannelEquiv wiring externalChannel
    change family'.incidentAssembly outgoing
          (ModeAmplitude.reindex
            (Incident.relabelEquiv (externalChannelEquiv wiring)) external)
          (Incident.mk externalChannel'.1) =
        family.incidentAssembly outgoing external (Incident.mk externalChannel.1)
    rw [family'.incidentAssembly_apply_external,
      ModeAmplitude.reindex_apply, family.incidentAssembly_apply_external]
    change external
        ((Incident.relabelEquiv (externalChannelEquiv wiring)).symm
          (Incident.relabelEquiv (externalChannelEquiv wiring)
            (Incident.mk externalChannel))) = external (Incident.mk externalChannel)
    rw [Equiv.symm_apply_apply]

/-- External readout of a fixed ambient outgoing amplitude is canonically relabelled. -/
lemma externalOutgoingReadout_apply_reindex (wiring : WiringEquiv family family')
    [Fintype family.ExternalChannel] [Fintype family'.ExternalChannel]
    [Fintype P.Channel] [DecidableEq P.Channel]
    (outgoing : ModeAmplitude (Outgoing P.Channel)) :
    family'.externalOutgoingReadout.toLinearMap outgoing =
      ModeAmplitude.reindex
        (Outgoing.relabelEquiv (externalChannelEquiv wiring))
        (family.externalOutgoingReadout.toLinearMap outgoing) := by
  classical
  rw [family'.externalOutgoingReadout_apply,
    family.externalOutgoingReadout_apply]
  apply WithLp.ofLp_injective 2
  funext external
  rcases external with ⟨external⟩
  obtain ⟨oldExternal, rfl⟩ := (externalChannelEquiv wiring).surjective external
  rw [ModeAmplitude.reindex_apply]
  change outgoing
      (family'.externalOutgoingEmbedding
        (Outgoing.relabelEquiv (externalChannelEquiv wiring)
          (Outgoing.mk oldExternal))) =
    outgoing (family.externalOutgoingEmbedding (Outgoing.mk oldExternal))
  rfl

end WiringEquiv

end PortConnectionFamily

namespace FlatNetlist

variable (netlist : FlatNetlist.{u, v, w, x})

/-!

## D. Flat-netlist invariance

-/

/-- Replace only the connection-family presentation of a flat netlist. -/
abbrev withConnections {ι' : Type y}
    (connections' : PortConnectionFamily netlist.PortFamily ι') :
    FlatNetlist.{u, v, w, y} where
  components := netlist.components
  Connection := ι'
  connections := connections'

/-- Relabel only the connection indices of a flat netlist. -/
abbrev reindexConnections {ι' : Type y} (e : netlist.Connection ≃ ι') :
    FlatNetlist.{u, v, w, y} :=
  netlist.withConnections (netlist.connections.reindex e)

/-- Exchange the endpoint presentation of every connection in a flat netlist. -/
abbrev symmConnections : FlatNetlist.{u, v, w, x} :=
  netlist.withConnections netlist.connections.symm

variable {netlist} {ι' : Type y}
  (connections' : PortConnectionFamily netlist.PortFamily ι')
  (wiring : PortConnectionFamily.WiringEquiv netlist.connections connections')

/-- Changing only the wiring presentation leaves the assembled component transform unchanged. -/
@[simp]
lemma scatteringTransform_withConnections :
    (netlist.withConnections connections').scatteringTransform =
      netlist.scatteringTransform := rfl

/-- Changing only the wiring presentation leaves the assembled component graph unchanged. -/
@[simp]
lemma componentBehavior_withConnections [Fintype netlist.Channel] :
    (netlist.withConnections connections').componentBehavior =
      netlist.componentBehavior := rfl

section Finite

variable [Fintype netlist.Channel] [Fintype netlist.ConnectedChannel]
  [Fintype connections'.Channel] [Fintype netlist.ExternalChannel]
  [Fintype connections'.ExternalChannel]

/-- Classical equality on the fixed ambient channel family. -/
local instance wiringChannelDecidableEq : DecidableEq netlist.Channel := Classical.decEq _

/-- Classical equality on the original connected-channel presentation. -/
local instance wiringConnectedChannelDecidableEq : DecidableEq netlist.ConnectedChannel :=
  Classical.decEq _

/-- Classical equality on the replacement connected-channel presentation. -/
local instance replacementConnectedChannelDecidableEq : DecidableEq connections'.Channel :=
  Classical.decEq _

omit [Fintype netlist.Channel] [Fintype netlist.ExternalChannel]
  [Fintype connections'.ExternalChannel] in
include wiring in
/-- Wiring presentation changes leave the ambient routing transform literally unchanged. -/
lemma routingTransform_withConnections :
    (netlist.withConnections connections').routingTransform =
      netlist.routingTransform :=
  PortConnectionFamily.WiringEquiv.partialRouting_eq wiring

omit [Fintype netlist.Channel] [Fintype netlist.ConnectedChannel]
  [Fintype connections'.Channel] [Fintype netlist.ExternalChannel]
  [Fintype connections'.ExternalChannel] in
/-- External input exposure changes covariantly under the canonical external relabelling. -/
lemma inputExposure_withConnections :
    (netlist.withConnections connections').inputExposure =
      netlist.inputExposure.reindex
        (PortConnectionFamily.WiringEquiv.externalIncidentEquiv wiring)
        (Equiv.refl _) :=
  PortConnectionFamily.WiringEquiv.externalIncidentInjection_eq wiring

omit [Fintype netlist.Channel] [Fintype netlist.ConnectedChannel]
  [Fintype connections'.Channel] [Fintype netlist.ExternalChannel]
  [Fintype connections'.ExternalChannel] in
/-- External output exposure changes covariantly under the canonical external relabelling. -/
lemma outputExposure_withConnections :
    (netlist.withConnections connections').outputExposure =
      netlist.outputExposure.reindex
        (PortConnectionFamily.WiringEquiv.externalOutgoingEquiv wiring)
        (Equiv.refl _) :=
  PortConnectionFamily.WiringEquiv.externalOutgoingInjection_eq wiring

omit [Fintype netlist.Channel] [Fintype netlist.ConnectedChannel]
  [Fintype connections'.Channel] [Fintype netlist.ExternalChannel]
  [Fintype connections'.ExternalChannel] in
/-- External output readout changes covariantly under the canonical external relabelling. -/
lemma outputReadout_withConnections :
    (netlist.withConnections connections').outputReadout =
      netlist.outputReadout.reindex (Equiv.refl _)
        (PortConnectionFamily.WiringEquiv.externalOutgoingEquiv wiring) :=
  PortConnectionFamily.WiringEquiv.externalOutgoingReadout_eq wiring

/-- Canonically relabelled external inputs assemble to the same ambient incident amplitude. -/
lemma incidentAssembly_withConnections
    (outgoing : ModeAmplitude netlist.OutgoingIndex)
    (external : ModeAmplitude netlist.ExternalIncident) :
    connections'.incidentAssembly outgoing
        (ModeAmplitude.reindex
          (PortConnectionFamily.WiringEquiv.externalIncidentEquiv wiring) external) =
      netlist.connections.incidentAssembly outgoing external :=
  PortConnectionFamily.WiringEquiv.incidentAssembly_reindex wiring outgoing external

omit [Fintype netlist.ConnectedChannel] [Fintype connections'.Channel] in
/-- A fixed ambient outgoing amplitude has canonically relabelled external readout. -/
lemma outputReadout_apply_withConnections
    (outgoing : ModeAmplitude netlist.OutgoingIndex) :
    (netlist.withConnections connections').outputReadout.toLinearMap outgoing =
      ModeAmplitude.reindex
        (PortConnectionFamily.WiringEquiv.externalOutgoingEquiv wiring)
        (netlist.outputReadout.toLinearMap outgoing) :=
  PortConnectionFamily.WiringEquiv.externalOutgoingReadout_apply_reindex wiring outgoing

omit [Fintype netlist.ExternalChannel]
  [Fintype connections'.ExternalChannel] in
include wiring in
/-- Wiring presentation changes leave the implicit feedback operator literally unchanged. -/
lemma feedbackOperator_withConnections :
    (netlist.withConnections connections').feedbackOperator =
      netlist.feedbackOperator := by
  unfold feedbackOperator
  rw [routingTransform_withConnections connections' wiring]
  rfl

/-- Complete solution membership is invariant after canonical external-input relabelling.

The incident/outgoing state vector itself is unchanged because the ambient component boundary is
fixed.
-/
lemma mem_solutionBehavior_withConnections_iff
    (external : ModeAmplitude netlist.ExternalIncident)
    (incident : ModeAmplitude netlist.IncidentIndex)
    (outgoing : ModeAmplitude netlist.OutgoingIndex) :
    (ModeAmplitude.reindex
          (PortConnectionFamily.WiringEquiv.externalIncidentEquiv wiring) external,
        incident.directSum outgoing) ∈
        (netlist.withConnections connections').solutionBehavior ↔
      (external, incident.directSum outgoing) ∈ netlist.solutionBehavior := by
  rw [(netlist.withConnections connections').mem_solutionBehavior_directSum_iff,
    netlist.mem_solutionBehavior_directSum_iff,
    componentBehavior_withConnections]
  change ((incident, outgoing) ∈ netlist.componentBehavior ∧
      incident = connections'.incidentAssembly outgoing
        (ModeAmplitude.reindex
          (PortConnectionFamily.WiringEquiv.externalIncidentEquiv wiring) external)) ↔
    (incident, outgoing) ∈ netlist.componentBehavior ∧
      incident = netlist.connections.incidentAssembly outgoing external
  rw [incidentAssembly_withConnections connections' wiring]

/-- External behavior membership is invariant after canonical input/output relabelling. -/
lemma mem_behavior_withConnections_iff
    (input : ModeAmplitude netlist.ExternalIncident)
    (output : ModeAmplitude netlist.ExternalOutgoing) :
    (ModeAmplitude.reindex
          (PortConnectionFamily.WiringEquiv.externalIncidentEquiv wiring) input,
        ModeAmplitude.reindex
          (PortConnectionFamily.WiringEquiv.externalOutgoingEquiv wiring) output) ∈
        (netlist.withConnections connections').behavior ↔
      (input, output) ∈ netlist.behavior := by
  rw [(netlist.withConnections connections').mem_behavior_iff_componentBehavior,
    netlist.mem_behavior_iff_componentBehavior]
  constructor
  · rintro ⟨incident, outgoing, hComponent, hIncident, hOutput⟩
    refine ⟨incident, outgoing, ?_, ?_, ?_⟩
    · simpa only [componentBehavior_withConnections] using hComponent
    · simpa only [incidentAssembly_withConnections] using hIncident
    · rw [outputReadout_apply_withConnections] at hOutput
      exact (ModeAmplitude.reindex
        (PortConnectionFamily.WiringEquiv.externalOutgoingEquiv wiring)).injective hOutput
  · rintro ⟨incident, outgoing, hComponent, hIncident, hOutput⟩
    refine ⟨incident, outgoing, ?_, ?_, ?_⟩
    · simpa only [componentBehavior_withConnections] using hComponent
    · simpa only [incidentAssembly_withConnections] using hIncident
    · rw [outputReadout_apply_withConnections]
      exact congrArg
        (ModeAmplitude.reindex
          (PortConnectionFamily.WiringEquiv.externalOutgoingEquiv wiring)) hOutput

/-- The complete external behavior changes only by the canonical external-channel relabelling. -/
lemma behavior_withConnections :
    (netlist.withConnections connections').behavior =
      netlist.behavior.reindex
        (PortConnectionFamily.WiringEquiv.externalIncidentEquiv wiring)
        (PortConnectionFamily.WiringEquiv.externalOutgoingEquiv wiring) := by
  ext ⟨input, output⟩
  rw [LinearBehavior.mem_reindex_iff]
  simpa only [ModeAmplitude.reindex_reindex_symm] using
    mem_behavior_withConnections_iff connections' wiring
      (ModeAmplitude.reindex
        (PortConnectionFamily.WiringEquiv.externalIncidentEquiv wiring).symm input)
      (ModeAmplitude.reindex
        (PortConnectionFamily.WiringEquiv.externalOutgoingEquiv wiring).symm output)

end Finite

end FlatNetlist

end

end Optics
