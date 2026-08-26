/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.ConnectionRoutingRephase
public import Physlib.Optics.Network.FlatNetlistElimination
public import Physlib.Optics.Network.HierarchicalReuse

/-!
# Gauge covariance of flat and hierarchical optical netlists

## i. Overview

Unit-phase coordinate changes transport arbitrary finite linear behaviors, including partial and
multivalued relations. When a connection family's incident and outgoing gauges match across every
mate, singular-safe closure commutes with that transport. Specializing the abstract closure law to
a flat netlist gives covariance of its external behavior after its component boundary behavior is
rephased. A response transform is extracted only under the netlist's existing well-posedness gate.

The same mate condition splits across the inner and outer stages of hierarchical append. Thus the
relational covariance law is compatible with the established N-08 flattening identity without
adding a physical or solver hypothesis.

## ii. Key results

- `LinearBehavior.rephase`: coordinate transport of an arbitrary finite linear relation.
- `LinearBehavior.rephase_congr`: coordinate transport respects equality of relations.
- `ModeTransform.toBehavior_rephase`: transform rephasing agrees with graph transport.
- `PortConnectionFamily.closeBehavior_rephase`: singular-safe connection closure is covariant for
  a matched gauge.
- `FlatNetlist.rephasedBehavior_eq`: the rephased component boundary closes to the rephasing of the
  original external behavior.
- `FlatNetlist.rephasedResponseTransform_eq`: response-transform covariance under the named
  `hWellPosed` hypothesis.
- `PortConnectionFamily.isMatchedGauge_append_iff`: flattened matching is exactly matching at both
  hierarchical stages.

## iii. Table of contents

- A. Rephasing finite linear behaviors
- B. Singular-safe closure covariance
- C. Flat-netlist behavior covariance
- D. Well-posed response covariance
- E. Hierarchical matching and flattening

## iv. References

This module discharges the `goal.md` lines 1920--1921 matched-gauge routing item at commit
`57c866bc` and targets ledger row N-07. The hierarchical statements use the already established
N-08 relation between staged and flattened closure only as a downstream structural canary.

The behavior results require only finite channel indices and the explicit mate-matching law.
`rephasedResponseTransform_eq` additionally names the pre-existing `FlatNetlist.IsWellPosed`
hypothesis because a response transform is not defined for a partial or multivalued behavior.
There is no time-reversal, reciprocity, reference-plane, passivity, losslessness, propagation,
component-packaging, or electromagnetic-power claim. The other three open network bullets quoted
in the Slice 7 proposal remain open.
-/

@[expose] public section

namespace Optics

noncomputable section

universe u v w x

/-!
## A. Rephasing finite linear behaviors
-/

namespace LinearBehavior

variable {input : Type u} {output : Type v}

/-- Transport a finite linear behavior along incident and outgoing unit-phase coordinate changes.

Unlike extraction of a transform, this operation preserves partial and multivalued relations.
-/
def rephase [Fintype input] [Fintype output]
    (gaugeIn : ModePhaseGauge input) (gaugeOut : ModePhaseGauge output)
    (behavior : LinearBehavior input output) : LinearBehavior input output :=
  behavior.map
    (((ModeAmplitude.rephase gaugeIn).toLinearEquiv.prodCongr
      (ModeAmplitude.rephase gaugeOut).toLinearEquiv) :
        (ModeAmplitude input × ModeAmplitude output) ≃ₗ[ℂ]
          (ModeAmplitude input × ModeAmplitude output)).toLinearMap

/-- Rephasing respects equality of the underlying finite linear relations. -/
lemma rephase_congr [Fintype input] [Fintype output]
    (gaugeIn : ModePhaseGauge input) (gaugeOut : ModePhaseGauge output)
    {first second : LinearBehavior input output} (hBehavior : first = second) :
    first.rephase gaugeIn gaugeOut = second.rephase gaugeIn gaugeOut :=
  congrArg (rephase gaugeIn gaugeOut) hBehavior

/-- Membership in a rephased behavior is original membership after removing both gauges. -/
@[simp]
lemma mem_rephase_iff [Fintype input] [Fintype output]
    (gaugeIn : ModePhaseGauge input) (gaugeOut : ModePhaseGauge output)
    (behavior : LinearBehavior input output) (inputAmplitude : ModeAmplitude input)
    (outputAmplitude : ModeAmplitude output) :
    (inputAmplitude, outputAmplitude) ∈ behavior.rephase gaugeIn gaugeOut ↔
      (ModeAmplitude.rephase gaugeIn⁻¹ inputAmplitude,
        ModeAmplitude.rephase gaugeOut⁻¹ outputAmplitude) ∈ behavior := by
  rw [rephase, Submodule.mem_map_equiv]
  have hInput :
      (ModeAmplitude.rephase gaugeIn).symm inputAmplitude =
        ModeAmplitude.rephase gaugeIn⁻¹ inputAmplitude := by
    apply (ModeAmplitude.rephase gaugeIn).injective
    simp
  have hOutput :
      (ModeAmplitude.rephase gaugeOut).symm outputAmplitude =
        ModeAmplitude.rephase gaugeOut⁻¹ outputAmplitude := by
    apply (ModeAmplitude.rephase gaugeOut).injective
    simp
  simp only [LinearEquiv.prodCongr_symm, LinearEquiv.prodCongr_apply]
  have hPair :
      ((ModeAmplitude.rephase gaugeIn).symm inputAmplitude,
          (ModeAmplitude.rephase gaugeOut).symm outputAmplitude) =
        (ModeAmplitude.rephase gaugeIn⁻¹ inputAmplitude,
          ModeAmplitude.rephase gaugeOut⁻¹ outputAmplitude) :=
    Prod.ext hInput hOutput
  constructor
  · intro hMember
    exact hPair ▸ hMember
  · intro hMember
    exact hPair.symm ▸ hMember

/-- Rephasing a behavior and then removing the same coordinate gauges recovers it. -/
@[simp]
lemma rephase_inv_rephase [Fintype input] [Fintype output]
    (gaugeIn : ModePhaseGauge input) (gaugeOut : ModePhaseGauge output)
    (behavior : LinearBehavior input output) :
    (behavior.rephase gaugeIn gaugeOut).rephase gaugeIn⁻¹ gaugeOut⁻¹ = behavior := by
  ext ⟨inputAmplitude, outputAmplitude⟩
  simp

/-- Functionality of a behavior is preserved by invertible phase-coordinate transport. -/
lemma IsFunctional.rephase [Fintype input] [Fintype output]
    {behavior : LinearBehavior input output} (hFunctional : behavior.IsFunctional)
    (gaugeIn : ModePhaseGauge input) (gaugeOut : ModePhaseGauge output) :
    (behavior.rephase gaugeIn gaugeOut).IsFunctional := by
  constructor
  · intro rephasedInput
    rcases hFunctional.1 (ModeAmplitude.rephase gaugeIn⁻¹ rephasedInput) with
      ⟨outputAmplitude, hOutput⟩
    refine ⟨ModeAmplitude.rephase gaugeOut outputAmplitude, ?_⟩
    rw [mem_rephase_iff]
    simpa using hOutput
  · intro rephasedInput firstOutput secondOutput hFirst hSecond
    rw [mem_rephase_iff] at hFirst hSecond
    apply (ModeAmplitude.rephase gaugeOut⁻¹).injective
    exact hFunctional.2 hFirst hSecond

end LinearBehavior

namespace ModeTransform

/-- Rephasing a transform and taking its graph agrees with rephasing the graph relation. -/
lemma toBehavior_rephase {input : Type u} {output : Type v}
    [Fintype input] [DecidableEq input] [Fintype output]
    (gaugeIn : ModePhaseGauge input) (gaugeOut : ModePhaseGauge output)
    (transform : ModeTransform input output) :
    (transform.rephase gaugeIn gaugeOut).toBehavior =
      transform.toBehavior.rephase gaugeIn gaugeOut := by
  ext ⟨inputAmplitude, outputAmplitude⟩
  rw [ModeTransform.mem_toBehavior_iff_toLinearMap,
    LinearBehavior.mem_rephase_iff,
    ModeTransform.mem_toBehavior_iff_toLinearMap,
    ModeTransform.toLinearMap_rephase_eq]
  constructor
  · intro hOutput
    rw [hOutput, ModeAmplitude.rephase_inv_rephase]
  · intro hOutput
    apply (ModeAmplitude.rephase gaugeOut⁻¹).injective
    rw [ModeAmplitude.rephase_inv_rephase]
    exact hOutput

end ModeTransform

/-!
## B. Singular-safe closure covariance
-/

namespace PortConnectionFamily

variable {P : PortModeFamily.{u, v}} {index : Type w}
variable (family : PortConnectionFamily P index)
variable [Fintype P.Channel] [Fintype family.Channel]

/-- The external complement is finite whenever the ambient and connected channel types are
finite. -/
local instance rephaseExternalChannelFintype : Fintype family.ExternalChannel := by
  classical
  infer_instance

/-- Classical equality on ambient channels for the singular-safe closure equations. -/
local instance rephaseChannelDecidableEq : DecidableEq P.Channel := Classical.decEq _

/-- Classical equality on connected channels for the singular-safe closure equations. -/
local instance rephaseConnectedChannelDecidableEq : DecidableEq family.Channel :=
  Classical.decEq _

/-- Singular-safe closure commutes with a mate-matched phase-coordinate change.

No existence, uniqueness, inverse, determinant, or functionality assumption appears. -/
lemma closeBehavior_rephase
    (behavior : LinearBehavior (Incident P.Channel) (Outgoing P.Channel))
    (gauge : ChannelEndGauge P.Channel) (hMatched : family.IsMatchedGauge gauge) :
    family.closeBehavior (behavior.rephase gauge.incident gauge.outgoing) =
      (family.closeBehavior behavior).rephase
        (family.externalGauge gauge).incident
        (family.externalGauge gauge).outgoing := by
  ext ⟨rephasedInput, rephasedOutput⟩
  rw [LinearBehavior.mem_rephase_iff,
    family.mem_closeBehavior_iff, family.mem_closeBehavior_iff]
  constructor
  · rintro ⟨rephasedIncident, rephasedOutgoing, hBehavior, hIncident, hOutput⟩
    rw [LinearBehavior.mem_rephase_iff] at hBehavior
    let incident := ModeAmplitude.rephase gauge.incident⁻¹ rephasedIncident
    let outgoing := ModeAmplitude.rephase gauge.outgoing⁻¹ rephasedOutgoing
    have hOutgoingRestore :
        ModeAmplitude.rephase gauge.outgoing outgoing = rephasedOutgoing := by
      simp [outgoing]
    refine ⟨incident, outgoing, hBehavior, ?_, ?_⟩
    · change ModeAmplitude.rephase gauge.incident⁻¹ rephasedIncident = _
      rw [hIncident]
      apply (ModeAmplitude.rephase gauge.incident).injective
      rw [ModeAmplitude.rephase_rephase_inv]
      have hAssembly := family.incidentAssembly_rephase gauge hMatched outgoing
        (ModeAmplitude.rephase
          (family.externalGauge gauge).incident⁻¹ rephasedInput)
      rw [hOutgoingRestore, ModeAmplitude.rephase_rephase_inv] at hAssembly
      exact hAssembly
    · rw [hOutput]
      apply (ModeAmplitude.rephase (family.externalGauge gauge).outgoing).injective
      rw [ModeAmplitude.rephase_rephase_inv]
      have hReadout := family.externalOutgoingReadout_apply_rephase gauge outgoing
      rw [hOutgoingRestore] at hReadout
      exact hReadout
  · rintro ⟨incident, outgoing, hBehavior, hIncident, hOutput⟩
    refine ⟨ModeAmplitude.rephase gauge.incident incident,
      ModeAmplitude.rephase gauge.outgoing outgoing, ?_, ?_, ?_⟩
    · rw [LinearBehavior.mem_rephase_iff]
      simpa only [ModeAmplitude.rephase_inv_rephase] using hBehavior
    · rw [hIncident]
      have hAssembly := family.incidentAssembly_rephase gauge hMatched outgoing
        (ModeAmplitude.rephase
          (family.externalGauge gauge).incident⁻¹ rephasedInput)
      rw [ModeAmplitude.rephase_rephase_inv] at hAssembly
      exact hAssembly.symm
    · calc
        rephasedOutput = ModeAmplitude.rephase
            (family.externalGauge gauge).outgoing
            (ModeAmplitude.rephase
              (family.externalGauge gauge).outgoing⁻¹ rephasedOutput) := by simp
        _ = ModeAmplitude.rephase (family.externalGauge gauge).outgoing
            (family.externalOutgoingReadout.toLinearMap outgoing) :=
          congrArg (ModeAmplitude.rephase
            (family.externalGauge gauge).outgoing) hOutput
        _ = family.externalOutgoingReadout.toLinearMap
            (ModeAmplitude.rephase gauge.outgoing outgoing) :=
          (family.externalOutgoingReadout_apply_rephase gauge outgoing).symm

end PortConnectionFamily

/-!
## C. Flat-netlist behavior covariance
-/

namespace FlatNetlist

variable (netlist : FlatNetlist.{u, v, w, x})
variable [Fintype netlist.Channel] [Fintype netlist.ConnectedChannel]

/-- The external channel family is finite under the standard flat-netlist hypotheses. -/
local instance flatRephaseExternalChannelFintype : Fintype netlist.ExternalChannel := by
  classical
  infer_instance

/-- The assembled component relation after changing all ambient incident and outgoing phase
coordinates. -/
def rephasedComponentBehavior (gauge : ChannelEndGauge netlist.Channel) :
    LinearBehavior netlist.IncidentIndex netlist.OutgoingIndex :=
  netlist.componentBehavior.rephase gauge.incident gauge.outgoing

/-- The singular-safe external relation obtained by closing the rephased component boundary with
the original physical connection family. -/
def rephasedBehavior (gauge : ChannelEndGauge netlist.Channel) :
    LinearBehavior netlist.ExternalIncident netlist.ExternalOutgoing :=
  netlist.connections.closeBehavior (netlist.rephasedComponentBehavior gauge)

/-- Closing a rephased component boundary gives exactly the external rephasing of the original
flat-netlist behavior. -/
lemma rephasedBehavior_eq (gauge : ChannelEndGauge netlist.Channel)
    (hMatched : netlist.connections.IsMatchedGauge gauge) :
    netlist.rephasedBehavior gauge =
      netlist.behavior.rephase
        (netlist.connections.externalGauge gauge).incident
        (netlist.connections.externalGauge gauge).outgoing := by
  classical
  rw [rephasedBehavior, rephasedComponentBehavior,
    netlist.connections.closeBehavior_rephase
      netlist.componentBehavior gauge hMatched,
    ← netlist.behavior_eq_closeBehavior]

/-!
## D. Well-posed response covariance
-/

/-- A rephased component boundary closes to a functional external relation whenever the original
netlist satisfies its existing complete-solution well-posedness gate. -/
lemma rephasedBehavior_isFunctional (gauge : ChannelEndGauge netlist.Channel)
    (hMatched : netlist.connections.IsMatchedGauge gauge)
    (hWellPosed : netlist.IsWellPosed) :
    (netlist.rephasedBehavior gauge).IsFunctional := by
  rw [netlist.rephasedBehavior_eq gauge hMatched]
  exact (netlist.behavior_isFunctional hWellPosed).rephase
    (netlist.connections.externalGauge gauge).incident
    (netlist.connections.externalGauge gauge).outgoing

/-- The covariantly rephased original response has exactly the rephased external graph. -/
lemma toBehavior_rephase_responseTransform
    (gauge : ChannelEndGauge netlist.Channel)
    (hMatched : netlist.connections.IsMatchedGauge gauge)
    (hWellPosed : netlist.IsWellPosed) :
    ((netlist.responseTransform hWellPosed).rephase
        (netlist.connections.externalGauge gauge).incident
        (netlist.connections.externalGauge gauge).outgoing).toBehavior =
      netlist.rephasedBehavior gauge := by
  classical
  rw [ModeTransform.toBehavior_rephase]
  exact (LinearBehavior.rephase_congr _ _
    (netlist.toBehavior_responseTransform hWellPosed)).trans
      (netlist.rephasedBehavior_eq gauge hMatched).symm

/-- The response transform extracted from the rephased singular-safe boundary relation.

Its `hWellPosed` argument is the original netlist's existing complete-solution gate; no new
physical hypothesis is introduced. -/
noncomputable def rephasedResponseTransform
    (gauge : ChannelEndGauge netlist.Channel)
    (hMatched : netlist.connections.IsMatchedGauge gauge)
    (hWellPosed : netlist.IsWellPosed) :
    ModeTransform netlist.ExternalIncident netlist.ExternalOutgoing := by
  classical
  exact (netlist.rephasedBehavior gauge).toModeTransform
    (netlist.rephasedBehavior_isFunctional gauge hMatched hWellPosed)

/-- On the named well-posed domain, the response extracted after component rephasing is exactly
the covariant rephasing of the original response transform. -/
lemma rephasedResponseTransform_eq
    (gauge : ChannelEndGauge netlist.Channel)
    (hMatched : netlist.connections.IsMatchedGauge gauge)
    (hWellPosed : netlist.IsWellPosed) :
    netlist.rephasedResponseTransform gauge hMatched hWellPosed =
      (netlist.responseTransform hWellPosed).rephase
        (netlist.connections.externalGauge gauge).incident
        (netlist.connections.externalGauge gauge).outgoing := by
  classical
  unfold rephasedResponseTransform
  exact LinearBehavior.toModeTransform_unique
    (netlist.rephasedBehavior gauge)
    (netlist.rephasedBehavior_isFunctional gauge hMatched hWellPosed)
    ((netlist.responseTransform hWellPosed).rephase
      (netlist.connections.externalGauge gauge).incident
      (netlist.connections.externalGauge gauge).outgoing)
    (netlist.toBehavior_rephase_responseTransform gauge hMatched hWellPosed)

end FlatNetlist

/-!
## E. Hierarchical matching and flattening
-/

namespace PortConnectionFamily

variable {P : PortModeFamily.{u, v}} {innerIndex : Type w} {outerIndex : Type x}
variable (inner : PortConnectionFamily P innerIndex)
variable (outer : PortConnectionFamily inner.externalPortModeFamily outerIndex)

/-- Restrict an ambient gauge to the dependent external boundary seen by the next hierarchy
stage. -/
def boundaryGauge (gauge : ChannelEndGauge P.Channel) :
    ChannelEndGauge inner.externalPortModeFamily.Channel where
  incident endpoint := gauge.incident
    (Incident.mk (inner.boundaryChannelEquiv endpoint.channel).1)
  outgoing endpoint := gauge.outgoing
    (Outgoing.mk (inner.boundaryChannelEquiv endpoint.channel).1)

/-- A flattened two-stage gauge is mate-matched exactly when its ambient inner restriction and
its induced outer-boundary restriction are both mate-matched. -/
lemma isMatchedGauge_append_iff (gauge : ChannelEndGauge P.Channel) :
    (inner.append outer).IsMatchedGauge gauge ↔
      inner.IsMatchedGauge gauge ∧ outer.IsMatchedGauge (inner.boundaryGauge gauge) := by
  constructor
  · intro hMatched
    constructor
    · rintro ⟨index, channel⟩
      have hChannel := hMatched ⟨Sum.inl index, channel⟩
      rw [inner.append_mateEquiv_inl outer,
        inner.append_channelEmbedding_inl outer,
        inner.append_channelEmbedding_inl outer] at hChannel
      exact hChannel
    · rintro ⟨index, channel⟩
      have hChannel := hMatched ⟨Sum.inr index, channel⟩
      rw [inner.append_mateEquiv_inr outer,
        inner.append_channelEmbedding_inr outer,
        inner.append_channelEmbedding_inr outer] at hChannel
      exact hChannel
  · rintro ⟨hInner, hOuter⟩ ⟨index, channel⟩
    rcases index with index | index
    · change (inner.connection index).LocalChannel at channel
      rw [inner.append_mateEquiv_inl outer,
        inner.append_channelEmbedding_inl outer,
        inner.append_channelEmbedding_inl outer]
      exact hInner ⟨index, channel⟩
    · change (outer.connection index).LocalChannel at channel
      rw [inner.append_mateEquiv_inr outer,
        inner.append_channelEmbedding_inr outer,
        inner.append_channelEmbedding_inr outer]
      exact hOuter ⟨index, channel⟩

section Finite

variable [Fintype P.Channel] [Fintype inner.Channel] [Fintype outer.Channel]

/-- The inner stage's structurally external channels inherit ambient finiteness. -/
local instance appendRephaseInnerExternalChannelFintype :
    Fintype inner.ExternalChannel := by
  classical
  infer_instance

/-- The inner boundary channel type inherits finiteness from its external-channel presentation.
-/
local instance appendRephaseBoundaryChannelFintype :
    Fintype inner.externalPortModeFamily.Channel :=
  Fintype.ofEquiv _ inner.boundaryChannelEquiv.symm

/-- The flattened connected channels are the finite sum of both stages' connected channels. -/
local instance appendRephaseConnectedChannelFintype :
    Fintype (inner.append outer).Channel :=
  Fintype.ofEquiv _ (inner.appendChannelEquiv outer).symm

/-- The final outer boundary inherits finiteness from the finite intermediate boundary. -/
local instance appendRephaseOuterExternalChannelFintype :
    Fintype outer.ExternalChannel := by
  classical
  infer_instance

/-- The flattened external channel family is finite under the two-stage structural hypotheses.
-/
local instance appendRephaseExternalChannelFintype :
    Fintype (inner.append outer).ExternalChannel := by
  classical
  infer_instance

/-- Rephasing before flattened closure agrees with first using the established staged closure
identity and then rephasing the final external boundary.

This is an equality of singular-safe relations and adds no well-posedness assumption. -/
lemma closeBehavior_append_rephase_eq_staged
    (behavior : LinearBehavior (Incident P.Channel) (Outgoing P.Channel))
    (gauge : ChannelEndGauge P.Channel)
    (hMatched : (inner.append outer).IsMatchedGauge gauge) :
    (inner.append outer).closeBehavior
        (behavior.rephase gauge.incident gauge.outgoing) =
      ((outer.closeBehavior (inner.innerBoundaryBehavior behavior)).reindex
          (Incident.relabelEquiv (inner.appendExternalChannelEquiv outer)).symm
          (Outgoing.relabelEquiv (inner.appendExternalChannelEquiv outer)).symm).rephase
        ((inner.append outer).externalGauge gauge).incident
        ((inner.append outer).externalGauge gauge).outgoing := by
  rw [(inner.append outer).closeBehavior_rephase behavior gauge hMatched,
    inner.closeBehavior_append outer behavior]

end Finite

end PortConnectionFamily

end

end Optics
