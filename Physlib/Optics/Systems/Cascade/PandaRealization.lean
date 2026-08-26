/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Systems.Cascade.PandaBridge

/-!
# Complete N7 realization of the PANDA forward graph

## i. Overview

This file relates the eighteen retained PANDA coordinates to the actual component-scattering and
physical-routing equations of `Panda.netlist`. A graph solution is lifted to all 32 incident and
32 outgoing aggregate component coordinates: the retained forward coordinates are copied from the
graph, and every reverse-going coordinate is set to zero. Conversely, every complete N7 state is
projected to its eighteen forward coordinates.

The main equivalence proves that the graph node equation is exactly the existence of such a
complete zero-reverse N7 realization. Unlike an edge-ownership statement, the equivalence checks
every local scattering output and both endpoints of every wire, so an omitted or duplicated graph
branch cannot pass merely by retaining valid individual edge gains.

## ii. Key results

- `Panda.liftedOutgoing_eq_scatteringTransform`: all component scattering equations.
- `Panda.liftedIncident_eq_incidentAssembly`: all fourteen wires and four externals.
- `Panda.isNodeSolution_iff_exists_netlistRealization`: the relational extraction equivalence.

## iii. Table of contents

- A. Component-indexed raw N7 equations
- B. Complete zero-reverse lift
- C. Physical routing
- D. Projection and relational equivalence

## iv. References

The complete N7 netlist is bidirectional. This file identifies only its zero-reverse forward
sector with the directed Definition-11 projection; it does not identify that projection with the
paper's undirected SFG or with the complete N5 feedback graph. No passivity, losslessness,
reciprocity, convergence, stability, resonance, bandwidth, dispersion, or power claim is made.
-/

@[expose] public section

namespace Optics

noncomputable section

namespace Panda
/-!
## A. Component-indexed raw N7 equations
-/
/-- The four directional-coupler components, used to state one family of local N7 laws. -/
inductive CouplerLabel
  | input
  | output
  | right
  | left

/-- The physical component selected by a coupler label. -/
def CouplerLabel.component : CouplerLabel → Component
  | .input => .inputCoupler
  | .output => .outputCoupler
  | .right => .rightCoupler
  | .left => .leftCoupler

/-- The physical parameters selected by a coupler label. -/
def CouplerLabel.parameters (p : Parameters) : CouplerLabel →
    DirectionalCoupler.Parameters
  | .input => p.inputCoupler
  | .output => p.outputCoupler
  | .right => p.rightCoupler
  | .left => p.leftCoupler

/-- The aggregate N7 channel at one selected coupler port. -/
def couplerChannel (p : Parameters) (label : CouplerLabel)
    (port : DirectionalCoupler.Port) : (netlist p).Channel := by
  cases label
  · exact ⟨⟨.inputCoupler, port⟩, ()⟩
  · exact ⟨⟨.outputCoupler, port⟩, ()⟩
  · exact ⟨⟨.rightCoupler, port⟩, ()⟩
  · exact ⟨⟨.leftCoupler, port⟩, ()⟩

/-- The eight propagation components, used to state one family of local N7 laws. -/
inductive PropagationLabel
  | mainOne
  | mainTwo
  | mainThree
  | mainFour
  | rightOne
  | rightTwo
  | leftOne
  | leftTwo

/-- The physical component selected by a propagation label. -/
def PropagationLabel.component : PropagationLabel → Component
  | .mainOne => .mainQuarterOne
  | .mainTwo => .mainQuarterTwo
  | .mainThree => .mainQuarterThree
  | .mainFour => .mainQuarterFour
  | .rightOne => .rightHalfOne
  | .rightTwo => .rightHalfTwo
  | .leftOne => .leftHalfOne
  | .leftTwo => .leftHalfTwo

/-- The physical parameters selected by a propagation label. -/
def PropagationLabel.parameters (p : Parameters) : PropagationLabel →
    MatchedPropagation.Parameters
  | .mainOne => p.mainQuarterOne
  | .mainTwo => p.mainQuarterTwo
  | .mainThree => p.mainQuarterThree
  | .mainFour => p.mainQuarterFour
  | .rightOne => p.rightHalfOne
  | .rightTwo => p.rightHalfTwo
  | .leftOne => p.leftHalfOne
  | .leftTwo => p.leftHalfTwo

/-- The aggregate N7 channel at one selected propagation port. -/
def propagationChannel (p : Parameters) (label : PropagationLabel)
    (port : MatchedPropagation.Port) : (netlist p).Channel := by
  cases label
  · exact ⟨⟨.mainQuarterOne, port⟩, ()⟩
  · exact ⟨⟨.mainQuarterTwo, port⟩, ()⟩
  · exact ⟨⟨.mainQuarterThree, port⟩, ()⟩
  · exact ⟨⟨.mainQuarterFour, port⟩, ()⟩
  · exact ⟨⟨.rightHalfOne, port⟩, ()⟩
  · exact ⟨⟨.rightHalfTwo, port⟩, ()⟩
  · exact ⟨⟨.leftHalfOne, port⟩, ()⟩
  · exact ⟨⟨.leftHalfTwo, port⟩, ()⟩

/-- Local incident endpoints of every PANDA component form a finite type. -/
noncomputable local instance realizationLocalIncidentFintype (p : Parameters)
    (component : (components p).Component) :
    Fintype (Incident ((components p).portFamily component).Channel) :=
  Incident.fintypeOf (componentsLocalChannelFintype p component)

/-- Local outgoing endpoints of every PANDA component form a finite type. -/
noncomputable local instance realizationLocalOutgoingFintype (p : Parameters)
    (component : (components p).Component) :
    Fintype (Outgoing ((components p).portFamily component).Channel) :=
  Outgoing.fintypeOf (componentsLocalChannelFintype p component)

/-- Restricting a complete scattering solution gives the selected component's local law. -/
private lemma componentBehavior_of_scatteringEquation (p : Parameters)
    (component : (components p).Component)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident) :
    (incident.restrictEmbedding
          (Incident.relabelEmbedding
            ((components p).componentChannelEmbedding component)),
      outgoing.restrictEmbedding
          (Outgoing.relabelEmbedding
            ((components p).componentChannelEmbedding component))) ∈
        ((components p).scattering component).toOrientedModeTransform.toBehavior := by
  have hMember : (incident, outgoing) ∈ (netlist p).componentBehavior :=
    ((netlist p).mem_componentBehavior_iff incident outgoing).mpr hScattering
  exact
    ((netlist p).mem_componentBehavior_iff_forall_component incident outgoing).mp
      hMember component

/-- The input-coupler restriction of a complete scattering solution is physical. -/
private lemma inputCoupler_physicalBehavior (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident) :
    (incident.restrictEmbedding
          (Incident.relabelEmbedding
            ((components p).componentChannelEmbedding .inputCoupler)),
      outgoing.restrictEmbedding
          (Outgoing.relabelEmbedding
            ((components p).componentChannelEmbedding .inputCoupler))) ∈
        DirectionalCoupler.physicalBehavior p.inputCoupler := by
  have hLocal := componentBehavior_of_scatteringEquation
    p .inputCoupler incident outgoing hScattering
  change _ ∈
    (DirectionalCoupler.physicalScattering p.inputCoupler Unit).toOrientedModeTransform.toBehavior
      at hLocal
  rwa [DirectionalCoupler.physicalScattering_realizes_physicalBehavior] at hLocal

/-- The output-coupler restriction of a complete scattering solution is physical. -/
private lemma outputCoupler_physicalBehavior (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident) :
    (incident.restrictEmbedding
          (Incident.relabelEmbedding
            ((components p).componentChannelEmbedding .outputCoupler)),
      outgoing.restrictEmbedding
          (Outgoing.relabelEmbedding
            ((components p).componentChannelEmbedding .outputCoupler))) ∈
        DirectionalCoupler.physicalBehavior p.outputCoupler := by
  have hLocal := componentBehavior_of_scatteringEquation
    p .outputCoupler incident outgoing hScattering
  change _ ∈
    (DirectionalCoupler.physicalScattering p.outputCoupler Unit).toOrientedModeTransform.toBehavior
      at hLocal
  rwa [DirectionalCoupler.physicalScattering_realizes_physicalBehavior] at hLocal

/-- The right-coupler restriction of a complete scattering solution is physical. -/
private lemma rightCoupler_physicalBehavior (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident) :
    (incident.restrictEmbedding
          (Incident.relabelEmbedding
            ((components p).componentChannelEmbedding .rightCoupler)),
      outgoing.restrictEmbedding
          (Outgoing.relabelEmbedding
            ((components p).componentChannelEmbedding .rightCoupler))) ∈
        DirectionalCoupler.physicalBehavior p.rightCoupler := by
  have hLocal := componentBehavior_of_scatteringEquation
    p .rightCoupler incident outgoing hScattering
  change _ ∈
    (DirectionalCoupler.physicalScattering p.rightCoupler Unit).toOrientedModeTransform.toBehavior
      at hLocal
  rwa [DirectionalCoupler.physicalScattering_realizes_physicalBehavior] at hLocal

/-- The left-coupler restriction of a complete scattering solution is physical. -/
private lemma leftCoupler_physicalBehavior (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident) :
    (incident.restrictEmbedding
          (Incident.relabelEmbedding
            ((components p).componentChannelEmbedding .leftCoupler)),
      outgoing.restrictEmbedding
          (Outgoing.relabelEmbedding
            ((components p).componentChannelEmbedding .leftCoupler))) ∈
        DirectionalCoupler.physicalBehavior p.leftCoupler := by
  have hLocal := componentBehavior_of_scatteringEquation
    p .leftCoupler incident outgoing hScattering
  change _ ∈
    (DirectionalCoupler.physicalScattering p.leftCoupler Unit).toOrientedModeTransform.toBehavior
      at hLocal
  rwa [DirectionalCoupler.physicalScattering_realizes_physicalBehavior] at hLocal

/-- A selected propagation restriction of a complete scattering solution is physical. -/
private lemma propagation_physicalBehavior (p : Parameters) (label : PropagationLabel)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident) :
    match label with
    | .mainOne =>
        (incident.restrictEmbedding (Incident.relabelEmbedding
            ((components p).componentChannelEmbedding .mainQuarterOne)),
          outgoing.restrictEmbedding (Outgoing.relabelEmbedding
            ((components p).componentChannelEmbedding .mainQuarterOne))) ∈
          MatchedPropagation.physicalBehavior p.mainQuarterOne
    | .mainTwo =>
        (incident.restrictEmbedding (Incident.relabelEmbedding
            ((components p).componentChannelEmbedding .mainQuarterTwo)),
          outgoing.restrictEmbedding (Outgoing.relabelEmbedding
            ((components p).componentChannelEmbedding .mainQuarterTwo))) ∈
          MatchedPropagation.physicalBehavior p.mainQuarterTwo
    | .mainThree =>
        (incident.restrictEmbedding (Incident.relabelEmbedding
            ((components p).componentChannelEmbedding .mainQuarterThree)),
          outgoing.restrictEmbedding (Outgoing.relabelEmbedding
            ((components p).componentChannelEmbedding .mainQuarterThree))) ∈
          MatchedPropagation.physicalBehavior p.mainQuarterThree
    | .mainFour =>
        (incident.restrictEmbedding (Incident.relabelEmbedding
            ((components p).componentChannelEmbedding .mainQuarterFour)),
          outgoing.restrictEmbedding (Outgoing.relabelEmbedding
            ((components p).componentChannelEmbedding .mainQuarterFour))) ∈
          MatchedPropagation.physicalBehavior p.mainQuarterFour
    | .rightOne =>
        (incident.restrictEmbedding (Incident.relabelEmbedding
            ((components p).componentChannelEmbedding .rightHalfOne)),
          outgoing.restrictEmbedding (Outgoing.relabelEmbedding
            ((components p).componentChannelEmbedding .rightHalfOne))) ∈
          MatchedPropagation.physicalBehavior p.rightHalfOne
    | .rightTwo =>
        (incident.restrictEmbedding (Incident.relabelEmbedding
            ((components p).componentChannelEmbedding .rightHalfTwo)),
          outgoing.restrictEmbedding (Outgoing.relabelEmbedding
            ((components p).componentChannelEmbedding .rightHalfTwo))) ∈
          MatchedPropagation.physicalBehavior p.rightHalfTwo
    | .leftOne =>
        (incident.restrictEmbedding (Incident.relabelEmbedding
            ((components p).componentChannelEmbedding .leftHalfOne)),
          outgoing.restrictEmbedding (Outgoing.relabelEmbedding
            ((components p).componentChannelEmbedding .leftHalfOne))) ∈
          MatchedPropagation.physicalBehavior p.leftHalfOne
    | .leftTwo =>
        (incident.restrictEmbedding (Incident.relabelEmbedding
            ((components p).componentChannelEmbedding .leftHalfTwo)),
          outgoing.restrictEmbedding (Outgoing.relabelEmbedding
            ((components p).componentChannelEmbedding .leftHalfTwo))) ∈
          MatchedPropagation.physicalBehavior p.leftHalfTwo := by
  have hLocal := componentBehavior_of_scatteringEquation
    p label.component incident outgoing hScattering
  cases label
  all_goals
    change _ ∈ (MatchedPropagation.physicalScattering _ Unit).toOrientedModeTransform.toBehavior
      at hLocal
    rwa [MatchedPropagation.physicalScattering_realizes_physicalBehavior] at hLocal

/-- The reverse first-arm coordinate extracted from one physical coupler law. -/
private lemma couplerPhysical_leftFirst (q : DirectionalCoupler.Parameters)
    (incident : ModeAmplitude (Incident (DirectionalCoupler.portFamily Unit).Channel))
    (outgoing : ModeAmplitude (Outgoing (DirectionalCoupler.portFamily Unit).Channel))
    (hPhysical : (incident, outgoing) ∈ DirectionalCoupler.physicalBehavior q) :
    outgoing (Outgoing.mk ⟨DirectionalCoupler.Port.leftFirst, ()⟩) =
      q.throughAmplitude * incident (Incident.mk ⟨DirectionalCoupler.Port.rightFirst, ()⟩) +
        DirectionalCoupler.crossCoefficient q *
          incident (Incident.mk ⟨DirectionalCoupler.Port.rightSecond, ()⟩) := by
  have hRaw := (DirectionalCoupler.mem_physicalBehavior_iff q _ _).mp hPhysical
  rw [DirectionalCoupler.mem_behavior_iff,
    DirectionalCoupler.mixing_toLinearMap_apply,
    DirectionalCoupler.mixing_toLinearMap_apply] at hRaw
  exact congrArg (fun amplitude => amplitude (Sum.inl (Outgoing.mk (Sum.inl ())))) hRaw

/-- The reverse second-arm coordinate extracted from one physical coupler law. -/
private lemma couplerPhysical_leftSecond (q : DirectionalCoupler.Parameters)
    (incident : ModeAmplitude (Incident (DirectionalCoupler.portFamily Unit).Channel))
    (outgoing : ModeAmplitude (Outgoing (DirectionalCoupler.portFamily Unit).Channel))
    (hPhysical : (incident, outgoing) ∈ DirectionalCoupler.physicalBehavior q) :
    outgoing (Outgoing.mk ⟨DirectionalCoupler.Port.leftSecond, ()⟩) =
      DirectionalCoupler.crossCoefficient q *
          incident (Incident.mk ⟨DirectionalCoupler.Port.rightFirst, ()⟩) +
        q.throughAmplitude *
          incident (Incident.mk ⟨DirectionalCoupler.Port.rightSecond, ()⟩) := by
  have hRaw := (DirectionalCoupler.mem_physicalBehavior_iff q _ _).mp hPhysical
  rw [DirectionalCoupler.mem_behavior_iff,
    DirectionalCoupler.mixing_toLinearMap_apply,
    DirectionalCoupler.mixing_toLinearMap_apply] at hRaw
  exact congrArg (fun amplitude => amplitude (Sum.inl (Outgoing.mk (Sum.inr ())))) hRaw

/-- The forward first-arm coordinate extracted from one physical coupler law. -/
private lemma couplerPhysical_rightFirst (q : DirectionalCoupler.Parameters)
    (incident : ModeAmplitude (Incident (DirectionalCoupler.portFamily Unit).Channel))
    (outgoing : ModeAmplitude (Outgoing (DirectionalCoupler.portFamily Unit).Channel))
    (hPhysical : (incident, outgoing) ∈ DirectionalCoupler.physicalBehavior q) :
    outgoing (Outgoing.mk ⟨DirectionalCoupler.Port.rightFirst, ()⟩) =
      q.throughAmplitude * incident (Incident.mk ⟨DirectionalCoupler.Port.leftFirst, ()⟩) +
        DirectionalCoupler.crossCoefficient q *
          incident (Incident.mk ⟨DirectionalCoupler.Port.leftSecond, ()⟩) := by
  have hRaw := (DirectionalCoupler.mem_physicalBehavior_iff q _ _).mp hPhysical
  rw [DirectionalCoupler.mem_behavior_iff,
    DirectionalCoupler.mixing_toLinearMap_apply,
    DirectionalCoupler.mixing_toLinearMap_apply] at hRaw
  exact congrArg (fun amplitude => amplitude (Sum.inr (Outgoing.mk (Sum.inl ())))) hRaw

/-- The forward second-arm coordinate extracted from one physical coupler law. -/
private lemma couplerPhysical_rightSecond (q : DirectionalCoupler.Parameters)
    (incident : ModeAmplitude (Incident (DirectionalCoupler.portFamily Unit).Channel))
    (outgoing : ModeAmplitude (Outgoing (DirectionalCoupler.portFamily Unit).Channel))
    (hPhysical : (incident, outgoing) ∈ DirectionalCoupler.physicalBehavior q) :
    outgoing (Outgoing.mk ⟨DirectionalCoupler.Port.rightSecond, ()⟩) =
      DirectionalCoupler.crossCoefficient q *
          incident (Incident.mk ⟨DirectionalCoupler.Port.leftFirst, ()⟩) +
        q.throughAmplitude *
          incident (Incident.mk ⟨DirectionalCoupler.Port.leftSecond, ()⟩) := by
  have hRaw := (DirectionalCoupler.mem_physicalBehavior_iff q _ _).mp hPhysical
  rw [DirectionalCoupler.mem_behavior_iff,
    DirectionalCoupler.mixing_toLinearMap_apply,
    DirectionalCoupler.mixing_toLinearMap_apply] at hRaw
  exact congrArg (fun amplitude => amplitude (Sum.inr (Outgoing.mk (Sum.inr ())))) hRaw

/-- The reverse coordinate extracted from one physical propagation law. -/
private lemma propagationPhysical_left (q : MatchedPropagation.Parameters)
    (incident : ModeAmplitude (Incident (MatchedPropagation.portFamily Unit).Channel))
    (outgoing : ModeAmplitude (Outgoing (MatchedPropagation.portFamily Unit).Channel))
    (hPhysical : (incident, outgoing) ∈ MatchedPropagation.physicalBehavior q) :
    outgoing (Outgoing.mk ⟨MatchedPropagation.Port.left, ()⟩) =
      MatchedPropagation.transmissionCoefficient q *
        incident (Incident.mk ⟨MatchedPropagation.Port.right, ()⟩) := by
  have hRaw := (MatchedPropagation.mem_physicalBehavior_iff q _ _).mp hPhysical
  rw [MatchedPropagation.mem_behavior_iff] at hRaw
  exact congrArg (fun amplitude => amplitude (Sum.inl (Outgoing.mk ()))) hRaw

/-- The forward coordinate extracted from one physical propagation law. -/
private lemma propagationPhysical_right (q : MatchedPropagation.Parameters)
    (incident : ModeAmplitude (Incident (MatchedPropagation.portFamily Unit).Channel))
    (outgoing : ModeAmplitude (Outgoing (MatchedPropagation.portFamily Unit).Channel))
    (hPhysical : (incident, outgoing) ∈ MatchedPropagation.physicalBehavior q) :
    outgoing (Outgoing.mk ⟨MatchedPropagation.Port.right, ()⟩) =
      MatchedPropagation.transmissionCoefficient q *
        incident (Incident.mk ⟨MatchedPropagation.Port.left, ()⟩) := by
  have hRaw := (MatchedPropagation.mem_physicalBehavior_iff q _ _).mp hPhysical
  rw [MatchedPropagation.mem_behavior_iff] at hRaw
  exact congrArg (fun amplitude => amplitude (Sum.inr (Outgoing.mk ()))) hRaw

/-- A selected coupler's reverse first-arm output obeys its raw scattering equation. -/
private lemma scatteringEquation_coupler_leftFirst (p : Parameters)
    (label : CouplerLabel) (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident) :
    outgoing (Outgoing.mk (couplerChannel p label .leftFirst)) =
      (label.parameters p).throughAmplitude *
          incident (Incident.mk (couplerChannel p label .rightFirst)) +
        DirectionalCoupler.crossCoefficient (label.parameters p) *
          incident (Incident.mk (couplerChannel p label .rightSecond)) := by
  cases label
  · exact couplerPhysical_leftFirst p.inputCoupler _ _
      (inputCoupler_physicalBehavior p incident outgoing hScattering)
  · exact couplerPhysical_leftFirst p.outputCoupler _ _
      (outputCoupler_physicalBehavior p incident outgoing hScattering)
  · exact couplerPhysical_leftFirst p.rightCoupler _ _
      (rightCoupler_physicalBehavior p incident outgoing hScattering)
  · exact couplerPhysical_leftFirst p.leftCoupler _ _
      (leftCoupler_physicalBehavior p incident outgoing hScattering)

/-- A selected coupler's reverse second-arm output obeys its raw scattering equation. -/
private lemma scatteringEquation_coupler_leftSecond (p : Parameters)
    (label : CouplerLabel) (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident) :
    outgoing (Outgoing.mk (couplerChannel p label .leftSecond)) =
      DirectionalCoupler.crossCoefficient (label.parameters p) *
          incident (Incident.mk (couplerChannel p label .rightFirst)) +
        (label.parameters p).throughAmplitude *
          incident (Incident.mk (couplerChannel p label .rightSecond)) := by
  cases label
  · exact couplerPhysical_leftSecond p.inputCoupler _ _
      (inputCoupler_physicalBehavior p incident outgoing hScattering)
  · exact couplerPhysical_leftSecond p.outputCoupler _ _
      (outputCoupler_physicalBehavior p incident outgoing hScattering)
  · exact couplerPhysical_leftSecond p.rightCoupler _ _
      (rightCoupler_physicalBehavior p incident outgoing hScattering)
  · exact couplerPhysical_leftSecond p.leftCoupler _ _
      (leftCoupler_physicalBehavior p incident outgoing hScattering)

/-- A selected coupler's forward first-arm output obeys its raw scattering equation. -/
private lemma scatteringEquation_coupler_rightFirst (p : Parameters)
    (label : CouplerLabel) (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident) :
    outgoing (Outgoing.mk (couplerChannel p label .rightFirst)) =
      (label.parameters p).throughAmplitude *
          incident (Incident.mk (couplerChannel p label .leftFirst)) +
        DirectionalCoupler.crossCoefficient (label.parameters p) *
          incident (Incident.mk (couplerChannel p label .leftSecond)) := by
  cases label
  · exact couplerPhysical_rightFirst p.inputCoupler _ _
      (inputCoupler_physicalBehavior p incident outgoing hScattering)
  · exact couplerPhysical_rightFirst p.outputCoupler _ _
      (outputCoupler_physicalBehavior p incident outgoing hScattering)
  · exact couplerPhysical_rightFirst p.rightCoupler _ _
      (rightCoupler_physicalBehavior p incident outgoing hScattering)
  · exact couplerPhysical_rightFirst p.leftCoupler _ _
      (leftCoupler_physicalBehavior p incident outgoing hScattering)

/-- A selected coupler's forward second-arm output obeys its raw scattering equation. -/
private lemma scatteringEquation_coupler_rightSecond (p : Parameters)
    (label : CouplerLabel) (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident) :
    outgoing (Outgoing.mk (couplerChannel p label .rightSecond)) =
      DirectionalCoupler.crossCoefficient (label.parameters p) *
          incident (Incident.mk (couplerChannel p label .leftFirst)) +
        (label.parameters p).throughAmplitude *
          incident (Incident.mk (couplerChannel p label .leftSecond)) := by
  cases label
  · exact couplerPhysical_rightSecond p.inputCoupler _ _
      (inputCoupler_physicalBehavior p incident outgoing hScattering)
  · exact couplerPhysical_rightSecond p.outputCoupler _ _
      (outputCoupler_physicalBehavior p incident outgoing hScattering)
  · exact couplerPhysical_rightSecond p.rightCoupler _ _
      (rightCoupler_physicalBehavior p incident outgoing hScattering)
  · exact couplerPhysical_rightSecond p.leftCoupler _ _
      (leftCoupler_physicalBehavior p incident outgoing hScattering)

/-- A selected delay's reverse output obeys its raw propagation equation. -/
private lemma scatteringEquation_propagation_left (p : Parameters)
    (label : PropagationLabel) (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident) :
    outgoing (Outgoing.mk (propagationChannel p label .left)) =
      MatchedPropagation.transmissionCoefficient (label.parameters p) *
        incident (Incident.mk (propagationChannel p label .right)) := by
  cases label
  · exact propagationPhysical_left p.mainQuarterOne _ _
      (propagation_physicalBehavior p .mainOne incident outgoing hScattering)
  · exact propagationPhysical_left p.mainQuarterTwo _ _
      (propagation_physicalBehavior p .mainTwo incident outgoing hScattering)
  · exact propagationPhysical_left p.mainQuarterThree _ _
      (propagation_physicalBehavior p .mainThree incident outgoing hScattering)
  · exact propagationPhysical_left p.mainQuarterFour _ _
      (propagation_physicalBehavior p .mainFour incident outgoing hScattering)
  · exact propagationPhysical_left p.rightHalfOne _ _
      (propagation_physicalBehavior p .rightOne incident outgoing hScattering)
  · exact propagationPhysical_left p.rightHalfTwo _ _
      (propagation_physicalBehavior p .rightTwo incident outgoing hScattering)
  · exact propagationPhysical_left p.leftHalfOne _ _
      (propagation_physicalBehavior p .leftOne incident outgoing hScattering)
  · exact propagationPhysical_left p.leftHalfTwo _ _
      (propagation_physicalBehavior p .leftTwo incident outgoing hScattering)

/-- A selected delay's forward output obeys its raw propagation equation. -/
private lemma scatteringEquation_propagation_right (p : Parameters)
    (label : PropagationLabel) (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident) :
    outgoing (Outgoing.mk (propagationChannel p label .right)) =
      MatchedPropagation.transmissionCoefficient (label.parameters p) *
        incident (Incident.mk (propagationChannel p label .left)) := by
  cases label
  · exact propagationPhysical_right p.mainQuarterOne _ _
      (propagation_physicalBehavior p .mainOne incident outgoing hScattering)
  · exact propagationPhysical_right p.mainQuarterTwo _ _
      (propagation_physicalBehavior p .mainTwo incident outgoing hScattering)
  · exact propagationPhysical_right p.mainQuarterThree _ _
      (propagation_physicalBehavior p .mainThree incident outgoing hScattering)
  · exact propagationPhysical_right p.mainQuarterFour _ _
      (propagation_physicalBehavior p .mainFour incident outgoing hScattering)
  · exact propagationPhysical_right p.rightHalfOne _ _
      (propagation_physicalBehavior p .rightOne incident outgoing hScattering)
  · exact propagationPhysical_right p.rightHalfTwo _ _
      (propagation_physicalBehavior p .rightTwo incident outgoing hScattering)
  · exact propagationPhysical_right p.leftHalfOne _ _
      (propagation_physicalBehavior p .leftOne incident outgoing hScattering)
  · exact propagationPhysical_right p.leftHalfTwo _ _
      (propagation_physicalBehavior p .leftTwo incident outgoing hScattering)
/-!
## B. Complete zero-reverse lift
-/
/-- The eighteen retained coordinates projected from a complete N7 component-boundary state. -/
def forwardState (p : Parameters) (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex) : Node → ℂ :=
  ![incident (Incident.mk (couplerChannel p .input .leftFirst)),
    incident (Incident.mk (couplerChannel p .input .leftSecond)),
    outgoing (Outgoing.mk (couplerChannel p .input .rightFirst)),
    outgoing (Outgoing.mk (couplerChannel p .input .rightSecond)),
    incident (Incident.mk (couplerChannel p .output .leftFirst)),
    incident (Incident.mk (couplerChannel p .output .leftSecond)),
    outgoing (Outgoing.mk (couplerChannel p .output .rightFirst)),
    outgoing (Outgoing.mk (couplerChannel p .output .rightSecond)),
    incident (Incident.mk (couplerChannel p .right .leftFirst)),
    outgoing (Outgoing.mk (couplerChannel p .right .rightFirst)),
    incident (Incident.mk (couplerChannel p .right .leftSecond)),
    outgoing (Outgoing.mk (couplerChannel p .right .rightSecond)),
    incident (Incident.mk (propagationChannel p .rightTwo .left)),
    incident (Incident.mk (couplerChannel p .left .leftFirst)),
    outgoing (Outgoing.mk (couplerChannel p .left .rightFirst)),
    incident (Incident.mk (couplerChannel p .left .leftSecond)),
    outgoing (Outgoing.mk (couplerChannel p .left .rightSecond)),
    incident (Incident.mk (propagationChannel p .leftTwo .left))]

/-- The complete incident N7 state obtained by setting every reverse coordinate to zero. -/
def liftedIncident (p : Parameters) (state : Node → ℂ) :
    ModeAmplitude (netlist p).IncidentIndex :=
  WithLp.toLp 2 fun endpoint =>
    match endpoint.channel.1.1, endpoint.channel.1.2 with
    | .inputCoupler, .leftFirst => state 0
    | .inputCoupler, .leftSecond => state 1
    | .inputCoupler, .rightFirst => 0
    | .inputCoupler, .rightSecond => 0
    | .outputCoupler, .leftFirst => state 4
    | .outputCoupler, .leftSecond => state 5
    | .outputCoupler, .rightFirst => 0
    | .outputCoupler, .rightSecond => 0
    | .rightCoupler, .leftFirst => state 8
    | .rightCoupler, .leftSecond => state 10
    | .rightCoupler, .rightFirst => 0
    | .rightCoupler, .rightSecond => 0
    | .leftCoupler, .leftFirst => state 13
    | .leftCoupler, .leftSecond => state 15
    | .leftCoupler, .rightFirst => 0
    | .leftCoupler, .rightSecond => 0
    | .mainQuarterOne, .left => state 3
    | .mainQuarterOne, .right => 0
    | .mainQuarterTwo, .left => state 9
    | .mainQuarterTwo, .right => 0
    | .mainQuarterThree, .left => state 6
    | .mainQuarterThree, .right => 0
    | .mainQuarterFour, .left => state 14
    | .mainQuarterFour, .right => 0
    | .rightHalfOne, .left => state 11
    | .rightHalfOne, .right => 0
    | .rightHalfTwo, .left => state 12
    | .rightHalfTwo, .right => 0
    | .leftHalfOne, .left => state 16
    | .leftHalfOne, .right => 0
    | .leftHalfTwo, .left => state 17
    | .leftHalfTwo, .right => 0

/-- The complete outgoing N7 state obtained by setting every reverse coordinate to zero. -/
def liftedOutgoing (p : Parameters) (state : Node → ℂ) :
    ModeAmplitude (netlist p).OutgoingIndex :=
  WithLp.toLp 2 fun endpoint =>
    match endpoint.channel.1.1, endpoint.channel.1.2 with
    | .inputCoupler, .leftFirst => 0
    | .inputCoupler, .leftSecond => 0
    | .inputCoupler, .rightFirst => state 2
    | .inputCoupler, .rightSecond => state 3
    | .outputCoupler, .leftFirst => 0
    | .outputCoupler, .leftSecond => 0
    | .outputCoupler, .rightFirst => state 6
    | .outputCoupler, .rightSecond => state 7
    | .rightCoupler, .leftFirst => 0
    | .rightCoupler, .leftSecond => 0
    | .rightCoupler, .rightFirst => state 9
    | .rightCoupler, .rightSecond => state 11
    | .leftCoupler, .leftFirst => 0
    | .leftCoupler, .leftSecond => 0
    | .leftCoupler, .rightFirst => state 14
    | .leftCoupler, .rightSecond => state 16
    | .mainQuarterOne, .left => 0
    | .mainQuarterOne, .right => state 8
    | .mainQuarterTwo, .left => 0
    | .mainQuarterTwo, .right => state 4
    | .mainQuarterThree, .left => 0
    | .mainQuarterThree, .right => state 13
    | .mainQuarterFour, .left => 0
    | .mainQuarterFour, .right => state 1
    | .rightHalfOne, .left => 0
    | .rightHalfOne, .right => state 12
    | .rightHalfTwo, .left => 0
    | .rightHalfTwo, .right => state 10
    | .leftHalfOne, .left => 0
    | .leftHalfOne, .right => state 17
    | .leftHalfTwo, .left => 0
    | .leftHalfTwo, .right => state 15

/-- A forward graph solution's lifted amplitudes satisfy all twelve component scattering laws. -/
lemma liftedOutgoing_eq_scatteringTransform (p : Parameters) (input : ℂ)
    (state : Node → ℂ) (hForward : ForwardEquations p input state) :
    liftedOutgoing p state =
      (netlist p).scatteringTransform.toLinearMap (liftedIncident p state) := by
  apply WithLp.ofLp_injective 2
  funext endpoint
  rcases endpoint with ⟨⟨⟨component, port⟩, mode⟩⟩
  -- These are all 32 physical outputs: sixteen coupler and sixteen delay coordinates.
  cases component <;> cases port <;> cases mode
  · change liftedOutgoing p state (Outgoing.mk (couplerChannel p .input .leftFirst)) =
      (netlist p).scatteringTransform.toLinearMap (liftedIncident p state)
        (Outgoing.mk (couplerChannel p .input .leftFirst))
    rw [scatteringEquation_coupler_leftFirst p .input (liftedIncident p state) _ rfl]
    simp [liftedIncident, liftedOutgoing, couplerChannel, CouplerLabel.parameters]
  · change liftedOutgoing p state (Outgoing.mk (couplerChannel p .input .leftSecond)) =
      (netlist p).scatteringTransform.toLinearMap (liftedIncident p state)
        (Outgoing.mk (couplerChannel p .input .leftSecond))
    rw [scatteringEquation_coupler_leftSecond p .input (liftedIncident p state) _ rfl]
    simp [liftedIncident, liftedOutgoing, couplerChannel, CouplerLabel.parameters]
  · change liftedOutgoing p state (Outgoing.mk (couplerChannel p .input .rightFirst)) =
      (netlist p).scatteringTransform.toLinearMap (liftedIncident p state)
        (Outgoing.mk (couplerChannel p .input .rightFirst))
    rw [scatteringEquation_coupler_rightFirst p .input (liftedIncident p state) _ rfl]
    simpa [liftedIncident, liftedOutgoing, couplerChannel, CouplerLabel.parameters] using
      hForward.nodeThree
  · change liftedOutgoing p state (Outgoing.mk (couplerChannel p .input .rightSecond)) =
      (netlist p).scatteringTransform.toLinearMap (liftedIncident p state)
        (Outgoing.mk (couplerChannel p .input .rightSecond))
    rw [scatteringEquation_coupler_rightSecond p .input (liftedIncident p state) _ rfl]
    simpa [liftedIncident, liftedOutgoing, couplerChannel, CouplerLabel.parameters] using
      hForward.nodeFour
  · change liftedOutgoing p state (Outgoing.mk (couplerChannel p .output .leftFirst)) =
      (netlist p).scatteringTransform.toLinearMap (liftedIncident p state)
        (Outgoing.mk (couplerChannel p .output .leftFirst))
    rw [scatteringEquation_coupler_leftFirst p .output (liftedIncident p state) _ rfl]
    simp [liftedIncident, liftedOutgoing, couplerChannel, CouplerLabel.parameters]
  · change liftedOutgoing p state (Outgoing.mk (couplerChannel p .output .leftSecond)) =
      (netlist p).scatteringTransform.toLinearMap (liftedIncident p state)
        (Outgoing.mk (couplerChannel p .output .leftSecond))
    rw [scatteringEquation_coupler_leftSecond p .output (liftedIncident p state) _ rfl]
    simp [liftedIncident, liftedOutgoing, couplerChannel, CouplerLabel.parameters]
  · change liftedOutgoing p state (Outgoing.mk (couplerChannel p .output .rightFirst)) =
      (netlist p).scatteringTransform.toLinearMap (liftedIncident p state)
        (Outgoing.mk (couplerChannel p .output .rightFirst))
    rw [scatteringEquation_coupler_rightFirst p .output (liftedIncident p state) _ rfl]
    simpa [liftedIncident, liftedOutgoing, couplerChannel, CouplerLabel.parameters] using
      hForward.nodeSeven
  · change liftedOutgoing p state (Outgoing.mk (couplerChannel p .output .rightSecond)) =
      (netlist p).scatteringTransform.toLinearMap (liftedIncident p state)
        (Outgoing.mk (couplerChannel p .output .rightSecond))
    rw [scatteringEquation_coupler_rightSecond p .output (liftedIncident p state) _ rfl]
    simpa [liftedIncident, liftedOutgoing, couplerChannel, CouplerLabel.parameters] using
      hForward.nodeEight
  · change liftedOutgoing p state (Outgoing.mk (couplerChannel p .right .leftFirst)) =
      (netlist p).scatteringTransform.toLinearMap (liftedIncident p state)
        (Outgoing.mk (couplerChannel p .right .leftFirst))
    rw [scatteringEquation_coupler_leftFirst p .right (liftedIncident p state) _ rfl]
    simp [liftedIncident, liftedOutgoing, couplerChannel, CouplerLabel.parameters]
  · change liftedOutgoing p state (Outgoing.mk (couplerChannel p .right .leftSecond)) =
      (netlist p).scatteringTransform.toLinearMap (liftedIncident p state)
        (Outgoing.mk (couplerChannel p .right .leftSecond))
    rw [scatteringEquation_coupler_leftSecond p .right (liftedIncident p state) _ rfl]
    simp [liftedIncident, liftedOutgoing, couplerChannel, CouplerLabel.parameters]
  · change liftedOutgoing p state (Outgoing.mk (couplerChannel p .right .rightFirst)) =
      (netlist p).scatteringTransform.toLinearMap (liftedIncident p state)
        (Outgoing.mk (couplerChannel p .right .rightFirst))
    rw [scatteringEquation_coupler_rightFirst p .right (liftedIncident p state) _ rfl]
    simpa [liftedIncident, liftedOutgoing, couplerChannel, CouplerLabel.parameters] using
      hForward.nodeTen
  · change liftedOutgoing p state (Outgoing.mk (couplerChannel p .right .rightSecond)) =
      (netlist p).scatteringTransform.toLinearMap (liftedIncident p state)
        (Outgoing.mk (couplerChannel p .right .rightSecond))
    rw [scatteringEquation_coupler_rightSecond p .right (liftedIncident p state) _ rfl]
    simpa [liftedIncident, liftedOutgoing, couplerChannel, CouplerLabel.parameters] using
      hForward.nodeTwelve
  · change liftedOutgoing p state (Outgoing.mk (couplerChannel p .left .leftFirst)) =
      (netlist p).scatteringTransform.toLinearMap (liftedIncident p state)
        (Outgoing.mk (couplerChannel p .left .leftFirst))
    rw [scatteringEquation_coupler_leftFirst p .left (liftedIncident p state) _ rfl]
    simp [liftedIncident, liftedOutgoing, couplerChannel, CouplerLabel.parameters]
  · change liftedOutgoing p state (Outgoing.mk (couplerChannel p .left .leftSecond)) =
      (netlist p).scatteringTransform.toLinearMap (liftedIncident p state)
        (Outgoing.mk (couplerChannel p .left .leftSecond))
    rw [scatteringEquation_coupler_leftSecond p .left (liftedIncident p state) _ rfl]
    simp [liftedIncident, liftedOutgoing, couplerChannel, CouplerLabel.parameters]
  · change liftedOutgoing p state (Outgoing.mk (couplerChannel p .left .rightFirst)) =
      (netlist p).scatteringTransform.toLinearMap (liftedIncident p state)
        (Outgoing.mk (couplerChannel p .left .rightFirst))
    rw [scatteringEquation_coupler_rightFirst p .left (liftedIncident p state) _ rfl]
    simpa [liftedIncident, liftedOutgoing, couplerChannel, CouplerLabel.parameters] using
      hForward.nodeFifteen
  · change liftedOutgoing p state (Outgoing.mk (couplerChannel p .left .rightSecond)) =
      (netlist p).scatteringTransform.toLinearMap (liftedIncident p state)
        (Outgoing.mk (couplerChannel p .left .rightSecond))
    rw [scatteringEquation_coupler_rightSecond p .left (liftedIncident p state) _ rfl]
    simpa [liftedIncident, liftedOutgoing, couplerChannel, CouplerLabel.parameters] using
      hForward.nodeSeventeen
  · change liftedOutgoing p state (Outgoing.mk (propagationChannel p .mainOne .left)) =
      (netlist p).scatteringTransform.toLinearMap (liftedIncident p state)
        (Outgoing.mk (propagationChannel p .mainOne .left))
    rw [scatteringEquation_propagation_left p .mainOne (liftedIncident p state) _ rfl]
    simp [liftedIncident, liftedOutgoing, propagationChannel, PropagationLabel.parameters]
  · change liftedOutgoing p state (Outgoing.mk (propagationChannel p .mainOne .right)) =
      (netlist p).scatteringTransform.toLinearMap (liftedIncident p state)
        (Outgoing.mk (propagationChannel p .mainOne .right))
    rw [scatteringEquation_propagation_right p .mainOne (liftedIncident p state) _ rfl]
    simpa [liftedIncident, liftedOutgoing, propagationChannel, PropagationLabel.parameters,
      Parameters.mainQuarterOneCoefficient] using hForward.nodeNine
  · change liftedOutgoing p state (Outgoing.mk (propagationChannel p .mainTwo .left)) =
      (netlist p).scatteringTransform.toLinearMap (liftedIncident p state)
        (Outgoing.mk (propagationChannel p .mainTwo .left))
    rw [scatteringEquation_propagation_left p .mainTwo (liftedIncident p state) _ rfl]
    simp [liftedIncident, liftedOutgoing, propagationChannel, PropagationLabel.parameters]
  · change liftedOutgoing p state (Outgoing.mk (propagationChannel p .mainTwo .right)) =
      (netlist p).scatteringTransform.toLinearMap (liftedIncident p state)
        (Outgoing.mk (propagationChannel p .mainTwo .right))
    rw [scatteringEquation_propagation_right p .mainTwo (liftedIncident p state) _ rfl]
    simpa [liftedIncident, liftedOutgoing, propagationChannel, PropagationLabel.parameters,
      Parameters.mainQuarterTwoCoefficient] using hForward.nodeFive
  · change liftedOutgoing p state (Outgoing.mk (propagationChannel p .mainThree .left)) =
      (netlist p).scatteringTransform.toLinearMap (liftedIncident p state)
        (Outgoing.mk (propagationChannel p .mainThree .left))
    rw [scatteringEquation_propagation_left p .mainThree (liftedIncident p state) _ rfl]
    simp [liftedIncident, liftedOutgoing, propagationChannel, PropagationLabel.parameters]
  · change liftedOutgoing p state (Outgoing.mk (propagationChannel p .mainThree .right)) =
      (netlist p).scatteringTransform.toLinearMap (liftedIncident p state)
        (Outgoing.mk (propagationChannel p .mainThree .right))
    rw [scatteringEquation_propagation_right p .mainThree (liftedIncident p state) _ rfl]
    simpa [liftedIncident, liftedOutgoing, propagationChannel, PropagationLabel.parameters,
      Parameters.mainQuarterThreeCoefficient] using hForward.nodeFourteen
  · change liftedOutgoing p state (Outgoing.mk (propagationChannel p .mainFour .left)) =
      (netlist p).scatteringTransform.toLinearMap (liftedIncident p state)
        (Outgoing.mk (propagationChannel p .mainFour .left))
    rw [scatteringEquation_propagation_left p .mainFour (liftedIncident p state) _ rfl]
    simp [liftedIncident, liftedOutgoing, propagationChannel, PropagationLabel.parameters]
  · change liftedOutgoing p state (Outgoing.mk (propagationChannel p .mainFour .right)) =
      (netlist p).scatteringTransform.toLinearMap (liftedIncident p state)
        (Outgoing.mk (propagationChannel p .mainFour .right))
    rw [scatteringEquation_propagation_right p .mainFour (liftedIncident p state) _ rfl]
    simpa [liftedIncident, liftedOutgoing, propagationChannel, PropagationLabel.parameters,
      Parameters.mainQuarterFourCoefficient] using hForward.nodeTwo
  · change liftedOutgoing p state (Outgoing.mk (propagationChannel p .rightOne .left)) =
      (netlist p).scatteringTransform.toLinearMap (liftedIncident p state)
        (Outgoing.mk (propagationChannel p .rightOne .left))
    rw [scatteringEquation_propagation_left p .rightOne (liftedIncident p state) _ rfl]
    simp [liftedIncident, liftedOutgoing, propagationChannel, PropagationLabel.parameters]
  · change liftedOutgoing p state (Outgoing.mk (propagationChannel p .rightOne .right)) =
      (netlist p).scatteringTransform.toLinearMap (liftedIncident p state)
        (Outgoing.mk (propagationChannel p .rightOne .right))
    rw [scatteringEquation_propagation_right p .rightOne (liftedIncident p state) _ rfl]
    simpa [liftedIncident, liftedOutgoing, propagationChannel, PropagationLabel.parameters,
      Parameters.rightHalfOneCoefficient] using hForward.nodeThirteen
  · change liftedOutgoing p state (Outgoing.mk (propagationChannel p .rightTwo .left)) =
      (netlist p).scatteringTransform.toLinearMap (liftedIncident p state)
        (Outgoing.mk (propagationChannel p .rightTwo .left))
    rw [scatteringEquation_propagation_left p .rightTwo (liftedIncident p state) _ rfl]
    simp [liftedIncident, liftedOutgoing, propagationChannel, PropagationLabel.parameters]
  · change liftedOutgoing p state (Outgoing.mk (propagationChannel p .rightTwo .right)) =
      (netlist p).scatteringTransform.toLinearMap (liftedIncident p state)
        (Outgoing.mk (propagationChannel p .rightTwo .right))
    rw [scatteringEquation_propagation_right p .rightTwo (liftedIncident p state) _ rfl]
    simpa [liftedIncident, liftedOutgoing, propagationChannel, PropagationLabel.parameters,
      Parameters.rightHalfTwoCoefficient] using hForward.nodeEleven
  · change liftedOutgoing p state (Outgoing.mk (propagationChannel p .leftOne .left)) =
      (netlist p).scatteringTransform.toLinearMap (liftedIncident p state)
        (Outgoing.mk (propagationChannel p .leftOne .left))
    rw [scatteringEquation_propagation_left p .leftOne (liftedIncident p state) _ rfl]
    simp [liftedIncident, liftedOutgoing, propagationChannel, PropagationLabel.parameters]
  · change liftedOutgoing p state (Outgoing.mk (propagationChannel p .leftOne .right)) =
      (netlist p).scatteringTransform.toLinearMap (liftedIncident p state)
        (Outgoing.mk (propagationChannel p .leftOne .right))
    rw [scatteringEquation_propagation_right p .leftOne (liftedIncident p state) _ rfl]
    simpa [liftedIncident, liftedOutgoing, propagationChannel, PropagationLabel.parameters,
      Parameters.leftHalfOneCoefficient] using hForward.nodeEighteen
  · change liftedOutgoing p state (Outgoing.mk (propagationChannel p .leftTwo .left)) =
      (netlist p).scatteringTransform.toLinearMap (liftedIncident p state)
        (Outgoing.mk (propagationChannel p .leftTwo .left))
    rw [scatteringEquation_propagation_left p .leftTwo (liftedIncident p state) _ rfl]
    simp [liftedIncident, liftedOutgoing, propagationChannel, PropagationLabel.parameters]
  · change liftedOutgoing p state (Outgoing.mk (propagationChannel p .leftTwo .right)) =
      (netlist p).scatteringTransform.toLinearMap (liftedIncident p state)
        (Outgoing.mk (propagationChannel p .leftTwo .right))
    rw [scatteringEquation_propagation_right p .leftTwo (liftedIncident p state) _ rfl]
    simpa [liftedIncident, liftedOutgoing, propagationChannel, PropagationLabel.parameters,
      Parameters.leftHalfTwoCoefficient] using hForward.nodeSixteen
/-!
## C. Physical routing
-/
/-- Incident assembly at a wire's left endpoint reads its right outgoing endpoint. -/
lemma incidentAssembly_apply_connectionLeft (p : Parameters) (connection : Connection)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (external : ModeAmplitude (netlist p).ExternalIncident) :
    (netlist p).connections.incidentAssembly outgoing external
        (Incident.mk (connectionLeftChannel p connection)) =
      outgoing (Outgoing.mk (connectionRightChannel p connection)) := by
  change
    (netlist p).connections.incidentAssembly outgoing external
        (Incident.mk ((netlist p).connections.channelEmbedding
          ⟨connection, Sum.inl (connectionLeftMode p connection)⟩)) = _
  rw [(netlist p).connections.incidentAssembly_apply_connected_channel]
  cases connection <;> rfl

/-- Incident assembly at a wire's right endpoint reads its left outgoing endpoint. -/
lemma incidentAssembly_apply_connectionRight (p : Parameters) (connection : Connection)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (external : ModeAmplitude (netlist p).ExternalIncident) :
    (netlist p).connections.incidentAssembly outgoing external
        (Incident.mk (connectionRightChannel p connection)) =
      outgoing (Outgoing.mk (connectionLeftChannel p connection)) := by
  change
    (netlist p).connections.incidentAssembly outgoing external
        (Incident.mk ((netlist p).connections.channelEmbedding
          ⟨connection, Sum.inr (connectionRightMode p connection)⟩)) = _
  rw [(netlist p).connections.incidentAssembly_apply_connected_channel]
  cases connection <;> rfl

/-- Incident assembly at the input port returns the supplied external amplitude. -/
lemma incidentAssembly_apply_input (p : Parameters)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (external : ModeAmplitude (netlist p).ExternalIncident) :
    (netlist p).connections.incidentAssembly outgoing external
        (Incident.mk (couplerChannel p .input .leftFirst)) =
      external (Incident.mk (inputChannel p)) := by
  change (netlist p).connections.incidentAssembly outgoing external
      (Incident.mk (componentChannel p .inputCoupler
        ⟨DirectionalCoupler.Port.leftFirst, ()⟩)) = _
  simpa only [inputChannel] using
    (netlist p).connections.incidentAssembly_apply_external
      outgoing external (inputChannel p)

/-- Incident assembly at the through port returns its external incident amplitude. -/
lemma incidentAssembly_apply_through (p : Parameters)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (external : ModeAmplitude (netlist p).ExternalIncident) :
    (netlist p).connections.incidentAssembly outgoing external
        (Incident.mk (couplerChannel p .input .rightFirst)) =
      external (Incident.mk (throughChannel p)) := by
  change (netlist p).connections.incidentAssembly outgoing external
      (Incident.mk (componentChannel p .inputCoupler
        ⟨DirectionalCoupler.Port.rightFirst, ()⟩)) = _
  simpa only [throughChannel] using
    (netlist p).connections.incidentAssembly_apply_external
      outgoing external (throughChannel p)

/-- Incident assembly at the add port returns its external incident amplitude. -/
lemma incidentAssembly_apply_add (p : Parameters)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (external : ModeAmplitude (netlist p).ExternalIncident) :
    (netlist p).connections.incidentAssembly outgoing external
        (Incident.mk (couplerChannel p .output .leftSecond)) =
      external (Incident.mk (addChannel p)) := by
  change (netlist p).connections.incidentAssembly outgoing external
      (Incident.mk (componentChannel p .outputCoupler
        ⟨DirectionalCoupler.Port.leftSecond, ()⟩)) = _
  simpa only [addChannel] using
    (netlist p).connections.incidentAssembly_apply_external
      outgoing external (addChannel p)

/-- Incident assembly at the drop port returns its external incident amplitude. -/
lemma incidentAssembly_apply_drop (p : Parameters)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (external : ModeAmplitude (netlist p).ExternalIncident) :
    (netlist p).connections.incidentAssembly outgoing external
        (Incident.mk (couplerChannel p .output .rightSecond)) =
      external (Incident.mk (dropChannel p)) := by
  change (netlist p).connections.incidentAssembly outgoing external
      (Incident.mk (componentChannel p .outputCoupler
        ⟨DirectionalCoupler.Port.rightSecond, ()⟩)) = _
  simpa only [dropChannel] using
    (netlist p).connections.incidentAssembly_apply_external
      outgoing external (dropChannel p)

/-- A forward graph solution's lift satisfies both ends of every wire and all four externals. -/
lemma liftedIncident_eq_incidentAssembly (p : Parameters) (input : ℂ)
    (state : Node → ℂ) (hForward : ForwardEquations p input state) :
    liftedIncident p state =
      (netlist p).connections.incidentAssembly
        (liftedOutgoing p state) (inputAmplitude p input) := by
  apply WithLp.ofLp_injective 2
  funext endpoint
  rcases endpoint with ⟨⟨⟨component, port⟩, mode⟩⟩
  -- Exhaustion checks 28 connected endpoints and the four external coordinates.
  cases component <;> cases port <;> cases mode
  · change liftedIncident p state (Incident.mk (couplerChannel p .input .leftFirst)) =
      (netlist p).connections.incidentAssembly (liftedOutgoing p state)
        (inputAmplitude p input) (Incident.mk (couplerChannel p .input .leftFirst))
    rw [incidentAssembly_apply_input]
    simpa [liftedIncident, couplerChannel] using hForward.nodeOne
  · change liftedIncident p state
        (Incident.mk (connectionRightChannel p .quarterFourToInput)) =
      (netlist p).connections.incidentAssembly (liftedOutgoing p state)
        (inputAmplitude p input)
        (Incident.mk (connectionRightChannel p .quarterFourToInput))
    rw [incidentAssembly_apply_connectionRight]
    rfl
  · change liftedIncident p state (Incident.mk (couplerChannel p .input .rightFirst)) =
      (netlist p).connections.incidentAssembly (liftedOutgoing p state)
        (inputAmplitude p input) (Incident.mk (couplerChannel p .input .rightFirst))
    rw [incidentAssembly_apply_through]
    simp [liftedIncident, couplerChannel]
  · change liftedIncident p state
        (Incident.mk (connectionLeftChannel p .inputToQuarterOne)) =
      (netlist p).connections.incidentAssembly (liftedOutgoing p state)
        (inputAmplitude p input)
        (Incident.mk (connectionLeftChannel p .inputToQuarterOne))
    rw [incidentAssembly_apply_connectionLeft]
    rfl

  · change liftedIncident p state
        (Incident.mk (connectionRightChannel p .quarterTwoToOutput)) =
      (netlist p).connections.incidentAssembly (liftedOutgoing p state)
        (inputAmplitude p input)
        (Incident.mk (connectionRightChannel p .quarterTwoToOutput))
    rw [incidentAssembly_apply_connectionRight]
    rfl
  · change liftedIncident p state (Incident.mk (couplerChannel p .output .leftSecond)) =
      (netlist p).connections.incidentAssembly (liftedOutgoing p state)
        (inputAmplitude p input) (Incident.mk (couplerChannel p .output .leftSecond))
    rw [incidentAssembly_apply_add]
    simpa [liftedIncident, couplerChannel] using hForward.nodeSix
  · change liftedIncident p state
        (Incident.mk (connectionLeftChannel p .outputToQuarterThree)) =
      (netlist p).connections.incidentAssembly (liftedOutgoing p state)
        (inputAmplitude p input)
        (Incident.mk (connectionLeftChannel p .outputToQuarterThree))
    rw [incidentAssembly_apply_connectionLeft]
    rfl

  · change liftedIncident p state (Incident.mk (couplerChannel p .output .rightSecond)) =
      (netlist p).connections.incidentAssembly (liftedOutgoing p state)
        (inputAmplitude p input) (Incident.mk (couplerChannel p .output .rightSecond))
    rw [incidentAssembly_apply_drop]
    simp [liftedIncident, couplerChannel]
  · change liftedIncident p state
        (Incident.mk (connectionRightChannel p .quarterOneToRight)) =
      (netlist p).connections.incidentAssembly (liftedOutgoing p state)
        (inputAmplitude p input)
        (Incident.mk (connectionRightChannel p .quarterOneToRight))
    rw [incidentAssembly_apply_connectionRight]
    rfl
  · change liftedIncident p state
        (Incident.mk (connectionRightChannel p .rightHalfTwoToCoupler)) =
      (netlist p).connections.incidentAssembly (liftedOutgoing p state)
        (inputAmplitude p input)
        (Incident.mk (connectionRightChannel p .rightHalfTwoToCoupler))
    rw [incidentAssembly_apply_connectionRight]
    rfl
  · change liftedIncident p state
        (Incident.mk (connectionLeftChannel p .rightToQuarterTwo)) =
      (netlist p).connections.incidentAssembly (liftedOutgoing p state)
        (inputAmplitude p input)
        (Incident.mk (connectionLeftChannel p .rightToQuarterTwo))
    rw [incidentAssembly_apply_connectionLeft]
    rfl
  · change liftedIncident p state
        (Incident.mk (connectionLeftChannel p .rightToHalfOne)) =
      (netlist p).connections.incidentAssembly (liftedOutgoing p state)
        (inputAmplitude p input)
        (Incident.mk (connectionLeftChannel p .rightToHalfOne))
    rw [incidentAssembly_apply_connectionLeft]
    rfl
  · change liftedIncident p state
        (Incident.mk (connectionRightChannel p .quarterThreeToLeft)) =
      (netlist p).connections.incidentAssembly (liftedOutgoing p state)
        (inputAmplitude p input)
        (Incident.mk (connectionRightChannel p .quarterThreeToLeft))
    rw [incidentAssembly_apply_connectionRight]
    rfl
  · change liftedIncident p state
        (Incident.mk (connectionRightChannel p .leftHalfTwoToCoupler)) =
      (netlist p).connections.incidentAssembly (liftedOutgoing p state)
        (inputAmplitude p input)
        (Incident.mk (connectionRightChannel p .leftHalfTwoToCoupler))
    rw [incidentAssembly_apply_connectionRight]
    rfl
  · change liftedIncident p state
        (Incident.mk (connectionLeftChannel p .leftToQuarterFour)) =
      (netlist p).connections.incidentAssembly (liftedOutgoing p state)
        (inputAmplitude p input)
        (Incident.mk (connectionLeftChannel p .leftToQuarterFour))
    rw [incidentAssembly_apply_connectionLeft]
    rfl
  · change liftedIncident p state
        (Incident.mk (connectionLeftChannel p .leftToHalfOne)) =
      (netlist p).connections.incidentAssembly (liftedOutgoing p state)
        (inputAmplitude p input)
        (Incident.mk (connectionLeftChannel p .leftToHalfOne))
    rw [incidentAssembly_apply_connectionLeft]
    rfl
  · change liftedIncident p state
        (Incident.mk (connectionRightChannel p .inputToQuarterOne)) =
      (netlist p).connections.incidentAssembly (liftedOutgoing p state)
        (inputAmplitude p input)
        (Incident.mk (connectionRightChannel p .inputToQuarterOne))
    rw [incidentAssembly_apply_connectionRight]
    rfl
  · change liftedIncident p state
        (Incident.mk (connectionLeftChannel p .quarterOneToRight)) =
      (netlist p).connections.incidentAssembly (liftedOutgoing p state)
        (inputAmplitude p input)
        (Incident.mk (connectionLeftChannel p .quarterOneToRight))
    rw [incidentAssembly_apply_connectionLeft]
    rfl
  · change liftedIncident p state
        (Incident.mk (connectionRightChannel p .rightToQuarterTwo)) =
      (netlist p).connections.incidentAssembly (liftedOutgoing p state)
        (inputAmplitude p input)
        (Incident.mk (connectionRightChannel p .rightToQuarterTwo))
    rw [incidentAssembly_apply_connectionRight]
    rfl
  · change liftedIncident p state
        (Incident.mk (connectionLeftChannel p .quarterTwoToOutput)) =
      (netlist p).connections.incidentAssembly (liftedOutgoing p state)
        (inputAmplitude p input)
        (Incident.mk (connectionLeftChannel p .quarterTwoToOutput))
    rw [incidentAssembly_apply_connectionLeft]
    rfl
  · change liftedIncident p state
        (Incident.mk (connectionRightChannel p .outputToQuarterThree)) =
      (netlist p).connections.incidentAssembly (liftedOutgoing p state)
        (inputAmplitude p input)
        (Incident.mk (connectionRightChannel p .outputToQuarterThree))
    rw [incidentAssembly_apply_connectionRight]
    rfl
  · change liftedIncident p state
        (Incident.mk (connectionLeftChannel p .quarterThreeToLeft)) =
      (netlist p).connections.incidentAssembly (liftedOutgoing p state)
        (inputAmplitude p input)
        (Incident.mk (connectionLeftChannel p .quarterThreeToLeft))
    rw [incidentAssembly_apply_connectionLeft]
    rfl
  · change liftedIncident p state
        (Incident.mk (connectionRightChannel p .leftToQuarterFour)) =
      (netlist p).connections.incidentAssembly (liftedOutgoing p state)
        (inputAmplitude p input)
        (Incident.mk (connectionRightChannel p .leftToQuarterFour))
    rw [incidentAssembly_apply_connectionRight]
    rfl
  · change liftedIncident p state
        (Incident.mk (connectionLeftChannel p .quarterFourToInput)) =
      (netlist p).connections.incidentAssembly (liftedOutgoing p state)
        (inputAmplitude p input)
        (Incident.mk (connectionLeftChannel p .quarterFourToInput))
    rw [incidentAssembly_apply_connectionLeft]
    rfl
  · change liftedIncident p state
        (Incident.mk (connectionRightChannel p .rightToHalfOne)) =
      (netlist p).connections.incidentAssembly (liftedOutgoing p state)
        (inputAmplitude p input)
        (Incident.mk (connectionRightChannel p .rightToHalfOne))
    rw [incidentAssembly_apply_connectionRight]
    rfl
  · change liftedIncident p state
        (Incident.mk (connectionLeftChannel p .rightHalfJoin)) =
      (netlist p).connections.incidentAssembly (liftedOutgoing p state)
        (inputAmplitude p input)
        (Incident.mk (connectionLeftChannel p .rightHalfJoin))
    rw [incidentAssembly_apply_connectionLeft]
    rfl
  · change liftedIncident p state
        (Incident.mk (connectionRightChannel p .rightHalfJoin)) =
      (netlist p).connections.incidentAssembly (liftedOutgoing p state)
        (inputAmplitude p input)
        (Incident.mk (connectionRightChannel p .rightHalfJoin))
    rw [incidentAssembly_apply_connectionRight]
    rfl
  · change liftedIncident p state
        (Incident.mk (connectionLeftChannel p .rightHalfTwoToCoupler)) =
      (netlist p).connections.incidentAssembly (liftedOutgoing p state)
        (inputAmplitude p input)
        (Incident.mk (connectionLeftChannel p .rightHalfTwoToCoupler))
    rw [incidentAssembly_apply_connectionLeft]
    rfl
  · change liftedIncident p state
        (Incident.mk (connectionRightChannel p .leftToHalfOne)) =
      (netlist p).connections.incidentAssembly (liftedOutgoing p state)
        (inputAmplitude p input)
        (Incident.mk (connectionRightChannel p .leftToHalfOne))
    rw [incidentAssembly_apply_connectionRight]
    rfl
  · change liftedIncident p state
        (Incident.mk (connectionLeftChannel p .leftHalfJoin)) =
      (netlist p).connections.incidentAssembly (liftedOutgoing p state)
        (inputAmplitude p input)
        (Incident.mk (connectionLeftChannel p .leftHalfJoin))
    rw [incidentAssembly_apply_connectionLeft]
    rfl
  · change liftedIncident p state
        (Incident.mk (connectionRightChannel p .leftHalfJoin)) =
      (netlist p).connections.incidentAssembly (liftedOutgoing p state)
        (inputAmplitude p input)
        (Incident.mk (connectionRightChannel p .leftHalfJoin))
    rw [incidentAssembly_apply_connectionRight]
    rfl
  · change liftedIncident p state
        (Incident.mk (connectionLeftChannel p .leftHalfTwoToCoupler)) =
      (netlist p).connections.incidentAssembly (liftedOutgoing p state)
        (inputAmplitude p input)
        (Incident.mk (connectionLeftChannel p .leftHalfTwoToCoupler))
    rw [incidentAssembly_apply_connectionLeft]
    rfl
/-!
## D. Projection and relational equivalence
-/
/-- The wire entering a selected propagation component. -/
def PropagationLabel.inputConnection : PropagationLabel → Connection
  | .mainOne => .inputToQuarterOne
  | .mainTwo => .rightToQuarterTwo
  | .mainThree => .outputToQuarterThree
  | .mainFour => .leftToQuarterFour
  | .rightOne => .rightToHalfOne
  | .rightTwo => .rightHalfJoin
  | .leftOne => .leftToHalfOne
  | .leftTwo => .leftHalfJoin

/-- The wire leaving a selected propagation component. -/
def PropagationLabel.outputConnection : PropagationLabel → Connection
  | .mainOne => .quarterOneToRight
  | .mainTwo => .quarterTwoToOutput
  | .mainThree => .quarterThreeToLeft
  | .mainFour => .quarterFourToInput
  | .rightOne => .rightHalfJoin
  | .rightTwo => .rightHalfTwoToCoupler
  | .leftOne => .leftHalfJoin
  | .leftTwo => .leftHalfTwoToCoupler

/-- The named physical output immediately upstream of a selected propagation component. -/
def PropagationLabel.upstreamChannel (p : Parameters) :
    PropagationLabel → (netlist p).Channel
  | .mainOne => couplerChannel p .input .rightSecond
  | .mainTwo => couplerChannel p .right .rightFirst
  | .mainThree => couplerChannel p .output .rightFirst
  | .mainFour => couplerChannel p .left .rightFirst
  | .rightOne => couplerChannel p .right .rightSecond
  | .rightTwo => propagationChannel p .rightOne .right
  | .leftOne => couplerChannel p .left .rightSecond
  | .leftTwo => propagationChannel p .leftOne .right

/-- The named physical input immediately downstream of a selected propagation component. -/
def PropagationLabel.downstreamChannel (p : Parameters) :
    PropagationLabel → (netlist p).Channel
  | .mainOne => couplerChannel p .right .leftFirst
  | .mainTwo => couplerChannel p .output .leftFirst
  | .mainThree => couplerChannel p .left .leftFirst
  | .mainFour => couplerChannel p .input .leftSecond
  | .rightOne => propagationChannel p .rightTwo .left
  | .rightTwo => couplerChannel p .right .leftSecond
  | .leftOne => propagationChannel p .leftTwo .left
  | .leftTwo => couplerChannel p .left .leftSecond

/-- The named upstream channel is the left endpoint of the selected input wire. -/
private lemma upstreamChannel_eq_inputConnectionLeft (p : Parameters)
    (label : PropagationLabel) :
    label.upstreamChannel p = connectionLeftChannel p label.inputConnection := by
  cases label <;> rfl

/-- The named downstream channel is the right endpoint of the selected output wire. -/
private lemma downstreamChannel_eq_outputConnectionRight (p : Parameters)
    (label : PropagationLabel) :
    label.downstreamChannel p = connectionRightChannel p label.outputConnection := by
  cases label <;> rfl

/-- A propagation component's left port is the right endpoint of its input wire. -/
private lemma propagationChannel_left_eq_inputConnectionRight (p : Parameters)
    (label : PropagationLabel) :
    propagationChannel p label .left =
      connectionRightChannel p label.inputConnection := by
  cases label <;> rfl

/-- A propagation component's right port is the left endpoint of its output wire. -/
private lemma propagationChannel_right_eq_outputConnectionLeft (p : Parameters)
    (label : PropagationLabel) :
    propagationChannel p label .right =
      connectionLeftChannel p label.outputConnection := by
  cases label <;> rfl

/-- A routed propagation component multiplies its upstream output by its physical coefficient. -/
lemma propagationCoordinate_of_netlistEquations (p : Parameters) (label : PropagationLabel)
    (external : ModeAmplitude (netlist p).ExternalIncident)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident)
    (hAssembly : incident = (netlist p).connections.incidentAssembly outgoing external) :
    incident (Incident.mk (label.downstreamChannel p)) =
      MatchedPropagation.transmissionCoefficient (label.parameters p) *
        outgoing (Outgoing.mk (label.upstreamChannel p)) := by
  have hAfter := congrArg (fun state => state
    (Incident.mk (connectionRightChannel p label.outputConnection))) hAssembly
  rw [incidentAssembly_apply_connectionRight] at hAfter
  have hBefore := congrArg (fun state => state
    (Incident.mk (connectionRightChannel p label.inputConnection))) hAssembly
  rw [incidentAssembly_apply_connectionRight] at hBefore
  have hPropagation := scatteringEquation_propagation_right
    p label incident outgoing hScattering
  calc
    _ = incident (Incident.mk (connectionRightChannel p label.outputConnection)) := by
      rw [downstreamChannel_eq_outputConnectionRight]
    _ = outgoing (Outgoing.mk (connectionLeftChannel p label.outputConnection)) := hAfter
    _ = outgoing (Outgoing.mk (propagationChannel p label .right)) := by
      rw [propagationChannel_right_eq_outputConnectionLeft]
    _ = MatchedPropagation.transmissionCoefficient (label.parameters p) *
        incident (Incident.mk (propagationChannel p label .left)) := hPropagation
    _ = MatchedPropagation.transmissionCoefficient (label.parameters p) *
        incident (Incident.mk (connectionRightChannel p label.inputConnection)) := by
      rw [propagationChannel_left_eq_inputConnectionRight]
    _ = MatchedPropagation.transmissionCoefficient (label.parameters p) *
        outgoing (Outgoing.mk (connectionLeftChannel p label.inputConnection)) := by rw [hBefore]
    _ = _ := by rw [upstreamChannel_eq_inputConnectionLeft]

/-- Projecting a lifted N7 state recovers all eighteen original graph coordinates. -/
lemma forwardState_lifted (p : Parameters) (state : Node → ℂ) :
    forwardState p (liftedIncident p state) (liftedOutgoing p state) = state := by
  funext node
  fin_cases node <;> rfl

/-- Raw scattering and wiring with source-only excitation imply the displayed forward equations. -/
lemma forwardEquations_of_netlistEquations (p : Parameters) (input : ℂ)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident)
    (hAssembly : incident = (netlist p).connections.incidentAssembly
      outgoing (inputAmplitude p input)) :
    ForwardEquations p input (forwardState p incident outgoing) := by
  have hInput := congrArg (fun state => state
    (Incident.mk (couplerChannel p .input .leftFirst))) hAssembly
  rw [incidentAssembly_apply_input] at hInput
  have hAdd := congrArg (fun state => state
    (Incident.mk (couplerChannel p .output .leftSecond))) hAssembly
  rw [incidentAssembly_apply_add] at hAdd
  have hMainOne := propagationCoordinate_of_netlistEquations
    p .mainOne (inputAmplitude p input) incident outgoing hScattering hAssembly
  have hMainTwo := propagationCoordinate_of_netlistEquations
    p .mainTwo (inputAmplitude p input) incident outgoing hScattering hAssembly
  have hMainThree := propagationCoordinate_of_netlistEquations
    p .mainThree (inputAmplitude p input) incident outgoing hScattering hAssembly
  have hMainFour := propagationCoordinate_of_netlistEquations
    p .mainFour (inputAmplitude p input) incident outgoing hScattering hAssembly
  have hRightOne := propagationCoordinate_of_netlistEquations
    p .rightOne (inputAmplitude p input) incident outgoing hScattering hAssembly
  have hRightTwo := propagationCoordinate_of_netlistEquations
    p .rightTwo (inputAmplitude p input) incident outgoing hScattering hAssembly
  have hLeftOne := propagationCoordinate_of_netlistEquations
    p .leftOne (inputAmplitude p input) incident outgoing hScattering hAssembly
  have hLeftTwo := propagationCoordinate_of_netlistEquations
    p .leftTwo (inputAmplitude p input) incident outgoing hScattering hAssembly
  have hRightJoin := congrArg (fun state => state
    (Incident.mk (connectionRightChannel p .rightHalfJoin))) hAssembly
  rw [incidentAssembly_apply_connectionRight] at hRightJoin
  have hRightJoin' :
      incident (Incident.mk (propagationChannel p .rightTwo .left)) =
        outgoing (Outgoing.mk (propagationChannel p .rightOne .right)) := by
    rw [propagationChannel_left_eq_inputConnectionRight,
      propagationChannel_right_eq_outputConnectionLeft]
    exact hRightJoin
  have hRightTwoNode :
      incident (Incident.mk (couplerChannel p .right .leftSecond)) =
        p.rightHalfTwoCoefficient *
          incident (Incident.mk (propagationChannel p .rightTwo .left)) := by
    calc
      _ = MatchedPropagation.transmissionCoefficient p.rightHalfTwo *
          outgoing (Outgoing.mk (propagationChannel p .rightOne .right)) := by
        simpa [PropagationLabel.parameters, PropagationLabel.upstreamChannel,
          PropagationLabel.downstreamChannel, Parameters.rightHalfTwoCoefficient] using hRightTwo
      _ = _ := by rw [Parameters.rightHalfTwoCoefficient, hRightJoin']
  have hLeftJoin := congrArg (fun state => state
    (Incident.mk (connectionRightChannel p .leftHalfJoin))) hAssembly
  rw [incidentAssembly_apply_connectionRight] at hLeftJoin
  have hLeftJoin' :
      incident (Incident.mk (propagationChannel p .leftTwo .left)) =
        outgoing (Outgoing.mk (propagationChannel p .leftOne .right)) := by
    rw [propagationChannel_left_eq_inputConnectionRight,
      propagationChannel_right_eq_outputConnectionLeft]
    exact hLeftJoin
  have hLeftTwoNode :
      incident (Incident.mk (couplerChannel p .left .leftSecond)) =
        p.leftHalfTwoCoefficient *
          incident (Incident.mk (propagationChannel p .leftTwo .left)) := by
    calc
      _ = MatchedPropagation.transmissionCoefficient p.leftHalfTwo *
          outgoing (Outgoing.mk (propagationChannel p .leftOne .right)) := by
        simpa [PropagationLabel.parameters, PropagationLabel.upstreamChannel,
          PropagationLabel.downstreamChannel, Parameters.leftHalfTwoCoefficient] using hLeftTwo
      _ = _ := by rw [Parameters.leftHalfTwoCoefficient, hLeftJoin']
  have hInputFirst := scatteringEquation_coupler_rightFirst
    p .input incident outgoing hScattering
  have hInputSecond := scatteringEquation_coupler_rightSecond
    p .input incident outgoing hScattering
  have hOutputFirst := scatteringEquation_coupler_rightFirst
    p .output incident outgoing hScattering
  have hOutputSecond := scatteringEquation_coupler_rightSecond
    p .output incident outgoing hScattering
  have hRightFirst := scatteringEquation_coupler_rightFirst
    p .right incident outgoing hScattering
  have hRightSecond := scatteringEquation_coupler_rightSecond
    p .right incident outgoing hScattering
  have hLeftFirst := scatteringEquation_coupler_rightFirst
    p .left incident outgoing hScattering
  have hLeftSecond := scatteringEquation_coupler_rightSecond
    p .left incident outgoing hScattering
  exact ⟨by simpa [forwardState] using hInput,
    by simpa [forwardState, PropagationLabel.parameters, PropagationLabel.upstreamChannel,
      PropagationLabel.downstreamChannel, Parameters.mainQuarterFourCoefficient] using hMainFour,
    by simpa [forwardState, CouplerLabel.parameters] using hInputFirst,
    by simpa [forwardState, CouplerLabel.parameters] using hInputSecond,
    by simpa [forwardState, PropagationLabel.parameters, PropagationLabel.upstreamChannel,
      PropagationLabel.downstreamChannel, Parameters.mainQuarterTwoCoefficient] using hMainTwo,
    by simpa [forwardState] using hAdd,
    by simpa [forwardState, CouplerLabel.parameters] using hOutputFirst,
    by simpa [forwardState, CouplerLabel.parameters] using hOutputSecond,
    by simpa [forwardState, PropagationLabel.parameters, PropagationLabel.upstreamChannel,
      PropagationLabel.downstreamChannel, Parameters.mainQuarterOneCoefficient] using hMainOne,
    by simpa [forwardState, CouplerLabel.parameters] using hRightFirst,
    by simpa [forwardState, PropagationLabel.parameters, PropagationLabel.upstreamChannel,
      PropagationLabel.downstreamChannel, Parameters.rightHalfTwoCoefficient] using hRightTwoNode,
    by simpa [forwardState, CouplerLabel.parameters] using hRightSecond,
    by simpa [forwardState, PropagationLabel.parameters, PropagationLabel.upstreamChannel,
      PropagationLabel.downstreamChannel, Parameters.rightHalfOneCoefficient] using hRightOne,
    by simpa [forwardState, PropagationLabel.parameters, PropagationLabel.upstreamChannel,
      PropagationLabel.downstreamChannel, Parameters.mainQuarterThreeCoefficient] using hMainThree,
    by simpa [forwardState, CouplerLabel.parameters] using hLeftFirst,
    by simpa [forwardState, PropagationLabel.parameters, PropagationLabel.upstreamChannel,
      PropagationLabel.downstreamChannel, Parameters.leftHalfTwoCoefficient] using hLeftTwoNode,
    by simpa [forwardState, CouplerLabel.parameters] using hLeftSecond,
    by simpa [forwardState, PropagationLabel.parameters, PropagationLabel.upstreamChannel,
      PropagationLabel.downstreamChannel, Parameters.leftHalfOneCoefficient] using hLeftOne⟩

/-- Every complete zero-reverse N7 realization projects to a solution of the directed graph. -/
lemma forwardState_isNodeSolution_of_netlistEquations (p : Parameters) (input : ℂ)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident)
    (hAssembly : incident = (netlist p).connections.incidentAssembly
      outgoing (inputAmplitude p input)) :
    Physlib.SignalFlowGraph.IsNodeSolution (signalFlowGraph p) (signalInput input)
      (forwardState p incident outgoing) := by
  rw [isNodeSolution_iff_forwardEquations]
  exact forwardEquations_of_netlistEquations p input incident outgoing
    hScattering hAssembly

/-- The directed graph equation is equivalent to a complete zero-reverse N7 realization. -/
lemma isNodeSolution_iff_exists_netlistRealization (p : Parameters) (input : ℂ)
    (state : Node → ℂ) :
    Physlib.SignalFlowGraph.IsNodeSolution (signalFlowGraph p) (signalInput input) state ↔
      ∃ incident : ModeAmplitude (netlist p).IncidentIndex,
        ∃ outgoing : ModeAmplitude (netlist p).OutgoingIndex,
          outgoing = (netlist p).scatteringTransform.toLinearMap incident ∧
            incident = (netlist p).connections.incidentAssembly
              outgoing (inputAmplitude p input) ∧
            forwardState p incident outgoing = state := by
  constructor
  · intro hState
    have hForward := (isNodeSolution_iff_forwardEquations p input state).mp hState
    exact ⟨liftedIncident p state, liftedOutgoing p state,
      liftedOutgoing_eq_scatteringTransform p input state hForward,
      liftedIncident_eq_incidentAssembly p input state hForward,
      forwardState_lifted p state⟩
  · rintro ⟨incident, outgoing, hScattering, hAssembly, hProjection⟩
    rw [← hProjection]
    exact forwardState_isNodeSolution_of_netlistEquations p input incident outgoing
      hScattering hAssembly
