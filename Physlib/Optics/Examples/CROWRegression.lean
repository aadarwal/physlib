/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Examples.CROW
public import Physlib.Optics.Systems.Microring.AllPass

/-!
# Exact regression for the coupled-resonator optical waveguide example

## i. Overview

This file expands one two-ring CROW fixture directly through primitive component and wiring
equations. The two end couplers use the exact `3-4-5` amplitudes, the shared inter-ring coupler
uses `5-12-13`, and every half-arc has amplitude transmission `1 / 2` and zero phase. The selected
bus response is therefore sensitive to both the mutually coupled topology and the coupler order.

The expected state is a raw witness for the flat relation. It does not use the production
theorem-spine lemma as an oracle. A separate exact inequality compares the response only with the
product of two isolated-ring transfers. It does not exclude coupled unit-cell transfer-matrix
products; such a formulation is published for CROWs.

These are fixed-carrier normalized modal-amplitude checks. They assert no physical loss model,
dispersion, fabrication tolerance, thermal effect, frequency sweep, stability, causality,
measurement, material, reciprocity, time reversal, reference-plane invariance, or electromagnetic
power interpretation. The wrong-index sentinel pins only the selected coordinate, not a physical
orientation claim.

## ii. Key results

- `crowRegression_mem_behavior`: the exact raw state satisfies the flat network relation.
- `crowRegression_responseTransform_entry`: compiled elimination returns the exact bus response.
- `crowRegression_wrongRingIndex_ne_response`: the internal-ring coordinate differs exactly.
- `crowResponse_ne_isolatedRingTransferProduct`: the response is not the isolated-ring product.

## iii. Table of contents

- A. Exact two-ring fixture
- B. Primitive component equations
- C. Raw flat-network witness
- D. Compiled response and negative controls

## iv. References

The CROW terminology and topology follow A. Yariv, Y. Xu, R. K. Lee, and A. Scherer,
*Optics Letters* 24(11), 711--713 (1999), doi:10.1364/OL.24.000711. A coupled unit-cell matrix is
given by J. E. Heebner et al., *JOSA B* 21(10), 1818--1832 (2004),
doi:10.1364/JOSAB.21.001818. Numeric parity with that matrix is deferred to slice 1B; no verdict is
claimed here. The human author must verify both citations before submission.
-/

@[expose] public section

namespace Optics

noncomputable section

namespace CROW

/-!
## A. Exact two-ring fixture
-/

/-- The exact `3-4-5` coupler used at both finite bus interfaces. -/
def crowRegressionEndCoupler : DirectionalCoupler.Parameters where
  throughAmplitude := 3 / 5
  crossAmplitude := 4 / 5

/-- The exact `5-12-13` coupler shared by the two rings. -/
def crowRegressionMiddleCoupler : DirectionalCoupler.Parameters where
  throughAmplitude := 5 / 13
  crossAmplitude := 12 / 13

/-- The zero-phase half-amplitude propagation law used on all four half-arcs. -/
def crowRegressionHalfArc : MatchedPropagation.Parameters where
  amplitudeTransmission := 1 / 2
  carrierPathPhase := 0

/-- The nonuniform exact two-ring CROW fixture. -/
def crowRegressionParameters : Parameters 2 where
  coupler interface := if interface = 1 then crowRegressionMiddleCoupler
    else crowRegressionEndCoupler
  forwardArc _ := crowRegressionHalfArc
  returnArc _ := crowRegressionHalfArc

/-- The end-coupler amplitudes obey the exact Pythagorean losslessness identity. -/
lemma crowRegression_endCoupler_pythagorean :
    crowRegressionEndCoupler.throughAmplitude ^ 2 +
      crowRegressionEndCoupler.crossAmplitude ^ 2 = 1 := by
  norm_num [crowRegressionEndCoupler]

/-- The middle-coupler amplitudes obey the exact Pythagorean losslessness identity. -/
lemma crowRegression_middleCoupler_pythagorean :
    crowRegressionMiddleCoupler.throughAmplitude ^ 2 +
      crowRegressionMiddleCoupler.crossAmplitude ^ 2 = 1 := by
  norm_num [crowRegressionMiddleCoupler]

/-- Componentwise incident values obtained by solving the primitive two-ring equations. -/
def crowRegressionIncidentValue :
    (component : Component 2) → (componentPortFamily component).Channel → ℂ
  | .coupler interface, ⟨.leftFirst, ()⟩ =>
      if interface = 0 then 1
      else if interface = 1 then -(1960 / 4717) * Complex.I
      else -(960 / 4717)
  | .coupler interface, ⟨.leftSecond, ()⟩ =>
      if interface = 0 then -(244 / 4717) * Complex.I
      else if interface = 1 then -(288 / 4717)
      else 0
  | .coupler _, ⟨.rightFirst, ()⟩ => 0
  | .coupler _, ⟨.rightSecond, ()⟩ => 0
  | .forwardArc ring, ⟨.left, ()⟩ =>
      if ring = 0 then -(3920 / 4717) * Complex.I else -(1920 / 4717)
  | .forwardArc _, ⟨.right, ()⟩ => 0
  | .returnArc ring, ⟨.left, ()⟩ =>
      if ring = 0 then -(488 / 4717) * Complex.I else -(576 / 4717)
  | .returnArc _, ⟨.right, ()⟩ => 0

/-- Componentwise outgoing values induced by the primitive scattering laws. -/
def crowRegressionOutgoingValue :
    (component : Component 2) → (componentPortFamily component).Channel → ℂ
  | .coupler _, ⟨.leftFirst, ()⟩ => 0
  | .coupler _, ⟨.leftSecond, ()⟩ => 0
  | .coupler interface, ⟨.rightFirst, ()⟩ =>
      if interface = 0 then 2635 / 4717
      else if interface = 1 then -(488 / 4717) * Complex.I
      else -(576 / 4717)
  | .coupler interface, ⟨.rightSecond, ()⟩ =>
      if interface = 0 then -(3920 / 4717) * Complex.I
      else if interface = 1 then -(1920 / 4717)
      else (768 / 4717) * Complex.I
  | .forwardArc _, ⟨.left, ()⟩ => 0
  | .forwardArc ring, ⟨.right, ()⟩ =>
      if ring = 0 then -(1960 / 4717) * Complex.I else -(960 / 4717)
  | .returnArc _, ⟨.left, ()⟩ => 0
  | .returnArc ring, ⟨.right, ()⟩ =>
      if ring = 0 then -(244 / 4717) * Complex.I else -(288 / 4717)

/-- Aggregate channels of the concrete two-ring component family. -/
abbrev CrowRegressionChannel :=
  (netlist crowRegressionParameters).Channel

/-- The aggregate incident amplitude of the exact raw solution. -/
def crowRegressionIncident : ModeAmplitude (Incident CrowRegressionChannel) :=
  WithLp.toLp 2 fun endpoint =>
    match endpoint.channel with
    | ⟨⟨component, port⟩, mode⟩ => crowRegressionIncidentValue component ⟨port, mode⟩

/-- The aggregate outgoing amplitude of the exact raw solution. -/
def crowRegressionOutgoing : ModeAmplitude (Outgoing CrowRegressionChannel) :=
  WithLp.toLp 2 fun endpoint =>
    match endpoint.channel with
    | ⟨⟨component, port⟩, mode⟩ => crowRegressionOutgoingValue component ⟨port, mode⟩

/-- The aggregate channel of a selected concrete component-local channel. -/
def crowRegressionChannel (component : Component 2)
    (channel : (componentPortFamily component).Channel) : CrowRegressionChannel :=
  (components crowRegressionParameters).componentChannelEmbedding component channel

/-- The channel at a selected concrete coupler port. -/
def crowRegressionCouplerChannel (interface : Fin 3) (port : DirectionalCoupler.Port) :
    CrowRegressionChannel :=
  crowRegressionChannel (.coupler interface) ⟨port, ()⟩

/-- The channel at a selected concrete forward half-arc port. -/
def crowRegressionForwardArcChannel (ring : Fin 2) (port : MatchedPropagation.Port) :
    CrowRegressionChannel :=
  crowRegressionChannel (.forwardArc ring) ⟨port, ()⟩

/-- The channel at a selected concrete return half-arc port. -/
def crowRegressionReturnArcChannel (ring : Fin 2) (port : MatchedPropagation.Port) :
    CrowRegressionChannel :=
  crowRegressionChannel (.returnArc ring) ⟨port, ()⟩

/-- The explicit port label underlying a concrete coupler channel. -/
@[simp]
lemma portLabelEquiv_crowRegressionCouplerChannel (interface : Fin 3)
    (port : DirectionalCoupler.Port) :
    portLabelEquiv crowRegressionParameters
        (crowRegressionCouplerChannel interface port).1 =
      .coupler interface port := by
  rfl

/-- The explicit port label underlying a concrete forward half-arc channel. -/
@[simp]
lemma portLabelEquiv_crowRegressionForwardArcChannel (ring : Fin 2)
    (port : MatchedPropagation.Port) :
    portLabelEquiv crowRegressionParameters
        (crowRegressionForwardArcChannel ring port).1 =
      .forwardArc ring port := by
  rfl

/-- The explicit port label underlying a concrete return half-arc channel. -/
@[simp]
lemma portLabelEquiv_crowRegressionReturnArcChannel (ring : Fin 2)
    (port : MatchedPropagation.Port) :
    portLabelEquiv crowRegressionParameters
        (crowRegressionReturnArcChannel ring port).1 =
      .returnArc ring port := by
  rfl

/-- The concrete flat connection family. -/
abbrev crowRegressionConnections := (netlist crowRegressionParameters).connections

/-- One connected channel in the concrete right-interface wiring stage. -/
def crowRegressionRightConnectedChannel (ring : Fin 2) (kind : Bool)
    (endpoint : PortConnection.End) : crowRegressionConnections.Channel :=
  match kind, endpoint with
  | false, .left => ⟨Sum.inl (ring, false), Sum.inl ()⟩
  | false, .right => ⟨Sum.inl (ring, false), Sum.inr ()⟩
  | true, .left => ⟨Sum.inl (ring, true), Sum.inl ()⟩
  | true, .right => ⟨Sum.inl (ring, true), Sum.inr ()⟩

/-- One connected channel in the concrete forward left-interface wiring stage. -/
def crowRegressionForwardConnectedChannel (ring : Fin 2)
    (endpoint : PortConnection.End) : crowRegressionConnections.Channel :=
  match endpoint with
  | .left => ⟨Sum.inr (Sum.inl ring), Sum.inl ()⟩
  | .right => ⟨Sum.inr (Sum.inl ring), Sum.inr ()⟩

/-- One connected channel in the concrete return left-interface wiring stage. -/
def crowRegressionReturnConnectedChannel (ring : Fin 2)
    (endpoint : PortConnection.End) : crowRegressionConnections.Channel :=
  match endpoint with
  | .left => ⟨Sum.inr (Sum.inr ring), Sum.inl ()⟩
  | .right => ⟨Sum.inr (Sum.inr ring), Sum.inr ()⟩

/-- The first endpoint of a forward right-interface link is the forward half-arc output. -/
@[simp]
lemma crowRegressionRightForward_left_embedding (ring : Fin 2) :
    crowRegressionConnections.channelEmbedding
        (crowRegressionRightConnectedChannel ring false .left) =
      crowRegressionForwardArcChannel ring .right := by
  rfl

/-- The second endpoint of a forward right-interface link is the next coupler input. -/
@[simp]
lemma crowRegressionRightForward_right_embedding (ring : Fin 2) :
    crowRegressionConnections.channelEmbedding
        (crowRegressionRightConnectedChannel ring false .right) =
      crowRegressionCouplerChannel ring.succ .leftFirst := by
  rfl

/-- The first endpoint of a return right-interface link is the next coupler output. -/
@[simp]
lemma crowRegressionRightReturn_left_embedding (ring : Fin 2) :
    crowRegressionConnections.channelEmbedding
        (crowRegressionRightConnectedChannel ring true .left) =
      crowRegressionCouplerChannel ring.succ .rightFirst := by
  rfl

/-- The second endpoint of a return right-interface link is the return half-arc input. -/
@[simp]
lemma crowRegressionRightReturn_right_embedding (ring : Fin 2) :
    crowRegressionConnections.channelEmbedding
        (crowRegressionRightConnectedChannel ring true .right) =
      crowRegressionReturnArcChannel ring .left := by
  rfl

/-- The first endpoint of a forward-stage link is the coupler's forward-ring output. -/
@[simp]
lemma crowRegressionForward_left_embedding (ring : Fin 2) :
    crowRegressionConnections.channelEmbedding
        (crowRegressionForwardConnectedChannel ring .left) =
      crowRegressionCouplerChannel ring.castSucc .rightSecond := by
  rfl

/-- The second endpoint of a forward-stage link is the forward half-arc input. -/
@[simp]
lemma crowRegressionForward_right_embedding (ring : Fin 2) :
    crowRegressionConnections.channelEmbedding
        (crowRegressionForwardConnectedChannel ring .right) =
      crowRegressionForwardArcChannel ring .left := by
  rfl

/-- The first endpoint of a return-stage link is the return half-arc output. -/
@[simp]
lemma crowRegressionReturn_left_embedding (ring : Fin 2) :
    crowRegressionConnections.channelEmbedding
        (crowRegressionReturnConnectedChannel ring .left) =
      crowRegressionReturnArcChannel ring .right := by
  rfl

/-- The second endpoint of a return-stage link is the coupler's return-ring input. -/
@[simp]
lemma crowRegressionReturn_right_embedding (ring : Fin 2) :
    crowRegressionConnections.channelEmbedding
        (crowRegressionReturnConnectedChannel ring .right) =
      crowRegressionCouplerChannel ring.castSucc .leftSecond := by
  rfl

/-- Mate routing sends a right-interface link's first end to its second end. -/
@[simp]
lemma crowRegressionRightConnectedChannel_mate_left (ring : Fin 2) (kind : Bool) :
    crowRegressionConnections.mateEquiv
        (crowRegressionRightConnectedChannel ring kind .left) =
      crowRegressionRightConnectedChannel ring kind .right := by
  cases kind <;> rfl

/-- Mate routing sends a right-interface link's second end to its first end. -/
@[simp]
lemma crowRegressionRightConnectedChannel_mate_right (ring : Fin 2) (kind : Bool) :
    crowRegressionConnections.mateEquiv
        (crowRegressionRightConnectedChannel ring kind .right) =
      crowRegressionRightConnectedChannel ring kind .left := by
  cases kind <;> rfl

/-- Mate routing sends a forward-stage link's first end to its second end. -/
@[simp]
lemma crowRegressionForwardConnectedChannel_mate_left (ring : Fin 2) :
    crowRegressionConnections.mateEquiv
        (crowRegressionForwardConnectedChannel ring .left) =
      crowRegressionForwardConnectedChannel ring .right := by
  rfl

/-- Mate routing sends a forward-stage link's second end to its first end. -/
@[simp]
lemma crowRegressionForwardConnectedChannel_mate_right (ring : Fin 2) :
    crowRegressionConnections.mateEquiv
        (crowRegressionForwardConnectedChannel ring .right) =
      crowRegressionForwardConnectedChannel ring .left := by
  rfl

/-- Mate routing sends a return-stage link's first end to its second end. -/
@[simp]
lemma crowRegressionReturnConnectedChannel_mate_left (ring : Fin 2) :
    crowRegressionConnections.mateEquiv
        (crowRegressionReturnConnectedChannel ring .left) =
      crowRegressionReturnConnectedChannel ring .right := by
  rfl

/-- Mate routing sends a return-stage link's second end to its first end. -/
@[simp]
lemma crowRegressionReturnConnectedChannel_mate_right (ring : Fin 2) :
    crowRegressionConnections.mateEquiv
        (crowRegressionReturnConnectedChannel ring .right) =
      crowRegressionReturnConnectedChannel ring .left := by
  rfl

/-- The four finite-bus ports left exposed by the concrete two-ring wiring. -/
inductive CrowRegressionExternalPort
  | leftInput
  | leftOutput
  | rightInput
  | rightOutput
  deriving DecidableEq

/-- The ambient component channel selected by one exposed finite-bus port. -/
def crowRegressionExternalAmbientChannel :
    CrowRegressionExternalPort → CrowRegressionChannel
  | .leftInput => crowRegressionCouplerChannel 0 .leftFirst
  | .leftOutput => crowRegressionCouplerChannel 0 .rightFirst
  | .rightInput => crowRegressionCouplerChannel 2 .leftSecond
  | .rightOutput => crowRegressionCouplerChannel 2 .rightSecond

/-- Each displayed finite-bus channel is absent from the concrete connection image. -/
lemma crowRegressionExternalAmbientChannel_not_connected
    (port : CrowRegressionExternalPort) :
    crowRegressionExternalAmbientChannel port ∉
      Set.range crowRegressionConnections.channelEmbedding := by
  rintro ⟨⟨connection, localChannel⟩, hChannel⟩
  rcases connection with right | forwardOrReturn
  · rcases right with ⟨ring, kind⟩
    cases kind <;> rcases localChannel with mode | mode <;> cases mode
    all_goals
      first
      | change crowRegressionConnections.channelEmbedding
            (crowRegressionRightConnectedChannel ring false .left) = _ at hChannel
        rw [crowRegressionRightForward_left_embedding] at hChannel
      | change crowRegressionConnections.channelEmbedding
            (crowRegressionRightConnectedChannel ring false .right) = _ at hChannel
        rw [crowRegressionRightForward_right_embedding] at hChannel
      | change crowRegressionConnections.channelEmbedding
            (crowRegressionRightConnectedChannel ring true .left) = _ at hChannel
        rw [crowRegressionRightReturn_left_embedding] at hChannel
      | change crowRegressionConnections.channelEmbedding
            (crowRegressionRightConnectedChannel ring true .right) = _ at hChannel
        rw [crowRegressionRightReturn_right_embedding] at hChannel
    all_goals
      have hLabel := congrArg
        (fun channel => portLabelEquiv crowRegressionParameters channel.1) hChannel
      cases port <;>
        simp [crowRegressionExternalAmbientChannel] at hLabel
  · rcases forwardOrReturn with forwardIndex | returnIndex
    · rcases localChannel with mode | mode <;> cases mode
      all_goals
        first
        | change crowRegressionConnections.channelEmbedding
              (crowRegressionForwardConnectedChannel forwardIndex .left) = _ at hChannel
          rw [crowRegressionForward_left_embedding] at hChannel
        | change crowRegressionConnections.channelEmbedding
              (crowRegressionForwardConnectedChannel forwardIndex .right) = _ at hChannel
          rw [crowRegressionForward_right_embedding] at hChannel
      all_goals
        have hLabel := congrArg
          (fun channel => portLabelEquiv crowRegressionParameters channel.1) hChannel
        cases port <;>
          simp [crowRegressionExternalAmbientChannel] at hLabel <;>
          exact forwardIndex.castSucc_ne_last (by simpa using hLabel)
    · rcases localChannel with mode | mode <;> cases mode
      all_goals
        first
        | change crowRegressionConnections.channelEmbedding
              (crowRegressionReturnConnectedChannel returnIndex .left) = _ at hChannel
          rw [crowRegressionReturn_left_embedding] at hChannel
        | change crowRegressionConnections.channelEmbedding
              (crowRegressionReturnConnectedChannel returnIndex .right) = _ at hChannel
          rw [crowRegressionReturn_right_embedding] at hChannel
      all_goals
        have hLabel := congrArg
          (fun channel => portLabelEquiv crowRegressionParameters channel.1) hChannel
        cases port <;>
          simp [crowRegressionExternalAmbientChannel] at hLabel <;>
          exact returnIndex.castSucc_ne_last (by simpa using hLabel)

/-- One typed external channel at the concrete CROW boundary. -/
def crowRegressionExternalChannel (port : CrowRegressionExternalPort) :
    crowRegressionConnections.ExternalChannel :=
  ⟨crowRegressionExternalAmbientChannel port,
    crowRegressionExternalAmbientChannel_not_connected port⟩

/-- Aggregate incident evaluation reduces to the declared componentwise table. -/
@[simp]
lemma crowRegressionIncident_component (component : Component 2)
    (channel : (componentPortFamily component).Channel) :
    crowRegressionIncident
        (Incident.mk (crowRegressionChannel component channel)) =
      crowRegressionIncidentValue component channel := by
  rfl

/-- Aggregate outgoing evaluation reduces to the declared componentwise table. -/
@[simp]
lemma crowRegressionOutgoing_component (component : Component 2)
    (channel : (componentPortFamily component).Channel) :
    crowRegressionOutgoing
        (Outgoing.mk (crowRegressionChannel component channel)) =
      crowRegressionOutgoingValue component channel := by
  rfl

/-- Incident evaluation at a named concrete coupler channel uses the exact table. -/
@[simp]
lemma crowRegressionIncident_coupler (interface : Fin 3)
    (port : DirectionalCoupler.Port) :
    crowRegressionIncident (Incident.mk (crowRegressionCouplerChannel interface port)) =
      crowRegressionIncidentValue (.coupler interface) ⟨port, ()⟩ := by
  rfl

/-- Outgoing evaluation at a named concrete coupler channel uses the exact table. -/
@[simp]
lemma crowRegressionOutgoing_coupler (interface : Fin 3)
    (port : DirectionalCoupler.Port) :
    crowRegressionOutgoing (Outgoing.mk (crowRegressionCouplerChannel interface port)) =
      crowRegressionOutgoingValue (.coupler interface) ⟨port, ()⟩ := by
  rfl

/-- Incident evaluation at a named concrete forward half-arc uses the exact table. -/
@[simp]
lemma crowRegressionIncident_forwardArc (ring : Fin 2)
    (port : MatchedPropagation.Port) :
    crowRegressionIncident (Incident.mk (crowRegressionForwardArcChannel ring port)) =
      crowRegressionIncidentValue (.forwardArc ring) ⟨port, ()⟩ := by
  rfl

/-- Outgoing evaluation at a named concrete forward half-arc uses the exact table. -/
@[simp]
lemma crowRegressionOutgoing_forwardArc (ring : Fin 2)
    (port : MatchedPropagation.Port) :
    crowRegressionOutgoing (Outgoing.mk (crowRegressionForwardArcChannel ring port)) =
      crowRegressionOutgoingValue (.forwardArc ring) ⟨port, ()⟩ := by
  rfl

/-- Incident evaluation at a named concrete return half-arc uses the exact table. -/
@[simp]
lemma crowRegressionIncident_returnArc (ring : Fin 2)
    (port : MatchedPropagation.Port) :
    crowRegressionIncident (Incident.mk (crowRegressionReturnArcChannel ring port)) =
      crowRegressionIncidentValue (.returnArc ring) ⟨port, ()⟩ := by
  rfl

/-- Outgoing evaluation at a named concrete return half-arc uses the exact table. -/
@[simp]
lemma crowRegressionOutgoing_returnArc (ring : Fin 2)
    (port : MatchedPropagation.Port) :
    crowRegressionOutgoing (Outgoing.mk (crowRegressionReturnArcChannel ring port)) =
      crowRegressionOutgoingValue (.returnArc ring) ⟨port, ()⟩ := by
  rfl

/-- The external input induced by the exact aggregate incident state. -/
def crowRegressionInput : ModeAmplitude (Incident crowRegressionConnections.ExternalChannel) :=
  crowRegressionIncident.restrictEmbedding crowRegressionConnections.externalIncidentEmbedding

/-- The external output induced by the exact aggregate outgoing state. -/
def crowRegressionOutput : ModeAmplitude (Outgoing crowRegressionConnections.ExternalChannel) :=
  crowRegressionOutgoing.restrictEmbedding crowRegressionConnections.externalOutgoingEmbedding

/-!
## B. Primitive component equations
-/

/-- The incident table restricted to one declared primitive component. -/
def crowRegressionLocalIncident (component : Component 2) :
    ModeAmplitude (Incident (componentPortFamily component).Channel) :=
  WithLp.toLp 2 fun endpoint => crowRegressionIncidentValue component endpoint.channel

/-- The outgoing table restricted to one declared primitive component. -/
def crowRegressionLocalOutgoing (component : Component 2) :
    ModeAmplitude (Outgoing (componentPortFamily component).Channel) :=
  WithLp.toLp 2 fun endpoint => crowRegressionOutgoingValue component endpoint.channel

/-- Aggregate incident restriction recovers the declared local incident table. -/
lemma crowRegressionIncident_restrict (component : Component 2) :
    crowRegressionIncident.restrictEmbedding
        (Incident.relabelEmbedding
          ((components crowRegressionParameters).componentChannelEmbedding component)) =
      crowRegressionLocalIncident component := by
  apply WithLp.ofLp_injective 2
  funext endpoint
  rfl

/-- Aggregate outgoing restriction recovers the declared local outgoing table. -/
lemma crowRegressionOutgoing_restrict (component : Component 2) :
    crowRegressionOutgoing.restrictEmbedding
        (Outgoing.relabelEmbedding
          ((components crowRegressionParameters).componentChannelEmbedding component)) =
      crowRegressionLocalOutgoing component := by
  apply WithLp.ofLp_injective 2
  funext endpoint
  rfl

/-- The declared aggregate amplitudes satisfy every primitive scattering equation directly. -/
lemma crowRegression_mem_componentBehavior :
    (crowRegressionIncident, crowRegressionOutgoing) ∈
      (netlist crowRegressionParameters).componentBehavior := by
  classical
  let componentFintype : Fintype
      (netlist crowRegressionParameters).components.Component := by
    change Fintype (Component 2)
    infer_instance
  let _ : Fintype (netlist crowRegressionParameters).components.Component :=
    componentFintype
  let localFintype
      (component : (netlist crowRegressionParameters).components.Component) :
      Fintype ((netlist crowRegressionParameters).components.portFamily component).Channel := by
    change Fintype (componentPortFamily component).Channel
    exact localChannelFintype component
  let _ : ∀ component : (netlist crowRegressionParameters).components.Component,
      Fintype ((netlist crowRegressionParameters).components.portFamily component).Channel :=
    localFintype
  apply ((netlist crowRegressionParameters).mem_componentBehavior_iff_forall_component
    crowRegressionIncident crowRegressionOutgoing).2
  intro component
  rcases component with ⟨interface⟩ | ⟨ring⟩ | ⟨ring⟩
  · change
      (crowRegressionIncident.restrictEmbedding
          (Incident.relabelEmbedding
            ((components crowRegressionParameters).componentChannelEmbedding
              (.coupler interface))),
        crowRegressionOutgoing.restrictEmbedding
          (Outgoing.relabelEmbedding
            ((components crowRegressionParameters).componentChannelEmbedding
              (.coupler interface)))) ∈
      (DirectionalCoupler.physicalScattering
        (crowRegressionParameters.coupler interface) Unit).toOrientedModeTransform.toBehavior
    rw [crowRegressionIncident_restrict, crowRegressionOutgoing_restrict,
      DirectionalCoupler.physicalScattering_realizes_physicalBehavior,
      DirectionalCoupler.mem_physicalBehavior_iff,
      DirectionalCoupler.mem_behavior_iff,
      DirectionalCoupler.mixing_toLinearMap_apply,
      DirectionalCoupler.mixing_toLinearMap_apply]
    apply WithLp.ofLp_injective 2
    funext endpoint
    rcases endpoint with endpoint | endpoint <;>
      rcases endpoint with ⟨channel⟩ <;>
      rcases channel with mode | mode <;> cases mode <;>
      fin_cases interface <;>
      norm_num [crowRegressionLocalIncident, crowRegressionLocalOutgoing,
        crowRegressionIncidentValue, crowRegressionOutgoingValue,
        crowRegressionParameters, crowRegressionEndCoupler,
        crowRegressionMiddleCoupler, DirectionalCoupler.crossCoefficient,
        DirectionalCoupler.incidentChannelEquiv,
        DirectionalCoupler.outgoingChannelEquiv, DirectionalCoupler.channelEquiv,
        ModeAmplitude.directSum, ModeAmplitude.reindex_apply,
        ModeAmplitude.restrictInl, ModeAmplitude.restrictInr] <;>
      apply Complex.ext <;>
      norm_num [crowRegressionIncidentValue, crowRegressionOutgoingValue]
  · change
      (crowRegressionIncident.restrictEmbedding
          (Incident.relabelEmbedding
            ((components crowRegressionParameters).componentChannelEmbedding
              (.forwardArc ring))),
        crowRegressionOutgoing.restrictEmbedding
          (Outgoing.relabelEmbedding
            ((components crowRegressionParameters).componentChannelEmbedding
              (.forwardArc ring)))) ∈
      (MatchedPropagation.physicalScattering
        (crowRegressionParameters.forwardArc ring) Unit).toOrientedModeTransform.toBehavior
    rw [crowRegressionIncident_restrict, crowRegressionOutgoing_restrict,
      MatchedPropagation.physicalScattering_realizes_physicalBehavior,
      MatchedPropagation.mem_physicalBehavior_iff,
      MatchedPropagation.mem_behavior_iff]
    obtain rfl | rfl : ring = 0 ∨ ring = 1 := by omega
    all_goals
      apply WithLp.ofLp_injective 2
      funext endpoint
      rcases endpoint with endpoint | endpoint <;>
        rcases endpoint with ⟨mode⟩ <;> cases mode <;>
        norm_num [crowRegressionLocalIncident, crowRegressionLocalOutgoing,
          crowRegressionIncidentValue, crowRegressionOutgoingValue,
          crowRegressionParameters, crowRegressionHalfArc,
          MatchedPropagation.transmissionCoefficient,
          MatchedPropagation.carrierPhaseFactor,
          MatchedPropagation.incidentChannelEquiv,
          MatchedPropagation.outgoingChannelEquiv, MatchedPropagation.channelEquiv,
          ModeAmplitude.directSum,
          ModeAmplitude.reindex_apply] <;>
        apply Complex.ext <;>
        norm_num [crowRegressionIncidentValue, crowRegressionOutgoingValue]
  · change
      (crowRegressionIncident.restrictEmbedding
          (Incident.relabelEmbedding
            ((components crowRegressionParameters).componentChannelEmbedding
              (.returnArc ring))),
        crowRegressionOutgoing.restrictEmbedding
          (Outgoing.relabelEmbedding
            ((components crowRegressionParameters).componentChannelEmbedding
              (.returnArc ring)))) ∈
      (MatchedPropagation.physicalScattering
        (crowRegressionParameters.returnArc ring) Unit).toOrientedModeTransform.toBehavior
    rw [crowRegressionIncident_restrict, crowRegressionOutgoing_restrict,
      MatchedPropagation.physicalScattering_realizes_physicalBehavior,
      MatchedPropagation.mem_physicalBehavior_iff,
      MatchedPropagation.mem_behavior_iff]
    obtain rfl | rfl : ring = 0 ∨ ring = 1 := by omega
    all_goals
      apply WithLp.ofLp_injective 2
      funext endpoint
      rcases endpoint with endpoint | endpoint <;>
        rcases endpoint with ⟨mode⟩ <;> cases mode <;>
        norm_num [crowRegressionLocalIncident, crowRegressionLocalOutgoing,
          crowRegressionIncidentValue, crowRegressionOutgoingValue,
          crowRegressionParameters, crowRegressionHalfArc,
          MatchedPropagation.transmissionCoefficient,
          MatchedPropagation.carrierPhaseFactor,
          MatchedPropagation.incidentChannelEquiv,
          MatchedPropagation.outgoingChannelEquiv, MatchedPropagation.channelEquiv,
          ModeAmplitude.directSum,
          ModeAmplitude.reindex_apply] <;>
        apply Complex.ext <;>
        norm_num [crowRegressionIncidentValue, crowRegressionOutgoingValue]

/-- A global scattering equation exposes all four primitive equations at one fixture coupler. -/
lemma crowRegression_coupler_equations (interface : Fin 3)
    (incident : ModeAmplitude (netlist crowRegressionParameters).IncidentIndex)
    (outgoing : ModeAmplitude (netlist crowRegressionParameters).OutgoingIndex)
    (hScattering : outgoing =
      (netlist crowRegressionParameters).scatteringTransform.toLinearMap incident) :
    outgoing (Outgoing.mk (crowRegressionCouplerChannel interface .rightFirst)) =
        (crowRegressionParameters.coupler interface).throughAmplitude *
            incident (Incident.mk (crowRegressionCouplerChannel interface .leftFirst)) +
          DirectionalCoupler.crossCoefficient
              (crowRegressionParameters.coupler interface) *
            incident (Incident.mk (crowRegressionCouplerChannel interface .leftSecond)) ∧
      outgoing (Outgoing.mk (crowRegressionCouplerChannel interface .rightSecond)) =
        DirectionalCoupler.crossCoefficient
              (crowRegressionParameters.coupler interface) *
            incident (Incident.mk (crowRegressionCouplerChannel interface .leftFirst)) +
          (crowRegressionParameters.coupler interface).throughAmplitude *
            incident (Incident.mk (crowRegressionCouplerChannel interface .leftSecond)) ∧
      outgoing (Outgoing.mk (crowRegressionCouplerChannel interface .leftFirst)) =
        (crowRegressionParameters.coupler interface).throughAmplitude *
            incident (Incident.mk (crowRegressionCouplerChannel interface .rightFirst)) +
          DirectionalCoupler.crossCoefficient
              (crowRegressionParameters.coupler interface) *
            incident (Incident.mk (crowRegressionCouplerChannel interface .rightSecond)) ∧
      outgoing (Outgoing.mk (crowRegressionCouplerChannel interface .leftSecond)) =
        DirectionalCoupler.crossCoefficient
              (crowRegressionParameters.coupler interface) *
            incident (Incident.mk (crowRegressionCouplerChannel interface .rightFirst)) +
          (crowRegressionParameters.coupler interface).throughAmplitude *
            incident (Incident.mk (crowRegressionCouplerChannel interface .rightSecond)) := by
  classical
  let componentFintype : Fintype
      (netlist crowRegressionParameters).components.Component := by
    change Fintype (Component 2)
    infer_instance
  let _ : Fintype (netlist crowRegressionParameters).components.Component :=
    componentFintype
  let localFintype
      (component : (netlist crowRegressionParameters).components.Component) :
      Fintype ((netlist crowRegressionParameters).components.portFamily component).Channel := by
    change Fintype (componentPortFamily component).Channel
    exact localChannelFintype component
  let _ : ∀ component : (netlist crowRegressionParameters).components.Component,
      Fintype ((netlist crowRegressionParameters).components.portFamily component).Channel :=
    localFintype
  have hMember : (incident, outgoing) ∈
      (netlist crowRegressionParameters).componentBehavior :=
    ((netlist crowRegressionParameters).mem_componentBehavior_iff incident outgoing).mpr
      hScattering
  have hLocal :=
    ((netlist crowRegressionParameters).mem_componentBehavior_iff_forall_component
      incident outgoing).mp hMember (.coupler interface)
  change
    (incident.restrictEmbedding
          (Incident.relabelEmbedding
            ((components crowRegressionParameters).componentChannelEmbedding
              (.coupler interface))),
      outgoing.restrictEmbedding
          (Outgoing.relabelEmbedding
            ((components crowRegressionParameters).componentChannelEmbedding
              (.coupler interface)))) ∈
        (DirectionalCoupler.physicalScattering
          (crowRegressionParameters.coupler interface) Unit).toOrientedModeTransform.toBehavior
    at hLocal
  rw [DirectionalCoupler.physicalScattering_realizes_physicalBehavior] at hLocal
  have hRaw :=
    (DirectionalCoupler.mem_physicalBehavior_iff
      (crowRegressionParameters.coupler interface) _ _).mp hLocal
  rw [DirectionalCoupler.mem_behavior_iff,
    DirectionalCoupler.mixing_toLinearMap_apply,
    DirectionalCoupler.mixing_toLinearMap_apply] at hRaw
  have hRightFirst := congrArg
    (fun amplitude => amplitude (Sum.inr (Outgoing.mk (Sum.inl ())))) hRaw
  have hRightSecond := congrArg
    (fun amplitude => amplitude (Sum.inr (Outgoing.mk (Sum.inr ())))) hRaw
  have hLeftFirst := congrArg
    (fun amplitude => amplitude (Sum.inl (Outgoing.mk (Sum.inl ())))) hRaw
  have hLeftSecond := congrArg
    (fun amplitude => amplitude (Sum.inl (Outgoing.mk (Sum.inr ())))) hRaw
  change _ = _ at hRightFirst hRightSecond hLeftFirst hLeftSecond
  exact ⟨hRightFirst, hRightSecond, hLeftFirst, hLeftSecond⟩

/-- A global scattering equation exposes both primitive equations on one forward half-arc. -/
lemma crowRegression_forwardArc_equations (ring : Fin 2)
    (incident : ModeAmplitude (netlist crowRegressionParameters).IncidentIndex)
    (outgoing : ModeAmplitude (netlist crowRegressionParameters).OutgoingIndex)
    (hScattering : outgoing =
      (netlist crowRegressionParameters).scatteringTransform.toLinearMap incident) :
    outgoing (Outgoing.mk (crowRegressionForwardArcChannel ring .right)) =
        MatchedPropagation.transmissionCoefficient
            (crowRegressionParameters.forwardArc ring) *
          incident (Incident.mk (crowRegressionForwardArcChannel ring .left)) ∧
      outgoing (Outgoing.mk (crowRegressionForwardArcChannel ring .left)) =
        MatchedPropagation.transmissionCoefficient
            (crowRegressionParameters.forwardArc ring) *
          incident (Incident.mk (crowRegressionForwardArcChannel ring .right)) := by
  classical
  let componentFintype : Fintype
      (netlist crowRegressionParameters).components.Component := by
    change Fintype (Component 2)
    infer_instance
  let _ : Fintype (netlist crowRegressionParameters).components.Component :=
    componentFintype
  let localFintype
      (component : (netlist crowRegressionParameters).components.Component) :
      Fintype ((netlist crowRegressionParameters).components.portFamily component).Channel := by
    change Fintype (componentPortFamily component).Channel
    exact localChannelFintype component
  let _ : ∀ component : (netlist crowRegressionParameters).components.Component,
      Fintype ((netlist crowRegressionParameters).components.portFamily component).Channel :=
    localFintype
  have hMember : (incident, outgoing) ∈
      (netlist crowRegressionParameters).componentBehavior :=
    ((netlist crowRegressionParameters).mem_componentBehavior_iff incident outgoing).mpr
      hScattering
  have hLocal :=
    ((netlist crowRegressionParameters).mem_componentBehavior_iff_forall_component
      incident outgoing).mp hMember (.forwardArc ring)
  change
    (incident.restrictEmbedding
          (Incident.relabelEmbedding
            ((components crowRegressionParameters).componentChannelEmbedding
              (.forwardArc ring))),
      outgoing.restrictEmbedding
          (Outgoing.relabelEmbedding
            ((components crowRegressionParameters).componentChannelEmbedding
              (.forwardArc ring)))) ∈
        (MatchedPropagation.physicalScattering
          (crowRegressionParameters.forwardArc ring) Unit).toOrientedModeTransform.toBehavior
    at hLocal
  rw [MatchedPropagation.physicalScattering_realizes_physicalBehavior] at hLocal
  have hRaw :=
    (MatchedPropagation.mem_physicalBehavior_iff
      (crowRegressionParameters.forwardArc ring) _ _).mp hLocal
  rw [MatchedPropagation.mem_behavior_iff] at hRaw
  have hRight := congrArg
    (fun amplitude => amplitude (Sum.inr (Outgoing.mk ()))) hRaw
  have hLeft := congrArg
    (fun amplitude => amplitude (Sum.inl (Outgoing.mk ()))) hRaw
  change _ = _ at hRight hLeft
  exact ⟨hRight, hLeft⟩

/-- A global scattering equation exposes both primitive equations on one return half-arc. -/
lemma crowRegression_returnArc_equations (ring : Fin 2)
    (incident : ModeAmplitude (netlist crowRegressionParameters).IncidentIndex)
    (outgoing : ModeAmplitude (netlist crowRegressionParameters).OutgoingIndex)
    (hScattering : outgoing =
      (netlist crowRegressionParameters).scatteringTransform.toLinearMap incident) :
    outgoing (Outgoing.mk (crowRegressionReturnArcChannel ring .right)) =
        MatchedPropagation.transmissionCoefficient
            (crowRegressionParameters.returnArc ring) *
          incident (Incident.mk (crowRegressionReturnArcChannel ring .left)) ∧
      outgoing (Outgoing.mk (crowRegressionReturnArcChannel ring .left)) =
        MatchedPropagation.transmissionCoefficient
            (crowRegressionParameters.returnArc ring) *
          incident (Incident.mk (crowRegressionReturnArcChannel ring .right)) := by
  classical
  let componentFintype : Fintype
      (netlist crowRegressionParameters).components.Component := by
    change Fintype (Component 2)
    infer_instance
  let _ : Fintype (netlist crowRegressionParameters).components.Component :=
    componentFintype
  let localFintype
      (component : (netlist crowRegressionParameters).components.Component) :
      Fintype ((netlist crowRegressionParameters).components.portFamily component).Channel := by
    change Fintype (componentPortFamily component).Channel
    exact localChannelFintype component
  let _ : ∀ component : (netlist crowRegressionParameters).components.Component,
      Fintype ((netlist crowRegressionParameters).components.portFamily component).Channel :=
    localFintype
  have hMember : (incident, outgoing) ∈
      (netlist crowRegressionParameters).componentBehavior :=
    ((netlist crowRegressionParameters).mem_componentBehavior_iff incident outgoing).mpr
      hScattering
  have hLocal :=
    ((netlist crowRegressionParameters).mem_componentBehavior_iff_forall_component
      incident outgoing).mp hMember (.returnArc ring)
  change
    (incident.restrictEmbedding
          (Incident.relabelEmbedding
            ((components crowRegressionParameters).componentChannelEmbedding
              (.returnArc ring))),
      outgoing.restrictEmbedding
          (Outgoing.relabelEmbedding
            ((components crowRegressionParameters).componentChannelEmbedding
              (.returnArc ring)))) ∈
        (MatchedPropagation.physicalScattering
          (crowRegressionParameters.returnArc ring) Unit).toOrientedModeTransform.toBehavior
    at hLocal
  rw [MatchedPropagation.physicalScattering_realizes_physicalBehavior] at hLocal
  have hRaw :=
    (MatchedPropagation.mem_physicalBehavior_iff
      (crowRegressionParameters.returnArc ring) _ _).mp hLocal
  rw [MatchedPropagation.mem_behavior_iff] at hRaw
  have hRight := congrArg
    (fun amplitude => amplitude (Sum.inr (Outgoing.mk ()))) hRaw
  have hLeft := congrArg
    (fun amplitude => amplitude (Sum.inl (Outgoing.mk ()))) hRaw
  change _ = _ at hRight hLeft
  exact ⟨hRight, hLeft⟩

/-- The eight homogeneous channel equations in either travel direction have only the zero state. -/
lemma crowRegression_chainCoordinates_eq_zero
    (returnEnd launchEnd launchMiddle returnMiddle launchNext outputEnd returnNext returnLink : ℂ)
    (hLaunchEnd : launchEnd = (3 / 5) * returnEnd)
    (hLaunchMiddle : launchMiddle = (1 / 2) * launchEnd)
    (hReturnMiddle :
      returnMiddle = (5 / 13) * launchMiddle - (12 / 13) * Complex.I * returnLink)
    (hLaunchNext :
      launchNext = -(12 / 13) * Complex.I * launchMiddle + (5 / 13) * returnLink)
    (hOutputEnd : outputEnd = (1 / 2) * launchNext)
    (hReturnNext : returnNext = (3 / 5) * outputEnd)
    (hReturnLink : returnLink = (1 / 2) * returnNext)
    (hReturnEnd : returnEnd = (1 / 2) * returnMiddle) :
    returnEnd = 0 ∧ launchEnd = 0 ∧ launchMiddle = 0 ∧ returnMiddle = 0 ∧
      launchNext = 0 ∧ outputEnd = 0 ∧ returnNext = 0 ∧ returnLink = 0 := by
  have hI : Complex.I * Complex.I = -(1 : ℂ) := Complex.I_mul_I
  have hLaunchMiddleScaled : (4717 : ℂ) * launchMiddle = 0 := by
    linear_combination
      2450 * hLaunchEnd + 4900 * hLaunchMiddle + 735 * hReturnMiddle -
        108 * Complex.I * hLaunchNext - 216 * Complex.I * hOutputEnd -
        360 * Complex.I * hReturnNext - 720 * Complex.I * hReturnLink +
        1470 * hReturnEnd + ((1296 / 13) * launchMiddle) * hI
  have hLaunchMiddleZero : launchMiddle = 0 :=
    (mul_eq_zero.mp hLaunchMiddleScaled).resolve_left (by norm_num)
  have hLaunchEndZero : launchEnd = 0 := by
    rw [hLaunchMiddleZero] at hLaunchMiddle
    exact (mul_eq_zero.mp hLaunchMiddle.symm).resolve_left (by norm_num)
  have hReturnEndZero : returnEnd = 0 := by
    rw [hLaunchEndZero] at hLaunchEnd
    exact (mul_eq_zero.mp hLaunchEnd.symm).resolve_left (by norm_num)
  have hReturnMiddleZero : returnMiddle = 0 := by
    rw [hReturnEndZero] at hReturnEnd
    exact (mul_eq_zero.mp hReturnEnd.symm).resolve_left (by norm_num)
  have hReturnLinkZero : returnLink = 0 := by
    rw [hReturnMiddleZero, hLaunchMiddleZero] at hReturnMiddle
    have hProduct : (-(12 / 13 : ℂ) * Complex.I) * returnLink = 0 := by
      calc
        _ = (5 / 13) * 0 - (12 / 13) * Complex.I * returnLink := by ring
        _ = 0 := hReturnMiddle.symm
    exact (mul_eq_zero.mp hProduct).resolve_left (by norm_num [Complex.I_ne_zero])
  have hLaunchNextZero : launchNext = 0 := by
    rw [hLaunchMiddleZero, hReturnLinkZero] at hLaunchNext
    simpa using hLaunchNext
  have hOutputEndZero : outputEnd = 0 := by
    rw [hLaunchNextZero, mul_zero] at hOutputEnd
    exact hOutputEnd
  have hReturnNextZero : returnNext = 0 := by
    rw [hOutputEndZero, mul_zero] at hReturnNext
    exact hReturnNext
  exact ⟨hReturnEndZero, hLaunchEndZero, hLaunchMiddleZero, hReturnMiddleZero,
    hLaunchNextZero, hOutputEndZero, hReturnNextZero, hReturnLinkZero⟩

/-!
## C. Raw flat-network witness
-/

/-- Mate routing and the restricted external input reconstruct the exact incident table. -/
lemma crowRegression_incidentAssembly :
    crowRegressionIncident =
      crowRegressionConnections.incidentAssembly
        crowRegressionOutgoing crowRegressionInput := by
  classical
  rw [crowRegressionConnections.incidentAssembly_eq_reindex_directSum]
  apply (ModeAmplitude.reindex
    crowRegressionConnections.incidentPartitionEquiv.symm).injective
  rw [ModeAmplitude.reindex_symm_reindex]
  apply WithLp.ofLp_injective 2
  funext endpoint
  rcases endpoint with connected | external
  · rcases connected with ⟨channel⟩
    rw [ModeAmplitude.reindex_apply, Equiv.symm_symm,
      crowRegressionConnections.incidentPartitionEquiv_apply_inl,
      crowRegressionConnections.incidentChannelEmbedding_apply,
      ModeAmplitude.directSum_apply_inl]
    have hRouting :
        crowRegressionConnections.idealRouting.toLinearMap
            (crowRegressionOutgoing.restrictEmbedding
              crowRegressionConnections.outgoingChannelEmbedding)
              (Incident.mk channel) =
          crowRegressionOutgoing
            (Outgoing.mk (crowRegressionConnections.channelEmbedding
              (crowRegressionConnections.mateEquiv channel))) := by
      simpa only [crowRegressionConnections.mateEquiv_apply_apply,
        ModeAmplitude.restrictEmbedding_apply,
        crowRegressionConnections.outgoingChannelEmbedding_apply] using
          crowRegressionConnections.idealRouting_apply
            (crowRegressionOutgoing.restrictEmbedding
              crowRegressionConnections.outgoingChannelEmbedding)
                (crowRegressionConnections.mateEquiv channel)
    rw [hRouting]
    rcases channel with ⟨connection, localChannel⟩
    rcases connection with right | forwardOrReturn
    · rcases right with ⟨ring, kind⟩
      cases kind <;> rcases localChannel with mode | mode <;> cases mode
      all_goals
        first
        | change crowRegressionIncident
              (Incident.mk (crowRegressionForwardArcChannel ring .right)) =
            crowRegressionOutgoing
              (Outgoing.mk (crowRegressionCouplerChannel ring.succ .leftFirst))
        | change crowRegressionIncident
              (Incident.mk (crowRegressionCouplerChannel ring.succ .leftFirst)) =
            crowRegressionOutgoing
              (Outgoing.mk (crowRegressionForwardArcChannel ring .right))
        | change crowRegressionIncident
              (Incident.mk (crowRegressionCouplerChannel ring.succ .rightFirst)) =
            crowRegressionOutgoing
              (Outgoing.mk (crowRegressionReturnArcChannel ring .left))
        | change crowRegressionIncident
              (Incident.mk (crowRegressionReturnArcChannel ring .left)) =
            crowRegressionOutgoing
              (Outgoing.mk (crowRegressionCouplerChannel ring.succ .rightFirst))
      all_goals fin_cases ring
      all_goals norm_num [crowRegressionIncidentValue,
        crowRegressionOutgoingValue]
      all_goals simp
    · rcases forwardOrReturn with forwardIndex | returnIndex
      · rcases localChannel with mode | mode <;> cases mode
        all_goals
          first
          | change crowRegressionIncident
                (Incident.mk
                  (crowRegressionCouplerChannel forwardIndex.castSucc .rightSecond)) =
              crowRegressionOutgoing
                (Outgoing.mk (crowRegressionForwardArcChannel forwardIndex .left))
          | change crowRegressionIncident
                (Incident.mk (crowRegressionForwardArcChannel forwardIndex .left)) =
              crowRegressionOutgoing
                (Outgoing.mk
                  (crowRegressionCouplerChannel forwardIndex.castSucc .rightSecond))
        all_goals fin_cases forwardIndex
        all_goals norm_num [crowRegressionIncidentValue,
          crowRegressionOutgoingValue]
      · rcases localChannel with mode | mode <;> cases mode
        all_goals
          first
          | change crowRegressionIncident
                (Incident.mk (crowRegressionReturnArcChannel returnIndex .right)) =
              crowRegressionOutgoing
                (Outgoing.mk
                  (crowRegressionCouplerChannel returnIndex.castSucc .leftSecond))
          | change crowRegressionIncident
                (Incident.mk
                  (crowRegressionCouplerChannel returnIndex.castSucc .leftSecond)) =
              crowRegressionOutgoing
                (Outgoing.mk (crowRegressionReturnArcChannel returnIndex .right))
        all_goals fin_cases returnIndex
        all_goals norm_num [crowRegressionIncidentValue,
          crowRegressionOutgoingValue]
  · rcases external with ⟨channel⟩
    simp only [ModeAmplitude.reindex_apply, Equiv.symm_symm,
      crowRegressionConnections.incidentPartitionEquiv_apply_inr,
      ModeAmplitude.directSum_apply_inr, crowRegressionInput,
      ModeAmplitude.restrictEmbedding_apply]

/-- The exact primitive state projects to a member of the flat CROW relation. -/
lemma crowRegression_mem_behavior :
    (crowRegressionInput, crowRegressionOutput) ∈
      (netlist crowRegressionParameters).behavior := by
  rw [(netlist crowRegressionParameters).mem_behavior_iff_componentBehavior]
  refine ⟨crowRegressionIncident, crowRegressionOutgoing,
    crowRegression_mem_componentBehavior, crowRegression_incidentAssembly, ?_⟩
  apply WithLp.ofLp_injective 2
  funext endpoint
  rcases endpoint with ⟨channel⟩
  rw [crowRegressionOutput, FlatNetlist.outputReadout,
    crowRegressionConnections.externalOutgoingReadout_apply,
    ModeAmplitude.restrictEmbedding_apply]

/-!
## D. Compiled response and negative controls
-/

end CROW

end

end Optics
