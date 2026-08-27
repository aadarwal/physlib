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
  | .coupler interface, ⟨port, ()⟩ =>
      match interface.val, port with
      | 0, .leftFirst => 1
      | 0, .leftSecond => -(244 / 4717) * Complex.I
      | 1, .leftFirst => -(1960 / 4717) * Complex.I
      | 1, .leftSecond => -(288 / 4717)
      | 2, .leftFirst => -(960 / 4717)
      | _, _ => 0
  | .forwardArc ring, ⟨port, ()⟩ =>
      match ring.val, port with
      | 0, .left => -(3920 / 4717) * Complex.I
      | 1, .left => -(1920 / 4717)
      | _, _ => 0
  | .returnArc ring, ⟨port, ()⟩ =>
      match ring.val, port with
      | 0, .left => -(488 / 4717) * Complex.I
      | 1, .left => -(576 / 4717)
      | _, _ => 0

/-- Componentwise outgoing values induced by the primitive scattering laws. -/
def crowRegressionOutgoingValue :
    (component : Component 2) → (componentPortFamily component).Channel → ℂ
  | .coupler interface, ⟨port, ()⟩ =>
      match interface.val, port with
      | 0, .rightFirst => 2635 / 4717
      | 0, .rightSecond => -(3920 / 4717) * Complex.I
      | 1, .rightFirst => -(488 / 4717) * Complex.I
      | 1, .rightSecond => -(1920 / 4717)
      | 2, .rightFirst => -(576 / 4717)
      | 2, .rightSecond => (768 / 4717) * Complex.I
      | _, _ => 0
  | .forwardArc ring, ⟨port, ()⟩ =>
      match ring.val, port with
      | 0, .right => -(1960 / 4717) * Complex.I
      | 1, .right => -(960 / 4717)
      | _, _ => 0
  | .returnArc ring, ⟨port, ()⟩ =>
      match ring.val, port with
      | 0, .right => -(244 / 4717) * Complex.I
      | 1, .right => -(288 / 4717)
      | _, _ => 0

/-- Aggregate channels of the concrete two-ring component family. -/
abbrev CrowRegressionChannel :=
  (components crowRegressionParameters).aggregatePortModeFamily.Channel

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

/-- The concrete flat connection family. -/
abbrev crowRegressionConnections := (netlist crowRegressionParameters).connections

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
    apply WithLp.ofLp_injective 2
    funext endpoint
    rcases endpoint with endpoint | endpoint <;>
      rcases endpoint with ⟨mode⟩ <;> cases mode <;> fin_cases ring <;>
      norm_num [crowRegressionLocalIncident, crowRegressionLocalOutgoing,
        crowRegressionIncidentValue, crowRegressionOutgoingValue,
        crowRegressionParameters, crowRegressionHalfArc,
        MatchedPropagation.transmissionCoefficient,
        MatchedPropagation.carrierPhaseFactor, ModeAmplitude.directSum,
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
    apply WithLp.ofLp_injective 2
    funext endpoint
    rcases endpoint with endpoint | endpoint <;>
      rcases endpoint with ⟨mode⟩ <;> cases mode <;> fin_cases ring <;>
      norm_num [crowRegressionLocalIncident, crowRegressionLocalOutgoing,
        crowRegressionIncidentValue, crowRegressionOutgoingValue,
        crowRegressionParameters, crowRegressionHalfArc,
        MatchedPropagation.transmissionCoefficient,
        MatchedPropagation.carrierPhaseFactor, ModeAmplitude.directSum,
        ModeAmplitude.reindex_apply] <;>
      apply Complex.ext <;>
      norm_num [crowRegressionIncidentValue, crowRegressionOutgoingValue]

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

/-!
## D. Compiled response and negative controls
-/

end CROW

end

end Optics
