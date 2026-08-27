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

/-!
## C. Raw flat-network witness
-/

/-!
## D. Compiled response and negative controls
-/

end CROW

end

end Optics
