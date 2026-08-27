/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Components.DirectionalCouplerPhysical
public import Physlib.Optics.Components.MatchedPropagationPhysical
public import Physlib.Optics.Network.FlatNetlistMason
public import Physlib.Optics.Network.HierarchicalReuse

/-!
# A parameterized coupled-resonator optical waveguide example

## i. Overview

This file is an end-to-end user of the typed network API. For every natural number `ringCount`,
it assembles a sequence of `ringCount` ring resonators from existing physical-port directional
couplers and matched-propagation components. Adjacent rings share a directional coupler. Only the
unused arm of the first and last couplers supplies bus access, so this is a directly
resonator-coupled sequence rather than a sequence of rings side-coupled to one common bus.

The component family contains `ringCount + 1` couplers and two propagation half-arcs per ring.
The wiring is staged without changing its meaning: right-interface links are closed first, then
the two left-interface link families. `HierarchicalNetlist.flatten_behavior_eq` identifies this
staged relation with the flat netlist, while `PortConnectionFamily.append_assoc_transport`
identifies the two three-stage parenthesizations after the canonical dependent-boundary transport.

On a supplied proof that the finite feedback equations are well posed, `generic_spine_agrees`
applies the generic theorem spine to the whole family at once. It identifies the flat relation
with compiled elimination and Mason response, while the hierarchy equality is singular safe. No
CROW-specific eliminator or stored closed response is introduced.

This is a fixed-carrier, single-mode algebraic network. The parameters do not constitute a
physical loss model, dispersion model, fabrication-tolerance model, or thermal model. The file
makes no reciprocity, time-reversal, reference-plane, causality, stability, measurement, material,
or electromagnetic-power claim. Coordinate power would mean normalized modal power, not
electromagnetic power before the finite, common-frequency, pairwise-integrable,
flux-orthogonal, unit-normalized Maxwell-profile bridge. No modal completeness or omitted-channel
claim is made.

## ii. Key results

- `CROW.netlist`: the flat directly coupled `ringCount`-ring network.
- `CROW.connections_assoc_transport`: canonical three-stage wiring associativity.
- `CROW.netlist_behavior_eq_staged`: hierarchical and flat relational semantics agree.
- `CROW.generic_spine_agrees`: the generic response spine on the well-posedness gate.

## iii. Table of contents

- A. Parameters and existing component family
- B. Three stages of directly coupled wiring
- C. Flat network boundary
- D. Generic theorem-spine instantiation

## iv. References

The construction is Physlib-original as an API example. The directly coupled topology follows
the meaning of CROW introduced by A. Yariv, Y. Xu, R. K. Lee, and A. Scherer, "Coupled-resonator
optical waveguide: a proposal and analysis," *Optics Letters* 24(11), 711--713 (1999),
doi:10.1364/OL.24.000711. The human author must verify this citation before submission.
-/

@[expose] public section

namespace Optics

noncomputable section

namespace CROW

/-!
## A. Parameters and existing component family
-/

/-- Component parameters for a directly coupled sequence of `ringCount` resonators. -/
structure Parameters (ringCount : ℕ) where
  /-- Coupler parameters at the two bus interfaces and every inter-ring interface. -/
  coupler : Fin (ringCount + 1) → DirectionalCoupler.Parameters
  /-- Propagation parameters on the forward half-arc of each ring. -/
  forwardArc : Fin ringCount → MatchedPropagation.Parameters
  /-- Propagation parameters on the return half-arc of each ring. -/
  returnArc : Fin ringCount → MatchedPropagation.Parameters

/-- Labels for the existing couplers and matched-propagation half-arcs in the sequence. -/
inductive Component (ringCount : ℕ)
  | coupler (interface : Fin (ringCount + 1))
  | forwardArc (ring : Fin ringCount)
  | returnArc (ring : Fin ringCount)
  deriving DecidableEq, Fintype

/-- The owned physical-port family selected by each CROW component label. -/
def componentPortFamily {ringCount : ℕ} : Component ringCount → PortModeFamily
  | .coupler _ => DirectionalCoupler.portFamily Unit
  | .forwardArc _ => MatchedPropagation.portFamily Unit
  | .returnArc _ => MatchedPropagation.portFamily Unit

/-- The local scattering law of every CROW component, selected from existing components. -/
def componentScattering {ringCount : ℕ} (p : Parameters ringCount) :
    (component : Component ringCount) →
      ScatteringMatrix (componentPortFamily component).Channel
  | .coupler interface =>
      DirectionalCoupler.physicalScattering (p.coupler interface) Unit
  | .forwardArc ring =>
      MatchedPropagation.physicalScattering (p.forwardArc ring) Unit
  | .returnArc ring =>
      MatchedPropagation.physicalScattering (p.returnArc ring) Unit

/-- The heterogeneous family of existing primitive components used by the CROW. -/
def components {ringCount : ℕ} (p : Parameters ringCount) : ScatteringComponentFamily where
  Component := Component ringCount
  portFamily := componentPortFamily
  scattering := componentScattering p

/-- Projected CROW component labels retain their finite enumeration. -/
noncomputable instance componentsComponentFintype {ringCount : ℕ}
    (p : Parameters ringCount) : Fintype (components p).Component := by
  change Fintype (Component ringCount)
  infer_instance

/-- Projected CROW component labels retain decidable equality. -/
noncomputable instance componentsComponentDecidableEq {ringCount : ℕ}
    (p : Parameters ringCount) : DecidableEq (components p).Component := by
  change DecidableEq (Component ringCount)
  infer_instance

/-- Every local primitive CROW channel family is finite. -/
noncomputable instance localChannelFintype {ringCount : ℕ}
    (component : Component ringCount) : Fintype (componentPortFamily component).Channel := by
  cases component
  · exact DirectionalCoupler.channelFintype
  · exact MatchedPropagation.channelFintype
  · exact MatchedPropagation.channelFintype

/-- Every local primitive CROW channel family has decidable equality. -/
noncomputable instance localChannelDecidableEq {ringCount : ℕ}
    (component : Component ringCount) :
    DecidableEq (componentPortFamily component).Channel := by
  cases component
  · exact DirectionalCoupler.channelDecidableEq
  · exact MatchedPropagation.channelDecidableEq
  · exact MatchedPropagation.channelDecidableEq

/-- Projected local CROW channel families remain finite. -/
noncomputable instance componentsLocalChannelFintype {ringCount : ℕ}
    (p : Parameters ringCount) (component : (components p).Component) :
    Fintype ((components p).portFamily component).Channel := by
  change Fintype (componentPortFamily component).Channel
  exact localChannelFintype component

/-- Projected local CROW channel families retain decidable equality. -/
noncomputable instance componentsLocalChannelDecidableEq {ringCount : ℕ}
    (p : Parameters ringCount) (component : (components p).Component) :
    DecidableEq ((components p).portFamily component).Channel := by
  change DecidableEq (componentPortFamily component).Channel
  exact localChannelDecidableEq component

/-- Aggregate primitive CROW channels are finite. -/
noncomputable instance componentsChannelFintype {ringCount : ℕ}
    (p : Parameters ringCount) :
    Fintype (components p).aggregatePortModeFamily.Channel := by
  letI : Fintype (components p).IndexedChannel := by
    change Fintype (Σ component : Component ringCount, (componentPortFamily component).Channel)
    infer_instance
  exact Fintype.ofEquiv (components p).IndexedChannel (components p).channelEquiv

/-- Aggregate primitive CROW channels have decidable equality. -/
noncomputable instance componentsChannelDecidableEq {ringCount : ℕ}
    (p : Parameters ringCount) :
    DecidableEq (components p).aggregatePortModeFamily.Channel := Classical.decEq _

/-- The aggregate port owned by a selected coupler port. -/
def couplerPort {ringCount : ℕ} (p : Parameters ringCount)
    (interface : Fin (ringCount + 1)) (port : DirectionalCoupler.Port) :
    (components p).aggregatePortModeFamily.Port :=
  ⟨Component.coupler interface, port⟩

/-- The aggregate port owned by a selected forward half-arc port. -/
def forwardArcPort {ringCount : ℕ} (p : Parameters ringCount)
    (ring : Fin ringCount) (port : MatchedPropagation.Port) :
    (components p).aggregatePortModeFamily.Port :=
  ⟨Component.forwardArc ring, port⟩

/-- The aggregate port owned by a selected return half-arc port. -/
def returnArcPort {ringCount : ℕ} (p : Parameters ringCount)
    (ring : Fin ringCount) (port : MatchedPropagation.Port) :
    (components p).aggregatePortModeFamily.Port :=
  ⟨Component.returnArc ring, port⟩

/-- A nondependent label for every owned primitive port in the CROW family. -/
inductive PortLabel (ringCount : ℕ)
  | coupler (interface : Fin (ringCount + 1)) (port : DirectionalCoupler.Port)
  | forwardArc (ring : Fin ringCount) (port : MatchedPropagation.Port)
  | returnArc (ring : Fin ringCount) (port : MatchedPropagation.Port)
  deriving DecidableEq

/-- The dependent aggregate port family is equivalent to explicit owned-port labels. -/
def portLabelEquiv {ringCount : ℕ} (p : Parameters ringCount) :
    (components p).aggregatePortModeFamily.Port ≃ PortLabel ringCount where
  toFun
    | ⟨Component.coupler interface, port⟩ => .coupler interface port
    | ⟨Component.forwardArc ring, port⟩ => .forwardArc ring port
    | ⟨Component.returnArc ring, port⟩ => .returnArc ring port
  invFun
    | .coupler interface port => couplerPort p interface port
    | .forwardArc ring port => forwardArcPort p ring port
    | .returnArc ring port => returnArcPort p ring port
  left_inv := by rintro ⟨component, port⟩; cases component <;> rfl
  right_inv := by intro port; cases port <;> rfl

@[simp]
lemma portLabelEquiv_couplerPort {ringCount : ℕ} (p : Parameters ringCount)
    (interface : Fin (ringCount + 1)) (port : DirectionalCoupler.Port) :
    portLabelEquiv p (couplerPort p interface port) = .coupler interface port := rfl

@[simp]
lemma portLabelEquiv_forwardArcPort {ringCount : ℕ} (p : Parameters ringCount)
    (ring : Fin ringCount) (port : MatchedPropagation.Port) :
    portLabelEquiv p (forwardArcPort p ring port) = .forwardArc ring port := rfl

@[simp]
lemma portLabelEquiv_returnArcPort {ringCount : ℕ} (p : Parameters ringCount)
    (ring : Fin ringCount) (port : MatchedPropagation.Port) :
    portLabelEquiv p (returnArcPort p ring port) = .returnArc ring port := rfl

/-!
## B. Three stages of directly coupled wiring
-/

/-- Right-interface links, two for each ring. -/
abbrev RightConnection (ringCount : ℕ) := Fin ringCount × Bool

/-- One selected half-arc connection at a ring's right interface. -/
def rightConnection {ringCount : ℕ} (p : Parameters ringCount) :
    RightConnection ringCount →
      PortConnection (components p).aggregatePortModeFamily
  | ⟨ring, false⟩ =>
      { left := forwardArcPort p ring MatchedPropagation.Port.right
        right := couplerPort p ring.succ DirectionalCoupler.Port.leftFirst
        left_ne_right := by intro h; cases h
        modeEquiv := Equiv.refl Unit }
  | ⟨ring, true⟩ =>
      { left := couplerPort p ring.succ DirectionalCoupler.Port.rightFirst
        right := returnArcPort p ring MatchedPropagation.Port.left
        left_ne_right := by intro h; cases h
        modeEquiv := Equiv.refl Unit }

/-- Links from both half-arcs to the coupler at the right interface of each ring. -/
def rightConnections {ringCount : ℕ} (p : Parameters ringCount) :
    PortConnectionFamily (components p).aggregatePortModeFamily
      (RightConnection ringCount) where
  connection := rightConnection p
  endpointPort_injective := by
    rintro ⟨⟨firstRing, firstKind⟩, firstEnd⟩
      ⟨⟨secondRing, secondKind⟩, secondEnd⟩ hPort
    cases firstKind <;> cases firstEnd <;>
      cases secondKind <;> cases secondEnd
    all_goals
      have hLabel := congrArg (portLabelEquiv p) hPort
      simp only [rightConnection, PortConnection.endpointPort] at hLabel
      simp_all

/-- A coupler's forward ring port is not consumed by the right-interface stage. -/
lemma coupler_rightSecond_not_rightConnected {ringCount : ℕ}
    (p : Parameters ringCount) (ring : Fin ringCount) :
    couplerPort p ring.castSucc DirectionalCoupler.Port.rightSecond ∉
      Set.range (rightConnections p).endpointEmbedding := by
  rintro ⟨⟨⟨otherRing, kind⟩, endpoint⟩, hPort⟩
  cases kind <;> cases endpoint <;>
    have hLabel := congrArg (portLabelEquiv p) hPort <;>
      simp [PortConnectionFamily.endpointEmbedding, PortConnectionFamily.endpointPort,
        rightConnections, rightConnection, PortConnection.endpointPort] at hLabel

/-- A forward half-arc's left port is not consumed by the right-interface stage. -/
lemma forwardArc_left_not_rightConnected {ringCount : ℕ}
    (p : Parameters ringCount) (ring : Fin ringCount) :
    forwardArcPort p ring MatchedPropagation.Port.left ∉
      Set.range (rightConnections p).endpointEmbedding := by
  rintro ⟨⟨⟨otherRing, kind⟩, endpoint⟩, hPort⟩
  cases kind <;> cases endpoint <;>
    have hLabel := congrArg (portLabelEquiv p) hPort <;>
      simp [PortConnectionFamily.endpointEmbedding, PortConnectionFamily.endpointPort,
        rightConnections, rightConnection, PortConnection.endpointPort] at hLabel

/-- A return half-arc's right port is not consumed by the right-interface stage. -/
lemma returnArc_right_not_rightConnected {ringCount : ℕ}
    (p : Parameters ringCount) (ring : Fin ringCount) :
    returnArcPort p ring MatchedPropagation.Port.right ∉
      Set.range (rightConnections p).endpointEmbedding := by
  rintro ⟨⟨⟨otherRing, kind⟩, endpoint⟩, hPort⟩
  cases kind <;> cases endpoint <;>
    have hLabel := congrArg (portLabelEquiv p) hPort <;>
      simp [PortConnectionFamily.endpointEmbedding, PortConnectionFamily.endpointPort,
        rightConnections, rightConnection, PortConnection.endpointPort] at hLabel

/-- A coupler's return ring port is not consumed by the right-interface stage. -/
lemma coupler_leftSecond_not_rightConnected {ringCount : ℕ}
    (p : Parameters ringCount) (ring : Fin ringCount) :
    couplerPort p ring.castSucc DirectionalCoupler.Port.leftSecond ∉
      Set.range (rightConnections p).endpointEmbedding := by
  rintro ⟨⟨⟨otherRing, kind⟩, endpoint⟩, hPort⟩
  cases kind <;> cases endpoint <;>
    have hLabel := congrArg (portLabelEquiv p) hPort <;>
      simp [PortConnectionFamily.endpointEmbedding, PortConnectionFamily.endpointPort,
        rightConnections, rightConnection, PortConnection.endpointPort] at hLabel

/-- Forward left-interface links, one for each ring. -/
abbrev ForwardConnection (ringCount : ℕ) := Fin ringCount

/-- One forward half-arc connection on the first-stage boundary. -/
def forwardConnection {ringCount : ℕ} (p : Parameters ringCount)
    (ring : ForwardConnection ringCount) :
    PortConnection (rightConnections p).externalPortModeFamily :=
  { left := ⟨couplerPort p ring.castSucc DirectionalCoupler.Port.rightSecond,
      coupler_rightSecond_not_rightConnected p ring⟩
    right := ⟨forwardArcPort p ring MatchedPropagation.Port.left,
      forwardArc_left_not_rightConnected p ring⟩
    left_ne_right := by intro h; cases h
    modeEquiv := Equiv.refl Unit }

/-- The forward half-arcs connected on the boundary left by the right-interface stage. -/
def forwardConnections {ringCount : ℕ} (p : Parameters ringCount) :
    PortConnectionFamily (rightConnections p).externalPortModeFamily
      (ForwardConnection ringCount) where
  connection := forwardConnection p
  endpointPort_injective := by
    rintro ⟨firstRing, firstEnd⟩ ⟨secondRing, secondEnd⟩ hPort
    cases firstEnd <;> cases secondEnd
    all_goals
      have hLabel := congrArg (fun port => portLabelEquiv p port.1) hPort
      simp only [forwardConnection, PortConnection.endpointPort] at hLabel
      simp_all

/-- A return half-arc's right boundary port is not consumed by the forward stage. -/
lemma returnArc_right_not_forwardConnected {ringCount : ℕ}
    (p : Parameters ringCount) (ring : Fin ringCount) :
    (⟨returnArcPort p ring MatchedPropagation.Port.right,
        returnArc_right_not_rightConnected p ring⟩ :
      (rightConnections p).externalPortModeFamily.Port) ∉
      Set.range (forwardConnections p).endpointEmbedding := by
  rintro ⟨⟨otherRing, endpoint⟩, hPort⟩
  cases endpoint <;>
    have hLabel := congrArg (fun port => portLabelEquiv p port.1) hPort <;>
      simp [PortConnectionFamily.endpointEmbedding, PortConnectionFamily.endpointPort,
        forwardConnections, forwardConnection, PortConnection.endpointPort] at hLabel

/-- A coupler's return boundary port is not consumed by the forward stage. -/
lemma coupler_leftSecond_not_forwardConnected {ringCount : ℕ}
    (p : Parameters ringCount) (ring : Fin ringCount) :
    (⟨couplerPort p ring.castSucc DirectionalCoupler.Port.leftSecond,
        coupler_leftSecond_not_rightConnected p ring⟩ :
      (rightConnections p).externalPortModeFamily.Port) ∉
      Set.range (forwardConnections p).endpointEmbedding := by
  rintro ⟨⟨otherRing, endpoint⟩, hPort⟩
  cases endpoint <;>
    have hLabel := congrArg (fun port => portLabelEquiv p port.1) hPort <;>
      simp [PortConnectionFamily.endpointEmbedding, PortConnectionFamily.endpointPort,
        forwardConnections, forwardConnection, PortConnection.endpointPort] at hLabel

/-- Return left-interface links, one for each ring. -/
abbrev ReturnConnection (ringCount : ℕ) := Fin ringCount

/-- One return half-arc connection on the boundary left by the first two stages. -/
def returnConnection {ringCount : ℕ} (p : Parameters ringCount)
    (ring : ReturnConnection ringCount) :
    PortConnection (forwardConnections p).externalPortModeFamily :=
  { left :=
      ⟨⟨returnArcPort p ring MatchedPropagation.Port.right,
          returnArc_right_not_rightConnected p ring⟩,
        returnArc_right_not_forwardConnected p ring⟩
    right :=
      ⟨⟨couplerPort p ring.castSucc DirectionalCoupler.Port.leftSecond,
          coupler_leftSecond_not_rightConnected p ring⟩,
        coupler_leftSecond_not_forwardConnected p ring⟩
    left_ne_right := by intro h; cases h
    modeEquiv := Equiv.refl Unit }

/-- The return half-arcs connected after the right and forward stages. -/
def returnConnections {ringCount : ℕ} (p : Parameters ringCount) :
    PortConnectionFamily (forwardConnections p).externalPortModeFamily
      (ReturnConnection ringCount) where
  connection := returnConnection p
  endpointPort_injective := by
    rintro ⟨firstRing, firstEnd⟩ ⟨secondRing, secondEnd⟩ hPort
    cases firstEnd <;> cases secondEnd
    all_goals
      have hLabel := congrArg (fun port => portLabelEquiv p port.1.1) hPort
      simp only [returnConnection, PortConnection.endpointPort] at hLabel
      simp_all

/-- The right-associated three-stage connection family used by the CROW hierarchy. -/
def connections {ringCount : ℕ} (p : Parameters ringCount) :
    PortConnectionFamily (components p).aggregatePortModeFamily
      (RightConnection ringCount ⊕
        (ForwardConnection ringCount ⊕ ReturnConnection ringCount)) :=
  (rightConnections p).appendThreeRight (forwardConnections p) (returnConnections p)

/-- The left-associated presentation transports the last stage to the appended boundary. -/
def leftAssociatedConnections {ringCount : ℕ} (p : Parameters ringCount) :
    PortConnectionFamily (components p).aggregatePortModeFamily
      ((RightConnection ringCount ⊕ ForwardConnection ringCount) ⊕
        ReturnConnection ringCount) :=
  (rightConnections p).appendThreeLeft (forwardConnections p) (returnConnections p)

/-- The two parenthesizations of the three physical wiring stages agree after transport. -/
lemma connections_assoc_transport {ringCount : ℕ} (p : Parameters ringCount) :
    (leftAssociatedConnections p).reindex
        (Equiv.sumAssoc (RightConnection ringCount) (ForwardConnection ringCount)
          (ReturnConnection ringCount)) =
      connections p :=
  (rightConnections p).append_assoc_transport
    (forwardConnections p) (returnConnections p)

/-- The two-stage hierarchy grouping right links before the remaining left links. -/
def hierarchy {ringCount : ℕ} (p : Parameters ringCount) : HierarchicalNetlist where
  components := components p
  InnerConnection := RightConnection ringCount
  inner := rightConnections p
  OuterConnection := ForwardConnection ringCount ⊕ ReturnConnection ringCount
  outer := (forwardConnections p).append (returnConnections p)

/-!
## C. Flat network boundary
-/

/-- The flat directly coupled CROW netlist obtained from the three-stage hierarchy. -/
def netlist {ringCount : ℕ} (p : Parameters ringCount) : FlatNetlist :=
  (hierarchy p).flatten

/-- Every right-interface connection has a finite local single-mode channel family. -/
noncomputable instance rightLocalChannelFintype {ringCount : ℕ}
    (p : Parameters ringCount) (connection : RightConnection ringCount) :
    Fintype ((rightConnections p).connection connection).LocalChannel := by
  rcases connection with ⟨ring, kind⟩
  cases kind <;> change Fintype (Unit ⊕ Unit) <;> infer_instance

/-- Right-interface connected channels are finite. -/
noncomputable instance rightChannelFintype {ringCount : ℕ}
    (p : Parameters ringCount) : Fintype (rightConnections p).Channel := by
  infer_instance

/-- Every forward-stage connection has a finite local single-mode channel family. -/
noncomputable instance forwardLocalChannelFintype {ringCount : ℕ}
    (p : Parameters ringCount) (connection : ForwardConnection ringCount) :
    Fintype ((forwardConnections p).connection connection).LocalChannel := by
  change Fintype (Unit ⊕ Unit)
  infer_instance

/-- Forward-stage connected channels are finite. -/
noncomputable instance forwardChannelFintype {ringCount : ℕ}
    (p : Parameters ringCount) : Fintype (forwardConnections p).Channel := by
  infer_instance

/-- Every return-stage connection has a finite local single-mode channel family. -/
noncomputable instance returnLocalChannelFintype {ringCount : ℕ}
    (p : Parameters ringCount) (connection : ReturnConnection ringCount) :
    Fintype ((returnConnections p).connection connection).LocalChannel := by
  change Fintype (Unit ⊕ Unit)
  infer_instance

/-- Return-stage connected channels are finite. -/
noncomputable instance returnChannelFintype {ringCount : ℕ}
    (p : Parameters ringCount) : Fintype (returnConnections p).Channel := by
  infer_instance

/-- The outer two-stage left-interface connection family has finite channels. -/
noncomputable instance outerChannelFintype {ringCount : ℕ}
    (p : Parameters ringCount) :
    Fintype ((forwardConnections p).append (returnConnections p)).Channel :=
  Fintype.ofEquiv _
    ((forwardConnections p).appendChannelEquiv (returnConnections p)).symm

/-- The flattened CROW connection family has finite channels. -/
noncomputable instance connectedChannelFintype {ringCount : ℕ}
    (p : Parameters ringCount) : Fintype (netlist p).ConnectedChannel :=
  Fintype.ofEquiv _
    ((rightConnections p).appendChannelEquiv
      ((forwardConnections p).append (returnConnections p))).symm

/-- Aggregate CROW channels are finite. -/
noncomputable instance channelFintype {ringCount : ℕ} (p : Parameters ringCount) :
    Fintype (netlist p).Channel := componentsChannelFintype p

/-- Aggregate CROW channels have decidable equality. -/
noncomputable instance channelDecidableEq {ringCount : ℕ} (p : Parameters ringCount) :
    DecidableEq (netlist p).Channel := Classical.decEq _

/-- Connected CROW channels have decidable equality. -/
noncomputable instance connectedChannelDecidableEq {ringCount : ℕ}
    (p : Parameters ringCount) : DecidableEq (netlist p).ConnectedChannel := Classical.decEq _

/-- External CROW channels are finite. -/
noncomputable instance externalChannelFintype {ringCount : ℕ}
    (p : Parameters ringCount) : Fintype (netlist p).ExternalChannel := by
  classical
  infer_instance

/-- The hierarchy's flattened ambient channel family is finite. -/
noncomputable instance hierarchyFlattenChannelFintype {ringCount : ℕ}
    (p : Parameters ringCount) : Fintype (hierarchy p).flatten.Channel := by
  change Fintype (components p).aggregatePortModeFamily.Channel
  exact componentsChannelFintype p

/-- The hierarchy's inner netlist shares the finite aggregate primitive channels. -/
noncomputable instance hierarchyInnerChannelFintype {ringCount : ℕ}
    (p : Parameters ringCount) : Fintype (hierarchy p).innerNetlist.Channel := by
  change Fintype (components p).aggregatePortModeFamily.Channel
  exact componentsChannelFintype p

/-- The hierarchy's inner netlist has finite right-interface connected channels. -/
noncomputable instance hierarchyInnerConnectedChannelFintype {ringCount : ℕ}
    (p : Parameters ringCount) :
    Fintype (hierarchy p).innerNetlist.ConnectedChannel := by
  change Fintype (rightConnections p).Channel
  exact rightChannelFintype p

/-- The first-stage hierarchy boundary has finite channels. -/
noncomputable instance hierarchyInnerBoundaryChannelFintype {ringCount : ℕ}
    (p : Parameters ringCount) :
    Fintype (hierarchy p).inner.externalPortModeFamily.Channel :=
  Fintype.ofEquiv _ (hierarchy p).inner.boundaryChannelEquiv.symm

/-- The hierarchy's outer two-stage connection family has finite channels. -/
noncomputable instance hierarchyOuterChannelFintype {ringCount : ℕ}
    (p : Parameters ringCount) : Fintype (hierarchy p).outer.Channel := by
  change Fintype ((forwardConnections p).append (returnConnections p)).Channel
  exact outerChannelFintype p

/-!
## D. Generic theorem-spine instantiation
-/

/-- The staged hierarchical behavior of the directly coupled sequence. -/
def stagedBehavior {ringCount : ℕ} (p : Parameters ringCount) :
    LinearBehavior (netlist p).ExternalIncident (netlist p).ExternalOutgoing :=
  ((hierarchy p).outer.closeBehavior
      ((hierarchy p).innerNetlist.behavior.reindex
        (Incident.relabelEquiv (hierarchy p).inner.boundaryChannelEquiv.symm)
        (Outgoing.relabelEquiv (hierarchy p).inner.boundaryChannelEquiv.symm))).reindex
    (Incident.relabelEquiv
      ((hierarchy p).inner.appendExternalChannelEquiv (hierarchy p).outer)).symm
    (Outgoing.relabelEquiv
      ((hierarchy p).inner.appendExternalChannelEquiv (hierarchy p).outer)).symm

/-- The flat CROW relation is exactly the generic staged hierarchical relation. -/
lemma netlist_behavior_eq_staged {ringCount : ℕ} (p : Parameters ringCount) :
    (netlist p).behavior = stagedBehavior p := by
  simpa only [netlist, stagedBehavior] using (hierarchy p).flatten_behavior_eq

/-- The generic response spine and hierarchy agree for every well-posed directly coupled CROW.

The result identifies component closure, the flat relation, staged hierarchical closure, compiled
elimination, and Mason extraction by instantiating generic API lemmas. The hierarchy equality does
not need well-posedness; the compiled and Mason equalities do. No topology-specific elimination is
performed, and no topology-specific bridge is added.
-/
lemma generic_spine_agrees {ringCount : ℕ} (p : Parameters ringCount)
    (hWellPosed : (netlist p).IsWellPosed) :
    (netlist p).behavior =
        (netlist p).connections.closeBehavior (netlist p).componentBehavior ∧
      (netlist p).behavior = stagedBehavior p ∧
      (netlist p).behavior = ((netlist p).responseTransform hWellPosed).toBehavior ∧
      (netlist p).responseTransform hWellPosed = (netlist p).masonResponseTransform := by
  refine ⟨(netlist p).behavior_eq_closeBehavior, netlist_behavior_eq_staged p, ?_, ?_⟩
  · exact ((netlist p).toBehavior_responseTransform hWellPosed).symm
  · exact (netlist p).responseTransform_eq_masonResponseTransform hWellPosed

end CROW

end

end Optics
