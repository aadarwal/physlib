/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Mathematics.SignalFlowGraph.Terminated
public import Physlib.Optics.Components.DirectionalCouplerPhysical
public import Physlib.Optics.Components.MatchedPropagationPhysical
public import Physlib.Optics.Network.FlatNetlistElimination

/-!
# Double-coupler double-ring topology

## i. Overview

This file constructs the double-coupler double-ring (DCDR) as an explicit `FlatNetlist` from two
N7 directional couplers and three N7 matched-propagation paths. The six connections leave exactly
the source-side input and output channels exposed. The N7 component laws used here are the pinned
`-I * k` field-amplitude coupler law and the fixed-carrier propagation coefficient; see
`Physlib/Optics/Components/DirectionalCoupler.lean:68-76` and
`Physlib/Optics/Components/MatchedPropagation.lean:93-103`.

The published FMICS'15 DCDR graph has eight nodes and eleven branches. This file retains those
branches as an edge-indexed `TerminatedMultigraph`, whose terminal and transfer conventions are at
`Physlib/Mathematics/SignalFlowGraph/Terminated.lean:227-241`. It obtains the scalar gain matrix by
the parallel-edge sum in `Physlib/Mathematics/SignalFlowGraph/Extraction.lean:175-183`, then passes
that matrix through `ofCoefficientMatrix`, defined at the same file's lines 95-97. The forward
eight-node equations are proved from the raw N7 component-scattering and netlist-routing
equations. They are not a hand-drawn replacement for the netlist.

The complete N7 netlist is bidirectional, while the source graph records the forward boundary
coordinates only. No claim identifies the eight-node matrix with the complete `C * S` feedback
graph, whose coordinates also include the reverse direction and the propagation-component
boundaries. The source's incoherent power coefficients `k` and `1-k` are likewise not silently
identified with N7 field amplitudes; that convention bridge is separate.

This is a fixed-carrier, single-mode topology. Power means normalized modal power, not
electromagnetic power. The formal bridge requires a finite family satisfying the integrability,
flux-orthogonality, and unit-normalization predicate in
`Physlib/Optics/HarmonicFlux/ModePower.lean:91-101`; that predicate's contract records common
carrier frequency, Maxwell qualification, and aperture interpretation as external requirements
at lines 93-95. No passivity, losslessness, reciprocity, causality, time-domain behavior,
stability, pole, zero, resonance, bandwidth, or material realization is asserted here.

## ii. Key results

- `DCDR.netlist`: the explicit two-coupler, three-path N7 flat netlist.
- `DCDR.signalMultigraph`: the edge-indexed eight-node, eleven-branch forward graph.
- `DCDR.signalFlowGraph`: its gain matrix, named through `ofCoefficientMatrix`.
- `DCDR.forwardState_isNodeSolution_of_netlistEquations`: the graph equations derived from the
  complete netlist equations.

## iii. Table of contents

- A. N7 parameters and explicit flat netlist
- B. External channels and forward coordinates
- C. The edge-indexed eight-node signal-flow graph
- D. Derivation from the N7 netlist equations

## iv. References

U. Siddique, S. M. Beillahi, and S. Tahar, "On the Formal Analysis of Photonic Signal Processing
Systems", FMICS 2015, LNCS 9128, Definition 8 and Theorem 3 (p. 173). Definition 8 lists the
eight nodes, eleven branches, input node 1, and output node 8.
-/

@[expose] public section

namespace Optics

noncomputable section

namespace DCDR

/-! ## A. N7 parameters and explicit flat netlist -/

/-- The two N7 couplers and three fixed-carrier N7 propagation paths of a DCDR. -/
structure Parameters where
  /-- Parameters of the first directional coupler. -/
  firstCoupler : DirectionalCoupler.Parameters
  /-- Parameters of the second directional coupler. -/
  secondCoupler : DirectionalCoupler.Parameters
  /-- Parameters of the upper forward propagation path. -/
  upperPath : MatchedPropagation.Parameters
  /-- Parameters of the lower forward propagation path. -/
  lowerPath : MatchedPropagation.Parameters
  /-- Parameters of the feedback propagation path. -/
  feedbackPath : MatchedPropagation.Parameters

/-- The complex coefficient of the upper forward path. -/
def Parameters.upperCoefficient (p : Parameters) : ℂ :=
  MatchedPropagation.transmissionCoefficient p.upperPath

/-- The complex coefficient of the lower forward path. -/
def Parameters.lowerCoefficient (p : Parameters) : ℂ :=
  MatchedPropagation.transmissionCoefficient p.lowerPath

/-- The complex coefficient of the feedback path. -/
def Parameters.feedbackCoefficient (p : Parameters) : ℂ :=
  MatchedPropagation.transmissionCoefficient p.feedbackPath

/-- The two directional couplers and three propagation components. -/
inductive Component
  | firstCoupler
  | secondCoupler
  | upperPath
  | lowerPath
  | feedbackPath
  deriving DecidableEq

/-- DCDR component labels form a finite type. -/
instance : Fintype Component where
  elems := {Component.firstCoupler, Component.secondCoupler, Component.upperPath,
    Component.lowerPath, Component.feedbackPath}
  complete component := by cases component <;> simp

/-- The owned physical-port family of each DCDR component. -/
def componentPortFamily : Component → PortModeFamily
  | .firstCoupler => DirectionalCoupler.portFamily Unit
  | .secondCoupler => DirectionalCoupler.portFamily Unit
  | .upperPath => MatchedPropagation.portFamily Unit
  | .lowerPath => MatchedPropagation.portFamily Unit
  | .feedbackPath => MatchedPropagation.portFamily Unit

/-- The local N7 scattering matrix selected by each DCDR component. -/
def componentScattering (p : Parameters) :
    (component : Component) → ScatteringMatrix (componentPortFamily component).Channel
  | .firstCoupler => DirectionalCoupler.physicalScattering p.firstCoupler Unit
  | .secondCoupler => DirectionalCoupler.physicalScattering p.secondCoupler Unit
  | .upperPath => MatchedPropagation.physicalScattering p.upperPath Unit
  | .lowerPath => MatchedPropagation.physicalScattering p.lowerPath Unit
  | .feedbackPath => MatchedPropagation.physicalScattering p.feedbackPath Unit

/-- The five N7 components before the DCDR wiring is installed. -/
def components (p : Parameters) : ScatteringComponentFamily where
  Component := Component
  portFamily := componentPortFamily
  scattering := componentScattering p

/-- The six wires joining the two couplers and three propagation paths. -/
inductive Connection
  | firstToUpper
  | upperToSecond
  | firstToLower
  | lowerToSecond
  | secondToFeedback
  | feedbackToFirst
  deriving DecidableEq

/-- DCDR connection labels form a finite type. -/
instance : Fintype Connection where
  elems := {Connection.firstToUpper, Connection.upperToSecond,
    Connection.firstToLower, Connection.lowerToSecond,
    Connection.secondToFeedback, Connection.feedbackToFirst}
  complete connection := by cases connection <;> simp

/-- The proof-carrying DCDR connections, leaving the input and output channels external. -/
def connections (p : Parameters) :
    PortConnectionFamily (components p).aggregatePortModeFamily Connection where
  connection
    | .firstToUpper =>
        { left := ⟨Component.firstCoupler, DirectionalCoupler.Port.rightFirst⟩
          right := ⟨Component.upperPath, MatchedPropagation.Port.left⟩
          left_ne_right := by intro h; cases h
          modeEquiv := Equiv.refl Unit }
    | .upperToSecond =>
        { left := ⟨Component.upperPath, MatchedPropagation.Port.right⟩
          right := ⟨Component.secondCoupler, DirectionalCoupler.Port.leftFirst⟩
          left_ne_right := by intro h; cases h
          modeEquiv := Equiv.refl Unit }
    | .firstToLower =>
        { left := ⟨Component.firstCoupler, DirectionalCoupler.Port.rightSecond⟩
          right := ⟨Component.lowerPath, MatchedPropagation.Port.left⟩
          left_ne_right := by intro h; cases h
          modeEquiv := Equiv.refl Unit }
    | .lowerToSecond =>
        { left := ⟨Component.lowerPath, MatchedPropagation.Port.right⟩
          right := ⟨Component.secondCoupler, DirectionalCoupler.Port.leftSecond⟩
          left_ne_right := by intro h; cases h
          modeEquiv := Equiv.refl Unit }
    | .secondToFeedback =>
        { left := ⟨Component.secondCoupler, DirectionalCoupler.Port.rightSecond⟩
          right := ⟨Component.feedbackPath, MatchedPropagation.Port.left⟩
          left_ne_right := by intro h; cases h
          modeEquiv := Equiv.refl Unit }
    | .feedbackToFirst =>
        { left := ⟨Component.feedbackPath, MatchedPropagation.Port.right⟩
          right := ⟨Component.firstCoupler, DirectionalCoupler.Port.leftSecond⟩
          left_ne_right := by intro h; cases h
          modeEquiv := Equiv.refl Unit }
  endpointPort_injective := by
    rintro ⟨firstConnection, firstEnd⟩ ⟨secondConnection, secondEnd⟩ hPort
    cases firstConnection <;> cases firstEnd <;>
      cases secondConnection <;> cases secondEnd
    all_goals first | rfl | cases hPort

/-- The explicit two-coupler, three-path DCDR flat netlist. -/
def netlist (p : Parameters) : FlatNetlist where
  components := components p
  Connection := Connection
  connections := connections p

/-- Every local DCDR component channel family is finite. -/
noncomputable instance localChannelFintype (component : Component) :
    Fintype (componentPortFamily component).Channel := by
  cases component
  · exact DirectionalCoupler.channelFintype
  · exact DirectionalCoupler.channelFintype
  · exact MatchedPropagation.channelFintype
  · exact MatchedPropagation.channelFintype
  · exact MatchedPropagation.channelFintype

/-- Every local DCDR component channel family has decidable equality. -/
noncomputable instance localChannelDecidableEq (component : Component) :
    DecidableEq (componentPortFamily component).Channel := by
  cases component
  · exact DirectionalCoupler.channelDecidableEq
  · exact DirectionalCoupler.channelDecidableEq
  · exact MatchedPropagation.channelDecidableEq
  · exact MatchedPropagation.channelDecidableEq
  · exact MatchedPropagation.channelDecidableEq

/-- Projected local component channels remain finite. -/
noncomputable instance componentsLocalChannelFintype (p : Parameters)
    (component : (components p).Component) :
    Fintype ((components p).portFamily component).Channel := by
  change Fintype (componentPortFamily component).Channel
  exact localChannelFintype component

/-- Projected local component channels retain decidable equality. -/
noncomputable instance componentsLocalChannelDecidableEq (p : Parameters)
    (component : (components p).Component) :
    DecidableEq ((components p).portFamily component).Channel := by
  change DecidableEq (componentPortFamily component).Channel
  exact localChannelDecidableEq component

/-- Projected aggregate DCDR channels are finite. -/
noncomputable instance componentsChannelFintype (p : Parameters) :
    Fintype (components p).aggregatePortModeFamily.Channel := by
  letI : Fintype (components p).IndexedChannel := by
    change Fintype (Σ component : Component, (componentPortFamily component).Channel)
    infer_instance
  exact Fintype.ofEquiv (components p).IndexedChannel (components p).channelEquiv

/-- Projected aggregate DCDR channels have decidable equality. -/
noncomputable instance componentsChannelDecidableEq (p : Parameters) :
    DecidableEq (components p).aggregatePortModeFamily.Channel := Classical.decEq _

/-- Projected component labels remain finite. -/
noncomputable instance netlistComponentFintype (p : Parameters) :
    Fintype (netlist p).components.Component := by
  change Fintype Component
  infer_instance

/-- Projected component labels retain decidable equality. -/
noncomputable instance netlistComponentDecidableEq (p : Parameters) :
    DecidableEq (netlist p).components.Component := by
  change DecidableEq Component
  infer_instance

/-- Every local channel family exposed by the DCDR netlist is finite. -/
noncomputable instance netlistLocalChannelFintype (p : Parameters)
    (component : (netlist p).components.Component) :
    Fintype ((netlist p).components.portFamily component).Channel := by
  change Fintype (componentPortFamily component).Channel
  exact localChannelFintype component

/-- Every local channel family exposed by the DCDR netlist has decidable equality. -/
noncomputable instance netlistLocalChannelDecidableEq (p : Parameters)
    (component : (netlist p).components.Component) :
    DecidableEq ((netlist p).components.portFamily component).Channel := by
  change DecidableEq (componentPortFamily component).Channel
  exact localChannelDecidableEq component

/-- Aggregate DCDR channels are finite. -/
noncomputable instance channelFintype (p : Parameters) : Fintype (netlist p).Channel := by
  letI : Fintype (components p).IndexedChannel := by
    change Fintype (Σ component : Component, (componentPortFamily component).Channel)
    infer_instance
  exact Fintype.ofEquiv (components p).IndexedChannel (components p).channelEquiv

/-- Aggregate DCDR channels have decidable equality. -/
noncomputable instance channelDecidableEq (p : Parameters) :
    DecidableEq (netlist p).Channel := Classical.decEq _

/-- Each concrete DCDR connection has a finite two-ended local channel family. -/
noncomputable instance connectionLocalChannelFintype (p : Parameters)
    (connection : Connection) :
    Fintype ((connections p).connection connection).LocalChannel := by
  cases connection <;> change Fintype (Unit ⊕ Unit) <;> infer_instance

/-- Internally connected DCDR channels are finite. -/
noncomputable instance connectedChannelFintype (p : Parameters) :
    Fintype (netlist p).ConnectedChannel := by
  change Fintype (connections p).Channel
  infer_instance

/-- Internally connected DCDR channels have decidable equality. -/
noncomputable instance connectedChannelDecidableEq (p : Parameters) :
    DecidableEq (netlist p).ConnectedChannel := Classical.decEq _

/-- External DCDR channels are finite. -/
noncomputable instance externalChannelFintype (p : Parameters) :
    Fintype (netlist p).ExternalChannel :=
  (netlist p).eliminationExternalChannelFintype

/-! ## B. External channels and forward coordinates -/

/-- The aggregate channel owned by a selected first-coupler port. -/
def firstCouplerChannel (p : Parameters) (port : DirectionalCoupler.Port) :
    (netlist p).Channel :=
  ⟨⟨Component.firstCoupler, port⟩, ()⟩

/-- The aggregate channel owned by a selected second-coupler port. -/
def secondCouplerChannel (p : Parameters) (port : DirectionalCoupler.Port) :
    (netlist p).Channel :=
  ⟨⟨Component.secondCoupler, port⟩, ()⟩

/-- The aggregate channel owned by a selected upper-path port. -/
def upperPathChannel (p : Parameters) (port : MatchedPropagation.Port) :
    (netlist p).Channel :=
  ⟨⟨Component.upperPath, port⟩, ()⟩

/-- The aggregate channel owned by a selected lower-path port. -/
def lowerPathChannel (p : Parameters) (port : MatchedPropagation.Port) :
    (netlist p).Channel :=
  ⟨⟨Component.lowerPath, port⟩, ()⟩

/-- The aggregate channel owned by a selected feedback-path port. -/
def feedbackPathChannel (p : Parameters) (port : MatchedPropagation.Port) :
    (netlist p).Channel :=
  ⟨⟨Component.feedbackPath, port⟩, ()⟩

/-- The first coupler's left first port is not internally connected. -/
lemma firstCoupler_leftFirst_not_connected (p : Parameters) :
    firstCouplerChannel p DirectionalCoupler.Port.leftFirst ∉
      Set.range (netlist p).connections.channelEmbedding := by
  rintro ⟨⟨connection, channel⟩, hChannel⟩
  cases connection <;> rcases channel with mode | mode <;> cases mode
  all_goals cases hChannel

/-- The second coupler's right first port is not internally connected. -/
lemma secondCoupler_rightFirst_not_connected (p : Parameters) :
    secondCouplerChannel p DirectionalCoupler.Port.rightFirst ∉
      Set.range (netlist p).connections.channelEmbedding := by
  rintro ⟨⟨connection, channel⟩, hChannel⟩
  cases connection <;> rcases channel with mode | mode <;> cases mode
  all_goals cases hChannel

/-- The packaged source-side input channel. -/
def inputChannel (p : Parameters) : (netlist p).ExternalChannel :=
  ⟨firstCouplerChannel p DirectionalCoupler.Port.leftFirst,
    firstCoupler_leftFirst_not_connected p⟩

/-- The packaged source-side output channel. -/
def outputChannel (p : Parameters) : (netlist p).ExternalChannel :=
  ⟨secondCouplerChannel p DirectionalCoupler.Port.rightFirst,
    secondCoupler_rightFirst_not_connected p⟩

/-- The source-side input and output channels belong to different couplers. -/
lemma inputChannel_ne_outputChannel (p : Parameters) :
    inputChannel p ≠ outputChannel p := by
  intro hChannel
  have hValue := congrArg Subtype.val hChannel
  cases hValue

/-- A coherent scalar amplitude injected only at the source-side input. -/
def inputAmplitude (p : Parameters) (amplitude : ℂ) :
    ModeAmplitude (netlist p).ExternalIncident :=
  PiLp.single 2 (Incident.mk (inputChannel p)) amplitude

/-- The coherent input has its supplied value at the input channel. -/
@[simp]
lemma inputAmplitude_apply_input (p : Parameters) (amplitude : ℂ) :
    inputAmplitude p amplitude (Incident.mk (inputChannel p)) = amplitude := by
  simp [inputAmplitude]

/-- The coherent input vanishes at the source-side output channel. -/
@[simp]
lemma inputAmplitude_apply_output (p : Parameters) (amplitude : ℂ) :
    inputAmplitude p amplitude (Incident.mk (outputChannel p)) = 0 := by
  rw [inputAmplitude]
  simp [Ne.symm (inputChannel_ne_outputChannel p)]

/-! ## C. The edge-indexed eight-node signal-flow graph -/

/-- The eight forward DCDR boundary signals, indexed as source nodes one through eight. -/
abbrev Node := Fin 8

/-- The eleven source branches, indexed in the order of FMICS'15 Definition 8. -/
abbrev Edge := Fin 11

/-- The source node of each branch in the published eleven-branch order. -/
def edgeSource : Edge → Node := ![0, 2, 5, 0, 3, 4, 5, 6, 1, 1, 4]

/-- The target node of each branch in the published eleven-branch order. -/
def edgeTarget : Edge → Node := ![2, 5, 7, 3, 4, 7, 6, 1, 2, 3, 6]

/-- The coherent N7 field gains in the published eleven-branch order. -/
def edgeGain (p : Parameters) : Edge → ℂ :=
  ![p.firstCoupler.throughAmplitude,
    p.upperCoefficient,
    p.secondCoupler.throughAmplitude,
    DirectionalCoupler.crossCoefficient p.firstCoupler,
    p.lowerCoefficient,
    DirectionalCoupler.crossCoefficient p.secondCoupler,
    DirectionalCoupler.crossCoefficient p.secondCoupler,
    p.feedbackCoefficient,
    DirectionalCoupler.crossCoefficient p.firstCoupler,
    p.firstCoupler.throughAmplitude,
    p.secondCoupler.throughAmplitude]

/-- The edge-indexed eight-node, eleven-branch forward DCDR graph. -/
def signalMultigraph (p : Parameters) :
    Physlib.SignalFlowGraph.Multigraph Node Edge where
  source := edgeSource
  target := edgeTarget
  gain := edgeGain p

/-- The forward DCDR gain matrix obtained from the edge-indexed graph. -/
noncomputable def coefficientMatrix (p : Parameters) : Matrix Node Node ℂ :=
  (signalMultigraph p).toMatrix

/-- The forward DCDR graph explicitly regarded as a coefficient-matrix extraction. -/
noncomputable def signalFlowGraph (p : Parameters) : Matrix Node Node ℂ :=
  Physlib.SignalFlowGraph.ofCoefficientMatrix (coefficientMatrix p)

/-- The edge-indexed DCDR graph with source node one and output node eight. -/
def terminatedMultigraph (p : Parameters) :
    Physlib.SignalFlowGraph.TerminatedMultigraph Node Edge where
  graph := signalMultigraph p
  input := 0
  output := 7

/-- The edge-indexed graph contains exactly eleven branches. -/
lemma edge_card : Fintype.card Edge = 11 := by decide

/-- The terminated graph pins source node one and output node eight. -/
lemma terminatedMultigraph_terminals (p : Parameters) :
    (terminatedMultigraph p).input = 0 ∧ (terminatedMultigraph p).output = 7 :=
  ⟨rfl, rfl⟩

/-- The named coefficient extraction leaves the multigraph gain matrix unchanged. -/
lemma signalFlowGraph_eq_coefficientMatrix (p : Parameters) :
    signalFlowGraph p = coefficientMatrix p := rfl

/-- The displayed coefficient matrix in the published node order one through eight. -/
def displayedCoefficientMatrix (p : Parameters) : Matrix Node Node ℂ :=
  ![![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, p.feedbackCoefficient, 0],
    ![p.firstCoupler.throughAmplitude,
      DirectionalCoupler.crossCoefficient p.firstCoupler, 0, 0, 0, 0, 0, 0],
    ![DirectionalCoupler.crossCoefficient p.firstCoupler,
      p.firstCoupler.throughAmplitude, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, p.lowerCoefficient, 0, 0, 0, 0],
    ![0, 0, p.upperCoefficient, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, p.secondCoupler.throughAmplitude,
      DirectionalCoupler.crossCoefficient p.secondCoupler, 0, 0],
    ![0, 0, 0, 0, DirectionalCoupler.crossCoefficient p.secondCoupler,
      p.secondCoupler.throughAmplitude, 0, 0]]

/-- Summing the eleven retained branches gives the displayed forward coefficient matrix. -/
lemma coefficientMatrix_eq_displayed (p : Parameters) :
    coefficientMatrix p = displayedCoefficientMatrix p := by
  ext output input
  rw [coefficientMatrix, Physlib.SignalFlowGraph.Multigraph.toMatrix_apply]
  change
    (∑ e with
      (signalMultigraph p).source e = input ∧
        (signalMultigraph p).target e = output,
      (signalMultigraph p).gain e) = displayedCoefficientMatrix p output input
  rw [Finset.sum_filter]
  fin_cases output <;> fin_cases input <;>
    simp [signalMultigraph, edgeSource, edgeTarget, edgeGain,
      displayedCoefficientMatrix, Fin.sum_univ_succ]

/-! ## D. Derivation from the N7 netlist equations -/

/-- The first-coupler restriction satisfies its N7 physical behavior. -/
lemma firstCoupler_physicalBehavior_of_scatteringEquation (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident) :
    (incident.restrictEmbedding
          (Incident.relabelEmbedding
            ((components p).componentChannelEmbedding Component.firstCoupler)),
      outgoing.restrictEmbedding
          (Outgoing.relabelEmbedding
            ((components p).componentChannelEmbedding Component.firstCoupler))) ∈
        DirectionalCoupler.physicalBehavior p.firstCoupler := by
  have hMember : (incident, outgoing) ∈ (netlist p).componentBehavior :=
    ((netlist p).mem_componentBehavior_iff incident outgoing).mpr hScattering
  have hLocal :=
    ((netlist p).mem_componentBehavior_iff_forall_component incident outgoing).mp
      hMember Component.firstCoupler
  change
    (incident.restrictEmbedding
          (Incident.relabelEmbedding
            ((components p).componentChannelEmbedding Component.firstCoupler)),
      outgoing.restrictEmbedding
          (Outgoing.relabelEmbedding
            ((components p).componentChannelEmbedding Component.firstCoupler))) ∈
        ModeTransform.toBehavior
          (ScatteringMatrix.toOrientedModeTransform
            (DirectionalCoupler.physicalScattering p.firstCoupler Unit)) at hLocal
  rw [DirectionalCoupler.physicalScattering_realizes_physicalBehavior] at hLocal
  exact hLocal

/-- The second-coupler restriction satisfies its N7 physical behavior. -/
lemma secondCoupler_physicalBehavior_of_scatteringEquation (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident) :
    (incident.restrictEmbedding
          (Incident.relabelEmbedding
            ((components p).componentChannelEmbedding Component.secondCoupler)),
      outgoing.restrictEmbedding
          (Outgoing.relabelEmbedding
            ((components p).componentChannelEmbedding Component.secondCoupler))) ∈
        DirectionalCoupler.physicalBehavior p.secondCoupler := by
  have hMember : (incident, outgoing) ∈ (netlist p).componentBehavior :=
    ((netlist p).mem_componentBehavior_iff incident outgoing).mpr hScattering
  have hLocal :=
    ((netlist p).mem_componentBehavior_iff_forall_component incident outgoing).mp
      hMember Component.secondCoupler
  change
    (incident.restrictEmbedding
          (Incident.relabelEmbedding
            ((components p).componentChannelEmbedding Component.secondCoupler)),
      outgoing.restrictEmbedding
          (Outgoing.relabelEmbedding
            ((components p).componentChannelEmbedding Component.secondCoupler))) ∈
        ModeTransform.toBehavior
          (ScatteringMatrix.toOrientedModeTransform
            (DirectionalCoupler.physicalScattering p.secondCoupler Unit)) at hLocal
  rw [DirectionalCoupler.physicalScattering_realizes_physicalBehavior] at hLocal
  exact hLocal

/-- The upper-path restriction satisfies its N7 physical behavior. -/
lemma upperPath_physicalBehavior_of_scatteringEquation (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident) :
    (incident.restrictEmbedding
          (Incident.relabelEmbedding
            ((components p).componentChannelEmbedding Component.upperPath)),
      outgoing.restrictEmbedding
          (Outgoing.relabelEmbedding
            ((components p).componentChannelEmbedding Component.upperPath))) ∈
        MatchedPropagation.physicalBehavior p.upperPath := by
  have hMember : (incident, outgoing) ∈ (netlist p).componentBehavior :=
    ((netlist p).mem_componentBehavior_iff incident outgoing).mpr hScattering
  have hLocal :=
    ((netlist p).mem_componentBehavior_iff_forall_component incident outgoing).mp
      hMember Component.upperPath
  change
    (incident.restrictEmbedding
          (Incident.relabelEmbedding
            ((components p).componentChannelEmbedding Component.upperPath)),
      outgoing.restrictEmbedding
          (Outgoing.relabelEmbedding
            ((components p).componentChannelEmbedding Component.upperPath))) ∈
        ModeTransform.toBehavior
          (ScatteringMatrix.toOrientedModeTransform
            (MatchedPropagation.physicalScattering p.upperPath Unit)) at hLocal
  rw [MatchedPropagation.physicalScattering_realizes_physicalBehavior] at hLocal
  exact hLocal

/-- The lower-path restriction satisfies its N7 physical behavior. -/
lemma lowerPath_physicalBehavior_of_scatteringEquation (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident) :
    (incident.restrictEmbedding
          (Incident.relabelEmbedding
            ((components p).componentChannelEmbedding Component.lowerPath)),
      outgoing.restrictEmbedding
          (Outgoing.relabelEmbedding
            ((components p).componentChannelEmbedding Component.lowerPath))) ∈
        MatchedPropagation.physicalBehavior p.lowerPath := by
  have hMember : (incident, outgoing) ∈ (netlist p).componentBehavior :=
    ((netlist p).mem_componentBehavior_iff incident outgoing).mpr hScattering
  have hLocal :=
    ((netlist p).mem_componentBehavior_iff_forall_component incident outgoing).mp
      hMember Component.lowerPath
  change
    (incident.restrictEmbedding
          (Incident.relabelEmbedding
            ((components p).componentChannelEmbedding Component.lowerPath)),
      outgoing.restrictEmbedding
          (Outgoing.relabelEmbedding
            ((components p).componentChannelEmbedding Component.lowerPath))) ∈
        ModeTransform.toBehavior
          (ScatteringMatrix.toOrientedModeTransform
            (MatchedPropagation.physicalScattering p.lowerPath Unit)) at hLocal
  rw [MatchedPropagation.physicalScattering_realizes_physicalBehavior] at hLocal
  exact hLocal

/-- The feedback-path restriction satisfies its N7 physical behavior. -/
lemma feedbackPath_physicalBehavior_of_scatteringEquation (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident) :
    (incident.restrictEmbedding
          (Incident.relabelEmbedding
            ((components p).componentChannelEmbedding Component.feedbackPath)),
      outgoing.restrictEmbedding
          (Outgoing.relabelEmbedding
            ((components p).componentChannelEmbedding Component.feedbackPath))) ∈
        MatchedPropagation.physicalBehavior p.feedbackPath := by
  have hMember : (incident, outgoing) ∈ (netlist p).componentBehavior :=
    ((netlist p).mem_componentBehavior_iff incident outgoing).mpr hScattering
  have hLocal :=
    ((netlist p).mem_componentBehavior_iff_forall_component incident outgoing).mp
      hMember Component.feedbackPath
  change
    (incident.restrictEmbedding
          (Incident.relabelEmbedding
            ((components p).componentChannelEmbedding Component.feedbackPath)),
      outgoing.restrictEmbedding
          (Outgoing.relabelEmbedding
            ((components p).componentChannelEmbedding Component.feedbackPath))) ∈
        ModeTransform.toBehavior
          (ScatteringMatrix.toOrientedModeTransform
            (MatchedPropagation.physicalScattering p.feedbackPath Unit)) at hLocal
  rw [MatchedPropagation.physicalScattering_realizes_physicalBehavior] at hLocal
  exact hLocal

/-- The first coupler gives the forward upper-arm coordinate law. -/
lemma scatteringEquation_firstCoupler_rightFirst (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident) :
    outgoing (Outgoing.mk
        (firstCouplerChannel p DirectionalCoupler.Port.rightFirst)) =
      (p.firstCoupler.throughAmplitude : ℂ) *
          incident (Incident.mk
            (firstCouplerChannel p DirectionalCoupler.Port.leftFirst)) +
        DirectionalCoupler.crossCoefficient p.firstCoupler *
          incident (Incident.mk
            (firstCouplerChannel p DirectionalCoupler.Port.leftSecond)) := by
  have hPhysical :=
    firstCoupler_physicalBehavior_of_scatteringEquation p incident outgoing hScattering
  have hRaw :=
    (DirectionalCoupler.mem_physicalBehavior_iff p.firstCoupler _ _).mp hPhysical
  rw [DirectionalCoupler.mem_behavior_iff,
    DirectionalCoupler.mixing_toLinearMap_apply,
    DirectionalCoupler.mixing_toLinearMap_apply] at hRaw
  have hCoordinate := congrArg
    (fun amplitude => amplitude (Sum.inr (Outgoing.mk (Sum.inl ())))) hRaw
  change
    outgoing (Outgoing.mk
        (firstCouplerChannel p DirectionalCoupler.Port.rightFirst)) =
      (p.firstCoupler.throughAmplitude : ℂ) *
          incident (Incident.mk
            (firstCouplerChannel p DirectionalCoupler.Port.leftFirst)) +
        DirectionalCoupler.crossCoefficient p.firstCoupler *
          incident (Incident.mk
            (firstCouplerChannel p DirectionalCoupler.Port.leftSecond)) at hCoordinate
  exact hCoordinate

/-- The first coupler gives the forward lower-arm coordinate law. -/
lemma scatteringEquation_firstCoupler_rightSecond (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident) :
    outgoing (Outgoing.mk
        (firstCouplerChannel p DirectionalCoupler.Port.rightSecond)) =
      DirectionalCoupler.crossCoefficient p.firstCoupler *
          incident (Incident.mk
            (firstCouplerChannel p DirectionalCoupler.Port.leftFirst)) +
        (p.firstCoupler.throughAmplitude : ℂ) *
          incident (Incident.mk
            (firstCouplerChannel p DirectionalCoupler.Port.leftSecond)) := by
  have hPhysical :=
    firstCoupler_physicalBehavior_of_scatteringEquation p incident outgoing hScattering
  have hRaw :=
    (DirectionalCoupler.mem_physicalBehavior_iff p.firstCoupler _ _).mp hPhysical
  rw [DirectionalCoupler.mem_behavior_iff,
    DirectionalCoupler.mixing_toLinearMap_apply,
    DirectionalCoupler.mixing_toLinearMap_apply] at hRaw
  have hCoordinate := congrArg
    (fun amplitude => amplitude (Sum.inr (Outgoing.mk (Sum.inr ())))) hRaw
  change
    outgoing (Outgoing.mk
        (firstCouplerChannel p DirectionalCoupler.Port.rightSecond)) =
      DirectionalCoupler.crossCoefficient p.firstCoupler *
          incident (Incident.mk
            (firstCouplerChannel p DirectionalCoupler.Port.leftFirst)) +
        (p.firstCoupler.throughAmplitude : ℂ) *
          incident (Incident.mk
            (firstCouplerChannel p DirectionalCoupler.Port.leftSecond)) at hCoordinate
  exact hCoordinate

/-- The second coupler gives the forward output coordinate law. -/
lemma scatteringEquation_secondCoupler_rightFirst (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident) :
    outgoing (Outgoing.mk
        (secondCouplerChannel p DirectionalCoupler.Port.rightFirst)) =
      (p.secondCoupler.throughAmplitude : ℂ) *
          incident (Incident.mk
            (secondCouplerChannel p DirectionalCoupler.Port.leftFirst)) +
        DirectionalCoupler.crossCoefficient p.secondCoupler *
          incident (Incident.mk
            (secondCouplerChannel p DirectionalCoupler.Port.leftSecond)) := by
  have hPhysical :=
    secondCoupler_physicalBehavior_of_scatteringEquation p incident outgoing hScattering
  have hRaw :=
    (DirectionalCoupler.mem_physicalBehavior_iff p.secondCoupler _ _).mp hPhysical
  rw [DirectionalCoupler.mem_behavior_iff,
    DirectionalCoupler.mixing_toLinearMap_apply,
    DirectionalCoupler.mixing_toLinearMap_apply] at hRaw
  have hCoordinate := congrArg
    (fun amplitude => amplitude (Sum.inr (Outgoing.mk (Sum.inl ())))) hRaw
  change
    outgoing (Outgoing.mk
        (secondCouplerChannel p DirectionalCoupler.Port.rightFirst)) =
      (p.secondCoupler.throughAmplitude : ℂ) *
          incident (Incident.mk
            (secondCouplerChannel p DirectionalCoupler.Port.leftFirst)) +
        DirectionalCoupler.crossCoefficient p.secondCoupler *
          incident (Incident.mk
            (secondCouplerChannel p DirectionalCoupler.Port.leftSecond)) at hCoordinate
  exact hCoordinate

/-- The second coupler gives the forward feedback-launch coordinate law. -/
lemma scatteringEquation_secondCoupler_rightSecond (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident) :
    outgoing (Outgoing.mk
        (secondCouplerChannel p DirectionalCoupler.Port.rightSecond)) =
      DirectionalCoupler.crossCoefficient p.secondCoupler *
          incident (Incident.mk
            (secondCouplerChannel p DirectionalCoupler.Port.leftFirst)) +
        (p.secondCoupler.throughAmplitude : ℂ) *
          incident (Incident.mk
            (secondCouplerChannel p DirectionalCoupler.Port.leftSecond)) := by
  have hPhysical :=
    secondCoupler_physicalBehavior_of_scatteringEquation p incident outgoing hScattering
  have hRaw :=
    (DirectionalCoupler.mem_physicalBehavior_iff p.secondCoupler _ _).mp hPhysical
  rw [DirectionalCoupler.mem_behavior_iff,
    DirectionalCoupler.mixing_toLinearMap_apply,
    DirectionalCoupler.mixing_toLinearMap_apply] at hRaw
  have hCoordinate := congrArg
    (fun amplitude => amplitude (Sum.inr (Outgoing.mk (Sum.inr ())))) hRaw
  change
    outgoing (Outgoing.mk
        (secondCouplerChannel p DirectionalCoupler.Port.rightSecond)) =
      DirectionalCoupler.crossCoefficient p.secondCoupler *
          incident (Incident.mk
            (secondCouplerChannel p DirectionalCoupler.Port.leftFirst)) +
        (p.secondCoupler.throughAmplitude : ℂ) *
          incident (Incident.mk
            (secondCouplerChannel p DirectionalCoupler.Port.leftSecond)) at hCoordinate
  exact hCoordinate

/-- The upper N7 path gives its forward propagation coordinate law. -/
lemma scatteringEquation_upperPath_right (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident) :
    outgoing (Outgoing.mk (upperPathChannel p MatchedPropagation.Port.right)) =
      p.upperCoefficient *
        incident (Incident.mk (upperPathChannel p MatchedPropagation.Port.left)) := by
  have hPhysical :=
    upperPath_physicalBehavior_of_scatteringEquation p incident outgoing hScattering
  have hRaw :=
    (MatchedPropagation.mem_physicalBehavior_iff p.upperPath _ _).mp hPhysical
  rw [MatchedPropagation.mem_behavior_iff] at hRaw
  have hCoordinate := congrArg
    (fun amplitude => amplitude (Sum.inr (Outgoing.mk ()))) hRaw
  change
    outgoing (Outgoing.mk (upperPathChannel p MatchedPropagation.Port.right)) =
      p.upperCoefficient *
        incident (Incident.mk
          (upperPathChannel p MatchedPropagation.Port.left)) at hCoordinate
  exact hCoordinate

/-- The lower N7 path gives its forward propagation coordinate law. -/
lemma scatteringEquation_lowerPath_right (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident) :
    outgoing (Outgoing.mk (lowerPathChannel p MatchedPropagation.Port.right)) =
      p.lowerCoefficient *
        incident (Incident.mk (lowerPathChannel p MatchedPropagation.Port.left)) := by
  have hPhysical :=
    lowerPath_physicalBehavior_of_scatteringEquation p incident outgoing hScattering
  have hRaw :=
    (MatchedPropagation.mem_physicalBehavior_iff p.lowerPath _ _).mp hPhysical
  rw [MatchedPropagation.mem_behavior_iff] at hRaw
  have hCoordinate := congrArg
    (fun amplitude => amplitude (Sum.inr (Outgoing.mk ()))) hRaw
  change
    outgoing (Outgoing.mk (lowerPathChannel p MatchedPropagation.Port.right)) =
      p.lowerCoefficient *
        incident (Incident.mk
          (lowerPathChannel p MatchedPropagation.Port.left)) at hCoordinate
  exact hCoordinate

/-- The feedback N7 path gives its forward propagation coordinate law. -/
lemma scatteringEquation_feedbackPath_right (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident) :
    outgoing (Outgoing.mk (feedbackPathChannel p MatchedPropagation.Port.right)) =
      p.feedbackCoefficient *
        incident (Incident.mk (feedbackPathChannel p MatchedPropagation.Port.left)) := by
  have hPhysical :=
    feedbackPath_physicalBehavior_of_scatteringEquation p incident outgoing hScattering
  have hRaw :=
    (MatchedPropagation.mem_physicalBehavior_iff p.feedbackPath _ _).mp hPhysical
  rw [MatchedPropagation.mem_behavior_iff] at hRaw
  have hCoordinate := congrArg
    (fun amplitude => amplitude (Sum.inr (Outgoing.mk ()))) hRaw
  change
    outgoing (Outgoing.mk (feedbackPathChannel p MatchedPropagation.Port.right)) =
      p.feedbackCoefficient *
        incident (Incident.mk
          (feedbackPathChannel p MatchedPropagation.Port.left)) at hCoordinate
  exact hCoordinate

/-- Incident assembly exposes the source-side input coordinate. -/
lemma incidentAssembly_apply_input (p : Parameters)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (external : ModeAmplitude (netlist p).ExternalIncident) :
    (netlist p).connections.incidentAssembly outgoing external
        (Incident.mk
          (firstCouplerChannel p DirectionalCoupler.Port.leftFirst)) =
      external (Incident.mk (inputChannel p)) := by
  exact (netlist p).connections.incidentAssembly_apply_external
    outgoing external (inputChannel p)

/-- The upper path receives the first coupler's upper output. -/
lemma incidentAssembly_apply_upperPath_left (p : Parameters)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (external : ModeAmplitude (netlist p).ExternalIncident) :
    (netlist p).connections.incidentAssembly outgoing external
        (Incident.mk (upperPathChannel p MatchedPropagation.Port.left)) =
      outgoing (Outgoing.mk
        (firstCouplerChannel p DirectionalCoupler.Port.rightFirst)) := by
  change
    (netlist p).connections.incidentAssembly outgoing external
        (Incident.mk ((netlist p).connections.channelEmbedding
          ⟨Connection.firstToUpper, Sum.inr ()⟩)) = _
  rw [(netlist p).connections.incidentAssembly_apply_connected_channel]
  rfl

/-- The second coupler's upper input receives the upper path's output. -/
lemma incidentAssembly_apply_secondCoupler_leftFirst (p : Parameters)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (external : ModeAmplitude (netlist p).ExternalIncident) :
    (netlist p).connections.incidentAssembly outgoing external
        (Incident.mk
          (secondCouplerChannel p DirectionalCoupler.Port.leftFirst)) =
      outgoing (Outgoing.mk (upperPathChannel p MatchedPropagation.Port.right)) := by
  change
    (netlist p).connections.incidentAssembly outgoing external
        (Incident.mk ((netlist p).connections.channelEmbedding
          ⟨Connection.upperToSecond, Sum.inr ()⟩)) = _
  rw [(netlist p).connections.incidentAssembly_apply_connected_channel]
  rfl

/-- The lower path receives the first coupler's lower output. -/
lemma incidentAssembly_apply_lowerPath_left (p : Parameters)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (external : ModeAmplitude (netlist p).ExternalIncident) :
    (netlist p).connections.incidentAssembly outgoing external
        (Incident.mk (lowerPathChannel p MatchedPropagation.Port.left)) =
      outgoing (Outgoing.mk
        (firstCouplerChannel p DirectionalCoupler.Port.rightSecond)) := by
  change
    (netlist p).connections.incidentAssembly outgoing external
        (Incident.mk ((netlist p).connections.channelEmbedding
          ⟨Connection.firstToLower, Sum.inr ()⟩)) = _
  rw [(netlist p).connections.incidentAssembly_apply_connected_channel]
  rfl

/-- The second coupler's lower input receives the lower path's output. -/
lemma incidentAssembly_apply_secondCoupler_leftSecond (p : Parameters)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (external : ModeAmplitude (netlist p).ExternalIncident) :
    (netlist p).connections.incidentAssembly outgoing external
        (Incident.mk
          (secondCouplerChannel p DirectionalCoupler.Port.leftSecond)) =
      outgoing (Outgoing.mk (lowerPathChannel p MatchedPropagation.Port.right)) := by
  change
    (netlist p).connections.incidentAssembly outgoing external
        (Incident.mk ((netlist p).connections.channelEmbedding
          ⟨Connection.lowerToSecond, Sum.inr ()⟩)) = _
  rw [(netlist p).connections.incidentAssembly_apply_connected_channel]
  rfl

/-- The feedback path receives the second coupler's feedback-launch output. -/
lemma incidentAssembly_apply_feedbackPath_left (p : Parameters)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (external : ModeAmplitude (netlist p).ExternalIncident) :
    (netlist p).connections.incidentAssembly outgoing external
        (Incident.mk (feedbackPathChannel p MatchedPropagation.Port.left)) =
      outgoing (Outgoing.mk
        (secondCouplerChannel p DirectionalCoupler.Port.rightSecond)) := by
  change
    (netlist p).connections.incidentAssembly outgoing external
        (Incident.mk ((netlist p).connections.channelEmbedding
          ⟨Connection.secondToFeedback, Sum.inr ()⟩)) = _
  rw [(netlist p).connections.incidentAssembly_apply_connected_channel]
  rfl

/-- The first coupler's feedback input receives the feedback path's output. -/
lemma incidentAssembly_apply_firstCoupler_leftSecond (p : Parameters)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (external : ModeAmplitude (netlist p).ExternalIncident) :
    (netlist p).connections.incidentAssembly outgoing external
        (Incident.mk
          (firstCouplerChannel p DirectionalCoupler.Port.leftSecond)) =
      outgoing (Outgoing.mk (feedbackPathChannel p MatchedPropagation.Port.right)) := by
  change
    (netlist p).connections.incidentAssembly outgoing external
        (Incident.mk ((netlist p).connections.channelEmbedding
          ⟨Connection.feedbackToFirst, Sum.inr ()⟩)) = _
  rw [(netlist p).connections.incidentAssembly_apply_connected_channel]
  rfl

/-- The eight forward boundary coordinates extracted from a complete N7 netlist state.

The coordinates are, in order: the first-coupler input and feedback input, its two forward
outputs, the lower and upper inputs of the second coupler, its feedback output, and its external
output.
-/
def forwardState (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex) : Node → ℂ :=
  ![incident (Incident.mk
      (firstCouplerChannel p DirectionalCoupler.Port.leftFirst)),
    incident (Incident.mk
      (firstCouplerChannel p DirectionalCoupler.Port.leftSecond)),
    outgoing (Outgoing.mk
      (firstCouplerChannel p DirectionalCoupler.Port.rightFirst)),
    outgoing (Outgoing.mk
      (firstCouplerChannel p DirectionalCoupler.Port.rightSecond)),
    incident (Incident.mk
      (secondCouplerChannel p DirectionalCoupler.Port.leftSecond)),
    incident (Incident.mk
      (secondCouplerChannel p DirectionalCoupler.Port.leftFirst)),
    outgoing (Outgoing.mk
      (secondCouplerChannel p DirectionalCoupler.Port.rightSecond)),
    outgoing (Outgoing.mk
      (secondCouplerChannel p DirectionalCoupler.Port.rightFirst))]

/-- Injection at source node one and nowhere else in the forward graph. -/
def signalInput (amplitude : ℂ) : Node → ℂ :=
  ![amplitude, 0, 0, 0, 0, 0, 0, 0]

/-- The eight scalar forward equations in the published node order. -/
structure ForwardEquations (p : Parameters) (input : ℂ) (state : Node → ℂ) : Prop where
  /-- Node one is the externally supplied input. -/
  nodeOne : state 0 = input
  /-- Node two is the propagated feedback from node seven. -/
  nodeTwo : state 1 = p.feedbackCoefficient * state 6
  /-- Node three is the first coupler's upper output. -/
  nodeThree : state 2 =
    (p.firstCoupler.throughAmplitude : ℂ) * state 0 +
      DirectionalCoupler.crossCoefficient p.firstCoupler * state 1
  /-- Node four is the first coupler's lower output. -/
  nodeFour : state 3 =
    DirectionalCoupler.crossCoefficient p.firstCoupler * state 0 +
      (p.firstCoupler.throughAmplitude : ℂ) * state 1
  /-- Node five is the lower-path propagation from node four. -/
  nodeFive : state 4 = p.lowerCoefficient * state 3
  /-- Node six is the upper-path propagation from node three. -/
  nodeSix : state 5 = p.upperCoefficient * state 2
  /-- Node seven is the second coupler's feedback output. -/
  nodeSeven : state 6 =
    (p.secondCoupler.throughAmplitude : ℂ) * state 4 +
      DirectionalCoupler.crossCoefficient p.secondCoupler * state 5
  /-- Node eight is the second coupler's external output. -/
  nodeEight : state 7 =
    DirectionalCoupler.crossCoefficient p.secondCoupler * state 4 +
      (p.secondCoupler.throughAmplitude : ℂ) * state 5

/-- The displayed eight equations are exactly the node equation of the extracted graph. -/
lemma isNodeSolution_iff_forwardEquations (p : Parameters) (input : ℂ)
    (state : Node → ℂ) :
    Physlib.SignalFlowGraph.IsNodeSolution (signalFlowGraph p) (signalInput input) state ↔
      ForwardEquations p input state := by
  rw [Physlib.SignalFlowGraph.IsNodeSolution, signalFlowGraph_eq_coefficientMatrix,
    coefficientMatrix_eq_displayed]
  constructor
  · intro hState
    have h0 := congrFun hState (0 : Node)
    have h1 := congrFun hState (1 : Node)
    have h2 := congrFun hState (2 : Node)
    have h3 := congrFun hState (3 : Node)
    have h4 := congrFun hState (4 : Node)
    have h5 := congrFun hState (5 : Node)
    have h6 := congrFun hState (6 : Node)
    have h7 := congrFun hState (7 : Node)
    exact ⟨by simpa [Matrix.mulVec, displayedCoefficientMatrix, signalInput,
        Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail] using h0,
      by simpa [Matrix.mulVec, displayedCoefficientMatrix, signalInput,
        Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail] using h1,
      by simpa [Matrix.mulVec, displayedCoefficientMatrix, signalInput,
        Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail] using h2,
      by simpa [Matrix.mulVec, displayedCoefficientMatrix, signalInput,
        Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail] using h3,
      by simpa [Matrix.mulVec, displayedCoefficientMatrix, signalInput,
        Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail] using h4,
      by simpa [Matrix.mulVec, displayedCoefficientMatrix, signalInput,
        Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail] using h5,
      by simpa [Matrix.mulVec, displayedCoefficientMatrix, signalInput,
        Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail] using h6,
      by simpa [Matrix.mulVec, displayedCoefficientMatrix, signalInput,
        Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail] using h7⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
    funext node
    fin_cases node
    · simpa [Matrix.mulVec, displayedCoefficientMatrix, signalInput,
        Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail] using h0
    · simpa [Matrix.mulVec, displayedCoefficientMatrix, signalInput,
        Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail] using h1
    · simpa [Matrix.mulVec, displayedCoefficientMatrix, signalInput,
        Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail] using h2
    · simpa [Matrix.mulVec, displayedCoefficientMatrix, signalInput,
        Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail] using h3
    · simpa [Matrix.mulVec, displayedCoefficientMatrix, signalInput,
        Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail] using h4
    · simpa [Matrix.mulVec, displayedCoefficientMatrix, signalInput,
        Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail] using h5
    · simpa [Matrix.mulVec, displayedCoefficientMatrix, signalInput,
        Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail] using h6
    · simpa [Matrix.mulVec, displayedCoefficientMatrix, signalInput,
        Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail] using h7

/-- The connected upper path propagates the first coupler's upper output to the second coupler. -/
lemma upperCoordinate_of_netlistEquations (p : Parameters)
    (external : ModeAmplitude (netlist p).ExternalIncident)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident)
    (hAssembly : incident = (netlist p).connections.incidentAssembly outgoing external) :
    incident (Incident.mk
        (secondCouplerChannel p DirectionalCoupler.Port.leftFirst)) =
      p.upperCoefficient *
        outgoing (Outgoing.mk
          (firstCouplerChannel p DirectionalCoupler.Port.rightFirst)) := by
  have hUpperIn := congrArg
    (fun state => state (Incident.mk
      (upperPathChannel p MatchedPropagation.Port.left))) hAssembly
  rw [incidentAssembly_apply_upperPath_left] at hUpperIn
  have hUpperOut := scatteringEquation_upperPath_right p incident outgoing hScattering
  have hSecondUpper := congrArg
    (fun state => state (Incident.mk
      (secondCouplerChannel p DirectionalCoupler.Port.leftFirst))) hAssembly
  rw [incidentAssembly_apply_secondCoupler_leftFirst] at hSecondUpper
  calc
    _ = outgoing (Outgoing.mk
        (upperPathChannel p MatchedPropagation.Port.right)) := hSecondUpper
    _ = p.upperCoefficient *
        incident (Incident.mk
          (upperPathChannel p MatchedPropagation.Port.left)) := hUpperOut
    _ = _ := by rw [hUpperIn]

/-- The connected lower path propagates the first coupler's lower output to the second coupler. -/
lemma lowerCoordinate_of_netlistEquations (p : Parameters)
    (external : ModeAmplitude (netlist p).ExternalIncident)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident)
    (hAssembly : incident = (netlist p).connections.incidentAssembly outgoing external) :
    incident (Incident.mk
        (secondCouplerChannel p DirectionalCoupler.Port.leftSecond)) =
      p.lowerCoefficient *
        outgoing (Outgoing.mk
          (firstCouplerChannel p DirectionalCoupler.Port.rightSecond)) := by
  have hLowerIn := congrArg
    (fun state => state (Incident.mk
      (lowerPathChannel p MatchedPropagation.Port.left))) hAssembly
  rw [incidentAssembly_apply_lowerPath_left] at hLowerIn
  have hLowerOut := scatteringEquation_lowerPath_right p incident outgoing hScattering
  have hSecondLower := congrArg
    (fun state => state (Incident.mk
      (secondCouplerChannel p DirectionalCoupler.Port.leftSecond))) hAssembly
  rw [incidentAssembly_apply_secondCoupler_leftSecond] at hSecondLower
  calc
    _ = outgoing (Outgoing.mk
        (lowerPathChannel p MatchedPropagation.Port.right)) := hSecondLower
    _ = p.lowerCoefficient *
        incident (Incident.mk
          (lowerPathChannel p MatchedPropagation.Port.left)) := hLowerOut
    _ = _ := by rw [hLowerIn]

/-- The connected feedback path propagates the second coupler's launch to its return input. -/
lemma feedbackCoordinate_of_netlistEquations (p : Parameters)
    (external : ModeAmplitude (netlist p).ExternalIncident)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident)
    (hAssembly : incident = (netlist p).connections.incidentAssembly outgoing external) :
    incident (Incident.mk
        (firstCouplerChannel p DirectionalCoupler.Port.leftSecond)) =
      p.feedbackCoefficient *
        outgoing (Outgoing.mk
          (secondCouplerChannel p DirectionalCoupler.Port.rightSecond)) := by
  have hFeedbackIn := congrArg
    (fun state => state (Incident.mk
      (feedbackPathChannel p MatchedPropagation.Port.left))) hAssembly
  rw [incidentAssembly_apply_feedbackPath_left] at hFeedbackIn
  have hFeedbackOut :=
    scatteringEquation_feedbackPath_right p incident outgoing hScattering
  have hFirstFeedback := congrArg
    (fun state => state (Incident.mk
      (firstCouplerChannel p DirectionalCoupler.Port.leftSecond))) hAssembly
  rw [incidentAssembly_apply_firstCoupler_leftSecond] at hFirstFeedback
  calc
    _ = outgoing (Outgoing.mk
        (feedbackPathChannel p MatchedPropagation.Port.right)) := hFirstFeedback
    _ = p.feedbackCoefficient *
        incident (Incident.mk
          (feedbackPathChannel p MatchedPropagation.Port.left)) := hFeedbackOut
    _ = _ := by rw [hFeedbackIn]

/-- The raw component and routing equations imply the eight forward DCDR equations. -/
lemma forwardEquations_of_netlistEquations (p : Parameters)
    (external : ModeAmplitude (netlist p).ExternalIncident)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident)
    (hAssembly : incident = (netlist p).connections.incidentAssembly outgoing external) :
    ForwardEquations p (external (Incident.mk (inputChannel p)))
      (forwardState p incident outgoing) := by
  have hInput := congrArg
    (fun state => state (Incident.mk
      (firstCouplerChannel p DirectionalCoupler.Port.leftFirst))) hAssembly
  rw [incidentAssembly_apply_input] at hInput
  have hUpper := upperCoordinate_of_netlistEquations p external incident outgoing
    hScattering hAssembly
  have hLower := lowerCoordinate_of_netlistEquations p external incident outgoing
    hScattering hAssembly
  have hFeedback := feedbackCoordinate_of_netlistEquations p external incident outgoing
    hScattering hAssembly
  have hFirstUpper :=
    scatteringEquation_firstCoupler_rightFirst p incident outgoing hScattering
  have hFirstLower :=
    scatteringEquation_firstCoupler_rightSecond p incident outgoing hScattering
  have hSecondOutput :=
    scatteringEquation_secondCoupler_rightFirst p incident outgoing hScattering
  have hSecondFeedback :=
    scatteringEquation_secondCoupler_rightSecond p incident outgoing hScattering
  exact
    ⟨by simpa [forwardState] using hInput,
      by simpa [forwardState] using hFeedback,
      by simpa [forwardState] using hFirstUpper,
      by simpa [forwardState] using hFirstLower,
      by simpa [forwardState] using hLower,
      by simpa [forwardState] using hUpper,
      by simpa [forwardState, add_comm] using hSecondFeedback,
      by simpa [forwardState, add_comm] using hSecondOutput⟩

/-- Every complete N7 solution induces a solution of the extracted eight-node graph. -/
lemma forwardState_isNodeSolution_of_netlistEquations (p : Parameters)
    (external : ModeAmplitude (netlist p).ExternalIncident)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident)
    (hAssembly : incident = (netlist p).connections.incidentAssembly outgoing external) :
    Physlib.SignalFlowGraph.IsNodeSolution (signalFlowGraph p)
      (signalInput (external (Incident.mk (inputChannel p))))
      (forwardState p incident outgoing) := by
  rw [isNodeSolution_iff_forwardEquations]
  exact forwardEquations_of_netlistEquations p external incident outgoing
    hScattering hAssembly

end DCDR

end

end Optics
