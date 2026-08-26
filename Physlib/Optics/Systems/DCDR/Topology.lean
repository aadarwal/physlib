/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Mathematics.SignalFlowGraph.Terminated
public import Physlib.Optics.Components.DirectionalCouplerPhysical
public import Physlib.Optics.Components.MatchedPropagationPhysical
public import Physlib.Optics.Network.FlatNetlist

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
eight-node equation is equivalent to the existence of a complete N7 component-scattering and
netlist-routing state with zero reverse excitation. Every retained edge is separately identified
with its exact assembled component entry and its routed input and output coordinates.

The complete N7 netlist is bidirectional, while the source graph records the forward boundary
coordinates only. No claim identifies the eight-node matrix with the complete `C * S` feedback
graph, whose coordinates also include the reverse direction and the propagation-component
boundaries. FMICS'15 p. 172 states that its coherent branch uses `sqrt (1-k)` and
`-I * sqrt k`, but defers that analysis to its unavailable reference [3]. Thus coherent N7
`t`/`-I*k` is the source's own unprinted coherent branch; the printed incoherent `1-k`/`k` model
is a different case, compared only if reference [3] surfaces.

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
- `DCDR.edgeGain_eq_n7ScatteringEntry`: every retained gain is an assembled N7 entry.
- `DCDR.isNodeSolution_iff_exists_netlistRealization`: graph solutions are exactly the projected
  complete zero-reverse N7 realizations.

## iii. Table of contents

- A. N7 parameters and explicit flat netlist
- B. External channels and forward coordinates
- C. The edge-indexed eight-node signal-flow graph
- D. Relational extraction from the N7 netlist equations

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

/-- Every external DCDR channel is one of the declared input and output channels. -/
lemma externalChannel_eq_input_or_output (p : Parameters)
    (channel : (netlist p).ExternalChannel) :
    channel = inputChannel p ∨ channel = outputChannel p := by
  rcases channel with ⟨⟨⟨component, port⟩, mode⟩, hExternal⟩
  cases component <;> cases port <;> cases mode
  · exact Or.inl rfl
  · exact absurd ⟨⟨Connection.feedbackToFirst, Sum.inr ()⟩, rfl⟩ hExternal
  · exact absurd ⟨⟨Connection.firstToUpper, Sum.inl ()⟩, rfl⟩ hExternal
  · exact absurd ⟨⟨Connection.firstToLower, Sum.inl ()⟩, rfl⟩ hExternal
  · exact absurd ⟨⟨Connection.upperToSecond, Sum.inr ()⟩, rfl⟩ hExternal
  · exact absurd ⟨⟨Connection.lowerToSecond, Sum.inr ()⟩, rfl⟩ hExternal
  · exact Or.inr rfl
  · exact absurd ⟨⟨Connection.secondToFeedback, Sum.inl ()⟩, rfl⟩ hExternal
  · exact absurd ⟨⟨Connection.firstToUpper, Sum.inr ()⟩, rfl⟩ hExternal
  · exact absurd ⟨⟨Connection.upperToSecond, Sum.inl ()⟩, rfl⟩ hExternal
  · exact absurd ⟨⟨Connection.firstToLower, Sum.inr ()⟩, rfl⟩ hExternal
  · exact absurd ⟨⟨Connection.lowerToSecond, Sum.inl ()⟩, rfl⟩ hExternal
  · exact absurd ⟨⟨Connection.secondToFeedback, Sum.inr ()⟩, rfl⟩ hExternal
  · exact absurd ⟨⟨Connection.feedbackToFirst, Sum.inl ()⟩, rfl⟩ hExternal

/-- The two channel labels select the external input and output, respectively. -/
def externalChannelOfFin (p : Parameters) : Fin 2 → (netlist p).ExternalChannel :=
  ![inputChannel p, outputChannel p]

/-- The declared input and output exhaust the external channel family. -/
noncomputable def externalChannelEquiv (p : Parameters) :
    Fin 2 ≃ (netlist p).ExternalChannel :=
  Equiv.ofBijective (externalChannelOfFin p) ⟨by
    intro first second hChannel
    fin_cases first <;> fin_cases second
    · rfl
    · exact absurd hChannel (inputChannel_ne_outputChannel p)
    · exact absurd hChannel (Ne.symm (inputChannel_ne_outputChannel p))
    · rfl, by
    intro channel
    rcases externalChannel_eq_input_or_output p channel with rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩⟩

/-- External DCDR channels are finite through their explicit two-channel classification. -/
noncomputable instance externalChannelFintype (p : Parameters) :
    Fintype (netlist p).ExternalChannel :=
  Fintype.ofEquiv (Fin 2) (externalChannelEquiv p)

/-- The DCDR has exactly two external channels. -/
lemma externalChannel_card (p : Parameters) :
    Fintype.card (netlist p).ExternalChannel = 2 := by
  rw [← Fintype.card_congr (externalChannelEquiv p)]
  decide

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

/-- The forward graph has exactly eight named boundary coordinates. -/
lemma node_card : Fintype.card Node = 8 := by decide

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

/-- The physical N7 incident channel supplying each retained graph edge. -/
def edgeN7InputChannel (p : Parameters) : Edge → (netlist p).Channel :=
  ![(netlist p).components.componentChannelEmbedding Component.firstCoupler
      ⟨DirectionalCoupler.Port.leftFirst, ()⟩,
    (netlist p).components.componentChannelEmbedding Component.upperPath
      ⟨MatchedPropagation.Port.left, ()⟩,
    (netlist p).components.componentChannelEmbedding Component.secondCoupler
      ⟨DirectionalCoupler.Port.leftFirst, ()⟩,
    (netlist p).components.componentChannelEmbedding Component.firstCoupler
      ⟨DirectionalCoupler.Port.leftFirst, ()⟩,
    (netlist p).components.componentChannelEmbedding Component.lowerPath
      ⟨MatchedPropagation.Port.left, ()⟩,
    (netlist p).components.componentChannelEmbedding Component.secondCoupler
      ⟨DirectionalCoupler.Port.leftSecond, ()⟩,
    (netlist p).components.componentChannelEmbedding Component.secondCoupler
      ⟨DirectionalCoupler.Port.leftFirst, ()⟩,
    (netlist p).components.componentChannelEmbedding Component.feedbackPath
      ⟨MatchedPropagation.Port.left, ()⟩,
    (netlist p).components.componentChannelEmbedding Component.firstCoupler
      ⟨DirectionalCoupler.Port.leftSecond, ()⟩,
    (netlist p).components.componentChannelEmbedding Component.firstCoupler
      ⟨DirectionalCoupler.Port.leftSecond, ()⟩,
    (netlist p).components.componentChannelEmbedding Component.secondCoupler
      ⟨DirectionalCoupler.Port.leftSecond, ()⟩]

/-- The physical N7 outgoing channel receiving each retained graph edge. -/
def edgeN7OutputChannel (p : Parameters) : Edge → (netlist p).Channel :=
  ![(netlist p).components.componentChannelEmbedding Component.firstCoupler
      ⟨DirectionalCoupler.Port.rightFirst, ()⟩,
    (netlist p).components.componentChannelEmbedding Component.upperPath
      ⟨MatchedPropagation.Port.right, ()⟩,
    (netlist p).components.componentChannelEmbedding Component.secondCoupler
      ⟨DirectionalCoupler.Port.rightFirst, ()⟩,
    (netlist p).components.componentChannelEmbedding Component.firstCoupler
      ⟨DirectionalCoupler.Port.rightSecond, ()⟩,
    (netlist p).components.componentChannelEmbedding Component.lowerPath
      ⟨MatchedPropagation.Port.right, ()⟩,
    (netlist p).components.componentChannelEmbedding Component.secondCoupler
      ⟨DirectionalCoupler.Port.rightFirst, ()⟩,
    (netlist p).components.componentChannelEmbedding Component.secondCoupler
      ⟨DirectionalCoupler.Port.rightSecond, ()⟩,
    (netlist p).components.componentChannelEmbedding Component.feedbackPath
      ⟨MatchedPropagation.Port.right, ()⟩,
    (netlist p).components.componentChannelEmbedding Component.firstCoupler
      ⟨DirectionalCoupler.Port.rightFirst, ()⟩,
    (netlist p).components.componentChannelEmbedding Component.firstCoupler
      ⟨DirectionalCoupler.Port.rightSecond, ()⟩,
    (netlist p).components.componentChannelEmbedding Component.secondCoupler
      ⟨DirectionalCoupler.Port.rightSecond, ()⟩]

/-- The four forward entries of an owned N7 directional-coupler scattering matrix. -/
private lemma directionalCoupler_forwardScatteringEntries
    (q : DirectionalCoupler.Parameters) :
    (DirectionalCoupler.physicalScattering q Unit).toModeTransform
          ⟨DirectionalCoupler.Port.rightFirst, ()⟩
          ⟨DirectionalCoupler.Port.leftFirst, ()⟩ = q.throughAmplitude ∧
      (DirectionalCoupler.physicalScattering q Unit).toModeTransform
          ⟨DirectionalCoupler.Port.rightSecond, ()⟩
          ⟨DirectionalCoupler.Port.leftFirst, ()⟩ =
        DirectionalCoupler.crossCoefficient q ∧
      (DirectionalCoupler.physicalScattering q Unit).toModeTransform
          ⟨DirectionalCoupler.Port.rightFirst, ()⟩
          ⟨DirectionalCoupler.Port.leftSecond, ()⟩ =
        DirectionalCoupler.crossCoefficient q ∧
      (DirectionalCoupler.physicalScattering q Unit).toModeTransform
          ⟨DirectionalCoupler.Port.rightSecond, ()⟩
          ⟨DirectionalCoupler.Port.leftSecond, ()⟩ = q.throughAmplitude := by
  simp [DirectionalCoupler.physicalScattering,
    ScatteringMatrix.toModeTransform_reindex, ModeTransform.reindex_apply,
    DirectionalCoupler.scattering, ReflectionlessTwoPort.scattering,
    DirectionalCoupler.mixing, DirectionalCoupler.portFamily,
    DirectionalCoupler.channelEquiv]

/-- The forward entry of an owned N7 matched-propagation scattering matrix. -/
private lemma matchedPropagation_forwardScatteringEntry
    (q : MatchedPropagation.Parameters) :
    (MatchedPropagation.physicalScattering q Unit).toModeTransform
        ⟨MatchedPropagation.Port.right, ()⟩
        ⟨MatchedPropagation.Port.left, ()⟩ =
      MatchedPropagation.transmissionCoefficient q := by
  simp [MatchedPropagation.physicalScattering,
    ScatteringMatrix.toModeTransform_reindex, ModeTransform.reindex_apply,
    MatchedPropagation.scattering, ReflectionlessTwoPort.scattering,
    MatchedPropagation.transmission, MatchedPropagation.portFamily,
    MatchedPropagation.channelEquiv]

/-- Every retained edge gain is the corresponding entry of the assembled N7 component law. -/
lemma edgeGain_eq_n7ScatteringEntry (p : Parameters) (edge : Edge) :
    edgeGain p edge =
      (netlist p).scatteringTransform
        (Outgoing.mk (edgeN7OutputChannel p edge))
        (Incident.mk (edgeN7InputChannel p edge)) := by
  -- The dependent local-channel types require one short check for each audited edge label.
  fin_cases edge
  · simp [edgeGain, edgeN7InputChannel, edgeN7OutputChannel]
    symm
    exact ((netlist p).scatteringTransform_entry_same Component.firstCoupler
      ⟨DirectionalCoupler.Port.rightFirst, ()⟩
      ⟨DirectionalCoupler.Port.leftFirst, ()⟩).trans (by
        change (DirectionalCoupler.physicalScattering p.firstCoupler Unit).toModeTransform
          ⟨DirectionalCoupler.Port.rightFirst, ()⟩
          ⟨DirectionalCoupler.Port.leftFirst, ()⟩ = p.firstCoupler.throughAmplitude
        exact (directionalCoupler_forwardScatteringEntries p.firstCoupler).1)
  · simp [edgeGain, edgeN7InputChannel, edgeN7OutputChannel]
    symm
    exact ((netlist p).scatteringTransform_entry_same Component.upperPath
      ⟨MatchedPropagation.Port.right, ()⟩ ⟨MatchedPropagation.Port.left, ()⟩).trans (by
        change (MatchedPropagation.physicalScattering p.upperPath Unit).toModeTransform
          ⟨MatchedPropagation.Port.right, ()⟩ ⟨MatchedPropagation.Port.left, ()⟩ =
            MatchedPropagation.transmissionCoefficient p.upperPath
        exact matchedPropagation_forwardScatteringEntry p.upperPath)
  · simp [edgeGain, edgeN7InputChannel, edgeN7OutputChannel]
    symm
    exact ((netlist p).scatteringTransform_entry_same Component.secondCoupler
      ⟨DirectionalCoupler.Port.rightFirst, ()⟩
      ⟨DirectionalCoupler.Port.leftFirst, ()⟩).trans (by
        change (DirectionalCoupler.physicalScattering p.secondCoupler Unit).toModeTransform
          ⟨DirectionalCoupler.Port.rightFirst, ()⟩
          ⟨DirectionalCoupler.Port.leftFirst, ()⟩ = p.secondCoupler.throughAmplitude
        exact (directionalCoupler_forwardScatteringEntries p.secondCoupler).1)
  · simp [edgeGain, edgeN7InputChannel, edgeN7OutputChannel]
    symm
    exact ((netlist p).scatteringTransform_entry_same Component.firstCoupler
      ⟨DirectionalCoupler.Port.rightSecond, ()⟩
      ⟨DirectionalCoupler.Port.leftFirst, ()⟩).trans (by
        change (DirectionalCoupler.physicalScattering p.firstCoupler Unit).toModeTransform
          ⟨DirectionalCoupler.Port.rightSecond, ()⟩
          ⟨DirectionalCoupler.Port.leftFirst, ()⟩ =
            DirectionalCoupler.crossCoefficient p.firstCoupler
        exact (directionalCoupler_forwardScatteringEntries p.firstCoupler).2.1)
  · simp [edgeGain, edgeN7InputChannel, edgeN7OutputChannel]
    symm
    exact ((netlist p).scatteringTransform_entry_same Component.lowerPath
      ⟨MatchedPropagation.Port.right, ()⟩ ⟨MatchedPropagation.Port.left, ()⟩).trans (by
        change (MatchedPropagation.physicalScattering p.lowerPath Unit).toModeTransform
          ⟨MatchedPropagation.Port.right, ()⟩ ⟨MatchedPropagation.Port.left, ()⟩ =
            MatchedPropagation.transmissionCoefficient p.lowerPath
        exact matchedPropagation_forwardScatteringEntry p.lowerPath)
  · simp [edgeGain, edgeN7InputChannel, edgeN7OutputChannel]
    symm
    exact ((netlist p).scatteringTransform_entry_same Component.secondCoupler
      ⟨DirectionalCoupler.Port.rightFirst, ()⟩
      ⟨DirectionalCoupler.Port.leftSecond, ()⟩).trans (by
        change (DirectionalCoupler.physicalScattering p.secondCoupler Unit).toModeTransform
          ⟨DirectionalCoupler.Port.rightFirst, ()⟩
          ⟨DirectionalCoupler.Port.leftSecond, ()⟩ =
            DirectionalCoupler.crossCoefficient p.secondCoupler
        exact (directionalCoupler_forwardScatteringEntries p.secondCoupler).2.2.1)
  · simp [edgeGain, edgeN7InputChannel, edgeN7OutputChannel]
    symm
    exact ((netlist p).scatteringTransform_entry_same Component.secondCoupler
      ⟨DirectionalCoupler.Port.rightSecond, ()⟩
      ⟨DirectionalCoupler.Port.leftFirst, ()⟩).trans (by
        change (DirectionalCoupler.physicalScattering p.secondCoupler Unit).toModeTransform
          ⟨DirectionalCoupler.Port.rightSecond, ()⟩
          ⟨DirectionalCoupler.Port.leftFirst, ()⟩ =
            DirectionalCoupler.crossCoefficient p.secondCoupler
        exact (directionalCoupler_forwardScatteringEntries p.secondCoupler).2.1)
  · simp [edgeGain, edgeN7InputChannel, edgeN7OutputChannel]
    symm
    exact ((netlist p).scatteringTransform_entry_same Component.feedbackPath
      ⟨MatchedPropagation.Port.right, ()⟩ ⟨MatchedPropagation.Port.left, ()⟩).trans (by
        change (MatchedPropagation.physicalScattering p.feedbackPath Unit).toModeTransform
          ⟨MatchedPropagation.Port.right, ()⟩ ⟨MatchedPropagation.Port.left, ()⟩ =
            MatchedPropagation.transmissionCoefficient p.feedbackPath
        exact matchedPropagation_forwardScatteringEntry p.feedbackPath)
  · simp [edgeGain, edgeN7InputChannel, edgeN7OutputChannel]
    symm
    exact ((netlist p).scatteringTransform_entry_same Component.firstCoupler
      ⟨DirectionalCoupler.Port.rightFirst, ()⟩
      ⟨DirectionalCoupler.Port.leftSecond, ()⟩).trans (by
        change (DirectionalCoupler.physicalScattering p.firstCoupler Unit).toModeTransform
          ⟨DirectionalCoupler.Port.rightFirst, ()⟩
          ⟨DirectionalCoupler.Port.leftSecond, ()⟩ =
            DirectionalCoupler.crossCoefficient p.firstCoupler
        exact (directionalCoupler_forwardScatteringEntries p.firstCoupler).2.2.1)
  · simp [edgeGain, edgeN7InputChannel, edgeN7OutputChannel]
    symm
    exact ((netlist p).scatteringTransform_entry_same Component.firstCoupler
      ⟨DirectionalCoupler.Port.rightSecond, ()⟩
      ⟨DirectionalCoupler.Port.leftSecond, ()⟩).trans (by
        change (DirectionalCoupler.physicalScattering p.firstCoupler Unit).toModeTransform
          ⟨DirectionalCoupler.Port.rightSecond, ()⟩
          ⟨DirectionalCoupler.Port.leftSecond, ()⟩ = p.firstCoupler.throughAmplitude
        exact (directionalCoupler_forwardScatteringEntries p.firstCoupler).2.2.2)
  · simp [edgeGain, edgeN7InputChannel, edgeN7OutputChannel]
    symm
    exact ((netlist p).scatteringTransform_entry_same Component.secondCoupler
      ⟨DirectionalCoupler.Port.rightSecond, ()⟩
      ⟨DirectionalCoupler.Port.leftSecond, ()⟩).trans (by
        change (DirectionalCoupler.physicalScattering p.secondCoupler Unit).toModeTransform
          ⟨DirectionalCoupler.Port.rightSecond, ()⟩
          ⟨DirectionalCoupler.Port.leftSecond, ()⟩ = p.secondCoupler.throughAmplitude
        exact (directionalCoupler_forwardScatteringEntries p.secondCoupler).2.2.2)

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

/-! ## D. Relational extraction from the N7 netlist equations -/

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

/-- The first coupler gives its reverse first-arm coordinate law. -/
lemma scatteringEquation_firstCoupler_leftFirst (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident) :
    outgoing (Outgoing.mk
        (firstCouplerChannel p DirectionalCoupler.Port.leftFirst)) =
      (p.firstCoupler.throughAmplitude : ℂ) *
          incident (Incident.mk
            (firstCouplerChannel p DirectionalCoupler.Port.rightFirst)) +
        DirectionalCoupler.crossCoefficient p.firstCoupler *
          incident (Incident.mk
            (firstCouplerChannel p DirectionalCoupler.Port.rightSecond)) := by
  have hPhysical :=
    firstCoupler_physicalBehavior_of_scatteringEquation p incident outgoing hScattering
  have hRaw :=
    (DirectionalCoupler.mem_physicalBehavior_iff p.firstCoupler _ _).mp hPhysical
  rw [DirectionalCoupler.mem_behavior_iff,
    DirectionalCoupler.mixing_toLinearMap_apply,
    DirectionalCoupler.mixing_toLinearMap_apply] at hRaw
  have hCoordinate := congrArg
    (fun amplitude => amplitude (Sum.inl (Outgoing.mk (Sum.inl ())))) hRaw
  change
    outgoing (Outgoing.mk
        (firstCouplerChannel p DirectionalCoupler.Port.leftFirst)) =
      (p.firstCoupler.throughAmplitude : ℂ) *
          incident (Incident.mk
            (firstCouplerChannel p DirectionalCoupler.Port.rightFirst)) +
        DirectionalCoupler.crossCoefficient p.firstCoupler *
          incident (Incident.mk
            (firstCouplerChannel p DirectionalCoupler.Port.rightSecond)) at hCoordinate
  exact hCoordinate

/-- The first coupler gives its reverse second-arm coordinate law. -/
lemma scatteringEquation_firstCoupler_leftSecond (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident) :
    outgoing (Outgoing.mk
        (firstCouplerChannel p DirectionalCoupler.Port.leftSecond)) =
      DirectionalCoupler.crossCoefficient p.firstCoupler *
          incident (Incident.mk
            (firstCouplerChannel p DirectionalCoupler.Port.rightFirst)) +
        (p.firstCoupler.throughAmplitude : ℂ) *
          incident (Incident.mk
            (firstCouplerChannel p DirectionalCoupler.Port.rightSecond)) := by
  have hPhysical :=
    firstCoupler_physicalBehavior_of_scatteringEquation p incident outgoing hScattering
  have hRaw :=
    (DirectionalCoupler.mem_physicalBehavior_iff p.firstCoupler _ _).mp hPhysical
  rw [DirectionalCoupler.mem_behavior_iff,
    DirectionalCoupler.mixing_toLinearMap_apply,
    DirectionalCoupler.mixing_toLinearMap_apply] at hRaw
  have hCoordinate := congrArg
    (fun amplitude => amplitude (Sum.inl (Outgoing.mk (Sum.inr ())))) hRaw
  change
    outgoing (Outgoing.mk
        (firstCouplerChannel p DirectionalCoupler.Port.leftSecond)) =
      DirectionalCoupler.crossCoefficient p.firstCoupler *
          incident (Incident.mk
            (firstCouplerChannel p DirectionalCoupler.Port.rightFirst)) +
        (p.firstCoupler.throughAmplitude : ℂ) *
          incident (Incident.mk
            (firstCouplerChannel p DirectionalCoupler.Port.rightSecond)) at hCoordinate
  exact hCoordinate

/-- The second coupler gives its reverse first-arm coordinate law. -/
lemma scatteringEquation_secondCoupler_leftFirst (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident) :
    outgoing (Outgoing.mk
        (secondCouplerChannel p DirectionalCoupler.Port.leftFirst)) =
      (p.secondCoupler.throughAmplitude : ℂ) *
          incident (Incident.mk
            (secondCouplerChannel p DirectionalCoupler.Port.rightFirst)) +
        DirectionalCoupler.crossCoefficient p.secondCoupler *
          incident (Incident.mk
            (secondCouplerChannel p DirectionalCoupler.Port.rightSecond)) := by
  have hPhysical :=
    secondCoupler_physicalBehavior_of_scatteringEquation p incident outgoing hScattering
  have hRaw :=
    (DirectionalCoupler.mem_physicalBehavior_iff p.secondCoupler _ _).mp hPhysical
  rw [DirectionalCoupler.mem_behavior_iff,
    DirectionalCoupler.mixing_toLinearMap_apply,
    DirectionalCoupler.mixing_toLinearMap_apply] at hRaw
  have hCoordinate := congrArg
    (fun amplitude => amplitude (Sum.inl (Outgoing.mk (Sum.inl ())))) hRaw
  change
    outgoing (Outgoing.mk
        (secondCouplerChannel p DirectionalCoupler.Port.leftFirst)) =
      (p.secondCoupler.throughAmplitude : ℂ) *
          incident (Incident.mk
            (secondCouplerChannel p DirectionalCoupler.Port.rightFirst)) +
        DirectionalCoupler.crossCoefficient p.secondCoupler *
          incident (Incident.mk
            (secondCouplerChannel p DirectionalCoupler.Port.rightSecond)) at hCoordinate
  exact hCoordinate

/-- The second coupler gives its reverse second-arm coordinate law. -/
lemma scatteringEquation_secondCoupler_leftSecond (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident) :
    outgoing (Outgoing.mk
        (secondCouplerChannel p DirectionalCoupler.Port.leftSecond)) =
      DirectionalCoupler.crossCoefficient p.secondCoupler *
          incident (Incident.mk
            (secondCouplerChannel p DirectionalCoupler.Port.rightFirst)) +
        (p.secondCoupler.throughAmplitude : ℂ) *
          incident (Incident.mk
            (secondCouplerChannel p DirectionalCoupler.Port.rightSecond)) := by
  have hPhysical :=
    secondCoupler_physicalBehavior_of_scatteringEquation p incident outgoing hScattering
  have hRaw :=
    (DirectionalCoupler.mem_physicalBehavior_iff p.secondCoupler _ _).mp hPhysical
  rw [DirectionalCoupler.mem_behavior_iff,
    DirectionalCoupler.mixing_toLinearMap_apply,
    DirectionalCoupler.mixing_toLinearMap_apply] at hRaw
  have hCoordinate := congrArg
    (fun amplitude => amplitude (Sum.inl (Outgoing.mk (Sum.inr ())))) hRaw
  change
    outgoing (Outgoing.mk
        (secondCouplerChannel p DirectionalCoupler.Port.leftSecond)) =
      DirectionalCoupler.crossCoefficient p.secondCoupler *
          incident (Incident.mk
            (secondCouplerChannel p DirectionalCoupler.Port.rightFirst)) +
        (p.secondCoupler.throughAmplitude : ℂ) *
          incident (Incident.mk
            (secondCouplerChannel p DirectionalCoupler.Port.rightSecond)) at hCoordinate
  exact hCoordinate

/-- The upper N7 path gives its reverse propagation coordinate law. -/
lemma scatteringEquation_upperPath_left (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident) :
    outgoing (Outgoing.mk (upperPathChannel p MatchedPropagation.Port.left)) =
      p.upperCoefficient *
        incident (Incident.mk (upperPathChannel p MatchedPropagation.Port.right)) := by
  have hPhysical :=
    upperPath_physicalBehavior_of_scatteringEquation p incident outgoing hScattering
  have hRaw :=
    (MatchedPropagation.mem_physicalBehavior_iff p.upperPath _ _).mp hPhysical
  rw [MatchedPropagation.mem_behavior_iff] at hRaw
  have hCoordinate := congrArg
    (fun amplitude => amplitude (Sum.inl (Outgoing.mk ()))) hRaw
  change
    outgoing (Outgoing.mk (upperPathChannel p MatchedPropagation.Port.left)) =
      p.upperCoefficient *
        incident (Incident.mk
          (upperPathChannel p MatchedPropagation.Port.right)) at hCoordinate
  exact hCoordinate

/-- The lower N7 path gives its reverse propagation coordinate law. -/
lemma scatteringEquation_lowerPath_left (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident) :
    outgoing (Outgoing.mk (lowerPathChannel p MatchedPropagation.Port.left)) =
      p.lowerCoefficient *
        incident (Incident.mk (lowerPathChannel p MatchedPropagation.Port.right)) := by
  have hPhysical :=
    lowerPath_physicalBehavior_of_scatteringEquation p incident outgoing hScattering
  have hRaw :=
    (MatchedPropagation.mem_physicalBehavior_iff p.lowerPath _ _).mp hPhysical
  rw [MatchedPropagation.mem_behavior_iff] at hRaw
  have hCoordinate := congrArg
    (fun amplitude => amplitude (Sum.inl (Outgoing.mk ()))) hRaw
  change
    outgoing (Outgoing.mk (lowerPathChannel p MatchedPropagation.Port.left)) =
      p.lowerCoefficient *
        incident (Incident.mk
          (lowerPathChannel p MatchedPropagation.Port.right)) at hCoordinate
  exact hCoordinate

/-- The feedback N7 path gives its reverse propagation coordinate law. -/
lemma scatteringEquation_feedbackPath_left (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident) :
    outgoing (Outgoing.mk (feedbackPathChannel p MatchedPropagation.Port.left)) =
      p.feedbackCoefficient *
        incident (Incident.mk (feedbackPathChannel p MatchedPropagation.Port.right)) := by
  have hPhysical :=
    feedbackPath_physicalBehavior_of_scatteringEquation p incident outgoing hScattering
  have hRaw :=
    (MatchedPropagation.mem_physicalBehavior_iff p.feedbackPath _ _).mp hPhysical
  rw [MatchedPropagation.mem_behavior_iff] at hRaw
  have hCoordinate := congrArg
    (fun amplitude => amplitude (Sum.inl (Outgoing.mk ()))) hRaw
  change
    outgoing (Outgoing.mk (feedbackPathChannel p MatchedPropagation.Port.left)) =
      p.feedbackCoefficient *
        incident (Incident.mk
          (feedbackPathChannel p MatchedPropagation.Port.right)) at hCoordinate
  exact hCoordinate

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

/-- Incident assembly exposes the source-side output coordinate as a second external input. -/
lemma incidentAssembly_apply_output (p : Parameters)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (external : ModeAmplitude (netlist p).ExternalIncident) :
    (netlist p).connections.incidentAssembly outgoing external
        (Incident.mk
          (secondCouplerChannel p DirectionalCoupler.Port.rightFirst)) =
      external (Incident.mk (outputChannel p)) := by
  exact (netlist p).connections.incidentAssembly_apply_external
    outgoing external (outputChannel p)

/-- Reverse incident assembly sends the upper path's left output to the first coupler. -/
lemma incidentAssembly_apply_firstCoupler_rightFirst (p : Parameters)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (external : ModeAmplitude (netlist p).ExternalIncident) :
    (netlist p).connections.incidentAssembly outgoing external
        (Incident.mk
          (firstCouplerChannel p DirectionalCoupler.Port.rightFirst)) =
      outgoing (Outgoing.mk (upperPathChannel p MatchedPropagation.Port.left)) := by
  change
    (netlist p).connections.incidentAssembly outgoing external
        (Incident.mk ((netlist p).connections.channelEmbedding
          ⟨Connection.firstToUpper, Sum.inl ()⟩)) = _
  rw [(netlist p).connections.incidentAssembly_apply_connected_channel]
  rfl

/-- Reverse incident assembly sends the lower path's left output to the first coupler. -/
lemma incidentAssembly_apply_firstCoupler_rightSecond (p : Parameters)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (external : ModeAmplitude (netlist p).ExternalIncident) :
    (netlist p).connections.incidentAssembly outgoing external
        (Incident.mk
          (firstCouplerChannel p DirectionalCoupler.Port.rightSecond)) =
      outgoing (Outgoing.mk (lowerPathChannel p MatchedPropagation.Port.left)) := by
  change
    (netlist p).connections.incidentAssembly outgoing external
        (Incident.mk ((netlist p).connections.channelEmbedding
          ⟨Connection.firstToLower, Sum.inl ()⟩)) = _
  rw [(netlist p).connections.incidentAssembly_apply_connected_channel]
  rfl

/-- Reverse incident assembly sends the feedback path's left output to the second coupler. -/
lemma incidentAssembly_apply_secondCoupler_rightSecond (p : Parameters)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (external : ModeAmplitude (netlist p).ExternalIncident) :
    (netlist p).connections.incidentAssembly outgoing external
        (Incident.mk
          (secondCouplerChannel p DirectionalCoupler.Port.rightSecond)) =
      outgoing (Outgoing.mk (feedbackPathChannel p MatchedPropagation.Port.left)) := by
  change
    (netlist p).connections.incidentAssembly outgoing external
        (Incident.mk ((netlist p).connections.channelEmbedding
          ⟨Connection.secondToFeedback, Sum.inl ()⟩)) = _
  rw [(netlist p).connections.incidentAssembly_apply_connected_channel]
  rfl

/-- Reverse incident assembly sends the second coupler's upper-left output into the upper path. -/
lemma incidentAssembly_apply_upperPath_right (p : Parameters)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (external : ModeAmplitude (netlist p).ExternalIncident) :
    (netlist p).connections.incidentAssembly outgoing external
        (Incident.mk (upperPathChannel p MatchedPropagation.Port.right)) =
      outgoing (Outgoing.mk
        (secondCouplerChannel p DirectionalCoupler.Port.leftFirst)) := by
  change
    (netlist p).connections.incidentAssembly outgoing external
        (Incident.mk ((netlist p).connections.channelEmbedding
          ⟨Connection.upperToSecond, Sum.inl ()⟩)) = _
  rw [(netlist p).connections.incidentAssembly_apply_connected_channel]
  rfl

/-- Reverse incident assembly sends the second coupler's lower-left output into the lower path. -/
lemma incidentAssembly_apply_lowerPath_right (p : Parameters)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (external : ModeAmplitude (netlist p).ExternalIncident) :
    (netlist p).connections.incidentAssembly outgoing external
        (Incident.mk (lowerPathChannel p MatchedPropagation.Port.right)) =
      outgoing (Outgoing.mk
        (secondCouplerChannel p DirectionalCoupler.Port.leftSecond)) := by
  change
    (netlist p).connections.incidentAssembly outgoing external
        (Incident.mk ((netlist p).connections.channelEmbedding
          ⟨Connection.lowerToSecond, Sum.inl ()⟩)) = _
  rw [(netlist p).connections.incidentAssembly_apply_connected_channel]
  rfl

/-- Reverse incident assembly sends the first coupler's feedback-left output into its path. -/
lemma incidentAssembly_apply_feedbackPath_right (p : Parameters)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (external : ModeAmplitude (netlist p).ExternalIncident) :
    (netlist p).connections.incidentAssembly outgoing external
        (Incident.mk (feedbackPathChannel p MatchedPropagation.Port.right)) =
      outgoing (Outgoing.mk
        (firstCouplerChannel p DirectionalCoupler.Port.leftSecond)) := by
  change
    (netlist p).connections.incidentAssembly outgoing external
        (Incident.mk ((netlist p).connections.channelEmbedding
          ⟨Connection.feedbackToFirst, Sum.inl ()⟩)) = _
  rw [(netlist p).connections.incidentAssembly_apply_connected_channel]
  rfl

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

/-- The complete incident N7 state obtained by lifting eight forward graph coordinates.

The seven reverse-going incident coordinates are set to zero. The forward coordinates at
component boundaries are copied from the graph nodes related by the six physical wires.
-/
def liftedIncident (p : Parameters) (state : Node → ℂ) :
    ModeAmplitude (netlist p).IncidentIndex :=
  WithLp.toLp 2 fun endpoint =>
    match endpoint.channel.1.1, endpoint.channel.1.2 with
    | .firstCoupler, .leftFirst => state 0
    | .firstCoupler, .leftSecond => state 1
    | .firstCoupler, .rightFirst => 0
    | .firstCoupler, .rightSecond => 0
    | .secondCoupler, .leftFirst => state 5
    | .secondCoupler, .leftSecond => state 4
    | .secondCoupler, .rightFirst => 0
    | .secondCoupler, .rightSecond => 0
    | .upperPath, .left => state 2
    | .upperPath, .right => 0
    | .lowerPath, .left => state 3
    | .lowerPath, .right => 0
    | .feedbackPath, .left => state 6
    | .feedbackPath, .right => 0

/-- The complete outgoing N7 state obtained by lifting eight forward graph coordinates.

The seven reverse-going outgoing coordinates are zero. Each retained forward output is copied
to the physical component endpoint represented by its graph node.
-/
def liftedOutgoing (p : Parameters) (state : Node → ℂ) :
    ModeAmplitude (netlist p).OutgoingIndex :=
  WithLp.toLp 2 fun endpoint =>
    match endpoint.channel.1.1, endpoint.channel.1.2 with
    | .firstCoupler, .leftFirst => 0
    | .firstCoupler, .leftSecond => 0
    | .firstCoupler, .rightFirst => state 2
    | .firstCoupler, .rightSecond => state 3
    | .secondCoupler, .leftFirst => 0
    | .secondCoupler, .leftSecond => 0
    | .secondCoupler, .rightFirst => state 7
    | .secondCoupler, .rightSecond => state 6
    | .upperPath, .left => 0
    | .upperPath, .right => state 5
    | .lowerPath, .left => 0
    | .lowerPath, .right => state 4
    | .feedbackPath, .left => 0
    | .feedbackPath, .right => state 1

/-- Every retained edge starts at the graph coordinate routed into its physical N7 input. -/
lemma liftedIncident_apply_edgeN7Input (p : Parameters) (state : Node → ℂ)
    (edge : Edge) :
    liftedIncident p state (Incident.mk (edgeN7InputChannel p edge)) =
      state (edgeSource edge) := by
  fin_cases edge <;>
    rfl

/-- Every retained edge ends at the graph coordinate routed from its physical N7 output. -/
lemma liftedOutgoing_apply_edgeN7Output (p : Parameters) (state : Node → ℂ)
    (edge : Edge) :
    liftedOutgoing p state (Outgoing.mk (edgeN7OutputChannel p edge)) =
      state (edgeTarget edge) := by
  fin_cases edge <;>
    rfl

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

/-- A forward graph solution's lifted N7 amplitudes satisfy every component scattering law. -/
lemma liftedOutgoing_eq_scatteringTransform (p : Parameters) (input : ℂ)
    (state : Node → ℂ) (hForward : ForwardEquations p input state) :
    liftedOutgoing p state =
      (netlist p).scatteringTransform.toLinearMap (liftedIncident p state) := by
  apply WithLp.ofLp_injective 2
  funext endpoint
  rcases endpoint with ⟨⟨⟨component, port⟩, mode⟩⟩
  -- These are the fourteen owned physical channels: seven reverse and seven forward outputs.
  cases component <;> cases port <;> cases mode
  · change liftedOutgoing p state (Outgoing.mk
        (firstCouplerChannel p DirectionalCoupler.Port.leftFirst)) =
      (netlist p).scatteringTransform.toLinearMap (liftedIncident p state)
        (Outgoing.mk (firstCouplerChannel p DirectionalCoupler.Port.leftFirst))
    rw [scatteringEquation_firstCoupler_leftFirst p (liftedIncident p state) _ rfl]
    simp [liftedIncident, liftedOutgoing, firstCouplerChannel]
  · change liftedOutgoing p state (Outgoing.mk
        (firstCouplerChannel p DirectionalCoupler.Port.leftSecond)) =
      (netlist p).scatteringTransform.toLinearMap (liftedIncident p state)
        (Outgoing.mk (firstCouplerChannel p DirectionalCoupler.Port.leftSecond))
    rw [scatteringEquation_firstCoupler_leftSecond p (liftedIncident p state) _ rfl]
    simp [liftedIncident, liftedOutgoing, firstCouplerChannel]
  · change liftedOutgoing p state (Outgoing.mk
        (firstCouplerChannel p DirectionalCoupler.Port.rightFirst)) =
      (netlist p).scatteringTransform.toLinearMap (liftedIncident p state)
        (Outgoing.mk (firstCouplerChannel p DirectionalCoupler.Port.rightFirst))
    rw [scatteringEquation_firstCoupler_rightFirst p (liftedIncident p state) _ rfl]
    simpa [liftedIncident, liftedOutgoing, firstCouplerChannel] using hForward.nodeThree
  · change liftedOutgoing p state (Outgoing.mk
        (firstCouplerChannel p DirectionalCoupler.Port.rightSecond)) =
      (netlist p).scatteringTransform.toLinearMap (liftedIncident p state)
        (Outgoing.mk (firstCouplerChannel p DirectionalCoupler.Port.rightSecond))
    rw [scatteringEquation_firstCoupler_rightSecond p (liftedIncident p state) _ rfl]
    simpa [liftedIncident, liftedOutgoing, firstCouplerChannel] using hForward.nodeFour
  · change liftedOutgoing p state (Outgoing.mk
        (secondCouplerChannel p DirectionalCoupler.Port.leftFirst)) =
      (netlist p).scatteringTransform.toLinearMap (liftedIncident p state)
        (Outgoing.mk (secondCouplerChannel p DirectionalCoupler.Port.leftFirst))
    rw [scatteringEquation_secondCoupler_leftFirst p (liftedIncident p state) _ rfl]
    simp [liftedIncident, liftedOutgoing, secondCouplerChannel]
  · change liftedOutgoing p state (Outgoing.mk
        (secondCouplerChannel p DirectionalCoupler.Port.leftSecond)) =
      (netlist p).scatteringTransform.toLinearMap (liftedIncident p state)
        (Outgoing.mk (secondCouplerChannel p DirectionalCoupler.Port.leftSecond))
    rw [scatteringEquation_secondCoupler_leftSecond p (liftedIncident p state) _ rfl]
    simp [liftedIncident, liftedOutgoing, secondCouplerChannel]
  · change liftedOutgoing p state (Outgoing.mk
        (secondCouplerChannel p DirectionalCoupler.Port.rightFirst)) =
      (netlist p).scatteringTransform.toLinearMap (liftedIncident p state)
        (Outgoing.mk (secondCouplerChannel p DirectionalCoupler.Port.rightFirst))
    rw [scatteringEquation_secondCoupler_rightFirst p (liftedIncident p state) _ rfl]
    simpa [liftedIncident, liftedOutgoing, secondCouplerChannel, add_comm] using
      hForward.nodeEight
  · change liftedOutgoing p state (Outgoing.mk
        (secondCouplerChannel p DirectionalCoupler.Port.rightSecond)) =
      (netlist p).scatteringTransform.toLinearMap (liftedIncident p state)
        (Outgoing.mk (secondCouplerChannel p DirectionalCoupler.Port.rightSecond))
    rw [scatteringEquation_secondCoupler_rightSecond p (liftedIncident p state) _ rfl]
    simpa [liftedIncident, liftedOutgoing, secondCouplerChannel, add_comm] using
      hForward.nodeSeven
  · change liftedOutgoing p state (Outgoing.mk
        (upperPathChannel p MatchedPropagation.Port.left)) =
      (netlist p).scatteringTransform.toLinearMap (liftedIncident p state)
        (Outgoing.mk (upperPathChannel p MatchedPropagation.Port.left))
    rw [scatteringEquation_upperPath_left p (liftedIncident p state) _ rfl]
    simp [liftedIncident, liftedOutgoing, upperPathChannel]
  · change liftedOutgoing p state (Outgoing.mk
        (upperPathChannel p MatchedPropagation.Port.right)) =
      (netlist p).scatteringTransform.toLinearMap (liftedIncident p state)
        (Outgoing.mk (upperPathChannel p MatchedPropagation.Port.right))
    rw [scatteringEquation_upperPath_right p (liftedIncident p state) _ rfl]
    simpa [liftedIncident, liftedOutgoing, upperPathChannel] using hForward.nodeSix
  · change liftedOutgoing p state (Outgoing.mk
        (lowerPathChannel p MatchedPropagation.Port.left)) =
      (netlist p).scatteringTransform.toLinearMap (liftedIncident p state)
        (Outgoing.mk (lowerPathChannel p MatchedPropagation.Port.left))
    rw [scatteringEquation_lowerPath_left p (liftedIncident p state) _ rfl]
    simp [liftedIncident, liftedOutgoing, lowerPathChannel]
  · change liftedOutgoing p state (Outgoing.mk
        (lowerPathChannel p MatchedPropagation.Port.right)) =
      (netlist p).scatteringTransform.toLinearMap (liftedIncident p state)
        (Outgoing.mk (lowerPathChannel p MatchedPropagation.Port.right))
    rw [scatteringEquation_lowerPath_right p (liftedIncident p state) _ rfl]
    simpa [liftedIncident, liftedOutgoing, lowerPathChannel] using hForward.nodeFive
  · change liftedOutgoing p state (Outgoing.mk
        (feedbackPathChannel p MatchedPropagation.Port.left)) =
      (netlist p).scatteringTransform.toLinearMap (liftedIncident p state)
        (Outgoing.mk (feedbackPathChannel p MatchedPropagation.Port.left))
    rw [scatteringEquation_feedbackPath_left p (liftedIncident p state) _ rfl]
    simp [liftedIncident, liftedOutgoing, feedbackPathChannel]
  · change liftedOutgoing p state (Outgoing.mk
        (feedbackPathChannel p MatchedPropagation.Port.right)) =
      (netlist p).scatteringTransform.toLinearMap (liftedIncident p state)
        (Outgoing.mk (feedbackPathChannel p MatchedPropagation.Port.right))
    rw [scatteringEquation_feedbackPath_right p (liftedIncident p state) _ rfl]
    simpa [liftedIncident, liftedOutgoing, feedbackPathChannel] using hForward.nodeTwo

/-- A forward graph solution's lifted N7 amplitudes satisfy all six wires and both externals. -/
lemma liftedIncident_eq_incidentAssembly (p : Parameters) (input : ℂ)
    (state : Node → ℂ) (hForward : ForwardEquations p input state) :
    liftedIncident p state =
      (netlist p).connections.incidentAssembly
        (liftedOutgoing p state) (inputAmplitude p input) := by
  apply WithLp.ofLp_injective 2
  funext endpoint
  rcases endpoint with ⟨⟨⟨component, port⟩, mode⟩⟩
  -- Exhausting all physical ports checks both ends of every wire and both external coordinates.
  cases component <;> cases port <;> cases mode
  · change liftedIncident p state (Incident.mk
        (firstCouplerChannel p DirectionalCoupler.Port.leftFirst)) =
      (netlist p).connections.incidentAssembly
        (liftedOutgoing p state) (inputAmplitude p input)
        (Incident.mk (firstCouplerChannel p DirectionalCoupler.Port.leftFirst))
    rw [incidentAssembly_apply_input]
    simpa [liftedIncident, firstCouplerChannel] using hForward.nodeOne
  · change liftedIncident p state (Incident.mk
        (firstCouplerChannel p DirectionalCoupler.Port.leftSecond)) =
      (netlist p).connections.incidentAssembly
        (liftedOutgoing p state) (inputAmplitude p input)
        (Incident.mk (firstCouplerChannel p DirectionalCoupler.Port.leftSecond))
    rw [incidentAssembly_apply_firstCoupler_leftSecond]
    simp [liftedIncident, liftedOutgoing, firstCouplerChannel, feedbackPathChannel]
  · change liftedIncident p state (Incident.mk
        (firstCouplerChannel p DirectionalCoupler.Port.rightFirst)) =
      (netlist p).connections.incidentAssembly
        (liftedOutgoing p state) (inputAmplitude p input)
        (Incident.mk (firstCouplerChannel p DirectionalCoupler.Port.rightFirst))
    rw [incidentAssembly_apply_firstCoupler_rightFirst]
    simp [liftedIncident, liftedOutgoing, firstCouplerChannel, upperPathChannel]
  · change liftedIncident p state (Incident.mk
        (firstCouplerChannel p DirectionalCoupler.Port.rightSecond)) =
      (netlist p).connections.incidentAssembly
        (liftedOutgoing p state) (inputAmplitude p input)
        (Incident.mk (firstCouplerChannel p DirectionalCoupler.Port.rightSecond))
    rw [incidentAssembly_apply_firstCoupler_rightSecond]
    simp [liftedIncident, liftedOutgoing, firstCouplerChannel, lowerPathChannel]
  · change liftedIncident p state (Incident.mk
        (secondCouplerChannel p DirectionalCoupler.Port.leftFirst)) =
      (netlist p).connections.incidentAssembly
        (liftedOutgoing p state) (inputAmplitude p input)
        (Incident.mk (secondCouplerChannel p DirectionalCoupler.Port.leftFirst))
    rw [incidentAssembly_apply_secondCoupler_leftFirst]
    simp [liftedIncident, liftedOutgoing, secondCouplerChannel, upperPathChannel]
  · change liftedIncident p state (Incident.mk
        (secondCouplerChannel p DirectionalCoupler.Port.leftSecond)) =
      (netlist p).connections.incidentAssembly
        (liftedOutgoing p state) (inputAmplitude p input)
        (Incident.mk (secondCouplerChannel p DirectionalCoupler.Port.leftSecond))
    rw [incidentAssembly_apply_secondCoupler_leftSecond]
    simp [liftedIncident, liftedOutgoing, secondCouplerChannel, lowerPathChannel]
  · change liftedIncident p state (Incident.mk
        (secondCouplerChannel p DirectionalCoupler.Port.rightFirst)) =
      (netlist p).connections.incidentAssembly
        (liftedOutgoing p state) (inputAmplitude p input)
        (Incident.mk (secondCouplerChannel p DirectionalCoupler.Port.rightFirst))
    rw [incidentAssembly_apply_output]
    simp [liftedIncident, secondCouplerChannel]
  · change liftedIncident p state (Incident.mk
        (secondCouplerChannel p DirectionalCoupler.Port.rightSecond)) =
      (netlist p).connections.incidentAssembly
        (liftedOutgoing p state) (inputAmplitude p input)
        (Incident.mk (secondCouplerChannel p DirectionalCoupler.Port.rightSecond))
    rw [incidentAssembly_apply_secondCoupler_rightSecond]
    simp [liftedIncident, liftedOutgoing, secondCouplerChannel, feedbackPathChannel]
  · change liftedIncident p state (Incident.mk
        (upperPathChannel p MatchedPropagation.Port.left)) =
      (netlist p).connections.incidentAssembly
        (liftedOutgoing p state) (inputAmplitude p input)
        (Incident.mk (upperPathChannel p MatchedPropagation.Port.left))
    rw [incidentAssembly_apply_upperPath_left]
    simp [liftedIncident, liftedOutgoing, upperPathChannel, firstCouplerChannel]
  · change liftedIncident p state (Incident.mk
        (upperPathChannel p MatchedPropagation.Port.right)) =
      (netlist p).connections.incidentAssembly
        (liftedOutgoing p state) (inputAmplitude p input)
        (Incident.mk (upperPathChannel p MatchedPropagation.Port.right))
    rw [incidentAssembly_apply_upperPath_right]
    simp [liftedIncident, liftedOutgoing, upperPathChannel, secondCouplerChannel]
  · change liftedIncident p state (Incident.mk
        (lowerPathChannel p MatchedPropagation.Port.left)) =
      (netlist p).connections.incidentAssembly
        (liftedOutgoing p state) (inputAmplitude p input)
        (Incident.mk (lowerPathChannel p MatchedPropagation.Port.left))
    rw [incidentAssembly_apply_lowerPath_left]
    simp [liftedIncident, liftedOutgoing, lowerPathChannel, firstCouplerChannel]
  · change liftedIncident p state (Incident.mk
        (lowerPathChannel p MatchedPropagation.Port.right)) =
      (netlist p).connections.incidentAssembly
        (liftedOutgoing p state) (inputAmplitude p input)
        (Incident.mk (lowerPathChannel p MatchedPropagation.Port.right))
    rw [incidentAssembly_apply_lowerPath_right]
    simp [liftedIncident, liftedOutgoing, lowerPathChannel, secondCouplerChannel]
  · change liftedIncident p state (Incident.mk
        (feedbackPathChannel p MatchedPropagation.Port.left)) =
      (netlist p).connections.incidentAssembly
        (liftedOutgoing p state) (inputAmplitude p input)
        (Incident.mk (feedbackPathChannel p MatchedPropagation.Port.left))
    rw [incidentAssembly_apply_feedbackPath_left]
    simp [liftedIncident, liftedOutgoing, feedbackPathChannel, secondCouplerChannel]
  · change liftedIncident p state (Incident.mk
        (feedbackPathChannel p MatchedPropagation.Port.right)) =
      (netlist p).connections.incidentAssembly
        (liftedOutgoing p state) (inputAmplitude p input)
        (Incident.mk (feedbackPathChannel p MatchedPropagation.Port.right))
    rw [incidentAssembly_apply_feedbackPath_right]
    simp [liftedIncident, liftedOutgoing, feedbackPathChannel, firstCouplerChannel]

/-- Projecting the lifted complete N7 state recovers the original eight graph coordinates. -/
lemma forwardState_lifted (p : Parameters) (state : Node → ℂ) :
    forwardState p (liftedIncident p state) (liftedOutgoing p state) = state := by
  funext node
  fin_cases node <;>
    rfl

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

/-- The extracted graph equation is equivalent to a complete zero-reverse N7 realization.

The forward implication constructs all fourteen incident and fourteen outgoing component
coordinates, proves the raw assembled scattering and routing equations, and projects back to the
given eight-node state. The reverse implication is the previously established netlist projection.
-/
lemma isNodeSolution_iff_exists_netlistRealization (p : Parameters) (input : ℂ)
    (state : Node → ℂ) :
    Physlib.SignalFlowGraph.IsNodeSolution
        (signalFlowGraph p) (signalInput input) state ↔
      ∃ incident : ModeAmplitude (netlist p).IncidentIndex,
        ∃ outgoing : ModeAmplitude (netlist p).OutgoingIndex,
          outgoing = (netlist p).scatteringTransform.toLinearMap incident ∧
            incident = (netlist p).connections.incidentAssembly
              outgoing (inputAmplitude p input) ∧
            forwardState p incident outgoing = state := by
  constructor
  · intro hState
    have hForward :=
      (isNodeSolution_iff_forwardEquations p input state).mp hState
    exact ⟨liftedIncident p state, liftedOutgoing p state,
      liftedOutgoing_eq_scatteringTransform p input state hForward,
      liftedIncident_eq_incidentAssembly p input state hForward,
      forwardState_lifted p state⟩
  · rintro ⟨incident, outgoing, hScattering, hAssembly, hProjection⟩
    rw [← hProjection]
    simpa using forwardState_isNodeSolution_of_netlistEquations p
      (inputAmplitude p input) incident outgoing hScattering hAssembly

end DCDR

end

end Optics
