/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Components.DirectionalCouplerPhysical
public import Physlib.Optics.Components.MatchedPropagationPhysical
public import Physlib.Optics.Network.FlatNetlist

/-!
# Double-coupler double-ring flat netlist

## i. Overview

This file constructs the double-coupler double-ring (DCDR) as an explicit `FlatNetlist` from
two N7 directional couplers and three N7 matched-propagation paths. Its six connections leave
exactly the source-side input and output channels exposed. The component laws are the pinned
`-I * k` field-amplitude coupler law and the fixed-carrier propagation coefficient; see
`Physlib/Optics/Components/DirectionalCoupler.lean:68-76` and
`Physlib/Optics/Components/MatchedPropagation.lean:93-103`.

Coherent N7 `t`/`-I * k` is the source's own unprinted coherent branch; the printed
incoherent `1 - k`/`k` model is a different case, compared only if reference [3] surfaces.

This is a fixed-carrier, single-mode topology. Power means normalized modal power, not
electromagnetic power. No passivity, losslessness, reciprocity, causality, time-domain behavior,
stability, pole, zero, resonance, bandwidth, or material realization is asserted here.

## ii. Key results

- `DCDR.netlist`: the explicit two-coupler, three-path N7 flat netlist.
- `DCDR.inputChannel` and `DCDR.outputChannel`: the two external channels.
- `DCDR.forwardState`: the eight projected forward boundary coordinates.

## iii. Table of contents

- A. N7 parameters and explicit flat netlist
- B. External channels and forward coordinates

## iv. References

U. Siddique, S. M. Beillahi, and S. Tahar, "On the Formal Analysis of Photonic Signal
Processing Systems", FMICS 2015, LNCS 9128, Definition 8 and Theorem 3 (p. 173).
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


end DCDR

end

end Optics

