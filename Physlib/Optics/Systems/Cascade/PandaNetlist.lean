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
# PANDA Vernier flat netlist

## i. Overview

This file constructs a fixed-carrier PANDA Vernier resonator as an explicit N7 `FlatNetlist`.
The component family contains four directional couplers, four main-ring quarter sections, and two
half-sections on each side ring. Fourteen proof-carrying wires leave exactly four external ports:
input, through, add, and drop.

The topology is bidirectional at the N7 layer. A later source bridge projects one forward
coordinate from each relevant component boundary; it does not replace this complete scattering
netlist by a hand-drawn graph.

## ii. Key results

- `Panda.netlist`: the four-coupler, eight-delay N7 netlist.
- `Panda.inputChannel`, `throughChannel`, `addChannel`, and `dropChannel`: its external ports.
- `Panda.inputAmplitude`: source-only coherent excitation.

## iii. Table of contents

- A. Components and parameters
- B. Physical wiring
- C. Finite channel instances
- D. External channels

## iv. References

The paper describes four couplers and three rings. Its printed graph is compared only in later
modules. This file asserts no source-formula identity, insertion-loss model, passivity,
losslessness, reciprocity, causality, bandwidth, dispersion, resonance, stability, material
realization, or electromagnetic power normalization.

S. M. Beillahi, U. Siddique, and S. Tahar, "Formal Analysis of Engineering Systems Based on
Signal-Flow-Graph Theory", NSV 2016, LNCS 10152, Definition 11 and Theorems 5-6, pp. 42-43.
-/

@[expose] public section

namespace Optics

noncomputable section

namespace Panda

/-! ## A. Components and parameters -/

/-- N7 component parameters for the four couplers and eight propagation sections of PANDA. -/
structure Parameters where
  /-- Input/through directional coupler. -/
  inputCoupler : DirectionalCoupler.Parameters
  /-- Main-ring/add/drop directional coupler. -/
  outputCoupler : DirectionalCoupler.Parameters
  /-- Right side-ring directional coupler. -/
  rightCoupler : DirectionalCoupler.Parameters
  /-- Left side-ring directional coupler. -/
  leftCoupler : DirectionalCoupler.Parameters
  /-- Main-ring quarter from the input coupler to the right coupler. -/
  mainQuarterOne : MatchedPropagation.Parameters
  /-- Main-ring quarter from the right coupler to the output coupler. -/
  mainQuarterTwo : MatchedPropagation.Parameters
  /-- Main-ring quarter from the output coupler to the left coupler. -/
  mainQuarterThree : MatchedPropagation.Parameters
  /-- Main-ring quarter from the left coupler to the input coupler. -/
  mainQuarterFour : MatchedPropagation.Parameters
  /-- First half of the right side ring. -/
  rightHalfOne : MatchedPropagation.Parameters
  /-- Second half of the right side ring. -/
  rightHalfTwo : MatchedPropagation.Parameters
  /-- First half of the left side ring. -/
  leftHalfOne : MatchedPropagation.Parameters
  /-- Second half of the left side ring. -/
  leftHalfTwo : MatchedPropagation.Parameters

/-- The twelve physical components of the PANDA netlist. -/
inductive Component
  | inputCoupler
  | outputCoupler
  | rightCoupler
  | leftCoupler
  | mainQuarterOne
  | mainQuarterTwo
  | mainQuarterThree
  | mainQuarterFour
  | rightHalfOne
  | rightHalfTwo
  | leftHalfOne
  | leftHalfTwo
  deriving DecidableEq

/-- PANDA component labels form a finite type. -/
instance : Fintype Component where
  elems := {.inputCoupler, .outputCoupler, .rightCoupler, .leftCoupler,
    .mainQuarterOne, .mainQuarterTwo, .mainQuarterThree, .mainQuarterFour,
    .rightHalfOne, .rightHalfTwo, .leftHalfOne, .leftHalfTwo}
  complete component := by cases component <;> simp

/-- The physical-port family owned by each PANDA component. -/
def componentPortFamily : Component → PortModeFamily
  | .inputCoupler => DirectionalCoupler.portFamily Unit
  | .outputCoupler => DirectionalCoupler.portFamily Unit
  | .rightCoupler => DirectionalCoupler.portFamily Unit
  | .leftCoupler => DirectionalCoupler.portFamily Unit
  | .mainQuarterOne => MatchedPropagation.portFamily Unit
  | .mainQuarterTwo => MatchedPropagation.portFamily Unit
  | .mainQuarterThree => MatchedPropagation.portFamily Unit
  | .mainQuarterFour => MatchedPropagation.portFamily Unit
  | .rightHalfOne => MatchedPropagation.portFamily Unit
  | .rightHalfTwo => MatchedPropagation.portFamily Unit
  | .leftHalfOne => MatchedPropagation.portFamily Unit
  | .leftHalfTwo => MatchedPropagation.portFamily Unit

/-- The local N7 scattering matrix selected by each PANDA component. -/
def componentScattering (p : Parameters) :
    (component : Component) → ScatteringMatrix (componentPortFamily component).Channel
  | .inputCoupler => DirectionalCoupler.physicalScattering p.inputCoupler Unit
  | .outputCoupler => DirectionalCoupler.physicalScattering p.outputCoupler Unit
  | .rightCoupler => DirectionalCoupler.physicalScattering p.rightCoupler Unit
  | .leftCoupler => DirectionalCoupler.physicalScattering p.leftCoupler Unit
  | .mainQuarterOne => MatchedPropagation.physicalScattering p.mainQuarterOne Unit
  | .mainQuarterTwo => MatchedPropagation.physicalScattering p.mainQuarterTwo Unit
  | .mainQuarterThree => MatchedPropagation.physicalScattering p.mainQuarterThree Unit
  | .mainQuarterFour => MatchedPropagation.physicalScattering p.mainQuarterFour Unit
  | .rightHalfOne => MatchedPropagation.physicalScattering p.rightHalfOne Unit
  | .rightHalfTwo => MatchedPropagation.physicalScattering p.rightHalfTwo Unit
  | .leftHalfOne => MatchedPropagation.physicalScattering p.leftHalfOne Unit
  | .leftHalfTwo => MatchedPropagation.physicalScattering p.leftHalfTwo Unit

/-- The twelve N7 components before the PANDA wiring is installed. -/
def components (p : Parameters) : ScatteringComponentFamily where
  Component := Component
  portFamily := componentPortFamily
  scattering := componentScattering p

/-! ## B. Physical wiring -/

/-- The fourteen wires closing the three rings while leaving four bus ports external. -/
inductive Connection
  | inputToQuarterOne
  | quarterOneToRight
  | rightToQuarterTwo
  | quarterTwoToOutput
  | outputToQuarterThree
  | quarterThreeToLeft
  | leftToQuarterFour
  | quarterFourToInput
  | rightToHalfOne
  | rightHalfJoin
  | rightHalfTwoToCoupler
  | leftToHalfOne
  | leftHalfJoin
  | leftHalfTwoToCoupler
  deriving DecidableEq

/-- PANDA connection labels form a finite type. -/
instance : Fintype Connection where
  elems := {.inputToQuarterOne, .quarterOneToRight, .rightToQuarterTwo,
    .quarterTwoToOutput, .outputToQuarterThree, .quarterThreeToLeft,
    .leftToQuarterFour, .quarterFourToInput, .rightToHalfOne, .rightHalfJoin,
    .rightHalfTwoToCoupler, .leftToHalfOne, .leftHalfJoin, .leftHalfTwoToCoupler}
  complete connection := by cases connection <;> simp

/-- The proof-carrying PANDA connections in physical ring order. -/
def connections (p : Parameters) :
    PortConnectionFamily (components p).aggregatePortModeFamily Connection where
  connection
    | .inputToQuarterOne =>
        { left := ⟨Component.inputCoupler, DirectionalCoupler.Port.rightSecond⟩
          right := ⟨Component.mainQuarterOne, MatchedPropagation.Port.left⟩
          left_ne_right := by intro h; cases h
          modeEquiv := Equiv.refl Unit }
    | .quarterOneToRight =>
        { left := ⟨Component.mainQuarterOne, MatchedPropagation.Port.right⟩
          right := ⟨Component.rightCoupler, DirectionalCoupler.Port.leftFirst⟩
          left_ne_right := by intro h; cases h
          modeEquiv := Equiv.refl Unit }
    | .rightToQuarterTwo =>
        { left := ⟨Component.rightCoupler, DirectionalCoupler.Port.rightFirst⟩
          right := ⟨Component.mainQuarterTwo, MatchedPropagation.Port.left⟩
          left_ne_right := by intro h; cases h
          modeEquiv := Equiv.refl Unit }
    | .quarterTwoToOutput =>
        { left := ⟨Component.mainQuarterTwo, MatchedPropagation.Port.right⟩
          right := ⟨Component.outputCoupler, DirectionalCoupler.Port.leftFirst⟩
          left_ne_right := by intro h; cases h
          modeEquiv := Equiv.refl Unit }
    | .outputToQuarterThree =>
        { left := ⟨Component.outputCoupler, DirectionalCoupler.Port.rightFirst⟩
          right := ⟨Component.mainQuarterThree, MatchedPropagation.Port.left⟩
          left_ne_right := by intro h; cases h
          modeEquiv := Equiv.refl Unit }
    | .quarterThreeToLeft =>
        { left := ⟨Component.mainQuarterThree, MatchedPropagation.Port.right⟩
          right := ⟨Component.leftCoupler, DirectionalCoupler.Port.leftFirst⟩
          left_ne_right := by intro h; cases h
          modeEquiv := Equiv.refl Unit }
    | .leftToQuarterFour =>
        { left := ⟨Component.leftCoupler, DirectionalCoupler.Port.rightFirst⟩
          right := ⟨Component.mainQuarterFour, MatchedPropagation.Port.left⟩
          left_ne_right := by intro h; cases h
          modeEquiv := Equiv.refl Unit }
    | .quarterFourToInput =>
        { left := ⟨Component.mainQuarterFour, MatchedPropagation.Port.right⟩
          right := ⟨Component.inputCoupler, DirectionalCoupler.Port.leftSecond⟩
          left_ne_right := by intro h; cases h
          modeEquiv := Equiv.refl Unit }
    | .rightToHalfOne =>
        { left := ⟨Component.rightCoupler, DirectionalCoupler.Port.rightSecond⟩
          right := ⟨Component.rightHalfOne, MatchedPropagation.Port.left⟩
          left_ne_right := by intro h; cases h
          modeEquiv := Equiv.refl Unit }
    | .rightHalfJoin =>
        { left := ⟨Component.rightHalfOne, MatchedPropagation.Port.right⟩
          right := ⟨Component.rightHalfTwo, MatchedPropagation.Port.left⟩
          left_ne_right := by intro h; cases h
          modeEquiv := Equiv.refl Unit }
    | .rightHalfTwoToCoupler =>
        { left := ⟨Component.rightHalfTwo, MatchedPropagation.Port.right⟩
          right := ⟨Component.rightCoupler, DirectionalCoupler.Port.leftSecond⟩
          left_ne_right := by intro h; cases h
          modeEquiv := Equiv.refl Unit }
    | .leftToHalfOne =>
        { left := ⟨Component.leftCoupler, DirectionalCoupler.Port.rightSecond⟩
          right := ⟨Component.leftHalfOne, MatchedPropagation.Port.left⟩
          left_ne_right := by intro h; cases h
          modeEquiv := Equiv.refl Unit }
    | .leftHalfJoin =>
        { left := ⟨Component.leftHalfOne, MatchedPropagation.Port.right⟩
          right := ⟨Component.leftHalfTwo, MatchedPropagation.Port.left⟩
          left_ne_right := by intro h; cases h
          modeEquiv := Equiv.refl Unit }
    | .leftHalfTwoToCoupler =>
        { left := ⟨Component.leftHalfTwo, MatchedPropagation.Port.right⟩
          right := ⟨Component.leftCoupler, DirectionalCoupler.Port.leftSecond⟩
          left_ne_right := by intro h; cases h
          modeEquiv := Equiv.refl Unit }
  endpointPort_injective := by
    rintro ⟨firstConnection, firstEnd⟩ ⟨secondConnection, secondEnd⟩ hPort
    cases firstConnection <;> cases firstEnd <;>
      cases secondConnection <;> cases secondEnd
    all_goals first | rfl | cases hPort

/-- The explicit four-coupler, eight-delay PANDA flat netlist. -/
def netlist (p : Parameters) : FlatNetlist where
  components := components p
  Connection := Connection
  connections := connections p

/-! ## C. Finite channel instances -/

/-- Every local PANDA component channel family is finite. -/
noncomputable instance localChannelFintype (component : Component) :
    Fintype (componentPortFamily component).Channel := by
  cases component
  all_goals first
    | exact DirectionalCoupler.channelFintype
    | exact MatchedPropagation.channelFintype

/-- Every local PANDA component channel family has decidable equality. -/
noncomputable instance localChannelDecidableEq (component : Component) :
    DecidableEq (componentPortFamily component).Channel := by
  cases component
  all_goals first
    | exact DirectionalCoupler.channelDecidableEq
    | exact MatchedPropagation.channelDecidableEq

/-- Projected local PANDA component channels remain finite. -/
noncomputable instance componentsLocalChannelFintype (p : Parameters)
    (component : (components p).Component) :
    Fintype ((components p).portFamily component).Channel := by
  change Fintype (componentPortFamily component).Channel
  exact localChannelFintype component

/-- Projected local PANDA component channels retain decidable equality. -/
noncomputable instance componentsLocalChannelDecidableEq (p : Parameters)
    (component : (components p).Component) :
    DecidableEq ((components p).portFamily component).Channel := by
  change DecidableEq (componentPortFamily component).Channel
  exact localChannelDecidableEq component

/-- Projected PANDA component labels remain finite. -/
noncomputable instance netlistComponentFintype (p : Parameters) :
    Fintype (netlist p).components.Component := by
  change Fintype Component
  infer_instance

/-- Projected PANDA component labels retain decidable equality. -/
noncomputable instance netlistComponentDecidableEq (p : Parameters) :
    DecidableEq (netlist p).components.Component := by
  change DecidableEq Component
  infer_instance

/-- Every local channel family exposed by the PANDA netlist is finite. -/
noncomputable instance netlistLocalChannelFintype (p : Parameters)
    (component : (netlist p).components.Component) :
    Fintype ((netlist p).components.portFamily component).Channel := by
  change Fintype (componentPortFamily component).Channel
  exact localChannelFintype component

/-- Every local PANDA netlist channel family has decidable equality. -/
noncomputable instance netlistLocalChannelDecidableEq (p : Parameters)
    (component : (netlist p).components.Component) :
    DecidableEq ((netlist p).components.portFamily component).Channel := by
  change DecidableEq (componentPortFamily component).Channel
  exact localChannelDecidableEq component

/-- Aggregate PANDA channels are finite. -/
noncomputable instance channelFintype (p : Parameters) : Fintype (netlist p).Channel := by
  letI : Fintype (components p).IndexedChannel := by
    change Fintype (Σ component : Component, (componentPortFamily component).Channel)
    infer_instance
  exact Fintype.ofEquiv (components p).IndexedChannel (components p).channelEquiv

/-- Aggregate PANDA channels have decidable equality. -/
noncomputable instance channelDecidableEq (p : Parameters) :
    DecidableEq (netlist p).Channel := Classical.decEq _

/-- Internally connected PANDA channels are finite. -/
noncomputable instance connectionLocalChannelFintype (p : Parameters)
    (connection : Connection) :
    Fintype ((connections p).connection connection).LocalChannel := by
  cases connection <;> change Fintype (Unit ⊕ Unit) <;> infer_instance

/-- Internally connected PANDA channels are finite. -/
noncomputable instance connectedChannelFintype (p : Parameters) :
    Fintype (netlist p).ConnectedChannel := by
  change Fintype (connections p).Channel
  infer_instance

/-- Internally connected PANDA channels have decidable equality. -/
noncomputable instance connectedChannelDecidableEq (p : Parameters) :
    DecidableEq (netlist p).ConnectedChannel := Classical.decEq _

/-- External PANDA channels are finite. -/
noncomputable instance externalChannelFintype (p : Parameters) :
    Fintype (netlist p).ExternalChannel := Fintype.ofFinite _

/-! ## D. External channels -/

/-- The aggregate channel owned by a selected component port. -/
def componentChannel (p : Parameters) (component : Component)
    (channel : (componentPortFamily component).Channel) : (netlist p).Channel :=
  (netlist p).components.componentChannelEmbedding component channel

/-- The input coupler's left first port is not internally connected. -/
lemma input_not_connected (p : Parameters) :
    componentChannel p .inputCoupler
        ⟨DirectionalCoupler.Port.leftFirst, ()⟩ ∉
      Set.range (netlist p).connections.channelEmbedding := by
  rintro ⟨⟨connection, channel⟩, hChannel⟩
  cases connection <;> rcases channel with mode | mode <;> cases mode
  all_goals cases hChannel

/-- The input coupler's right first port is not internally connected. -/
lemma through_not_connected (p : Parameters) :
    componentChannel p .inputCoupler
        ⟨DirectionalCoupler.Port.rightFirst, ()⟩ ∉
      Set.range (netlist p).connections.channelEmbedding := by
  rintro ⟨⟨connection, channel⟩, hChannel⟩
  cases connection <;> rcases channel with mode | mode <;> cases mode
  all_goals cases hChannel

/-- The output coupler's left second port is not internally connected. -/
lemma add_not_connected (p : Parameters) :
    componentChannel p .outputCoupler
        ⟨DirectionalCoupler.Port.leftSecond, ()⟩ ∉
      Set.range (netlist p).connections.channelEmbedding := by
  rintro ⟨⟨connection, channel⟩, hChannel⟩
  cases connection <;> rcases channel with mode | mode <;> cases mode
  all_goals cases hChannel

/-- The output coupler's right second port is not internally connected. -/
lemma drop_not_connected (p : Parameters) :
    componentChannel p .outputCoupler
        ⟨DirectionalCoupler.Port.rightSecond, ()⟩ ∉
      Set.range (netlist p).connections.channelEmbedding := by
  rintro ⟨⟨connection, channel⟩, hChannel⟩
  cases connection <;> rcases channel with mode | mode <;> cases mode
  all_goals cases hChannel

/-- The packaged input channel. -/
def inputChannel (p : Parameters) : (netlist p).ExternalChannel :=
  ⟨componentChannel p .inputCoupler ⟨DirectionalCoupler.Port.leftFirst, ()⟩,
    input_not_connected p⟩

/-- The packaged through-output channel. -/
def throughChannel (p : Parameters) : (netlist p).ExternalChannel :=
  ⟨componentChannel p .inputCoupler ⟨DirectionalCoupler.Port.rightFirst, ()⟩,
    through_not_connected p⟩

/-- The packaged add-input channel. -/
def addChannel (p : Parameters) : (netlist p).ExternalChannel :=
  ⟨componentChannel p .outputCoupler ⟨DirectionalCoupler.Port.leftSecond, ()⟩,
    add_not_connected p⟩

/-- The packaged drop-output channel. -/
def dropChannel (p : Parameters) : (netlist p).ExternalChannel :=
  ⟨componentChannel p .outputCoupler ⟨DirectionalCoupler.Port.rightSecond, ()⟩,
    drop_not_connected p⟩

/-- The input channel differs from the add channel. -/
lemma inputChannel_ne_addChannel (p : Parameters) : inputChannel p ≠ addChannel p := by
  intro hChannel
  have hValue := congrArg Subtype.val hChannel
  cases hValue

/-- The input channel differs from the through channel. -/
lemma inputChannel_ne_throughChannel (p : Parameters) :
    inputChannel p ≠ throughChannel p := by
  intro hChannel
  have hValue := congrArg Subtype.val hChannel
  cases hValue

/-- The input channel differs from the drop channel. -/
lemma inputChannel_ne_dropChannel (p : Parameters) : inputChannel p ≠ dropChannel p := by
  intro hChannel
  have hValue := congrArg Subtype.val hChannel
  cases hValue

/-- A coherent source supplied only at the input port. -/
def inputAmplitude (p : Parameters) (amplitude : ℂ) :
    ModeAmplitude (netlist p).ExternalIncident :=
  PiLp.single 2 (Incident.mk (inputChannel p)) amplitude

/-- The coherent source has its supplied value at the input port. -/
@[simp]
lemma inputAmplitude_apply_input (p : Parameters) (amplitude : ℂ) :
    inputAmplitude p amplitude (Incident.mk (inputChannel p)) = amplitude := by
  simp [inputAmplitude]

/-- The source-only excitation vanishes at the add port. -/
@[simp]
lemma inputAmplitude_apply_add (p : Parameters) (amplitude : ℂ) :
    inputAmplitude p amplitude (Incident.mk (addChannel p)) = 0 := by
  rw [inputAmplitude]
  simp [inputChannel_ne_addChannel p]

/-- The source-only excitation vanishes at the through port. -/
@[simp]
lemma inputAmplitude_apply_through (p : Parameters) (amplitude : ℂ) :
    inputAmplitude p amplitude (Incident.mk (throughChannel p)) = 0 := by
  rw [inputAmplitude]
  simp [inputChannel_ne_throughChannel p]

/-- The source-only excitation vanishes at the drop port. -/
@[simp]
lemma inputAmplitude_apply_drop (p : Parameters) (amplitude : ℂ) :
    inputAmplitude p amplitude (Incident.mk (dropChannel p)) = 0 := by
  rw [inputAmplitude]
  simp [inputChannel_ne_dropChannel p]

end Panda

end

end Optics
