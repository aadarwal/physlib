/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.HierarchicalReuse

/-!
# Regression tests for three-stage hierarchical reuse

## i. Overview

Four two-port algebraic components form a directed chain with gains `2`, `3`, `5`, and `7`.
Three connection stages join consecutive component boundaries. The same concrete incident and
outgoing state is checked directly against both parenthesized connection families, with nonzero
values on every forward cross-component wire and final response `210`.

A hostile boundary transport swaps the third-stage source port with the external drive port. Its
raw mate equation forces zero at a coordinate where the canonical state has value `30`, so the
fixture rejects a subsystem-boundary, port-lift, associator-branch, or cascade-index mistake.

## ii. Key results

- `reuseRegression_mem_both_parenthesizations`: the independently expanded raw solutions agree.
- `reuseRegression_cross_amplitudes_nonzero`: all three cross-component amplitudes are nonzero.
- `reuseRegression_hostile_incidentAssembly_ne`: the hostile transported boundary is rejected.

## iii. Table of contents

- A. Four algebraic component operators
- B. Three connection stages
- C. The two parenthesized families
- D. The hand-expanded state
- E. Raw equations for the right parenthesization
- F. Raw equations for the left parenthesization
- G. A hostile boundary transport

## iv. References

This is the dynamic N-08 regression for the reuse machinery in `goal.md` lines 2098--2102, with
the S-08 lattice hierarchy as its downstream canary. These supplied coefficients are not claimed
to be passive, lossless, reciprocal, stable, causal, normalized, or physically realized. No
well-posedness or electromagnetic-power statement is made.
-/

@[expose] public section

namespace Optics

noncomputable section

/-!

## A. Four algebraic component operators

-/

/-- The four ordered component sites in the three-stage regression chain. -/
inductive ReuseRegressionComponent
  | first
  | second
  | third
  | fourth
  deriving DecidableEq

/-- The regression chain has exactly four component sites. -/
instance : Fintype ReuseRegressionComponent where
  elems := {.first, .second, .third, .fourth}
  complete := fun component => by cases component <;> decide

/-- Every component has a west port (`false`) and east port (`true`), each with one mode. -/
abbrev reuseRegressionPortModeFamily : PortModeFamily where
  Port := ReuseRegressionComponent × Bool
  Mode := fun _ => Unit

/-- The ambient channel type of the four-component fixture. -/
abbrev ReuseRegressionChannel := reuseRegressionPortModeFamily.Channel

/-- The block-diagonal scattering matrix. Each nonzero entry crosses from the west incident port
to the east outgoing port of the same component. -/
def reuseRegressionScattering : ScatteringMatrix ReuseRegressionChannel where
  toModeTransform := fun output input =>
    match output.1.1, output.1.2, input.1.1, input.1.2 with
    | .first, true, .first, false => 2
    | .second, true, .second, false => 3
    | .third, true, .third, false => 5
    | .fourth, true, .fourth, false => 7
    | _, _, _, _ => 0

/-- The oriented incident-to-outgoing operator supplied by the fixture scattering matrix. -/
def reuseRegressionComponentOperator :
    ModeTransform (Incident ReuseRegressionChannel) (Outgoing ReuseRegressionChannel) :=
  reuseRegressionScattering.toOrientedModeTransform

/-- The relational graph of the supplied four-component operator. -/
def reuseRegressionComponentBehavior :
    LinearBehavior (Incident ReuseRegressionChannel) (Outgoing ReuseRegressionChannel) :=
  reuseRegressionComponentOperator.toBehavior

/-!

## B. Three connection stages

-/

/-- The first stage connects the first component's east port to the second component's west
port. -/
abbrev reuseRegressionFirstConnection : PortConnection reuseRegressionPortModeFamily where
  left := (.first, true)
  right := (.second, false)
  left_ne_right := by
    intro hPort
    exact ReuseRegressionComponent.noConfusion (congrArg Prod.fst hPort)
  modeEquiv := Equiv.refl Unit

/-- The first singleton connection family. -/
abbrev reuseRegressionFirstFamily :
    PortConnectionFamily reuseRegressionPortModeFamily Unit where
  connection _ := reuseRegressionFirstConnection
  endpointPort_injective := by
    rintro ⟨firstIndex, firstEnd⟩ ⟨secondIndex, secondEnd⟩ hPort
    cases firstIndex
    cases secondIndex
    cases firstEnd <;> cases secondEnd
    · rfl
    · exact ReuseRegressionComponent.noConfusion (congrArg Prod.fst hPort)
    · exact ReuseRegressionComponent.noConfusion (congrArg Prod.fst hPort)
    · rfl

/-- The second component's east port is external after the first stage. -/
lemma reuseRegression_secondEast_unconnected_first :
    ((.second, true) : reuseRegressionPortModeFamily.Port) ∉
      Set.range reuseRegressionFirstFamily.endpointEmbedding := by
  rintro ⟨⟨index, endpoint⟩, hPort⟩
  cases index
  cases endpoint <;>
    exact ReuseRegressionComponent.noConfusion (congrArg Prod.fst hPort)

/-- The third component's west port is external after the first stage. -/
lemma reuseRegression_thirdWest_unconnected_first :
    ((.third, false) : reuseRegressionPortModeFamily.Port) ∉
      Set.range reuseRegressionFirstFamily.endpointEmbedding := by
  rintro ⟨⟨index, endpoint⟩, hPort⟩
  cases index
  cases endpoint <;>
    exact ReuseRegressionComponent.noConfusion (congrArg Prod.fst hPort)

/-- The external drive port is external after the first stage. -/
lemma reuseRegression_firstWest_unconnected_first :
    ((.first, false) : reuseRegressionPortModeFamily.Port) ∉
      Set.range reuseRegressionFirstFamily.endpointEmbedding := by
  rintro ⟨⟨index, endpoint⟩, hPort⟩
  cases index
  cases endpoint
  · exact Bool.noConfusion (congrArg Prod.snd hPort)
  · exact ReuseRegressionComponent.noConfusion (congrArg Prod.fst hPort)

/-- The second-stage left boundary port. -/
abbrev reuseRegressionSecondEastBoundary :
    reuseRegressionFirstFamily.externalPortModeFamily.Port :=
  ⟨(.second, true), reuseRegression_secondEast_unconnected_first⟩

/-- The second-stage right boundary port. -/
abbrev reuseRegressionThirdWestBoundary :
    reuseRegressionFirstFamily.externalPortModeFamily.Port :=
  ⟨(.third, false), reuseRegression_thirdWest_unconnected_first⟩

/-- The drive port presented on the first-stage boundary. -/
abbrev reuseRegressionFirstWestBoundary :
    reuseRegressionFirstFamily.externalPortModeFamily.Port :=
  ⟨(.first, false), reuseRegression_firstWest_unconnected_first⟩

/-- The second stage connects the second component's east boundary to the third component's west
boundary. -/
abbrev reuseRegressionSecondConnection :
    PortConnection reuseRegressionFirstFamily.externalPortModeFamily where
  left := reuseRegressionSecondEastBoundary
  right := reuseRegressionThirdWestBoundary
  left_ne_right := by
    intro hPort
    exact ReuseRegressionComponent.noConfusion
      (congrArg (fun port => port.1.1) hPort)
  modeEquiv := Equiv.refl Unit

/-- The second singleton connection family. -/
abbrev reuseRegressionSecondFamily :
    PortConnectionFamily reuseRegressionFirstFamily.externalPortModeFamily Unit where
  connection _ := reuseRegressionSecondConnection
  endpointPort_injective := by
    rintro ⟨firstIndex, firstEnd⟩ ⟨secondIndex, secondEnd⟩ hPort
    cases firstIndex
    cases secondIndex
    cases firstEnd <;> cases secondEnd
    · rfl
    · exact ReuseRegressionComponent.noConfusion
        (congrArg (fun port => port.1.1) hPort)
    · exact ReuseRegressionComponent.noConfusion
        (congrArg (fun port => port.1.1) hPort)
    · rfl

/-- The third component's east port is external after the first two stages. -/
lemma reuseRegression_thirdEast_unconnected_second :
    (⟨(.third, true), by
        rintro ⟨⟨index, endpoint⟩, hPort⟩
        cases index
        cases endpoint <;>
          exact ReuseRegressionComponent.noConfusion (congrArg Prod.fst hPort)⟩ :
      reuseRegressionFirstFamily.externalPortModeFamily.Port) ∉
        Set.range reuseRegressionSecondFamily.endpointEmbedding := by
  rintro ⟨⟨index, endpoint⟩, hPort⟩
  cases index
  cases endpoint <;>
    exact ReuseRegressionComponent.noConfusion
      (congrArg (fun port => port.1.1) hPort)

/-- The fourth component's west port is external after the first two stages. -/
lemma reuseRegression_fourthWest_unconnected_second :
    (⟨(.fourth, false), by
        rintro ⟨⟨index, endpoint⟩, hPort⟩
        cases index
        cases endpoint <;>
          exact ReuseRegressionComponent.noConfusion (congrArg Prod.fst hPort)⟩ :
      reuseRegressionFirstFamily.externalPortModeFamily.Port) ∉
        Set.range reuseRegressionSecondFamily.endpointEmbedding := by
  rintro ⟨⟨index, endpoint⟩, hPort⟩
  cases index
  cases endpoint <;>
    exact ReuseRegressionComponent.noConfusion
      (congrArg (fun port => port.1.1) hPort)

/-- The drive port remains external after the second stage. -/
lemma reuseRegression_firstWest_unconnected_second :
    reuseRegressionFirstWestBoundary ∉
      Set.range reuseRegressionSecondFamily.endpointEmbedding := by
  rintro ⟨⟨index, endpoint⟩, hPort⟩
  cases index
  cases endpoint
  · exact ReuseRegressionComponent.noConfusion
      (congrArg (fun port => port.1.1) hPort)
  · exact ReuseRegressionComponent.noConfusion
      (congrArg (fun port => port.1.1) hPort)

/-- The third-stage left boundary port. -/
abbrev reuseRegressionThirdEastBoundary :
    reuseRegressionSecondFamily.externalPortModeFamily.Port :=
  ⟨⟨(.third, true), by
      rintro ⟨⟨index, endpoint⟩, hPort⟩
      cases index
      cases endpoint <;>
        exact ReuseRegressionComponent.noConfusion (congrArg Prod.fst hPort)⟩,
    reuseRegression_thirdEast_unconnected_second⟩

/-- The third-stage right boundary port. -/
abbrev reuseRegressionFourthWestBoundary :
    reuseRegressionSecondFamily.externalPortModeFamily.Port :=
  ⟨⟨(.fourth, false), by
      rintro ⟨⟨index, endpoint⟩, hPort⟩
      cases index
      cases endpoint <;>
        exact ReuseRegressionComponent.noConfusion (congrArg Prod.fst hPort)⟩,
    reuseRegression_fourthWest_unconnected_second⟩

/-- The drive port presented on the second-stage boundary. -/
abbrev reuseRegressionFirstWestSecondBoundary :
    reuseRegressionSecondFamily.externalPortModeFamily.Port :=
  ⟨reuseRegressionFirstWestBoundary, reuseRegression_firstWest_unconnected_second⟩

/-- The third stage connects the third component's east boundary to the fourth component's west
boundary. -/
abbrev reuseRegressionThirdConnection :
    PortConnection reuseRegressionSecondFamily.externalPortModeFamily where
  left := reuseRegressionThirdEastBoundary
  right := reuseRegressionFourthWestBoundary
  left_ne_right := by
    intro hPort
    exact ReuseRegressionComponent.noConfusion
      (congrArg (fun port => port.1.1.1) hPort)
  modeEquiv := Equiv.refl Unit

/-- The third singleton connection family. -/
abbrev reuseRegressionThirdFamily :
    PortConnectionFamily reuseRegressionSecondFamily.externalPortModeFamily Unit where
  connection _ := reuseRegressionThirdConnection
  endpointPort_injective := by
    rintro ⟨firstIndex, firstEnd⟩ ⟨secondIndex, secondEnd⟩ hPort
    cases firstIndex
    cases secondIndex
    cases firstEnd <;> cases secondEnd
    · rfl
    · exact ReuseRegressionComponent.noConfusion
        (congrArg (fun port => port.1.1.1) hPort)
    · exact ReuseRegressionComponent.noConfusion
        (congrArg (fun port => port.1.1.1) hPort)
    · rfl

/-!

## C. The two parenthesized families

-/

/-- The right-associated concrete connection family. -/
abbrev reuseRegressionRightFamily :
    PortConnectionFamily reuseRegressionPortModeFamily (Unit ⊕ (Unit ⊕ Unit)) :=
  reuseRegressionFirstFamily.append
    (reuseRegressionSecondFamily.append reuseRegressionThirdFamily)

/-- The left-associated concrete connection family after correct third-boundary transport. -/
abbrev reuseRegressionLeftFamily :
    PortConnectionFamily reuseRegressionPortModeFamily ((Unit ⊕ Unit) ⊕ Unit) :=
  (reuseRegressionFirstFamily.append reuseRegressionSecondFamily).append
    (reuseRegressionThirdFamily.transport
      (reuseRegressionFirstFamily.prependExternalPortModeFamilyEquiv
        reuseRegressionSecondFamily))

/-- The ambient fixture channels are finite. -/
local instance reuseRegressionChannelFintype : Fintype ReuseRegressionChannel :=
  Fintype.ofFinite _

/-- The right-associated connected channels are finite. -/
local instance reuseRegressionRightChannelFintype :
    Fintype reuseRegressionRightFamily.Channel := Fintype.ofFinite _

/-- The left-associated connected channels are finite. -/
local instance reuseRegressionLeftChannelFintype :
    Fintype reuseRegressionLeftFamily.Channel := Fintype.ofFinite _

/-- The right-associated external channels are finite. -/
local instance reuseRegressionRightExternalFintype :
    Fintype reuseRegressionRightFamily.ExternalChannel := Fintype.ofFinite _

/-- The left-associated external channels are finite. -/
local instance reuseRegressionLeftExternalFintype :
    Fintype reuseRegressionLeftFamily.ExternalChannel := Fintype.ofFinite _

/-- Classical equality on ambient channels for raw assembly. -/
local instance reuseRegressionChannelDecidableEq : DecidableEq ReuseRegressionChannel :=
  Classical.decEq _

/-- Classical equality on right-associated connected channels. -/
local instance reuseRegressionRightChannelDecidableEq :
    DecidableEq reuseRegressionRightFamily.Channel := Classical.decEq _

/-- Classical equality on left-associated connected channels. -/
local instance reuseRegressionLeftChannelDecidableEq :
    DecidableEq reuseRegressionLeftFamily.Channel := Classical.decEq _

/-!

## D. The hand-expanded state

-/

/-- The hand-expanded ambient incident state. Its west-port values are `1`, `2`, `6`, and `30`.
-/
def reuseRegressionIncident : ModeAmplitude (Incident ReuseRegressionChannel) :=
  WithLp.toLp 2 fun endpoint =>
    match endpoint.channel.1.1, endpoint.channel.1.2 with
    | .first, false => 1
    | .second, false => 2
    | .third, false => 6
    | .fourth, false => 30
    | _, _ => 0

/-- The hand-expanded ambient outgoing state. Its east-port values are `2`, `6`, `30`, and
`210`. -/
def reuseRegressionOutgoing : ModeAmplitude (Outgoing ReuseRegressionChannel) :=
  WithLp.toLp 2 fun endpoint =>
    match endpoint.channel.1.1, endpoint.channel.1.2 with
    | .first, true => 2
    | .second, true => 6
    | .third, true => 30
    | .fourth, true => 210
    | _, _ => 0

/-- Restrict the hand-expanded ambient incident state to any family's external input labels. -/
def reuseRegressionExternalInput {index : Type*}
    (family : PortConnectionFamily reuseRegressionPortModeFamily index) :
    ModeAmplitude (Incident family.ExternalChannel) :=
  WithLp.toLp 2 fun endpoint =>
    reuseRegressionIncident (Incident.mk endpoint.channel.1)

/-- Restrict the hand-expanded ambient outgoing state to any family's external output labels. -/
def reuseRegressionExternalOutput {index : Type*}
    (family : PortConnectionFamily reuseRegressionPortModeFamily index) :
    ModeAmplitude (Outgoing family.ExternalChannel) :=
  WithLp.toLp 2 fun endpoint =>
    reuseRegressionOutgoing (Outgoing.mk endpoint.channel.1)

/-- The hand-expanded incident and outgoing amplitudes satisfy the supplied component operator
before any wiring equation is used. -/
lemma reuseRegression_mem_componentBehavior :
    (reuseRegressionIncident, reuseRegressionOutgoing) ∈
      reuseRegressionComponentBehavior := by
  classical
  rw [reuseRegressionComponentBehavior, ModeTransform.mem_toBehavior_iff_toLinearMap,
    reuseRegressionComponentOperator,
    ScatteringMatrix.toLinearMap_toOrientedModeTransform]
  apply WithLp.ofLp_injective 2
  funext endpoint
  rcases endpoint with ⟨⟨⟨component, port⟩, mode⟩⟩
  rw [ModeAmplitude.reindex_apply]
  simp only [Equiv.symm_symm, Outgoing.channelEquiv_apply]
  rw [Matrix.ofLp_toLpLin, Matrix.toLin'_apply]
  cases component <;> cases port <;> cases mode <;>
    simp [ModeAmplitude.reindex_apply, Matrix.mulVec, dotProduct, Fintype.sum_sigma,
      reuseRegressionScattering, reuseRegressionIncident, reuseRegressionOutgoing]

/-- The three forward cross-component amplitudes are all nonzero and pairwise distinguish the
three cascade stages. -/
lemma reuseRegression_cross_amplitudes_nonzero :
    reuseRegressionOutgoing
          (Outgoing.mk ⟨(.first, true), ()⟩) ≠ 0 ∧
      reuseRegressionOutgoing
          (Outgoing.mk ⟨(.second, true), ()⟩) ≠ 0 ∧
      reuseRegressionOutgoing
          (Outgoing.mk ⟨(.third, true), ()⟩) ≠ 0 := by
  norm_num [reuseRegressionOutgoing]

/-!

## E. Raw equations for the right parenthesization

-/

/-- The first west channel is structurally external in the right parenthesization. -/
lemma reuseRegression_right_firstWest_external :
    (⟨(.first, false), ()⟩ : ReuseRegressionChannel) ∉
      Set.range reuseRegressionRightFamily.channelEmbedding := by
  rintro ⟨⟨connectionIndex, localChannel⟩, hChannel⟩
  rcases connectionIndex with firstIndex | laterIndex
  · cases firstIndex
    rcases localChannel with mode | mode <;> cases mode
    · exact Bool.noConfusion (congrArg (fun channel => channel.1.2) hChannel)
    · exact ReuseRegressionComponent.noConfusion
        (congrArg (fun channel => channel.1.1) hChannel)
  · rcases laterIndex with secondIndex | thirdIndex
    · cases secondIndex
      rcases localChannel with mode | mode <;> cases mode <;>
        exact ReuseRegressionComponent.noConfusion
          (congrArg (fun channel => channel.1.1) hChannel)
    · cases thirdIndex
      rcases localChannel with mode | mode <;> cases mode <;>
        exact ReuseRegressionComponent.noConfusion
          (congrArg (fun channel => channel.1.1) hChannel)

/-- The fourth east channel is structurally external in the right parenthesization. -/
lemma reuseRegression_right_fourthEast_external :
    (⟨(.fourth, true), ()⟩ : ReuseRegressionChannel) ∉
      Set.range reuseRegressionRightFamily.channelEmbedding := by
  rintro ⟨⟨connectionIndex, localChannel⟩, hChannel⟩
  rcases connectionIndex with firstIndex | laterIndex
  · cases firstIndex
    rcases localChannel with mode | mode <;> cases mode <;>
      exact ReuseRegressionComponent.noConfusion
        (congrArg (fun channel => channel.1.1) hChannel)
  · rcases laterIndex with secondIndex | thirdIndex
    · cases secondIndex
      rcases localChannel with mode | mode <;> cases mode <;>
        exact ReuseRegressionComponent.noConfusion
          (congrArg (fun channel => channel.1.1) hChannel)
    · cases thirdIndex
      rcases localChannel with mode | mode <;> cases mode
      · exact ReuseRegressionComponent.noConfusion
          (congrArg (fun channel => channel.1.1) hChannel)
      · exact Bool.noConfusion (congrArg (fun channel => channel.1.2) hChannel)

/-- The right-associated incident assembly satisfies all six connected mate equations and both
external injection equations. -/
lemma reuseRegression_right_incidentAssembly :
    reuseRegressionIncident =
      reuseRegressionRightFamily.incidentAssembly reuseRegressionOutgoing
        (reuseRegressionExternalInput reuseRegressionRightFamily) := by
  classical
  apply WithLp.ofLp_injective 2
  funext endpoint
  rcases endpoint with ⟨⟨⟨component, port⟩, mode⟩⟩
  cases component <;> cases port <;> cases mode
  · let external : reuseRegressionRightFamily.ExternalChannel :=
      ⟨⟨(.first, false), ()⟩, reuseRegression_right_firstWest_external⟩
    change reuseRegressionIncident (Incident.mk external.1) = _
    rw [reuseRegressionRightFamily.incidentAssembly_apply_external]
    rfl
  · rw [show (⟨(.first, true), ()⟩ : ReuseRegressionChannel) =
        reuseRegressionRightFamily.channelEmbedding
          ⟨Sum.inl (), Sum.inl ()⟩ from rfl,
      reuseRegressionRightFamily.incidentAssembly_apply_connected_channel]
    rfl
  · rw [show (⟨(.second, false), ()⟩ : ReuseRegressionChannel) =
        reuseRegressionRightFamily.channelEmbedding
          ⟨Sum.inl (), Sum.inr ()⟩ from rfl,
      reuseRegressionRightFamily.incidentAssembly_apply_connected_channel]
    rfl
  · rw [show (⟨(.second, true), ()⟩ : ReuseRegressionChannel) =
        reuseRegressionRightFamily.channelEmbedding
          ⟨Sum.inr (Sum.inl ()), Sum.inl ()⟩ from rfl,
      reuseRegressionRightFamily.incidentAssembly_apply_connected_channel]
    rfl
  · rw [show (⟨(.third, false), ()⟩ : ReuseRegressionChannel) =
        reuseRegressionRightFamily.channelEmbedding
          ⟨Sum.inr (Sum.inl ()), Sum.inr ()⟩ from rfl,
      reuseRegressionRightFamily.incidentAssembly_apply_connected_channel]
    rfl
  · rw [show (⟨(.third, true), ()⟩ : ReuseRegressionChannel) =
        reuseRegressionRightFamily.channelEmbedding
          ⟨Sum.inr (Sum.inr ()), Sum.inl ()⟩ from rfl,
      reuseRegressionRightFamily.incidentAssembly_apply_connected_channel]
    rfl
  · rw [show (⟨(.fourth, false), ()⟩ : ReuseRegressionChannel) =
        reuseRegressionRightFamily.channelEmbedding
          ⟨Sum.inr (Sum.inr ()), Sum.inr ()⟩ from rfl,
      reuseRegressionRightFamily.incidentAssembly_apply_connected_channel]
    rfl
  · let external : reuseRegressionRightFamily.ExternalChannel :=
      ⟨⟨(.fourth, true), ()⟩, reuseRegression_right_fourthEast_external⟩
    change reuseRegressionIncident (Incident.mk external.1) = _
    rw [reuseRegressionRightFamily.incidentAssembly_apply_external]
    rfl

/-- Right-associated external readout is the direct restriction of the hand-expanded outgoing
state. -/
lemma reuseRegression_right_outputReadout :
    reuseRegressionExternalOutput reuseRegressionRightFamily =
      reuseRegressionRightFamily.externalOutgoingReadout.toLinearMap
        reuseRegressionOutgoing := by
  classical
  rw [PortConnectionFamily.externalOutgoingReadout_apply]
  apply WithLp.ofLp_injective 2
  funext endpoint
  rw [ModeAmplitude.restrictEmbedding_apply]
  rfl

/-- The right-associated family admits the hand-expanded raw solution. -/
lemma reuseRegression_mem_right :
    (reuseRegressionExternalInput reuseRegressionRightFamily,
        reuseRegressionExternalOutput reuseRegressionRightFamily) ∈
      reuseRegressionRightFamily.closeBehavior reuseRegressionComponentBehavior := by
  classical
  rw [PortConnectionFamily.mem_closeBehavior_iff]
  exact ⟨reuseRegressionIncident, reuseRegressionOutgoing,
    reuseRegression_mem_componentBehavior,
    reuseRegression_right_incidentAssembly,
    reuseRegression_right_outputReadout⟩

/-!

## F. Raw equations for the left parenthesization

-/

end


end Optics
