/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.FlatNetlistElimination
public import Physlib.Optics.Network.TwoPortSeriesNetlistCoordinates

/-!
# External coordinates of the canonical two-port series netlist

## i. Overview

The canonical two-device series netlist exposes exactly the first component's left channels and
the second component's right channels. This file packages that fact as a channel equivalence.

## ii. Key results

- `TwoPortSeriesNetlist.leftExternalChannel`: the exposed first-component channel.
- `TwoPortSeriesNetlist.rightExternalChannel`: the exposed second-component channel.
- `TwoPortSeriesNetlist.externalChannelEquiv`: external channels equal the outer channel sum.

## iii. Table of contents

- A. External-channel coordinates

## iv. References

This typed coordinate bridge is Physlib-original; no external source is used here.

-/

@[expose] public section

namespace Optics

noncomputable section

universe u

namespace TwoPortSeriesNetlist

variable {left middle right : Type u}

/-!

## A. External-channel coordinates

-/

/-- The exposed left channel of the first component. -/
def leftExternalChannel (first : ScatteringMatrix (left ⊕ middle))
    (second : ScatteringMatrix (middle ⊕ right)) (mode : left) :
    (netlist first second).Channel :=
  ⟨⟨false, Port.left⟩, mode⟩

/-- The exposed right channel of the second component. -/
def rightExternalChannel (first : ScatteringMatrix (left ⊕ middle))
    (second : ScatteringMatrix (middle ⊕ right)) (mode : right) :
    (netlist first second).Channel :=
  ⟨⟨true, Port.right⟩, mode⟩

/-- Forget component ownership while retaining a channel's local left/right port tag. -/
private def localPort (first : ScatteringMatrix (left ⊕ middle))
    (second : ScatteringMatrix (middle ⊕ right))
    (channel : (netlist first second).Channel) : Port :=
  match channel with
  | ⟨⟨false, port⟩, _⟩ => port
  | ⟨⟨true, port⟩, _⟩ => port

/-- A first-component left channel is not selected by the middle connection. -/
lemma leftExternalChannel_not_mem_range (first : ScatteringMatrix (left ⊕ middle))
    (second : ScatteringMatrix (middle ⊕ right)) (mode : left) :
    leftExternalChannel first second mode ∉
      Set.range (connections first second).channelEmbedding := by
  rintro ⟨⟨index, connected⟩, equality⟩
  cases index
  rcases connected with middleMode | middleMode
  · exact Port.noConfusion (congrArg (localPort first second) equality)
  · exact Bool.noConfusion (congrArg (fun channel => channel.1.1) equality)

/-- A second-component right channel is not selected by the middle connection. -/
lemma rightExternalChannel_not_mem_range (first : ScatteringMatrix (left ⊕ middle))
    (second : ScatteringMatrix (middle ⊕ right)) (mode : right) :
    rightExternalChannel first second mode ∉
      Set.range (connections first second).channelEmbedding := by
  rintro ⟨⟨index, connected⟩, equality⟩
  cases index
  rcases connected with middleMode | middleMode
  · exact Bool.noConfusion (congrArg (fun channel => channel.1.1) equality)
  · exact Port.noConfusion (congrArg (localPort first second) equality)

/-- The external channels of the series netlist are exactly the outer left and right channels. -/
def externalChannelEquiv (first : ScatteringMatrix (left ⊕ middle))
    (second : ScatteringMatrix (middle ⊕ right)) :
    left ⊕ right ≃ (netlist first second).ExternalChannel where
  toFun
    | Sum.inl mode =>
        ⟨leftExternalChannel first second mode,
          leftExternalChannel_not_mem_range first second mode⟩
    | Sum.inr mode =>
        ⟨rightExternalChannel first second mode,
          rightExternalChannel_not_mem_range first second mode⟩
  invFun
    | ⟨⟨⟨false, Port.left⟩, mode⟩, _⟩ => Sum.inl mode
    | ⟨⟨⟨false, Port.right⟩, mode⟩, hExternal⟩ =>
        False.elim (hExternal ⟨⟨(), Sum.inl mode⟩, rfl⟩)
    | ⟨⟨⟨true, Port.left⟩, mode⟩, hExternal⟩ =>
        False.elim (hExternal ⟨⟨(), Sum.inr mode⟩, rfl⟩)
    | ⟨⟨⟨true, Port.right⟩, mode⟩, _⟩ => Sum.inr mode
  left_inv channel := by cases channel <;> rfl
  right_inv channel := by
    rcases channel with ⟨⟨⟨component, port⟩, mode⟩, hExternal⟩
    cases component <;> cases port
    · rfl
    · exact False.elim (hExternal ⟨⟨(), Sum.inl mode⟩, rfl⟩)
    · exact False.elim (hExternal ⟨⟨(), Sum.inr mode⟩, rfl⟩)
    · rfl

/-- External channels are finite through their canonical outer-channel coordinates. -/
noncomputable instance externalChannelFintype [Fintype left] [Fintype middle] [Fintype right]
    (first : ScatteringMatrix (left ⊕ middle))
    (second : ScatteringMatrix (middle ⊕ right)) :
    Fintype (netlist first second).ExternalChannel :=
  (netlist first second).eliminationExternalChannelFintype

/-- External channels have classically decidable equality in their canonical coordinates. -/
instance externalChannelDecidableEq (first : ScatteringMatrix (left ⊕ middle))
    (second : ScatteringMatrix (middle ⊕ right)) :
    DecidableEq (netlist first second).ExternalChannel := Classical.decEq _

end TwoPortSeriesNetlist

end

end Optics
