/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.TwoPortSeriesNetlist

/-!
# Finite coordinates of the canonical two-port series netlist

## i. Overview

This file gives the canonical nested-sum coordinates and finite instances for the two-device
series boundary and its connected middle channels.

## ii. Key results

- `TwoPortSeriesNetlist.aggregateChannelEquiv`: nested component channels equal the boundary.
- `TwoPortSeriesNetlist.netlistComponentFintype`: the canonical family has two components.
- `TwoPortSeriesNetlist.netlistChannelFintype`: finiteness of the aggregate boundary.
- `TwoPortSeriesNetlist.connectedChannelFintype`: finiteness of the middle connection.

## iii. Table of contents

- A. Aggregate and connected coordinates

## iv. References

This typed coordinate layer is Physlib-original; no external source is used here.

-/

@[expose] public section

namespace Optics

noncomputable section

universe u

namespace TwoPortSeriesNetlist

variable {left middle right : Type u}

/-!

## A. Aggregate and connected coordinates

-/

/-- Nested component channels re-associated into the aggregate physical boundary. -/
def aggregateChannelEquiv (first : ScatteringMatrix (left ⊕ middle))
    (second : ScatteringMatrix (middle ⊕ right)) :
    (left ⊕ middle) ⊕ (middle ⊕ right) ≃
      (components first second).aggregatePortModeFamily.Channel :=
  { toFun := fun
      | Sum.inl (Sum.inl mode) => ⟨⟨false, Port.left⟩, mode⟩
      | Sum.inl (Sum.inr mode) => ⟨⟨false, Port.right⟩, mode⟩
      | Sum.inr (Sum.inl mode) => ⟨⟨true, Port.left⟩, mode⟩
      | Sum.inr (Sum.inr mode) => ⟨⟨true, Port.right⟩, mode⟩
    invFun := fun
      | ⟨⟨false, Port.left⟩, mode⟩ => Sum.inl (Sum.inl mode)
      | ⟨⟨false, Port.right⟩, mode⟩ => Sum.inl (Sum.inr mode)
      | ⟨⟨true, Port.left⟩, mode⟩ => Sum.inr (Sum.inl mode)
      | ⟨⟨true, Port.right⟩, mode⟩ => Sum.inr (Sum.inr mode)
    left_inv := by
      intro channel
      rcases channel with channel | channel <;>
        rcases channel with mode | mode <;> rfl
    right_inv := by
      rintro ⟨⟨component, port⟩, mode⟩
      cases component <;> cases port <;> rfl }

/-- The canonical series netlist has exactly two components. -/
instance netlistComponentFintype (first : ScatteringMatrix (left ⊕ middle))
    (second : ScatteringMatrix (middle ⊕ right)) :
    Fintype (netlist first second).components.Component := by
  change Fintype Bool
  infer_instance

/-- Every local component channel family is finite when the three mode families are finite. -/
noncomputable instance componentChannelFintype [Fintype left] [Fintype middle]
    [Fintype right] (first : ScatteringMatrix (left ⊕ middle))
    (second : ScatteringMatrix (middle ⊕ right)) (component : Bool) :
    Fintype ((components first second).portFamily component).Channel := by
  cases component <;> simp only [components, componentPortFamily] <;> infer_instance

/-- Every local component channel family has decidable equality in finite coordinates. -/
instance componentChannelDecidableEq [DecidableEq left] [DecidableEq middle]
    [DecidableEq right] (first : ScatteringMatrix (left ⊕ middle))
    (second : ScatteringMatrix (middle ⊕ right)) (component : Bool) :
    DecidableEq ((components first second).portFamily component).Channel := by
  cases component <;> simp only [components, componentPortFamily] <;> infer_instance

/-- Every local channel family stored by the canonical netlist is finite. -/
noncomputable instance netlistComponentChannelFintype
    [Fintype left] [Fintype middle] [Fintype right]
    (first : ScatteringMatrix (left ⊕ middle))
    (second : ScatteringMatrix (middle ⊕ right))
    (component : (netlist first second).components.Component) :
    Fintype ((netlist first second).components.portFamily component).Channel :=
  componentChannelFintype first second component

/-- The aggregate component boundary is finite when all three mode families are finite. -/
noncomputable instance netlistChannelFintype [Fintype left] [Fintype middle]
    [Fintype right] (first : ScatteringMatrix (left ⊕ middle))
    (second : ScatteringMatrix (middle ⊕ right)) :
    Fintype (netlist first second).Channel :=
  Fintype.ofEquiv ((left ⊕ middle) ⊕ (middle ⊕ right))
    (aggregateChannelEquiv first second)

/-- The aggregate component boundary has decidable equality in finite coordinates. -/
instance netlistChannelDecidableEq [Fintype left] [Fintype middle] [Fintype right]
    (first : ScatteringMatrix (left ⊕ middle))
    (second : ScatteringMatrix (middle ⊕ right)) :
    DecidableEq (netlist first second).Channel := Classical.decEq _

set_option linter.checkUnivs false in
/-- The two middle connection channels form a finite family. -/
noncomputable instance connectedChannelFintype [Fintype middle]
    (first : ScatteringMatrix (left ⊕ middle))
    (second : ScatteringMatrix (middle ⊕ right)) :
    Fintype (netlist first second).ConnectedChannel := by
  change Fintype (Σ _ : Unit, middle ⊕ middle)
  infer_instance

/-- The two middle connection channels have decidable equality. -/
instance connectedChannelDecidableEq [DecidableEq middle]
    (first : ScatteringMatrix (left ⊕ middle))
    (second : ScatteringMatrix (middle ⊕ right)) :
    DecidableEq (netlist first second).ConnectedChannel := Classical.decEq _

end TwoPortSeriesNetlist

end

end Optics
