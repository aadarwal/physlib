/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.FlatNetlist
public import Physlib.Optics.Network.TwoPortScattering

/-!
# Canonical flat netlist for two two-port components in series

## i. Overview

This file packages two arbitrary typed scattering matrices as separately owned physical
two-port components and joins exactly their middle ports.

## ii. Key results

- `TwoPortSeriesNetlist.portFamily`: an owned left/right physical-port family.
- `TwoPortSeriesNetlist.components`: the two independently stored scattering components.
- `TwoPortSeriesNetlist.connections`: the unique middle-port connection.
- `TwoPortSeriesNetlist.netlist`: the resulting two-device `FlatNetlist`.

## iii. Table of contents

- A. Physical two-port coordinates
- B. Two-device series wiring

## iv. References

This typed netlist construction is Physlib-original; no external source is used here.

-/

@[expose] public section

namespace Optics

noncomputable section

universe u

namespace TwoPortSeriesNetlist

variable {left middle right : Type u}

/-!

## A. Physical two-port coordinates

-/

/-- The left and right physical ports of a generic two-port component. -/
inductive Port
  | left
  | right
  deriving DecidableEq

/-- A generic two-port has exactly two physical ports. -/
instance : Fintype Port where
  elems := {Port.left, Port.right}
  complete port := by
    cases port <;> simp

/-- A physical two-port family with independently typed left and right mode fibers. -/
def portFamily (left right : Type u) : PortModeFamily.{0, u} where
  Port := Port
  Mode
    | Port.left => left
    | Port.right => right

/-- The pinned left-then-right channel coordinates of a physical two-port family. -/
def channelEquiv (left right : Type u) :
    left ⊕ right ≃ (portFamily left right).Channel where
  toFun
    | Sum.inl mode => ⟨Port.left, mode⟩
    | Sum.inr mode => ⟨Port.right, mode⟩
  invFun
    | ⟨Port.left, mode⟩ => Sum.inl mode
    | ⟨Port.right, mode⟩ => Sum.inr mode
  left_inv channel := by cases channel <;> rfl
  right_inv channel := by rcases channel with ⟨port, mode⟩; cases port <;> rfl

/-- Physical two-port channels are finite when both mode fibers are finite. -/
noncomputable instance channelFintype [Fintype left] [Fintype right] :
    Fintype (portFamily left right).Channel :=
  Fintype.ofEquiv (left ⊕ right) (channelEquiv left right)

/-- Physical two-port channels inherit decidable equality from the pinned coordinates. -/
instance channelDecidableEq [DecidableEq left] [DecidableEq right] :
    DecidableEq (portFamily left right).Channel :=
  (channelEquiv left right).symm.decidableEq

/-- Relabel an algebraic two-port scattering matrix into component-owned physical channels. -/
def physicalScattering (scattering : ScatteringMatrix (left ⊕ right)) :
    ScatteringMatrix (portFamily left right).Channel :=
  scattering.reindex (channelEquiv left right)

/-!

## B. Two-device series wiring

-/

/-- The first and second local port families in a two-device series connection. -/
def componentPortFamily (left middle right : Type u) : Bool → PortModeFamily.{0, u}
  | false => portFamily left middle
  | true => portFamily middle right

/-- The two local scattering matrices in component-owned physical coordinates. -/
def componentScattering (first : ScatteringMatrix (left ⊕ middle))
    (second : ScatteringMatrix (middle ⊕ right)) :
    (component : Bool) →
      ScatteringMatrix (componentPortFamily left middle right component).Channel
  | false => physicalScattering first
  | true => physicalScattering second

/-- The two separately owned scattering components before their middle ports are wired. -/
def components (first : ScatteringMatrix (left ⊕ middle))
    (second : ScatteringMatrix (middle ⊕ right)) : ScatteringComponentFamily where
  Component := Bool
  portFamily := componentPortFamily left middle right
  scattering := componentScattering first second

/-- The single physical connection joining the first right port to the second left port. -/
def connection (first : ScatteringMatrix (left ⊕ middle))
    (second : ScatteringMatrix (middle ⊕ right)) :
    PortConnection (components first second).aggregatePortModeFamily where
  left := ⟨false, Port.right⟩
  right := ⟨true, Port.left⟩
  left_ne_right := fun equality => Bool.noConfusion (congrArg Sigma.fst equality)
  modeEquiv := Equiv.refl middle

/-- The proof-carrying singleton family containing exactly the middle-port connection. -/
def connections (first : ScatteringMatrix (left ⊕ middle))
    (second : ScatteringMatrix (middle ⊕ right)) :
    PortConnectionFamily (components first second).aggregatePortModeFamily Unit where
  connection := fun _ => connection first second
  endpointPort_injective := by
    rintro ⟨firstIndex, firstEnd⟩ ⟨secondIndex, secondEnd⟩ equality
    cases firstIndex
    cases secondIndex
    cases firstEnd <;> cases secondEnd
    · rfl
    · exact Bool.noConfusion (congrArg Sigma.fst equality)
    · exact Bool.noConfusion (congrArg Sigma.fst equality)
    · rfl

/-- The canonical flat netlist of two scattering components joined in series. -/
def netlist (first : ScatteringMatrix (left ⊕ middle))
    (second : ScatteringMatrix (middle ⊕ right)) : FlatNetlist where
  components := components first second
  Connection := Unit
  connections := connections first second

end TwoPortSeriesNetlist

end

end Optics
