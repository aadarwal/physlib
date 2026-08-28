/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

/-
Reconnaissance elaboration probe — R4 layer-(A) claim, binary tree splitter.

Tests ONE claim from R4.md section 3.4: that the binary tree composes at the
`LinearBehavior` layer by general combinators alone, generically in `N`, with the
types lining up DEFINITIONALLY at each step and no bespoke module.

Elaboration-only; no proofs and no deferred obligations. If this file elaborates, R4's layer-(A)
EXPRESSIBLE verdict is confirmed as fact rather than a type-read. If it fails, the
failure message names which step of the recursion does not line up.

Cited declarations (all at pin cfaeef36):
  LinearBehavior.weightedSplit  Physlib/Optics/Network/RectangularBehavior.lean:109
  LinearBehavior.parallel       Physlib/Optics/Network/LinearBehavior.lean:594
  LinearBehavior.series         Physlib/Optics/Network/LinearBehavior.lean:438
  LinearBehavior.identity       Physlib/Optics/Network/LinearBehavior.lean:413
-/

public import Physlib.Optics.Network.RectangularBehavior

@[expose] public section

namespace Optics.CitableR4

open Optics

noncomputable section

universe u

/-- Leaf index after `n` levels: `Leaves ι (n+1) = Leaves ι n ⊕ Leaves ι n`. -/
def Leaves (ι : Type u) : Nat → Type u
  | 0 => ι
  | n + 1 => Leaves ι n ⊕ Leaves ι n

/-- One level of the tree: every current leaf splits in two.

The recursive step is the load-bearing one. `parallel` on
`LinearBehavior (Leaves ι n) (Leaves ι (n+1))` yields
`LinearBehavior (Leaves ι n ⊕ Leaves ι n) (Leaves ι (n+1) ⊕ Leaves ι (n+1))`,
which must BE `LinearBehavior (Leaves ι (n+1)) (Leaves ι (n+2))` definitionally. -/
def level (leftWeight rightWeight : ℂ) (ι : Type u) :
    (n : Nat) → LinearBehavior (Leaves ι n) (Leaves ι (n + 1))
  | 0 => LinearBehavior.weightedSplit leftWeight rightWeight
  | n + 1 => (level leftWeight rightWeight ι n).parallel (level leftWeight rightWeight ι n)

/-- The depth-`n` binary tree splitter, one input to `2 ^ n` leaves. -/
def tree (leftWeight rightWeight : ℂ) (ι : Type u) :
    (n : Nat) → LinearBehavior ι (Leaves ι n)
  | 0 => LinearBehavior.identity
  | n + 1 => (tree leftWeight rightWeight ι n).series (level leftWeight rightWeight ι n)

/-- The claim, stated as a type ascription at a concrete depth. -/
example (c₀ c₁ : ℂ) : LinearBehavior Unit (Leaves Unit 3) := tree c₀ c₁ Unit 3

end

end Optics.CitableR4

/-- Universe check, per R4's own correction: the definitions above are declared at
`Type u`, so instantiating at `Type 1` exercises the universe-polymorphic form rather
than only `Type 0`. -/
example (c₀ c₁ : ℂ) :
    Optics.LinearBehavior (ULift.{1} Unit) (Optics.CitableR4.Leaves (ULift.{1} Unit) 2) :=
  Optics.CitableR4.tree c₀ c₁ (ULift.{1} Unit) 2
