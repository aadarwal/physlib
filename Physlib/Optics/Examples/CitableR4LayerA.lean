/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.RectangularBehavior

/-!
# Citable R4 layer-A probe

## i. Overview

Structural admission only: elaboration does NOT show semantic correctness, physical validity, or
carrying-capacity. Sorried side-conditions are carrying-capacity grade and excluded.

Elevates R4's layer-(A) claim (binary tree splitter): the tree composes at the `LinearBehavior`
layer by general combinators alone, generically in `N`, with the types lining up DEFINITIONALLY
at each step and no bespoke module.

## ii. Key results

The recursion elaborates universe-polymorphically, instantiated at depth 3 and, beyond the recon
probe, at the non-zero universe `ULift.{1} Unit`. Elaboration-only; no proofs and no deferred
obligations.

## iii. Table of contents

- A. Structural probe

## iv. References

Elevated from the R4 reconnaissance probe (session record). Cited declarations at probe pin
cfaeef36: `LinearBehavior.weightedSplit` (Network/RectangularBehavior.lean:109),
`LinearBehavior.parallel` (Network/LinearBehavior.lean:594), `LinearBehavior.series`
(Network/LinearBehavior.lean:438), `LinearBehavior.identity` (Network/LinearBehavior.lean:413).
-/

@[expose] public section

namespace Optics.CitableR4

open Optics

noncomputable section

/-!
## A. Structural probe
-/

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
