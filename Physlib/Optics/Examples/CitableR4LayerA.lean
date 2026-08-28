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
## ii. Key results
The recursive tree splitter elaborates at a concrete depth.
## iii. Table of contents
- A. Structural probe
## iv. References
ReconProbeR4.
-/
namespace Optics.CitableR4
open Optics
noncomputable section
def Leaves (ι : Type) : Nat → Type | 0 => ι | n + 1 => Leaves ι n ⊕ Leaves ι n
def level (l r : ℂ) (ι : Type) : (n : Nat) →
    LinearBehavior (Leaves ι n) (Leaves ι (n + 1))
  | 0 => LinearBehavior.weightedSplit l r
  | n + 1 => (level l r ι n).parallel (level l r ι n)
def tree (l r : ℂ) (ι : Type) : (n : Nat) → LinearBehavior ι (Leaves ι n)
  | 0 => LinearBehavior.identity
  | n + 1 => (tree l r ι n).series (level l r ι n)
example (l r : ℂ) : LinearBehavior Unit (Leaves Unit 2) := tree l r Unit 2
end
end Optics.CitableR4
