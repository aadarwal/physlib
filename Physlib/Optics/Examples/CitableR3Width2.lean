/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Physlib.Optics.Network.TwoPortChainFold
/-!
# Citable R3 width-2 probe
## i. Overview
Structural admission only: elaboration does NOT show semantic correctness, physical validity, or
carrying-capacity. Sorried side-conditions are carrying-capacity grade and excluded.
## ii. Key results
Width-two cascade definitions elaborate; the opaque-def hazard is retained as a commented negative control.
## iii. Table of contents
- A. Width-two structural probe
## iv. References
ReconProbeR3 and ReconProbeR3Def.
-/
namespace Optics.CitableR3
open Optics
noncomputable section
abbrev W := Unit ⊕ Unit
def lattice (stages : List (BackwardFirstTwoPortBehavior W W)) : BackwardFirstTwoPortBehavior W W :=
  BackwardFirstTwoPortBehavior.seriesFold stages
-- Negative control: replacing `abbrev W` by an opaque `def` is intentionally non-elaborating.
end
end Optics.CitableR3
