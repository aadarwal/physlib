/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Systems.Microring.SourceBridgeSfg

/-!
# Stagewise SFG-TR'14 add-drop data in a cascade list

## i. Overview

This file reuses the discharged SFG-TR'14 add-drop dictionary stage by stage in a list of
microring data. The scalar map is literally the composition of `SfgParameters.ofAddDrop` with
`sfgAddDropTransfer`; it is not a new source formula or a claim that the listed drop ports are
physically interconnected.

The underlying dictionary maps source node 1 to Physlib's input and source node 8 to its drop
channel at `Physlib/Optics/Systems/Microring/SourceBridgeSfg.lean:64-74`. Its comparison theorem
requires the principal-root equality at that file's lines 98-105. This file retains that equality
for every listed stage.

## ii. Key results

- `sfgAddDropStageTransfer`: the existing source transfer after the existing parameter map.
- `sfgAddDropStageTransfers_eq_dropTransfers`: stagewise agreement on the root gates.

## iii. Table of contents

- A. Composed stage dictionary
- B. Stagewise list comparison

## iv. References and non-claims

SFG-TR'14 Def. 35 gives an eight-node add-drop signal-flow graph and Thm. 7 gives
`-S1*S2*sqrt(xi)/(1-C1*C2*xi)`; the audited mapping is already recorded in
`SourceBridgeSfg.lean:51-105`. No part of that source statement is reproved here.

The list below is bookkeeping for a cascade development, not a scalar cascade law. No PANDA,
NSV'16, DATE lattice, quadruple-ring, coupled-lattice, full `M x N` lattice, dispersion, bending
loss, bandwidth, causality, resonance, or measurement-validation claim is made. Power, if later
introduced, means normalized modal power; its electromagnetic interpretation requires the
finite common-frequency Maxwell and aperture-flux hypotheses at
`Physlib/Optics/HarmonicFlux/PropagatingModePower.lean:60-90`.
-/

@[expose] public section

namespace Optics

noncomputable section

namespace MicroringCascade

open MicroringSourceBridge

/-! ## A. Composed stage dictionary -/

/-- SFG-TR'14's add-drop transfer after the existing Physlib-to-source parameter map.

This is function composition only; it introduces no new source graph or cascade interconnection.
-/
def sfgAddDropStageTransfer : AddDrop.Parameters → ℂ :=
  sfgAddDropTransfer ∘ SfgParameters.ofAddDrop

/-- The composed stage dictionary agrees with Physlib's drop transfer on the explicit
principal-root/selected-half-arc gate inherited from `SourceBridgeSfg.lean:98-105`. -/
lemma sfgAddDropStageTransfer_eq_dropTransfer (p : AddDrop.Parameters)
    (hSqrt : Complex.sqrt p.roundTripCoefficient = p.firstArcCoefficient) :
    sfgAddDropStageTransfer p = AddDrop.dropTransfer p :=
  sfgAddDropTransfer_eq_dropTransfer p hSqrt

/-! ## B. Stagewise list comparison -/

/-- The source-mapped transfer attached independently to every listed add-drop stage. -/
def sfgAddDropStageTransfers (stages : List AddDrop.Parameters) : List ℂ :=
  stages.map sfgAddDropStageTransfer

/-- Every listed source transfer agrees with its Physlib drop transfer when every stage retains
the explicit principal-root/selected-half-arc branch gate. -/
lemma sfgAddDropStageTransfers_eq_dropTransfers (stages : List AddDrop.Parameters)
    (hSqrt : ∀ p ∈ stages,
      Complex.sqrt p.roundTripCoefficient = p.firstArcCoefficient) :
    sfgAddDropStageTransfers stages = stages.map AddDrop.dropTransfer := by
  induction stages with
  | nil => rfl
  | cons p stages inductionHypothesis =>
      rw [sfgAddDropStageTransfers, List.map_cons, List.map_cons,
        sfgAddDropStageTransfer_eq_dropTransfer p (hSqrt p (by simp))]
      change sfgAddDropStageTransfers stages = stages.map AddDrop.dropTransfer
      apply inductionHypothesis
      intro q hq
      exact hSqrt q (by simp [hq])

end MicroringCascade

end

end Optics
