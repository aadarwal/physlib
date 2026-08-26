/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.TwoPortChainFold
public import Physlib.Optics.Systems.Microring.SourceBridgeDate

/-!
# Heterogeneous DATE microring cascades

## i. Overview

DATE'14 Defs. 4--7 list four-port rings and insert a bus-continuity matrix after each ring; the
source summary and sign pair are recorded at `HOL-CORPUS.md:199-203`. In source coordinates,
`c` propagates to the next `c` with `exp (+I * phi)`, while `a` propagates to the next `a` with
`exp (-I * phi)`.

The typed DATE ring matrix uses backward-first order `(c,a) -> (d,b)` at
`Physlib/Optics/Systems/Microring/SourceBridgeDate.lean:1024-1032`. Thus this file maps the first,
backward coordinate to `MatchedPropagation.carrierPhaseFactor (-phi)` and the second, forward
coordinate to `MatchedPropagation.carrierPhaseFactor phi`. The latter definition is Physlib's
`exp (-I * phi)` convention at `Physlib/Optics/Components/MatchedPropagation.lean:93-99`; the
opposite source sign is represented explicitly rather than silently flipped.

Stages are listed from the input side to the output side. Their matrices are folded by
`BackwardFirstChainTransform.fold` at
`Physlib/Optics/Network/TwoPortChainFold.lean:90-114`, so a later stage multiplies on the left.
The relational cascade is independent of that matrix fold. On the exact domain where every DATE
ring has bijective right-to-left transmission, DATE'14 Thm. 3 is recovered as equality of the
relational cascade with the folded chain graph.

## ii. Key results

- `DateCascadeStage.continuityChainMatrix`: DATE Def. 6 with both propagation signs exposed.
- `DateCascadeStage.compositionMatrix`: one `continuity ** ring` source stage.
- `dateCascadeComposition`: DATE Def. 7 through the neutral N3T list fold.
- `dateCascadeBehavior_eq_composition_toBehavior`: arbitrary relational cascades agree with the
  folded chain matrix under the exact per-ring pivot gates.
- `dateCascade_leftToRightChainTransform_eq_composition`: the behavior-derived matrix statement.

## iii. Table of contents

- A. DATE stage and continuity convention
- B. Heterogeneous cascade behavior and composition

## iv. References
This module makes no quadruple-ring, coupled-lattice, full `M x N` lattice, termination,
Sylvester, Chebyshev, or resonance claim. It also makes no SFG-TR'14 or NSV'16 comparison;
any later such comparison must retain the explicit principal-root/selected-half-arc branch gate.

DATE'14 Defs. 4--7 and Thm. 3 are summarized at `HOL-CORPUS.md:199-203`; the source proves the
uncoupled row sublattice only, as recorded at `HOL-CORPUS.md:210-216`.

Effective index is constant at the selected carrier. No dispersion, bending loss, bandwidth,
causality, or material realization is modeled. Power means normalized modal power, not
electromagnetic power before the bridge at
`Physlib/Optics/HarmonicFlux/PropagatingModePower.lean:16-22,60-93`; that bridge requires finite,
common-frequency Maxwell profiles which are pairwise integrable, mutually flux-orthogonal, and
unit normalized on the measured domain. No such hypotheses are inferred here.

The DATE matrices and quotients are totalized. Their relational chain meaning below requires the
displayed bijective transmission gates; no nonzero denominator, unitary-coupler, passivity,
reciprocity, losslessness, or well-posed N5 realization is inferred by the fold.
-/

@[expose] public section

namespace Optics

noncomputable section

namespace MicroringCascade

open MicroringSourceBridge

/-!

## A. DATE stage and continuity convention

-/

/-- One DATE'14 four-port ring together with its following bus length `L_b`.

The source list and bus-spacing convention are recorded at `HOL-CORPUS.md:199-203`.
-/
structure DateCascadeStage where
  /-- The DATE'14 four-port microring parameters. -/
  ring : DateParameters
  /-- The following bus length `L_b`. -/
  busLength : ℝ

namespace DateCascadeStage

/-- The bus phase lift `(2*pi/lambda)*n_eff*L_b` from DATE Def. 6
(`HOL-CORPUS.md:201`). -/
def busPhase (stage : DateCascadeStage) : ℝ :=
  (2 * Real.pi / stage.ring.wavelength) * stage.ring.effectiveIndex * stage.busLength

/-- DATE's backward-coordinate continuity factor `exp (+I*phi)`.

It is represented by Physlib's `exp (-I*phase)` function at the explicit argument `-phi`; see
`Physlib/Optics/Components/MatchedPropagation.lean:93-99` and `HOL-CORPUS.md:201`.
-/
def backwardContinuityFactor (stage : DateCascadeStage) : ℂ :=
  MatchedPropagation.carrierPhaseFactor (((-stage.busPhase : ℝ)) : Real.Angle)

/-- DATE's forward-coordinate continuity factor `exp (-I*phi)`.

This is Physlib's fixed-carrier factor at
`Physlib/Optics/Components/MatchedPropagation.lean:93-99` without a sign adapter.
-/
def forwardContinuityFactor (stage : DateCascadeStage) : ℂ :=
  MatchedPropagation.carrierPhaseFactor ((stage.busPhase : ℝ) : Real.Angle)

/-- DATE Def. 6's diagonal continuity matrix in backward-first order.

The first coordinate is the source `c/d` channel and gets `exp (+I*phi)`; the second is the source
`a/b` channel and gets `exp (-I*phi)`, exactly as listed at `HOL-CORPUS.md:201`.
-/
def continuityChainMatrix (stage : DateCascadeStage) :
    BackwardFirstChainTransform Unit Unit
  | Sum.inl _, Sum.inl _ => stage.backwardContinuityFactor
  | Sum.inl _, Sum.inr _ => 0
  | Sum.inr _, Sum.inl _ => 0
  | Sum.inr _, Sum.inr _ => stage.forwardContinuityFactor

/-- The singular-safe backward-first relation of the DATE four-port ring followed by its bus.

The ring regrouping is the source scattering relation at
`Physlib/Optics/Systems/Microring/SourceBridgeDate.lean:861-926`; the following bus is a chain
graph. No chain-view proof is required to define this relation.
-/
def behavior (stage : DateCascadeStage) : BackwardFirstTwoPortBehavior Unit Unit :=
  (dateSourceFourPortScattering stage.ring).toBackwardFirstBehavior.series
    stage.continuityChainMatrix.toBehavior

/-- DATE Def. 7's one-stage product `continuity_mat ** mrr_mat`.

The ring matrix is the backward-first form at
`Physlib/Optics/Systems/Microring/SourceBridgeDate.lean:1024-1032`.
-/
def compositionMatrix (stage : DateCascadeStage) :
    BackwardFirstChainTransform Unit Unit :=
  stage.continuityChainMatrix * dateFourPortBackwardFirstChainMatrix stage.ring

/-- The exact N3T pivot gate for the stage's DATE ring. -/
def HasBijectiveRingTransmission (stage : DateCascadeStage) : Prop :=
  (dateSourceFourPortScattering stage.ring).HasBijectiveRightToLeftTransmission

/-- The DATE ring pivot is bijective exactly when its scalar forward transfer is nonzero. -/
lemma hasBijectiveRingTransmission_iff_forwardTransfer_ne_zero (stage : DateCascadeStage) :
    stage.HasBijectiveRingTransmission ↔ dateForwardTransfer stage.ring ≠ 0 := by
  constructor
  · intro hBijective hZero
    have hMapped :
        (dateSourceFourPortScattering stage.ring).rightToLeftTransmission.toLinearMap
            (sourceScalarAmplitude 1) =
          (dateSourceFourPortScattering stage.ring).rightToLeftTransmission.toLinearMap 0 := by
      rw [dateSourceFourPortScattering_rightToLeftTransmission_action,
        dateSourceFourPortScattering_rightToLeftTransmission_action]
      apply WithLp.ofLp_injective 2
      funext index
      rcases index with ⟨⟨⟩⟩
      simp [sourceScalarAmplitude, hZero]
    have hEqual := hBijective.1 hMapped
    have hCoordinate := congrArg
      (fun amplitude : ModeAmplitude (BackwardWave Unit) =>
        amplitude (BackwardWave.mk ())) hEqual
    norm_num [sourceScalarAmplitude] at hCoordinate
  · exact dateSourceFourPortScattering_hasBijectiveRightToLeftTransmission stage.ring

/-- Under its exact ring pivot, one relational stage is the graph of its source matrix product. -/
lemma behavior_eq_compositionMatrix_toBehavior (stage : DateCascadeStage)
    (hTransmission : stage.HasBijectiveRingTransmission) :
    stage.behavior = stage.compositionMatrix.toBehavior := by
  let hForward :=
    (stage.hasBijectiveRingTransmission_iff_forwardTransfer_ne_zero).mp hTransmission
  let hPivot :=
    dateSourceFourPortScattering_hasBijectiveRightToLeftTransmission stage.ring hForward
  calc
    stage.behavior =
        ((dateSourceFourPortScattering stage.ring).toBackwardFirstChainTransform
          hPivot).toBehavior.series stage.continuityChainMatrix.toBehavior := by
      exact congrArg
        (fun ringBehavior : BackwardFirstTwoPortBehavior Unit Unit =>
          ringBehavior.series stage.continuityChainMatrix.toBehavior)
        (TwoPortScatteringTransform.toBehavior_toBackwardFirstChainTransform _ _).symm
    _ = ModeTransform.toBehavior
        (stage.continuityChainMatrix *
          (dateSourceFourPortScattering stage.ring).toBackwardFirstChainTransform
            hPivot) :=
      ModeTransform.toBehavior_mul _ _
    _ = stage.compositionMatrix.toBehavior := by
      rw [dateSourceFourPortChainTransform_eq stage.ring hForward]
      rfl

end DateCascadeStage

/-!

## B. Heterogeneous cascade behavior and composition

-/

/-- Relational cascade of DATE stages listed from the input side to the output side. -/
def dateCascadeBehavior (stages : List DateCascadeStage) :
    BackwardFirstTwoPortBehavior Unit Unit :=
  BackwardFirstTwoPortBehavior.seriesFold (stages.map DateCascadeStage.behavior)

/-- DATE Def. 7's heterogeneous cascade composition through the neutral N3T fold.

The fold order is fixed at `Physlib/Optics/Network/TwoPortChainFold.lean:90-114`: the head stage
is input-side and later stages multiply on the left.
-/
def dateCascadeComposition (stages : List DateCascadeStage) :
    BackwardFirstChainTransform Unit Unit :=
  BackwardFirstChainTransform.fold (stages.map DateCascadeStage.compositionMatrix)

/-- DATE'14 Thm. 3: an arbitrary heterogeneous relational cascade equals its folded chain graph.

Every ring retains the exact `HasBijectiveRightToLeftTransmission` gate required by the N3T
coordinate solve; no complete-matrix inverse is assumed.
-/
theorem dateCascadeBehavior_eq_composition_toBehavior (stages : List DateCascadeStage)
    (hStages : ∀ stage ∈ stages, stage.HasBijectiveRingTransmission) :
    dateCascadeBehavior stages = (dateCascadeComposition stages).toBehavior := by
  change BackwardFirstTwoPortBehavior.seriesFold
      (stages.map DateCascadeStage.behavior) =
    (BackwardFirstChainTransform.fold
      (stages.map DateCascadeStage.compositionMatrix)).toBehavior
  rw [← BackwardFirstChainTransform.seriesFold_map_toBehavior_eq_fold_toBehavior]
  induction stages with
  | nil => rfl
  | cons first rest ih =>
      simp only [List.map_cons, BackwardFirstTwoPortBehavior.seriesFold]
      rw [first.behavior_eq_compositionMatrix_toBehavior (hStages first (by simp))]
      apply congrArg (first.compositionMatrix.toBehavior.series ·)
      exact ih fun stage hStage => hStages stage (by simp [hStage])

/-- The heterogeneous DATE cascade has a functional left-to-right chain view on its pivot domain. -/
lemma dateCascadeBehavior_hasLeftToRightChainView (stages : List DateCascadeStage)
    (hStages : ∀ stage ∈ stages, stage.HasBijectiveRingTransmission) :
    (dateCascadeBehavior stages).HasLeftToRightChainView := by
  rw [dateCascadeBehavior_eq_composition_toBehavior stages hStages]
  exact (dateCascadeComposition stages).toBehavior_isFunctional

/-- Extracting the heterogeneous DATE cascade's chain transform recovers its source fold. -/
lemma dateCascade_leftToRightChainTransform_eq_composition (stages : List DateCascadeStage)
    (hStages : ∀ stage ∈ stages, stage.HasBijectiveRingTransmission) :
    BackwardFirstTwoPortBehavior.leftToRightChainTransform
        (dateCascadeBehavior stages)
        (dateCascadeBehavior_hasLeftToRightChainView stages hStages) =
      dateCascadeComposition stages := by
  exact BackwardFirstTwoPortBehavior.leftToRightChainTransform_unique
    (dateCascadeBehavior stages)
    (dateCascadeBehavior_hasLeftToRightChainView stages hStages)
    (dateCascadeComposition stages)
    (dateCascadeBehavior_eq_composition_toBehavior stages hStages).symm

end MicroringCascade

end

end Optics
