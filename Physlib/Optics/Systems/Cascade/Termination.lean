/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.TwoPortChainTermination
public import Physlib.Optics.Systems.Cascade.Identical

/-!
# Zero-return termination of DATE cascades

## i. Overview

DATE'14 Def. 8 imposes `c_N = 0` at the right boundary. In backward-first travelling-wave
coordinates this is the zero-return load `aR = 0` from
`Physlib/Optics/Network/TwoPortTermination.lean:100-121`.

The corresponding chain pivot is `M11`. The exact general well-posedness criterion is proved at
`Physlib/Optics/Network/TwoPortChainTermination.lean:349-389`, and its zero-return specialization
identifies the pivot with the leading block at
`Physlib/Optics/Network/TwoPortChainTermination.lean:686-710`. For DATE's singleton channel,
well-posedness is therefore equivalent to the missing source condition `M11 != 0`.

The response coefficients below are extracted from the terminated relational cascade, not
defined by quotient formulas. DATE'14 Thm. 5 is then recovered as
`reflect = -M12/M11` and `transm = 1/M11`. The latter uses the determinant-one property derived
from the per-ring chain gates. DATE'14 Thm. 6 follows by substituting the proved Sylvester form.

## ii. Key results

- `DateCascadeTerminationHypotheses`: the per-ring chain gates and nonzero termination pivot.
- `dateTerminatedCascade_reflectivity_eq_neg_entry12_div_entry11`: DATE'14 Thm. 5 reflection.
- `dateTerminatedCascade_transmissivity_eq_one_div_entry11`: DATE'14 Thm. 5 transmission.
- `dateIdenticalTerminatedCascade_reflectivity_eq_closedForm`: DATE'14 Thm. 6 reflection.
- `dateIdenticalTerminatedCascade_transmissivity_eq_closedForm`: DATE'14 Thm. 6 transmission.

## iii. Table of contents

- A. Determinants and the scalar termination pivot
- B. Relational zero-return responses
- C. Identical-cascade closed form

## iv. References and non-claims

DATE'14 Def. 8 and Thms. 5--6 are summarized at `HOL-CORPUS.md:205-208`. The source omits the
required `M11 != 0` condition; this module states it explicitly. Its reflectivity and
transmissivity names denote the source's complex field-amplitude ratios, not power fractions.

The zero-return relation is only `aR = 0`. It makes no impedance-matching, absorption, radiation,
passivity, reciprocity, losslessness, causality, bandwidth, or material-realization claim. The
reported transmitted field is the forward wave at the declared right termination plane.
-/

@[expose] public section

namespace Optics

noncomputable section

namespace MicroringCascade

open MicroringSourceBridge

/-!

## A. Determinants and the scalar termination pivot

-/

/-- DATE's signed continuity matrix has determinant one. -/
lemma DateCascadeStage.continuityChainMatrix_det (stage : DateCascadeStage) :
    Matrix.det stage.continuityChainMatrix = 1 := by
  rw [← Matrix.det_reindex_self dateBackwardFirstFinEquiv.symm
    stage.continuityChainMatrix, Matrix.det_fin_two]
  simp [Matrix.reindex_apply, DateCascadeStage.continuityChainMatrix,
    dateBackwardFirstFinEquiv, DateCascadeStage.backwardContinuityFactor,
    DateCascadeStage.forwardContinuityFactor, MatchedPropagation.carrierPhaseFactor,
    Real.Angle.toCircle_neg, Circle.coe_inv]

/-- DATE's four-port ring chain matrix has determinant one on its source pivot. -/
lemma dateFourPortBackwardFirstChainMatrix_det (ring : DateParameters)
    (hForward : dateForwardTransfer ring ≠ 0) :
    Matrix.det (dateFourPortBackwardFirstChainMatrix ring) = 1 := by
  rw [← Matrix.det_reindex_self dateBackwardFirstFinEquiv.symm
    (dateFourPortBackwardFirstChainMatrix ring), Matrix.det_fin_two]
  change
    (1 / dateForwardTransfer ring) *
        ((dateForwardTransfer ring ^ 2 - dateBackwardTransfer ring ^ 2) /
          dateForwardTransfer ring) -
      (-dateBackwardTransfer ring / dateForwardTransfer ring) *
        (dateBackwardTransfer ring / dateForwardTransfer ring) = 1
  field_simp [hForward]
  ring

/-- A well-formed DATE stage composition has determinant one. -/
lemma DateCascadeStage.compositionMatrix_det (stage : DateCascadeStage)
    (hTransmission : stage.HasBijectiveRingTransmission) :
    Matrix.det stage.compositionMatrix = 1 := by
  rw [DateCascadeStage.compositionMatrix, Matrix.det_mul,
    stage.continuityChainMatrix_det,
    dateFourPortBackwardFirstChainMatrix_det stage.ring
      ((stage.hasBijectiveRingTransmission_iff_forwardTransfer_ne_zero).mp hTransmission)]
  norm_num

/-- A DATE cascade composition has determinant one under its exact per-ring chain gates. -/
lemma dateCascadeComposition_det (stages : List DateCascadeStage)
    (hStages : ∀ stage ∈ stages, stage.HasBijectiveRingTransmission) :
    Matrix.det (dateCascadeComposition stages) = 1 := by
  change Matrix.det (BackwardFirstChainTransform.fold
    (stages.map DateCascadeStage.compositionMatrix)) = 1
  induction stages with
  | nil => simp [BackwardFirstChainTransform.fold]
  | cons first rest ih =>
      rw [List.map_cons, BackwardFirstChainTransform.fold, Matrix.det_mul,
        first.compositionMatrix_det (hStages first (by simp)),
        ih (fun stage hStage => hStages stage (by simp [hStage]))]
      norm_num

/-- The singleton leading block acts by multiplication by DATE's `M11` entry. -/
lemma dateChain_leadingBlock_action (matrix : BackwardFirstChainTransform Unit Unit)
    (amplitude : ModeAmplitude (BackwardWave Unit)) :
    matrix.leadingBlock.toLinearMap amplitude =
      sourceScalarAmplitude
        (dateChainEntry matrix 0 0 * amplitude (BackwardWave.mk ())) := by
  apply WithLp.ofLp_injective 2
  funext output
  rcases output with ⟨⟨⟩⟩
  simp only [ModeTransform.toLinearMap, Matrix.toLpLin_apply, Matrix.mulVec,
    dotProduct, sourceScalarAmplitude]
  rw [← BackwardWave.channelEquiv.symm.sum_comp]
  simp [dateChainEntry, dateBackwardFirstFinEquiv,
    BackwardFirstChainTransform.leadingBlock, Matrix.toBlocks₁₁]

/-- For DATE's singleton channel, the leading chain block is bijective exactly when `M11 != 0`.

Together with `TwoPortChainTermination.lean:686-710`, this is the corrected source pivot condition.
-/
lemma dateChain_hasBijectiveLeadingBlock_iff_entry11_ne_zero
    (matrix : BackwardFirstChainTransform Unit Unit) :
    matrix.HasBijectiveLeadingBlock ↔ dateChainEntry matrix 0 0 ≠ 0 := by
  constructor
  · intro hLeading hZero
    let unitAmplitude :=
      (sourceScalarAmplitude 1 : ModeAmplitude (BackwardWave Unit))
    have hEqual : matrix.leadingBlock.toLinearMap unitAmplitude =
        matrix.leadingBlock.toLinearMap 0 := by
      rw [dateChain_leadingBlock_action, dateChain_leadingBlock_action, hZero]
      simp [unitAmplitude, sourceScalarAmplitude]
    have hUnit := hLeading.1 hEqual
    have hCoordinate := congrArg
      (fun amplitude : ModeAmplitude (BackwardWave Unit) =>
        amplitude (BackwardWave.mk ())) hUnit
    norm_num [unitAmplitude, sourceScalarAmplitude] at hCoordinate
  · intro hEntry
    constructor
    · intro first second hEqual
      rw [dateChain_leadingBlock_action, dateChain_leadingBlock_action] at hEqual
      have hCoordinate := congrArg
        (fun amplitude : ModeAmplitude (BackwardWave Unit) =>
          amplitude (BackwardWave.mk ())) hEqual
      change dateChainEntry matrix 0 0 * first (BackwardWave.mk ()) =
        dateChainEntry matrix 0 0 * second (BackwardWave.mk ()) at hCoordinate
      apply WithLp.ofLp_injective 2
      funext input
      rcases input with ⟨⟨⟩⟩
      exact mul_left_cancel₀ hEntry hCoordinate
    · intro output
      refine ⟨(sourceScalarAmplitude
        ((dateChainEntry matrix 0 0)⁻¹ * output (BackwardWave.mk ())) :
          ModeAmplitude (BackwardWave Unit)), ?_⟩
      rw [dateChain_leadingBlock_action]
      apply WithLp.ofLp_injective 2
      funext input
      rcases input with ⟨⟨⟩⟩
      change dateChainEntry matrix 0 0 *
          ((dateChainEntry matrix 0 0)⁻¹ * output (BackwardWave.mk ())) =
        output (BackwardWave.mk ())
      field_simp

end MicroringCascade

end

end Optics
