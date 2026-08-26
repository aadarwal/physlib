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
from the per-ring chain gates.

The identical-cascade results instead substitute Physlib's proved real-angle Sylvester form into
those relational responses. They do not formalize printed DATE'14 Thm. 6. That display uses the
forward factor `exp (-I*phi)`, whereas the relevant backward-first chain entries contain the
backward factor `exp (+I*phi)`. It also prints a distinct `Re(cos⁻¹(...))` angle, while
`dateSylvesterAngle` is `Real.arccos (Re(m11))`. No bridge between those expressions is assumed.

## ii. Key results

- `DateCascadeTerminationHypotheses`: the per-ring chain gates and nonzero termination pivot.
- `dateTerminatedCascade_reflectivity_eq_neg_entry12_div_entry11`: DATE'14 Thm. 5 reflection.
- `dateTerminatedCascade_transmissivity_eq_one_div_entry11`: DATE'14 Thm. 5 transmission.
- `dateIdenticalTerminatedCascade_reflectivity_eq_relationalSylvesterForm`: corrected reflection.
- `dateIdenticalTerminatedCascade_transmissivity_eq_relationalSylvesterForm`: corrected forward
  response.

## iii. Table of contents

- A. Determinants and the scalar termination pivot
- B. Relational zero-return responses
- C. Identical-cascade closed form

## iv. References and non-claims

DATE'14 Def. 8 and Thms. 5--6 are summarized at `HOL-CORPUS.md:205-208`. The source omits the
required `M11 != 0` condition; this module states it explicitly. Exact parity with printed Thm. 6
is withheld for the forward-factor and angle mismatches above. The reflectivity and
transmissivity names denote complex field-amplitude ratios, not power fractions.

The zero-return relation is only `aR = 0`. It makes no impedance-matching, absorption, radiation,
passivity, reciprocity, losslessness, causality, bandwidth, or material-realization claim. The
reported transmitted field is the forward wave at the declared right termination plane.

This module makes no quadruple-ring, coupled-lattice, or full `M x N` lattice claim. It makes no
SFG-TR'14 or NSV'16 comparison; any such bridge must retain IP-12's explicit
principal-root/selected-half-arc equality. Effective index is constant at the selected carrier,
and no dispersion model is inferred. In particular, the corrected identical-cascade lemmas do
not discharge the bundled IP-18 row containing printed DATE'14 Thm. 6.
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

/-- The determinant in DATE's pinned source-coordinate order. -/
lemma dateChain_det_eq_entry11_mul_entry22_sub_entry12_mul_entry21
    (matrix : BackwardFirstChainTransform Unit Unit) :
    Matrix.det matrix =
      dateChainEntry matrix 0 0 * dateChainEntry matrix 1 1 -
        dateChainEntry matrix 0 1 * dateChainEntry matrix 1 0 := by
  rw [← Matrix.det_reindex_self dateBackwardFirstFinEquiv.symm matrix,
    Matrix.det_fin_two]
  simp [Matrix.reindex_apply, dateChainEntry]

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

/-- For a singleton chain, zero-return termination is well posed exactly when `M11 != 0`.

This specializes the exact pivot criterion at
`Physlib/Optics/Network/TwoPortChainTermination.lean:349-389` and its zero-return pivot at
`Physlib/Optics/Network/TwoPortChainTermination.lean:686-710`.
-/
lemma dateChain_hasWellPosedZeroReturn_iff_entry11_ne_zero
    (matrix : BackwardFirstChainTransform Unit Unit) :
    matrix.HasWellPosedRightTermination (0 : RightLoadTransform Unit) ↔
      dateChainEntry matrix 0 0 ≠ 0 := by
  constructor
  · intro hWellPosed hZero
    have hInjective :=
      (matrix.isSingleValued_rightTerminationBehavior_iff_pivot_injective
        (0 : RightLoadTransform Unit)).mp hWellPosed.2
    rw [matrix.rightTerminationPivot_zero] at hInjective
    let unitAmplitude :=
      (sourceScalarAmplitude 1 : ModeAmplitude (BackwardWave Unit))
    have hEqual : matrix.leadingBlock.toLinearMap unitAmplitude =
        matrix.leadingBlock.toLinearMap 0 := by
      rw [dateChain_leadingBlock_action, dateChain_leadingBlock_action, hZero]
      simp [unitAmplitude, sourceScalarAmplitude]
    have hUnit := hInjective hEqual
    have hCoordinate := congrArg
      (fun amplitude : ModeAmplitude (BackwardWave Unit) =>
        amplitude (BackwardWave.mk ())) hUnit
    norm_num [unitAmplitude, sourceScalarAmplitude] at hCoordinate
  · intro hEntry
    let hLeading :=
      (dateChain_hasBijectiveLeadingBlock_iff_entry11_ne_zero matrix).2 hEntry
    exact matrix.hasWellPosedRightTermination_of_hasBijectivePivot 0
      (matrix.hasBijectiveRightTerminationPivot_zero hLeading)

/-- The inverse singleton leading block has entry `1 / M11`. -/
lemma dateChain_leadingBlockInverse_entry
    (matrix : BackwardFirstChainTransform Unit Unit)
    (hLeading : matrix.HasBijectiveLeadingBlock) :
    (matrix.leadingBlockInverse hLeading)
        (BackwardWave.mk ()) (BackwardWave.mk ()) =
      1 / dateChainEntry matrix 0 0 := by
  let unitAmplitude :=
    (sourceScalarAmplitude 1 : ModeAmplitude (BackwardWave Unit))
  have hInverse := matrix.leadingBlock_apply_inverse hLeading unitAmplitude
  rw [dateChain_leadingBlock_action] at hInverse
  have hCoordinate := congrArg
    (fun amplitude : ModeAmplitude (BackwardWave Unit) =>
      amplitude (BackwardWave.mk ())) hInverse
  simp only [ModeTransform.toLinearMap, Matrix.toLpLin_apply, Matrix.mulVec,
    dotProduct, sourceScalarAmplitude] at hCoordinate
  rw [← BackwardWave.channelEquiv.symm.sum_comp] at hCoordinate
  simp only [Finset.univ_unique, Finset.sum_singleton] at hCoordinate
  change dateChainEntry matrix 0 0 *
      ((matrix.leadingBlockInverse hLeading)
        (BackwardWave.mk ()) (BackwardWave.mk ()) * 1) = 1 at hCoordinate
  have hEntry :=
    (dateChain_hasBijectiveLeadingBlock_iff_entry11_ne_zero matrix).mp hLeading
  apply (eq_div_iff hEntry).2
  simpa [mul_comm] using hCoordinate

/-- The zero-return reflected scalar entry of a singleton DATE-ordered chain. -/
lemma dateChain_rightTerminatedReflection_entry_zero
    (matrix : BackwardFirstChainTransform Unit Unit)
    (hLeading : matrix.HasBijectiveLeadingBlock)
    (hPivot : matrix.HasBijectiveRightTerminationPivot
      (0 : RightLoadTransform Unit)) :
    (matrix.rightTerminatedReflectionTransform 0 hPivot)
        (BackwardWave.mk ()) (ForwardWave.mk ()) =
      -dateChainEntry matrix 0 1 / dateChainEntry matrix 0 0 := by
  rw [matrix.rightTerminatedReflectionTransform_eq_blockFormula,
    matrix.rightTerminatedReflectionBlockFormula_zero hLeading]
  change -((matrix.leadingBlockInverse hLeading * matrix.upperRightBlock)
    (BackwardWave.mk ()) (ForwardWave.mk ())) = _
  rw [Matrix.mul_apply, ← BackwardWave.channelEquiv.symm.sum_comp]
  simp only [Finset.univ_unique, Finset.sum_singleton]
  rw [dateChain_leadingBlockInverse_entry]
  simp [dateChainEntry, dateBackwardFirstFinEquiv,
    BackwardFirstChainTransform.upperRightBlock, Matrix.toBlocks₁₂]
  ring

/-- A determinant-one singleton chain has zero-return forward entry `1 / M11`. -/
lemma dateChain_rightTerminatedTransmission_entry_zero
    (matrix : BackwardFirstChainTransform Unit Unit)
    (hDeterminant : Matrix.det matrix = 1)
    (hLeading : matrix.HasBijectiveLeadingBlock)
    (hPivot : matrix.HasBijectiveRightTerminationPivot
      (0 : RightLoadTransform Unit)) :
    (matrix.rightTerminatedTransmissionTransform 0 hPivot)
        (ForwardWave.mk ()) (ForwardWave.mk ()) =
      1 / dateChainEntry matrix 0 0 := by
  rw [matrix.rightTerminatedTransmissionTransform_eq_blockFormula,
    matrix.rightTerminatedTransmissionBlockFormula_zero hLeading]
  change matrix.lowerRightBlock (ForwardWave.mk ()) (ForwardWave.mk ()) -
      (matrix.lowerLeftBlock * matrix.leadingBlockInverse hLeading *
        matrix.upperRightBlock) (ForwardWave.mk ()) (ForwardWave.mk ()) = _
  rw [Matrix.mul_apply, ← BackwardWave.channelEquiv.symm.sum_comp]
  simp only [Finset.univ_unique, Finset.sum_singleton]
  rw [Matrix.mul_apply, ← BackwardWave.channelEquiv.symm.sum_comp]
  simp only [Finset.univ_unique, Finset.sum_singleton]
  rw [dateChain_leadingBlockInverse_entry]
  change dateChainEntry matrix 1 1 -
      dateChainEntry matrix 1 0 * (1 / dateChainEntry matrix 0 0) *
        dateChainEntry matrix 0 1 = 1 / dateChainEntry matrix 0 0
  have hEntry :=
    (dateChain_hasBijectiveLeadingBlock_iff_entry11_ne_zero matrix).mp hLeading
  rw [dateChain_det_eq_entry11_mul_entry22_sub_entry12_mul_entry21] at hDeterminant
  apply (eq_div_iff hEntry).2
  field_simp [hEntry]
  linear_combination hDeterminant

/-!

## B. Relational zero-return responses

-/

/-- The exact gates for DATE's `c_N = 0` termination.

The first field validates every source ring-to-chain conversion. The second is the scalar
specialization of the zero-return pivot gate from `TwoPortChainTermination.lean:686-710`.
-/
structure DateCascadeTerminationHypotheses (stages : List DateCascadeStage) : Prop where
  /-- Every DATE ring has the transmission pivot required by its chain view. -/
  ringTransmission : ∀ stage ∈ stages, stage.HasBijectiveRingTransmission
  /-- The complete cascade's source entry `M11` is nonzero. -/
  entry11_ne_zero : dateChainEntry (dateCascadeComposition stages) 0 0 ≠ 0

/-- The source `M11 != 0` gate makes the cascade's singleton leading block bijective. -/
lemma DateCascadeTerminationHypotheses.hasBijectiveLeadingBlock
    {stages : List DateCascadeStage}
    (h : DateCascadeTerminationHypotheses stages) :
    (dateCascadeComposition stages).HasBijectiveLeadingBlock :=
  (dateChain_hasBijectiveLeadingBlock_iff_entry11_ne_zero _).2 h.entry11_ne_zero

/-- The source `M11 != 0` gate supplies the zero-return termination pivot. -/
lemma DateCascadeTerminationHypotheses.hasBijectiveZeroReturnPivot
    {stages : List DateCascadeStage}
    (h : DateCascadeTerminationHypotheses stages) :
    (dateCascadeComposition stages).HasBijectiveRightTerminationPivot
      (0 : RightLoadTransform Unit) :=
  (dateCascadeComposition stages).hasBijectiveRightTerminationPivot_zero
    h.hasBijectiveLeadingBlock

/-- DATE's relational cascade has a well-posed `c_N = 0` termination on the exact pivot gate. -/
lemma DateCascadeTerminationHypotheses.hasWellPosedZeroReturn
    {stages : List DateCascadeStage}
    (h : DateCascadeTerminationHypotheses stages) :
    (dateCascadeBehavior stages).HasWellPosedRightTermination
      (RightLoadBehavior.zeroReflection : RightLoadBehavior Unit) := by
  rw [dateCascadeBehavior_eq_composition_toBehavior stages h.ringTransmission]
  simpa using
    (dateCascadeComposition stages).toBehavior_hasWellPosedRightTermination_of_hasBijectivePivot
        (0 : RightLoadTransform Unit) h.hasBijectiveZeroReturnPivot

/-- The left-reflection transform extracted from DATE's terminated relational cascade. -/
noncomputable def dateTerminatedCascadeReflectionTransform
    (stages : List DateCascadeStage)
    (h : DateCascadeTerminationHypotheses stages) :
    ModeTransform (ForwardWave Unit) (BackwardWave Unit) :=
  (dateCascadeBehavior stages).rightTerminatedReflectionTransform
    RightLoadBehavior.zeroReflection h.hasWellPosedZeroReturn

/-- The right-plane forward transform extracted from DATE's terminated relational cascade. -/
noncomputable def dateTerminatedCascadeTransmissionTransform
    (stages : List DateCascadeStage)
    (h : DateCascadeTerminationHypotheses stages) :
    ModeTransform (ForwardWave Unit) (ForwardWave Unit) :=
  (dateCascadeBehavior stages).rightTerminatedTransmissionTransform
    RightLoadBehavior.zeroReflection h.hasWellPosedZeroReturn

/-- DATE's complex field-amplitude reflection coefficient at a zero-return termination. -/
noncomputable def dateTerminatedCascadeReflectivity
    (stages : List DateCascadeStage)
    (h : DateCascadeTerminationHypotheses stages) : ℂ :=
  dateTerminatedCascadeReflectionTransform stages h
    (BackwardWave.mk ()) (ForwardWave.mk ())

/-- DATE's complex field-amplitude transmission coefficient at the right termination plane. -/
noncomputable def dateTerminatedCascadeTransmissivity
    (stages : List DateCascadeStage)
    (h : DateCascadeTerminationHypotheses stages) : ℂ :=
  dateTerminatedCascadeTransmissionTransform stages h
    (ForwardWave.mk ()) (ForwardWave.mk ())

/-- The relationally extracted DATE reflection transform equals the chain zero-return response. -/
lemma dateTerminatedCascadeReflectionTransform_eq_chain
    (stages : List DateCascadeStage)
    (h : DateCascadeTerminationHypotheses stages) :
    dateTerminatedCascadeReflectionTransform stages h =
      (dateCascadeComposition stages).rightTerminatedReflectionTransform 0
        h.hasBijectiveZeroReturnPivot := by
  apply ModeTransform.toBehavior_injective
  rw [dateTerminatedCascadeReflectionTransform,
    BackwardFirstTwoPortBehavior.toBehavior_rightTerminatedReflectionTransform,
    (dateCascadeComposition stages).toBehavior_rightTerminatedReflectionTransform,
    dateCascadeBehavior_eq_composition_toBehavior stages h.ringTransmission,
    RightLoadBehavior.ofReflection_zero]

/-- The relationally extracted DATE forward transform equals the chain zero-return response. -/
lemma dateTerminatedCascadeTransmissionTransform_eq_chain
    (stages : List DateCascadeStage)
    (h : DateCascadeTerminationHypotheses stages) :
    dateTerminatedCascadeTransmissionTransform stages h =
      (dateCascadeComposition stages).rightTerminatedTransmissionTransform 0
        h.hasBijectiveZeroReturnPivot := by
  apply ModeTransform.toBehavior_injective
  rw [dateTerminatedCascadeTransmissionTransform,
    BackwardFirstTwoPortBehavior.toBehavior_rightTerminatedTransmissionTransform,
    (dateCascadeComposition stages).toBehavior_rightTerminatedTransmissionTransform,
    dateCascadeBehavior_eq_composition_toBehavior stages h.ringTransmission,
    RightLoadBehavior.ofReflection_zero]

/-- DATE'14 Thm. 5: the terminated reflection is `-M12 / M11`.

The quotient is a theorem about the transform extracted from the loaded relational behavior;
it is not the definition of `dateTerminatedCascadeReflectivity`.
-/
theorem dateTerminatedCascade_reflectivity_eq_neg_entry12_div_entry11
    (stages : List DateCascadeStage)
    (h : DateCascadeTerminationHypotheses stages) :
    dateTerminatedCascadeReflectivity stages h =
      -dateChainEntry (dateCascadeComposition stages) 0 1 /
        dateChainEntry (dateCascadeComposition stages) 0 0 := by
  rw [dateTerminatedCascadeReflectivity,
    dateTerminatedCascadeReflectionTransform_eq_chain]
  exact dateChain_rightTerminatedReflection_entry_zero _
    h.hasBijectiveLeadingBlock h.hasBijectiveZeroReturnPivot

/-- DATE'14 Thm. 5: the terminated forward response is `1 / M11`.

This reduction from the Schur response uses the determinant-one consequence of the exact
per-ring chain gates.
-/
theorem dateTerminatedCascade_transmissivity_eq_one_div_entry11
    (stages : List DateCascadeStage)
    (h : DateCascadeTerminationHypotheses stages) :
    dateTerminatedCascadeTransmissivity stages h =
      1 / dateChainEntry (dateCascadeComposition stages) 0 0 := by
  rw [dateTerminatedCascadeTransmissivity,
    dateTerminatedCascadeTransmissionTransform_eq_chain]
  exact dateChain_rightTerminatedTransmission_entry_zero _
    (dateCascadeComposition_det stages h.ringTransmission)
    h.hasBijectiveLeadingBlock h.hasBijectiveZeroReturnPivot

/-!

## C. Corrected identical-cascade Sylvester form

-/

/-- The exact joint domain for the corrected relational/Sylvester specialization.

It retains the ring chain pivot, all Sylvester hypotheses, and the distinct `M11 != 0`
termination pivot for the selected count.
-/
structure DateIdenticalTerminationHypotheses
    (stage : DateCascadeStage) (count : ℕ) : Prop where
  /-- The repeated ring admits DATE's source chain presentation. -/
  ringTransmission : stage.HasBijectiveRingTransmission
  /-- The one-stage matrix lies in the source's Sylvester domain. -/
  sylvester : DateSylvesterHypotheses stage.compositionMatrix
  /-- The selected matrix power has nonzero termination pivot. -/
  entry11_ne_zero :
    dateChainEntry (dateIdenticalCascadeComposition stage count) 0 0 ≠ 0

/-- Joint identical-cascade gates viewed as heterogeneous termination gates. -/
lemma DateIdenticalTerminationHypotheses.toCascade
    {stage : DateCascadeStage} {count : ℕ}
    (h : DateIdenticalTerminationHypotheses stage count) :
    DateCascadeTerminationHypotheses (List.replicate count stage) where
  ringTransmission := by
    intro repeated hRepeated
    rw [List.eq_of_mem_replicate hRepeated]
    exact h.ringTransmission
  entry11_ne_zero := by
    simpa [dateIdenticalCascadeComposition] using h.entry11_ne_zero

/-- Reflection of an identical DATE cascade, still extracted from its terminated behavior. -/
noncomputable def dateIdenticalTerminatedCascadeReflectivity
    (stage : DateCascadeStage) (count : ℕ)
    (h : DateIdenticalTerminationHypotheses stage count) : ℂ :=
  dateTerminatedCascadeReflectivity (List.replicate count stage) h.toCascade

/-- Forward response of an identical DATE cascade at its right termination plane. -/
noncomputable def dateIdenticalTerminatedCascadeTransmissivity
    (stage : DateCascadeStage) (count : ℕ)
    (h : DateIdenticalTerminationHypotheses stage count) : ℂ :=
  dateTerminatedCascadeTransmissivity (List.replicate count stage) h.toCascade

/-- The `M11` entry of DATE's Sylvester matrix form. -/
lemma dateSylvesterClosedForm_entry11
    (matrix : BackwardFirstChainTransform Unit Unit) (count : ℕ) :
    dateChainEntry (dateSylvesterClosedForm matrix count) 0 0 =
      dateSylvesterSineCoefficient matrix count * dateChainEntry matrix 0 0 -
        dateSylvesterSineCoefficient matrix ((count : ℤ) - 1) := by
  simp [dateChainEntry, dateSylvesterClosedForm, dateBackwardFirstFinEquiv]

/-- The `M12` entry of DATE's Sylvester matrix form. -/
lemma dateSylvesterClosedForm_entry12
    (matrix : BackwardFirstChainTransform Unit Unit) (count : ℕ) :
    dateChainEntry (dateSylvesterClosedForm matrix count) 0 1 =
      dateSylvesterSineCoefficient matrix count * dateChainEntry matrix 0 1 := by
  simp [dateChainEntry, dateSylvesterClosedForm, dateBackwardFirstFinEquiv]

/-- A DATE stage's `m11` entry is its backward bus factor divided by `R`. -/
lemma DateCascadeStage.compositionMatrix_entry11 (stage : DateCascadeStage) :
    dateChainEntry stage.compositionMatrix 0 0 =
      stage.backwardContinuityFactor / dateForwardTransfer stage.ring := by
  simp [dateChainEntry, dateBackwardFirstFinEquiv,
    DateCascadeStage.compositionMatrix, Matrix.mul_apply,
    DateCascadeStage.continuityChainMatrix,
    dateFourPortBackwardFirstChainMatrix,
    ← BackwardWave.channelEquiv.symm.sum_comp,
    ← ForwardWave.channelEquiv.symm.sum_comp]
  simp [div_eq_mul_inv]

/-- A DATE stage's `m12` entry is `-E T / R` in source notation. -/
lemma DateCascadeStage.compositionMatrix_entry12 (stage : DateCascadeStage) :
    dateChainEntry stage.compositionMatrix 0 1 =
      -stage.backwardContinuityFactor * dateBackwardTransfer stage.ring /
        dateForwardTransfer stage.ring := by
  simp [dateChainEntry, dateBackwardFirstFinEquiv,
    DateCascadeStage.compositionMatrix, Matrix.mul_apply,
    DateCascadeStage.continuityChainMatrix,
    dateFourPortBackwardFirstChainMatrix,
    ← BackwardWave.channelEquiv.symm.sum_comp,
    ← ForwardWave.channelEquiv.symm.sum_comp]
  ring

/-- The common denominator obtained from the proved backward-first Sylvester entries. -/
def dateIdenticalSylvesterTerminationDenominator
    (stage : DateCascadeStage) (count : ℕ) : ℂ :=
  stage.backwardContinuityFactor *
      dateSylvesterSineCoefficient stage.compositionMatrix count -
    dateForwardTransfer stage.ring *
      dateSylvesterSineCoefficient stage.compositionMatrix ((count : ℤ) - 1)

/-- On the Sylvester domain, repeated `M11` is the corrected denominator divided by `R`. -/
lemma dateIdenticalCascadeComposition_entry11_eq_sylvesterDenominator_div_forwardTransfer
    (stage : DateCascadeStage) (count : ℕ)
    (h : DateIdenticalTerminationHypotheses stage count) :
    dateChainEntry (dateIdenticalCascadeComposition stage count) 0 0 =
      dateIdenticalSylvesterTerminationDenominator stage count /
        dateForwardTransfer stage.ring := by
  rw [dateIdenticalCascadeComposition_eq_sylvesterClosedForm stage count h.sylvester,
    dateSylvesterClosedForm_entry11, stage.compositionMatrix_entry11]
  have hForward :=
    (stage.hasBijectiveRingTransmission_iff_forwardTransfer_ne_zero).mp
      h.ringTransmission
  rw [dateIdenticalSylvesterTerminationDenominator]
  field_simp [hForward]

/-- The selected corrected denominator is nonzero on the termination domain. -/
lemma DateIdenticalTerminationHypotheses.sylvesterDenominator_ne_zero
    {stage : DateCascadeStage} {count : ℕ}
    (h : DateIdenticalTerminationHypotheses stage count) :
    dateIdenticalSylvesterTerminationDenominator stage count ≠ 0 := by
  have hEntry := h.entry11_ne_zero
  rw [dateIdenticalCascadeComposition_entry11_eq_sylvesterDenominator_div_forwardTransfer
    stage count h] at hEntry
  exact (div_ne_zero_iff.mp hEntry).1

/-- Corrected relational/Sylvester reflection; this is not printed DATE'14 Thm. 6. -/
lemma dateIdenticalTerminatedCascade_reflectivity_eq_relationalSylvesterForm
    (stage : DateCascadeStage) (count : ℕ)
    (h : DateIdenticalTerminationHypotheses stage count) :
    dateIdenticalTerminatedCascadeReflectivity stage count h =
      dateBackwardTransfer stage.ring * stage.backwardContinuityFactor *
          dateSylvesterSineCoefficient stage.compositionMatrix count /
        dateIdenticalSylvesterTerminationDenominator stage count := by
  rw [dateIdenticalTerminatedCascadeReflectivity,
    dateTerminatedCascade_reflectivity_eq_neg_entry12_div_entry11]
  change -dateChainEntry (dateIdenticalCascadeComposition stage count) 0 1 /
      dateChainEntry (dateIdenticalCascadeComposition stage count) 0 0 = _
  rw [dateIdenticalCascadeComposition_eq_sylvesterClosedForm stage count h.sylvester,
    dateSylvesterClosedForm_entry11, dateSylvesterClosedForm_entry12,
    stage.compositionMatrix_entry11, stage.compositionMatrix_entry12]
  have hForward :=
    (stage.hasBijectiveRingTransmission_iff_forwardTransfer_ne_zero).mp
      h.ringTransmission
  have hDenominator := h.sylvesterDenominator_ne_zero
  rw [dateIdenticalSylvesterTerminationDenominator] at hDenominator ⊢
  field_simp [hForward, hDenominator]

/-- Corrected relational/Sylvester forward response; this is not printed DATE'14 Thm. 6. -/
lemma dateIdenticalTerminatedCascade_transmissivity_eq_relationalSylvesterForm
    (stage : DateCascadeStage) (count : ℕ)
    (h : DateIdenticalTerminationHypotheses stage count) :
    dateIdenticalTerminatedCascadeTransmissivity stage count h =
      dateForwardTransfer stage.ring /
        dateIdenticalSylvesterTerminationDenominator stage count := by
  rw [dateIdenticalTerminatedCascadeTransmissivity,
    dateTerminatedCascade_transmissivity_eq_one_div_entry11]
  change 1 / dateChainEntry (dateIdenticalCascadeComposition stage count) 0 0 = _
  rw [dateIdenticalCascadeComposition_entry11_eq_sylvesterDenominator_div_forwardTransfer
    stage count h]
  have hForward :=
    (stage.hasBijectiveRingTransmission_iff_forwardTransfer_ne_zero).mp
      h.ringTransmission
  field_simp [hForward, h.sylvesterDenominator_ne_zero]

end MicroringCascade

end

end Optics
