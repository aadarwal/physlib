/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Systems.Cascade.Termination

/-!
# Regression tests for terminated DATE cascades

## i. Overview

The positive fixture uses the rational unitary ring data `(r,t) = (3/5,4/5)`, a half-turn ring
phase, and a quarter-turn following bus. Its one-stage matrix has nonzero off-diagonal entries,
so the three-stage response detects the reflection sign, coordinate order, load orientation, and
transmission denominator. The two- and three-stage folds are expanded directly from the matrices.

The negative fixture keeps the ring pivot `R = -24/25 != 0`, while its two-stage product has
`M11 = 0`. An explicit nonzero vector in the raw termination-pivot kernel proves that the chain
termination is not well posed. Thus the complete-cascade pivot gate can genuinely fail.

## ii. Key results

- `dateTerminationRegression_rawFold_two` and `_three`: joined raw DATE-stage folds.
- `dateTerminationRegression_two_responses_by_hand`: reflection `0`, transmission `-1`.
- `dateTerminationRegression_three_responses_by_hand`: reflection `8 I / 17`, transmission
  `-15 I / 17`.
- `dateTerminationRegressionSingular_not_wellPosed`: the `M11 = 0` control.

## iii. Table of contents

- A. Positive rational DATE stage
- B. Raw two- and three-stage folds
- C. Terminated responses from the behavior
- D. Singular parameter control

## iv. References

The response anchors use the graph of the behavior-derived transforms and the raw termination
equations. They do not invoke either DATE'14 Thm. 5 quotient theorem or either corrected
identical-cascade Sylvester lemma from `Termination.lean`.
-/

@[expose] public section

namespace Optics

noncomputable section

namespace MicroringCascade

open MicroringSourceBridge

/-!

## A. Positive rational DATE stage

-/

/-- Rational 3-4-5 DATE data with a half-turn ring phase and no attenuation. -/
def dateTerminationRegressionRing : DateParameters where
  reflectivity := 3 / 5
  transmissivity := 4 / 5
  couplingLength := 1
  powerAttenuation := 0
  wavelength := 2
  effectiveIndex := 1

/-- The positive fixture adds a quarter-turn following bus. -/
def dateTerminationRegressionStage : DateCascadeStage where
  ring := dateTerminationRegressionRing
  busLength := 1 / 2

/-- The fixture ring has full-round-trip phase `pi`. -/
lemma dateTerminationRegressionRing_roundTripPhase :
    dateTerminationRegressionRing.roundTripPhase = Real.pi := by
  rw [DateParameters.roundTripPhase]
  norm_num [dateTerminationRegressionRing]

/-- The fixture ring has unit field attenuation. -/
lemma dateTerminationRegressionRing_fieldAttenuation :
    dateTerminationRegressionRing.fieldAttenuation = 1 := by
  norm_num [DateParameters.fieldAttenuation, dateTerminationRegressionRing]

/-- The fixture ring has full- and half-turn carrier factors `-1` and `-I`. -/
lemma dateTerminationRegressionRing_phaseFactors :
    dateTerminationRegressionRing.phaseFactor = -1 ∧
      dateTerminationRegressionRing.halfPhaseFactor = -Complex.I := by
  constructor
  · rw [DateParameters.phaseFactor, dateTerminationRegressionRing_roundTripPhase]
    norm_num [MatchedPropagation.carrierPhaseFactor]
  · rw [DateParameters.halfPhaseFactor,
      dateTerminationRegressionRing_roundTripPhase]
    norm_num [MatchedPropagation.carrierPhaseFactor]

/-- The fixture's DATE denominator is `34/25`. -/
lemma dateTerminationRegressionRing_denominator :
    dateTerminationRegressionRing.denominator = 34 / 25 := by
  rw [DateParameters.denominator, dateTerminationRegressionRing_phaseFactors.1,
    dateTerminationRegressionRing_fieldAttenuation]
  norm_num [dateTerminationRegressionRing]

/-- Direct source expansion gives `R = -15/17` and `T = 8 I/17`. -/
lemma dateTerminationRegressionRing_transfers :
    dateForwardTransfer dateTerminationRegressionRing = -15 / 17 ∧
      dateBackwardTransfer dateTerminationRegressionRing =
        (8 / 17 : ℂ) * Complex.I := by
  constructor
  · rw [dateForwardTransfer, dateTerminationRegressionRing_denominator,
      dateTerminationRegressionRing_phaseFactors.1,
      dateTerminationRegressionRing_fieldAttenuation]
    norm_num [dateTerminationRegressionRing]
  · rw [dateBackwardTransfer, dateTerminationRegressionRing_denominator,
      dateTerminationRegressionRing_phaseFactors.2,
      dateTerminationRegressionRing_fieldAttenuation]
    norm_num [dateTerminationRegressionRing]
    ring

/-- The positive fixture satisfies the exact ring-to-chain pivot. -/
lemma dateTerminationRegressionStage_hasBijectiveRingTransmission :
    dateTerminationRegressionStage.HasBijectiveRingTransmission := by
  rw [dateTerminationRegressionStage.hasBijectiveRingTransmission_iff_forwardTransfer_ne_zero]
  rw [show dateTerminationRegressionStage.ring = dateTerminationRegressionRing by rfl,
    dateTerminationRegressionRing_transfers.1]
  norm_num

/-- The following bus phase is exactly `pi/2`. -/
lemma dateTerminationRegressionStage_busPhase :
    dateTerminationRegressionStage.busPhase = Real.pi / 2 := by
  norm_num [dateTerminationRegressionStage, DateCascadeStage.busPhase,
    dateTerminationRegressionRing]
  ring

/-- The backward and forward bus factors are `I` and `-I`. -/
lemma dateTerminationRegressionStage_signedContinuity :
    dateTerminationRegressionStage.backwardContinuityFactor = Complex.I ∧
      dateTerminationRegressionStage.forwardContinuityFactor = -Complex.I := by
  rw [DateCascadeStage.backwardContinuityFactor,
    DateCascadeStage.forwardContinuityFactor,
    dateTerminationRegressionStage_busPhase]
  constructor <;>
    simp [MatchedPropagation.carrierPhaseFactor, Real.Angle.toCircle_coe,
      Circle.coe_exp, Complex.exp_mul_I]

/-- The concrete one-stage matrix in DATE's backward-first coordinates. -/
def dateTerminationRegressionMatrix : BackwardFirstChainTransform Unit Unit
  | Sum.inl _, Sum.inl _ => -(17 / 15 : ℂ) * Complex.I
  | Sum.inl _, Sum.inr _ => -(8 / 15 : ℂ)
  | Sum.inr _, Sum.inl _ => -(8 / 15 : ℂ)
  | Sum.inr _, Sum.inr _ => (17 / 15 : ℂ) * Complex.I

/-- The parameter-derived DATE stage displays the concrete matrix entry by entry. -/
lemma dateTerminationRegressionStage_compositionMatrix :
    dateTerminationRegressionStage.compositionMatrix =
      dateTerminationRegressionMatrix := by
  ext (output | output) (input | input) <;>
    rcases output with ⟨⟨⟩⟩ <;>
    rcases input with ⟨⟨⟩⟩ <;>
    simp only [DateCascadeStage.compositionMatrix, Matrix.mul_apply,
      Fintype.sum_sum_type]
  all_goals simp_rw [← BackwardWave.channelEquiv.symm.sum_comp,
    ← ForwardWave.channelEquiv.symm.sum_comp]
  all_goals simp [DateCascadeStage.continuityChainMatrix,
    dateTerminationRegressionStage_signedContinuity.1,
    dateTerminationRegressionStage_signedContinuity.2,
    dateFourPortBackwardFirstChainMatrix,
    show dateTerminationRegressionStage.ring = dateTerminationRegressionRing by rfl,
    dateTerminationRegressionRing_transfers.1,
    dateTerminationRegressionRing_transfers.2,
    dateTerminationRegressionMatrix]
  all_goals ring_nf
  all_goals (try rw [Complex.I_sq])
  all_goals (try rw [show Complex.I ^ 3 = -Complex.I by
    calc
      Complex.I ^ 3 = Complex.I ^ 2 * Complex.I := by rw [pow_succ]
      _ = -Complex.I := by rw [Complex.I_sq]; ring])
  all_goals norm_num
  all_goals ring

/-- The concrete stage satisfies the complete source Sylvester domain by direct calculation. -/
lemma dateTerminationRegressionStage_sylvester :
    DateSylvesterHypotheses dateTerminationRegressionStage.compositionMatrix := by
  rw [dateTerminationRegressionStage_compositionMatrix]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← Matrix.det_reindex_self dateBackwardFirstFinEquiv.symm
      dateTerminationRegressionMatrix, Matrix.det_fin_two]
    simp [Matrix.reindex_apply, dateBackwardFirstFinEquiv,
      dateTerminationRegressionMatrix]
    ring_nf
    rw [Complex.I_sq]
    norm_num
  · norm_num [dateChainEntry, dateBackwardFirstFinEquiv,
      dateTerminationRegressionMatrix]
  · norm_num [dateChainEntry, dateBackwardFirstFinEquiv,
      dateTerminationRegressionMatrix]
  · simp [dateChainEntry, dateBackwardFirstFinEquiv,
      dateTerminationRegressionMatrix]
    simp only [starRingEnd_apply]
    norm_num
  · simp [dateChainEntry, dateBackwardFirstFinEquiv,
      dateTerminationRegressionMatrix]
    simp only [starRingEnd_apply]
    norm_num

/-!

## B. Raw two- and three-stage folds

-/

/-- The raw two-stage fold is negative identity, expanded without the power theorem. -/
lemma dateTerminationRegression_rawFold_two :
    dateIdenticalCascadeComposition dateTerminationRegressionStage 2 = -1 := by
  change
    (1 * dateTerminationRegressionStage.compositionMatrix) *
        dateTerminationRegressionStage.compositionMatrix = -1
  rw [Matrix.one_mul, dateTerminationRegressionStage_compositionMatrix]
  ext (output | output) (input | input) <;>
    rcases output with ⟨⟨⟩⟩ <;>
    rcases input with ⟨⟨⟩⟩ <;>
    simp only [Matrix.mul_apply, Fintype.sum_sum_type]
  all_goals simp_rw [← BackwardWave.channelEquiv.symm.sum_comp,
    ← ForwardWave.channelEquiv.symm.sum_comp]
  all_goals simp [dateTerminationRegressionMatrix]
  all_goals ring_nf
  all_goals (try rw [Complex.I_sq])
  all_goals norm_num

/-- The raw three-stage fold is the negative one-stage matrix. -/
lemma dateTerminationRegression_rawFold_three :
    dateIdenticalCascadeComposition dateTerminationRegressionStage 3 =
      -dateTerminationRegressionMatrix := by
  change
    ((1 * dateTerminationRegressionStage.compositionMatrix) *
        dateTerminationRegressionStage.compositionMatrix) *
      dateTerminationRegressionStage.compositionMatrix =
        -dateTerminationRegressionMatrix
  have hTwo := dateTerminationRegression_rawFold_two
  change
    (1 * dateTerminationRegressionStage.compositionMatrix) *
      dateTerminationRegressionStage.compositionMatrix = -1 at hTwo
  rw [hTwo]
  rw [dateTerminationRegressionStage_compositionMatrix, Matrix.neg_mul,
    Matrix.one_mul]

/-- The two-stage `M11` pivot is `-1`. -/
lemma dateTerminationRegression_rawFold_two_entry11 :
    dateChainEntry
        (dateIdenticalCascadeComposition dateTerminationRegressionStage 2) 0 0 = -1 := by
  rw [dateTerminationRegression_rawFold_two]
  norm_num [dateChainEntry, dateBackwardFirstFinEquiv, Matrix.one_apply]

/-- The three-stage `M11` pivot is `17 I/15`. -/
lemma dateTerminationRegression_rawFold_three_entry11 :
    dateChainEntry
        (dateIdenticalCascadeComposition dateTerminationRegressionStage 3) 0 0 =
      (17 / 15 : ℂ) * Complex.I := by
  rw [dateTerminationRegression_rawFold_three]
  norm_num [dateChainEntry, dateBackwardFirstFinEquiv,
    dateTerminationRegressionMatrix]

/-- The positive two-stage fixture satisfies all termination and source gates. -/
lemma dateTerminationRegressionHypotheses_two :
    DateIdenticalTerminationHypotheses dateTerminationRegressionStage 2 where
  ringTransmission := dateTerminationRegressionStage_hasBijectiveRingTransmission
  sylvester := dateTerminationRegressionStage_sylvester
  entry11_ne_zero := by
    rw [dateTerminationRegression_rawFold_two_entry11]
    norm_num

/-- The positive three-stage fixture satisfies all termination and source gates. -/
lemma dateTerminationRegressionHypotheses_three :
    DateIdenticalTerminationHypotheses dateTerminationRegressionStage 3 where
  ringTransmission := dateTerminationRegressionStage_hasBijectiveRingTransmission
  sylvester := dateTerminationRegressionStage_sylvester
  entry11_ne_zero := by
    rw [dateTerminationRegression_rawFold_three_entry11]
    intro hZero
    have hIm := congrArg Complex.im hZero
    norm_num at hIm

/-!

## C. Terminated responses from the behavior

-/

/-- The two-stage raw pivot acts as multiplication by `-1`. -/
lemma dateTerminationRegression_negativeOne_pivot_action
    (amplitude : ModeAmplitude (BackwardWave Unit)) :
    ((-1 : BackwardFirstChainTransform Unit Unit).rightTerminationPivot 0).toLinearMap
        amplitude = sourceScalarAmplitude (-amplitude (BackwardWave.mk ())) := by
  apply WithLp.ofLp_injective 2
  funext output
  rcases output with ⟨⟨⟩⟩
  simp [BackwardFirstChainTransform.rightTerminationPivot,
    BackwardFirstChainTransform.leadingBlock,
    BackwardFirstChainTransform.lowerLeftBlock, Matrix.toBlocks₁₁,
    Matrix.toBlocks₂₁, ModeTransform.toLinearMap, Matrix.toLpLin_apply,
    Matrix.mulVec, dotProduct, sourceScalarAmplitude,
    ← BackwardWave.channelEquiv.symm.sum_comp, Matrix.one_apply]

/-- The two-stage raw incident block vanishes. -/
lemma dateTerminationRegression_negativeOne_incident_action
    (amplitude : ModeAmplitude (ForwardWave Unit)) :
    ((-1 : BackwardFirstChainTransform Unit Unit).rightTerminationIncidentBlock 0).toLinearMap
        amplitude = 0 := by
  apply WithLp.ofLp_injective 2
  funext output
  rcases output with ⟨⟨⟩⟩
  simp [BackwardFirstChainTransform.rightTerminationIncidentBlock,
    BackwardFirstChainTransform.upperRightBlock,
    BackwardFirstChainTransform.lowerRightBlock, Matrix.toBlocks₁₂,
    Matrix.toBlocks₂₂, ModeTransform.toLinearMap, Matrix.toLpLin_apply,
    Matrix.mulVec, dotProduct,
    ← ForwardWave.channelEquiv.symm.sum_comp, Matrix.one_apply]

/-- The two-stage raw lower-left block vanishes. -/
lemma dateTerminationRegression_negativeOne_lowerLeft_action
    (amplitude : ModeAmplitude (BackwardWave Unit)) :
    (-1 : BackwardFirstChainTransform Unit Unit).lowerLeftBlock.toLinearMap amplitude = 0 := by
  apply WithLp.ofLp_injective 2
  funext output
  rcases output with ⟨⟨⟩⟩
  simp [BackwardFirstChainTransform.lowerLeftBlock, Matrix.toBlocks₂₁,
    ModeTransform.toLinearMap, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    ← BackwardWave.channelEquiv.symm.sum_comp]

/-- The two-stage raw lower-right block acts as multiplication by `-1`. -/
lemma dateTerminationRegression_negativeOne_lowerRight_action
    (amplitude : ModeAmplitude (ForwardWave Unit)) :
    (-1 : BackwardFirstChainTransform Unit Unit).lowerRightBlock.toLinearMap amplitude =
      sourceScalarAmplitude (-amplitude (ForwardWave.mk ())) := by
  apply WithLp.ofLp_injective 2
  funext output
  rcases output with ⟨⟨⟩⟩
  simp [BackwardFirstChainTransform.lowerRightBlock, Matrix.toBlocks₂₂,
    ModeTransform.toLinearMap, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    sourceScalarAmplitude, ← ForwardWave.channelEquiv.symm.sum_comp,
    Matrix.one_apply]

/-- The three-stage raw pivot acts by `17 I/15`. -/
lemma dateTerminationRegression_negativeMatrix_pivot_action
    (amplitude : ModeAmplitude (BackwardWave Unit)) :
    ((-dateTerminationRegressionMatrix).rightTerminationPivot 0).toLinearMap
        amplitude =
      sourceScalarAmplitude
        ((17 / 15 : ℂ) * Complex.I * amplitude (BackwardWave.mk ())) := by
  apply WithLp.ofLp_injective 2
  funext output
  rcases output with ⟨⟨⟩⟩
  simp [BackwardFirstChainTransform.rightTerminationPivot,
    BackwardFirstChainTransform.leadingBlock,
    BackwardFirstChainTransform.lowerLeftBlock, Matrix.toBlocks₁₁,
    Matrix.toBlocks₂₁, ModeTransform.toLinearMap, Matrix.toLpLin_apply,
    Matrix.mulVec, dotProduct, sourceScalarAmplitude,
    ← BackwardWave.channelEquiv.symm.sum_comp,
    dateTerminationRegressionMatrix]

/-- The three-stage raw incident block acts by `-8/15`. -/
lemma dateTerminationRegression_negativeMatrix_incident_action
    (amplitude : ModeAmplitude (ForwardWave Unit)) :
    ((-dateTerminationRegressionMatrix).rightTerminationIncidentBlock 0).toLinearMap
        amplitude =
      sourceScalarAmplitude (-(8 / 15 : ℂ) * amplitude (ForwardWave.mk ())) := by
  apply WithLp.ofLp_injective 2
  funext output
  rcases output with ⟨⟨⟩⟩
  simp [BackwardFirstChainTransform.rightTerminationIncidentBlock,
    BackwardFirstChainTransform.upperRightBlock,
    BackwardFirstChainTransform.lowerRightBlock, Matrix.toBlocks₁₂,
    Matrix.toBlocks₂₂, ModeTransform.toLinearMap, Matrix.toLpLin_apply,
    Matrix.mulVec, dotProduct, sourceScalarAmplitude,
    ← ForwardWave.channelEquiv.symm.sum_comp,
    dateTerminationRegressionMatrix]

/-- The three-stage raw lower-left block acts by `8/15`. -/
lemma dateTerminationRegression_negativeMatrix_lowerLeft_action
    (amplitude : ModeAmplitude (BackwardWave Unit)) :
    (-dateTerminationRegressionMatrix).lowerLeftBlock.toLinearMap amplitude =
      sourceScalarAmplitude ((8 / 15 : ℂ) * amplitude (BackwardWave.mk ())) := by
  apply WithLp.ofLp_injective 2
  funext output
  rcases output with ⟨⟨⟩⟩
  simp [BackwardFirstChainTransform.lowerLeftBlock, Matrix.toBlocks₂₁,
    ModeTransform.toLinearMap, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    sourceScalarAmplitude, ← BackwardWave.channelEquiv.symm.sum_comp,
    dateTerminationRegressionMatrix]

/-- The three-stage raw lower-right block acts by `-17 I/15`. -/
lemma dateTerminationRegression_negativeMatrix_lowerRight_action
    (amplitude : ModeAmplitude (ForwardWave Unit)) :
    (-dateTerminationRegressionMatrix).lowerRightBlock.toLinearMap amplitude =
      sourceScalarAmplitude
        (-(17 / 15 : ℂ) * Complex.I * amplitude (ForwardWave.mk ())) := by
  apply WithLp.ofLp_injective 2
  funext output
  rcases output with ⟨⟨⟩⟩
  simp [BackwardFirstChainTransform.lowerRightBlock, Matrix.toBlocks₂₂,
    ModeTransform.toLinearMap, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    sourceScalarAmplitude, ← ForwardWave.channelEquiv.symm.sum_comp,
    dateTerminationRegressionMatrix]

/-- The two-stage behavior directly yields reflection zero. -/
lemma dateTerminationRegression_two_reflectivity_by_hand :
    dateIdenticalTerminatedCascadeReflectivity dateTerminationRegressionStage 2
      dateTerminationRegressionHypotheses_two = 0 := by
  rw [dateIdenticalTerminatedCascadeReflectivity, dateTerminatedCascadeReflectivity,
    dateTerminatedCascadeReflectionTransform_eq_chain]
  let incident :=
    (sourceScalarAmplitude 1 : ModeAmplitude (ForwardWave Unit))
  let response :=
    (dateCascadeComposition
      (List.replicate 2 dateTerminationRegressionStage)).rightTerminatedReflectionTransform 0
        dateTerminationRegressionHypotheses_two.toCascade.hasBijectiveZeroReturnPivot
  change response (BackwardWave.mk ()) (ForwardWave.mk ()) = 0
  have hGraph : (incident, response.toLinearMap incident) ∈ response.toBehavior := by
    rw [ModeTransform.mem_toBehavior_iff_toLinearMap]
  dsimp only [response] at hGraph
  rw [BackwardFirstChainTransform.toBehavior_rightTerminatedReflectionTransform,
    BackwardFirstChainTransform.mem_rightTerminatedReflectionBehavior_iff_pivotEquation]
      at hGraph
  have hRaw :
      dateCascadeComposition (List.replicate 2 dateTerminationRegressionStage) = -1 := by
    simpa [dateIdenticalCascadeComposition] using
      dateTerminationRegression_rawFold_two
  have hPivotAction (amplitude : ModeAmplitude (BackwardWave Unit)) :
      ((dateCascadeComposition
        (List.replicate 2 dateTerminationRegressionStage)).rightTerminationPivot 0).toLinearMap
          amplitude =
        sourceScalarAmplitude (-amplitude (BackwardWave.mk ())) := by
    rw [hRaw]
    exact dateTerminationRegression_negativeOne_pivot_action amplitude
  have hIncidentAction (amplitude : ModeAmplitude (ForwardWave Unit)) :
      ModeTransform.toLinearMap
          (BackwardFirstChainTransform.rightTerminationIncidentBlock
            (dateCascadeComposition
              (List.replicate 2 dateTerminationRegressionStage)) 0) amplitude = 0 := by
    rw [hRaw]
    exact dateTerminationRegression_negativeOne_incident_action amplitude
  rw [hPivotAction, hIncidentAction] at hGraph
  have hCoordinate := congrArg
    (fun amplitude : ModeAmplitude (BackwardWave Unit) =>
      amplitude (BackwardWave.mk ())) hGraph
  simp only [sourceScalarAmplitude] at hCoordinate
  simp only [ModeTransform.toLinearMap, Matrix.toLpLin_apply, Matrix.mulVec,
    dotProduct] at hCoordinate
  rw [← ForwardWave.channelEquiv.symm.sum_comp] at hCoordinate
  simpa [response, incident, sourceScalarAmplitude] using hCoordinate

/-- The two-stage behavior directly yields transmission `-1`. -/
lemma dateTerminationRegression_two_transmissivity_by_hand :
    dateIdenticalTerminatedCascadeTransmissivity dateTerminationRegressionStage 2
      dateTerminationRegressionHypotheses_two = -1 := by
  rw [dateIdenticalTerminatedCascadeTransmissivity, dateTerminatedCascadeTransmissivity,
    dateTerminatedCascadeTransmissionTransform_eq_chain]
  let incident :=
    (sourceScalarAmplitude 1 : ModeAmplitude (ForwardWave Unit))
  let response :=
    (dateCascadeComposition
      (List.replicate 2 dateTerminationRegressionStage)).rightTerminatedTransmissionTransform 0
        dateTerminationRegressionHypotheses_two.toCascade.hasBijectiveZeroReturnPivot
  change response (ForwardWave.mk ()) (ForwardWave.mk ()) = -1
  have hGraph : (incident, response.toLinearMap incident) ∈ response.toBehavior := by
    rw [ModeTransform.mem_toBehavior_iff_toLinearMap]
  dsimp only [response] at hGraph
  rw [BackwardFirstChainTransform.toBehavior_rightTerminatedTransmissionTransform,
    BackwardFirstChainTransform.mem_rightTerminatedTransmissionBehavior_iff_pivotEquation]
      at hGraph
  rcases hGraph with ⟨leftBackward, hPivot, hForward⟩
  have hRaw :
      dateCascadeComposition (List.replicate 2 dateTerminationRegressionStage) = -1 := by
    simpa [dateIdenticalCascadeComposition] using
      dateTerminationRegression_rawFold_two
  have hPivotAction (amplitude : ModeAmplitude (BackwardWave Unit)) :
      ((dateCascadeComposition
        (List.replicate 2 dateTerminationRegressionStage)).rightTerminationPivot 0).toLinearMap
          amplitude =
        sourceScalarAmplitude (-amplitude (BackwardWave.mk ())) := by
    rw [hRaw]
    exact dateTerminationRegression_negativeOne_pivot_action amplitude
  have hIncidentAction (amplitude : ModeAmplitude (ForwardWave Unit)) :
      ModeTransform.toLinearMap
          (BackwardFirstChainTransform.rightTerminationIncidentBlock
            (dateCascadeComposition
              (List.replicate 2 dateTerminationRegressionStage)) 0) amplitude = 0 := by
    rw [hRaw]
    exact dateTerminationRegression_negativeOne_incident_action amplitude
  rw [hPivotAction, hIncidentAction] at hPivot
  have hBackward : leftBackward = 0 := by
    apply WithLp.ofLp_injective 2
    funext output
    rcases output with ⟨⟨⟩⟩
    have hCoordinate := congrArg
      (fun amplitude : ModeAmplitude (BackwardWave Unit) =>
        amplitude (BackwardWave.mk ())) hPivot
    norm_num [sourceScalarAmplitude] at hCoordinate
    exact hCoordinate
  have hLowerLeftAction (amplitude : ModeAmplitude (BackwardWave Unit)) :
      (dateCascadeComposition
        (List.replicate 2 dateTerminationRegressionStage)).lowerLeftBlock.toLinearMap
          amplitude = 0 := by
    rw [hRaw]
    exact dateTerminationRegression_negativeOne_lowerLeft_action amplitude
  have hLowerRightAction (amplitude : ModeAmplitude (ForwardWave Unit)) :
      (dateCascadeComposition
        (List.replicate 2 dateTerminationRegressionStage)).lowerRightBlock.toLinearMap
          amplitude = sourceScalarAmplitude (-amplitude (ForwardWave.mk ())) := by
    rw [hRaw]
    exact dateTerminationRegression_negativeOne_lowerRight_action amplitude
  rw [hLowerLeftAction, hLowerRightAction] at hForward
  have hCoordinate := congrArg
    (fun amplitude : ModeAmplitude (ForwardWave Unit) =>
      amplitude (ForwardWave.mk ())) hForward
  simp only [sourceScalarAmplitude] at hCoordinate
  simp only [ModeTransform.toLinearMap, Matrix.toLpLin_apply, Matrix.mulVec,
    dotProduct] at hCoordinate
  rw [← ForwardWave.channelEquiv.symm.sum_comp] at hCoordinate
  simpa [response, incident, sourceScalarAmplitude] using hCoordinate

/-- The two-stage terminated responses are independently pinned together. -/
lemma dateTerminationRegression_two_responses_by_hand :
    dateIdenticalTerminatedCascadeReflectivity dateTerminationRegressionStage 2
          dateTerminationRegressionHypotheses_two = 0 ∧
      dateIdenticalTerminatedCascadeTransmissivity dateTerminationRegressionStage 2
          dateTerminationRegressionHypotheses_two = -1 :=
  ⟨dateTerminationRegression_two_reflectivity_by_hand,
    dateTerminationRegression_two_transmissivity_by_hand⟩

/-- The three-stage behavior directly yields reflection `8 I/17`. -/
lemma dateTerminationRegression_three_reflectivity_by_hand :
    dateIdenticalTerminatedCascadeReflectivity dateTerminationRegressionStage 3
      dateTerminationRegressionHypotheses_three = (8 / 17 : ℂ) * Complex.I := by
  rw [dateIdenticalTerminatedCascadeReflectivity, dateTerminatedCascadeReflectivity,
    dateTerminatedCascadeReflectionTransform_eq_chain]
  let incident :=
    (sourceScalarAmplitude 1 : ModeAmplitude (ForwardWave Unit))
  let response :=
    (dateCascadeComposition
      (List.replicate 3 dateTerminationRegressionStage)).rightTerminatedReflectionTransform 0
        dateTerminationRegressionHypotheses_three.toCascade.hasBijectiveZeroReturnPivot
  change response (BackwardWave.mk ()) (ForwardWave.mk ()) =
    (8 / 17 : ℂ) * Complex.I
  have hGraph : (incident, response.toLinearMap incident) ∈ response.toBehavior := by
    rw [ModeTransform.mem_toBehavior_iff_toLinearMap]
  dsimp only [response] at hGraph
  rw [BackwardFirstChainTransform.toBehavior_rightTerminatedReflectionTransform,
    BackwardFirstChainTransform.mem_rightTerminatedReflectionBehavior_iff_pivotEquation]
      at hGraph
  have hRaw :
      dateCascadeComposition (List.replicate 3 dateTerminationRegressionStage) =
        -dateTerminationRegressionMatrix := by
    simpa [dateIdenticalCascadeComposition] using
      dateTerminationRegression_rawFold_three
  have hPivotAction (amplitude : ModeAmplitude (BackwardWave Unit)) :
      ((dateCascadeComposition
        (List.replicate 3 dateTerminationRegressionStage)).rightTerminationPivot 0).toLinearMap
          amplitude =
        sourceScalarAmplitude
          ((17 / 15 : ℂ) * Complex.I * amplitude (BackwardWave.mk ())) := by
    rw [hRaw]
    exact dateTerminationRegression_negativeMatrix_pivot_action amplitude
  have hIncidentAction (amplitude : ModeAmplitude (ForwardWave Unit)) :
      ModeTransform.toLinearMap
          (BackwardFirstChainTransform.rightTerminationIncidentBlock
            (dateCascadeComposition
              (List.replicate 3 dateTerminationRegressionStage)) 0) amplitude =
        sourceScalarAmplitude (-(8 / 15 : ℂ) * amplitude (ForwardWave.mk ())) := by
    rw [hRaw]
    exact dateTerminationRegression_negativeMatrix_incident_action amplitude
  rw [hPivotAction, hIncidentAction] at hGraph
  have hCoordinate := congrArg
    (fun amplitude : ModeAmplitude (BackwardWave Unit) =>
      amplitude (BackwardWave.mk ())) hGraph
  dsimp only [incident] at hCoordinate
  simp only [sourceScalarAmplitude, WithLp.ofLp_toLp] at hCoordinate
  have hFactor : (17 / 15 : ℂ) * Complex.I ≠ 0 := by
    intro hZero
    have hIm := congrArg Complex.im hZero
    norm_num at hIm
  have hCoordinateResponse :
      (17 / 15 : ℂ) * Complex.I *
          (response.toLinearMap incident) (BackwardWave.mk ()) = -(8 / 15 : ℂ) := by
    simpa only [response, incident, sourceScalarAmplitude,
      WithLp.ofLp_toLp, mul_one] using hCoordinate
  have hResponse :
      (response.toLinearMap incident) (BackwardWave.mk ()) =
        (8 / 17 : ℂ) * Complex.I := by
    apply mul_left_cancel₀ hFactor
    rw [hCoordinateResponse]
    ring_nf
    rw [Complex.I_sq]
    norm_num
  simp only [ModeTransform.toLinearMap, Matrix.toLpLin_apply, Matrix.mulVec,
    dotProduct] at hResponse
  rw [← ForwardWave.channelEquiv.symm.sum_comp] at hResponse
  simpa [response, incident, sourceScalarAmplitude] using hResponse

/-- The three-stage behavior directly yields transmission `-15 I/17`. -/
lemma dateTerminationRegression_three_transmissivity_by_hand :
    dateIdenticalTerminatedCascadeTransmissivity dateTerminationRegressionStage 3
      dateTerminationRegressionHypotheses_three = -(15 / 17 : ℂ) * Complex.I := by
  rw [dateIdenticalTerminatedCascadeTransmissivity, dateTerminatedCascadeTransmissivity,
    dateTerminatedCascadeTransmissionTransform_eq_chain]
  let incident :=
    (sourceScalarAmplitude 1 : ModeAmplitude (ForwardWave Unit))
  let response :=
    (dateCascadeComposition
      (List.replicate 3 dateTerminationRegressionStage)).rightTerminatedTransmissionTransform 0
        dateTerminationRegressionHypotheses_three.toCascade.hasBijectiveZeroReturnPivot
  change response (ForwardWave.mk ()) (ForwardWave.mk ()) =
    -(15 / 17 : ℂ) * Complex.I
  have hGraph : (incident, response.toLinearMap incident) ∈ response.toBehavior := by
    rw [ModeTransform.mem_toBehavior_iff_toLinearMap]
  dsimp only [response] at hGraph
  rw [BackwardFirstChainTransform.toBehavior_rightTerminatedTransmissionTransform,
    BackwardFirstChainTransform.mem_rightTerminatedTransmissionBehavior_iff_pivotEquation]
      at hGraph
  rcases hGraph with ⟨leftBackward, hPivot, hForward⟩
  have hRaw :
      dateCascadeComposition (List.replicate 3 dateTerminationRegressionStage) =
        -dateTerminationRegressionMatrix := by
    simpa [dateIdenticalCascadeComposition] using
      dateTerminationRegression_rawFold_three
  have hPivotAction (amplitude : ModeAmplitude (BackwardWave Unit)) :
      ((dateCascadeComposition
        (List.replicate 3 dateTerminationRegressionStage)).rightTerminationPivot 0).toLinearMap
          amplitude =
        sourceScalarAmplitude
          ((17 / 15 : ℂ) * Complex.I * amplitude (BackwardWave.mk ())) := by
    rw [hRaw]
    exact dateTerminationRegression_negativeMatrix_pivot_action amplitude
  have hIncidentAction (amplitude : ModeAmplitude (ForwardWave Unit)) :
      ModeTransform.toLinearMap
          (BackwardFirstChainTransform.rightTerminationIncidentBlock
            (dateCascadeComposition
              (List.replicate 3 dateTerminationRegressionStage)) 0) amplitude =
        sourceScalarAmplitude (-(8 / 15 : ℂ) * amplitude (ForwardWave.mk ())) := by
    rw [hRaw]
    exact dateTerminationRegression_negativeMatrix_incident_action amplitude
  rw [hPivotAction, hIncidentAction] at hPivot
  have hPivotCoordinate := congrArg
    (fun amplitude : ModeAmplitude (BackwardWave Unit) =>
      amplitude (BackwardWave.mk ())) hPivot
  dsimp only [incident] at hPivotCoordinate
  simp only [sourceScalarAmplitude, WithLp.ofLp_toLp] at hPivotCoordinate
  have hFactor : (17 / 15 : ℂ) * Complex.I ≠ 0 := by
    intro hZero
    have hIm := congrArg Complex.im hZero
    norm_num at hIm
  have hBackwardCoordinate :
      leftBackward (BackwardWave.mk ()) = (8 / 17 : ℂ) * Complex.I := by
    apply mul_left_cancel₀ hFactor
    rw [hPivotCoordinate]
    ring_nf
    rw [Complex.I_sq]
    norm_num
  have hLowerLeftAction (amplitude : ModeAmplitude (BackwardWave Unit)) :
      (dateCascadeComposition
        (List.replicate 3 dateTerminationRegressionStage)).lowerLeftBlock.toLinearMap
          amplitude =
        sourceScalarAmplitude ((8 / 15 : ℂ) * amplitude (BackwardWave.mk ())) := by
    rw [hRaw]
    exact dateTerminationRegression_negativeMatrix_lowerLeft_action amplitude
  have hLowerRightAction (amplitude : ModeAmplitude (ForwardWave Unit)) :
      (dateCascadeComposition
        (List.replicate 3 dateTerminationRegressionStage)).lowerRightBlock.toLinearMap
          amplitude =
        sourceScalarAmplitude
          (-(17 / 15 : ℂ) * Complex.I * amplitude (ForwardWave.mk ())) := by
    rw [hRaw]
    exact dateTerminationRegression_negativeMatrix_lowerRight_action amplitude
  rw [hLowerLeftAction, hLowerRightAction] at hForward
  have hForwardCoordinate := congrArg
    (fun amplitude : ModeAmplitude (ForwardWave Unit) =>
      amplitude (ForwardWave.mk ())) hForward
  dsimp only [incident] at hForwardCoordinate
  simp only [WithLp.ofLp_add, Pi.add_apply, sourceScalarAmplitude,
    WithLp.ofLp_toLp] at hForwardCoordinate
  rw [hBackwardCoordinate] at hForwardCoordinate
  have hForwardCoordinateResponse :
      (response.toLinearMap incident) (ForwardWave.mk ()) =
        (8 / 15 : ℂ) * ((8 / 17 : ℂ) * Complex.I) +
          (-(17 / 15 : ℂ)) * Complex.I := by
    simpa only [response, incident, sourceScalarAmplitude,
      WithLp.ofLp_toLp, mul_one] using hForwardCoordinate
  have hResponse :
      (response.toLinearMap incident) (ForwardWave.mk ()) =
        -(15 / 17 : ℂ) * Complex.I := by
    rw [hForwardCoordinateResponse]
    ring
  simp only [ModeTransform.toLinearMap, Matrix.toLpLin_apply, Matrix.mulVec,
    dotProduct] at hResponse
  rw [← ForwardWave.channelEquiv.symm.sum_comp] at hResponse
  simpa [response, incident, sourceScalarAmplitude] using hResponse

/-- The three-stage terminated responses are independently pinned together. -/
lemma dateTerminationRegression_three_responses_by_hand :
    dateIdenticalTerminatedCascadeReflectivity dateTerminationRegressionStage 3
          dateTerminationRegressionHypotheses_three = (8 / 17 : ℂ) * Complex.I ∧
      dateIdenticalTerminatedCascadeTransmissivity dateTerminationRegressionStage 3
          dateTerminationRegressionHypotheses_three =
        -(15 / 17 : ℂ) * Complex.I :=
  ⟨dateTerminationRegression_three_reflectivity_by_hand,
    dateTerminationRegression_three_transmissivity_by_hand⟩

/-!

## D. Singular parameter control

-/

/-- A nonunitary rational ring chosen so that the two-stage `M11` entry vanishes. -/
def dateTerminationRegressionSingularRing : DateParameters where
  reflectivity := 3 / 4
  transmissivity := 5 / 4
  couplingLength := 1
  powerAttenuation := 0
  wavelength := 2
  effectiveIndex := 1

/-- The singular control uses the same quarter-turn following bus as the positive fixture. -/
def dateTerminationRegressionSingularStage : DateCascadeStage where
  ring := dateTerminationRegressionSingularRing
  busLength := 1 / 2

/-- Direct expansion gives the singular ring's phase and attenuation data. -/
lemma dateTerminationRegressionSingularRing_phaseData :
    dateTerminationRegressionSingularRing.roundTripPhase = Real.pi ∧
      dateTerminationRegressionSingularRing.fieldAttenuation = 1 ∧
      dateTerminationRegressionSingularRing.phaseFactor = -1 ∧
      dateTerminationRegressionSingularRing.halfPhaseFactor = -Complex.I := by
  have hPhase : dateTerminationRegressionSingularRing.roundTripPhase = Real.pi := by
    rw [DateParameters.roundTripPhase]
    norm_num [dateTerminationRegressionSingularRing]
  have hAttenuation : dateTerminationRegressionSingularRing.fieldAttenuation = 1 := by
    norm_num [DateParameters.fieldAttenuation,
      dateTerminationRegressionSingularRing]
  refine ⟨hPhase, hAttenuation, ?_, ?_⟩
  · rw [DateParameters.phaseFactor, hPhase]
    norm_num [MatchedPropagation.carrierPhaseFactor]
  · rw [DateParameters.halfPhaseFactor, hPhase]
    norm_num [MatchedPropagation.carrierPhaseFactor]

/-- The singular ring has `R = -24/25` and `T = I`, so its own chain pivot is valid. -/
lemma dateTerminationRegressionSingularRing_transfers :
    dateForwardTransfer dateTerminationRegressionSingularRing = -24 / 25 ∧
      dateBackwardTransfer dateTerminationRegressionSingularRing = Complex.I := by
  have hDenominator : dateTerminationRegressionSingularRing.denominator = 25 / 16 := by
    rw [DateParameters.denominator,
      dateTerminationRegressionSingularRing_phaseData.2.2.1,
      dateTerminationRegressionSingularRing_phaseData.2.1]
    norm_num [dateTerminationRegressionSingularRing]
  constructor
  · rw [dateForwardTransfer, hDenominator,
      dateTerminationRegressionSingularRing_phaseData.2.2.1,
      dateTerminationRegressionSingularRing_phaseData.2.1]
    norm_num [dateTerminationRegressionSingularRing]
  · rw [dateBackwardTransfer, hDenominator,
      dateTerminationRegressionSingularRing_phaseData.2.2.2,
      dateTerminationRegressionSingularRing_phaseData.2.1]
    norm_num [dateTerminationRegressionSingularRing]

/-- The singular parameter stage retains a valid ring-to-chain pivot. -/
lemma dateTerminationRegressionSingularStage_hasBijectiveRingTransmission :
    dateTerminationRegressionSingularStage.HasBijectiveRingTransmission := by
  rw [DateCascadeStage.hasBijectiveRingTransmission_iff_forwardTransfer_ne_zero]
  rw [show dateTerminationRegressionSingularStage.ring =
      dateTerminationRegressionSingularRing by rfl,
    dateTerminationRegressionSingularRing_transfers.1]
  norm_num

/-- The singular control's following bus still has factors `I` and `-I`. -/
lemma dateTerminationRegressionSingularStage_signedContinuity :
    dateTerminationRegressionSingularStage.backwardContinuityFactor = Complex.I ∧
      dateTerminationRegressionSingularStage.forwardContinuityFactor = -Complex.I := by
  have hBus : dateTerminationRegressionSingularStage.busPhase = Real.pi / 2 := by
    norm_num [dateTerminationRegressionSingularStage, DateCascadeStage.busPhase,
      dateTerminationRegressionSingularRing]
    ring
  rw [DateCascadeStage.backwardContinuityFactor,
    DateCascadeStage.forwardContinuityFactor, hBus]
  constructor <;>
    simp [MatchedPropagation.carrierPhaseFactor, Real.Angle.toCircle_coe,
      Circle.coe_exp, Complex.exp_mul_I]

/-- The one-stage matrix used to expose the two-stage zero pivot. -/
def dateTerminationRegressionSingularMatrix : BackwardFirstChainTransform Unit Unit
  | Sum.inl _, Sum.inl _ => -(25 / 24 : ℂ) * Complex.I
  | Sum.inl _, Sum.inr _ => -(25 / 24 : ℂ)
  | Sum.inr _, Sum.inl _ => -(25 / 24 : ℂ)
  | Sum.inr _, Sum.inr _ => (1201 / 600 : ℂ) * Complex.I

/-- The singular parameter stage expands to its displayed source-coordinate matrix. -/
lemma dateTerminationRegressionSingularStage_compositionMatrix :
    dateTerminationRegressionSingularStage.compositionMatrix =
      dateTerminationRegressionSingularMatrix := by
  ext (output | output) (input | input) <;>
    rcases output with ⟨⟨⟩⟩ <;>
    rcases input with ⟨⟨⟩⟩ <;>
    simp only [DateCascadeStage.compositionMatrix, Matrix.mul_apply,
      Fintype.sum_sum_type]
  all_goals simp_rw [← BackwardWave.channelEquiv.symm.sum_comp,
    ← ForwardWave.channelEquiv.symm.sum_comp]
  all_goals simp [DateCascadeStage.continuityChainMatrix,
    dateTerminationRegressionSingularStage_signedContinuity.1,
    dateTerminationRegressionSingularStage_signedContinuity.2,
    dateFourPortBackwardFirstChainMatrix,
    show dateTerminationRegressionSingularStage.ring =
      dateTerminationRegressionSingularRing by rfl,
    dateTerminationRegressionSingularRing_transfers.1,
    dateTerminationRegressionSingularRing_transfers.2,
    dateTerminationRegressionSingularMatrix]
  all_goals ring_nf
  all_goals (try rw [Complex.I_sq])
  all_goals norm_num

/-- The raw two-stage product has `M11 = 0` by direct matrix multiplication. -/
lemma dateTerminationRegressionSingular_rawFold_entry11 :
    dateChainEntry
        (dateIdenticalCascadeComposition dateTerminationRegressionSingularStage 2) 0 0 = 0 := by
  change dateChainEntry
    ((1 * dateTerminationRegressionSingularStage.compositionMatrix) *
      dateTerminationRegressionSingularStage.compositionMatrix) 0 0 = 0
  rw [Matrix.one_mul, dateTerminationRegressionSingularStage_compositionMatrix]
  simp only [dateChainEntry, dateBackwardFirstFinEquiv, Matrix.mul_apply,
    Fintype.sum_sum_type]
  simp_rw [← BackwardWave.channelEquiv.symm.sum_comp,
    ← ForwardWave.channelEquiv.symm.sum_comp]
  norm_num [dateTerminationRegressionSingularMatrix]
  ring_nf
  rw [Complex.I_sq]
  norm_num

/-- A nonzero singleton amplitude used to expose the raw two-stage pivot kernel. -/
def dateTerminationRegressionSingularKernel : ModeAmplitude (BackwardWave Unit) :=
  sourceScalarAmplitude 1

/-- The singleton kernel witness is nonzero. -/
lemma dateTerminationRegressionSingularKernel_ne_zero :
    dateTerminationRegressionSingularKernel ≠ 0 := by
  intro hZero
  have hCoordinate := congrArg
    (fun amplitude : ModeAmplitude (BackwardWave Unit) =>
      amplitude (BackwardWave.mk ())) hZero
  norm_num [dateTerminationRegressionSingularKernel, sourceScalarAmplitude] at hCoordinate

/-- Direct expansion sends the nonzero singleton witness to zero through the raw pivot. -/
lemma dateTerminationRegressionSingular_pivot_kernel :
    ((dateIdenticalCascadeComposition
      dateTerminationRegressionSingularStage 2).rightTerminationPivot 0).toLinearMap
        dateTerminationRegressionSingularKernel = 0 := by
  rw [BackwardFirstChainTransform.rightTerminationPivot_zero]
  apply WithLp.ofLp_injective 2
  funext output
  rcases output with ⟨⟨⟩⟩
  simp only [BackwardFirstChainTransform.leadingBlock, Matrix.toBlocks₁₁,
    ModeTransform.toLinearMap, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    dateTerminationRegressionSingularKernel, sourceScalarAmplitude]
  rw [← BackwardWave.channelEquiv.symm.sum_comp]
  simpa [dateChainEntry, dateBackwardFirstFinEquiv] using
    dateTerminationRegressionSingular_rawFold_entry11

/-- The raw zero-return pivot is not injective, witnessed independently of production gates. -/
lemma dateTerminationRegressionSingular_pivot_not_injective :
    ¬Function.Injective
      ((dateIdenticalCascadeComposition
        dateTerminationRegressionSingularStage 2).rightTerminationPivot 0).toLinearMap := by
  intro hInjective
  apply dateTerminationRegressionSingularKernel_ne_zero
  apply hInjective
  rw [dateTerminationRegressionSingular_pivot_kernel, map_zero]

/-- The `M11 = 0` chain termination fails the generic N3T well-posedness criterion. -/
lemma dateTerminationRegressionSingular_chain_not_wellPosed :
    ¬(dateIdenticalCascadeComposition
      dateTerminationRegressionSingularStage 2).HasWellPosedRightTermination
        (0 : RightLoadTransform Unit) := by
  intro hWellPosed
  have hGeneric :=
    (BackwardFirstChainTransform.hasWellPosedRightTermination_iff_pivot_injective_and_solvable
      (dateIdenticalCascadeComposition dateTerminationRegressionSingularStage 2)
      (0 : RightLoadTransform Unit)).mp hWellPosed
  exact dateTerminationRegressionSingular_pivot_not_injective hGeneric.1

/-- The same concrete parameter cascade has no well-posed relational zero-return termination. -/
lemma dateTerminationRegressionSingular_not_wellPosed :
    ¬(dateIdenticalCascadeBehavior
      dateTerminationRegressionSingularStage 2).HasWellPosedRightTermination
        (RightLoadBehavior.zeroReflection : RightLoadBehavior Unit) := by
  intro hWellPosed
  have hStages : ∀ repeated ∈
      List.replicate 2 dateTerminationRegressionSingularStage,
      repeated.HasBijectiveRingTransmission := by
    intro repeated hRepeated
    rw [List.eq_of_mem_replicate hRepeated]
    exact dateTerminationRegressionSingularStage_hasBijectiveRingTransmission
  change BackwardFirstTwoPortBehavior.HasWellPosedRightTermination
    (dateCascadeBehavior (List.replicate 2 dateTerminationRegressionSingularStage))
      (RightLoadBehavior.zeroReflection : RightLoadBehavior Unit) at hWellPosed
  rw [dateCascadeBehavior_eq_composition_toBehavior _ hStages] at hWellPosed
  have hChain :
      (dateIdenticalCascadeComposition
        dateTerminationRegressionSingularStage 2).HasWellPosedRightTermination
          (0 : RightLoadTransform Unit) := by
    change (BackwardFirstTwoPortBehavior.terminateRight
      (dateIdenticalCascadeComposition
        dateTerminationRegressionSingularStage 2).toBehavior
      (RightLoadBehavior.ofReflection (0 : RightLoadTransform Unit))).IsFunctional
    rw [RightLoadBehavior.ofReflection_zero]
    simpa [dateIdenticalCascadeComposition] using hWellPosed
  exact dateTerminationRegressionSingular_chain_not_wellPosed hChain

/-- The production cascade gate is genuinely unavailable at the singular parameter point. -/
lemma dateTerminationRegressionSingular_not_hypotheses :
    ¬DateCascadeTerminationHypotheses
      (List.replicate 2 dateTerminationRegressionSingularStage) := by
  intro h
  apply h.entry11_ne_zero
  simpa [dateIdenticalCascadeComposition] using
    dateTerminationRegressionSingular_rawFold_entry11

end MicroringCascade

end

end Optics
