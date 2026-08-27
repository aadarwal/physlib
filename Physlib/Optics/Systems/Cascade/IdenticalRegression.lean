/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Systems.Cascade.Identical

/-!
# Regression tests for identical DATE cascades and the Sylvester form

## i. Overview

The `N = 2` and `N = 3` identical DATE folds are unfolded directly through the replicated list;
neither proof calls the H-04 headline theorem. The H-05 fixture is the concrete source-ordered
matrix `diag(I, -I)`. Its determinant and all four source hypotheses are checked directly, while
its second and third powers are expanded through `Matrix.mul_apply` rather than Cayley--Hamilton
or either closed-form theorem.

The corresponding sine forms are reduced independently to `-1` and `-matrix`. The negative
control uses the identity matrix. It satisfies determinant one, the lower trace bound, and both
conjugacy equations, but fails the strict upper trace bound. Its totalized sine form is zero at
`N = 1`, so the ungated closed-form equality is false.

The joined fixture supplies rational DATE ring data and one bus length. Its production stage
matrix is displayed entry by entry as `diag(I, -I)`. Raw replicated folds and source sine
expressions for that same stage are then calculated independently at `N = 2` and `N = 3`.

## ii. Key results

- `dateIdenticalCascadeRegression_two_by_hand`: the directly unfolded two-stage replicate.
- `dateIdenticalCascadeRegression_three_by_hand`: the directly unfolded three-stage replicate.
- `dateSylvesterRegressionMatrix_hypotheses`: a concrete point in the complete source domain.
- `dateSylvesterRegressionMatrix_pow_two` and `_pow_three`: direct power expansions.
- `dateSylvesterRegressionMatrix_closedForm_two` and `_closedForm_three`: independent sine checks.
- `dateSylvesterRegression_identity_closedForm_false`: a mechanically false ungated formula.
- `dateJoinedSylvesterRegressionStage_compositionMatrix`: the concrete DATE stage matrix.
- `dateJoinedSylvesterRegressionStage_two_by_hand` and `_three_by_hand`: joined raw-fold checks.

## iii. Table of contents

- A. Identical cascade counts two and three
- B. Sylvester source-domain fixture
- C. Strict-trace negative control
- D. Joined concrete-stage anchor

## iv. References
These fixtures make no quadruple-ring, lattice, termination, resonance, dispersion, bending-loss,
causality, passivity, reciprocity, or electromagnetic-power claim. They test totalized matrices;
relational meaning remains gated by the production pivot theorem.

DATE'14 Thm. 4 and the Sylvester result are summarized at `HOL-CORPUS.md:204-207`.
-/

@[expose] public section

namespace Optics

noncomputable section

namespace MicroringCascade

open MicroringSourceBridge
open scoped ComplexConjugate

/-!

## A. Identical cascade counts two and three

-/

/-- The two-stage identical DATE fold is expanded without the general power theorem. -/
lemma dateIdenticalCascadeRegression_two_by_hand (stage : DateCascadeStage) :
    dateIdenticalCascadeComposition stage 2 = stage.compositionMatrix ^ 2 := by
  simp [dateIdenticalCascadeComposition, dateCascadeComposition,
    BackwardFirstChainTransform.fold, pow_succ]

/-- The three-stage identical DATE fold is expanded without the general power theorem. -/
lemma dateIdenticalCascadeRegression_three_by_hand (stage : DateCascadeStage) :
    dateIdenticalCascadeComposition stage 3 = stage.compositionMatrix ^ 3 := by
  simp [dateIdenticalCascadeComposition, dateCascadeComposition,
    BackwardFirstChainTransform.fold, pow_succ]

/-!

## B. Sylvester source-domain fixture

-/

/-- A source-domain matrix with strict trace interior and determinant one. -/
def dateSylvesterRegressionMatrix : BackwardFirstChainTransform Unit Unit
  | Sum.inl _, Sum.inl _ => Complex.I
  | Sum.inl _, Sum.inr _ => 0
  | Sum.inr _, Sum.inl _ => 0
  | Sum.inr _, Sum.inr _ => -Complex.I

/-- The fixture determinant is one, computed after the canonical `Fin 2` reindex. -/
lemma dateSylvesterRegressionMatrix_det :
    Matrix.det dateSylvesterRegressionMatrix = 1 := by
  rw [← Matrix.det_reindex_self dateBackwardFirstFinEquiv.symm
    dateSylvesterRegressionMatrix, Matrix.det_fin_two]
  norm_num [Matrix.reindex_apply, dateSylvesterRegressionMatrix,
    dateBackwardFirstFinEquiv, Complex.I_mul_I]

/-- The fixture satisfies every determinant, strict-trace, and conjugacy source hypothesis. -/
lemma dateSylvesterRegressionMatrix_hypotheses :
    DateSylvesterHypotheses dateSylvesterRegressionMatrix := by
  refine ⟨dateSylvesterRegressionMatrix_det, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [dateChainEntry, dateSylvesterRegressionMatrix,
      dateBackwardFirstFinEquiv]

/-- Direct entry expansion gives the fixture's second power as negative identity. -/
lemma dateSylvesterRegressionMatrix_pow_two :
    dateSylvesterRegressionMatrix ^ 2 = -1 := by
  ext (output | output) (input | input) <;>
    rcases output with ⟨⟨⟩⟩ <;>
    rcases input with ⟨⟨⟩⟩ <;>
    simp only [pow_two, Matrix.mul_apply, Fintype.sum_sum_type]
  all_goals simp_rw [← BackwardWave.channelEquiv.symm.sum_comp,
    ← ForwardWave.channelEquiv.symm.sum_comp]
  all_goals norm_num [dateSylvesterRegressionMatrix,
    Complex.I_mul_I, Matrix.one_apply]
  all_goals simp

/-- Direct entry expansion gives the fixture's third power as its negation. -/
lemma dateSylvesterRegressionMatrix_pow_three :
    dateSylvesterRegressionMatrix ^ 3 = -dateSylvesterRegressionMatrix := by
  ext (output | output) (input | input) <;>
    rcases output with ⟨⟨⟩⟩ <;>
    rcases input with ⟨⟨⟩⟩ <;>
    simp only [show 3 = 2 + 1 by norm_num, pow_succ,
      Matrix.mul_apply, Fintype.sum_sum_type]
  all_goals simp_rw [← BackwardWave.channelEquiv.symm.sum_comp,
    ← ForwardWave.channelEquiv.symm.sum_comp]
  all_goals norm_num [dateSylvesterRegressionMatrix,
    Complex.I_mul_I, Matrix.one_apply]
  all_goals simp

/-- Direct evaluation of the source sine coefficients at `N = 2` gives negative identity. -/
lemma dateSylvesterRegressionMatrix_closedForm_two :
    dateSylvesterRegressionMatrix ^ 2 =
      dateSylvesterClosedForm dateSylvesterRegressionMatrix 2 := by
  have hAngle : dateSylvesterAngle dateSylvesterRegressionMatrix = Real.pi / 2 := by
    simp [dateSylvesterAngle, dateChainEntry, dateSylvesterRegressionMatrix,
      dateBackwardFirstFinEquiv]
  have hCoefficientOne :
      dateSylvesterSineCoefficient dateSylvesterRegressionMatrix 1 = 1 := by
    simp [dateSylvesterSineCoefficient, hAngle]
  have hCoefficientTwo :
      dateSylvesterSineCoefficient dateSylvesterRegressionMatrix 2 = 0 := by
    rw [dateSylvesterSineCoefficient, hAngle]
    norm_num [show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring]
  rw [dateSylvesterRegressionMatrix_pow_two, dateSylvesterClosedForm]
  change -1 =
    dateSylvesterSineCoefficient dateSylvesterRegressionMatrix 2 •
        dateSylvesterRegressionMatrix -
      dateSylvesterSineCoefficient dateSylvesterRegressionMatrix 1 • 1
  rw [hCoefficientOne, hCoefficientTwo]
  module

/-- Direct evaluation of the source sine coefficients at `N = 3` gives matrix negation. -/
lemma dateSylvesterRegressionMatrix_closedForm_three :
    dateSylvesterRegressionMatrix ^ 3 =
      dateSylvesterClosedForm dateSylvesterRegressionMatrix 3 := by
  have hAngle : dateSylvesterAngle dateSylvesterRegressionMatrix = Real.pi / 2 := by
    simp [dateSylvesterAngle, dateChainEntry, dateSylvesterRegressionMatrix,
      dateBackwardFirstFinEquiv]
  have hCoefficientTwo :
      dateSylvesterSineCoefficient dateSylvesterRegressionMatrix 2 = 0 := by
    rw [dateSylvesterSineCoefficient, hAngle]
    norm_num [show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring]
  have hCoefficientThree :
      dateSylvesterSineCoefficient dateSylvesterRegressionMatrix 3 = -1 := by
    rw [dateSylvesterSineCoefficient, hAngle]
    norm_num [show (3 : ℝ) * (Real.pi / 2) = Real.pi + Real.pi / 2 by ring,
      Real.sin_add]
  rw [dateSylvesterRegressionMatrix_pow_three, dateSylvesterClosedForm]
  change -dateSylvesterRegressionMatrix =
    dateSylvesterSineCoefficient dateSylvesterRegressionMatrix 3 •
        dateSylvesterRegressionMatrix -
      dateSylvesterSineCoefficient dateSylvesterRegressionMatrix 2 • 1
  rw [hCoefficientTwo, hCoefficientThree]
  module

/-!

## C. Strict-trace negative control

-/

/-- Identity satisfies every source condition except the strict upper trace bound. -/
lemma dateSylvesterRegression_identity_exact_failure :
    Matrix.det (1 : BackwardFirstChainTransform Unit Unit) = 1 ∧
      -1 < (dateChainEntry (1 : BackwardFirstChainTransform Unit Unit) 0 0).re ∧
      ¬ (dateChainEntry (1 : BackwardFirstChainTransform Unit Unit) 0 0).re < 1 ∧
      dateChainEntry (1 : BackwardFirstChainTransform Unit Unit) 1 1 =
        conj (dateChainEntry (1 : BackwardFirstChainTransform Unit Unit) 0 0) ∧
      dateChainEntry (1 : BackwardFirstChainTransform Unit Unit) 0 1 =
        conj (dateChainEntry (1 : BackwardFirstChainTransform Unit Unit) 1 0) := by
  norm_num [dateChainEntry, dateBackwardFirstFinEquiv, Matrix.one_apply]
  simp

/-- Consequently, identity is outside the source's exact Sylvester domain. -/
lemma dateSylvesterRegression_identity_not_hypotheses :
    ¬ DateSylvesterHypotheses (1 : BackwardFirstChainTransform Unit Unit) := by
  intro h
  have hUpper := h.entry11_re_lt_one
  norm_num [dateChainEntry, dateBackwardFirstFinEquiv] at hUpper

/-- At that excluded boundary point, the totalized `N = 1` source sine form is false. -/
lemma dateSylvesterRegression_identity_closedForm_false :
    (1 : BackwardFirstChainTransform Unit Unit) ^ 1 ≠
      dateSylvesterClosedForm 1 1 := by
  intro hFalse
  have hEntry := congrFun
    (congrFun hFalse (Sum.inl (BackwardWave.mk ())))
      (Sum.inl (BackwardWave.mk ()))
  norm_num [dateSylvesterClosedForm, dateSylvesterSineCoefficient,
    dateSylvesterAngle, dateChainEntry, dateBackwardFirstFinEquiv] at hEntry

/-!

## D. Joined concrete-stage anchor

-/

/-- Rational DATE ring data for the joined fold-to-Sylvester regression. -/
def dateJoinedSylvesterRegressionRing : DateParameters where
  reflectivity := -1
  transmissivity := 0
  couplingLength := 1
  powerAttenuationCoefficient := 0
  wavelength := 4
  effectiveIndex := 1

/-- The concrete DATE stage used on both sides of the joined regression. -/
def dateJoinedSylvesterRegressionStage : DateCascadeStage where
  ring := dateJoinedSylvesterRegressionRing
  busLength := 1

/-- The joined fixture has a positive quarter-turn bus phase. -/
lemma dateJoinedSylvesterRegressionStage_busPhase :
    dateJoinedSylvesterRegressionStage.busPhase = Real.pi / 2 := by
  norm_num [dateJoinedSylvesterRegressionStage, DateCascadeStage.busPhase,
    dateJoinedSylvesterRegressionRing]
  ring

/-- The joined ring has unit field attenuation. -/
lemma dateJoinedSylvesterRegressionRing_fieldAttenuation :
    dateJoinedSylvesterRegressionRing.fieldAttenuation = 1 := by
  norm_num [dateJoinedSylvesterRegressionRing, DateParameters.fieldAttenuation]

/-- The joined ring's internal phase factor is `-I`. -/
lemma dateJoinedSylvesterRegressionRing_phaseFactor :
    dateJoinedSylvesterRegressionRing.phaseFactor = -Complex.I := by
  have hPhase : dateJoinedSylvesterRegressionRing.roundTripPhase = Real.pi / 2 := by
    norm_num [dateJoinedSylvesterRegressionRing, DateParameters.roundTripPhase]
    ring
  rw [DateParameters.phaseFactor, hPhase]
  simp [MatchedPropagation.carrierPhaseFactor,
    Real.Angle.toCircle_coe, Circle.coe_exp, Complex.exp_mul_I]

/-- The joined ring's DATE denominator is `1 + I`. -/
lemma dateJoinedSylvesterRegressionRing_denominator :
    dateJoinedSylvesterRegressionRing.denominator = 1 + Complex.I := by
  rw [DateParameters.denominator,
    dateJoinedSylvesterRegressionRing_fieldAttenuation,
    dateJoinedSylvesterRegressionRing_phaseFactor]
  norm_num [dateJoinedSylvesterRegressionRing]

/-- The joined ring has exact forward transfer one. -/
lemma dateJoinedSylvesterRegressionRing_forwardTransfer :
    dateForwardTransfer dateJoinedSylvesterRegressionRing = 1 := by
  rw [dateForwardTransfer,
    dateJoinedSylvesterRegressionRing_fieldAttenuation,
    dateJoinedSylvesterRegressionRing_phaseFactor,
    dateJoinedSylvesterRegressionRing_denominator]
  norm_num [dateJoinedSylvesterRegressionRing]
  intro hZero
  have hReal := congrArg Complex.re hZero
  norm_num at hReal

/-- The joined ring has exact backward transfer zero. -/
lemma dateJoinedSylvesterRegressionRing_backwardTransfer :
    dateBackwardTransfer dateJoinedSylvesterRegressionRing = 0 := by
  simp [dateBackwardTransfer, dateJoinedSylvesterRegressionRing]

/-- The joined stage has `I` and `-I` as its two continuity factors. -/
lemma dateJoinedSylvesterRegressionStage_signedContinuity :
    dateJoinedSylvesterRegressionStage.backwardContinuityFactor = Complex.I ∧
      dateJoinedSylvesterRegressionStage.forwardContinuityFactor = -Complex.I := by
  rw [DateCascadeStage.backwardContinuityFactor,
    DateCascadeStage.forwardContinuityFactor,
    dateJoinedSylvesterRegressionStage_busPhase]
  constructor <;>
    simp [MatchedPropagation.carrierPhaseFactor, Real.Angle.toCircle_coe,
      Circle.coe_exp, Complex.exp_mul_I]

/-- The concrete stage composition displays `diag(I, -I)` entry by entry. -/
lemma dateJoinedSylvesterRegressionStage_compositionMatrix :
    dateJoinedSylvesterRegressionStage.compositionMatrix =
      dateSylvesterRegressionMatrix := by
  ext (output | output) (input | input) <;>
    rcases output with ⟨⟨⟩⟩ <;>
    rcases input with ⟨⟨⟩⟩ <;>
    simp only [DateCascadeStage.compositionMatrix, Matrix.mul_apply,
      Fintype.sum_sum_type]
  all_goals simp_rw [← BackwardWave.channelEquiv.symm.sum_comp,
    ← ForwardWave.channelEquiv.symm.sum_comp]
  all_goals simp [DateCascadeStage.continuityChainMatrix,
    dateJoinedSylvesterRegressionStage_signedContinuity.1,
    dateJoinedSylvesterRegressionStage_signedContinuity.2,
    dateFourPortBackwardFirstChainMatrix,
    show dateJoinedSylvesterRegressionStage.ring =
      dateJoinedSylvesterRegressionRing by rfl,
    dateJoinedSylvesterRegressionRing_forwardTransfer,
    dateJoinedSylvesterRegressionRing_backwardTransfer,
    dateSylvesterRegressionMatrix]

/-- All four source-ordered entries of the concrete stage composition. -/
lemma dateJoinedSylvesterRegressionStage_compositionMatrix_entries :
    dateChainEntry dateJoinedSylvesterRegressionStage.compositionMatrix 0 0 =
        Complex.I ∧
      dateChainEntry dateJoinedSylvesterRegressionStage.compositionMatrix 0 1 = 0 ∧
      dateChainEntry dateJoinedSylvesterRegressionStage.compositionMatrix 1 0 = 0 ∧
      dateChainEntry dateJoinedSylvesterRegressionStage.compositionMatrix 1 1 =
        -Complex.I := by
  rw [dateJoinedSylvesterRegressionStage_compositionMatrix]
  norm_num [dateChainEntry, dateSylvesterRegressionMatrix,
    dateBackwardFirstFinEquiv]

/-- The concrete stage satisfies all source Sylvester hypotheses by entry calculation. -/
lemma dateJoinedSylvesterRegressionStage_hypotheses :
    DateSylvesterHypotheses
      dateJoinedSylvesterRegressionStage.compositionMatrix := by
  rw [dateJoinedSylvesterRegressionStage_compositionMatrix]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← Matrix.det_reindex_self dateBackwardFirstFinEquiv.symm
      dateSylvesterRegressionMatrix, Matrix.det_fin_two]
    norm_num [Matrix.reindex_apply, dateSylvesterRegressionMatrix,
      dateBackwardFirstFinEquiv, Complex.I_mul_I]
  all_goals norm_num [dateChainEntry, dateSylvesterRegressionMatrix,
    dateBackwardFirstFinEquiv]

/-- The raw two-stage fold of the concrete DATE stage is negative identity.

The initial `change` definitionally expands `replicate`, `map`, and the neutral fold.
-/
lemma dateJoinedSylvesterRegressionStage_rawFold_two :
    dateIdenticalCascadeComposition dateJoinedSylvesterRegressionStage 2 = -1 := by
  change
    (1 * dateJoinedSylvesterRegressionStage.compositionMatrix) *
        dateJoinedSylvesterRegressionStage.compositionMatrix = -1
  rw [Matrix.one_mul, dateJoinedSylvesterRegressionStage_compositionMatrix]
  ext (output | output) (input | input) <;>
    rcases output with ⟨⟨⟩⟩ <;>
    rcases input with ⟨⟨⟩⟩ <;>
    simp only [Matrix.mul_apply, Fintype.sum_sum_type]
  all_goals simp_rw [← BackwardWave.channelEquiv.symm.sum_comp,
    ← ForwardWave.channelEquiv.symm.sum_comp]
  all_goals norm_num [dateSylvesterRegressionMatrix,
    Complex.I_mul_I, Matrix.one_apply]
  all_goals simp

/-- The raw three-stage fold of the concrete DATE stage is its matrix negation.

The initial `change` definitionally expands `replicate`, `map`, and the neutral fold.
-/
lemma dateJoinedSylvesterRegressionStage_rawFold_three :
    dateIdenticalCascadeComposition dateJoinedSylvesterRegressionStage 3 =
      -dateJoinedSylvesterRegressionStage.compositionMatrix := by
  change
    ((1 * dateJoinedSylvesterRegressionStage.compositionMatrix) *
        dateJoinedSylvesterRegressionStage.compositionMatrix) *
      dateJoinedSylvesterRegressionStage.compositionMatrix =
        -dateJoinedSylvesterRegressionStage.compositionMatrix
  rw [Matrix.one_mul, dateJoinedSylvesterRegressionStage_compositionMatrix]
  ext (output | output) (input | input) <;>
    rcases output with ⟨⟨⟩⟩ <;>
    rcases input with ⟨⟨⟩⟩ <;>
    simp only [Matrix.mul_apply, Fintype.sum_sum_type]
  all_goals simp_rw [← BackwardWave.channelEquiv.symm.sum_comp,
    ← ForwardWave.channelEquiv.symm.sum_comp]
  all_goals norm_num [dateSylvesterRegressionMatrix,
    Complex.I_mul_I, Matrix.one_apply]

/-- The joined stage's source angle is the positive quarter turn. -/
lemma dateJoinedSylvesterRegressionStage_angle :
    dateSylvesterAngle dateJoinedSylvesterRegressionStage.compositionMatrix =
      Real.pi / 2 := by
  rw [dateJoinedSylvesterRegressionStage_compositionMatrix]
  simp [dateSylvesterAngle, dateChainEntry, dateSylvesterRegressionMatrix,
    dateBackwardFirstFinEquiv]

/-- Direct sine evaluation gives negative identity at `N = 2`. -/
lemma dateJoinedSylvesterRegressionStage_sineForm_two :
    dateSylvesterClosedForm
      dateJoinedSylvesterRegressionStage.compositionMatrix 2 = -1 := by
  have hCoefficientOne :
      dateSylvesterSineCoefficient
          dateJoinedSylvesterRegressionStage.compositionMatrix 1 = 1 := by
    simp [dateSylvesterSineCoefficient,
      dateJoinedSylvesterRegressionStage_angle]
  have hCoefficientTwo :
      dateSylvesterSineCoefficient
          dateJoinedSylvesterRegressionStage.compositionMatrix 2 = 0 := by
    rw [dateSylvesterSineCoefficient,
      dateJoinedSylvesterRegressionStage_angle]
    norm_num [show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring]
  rw [dateSylvesterClosedForm]
  change
    dateSylvesterSineCoefficient
          dateJoinedSylvesterRegressionStage.compositionMatrix 2 •
        dateJoinedSylvesterRegressionStage.compositionMatrix -
      dateSylvesterSineCoefficient
          dateJoinedSylvesterRegressionStage.compositionMatrix 1 • 1 = -1
  rw [hCoefficientOne, hCoefficientTwo]
  module

/-- Direct sine evaluation gives matrix negation at `N = 3`. -/
lemma dateJoinedSylvesterRegressionStage_sineForm_three :
    dateSylvesterClosedForm
        dateJoinedSylvesterRegressionStage.compositionMatrix 3 =
      -dateJoinedSylvesterRegressionStage.compositionMatrix := by
  have hCoefficientTwo :
      dateSylvesterSineCoefficient
          dateJoinedSylvesterRegressionStage.compositionMatrix 2 = 0 := by
    rw [dateSylvesterSineCoefficient,
      dateJoinedSylvesterRegressionStage_angle]
    norm_num [show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring]
  have hCoefficientThree :
      dateSylvesterSineCoefficient
          dateJoinedSylvesterRegressionStage.compositionMatrix 3 = -1 := by
    rw [dateSylvesterSineCoefficient,
      dateJoinedSylvesterRegressionStage_angle]
    norm_num [show (3 : ℝ) * (Real.pi / 2) =
      Real.pi + Real.pi / 2 by ring, Real.sin_add]
  rw [dateSylvesterClosedForm]
  change
    dateSylvesterSineCoefficient
          dateJoinedSylvesterRegressionStage.compositionMatrix 3 •
        dateJoinedSylvesterRegressionStage.compositionMatrix -
      dateSylvesterSineCoefficient
          dateJoinedSylvesterRegressionStage.compositionMatrix 2 • 1 =
        -dateJoinedSylvesterRegressionStage.compositionMatrix
  rw [hCoefficientTwo, hCoefficientThree]
  module

/-- The raw two-stage DATE fold equals its hand-computed sine expression. -/
lemma dateJoinedSylvesterRegressionStage_two_by_hand :
    dateIdenticalCascadeComposition dateJoinedSylvesterRegressionStage 2 =
      dateSylvesterClosedForm
        dateJoinedSylvesterRegressionStage.compositionMatrix 2 := by
  rw [dateJoinedSylvesterRegressionStage_rawFold_two,
    dateJoinedSylvesterRegressionStage_sineForm_two]

/-- The raw three-stage DATE fold equals its hand-computed sine expression. -/
lemma dateJoinedSylvesterRegressionStage_three_by_hand :
    dateIdenticalCascadeComposition dateJoinedSylvesterRegressionStage 3 =
      dateSylvesterClosedForm
        dateJoinedSylvesterRegressionStage.compositionMatrix 3 := by
  rw [dateJoinedSylvesterRegressionStage_rawFold_three,
    dateJoinedSylvesterRegressionStage_sineForm_three]

end MicroringCascade

end

end Optics
