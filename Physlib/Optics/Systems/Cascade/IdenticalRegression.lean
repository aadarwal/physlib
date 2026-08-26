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

## ii. Key results

- `dateIdenticalCascadeRegression_two_by_hand`: the directly unfolded two-stage replicate.
- `dateIdenticalCascadeRegression_three_by_hand`: the directly unfolded three-stage replicate.
- `dateSylvesterRegressionMatrix_hypotheses`: a concrete point in the complete source domain.
- `dateSylvesterRegressionMatrix_pow_two` and `_pow_three`: direct power expansions.
- `dateSylvesterRegressionMatrix_closedForm_two` and `_closedForm_three`: independent sine checks.
- `dateSylvesterRegression_identity_closedForm_false`: a mechanically false ungated formula.

## iii. Table of contents

- A. Identical cascade counts two and three
- B. Sylvester source-domain fixture
- C. Strict-trace negative control

## iv. References and non-claims

DATE'14 Thm. 4 and the unnumbered Sylvester result are summarized at
`HOL-CORPUS.md:204-207`. These fixtures make no quadruple-ring, lattice, termination, resonance,
dispersion, bending-loss, causality, passivity, reciprocity, or electromagnetic-power claim.
They test totalized matrices; relational meaning remains gated by the production pivot theorem.
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

end MicroringCascade

end

end Optics
