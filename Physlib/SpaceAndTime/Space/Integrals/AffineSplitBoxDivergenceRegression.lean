/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.SpaceAndTime.Space.Integrals.AffineSplitBoxDivergence

/-!
# Split affine-box divergence regression

## i. Overview

This file checks the split-box divergence theorem on two independent polynomial fields in the
standard frame. The negative field is `(0, 0, z)` and the positive field is `(0, 0, 2z + 3)`.
On the two unit half-boxes the bulk divergence is `12`, the retained carrier jump is `12`, and the
outer principal flux is `24`; all lateral fluxes vanish.

The independently evaluated nonzero carrier term catches accidental cancellation of the two
carrier faces, while the unequal bulk divergences catch reuse of one side's field on both halves.

## ii. Key results

- `bulkDivergence_exact`: the two half-box volume terms sum to `12`.
- `carrierJump_exact`: the retained positive-minus-negative carrier flux is `12`.
- `outerFlux_exact`: the independently evaluated outer flux is `24`.
- `production_and_exact`: the production theorem joins all three exact evaluations.

## iii. Table of contents

- A. Two-sided polynomial fixture
- B. Independent flux and divergence computations
- C. Production-theorem sentinel

## iv. References

This is a Physlib-original adversarial regression for the neutral split-box calculus layer.
-/

@[expose] public section

open Matrix MeasureTheory
open scoped Interval

namespace Space
namespace AffineSplitBoxDivergenceRegression

noncomputable section

/-!
## A. Two-sided polynomial fixture
-/

/-- The origin used as the split-box center. -/
def center : Space :=
  ⟨![(0 : ℝ), 0, 0]⟩

/-- The first standard frame direction. -/
def first : Space :=
  ⟨![(1 : ℝ), 0, 0]⟩

/-- The second standard frame direction. -/
def second : Space :=
  ⟨![(0 : ℝ), 1, 0]⟩

/-- The third standard frame direction. -/
def third : Space :=
  ⟨![(0 : ℝ), 0, 1]⟩

/-- The third coordinate vector in the field codomain. -/
def outputTwo : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![(0 : ℝ), 0, 1]

/-- The negative-side field `(0, 0, z)`. -/
def negativeField (x : Space) : EuclideanSpace ℝ (Fin 3) :=
  x 2 • outputTwo

/-- The positive-side field `(0, 0, 2z + 3)`. -/
def positiveField (x : Space) : EuclideanSpace ℝ (Fin 3) :=
  (2 * x 2 + 3) • outputTwo

/-- The negative fixture field is continuously differentiable. -/
lemma negativeField_contDiff : ContDiff ℝ 1 negativeField := by
  unfold negativeField
  fun_prop

/-- The positive fixture field is continuously differentiable. -/
lemma positiveField_contDiff : ContDiff ℝ 1 positiveField := by
  unfold positiveField
  fun_prop

/-- The standard affine-box parameterization has coordinates `(u, v, w)`. -/
lemma point_apply (u v w : ℝ) :
    affineBoxPoint center first second third u v w = ⟨![u, v, w]⟩ := by
  ext i
  fin_cases i <;> simp [affineBoxPoint, center, first, second, third]

/-- The standard frame has signed volume one. -/
lemma orientedVolume :
    inner ℝ (basis.repr first) (basis.repr second ⨯ₑ₃ basis.repr third) = 1 := by
  norm_num [first, second, third, crossProduct, PiLp.inner_apply,
    Fin.sum_univ_three, RCLike.inner_apply, basis_repr_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

/-- The negative field has constant divergence one. -/
lemma negativeField_divergence (x : Space) : (∇ ⬝ negativeField) x = 1 := by
  norm_num [negativeField, outputTwo, div, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

/-- The positive field has constant divergence two. -/
lemma positiveField_divergence (x : Space) : (∇ ⬝ positiveField) x = 2 := by
  norm_num [positiveField, outputTwo, div, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  rw [deriv_eq, fderiv_fun_add (by fun_prop) (by fun_prop),
    fderiv_const_mul (by fun_prop), fderiv_fun_const]
  simp [← deriv_eq]

/-- The negative-side local regularity record on the lower unit half-box. -/
lemma negativeRegularity :
    AffineBoxDivergenceRegularity negativeField center first second third
      (-1) (-1) (-1) 1 1 0 ∅ := by
  apply AffineBoxDivergenceRegularity.of_differentiable
    negativeField center first second third (-1) (-1) (-1) 1 1 0
    (negativeField_contDiff.differentiable (by norm_num))
  have hContinuous : Continuous fun q : Fin 3 → ℝ ↦
      (∇ ⬝ negativeField) (affineBoxCoordinatePoint center first second third q) *
        inner ℝ (basis.repr first) (basis.repr second ⨯ₑ₃ basis.repr third) := by
    simp_rw [negativeField_divergence, orientedVolume]
    fun_prop
  exact hContinuous.continuousOn.integrableOn_compact isCompact_Icc

/-- The positive-side local regularity record on the upper unit half-box. -/
lemma positiveRegularity :
    AffineBoxDivergenceRegularity positiveField center first second third
      (-1) (-1) 0 1 1 1 ∅ := by
  apply AffineBoxDivergenceRegularity.of_differentiable
    positiveField center first second third (-1) (-1) 0 1 1 1
    (positiveField_contDiff.differentiable (by norm_num))
  have hContinuous : Continuous fun q : Fin 3 → ℝ ↦
      (∇ ⬝ positiveField) (affineBoxCoordinatePoint center first second third q) *
        inner ℝ (basis.repr first) (basis.repr second ⨯ₑ₃ basis.repr third) := by
    simp_rw [positiveField_divergence, orientedVolume]
    fun_prop
  exact hContinuous.continuousOn.integrableOn_compact isCompact_Icc

/-- The two local regularity records form the split-box regularity package. -/
lemma regularity : AffineSplitBoxDivergenceRegularity negativeField positiveField
    center first second third 1 1 ∅ ∅ :=
  ⟨negativeRegularity, positiveRegularity⟩

/-!
## B. Independent flux and divergence computations
-/

/-- Every negative-side first- or second-lateral cofactor pairing vanishes. -/
lemma negativeLateralPairings (u v w : ℝ) :
    inner ℝ (negativeField (affineBoxPoint center first second third u v w))
        (basis.repr second ⨯ₑ₃ basis.repr third) = 0 ∧
      inner ℝ (negativeField (affineBoxPoint center first second third u v w))
        (basis.repr third ⨯ₑ₃ basis.repr first) = 0 := by
  rw [point_apply]
  norm_num [negativeField, outputTwo, first, second, third, crossProduct,
    PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, basis_repr_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

/-- Every positive-side first- or second-lateral cofactor pairing vanishes. -/
lemma positiveLateralPairings (u v w : ℝ) :
    inner ℝ (positiveField (affineBoxPoint center first second third u v w))
        (basis.repr second ⨯ₑ₃ basis.repr third) = 0 ∧
      inner ℝ (positiveField (affineBoxPoint center first second third u v w))
        (basis.repr third ⨯ₑ₃ basis.repr first) = 0 := by
  rw [point_apply]
  norm_num [positiveField, outputTwo, first, second, third, crossProduct,
    PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, basis_repr_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

/-- The negative principal-face density is `w`. -/
lemma negativePrincipalDensity (u v w : ℝ) :
    inner ℝ (negativeField (affineBoxPoint center first second third u v w))
        (basis.repr first ⨯ₑ₃ basis.repr second) = w := by
  rw [point_apply]
  norm_num [negativeField, outputTwo, first, second, crossProduct,
    PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, basis_repr_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

/-- The positive principal-face density is `2w + 3`. -/
lemma positivePrincipalDensity (u v w : ℝ) :
    inner ℝ (positiveField (affineBoxPoint center first second third u v w))
        (basis.repr first ⨯ₑ₃ basis.repr second) = 2 * w + 3 := by
  rw [point_apply]
  norm_num [positiveField, outputTwo, first, second, crossProduct,
    PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, basis_repr_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

/-- Direct integration gives total bulk divergence `12`. -/
lemma bulkDivergence_exact :
    affineSplitBoxBulkDivergence negativeField positiveField
      center first second third 1 1 = 12 := by
  unfold affineSplitBoxBulkDivergence
  simp_rw [negativeField_divergence, positiveField_divergence, orientedVolume]
  norm_num

/-- All four split lateral-face fluxes vanish. -/
lemma lateralFlux_exact :
    affineSplitBoxLateralFlux negativeField positiveField
      center first second third 1 1 = 0 := by
  unfold affineSplitBoxLateralFlux
  simp_rw [(negativeLateralPairings _ _ _).1, (negativeLateralPairings _ _ _).2,
    (positiveLateralPairings _ _ _).1, (positiveLateralPairings _ _ _).2]
  norm_num

/-- Direct top-minus-bottom integration gives principal flux `24`. -/
lemma principalFlux_exact :
    affineSplitBoxPrincipalFlux negativeField positiveField
      center first second third 1 1 = 24 := by
  unfold affineSplitBoxPrincipalFlux
  simp_rw [positivePrincipalDensity, negativePrincipalDensity]
  norm_num

/-- The independently retained carrier jump is `12`. -/
lemma carrierJump_exact :
    affineSplitBoxCarrierJump negativeField positiveField
      center first second third 1 = 12 := by
  unfold affineSplitBoxCarrierJump
  simp_rw [positivePrincipalDensity, negativePrincipalDensity]
  norm_num

/-- The independently evaluated outer flux is `24`. -/
lemma outerFlux_exact :
    affineSplitBoxOuterFlux negativeField positiveField
      center first second third 1 1 = 24 := by
  rw [affineSplitBoxOuterFlux, principalFlux_exact, lateralFlux_exact]
  norm_num

/-!
## C. Production-theorem sentinel
-/

/-- The production split-box theorem agrees with all independent exact evaluations. -/
lemma production_and_exact :
    affineSplitBoxOuterFlux negativeField positiveField
          center first second third 1 1 =
        affineSplitBoxBulkDivergence negativeField positiveField
            center first second third 1 1 +
          affineSplitBoxCarrierJump negativeField positiveField
            center first second third 1 ∧
      affineSplitBoxOuterFlux negativeField positiveField
          center first second third 1 1 = 24 ∧
      affineSplitBoxBulkDivergence negativeField positiveField
          center first second third 1 1 = 12 ∧
      affineSplitBoxCarrierJump negativeField positiveField
          center first second third 1 = 12 := by
  refine ⟨affineSplitBoxOuterFlux_eq_bulkDivergence_add_carrierJump
    negativeField positiveField center first second third 1 1
    (by norm_num) (by norm_num) ∅ ∅ regularity,
    outerFlux_exact, bulkDivergence_exact, carrierJump_exact⟩

end
end AffineSplitBoxDivergenceRegression
end Space
