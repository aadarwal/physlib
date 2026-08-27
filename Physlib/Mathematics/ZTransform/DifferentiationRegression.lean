/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Mathematics.ZTransform.Differentiation

/-!
# Regression tests for Z-transform differentiation

## i. Overview

This file tests the complex-differentiation convention on a sequence supported only at index two.
Its transform is computed directly from the primitive `tsum`, and its derivative at `z = 2` is
computed with Mathlib's derivative of inversion. The fixture therefore does not use the production
termwise-differentiation theorem as an oracle.

The index-multiplied transform is `3 / 2`, while the derivative is `-3 / 4`. Consequently the
correct factor `-z` gives `3 / 2`; reversing the sign gives `-3 / 2`, and omitting `z` gives
`3 / 4`. The hostile sentinel records both failures.

## ii. Key results

- `Physlib.ZTransform.transform_differentiationFixture`: direct transform of the one-tap fixture.
- `Physlib.ZTransform.transform_indexMul_differentiationFixture`: direct transform after index
  multiplication.
- `Physlib.ZTransform.deriv_transform_differentiationFixture_at_two`: primitive derivative value.
- `Physlib.ZTransform.transform_indexMul_differentiationFixture_production_agreement`: the
  production identity specialized to the independently witnessed fixture domain.
- `Physlib.ZTransform.transform_indexMul_wrongSign_or_missingFactor_ne`: hostile sign-and-factor
  sentinel.

## iii. Table of contents

- A. Finite-support fixture
- B. Primitive transform and derivative computations
- C. Production agreement
- D. Hostile sign-and-factor sentinel

## iv. References

This is a regression companion to `Physlib.Mathematics.ZTransform.Differentiation`. It makes no
additional source-parity, boundary-convergence, stability, or physical interpretation claim.
-/

@[expose] public section

namespace Physlib.ZTransform

noncomputable section

/-!

## A. Finite-support fixture

-/

/-- A sequence with the single value `3` at index two. -/
def differentiationFixture (n : ℤ) : ℂ := if n = 2 then 3 else 0

/-- The transform series of the fixture has exactly one nonzero term. -/
@[simp]
lemma seriesTerm_differentiationFixture (z : ℂ) (n : ℕ) :
    seriesTerm differentiationFixture z n = if n = 2 then 3 * z⁻¹ ^ 2 else 0 := by
  by_cases hn : n = 2
  · subst n
    simp [seriesTerm, differentiationFixture]
  · have hnInt : (n : ℤ) ≠ 2 := by
      exact_mod_cast hn
    simp [seriesTerm, differentiationFixture, hn, hnInt]

/-- The fixture transform series is summable at every point. -/
lemma summable_seriesTerm_differentiationFixture (z : ℂ) :
    Summable (seriesTerm differentiationFixture z) := by
  refine summable_of_ne_finset_zero (s := ({2} : Finset ℕ)) fun n hn => ?_
  simp only [Finset.mem_singleton] at hn
  simp [seriesTerm_differentiationFixture, hn]

/-!

## B. Primitive transform and derivative computations

-/

/-- The fixture transform is computed directly from its one-term `tsum`. -/
lemma transform_differentiationFixture (z : ℂ) :
    transform differentiationFixture z = 3 * z⁻¹ ^ 2 := by
  rw [transform, tsum_eq_sum (s := ({2} : Finset ℕ)) fun n hn => ?_]
  · simp
  · simp only [Finset.mem_singleton] at hn
    simp [seriesTerm_differentiationFixture, hn]

/-- Multiplication by the index changes the fixture coefficient from `3` to `6`; this transform
is computed directly from the finite series, without the production differentiation identity. -/
lemma transform_indexMul_differentiationFixture (z : ℂ) :
    transform (fun n : ℤ => (n : ℂ) * differentiationFixture n) z = 6 * z⁻¹ ^ 2 := by
  rw [transform, tsum_eq_sum (s := ({2} : Finset ℕ)) fun n hn => ?_]
  · norm_num [seriesTerm, differentiationFixture]
  · simp only [Finset.mem_singleton] at hn
    have hnInt : (n : ℤ) ≠ 2 := by
      exact_mod_cast hn
    simp [seriesTerm, differentiationFixture, hnInt]

/-- At `z = 2`, the derivative of the primitive fixture transform is `-3 / 4`. -/
lemma deriv_transform_differentiationFixture_at_two :
    deriv (transform differentiationFixture) 2 = -(3 / 4 : ℂ) := by
  rw [show transform differentiationFixture = fun z => 3 * z⁻¹ ^ 2 by
    funext z
    exact transform_differentiationFixture z]
  have hinv : HasDerivAt (fun z : ℂ => z⁻¹) (-(2 ^ 2 : ℂ)⁻¹) 2 :=
    hasDerivAt_inv (by norm_num)
  convert (hinv.pow 2).const_mul 3 |>.deriv using 1 <;> norm_num

/-!

## C. Production agreement

-/

/-- The independently finite-supported fixture belongs to the absolute ROC at one. -/
lemma one_mem_ROC_differentiationFixture :
    (1 : ℂ) ∈ ROC differentiationFixture := by
  exact ⟨by norm_num, summable_seriesTerm_differentiationFixture 1⟩

/-- The production specialization uses a genuinely strict radial margin from one to two. -/
lemma norm_one_lt_norm_two : ‖(1 : ℂ)‖ < ‖(2 : ℂ)‖ := by
  norm_num

/-- The production index-multiplication theorem agrees with the independently computed fixture
at its concrete nonunit evaluation point. -/
lemma transform_indexMul_differentiationFixture_production_agreement :
    transform (fun n : ℤ => (n : ℂ) * differentiationFixture n) 2 =
      -2 * deriv (transform differentiationFixture) 2 := by
  exact transform_indexMul_eq_neg_z_mul_deriv
    one_mem_ROC_differentiationFixture norm_one_lt_norm_two

/-!

## D. Hostile sign-and-factor sentinel

-/

/-- At the same nonunit point, reversing the sign or omitting the factor `z` gives a value
different from the independently computed index-multiplied transform. -/
lemma transform_indexMul_wrongSign_or_missingFactor_ne :
    (2 * deriv (transform differentiationFixture) 2 ≠
        transform (fun n : ℤ => (n : ℂ) * differentiationFixture n) 2) ∧
      (-deriv (transform differentiationFixture) 2 ≠
        transform (fun n : ℤ => (n : ℂ) * differentiationFixture n) 2) := by
  rw [deriv_transform_differentiationFixture_at_two,
    transform_indexMul_differentiationFixture]
  norm_num

end

end Physlib.ZTransform
