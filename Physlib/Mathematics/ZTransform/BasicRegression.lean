/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Mathematics.ZTransform.Basic

/-!
# Regression tests for the unilateral Z-transform

## i. Overview

These examples check the hypotheses of the shift laws rather than only their conclusions. Two of
them are deliberately negative: they exhibit sequences at which a hypothesis-free version of a
shift law is false, so a later simplification of `Physlib.ZTransform.transform_delay` or
`Physlib.ZTransform.transform_advance` cannot silently pass.

The first negative example removes causality. A sequence supported only at index `-1` has zero
unilateral transform because the transform never sees a negative index, yet delaying it by one
sample moves that sample to index `0` and produces transform `1`. The right-shift law therefore
fails without the causality hypothesis, and by exactly the amount that the hypothesis excludes.

The second negative example removes the startup sum. The unit impulse advanced by one sample has
zero unilateral transform, while `z` times the transform of the unit impulse is `z`. The
left-shift law therefore fails without its explicit startup term at every nonzero `z`.

The remaining examples are positive: a two-tap finite-impulse-response sequence has the expected
polynomial transform in `z⁻¹`, and scaling in the `z` domain moves a delayed impulse in the
direction that the law asserts rather than the reciprocal direction.

## ii. Key results

- `Physlib.ZTransform.transform_delay_ne_of_not_isCausal`: the right-shift law is false without
  the causality hypothesis.
- `Physlib.ZTransform.transform_advance_ne_without_startup`: the left-shift law is false without
  its startup sum.
- `Physlib.ZTransform.transform_twoTap`: a two-tap sequence transforms to `b₀ + b₁ * z⁻¹`.
- `Physlib.ZTransform.transform_zScale_delay_unitImpulse`: `z`-domain scaling of a delayed
  impulse produces `a * z⁻¹`, not `a⁻¹ * z⁻¹`.

## iii. Table of contents

- A. A non-causal sequence defeats the right-shift law
- B. A missing startup sum defeats the left-shift law
- C. A two-tap finite-impulse-response sequence
- D. Scaling in the z-domain moves a delayed impulse

## iv. References

The statements checked here are those of U. Siddique, M. Y. Mahmoud, and S. Tahar, "On the
Formalization of Z-Transform in HOL", ITP 2014, LNCS 8558, Theorem 5 (left shift, p. 489) and
Theorem 6 (right shift, p. 490). This file adds no new mathematics; it certifies that the
hypotheses carried by those two theorems in
`Physlib.Mathematics.ZTransform.Basic` are load-bearing.

These are algebraic regressions on complex sequences. No physical, optical, or signal-processing
interpretation is asserted.

-/

@[expose] public section

namespace Physlib.ZTransform

noncomputable section

/-!

## A. A non-causal sequence defeats the right-shift law

-/

/-- A sequence supported only at index `-1`, used as a non-causal counterexample. -/
def regressionAtNegOne : ℤ → ℂ := fun n => if n = -1 then 1 else 0

/-- The counterexample sequence is not causal. -/
lemma regressionAtNegOne_not_isCausal : ¬ IsCausal regressionAtNegOne := by
  intro h
  have := h (-1) (by norm_num)
  simp [regressionAtNegOne] at this

/-- Every nonnegative-index sample of the counterexample sequence vanishes. -/
@[simp]
lemma seriesTerm_regressionAtNegOne (z : ℂ) (n : ℕ) : seriesTerm regressionAtNegOne z n = 0 := by
  have hne : ((n : ℤ)) ≠ -1 := by omega
  simp [seriesTerm, regressionAtNegOne, hne]

/-- The counterexample sequence has zero unilateral transform everywhere. -/
@[simp]
lemma transform_regressionAtNegOne (z : ℂ) : transform regressionAtNegOne z = 0 := by
  simp [transform]

/-- Delaying the counterexample sequence by one sample moves its single nonzero sample to
index `0`. -/
@[simp]
lemma seriesTerm_delay_regressionAtNegOne (z : ℂ) (n : ℕ) :
    seriesTerm (delay 1 regressionAtNegOne) z n = if n = 0 then 1 else 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [seriesTerm, delay, regressionAtNegOne]
  · have hne : ((n : ℤ) - 1) ≠ -1 := by omega
    simp [seriesTerm, delay, regressionAtNegOne, hne, hn.ne']

/-- The delayed counterexample sequence has unit transform. -/
lemma transform_delay_regressionAtNegOne (z : ℂ) :
    transform (delay 1 regressionAtNegOne) z = 1 := by
  rw [transform]
  simp only [seriesTerm_delay_regressionAtNegOne]
  rw [tsum_eq_single 0 fun n hn => by simp [hn]]
  simp

/-- Without the causality hypothesis the right-shift law is false: for this non-causal sequence
the delayed transform is `1` while `z⁻¹` times the original transform is `0`. -/
theorem transform_delay_ne_of_not_isCausal (z : ℂ) :
    transform (delay 1 regressionAtNegOne) z ≠ z⁻¹ ^ 1 * transform regressionAtNegOne z := by
  rw [transform_delay_regressionAtNegOne, transform_regressionAtNegOne, mul_zero]
  exact one_ne_zero

/-!

## B. A missing startup sum defeats the left-shift law

-/

/-- Advancing the unit impulse by one sample removes its only nonnegative sample. -/
@[simp]
lemma seriesTerm_advance_unitImpulse (z : ℂ) (n : ℕ) :
    seriesTerm (advance 1 unitImpulse) z n = 0 := by
  have hne : ((n : ℤ) + 1) ≠ 0 := by omega
  simp [seriesTerm, advance, unitImpulse, hne]

/-- The advanced unit impulse has zero unilateral transform. -/
lemma transform_advance_unitImpulse (z : ℂ) : transform (advance 1 unitImpulse) z = 0 := by
  simp [transform]

/-- The left-shift law holds for the unit impulse exactly because of its startup term. -/
lemma transform_advance_unitImpulse_eq (z : ℂ) (hz : z ≠ 0) :
    transform (advance 1 unitImpulse) z =
      z ^ 1 * (transform unitImpulse z - ∑ n ∈ Finset.range 1, seriesTerm unitImpulse z n) :=
  transform_advance hz 1 (summable_seriesTerm_unitImpulse z)

/-- Dropping the startup sum makes the left-shift law false at every nonzero `z`: the advanced
transform is `0` while `z` times the original transform is `z`. -/
theorem transform_advance_ne_without_startup {z : ℂ} (hz : z ≠ 0) :
    transform (advance 1 unitImpulse) z ≠ z ^ 1 * transform unitImpulse z := by
  rw [transform_advance_unitImpulse, transform_unitImpulse, mul_one, pow_one]
  exact fun h => hz h.symm

/-!

## C. A two-tap finite-impulse-response sequence

-/

/-- The two-tap finite-impulse-response sequence with taps `b₀` at index `0` and `b₁` at
index `1`. -/
def twoTap (b₀ b₁ : ℂ) : ℤ → ℂ := fun n => if n = 0 then b₀ else if n = 1 then b₁ else 0

/-- The two-tap sequence is causal. -/
lemma twoTap_isCausal (b₀ b₁ : ℂ) : IsCausal (twoTap b₀ b₁) := by
  intro n hn
  have h0 : n ≠ 0 := by omega
  have h1 : n ≠ 1 := by omega
  simp [twoTap, h0, h1]

/-- The transform series of the two-tap sequence is supported on the first two indices. -/
@[simp]
lemma seriesTerm_twoTap (b₀ b₁ z : ℂ) (n : ℕ) :
    seriesTerm (twoTap b₀ b₁) z n = if n = 0 then b₀ else if n = 1 then b₁ * z⁻¹ else 0 := by
  match n with
  | 0 => simp [seriesTerm, twoTap]
  | 1 => simp [seriesTerm, twoTap]
  | (k + 2) =>
    have h0 : ((k : ℤ) + 2) ≠ 0 := by omega
    have h1 : ((k : ℤ) + 2) ≠ 1 := by omega
    simp [seriesTerm, twoTap, h0, h1]

/-- The transform series of the two-tap sequence is summable at every point. -/
lemma summable_seriesTerm_twoTap (b₀ b₁ z : ℂ) : Summable (seriesTerm (twoTap b₀ b₁) z) := by
  refine summable_of_ne_finset_zero (s := ({0, 1} : Finset ℕ)) fun n hn => ?_
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
  simp [seriesTerm_twoTap, hn.1, hn.2]

/-- A two-tap sequence transforms to the first-degree polynomial `b₀ + b₁ * z⁻¹` in `z⁻¹`. -/
theorem transform_twoTap (b₀ b₁ z : ℂ) : transform (twoTap b₀ b₁) z = b₀ + b₁ * z⁻¹ := by
  rw [transform, tsum_eq_sum (s := ({0, 1} : Finset ℕ)) fun n hn => ?_]
  · simp
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    simp [seriesTerm_twoTap, hn.1, hn.2]

/-!

## D. Scaling in the z-domain moves a delayed impulse

-/

/-- Scaling a delayed unit impulse by `a ^ n` multiplies its transform by `a`, so the law replaces
`z` by `z / a` rather than by `a * z`. -/
theorem transform_zScale_delay_unitImpulse (a z : ℂ) :
    transform (zScale a (delay 1 unitImpulse)) z = a * z⁻¹ := by
  rw [transform_zScale, transform_delay_unitImpulse, pow_one, div_eq_mul_inv, mul_inv_rev,
    inv_inv]

/-- The scaled result is not the reciprocal convention, for a concrete nonzero scale and point. -/
theorem transform_zScale_delay_unitImpulse_ne_inv :
    transform (zScale 2 (delay 1 unitImpulse)) 1 ≠ (2 : ℂ)⁻¹ * (1 : ℂ)⁻¹ := by
  rw [transform_zScale_delay_unitImpulse]
  norm_num

end

end Physlib.ZTransform
