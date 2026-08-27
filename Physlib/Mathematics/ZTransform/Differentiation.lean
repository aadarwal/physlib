/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.Calculus.Deriv.ZPow
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Physlib.Mathematics.ZTransform.Convergence

/-!
# Complex differentiation of the unilateral Z-transform

## i. Overview

This file differentiates the unilateral Z-transform on the strict radial interior of its
absolute region of convergence. If `w` is in `ROC f` and `‖w‖ < ‖z‖`, absolute convergence
at `w` supplies both convergence of the transform at `z` and a locally uniform summable bound
for the derivatives of the series terms near `z`. Mathlib's theorem on differentiating a series
on an open preconnected set then identifies the derivative of the transform with the sum of the
term derivatives.

The strict inequality is the analytic margin used by the proof. An intermediate radius between
`‖w‖` and `‖z‖` gives a comparison point for the derivative series. A ball about `z` stays
outside that intermediate circle, so every derivative term on the ball is bounded by its value
at the comparison point. This makes the termwise-differentiation gate explicit rather than
treating interchange of differentiation and infinite summation as a formal rewrite.

There are two convergence steps. First, the derivative series at any strictly outer point is
factored into the absolutely summable transform series at `w` and a bounded geometric factor.
Second, the derivative series at the intermediate comparison point supplies a single summable
majorant on the whole open ball. Thus the hypotheses passed to Mathlib are obtained from `ROC`
membership and the strict modulus inequality, not assumed as an opaque uniform-convergence
premise.

The derivative is the complex derivative over `ℂ`. The multiplication-by-index corollary is
proved by distributing `-z` through the summable derivative series and cancelling one inverse
power of the nonzero evaluation point. It is therefore downstream of the analytic result rather
than a restatement of the quotient or of a separately defined transform formula.

The resulting multiplication-by-index law is

`Z{n f[n]}(z) = -z * (d/dz) Z{f[n]}(z)`.

Here the index multiplier is interpreted in `ℂ`, and only the nonnegative samples enter the
unilateral transform. No causality hypothesis is needed for this analytic identity.

## ii. Key results

- `Physlib.ZTransform.hasDerivAt_seriesTerm`: derivative of one transform-series term.
- `Physlib.ZTransform.summable_derivativeSeries`: summability of the term derivatives at a
  point strictly outside an inner ROC witness.
- `Physlib.ZTransform.hasDerivAt_transform`: termwise differentiation of the transform.
- `Physlib.ZTransform.transform_indexMul_eq_neg_z_mul_deriv`: multiplication by the sample index
  corresponds to `-z` times complex differentiation.

## iii. Table of contents

- A. Derivative of one series term
- B. Summability of the derivative series
- C. Differentiation of the transform

## iv. References

The multiplication-by-index identity corresponds to Theorem 10 (p. 491) of U. Siddique,
M. Y. Mahmoud, and S. Tahar, "On the Formalization of Z-Transform in HOL", ITP 2014,
LNCS 8558, pp. 483-498.

The source assumes a nonzero point with positive real part and convergence of the
index-multiplied transform. The result here instead uses the checkable sufficient condition that
the original transform converge absolutely at a point of strictly smaller modulus. This radial
margin justifies locally uniform convergence of the derivative series; the positive-real-part
restriction is unnecessary. No converse, boundary differentiability, ordered-convergence result,
inverse transform, stability statement, or physical or optical interpretation is asserted.

This file is neutral mathematics and imports no physics.
-/

@[expose] public section

namespace Physlib.ZTransform

noncomputable section

open Filter Metric

/-!

## A. Derivative of one series term

-/

/-- Away from zero, the derivative of the `n`-th transform-series term is
`-n * f n * z⁻¹ ^ (n + 1)`. -/
lemma hasDerivAt_seriesTerm (f : ℤ → ℂ) (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    HasDerivAt (fun y => seriesTerm f y n)
      (-((n : ℂ) * f n * z⁻¹ ^ (n + 1))) z := by
  rw [show (fun y => seriesTerm f y n) = fun y => f n * y ^ (-(n : ℤ)) by
    funext y
    exact seriesTerm_eq_zpow f y n]
  convert (hasDerivAt_zpow (-(n : ℤ)) z (Or.inl hz)).const_mul (f n) using 1
  simp only [Int.cast_neg, Int.cast_natCast]
  rw [zpow_sub₀ hz, zpow_neg, zpow_natCast]
  field_simp
  ring

/-!

## B. Summability of the derivative series

-/

/-- If the transform converges absolutely at `w` and `z` has strictly larger modulus, then the
series of term derivatives is summable at `z`.

The proof factors each derivative term into the summable transform term at `w` and a factor
proportional to `n * (w / z) ^ n`. The latter tends to zero because `‖w / z‖ < 1`.
-/
lemma summable_derivativeSeries {f : ℤ → ℂ} {w z : ℂ}
    (hw : w ∈ ROC f) (hwz : ‖w‖ < ‖z‖) :
    Summable fun n : ℕ => -((n : ℂ) * f n * z⁻¹ ^ (n + 1)) := by
  have hz : z ≠ 0 := ne_zero_of_norm_le hw.1 hwz.le
  have hquotient : ‖w / z‖ < 1 := by
    rw [norm_div, div_lt_one₀ (norm_pos_iff.mpr hz)]
    exact hwz
  have hgeometric : Summable fun n : ℕ => (n : ℂ) ^ 1 * (w / z) ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one 1 hquotient
  have hgeometricZero :
      Tendsto (fun n : ℕ => (n : ℂ) * (w / z) ^ n) atTop (nhds 0) := by
    simpa using hgeometric.tendsto_atTop_zero
  have hfactorZero :
      Tendsto (fun n : ℕ => -((n : ℂ) * (w / z) ^ n * z⁻¹)) cofinite (nhds 0) := by
    rw [Nat.cofinite_eq_atTop]
    simpa only [neg_zero, zero_mul] using (hgeometricZero.mul_const z⁻¹).neg
  have hproduct : Summable fun n : ℕ =>
      seriesTerm f w n * -((n : ℂ) * (w / z) ^ n * z⁻¹) :=
    (summable_norm_iff.mpr hw.2).mul_tendsto_const hfactorZero
  refine hproduct.congr fun n => ?_
  have hcancel : w⁻¹ ^ n * w ^ n = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hw.1, one_pow]
  calc
    seriesTerm f w n * -((n : ℂ) * (w / z) ^ n * z⁻¹) =
        -((n : ℂ) * f n * (w⁻¹ ^ n * w ^ n) * (z⁻¹ ^ n * z⁻¹)) := by
      rw [seriesTerm, div_pow, div_eq_mul_inv, inv_pow]
      ring
    _ = -((n : ℂ) * f n * z⁻¹ ^ (n + 1)) := by
      rw [hcancel, mul_one, pow_succ]

/-- Increasing the evaluation modulus can only decrease the norm of a derivative-series term. -/
private lemma norm_derivativeSeriesTerm_le (f : ℤ → ℂ) {v y : ℂ}
    (hv : v ≠ 0) (hvy : ‖v‖ ≤ ‖y‖) (n : ℕ) :
    ‖-((n : ℂ) * f n * y⁻¹ ^ (n + 1))‖ ≤
      ‖-((n : ℂ) * f n * v⁻¹ ^ (n + 1))‖ := by
  have hypos : 0 < ‖y‖ := (norm_pos_iff.mpr hv).trans_le hvy
  have hinv : ‖y‖⁻¹ ≤ ‖v‖⁻¹ := by
    gcongr
  simp only [norm_neg, norm_mul, norm_pow, norm_inv]
  gcongr

/-!

## C. Differentiation of the transform

-/

/-- The unilateral Z-transform is complex differentiable at every point strictly outside an
inner absolute-convergence witness. Its derivative is the sum of the term derivatives.

The proof applies `hasDerivAt_tsum_of_isPreconnected` on an open ball about `z`. The comparison
radius is the midpoint of `‖w‖` and `‖z‖`; the entire ball lies outside that circle, giving
a summable uniform majorant for the derivatives.
-/
lemma hasDerivAt_transform {f : ℤ → ℂ} {w z : ℂ}
    (hw : w ∈ ROC f) (hwz : ‖w‖ < ‖z‖) :
    HasDerivAt (transform f)
      (∑' n : ℕ, -((n : ℂ) * f n * z⁻¹ ^ (n + 1))) z := by
  let radius : ℝ := (‖w‖ + ‖z‖) / 2
  let v : ℂ := radius
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw.1
  have hz : z ≠ 0 := ne_zero_of_norm_le hw.1 hwz.le
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hradiusPos : 0 < radius := by
    dsimp [radius]
    linarith
  have hvnorm : ‖v‖ = radius := by
    simp [v, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hradiusPos]
  have hwv : ‖w‖ < ‖v‖ := by
    rw [hvnorm]
    dsimp [radius]
    linarith
  have hvz : ‖v‖ < ‖z‖ := by
    rw [hvnorm]
    dsimp [radius]
    linarith
  have hv : v ≠ 0 := norm_pos_iff.mp (hwpos.trans hwv)
  let r : ℝ := ‖z‖ - ‖v‖
  have hr : 0 < r := by
    exact sub_pos.mpr hvz
  have hmajorant : Summable fun n : ℕ =>
      ‖-((n : ℂ) * f n * v⁻¹ ^ (n + 1))‖ :=
    summable_norm_iff.mpr (summable_derivativeSeries hw hwv)
  have hzsum : Summable (seriesTerm f z) :=
    summable_seriesTerm_of_norm_le hw.1 hwz.le hw.2
  simpa only [transform] using
    hasDerivAt_tsum_of_isPreconnected
      (u := fun n : ℕ => ‖-((n : ℂ) * f n * v⁻¹ ^ (n + 1))‖)
      (t := ball z r) (g := fun n y => seriesTerm f y n)
      (g' := fun n y => -((n : ℂ) * f n * y⁻¹ ^ (n + 1)))
      (y₀ := z) (y := z) hmajorant isOpen_ball (convex_ball z r).isPreconnected
      (fun n y hy => by
        have hdist : ‖z - y‖ < r := by
          simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hy
        have hvy : ‖v‖ < ‖y‖ := by
          have hnorm := norm_sub_norm_le z y
          dsimp [r] at hdist
          linarith
        exact hasDerivAt_seriesTerm f n (ne_zero_of_norm_le hv hvy.le))
      (fun n y hy => by
        have hdist : ‖z - y‖ < r := by
          simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hy
        have hvy : ‖v‖ < ‖y‖ := by
          have hnorm := norm_sub_norm_le z y
          dsimp [r] at hdist
          linarith
        exact norm_derivativeSeriesTerm_le f hv hvy.le n)
      (mem_ball_self hr) hzsum (mem_ball_self hr)

/-- Multiplication of a unilateral sequence by its sample index corresponds to `-z` times the
complex derivative of its Z-transform. The strict inner-ROC witness supplies the locally uniform
derivative-series convergence needed for the interchange.
-/
lemma transform_indexMul_eq_neg_z_mul_deriv {f : ℤ → ℂ} {w z : ℂ}
    (hw : w ∈ ROC f) (hwz : ‖w‖ < ‖z‖) :
    transform (fun n : ℤ => (n : ℂ) * f n) z = -z * deriv (transform f) z := by
  have hz : z ≠ 0 := ne_zero_of_norm_le hw.1 hwz.le
  have hseries := summable_derivativeSeries hw hwz
  change (∑' n : ℕ, (n : ℂ) * f n * z⁻¹ ^ n) = -z * deriv (transform f) z
  rw [(hasDerivAt_transform hw hwz).deriv, ← hseries.tsum_mul_left (-z)]
  refine tsum_congr fun n => ?_
  rw [pow_succ]
  calc
    (n : ℂ) * f n * z⁻¹ ^ n =
        ((n : ℂ) * f n * z⁻¹ ^ n) * (z * z⁻¹) := by
      rw [mul_inv_cancel₀ hz, mul_one]
    _ = -z * -((n : ℂ) * f n * (z⁻¹ ^ n * z⁻¹)) := by
      ring

end

end Physlib.ZTransform
