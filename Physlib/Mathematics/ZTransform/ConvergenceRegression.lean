/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Mathlib.Analysis.PSeries
public import Physlib.Mathematics.ZTransform.Convergence

/-!
# Regression tests for the region of convergence

## i. Overview

The main result here is that the absolute and conditional regions of convergence of the
unilateral Z-transform are not the same set. The sequence `1 / (n + 1)`, extended by zero to
negative indices, has transform series `∑ (-1) ^ n / (n + 1)` at `z = -1`. That series converges,
by the alternating series test, and does not converge absolutely, because the harmonic series
diverges. So `-1` lies in the conditional region and not in the absolute one, and the inclusion
proved in `Physlib.Mathematics.ZTransform.Basic` is strict for this sequence.

This turns the requirement that the two regions be kept apart into a theorem rather than a
convention. A development that defined one region and called it the other would fail here.

The remaining examples fix the boundary and the rotation behaviour of the region of convergence.
A geometric sequence of ratio `a` does not converge at `z = a` itself, so the region is the open
exterior and not the closed one. The unit step diverges at `Complex.I` and converges at
`2 * Complex.I`, which are two points of different modulus on the same ray, and it diverges at
`1` and at `Complex.I`, which are two points of the same modulus; together these fix that
membership depends on the modulus and on nothing else.

## ii. Key results

- `Physlib.ZTransform.not_summable_seriesTerm_harmonicSeq`: the transform series of `1 / (n + 1)`
  is not absolutely convergent at `z = -1`.
- `Physlib.ZTransform.neg_one_mem_condROC_harmonicSeq`: it is conditionally convergent there.
- `Physlib.ZTransform.ROC_ssubset_condROC_harmonicSeq`: the absolute region of convergence is a
  strict subset of the conditional one for this sequence.
- `Physlib.ZTransform.exists_ROC_ssubset_condROC`: the two regions are not the same construction.
- `Physlib.ZTransform.self_notMem_ROC_geometricSeq`: the region of convergence of a geometric
  sequence excludes its own ratio, so the exterior is open.

## iii. Table of contents

- A. The alternating harmonic sequence
- B. Conditional convergence without absolute convergence
- C. The boundary of a geometric region of convergence
- D. Dependence on the modulus alone

## iv. References

The separation proved here is required by `goal.md` section H.4 S5, "analytic unilateral
Z-transform with conditional and absolute convergence regions kept distinct", and by the
regression row T-03 of `goal.md` section I.3. Both U. Siddique, M. Y. Mahmoud, and S. Tahar,
"On the Formalization of Z-Transform in HOL", ITP 2014, LNCS 8558, Definition 9 (p. 488), and
the journal version, "Formal Analysis of Discrete-Time Systems using z-Transform", Journal of
Applied Logics 5(4), 2018, pp. 875-906, expressly choose ordered convergence for their region
while discussing absolute convergence as a distinct alternative. Physlib names both: `condROC`
corresponds to that ordered notion and `ROC` is the stronger absolute region. The strict-subset
result is a Physlib extension showing mechanically why the two must not be identified.

The alternating harmonic series and the divergence of the harmonic series are standard; they are
taken from Mathlib rather than reproved.

These are algebraic and analytic regressions on complex sequences. No physical, optical, or
signal-processing interpretation is asserted.

-/

@[expose] public section

namespace Physlib.ZTransform

noncomputable section

open Filter

/-!

## A. The alternating harmonic sequence

-/

/-- The causal sequence whose nonnegative-index samples are `1 / (n + 1)`. -/
def harmonicSeq : ℤ → ℂ := zeroExtend fun n : ℕ => ((n + 1 : ℕ) : ℂ)⁻¹

/-- The harmonic sequence is causal. -/
lemma harmonicSeq_isCausal : IsCausal harmonicSeq :=
  zeroExtend_isCausal _

/-- The transform series of the harmonic sequence at `z = -1` alternates in sign. -/
lemma seriesTerm_harmonicSeq_neg_one (n : ℕ) :
    seriesTerm harmonicSeq (-1) n =
      (((-1 : ℝ) ^ n * (((n + 1 : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) := by
  rw [seriesTerm, harmonicSeq, zeroExtend_natCast]
  push_cast
  rw [inv_neg, inv_one, neg_pow, one_pow, mul_one]
  ring

/-- The norm of the `n`-th term at `z = -1` is `1 / (n + 1)`. -/
lemma norm_seriesTerm_harmonicSeq_neg_one (n : ℕ) :
    ‖seriesTerm harmonicSeq (-1) n‖ = (((n + 1 : ℕ) : ℝ))⁻¹ := by
  rw [seriesTerm_harmonicSeq_neg_one, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_pow,
    abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg (by positivity)]

/-!

## B. Conditional convergence without absolute convergence

-/

/-- The transform series of the harmonic sequence does not converge absolutely at `z = -1`,
because the harmonic series diverges. -/
lemma not_summable_seriesTerm_harmonicSeq :
    ¬ Summable (seriesTerm harmonicSeq (-1)) := by
  intro hs
  have hnorm : Summable fun n : ℕ => (((n + 1 : ℕ) : ℝ))⁻¹ := by
    refine (summable_norm_iff.mpr hs).congr fun n => ?_
    exact norm_seriesTerm_harmonicSeq_neg_one n
  exact Real.not_summable_natCast_inv
    ((summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ))⁻¹) 1).mp hnorm)

/-- The point `-1` is not in the absolute region of convergence of the harmonic sequence. -/
lemma neg_one_notMem_ROC_harmonicSeq : (-1 : ℂ) ∉ ROC harmonicSeq := by
  intro h
  exact not_summable_seriesTerm_harmonicSeq h.2

/-- The point `-1` is in the conditional region of convergence of the harmonic sequence, by the
alternating series test. -/
lemma neg_one_mem_condROC_harmonicSeq : (-1 : ℂ) ∈ condROC harmonicSeq := by
  have hanti : Antitone fun n : ℕ => (((n + 1 : ℕ) : ℝ))⁻¹ := by
    intro a b hab
    have hcast : ((a : ℝ) + 1) ≤ ((b : ℝ) + 1) := by exact_mod_cast Nat.add_le_add_right hab 1
    push_cast
    gcongr
  have htend : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ))⁻¹) atTop (nhds 0) := by
    simpa [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  obtain ⟨l, hl⟩ := hanti.tendsto_alternating_series_of_tendsto_zero htend
  refine ⟨by norm_num, (l : ℂ), ?_⟩
  have hsum : ∀ N : ℕ, ∑ n ∈ Finset.range N, seriesTerm harmonicSeq (-1) n =
      ((∑ i ∈ Finset.range N, (-1 : ℝ) ^ i * (((i + 1 : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) := by
    intro N
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun n _ => seriesTerm_harmonicSeq_neg_one n
  simp_rw [hsum]
  exact (Complex.continuous_ofReal.tendsto l).comp hl

/-- For the harmonic sequence the absolute region of convergence is a strict subset of the
conditional one. -/
lemma ROC_ssubset_condROC_harmonicSeq : ROC harmonicSeq ⊂ condROC harmonicSeq :=
  (Set.ssubset_iff_of_subset (ROC_subset_condROC harmonicSeq)).mpr
    ⟨-1, neg_one_mem_condROC_harmonicSeq, neg_one_notMem_ROC_harmonicSeq⟩

/-- The absolute and conditional regions of convergence are not the same construction: some
sequence separates them. -/
lemma exists_ROC_ssubset_condROC : ∃ f : ℤ → ℂ, ROC f ⊂ condROC f :=
  ⟨harmonicSeq, ROC_ssubset_condROC_harmonicSeq⟩

/-!

## C. The boundary of a geometric region of convergence

-/

/-- A geometric sequence does not converge absolutely at its own ratio, so its region of
convergence is the open exterior of the circle of radius `‖a‖`. -/
lemma self_notMem_ROC_geometricSeq {a : ℂ} (ha : a ≠ 0) : a ∉ ROC (geometricSeq a) := by
  rw [ROC_geometricSeq ha]
  simp

/-- A point strictly outside the circle of radius `‖a‖` is in the region of convergence. -/
lemma two_mul_mem_ROC_geometricSeq {a : ℂ} (ha : a ≠ 0) : 2 * a ∈ ROC (geometricSeq a) := by
  have hapos : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have h2 : ‖(2 : ℂ) * a‖ = 2 * ‖a‖ := by rw [norm_mul]; norm_num
  rw [ROC_geometricSeq ha]
  show ‖a‖ < ‖(2 : ℂ) * a‖
  rw [h2]
  linarith

/-- The transform of the geometric sequence with ratio `1 / 2`, evaluated at `1`. -/
lemma transform_geometricSeq_half : transform (geometricSeq (1 / 2)) 1 = 2 := by
  have hnorm : ‖(1 / 2 : ℂ)‖ < ‖(1 : ℂ)‖ := by norm_num
  rw [transform_geometricSeq (by norm_num) hnorm]
  norm_num

/-!

## D. Dependence on the modulus alone

-/

/-- The unit step diverges on the unit circle at `1`. -/
lemma one_notMem_ROC_unitStep : (1 : ℂ) ∉ ROC unitStep := by
  rw [ROC_unitStep]
  simp

/-- The unit step diverges at `Complex.I`, which has the same modulus as `1`. -/
lemma I_notMem_ROC_unitStep : Complex.I ∉ ROC unitStep := by
  rw [ROC_unitStep]
  simp

/-- The unit step converges at `2 * Complex.I`, which lies on the same ray as `Complex.I` but has
larger modulus. -/
lemma two_mul_I_mem_ROC_unitStep : 2 * Complex.I ∈ ROC unitStep := by
  rw [ROC_unitStep]
  show (1 : ℝ) < ‖(2 : ℂ) * Complex.I‖
  rw [norm_mul, Complex.norm_I, mul_one]
  norm_num

end

end Physlib.ZTransform
