/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Mathematics.ZTransform.Convergence

/-!
# Inversion and uniqueness of the unilateral Z-transform

## i. Overview

Every nonnegative-index sample of a sequence is recovered from its transform by a limit at
infinity, and consequently a sequence with a nonempty absolute region of convergence is
determined by its transform there.

The estimate that drives everything is elementary. If the transform converges absolutely at `w`,
then for every `z` of modulus at least `‖w‖` the tail beyond the first sample is bounded by the
total mass at `w` times `‖w‖ / ‖z‖`. Letting `‖z‖` grow gives the initial-value theorem: the
transform tends to the sample at index zero as `z` leaves every bounded set.

Applying that to the advanced sequence, and using the left-shift law with its startup sum, gives
an explicit inversion formula for every sample: `f m` is the limit at infinity of
`z ^ m * (transform f z - ∑ n < m, f n * z⁻¹ ^ n)`. No complex differentiation and no
analyticity machinery is used.

Uniqueness follows by strong induction on the index. Two sequences whose transforms agree on the
closed exterior of a circle inside both regions of convergence have the same nonnegative-index
samples; if both are causal, they are equal. The causality hypothesis is not decorative: the
unilateral transform never sees a negative index, so without it the negative-index samples are
genuinely unconstrained, and the companion regression file exhibits two sequences with identical
transforms that differ at a negative index.

## ii. Key results

- `Physlib.ZTransform.norm_transform_sub_apply_zero_le`: the quantitative tail estimate.
- `Physlib.ZTransform.tendsto_transform_cobounded`: the initial-value theorem, that the
  transform tends to the sample at index zero at infinity.
- `Physlib.ZTransform.tendsto_inversion_cobounded`: the inversion formula recovering the sample
  at any index `m`.
- `Physlib.ZTransform.eq_natCast_of_transform_eqOn`: transforms agreeing on the closed exterior
  of a circle force equal nonnegative-index samples.
- `Physlib.ZTransform.eq_of_isCausal_of_transform_eqOn`: for causal sequences, equal transforms
  force equal sequences.

## iii. Table of contents

- A. The tail estimate
- B. The initial-value theorem
- C. Recovering every sample
- D. Uniqueness

## iv. References

The results correspond to Theorem 15 (inverse z-transform, p. 894), Theorem 16 (uniqueness,
p. 894), and Theorem 17 (initial value, p. 894) of U. Siddique, M. Y. Mahmoud, and S. Tahar,
"Formal Analysis of Discrete-Time Systems using z-Transform", Journal of Applied Logics 5(4),
2018, pp. 875-907. Those three theorems are absent from the earlier conference version,
"On the Formalization of Z-Transform in HOL", ITP 2014, LNCS 8558, whose section 6 (p. 497)
lists them as future work.

Two differences from the source are recorded. First, the source recovers the samples as
`f n = D^n (fun z => transform f z⁻¹) 0 / n !`, that is as Taylor coefficients at the origin of
the transform in the reciprocal variable. This file recovers them instead as limits at infinity,
`tendsto_inversion_cobounded`, which is the same content by a different route and needs no
complex differentiation. The Taylor-coefficient form is not proved here; it would need the
power series in the reciprocal variable to be exhibited as an analytic function with its radius
of convergence, and is recorded as remaining work rather than claimed.

Second, the source states uniqueness for one-sided sequences, so causality is implicit in its
setting. Here sequences are two-sided and the unilateral transform cannot see a negative index,
so uniqueness of the sequence itself requires causality as an explicit hypothesis. Without it
only the nonnegative-index samples are determined, and that weaker statement is what
`eq_natCast_of_transform_eqOn` asserts.

This file is neutral mathematics and imports no physics.

-/

@[expose] public section

namespace Physlib.ZTransform

noncomputable section

open Filter Bornology

variable {f g : ℤ → ℂ} {w z : ℂ}

/-!

## A. The tail estimate

-/

/-- The total mass of the transform series at a point of the absolute region of convergence. -/
def seriesMass (f : ℤ → ℂ) (w : ℂ) : ℝ := ∑' n : ℕ, ‖seriesTerm f w n‖

/-- The total mass is nonnegative. -/
lemma seriesMass_nonneg (f : ℤ → ℂ) (w : ℂ) : 0 ≤ seriesMass f w :=
  tsum_nonneg fun _ => norm_nonneg _

/-- A single shifted term at `z` is dominated by the corresponding term at a point of smaller
modulus, scaled by the modulus ratio. -/
lemma norm_seriesTerm_succ_le (f : ℤ → ℂ) (hw : w ≠ 0) (hle : ‖w‖ ≤ ‖z‖) (n : ℕ) :
    ‖seriesTerm f z (n + 1)‖ ≤ ‖seriesTerm f w (n + 1)‖ * (‖w‖ / ‖z‖) := by
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le hwpos hle
  have hinv : ‖z‖⁻¹ ≤ ‖w‖⁻¹ := by gcongr
  rw [norm_seriesTerm, norm_seriesTerm]
  have hww : ‖w‖⁻¹ * ‖w‖ = 1 := inv_mul_cancel₀ (ne_of_gt hwpos)
  have hrhs : ‖f ((n + 1 : ℕ) : ℤ)‖ * ‖w‖⁻¹ ^ (n + 1) * (‖w‖ / ‖z‖)
      = ‖f ((n + 1 : ℕ) : ℤ)‖ * ‖z‖⁻¹ * ‖w‖⁻¹ ^ n := by
    rw [pow_succ, div_eq_mul_inv]
    linear_combination (‖f ((n + 1 : ℕ) : ℤ)‖ * ‖w‖⁻¹ ^ n * ‖z‖⁻¹) * hww
  rw [hrhs, pow_succ]
  calc ‖f ((n + 1 : ℕ) : ℤ)‖ * (‖z‖⁻¹ ^ n * ‖z‖⁻¹)
      = ‖f ((n + 1 : ℕ) : ℤ)‖ * ‖z‖⁻¹ * ‖z‖⁻¹ ^ n := by ring
    _ ≤ ‖f ((n + 1 : ℕ) : ℤ)‖ * ‖z‖⁻¹ * ‖w‖⁻¹ ^ n := by gcongr

/-- The transform differs from the sample at index zero by at most the total mass times the
modulus ratio. This is the estimate behind the initial-value theorem. -/
theorem norm_transform_sub_apply_zero_le (hw : w ∈ ROC f) (hle : ‖w‖ ≤ ‖z‖) :
    ‖transform f z - f 0‖ ≤ seriesMass f w * (‖w‖ / ‖z‖) := by
  have hwne : w ≠ 0 := hw.1
  have hz : z ∈ ROC f := ROC_mem_of_mem_of_norm_le hw hle
  have hnw : Summable fun n : ℕ => ‖seriesTerm f w n‖ := summable_norm_iff.mpr hw.2
  have hnz : Summable fun n : ℕ => ‖seriesTerm f z n‖ := summable_norm_iff.mpr hz.2
  have hnzs : Summable fun n : ℕ => ‖seriesTerm f z (n + 1)‖ :=
    (summable_nat_add_iff (f := fun n : ℕ => ‖seriesTerm f z n‖) 1).mpr hnz
  have hnws : Summable fun n : ℕ => ‖seriesTerm f w (n + 1)‖ :=
    (summable_nat_add_iff (f := fun n : ℕ => ‖seriesTerm f w n‖) 1).mpr hnw
  have h0 : seriesTerm f z 0 = f 0 := by simp [seriesTerm]
  have hsplit : transform f z - f 0 = ∑' n : ℕ, seriesTerm f z (n + 1) := by
    rw [transform, hz.2.tsum_eq_zero_add, h0, add_sub_cancel_left]
  have hmass : ∑' n : ℕ, ‖seriesTerm f w (n + 1)‖ ≤ seriesMass f w := by
    have hsum := hnw.sum_add_tsum_nat_add (f := fun n : ℕ => ‖seriesTerm f w n‖) 1
    have hnonneg : 0 ≤ ∑ i ∈ Finset.range 1, ‖seriesTerm f w i‖ :=
      Finset.sum_nonneg fun _ _ => norm_nonneg _
    rw [seriesMass, ← hsum]
    linarith
  calc ‖transform f z - f 0‖
      = ‖∑' n : ℕ, seriesTerm f z (n + 1)‖ := by rw [hsplit]
    _ ≤ ∑' n : ℕ, ‖seriesTerm f z (n + 1)‖ := norm_tsum_le_tsum_norm hnzs
    _ ≤ ∑' n : ℕ, ‖seriesTerm f w (n + 1)‖ * (‖w‖ / ‖z‖) :=
        Summable.tsum_le_tsum (fun n => norm_seriesTerm_succ_le f hwne hle n) hnzs
          (hnws.mul_right _)
    _ = (∑' n : ℕ, ‖seriesTerm f w (n + 1)‖) * (‖w‖ / ‖z‖) := tsum_mul_right
    _ ≤ seriesMass f w * (‖w‖ / ‖z‖) :=
        mul_le_mul_of_nonneg_right hmass (by positivity)

/-!

## B. The initial-value theorem

-/

/-- The modulus ratio tends to zero as the evaluation point leaves every bounded set. -/
lemma tendsto_norm_ratio_cobounded (M c : ℝ) :
    Tendsto (fun z : ℂ => M * (c / ‖z‖)) (cobounded ℂ) (nhds 0) := by
  have hz : Tendsto (fun z : ℂ => ‖z‖) (cobounded ℂ) atTop := tendsto_norm_cobounded_atTop
  have hinv : Tendsto (fun z : ℂ => ‖z‖⁻¹) (cobounded ℂ) (nhds 0) :=
    tendsto_inv_atTop_zero.comp hz
  have := (hinv.const_mul (M * c))
  rw [mul_zero] at this
  refine this.congr fun z => ?_
  rw [div_eq_mul_inv]
  ring

/-- The initial-value theorem: the transform tends to the sample at index zero as the evaluation
point leaves every bounded set. -/
theorem tendsto_transform_cobounded (hw : w ∈ ROC f) :
    Tendsto (transform f) (cobounded ℂ) (nhds (f 0)) := by
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm' ?_ (tendsto_norm_ratio_cobounded (seriesMass f w) ‖w‖)
  filter_upwards [eventually_cobounded_le_norm (E := ℂ) ‖w‖] with z hz
  exact norm_transform_sub_apply_zero_le hw hz

/-!

## C. Recovering every sample

-/

/-- The inversion formula: the sample at index `m` is the limit at infinity of `z ^ m` times the
transform with its first `m` startup terms removed. -/
theorem tendsto_inversion_cobounded (hw : w ∈ ROC f) (m : ℕ) :
    Tendsto (fun z : ℂ => z ^ m * (transform f z - ∑ n ∈ Finset.range m, seriesTerm f z n))
      (cobounded ℂ) (nhds (f m)) := by
  have hwne : w ≠ 0 := hw.1
  have hadv : w ∈ ROC (advance m f) :=
    ⟨hwne, summable_seriesTerm_advance hwne m hw.2⟩
  have hzero : advance m f 0 = f m := by
    simp [advance]
  have hbase := tendsto_transform_cobounded hadv
  rw [hzero] at hbase
  refine hbase.congr' ?_
  filter_upwards [eventually_cobounded_le_norm (E := ℂ) ‖w‖] with z hz
  have hzne : z ≠ 0 := ne_zero_of_norm_le hwne hz
  have hzmem : z ∈ ROC f := ROC_mem_of_mem_of_norm_le hw hz
  exact transform_advance hzne m hzmem.2

/-!

## D. Uniqueness

-/

/-- Two sequences whose transforms agree on the closed exterior of a circle lying inside both
absolute regions of convergence have the same nonnegative-index samples. -/
theorem eq_natCast_of_transform_eqOn (hf : w ∈ ROC f) (hg : w ∈ ROC g)
    (heq : ∀ z : ℂ, ‖w‖ ≤ ‖z‖ → transform f z = transform g z) (n : ℕ) : f n = g n := by
  induction n using Nat.strong_induction_on with
  | _ m ih =>
    have hlim : Tendsto
        (fun z : ℂ => z ^ m * (transform f z - ∑ n ∈ Finset.range m, seriesTerm f z n))
        (cobounded ℂ) (nhds (g m)) := by
      refine (tendsto_inversion_cobounded hg m).congr' ?_
      filter_upwards [eventually_cobounded_le_norm (E := ℂ) ‖w‖] with z hz
      rw [heq z hz]
      refine congrArg _ (congrArg _ (Finset.sum_congr rfl fun n hn => ?_))
      rw [seriesTerm, seriesTerm, ih n (Finset.mem_range.mp hn)]
    exact tendsto_nhds_unique (tendsto_inversion_cobounded hf m) hlim

/-- Two causal sequences whose transforms agree on the closed exterior of a circle lying inside
both absolute regions of convergence are equal. Causality is required: the unilateral transform
never sees a negative index. -/
theorem eq_of_isCausal_of_transform_eqOn (hcf : IsCausal f) (hcg : IsCausal g) (hf : w ∈ ROC f)
    (hg : w ∈ ROC g) (heq : ∀ z : ℂ, ‖w‖ ≤ ‖z‖ → transform f z = transform g z) : f = g := by
  funext n
  rcases lt_or_ge n 0 with hn | hn
  · rw [hcf n hn, hcg n hn]
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    exact eq_natCast_of_transform_eqOn hf hg heq m

end

end Physlib.ZTransform
