/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Causal sequences and the unilateral Z-transform

## i. Overview

This file develops the unilateral Z-transform of a two-sided complex sequence `f : ℤ → ℂ` as
the analytic series `∑' n : ℕ, f n * z⁻¹ ^ n`. Only the nonnegative-index samples enter the
series, so the transform is unilateral even though the sequence itself is two-sided. Keeping the
negative indices in the domain is what allows the delay and advance laws below to be stated
without silently discarding startup data: the advance law produces an explicit finite startup
sum, and the delay law is stated under an explicit causality hypothesis rather than assumed.

Two regions of convergence are defined and deliberately kept apart. `ROC f` is the set of nonzero
`z` at which the term sequence is `Summable`, which for a complex-valued series is absolute
convergence. `condROC f` is the set of nonzero `z` at which the sequence of partial sums over
`Finset.range N` converges. Absolute convergence implies conditional convergence; the reverse
inclusion is not proved here because it is false, and a counterexample is supplied separately.

The transform value `transform f z` is Mathlib's `tsum`, so it is the unconditional sum and is
`0` by convention outside `ROC f`. Every theorem that computes a transform therefore carries the
summability hypothesis it needs, and no theorem in this file asserts a value at a point of
`condROC f \ ROC f`.

## ii. Key results

- `Physlib.ZTransform.IsCausal`: a two-sided sequence vanishes at every negative index.
- `Physlib.ZTransform.seriesTerm`: the `n`-th term `f n * z⁻¹ ^ n` of the transform series.
- `Physlib.ZTransform.ROC`: the absolute region of convergence.
- `Physlib.ZTransform.condROC`: the conditional region of convergence.
- `Physlib.ZTransform.ROC_subset_condROC`: absolute convergence implies conditional convergence.
- `Physlib.ZTransform.summable_norm_seriesTerm_iff`: membership of `ROC` is absolute convergence.
- `Physlib.ZTransform.transform`: the unilateral Z-transform.
- `Physlib.ZTransform.transform_add`, `Physlib.ZTransform.transform_const_mul`: linearity.
- `Physlib.ZTransform.transform_delay`: the right-shift law
  `z⁻¹ ^ m * transform f z` for a causal sequence.
- `Physlib.ZTransform.advanceStartup`: the finite startup contribution removed by an advance.
- `Physlib.ZTransform.transform_advance`: the left-shift law with its explicit startup sum.
- `Physlib.ZTransform.transform_firstDifference`: the first-difference law `(1 - z⁻¹)`.
- `Physlib.ZTransform.transform_zScale`: scaling in the `z` domain.
- `Physlib.ZTransform.transform_unitImpulse`: the unit impulse transforms to `1`.

## iii. Table of contents

- A. Causal two-sided sequences
- B. The unilateral Z-transform series
- C. Absolute and conditional regions of convergence
- D. Linearity
- E. Delay and advance
- F. The first difference
- G. Scaling in the z-domain
- H. The unit impulse

## iv. References

The transform, region, right-shift, first-difference, and scaling statements follow U. Siddique,
M. Y. Mahmoud, and S. Tahar, "On the Formalization of Z-Transform in HOL", ITP 2014,
LNCS 8558, pp. 483-498: Definitions 8-9 and Theorems 2-3 (p. 488), Theorem 6 (p. 490),
Theorem 7 (p. 490), and Theorems 8-9 (p. 491).

Linearity and the left-shift law follow the corrected journal version instead, U. Siddique,
M. Y. Mahmoud, and S. Tahar, "Formal Analysis of Discrete-Time Systems using z-Transform",
Journal of Applied Logics 5(4), 2018, pp. 875-906, Theorems 4-5 (pp. 884-885). ITP 2014
Theorem 4 prints the first coefficient on both input terms while using a distinct second
coefficient in the result. Its equation (5) and Theorem 5 also place the startup sum outside the
`z ^ m` factor. The latter form is false: at the unit impulse and `m = 1` it gives `z - 1`, while
the advanced unit impulse has transform `0`. The journal statement keeps `z ^ m` in front of the
startup sum, and the companion regression obtains `0` at that same point.

The unit impulse and its transform also follow the journal version, Definition 14 and Theorem 12
(p. 888).

Two deliberate departures from both sources are recorded here. First, both expressly choose
ordered convergence of the natural partial sums for their region of convergence, rather than
absolute convergence. `condROC` is the corresponding Physlib notion, with the nonzero condition
used by the journal version; `ROC` uses Mathlib's unconditional `Summable` and is the stronger
absolute region. The algebraic laws below are proved on that stronger region. Second, the sources
index sequences so that causality is a side condition on a one-sided index set, while this file
uses a two-sided index set and states causality as `IsCausal`.

A textbook reference for the same statement list is A. V. Oppenheim and R. W. Schafer,
*Discrete-Time Signal Processing*, 3rd ed., Pearson, 2010, chapter 3.

Nothing here is claimed about inverse transforms, uniqueness, stability, or any physical or
optical interpretation. This file is neutral mathematics: it imports no physics.

-/

@[expose] public section

namespace Physlib.ZTransform

noncomputable section

/-!

## A. Causal two-sided sequences

-/

/-- A two-sided complex sequence is causal when it vanishes at every negative index. -/
def IsCausal (f : ℤ → ℂ) : Prop := ∀ n : ℤ, n < 0 → f n = 0

/-- A causal sequence vanishes at every negative index. -/
lemma IsCausal.apply_of_neg {f : ℤ → ℂ} (hf : IsCausal f) {n : ℤ} (hn : n < 0) : f n = 0 :=
  hf n hn

/-- The zero sequence is causal. -/
lemma isCausal_zero : IsCausal (0 : ℤ → ℂ) := fun _ _ => rfl

/-- A sum of causal sequences is causal. -/
lemma IsCausal.add {f g : ℤ → ℂ} (hf : IsCausal f) (hg : IsCausal g) : IsCausal (f + g) :=
  fun n hn => by simp [Pi.add_apply, hf n hn, hg n hn]

/-- A scalar multiple of a causal sequence is causal. -/
lemma IsCausal.const_mul {f : ℤ → ℂ} (hf : IsCausal f) (c : ℂ) :
    IsCausal (fun n => c * f n) := fun n hn => by simp [hf n hn]

/-- The zero extension of a one-sided sequence to a two-sided sequence. -/
def zeroExtend (a : ℕ → ℂ) : ℤ → ℂ := fun n => if 0 ≤ n then a n.toNat else 0

/-- A zero extension is causal. -/
lemma zeroExtend_isCausal (a : ℕ → ℂ) : IsCausal (zeroExtend a) := by
  intro n hn
  simp [zeroExtend, not_le.mpr hn]

/-- A zero extension agrees with the original sequence at every nonnegative index. -/
@[simp]
lemma zeroExtend_natCast (a : ℕ → ℂ) (n : ℕ) : zeroExtend a (n : ℤ) = a n := by
  simp [zeroExtend]

/-!

## B. The unilateral Z-transform series

-/

/-- The `n`-th term of the unilateral Z-transform series of `f` at `z`. -/
def seriesTerm (f : ℤ → ℂ) (z : ℂ) (n : ℕ) : ℂ := f n * z⁻¹ ^ n

/-- The transform series term written with a negative integer power. -/
lemma seriesTerm_eq_zpow (f : ℤ → ℂ) (z : ℂ) (n : ℕ) :
    seriesTerm f z n = f n * z ^ (-(n : ℤ)) := by
  rw [seriesTerm, zpow_neg, zpow_natCast, ← inv_pow]

/-- The unilateral Z-transform of a two-sided complex sequence. -/
def transform (f : ℤ → ℂ) (z : ℂ) : ℂ := ∑' n : ℕ, seriesTerm f z n

/-- The transform is the unconditional sum of its series terms. -/
lemma transform_eq_tsum (f : ℤ → ℂ) (z : ℂ) :
    transform f z = ∑' n : ℕ, f n * z⁻¹ ^ n := rfl

/-- The zero sequence has zero transform. -/
@[simp]
lemma transform_zero (z : ℂ) : transform 0 z = 0 := by
  simp [transform, seriesTerm]

/-!

## C. Absolute and conditional regions of convergence

-/

/-- The absolute region of convergence: the nonzero points at which the transform series is
summable. Summability of a complex-valued family is absolute convergence. -/
def ROC (f : ℤ → ℂ) : Set ℂ := {z : ℂ | z ≠ 0 ∧ Summable (seriesTerm f z)}

/-- The conditional region of convergence: the nonzero points at which the partial sums of the
transform series converge. -/
def condROC (f : ℤ → ℂ) : Set ℂ :=
  {z : ℂ | z ≠ 0 ∧ ∃ S : ℂ,
    Filter.Tendsto (fun N => ∑ n ∈ Finset.range N, seriesTerm f z n) Filter.atTop (nhds S)}

/-- Membership of the absolute region of convergence, unfolded. -/
lemma mem_ROC_iff {f : ℤ → ℂ} {z : ℂ} :
    z ∈ ROC f ↔ z ≠ 0 ∧ Summable (seriesTerm f z) := Iff.rfl

/-- Membership of the conditional region of convergence, unfolded. -/
lemma mem_condROC_iff {f : ℤ → ℂ} {z : ℂ} :
    z ∈ condROC f ↔ z ≠ 0 ∧ ∃ S : ℂ,
      Filter.Tendsto (fun N => ∑ n ∈ Finset.range N, seriesTerm f z n) Filter.atTop (nhds S) :=
  Iff.rfl

/-- The origin belongs to neither region of convergence. -/
@[simp]
lemma zero_notMem_ROC (f : ℤ → ℂ) : (0 : ℂ) ∉ ROC f := by
  simp [ROC]

/-- Summability of the transform series is equivalent to summability of its norms, so membership
of `ROC` is absolute convergence. -/
lemma summable_norm_seriesTerm_iff {f : ℤ → ℂ} {z : ℂ} :
    (Summable fun n : ℕ => ‖seriesTerm f z n‖) ↔ Summable (seriesTerm f z) :=
  summable_norm_iff

/-- Absolute convergence implies conditional convergence, so the absolute region of convergence is
contained in the conditional one. -/
lemma ROC_subset_condROC (f : ℤ → ℂ) : ROC f ⊆ condROC f := by
  rintro z ⟨hz, hs⟩
  exact ⟨hz, _, hs.hasSum.tendsto_sum_nat⟩

/-- On the absolute region of convergence the partial sums converge to the transform. -/
lemma tendsto_sum_range_transform {f : ℤ → ℂ} {z : ℂ} (hz : z ∈ ROC f) :
    Filter.Tendsto (fun N => ∑ n ∈ Finset.range N, seriesTerm f z n) Filter.atTop
      (nhds (transform f z)) :=
  hz.2.hasSum.tendsto_sum_nat

/-!

## D. Linearity

-/

/-- The transform series of a sum splits. -/
lemma seriesTerm_add (f g : ℤ → ℂ) (z : ℂ) :
    seriesTerm (f + g) z = seriesTerm f z + seriesTerm g z := by
  funext n
  simp [seriesTerm, Pi.add_apply, add_mul]

/-- The transform series of a scalar multiple. -/
lemma seriesTerm_const_mul (c : ℂ) (f : ℤ → ℂ) (z : ℂ) :
    seriesTerm (fun n => c * f n) z = fun n => c * seriesTerm f z n := by
  funext n
  simp [seriesTerm, mul_assoc]

/-- The transform series of a negation. -/
lemma seriesTerm_neg (f : ℤ → ℂ) (z : ℂ) :
    seriesTerm (-f) z = -seriesTerm f z := by
  funext n
  simp [seriesTerm, Pi.neg_apply, neg_mul]

/-- The transform series of a difference splits. -/
lemma seriesTerm_sub (f g : ℤ → ℂ) (z : ℂ) :
    seriesTerm (f - g) z = seriesTerm f z - seriesTerm g z := by
  funext n
  simp [seriesTerm, Pi.sub_apply, sub_mul]

/-- Summability of the transform series of a sum, from summability of the summands. -/
lemma summable_seriesTerm_add {f g : ℤ → ℂ} {z : ℂ} (hf : Summable (seriesTerm f z))
    (hg : Summable (seriesTerm g z)) : Summable (seriesTerm (f + g) z) := by
  rw [seriesTerm_add]
  exact hf.add hg

/-- Summability of the transform series of a scalar multiple. -/
lemma summable_seriesTerm_const_mul {f : ℤ → ℂ} {z : ℂ} (c : ℂ)
    (hf : Summable (seriesTerm f z)) : Summable (seriesTerm (fun n => c * f n) z) := by
  rw [seriesTerm_const_mul]
  exact hf.mul_left c

/-- Summability of the transform series of a difference. -/
lemma summable_seriesTerm_sub {f g : ℤ → ℂ} {z : ℂ} (hf : Summable (seriesTerm f z))
    (hg : Summable (seriesTerm g z)) : Summable (seriesTerm (f - g) z) := by
  rw [seriesTerm_sub]
  exact hf.sub hg

/-- The transform is additive where both summands converge absolutely. -/
lemma transform_add {f g : ℤ → ℂ} {z : ℂ} (hf : Summable (seriesTerm f z))
    (hg : Summable (seriesTerm g z)) :
    transform (f + g) z = transform f z + transform g z := by
  rw [transform, transform, transform, seriesTerm_add]
  exact hf.tsum_add hg

/-- The transform is homogeneous, with no convergence hypothesis. -/
lemma transform_const_mul (c : ℂ) (f : ℤ → ℂ) (z : ℂ) :
    transform (fun n => c * f n) z = c * transform f z := by
  rw [transform, transform, seriesTerm_const_mul]
  exact tsum_mul_left

/-- The transform of a negation. -/
lemma transform_neg (f : ℤ → ℂ) (z : ℂ) : transform (-f) z = -transform f z := by
  rw [transform, transform, seriesTerm_neg]
  exact tsum_neg

/-- The transform of a difference, where both terms converge absolutely. -/
lemma transform_sub {f g : ℤ → ℂ} {z : ℂ} (hf : Summable (seriesTerm f z))
    (hg : Summable (seriesTerm g z)) :
    transform (f - g) z = transform f z - transform g z := by
  rw [transform, transform, transform, seriesTerm_sub]
  exact hf.tsum_sub hg

/-- The absolute region of convergence of a sum contains the intersection of the two regions. -/
lemma inter_ROC_subset_ROC_add (f g : ℤ → ℂ) : ROC f ∩ ROC g ⊆ ROC (f + g) := by
  rintro z ⟨⟨hz, hf⟩, -, hg⟩
  exact ⟨hz, summable_seriesTerm_add hf hg⟩

/-- Multiplying a sequence by a nonzero constant does not change its absolute region of
convergence. -/
lemma ROC_const_mul {c : ℂ} (hc : c ≠ 0) (f : ℤ → ℂ) :
    ROC (fun n => c * f n) = ROC f := by
  ext z
  refine and_congr_right fun _ => ⟨fun h => ?_, fun h => summable_seriesTerm_const_mul c h⟩
  refine (h.mul_left c⁻¹).congr fun n => ?_
  simp only [seriesTerm]
  rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

/-!

## E. Delay and advance

-/

/-- The right shift, or time delay, of a sequence by `m` samples. -/
def delay (m : ℕ) (f : ℤ → ℂ) : ℤ → ℂ := fun n => f (n - m)

/-- The left shift, or time advance, of a sequence by `m` samples. -/
def advance (m : ℕ) (f : ℤ → ℂ) : ℤ → ℂ := fun n => f (n + m)

/-- The finite startup contribution removed before advancing a unilateral transform. -/
def advanceStartup (f : ℤ → ℂ) (z : ℂ) (m : ℕ) : ℂ :=
  ∑ n ∈ Finset.range m, seriesTerm f z n

/-- Delaying a causal sequence keeps it causal. -/
lemma IsCausal.delay {f : ℤ → ℂ} (hf : IsCausal f) (m : ℕ) : IsCausal (delay m f) := by
  intro n hn
  exact hf _ (by omega)

/-- The delayed transform series term at an index at least `m` is a shifted term. -/
lemma seriesTerm_delay_add (f : ℤ → ℂ) (z : ℂ) (m n : ℕ) :
    seriesTerm (delay m f) z (n + m) = z⁻¹ ^ m * seriesTerm f z n := by
  simp only [seriesTerm, delay, Nat.cast_add, add_sub_cancel_right, pow_add]
  ring

/-- The delayed transform series term of a causal sequence vanishes below index `m`. -/
lemma seriesTerm_delay_of_lt {f : ℤ → ℂ} (hf : IsCausal f) (z : ℂ) {m n : ℕ}
    (hn : n < m) : seriesTerm (delay m f) z n = 0 := by
  have hneg : ((n : ℤ) - (m : ℤ)) < 0 := by omega
  simp [seriesTerm, delay, hf _ hneg]

/-- Delaying a sequence preserves summability of the transform series. -/
lemma summable_seriesTerm_delay {f : ℤ → ℂ} {z : ℂ} (m : ℕ)
    (hf : Summable (seriesTerm f z)) : Summable (seriesTerm (delay m f) z) := by
  refine (summable_nat_add_iff (f := seriesTerm (delay m f) z) m).mp ?_
  refine (hf.mul_left (z⁻¹ ^ m)).congr fun n => ?_
  rw [seriesTerm_delay_add]

/-- The right-shift, or time-delay, law: delaying a causal sequence by `m` samples multiplies its
transform by `z⁻¹ ^ m`. -/
lemma transform_delay {f : ℤ → ℂ} {z : ℂ} (hf : IsCausal f) (m : ℕ)
    (hs : Summable (seriesTerm f z)) :
    transform (delay m f) z = z⁻¹ ^ m * transform f z := by
  have hd : Summable (seriesTerm (delay m f) z) := summable_seriesTerm_delay m hs
  have hsplit := hd.sum_add_tsum_nat_add (f := seriesTerm (delay m f) z) m
  have hzero : ∑ n ∈ Finset.range m, seriesTerm (delay m f) z n = 0 :=
    Finset.sum_eq_zero fun n hn => seriesTerm_delay_of_lt hf z (Finset.mem_range.mp hn)
  have hshift : ∑' n : ℕ, seriesTerm (delay m f) z (n + m) = z⁻¹ ^ m * transform f z := by
    rw [transform, ← tsum_mul_left]
    exact tsum_congr fun n => seriesTerm_delay_add f z m n
  rw [transform, ← hsplit, hzero, hshift, zero_add]

/-- The advanced transform series term is a shifted term rescaled by `z ^ m`. -/
lemma seriesTerm_advance_eq {f : ℤ → ℂ} {z : ℂ} (hz : z ≠ 0) (m n : ℕ) :
    z ^ m * seriesTerm f z (n + m) = seriesTerm (advance m f) z n := by
  have hpow : z ^ m * z⁻¹ ^ m = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hz, one_pow]
  simp only [seriesTerm, advance, Nat.cast_add, pow_add]
  linear_combination (f ((n : ℤ) + (m : ℤ)) * z⁻¹ ^ n) * hpow

/-- Advancing a sequence by `m` samples preserves summability of the transform series away from
the origin. -/
lemma summable_seriesTerm_advance {f : ℤ → ℂ} {z : ℂ} (hz : z ≠ 0) (m : ℕ)
    (hf : Summable (seriesTerm f z)) : Summable (seriesTerm (advance m f) z) := by
  have hshift : Summable (fun n : ℕ => seriesTerm f z (n + m)) :=
    (summable_nat_add_iff (f := seriesTerm f z) m).mpr hf
  exact (hshift.mul_left (z ^ m)).congr fun n => seriesTerm_advance_eq hz m n

/-- The left-shift, or time-advance, law: advancing a sequence by `m` samples multiplies its
transform by `z ^ m` after removing the explicit startup sum of the first `m` samples. -/
lemma transform_advance {f : ℤ → ℂ} {z : ℂ} (hz : z ≠ 0) (m : ℕ)
    (hs : Summable (seriesTerm f z)) :
    transform (advance m f) z =
      z ^ m * (transform f z - advanceStartup f z m) := by
  have hsplit := hs.sum_add_tsum_nat_add (f := seriesTerm f z) m
  have hpowinv : z⁻¹ ^ m * z ^ m = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hz, one_pow]
  have hshift : ∑' n : ℕ, seriesTerm f z (n + m) = z⁻¹ ^ m * transform (advance m f) z := by
    rw [transform, ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    rw [← seriesTerm_advance_eq hz m n, ← mul_assoc, hpowinv, one_mul]
  have hpow : z ^ m * z⁻¹ ^ m = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hz, one_pow]
  have hrec : transform f z - advanceStartup f z m =
      z⁻¹ ^ m * transform (advance m f) z := by
    rw [advanceStartup, ← hshift, transform, ← hsplit]
    ring
  rw [hrec, ← mul_assoc, hpow, one_mul]

/-!

## F. The first difference

-/

/-- The first difference of a sequence. -/
def firstDifference (f : ℤ → ℂ) : ℤ → ℂ := f - delay 1 f

/-- The first difference evaluated at an index. -/
lemma firstDifference_apply (f : ℤ → ℂ) (n : ℤ) :
    firstDifference f n = f n - f (n - 1) := by
  simp [firstDifference, delay]

/-- The first-difference law: the transform of the first difference of a causal sequence is
`(1 - z⁻¹)` times its transform. -/
lemma transform_firstDifference {f : ℤ → ℂ} {z : ℂ} (hf : IsCausal f)
    (hs : Summable (seriesTerm f z)) :
    transform (firstDifference f) z = (1 - z⁻¹) * transform f z := by
  have hd : Summable (seriesTerm (delay 1 f) z) := summable_seriesTerm_delay 1 hs
  rw [firstDifference, transform_sub hs hd, transform_delay hf 1 hs, pow_one]
  ring

/-!

## G. Scaling in the z-domain

-/

/-- Multiplication of a sequence by the geometric factor `a ^ n`. -/
def zScale (a : ℂ) (f : ℤ → ℂ) : ℤ → ℂ := fun n => a ^ n * f n

/-- Scaling a causal sequence keeps it causal. -/
lemma IsCausal.zScale {f : ℤ → ℂ} (hf : IsCausal f) (a : ℂ) : IsCausal (zScale a f) := by
  intro n hn
  simp [ZTransform.zScale, hf n hn]

/-- The transform series of a geometrically scaled sequence at `z` is the original series at
`z / a`. This holds with no hypothesis on `a` or `z`. -/
lemma seriesTerm_zScale (a : ℂ) (f : ℤ → ℂ) (z : ℂ) :
    seriesTerm (zScale a f) z = seriesTerm f (z / a) := by
  have hinv : (z / a)⁻¹ = a * z⁻¹ := by
    rw [div_eq_mul_inv, mul_inv_rev, inv_inv]
  funext n
  simp only [seriesTerm, ZTransform.zScale, hinv, zpow_natCast, mul_pow]
  ring

/-- Scaling in the `z` domain: multiplying a sequence by `a ^ n` replaces `z` by `z / a` in its
transform. -/
lemma transform_zScale (a : ℂ) (f : ℤ → ℂ) (z : ℂ) :
    transform (zScale a f) z = transform f (z / a) := by
  rw [transform, transform, seriesTerm_zScale]

/-- Scaling in the `z` domain transports the absolute region of convergence by division. -/
lemma ROC_zScale {a : ℂ} (ha : a ≠ 0) (f : ℤ → ℂ) :
    ROC (zScale a f) = (fun z => z / a) ⁻¹' ROC f := by
  ext z
  constructor
  · rintro ⟨hz, hs⟩
    rw [seriesTerm_zScale] at hs
    exact ⟨div_ne_zero hz ha, hs⟩
  · rintro ⟨hz, hs⟩
    refine ⟨fun h => hz (by simp [h]), ?_⟩
    rw [seriesTerm_zScale]
    exact hs

/-!

## H. The unit impulse

-/

/-- The unit impulse, or Kronecker delta, sequence. -/
def unitImpulse : ℤ → ℂ := fun n => if n = 0 then 1 else 0

/-- The unit impulse is causal. -/
lemma unitImpulse_isCausal : IsCausal unitImpulse := by
  intro n hn
  simp [unitImpulse, hn.ne]

/-- The transform series term of the unit impulse selects the index zero. -/
@[simp]
lemma seriesTerm_unitImpulse (z : ℂ) (n : ℕ) :
    seriesTerm unitImpulse z n = if n = 0 then 1 else 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [seriesTerm, unitImpulse]
  · have hne : ((n : ℤ)) ≠ 0 := by omega
    simp [seriesTerm, unitImpulse, hn.ne']

/-- The transform series of the unit impulse is summable at every point. -/
lemma summable_seriesTerm_unitImpulse (z : ℂ) : Summable (seriesTerm unitImpulse z) := by
  refine summable_of_ne_finset_zero (s := ({0} : Finset ℕ)) fun n hn => ?_
  rw [Finset.mem_singleton] at hn
  simp [seriesTerm_unitImpulse, hn]

/-- The unit impulse transforms to `1`. -/
@[simp]
lemma transform_unitImpulse (z : ℂ) : transform unitImpulse z = 1 := by
  rw [transform]
  simp only [seriesTerm_unitImpulse]
  rw [tsum_eq_single 0 (fun n hn => by simp [hn])]
  simp

/-- The absolute region of convergence of the unit impulse is the punctured plane. -/
lemma ROC_unitImpulse : ROC unitImpulse = {z : ℂ | z ≠ 0} := by
  ext z
  exact ⟨fun h => h.1, fun h => ⟨h, summable_seriesTerm_unitImpulse z⟩⟩

/-- A delayed unit impulse transforms to `z⁻¹ ^ m`. -/
lemma transform_delay_unitImpulse (m : ℕ) (z : ℂ) :
    transform (delay m unitImpulse) z = z⁻¹ ^ m := by
  rw [transform_delay unitImpulse_isCausal m (summable_seriesTerm_unitImpulse z),
    transform_unitImpulse, mul_one]

end

end Physlib.ZTransform
