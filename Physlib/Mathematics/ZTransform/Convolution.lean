/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Mathematics.ZTransform.Stability

/-!
# The convolution theorem for the unilateral Z-transform

## i. Overview

The causal convolution defined in `Physlib.Mathematics.ZTransform.Stability` is an infinite sum
over nonnegative lags. When the input is causal that sum is finite at every index: lags beyond
the index reach negative input samples, which vanish. So at a nonnegative index the convolution
is the ordinary Cauchy product of the first samples, and its transform series term is the
corresponding convolution of the two transform series terms.

The convolution theorem then follows from Mathlib's Cauchy product for absolutely convergent
series: where both transforms converge absolutely, the transform of the convolution is the
product of the transforms. Causality is required of the input only. The other sequence, the one
being convolved with, may have nonzero negative-index samples; they are simply never read,
because the convolution sums over nonnegative lags.

The convolution operator is defined in the stability file rather than here, because
bounded-input bounded-output stability cannot be stated without it. This file adds no second
definition.

## ii. Key results

- `Physlib.ZTransform.convolution_natCast`: at a nonnegative index the convolution with a causal
  input is a finite sum.
- `Physlib.ZTransform.convolution_unitImpulse_left`: the unit impulse is a left identity.
- `Physlib.ZTransform.IsCausal.convolution`: a causal input gives a causal convolution.
- `Physlib.ZTransform.seriesTerm_convolution`: the transform series term of a convolution is the
  Cauchy product of the two transform series terms.
- `Physlib.ZTransform.summable_seriesTerm_convolution`: the convolution's transform series
  converges absolutely wherever both factors do.
- `Physlib.ZTransform.transform_convolution`: the convolution theorem.
- `Physlib.ZTransform.mem_ROC_convolution`: the region of convergence of a convolution contains
  the intersection of the two regions.
- `Physlib.ZTransform.convolution_unitImpulse_right`: the response to the unit impulse reads the
  nonnegative-index samples back off the sequence.
- `Physlib.ZTransform.eq_of_isCausal_of_convolution_unitImpulse_eq`: a causal sequence is
  identified by its impulse response.

## iii. Table of contents

- A. The convolution at a nonnegative index
- B. The transform series term of a convolution
- C. The convolution theorem
- D. Identification from the impulse response

## iv. References

`goal.md` section H.4 S5 requires "finite convolution and linear recurrences with initial
conditions". This file supplies the convolution half; the recurrence half is in
`Physlib.Mathematics.ZTransform.DifferenceEquation` and
`Physlib.Mathematics.ZTransform.Existence`.

The Cauchy product for absolutely convergent series is Mathlib's
`tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm`; it is used rather than reproved. A textbook
reference for the convolution theorem itself is A. V. Oppenheim and R. W. Schafer,
*Discrete-Time Signal Processing*, 3rd ed., Pearson, 2010, chapter 3.

The Concordia HVG corpus contains no convolution theorem for the z-transform in any fetched
source, so this file is not a parity claim.

Two things are deliberately not claimed. The convolution is not asserted to be commutative; with
a two-sided left argument and a one-sided sum it is not, and no theorem here says otherwise. And
no claim is made about the convolution at a point where only one of the two transforms
converges.

This file is neutral mathematics and imports no physics.

-/

@[expose] public section

namespace Physlib.ZTransform

noncomputable section

variable {h x : ℤ → ℂ} {z : ℂ}

/-!

## A. The convolution at a nonnegative index

-/

/-- The unit impulse evaluated at a nonnegative index. -/
private lemma unitImpulse_natCast (k : ℕ) :
    unitImpulse ((k : ℕ) : ℤ) = if k = 0 then 1 else 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [unitImpulse]
  · simp [unitImpulse, hk.ne']

/-- A convolution with a causal input is causal. -/
lemma IsCausal.convolution (hx : IsCausal x) (h : ℤ → ℂ) :
    IsCausal (ZTransform.convolution h x) := by
  intro n hn
  have hterm : ∀ k : ℕ, h k * x (n - k) = 0 := fun k => by
    rw [hx _ (by omega), mul_zero]
  show ∑' k : ℕ, h k * x (n - k) = 0
  simp only [hterm, tsum_zero]

/-- At a nonnegative index, a convolution with a causal input is the finite Cauchy sum of the
first samples. -/
lemma convolution_natCast (hx : IsCausal x) (h : ℤ → ℂ) (n : ℕ) :
    convolution h x (n : ℤ) = ∑ k ∈ Finset.range (n + 1), h k * x ((n - k : ℕ) : ℤ) := by
  rw [convolution, tsum_eq_sum (s := Finset.range (n + 1)) fun k hk => ?_]
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hcast : ((n : ℤ) - (k : ℤ)) = ((n - k : ℕ) : ℤ) := by omega
    rw [hcast]
  · have hkn : n < k := Nat.lt_of_succ_le (not_lt.mp (fun hlt =>
      hk (Finset.mem_range.mpr hlt)))
    rw [hx _ (by omega), mul_zero]

/-- The unit impulse is a left identity for the causal convolution. -/
lemma convolution_unitImpulse_left (x : ℤ → ℂ) : convolution unitImpulse x = x := by
  funext n
  show ∑' k : ℕ, unitImpulse k * x (n - k) = x n
  rw [tsum_eq_single 0 fun k hk => by rw [unitImpulse_natCast, if_neg hk, zero_mul],
    unitImpulse_natCast, if_pos rfl, one_mul, Nat.cast_zero, sub_zero]

/-!

## B. The transform series term of a convolution

-/

/-- The transform series term of a convolution with a causal input is the Cauchy product of the
two transform series terms. -/
lemma seriesTerm_convolution (hx : IsCausal x) (h : ℤ → ℂ) (z : ℂ) (n : ℕ) :
    seriesTerm (convolution h x) z n
      = ∑ k ∈ Finset.range (n + 1), seriesTerm h z k * seriesTerm x z (n - k) := by
  rw [seriesTerm, convolution_natCast hx h n, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hpow : z⁻¹ ^ k * z⁻¹ ^ (n - k) = z⁻¹ ^ n := by
    rw [← pow_add]
    congr 1
    omega
  rw [seriesTerm, seriesTerm, ← hpow]
  ring

/-- The transform series of a convolution converges absolutely wherever both factors do. -/
lemma summable_seriesTerm_convolution (hx : IsCausal x) (hh : Summable (seriesTerm h z))
    (hxz : Summable (seriesTerm x z)) : Summable (seriesTerm (convolution h x) z) := by
  have hcauchy : Summable fun n : ℕ =>
      ∑ k ∈ Finset.range (n + 1), seriesTerm h z k * seriesTerm x z (n - k) :=
    (summable_norm_sum_mul_range_of_summable_norm (f := seriesTerm h z) (g := seriesTerm x z)
      (summable_norm_iff.mpr hh) (summable_norm_iff.mpr hxz)).of_norm
  exact hcauchy.congr fun n => (seriesTerm_convolution hx h z n).symm

/-!

## C. The convolution theorem

-/

/-- The convolution theorem: where both transforms converge absolutely, the transform of the
causal convolution is the product of the transforms. Causality is required of the input only. -/
lemma transform_convolution (hx : IsCausal x) (hh : Summable (seriesTerm h z))
    (hxz : Summable (seriesTerm x z)) :
    transform (convolution h x) z = transform h z * transform x z := by
  have hcauchy : (∑' n : ℕ, seriesTerm h z n) * ∑' n : ℕ, seriesTerm x z n
      = ∑' n : ℕ, ∑ k ∈ Finset.range (n + 1), seriesTerm h z k * seriesTerm x z (n - k) :=
    tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm (f := seriesTerm h z) (g := seriesTerm x z)
      (summable_norm_iff.mpr hh) (summable_norm_iff.mpr hxz)
  rw [transform, tsum_congr (seriesTerm_convolution hx h z), ← hcauchy, transform, transform]

/-- The absolute region of convergence of a convolution contains the intersection of the two
absolute regions of convergence. -/
lemma mem_ROC_convolution (hx : IsCausal x) (hh : z ∈ ROC h) (hxz : z ∈ ROC x) :
    z ∈ ROC (convolution h x) :=
  ⟨hh.1, summable_seriesTerm_convolution hx hh.2 hxz.2⟩

/-!

## D. Identification from the impulse response

-/

/-- The response to the unit impulse reads the nonnegative-index samples back off the sequence.
This is the identification direction: a sample is recovered from a response to a known input,
rather than a response being predicted from a sample. -/
lemma convolution_unitImpulse_right (h : ℤ → ℂ) (m : ℕ) :
    convolution h unitImpulse (m : ℤ) = h m := by
  have hzero : ∀ k : ℕ, k ≠ m → h k * unitImpulse ((m : ℤ) - (k : ℤ)) = 0 := by
    intro k hk
    have hne : ((m : ℤ) - (k : ℤ)) ≠ 0 := by omega
    rw [show unitImpulse ((m : ℤ) - (k : ℤ)) = 0 from if_neg hne, mul_zero]
  show ∑' k : ℕ, h k * unitImpulse ((m : ℤ) - (k : ℤ)) = h m
  rw [tsum_eq_single m hzero, sub_self, show unitImpulse (0 : ℤ) = 1 from if_pos rfl, mul_one]

/-- A sequence is determined at every nonnegative index by its impulse response. -/
lemma eq_natCast_of_convolution_unitImpulse_eq {h₁ h₂ : ℤ → ℂ}
    (heq : convolution h₁ unitImpulse = convolution h₂ unitImpulse) (m : ℕ) :
    h₁ m = h₂ m := by
  rw [← convolution_unitImpulse_right h₁ m, ← convolution_unitImpulse_right h₂ m, heq]

/-- Two causal sequences with the same impulse response are equal, so a causal sequence is
identified by its impulse response. -/
lemma eq_of_isCausal_of_convolution_unitImpulse_eq {h₁ h₂ : ℤ → ℂ} (hc₁ : IsCausal h₁)
    (hc₂ : IsCausal h₂) (heq : convolution h₁ unitImpulse = convolution h₂ unitImpulse) :
    h₁ = h₂ := by
  funext n
  rcases lt_or_ge n 0 with hn | hn
  · rw [hc₁ n hn, hc₂ n hn]
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    exact eq_natCast_of_convolution_unitImpulse_eq heq m

end

end Physlib.ZTransform
