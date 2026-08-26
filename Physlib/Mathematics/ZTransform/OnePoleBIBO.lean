/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Mathematics.ZTransform.Convolution
public import Physlib.Mathematics.ZTransform.OnePole

/-!
# BIBO stability of one-pole systems

## i. Overview

This file proves the exact bounded-input bounded-output criterion for the causal geometric impulse
response. Ratios outside the unit circle are rejected by the bounded unit impulse. On the unit
circle, the geometric sequence itself is a bounded input whose self-convolution grows linearly.
Together with the absolute-region-of-convergence result, these witnesses prove that BIBO stability
is exactly `‖a‖ < 1` and hence agrees with the one-pole Schur condition.

## ii. Key results

- `not_isBIBOStable_geometricSeq_of_one_lt_norm`: the outside-disk witness.
- `norm_convolution_geometricSeq_self`: exact linear growth on the boundary.
- `not_isBIBOStable_geometricSeq_of_norm_eq_one`: the boundary witness.
- `isBIBOStable_geometricSeq_iff`: the exact BIBO criterion.
- `isBIBOStable_geometricSeq_iff_isSchurStable_onePole`: the Schur bridge.

## iii. Table of contents

- A. Explicit unstable witnesses
- B. Exact one-pole equivalences

## iv. References and non-claims

These are neutral results about complex sequences and the unilateral Z-transform. They do not
assert optical passivity, physical resonance, network reachability, or stability for a general
proper rational transfer function. The definitions of bounded sequences, causal convolution, and
BIBO stability are reused from `Physlib/Mathematics/ZTransform/Stability.lean`; the finite-sum
convolution identities are reused from `Convolution.lean`.
-/

@[expose] public section

namespace Physlib.ZTransform

noncomputable section

/-!

## A. Explicit unstable witnesses

-/

/-- The unit impulse is a bounded input sequence. -/
lemma isBoundedSeq_unitImpulse : IsBoundedSeq unitImpulse := by
  refine ⟨1, fun n => ?_⟩
  by_cases hn : n = 0
  · simp [unitImpulse, hn]
  · simp [unitImpulse, hn]

/-- A causal geometric sequence is bounded when its ratio has modulus at most one. -/
lemma isBoundedSeq_geometricSeq_of_norm_le_one {a : ℂ} (ha : ‖a‖ ≤ 1) :
    IsBoundedSeq (geometricSeq a) := by
  refine ⟨1, fun n => ?_⟩
  by_cases hn : n < 0
  · rw [geometricSeq_isCausal a n hn, norm_zero]
    exact zero_le_one
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_not_gt hn)
    rw [geometricSeq_natCast, norm_pow]
    exact pow_le_one₀ (norm_nonneg a) ha

/-- Outside the unit circle, the geometric impulse response is not BIBO stable. -/
lemma not_isBIBOStable_geometricSeq_of_one_lt_norm {a : ℂ} (ha : 1 < ‖a‖) :
    ¬ IsBIBOStable (geometricSeq a) := by
  intro hStable
  obtain ⟨bound, hBound⟩ := hStable unitImpulse isBoundedSeq_unitImpulse
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt bound ha
  have hAtN := hBound (n : ℤ)
  rw [convolution_unitImpulse_right, geometricSeq_natCast, norm_pow] at hAtN
  exact (not_le_of_gt hn) hAtN

/-- On the unit-circle boundary, self-convolution grows linearly in sample number. -/
lemma norm_convolution_geometricSeq_self {a : ℂ} (ha : ‖a‖ = 1) (n : ℕ) :
    ‖convolution (geometricSeq a) (geometricSeq a) (n : ℤ)‖ = n + 1 := by
  rw [convolution_natCast (geometricSeq_isCausal a)]
  have hSummand :
      (∑ k ∈ Finset.range (n + 1),
          geometricSeq a (k : ℤ) * geometricSeq a ((n - k : ℕ) : ℤ)) =
        ∑ _k ∈ Finset.range (n + 1), a ^ n := by
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [geometricSeq_natCast]
    rw [← pow_add, Nat.add_sub_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))]
  rw [hSummand]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, norm_mul, norm_pow,
    ha, one_pow, mul_one]
  simpa only [Nat.cast_add, Nat.cast_one] using Complex.norm_natCast (n + 1)

/-- A geometric impulse response on the unit-circle boundary is not BIBO stable. -/
lemma not_isBIBOStable_geometricSeq_of_norm_eq_one {a : ℂ} (ha : ‖a‖ = 1) :
    ¬ IsBIBOStable (geometricSeq a) := by
  intro hStable
  have hInput : IsBoundedSeq (geometricSeq a) :=
    isBoundedSeq_geometricSeq_of_norm_le_one ha.le
  obtain ⟨bound, hBound⟩ := hStable (geometricSeq a) hInput
  obtain ⟨n, hn⟩ := exists_nat_gt bound
  have hAtN := hBound (n : ℤ)
  rw [norm_convolution_geometricSeq_self ha] at hAtN
  linarith

/-- BIBO stability of a causal geometric response forces its ratio inside the unit disk. -/
lemma norm_lt_one_of_isBIBOStable_geometricSeq {a : ℂ}
    (hStable : IsBIBOStable (geometricSeq a)) : ‖a‖ < 1 := by
  by_contra hNot
  have hAtLeast : 1 ≤ ‖a‖ := le_of_not_gt hNot
  rcases hAtLeast.eq_or_lt with hBoundary | hOutside
  · exact not_isBIBOStable_geometricSeq_of_norm_eq_one hBoundary.symm hStable
  · exact not_isBIBOStable_geometricSeq_of_one_lt_norm hOutside hStable

/-!

## B. Exact one-pole equivalences

-/

/-- A nonzero stable one-pole coefficient gives a BIBO-stable geometric response. -/
lemma isBIBOStable_geometricSeq {a : ℂ} (ha : a ≠ 0) (h : ‖a‖ < 1) :
    IsBIBOStable (geometricSeq a) :=
  isBIBOStable_of_sphere_subset_ROC _ (sphere_subset_ROC_geometricSeq ha h)

/-- For a nonzero one-pole response, BIBO stability is exactly the strict pole condition. -/
lemma isBIBOStable_geometricSeq_iff {a : ℂ} (ha : a ≠ 0) :
    IsBIBOStable (geometricSeq a) ↔ ‖a‖ < 1 :=
  ⟨norm_lt_one_of_isBIBOStable_geometricSeq, isBIBOStable_geometricSeq ha⟩

/-- For a nonzero one-pole response, BIBO and Schur stability are equivalent. -/
lemma isBIBOStable_geometricSeq_iff_isSchurStable_onePole {a : ℂ} (ha : a ≠ 0) :
    IsBIBOStable (geometricSeq a) ↔ IsSchurStable {1} (onePoleFeedback a) := by
  rw [isBIBOStable_geometricSeq_iff ha, isSchurStable_onePole_iff ha]

/-- For a nonzero one-pole response, absolute summability and BIBO stability are equivalent. -/
lemma isAbsSummable_geometricSeq_iff_isBIBOStable {a : ℂ} (ha : a ≠ 0) :
    IsAbsSummable (geometricSeq a) ↔ IsBIBOStable (geometricSeq a) := by
  rw [isAbsSummable_geometricSeq ha, isBIBOStable_geometricSeq_iff ha]

end

end Physlib.ZTransform
