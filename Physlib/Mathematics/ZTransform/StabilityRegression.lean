/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Mathematics.ZTransform.OnePoleBIBO

/-!
# Regression tests for stability

## i. Overview

The production one-pole API is exercised at the unstable coefficient `a = 2`: the geometric
solution is not absolutely summable, `1` is not in its region of convergence, and the candidate
pole is exactly `2`. The stable conclusions therefore genuinely depend on the parameter and are
not proved by accident.

The candidate pole set of the one-pole recurrence is computed exactly, as a singleton, and Schur
stability is characterized exactly as the modulus condition on `a`. That pins the direction of
the reciprocal substitution: a system with `a = 2` has its candidate pole at `2` and not at
`1 / 2`, so a reversed convention fails here.

The last example has a two-delay feedback denominator with a repeated reciprocal-coordinate root
at `2`. Its candidate-pole set is exactly `{2⁻¹}`. It is Schur stable, while its feedback
coefficients have total modulus `5 / 4`, which is not less than one. So the sufficient
coefficient criterion of `Physlib.Mathematics.ZTransform.Stability` does not apply to it, and the
criterion is therefore proved to be strictly sufficient rather than necessary.

## ii. Key results

- `Physlib.ZTransform.not_isAbsSummable_geometricSeq_two`: the audited unstable case.
- `Physlib.ZTransform.candidatePoles_twoPole`: the exact nonempty candidate-pole set `{2⁻¹}`.
- `Physlib.ZTransform.isSchurStable_twoPole`: a Schur-stable two-delay feedback denominator.
- `Physlib.ZTransform.not_sum_norm_lt_one_twoPole`: which fails the sufficient criterion, so the
  criterion is not necessary.

## iii. Table of contents

- A. The audited unstable one-pole case
- B. A stable two-pole recurrence that fails the sufficient criterion

## iv. References

Ledger row ZT-10 records that no fetched source contains a Schur-stability or bounded-input
bounded-output theorem, so these regressions check Physlib-original statements and are not parity
claims. The requirement to include an audited unstable parameter case is `goal.md` section I.3,
regression row S-07.

These are algebraic and analytic regressions on complex sequences. No physical, optical, or
signal-processing interpretation is asserted.

-/

@[expose] public section

namespace Physlib.ZTransform

noncomputable section

/-!

## A. The audited unstable one-pole case

-/

/-- The audited unstable case: the geometric sequence with ratio `2` is not absolutely
summable. -/
lemma not_isAbsSummable_geometricSeq_two : ¬ IsAbsSummable (geometricSeq 2) := by
  rw [isAbsSummable_geometricSeq (by norm_num)]
  norm_num

/-- The audited unstable case: `1` is not in the region of convergence. -/
lemma one_notMem_ROC_geometricSeq_two : (1 : ℂ) ∉ ROC (geometricSeq 2) := by
  rw [ROC_geometricSeq (by norm_num)]
  norm_num

/-- The audited unstable case: the one-pole recurrence with coefficient `2` is not Schur
stable. -/
lemma not_isSchurStable_onePole_two : ¬ IsSchurStable {1} (onePoleFeedback 2) := by
  rw [isSchurStable_onePole_iff (by norm_num)]
  norm_num

/-- The audited unstable case: the candidate pole is at `2` and not at its reciprocal. -/
lemma candidatePoles_onePole_two : candidatePoles {1} (onePoleFeedback 2) = {(2 : ℂ)} :=
  candidatePoles_onePole (by norm_num)

/-!

## B. A stable two-pole recurrence that fails the sufficient criterion

-/

/-- Feedback coefficients whose denominator has a repeated reciprocal-coordinate root at `2`. -/
def twoPoleFeedback : ℕ → ℂ := fun k => if k = 1 then 1 else if k = 2 then -(1 / 4) else 0

/-- The feedback coefficient at lag one. -/
lemma twoPoleFeedback_one : twoPoleFeedback 1 = 1 := if_pos rfl

/-- The feedback coefficient at lag two. -/
lemma twoPoleFeedback_two : twoPoleFeedback 2 = -(1 / 4) := by
  rw [twoPoleFeedback, if_neg (by decide : ¬(2 : ℕ) = 1), if_pos rfl]

/-- The denominator symbol of the two-pole recurrence is a perfect square. -/
lemma delaySymbol_twoPoleFeedback (u : ℂ) :
    1 - delaySymbol {1, 2} twoPoleFeedback u = (u - 2) ^ 2 / 4 := by
  rw [delaySymbol, Finset.sum_insert (by decide), Finset.sum_singleton, twoPoleFeedback_one,
    twoPoleFeedback_two, pow_one]
  ring

/-- The candidate-pole set of the two-delay feedback denominator is exactly the nonempty
singleton `{2⁻¹}`. -/
lemma candidatePoles_twoPole : candidatePoles {1, 2} twoPoleFeedback = {(2 : ℂ)⁻¹} := by
  ext z
  simp only [candidatePoles, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨-, hzero⟩
    rw [delaySymbol_twoPoleFeedback] at hzero
    have hsq : (z⁻¹ - 2) ^ 2 = 0 := by linear_combination 4 * hzero
    have hz : z⁻¹ = 2 := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
      linear_combination this
    rw [← hz, inv_inv]
  · rintro rfl
    refine ⟨by norm_num, ?_⟩
    rw [delaySymbol_twoPoleFeedback]
    norm_num

/-- The two-delay feedback denominator is Schur stable: its candidate-pole set is `{2⁻¹}`. -/
lemma isSchurStable_twoPole : IsSchurStable {1, 2} twoPoleFeedback := by
  rw [IsSchurStable, candidatePoles_twoPole]
  intro z hz
  rw [Set.mem_singleton_iff.mp hz, norm_inv]
  norm_num

/-- The two-pole recurrence fails the sufficient coefficient criterion, whose hypothesis is a
total feedback modulus below one: here the total is `5 / 4`. -/
lemma not_sum_norm_lt_one_twoPole :
    ¬ (∑ k ∈ ({1, 2} : Finset ℕ), ‖twoPoleFeedback k‖) < 1 := by
  rw [Finset.sum_insert (by decide), Finset.sum_singleton, twoPoleFeedback_one,
    twoPoleFeedback_two]
  norm_num

end

end Physlib.ZTransform
