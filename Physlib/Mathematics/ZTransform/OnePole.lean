/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Mathematics.ZTransform.Stability

/-!
# One-pole Z-transform systems

## i. Overview

This file supplies a production API for the lag-one recurrence with feedback coefficient `a`.
Its denominator has the single candidate pole `z = a` when `a` is nonzero, so Schur stability
is exactly `‖a‖ < 1`. The associated causal geometric sequence is absolutely summable exactly
under the same strict inequality, and that condition puts the unit circle in its region of
convergence.

## ii. Key definitions and results

- `onePoleFeedbackCoefficients`: feedback only at lag one.
- `candidatePoles_onePoleFeedbackCoefficients`: the exact candidate-pole singleton.
- `isSchurStable_onePoleFeedbackCoefficients_iff`: the exact Schur criterion.
- `isAbsSummable_geometricSeq_iff_norm_lt_one`: the exact summability criterion.
- `sphere_subset_ROC_geometricSeq_of_norm_lt_one`: the unit-circle ROC bridge.

## iii. Table of contents

- A. Lag-one denominator and candidate pole
- B. Geometric impulse response

## iv. References and non-claims

`candidatePoles` and `IsSchurStable` are defined in
`Physlib/Mathematics/ZTransform/Stability.lean:226-234`. Absolute summability, the region of
convergence, and their unit-circle equivalence are defined or proved in that file at lines
113-161. This file imports only production Z-transform modules and is neutral mathematics.

A candidate denominator zero need not be an actual transfer-function pole after numerator
cancellation. No optics, physical resonance, network reachability, or general rational BIBO
equivalence is asserted here.
-/

@[expose] public section

namespace Physlib.ZTransform

noncomputable section

/-!

## A. Lag-one denominator and candidate pole

-/

/-- Feedback coefficients for `y n = a * y (n - 1) + x n`. -/
def onePoleFeedbackCoefficients (a : ℂ) : ℕ → ℂ :=
  fun k ↦ if k = 1 then a else 0

/-- The lag-one feedback coefficient is `a`. -/
lemma onePoleFeedbackCoefficients_one (a : ℂ) :
    onePoleFeedbackCoefficients a 1 = a :=
  if_pos rfl

/-- The delay symbol of the lag-one feedback coefficients is `a * u`. -/
lemma delaySymbol_onePoleFeedbackCoefficients (a u : ℂ) :
    delaySymbol {1} (onePoleFeedbackCoefficients a) u = a * u := by
  rw [delaySymbol, Finset.sum_singleton, onePoleFeedbackCoefficients_one, pow_one]

/-- For nonzero `a`, the lag-one candidate-pole set is exactly `{a}`. -/
lemma candidatePoles_onePoleFeedbackCoefficients {a : ℂ} (ha : a ≠ 0) :
    candidatePoles {1} (onePoleFeedbackCoefficients a) = {a} := by
  ext z
  simp only [candidatePoles, Set.mem_ofPred_eq, Set.mem_singleton_iff,
    delaySymbol_onePoleFeedbackCoefficients]
  constructor
  · rintro ⟨hz, hzero⟩
    have h : a * z⁻¹ = 1 := by linear_combination -hzero
    field_simp at h
    exact h.symm
  · rintro rfl
    exact ⟨ha, by rw [mul_inv_cancel₀ ha, sub_self]⟩

/-- For nonzero `a`, lag-one Schur stability is exactly `‖a‖ < 1`. -/
lemma isSchurStable_onePoleFeedbackCoefficients_iff {a : ℂ} (ha : a ≠ 0) :
    IsSchurStable {1} (onePoleFeedbackCoefficients a) ↔ ‖a‖ < 1 := by
  rw [IsSchurStable, candidatePoles_onePoleFeedbackCoefficients ha]
  exact ⟨fun h => h a rfl, fun h z hz => by rw [Set.mem_singleton_iff.mp hz]; exact h⟩

/-!

## B. Geometric impulse response

-/

/-- A nonzero-ratio geometric sequence is absolutely summable exactly when `‖a‖ < 1`. -/
lemma isAbsSummable_geometricSeq_iff_norm_lt_one {a : ℂ} (ha : a ≠ 0) :
    IsAbsSummable (geometricSeq a) ↔ ‖a‖ < 1 := by
  rw [isAbsSummable_iff_one_mem_ROC, ROC_geometricSeq ha]
  simp

/-- If `‖a‖ < 1`, the unit circle lies in the geometric sequence's region of convergence. -/
lemma sphere_subset_ROC_geometricSeq_of_norm_lt_one {a : ℂ} (ha : a ≠ 0)
    (hNorm : ‖a‖ < 1) : Metric.sphere (0 : ℂ) 1 ⊆ ROC (geometricSeq a) :=
  (isAbsSummable_iff_sphere_subset_ROC _).mp
    ((isAbsSummable_geometricSeq_iff_norm_lt_one ha).mpr hNorm)

end

end Physlib.ZTransform
