/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Mathematics.ZTransform.DifferenceEquation

/-!
# Stability of causal discrete-time systems

## i. Overview

Three conditions are usually run together under the word "stable": that a sequence is absolutely
summable, that the region of convergence of its transform contains the unit circle, and that the
system it drives carries bounded inputs to bounded outputs. This file separates them, proves the
implications it can prove, and says which converse is not proved.

Absolute summability of a causal sequence and containment of the unit circle in the absolute
region of convergence are proved **equivalent**, and in a strong form: the region of convergence
then contains the entire closed exterior of the unit circle, because absolute convergence depends
on the evaluation point only through its modulus. Both directions are proved.

Absolute summability implies bounded-input bounded-output stability of the causal convolution
operator, with an explicit bound. That direction is proved. **The converse is not proved here.**
Bounded-input bounded-output stability implies absolute summability for this class, but the
standard argument needs a sign-selecting input, and until that is formalized no theorem in this
file asserts it. Nothing here should be read as an equivalence.

For a difference equation, a zero of the denominator symbol is a *candidate* pole. Schur
stability is defined as every candidate pole lying strictly inside the unit circle. It is proved
that Schur stability makes the denominator nonvanishing on the closed exterior of the unit
circle, and hence that the transfer relation holds there for absolutely summable input and
output. **It is not proved that Schur stability implies the impulse response is absolutely
summable.** That is the substantive direction of the classical theorem and needs a partial
fraction or companion-matrix argument that is not present here.

A sufficient coefficient criterion is proved: if the feedback coefficients have total modulus
less than one, the system is Schur stable. It is sufficient and not necessary, and the companion
regression file exhibits a Schur-stable system that fails it.

## ii. Key results

- `Physlib.ZTransform.IsAbsSummable`: absolute summability of the nonnegative-index samples.
- `Physlib.ZTransform.isAbsSummable_iff_one_mem_ROC`: absolute summability is membership of `1`
  in the absolute region of convergence.
- `Physlib.ZTransform.isAbsSummable_iff_closedExterior_subset_ROC`: equivalently, the region of
  convergence contains the whole closed exterior of the unit circle.
- `Physlib.ZTransform.convolution`: the causal convolution operator.
- `Physlib.ZTransform.norm_convolution_le`: the explicit bounded-input bound.
- `Physlib.ZTransform.isBIBOStable_of_isAbsSummable`: absolute summability implies
  bounded-input bounded-output stability. The converse is not proved.
- `Physlib.ZTransform.candidatePoles`, `Physlib.ZTransform.IsSchurStable`: candidate poles of a
  difference equation and the Schur condition.
- `Physlib.ZTransform.transform_eq_transferFunction_mul_of_isSchurStable`: the transfer relation
  on the closed exterior of the unit circle.
- `Physlib.ZTransform.isSchurStable_of_sum_norm_lt_one`: a sufficient coefficient criterion.

## iii. Table of contents

- A. Absolute summability and the closed exterior of the unit circle
- B. Bounded sequences and the causal convolution
- C. Bounded-input bounded-output stability
- D. Candidate poles and Schur stability
- E. A sufficient coefficient criterion

## iv. References

Ledger row ZT-10 of the Physlib parity ledger records that no fetched source in the Concordia
HVG optics corpus contains a Schur-stability theorem, a bounded-input bounded-output equivalence,
or a group-delay or dispersion theorem. This file is therefore Physlib-original and is not a
parity claim against any source. It should be reviewed on its own merits.

The statements follow the standard treatment in A. V. Oppenheim and R. W. Schafer,
*Discrete-Time Signal Processing*, 3rd ed., Pearson, 2010, chapters 2 and 3, where absolute
summability of the impulse response, containment of the unit circle in the region of convergence,
and bounded-input bounded-output stability are related.

The requirement to state which direction of each equivalence is proved, and to withhold the rest
explicitly, is `goal.md` section H.4 S4P, "discrete-time Schur stability and BIBO equivalence
only for a stated proper causal rational class".

Three things are deliberately not claimed here. First, bounded-input bounded-output stability is
not proved to imply absolute summability. Second, Schur stability is not proved to imply that a
solution of the difference equation is absolutely summable. Third, no theorem here asserts that a
candidate pole is an actual pole of the transfer function, since a numerator zero at the same
point can cancel it.

The convolution operator is defined here because bounded-input bounded-output stability cannot be
stated without it. Its transform, the convolution theorem, is not proved here.

This file is neutral mathematics and imports no physics.

-/

@[expose] public section

namespace Physlib.ZTransform

noncomputable section

variable {s t : Finset ℕ} {α β : ℕ → ℂ} {h x y : ℤ → ℂ}

/-!

## A. Absolute summability and the closed exterior of the unit circle

-/

/-- A sequence is absolutely summable when the norms of its nonnegative-index samples are
summable. Negative-index samples are ignored, matching the unilateral transform. -/
def IsAbsSummable (h : ℤ → ℂ) : Prop := Summable fun n : ℕ => ‖h n‖

/-- The transform series at `1` is the sequence itself. -/
@[simp]
lemma seriesTerm_one (h : ℤ → ℂ) (n : ℕ) : seriesTerm h 1 n = h n := by
  simp [seriesTerm]

/-- Absolute summability is exactly membership of `1` in the absolute region of convergence. -/
theorem isAbsSummable_iff_one_mem_ROC (h : ℤ → ℂ) :
    IsAbsSummable h ↔ (1 : ℂ) ∈ ROC h := by
  have hfun : seriesTerm h 1 = fun n : ℕ => h n := funext (seriesTerm_one h)
  constructor
  · intro hs
    exact ⟨one_ne_zero, by rw [hfun]; exact summable_norm_iff.mp hs⟩
  · rintro ⟨-, hs⟩
    rw [hfun] at hs
    exact summable_norm_iff.mpr hs

/-- Absolute summability is exactly containment of the closed exterior of the unit circle in the
absolute region of convergence. -/
theorem isAbsSummable_iff_closedExterior_subset_ROC (h : ℤ → ℂ) :
    IsAbsSummable h ↔ {z : ℂ | 1 ≤ ‖z‖} ⊆ ROC h := by
  rw [isAbsSummable_iff_one_mem_ROC]
  constructor
  · intro hmem z hz
    refine ROC_mem_of_mem_of_norm_le hmem ?_
    rw [norm_one]
    exact hz
  · intro hsub
    exact hsub (by simp)

/-- Absolute summability is exactly containment of the unit circle in the absolute region of
convergence. -/
theorem isAbsSummable_iff_sphere_subset_ROC (h : ℤ → ℂ) :
    IsAbsSummable h ↔ Metric.sphere (0 : ℂ) 1 ⊆ ROC h := by
  rw [isAbsSummable_iff_one_mem_ROC]
  constructor
  · intro hmem z hz
    refine ROC_mem_of_mem_of_norm_eq hmem ?_
    rw [norm_one]
    exact (mem_sphere_zero_iff_norm.mp hz).symm
  · intro hsub
    exact hsub (mem_sphere_zero_iff_norm.mpr norm_one)

/-!

## B. Bounded sequences and the causal convolution

-/

/-- A two-sided sequence is bounded when its samples have a common norm bound. -/
def IsBoundedSeq (x : ℤ → ℂ) : Prop := ∃ C : ℝ, ∀ n : ℤ, ‖x n‖ ≤ C

/-- The causal convolution of a sequence with an input, summing over nonnegative lags. -/
def convolution (h x : ℤ → ℂ) : ℤ → ℂ := fun n => ∑' k : ℕ, h k * x (n - k)

/-- A bound on a bounded sequence is nonnegative. -/
lemma IsBoundedSeq.nonneg_of_bound {C : ℝ} (hC : ∀ n : ℤ, ‖x n‖ ≤ C) : 0 ≤ C :=
  le_trans (norm_nonneg _) (hC 0)

/-- For an absolutely summable sequence and a bounded input, the convolution series converges
absolutely at every index. -/
lemma summable_norm_convolution_term (hh : IsAbsSummable h) {C : ℝ}
    (hC : ∀ n : ℤ, ‖x n‖ ≤ C) (n : ℤ) :
    Summable fun k : ℕ => ‖h k * x (n - k)‖ := by
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_) (hh.mul_right C)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)

/-- The explicit bounded-input bound: the convolution is bounded by the total mass of the
sequence times the input bound. -/
theorem norm_convolution_le (hh : IsAbsSummable h) {C : ℝ} (hC : ∀ n : ℤ, ‖x n‖ ≤ C) (n : ℤ) :
    ‖convolution h x n‖ ≤ (∑' k : ℕ, ‖h k‖) * C := by
  have hsum := summable_norm_convolution_term hh hC n
  refine le_trans (norm_tsum_le_tsum_norm hsum) ?_
  rw [← tsum_mul_right]
  refine Summable.tsum_le_tsum (fun k => ?_) hsum (hh.mul_right C)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)

/-!

## C. Bounded-input bounded-output stability

-/

/-- A sequence is bounded-input bounded-output stable when convolving with it carries every
bounded input to a bounded output. -/
def IsBIBOStable (h : ℤ → ℂ) : Prop :=
  ∀ x : ℤ → ℂ, IsBoundedSeq x → IsBoundedSeq (convolution h x)

/-- Absolute summability implies bounded-input bounded-output stability. The converse is true for
this class but is not proved here. -/
theorem isBIBOStable_of_isAbsSummable (hh : IsAbsSummable h) : IsBIBOStable h := by
  rintro x ⟨C, hC⟩
  exact ⟨(∑' k : ℕ, ‖h k‖) * C, fun n => norm_convolution_le hh hC n⟩

/-- Containment of the unit circle in the absolute region of convergence implies bounded-input
bounded-output stability. -/
theorem isBIBOStable_of_sphere_subset_ROC (h : ℤ → ℂ)
    (hs : Metric.sphere (0 : ℂ) 1 ⊆ ROC h) : IsBIBOStable h :=
  isBIBOStable_of_isAbsSummable ((isAbsSummable_iff_sphere_subset_ROC h).mpr hs)

/-!

## D. Candidate poles and Schur stability

-/

/-- The candidate poles of a difference equation: the nonzero points at which the denominator
symbol vanishes. A candidate pole is an actual pole of the transfer function only if the
numerator does not vanish there as well, which is not asserted. -/
def candidatePoles (s : Finset ℕ) (α : ℕ → ℂ) : Set ℂ :=
  {z : ℂ | z ≠ 0 ∧ 1 - delaySymbol s α z⁻¹ = 0}

/-- A difference equation is Schur stable when every candidate pole lies strictly inside the unit
circle. -/
def IsSchurStable (s : Finset ℕ) (α : ℕ → ℂ) : Prop := ∀ z ∈ candidatePoles s α, ‖z‖ < 1

/-- Under Schur stability the denominator symbol does not vanish anywhere on the closed exterior
of the unit circle. -/
theorem denominator_ne_zero_of_isSchurStable (hS : IsSchurStable s α) {z : ℂ} (hz : 1 ≤ ‖z‖) :
    1 - delaySymbol s α z⁻¹ ≠ 0 := by
  intro hzero
  have hne : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hz
    linarith
  exact absurd (hS z ⟨hne, hzero⟩) (not_lt.mpr hz)

/-- Under Schur stability, with absolutely summable input and output, the region of convergence
of the transfer relation contains the closed exterior of the unit circle. -/
theorem closedExterior_subset_iirROC_of_isSchurStable (hS : IsSchurStable s α)
    (hx : IsAbsSummable x) (hy : IsAbsSummable y) :
    {z : ℂ | 1 ≤ ‖z‖} ⊆ iirROC s α x y := by
  intro z hz
  refine ⟨⟨(isAbsSummable_iff_closedExterior_subset_ROC x).mp hx hz,
    (isAbsSummable_iff_closedExterior_subset_ROC y).mp hy hz⟩, ?_⟩
  exact denominator_ne_zero_of_isSchurStable hS hz

/-- Under Schur stability, with absolutely summable causal input and output, the transfer
relation holds at every point of the closed exterior of the unit circle, in particular at every
point of the unit circle itself. -/
theorem transform_eq_transferFunction_mul_of_isSchurStable (hcx : IsCausal x) (hcy : IsCausal y)
    (hS : IsSchurStable s α) (hx : IsAbsSummable x) (hy : IsAbsSummable y)
    (hr : IsRecurrenceSolution s t α β x y) {z : ℂ} (hz : 1 ≤ ‖z‖) :
    transform y z = transferFunction s t α β z * transform x z :=
  transform_eq_transferFunction_mul_of_mem_iirROC hcx hcy
    (closedExterior_subset_iirROC_of_isSchurStable hS hx hy hz) hr

/-!

## E. A sufficient coefficient criterion

-/

/-- If the feedback coefficients have total modulus less than one, the difference equation is
Schur stable. The criterion is sufficient and not necessary; a Schur-stable system failing it is
exhibited in the companion regression file. -/
theorem isSchurStable_of_sum_norm_lt_one (hsum : ∑ k ∈ s, ‖α k‖ < 1) : IsSchurStable s α := by
  rintro z ⟨hne, hzero⟩
  by_contra hge
  rw [not_lt] at hge
  have hinv : ‖z⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ hge
  have hone : delaySymbol s α z⁻¹ = 1 := by linear_combination -hzero
  have hbound : ‖delaySymbol s α z⁻¹‖ ≤ ∑ k ∈ s, ‖α k‖ := by
    refine le_trans (norm_sum_le s _) (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hinv)
  rw [hone, norm_one] at hbound
  linarith

end

end Physlib.ZTransform
