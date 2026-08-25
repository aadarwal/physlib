/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Mathematics.ZTransform.DifferenceEquation

/-!
# Regression tests for difference equations and transfer functions

## i. Overview

The first example is a solved case, and it is the reason the transfer-function theory is not
vacuous. No existence theorem for causal solutions is proved in
`Physlib.Mathematics.ZTransform.DifferenceEquation`, so every statement there is conditional on
being handed a solution. Here the causal geometric sequence is shown to solve the one-pole
recurrence `y n = a * y (n - 1) + x n` driven by the unit impulse, and its transform, computed
independently in `Physlib.Mathematics.ZTransform.Convergence` by summing a geometric series, is
shown to agree with the transfer function times the input transform. Two independent routes to
the same value therefore meet.

The second example is the first-order all-pass section `(a + z⁻¹) / (1 + a * z⁻¹)`. Its symbolic
form is derived from the recurrence coefficients rather than written down, and for a real
coefficient its modulus on the unit circle is proved to be exactly one. That is a property, not a
formula, so it fails if the numerator and denominator coefficients are swapped.

The third example is the audited second-order low-pass filter of the source, with the exact
rational coefficients the source uses. Its symbols are computed, its gain at `z = 1` is exactly
one, and its gain at `z = -1` is exactly zero. The first of those detects a sign error in the
feedback symbol, since replacing `1 - delaySymbol` by `1 + delaySymbol` changes the value at
`z = 1` from `1` to a number that is not `1`. The second is the Nyquist null that makes the
filter a low-pass rather than an arbitrary second-order section.

## ii. Key results

- `Physlib.ZTransform.isRecurrenceSolution_geometricSeq`: the geometric sequence solves the
  one-pole recurrence driven by the unit impulse.
- `Physlib.ZTransform.transform_geometricSeq_eq_transferFunction_mul`: its transform agrees with
  the transfer function times the input transform.
- `Physlib.ZTransform.transferFunction_allPass`: the first-order all-pass symbolic form.
- `Physlib.ZTransform.norm_transferFunction_allPass`: its modulus is one on the unit circle.
- `Physlib.ZTransform.transferFunction_lowPass_one`: the audited low-pass has unit gain at
  `z = 1`.
- `Physlib.ZTransform.transferFunction_lowPass_neg_one`: it has zero gain at `z = -1`.

## iii. Table of contents

- A. A solved one-pole recurrence
- B. The first-order all-pass section
- C. The audited second-order low-pass filter

## iv. References

The second-order low-pass coefficients are those of Definition 14 and Theorem 14 (pp. 496-497) of
U. Siddique, M. Y. Mahmoud, and S. Tahar, "On the Formalization of Z-Transform in HOL", ITP 2014,
LNCS 8558, namely feedback `[0, 1.194, -0.436]` and feedforward `[0.0605, 0.121, 0.0605]`, given
there as exact rationals. They are used here as exact rationals, not as floating-point
approximations. The leading feedback entry `0` is the source's structural constraint that the
feedback is strictly causal, which appears here as the lag set `{1, 2}` not containing `0`.

The all-pass section and the unit-gain and Nyquist-null checks are standard; a textbook reference
is A. V. Oppenheim and R. W. Schafer, *Discrete-Time Signal Processing*, 3rd ed., Pearson, 2010,
chapter 5. The source proves a frequency response for the low-pass filter, not these two exact
values; the values are chosen here because they are exact and because each detects a specific
error.

These are algebraic regressions on complex sequences. No physical, optical, or signal-processing
interpretation is asserted, and no claim is made that any of these filters is realizable.

-/

@[expose] public section

namespace Physlib.ZTransform

noncomputable section

/-!

## A. A solved one-pole recurrence

-/

/-- The feedback coefficients of the one-pole recurrence `y n = a * y (n - 1) + x n`. -/
def onePoleFeedback (a : ℂ) : ℕ → ℂ := fun k => if k = 1 then a else 0

/-- The only feedback coefficient of the one-pole recurrence is at lag one. -/
lemma onePoleFeedback_one (a : ℂ) : onePoleFeedback a 1 = a := if_pos rfl

/-- The feedforward coefficients of the one-pole recurrence: the input enters undelayed. -/
def onePoleFeedforward : ℕ → ℂ := fun _ => 1

/-- The feedforward coefficient at lag zero is one. -/
lemma onePoleFeedforward_zero : onePoleFeedforward 0 = 1 := rfl

/-- The unit impulse takes the value one at index zero. -/
lemma unitImpulse_zero : unitImpulse 0 = 1 := if_pos rfl

/-- The geometric sequence takes the value one at index zero. -/
lemma geometricSeq_zero (a : ℂ) : geometricSeq a 0 = 1 := by
  simpa using geometricSeq_natCast a 0

/-- The causal geometric sequence solves the one-pole recurrence driven by the unit impulse. -/
theorem isRecurrenceSolution_geometricSeq (a : ℂ) :
    IsRecurrenceSolution {1} {0} (onePoleFeedback a) onePoleFeedforward unitImpulse
      (geometricSeq a) := by
  funext n
  rw [Pi.add_apply]
  simp only [delayCombination, Finset.sum_singleton, onePoleFeedback_one,
    onePoleFeedforward_zero, Nat.cast_one, Nat.cast_zero, sub_zero, one_mul]
  rcases lt_or_ge n 0 with hn | hn
  · rw [geometricSeq_isCausal a n hn, geometricSeq_isCausal a (n - 1) (by omega),
      unitImpulse_isCausal n hn, mul_zero, add_zero]
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rcases m with _ | k
    · rw [Nat.cast_zero, geometricSeq_zero, geometricSeq_isCausal a (0 - 1) (by norm_num),
        unitImpulse_zero, mul_zero, zero_add]
    · have hstep : ((k + 1 : ℕ) : ℤ) - 1 = ((k : ℕ) : ℤ) := by push_cast; ring
      have himp : unitImpulse ((k + 1 : ℕ) : ℤ) = 0 := by
        show (if ((k + 1 : ℕ) : ℤ) = 0 then (1 : ℂ) else 0) = 0
        rw [if_neg (by omega)]
      rw [hstep, himp, geometricSeq_natCast, geometricSeq_natCast, add_zero, pow_succ]
      ring

/-- The transfer function of the one-pole recurrence is `(1 - a * z⁻¹)⁻¹`. -/
theorem transferFunction_onePole (a z : ℂ) :
    transferFunction {1} {0} (onePoleFeedback a) onePoleFeedforward z = (1 - a * z⁻¹)⁻¹ := by
  rw [transferFunction, delaySymbol, delaySymbol, Finset.sum_singleton, Finset.sum_singleton,
    onePoleFeedback_one, onePoleFeedforward_zero, pow_zero, pow_one, one_mul, one_div]

/-- Outside the circle of radius `‖a‖` the geometric transform computed by summing the series
agrees with the transfer function times the input transform. -/
theorem transform_geometricSeq_eq_transferFunction_mul {a z : ℂ} (ha : a ≠ 0) (hz : ‖a‖ < ‖z‖) :
    transform (geometricSeq a) z =
      transferFunction {1} {0} (onePoleFeedback a) onePoleFeedforward z *
        transform unitImpulse z := by
  rw [transform_geometricSeq ha hz, transferFunction_onePole, transform_unitImpulse, mul_one]

/-!

## B. The first-order all-pass section

-/

/-- The feedback coefficients of the first-order all-pass section. -/
def allPassFeedback (a : ℂ) : ℕ → ℂ := fun k => if k = 1 then -a else 0

/-- The only feedback coefficient of the all-pass section is at lag one. -/
lemma allPassFeedback_one (a : ℂ) : allPassFeedback a 1 = -a := if_pos rfl

/-- The feedforward coefficients of the first-order all-pass section. -/
def allPassFeedforward (a : ℂ) : ℕ → ℂ := fun k => if k = 0 then a else 1

/-- The undelayed feedforward coefficient of the all-pass section. -/
lemma allPassFeedforward_zero (a : ℂ) : allPassFeedforward a 0 = a := if_pos rfl

/-- The unit-delay feedforward coefficient of the all-pass section. -/
lemma allPassFeedforward_one (a : ℂ) : allPassFeedforward a 1 = 1 := if_neg one_ne_zero

/-- The first-order all-pass transfer function is `(a + z⁻¹) / (1 + a * z⁻¹)`. -/
theorem transferFunction_allPass (a z : ℂ) :
    transferFunction {1} {0, 1} (allPassFeedback a) (allPassFeedforward a) z =
      (a + z⁻¹) / (1 + a * z⁻¹) := by
  rw [transferFunction, delaySymbol, delaySymbol, Finset.sum_singleton,
    Finset.sum_insert (by decide), Finset.sum_singleton, allPassFeedback_one,
    allPassFeedforward_zero, allPassFeedforward_one, pow_zero, pow_one, mul_one, one_mul,
    neg_mul, sub_neg_eq_add]

/-- For a real number `a` and a unit-modulus complex number `u`, the moduli of `a + u` and
`1 + a * u` agree. This is the algebraic content of the all-pass property. -/
lemma norm_ofReal_add_eq_norm_one_add_mul {a : ℝ} {u : ℂ} (hu : ‖u‖ = 1) :
    ‖(a : ℂ) + u‖ = ‖1 + (a : ℂ) * u‖ := by
  have hsq : u.re ^ 2 + u.im ^ 2 = 1 := by
    have h : Complex.normSq u = 1 := by rw [← Complex.sq_norm, hu, one_pow]
    rw [Complex.normSq_apply] at h
    linear_combination h
  have h2 : ‖(a : ℂ) + u‖ ^ 2 = ‖1 + (a : ℂ) * u‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im]
    linear_combination (1 - (a : ℝ) ^ 2) * hsq
  nlinarith [norm_nonneg ((a : ℂ) + u), norm_nonneg (1 + (a : ℂ) * u), h2]

/-- For a real coefficient the first-order all-pass section has modulus one at every point of the
unit circle at which its denominator does not vanish. -/
theorem norm_transferFunction_allPass {a : ℝ} {z : ℂ} (hz : ‖z‖ = 1)
    (hden : 1 + (a : ℂ) * z⁻¹ ≠ 0) :
    ‖transferFunction {1} {0, 1} (allPassFeedback (a : ℂ)) (allPassFeedforward (a : ℂ)) z‖
      = 1 := by
  have hinv : ‖z⁻¹‖ = 1 := by rw [norm_inv, hz, inv_one]
  rw [transferFunction_allPass, norm_div, norm_ofReal_add_eq_norm_one_add_mul hinv,
    div_self (norm_ne_zero_iff.mpr hden)]

/-!

## C. The audited second-order low-pass filter

-/

/-- The feedback coefficients of the audited second-order low-pass filter, as exact rationals. -/
def lowPassFeedback : ℕ → ℂ :=
  fun k => if k = 1 then 1194 / 1000 else if k = 2 then -(436 / 1000) else 0

/-- The feedback coefficient at lag one. -/
lemma lowPassFeedback_one : lowPassFeedback 1 = 1194 / 1000 := if_pos rfl

/-- The feedback coefficient at lag two. -/
lemma lowPassFeedback_two : lowPassFeedback 2 = -(436 / 1000) := by
  rw [lowPassFeedback, if_neg (by decide : ¬(2 : ℕ) = 1), if_pos rfl]

/-- The feedforward coefficients of the audited second-order low-pass filter, as exact
rationals. -/
def lowPassFeedforward : ℕ → ℂ :=
  fun k => if k = 0 then 605 / 10000 else if k = 1 then 121 / 1000 else 605 / 10000

/-- The undelayed feedforward coefficient. -/
lemma lowPassFeedforward_zero : lowPassFeedforward 0 = 605 / 10000 := if_pos rfl

/-- The unit-delay feedforward coefficient. -/
lemma lowPassFeedforward_one : lowPassFeedforward 1 = 121 / 1000 := by
  rw [lowPassFeedforward, if_neg (by decide : ¬(1 : ℕ) = 0), if_pos rfl]

/-- The two-delay feedforward coefficient. -/
lemma lowPassFeedforward_two : lowPassFeedforward 2 = 605 / 10000 := by
  rw [lowPassFeedforward, if_neg (by decide : ¬(2 : ℕ) = 0),
    if_neg (by decide : ¬(2 : ℕ) = 1)]

/-- The feedback lag set of the audited filter excludes the lag zero, so the filter is strictly
causal. -/
theorem zero_notMem_lowPass_lags : (0 : ℕ) ∉ ({1, 2} : Finset ℕ) := by decide

/-- The feedforward symbol of the audited filter. -/
theorem delaySymbol_lowPassFeedforward (u : ℂ) :
    delaySymbol {0, 1, 2} lowPassFeedforward u =
      605 / 10000 + 121 / 1000 * u + 605 / 10000 * u ^ 2 := by
  rw [delaySymbol, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, lowPassFeedforward_zero, lowPassFeedforward_one,
    lowPassFeedforward_two, pow_zero, pow_one, mul_one]
  ring

/-- The feedback symbol of the audited filter. -/
theorem delaySymbol_lowPassFeedback (u : ℂ) :
    delaySymbol {1, 2} lowPassFeedback u = 1194 / 1000 * u - 436 / 1000 * u ^ 2 := by
  rw [delaySymbol, Finset.sum_insert (by decide), Finset.sum_singleton, lowPassFeedback_one,
    lowPassFeedback_two, pow_one]
  ring

/-- The audited low-pass filter has exactly unit gain at `z = 1`. Replacing the denominator
`1 - delaySymbol` by `1 + delaySymbol` changes this value, so the check fixes that sign. -/
theorem transferFunction_lowPass_one :
    transferFunction {1, 2} {0, 1, 2} lowPassFeedback lowPassFeedforward 1 = 1 := by
  rw [transferFunction, inv_one, delaySymbol_lowPassFeedforward, delaySymbol_lowPassFeedback]
  norm_num

/-- The audited low-pass filter has exactly zero gain at `z = -1`, the Nyquist point. -/
theorem transferFunction_lowPass_neg_one :
    transferFunction {1, 2} {0, 1, 2} lowPassFeedback lowPassFeedforward (-1) = 0 := by
  rw [transferFunction, delaySymbol_lowPassFeedforward, delaySymbol_lowPassFeedback]
  norm_num

end

end Physlib.ZTransform
