/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Complex exponential characters of real modules

## i. Overview

This module bundles the exponential of a complex-valued real-linear functional as a
multiplicative character. If `L : V →ₗ[ℝ] ℂ`, its character sends `v` to `exp (L v)`.

The additive source `V` is presented as `Multiplicative V` so that the character is a
`MonoidHom` and Mathlib's Dedekind linear-independence theorem for monoid characters applies
directly. No topology or norm is required on `V`; only its real-module structure is used.

The module first proves that a complex rate is zero if all of its real rescalings exponentiate
to one. This removes the periodic ambiguity of the complex exponential because every real
rescaling is tested, rather than a single value. It then shows that the exponential character
determines its real-linear exponent functional and concludes linear independence of distinct
such characters.

## ii. Key results

- `Complex.forall_exp_real_smul_eq_one_iff`: a complex rate vanishes exactly when all real
  rescalings exponentiate to one.
- `Complex.realLinearExponentialCharacter_injective`: the character determines its exponent
  functional.
- `Complex.linearIndependent_realLinearExponentialCharacter`: distinct real-linear exponential
  characters are linearly independent over `ℂ`.
- `Complex.finsupp_sum_mul_exp_eq_zero_iff`: a finite sum of exponential characters vanishes
  everywhere exactly when every aggregated coefficient vanishes.

## iii. Table of contents

- A. Real rescalings of one complex rate
- B. Characters of real-linear functionals
- C. Linear independence

## iv. References

The final result is an application of Mathlib's `linearIndependent_monoidHom`, the Dedekind
linear-independence theorem for monoid characters.
-/

@[expose] public section

noncomputable section

namespace Complex

/-!

## A. Real rescalings of one complex rate

-/

/-- Every real rescaling of a complex rate exponentiates to one exactly when the rate is zero. -/
lemma forall_exp_real_smul_eq_one_iff (z : ℂ) :
    (∀ t : ℝ, exp (t • z) = 1) ↔ z = 0 := by
  constructor
  · intro h
    have hzre : z.re = 0 := by
      have hone : exp z = 1 := by simpa using h 1
      have hnorm := congrArg norm hone
      rw [norm_exp] at hnorm
      exact (Real.exp_eq_one_iff z.re).mp (by simpa using hnorm)
    apply Complex.ext
    · simpa using hzre
    · by_contra hzim
      have hzim' : z.im ≠ 0 := by simpa using hzim
      have hpi := h (Real.pi / z.im)
      have hexponent : (Real.pi / z.im) • z = (Real.pi : ℂ) * I := by
        apply Complex.ext
        · simp [hzre]
        · simpa using div_mul_cancel₀ Real.pi hzim'
      rw [hexponent, exp_pi_mul_I] at hpi
      norm_num at hpi
  · rintro rfl
    simp

/-!

## B. Characters of real-linear functionals

-/

variable {V : Type*} [AddCommMonoid V] [Module ℝ V]

/-- The multiplicative complex exponential character associated to a complex-valued real-linear
functional.

The type synonym `Multiplicative V` presents addition in `V` as multiplication, matching the
domain expected by `MonoidHom`. -/
def realLinearExponentialCharacter
    (L : V →ₗ[ℝ] ℂ) : Multiplicative V →* ℂ :=
  expMonoidHom.comp L.toAddMonoidHom.toMultiplicative

@[simp]
lemma realLinearExponentialCharacter_apply (L : V →ₗ[ℝ] ℂ) (v : V) :
    realLinearExponentialCharacter L (.ofAdd v) = exp (L v) := rfl

/-- A complex-valued real-linear functional is determined by its exponential character. -/
lemma realLinearExponentialCharacter_injective :
    Function.Injective (realLinearExponentialCharacter (V := V)) := by
  intro L M hcharacter
  ext v
  apply sub_eq_zero.mp
  rw [← forall_exp_real_smul_eq_one_iff]
  intro t
  have ht := DFunLike.congr_fun hcharacter (Multiplicative.ofAdd (t • v))
  simp only [realLinearExponentialCharacter_apply, map_smul, real_smul] at ht
  rw [smul_sub]
  simp only [real_smul]
  rw [exp_sub, ht, div_self (exp_ne_zero _)]

/-!

## C. Linear independence

-/

/-- Exponential characters of distinct complex-valued real-linear functionals are linearly
independent over `ℂ`. -/
lemma linearIndependent_realLinearExponentialCharacter :
    LinearIndependent ℂ
      (fun L : V →ₗ[ℝ] ℂ =>
        (realLinearExponentialCharacter L : Multiplicative V → ℂ)) := by
  exact (linearIndependent_monoidHom (Multiplicative V) ℂ).comp
    realLinearExponentialCharacter realLinearExponentialCharacter_injective

/-- A finitely supported sum of exponentials of complex-valued real-linear functionals vanishes
everywhere exactly when every aggregated coefficient vanishes. -/
lemma finsupp_sum_mul_exp_eq_zero_iff (a : (V →ₗ[ℝ] ℂ) →₀ ℂ) :
    (∀ v : V, a.sum (fun L c => c * exp (L v)) = 0) ↔ a = 0 := by
  constructor
  · intro h
    apply (linearIndependent_iff.mp
      (linearIndependent_realLinearExponentialCharacter (V := V))) a
    funext v
    induction v using Multiplicative.rec with
    | _ v =>
      simpa [Finsupp.linearCombination_apply, Finsupp.sum, smul_eq_mul] using h v
  · rintro rfl
    simp

end Complex
