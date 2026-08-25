/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Mathlib.Data.List.DropRight
public import Mathlib.Data.List.GetD
public import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# Executable coefficients for rational functions

## i. Overview

This file separates an executable coefficient-list presentation from Mathlib's canonical but
noncomputable rational-function representation. Polynomial coefficients are stored from constant
term upward and have no trailing zero. Rational coefficients store an unreduced numerator and a
nonzero denominator. Their interpretation in `RatFunc` is exact even though the stored fraction is
not required to be coprime.

Evaluation uses Horner recursion on the stored lists. It agrees with `RatFunc.eval` whenever the
stored denominator is nonzero at the evaluation point. This hypothesis is deliberately sufficient
rather than necessary: a stored common factor may vanish even after Mathlib cancels it.

The subring `RationalFunction.regularAt` packages rational functions whose canonical denominator
does not vanish at one point. On that subring, `RatFunc.eval` is an honest ring homomorphism. This
is the algebraic interface needed to evaluate finite matrix expressions without treating
finite-point evaluation as a global homomorphism on `RatFunc`.

## ii. Scope

The executable fraction presentation is normalized polynomial-by-polynomial, but it is not reduced
by a polynomial gcd. No inverse, pole-removal algorithm, multivariable interpretation, analytic
response domain, or physical-frequency meaning is supplied here. A failed stored-denominator guard
supplies no certified agreement with canonical rational-function evaluation. Direct field division
remains total in Lean, including at a zero denominator.

## iii. Key definitions and results

- `RationalFunction.regularAt`: rational functions with nonvanishing canonical denominator.
- `RationalFunction.evalRegularAt`: evaluation as a ring homomorphism on that subring.
- `PolynomialCoefficients`: executable normalized little-endian polynomial coefficients.
- `PolynomialCoefficients.eval_toPolynomial`: Horner evaluation agrees with polynomial evaluation.
- `RationalCoefficients`: executable unreduced numerator and nonzero denominator lists.
- `RationalCoefficients.toRatFunc`: proof-exact interpretation in the rational-function field.
- `RationalCoefficients.ratFunc_eval_eq_evalAt`: guarded agreement of both evaluations.

## iv. Table of contents

- A. Rational functions regular at one point
- B. Normalized polynomial coefficients
- C. Unreduced rational coefficients
- D. Guarded rational-function interpretation

-/

@[expose] public section

namespace Physlib

universe u

/-!

## A. Rational functions regular at one point

-/

namespace RationalFunction

open Polynomial

variable {K L : Type u} [Field K] [Field L]

/-- Nonvanishing of a polynomial denominator propagates backward along denominator divisibility. -/
lemma eval₂_denom_ne_zero_of_dvd {f : K →+* L} {point : L}
    {r : RatFunc K} {denominator : K[X]} (hDvd : r.denom ∣ denominator)
    (hDenominator : denominator.eval₂ f point ≠ 0) :
    r.denom.eval₂ f point ≠ 0 := by
  intro hCanonical
  exact hDenominator
    (Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero f point hDvd hCanonical)

/-- The subring of rational functions whose canonical denominator is nonzero at `point`. -/
def regularAt (f : K →+* L) (point : L) : Subring (RatFunc K) where
  carrier := {r | r.denom.eval₂ f point ≠ 0}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    intro first second hFirst hSecond
    exact eval₂_denom_ne_zero_of_dvd (RatFunc.denom_add_dvd first second)
      (by simpa using mul_ne_zero hFirst hSecond)
  mul_mem' := by
    intro first second hFirst hSecond
    exact eval₂_denom_ne_zero_of_dvd (RatFunc.denom_mul_dvd first second)
      (by simpa using mul_ne_zero hFirst hSecond)
  neg_mem' := by
    intro r hRegular
    apply eval₂_denom_ne_zero_of_dvd
      ((RatFunc.denom_dvd r.denom_ne_zero).2 ?_) hRegular
    refine ⟨-r.num, ?_⟩
    rw [map_neg, neg_div, RatFunc.num_div_denom]

/-- Evaluation of rational functions regular at `point`, as a ring homomorphism. -/
noncomputable def evalRegularAt (f : K →+* L) (point : L) : regularAt f point →+* L where
  toFun := fun r => RatFunc.eval (K := K) f point r.1
  map_zero' := RatFunc.eval_zero f point
  map_one' := RatFunc.eval_one f point
  map_add' := fun first second =>
    RatFunc.eval_add f point first.2 second.2
  map_mul' := fun first second =>
    RatFunc.eval_mul f point first.2 second.2

@[simp]
lemma evalRegularAt_apply (f : K →+* L) (point : L) (r : regularAt f point) :
    evalRegularAt f point r = RatFunc.eval (K := K) f point r.1 := rfl

end RationalFunction

/-!

## B. Normalized polynomial coefficients

-/

/-- Executable polynomial coefficients, constant term first and with no trailing zero. -/
structure PolynomialCoefficients (K : Type*) [Zero K] where
  /-- Coefficients in ascending powers of the distinguished variable. -/
  coefficients : List K
  /-- Every nonempty coefficient list ends in a nonzero coefficient. -/
  normalized : ∀ h : coefficients ≠ [], coefficients.getLast h ≠ 0

namespace PolynomialCoefficients

variable {K L : Type u}

/-- Two normalized coefficient presentations are equal when their stored lists are equal. -/
@[ext]
lemma ext [Zero K] {first second : PolynomialCoefficients K}
    (h : first.coefficients = second.coefficients) : first = second := by
  cases first
  cases second
  simp_all

instance [Zero K] [DecidableEq K] : DecidableEq (PolynomialCoefficients K) :=
  fun first second =>
    if h : first.coefficients = second.coefficients then isTrue (ext h)
    else isFalse fun hEqual => h (congrArg coefficients hEqual)

/-- Remove every trailing zero from a little-endian coefficient list. -/
def ofList [Zero K] [DecidableEq K] (coefficients : List K) : PolynomialCoefficients K where
  coefficients := coefficients.rdropWhile (· == 0)
  normalized := by
    intro hNonempty
    have hLast := List.rdropWhile_last_not (fun coefficient : K => coefficient == 0)
      coefficients hNonempty
    simpa using hLast

@[simp]
lemma ofList_coefficients [Zero K] [DecidableEq K] (coefficients : List K) :
    (ofList coefficients).coefficients = coefficients.rdropWhile (· == 0) := rfl

/-- Normalizing the coefficients of an already normalized presentation changes nothing. -/
@[simp]
lemma ofList_coefficients_eq [Zero K] (p : PolynomialCoefficients K) [DecidableEq K] :
    ofList p.coefficients = p := by
  apply ext
  exact List.rdropWhile_eq_self_iff.mpr fun hNonempty => by
    simpa using p.normalized hNonempty

instance [Zero K] [DecidableEq K] : Zero (PolynomialCoefficients K) :=
  ⟨ofList []⟩

instance [Zero K] [One K] [DecidableEq K] : One (PolynomialCoefficients K) :=
  ⟨ofList [1]⟩

@[simp]
lemma zero_coefficients [Zero K] [DecidableEq K] :
    (0 : PolynomialCoefficients K).coefficients = [] := rfl

@[simp]
lemma one_coefficients [Zero K] [One K] [NeZero (1 : K)] [DecidableEq K] :
    (1 : PolynomialCoefficients K).coefficients = [1] := by
  change [1].rdropWhile (· == (0 : K)) = [1]
  rw [List.rdropWhile_singleton, if_neg]
  simp

/-- The normalized coefficient presentation of a constant polynomial. -/
def constant [Zero K] [DecidableEq K] (coefficient : K) : PolynomialCoefficients K :=
  ofList [coefficient]

/-- The normalized coefficient presentation of the distinguished variable. -/
def X [Zero K] [One K] [DecidableEq K] : PolynomialCoefficients K :=
  ofList [0, 1]

/-- Interpret normalized coefficients as a polynomial in the distinguished variable. -/
noncomputable def toPolynomial [Semiring K] (p : PolynomialCoefficients K) : Polynomial K :=
  p.coefficients.foldr
    (fun coefficient polynomial => Polynomial.C coefficient + polynomial * Polynomial.X) 0

/-- Executable Horner evaluation of a normalized coefficient list. -/
def eval [Semiring K] [Semiring L] (f : K →+* L) (point : L)
    (p : PolynomialCoefficients K) : L :=
  p.coefficients.foldr (fun coefficient value => f coefficient + value * point) 0

private lemma coeff_foldr_polynomial [Semiring K] (coefficients : List K) (degree : ℕ) :
    (coefficients.foldr
      (fun coefficient polynomial => Polynomial.C coefficient + polynomial * Polynomial.X)
      0).coeff degree = coefficients.getD degree 0 := by
  induction coefficients generalizing degree with
  | nil => simp
  | cons coefficient coefficients ih =>
      cases degree with
      | zero => simp
      | succ degree => simpa using ih degree

/-- Polynomial interpretation reads exactly the stored coefficient at every degree. -/
lemma coeff_toPolynomial [Semiring K] (p : PolynomialCoefficients K) (degree : ℕ) :
    p.toPolynomial.coeff degree = p.coefficients.getD degree 0 :=
  coeff_foldr_polynomial p.coefficients degree

/-- A nonempty normalized coefficient list denotes a nonzero polynomial. -/
lemma toPolynomial_ne_zero_of_coefficients_ne_nil [Semiring K]
    (p : PolynomialCoefficients K) (hNonempty : p.coefficients ≠ []) :
    p.toPolynomial ≠ 0 := by
  let degree := p.coefficients.length - 1
  have hLength : 0 < p.coefficients.length := List.length_pos_iff_ne_nil.mpr hNonempty
  have hDegree : degree < p.coefficients.length := by
    dsimp only [degree]
    omega
  have hCoefficient : p.coefficients.getD degree 0 ≠ 0 := by
    rw [List.getD_eq_getElem p.coefficients 0 hDegree]
    simpa only [degree, List.getLast_eq_getElem] using p.normalized hNonempty
  intro hZero
  apply hCoefficient
  rw [← p.coeff_toPolynomial degree, hZero]
  simp

/-- Horner evaluation agrees with evaluation of the polynomial interpretation. -/
lemma eval_toPolynomial [Semiring K] [Semiring L] (f : K →+* L) (point : L)
    (p : PolynomialCoefficients K) :
    p.toPolynomial.eval₂ f point = p.eval f point := by
  unfold toPolynomial eval
  induction p.coefficients with
  | nil => simp
  | cons coefficient coefficients ih =>
      simp [ih]

@[simp]
lemma eval_zero [Semiring K] [Semiring L] [DecidableEq K]
    (f : K →+* L) (point : L) :
    (0 : PolynomialCoefficients K).eval f point = 0 := rfl

@[simp]
lemma eval_one [Semiring K] [Semiring L] [NeZero (1 : K)] [DecidableEq K]
    (f : K →+* L) (point : L) :
    (1 : PolynomialCoefficients K).eval f point = 1 := by
  unfold eval
  rw [one_coefficients]
  simp

@[simp]
lemma toPolynomial_zero [Semiring K] [DecidableEq K] :
    (0 : PolynomialCoefficients K).toPolynomial = 0 := rfl

@[simp]
lemma toPolynomial_one [Semiring K] [NeZero (1 : K)] [DecidableEq K] :
    (1 : PolynomialCoefficients K).toPolynomial = 1 := by
  unfold toPolynomial
  rw [one_coefficients]
  simp

end PolynomialCoefficients

/-!

## C. Unreduced rational coefficients

-/

/-- An executable unreduced rational function with normalized numerator and denominator lists. -/
structure RationalCoefficients (K : Type*) [Zero K] [DecidableEq K] where
  /-- The normalized numerator coefficients. -/
  numerator : PolynomialCoefficients K
  /-- The normalized, nonempty denominator coefficients. -/
  denominator : PolynomialCoefficients K
  /-- The stored denominator polynomial is not the zero coefficient list. -/
  denominator_nonempty : denominator.coefficients ≠ []

namespace RationalCoefficients

variable {K L : Type u}

/-- Rational coefficient presentations are equal when both stored polynomial lists are equal. -/
@[ext]
lemma ext [Zero K] [DecidableEq K] {first second : RationalCoefficients K}
    (hNumerator : first.numerator = second.numerator)
    (hDenominator : first.denominator = second.denominator) : first = second := by
  cases first
  cases second
  simp_all

instance [Zero K] [DecidableEq K] : DecidableEq (RationalCoefficients K) :=
  fun first second =>
    if hNumerator : first.numerator = second.numerator then
      if hDenominator : first.denominator = second.denominator then
        isTrue (ext hNumerator hDenominator)
      else isFalse fun hEqual => hDenominator (congrArg denominator hEqual)
    else isFalse fun hEqual => hNumerator (congrArg numerator hEqual)

/-- Normalize two raw lists and reject a zero denominator. -/
def ofLists? [Zero K] [DecidableEq K]
    (numerator denominator : List K) : Option (RationalCoefficients K) :=
  let normalizedNumerator := PolynomialCoefficients.ofList numerator
  let normalizedDenominator := PolynomialCoefficients.ofList denominator
  if h : normalizedDenominator.coefficients = [] then none
  else some ⟨normalizedNumerator, normalizedDenominator, h⟩

instance [Zero K] [One K] [NeZero (1 : K)] [DecidableEq K] :
    Zero (RationalCoefficients K) where
  zero :=
    { numerator := 0
      denominator := 1
      denominator_nonempty := by simp }

instance [Zero K] [One K] [NeZero (1 : K)] [DecidableEq K] :
    One (RationalCoefficients K) where
  one :=
    { numerator := 1
      denominator := 1
      denominator_nonempty := by simp }

@[simp]
lemma zero_numerator [Zero K] [One K] [NeZero (1 : K)] [DecidableEq K] :
    (0 : RationalCoefficients K).numerator = 0 := rfl

@[simp]
lemma zero_denominator [Zero K] [One K] [NeZero (1 : K)] [DecidableEq K] :
    (0 : RationalCoefficients K).denominator = 1 := rfl

@[simp]
lemma one_numerator [Zero K] [One K] [NeZero (1 : K)] [DecidableEq K] :
    (1 : RationalCoefficients K).numerator = 1 := rfl

@[simp]
lemma one_denominator [Zero K] [One K] [NeZero (1 : K)] [DecidableEq K] :
    (1 : RationalCoefficients K).denominator = 1 := rfl

/-- Evaluate the stored numerator and denominator directly by Horner recursion. -/
def evalAt [Field K] [Field L] [DecidableEq K]
    (r : RationalCoefficients K) (f : K →+* L) (point : L) : L :=
  r.numerator.eval f point / r.denominator.eval f point

/-- The stored denominator, before any rational-function cancellation, is nonzero at `point`. -/
def StoredDenominatorNonzeroAt [Field K] [Field L] [DecidableEq K]
    (r : RationalCoefficients K) (f : K →+* L) (point : L) : Prop :=
  r.denominator.eval f point ≠ 0

instance [Field K] [Field L] [DecidableEq K] [DecidableEq L] (f : K →+* L) (point : L)
    (r : RationalCoefficients K) : Decidable (r.StoredDenominatorNonzeroAt f point) :=
  inferInstanceAs (Decidable (r.denominator.eval f point ≠ 0))

@[simp]
lemma evalAt_zero [Field K] [Field L] [DecidableEq K] (f : K →+* L) (point : L) :
    (0 : RationalCoefficients K).evalAt f point = 0 := by
  simp [evalAt]

@[simp]
lemma evalAt_one [Field K] [Field L] [DecidableEq K] (f : K →+* L) (point : L) :
    (1 : RationalCoefficients K).evalAt f point = 1 := by
  simp [evalAt]

@[simp]
lemma storedDenominatorNonzeroAt_zero [Field K] [Field L] [DecidableEq K]
    (f : K →+* L) (point : L) :
    (0 : RationalCoefficients K).StoredDenominatorNonzeroAt f point := by
  simp [StoredDenominatorNonzeroAt]

@[simp]
lemma storedDenominatorNonzeroAt_one [Field K] [Field L] [DecidableEq K]
    (f : K →+* L) (point : L) :
    (1 : RationalCoefficients K).StoredDenominatorNonzeroAt f point := by
  simp [StoredDenominatorNonzeroAt]

/-!

## D. Guarded rational-function interpretation

-/

variable [Field K] [DecidableEq K]

/-- Interpret executable coefficients as an element of the rational-function field. -/
noncomputable def toRatFunc (r : RationalCoefficients K) : RatFunc K :=
  RatFunc.mk r.numerator.toPolynomial r.denominator.toPolynomial

/-- The stored denominator has a nonzero polynomial interpretation. -/
lemma denominator_toPolynomial_ne_zero (r : RationalCoefficients K) :
    r.denominator.toPolynomial ≠ 0 :=
  r.denominator.toPolynomial_ne_zero_of_coefficients_ne_nil r.denominator_nonempty

@[simp]
lemma toRatFunc_zero : toRatFunc (0 : RationalCoefficients K) = 0 := by
  rw [toRatFunc, RatFunc.mk_eq_div]
  simp

@[simp]
lemma toRatFunc_one : toRatFunc (1 : RationalCoefficients K) = 1 := by
  rw [toRatFunc, RatFunc.mk_eq_div]
  simp

/-- A nonzero stored denominator forces the canonical `RatFunc` denominator to be nonzero there. -/
lemma canonicalDenominatorNonzeroAt [Field L] (f : K →+* L) (point : L)
    (r : RationalCoefficients K) (hStored : r.StoredDenominatorNonzeroAt f point) :
    r.toRatFunc.denom.eval₂ f point ≠ 0 := by
  apply RationalFunction.eval₂_denom_ne_zero_of_dvd
    ((RatFunc.denom_dvd r.denominator_toPolynomial_ne_zero).2 ?_)
  · change r.denominator.eval f point ≠ 0 at hStored
    simpa only [r.denominator.eval_toPolynomial f point] using hStored
  · refine ⟨r.numerator.toPolynomial, ?_⟩
    exact RatFunc.mk_eq_div _ _

/-- Guarded direct evaluation agrees with Mathlib's canonical rational-function evaluation. -/
lemma ratFunc_eval_eq_evalAt [Field L] (f : K →+* L) (point : L)
    (r : RationalCoefficients K) (hStored : r.StoredDenominatorNonzeroAt f point) :
    RatFunc.eval (K := K) f point r.toRatFunc = r.evalAt f point := by
  have hDenominator := r.denominator_toPolynomial_ne_zero
  have hCanonical := r.canonicalDenominatorNonzeroAt f point hStored
  have hFraction : r.toRatFunc =
      algebraMap (Polynomial K) (RatFunc K) r.numerator.toPolynomial /
        algebraMap (Polynomial K) (RatFunc K) r.denominator.toPolynomial :=
    RatFunc.mk_eq_div _ _
  have hCross : r.toRatFunc.num * r.denominator.toPolynomial =
      r.numerator.toPolynomial * r.toRatFunc.denom :=
    (RatFunc.num_mul_eq_mul_denom_iff hDenominator).2 hFraction
  have hEvaluated := congrArg (Polynomial.eval₂ f point) hCross
  simp only [Polynomial.eval₂_mul] at hEvaluated
  rw [r.numerator.eval_toPolynomial f point,
    r.denominator.eval_toPolynomial f point] at hEvaluated
  change r.denominator.eval f point ≠ 0 at hStored
  rw [RatFunc.eval, evalAt]
  exact (div_eq_div_iff hCanonical hStored).2 hEvaluated

/-- Regard guarded executable coefficients as a rational function regular at the point. -/
noncomputable def toRegularAt [Field L] (f : K →+* L) (point : L)
    (r : RationalCoefficients K) (hStored : r.StoredDenominatorNonzeroAt f point) :
    RationalFunction.regularAt f point :=
  ⟨r.toRatFunc, r.canonicalDenominatorNonzeroAt f point hStored⟩

lemma evalRegularAt_toRegularAt [Field L] (f : K →+* L) (point : L)
    (r : RationalCoefficients K) (hStored : r.StoredDenominatorNonzeroAt f point) :
    RationalFunction.evalRegularAt f point (r.toRegularAt f point hStored) =
      r.evalAt f point :=
  r.ratFunc_eval_eq_evalAt f point hStored

end RationalCoefficients

end Physlib
