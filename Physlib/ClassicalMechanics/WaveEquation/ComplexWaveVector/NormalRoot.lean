/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.ClassicalMechanics.WaveEquation.ComplexWaveVector.Hyperplane

/-!
# Real-radicand normal roots of complex wave vectors

## i. Overview

This file classifies the complex normal component of a wave vector when its square is a real
number. A nonnegative radicand gives the two real alternatives `±√c`; a nonpositive radicand
gives the two imaginary alternatives `±I * √(-c)`. At zero all alternatives agree with the
unique zero normal component.

These results classify algebraic roots only. They choose no preferred sign and assign no medium,
interface wave role, propagation, grazing, evanescence, group velocity, energy flux, outgoing, or
power meaning.

## ii. Key results

- `normalComponent_eq_sqrt_or_eq_neg_sqrt_of_sq_eq_of_nonneg`: the nonnegative-radicand roots.
- `normalComponent_eq_zero_of_sq_eq_zero`: the unique zero root.
- `normalComponent_eq_I_mul_sqrt_or_eq_neg_I_mul_sqrt_of_sq_eq_of_nonpos`: the
  nonpositive-radicand roots.

## iii. Table of contents

- A. Nonnegative radicands
- B. Zero radicand
- C. Nonpositive radicands

## iv. References

The proofs combine Physlib's complex hyperplane-normal component with Mathlib's real square root
and two-root classification in an integral domain. No external formal-development source is copied
or translated here.
-/

@[expose] public section

namespace ClassicalMechanics

open Space

noncomputable section

namespace ComplexWaveVector

variable {d : ℕ}

/-!

## A. Nonnegative radicands

-/

/-- If a complex wave vector's squared hyperplane-normal component is a nonnegative real number,
then the normal component is its positive or negative real square root. The alternatives coincide
when the radicand is zero. -/
lemma normalComponent_eq_sqrt_or_eq_neg_sqrt_of_sq_eq_of_nonneg
    (plane : OrientedAffineHyperplane d) (z : ComplexWaveVector d) (radicand : ℝ)
    (hSquare : hyperplaneNormalComponent plane z ^ 2 = (radicand : ℂ))
    (hRadicand : 0 ≤ radicand) :
    hyperplaneNormalComponent plane z = (Real.sqrt radicand : ℂ) ∨
      hyperplaneNormalComponent plane z = -(Real.sqrt radicand : ℂ) := by
  have hRootSquare : (Real.sqrt radicand : ℂ) ^ 2 = (radicand : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hRadicand]
  exact eq_or_eq_neg_of_sq_eq_sq _ _ (hSquare.trans hRootSquare.symm)

/-!

## B. Zero radicand

-/

/-- A complex wave vector whose squared hyperplane-normal component is zero has zero normal
component.

This records the unique normal-root case needed at a later critical or grazing boundary; by itself
it assigns neither interpretation. -/
lemma normalComponent_eq_zero_of_sq_eq_zero
    (plane : OrientedAffineHyperplane d) (z : ComplexWaveVector d)
    (hSquare : hyperplaneNormalComponent plane z ^ 2 = 0) :
    hyperplaneNormalComponent plane z = 0 := by
  exact sq_eq_zero_iff.mp hSquare

/-!

## C. Nonpositive radicands

-/

/-- If a complex wave vector's squared hyperplane-normal component is a nonpositive real number,
then the normal component is plus or minus `I` times the positive real square root of the negated
radicand. The alternatives coincide when the radicand is zero. -/
lemma normalComponent_eq_I_mul_sqrt_or_eq_neg_I_mul_sqrt_of_sq_eq_of_nonpos
    (plane : OrientedAffineHyperplane d) (z : ComplexWaveVector d) (radicand : ℝ)
    (hSquare : hyperplaneNormalComponent plane z ^ 2 = (radicand : ℂ))
    (hRadicand : radicand ≤ 0) :
    hyperplaneNormalComponent plane z =
        Complex.I * (Real.sqrt (-radicand) : ℂ) ∨
      hyperplaneNormalComponent plane z =
        -(Complex.I * (Real.sqrt (-radicand) : ℂ)) := by
  have hRootSquare :
      (Complex.I * (Real.sqrt (-radicand) : ℂ)) ^ 2 = (radicand : ℂ) := by
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow,
      Real.sq_sqrt (neg_nonneg.mpr hRadicand)]
    simp only [neg_mul, one_mul, Complex.ofReal_neg, neg_neg]
  exact eq_or_eq_neg_of_sq_eq_sq _ _ (hSquare.trans hRootSquare.symm)

end ComplexWaveVector

end
end ClassicalMechanics
