/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
/-!

# The complete elliptic integral of the first kind

This file may eventually be upstreamed to Mathlib.

## i. Overview

Legendre's complete elliptic integral of the first kind is, in the parameter convention,

`K(m) = ∫ φ in 0..π/2, (1 - m sin² φ) ^ (-1/2)`

(Abramowitz & Stegun 17.3.1). The physics literature more often uses the modulus convention and
writes `K(k)`, as Landau & Lifshitz do, for what is here `completeEllipticK (k ^ 2)`; the two
conventions are related by `m = k²`. Mathlib knows the Weierstrass elliptic function `℘`
(`PeriodPair.weierstrassP`) but has no Legendre-form elliptic integrals; this file defines the
complete integral of the first kind and develops its basic theory on the domain `m < 1`, where
the radicand `1 - m sin² φ` is positive and the integrand continuous.

For `m ≥ 1` the definition still elaborates, but its value is a junk value. At `m = 1` the
integrand agrees with `1 / cos φ` on `[0, π/2)`, which is not interval integrable, so the
integral is `0` by `intervalIntegral.integral_undef`. For `m > 1` the radicand becomes negative
near `φ = π/2`, where the real power at exponent `-(1/2)` of a negative base vanishes
(`Real.rpow_def_of_neg` supplies the factor `cos (-(π / 2)) = 0`), so the value is a finite
number unrelated to Legendre's divergent integral. Every lemma of this file therefore carries
its domain hypothesis `m < 1` explicitly.

## ii. Key results

- `completeEllipticK` : the complete elliptic integral of the first kind, as a function of
  the parameter `m`.
- `completeEllipticK_integrand_pos` : for `m < 1` the radicand `1 - m sin² φ` is positive.
- `continuous_completeEllipticK_integrand` : for `m < 1` the integrand is continuous.
- `completeEllipticK_intervalIntegrable` : for `m < 1` the integrand is interval integrable
  on `[0, π/2]`.
- `completeEllipticK_zero` : `K 0 = π / 2`.
- `completeEllipticK_pos` : for `m < 1` the integral is positive.

## iii. Table of contents

- A. Definition and the integrand
- B. Value at zero and positivity

## iv. References

- M. Abramowitz, I. A. Stegun, Handbook of Mathematical Functions, §17.3 (the parameter
  convention, 17.3.1).
- Landau & Lifshitz, Mechanics, 3rd ed., §11 (the pendulum period as `K(k)`, in the modulus
  convention).

-/

@[expose] public section

open MeasureTheory

namespace Real

/-!

## A. Definition and the integrand

The integral is defined for every real parameter `m`; on the domain `m < 1` the radicand is
positive, so the integrand is continuous and interval integrable.

-/

/-- The complete elliptic integral of the first kind in the parameter convention,
`K(m) = ∫ φ in 0..π/2, (1 - m sin² φ) ^ (-1/2)`. The physics literature often writes `K(k)`
with `m = k²`. For `m ≥ 1` the value is a junk value: see the module docstring. -/
noncomputable def completeEllipticK (m : ℝ) : ℝ :=
  ∫ φ in (0 : ℝ)..π / 2, (1 - m * sin φ ^ 2) ^ (-(1 / 2 : ℝ))

/-- For `m < 1` the radicand `1 - m sin² φ` of the integrand of `completeEllipticK m` is
positive at every angle `φ`. -/
lemma completeEllipticK_integrand_pos {m : ℝ} (hm : m < 1) (φ : ℝ) :
    0 < 1 - m * sin φ ^ 2 := by
  have hs0 : (0 : ℝ) ≤ sin φ ^ 2 := sq_nonneg _
  have hs1 : sin φ ^ 2 ≤ 1 := sin_sq_le_one φ
  rcases le_or_gt m 0 with hm0 | hm0
  · nlinarith
  · nlinarith

/-- For `m < 1` the integrand of `completeEllipticK m` is continuous, the real power being
taken at a positive base. -/
lemma continuous_completeEllipticK_integrand {m : ℝ} (hm : m < 1) :
    Continuous fun φ : ℝ => (1 - m * sin φ ^ 2) ^ (-(1 / 2 : ℝ)) := by
  refine Continuous.rpow_const ?_ fun φ => Or.inl (completeEllipticK_integrand_pos hm φ).ne'
  fun_prop

/-- For `m < 1` the integrand of `completeEllipticK m` is interval integrable on `[0, π/2]`. -/
lemma completeEllipticK_intervalIntegrable {m : ℝ} (hm : m < 1) :
    IntervalIntegrable (fun φ : ℝ => (1 - m * sin φ ^ 2) ^ (-(1 / 2 : ℝ))) volume 0 (π / 2) :=
  (continuous_completeEllipticK_integrand hm).intervalIntegrable 0 (π / 2)

/-!

## B. Value at zero and positivity

At `m = 0` the integrand is the constant `1` and the integral is elementary; for `m < 1` the
integral is positive, being the integral of a positive continuous function.

-/

/-- `K 0 = π / 2`: at parameter zero the integrand of `completeEllipticK` is the constant `1`. -/
@[simp]
lemma completeEllipticK_zero : completeEllipticK 0 = π / 2 := by
  simp [completeEllipticK]

/-- For `m < 1` the complete elliptic integral `completeEllipticK m` is positive. -/
lemma completeEllipticK_pos {m : ℝ} (hm : m < 1) : 0 < completeEllipticK m := by
  refine intervalIntegral.intervalIntegral_pos_of_pos_on
    (completeEllipticK_intervalIntegrable hm) (fun φ _ => ?_) pi_div_two_pos
  exact rpow_pos_of_pos (completeEllipticK_integrand_pos hm φ) _

end Real
