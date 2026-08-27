/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Mathematics.ZTransform.FrequencyResponse

/-!
# Regression tests for Z-transform frequency response

## i. Overview

This file fixes the reciprocal-unit-circle sign with an exact quadrature fixture. The finite-lag
section has feedforward symbol `1 + 2 u` and feedback symbol `u / 2`. At angular frequency
`π / 2`, the Z point is `I`, its reciprocal delay variable is `-I`, and the transfer function is
exactly `-2 I`.

The hostile comparison evaluates the same coefficient primitives with `I` in place of `I⁻¹`.
That opposite-sign delay substitution gives `2 I`, so it cannot equal the transfer function. The
sentinel unfolds the transfer function, delay symbols, unit-circle point, and coefficients rather
than using the production unit-circle expansion.

## ii. Key results

- `Physlib.ZTransform.quadratureUnitCirclePoint`: the exact point at `π / 2`.
- `Physlib.ZTransform.transferFunction_quadrature`: the exact value `-2 I`.
- `Physlib.ZTransform.transferFunction_wrongUnitCircleSign_ne`: the reciprocal-sign sentinel.

## iii. Table of contents

- A. Quadrature coefficient fixture
- B. Exact response and hostile sign sentinel

## iv. References

These are exact algebraic regressions. They assert no frequency band, stability, physical
realization, or existence of a sequence solving the associated recurrence.

-/

@[expose] public section

namespace Physlib.ZTransform

noncomputable section

/-!

## A. Quadrature coefficient fixture

-/

/-- Feedforward coefficients with symbol `1 + 2 u`. -/
def quadratureFeedforward : ℕ → ℂ :=
  fun k => if k = 0 then 1 else if k = 1 then 2 else 0

/-- Feedback coefficients with symbol `u / 2`. -/
def quadratureFeedback : ℕ → ℂ :=
  fun k => if k = 1 then 1 / 2 else 0

/-- The feedforward symbol expands directly from the fixture coefficients. -/
lemma delaySymbol_quadratureFeedforward (u : ℂ) :
    delaySymbol {0, 1} quadratureFeedforward u = 1 + 2 * u := by
  norm_num [delaySymbol, quadratureFeedforward]

/-- The feedback symbol expands directly from the fixture coefficients. -/
lemma delaySymbol_quadratureFeedback (u : ℂ) :
    delaySymbol {1} quadratureFeedback u = u / 2 := by
  norm_num [delaySymbol, quadratureFeedback]
  ring

/-!

## B. Exact response and hostile sign sentinel

-/

/-- Angular frequency `π / 2` gives the exact unit-circle point `I`. -/
lemma quadratureUnitCirclePoint : unitCirclePoint (Real.pi / 2) = Complex.I := by
  rw [unitCirclePoint, Complex.exp_ofReal_mul_I]
  norm_num

private lemma one_add_I_half_ne_zero : 1 + Complex.I * (1 / 2 : ℂ) ≠ 0 := by
  intro h
  have hRe := congrArg Complex.re h
  norm_num at hRe

private lemma one_sub_I_half_ne_zero : 1 - (1 / 2 : ℂ) * Complex.I ≠ 0 := by
  intro h
  have hRe := congrArg Complex.re h
  norm_num at hRe

private lemma two_add_I_ne_zero : (2 : ℂ) + Complex.I ≠ 0 := by
  intro h
  have hRe := congrArg Complex.re h
  norm_num at hRe

private lemma two_sub_I_ne_zero : (2 : ℂ) - Complex.I ≠ 0 := by
  intro h
  have hRe := congrArg Complex.re h
  norm_num at hRe

/-- The quadrature fixture has transfer value `-2 I` at angular frequency `π / 2`. This proof
expands the defining coefficient primitives independently of the production transfer formula. -/
lemma transferFunction_quadrature :
    transferFunction {1} {0, 1} quadratureFeedback quadratureFeedforward
      (unitCirclePoint (Real.pi / 2)) = -2 * Complex.I := by
  rw [transferFunction, quadratureUnitCirclePoint]
  norm_num [delaySymbol, quadratureFeedback, quadratureFeedforward]
  field_simp [one_add_I_half_ne_zero, two_add_I_ne_zero]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Replacing the reciprocal point `I⁻¹ = -I` by `I` reverses the frequency sign and changes the
fixture value. Both sides expand from the primitive transfer and coefficient definitions. -/
lemma transferFunction_wrongUnitCircleSign_ne :
    transferFunction {1} {0, 1} quadratureFeedback quadratureFeedforward
        (unitCirclePoint (Real.pi / 2)) ≠
      delaySymbol {0, 1} quadratureFeedforward (unitCirclePoint (Real.pi / 2)) /
        (1 - delaySymbol {1} quadratureFeedback (unitCirclePoint (Real.pi / 2))) := by
  rw [transferFunction, unitCirclePoint, Complex.exp_ofReal_mul_I]
  norm_num [delaySymbol, quadratureFeedback, quadratureFeedforward]
  intro h
  field_simp [one_add_I_half_ne_zero, one_sub_I_half_ne_zero, two_add_I_ne_zero,
    two_sub_I_ne_zero] at h
  have hIm := congrArg Complex.im h
  norm_num at hIm

end

end Physlib.ZTransform
