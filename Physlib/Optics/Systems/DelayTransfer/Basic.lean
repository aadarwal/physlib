/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.MvPolynomial

/-!
# Formal delay variables and rational models

## i. Overview

A finite-delay optical model first treats every delay factor as an independent formal variable.
For `n` declared delays, `DelayTuple n` is an assignment of complex values to those variables,
`DelayPolynomial n` is the corresponding multivariate polynomial ring, and `DelayRational n` is
its fraction field.

`RationalModel` retains an explicit numerator and denominator for a fraction-field element. This
presentation is intentional: evaluation of an abstract fraction field cannot be a global ring map
at a point where a nonzero polynomial becomes zero. The retained denominator therefore supplies
the exact pointwise `evaluationDomain`, while `toRational` records the represented element of the
polynomial quotient field.

The physical substitutions are separate named maps. `laplaceEvaluation delays s` sends the
`i`-th formal variable to `exp (-s * delays i)`. `zInverseEvaluation z` sends the single formal
delay to `z⁻¹`. Neither definition identifies Laplace frequency, discrete `z`, or physical
angular frequency.

## ii. Key definitions and results

- `DelayTuple`: an assignment to a finite family of formal delay variables.
- `DelayPolynomial`, `DelayRational`: the polynomial ring and its fraction field.
- `formalDelay`: the fraction-field image of one polynomial indeterminate.
- `RationalModel`: an explicit regularity-auditable presentation of a rational function.
- `RationalModel.evaluationDomain`: points where the retained denominator is nonzero.
- `laplaceEvaluation`: the substitution `q_i = exp (-s * τ_i)`.
- `zInverseEvaluation`: the one-delay substitution `q = z⁻¹`.

## iii. Table of contents

- A. Formal delay variables
- B. Rational presentations and their evaluation domains
- C. Laplace and reciprocal-z substitutions

## iv. References and non-claims

This module implements the convention required by `goal.md` section E.8 and section H.4 S4.
It is source-neutral. Delay variables are formal, and no declaration says that a rational function
of them is rational in physical frequency. Such a statement would require a separate propagation
and dispersion model. No pole, zero, resonance, stability, causality, or global phase claim is
made here.
-/

@[expose] public section

namespace Optics.DelayTransfer

noncomputable section

/-!

## A. Formal delay variables

-/

/-- An assignment of complex values to `n` independent formal delay variables. -/
abbrev DelayTuple (n : ℕ) := Fin n → ℂ

/-- Multivariate complex polynomials in `n` independent formal delay variables. -/
abbrev DelayPolynomial (n : ℕ) := MvPolynomial (Fin n) ℂ

/-- The fraction field of multivariate complex delay polynomials. -/
abbrev DelayRational (n : ℕ) := FractionRing (DelayPolynomial n)

/-- The `i`-th formal delay indeterminate in the multivariate fraction field. -/
def formalDelay {n : ℕ} (i : Fin n) : DelayRational n :=
  algebraMap (DelayPolynomial n) (DelayRational n) (MvPolynomial.X i)

/-!

## B. Rational presentations and their evaluation domains

-/

/-- A rational delay function with an explicit polynomial numerator and denominator.

The explicit presentation determines the pointwise evaluation domain. `toRational` maps it to the
actual fraction field, so this is not a replacement equality notion for rational functions.
-/
structure RationalModel (n : ℕ) where
  /-- The retained numerator polynomial. -/
  numerator : DelayPolynomial n
  /-- The retained denominator polynomial. -/
  denominator : DelayPolynomial n
  /-- The retained denominator is nonzero as a formal polynomial. -/
  denominator_ne_zero : denominator ≠ 0

namespace RationalModel

variable {n : ℕ}

/-- The fraction-field element represented by an explicit rational model. -/
def toRational (model : RationalModel n) : DelayRational n :=
  algebraMap (DelayPolynomial n) (DelayRational n) model.numerator /
    algebraMap (DelayPolynomial n) (DelayRational n) model.denominator

/-- The pointwise domain on which the retained denominator evaluates nontrivially. -/
def evaluationDomain (model : RationalModel n) : Set (DelayTuple n) :=
  {value | MvPolynomial.eval value model.denominator ≠ 0}

/-- Totalized evaluation of the retained numerator and denominator.

Only values in `evaluationDomain` carry rational-function meaning; outside it, division uses the
field's total inverse and no transfer-function interpretation is asserted.
-/
def eval (model : RationalModel n) (value : DelayTuple n) : ℂ :=
  MvPolynomial.eval value model.numerator /
    MvPolynomial.eval value model.denominator

/-- Membership of the evaluation domain is exactly nonvanishing of the retained denominator. -/
lemma mem_evaluationDomain_iff (model : RationalModel n) (value : DelayTuple n) :
    value ∈ model.evaluationDomain ↔
      MvPolynomial.eval value model.denominator ≠ 0 := Iff.rfl

/-- Evaluation expands to the retained numerator divided by the retained denominator. -/
lemma eval_eq (model : RationalModel n) (value : DelayTuple n) :
    model.eval value =
      MvPolynomial.eval value model.numerator /
        MvPolynomial.eval value model.denominator := rfl

/-- A polynomial viewed as a rational model with denominator one. -/
def ofPolynomial (polynomial : DelayPolynomial n) : RationalModel n where
  numerator := polynomial
  denominator := 1
  denominator_ne_zero := one_ne_zero

/-- A constant rational model. -/
def constant (constant : ℂ) : RationalModel n :=
  ofPolynomial (MvPolynomial.C constant)

/-- The rational model of the `i`-th formal delay variable. -/
def indeterminate (i : Fin n) : RationalModel n :=
  ofPolynomial (MvPolynomial.X i)

/-- A polynomial rational model is regular at every delay assignment. -/
lemma evaluationDomain_ofPolynomial (polynomial : DelayPolynomial n) :
    (ofPolynomial polynomial).evaluationDomain = Set.univ := by
  ext value
  simp [evaluationDomain, ofPolynomial]

/-- Evaluating a polynomial rational model is ordinary multivariate evaluation. -/
@[simp]
lemma eval_ofPolynomial (polynomial : DelayPolynomial n) (value : DelayTuple n) :
    (ofPolynomial polynomial).eval value = MvPolynomial.eval value polynomial := by
  simp [eval, ofPolynomial]

/-- Evaluating a constant rational model returns that constant. -/
@[simp]
lemma eval_constant (c : ℂ) (value : DelayTuple n) :
    (constant c).eval value = c := by
  simp [constant]

/-- Evaluating the `i`-th rational variable selects the `i`-th assigned delay value. -/
@[simp]
lemma eval_indeterminate (i : Fin n) (value : DelayTuple n) :
    (indeterminate i).eval value = value i := by
  simp [indeterminate]

/-- The rational value of the explicit variable model is the formal delay indeterminate. -/
lemma toRational_indeterminate (i : Fin n) :
    (indeterminate i).toRational = formalDelay i := by
  simp [toRational, indeterminate, ofPolynomial, formalDelay]

end RationalModel

/-!

## C. Laplace and reciprocal-z substitutions

-/

/-- Evaluation of formal delays at `q_i = exp (-s * τ_i)` for real delay data `τ`. -/
def laplaceEvaluation {n : ℕ} (delays : Fin n → ℝ) (s : ℂ) : DelayTuple n :=
  fun i => Complex.exp (-s * (delays i : ℂ))

/-- The Laplace substitution evaluates each coordinate at its declared exponential delay. -/
lemma laplaceEvaluation_apply {n : ℕ} (delays : Fin n → ℝ) (s : ℂ) (i : Fin n) :
    laplaceEvaluation delays s i = Complex.exp (-s * (delays i : ℂ)) := rfl

/-- Evaluation of one formal delay using the convention `q = z⁻¹`. -/
def zInverseEvaluation (z : ℂ) : DelayTuple 1 :=
  fun _ => z⁻¹

/-- The unique coordinate of the reciprocal-z substitution is `z⁻¹`. -/
lemma zInverseEvaluation_apply (z : ℂ) (i : Fin 1) :
    zInverseEvaluation z i = z⁻¹ := rfl

end

end Optics.DelayTransfer
