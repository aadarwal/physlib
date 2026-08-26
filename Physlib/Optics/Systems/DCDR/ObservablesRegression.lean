/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Systems.DCDR.Observables
public import Physlib.Optics.Systems.DCDR.PolesRegression

/-!
# Exact zero-location regressions for the double-coupler double-ring

## i. Overview

This file gives the coherent DCDR zero-location observable a nonvacuous positive fixture and a
strict-boundary negative fixture. Both use the coherent N7 coupler with `t = 3/5`, `k = 4/5`
from `PolesRegression.lean`. The positive response has numerator `4*q - q^3`, hence finite
reciprocal-coordinate zeros `z = ±1/2`. The boundary response has numerator `q - q^3`, hence
the finite zero `z = 1` and fails the strict all-zeros condition.

Every response polynomial, Bezout identity, reciprocal root, and norm bound is expanded directly
from the rational data. The positive and negative conclusions do not use
`printedIncoherent_allZerosInsideUnitDisk_of_strict` or any other observable result. Thus the
negative fixture can fail if the coefficients or strictness change.

The separately printed incoherent FMICS'15 Theorem 5 assumptions are also checked at a boundary
point. All three printed assumptions hold, including the two nonzero hypotheses discovered by the
paper, while the strict conclusion fails. This records the paper's non-strict/strict mismatch; it
does not re-credit the two nonzero hypotheses to Physlib and does not identify the printed model
with the coherent fixtures.

## ii. Key definitions and results

- `insideZerosParameters`: coherent response with finite zeros at `±1/2`.
- `insideZerosResponseReduction_allZerosInsideUnitDisk`: direct positive anchor.
- `boundaryZerosParameters`: coherent response with a finite zero at `1`.
- `boundaryZerosResponseReduction_not_allZerosInsideUnitDisk`: required failing check.
- `printedIncoherentTheoremFiveConditions_boundary`: all printed assumptions hold at the boundary.
- `printedIncoherentAllZerosInsideUnitDisk_boundary_fails`: the strict conclusion fails there.

## iii. Table of contents

- A. Exact coherent parameter fixtures
- B. Hand-expanded rational data
- C. Explicit coprime reductions
- D. Direct coherent zero-location anchors
- E. Printed incoherent strictness boundary

## iv. References and non-claims

U. Siddique, S. M. Beillahi, and S. Tahar, "On the Formal Analysis of Photonic Signal
Processing Systems", FMICS 2015, LNCS 9128, Definition 7 and Theorem 5.

No statement calls the zero-location condition "resonance". This file introduces neither
normalized-modal power nor electromagnetic power; no E3b power bridge is used. It supplies no
physical-frequency, passivity, BIBO, coherent/incoherent equivalence, or material-model claim and
gives no causality or time-domain interpretation.
-/

@[expose] public section

namespace Optics.DCDR

noncomputable section

open Polynomial

/-!

## A. Exact coherent parameter fixtures

-/

/-- Coherent parameters whose selected numerator is `4*q - q^3`. -/
def insideZerosParameters : UnitDelayParameters where
  firstCoupler := poleRegressionCoupler
  secondCoupler := poleRegressionCoupler
  upperGain := 20
  lowerGain := 5
  feedbackGain := 1 / 100

/-- Coherent parameters whose selected numerator is `q - q^3`. -/
def boundaryZerosParameters : UnitDelayParameters where
  firstCoupler := poleRegressionCoupler
  secondCoupler := poleRegressionCoupler
  upperGain := 41 / 9
  lowerGain := 1
  feedbackGain := 9 / 41

/-- The positive zero-location fixture has nonnegative formal gains. -/
lemma insideZerosParameters_isAdmissible :
    insideZerosParameters.IsAdmissible := by
  norm_num [UnitDelayParameters.IsAdmissible, insideZerosParameters]

/-- The strict-boundary fixture has nonnegative formal gains. -/
lemma boundaryZerosParameters_isAdmissible :
    boundaryZerosParameters.IsAdmissible := by
  norm_num [UnitDelayParameters.IsAdmissible, boundaryZerosParameters]

/-!

## B. Hand-expanded rational data

-/

/-- The positive fixture's directly expanded numerator. -/
def insideZerosNumerator : Polynomial ℂ :=
  C 4 * X - X ^ 3

/-- The positive fixture's directly expanded denominator. -/
def insideZerosDenominator : Polynomial ℂ :=
  1 + C (11 / 100) * X ^ 2

/-- The strict-boundary fixture's directly expanded numerator. -/
def boundaryZerosNumerator : Polynomial ℂ :=
  X - X ^ 3

/-- The strict-boundary fixture's directly expanded denominator. -/
def boundaryZerosDenominator : Polynomial ℂ :=
  1 + C (23 / 41) * X ^ 2

/-- Direct expansion gives the positive fixture's loop polynomial. -/
lemma insideZeros_loopPolynomial_expansion :
    insideZerosParameters.loopPolynomial = -(C (11 / 100) * X ^ 2) := by
  apply Polynomial.funext
  intro q
  norm_num [UnitDelayParameters.loopPolynomial, UnitDelayParameters.upperPolynomial,
    UnitDelayParameters.lowerPolynomial, UnitDelayParameters.feedbackPolynomial,
    insideZerosParameters, poleRegressionCoupler,
    DirectionalCoupler.crossCoefficient, pow_succ, Complex.I_mul_I]
  ring_nf
  rw [show Complex.I ^ 2 = (-1 : ℂ) by
    norm_num [pow_two, Complex.I_mul_I]]
  ring

/-- Direct expansion gives the positive fixture's denominator. -/
lemma insideZeros_denominatorPolynomial_expansion :
    insideZerosParameters.denominatorPolynomial = insideZerosDenominator := by
  rw [UnitDelayParameters.denominatorPolynomial,
    insideZeros_loopPolynomial_expansion]
  simp [insideZerosDenominator]

/-- Direct expansion of all coherent scalar factors gives the positive numerator. -/
lemma insideZeros_responseNumeratorPolynomial_expansion :
    insideZerosParameters.responseNumeratorPolynomial = insideZerosNumerator := by
  apply Polynomial.funext
  intro q
  norm_num [UnitDelayParameters.responseNumeratorPolynomial,
    UnitDelayParameters.directPolynomial, UnitDelayParameters.denominatorPolynomial,
    UnitDelayParameters.loopPolynomial, UnitDelayParameters.feedbackReadoutPolynomial,
    UnitDelayParameters.feedbackDrivePolynomial, UnitDelayParameters.upperPolynomial,
    UnitDelayParameters.lowerPolynomial, UnitDelayParameters.feedbackPolynomial,
    insideZerosParameters, poleRegressionCoupler,
    DirectionalCoupler.crossCoefficient, insideZerosNumerator, pow_succ,
    Complex.I_mul_I]
  ring_nf
  rw [show Complex.I ^ 2 = (-1 : ℂ) by
      norm_num [pow_two, Complex.I_mul_I],
    show Complex.I ^ 4 = (1 : ℂ) by
      norm_num [pow_succ, Complex.I_mul_I]]
  ring

/-- Direct expansion gives the strict-boundary fixture's loop polynomial. -/
lemma boundaryZeros_loopPolynomial_expansion :
    boundaryZerosParameters.loopPolynomial = -(C (23 / 41) * X ^ 2) := by
  apply Polynomial.funext
  intro q
  norm_num [UnitDelayParameters.loopPolynomial, UnitDelayParameters.upperPolynomial,
    UnitDelayParameters.lowerPolynomial, UnitDelayParameters.feedbackPolynomial,
    boundaryZerosParameters, poleRegressionCoupler,
    DirectionalCoupler.crossCoefficient, pow_succ, Complex.I_mul_I]
  ring_nf
  rw [show Complex.I ^ 2 = (-1 : ℂ) by
    norm_num [pow_two, Complex.I_mul_I]]
  ring

/-- Direct expansion gives the strict-boundary fixture's denominator. -/
lemma boundaryZeros_denominatorPolynomial_expansion :
    boundaryZerosParameters.denominatorPolynomial = boundaryZerosDenominator := by
  rw [UnitDelayParameters.denominatorPolynomial,
    boundaryZeros_loopPolynomial_expansion]
  simp [boundaryZerosDenominator]

/-- Direct expansion of all coherent scalar factors gives the strict-boundary numerator. -/
lemma boundaryZeros_responseNumeratorPolynomial_expansion :
    boundaryZerosParameters.responseNumeratorPolynomial = boundaryZerosNumerator := by
  apply Polynomial.funext
  intro q
  norm_num [UnitDelayParameters.responseNumeratorPolynomial,
    UnitDelayParameters.directPolynomial, UnitDelayParameters.denominatorPolynomial,
    UnitDelayParameters.loopPolynomial, UnitDelayParameters.feedbackReadoutPolynomial,
    UnitDelayParameters.feedbackDrivePolynomial, UnitDelayParameters.upperPolynomial,
    UnitDelayParameters.lowerPolynomial, UnitDelayParameters.feedbackPolynomial,
    boundaryZerosParameters, poleRegressionCoupler,
    DirectionalCoupler.crossCoefficient, boundaryZerosNumerator, pow_succ,
    Complex.I_mul_I]
  ring_nf
  rw [show Complex.I ^ 2 = (-1 : ℂ) by
      norm_num [pow_two, Complex.I_mul_I],
    show Complex.I ^ 4 = (1 : ℂ) by
      norm_num [pow_succ, Complex.I_mul_I]]
  ring

/-!

## C. Explicit coprime reductions

-/

/-- The positive numerator is a nonzero polynomial. -/
lemma insideZerosNumerator_ne_zero : insideZerosNumerator ≠ 0 := by
  intro hZero
  have hEvaluation := congrArg (Polynomial.eval 1) hZero
  norm_num [insideZerosNumerator] at hEvaluation

/-- The positive denominator is a nonzero polynomial. -/
lemma insideZerosDenominator_ne_zero : insideZerosDenominator ≠ 0 := by
  intro hZero
  have hEvaluation := congrArg (Polynomial.eval 0) hZero
  norm_num [insideZerosDenominator] at hEvaluation

/-- An explicit Bezout identity certifies the positive quotient as coprime. -/
lemma insideZerosNumerator_isCoprime :
    IsCoprime insideZerosNumerator insideZerosDenominator := by
  refine ⟨C (-121 / 14400) * X,
    1 - C (11 / 144) * X ^ 2, ?_⟩
  apply Polynomial.funext
  intro q
  norm_num [insideZerosNumerator, insideZerosDenominator]
  ring

/-- The strict-boundary numerator is a nonzero polynomial. -/
lemma boundaryZerosNumerator_ne_zero : boundaryZerosNumerator ≠ 0 := by
  intro hZero
  have hCoefficient := congrArg (fun polynomial => polynomial.coeff 1) hZero
  norm_num [boundaryZerosNumerator] at hCoefficient

/-- The strict-boundary denominator is a nonzero polynomial. -/
lemma boundaryZerosDenominator_ne_zero : boundaryZerosDenominator ≠ 0 := by
  intro hZero
  have hEvaluation := congrArg (Polynomial.eval 0) hZero
  norm_num [boundaryZerosDenominator] at hEvaluation

/-- An explicit Bezout identity certifies the strict-boundary quotient as coprime. -/
lemma boundaryZerosNumerator_isCoprime :
    IsCoprime boundaryZerosNumerator boundaryZerosDenominator := by
  refine ⟨C (-529 / 2624) * X,
    1 - C (23 / 64) * X ^ 2, ?_⟩
  apply Polynomial.funext
  intro q
  norm_num [boundaryZerosNumerator, boundaryZerosDenominator]
  ring

/-- The exact coprime quotient for the positive zero-location fixture. -/
def insideZerosReducedResponse : DelayTransfer.ReducedRationalResponse where
  numerator := insideZerosNumerator
  denominator := insideZerosDenominator
  numerator_ne_zero := insideZerosNumerator_ne_zero
  denominator_ne_zero := insideZerosDenominator_ne_zero
  isCoprime := insideZerosNumerator_isCoprime

/-- The exact coprime quotient for the strict-boundary fixture. -/
def boundaryZerosReducedResponse : DelayTransfer.ReducedRationalResponse where
  numerator := boundaryZerosNumerator
  denominator := boundaryZerosDenominator
  numerator_ne_zero := boundaryZerosNumerator_ne_zero
  denominator_ne_zero := boundaryZerosDenominator_ne_zero
  isCoprime := boundaryZerosNumerator_isCoprime

/-- The positive response reduction removes only the unit polynomial. -/
def insideZerosRationalReduction : DelayTransfer.RationalReduction where
  rawNumerator := insideZerosParameters.responseNumeratorPolynomial
  rawDenominator := insideZerosParameters.denominatorPolynomial
  cancelledFactor := 1
  reduced := insideZerosReducedResponse
  cancelledFactor_ne_zero := one_ne_zero
  rawNumerator_eq := by
    rw [insideZeros_responseNumeratorPolynomial_expansion]
    simp [insideZerosReducedResponse]
  rawDenominator_eq := by
    rw [insideZeros_denominatorPolynomial_expansion]
    simp [insideZerosReducedResponse]

/-- The strict-boundary response reduction removes only the unit polynomial. -/
def boundaryZerosRationalReduction : DelayTransfer.RationalReduction where
  rawNumerator := boundaryZerosParameters.responseNumeratorPolynomial
  rawDenominator := boundaryZerosParameters.denominatorPolynomial
  cancelledFactor := 1
  reduced := boundaryZerosReducedResponse
  cancelledFactor_ne_zero := one_ne_zero
  rawNumerator_eq := by
    rw [boundaryZeros_responseNumeratorPolynomial_expansion]
    simp [boundaryZerosReducedResponse]
  rawDenominator_eq := by
    rw [boundaryZeros_denominatorPolynomial_expansion]
    simp [boundaryZerosReducedResponse]

/-- The positive reduction tied to the selected coherent DCDR response polynomials. -/
def insideZerosResponseReduction : ResponseReduction insideZerosParameters where
  reduction := insideZerosRationalReduction
  rawNumerator_eq := rfl
  rawDenominator_eq := rfl

/-- The strict-boundary reduction tied to the selected coherent DCDR response polynomials. -/
def boundaryZerosResponseReduction : ResponseReduction boundaryZerosParameters where
  reduction := boundaryZerosRationalReduction
  rawNumerator_eq := rfl
  rawDenominator_eq := rfl

/-!

## D. Direct coherent zero-location anchors

-/

/-- Direct numerator substitution shows that `z = 1/2` is a finite zero of the positive fixture. -/
lemma insideZerosResponseReduction_half_mem_zZeros :
    (1 / 2 : ℂ) ∈ insideZerosResponseReduction.reduction.reduced.zZeros := by
  constructor
  · norm_num
  · change insideZerosNumerator.eval (1 / 2 : ℂ)⁻¹ = 0
    norm_num [insideZerosNumerator]

/-- Direct rational-data expansion puts every finite zero of the positive fixture inside the
unit disk.

This proof does not use the production strict-result lemma.
-/
lemma insideZerosResponseReduction_allZerosInsideUnitDisk :
    insideZerosResponseReduction.allZerosInsideUnitDisk := by
  intro z hzRoot
  rcases hzRoot with ⟨hz, hNumerator⟩
  change insideZerosNumerator.eval z⁻¹ = 0 at hNumerator
  have hEquation : 4 * z⁻¹ - z⁻¹ ^ 3 = 0 := by
    simpa [insideZerosNumerator] using hNumerator
  have hSquare : z ^ 2 = (1 / 4 : ℂ) := by
    field_simp [hz] at hEquation ⊢
    linear_combination hEquation
  have hNorm := congrArg norm hSquare
  norm_num [norm_pow] at hNorm
  nlinarith [norm_nonneg z]

/-- Direct numerator substitution shows that `z = 1` is a finite boundary zero. -/
lemma boundaryZerosResponseReduction_one_mem_zZeros :
    (1 : ℂ) ∈ boundaryZerosResponseReduction.reduction.reduced.zZeros := by
  constructor
  · norm_num
  · change boundaryZerosNumerator.eval (1 : ℂ)⁻¹ = 0
    norm_num [boundaryZerosNumerator]

/-- The explicit norm-one zero makes the strict all-zeros condition fail. -/
lemma boundaryZerosResponseReduction_not_allZerosInsideUnitDisk :
    ¬boundaryZerosResponseReduction.allZerosInsideUnitDisk := by
  intro hInside
  have hStrict := hInside 1 boundaryZerosResponseReduction_one_mem_zZeros
  norm_num at hStrict

/-!

## E. Printed incoherent strictness boundary

-/

/-- At unit gains and zero printed couplings, all three FMICS'15 Theorem 5 hypotheses hold. -/
lemma printedIncoherentTheoremFiveConditions_boundary :
    PrintedIncoherentTheoremFiveConditions 1 1 1 0 0 := by
  norm_num [PrintedIncoherentTheoremFiveConditions,
    printedIncoherentZeroCubicCoefficient,
    printedIncoherentZeroLinearCoefficient]

/-- At the same point, Physlib's strict sufficient condition fails. -/
lemma printedIncoherentStrictAllZerosConditions_boundary_fails :
    ¬PrintedIncoherentStrictAllZerosConditions 1 1 1 0 0 := by
  norm_num [PrintedIncoherentStrictAllZerosConditions,
    printedIncoherentZeroCubicCoefficient,
    printedIncoherentZeroLinearCoefficient]

/-- The printed incoherent numerator has the reciprocal-coordinate boundary zero `z = 1`. -/
lemma printedIncoherentZeroPolynomial_boundary_one :
    (printedIncoherentZeroPolynomial 1 1 1 0 0).eval (1 : ℂ)⁻¹ = 0 := by
  norm_num [printedIncoherentZeroPolynomial,
    printedIncoherentZeroCubicCoefficient,
    printedIncoherentZeroLinearCoefficient]

/-- The printed Theorem 5 boundary point fails the paper's strict Definition 7 zero condition. -/
lemma printedIncoherentAllZerosInsideUnitDisk_boundary_fails :
    ¬PrintedIncoherentAllZerosInsideUnitDisk 1 1 1 0 0 := by
  intro hInside
  have hStrict := hInside 1 (by norm_num)
    printedIncoherentZeroPolynomial_boundary_one
  norm_num at hStrict

end

end Optics.DCDR
