/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Systems.DCDR.SourceBridge

/-!
# Exact audit of FMICS'15's reported passive DCDR instability

## i. Overview

FMICS'15 p. 175 reports the following passive case after discussing its printed incoherent
Theorem 4:

> “In an effort to validate the stability results provided in [5], we discovered that both given
> values of poles cannot satisfy the stability conditions. We formally proved the instability of
> the DCDR in case of passive operation (i.e., `G1 = G2 = G3 = 1`) with `k1 = k2 = 0.9` as
> follows: `unstable psp (λz. DCDR (1/z) (1/z) (1/z) 0.9 0.9
> [0.905539; -0.905539])`, where `unstable psp sys = ¬(is stable psp sys)` as described in
> Definition 7.”

This file audits the printed data with exact rational and real algebra. Under Physlib's explicit
legend `q = z⁻¹`, the printed denominator is `1 - (41/50) * q²`. Its formal-`q` roots are
`±sqrt (50/41)`, whose squared moduli are `50/41 > 1`; its finite reciprocal-`z` poles are
`±sqrt (41/50)`, whose squared moduli are `41/50 < 1`. The Schur predicate applies to the latter.

The source decimals are interpreted coordinate-explicitly as proposed `z`-poles. Exact integer
arithmetic proves `905539² ≠ 820000 * 10⁶`, so neither signed decimal is a pole. A
rational squeeze certifies the positive decimal's absolute error from `sqrt (41/50)` without
floating-point data.

The mapped coherent N7 model is audited separately. Its denominator is
`1 + (4/5) * q²`, not the printed incoherent denominator. Its formal roots and reciprocal poles
are imaginary, and its reciprocal poles are also strictly inside the unit disk. No theorem below
identifies the two response models.

## ii. Key results

- `passivePrintedReducedResponse_poles`: exact formal-`q` roots.
- `passivePrintedReducedResponse_zPoles`: exact reciprocal-`z` poles.
- `passivePrintedReducedResponse_isSchurStable`: direct strict unit-disk check.
- `passiveCoherentReducedResponse_poles`: exact coherent formal-`q` roots.
- `passiveCoherentReducedResponse_zPoles`: exact coherent reciprocal-`z` poles.
- `passiveReportedPole_integer_square_ne`: exact mismatch behind both printed decimals.
- `passiveReportedPole_absoluteError`: a rational interval for the positive error.
- `passivePrintedTheoremFourConditions`: the printed hypotheses hold at this point.

## iii. Table of contents

- A. Exact parameter and polynomial data
- B. Cancellation-free printed and coherent quotients
- C. Formal-`q` and reciprocal-`z` roots
- D. Decimal pole-list audit
- E. Printed claim audit

## iv. References

No result claims physical resonance, coherent--incoherent equivalence, BIBO stability beyond
S4P's stated gate, normalized-modal or electromagnetic power, causality or time-domain behavior,
or a physical-frequency interpretation of formal `q` or reciprocal `z`.

U. Siddique, S. M. Beillahi, and S. Tahar, “On the Formal Analysis of Photonic Signal
Processing Systems”, FMICS 2015, LNCS 9128, Definition 7, Theorems 3--4, pp. 170, 173--175.

The public HOL script deferred to reference [3] is unavailable. This file does not assert whether
the source's `psp` predicate treats its displayed pole list as supplied data, nor what its script
proves. It makes no claim about Binh [5]. The checked set-based facts expose a printed-text
conflict: the p. 175 prose says unstable, while the printed denominator and Definition 7's strict
pole-location criterion give stability. The alternative reading—that “unstable” rejects the
rounded supplied pole list rather than locating an actual pole outside the unit disk—remains open.
-/

@[expose] public section

namespace Optics.DCDR

noncomputable section

open Polynomial
open scoped ComplexOrder

/-!

## A. Exact parameter and polynomial data

-/

/-- The exact printed numerator at FMICS'15 p. 175's passive point. -/
def passivePrintedNumerator : Polynomial ℂ :=
  C (41 / 50) * X - C (16 / 25) * X ^ 3

/-- The exact printed denominator at FMICS'15 p. 175's passive point. -/
def passivePrintedDenominator : Polynomial ℂ :=
  1 - C (41 / 50) * X ^ 2

/-- The exact coherent N7 numerator at the dictionary image of the passive point. -/
def passiveCoherentNumerator : Polynomial ℂ :=
  -(C (4 / 5) * X) - X ^ 3

/-- The exact coherent N7 denominator at the dictionary image of the passive point. -/
def passiveCoherentDenominator : Polynomial ℂ :=
  1 + C (4 / 5) * X ^ 2

/-- Direct unfolding exposes every printed source symbol as exact rational data. -/
lemma passiveCaseSourceParameters_data :
    DCDRSourceBridge.passiveCaseSourceParameters.G1 = 1 ∧
      DCDRSourceBridge.passiveCaseSourceParameters.G2 = 1 ∧
      DCDRSourceBridge.passiveCaseSourceParameters.G3 = 1 ∧
      DCDRSourceBridge.passiveCaseSourceParameters.k1 = 9 / 10 ∧
      DCDRSourceBridge.passiveCaseSourceParameters.k2 = 9 / 10 := by
  norm_num [DCDRSourceBridge.passiveCaseSourceParameters]

/-- The passive source point lies in both domains of the source dictionary. -/
lemma passiveCaseSourceParameters_domains :
    DCDRSourceBridge.passiveCaseSourceParameters.HasAdmissibleCouplings ∧
      DCDRSourceBridge.passiveCaseSourceParameters.HasNonnegativeGains := by
  norm_num [DCDRSourceBridge.SourceParameters.HasAdmissibleCouplings,
    DCDRSourceBridge.SourceParameters.HasNonnegativeGains,
    DCDRSourceBridge.passiveCaseSourceParameters]

/-- The coherent dictionary image retains the three unit gains and square-root amplitudes. -/
lemma passiveCaseUnitDelayParameters_data :
    DCDRSourceBridge.passiveCaseUnitDelayParameters.firstCoupler.throughAmplitude =
        Real.sqrt (1 / 10) ∧
      DCDRSourceBridge.passiveCaseUnitDelayParameters.firstCoupler.crossAmplitude =
        Real.sqrt (9 / 10) ∧
      DCDRSourceBridge.passiveCaseUnitDelayParameters.secondCoupler.throughAmplitude =
        Real.sqrt (1 / 10) ∧
      DCDRSourceBridge.passiveCaseUnitDelayParameters.secondCoupler.crossAmplitude =
        Real.sqrt (9 / 10) ∧
      DCDRSourceBridge.passiveCaseUnitDelayParameters.upperGain = 1 ∧
      DCDRSourceBridge.passiveCaseUnitDelayParameters.lowerGain = 1 ∧
      DCDRSourceBridge.passiveCaseUnitDelayParameters.feedbackGain = 1 := by
  norm_num [DCDRSourceBridge.passiveCaseUnitDelayParameters,
    DCDRSourceBridge.SourceParameters.toCoherentUnitDelayParameters,
    DCDRSourceBridge.intensityGainToFieldAmplitudeGain,
    DCDRSourceBridge.passiveCaseSourceParameters]

/-- Primitive substitution separates the two printed Theorem 3 loop terms. -/
lemma passiveCase_printedLoopTerms :
    DCDRSourceBridge.passiveCaseSourceParameters.k1 *
          DCDRSourceBridge.passiveCaseSourceParameters.k2 *
          DCDRSourceBridge.passiveCaseSourceParameters.G1 *
          DCDRSourceBridge.passiveCaseSourceParameters.G3 = 81 / 100 ∧
      (1 - DCDRSourceBridge.passiveCaseSourceParameters.k1) *
          (1 - DCDRSourceBridge.passiveCaseSourceParameters.k2) *
          DCDRSourceBridge.passiveCaseSourceParameters.G2 *
          DCDRSourceBridge.passiveCaseSourceParameters.G3 = 1 / 100 := by
  norm_num [DCDRSourceBridge.passiveCaseSourceParameters]

/-- Primitive expansion gives the printed Theorem 3 loop coefficient `41/50`. -/
lemma passiveCase_printedLoopCoefficient :
    DCDRSourceBridge.passiveCaseSourceParameters.printedLoopCoefficient = 41 / 50 := by
  norm_num [DCDRSourceBridge.SourceParameters.printedLoopCoefficient,
    DCDRSourceBridge.passiveCaseSourceParameters]

/-- Primitive expansion gives the printed numerator coefficients `41/50` and `16/25`. -/
lemma passiveCase_printedNumeratorPolynomial_expansion :
    DCDRSourceBridge.passiveCaseSourceParameters.printedNumeratorPolynomial =
      passivePrintedNumerator := by
  norm_num [DCDRSourceBridge.SourceParameters.printedNumeratorPolynomial,
    DCDRSourceBridge.SourceParameters.printedLinearCoefficient,
    DCDRSourceBridge.SourceParameters.printedCubicCoefficient,
    DCDRSourceBridge.passiveCaseSourceParameters, passivePrintedNumerator]

/-- Primitive expansion gives `1 - (81/100 + 1/100) * q² = 1 - (41/50) * q²`. -/
lemma passiveCase_printedDenominatorPolynomial_expansion :
    DCDRSourceBridge.passiveCaseSourceParameters.printedDenominatorPolynomial =
      passivePrintedDenominator := by
  norm_num [DCDRSourceBridge.SourceParameters.printedDenominatorPolynomial,
    DCDRSourceBridge.SourceParameters.printedLoopCoefficient,
    DCDRSourceBridge.passiveCaseSourceParameters, passivePrintedDenominator]

/-- Primitive coherent N7 expansion gives loop coefficient `-4/5`. -/
lemma passiveCase_coherentLoopCoefficient :
    DCDRSourceBridge.passiveCaseUnitDelayParameters.loopCoefficient = -4 / 5 := by
  have hThrough : (Real.sqrt (1 / 10) : ℂ) ^ 2 = 1 / 10 := by
    rw [← Complex.ofReal_pow,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 10)]
    norm_num
  have hCross : (Real.sqrt (9 / 10) : ℂ) ^ 2 = 9 / 10 := by
    rw [← Complex.ofReal_pow,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 9 / 10)]
    norm_num
  simp only [DCDRSourceBridge.passiveCaseUnitDelayParameters,
    DCDRSourceBridge.SourceParameters.toCoherentUnitDelayParameters,
    DCDRSourceBridge.intensityGainToFieldAmplitudeGain,
    DCDRSourceBridge.passiveCaseSourceParameters, UnitDelayParameters.loopCoefficient,
    DirectionalCoupler.crossCoefficient]
  ring_nf
  rw [hThrough, hCross, Complex.I_sq]
  norm_num

/-- Direct coherent expansion gives the displayed denominator. -/
lemma passiveCase_coherentDenominatorPolynomial_expansion :
    DCDRSourceBridge.passiveCaseUnitDelayParameters.denominatorPolynomial =
      passiveCoherentDenominator := by
  rw [UnitDelayParameters.denominatorPolynomial_eq_one_sub_C_mul_X_sq,
    passiveCase_coherentLoopCoefficient]
  norm_num [passiveCoherentDenominator]

/-- Direct expansion of the coherent response data gives the displayed numerator. -/
lemma passiveCase_coherentNumeratorPolynomial_expansion :
    DCDRSourceBridge.passiveCaseUnitDelayParameters.responseNumeratorPolynomial =
      passiveCoherentNumerator := by
  have hThrough : (Real.sqrt (1 / 10) : ℂ) ^ 2 = 1 / 10 := by
    rw [← Complex.ofReal_pow,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 10)]
    norm_num
  have hThroughFour : (Real.sqrt (1 / 10) : ℂ) ^ 4 = 1 / 100 := by
    calc
      (Real.sqrt (1 / 10) : ℂ) ^ 4 =
          ((Real.sqrt (1 / 10) : ℂ) ^ 2) ^ 2 := by ring
      _ = 1 / 100 := by rw [hThrough]; norm_num
  have hNine : (Real.sqrt 9 : ℂ) ^ 2 = 9 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 9)
  have hTen : (Real.sqrt 10 : ℂ) ^ 2 = 10 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 10)
  have hNineFour : (Real.sqrt 9 : ℂ) ^ 4 = 81 := by
    calc
      (Real.sqrt 9 : ℂ) ^ 4 = ((Real.sqrt 9 : ℂ) ^ 2) ^ 2 := by ring
      _ = 81 := by rw [hNine]; norm_num
  have hTenFour : (Real.sqrt 10 : ℂ) ^ 4 = 100 := by
    calc
      (Real.sqrt 10 : ℂ) ^ 4 = ((Real.sqrt 10 : ℂ) ^ 2) ^ 2 := by ring
      _ = 100 := by rw [hTen]; norm_num
  have hTenInvTwo : (Real.sqrt 10 : ℂ)⁻¹ ^ 2 = 1 / 10 := by
    rw [inv_pow, hTen]
    norm_num
  have hTenInvFour : (Real.sqrt 10 : ℂ)⁻¹ ^ 4 = 1 / 100 := by
    rw [inv_pow, hTenFour]
    norm_num
  apply Polynomial.funext
  intro q
  simp only [UnitDelayParameters.responseNumeratorPolynomial,
    UnitDelayParameters.directPolynomial, UnitDelayParameters.denominatorPolynomial,
    UnitDelayParameters.loopPolynomial, UnitDelayParameters.feedbackReadoutPolynomial,
    UnitDelayParameters.feedbackDrivePolynomial, UnitDelayParameters.upperPolynomial,
    UnitDelayParameters.lowerPolynomial, UnitDelayParameters.feedbackPolynomial,
    DCDRSourceBridge.passiveCaseUnitDelayParameters,
    DCDRSourceBridge.SourceParameters.toCoherentUnitDelayParameters,
    DCDRSourceBridge.intensityGainToFieldAmplitudeGain,
    DCDRSourceBridge.passiveCaseSourceParameters, DirectionalCoupler.crossCoefficient,
    passiveCoherentNumerator]
  simp only [Nat.ofNat_nonneg, Real.sqrt_div, Complex.ofReal_div, neg_mul, map_neg,
    map_mul, Complex.ofReal_one, map_one, one_mul, mul_neg, neg_neg, eval_add,
    eval_mul, eval_C, eval_X, eval_sub, eval_one, eval_neg, eval_pow]
  ring_nf
  rw [hThrough, hThroughFour, hNine, hNineFour, hTenInvTwo, hTenInvFour,
    show Complex.I ^ 2 = (-1 : ℂ) by norm_num [pow_two, Complex.I_mul_I],
    show Complex.I ^ 4 = (1 : ℂ) by norm_num [pow_succ, Complex.I_mul_I]]
  norm_num
  ring

/-- The printed and coherent loop coefficients differ at the same five source symbols. -/
lemma passiveCase_loopCoefficients_ne :
    (DCDRSourceBridge.passiveCaseSourceParameters.printedLoopCoefficient : ℂ) ≠
      DCDRSourceBridge.passiveCaseUnitDelayParameters.loopCoefficient := by
  rw [passiveCase_printedLoopCoefficient, passiveCase_coherentLoopCoefficient]
  norm_num

/-- The printed incoherent and mapped coherent denominators differ at the passive point. -/
lemma passiveCase_denominatorPolynomials_ne :
    DCDRSourceBridge.passiveCaseSourceParameters.printedDenominatorPolynomial ≠
      DCDRSourceBridge.passiveCaseUnitDelayParameters.denominatorPolynomial := by
  rw [passiveCase_printedDenominatorPolynomial_expansion,
    passiveCase_coherentDenominatorPolynomial_expansion]
  intro hEqual
  have hEvaluation := congrArg (Polynomial.eval 1) hEqual
  norm_num [passivePrintedDenominator, passiveCoherentDenominator] at hEvaluation

/-!

## B. Cancellation-free printed and coherent quotients

-/

/-- The exact printed numerator is nonzero. -/
lemma passivePrintedNumerator_ne_zero : passivePrintedNumerator ≠ 0 := by
  intro hZero
  have hCoefficient := congrArg (fun polynomial => polynomial.coeff 1) hZero
  norm_num [passivePrintedNumerator] at hCoefficient

/-- The exact printed denominator is nonzero. -/
lemma passivePrintedDenominator_ne_zero : passivePrintedDenominator ≠ 0 := by
  intro hZero
  have hEvaluation := congrArg (Polynomial.eval 0) hZero
  norm_num [passivePrintedDenominator] at hEvaluation

/-- A primitive Bezout identity rules out cancellation in the printed quotient. -/
lemma passivePrintedNumerator_isCoprime :
    IsCoprime passivePrintedNumerator passivePrintedDenominator := by
  refine ⟨C (1681 / 81) * X, 1 - C (1312 / 81) * X ^ 2, ?_⟩
  apply Polynomial.funext
  intro q
  norm_num [passivePrintedNumerator, passivePrintedDenominator]
  ring

/-- The exact printed quotient, with no common numerator/denominator factor. -/
def passivePrintedReducedResponse : DelayTransfer.ReducedRationalResponse where
  numerator := passivePrintedNumerator
  denominator := passivePrintedDenominator
  numerator_ne_zero := passivePrintedNumerator_ne_zero
  denominator_ne_zero := passivePrintedDenominator_ne_zero
  isCoprime := passivePrintedNumerator_isCoprime

/-- The printed passive quotient removes only the unit polynomial. -/
def passivePrintedRationalReduction : DelayTransfer.RationalReduction where
  rawNumerator :=
    DCDRSourceBridge.passiveCaseSourceParameters.printedNumeratorPolynomial
  rawDenominator :=
    DCDRSourceBridge.passiveCaseSourceParameters.printedDenominatorPolynomial
  cancelledFactor := 1
  reduced := passivePrintedReducedResponse
  cancelledFactor_ne_zero := one_ne_zero
  rawNumerator_eq := by
    rw [passiveCase_printedNumeratorPolynomial_expansion]
    simp [passivePrintedReducedResponse]
  rawDenominator_eq := by
    rw [passiveCase_printedDenominatorPolynomial_expansion]
    simp [passivePrintedReducedResponse]

/-- The exact coherent numerator is nonzero. -/
lemma passiveCoherentNumerator_ne_zero : passiveCoherentNumerator ≠ 0 := by
  intro hZero
  have hCoefficient := congrArg (fun polynomial => polynomial.coeff 1) hZero
  norm_num [passiveCoherentNumerator] at hCoefficient

/-- The exact coherent denominator is nonzero. -/
lemma passiveCoherentDenominator_ne_zero : passiveCoherentDenominator ≠ 0 := by
  intro hZero
  have hEvaluation := congrArg (Polynomial.eval 0) hZero
  norm_num [passiveCoherentDenominator] at hEvaluation

/-- A primitive Bezout identity rules out cancellation in the coherent quotient. -/
lemma passiveCoherentNumerator_isCoprime :
    IsCoprime passiveCoherentNumerator passiveCoherentDenominator := by
  refine ⟨C (-16 / 9) * X, 1 - C (20 / 9) * X ^ 2, ?_⟩
  apply Polynomial.funext
  intro q
  norm_num [passiveCoherentNumerator, passiveCoherentDenominator]
  ring

/-- The exact coherent quotient, with no common numerator/denominator factor. -/
def passiveCoherentReducedResponse : DelayTransfer.ReducedRationalResponse where
  numerator := passiveCoherentNumerator
  denominator := passiveCoherentDenominator
  numerator_ne_zero := passiveCoherentNumerator_ne_zero
  denominator_ne_zero := passiveCoherentDenominator_ne_zero
  isCoprime := passiveCoherentNumerator_isCoprime

/-- The coherent passive quotient removes only the unit polynomial. -/
def passiveCoherentRationalReduction : DelayTransfer.RationalReduction where
  rawNumerator :=
    DCDRSourceBridge.passiveCaseUnitDelayParameters.responseNumeratorPolynomial
  rawDenominator :=
    DCDRSourceBridge.passiveCaseUnitDelayParameters.denominatorPolynomial
  cancelledFactor := 1
  reduced := passiveCoherentReducedResponse
  cancelledFactor_ne_zero := one_ne_zero
  rawNumerator_eq := by
    rw [passiveCase_coherentNumeratorPolynomial_expansion]
    simp [passiveCoherentReducedResponse]
  rawDenominator_eq := by
    rw [passiveCase_coherentDenominatorPolynomial_expansion]
    simp [passiveCoherentReducedResponse]

/-- The cancellation-free coherent quotient is tied to the selected DCDR response polynomials. -/
def passiveCoherentResponseReduction :
    ResponseReduction DCDRSourceBridge.passiveCaseUnitDelayParameters where
  reduction := passiveCoherentRationalReduction
  rawNumerator_eq := rfl
  rawDenominator_eq := rfl

/-!

## C. Formal-`q` and reciprocal-`z` roots

-/

/-- The positive real magnitude of either printed formal-`q` root. -/
def passivePrintedFormalRootMagnitude : ℝ := Real.sqrt (50 / 41)

/-- The positive real magnitude of either printed reciprocal-`z` pole. -/
def passivePrintedReciprocalPoleMagnitude : ℝ := Real.sqrt (41 / 50)

/-- The printed formal-root magnitude has square `50/41`. -/
lemma passivePrintedFormalRootMagnitude_sq :
    passivePrintedFormalRootMagnitude ^ 2 = 50 / 41 := by
  exact Real.sq_sqrt (by norm_num)

/-- The printed reciprocal-pole magnitude has square `41/50`. -/
lemma passivePrintedReciprocalPoleMagnitude_sq :
    passivePrintedReciprocalPoleMagnitude ^ 2 = 41 / 50 := by
  exact Real.sq_sqrt (by norm_num)

/-- The printed denominator's exact roots in the formal coordinate `q`. -/
lemma passivePrintedReducedResponse_poles :
    passivePrintedReducedResponse.poles =
      {(passivePrintedFormalRootMagnitude : ℂ),
        -(passivePrintedFormalRootMagnitude : ℂ)} := by
  ext q
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hRoot
    change passivePrintedDenominator.eval q = 0 at hRoot
    have hEquation : 1 - (41 / 50 : ℂ) * q ^ 2 = 0 := by
      simpa only [passivePrintedDenominator, eval_sub, eval_one, eval_mul, eval_C,
        eval_pow, eval_X] using hRoot
    have hSquare : q ^ 2 = 50 / 41 := by
      linear_combination -(50 / 41) * hEquation
    have hMagnitudeSquare : (passivePrintedFormalRootMagnitude : ℂ) ^ 2 =
        50 / 41 := by
      rw [← Complex.ofReal_pow, passivePrintedFormalRootMagnitude_sq]
      norm_num
    have hFactor :
        (q - passivePrintedFormalRootMagnitude) *
            (q + passivePrintedFormalRootMagnitude) = 0 := by
      calc
        (q - passivePrintedFormalRootMagnitude) *
            (q + passivePrintedFormalRootMagnitude) =
            q ^ 2 - (passivePrintedFormalRootMagnitude : ℂ) ^ 2 := by ring
        _ = 0 := by rw [hSquare, hMagnitudeSquare]; norm_num
    rcases mul_eq_zero.mp hFactor with hPositive | hNegative
    · left
      linear_combination hPositive
    · right
      linear_combination hNegative
  · rintro (rfl | rfl)
    · change passivePrintedDenominator.eval
        (passivePrintedFormalRootMagnitude : ℂ) = 0
      simp only [passivePrintedDenominator, eval_sub, eval_one, eval_mul, eval_C,
        eval_pow, eval_X]
      rw [← Complex.ofReal_pow, passivePrintedFormalRootMagnitude_sq]
      norm_num
    · change passivePrintedDenominator.eval
        (-(passivePrintedFormalRootMagnitude : ℂ)) = 0
      simp only [passivePrintedDenominator, eval_sub, eval_one, eval_mul, eval_C,
        eval_pow, eval_X, neg_sq]
      rw [← Complex.ofReal_pow, passivePrintedFormalRootMagnitude_sq]
      norm_num

/-- The same printed roots in the finite reciprocal coordinate selected by `q = z⁻¹`. -/
lemma passivePrintedReducedResponse_zPoles :
    passivePrintedReducedResponse.zPoles =
      {(passivePrintedReciprocalPoleMagnitude : ℂ),
        -(passivePrintedReciprocalPoleMagnitude : ℂ)} := by
  ext z
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hz, hRoot⟩
    change passivePrintedDenominator.eval z⁻¹ = 0 at hRoot
    have hEquation : 1 - (41 / 50 : ℂ) * z⁻¹ ^ 2 = 0 := by
      simpa only [passivePrintedDenominator, eval_sub, eval_one, eval_mul, eval_C,
        eval_pow, eval_X] using hRoot
    have hSquare : z ^ 2 = 41 / 50 := by
      field_simp [hz] at hEquation
      linear_combination (1 / 50) * hEquation
    have hMagnitudeSquare : (passivePrintedReciprocalPoleMagnitude : ℂ) ^ 2 =
        41 / 50 := by
      rw [← Complex.ofReal_pow, passivePrintedReciprocalPoleMagnitude_sq]
      norm_num
    have hFactor :
        (z - passivePrintedReciprocalPoleMagnitude) *
            (z + passivePrintedReciprocalPoleMagnitude) = 0 := by
      calc
        (z - passivePrintedReciprocalPoleMagnitude) *
            (z + passivePrintedReciprocalPoleMagnitude) =
            z ^ 2 - (passivePrintedReciprocalPoleMagnitude : ℂ) ^ 2 := by ring
        _ = 0 := by rw [hSquare, hMagnitudeSquare]; norm_num
    rcases mul_eq_zero.mp hFactor with hPositive | hNegative
    · left
      linear_combination hPositive
    · right
      linear_combination hNegative
  · rintro (rfl | rfl)
    · have hPositive : 0 < passivePrintedReciprocalPoleMagnitude :=
        Real.sqrt_pos.2 (by norm_num)
      have hNonzero : (passivePrintedReciprocalPoleMagnitude : ℂ) ≠ 0 := by
        exact_mod_cast hPositive.ne'
      constructor
      · exact hNonzero
      · change passivePrintedDenominator.eval
          (passivePrintedReciprocalPoleMagnitude : ℂ)⁻¹ = 0
        simp only [passivePrintedDenominator, eval_sub, eval_one, eval_mul, eval_C,
          eval_pow, eval_X]
        field_simp [hNonzero]
        rw [← Complex.ofReal_pow, passivePrintedReciprocalPoleMagnitude_sq]
        norm_num
    · have hPositive : 0 < passivePrintedReciprocalPoleMagnitude :=
        Real.sqrt_pos.2 (by norm_num)
      have hNonzero : (-(passivePrintedReciprocalPoleMagnitude : ℂ)) ≠ 0 := by
        exact neg_ne_zero.mpr (by exact_mod_cast hPositive.ne')
      constructor
      · exact hNonzero
      · change passivePrintedDenominator.eval
          (-(passivePrintedReciprocalPoleMagnitude : ℂ))⁻¹ = 0
        simp only [passivePrintedDenominator, eval_sub, eval_one, eval_mul, eval_C,
          eval_pow, eval_X]
        field_simp [hNonzero]
        rw [← Complex.ofReal_pow, passivePrintedReciprocalPoleMagnitude_sq]
        norm_num

/-- Every printed formal-`q` root has squared modulus `50/41`, strictly above one. -/
lemma passivePrintedFormalRoot_norm_sq {q : ℂ}
    (hq : q ∈ passivePrintedReducedResponse.poles) :
    ‖q‖ ^ 2 = 50 / 41 := by
  rw [passivePrintedReducedResponse_poles] at hq
  rcases hq with rfl | rfl
  · rw [Complex.norm_real, Real.norm_eq_abs, passivePrintedFormalRootMagnitude,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    exact passivePrintedFormalRootMagnitude_sq
  · rw [norm_neg, Complex.norm_real, Real.norm_eq_abs,
      passivePrintedFormalRootMagnitude,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    exact passivePrintedFormalRootMagnitude_sq

/-- Every printed reciprocal-`z` pole has squared modulus `41/50`, strictly below one. -/
lemma passivePrintedReciprocalPole_norm_sq {z : ℂ}
    (hz : z ∈ passivePrintedReducedResponse.zPoles) :
    ‖z‖ ^ 2 = 41 / 50 := by
  rw [passivePrintedReducedResponse_zPoles] at hz
  rcases hz with rfl | rfl
  · rw [Complex.norm_real, Real.norm_eq_abs,
      passivePrintedReciprocalPoleMagnitude,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    exact passivePrintedReciprocalPoleMagnitude_sq
  · rw [norm_neg, Complex.norm_real, Real.norm_eq_abs,
      passivePrintedReciprocalPoleMagnitude,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    exact passivePrintedReciprocalPoleMagnitude_sq

/-- Direct root expansion puts the exact printed reciprocal poles strictly inside the unit disk. -/
lemma passivePrintedReducedResponse_isSchurStable :
    passivePrintedReducedResponse.IsSchurStable := by
  intro z hz
  have hNormSq := passivePrintedReciprocalPole_norm_sq hz
  have hNormNonnegative := norm_nonneg z
  nlinarith

/-- The positive real magnitude of either coherent formal-`q` root. -/
def passiveCoherentFormalRootMagnitude : ℝ := Real.sqrt (5 / 4)

/-- The positive real magnitude of either coherent reciprocal-`z` pole. -/
def passiveCoherentReciprocalPoleMagnitude : ℝ := Real.sqrt (4 / 5)

/-- The coherent formal-root magnitude has square `5/4`. -/
lemma passiveCoherentFormalRootMagnitude_sq :
    passiveCoherentFormalRootMagnitude ^ 2 = 5 / 4 := by
  exact Real.sq_sqrt (by norm_num)

/-- The coherent reciprocal-pole magnitude has square `4/5`. -/
lemma passiveCoherentReciprocalPoleMagnitude_sq :
    passiveCoherentReciprocalPoleMagnitude ^ 2 = 4 / 5 := by
  exact Real.sq_sqrt (by norm_num)

/-- The coherent denominator's exact roots in the formal coordinate `q`. -/
lemma passiveCoherentReducedResponse_poles :
    passiveCoherentReducedResponse.poles =
      {(passiveCoherentFormalRootMagnitude : ℂ) * Complex.I,
        -((passiveCoherentFormalRootMagnitude : ℂ) * Complex.I)} := by
  have hMagnitudeSquare :
      ((passiveCoherentFormalRootMagnitude : ℂ) * Complex.I) ^ 2 = -5 / 4 := by
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow,
      passiveCoherentFormalRootMagnitude_sq]
    norm_num
  ext q
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hRoot
    change passiveCoherentDenominator.eval q = 0 at hRoot
    have hEquation : 1 + (4 / 5 : ℂ) * q ^ 2 = 0 := by
      simpa only [passiveCoherentDenominator, eval_add, eval_one, eval_mul, eval_C,
        eval_pow, eval_X] using hRoot
    have hSquare : q ^ 2 = -5 / 4 := by
      linear_combination (5 / 4) * hEquation
    have hFactor :
        (q - passiveCoherentFormalRootMagnitude * Complex.I) *
            (q + passiveCoherentFormalRootMagnitude * Complex.I) = 0 := by
      calc
        (q - passiveCoherentFormalRootMagnitude * Complex.I) *
            (q + passiveCoherentFormalRootMagnitude * Complex.I) =
            q ^ 2 -
              ((passiveCoherentFormalRootMagnitude : ℂ) * Complex.I) ^ 2 := by ring
        _ = 0 := by rw [hSquare, hMagnitudeSquare]; norm_num
    rcases mul_eq_zero.mp hFactor with hPositive | hNegative
    · left
      linear_combination hPositive
    · right
      linear_combination hNegative
  · rintro (rfl | rfl)
    · change passiveCoherentDenominator.eval
        ((passiveCoherentFormalRootMagnitude : ℂ) * Complex.I) = 0
      simp only [passiveCoherentDenominator, eval_add, eval_one, eval_mul, eval_C,
        eval_pow, eval_X]
      rw [hMagnitudeSquare]
      norm_num
    · change passiveCoherentDenominator.eval
        (-((passiveCoherentFormalRootMagnitude : ℂ) * Complex.I)) = 0
      simp only [passiveCoherentDenominator, eval_add, eval_one, eval_mul, eval_C,
        eval_pow, eval_X, neg_sq]
      rw [hMagnitudeSquare]
      norm_num

/-- The same coherent roots in the finite reciprocal coordinate selected by `q = z⁻¹`. -/
lemma passiveCoherentReducedResponse_zPoles :
    passiveCoherentReducedResponse.zPoles =
      {(passiveCoherentReciprocalPoleMagnitude : ℂ) * Complex.I,
        -((passiveCoherentReciprocalPoleMagnitude : ℂ) * Complex.I)} := by
  have hMagnitudeSquare :
      ((passiveCoherentReciprocalPoleMagnitude : ℂ) * Complex.I) ^ 2 = -4 / 5 := by
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow,
      passiveCoherentReciprocalPoleMagnitude_sq]
    norm_num
  ext z
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hz, hRoot⟩
    change passiveCoherentDenominator.eval z⁻¹ = 0 at hRoot
    have hEquation : 1 + (4 / 5 : ℂ) * z⁻¹ ^ 2 = 0 := by
      simpa only [passiveCoherentDenominator, eval_add, eval_one, eval_mul, eval_C,
        eval_pow, eval_X] using hRoot
    have hSquare : z ^ 2 = -4 / 5 := by
      field_simp [hz] at hEquation
      linear_combination (1 / 5) * hEquation
    have hFactor :
        (z - passiveCoherentReciprocalPoleMagnitude * Complex.I) *
            (z + passiveCoherentReciprocalPoleMagnitude * Complex.I) = 0 := by
      calc
        (z - passiveCoherentReciprocalPoleMagnitude * Complex.I) *
            (z + passiveCoherentReciprocalPoleMagnitude * Complex.I) =
            z ^ 2 -
              ((passiveCoherentReciprocalPoleMagnitude : ℂ) * Complex.I) ^ 2 := by ring
        _ = 0 := by rw [hSquare, hMagnitudeSquare]; norm_num
    rcases mul_eq_zero.mp hFactor with hPositive | hNegative
    · left
      linear_combination hPositive
    · right
      linear_combination hNegative
  · rintro (rfl | rfl)
    · have hPositive : 0 < passiveCoherentReciprocalPoleMagnitude :=
        Real.sqrt_pos.2 (by norm_num)
      have hNonzero :
          (passiveCoherentReciprocalPoleMagnitude : ℂ) * Complex.I ≠ 0 :=
        mul_ne_zero (by exact_mod_cast hPositive.ne') Complex.I_ne_zero
      constructor
      · exact hNonzero
      · change passiveCoherentDenominator.eval
          ((passiveCoherentReciprocalPoleMagnitude : ℂ) * Complex.I)⁻¹ = 0
        simp only [passiveCoherentDenominator, eval_add, eval_one, eval_mul, eval_C,
          eval_pow, eval_X]
        field_simp [hNonzero]
        rw [Complex.I_sq, ← Complex.ofReal_pow,
          passiveCoherentReciprocalPoleMagnitude_sq]
        norm_num
    · have hPositive : 0 < passiveCoherentReciprocalPoleMagnitude :=
        Real.sqrt_pos.2 (by norm_num)
      have hNonzero :
          -((passiveCoherentReciprocalPoleMagnitude : ℂ) * Complex.I) ≠ 0 :=
        neg_ne_zero.mpr
          (mul_ne_zero (by exact_mod_cast hPositive.ne') Complex.I_ne_zero)
      constructor
      · exact hNonzero
      · change passiveCoherentDenominator.eval
          (-((passiveCoherentReciprocalPoleMagnitude : ℂ) * Complex.I))⁻¹ = 0
        simp only [passiveCoherentDenominator, eval_add, eval_one, eval_mul, eval_C,
          eval_pow, eval_X]
        field_simp [hNonzero]
        rw [Complex.I_sq, ← Complex.ofReal_pow,
          passiveCoherentReciprocalPoleMagnitude_sq]
        norm_num

/-- Every coherent formal-`q` root has squared modulus `5/4`, strictly above one. -/
lemma passiveCoherentFormalRoot_norm_sq {q : ℂ}
    (hq : q ∈ passiveCoherentReducedResponse.poles) :
    ‖q‖ ^ 2 = 5 / 4 := by
  rw [passiveCoherentReducedResponse_poles] at hq
  rcases hq with rfl | rfl
  · rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      passiveCoherentFormalRootMagnitude,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    exact passiveCoherentFormalRootMagnitude_sq
  · rw [norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, passiveCoherentFormalRootMagnitude,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    exact passiveCoherentFormalRootMagnitude_sq

/-- Every coherent reciprocal-`z` pole has squared modulus `4/5`, strictly below one. -/
lemma passiveCoherentReciprocalPole_norm_sq {z : ℂ}
    (hz : z ∈ passiveCoherentReducedResponse.zPoles) :
    ‖z‖ ^ 2 = 4 / 5 := by
  rw [passiveCoherentReducedResponse_zPoles] at hz
  rcases hz with rfl | rfl
  · rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      passiveCoherentReciprocalPoleMagnitude,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    exact passiveCoherentReciprocalPoleMagnitude_sq
  · rw [norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, passiveCoherentReciprocalPoleMagnitude,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    exact passiveCoherentReciprocalPoleMagnitude_sq

/-- Direct root expansion puts the coherent reciprocal poles strictly inside the unit disk. -/
lemma passiveCoherentReducedResponse_isSchurStable :
    passiveCoherentReducedResponse.IsSchurStable := by
  intro z hz
  have hNormSq := passiveCoherentReciprocalPole_norm_sq hz
  have hNormNonnegative := norm_nonneg z
  nlinarith

/-!

## D. Decimal pole-list audit

-/

/-- FMICS'15 p. 175's positive displayed pole, retained as an exact rational real. -/
def passiveReportedPoleMagnitude : ℝ := 905539 / 1000000

/-- Multiplication by `z²` turns `D(z⁻¹)` into this finite reciprocal-`z` polynomial. -/
def passivePrintedZDenominator : Polynomial ℂ :=
  X ^ 2 - C (41 / 50)

/-- The printed decimal's integer square misses the integer required by the `z` denominator. -/
lemma passiveReportedPole_integer_square_ne :
    (905539 : ℕ) ^ 2 ≠ 820000 * 10 ^ 6 := by
  norm_num

/-- Both signed printed `z` candidates give the same nonzero exact `z`-form evaluation. -/
lemma passiveReportedPoles_zForm_evaluation :
    passivePrintedZDenominator.eval (passiveReportedPoleMagnitude : ℂ) =
        880521 / 1000000000000 ∧
      passivePrintedZDenominator.eval (-(passiveReportedPoleMagnitude : ℂ)) =
        880521 / 1000000000000 := by
  constructor <;>
    norm_num [passivePrintedZDenominator, passiveReportedPoleMagnitude]

/-- Thus neither signed displayed decimal is a root in the reciprocal-`z` coordinate. -/
lemma passiveReportedPoles_zForm_nonroots :
    passivePrintedZDenominator.eval (passiveReportedPoleMagnitude : ℂ) ≠ 0 ∧
      passivePrintedZDenominator.eval (-(passiveReportedPoleMagnitude : ℂ)) ≠ 0 := by
  rw [passiveReportedPoles_zForm_evaluation.1,
    passiveReportedPoles_zForm_evaluation.2]
  norm_num

/-- In the equivalent formal coordinate `q = z⁻¹`, both evaluations remain nonzero. -/
lemma passiveReportedPoles_qForm_evaluation :
    passivePrintedDenominator.eval (passiveReportedPoleMagnitude : ℂ)⁻¹ =
        880521 / 820000880521 ∧
      passivePrintedDenominator.eval (-(passiveReportedPoleMagnitude : ℂ))⁻¹ =
        880521 / 820000880521 := by
  constructor <;>
    norm_num [passivePrintedDenominator, passiveReportedPoleMagnitude]

/-- The two decimals fail the formal-`q` denominator after the explicit reciprocal map. -/
lemma passiveReportedPoles_qForm_nonroots :
    passivePrintedDenominator.eval (passiveReportedPoleMagnitude : ℂ)⁻¹ ≠ 0 ∧
      passivePrintedDenominator.eval (-(passiveReportedPoleMagnitude : ℂ))⁻¹ ≠ 0 := by
  rw [passiveReportedPoles_qForm_evaluation.1,
    passiveReportedPoles_qForm_evaluation.2]
  norm_num

/-- Neither supplied decimal is an actual reciprocal-`z` pole of the reduced quotient. -/
lemma passiveReportedPoles_not_mem_zPoles :
    (passiveReportedPoleMagnitude : ℂ) ∉ passivePrintedReducedResponse.zPoles ∧
      -(passiveReportedPoleMagnitude : ℂ) ∉ passivePrintedReducedResponse.zPoles := by
  constructor
  · rintro ⟨_, hRoot⟩
    exact passiveReportedPoles_qForm_nonroots.1 hRoot
  · rintro ⟨_, hRoot⟩
    exact passiveReportedPoles_qForm_nonroots.2 hRoot

/-- Their reciprocals are equivalently absent from the formal-`q` pole set. -/
lemma passiveReportedReciprocals_not_mem_poles :
    (passiveReportedPoleMagnitude : ℂ)⁻¹ ∉ passivePrintedReducedResponse.poles ∧
      (-(passiveReportedPoleMagnitude : ℂ))⁻¹ ∉
        passivePrintedReducedResponse.poles := by
  exact passiveReportedPoles_qForm_nonroots

/-- Exact rational squaring traps the true positive reciprocal-`z` pole tightly. -/
lemma passiveReportedPole_rational_squeeze :
    (9055385 / 10000000 : ℝ) < passivePrintedReciprocalPoleMagnitude ∧
      passivePrintedReciprocalPoleMagnitude < 9055386 / 10000000 := by
  have hSquare := passivePrintedReciprocalPoleMagnitude_sq
  have hNonnegative : 0 ≤ passivePrintedReciprocalPoleMagnitude :=
    Real.sqrt_nonneg _
  constructor
  · have hLowerSquare :
        (9055385 / 10000000 : ℝ) ^ 2 < 41 / 50 := by
      norm_num
    nlinarith
  · have hUpperSquare :
        (41 / 50 : ℝ) < (9055386 / 10000000) ^ 2 := by
      norm_num
    nlinarith

/-- The positive source decimal exceeds the exact `z` pole by between four and five tenths of a
millionth.
-/
lemma passiveReportedPole_absoluteError :
    (4 / 10000000 : ℝ) <
        |passiveReportedPoleMagnitude - passivePrintedReciprocalPoleMagnitude| ∧
      |passiveReportedPoleMagnitude - passivePrintedReciprocalPoleMagnitude| <
        5 / 10000000 := by
  have hSqueeze := passiveReportedPole_rational_squeeze
  have hPositive :
      0 < passiveReportedPoleMagnitude - passivePrintedReciprocalPoleMagnitude := by
    unfold passiveReportedPoleMagnitude
    nlinarith [hSqueeze.2]
  rw [abs_of_pos hPositive]
  unfold passiveReportedPoleMagnitude
  constructor <;> nlinarith [hSqueeze.1, hSqueeze.2]

/-- The negative signed decimal has the same certified absolute error from its exact `z` pole. -/
lemma passiveReportedNegativePole_absoluteError :
    (4 / 10000000 : ℝ) <
        |(-passiveReportedPoleMagnitude) -
          (-passivePrintedReciprocalPoleMagnitude)| ∧
      |(-passiveReportedPoleMagnitude) -
          (-passivePrintedReciprocalPoleMagnitude)| < 5 / 10000000 := by
  simpa only [neg_sub_neg, abs_sub_comm] using passiveReportedPole_absoluteError

/-!

## E. Printed claim audit

-/

/-- At the passive source point, FMICS'15 Theorem 4's printed expression is exactly `41/50`. -/
lemma passiveCase_printedTheoremFourExpression :
    printedIncoherentStabilityExpression
      DCDRSourceBridge.passiveCaseSourceParameters.G1
      DCDRSourceBridge.passiveCaseSourceParameters.G2
      DCDRSourceBridge.passiveCaseSourceParameters.G3
      DCDRSourceBridge.passiveCaseSourceParameters.k1
      DCDRSourceBridge.passiveCaseSourceParameters.k2 = 41 / 50 := by
  norm_num [printedIncoherentStabilityExpression,
    DCDRSourceBridge.passiveCaseSourceParameters]

/-- Both non-strict hypotheses printed in FMICS'15 Theorem 4 hold at the passive point. -/
lemma passivePrintedTheoremFourConditions :
    PrintedIncoherentStabilityConditions
      DCDRSourceBridge.passiveCaseSourceParameters.G1
      DCDRSourceBridge.passiveCaseSourceParameters.G2
      DCDRSourceBridge.passiveCaseSourceParameters.G3
      DCDRSourceBridge.passiveCaseSourceParameters.k1
      DCDRSourceBridge.passiveCaseSourceParameters.k2 := by
  rw [PrintedIncoherentStabilityConditions,
    passiveCase_printedTheoremFourExpression]
  constructor
  · have hNonnegative : (0 : ℂ) ≤ 41 / 50 :=
      (RCLike.nonneg_iff).2 ⟨by norm_num, by norm_num⟩
    have hSquare : Real.sqrt (41 / 50) ^ 2 = 41 / 50 :=
      Real.sq_sqrt (by norm_num)
    have hSqrtNonnegative : 0 ≤ Real.sqrt (41 / 50) :=
      Real.sqrt_nonneg _
    have hBound : Real.sqrt (41 / 50) ≤ 1 := by
      nlinarith
    rw [Complex.sqrt_of_nonneg hNonnegative, Complex.norm_real,
      Real.norm_eq_abs]
    simp only [Complex.div_ofNat_re, Complex.re_ofNat]
    rw [abs_of_nonneg hSqrtNonnegative]
    exact hBound
  · norm_num

end

end Optics.DCDR
