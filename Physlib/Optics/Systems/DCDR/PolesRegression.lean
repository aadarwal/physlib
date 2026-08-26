/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Systems.DCDR.Poles

/-!
# Exact pole and stability regressions for the double-coupler double-ring

## i. Overview

This file supplies two exact one-delay DCDR fixtures. Both use coherent N7 couplers with
`t = 3/5` and `k = 4/5`. The positive anchor has gains `(61/64, 1, 1)` and reduced reciprocal-Z
poles of norm `1/2`. The audited active fixture has gains `(17/4, 2, 2)`, so all three gains are
strictly greater than one as in FMICS'15 Table 1's optical-amplifier configuration. Its reduced
response has the explicit pole `2 * I`, outside the open unit disk.

Every polynomial and pole fact below is expanded directly from the rational data. The proofs do
not use `mem_candidateSingularities_iff`, either `ResponseReduction` pole-set theorem, or a Schur
or BIBO implication. This makes the unstable fixture capable of failing if its coefficients or
wiring-derived response polynomial change.

FMICS'15 Theorem 4 concerns the separately printed incoherent `1 - k`/`k` response. Its stability
hypotheses are represented by `PrintedIncoherentStabilityConditions`, including the source's
second, nonzero hypothesis recorded by the parity ledger. No theorem identifies those printed
conditions with the coherent N7 fixture. The source's own unprinted coherent branch is the one
modeled here.

## ii. Key definitions and results

- `stableUnitDelayParameters`: exact stable positive anchor.
- `unstableAmplifierParameters`: exact audited `G_i > 1` active fixture.
- `stableResponseReduction`, `unstableResponseReduction`: explicit no-cancellation reductions.
- `stableReducedResponse_isSchurStable`: direct positive stability anchor.
- `unstableReducedResponse_two_mul_I_mem_zPoles`: explicit outside pole.
- `unstableReducedResponse_not_isSchurStable`: direct failure of the Schur premise.

## iii. Table of contents

- A. Printed incoherent audit predicate
- B. Exact coherent parameter fixtures
- C. Hand-expanded rational data and reductions
- D. Stable and unstable reciprocal-Z anchors

## iv. References and non-claims

U. Siddique, S. M. Beillahi, and S. Tahar, "On the Formal Analysis of Photonic Signal
Processing Systems", FMICS 2015, LNCS 9128, Table 1 and Theorem 4. The corresponding HOL corpus
audit is recorded at `HOL-CORPUS.md:307-308`.

The active fixture is an exact coherent regression, not a reconstruction of the paper's passive
decimal pole list. The printed incoherent theorem is retained only as an audit predicate. No
physical resonance theorem, physical-frequency interpretation, material amplifier model,
passivity claim, power observable, or DCDR BIBO theorem is asserted. S4's BIBO equivalence at
`Physlib/Optics/Systems/DelayTransfer/Stability.lean:374-403` is only for
`ProperCausalOnePole`; both denominators here have a nonzero quadratic coefficient.
-/

@[expose] public section

namespace Optics.DCDR

noncomputable section

open Polynomial

/-!

## A. Printed incoherent audit predicate

-/

/-- The complex expression appearing in FMICS'15 Theorem 4's printed incoherent conditions. -/
def printedIncoherentStabilityExpression
    (G1 G2 G3 k1 k2 : ℂ) : ℂ :=
  k1 * k2 * G1 * G2 + (1 - k1) * (1 - k2) * G2 * G3

/-- The two printed incoherent stability hypotheses, including the source's necessary nonzero
condition for the displayed roots to be valid poles. -/
def PrintedIncoherentStabilityConditions
    (G1 G2 G3 k1 k2 : ℂ) : Prop :=
  ‖printedIncoherentStabilityExpression G1 G2 G3 k1 k2‖ ≤ 1 ∧
    printedIncoherentStabilityExpression G1 G2 G3 k1 k2 ≠ 0

/-!

## B. Exact coherent parameter fixtures

-/

/-- The exact `3/5` through, `4/5` cross-amplitude coherent coupler. -/
def poleRegressionCoupler : DirectionalCoupler.Parameters where
  throughAmplitude := 3 / 5
  crossAmplitude := 4 / 5

/-- A coherent stable point with loop polynomial `-(1/4) * q^2`. -/
def stableUnitDelayParameters : UnitDelayParameters where
  firstCoupler := poleRegressionCoupler
  secondCoupler := poleRegressionCoupler
  upperGain := 61 / 64
  lowerGain := 1
  feedbackGain := 1

/-- An exact active-amplifier point whose loop polynomial is `-4 * q^2`. -/
def unstableAmplifierParameters : UnitDelayParameters where
  firstCoupler := poleRegressionCoupler
  secondCoupler := poleRegressionCoupler
  upperGain := 17 / 4
  lowerGain := 2
  feedbackGain := 2

/-- The stable positive anchor has algebraically admissible nonnegative gains. -/
lemma stableUnitDelayParameters_isAdmissible :
    stableUnitDelayParameters.IsAdmissible := by
  norm_num [UnitDelayParameters.IsAdmissible, stableUnitDelayParameters]

/-- The active fixture has algebraically admissible nonnegative gains. -/
lemma unstableAmplifierParameters_isAdmissible :
    unstableAmplifierParameters.IsAdmissible := by
  norm_num [UnitDelayParameters.IsAdmissible, unstableAmplifierParameters]

/-- All three active-fixture gains satisfy Table 1's strict amplifier inequalities. -/
lemma unstableAmplifierParameters_all_gains_gt_one :
    1 < unstableAmplifierParameters.upperGain ∧
      1 < unstableAmplifierParameters.lowerGain ∧
        1 < unstableAmplifierParameters.feedbackGain := by
  norm_num [unstableAmplifierParameters]

/-!

## C. Hand-expanded rational data and reductions

-/

/-- The stable fixture's directly expanded response numerator. -/
def stableNumerator : Polynomial ℂ :=
  C (-19 / 64) * X + C (-61 / 64) * X ^ 3

/-- The stable fixture's directly expanded response denominator. -/
def stableDenominator : Polynomial ℂ :=
  1 + C (1 / 4) * X ^ 2

/-- The active fixture's directly expanded response numerator. -/
def unstableNumerator : Polynomial ℂ :=
  C (1 / 4) * X - C 17 * X ^ 3

/-- The active fixture's directly expanded response denominator. -/
def unstableDenominator : Polynomial ℂ :=
  1 + C 4 * X ^ 2

/-- Direct expansion of the stable loop data gives `-(1/4) * q^2`. -/
lemma stable_loopPolynomial_expansion :
    stableUnitDelayParameters.loopPolynomial = -(C (1 / 4) * X ^ 2) := by
  apply Polynomial.funext
  intro q
  norm_num [UnitDelayParameters.loopPolynomial, UnitDelayParameters.upperPolynomial,
    UnitDelayParameters.lowerPolynomial, UnitDelayParameters.feedbackPolynomial,
    stableUnitDelayParameters, poleRegressionCoupler,
    DirectionalCoupler.crossCoefficient, pow_succ, Complex.I_mul_I]
  ring_nf
  rw [show Complex.I ^ 2 = (-1 : ℂ) by
    norm_num [pow_two, Complex.I_mul_I]]
  ring

/-- Direct expansion of the stable rational data gives the displayed denominator. -/
lemma stable_denominatorPolynomial_expansion :
    stableUnitDelayParameters.denominatorPolynomial = stableDenominator := by
  rw [UnitDelayParameters.denominatorPolynomial, stable_loopPolynomial_expansion]
  simp [stableDenominator]

/-- Direct expansion of all four scalar factors gives the displayed stable numerator. -/
lemma stable_responseNumeratorPolynomial_expansion :
    stableUnitDelayParameters.responseNumeratorPolynomial = stableNumerator := by
  apply Polynomial.funext
  intro q
  norm_num [UnitDelayParameters.responseNumeratorPolynomial,
    UnitDelayParameters.directPolynomial, UnitDelayParameters.denominatorPolynomial,
    UnitDelayParameters.loopPolynomial, UnitDelayParameters.feedbackReadoutPolynomial,
    UnitDelayParameters.feedbackDrivePolynomial, UnitDelayParameters.upperPolynomial,
    UnitDelayParameters.lowerPolynomial, UnitDelayParameters.feedbackPolynomial,
    stableUnitDelayParameters, poleRegressionCoupler,
    DirectionalCoupler.crossCoefficient, stableNumerator, pow_succ,
    Complex.I_mul_I]
  ring_nf
  rw [show Complex.I ^ 2 = (-1 : ℂ) by
      norm_num [pow_two, Complex.I_mul_I],
    show Complex.I ^ 4 = (1 : ℂ) by
      norm_num [pow_succ, Complex.I_mul_I]]
  ring

/-- Direct expansion of the active loop data gives `-4 * q^2`. -/
lemma unstable_loopPolynomial_expansion :
    unstableAmplifierParameters.loopPolynomial = -(C 4 * X ^ 2) := by
  apply Polynomial.funext
  intro q
  norm_num [UnitDelayParameters.loopPolynomial, UnitDelayParameters.upperPolynomial,
    UnitDelayParameters.lowerPolynomial, UnitDelayParameters.feedbackPolynomial,
    unstableAmplifierParameters, poleRegressionCoupler,
    DirectionalCoupler.crossCoefficient, pow_succ, Complex.I_mul_I]
  ring_nf
  rw [show Complex.I ^ 2 = (-1 : ℂ) by
    norm_num [pow_two, Complex.I_mul_I]]
  ring

/-- Direct expansion of the active rational data gives the displayed denominator. -/
lemma unstable_denominatorPolynomial_expansion :
    unstableAmplifierParameters.denominatorPolynomial = unstableDenominator := by
  rw [UnitDelayParameters.denominatorPolynomial, unstable_loopPolynomial_expansion]
  simp [unstableDenominator]

/-- Direct expansion of all four scalar factors gives the displayed active numerator. -/
lemma unstable_responseNumeratorPolynomial_expansion :
    unstableAmplifierParameters.responseNumeratorPolynomial = unstableNumerator := by
  apply Polynomial.funext
  intro q
  norm_num [UnitDelayParameters.responseNumeratorPolynomial,
    UnitDelayParameters.directPolynomial, UnitDelayParameters.denominatorPolynomial,
    UnitDelayParameters.loopPolynomial, UnitDelayParameters.feedbackReadoutPolynomial,
    UnitDelayParameters.feedbackDrivePolynomial, UnitDelayParameters.upperPolynomial,
    UnitDelayParameters.lowerPolynomial, UnitDelayParameters.feedbackPolynomial,
    unstableAmplifierParameters, poleRegressionCoupler,
    DirectionalCoupler.crossCoefficient, unstableNumerator, pow_succ,
    Complex.I_mul_I]
  ring_nf
  rw [show Complex.I ^ 2 = (-1 : ℂ) by
      norm_num [pow_two, Complex.I_mul_I],
    show Complex.I ^ 4 = (1 : ℂ) by
      norm_num [pow_succ, Complex.I_mul_I]]
  ring

/-- The stable numerator is a nonzero polynomial. -/
lemma stableNumerator_ne_zero : stableNumerator ≠ 0 := by
  intro hZero
  have hEvaluation := congrArg (Polynomial.eval 1) hZero
  norm_num [stableNumerator] at hEvaluation

/-- The stable denominator is a nonzero polynomial. -/
lemma stableDenominator_ne_zero : stableDenominator ≠ 0 := by
  intro hZero
  have hEvaluation := congrArg (Polynomial.eval 0) hZero
  norm_num [stableDenominator] at hEvaluation

/-- An explicit Bezout identity certifies the stable numerator and denominator as coprime. -/
lemma stableNumerator_isCoprime : IsCoprime stableNumerator stableDenominator := by
  refine ⟨C (-16 / 225) * X,
    1 - C (61 / 225) * X ^ 2, ?_⟩
  apply Polynomial.funext
  intro q
  norm_num [stableNumerator, stableDenominator]
  ring

/-- The active numerator is a nonzero polynomial. -/
lemma unstableNumerator_ne_zero : unstableNumerator ≠ 0 := by
  intro hZero
  have hEvaluation := congrArg (Polynomial.eval 1) hZero
  norm_num [unstableNumerator] at hEvaluation

/-- The active denominator is a nonzero polynomial. -/
lemma unstableDenominator_ne_zero : unstableDenominator ≠ 0 := by
  intro hZero
  have hEvaluation := congrArg (Polynomial.eval 0) hZero
  norm_num [unstableDenominator] at hEvaluation

/-- An explicit Bezout identity certifies the active numerator and denominator as coprime. -/
lemma unstableNumerator_isCoprime : IsCoprime unstableNumerator unstableDenominator := by
  refine ⟨C (-8 / 9) * X,
    1 - C (34 / 9) * X ^ 2, ?_⟩
  apply Polynomial.funext
  intro q
  norm_num [unstableNumerator, unstableDenominator]
  ring

/-- The exact coprime reduced quotient at the stable positive anchor. -/
def stableReducedResponse : DelayTransfer.ReducedRationalResponse where
  numerator := stableNumerator
  denominator := stableDenominator
  numerator_ne_zero := stableNumerator_ne_zero
  denominator_ne_zero := stableDenominator_ne_zero
  isCoprime := stableNumerator_isCoprime

/-- The exact coprime reduced quotient at the active unstable anchor. -/
def unstableReducedResponse : DelayTransfer.ReducedRationalResponse where
  numerator := unstableNumerator
  denominator := unstableDenominator
  numerator_ne_zero := unstableNumerator_ne_zero
  denominator_ne_zero := unstableDenominator_ne_zero
  isCoprime := unstableNumerator_isCoprime

/-- The stable response reduction removes only the unit polynomial. -/
def stableRationalReduction : DelayTransfer.RationalReduction where
  rawNumerator := stableUnitDelayParameters.responseNumeratorPolynomial
  rawDenominator := stableUnitDelayParameters.denominatorPolynomial
  cancelledFactor := 1
  reduced := stableReducedResponse
  cancelledFactor_ne_zero := one_ne_zero
  rawNumerator_eq := by
    rw [stable_responseNumeratorPolynomial_expansion]
    simp [stableReducedResponse]
  rawDenominator_eq := by
    rw [stable_denominatorPolynomial_expansion]
    simp [stableReducedResponse]

/-- The active response reduction removes only the unit polynomial. -/
def unstableRationalReduction : DelayTransfer.RationalReduction where
  rawNumerator := unstableAmplifierParameters.responseNumeratorPolynomial
  rawDenominator := unstableAmplifierParameters.denominatorPolynomial
  cancelledFactor := 1
  reduced := unstableReducedResponse
  cancelledFactor_ne_zero := one_ne_zero
  rawNumerator_eq := by
    rw [unstable_responseNumeratorPolynomial_expansion]
    simp [unstableReducedResponse]
  rawDenominator_eq := by
    rw [unstable_denominatorPolynomial_expansion]
    simp [unstableReducedResponse]

/-- The stable reduction is tied to the selected compiled DCDR response polynomials. -/
def stableResponseReduction : ResponseReduction stableUnitDelayParameters where
  reduction := stableRationalReduction
  rawNumerator_eq := rfl
  rawDenominator_eq := rfl

/-- The active reduction is tied to the selected compiled DCDR response polynomials. -/
def unstableResponseReduction : ResponseReduction unstableAmplifierParameters where
  reduction := unstableRationalReduction
  rawNumerator_eq := rfl
  rawDenominator_eq := rfl

/-- The stable reduction satisfies S4's explicit no-pole-cancellation condition everywhere. -/
lemma stableResponseReduction_noPoleCancellation :
    ∀ q ∈ stableRationalReduction.rawDenominatorRoots,
      stableRationalReduction.NoPoleCancellation q := by
  intro q _hq
  simp [DelayTransfer.RationalReduction.NoPoleCancellation,
    stableRationalReduction]

/-- The active reduction satisfies S4's explicit no-pole-cancellation condition everywhere. -/
lemma unstableResponseReduction_noPoleCancellation :
    ∀ q ∈ unstableRationalReduction.rawDenominatorRoots,
      unstableRationalReduction.NoPoleCancellation q := by
  intro q _hq
  simp [DelayTransfer.RationalReduction.NoPoleCancellation,
    unstableRationalReduction]

/-!

## D. Stable and unstable reciprocal-Z anchors

-/

/-- The stable denominator has a nonzero quadratic coefficient, so it is not an S4 one-pole
denominator. -/
lemma stableDenominator_ne_onePoleDenominator (a : ℂ) :
    stableDenominator ≠
      (DelayTransfer.ReducedRationalResponse.onePoleReducedResponse a).denominator := by
  intro hEqual
  have hCoefficient := congrArg (fun polynomial => polynomial.coeff 2) hEqual
  norm_num [stableDenominator,
    DelayTransfer.ReducedRationalResponse.onePoleReducedResponse] at hCoefficient

/-- The active denominator has a nonzero quadratic coefficient, so it is not an S4 one-pole
denominator. -/
lemma unstableDenominator_ne_onePoleDenominator (a : ℂ) :
    unstableDenominator ≠
      (DelayTransfer.ReducedRationalResponse.onePoleReducedResponse a).denominator := by
  intro hEqual
  have hCoefficient := congrArg (fun polynomial => polynomial.coeff 2) hEqual
  norm_num [unstableDenominator,
    DelayTransfer.ReducedRationalResponse.onePoleReducedResponse] at hCoefficient

/-- Every directly expanded reciprocal-Z pole of the stable quotient lies inside the unit disk. -/
lemma stableReducedResponse_isSchurStable :
    stableReducedResponse.IsSchurStable := by
  intro z hz
  rcases hz with ⟨hzNonzero, hzRoot⟩
  change stableDenominator.eval z⁻¹ = 0 at hzRoot
  have hEquation : 1 + (1 / 4 : ℂ) * z⁻¹ ^ 2 = 0 := by
    simpa [stableDenominator] using hzRoot
  have hInverseSquare : z⁻¹ ^ 2 = (-4 : ℂ) := by
    linear_combination 4 * hEquation
  have hNorm := congrArg norm hInverseSquare
  norm_num [norm_pow, norm_inv] at hNorm
  have hNormNonzero : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hzNonzero
  field_simp [hNormNonzero] at hNorm
  nlinarith [norm_nonneg z]

/-- Direct substitution shows that `2 * I` is a reduced reciprocal-Z pole of the active fixture. -/
lemma unstableReducedResponse_two_mul_I_mem_zPoles :
    (2 : ℂ) * Complex.I ∈ unstableReducedResponse.zPoles := by
  constructor
  · exact mul_ne_zero (by norm_num) Complex.I_ne_zero
  · change unstableDenominator.eval (((2 : ℂ) * Complex.I)⁻¹) = 0
    rw [mul_inv_rev, Complex.inv_I]
    norm_num [unstableDenominator]
    ring_nf
    simp

/-- The displayed active-fixture pole has norm two, outside the open unit disk. -/
lemma norm_two_mul_I : ‖(2 : ℂ) * Complex.I‖ = 2 := by
  norm_num

/-- The active fixture directly fails the reduced Schur predicate. -/
lemma unstableReducedResponse_not_isSchurStable :
    ¬unstableReducedResponse.IsSchurStable := by
  intro hStable
  have hInside := hStable ((2 : ℂ) * Complex.I)
    unstableReducedResponse_two_mul_I_mem_zPoles
  rw [norm_two_mul_I] at hInside
  norm_num at hInside

/-- The same directly expanded pole is an actual pole of the response-indexed active reduction. -/
lemma unstableResponseReduction_two_mul_I_mem_actualPoles :
    (2 : ℂ) * Complex.I ∈ unstableResponseReduction.actualPoles := by
  simpa [ResponseReduction.actualPoles, unstableResponseReduction,
    unstableRationalReduction] using unstableReducedResponse_two_mul_I_mem_zPoles

end


end Optics.DCDR
