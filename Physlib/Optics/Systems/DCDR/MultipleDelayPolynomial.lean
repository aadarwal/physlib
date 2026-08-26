/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Systems.DCDR.MultipleDelay

/-!
# Polynomial and reduction layer for the multiple-delay DCDR

## i. Overview

This file derives the coherent numerator and denominator shapes of the multiple-delay N7 family.
The denominator degree is at most `max (m1 + m3) (m2 + m3)`; the numerator has the two direct
path degrees and the three-path degree `m1 + m2 + m3`.

`MultipleDelayResponseReduction` reuses S4's `RationalReduction` certificate from
`Physlib/Optics/Systems/DelayTransfer/Poles.lean:168-183`. Actual poles use the reduced
reciprocal-`z` set and degree bound at
`Physlib/Optics/Systems/DelayTransfer/Stability.lean:225-243`, with `q = z⁻¹`.
Cancellation can lower, but cannot raise, the raw denominator degree.

## ii. Key results

- `MultipleDelayParameters.loopPolynomial_expansion`: the two feedback path pairs.
- `MultipleDelayParameters.responseNumeratorPolynomial_expansion`: the three retained terms.
- `MultipleDelayParameters.denominatorPolynomial_natDegree_le`: denominator shape bound.
- `MultipleDelayParameters.responseNumeratorPolynomial_natDegree_le`: numerator shape bound.
- `MultipleDelayResponseReduction.ncard_actualPoles_le_rawDenominatorDegree`: generic bound.
- `MultipleDelayResponseReduction.ncard_actualPoles_le_delayShape`: DCDR specialization.

## iii. Table of contents

- A. Coherent polynomial expansions and degree bounds
- B. Cancellation-aware reduction and pole bounds

## iv. References

No result here claims physical resonance, coherent--incoherent equivalence, BIBO stability beyond
S4P's stated gate, normalized-modal or electromagnetic power, causality or time-domain behavior,
a physical-frequency interpretation, or any fact about the unavailable HOL script.

S4P restricts its Schur/BIBO result to the proper causal one-pole class at
`Physlib/Optics/Systems/DelayTransfer/Stability.lean:424-457`.

U. Siddique, S. M. Beillahi, and S. Tahar, “On the Formal Analysis of Photonic Signal
Processing Systems”, FMICS 2015, LNCS 9128, Theorem 3 and Table 1, pp. 173--174.
-/

@[expose] public section

namespace Optics.DCDR

noncomputable section

open Polynomial

/-!

## A. Coherent polynomial expansions and degree bounds

-/

/-- The coefficient of the lower-path term in the coherent loop polynomial. -/
def MultipleDelayParameters.lowerLoopCoefficient
    (p : MultipleDelayParameters) : ℂ :=
  (p.secondCoupler.throughAmplitude : ℂ) * p.firstCoupler.throughAmplitude

/-- The coefficient of the upper-path term in the coherent loop polynomial. -/
def MultipleDelayParameters.upperLoopCoefficient
    (p : MultipleDelayParameters) : ℂ :=
  DirectionalCoupler.crossCoefficient p.secondCoupler *
    DirectionalCoupler.crossCoefficient p.firstCoupler

/-- The coherent loop is the sum of its two path-pair monomials. -/
lemma MultipleDelayParameters.loopPolynomial_expansion
    (p : MultipleDelayParameters) :
    p.loopPolynomial =
      C p.lowerLoopCoefficient * p.lowerPolynomial * p.feedbackPolynomial +
        C p.upperLoopCoefficient * p.upperPolynomial * p.feedbackPolynomial := by
  simp [MultipleDelayParameters.loopPolynomial,
    MultipleDelayParameters.lowerLoopCoefficient,
    MultipleDelayParameters.upperLoopCoefficient]
  ring

/-- The coefficient of the retained direct upper-path term. -/
def MultipleDelayParameters.directUpperCoefficient
    (p : MultipleDelayParameters) : ℂ :=
  (p.secondCoupler.throughAmplitude : ℂ) * p.firstCoupler.throughAmplitude

/-- The coefficient of the retained direct lower-path term. -/
def MultipleDelayParameters.directLowerCoefficient
    (p : MultipleDelayParameters) : ℂ :=
  DirectionalCoupler.crossCoefficient p.secondCoupler *
    DirectionalCoupler.crossCoefficient p.firstCoupler

/-- The coherent coupler coefficient of the three-path numerator monomial. -/
def MultipleDelayParameters.cubicCouplerCoefficient
    (p : MultipleDelayParameters) : ℂ :=
  ((p.firstCoupler.throughAmplitude : ℂ) ^ 2 -
      DirectionalCoupler.crossCoefficient p.firstCoupler ^ 2) *
    (DirectionalCoupler.crossCoefficient p.secondCoupler ^ 2 -
      (p.secondCoupler.throughAmplitude : ℂ) ^ 2)

/-- Direct expansion cancels the repeated-arm terms and leaves the Theorem-3 degree shape. -/
lemma MultipleDelayParameters.responseNumeratorPolynomial_expansion
    (p : MultipleDelayParameters) :
    p.responseNumeratorPolynomial =
      C p.directUpperCoefficient * p.upperPolynomial +
        C p.directLowerCoefficient * p.lowerPolynomial +
          C p.cubicCouplerCoefficient * p.upperPolynomial * p.lowerPolynomial *
            p.feedbackPolynomial := by
  simp [MultipleDelayParameters.responseNumeratorPolynomial,
    MultipleDelayParameters.directPolynomial,
    MultipleDelayParameters.denominatorPolynomial,
    MultipleDelayParameters.loopPolynomial,
    MultipleDelayParameters.feedbackReadoutPolynomial,
    MultipleDelayParameters.feedbackDrivePolynomial,
    MultipleDelayParameters.directUpperCoefficient,
    MultipleDelayParameters.directLowerCoefficient,
    MultipleDelayParameters.cubicCouplerCoefficient]
  ring

/-- The upper path polynomial has degree at most `m1`. -/
lemma MultipleDelayParameters.upperPolynomial_natDegree_le
    (p : MultipleDelayParameters) : p.upperPolynomial.natDegree ≤ p.m1 :=
  Polynomial.natDegree_C_mul_X_pow_le p.upperGain p.m1

/-- The lower path polynomial has degree at most `m2`. -/
lemma MultipleDelayParameters.lowerPolynomial_natDegree_le
    (p : MultipleDelayParameters) : p.lowerPolynomial.natDegree ≤ p.m2 :=
  Polynomial.natDegree_C_mul_X_pow_le p.lowerGain p.m2

/-- The feedback path polynomial has degree at most `m3`. -/
lemma MultipleDelayParameters.feedbackPolynomial_natDegree_le
    (p : MultipleDelayParameters) : p.feedbackPolynomial.natDegree ≤ p.m3 :=
  Polynomial.natDegree_C_mul_X_pow_le p.feedbackGain p.m3

/-- The coherent denominator degree is bounded by the two printed path-pair exponents. -/
lemma MultipleDelayParameters.denominatorPolynomial_natDegree_le
    (p : MultipleDelayParameters) :
    p.denominatorPolynomial.natDegree ≤ max (p.m1 + p.m3) (p.m2 + p.m3) := by
  have hLowerScaled :
      (C p.lowerLoopCoefficient * p.lowerPolynomial).natDegree ≤ p.m2 := by
    exact (Polynomial.natDegree_C_mul_le _ _).trans
      p.lowerPolynomial_natDegree_le
  have hLower :
      (C p.lowerLoopCoefficient * p.lowerPolynomial *
        p.feedbackPolynomial).natDegree ≤ p.m2 + p.m3 := by
    exact Polynomial.natDegree_mul_le.trans
      (Nat.add_le_add hLowerScaled p.feedbackPolynomial_natDegree_le)
  have hUpperScaled :
      (C p.upperLoopCoefficient * p.upperPolynomial).natDegree ≤ p.m1 := by
    exact (Polynomial.natDegree_C_mul_le _ _).trans
      p.upperPolynomial_natDegree_le
  have hUpper :
      (C p.upperLoopCoefficient * p.upperPolynomial *
        p.feedbackPolynomial).natDegree ≤ p.m1 + p.m3 := by
    exact Polynomial.natDegree_mul_le.trans
      (Nat.add_le_add hUpperScaled p.feedbackPolynomial_natDegree_le)
  have hLoop :
      (C p.lowerLoopCoefficient * p.lowerPolynomial * p.feedbackPolynomial +
        C p.upperLoopCoefficient * p.upperPolynomial *
          p.feedbackPolynomial).natDegree ≤
        max (p.m2 + p.m3) (p.m1 + p.m3) :=
    (Polynomial.natDegree_add_le _ _).trans (max_le_max hLower hUpper)
  rw [MultipleDelayParameters.denominatorPolynomial,
    p.loopPolynomial_expansion]
  calc
    _ ≤ max (1 : Polynomial ℂ).natDegree
        (C p.lowerLoopCoefficient * p.lowerPolynomial * p.feedbackPolynomial +
          C p.upperLoopCoefficient * p.upperPolynomial *
            p.feedbackPolynomial).natDegree := Polynomial.natDegree_sub_le _ _
    _ ≤ max 0 (max (p.m2 + p.m3) (p.m1 + p.m3)) :=
      max_le_max (by simp) hLoop
    _ = max (p.m1 + p.m3) (p.m2 + p.m3) := by simp [max_comm]

/-- The coherent numerator degree has the two-direct-path plus three-path shape. -/
lemma MultipleDelayParameters.responseNumeratorPolynomial_natDegree_le
    (p : MultipleDelayParameters) :
    p.responseNumeratorPolynomial.natDegree ≤
      max (max p.m1 p.m2) (p.m1 + p.m2 + p.m3) := by
  have hUpper :
      (C p.directUpperCoefficient * p.upperPolynomial).natDegree ≤ p.m1 := by
    exact (Polynomial.natDegree_C_mul_le _ _).trans
      p.upperPolynomial_natDegree_le
  have hLower :
      (C p.directLowerCoefficient * p.lowerPolynomial).natDegree ≤ p.m2 := by
    exact (Polynomial.natDegree_C_mul_le _ _).trans
      p.lowerPolynomial_natDegree_le
  have hCubicUpper :
      (C p.cubicCouplerCoefficient * p.upperPolynomial).natDegree ≤ p.m1 := by
    exact (Polynomial.natDegree_C_mul_le _ _).trans
      p.upperPolynomial_natDegree_le
  have hCubicUpperLower :
      (C p.cubicCouplerCoefficient * p.upperPolynomial *
        p.lowerPolynomial).natDegree ≤ p.m1 + p.m2 := by
    exact Polynomial.natDegree_mul_le.trans
      (Nat.add_le_add hCubicUpper p.lowerPolynomial_natDegree_le)
  have hCubic :
      (C p.cubicCouplerCoefficient * p.upperPolynomial * p.lowerPolynomial *
        p.feedbackPolynomial).natDegree ≤ p.m1 + p.m2 + p.m3 := by
    exact Polynomial.natDegree_mul_le.trans
      (Nat.add_le_add hCubicUpperLower p.feedbackPolynomial_natDegree_le)
  have hDirect :
      (C p.directUpperCoefficient * p.upperPolynomial +
        C p.directLowerCoefficient * p.lowerPolynomial).natDegree ≤
        max p.m1 p.m2 :=
    (Polynomial.natDegree_add_le _ _).trans (max_le_max hUpper hLower)
  rw [p.responseNumeratorPolynomial_expansion]
  exact (Polynomial.natDegree_add_le _ _).trans (max_le_max hDirect hCubic)

/-!

## B. Cancellation-aware reduction and pole bounds

-/

/-- An S4 common-factor reduction
(`Physlib/Optics/Systems/DelayTransfer/Poles.lean:168-183`) for this response. -/
structure MultipleDelayResponseReduction (p : MultipleDelayParameters) where
  /-- The S4 common-factor reduction at
  `Physlib/Optics/Systems/DelayTransfer/Poles.lean:168-183`. -/
  reduction : DelayTransfer.RationalReduction
  /-- The raw numerator is the selected coherent response numerator. -/
  rawNumerator_eq : reduction.rawNumerator = p.responseNumeratorPolynomial
  /-- The raw denominator is the coherent internal solve denominator. -/
  rawDenominator_eq : reduction.rawDenominator = p.denominatorPolynomial

namespace MultipleDelayResponseReduction

variable {p : MultipleDelayParameters}

/-- Reduced reciprocal-`z` poles as defined in
`Physlib/Optics/Systems/DelayTransfer/Stability.lean:225-243`. -/
def actualPoles (certificate : MultipleDelayResponseReduction p) : Set ℂ :=
  certificate.reduction.reduced.zPoles

/-- The certified reciprocal-coordinate pole set is finite. -/
lemma finite_actualPoles (certificate : MultipleDelayResponseReduction p) :
    certificate.actualPoles.Finite :=
  certificate.reduction.reduced.finite_zPoles

/-- The actual reciprocal-`z` pole count is at most the reduced denominator degree. -/
lemma ncard_actualPoles_le_reducedDenominatorDegree
    (certificate : MultipleDelayResponseReduction p) :
    certificate.actualPoles.ncard ≤
      certificate.reduction.reduced.denominator.natDegree :=
  certificate.reduction.reduced.ncard_zPoles_le_natDegree

/-- Cancellation cannot raise the denominator degree above the selected raw denominator degree. -/
lemma reducedDenominator_natDegree_le_rawDenominatorDegree
    (certificate : MultipleDelayResponseReduction p) :
    certificate.reduction.reduced.denominator.natDegree ≤
      p.denominatorPolynomial.natDegree := by
  have hDivides : certificate.reduction.reduced.denominator ∣
      certificate.reduction.rawDenominator := by
    refine ⟨certificate.reduction.cancelledFactor, ?_⟩
    exact certificate.reduction.rawDenominator_eq.trans (mul_comm _ _)
  calc
    certificate.reduction.reduced.denominator.natDegree ≤
        certificate.reduction.rawDenominator.natDegree :=
      Polynomial.natDegree_le_of_dvd hDivides
        certificate.reduction.rawDenominator_ne_zero
    _ = p.denominatorPolynomial.natDegree :=
      congrArg Polynomial.natDegree certificate.rawDenominator_eq

/-- The actual reciprocal-`z` pole count is at most the raw denominator degree. -/
lemma ncard_actualPoles_le_rawDenominatorDegree
    (certificate : MultipleDelayResponseReduction p) :
    certificate.actualPoles.ncard ≤ p.denominatorPolynomial.natDegree :=
  certificate.ncard_actualPoles_le_reducedDenominatorDegree.trans
    certificate.reducedDenominator_natDegree_le_rawDenominatorDegree

/-- The selected multiple-delay quotient has at most the two path-pair degree bound in `z`. -/
lemma ncard_actualPoles_le_delayShape
    (certificate : MultipleDelayResponseReduction p) :
    certificate.actualPoles.ncard ≤ max (p.m1 + p.m3) (p.m2 + p.m3) :=
  certificate.ncard_actualPoles_le_rawDenominatorDegree.trans
    p.denominatorPolynomial_natDegree_le

/-- Away from the cancelled factor and reduced denominator, the reduction evaluates to the
retained raw multiple-delay quotient. -/
lemma reduced_eval_eq_responseModel
    (certificate : MultipleDelayResponseReduction p) (hp : p.IsAdmissible) (q : ℂ)
    (hFactor : certificate.reduction.NoPoleCancellation q)
    (hReduced : q ∈ certificate.reduction.reduced.evaluationDomain) :
    certificate.reduction.reduced.eval q = (p.responseModel hp).eval (fun _ => q) := by
  change certificate.reduction.cancelledFactor.eval q ≠ 0 at hFactor
  change certificate.reduction.reduced.denominator.eval q ≠ 0 at hReduced
  rw [DelayTransfer.ReducedRationalResponse.eval,
    DelayTransfer.RationalModel.eval_eq]
  simp only [MultipleDelayParameters.responseModel,
    MvPolynomial.eval_toMvPolynomial]
  rw [← certificate.rawNumerator_eq, ← certificate.rawDenominator_eq,
    certificate.reduction.rawNumerator_eq,
    certificate.reduction.rawDenominator_eq, eval_mul, eval_mul]
  field_simp

/-- On the common N5 and reduced-quotient domain, the selected responses agree. -/
lemma reduced_eval_eq_rationalEliminationResponse
    (certificate : MultipleDelayResponseReduction p) (hp : p.IsAdmissible) (q : ℂ)
    (hDomain : (fun _ : Fin 1 => q) ∈
      (multipleDelayRationalNetlist p).responseDomain)
    (hFactor : certificate.reduction.NoPoleCancellation q)
    (hReduced : q ∈ certificate.reduction.reduced.evaluationDomain) :
    certificate.reduction.reduced.eval q =
      multipleDelayRationalEliminationResponse p q hDomain := by
  rw [certificate.reduced_eval_eq_responseModel hp q hFactor hReduced,
    multipleDelayRationalEliminationResponse_eq_responseModel p hp q hDomain]

end MultipleDelayResponseReduction

end

end Optics.DCDR
