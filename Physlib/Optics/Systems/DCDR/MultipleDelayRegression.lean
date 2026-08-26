/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Systems.DCDR.MultipleDelaySource

/-!
# Exact multiple-delay regressions for the double-coupler double-ring

## i. Overview

This file gives each of FMICS'15 Table 1's four DCDR rows an exact source-data fixture. Every
fixture has a directly expanded printed Theorem 3 numerator and denominator. Those polynomial
anchors depend on the stored exponents, so changing a row's `m_i` data breaks the regression
rather than merely changing a descriptive predicate.

The distinct-delay coherent fixture uses `(m1, m2, m3) = (2, 1, 3)`. Its selected response is
`-q / (1-q^4)`, with no cancellation. Its raw denominator has degree four and its reciprocal-`z`
pole set, under `q = z⁻¹`, is proved directly to be `{1, -1, I, -I}`. Thus the pole count is
exactly four and attains the denominator degree. This executable witness makes the slice-5
at-most-two result at `Physlib/Optics/Systems/DCDR/SourceBridge.lean:154-162` visibly specific
to the unit-delay family.

The polynomial expansions, coprimality identity, four-root enumeration, and cardinality proof
unfold the fixture data and use polynomial or complex-field primitives. They do not invoke the
production degree bounds or pole-cardinality lemmas, so a wrong gain, exponent, coordinate, or
coupler coefficient can make them fail.

The unit-delay bridge is exercised at gains `(2, 3/2, 1/2)` and `q = 1/2`, so its feedback gain
is nonzero and two gains have non-unit magnitude. Both rational families independently produce
the selected response `1`. A separate negative-upper-gain fixture has empty old response domain
and nonempty embedded response domain. It makes the old admissibility hypothesis on the production
domain bridge visibly load-bearing.

## ii. Key results

- `DCDRSourceBridge.tableActiveUnitDelay_printedPolynomials`: the active unit-delay row.
- `DCDRSourceBridge.tableOpticalAmplifier_printedPolynomials`: the `G_i > 1` row.
- `DCDRSourceBridge.tablePassive_printedPolynomials`: the unit-gain passive row.
- `DCDRSourceBridge.tableMultipleDelay_printedPolynomials`: the distinct-exponent row.
- `DCDR.tightMultipleDelay_denominatorPolynomial_expansion`: exact degree-four denominator.
- `DCDR.tightMultipleDelay_responseNumeratorPolynomial_expansion`: exact noncancelled numerator.
- `DCDR.tightMultipleDelay_zPoles_eq_four`: direct reciprocal-coordinate pole enumeration.
- `DCDR.tightMultipleDelay_ncard_actualPoles_eq_natDegree`: tight cardinality bound.
- `DCDR.unitDelayBridge_both_responses_eq_one`: both rational families at a nontrivial point.
- `DCDR.unitDelayValidityGate_is_loadBearing`: the negative-gain validity counterexample.

## iii. Table of contents

- A. FMICS'15 Table 1 source-data fixtures
- B. Coherent distinct-delay tight pole fixture
- C. Primitive reciprocal-coordinate pole enumeration
- D. Admissibility-gated unit-delay bridge sentinels

## iv. References

These algebraic fixtures do not claim physical resonance, coherent--incoherent equivalence, BIBO
stability beyond S4P's gate, normalized-modal or electromagnetic power, causality or time-domain
behavior, a physical-frequency interpretation, or any fact about the unavailable HOL script.

S4P restricts its Schur/BIBO result to the proper causal one-pole class at
`Physlib/Optics/Systems/DelayTransfer/Stability.lean:424-457`.

FMICS'15 Eq. 3 prints verbatim: “The general expression for the photonic transmittance is given
as follows: `T_i = t_{a_i} G_i z^{m_i}`.” This file uses the unit-attenuation formal-`q`
specialization and the reciprocal reparameterization `q = z⁻¹` defined at
`Physlib/Optics/Systems/DelayTransfer/Evaluation.lean:397-455`.

FMICS'15 Table 1 prints “Active DCDR Circuit with Unit Delay” with `m1 = m2 = m3 = 1`,
“Optical Amplifier in the Fiber Path” with those delays and `G_i > 1`,
“Passive DCDR Circuit” with `G1 = G2 = G3 = 1`, and “DCDR with Multiple Delay” with
different combinations of `m_i`.

U. Siddique, S. M. Beillahi, and S. Tahar, “On the Formal Analysis of Photonic Signal
Processing Systems”, FMICS 2015, LNCS 9128, Equation 3, Theorem 3, and Table 1, pp. 169--174.
-/

@[expose] public section

namespace Optics

noncomputable section

open Polynomial

namespace DCDRSourceBridge

/-!

## A. FMICS'15 Table 1 source-data fixtures

-/

/-- Exact active-unit-delay source symbols for the first Table 1 row. -/
def tableActiveUnitDelayParameters : MultipleDelaySourceParameters where
  G1 := 2
  G2 := 1
  G3 := 1
  k1 := 0
  k2 := 0
  m1 := 1
  m2 := 1
  m3 := 1

/-- The active row stores the literal unit-delay triple. -/
lemma tableActiveUnitDelayParameters_data :
    tableActiveUnitDelayParameters.m1 = 1 ∧
      tableActiveUnitDelayParameters.m2 = 1 ∧
        tableActiveUnitDelayParameters.m3 = 1 :=
  ⟨rfl, rfl, rfl⟩

/-- Direct Theorem 3 substitution anchors both active-row polynomials. -/
lemma tableActiveUnitDelay_printedPolynomials :
    tableActiveUnitDelayParameters.printedNumeratorPolynomial =
        C 2 * X - C 2 * X ^ 3 ∧
      tableActiveUnitDelayParameters.printedDenominatorPolynomial = 1 - X ^ 2 := by
  constructor <;>
    norm_num [tableActiveUnitDelayParameters,
      MultipleDelaySourceParameters.printedNumeratorPolynomial,
      MultipleDelaySourceParameters.printedDenominatorPolynomial,
      MultipleDelaySourceParameters.printedUpperCoefficient,
      MultipleDelaySourceParameters.printedLowerCoefficient,
      MultipleDelaySourceParameters.printedCubicCoefficient,
      MultipleDelaySourceParameters.printedUpperLoopCoefficient,
      MultipleDelaySourceParameters.printedLowerLoopCoefficient]

/-- Exact optical-amplifier source symbols for the second Table 1 row. -/
def tableOpticalAmplifierParameters : MultipleDelaySourceParameters where
  G1 := 2
  G2 := 3
  G3 := 4
  k1 := 1
  k2 := 1
  m1 := 1
  m2 := 1
  m3 := 1

/-- The amplifier row stores unit delays and all three strict gain inequalities. -/
lemma tableOpticalAmplifierParameters_data :
    tableOpticalAmplifierParameters.m1 = 1 ∧
      tableOpticalAmplifierParameters.m2 = 1 ∧
        tableOpticalAmplifierParameters.m3 = 1 ∧
          1 < tableOpticalAmplifierParameters.G1 ∧
            1 < tableOpticalAmplifierParameters.G2 ∧
              1 < tableOpticalAmplifierParameters.G3 := by
  norm_num [tableOpticalAmplifierParameters]

/-- Direct Theorem 3 substitution anchors both amplifier-row polynomials. -/
lemma tableOpticalAmplifier_printedPolynomials :
    tableOpticalAmplifierParameters.printedNumeratorPolynomial =
        C 3 * X - C 24 * X ^ 3 ∧
      tableOpticalAmplifierParameters.printedDenominatorPolynomial =
        1 - C 8 * X ^ 2 := by
  constructor <;>
    norm_num [tableOpticalAmplifierParameters,
      MultipleDelaySourceParameters.printedNumeratorPolynomial,
      MultipleDelaySourceParameters.printedDenominatorPolynomial,
      MultipleDelaySourceParameters.printedUpperCoefficient,
      MultipleDelaySourceParameters.printedLowerCoefficient,
      MultipleDelaySourceParameters.printedCubicCoefficient,
      MultipleDelaySourceParameters.printedUpperLoopCoefficient,
      MultipleDelaySourceParameters.printedLowerLoopCoefficient]

/-- Exact unit-gain passive source symbols for the third Table 1 row. -/
def tablePassiveParameters : MultipleDelaySourceParameters where
  G1 := 1
  G2 := 1
  G3 := 1
  k1 := 0
  k2 := 0
  m1 := 1
  m2 := 1
  m3 := 1

/-- The passive row stores the literal unit-gain triple. -/
lemma tablePassiveParameters_data :
    tablePassiveParameters.G1 = 1 ∧
      tablePassiveParameters.G2 = 1 ∧ tablePassiveParameters.G3 = 1 :=
  ⟨rfl, rfl, rfl⟩

/-- Direct Theorem 3 substitution anchors both passive-row polynomials. -/
lemma tablePassive_printedPolynomials :
    tablePassiveParameters.printedNumeratorPolynomial = X - X ^ 3 ∧
      tablePassiveParameters.printedDenominatorPolynomial = 1 - X ^ 2 := by
  constructor <;>
    norm_num [tablePassiveParameters,
      MultipleDelaySourceParameters.printedNumeratorPolynomial,
      MultipleDelaySourceParameters.printedDenominatorPolynomial,
      MultipleDelaySourceParameters.printedUpperCoefficient,
      MultipleDelaySourceParameters.printedLowerCoefficient,
      MultipleDelaySourceParameters.printedCubicCoefficient,
      MultipleDelaySourceParameters.printedUpperLoopCoefficient,
      MultipleDelaySourceParameters.printedLowerLoopCoefficient]

/-- Exact distinct-delay source symbols for the fourth Table 1 row. -/
def tableMultipleDelayParameters : MultipleDelaySourceParameters where
  G1 := 1
  G2 := 1
  G3 := 1
  k1 := 0
  k2 := 0
  m1 := 2
  m2 := 1
  m3 := 3

/-- The multiple-delay row stores three pairwise distinct positive exponents. -/
lemma tableMultipleDelayParameters_data :
    tableMultipleDelayParameters.m1 = 2 ∧
      tableMultipleDelayParameters.m2 = 1 ∧
        tableMultipleDelayParameters.m3 = 3 ∧
          tableMultipleDelayParameters.m1 ≠ tableMultipleDelayParameters.m2 ∧
            tableMultipleDelayParameters.m1 ≠ tableMultipleDelayParameters.m3 ∧
              tableMultipleDelayParameters.m2 ≠ tableMultipleDelayParameters.m3 := by
  norm_num [tableMultipleDelayParameters]

/-- Direct Theorem 3 substitution anchors both distinct-delay polynomials. -/
lemma tableMultipleDelay_printedPolynomials :
    tableMultipleDelayParameters.printedNumeratorPolynomial = X ^ 2 - X ^ 6 ∧
      tableMultipleDelayParameters.printedDenominatorPolynomial = 1 - X ^ 4 := by
  constructor <;>
    norm_num [tableMultipleDelayParameters,
      MultipleDelaySourceParameters.printedNumeratorPolynomial,
      MultipleDelaySourceParameters.printedDenominatorPolynomial,
      MultipleDelaySourceParameters.printedUpperCoefficient,
      MultipleDelaySourceParameters.printedLowerCoefficient,
      MultipleDelaySourceParameters.printedCubicCoefficient,
      MultipleDelaySourceParameters.printedUpperLoopCoefficient,
      MultipleDelaySourceParameters.printedLowerLoopCoefficient]

end DCDRSourceBridge

namespace DCDR

/-!

## B. Coherent distinct-delay tight pole fixture

-/

/-- The exact algebraic coherent coupler used by the tight degree-four fixture. -/
def tightMultipleDelayCoupler : DirectionalCoupler.Parameters where
  throughAmplitude := 1
  crossAmplitude := 1

/-- A distinct-delay coherent point with selected response `-q/(1-q^4)`. -/
def tightMultipleDelayParameters : MultipleDelayParameters where
  firstCoupler := tightMultipleDelayCoupler
  secondCoupler := tightMultipleDelayCoupler
  upperGain := 0
  lowerGain := 1
  feedbackGain := 1
  m1 := 2
  m2 := 1
  m3 := 3

/-- The tight fixture has three positive, pairwise distinct delay exponents. -/
lemma tightMultipleDelayParameters_data :
    tightMultipleDelayParameters.IsAdmissible ∧
      tightMultipleDelayParameters.m1 ≠ tightMultipleDelayParameters.m2 ∧
        tightMultipleDelayParameters.m1 ≠ tightMultipleDelayParameters.m3 ∧
          tightMultipleDelayParameters.m2 ≠ tightMultipleDelayParameters.m3 := by
  norm_num [MultipleDelayParameters.IsAdmissible, tightMultipleDelayParameters]

/-- Primitive expansion gives the degree-four coherent solve denominator. -/
lemma tightMultipleDelay_denominatorPolynomial_expansion :
    tightMultipleDelayParameters.denominatorPolynomial = 1 - X ^ 4 := by
  simp [MultipleDelayParameters.denominatorPolynomial,
    MultipleDelayParameters.loopPolynomial,
    MultipleDelayParameters.upperPolynomial,
    MultipleDelayParameters.lowerPolynomial,
    MultipleDelayParameters.feedbackPolynomial,
    tightMultipleDelayParameters, tightMultipleDelayCoupler,
    DirectionalCoupler.crossCoefficient]
  ring

/-- Primitive elimination expansion gives the noncancelled numerator `-q`. -/
lemma tightMultipleDelay_responseNumeratorPolynomial_expansion :
    tightMultipleDelayParameters.responseNumeratorPolynomial = -X := by
  simp [MultipleDelayParameters.responseNumeratorPolynomial,
    MultipleDelayParameters.directPolynomial,
    MultipleDelayParameters.denominatorPolynomial,
    MultipleDelayParameters.loopPolynomial,
    MultipleDelayParameters.feedbackReadoutPolynomial,
    MultipleDelayParameters.feedbackDrivePolynomial,
    MultipleDelayParameters.upperPolynomial,
    MultipleDelayParameters.lowerPolynomial,
    MultipleDelayParameters.feedbackPolynomial,
    tightMultipleDelayParameters, tightMultipleDelayCoupler,
    DirectionalCoupler.crossCoefficient]
  ring_nf
  rw [← Polynomial.C_pow, Complex.I_sq]
  simp

/-- The tight raw denominator has degree four, strictly above the unit-delay bound two. -/
lemma tightMultipleDelay_denominatorPolynomial_natDegree_eq_four :
    tightMultipleDelayParameters.denominatorPolynomial.natDegree = 4 := by
  rw [tightMultipleDelay_denominatorPolynomial_expansion]
  apply Nat.le_antisymm
  · exact (Polynomial.natDegree_sub_le _ _).trans
      (max_le (by simp) (by simp))
  · apply Polynomial.le_natDegree_of_ne_zero
    norm_num [Polynomial.coeff_sub, Polynomial.coeff_one,
      Polynomial.coeff_X_pow]

/-- The directly expanded tight numerator is nonzero. -/
lemma tightMultipleDelayNumerator_ne_zero : (-X : Polynomial ℂ) ≠ 0 := by
  exact neg_ne_zero.mpr Polynomial.X_ne_zero

/-- The directly expanded tight denominator is nonzero. -/
lemma tightMultipleDelayDenominator_ne_zero : (1 - X ^ 4 : Polynomial ℂ) ≠ 0 := by
  intro hZero
  have hEvaluation := congrArg (Polynomial.eval 0) hZero
  norm_num at hEvaluation

/-- A primitive Bezout identity certifies that `-q` and `1-q^4` are coprime. -/
lemma tightMultipleDelayNumerator_isCoprime :
    IsCoprime (-X : Polynomial ℂ) (1 - X ^ 4) := by
  refine ⟨-X ^ 3, 1, ?_⟩
  ring

/-- The exact reduced quotient `-q/(1-q^4)`. -/
def tightMultipleDelayReducedResponse : DelayTransfer.ReducedRationalResponse where
  numerator := -X
  denominator := 1 - X ^ 4
  numerator_ne_zero := tightMultipleDelayNumerator_ne_zero
  denominator_ne_zero := tightMultipleDelayDenominator_ne_zero
  isCoprime := tightMultipleDelayNumerator_isCoprime

/-- The tight fixture removes only the unit polynomial. -/
def tightMultipleDelayRationalReduction : DelayTransfer.RationalReduction where
  rawNumerator := tightMultipleDelayParameters.responseNumeratorPolynomial
  rawDenominator := tightMultipleDelayParameters.denominatorPolynomial
  cancelledFactor := 1
  reduced := tightMultipleDelayReducedResponse
  cancelledFactor_ne_zero := one_ne_zero
  rawNumerator_eq := by
    rw [tightMultipleDelay_responseNumeratorPolynomial_expansion]
    simp [tightMultipleDelayReducedResponse]
  rawDenominator_eq := by
    rw [tightMultipleDelay_denominatorPolynomial_expansion]
    simp [tightMultipleDelayReducedResponse]

/-- The exact reduction is tied to the selected coherent multiple-delay response. -/
def tightMultipleDelayResponseReduction :
    MultipleDelayResponseReduction tightMultipleDelayParameters where
  reduction := tightMultipleDelayRationalReduction
  rawNumerator_eq := rfl
  rawDenominator_eq := rfl

/-!

## C. Primitive reciprocal-coordinate pole enumeration

-/

/-- Direct fourth-degree solving gives all reciprocal-`z` poles under `q = z⁻¹`. -/
lemma tightMultipleDelay_zPoles_eq_four :
    tightMultipleDelayReducedResponse.zPoles =
      {(1 : ℂ), -1, Complex.I, -Complex.I} := by
  have hIPow : Complex.I ^ 4 = 1 := by
    calc
      Complex.I ^ 4 = (Complex.I ^ 2) ^ 2 := by ring
      _ = 1 := by rw [Complex.I_sq]; norm_num
  have hNegIPow : (-Complex.I) ^ 4 = 1 := by
    calc
      (-Complex.I) ^ 4 = Complex.I ^ 4 := by ring
      _ = 1 := hIPow
  ext z
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hz, hRoot⟩
    change (1 - X ^ 4 : Polynomial ℂ).eval z⁻¹ = 0 at hRoot
    have hEquation : 1 - z⁻¹ ^ 4 = 0 := by
      simpa using hRoot
    have hPower : z ^ 4 = 1 := by
      field_simp [hz] at hEquation
      linear_combination hEquation
    have hFactor :
        ((z - 1) * (z + 1)) *
          ((z - Complex.I) * (z + Complex.I)) = 0 := by
      calc
        ((z - 1) * (z + 1)) *
            ((z - Complex.I) * (z + Complex.I)) =
            (z ^ 2 - 1) * (z ^ 2 - Complex.I ^ 2) := by ring
        _ = z ^ 4 - 1 := by
          rw [Complex.I_sq]
          ring
        _ = 0 := by linear_combination hPower
    rcases mul_eq_zero.mp hFactor with hReal | hImaginary
    · rcases mul_eq_zero.mp hReal with hOne | hNegOne
      · left
        linear_combination hOne
      · right
        left
        linear_combination hNegOne
    · rcases mul_eq_zero.mp hImaginary with hI | hNegI
      · right
        right
        left
        linear_combination hI
      · right
        right
        right
        linear_combination hNegI
  · rintro (rfl | rfl | rfl | rfl)
    · constructor
      · norm_num
      · change (1 - X ^ 4 : Polynomial ℂ).eval (1 : ℂ)⁻¹ = 0
        norm_num
    · constructor
      · norm_num
      · change (1 - X ^ 4 : Polynomial ℂ).eval (-1 : ℂ)⁻¹ = 0
        norm_num
    · constructor
      · exact Complex.I_ne_zero
      · change (1 - X ^ 4 : Polynomial ℂ).eval Complex.I⁻¹ = 0
        rw [Complex.inv_I]
        simp [hNegIPow]
    · constructor
      · exact neg_ne_zero.mpr Complex.I_ne_zero
      · change (1 - X ^ 4 : Polynomial ℂ).eval (-Complex.I)⁻¹ = 0
        rw [inv_neg, Complex.inv_I]
        norm_num [Complex.I_mul_I]

/-- Primitive set cardinality gives exactly four reciprocal-coordinate poles. -/
lemma tightMultipleDelay_ncard_actualPoles_eq_four :
    tightMultipleDelayResponseReduction.actualPoles.ncard = 4 := by
  change tightMultipleDelayReducedResponse.zPoles.ncard = 4
  rw [tightMultipleDelay_zPoles_eq_four]
  norm_num [Set.ncard_insert_of_notMem, Complex.ext_iff]

/-- The exact four-pole count attains the raw denominator degree. -/
lemma tightMultipleDelay_ncard_actualPoles_eq_natDegree :
    tightMultipleDelayResponseReduction.actualPoles.ncard =
      tightMultipleDelayParameters.denominatorPolynomial.natDegree := by
  rw [tightMultipleDelay_ncard_actualPoles_eq_four,
    tightMultipleDelay_denominatorPolynomial_natDegree_eq_four]

/-!

## D. Admissibility-gated unit-delay bridge sentinels

-/

/-- A normalized zero-cross coherent coupler used to expose the retained feedback algebra. -/
def unitDelayBridgeCoupler : DirectionalCoupler.Parameters where
  throughAmplitude := 1
  crossAmplitude := 0

/-- A nontrivial admissible unit-delay point with nonzero, non-unit feedback gain. -/
def unitDelayBridgeParameters : UnitDelayParameters where
  firstCoupler := unitDelayBridgeCoupler
  secondCoupler := unitDelayBridgeCoupler
  upperGain := 2
  lowerGain := 3 / 2
  feedbackGain := 1 / 2

/-- The nonzero formal-delay value used by the shared-response bridge fixture. -/
def unitDelayBridgeQ : ℂ := 1 / 2

/-- The bridge fixture satisfies the earlier nonnegative-real-gain predicate. -/
lemma unitDelayBridgeParameters_isAdmissible :
    unitDelayBridgeParameters.IsAdmissible := by
  norm_num [UnitDelayParameters.IsAdmissible, unitDelayBridgeParameters]

/-- Primitive one-delay expansion gives equal numerator and denominator values `13/16`. -/
lemma unitDelayBridge_old_polynomial_evaluations :
    unitDelayBridgeParameters.responseNumeratorPolynomial.eval unitDelayBridgeQ = 13 / 16 ∧
      unitDelayBridgeParameters.denominatorPolynomial.eval unitDelayBridgeQ = 13 / 16 := by
  constructor <;>
    norm_num [UnitDelayParameters.responseNumeratorPolynomial,
      UnitDelayParameters.directPolynomial,
      UnitDelayParameters.denominatorPolynomial,
      UnitDelayParameters.loopPolynomial,
      UnitDelayParameters.feedbackReadoutPolynomial,
      UnitDelayParameters.feedbackDrivePolynomial,
      UnitDelayParameters.upperPolynomial,
      UnitDelayParameters.lowerPolynomial,
      UnitDelayParameters.feedbackPolynomial,
      unitDelayBridgeParameters, unitDelayBridgeCoupler,
      unitDelayBridgeQ, DirectionalCoupler.crossCoefficient]

/-- Independent multiple-delay expansion gives the same two values at the embedded point. -/
lemma unitDelayBridge_embedded_polynomial_evaluations :
    unitDelayBridgeParameters.toMultipleDelayParameters.responseNumeratorPolynomial.eval
        unitDelayBridgeQ = 13 / 16 ∧
      unitDelayBridgeParameters.toMultipleDelayParameters.denominatorPolynomial.eval
        unitDelayBridgeQ = 13 / 16 := by
  constructor <;>
    norm_num [MultipleDelayParameters.responseNumeratorPolynomial,
      MultipleDelayParameters.directPolynomial,
      MultipleDelayParameters.denominatorPolynomial,
      MultipleDelayParameters.loopPolynomial,
      MultipleDelayParameters.feedbackReadoutPolynomial,
      MultipleDelayParameters.feedbackDrivePolynomial,
      MultipleDelayParameters.upperPolynomial,
      MultipleDelayParameters.lowerPolynomial,
      MultipleDelayParameters.feedbackPolynomial,
      UnitDelayParameters.toMultipleDelayParameters,
      unitDelayBridgeParameters, unitDelayBridgeCoupler,
      unitDelayBridgeQ, DirectionalCoupler.crossCoefficient]

/-- Direct nonvanishing and validity place the bridge point in the old response domain. -/
def unitDelayBridgeOldDomainProof :
    (fun _ : Fin 1 => unitDelayBridgeQ) ∈
      (rationalNetlist unitDelayBridgeParameters).responseDomain :=
  rationalNetlist_mem_responseDomain unitDelayBridgeParameters unitDelayBridgeQ
    unitDelayBridgeParameters_isAdmissible (by
      rw [unitDelayBridge_old_polynomial_evaluations.2]
      norm_num)

/-- Direct nonvanishing and positive exponents place the point in the embedded response domain. -/
def unitDelayBridgeEmbeddedDomainProof :
    (fun _ : Fin 1 => unitDelayBridgeQ) ∈
      (multipleDelayRationalNetlist
        unitDelayBridgeParameters.toMultipleDelayParameters).responseDomain :=
  multipleDelayRationalNetlist_mem_responseDomain
    unitDelayBridgeParameters.toMultipleDelayParameters unitDelayBridgeQ
    unitDelayBridgeParameters.toMultipleDelayParameters_isAdmissible (by
      rw [unitDelayBridge_embedded_polynomial_evaluations.2]
      norm_num)

/-- The earlier rational family independently evaluates to the exact selected response `1`. -/
lemma unitDelayBridge_old_response_eq_one :
    rationalEliminationResponse unitDelayBridgeParameters unitDelayBridgeQ
      unitDelayBridgeOldDomainProof = 1 := by
  rw [rationalEliminationResponse_eq_responseModel]
  change
    unitDelayBridgeParameters.responseNumeratorPolynomial.eval unitDelayBridgeQ /
        unitDelayBridgeParameters.denominatorPolynomial.eval unitDelayBridgeQ = 1
  rw [unitDelayBridge_old_polynomial_evaluations.1,
    unitDelayBridge_old_polynomial_evaluations.2]
  norm_num

/-- The embedded multiple-delay family independently evaluates to the same response `1`. -/
lemma unitDelayBridge_embedded_response_eq_one :
    multipleDelayRationalEliminationResponse
        unitDelayBridgeParameters.toMultipleDelayParameters unitDelayBridgeQ
        unitDelayBridgeEmbeddedDomainProof = 1 := by
  rw [multipleDelayRationalEliminationResponse_eq_responseModel]
  change
    unitDelayBridgeParameters.toMultipleDelayParameters.responseNumeratorPolynomial.eval
          unitDelayBridgeQ /
        unitDelayBridgeParameters.toMultipleDelayParameters.denominatorPolynomial.eval
          unitDelayBridgeQ = 1
  rw [unitDelayBridge_embedded_polynomial_evaluations.1,
    unitDelayBridge_embedded_polynomial_evaluations.2]
  norm_num

/-- At a nontrivial common point, both selected N5 response entries are pinned to `1`. -/
lemma unitDelayBridge_both_responses_eq_one :
    rationalEliminationResponse unitDelayBridgeParameters unitDelayBridgeQ
          unitDelayBridgeOldDomainProof = 1 ∧
      multipleDelayRationalEliminationResponse
          unitDelayBridgeParameters.toMultipleDelayParameters unitDelayBridgeQ
          unitDelayBridgeEmbeddedDomainProof = 1 :=
  ⟨unitDelayBridge_old_response_eq_one,
    unitDelayBridge_embedded_response_eq_one⟩

/-- The reviewer's validity counterexample: negative upper gain and zero feedback gain. -/
def unitDelayValidityCounterexample : UnitDelayParameters where
  firstCoupler := unitDelayBridgeCoupler
  secondCoupler := unitDelayBridgeCoupler
  upperGain := -1
  lowerGain := 1
  feedbackGain := 0

/-- The counterexample fails the old gain gate but passes the embedded exponent gate. -/
lemma unitDelayValidityCounterexample_predicates :
    ¬ unitDelayValidityCounterexample.IsAdmissible ∧
      unitDelayValidityCounterexample.toMultipleDelayParameters.IsAdmissible := by
  norm_num [UnitDelayParameters.IsAdmissible,
    MultipleDelayParameters.IsAdmissible,
    UnitDelayParameters.toMultipleDelayParameters,
    unitDelayValidityCounterexample]

/-- The old family has no physical response-domain point when its negative gain gate fails. -/
lemma unitDelayValidityCounterexample_old_responseDomain_eq_empty :
    (rationalNetlist unitDelayValidityCounterexample).responseDomain = ∅ := by
  refine eq_empty_iff_forall_notMem.mpr ?_
  intro value hValue
  have hAdmissible : unitDelayValidityCounterexample.IsAdmissible :=
    (hValue.2 Component.upperPath).1
  exact unitDelayValidityCounterexample_predicates.1 hAdmissible

/-- Primitive expansion gives embedded denominator value one at formal `q = 0`. -/
lemma unitDelayValidityCounterexample_embedded_denominator_at_zero :
    unitDelayValidityCounterexample.toMultipleDelayParameters.denominatorPolynomial.eval 0 =
      1 := by
  norm_num [MultipleDelayParameters.denominatorPolynomial,
    MultipleDelayParameters.loopPolynomial,
    MultipleDelayParameters.upperPolynomial,
    MultipleDelayParameters.lowerPolynomial,
    MultipleDelayParameters.feedbackPolynomial,
    UnitDelayParameters.toMultipleDelayParameters,
    unitDelayValidityCounterexample, unitDelayBridgeCoupler,
    DirectionalCoupler.crossCoefficient]

/-- The embedded family nevertheless contains formal `q = 0` in its response domain. -/
lemma unitDelayValidityCounterexample_embedded_responseDomain_nonempty :
    (multipleDelayRationalNetlist
      unitDelayValidityCounterexample.toMultipleDelayParameters).responseDomain.Nonempty := by
  refine ⟨fun _ : Fin 1 => 0, ?_⟩
  apply multipleDelayRationalNetlist_mem_responseDomain
  · exact unitDelayValidityCounterexample_predicates.2
  · rw [unitDelayValidityCounterexample_embedded_denominator_at_zero]
    norm_num

/-- The old admissibility gate is load-bearing: without it, the two response domains differ. -/
lemma unitDelayValidityGate_is_loadBearing :
    (rationalNetlist unitDelayValidityCounterexample).responseDomain = ∅ ∧
      (multipleDelayRationalNetlist
        unitDelayValidityCounterexample.toMultipleDelayParameters).responseDomain.Nonempty :=
  ⟨unitDelayValidityCounterexample_old_responseDomain_eq_empty,
    unitDelayValidityCounterexample_embedded_responseDomain_nonempty⟩

end DCDR

end

end Optics
