/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Systems.DCDR.PolesRegression

/-!
# Exact source-dictionary and pole-cardinality regressions for the DCDR

## i. Overview

This file gives the IP-22 pole bound two independent teeth. The active coherent fixture's reduced
denominator is expanded directly as `1 + 4*q²`; its reciprocal pole set is proved to be exactly
`{2*I, -2*I}`, so the bound two is attained. A separate coherent fixture has zero feedback gain;
its raw denominator expands to one, its selected quotient has no poles, and the degree genuinely
drops below two.

Neither cardinality result invokes `ResponseReduction.ncard_actualPoles_le_two` or either generic
cardinality lemma. The proofs unfold the exact polynomial data and use elementary complex-field
algebra, so they can fail if the coefficients, reciprocal coordinate, or selected reduction
changes.

An additional source-dictionary fixture has all five printed parameters equal to one. Its printed
incoherent loop coefficient is one, while the mapped coherent N7 coefficient is minus one because
two cross edges each carry `-I`. This is evidence of model divergence, not an equivalence claim.
Another exact source fixture satisfies the strict version of printed Theorem 4's expression while
the reciprocal pole of Theorem 3's differently indexed denominator has norm two. It makes the
withholding of a forced strict Theorem 4 bridge executable.

At that same fixture, the printed `G1*G2` expression is `1/4`, while direct expansion of the
recovered script's `G1*G3` expression is `4`. The printed condition holds and the script condition
fails. These two facts are proved separately from the literal products; no source-convention
conversion is used.

The gain-role fixture uses printed intensities `(1/4, 1/9, 4/25)`. Primitive square-root
expansion gives coherent field gains `(1/2, 1/3, 2/5)`, while an independent printed-polynomial
expansion retains the literal intensity values. Thus replacing the coherent map cannot silently
replace `G_i` by `sqrt G_i` in the source transcription.

## ii. Key results

- `unstableReducedResponse_zPoles_eq_pair`: exact two-element reciprocal pole set.
- `unstableResponseReduction_ncard_actualPoles_eq_two`: tight DCDR pole count.
- `degreeDropResponseReduction_ncard_actualPoles_eq_zero`: degenerate denominator fixture.
- `sourceGainConversion_coherentGains`: exact intensity-to-field conversion anchor.
- `sourceGainConversion_printedPolynomials`: literal printed-source noninterference anchor.
- `sourceDictionaryDivergence_loopCoefficients_ne`: incoherent/coherent divergence witness.
- `sourceThmFourMismatch_not_isSchurStable`: executable Theorem 3/4 mismatch witness.
- `sourceThmFourMismatch_printedExpression`: the printed `G1*G2` value `1/4`.
- `sourceThmFourMismatch_scriptExpression`: the script `G1*G3` value `4`.
- `sourceThmFourMismatch_conditions_disagree`: the two source conditions differ at one point.

## iii. Table of contents

- A. Tight two-pole fixture
- B. Degree-drop fixture
- C. Source-dictionary gain conversion, divergence, and printed-form mismatch fixtures

## iv. References

These exact algebraic fixtures do not claim physical resonance, coherent--incoherent equivalence,
BIBO stability, normalized-modal or electromagnetic power, causality or time-domain behavior, or
a physical-frequency interpretation.

The recovered script's `G1*G3` condition is audited as a separate object from the printed
Theorem 4 `G1*G2` condition; no equality or implication between them is asserted.
-/

@[expose] public section

namespace Optics.DCDR

noncomputable section

open Polynomial
open scoped ComplexOrder

/-!

## A. Tight two-pole fixture

-/

/-- Direct quadratic solving gives both and only the active fixture's reciprocal poles. -/
lemma unstableReducedResponse_zPoles_eq_pair :
    unstableReducedResponse.zPoles =
      {(2 : ℂ) * Complex.I, -((2 : ℂ) * Complex.I)} := by
  ext z
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hz, hRoot⟩
    change unstableDenominator.eval z⁻¹ = 0 at hRoot
    have hEquation : 1 + 4 * z⁻¹ ^ 2 = 0 := by
      simpa [unstableDenominator] using hRoot
    have hSquare : z ^ 2 = -4 := by
      field_simp [hz] at hEquation
      linear_combination hEquation
    have hFactor :
        (z - 2 * Complex.I) * (z + 2 * Complex.I) = 0 := by
      calc
        (z - 2 * Complex.I) * (z + 2 * Complex.I) =
            z ^ 2 - (2 * Complex.I) ^ 2 := by ring
        _ = z ^ 2 + 4 := by
          ring_nf
          rw [Complex.I_sq]
          ring
        _ = 0 := by linear_combination hSquare
    rcases mul_eq_zero.mp hFactor with hFirst | hSecond
    · left
      linear_combination hFirst
    · right
      linear_combination hSecond
  · rintro (rfl | rfl)
    · constructor
      · exact mul_ne_zero (by norm_num) Complex.I_ne_zero
      · change unstableDenominator.eval (((2 : ℂ) * Complex.I)⁻¹) = 0
        rw [mul_inv_rev, Complex.inv_I]
        norm_num [unstableDenominator, Complex.I_mul_I]
        ring_nf
        simp
    · constructor
      · exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) Complex.I_ne_zero)
      · change unstableDenominator.eval (-((2 : ℂ) * Complex.I))⁻¹ = 0
        rw [inv_neg, mul_inv_rev, Complex.inv_I]
        norm_num [unstableDenominator, Complex.I_mul_I]
        ring_nf
        simp

/-- The active selected DCDR quotient attains the general upper bound of two actual poles. -/
lemma unstableResponseReduction_ncard_actualPoles_eq_two :
    unstableResponseReduction.actualPoles.ncard = 2 := by
  change unstableReducedResponse.zPoles.ncard = 2
  rw [unstableReducedResponse_zPoles_eq_pair]
  have hDistinct : (2 : ℂ) * Complex.I ≠ -((2 : ℂ) * Complex.I) := by
    intro hEqual
    have hImaginary := congrArg Complex.im hEqual
    norm_num at hImaginary
  rw [Set.ncard_insert_of_notMem (by simpa using hDistinct)]
  simp

/-!

## B. Degree-drop fixture

-/

/-- A unit-through coherent coupler used by the zero-feedback degree-drop fixture. -/
def degreeDropCoupler : DirectionalCoupler.Parameters where
  throughAmplitude := 1
  crossAmplitude := 0

/-- Zero feedback makes the raw quadratic denominator degenerate to the constant one. -/
def degreeDropParameters : UnitDelayParameters where
  firstCoupler := degreeDropCoupler
  secondCoupler := degreeDropCoupler
  upperGain := 1
  lowerGain := 0
  feedbackGain := 0

/-- Direct expansion gives the constant raw denominator one. -/
lemma degreeDrop_denominatorPolynomial_expansion :
    degreeDropParameters.denominatorPolynomial = 1 := by
  simp [UnitDelayParameters.denominatorPolynomial, UnitDelayParameters.loopPolynomial,
    UnitDelayParameters.upperPolynomial, UnitDelayParameters.lowerPolynomial,
    UnitDelayParameters.feedbackPolynomial, degreeDropParameters, degreeDropCoupler,
    DirectionalCoupler.crossCoefficient]

/-- Direct expansion gives the nonzero raw numerator `q`. -/
lemma degreeDrop_responseNumeratorPolynomial_expansion :
    degreeDropParameters.responseNumeratorPolynomial = X := by
  simp [UnitDelayParameters.responseNumeratorPolynomial,
    UnitDelayParameters.directPolynomial, UnitDelayParameters.denominatorPolynomial,
    UnitDelayParameters.loopPolynomial, UnitDelayParameters.feedbackReadoutPolynomial,
    UnitDelayParameters.feedbackDrivePolynomial, UnitDelayParameters.upperPolynomial,
    UnitDelayParameters.lowerPolynomial, UnitDelayParameters.feedbackPolynomial,
    degreeDropParameters, degreeDropCoupler, DirectionalCoupler.crossCoefficient]

/-- The exact reduced quotient `q / 1` for the degree-drop fixture. -/
def degreeDropReducedResponse : DelayTransfer.ReducedRationalResponse where
  numerator := X
  denominator := 1
  numerator_ne_zero := Polynomial.X_ne_zero
  denominator_ne_zero := one_ne_zero
  isCoprime := isCoprime_one_right

/-- The degree-drop fixture removes only the unit polynomial. -/
def degreeDropRationalReduction : DelayTransfer.RationalReduction where
  rawNumerator := degreeDropParameters.responseNumeratorPolynomial
  rawDenominator := degreeDropParameters.denominatorPolynomial
  cancelledFactor := 1
  reduced := degreeDropReducedResponse
  cancelledFactor_ne_zero := one_ne_zero
  rawNumerator_eq := by
    rw [degreeDrop_responseNumeratorPolynomial_expansion]
    simp [degreeDropReducedResponse]
  rawDenominator_eq := by
    rw [degreeDrop_denominatorPolynomial_expansion]
    simp [degreeDropReducedResponse]

/-- The exact reduction is tied to the selected degree-drop DCDR response. -/
def degreeDropResponseReduction : ResponseReduction degreeDropParameters where
  reduction := degreeDropRationalReduction
  rawNumerator_eq := rfl
  rawDenominator_eq := rfl

/-- Direct unfolding shows that the degree-drop selected quotient has no actual poles. -/
lemma degreeDropResponseReduction_actualPoles_eq_empty :
    degreeDropResponseReduction.actualPoles = ∅ := by
  ext z
  simp [ResponseReduction.actualPoles, degreeDropResponseReduction,
    degreeDropRationalReduction, degreeDropReducedResponse,
    DelayTransfer.ReducedRationalResponse.zPoles,
    DelayTransfer.ReducedRationalResponse.poles]

/-- The degenerate denominator fixture has exactly zero actual reciprocal poles. -/
lemma degreeDropResponseReduction_ncard_actualPoles_eq_zero :
    degreeDropResponseReduction.actualPoles.ncard = 0 := by
  rw [degreeDropResponseReduction_actualPoles_eq_empty]
  simp

/-!

## C. Source-dictionary gain conversion, divergence, and printed-form mismatch fixtures

-/

/-- Exact source intensities whose canonical field gains are rational square roots. -/
def sourceGainConversionParameters : DCDRSourceBridge.SourceParameters where
  G1 := 1 / 4
  G2 := 1 / 9
  G3 := 4 / 25
  k1 := 1
  k2 := 1

/-- The exact gain-role fixture lies in the faithful square-root source domain. -/
lemma sourceGainConversion_hasNonnegativeGains :
    sourceGainConversionParameters.HasNonnegativeGains := by
  norm_num [DCDRSourceBridge.SourceParameters.HasNonnegativeGains,
    sourceGainConversionParameters]

/-- Primitive square-root expansion gives the three canonical coherent field gains. -/
lemma sourceGainConversion_coherentGains :
    sourceGainConversionParameters.toCoherentUnitDelayParameters.upperGain = 1 / 2 ∧
      sourceGainConversionParameters.toCoherentUnitDelayParameters.lowerGain = 1 / 3 ∧
      sourceGainConversionParameters.toCoherentUnitDelayParameters.feedbackGain = 2 / 5 := by
  have hFour : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hNine : Real.sqrt (9 : ℝ) = 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hTwentyFive : Real.sqrt (25 : ℝ) = 5 := by
    rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num [DCDRSourceBridge.SourceParameters.toCoherentUnitDelayParameters,
    DCDRSourceBridge.intensityGainToFieldAmplitudeGain, sourceGainConversionParameters,
    hFour, hNine, hTwentyFive]

/-- Squaring the independently expanded field gains recovers all three source intensities. -/
lemma sourceGainConversion_squaredGains :
    DCDRSourceBridge.fieldAmplitudeGainToIntensityGain
        sourceGainConversionParameters.toCoherentUnitDelayParameters.upperGain = 1 / 4 ∧
      DCDRSourceBridge.fieldAmplitudeGainToIntensityGain
          sourceGainConversionParameters.toCoherentUnitDelayParameters.lowerGain = 1 / 9 ∧
      DCDRSourceBridge.fieldAmplitudeGainToIntensityGain
          sourceGainConversionParameters.toCoherentUnitDelayParameters.feedbackGain = 4 / 25 := by
  have hFour : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hNine : Real.sqrt (9 : ℝ) = 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hTwentyFive : Real.sqrt (25 : ℝ) = 5 := by
    rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num [DCDRSourceBridge.fieldAmplitudeGainToIntensityGain,
    DCDRSourceBridge.SourceParameters.toCoherentUnitDelayParameters,
    DCDRSourceBridge.intensityGainToFieldAmplitudeGain, sourceGainConversionParameters,
    hFour, hNine, hTwentyFive]

/-- The literal printed polynomials retain source intensities, not mapped field amplitudes. -/
lemma sourceGainConversion_printedPolynomials :
    sourceGainConversionParameters.printedNumeratorPolynomial =
        C (1 / 9) * X - C (1 / 225) * X ^ 3 ∧
      sourceGainConversionParameters.printedDenominatorPolynomial =
        1 - C (1 / 25) * X ^ 2 := by
  constructor <;>
    norm_num [DCDRSourceBridge.SourceParameters.printedNumeratorPolynomial,
      DCDRSourceBridge.SourceParameters.printedDenominatorPolynomial,
      DCDRSourceBridge.SourceParameters.printedLinearCoefficient,
      DCDRSourceBridge.SourceParameters.printedCubicCoefficient,
      DCDRSourceBridge.SourceParameters.printedLoopCoefficient,
      sourceGainConversionParameters]

/-- All-one printed symbols expose the incoherent/coherent loop-coefficient difference. -/
def sourceDictionaryDivergenceParameters : DCDRSourceBridge.SourceParameters where
  G1 := 1
  G2 := 1
  G3 := 1
  k1 := 1
  k2 := 1

/-- Direct printed-intensity expansion gives loop coefficient one. -/
lemma sourceDictionaryDivergence_printedLoopCoefficient :
    sourceDictionaryDivergenceParameters.printedLoopCoefficient = 1 := by
  norm_num [DCDRSourceBridge.SourceParameters.printedLoopCoefficient,
    sourceDictionaryDivergenceParameters]

/-- Direct N7 amplitude expansion gives coherent loop coefficient minus one. -/
lemma sourceDictionaryDivergence_coherentLoopCoefficient :
    sourceDictionaryDivergenceParameters.toCoherentUnitDelayParameters.loopCoefficient = -1 := by
  norm_num [DCDRSourceBridge.SourceParameters.toCoherentUnitDelayParameters,
    DCDRSourceBridge.intensityGainToFieldAmplitudeGain,
    UnitDelayParameters.loopCoefficient, sourceDictionaryDivergenceParameters,
    DirectionalCoupler.crossCoefficient, Complex.I_mul_I]

/-- The source dictionary does not identify the printed and coherent loop coefficients. -/
lemma sourceDictionaryDivergence_loopCoefficients_ne :
    (sourceDictionaryDivergenceParameters.printedLoopCoefficient : ℂ) ≠
      sourceDictionaryDivergenceParameters.toCoherentUnitDelayParameters.loopCoefficient := by
  rw [sourceDictionaryDivergence_printedLoopCoefficient,
    sourceDictionaryDivergence_coherentLoopCoefficient]
  norm_num

/-- A printed source point separating Theorem 4's `G1*G2` from Theorem 3's `G1*G3`. -/
def sourceThmFourMismatchParameters : DCDRSourceBridge.SourceParameters where
  G1 := 1
  G2 := 1 / 4
  G3 := 4
  k1 := 1
  k2 := 1

/-- Direct expansion gives the printed Theorem 4 `G1*G2` expression `1/4`. -/
lemma sourceThmFourMismatch_printedExpression :
    printedIncoherentStabilityExpression
      sourceThmFourMismatchParameters.G1 sourceThmFourMismatchParameters.G2
      sourceThmFourMismatchParameters.G3 sourceThmFourMismatchParameters.k1
      sourceThmFourMismatchParameters.k2 = (1 / 4 : ℂ) := by
  norm_num [printedIncoherentStabilityExpression, sourceThmFourMismatchParameters]

/-- Direct expansion gives the recovered script's `G1*G3` expression `4`. -/
lemma sourceThmFourMismatch_scriptExpression :
    (sourceThmFourMismatchParameters.k1 : ℂ) *
          sourceThmFourMismatchParameters.k2 * sourceThmFourMismatchParameters.G1 *
          sourceThmFourMismatchParameters.G3 +
        (1 - sourceThmFourMismatchParameters.k1) *
          (1 - sourceThmFourMismatchParameters.k2) *
          sourceThmFourMismatchParameters.G2 * sourceThmFourMismatchParameters.G3 = 4 := by
  norm_num [sourceThmFourMismatchParameters]

/-- The mismatch fixture satisfies the strict square-root bound and the printed nonzero gate. -/
lemma sourceThmFourMismatch_strictConditions :
    ‖Complex.sqrt (printedIncoherentStabilityExpression
      sourceThmFourMismatchParameters.G1 sourceThmFourMismatchParameters.G2
      sourceThmFourMismatchParameters.G3 sourceThmFourMismatchParameters.k1
      sourceThmFourMismatchParameters.k2)‖ < 1 ∧
    printedIncoherentStabilityExpression
      sourceThmFourMismatchParameters.G1 sourceThmFourMismatchParameters.G2
      sourceThmFourMismatchParameters.G3 sourceThmFourMismatchParameters.k1
      sourceThmFourMismatchParameters.k2 ≠ 0 := by
  rw [sourceThmFourMismatch_printedExpression]
  constructor
  · have hNonneg : (0 : ℂ) ≤ 1 / 4 :=
      (RCLike.nonneg_iff).2 ⟨by norm_num, by norm_num⟩
    have hRealSqrt : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
      rw [Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)]
      norm_num
    rw [Complex.sqrt_of_nonneg hNonneg]
    norm_num [hRealSqrt]
  · norm_num

/-- The mismatch fixture satisfies the printed paper's non-strict Theorem 4 conditions. -/
lemma sourceThmFourMismatch_printedConditions :
    PrintedIncoherentStabilityConditions
      sourceThmFourMismatchParameters.G1 sourceThmFourMismatchParameters.G2
      sourceThmFourMismatchParameters.G3 sourceThmFourMismatchParameters.k1
      sourceThmFourMismatchParameters.k2 :=
  ⟨sourceThmFourMismatch_strictConditions.1.le,
    sourceThmFourMismatch_strictConditions.2⟩

/-- The mismatch fixture fails the recovered script's non-strict conditions because its square
root has norm two. -/
lemma sourceThmFourMismatch_scriptConditions_fail :
    ¬FMICSScriptIncoherentStabilityConditions
      sourceThmFourMismatchParameters.G1 sourceThmFourMismatchParameters.G2
      sourceThmFourMismatchParameters.G3 sourceThmFourMismatchParameters.k1
      sourceThmFourMismatchParameters.k2 := by
  rintro ⟨hBound, _⟩
  rw [sourceThmFourMismatch_scriptExpression] at hBound
  have hNonnegative : (0 : ℂ) ≤ 4 :=
    (RCLike.nonneg_iff).2 ⟨by norm_num, by norm_num⟩
  have hSqrtFour : Real.sqrt (4 : ℝ) = 2 := by
    norm_num
  rw [Complex.sqrt_of_nonneg hNonnegative, hSqrtFour] at hBound
  norm_num at hBound

/-- At one exact source point, the printed conditions hold and the recovered-script conditions
fail.

The two conjuncts come from independent literal-product expansions.
-/
lemma sourceThmFourMismatch_conditions_disagree :
    PrintedIncoherentStabilityConditions
        sourceThmFourMismatchParameters.G1 sourceThmFourMismatchParameters.G2
        sourceThmFourMismatchParameters.G3 sourceThmFourMismatchParameters.k1
        sourceThmFourMismatchParameters.k2 ∧
      ¬FMICSScriptIncoherentStabilityConditions
        sourceThmFourMismatchParameters.G1 sourceThmFourMismatchParameters.G2
        sourceThmFourMismatchParameters.G3 sourceThmFourMismatchParameters.k1
        sourceThmFourMismatchParameters.k2 :=
  ⟨sourceThmFourMismatch_printedConditions,
    sourceThmFourMismatch_scriptConditions_fail⟩

/-- The same fixture's printed Theorem 3 denominator has quadratic coefficient four. -/
lemma sourceThmFourMismatch_denominatorPolynomial_expansion :
    sourceThmFourMismatchParameters.printedDenominatorPolynomial =
      1 - C 4 * X ^ 2 := by
  norm_num [DCDRSourceBridge.SourceParameters.printedDenominatorPolynomial,
    DCDRSourceBridge.SourceParameters.printedLoopCoefficient,
    sourceThmFourMismatchParameters]

/-- A coprime quotient carrying the mismatch fixture's printed denominator. -/
def sourceThmFourMismatchReducedResponse : DelayTransfer.ReducedRationalResponse where
  numerator := 1
  denominator := sourceThmFourMismatchParameters.printedDenominatorPolynomial
  numerator_ne_zero := one_ne_zero
  denominator_ne_zero := by
    intro hZero
    have hEvaluation := congrArg (Polynomial.eval 0) hZero
    rw [sourceThmFourMismatch_denominatorPolynomial_expansion] at hEvaluation
    norm_num at hEvaluation
  isCoprime := isCoprime_one_left

/-- Direct substitution makes `z = 2` a pole of the printed Theorem 3 denominator. -/
lemma sourceThmFourMismatch_two_mem_zPoles :
    (2 : ℂ) ∈ sourceThmFourMismatchReducedResponse.zPoles := by
  constructor
  · norm_num
  · change sourceThmFourMismatchParameters.printedDenominatorPolynomial.eval
      ((2 : ℂ)⁻¹) = 0
    rw [sourceThmFourMismatch_denominatorPolynomial_expansion]
    norm_num

/-- The strict printed Theorem 4 expression does not control Theorem 3's mismatched denominator.

This is why `SourceBridge.lean` withholds, rather than forces, a corrected strict stability lemma.
-/
lemma sourceThmFourMismatch_not_isSchurStable :
    ¬sourceThmFourMismatchReducedResponse.IsSchurStable := by
  intro hStable
  have hInside := hStable 2 sourceThmFourMismatch_two_mem_zPoles
  norm_num at hInside

end

end Optics.DCDR
