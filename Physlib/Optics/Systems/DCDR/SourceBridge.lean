/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Systems.DCDR.Poles

/-!
# FMICS'15 source dictionary and pole-cardinality bridge for the DCDR

## i. Overview

This file discharges the DCDR part of parity row IP-22. At S4's
`ReducedRationalResponse` level, formal-`q` denominator roots are `poles` and their nonzero
reciprocals under `q = z⁻¹` are `zPoles`. The generic finiteness and cardinality results are
`ReducedRationalResponse.finite_poles_and_ncard_le_of_denominator_eq_coefficients` and its
`zPoles` counterpart in `DelayTransfer/Stability.lean`. The latter is the coordinate matching
FMICS'15 Definition 6: it requires `z ≠ 0`, and its finite presentation also omits the non-finite
reciprocal of `q = 0`. These restrictions cannot produce more elements than the formal root set.

The coherent unit-delay DCDR denominator has degree at most two before cancellation. Every
response-indexed reduction therefore has at most two actual reciprocal-coordinate poles, the
coherent analogue of FMICS'15 p. 174's “2 poles at maximum” consequence of its Theorem 2.

`DCDRSourceBridge.SourceParameters` is a symbol dictionary for the five real unit-delay source
parameters `G1`, `G2`, `G3`, `k1`, and `k2`. Its printed incoherent polynomials retain the
intensity gains `G_i` and intensity coefficients `1-k` and `k`. Its map to the coherent Physlib
family instead uses the named field gains `sqrt G_i`, the amplitudes `sqrt (1-k)` and `sqrt k`,
and N7 cross coefficient `-I * sqrt k`. Squaring the mapped gains and amplitudes recovers the
printed intensities on the stated source domains, but no transfer, denominator, pole, or
stability equivalence between these two models is asserted.

`passiveCaseSourceParameters` records FMICS'15 p. 175's passive point exactly, replacing the
printed decimals by rational data only. `passiveCaseUnitDelayParameters` is its coherent N7 image
through the same dictionary; it does not identify the coherent and printed incoherent responses.

## ii. Key results

- `DCDR.UnitDelayParameters.loopCoefficient`: the coherent quadratic loop coefficient.
- `DCDR.UnitDelayParameters.denominatorPolynomial_natDegree_le_two`: the raw degree bound.
- `DCDR.ResponseReduction.ncard_actualPoles_le_two`: the cancellation-aware pole bound.
- `DCDRSourceBridge.intensityGainToFieldAmplitudeGain`: intensity-to-field conversion.
- `DCDRSourceBridge.fieldAmplitudeGainToIntensityGain`: field-to-intensity conversion.
- `DCDRSourceBridge.SourceParameters`: the five-symbol FMICS'15 unit-delay dictionary.
- `DCDRSourceBridge.SourceParameters.toCoherentUnitDelayParameters`: its coherent N7 map.
- `DCDRSourceBridge.SourceParameters.coherentLoopCoefficient`: its named coherent coefficient.
- `DCDRSourceBridge.SourceParameters.printedDenominatorPolynomial`: the printed incoherent data.
- `DCDRSourceBridge.SourceParameters.printedDenominatorPolynomial_eq_coefficients`: its
  coefficient-list presentation through degree two.
- `DCDRSourceBridge.passiveCaseSourceParameters`: FMICS'15 p. 175's exact passive symbols.
- `DCDRSourceBridge.passiveCaseUnitDelayParameters`: their coherent N7 dictionary image.

## iii. Table of contents

- A. Coherent DCDR denominator degree and actual-pole count
- B. Printed incoherent stability audit predicate
- C. FMICS'15 unit-delay source dictionary
- D. Printed incoherent coefficient data
- E. FMICS'15 passive case data

## iv. References

No result here claims physical resonance, coherent--incoherent equivalence, a general BIBO
theorem, normalized-modal or electromagnetic power, causality or a time-domain realization, or
a physical-frequency interpretation of formal `q` or reciprocal `z`.

U. Siddique, S. M. Beillahi, and S. Tahar, “On the Formal Analysis of Photonic Signal
Processing Systems”, FMICS 2015, LNCS 9128, Theorems 1--4, pp. 170--175.

The source's Theorem 1 is definitional in Physlib: `RationalModel.eval_eq` and
`ReducedRationalResponse.eval` are the numerator-over-denominator quotient. No duplicate theorem
is introduced. The coefficient-list adapters are lemmas rather than theorems because they are
coordinate-explicit specializations to an already reduced polynomial quotient, not literal
restatements of the source's universally quantified system theorem.

The source's Theorem 3 unit-delay denominator contains the product `G1*G3`, whereas its printed
Theorem 4 expression contains `G1*G2`. Both are recorded without silently identifying them.
Consequently this file does not force a strict corrected Theorem 4 bridge. The coherent N7
`t`/`-I*k` construction is the source's own unprinted coherent branch; the printed incoherent
`1-k`/`k` graph is a different case.
-/

@[expose] public section

namespace Optics

noncomputable section

open Polynomial

namespace DCDR

/-!

## A. Coherent DCDR denominator degree and actual-pole count

-/

/-- The scalar multiplying `q²` in the coherent unit-delay feedback loop. -/
def UnitDelayParameters.loopCoefficient (p : UnitDelayParameters) : ℂ :=
  (p.feedbackGain : ℂ) *
    ((p.secondCoupler.throughAmplitude : ℂ) * (p.lowerGain : ℂ) *
        p.firstCoupler.throughAmplitude +
      DirectionalCoupler.crossCoefficient p.secondCoupler * (p.upperGain : ℂ) *
        DirectionalCoupler.crossCoefficient p.firstCoupler)

/-- Direct polynomial expansion exposes the coherent loop as one quadratic monomial. -/
lemma UnitDelayParameters.loopPolynomial_eq_C_mul_X_sq (p : UnitDelayParameters) :
    p.loopPolynomial = C p.loopCoefficient * X ^ 2 := by
  apply Polynomial.funext
  intro q
  simp [UnitDelayParameters.loopPolynomial, UnitDelayParameters.loopCoefficient,
    UnitDelayParameters.upperPolynomial, UnitDelayParameters.lowerPolynomial,
    UnitDelayParameters.feedbackPolynomial]
  ring

/-- The coherent unit-delay solve denominator is `1 - loopCoefficient*q²`. -/
lemma UnitDelayParameters.denominatorPolynomial_eq_one_sub_C_mul_X_sq
    (p : UnitDelayParameters) :
    p.denominatorPolynomial = 1 - C p.loopCoefficient * X ^ 2 := by
  rw [UnitDelayParameters.denominatorPolynomial, p.loopPolynomial_eq_C_mul_X_sq]

/-- The raw coherent unit-delay DCDR denominator has degree at most two. -/
lemma UnitDelayParameters.denominatorPolynomial_natDegree_le_two
    (p : UnitDelayParameters) :
    p.denominatorPolynomial.natDegree ≤ 2 := by
  rw [p.denominatorPolynomial_eq_one_sub_C_mul_X_sq]
  exact (Polynomial.natDegree_sub_le _ _).trans
    (max_le (by simp) (Polynomial.natDegree_C_mul_X_pow_le p.loopCoefficient 2))

namespace ResponseReduction

variable {p : UnitDelayParameters}

/-- Cancellation cannot raise the denominator degree above the raw DCDR degree two. -/
lemma reducedDenominator_natDegree_le_two (certificate : ResponseReduction p) :
    certificate.reduction.reduced.denominator.natDegree ≤ 2 := by
  have hDivides : certificate.reduction.reduced.denominator ∣
      certificate.reduction.rawDenominator := by
    refine ⟨certificate.reduction.cancelledFactor, ?_⟩
    exact certificate.reduction.rawDenominator_eq.trans (mul_comm _ _)
  calc
    certificate.reduction.reduced.denominator.natDegree ≤
        certificate.reduction.rawDenominator.natDegree :=
      Polynomial.natDegree_le_of_dvd hDivides
        certificate.reduction.rawDenominator_ne_zero
    _ = p.denominatorPolynomial.natDegree := congrArg Polynomial.natDegree
      certificate.rawDenominator_eq
    _ ≤ 2 := p.denominatorPolynomial_natDegree_le_two

/-- The certified actual reciprocal-coordinate pole set is finite. -/
lemma finite_actualPoles (certificate : ResponseReduction p) :
    certificate.actualPoles.Finite := by
  exact certificate.reduction.reduced.finite_zPoles

/-- Every selected unit-delay DCDR quotient has at most two actual reciprocal-coordinate poles.

This conclusion is cancellation-aware: it bounds the reduced denominator and does not promote a
cancelled internal singularity to an actual pole.
-/
lemma ncard_actualPoles_le_two (certificate : ResponseReduction p) :
    certificate.actualPoles.ncard ≤ 2 :=
  certificate.reduction.reduced.ncard_zPoles_le_natDegree.trans
    certificate.reducedDenominator_natDegree_le_two

end ResponseReduction

/-!

## B. Printed incoherent stability audit predicate

-/

/-- The complex expression printed in FMICS'15 Theorem 4's incoherent conditions. -/
def printedIncoherentStabilityExpression
    (G1 G2 G3 k1 k2 : ℂ) : ℂ :=
  k1 * k2 * G1 * G2 + (1 - k1) * (1 - k2) * G2 * G3

/-- The two printed incoherent Theorem 4 hypotheses, including its non-strict bound.

The second hypothesis is FMICS'15's own discovery relative to Binh [5]. It is not a Physlib
correction. The non-strict first hypothesis is intentionally distinct from strict Schur stability.
-/
def PrintedIncoherentStabilityConditions
    (G1 G2 G3 k1 k2 : ℂ) : Prop :=
  ‖Complex.sqrt (printedIncoherentStabilityExpression G1 G2 G3 k1 k2)‖ ≤ 1 ∧
    printedIncoherentStabilityExpression G1 G2 G3 k1 k2 ≠ 0

end DCDR

namespace DCDRSourceBridge

/-!

## C. FMICS'15 unit-delay source dictionary

-/

/-- Convert a nonnegative intensity gain to its canonical coherent field-amplitude gain. -/
def intensityGainToFieldAmplitudeGain (G : ℝ) : ℝ :=
  Real.sqrt G

/-- Convert a real field-amplitude gain to its intensity gain. -/
def fieldAmplitudeGainToIntensityGain (g : ℝ) : ℝ :=
  g ^ 2

/-- Squaring the canonical field gain recovers a nonnegative source intensity gain. -/
lemma fieldAmplitudeGainToIntensityGain_intensityGainToFieldAmplitudeGain
    {G : ℝ} (hG : 0 ≤ G) :
    fieldAmplitudeGainToIntensityGain (intensityGainToFieldAmplitudeGain G) = G := by
  exact Real.sq_sqrt hG

/-- Taking the canonical square root recovers a nonnegative field-amplitude gain. -/
lemma intensityGainToFieldAmplitudeGain_fieldAmplitudeGainToIntensityGain
    {g : ℝ} (hg : 0 ≤ g) :
    intensityGainToFieldAmplitudeGain (fieldAmplitudeGainToIntensityGain g) = g := by
  exact Real.sqrt_sq hg

/-- The five real parameters of FMICS'15's printed incoherent unit-delay DCDR formulas.

The paper quantifies complex symbols. This structure records the real-valued subfamily that can
be mapped to Physlib's real N7 amplitudes. Its `G_i` fields remain printed intensity gains; the
coherent map below assigns their canonical field-amplitude square roots.
-/
structure SourceParameters where
  /-- Printed upper-path intensity gain `G1`. -/
  G1 : ℝ
  /-- Printed lower-path intensity gain `G2`. -/
  G2 : ℝ
  /-- Printed feedback-path intensity gain `G3`. -/
  G3 : ℝ
  /-- Printed first incoherent intensity coefficient `k1`. -/
  k1 : ℝ
  /-- Printed second incoherent intensity coefficient `k2`. -/
  k2 : ℝ

/-- The source domain on which `k1` and `k2` are normalized intensity coefficients. -/
def SourceParameters.HasAdmissibleCouplings (p : SourceParameters) : Prop :=
  0 ≤ p.k1 ∧ p.k1 ≤ 1 ∧ 0 ≤ p.k2 ∧ p.k2 ≤ 1

/-- The source domain on which all three printed intensity gains admit faithful square roots. -/
def SourceParameters.HasNonnegativeGains (p : SourceParameters) : Prop :=
  0 ≤ p.G1 ∧ 0 ≤ p.G2 ∧ 0 ≤ p.G3

/-- The symbol map from printed intensities to coherent N7 amplitudes and field gains.

Its source interpretation is restricted to `HasNonnegativeGains`, where squaring each mapped
field gain recovers the printed intensity. This is a dictionary, not an equality between the
incoherent and coherent response models.
-/
def SourceParameters.toCoherentUnitDelayParameters
    (p : SourceParameters) : DCDR.UnitDelayParameters where
  firstCoupler :=
    { throughAmplitude := Real.sqrt (1 - p.k1)
      crossAmplitude := Real.sqrt p.k1 }
  secondCoupler :=
    { throughAmplitude := Real.sqrt (1 - p.k2)
      crossAmplitude := Real.sqrt p.k2 }
  upperGain := intensityGainToFieldAmplitudeGain p.G1
  lowerGain := intensityGainToFieldAmplitudeGain p.G2
  feedbackGain := intensityGainToFieldAmplitudeGain p.G3

/-- The coherent map exposes the four coupler amplitudes and three converted field gains. -/
lemma SourceParameters.toCoherentUnitDelayParameters_data (p : SourceParameters) :
    p.toCoherentUnitDelayParameters.firstCoupler.throughAmplitude =
        Real.sqrt (1 - p.k1) ∧
      p.toCoherentUnitDelayParameters.firstCoupler.crossAmplitude = Real.sqrt p.k1 ∧
      p.toCoherentUnitDelayParameters.secondCoupler.throughAmplitude =
          Real.sqrt (1 - p.k2) ∧
      p.toCoherentUnitDelayParameters.secondCoupler.crossAmplitude = Real.sqrt p.k2 ∧
      p.toCoherentUnitDelayParameters.upperGain =
          intensityGainToFieldAmplitudeGain p.G1 ∧
      p.toCoherentUnitDelayParameters.lowerGain =
          intensityGainToFieldAmplitudeGain p.G2 ∧
      p.toCoherentUnitDelayParameters.feedbackGain =
          intensityGainToFieldAmplitudeGain p.G3 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Canonical square-root gains lie in the coherent family's algebraic gain domain. -/
lemma SourceParameters.toCoherentUnitDelayParameters_isAdmissible (p : SourceParameters) :
    p.toCoherentUnitDelayParameters.IsAdmissible := by
  exact ⟨Real.sqrt_nonneg p.G1, Real.sqrt_nonneg p.G2, Real.sqrt_nonneg p.G3⟩

/-- On the source coupling domain, the first coherent through amplitude squares to `1-k1`. -/
lemma SourceParameters.firstThroughAmplitude_sq {p : SourceParameters}
    (hp : p.HasAdmissibleCouplings) :
    p.toCoherentUnitDelayParameters.firstCoupler.throughAmplitude ^ 2 = 1 - p.k1 := by
  exact Real.sq_sqrt (sub_nonneg.mpr hp.2.1)

/-- On the source coupling domain, the first coherent cross amplitude squares to `k1`. -/
lemma SourceParameters.firstCrossAmplitude_sq {p : SourceParameters}
    (hp : p.HasAdmissibleCouplings) :
    p.toCoherentUnitDelayParameters.firstCoupler.crossAmplitude ^ 2 = p.k1 := by
  exact Real.sq_sqrt hp.1

/-- On the source coupling domain, the second coherent through amplitude squares to `1-k2`. -/
lemma SourceParameters.secondThroughAmplitude_sq {p : SourceParameters}
    (hp : p.HasAdmissibleCouplings) :
    p.toCoherentUnitDelayParameters.secondCoupler.throughAmplitude ^ 2 = 1 - p.k2 := by
  exact Real.sq_sqrt (sub_nonneg.mpr hp.2.2.2)

/-- On the source coupling domain, the second coherent cross amplitude squares to `k2`. -/
lemma SourceParameters.secondCrossAmplitude_sq {p : SourceParameters}
    (hp : p.HasAdmissibleCouplings) :
    p.toCoherentUnitDelayParameters.secondCoupler.crossAmplitude ^ 2 = p.k2 := by
  exact Real.sq_sqrt hp.2.2.1

/-- The mapped upper field gain squares back to the printed upper intensity gain. -/
lemma SourceParameters.toCoherentUnitDelayParameters_upperGain_intensity
    {p : SourceParameters} (hp : p.HasNonnegativeGains) :
    fieldAmplitudeGainToIntensityGain p.toCoherentUnitDelayParameters.upperGain = p.G1 := by
  exact fieldAmplitudeGainToIntensityGain_intensityGainToFieldAmplitudeGain hp.1

/-- The mapped lower field gain squares back to the printed lower intensity gain. -/
lemma SourceParameters.toCoherentUnitDelayParameters_lowerGain_intensity
    {p : SourceParameters} (hp : p.HasNonnegativeGains) :
    fieldAmplitudeGainToIntensityGain p.toCoherentUnitDelayParameters.lowerGain = p.G2 := by
  exact fieldAmplitudeGainToIntensityGain_intensityGainToFieldAmplitudeGain hp.2.1

/-- The mapped feedback field gain squares back to the printed feedback intensity gain. -/
lemma SourceParameters.toCoherentUnitDelayParameters_feedbackGain_intensity
    {p : SourceParameters} (hp : p.HasNonnegativeGains) :
    fieldAmplitudeGainToIntensityGain p.toCoherentUnitDelayParameters.feedbackGain = p.G3 := by
  exact fieldAmplitudeGainToIntensityGain_intensityGainToFieldAmplitudeGain hp.2.2

/-- The coherent N7 loop coefficient named in the printed source symbols. -/
def SourceParameters.coherentLoopCoefficient (p : SourceParameters) : ℂ :=
  (intensityGainToFieldAmplitudeGain p.G3 : ℂ) *
    ((Real.sqrt (1 - p.k2) : ℂ) *
        (intensityGainToFieldAmplitudeGain p.G2 : ℂ) * Real.sqrt (1 - p.k1) +
      (-Complex.I * Real.sqrt p.k2) *
        (intensityGainToFieldAmplitudeGain p.G1 : ℂ) *
        (-Complex.I * Real.sqrt p.k1))

/-- The mapped coherent loop retains square-root amplitudes and the two `-I` cross gauges.

The definition of `coherentLoopCoefficient` pinpoints why this is not the printed incoherent
intensity coefficient below.
-/
lemma SourceParameters.toCoherentUnitDelayParameters_loopCoefficient (p : SourceParameters) :
    p.toCoherentUnitDelayParameters.loopCoefficient =
      p.coherentLoopCoefficient := by
  rfl

/-- The mapped coherent denominator uses the named amplitude-and-gauge coefficient. -/
lemma SourceParameters.toCoherentUnitDelayParameters_denominatorPolynomial
    (p : SourceParameters) :
    p.toCoherentUnitDelayParameters.denominatorPolynomial =
      1 - C p.coherentLoopCoefficient * X ^ 2 := by
  rw [p.toCoherentUnitDelayParameters.denominatorPolynomial_eq_one_sub_C_mul_X_sq,
    p.toCoherentUnitDelayParameters_loopCoefficient]

/-!

## D. Printed incoherent coefficient data

-/

/-- The coefficient multiplying `q` in the printed unit-delay numerator. -/
def SourceParameters.printedLinearCoefficient (p : SourceParameters) : ℝ :=
  (1 - p.k1) * (1 - p.k2) * p.G1 + p.k1 * p.k2 * p.G2

/-- The coefficient multiplying `q³` with a minus sign in the printed unit-delay numerator. -/
def SourceParameters.printedCubicCoefficient (p : SourceParameters) : ℝ :=
  (1 - 2 * p.k1) * (1 - 2 * p.k2) * p.G1 * p.G2 * p.G3

/-- The coefficient multiplying `q²` in FMICS'15 Theorem 3's unit-delay denominator. -/
def SourceParameters.printedLoopCoefficient (p : SourceParameters) : ℝ :=
  p.k1 * p.k2 * p.G1 * p.G3 +
    (1 - p.k1) * (1 - p.k2) * p.G2 * p.G3

/-- The printed incoherent unit-delay numerator polynomial, in Physlib's formal-`q` legend. -/
def SourceParameters.printedNumeratorPolynomial
    (p : SourceParameters) : Polynomial ℂ :=
  C (p.printedLinearCoefficient : ℂ) * X -
    C (p.printedCubicCoefficient : ℂ) * X ^ 3

/-- The printed incoherent unit-delay denominator polynomial, in Physlib's formal-`q` legend. -/
def SourceParameters.printedDenominatorPolynomial
    (p : SourceParameters) : Polynomial ℂ :=
  1 - C (p.printedLoopCoefficient : ℂ) * X ^ 2

/-- The printed denominator's explicit coefficient list on indices `0`, `1`, and `2`. -/
def SourceParameters.printedDenominatorCoefficients
    (p : SourceParameters) : ℕ → ℂ
  | 0 => 1
  | 2 => -(p.printedLoopCoefficient : ℂ)
  | _ => 0

/-- The explicit printed denominator list has the nonzero constant coefficient one. -/
lemma SourceParameters.printedDenominatorCoefficients_nonzero (p : SourceParameters) :
    ∃ i ∈ Finset.range 3, p.printedDenominatorCoefficients i ≠ 0 := by
  refine ⟨0, by simp, ?_⟩
  simp [SourceParameters.printedDenominatorCoefficients]

/-- The printed unit-delay denominator is exactly its coefficient sum through degree two. -/
lemma SourceParameters.printedDenominatorPolynomial_eq_coefficients
    (p : SourceParameters) :
    p.printedDenominatorPolynomial =
      ∑ i ∈ Finset.range 3, C (p.printedDenominatorCoefficients i) * X ^ i := by
  simp [SourceParameters.printedDenominatorPolynomial,
    SourceParameters.printedDenominatorCoefficients, Finset.sum_range_succ,
    sub_eq_add_neg]

/-- The printed incoherent unit-delay denominator has degree at most two. -/
lemma SourceParameters.printedDenominatorPolynomial_natDegree_le_two
    (p : SourceParameters) :
    p.printedDenominatorPolynomial.natDegree ≤ 2 := by
  rw [p.printedDenominatorPolynomial_eq_coefficients]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  exact (Polynomial.natDegree_C_mul_X_pow_le
    (p.printedDenominatorCoefficients i) i).trans
      (Nat.le_of_lt_succ (Finset.mem_range.mp hi))

/-- The printed unit-delay coefficient data gives finite reciprocal poles, at most two.

This is a polynomial-coordinate consequence only; it does not identify the printed denominator
with the coherent DCDR denominator.
-/
lemma SourceParameters.finite_zPoles_and_ncard_le_two
    (p : SourceParameters) (response : DelayTransfer.ReducedRationalResponse)
    (hDenominator : response.denominator = p.printedDenominatorPolynomial) :
    response.zPoles.Finite ∧ response.zPoles.ncard ≤ 2 := by
  apply response.finite_zPoles_and_ncard_le_of_denominator_eq_coefficients 2
    p.printedDenominatorCoefficients p.printedDenominatorCoefficients_nonzero
  exact hDenominator.trans p.printedDenominatorPolynomial_eq_coefficients

/-!

## E. FMICS'15 passive case data

-/

/-- FMICS'15 p. 175's passive source point, with both printed decimal couplings stored exactly as
the rational number `9/10`.
-/
def passiveCaseSourceParameters : SourceParameters where
  G1 := 1
  G2 := 1
  G3 := 1
  k1 := 9 / 10
  k2 := 9 / 10

/-- The coherent N7 image of FMICS'15 p. 175's passive source point.

This is a dictionary image, not an equality with the printed incoherent response.
-/
def passiveCaseUnitDelayParameters : DCDR.UnitDelayParameters :=
  passiveCaseSourceParameters.toCoherentUnitDelayParameters

end DCDRSourceBridge

end

end Optics
