/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Systems.DCDR.MultipleDelayPolynomial

/-!
# FMICS'15 multiple-delay source dictionary for the DCDR

## i. Overview

FMICS'15 Eq. 3 prints verbatim: “The general expression for the photonic transmittance is given
as follows: `T_i = t_{a_i} G_i z^{m_i}`.” This dictionary takes `t_{a_i} = 1`, renames the
retained polynomial indeterminate to formal `q`, and uses the reciprocal reparameterization at
`Physlib/Optics/Systems/DelayTransfer/Evaluation.lean:397-455`. Thus `q = z⁻¹`, and its path
substitution is `T_i = G_i*q^m_i = G_i/z^m_i`.

FMICS'15 Table 1 prints these four configurations:

- “Active DCDR Circuit with Unit Delay” — `m1 = m2 = m3 = 1`;
- “Optical Amplifier in the Fiber Path” — `(m1 = m2 = m3 = 1) ∧ (G_i > 1)`;
- “Passive DCDR Circuit” — `G1 = G2 = G3 = 1`;
- “DCDR with Multiple Delay” — `m_i` can have different combinations.

For `T_i = G_i*q^m_i`, the printed Theorem 3 numerator and denominator retain the source's
intensity gains `G_i` and the source's `1-k` and `k` coefficients. The map to the coherent N7
family instead uses square-root field gains, square-root coupler amplitudes, and the pinned `-I`
cross gauge. No response, pole, or stability identity between those two polynomial models is
asserted.

The real unit-delay source dictionary being extended is at
`Physlib/Optics/Systems/DCDR/SourceBridge.lean:197-237`; the pinned cross gauge is declared at
`Physlib/Optics/Components/DirectionalCoupler.lean:63-79`.

## ii. Key results

- `DCDRSourceBridge.MultipleDelaySourceParameters`: the eight-symbol source dictionary.
- `MultipleDelaySourceParameters.HasNonnegativeGains`: the coherent-map source domain.
- `MultipleDelaySourceParameters.toCoherentMultipleDelayParameters`: the coherent symbol map.
- `MultipleDelaySourceParameters.printedNumeratorPolynomial`: printed Theorem 3 numerator.
- `MultipleDelaySourceParameters.printedDenominatorPolynomial`: printed Theorem 3 denominator.
- `MultipleDelaySourceParameters.printedDenominatorPolynomial_natDegree_le`: degree bound.
- `MultipleDelaySourceParameters.finite_zPoles_and_ncard_le_delayShape`: pole-count adapter.

## iii. Table of contents

- A. FMICS'15 multiple-delay source dictionary

## iv. References

No result here claims physical resonance, coherent--incoherent equivalence, BIBO stability beyond
S4P's stated gate, normalized-modal or electromagnetic power, causality or time-domain behavior,
a physical-frequency interpretation, or any fact about the unavailable HOL script.

S4P restricts its Schur/BIBO result to the proper causal one-pole class at
`Physlib/Optics/Systems/DelayTransfer/Stability.lean:424-457`.

U. Siddique, S. M. Beillahi, and S. Tahar, “On the Formal Analysis of Photonic Signal
Processing Systems”, FMICS 2015, LNCS 9128, Equation 3, Theorem 3, and Table 1, pp. 169--174.

The coherent N7 `t`/`-I*k` construction is the source's own unprinted coherent branch; the
printed incoherent `1-k`/`k` graph remains a separate case.
-/

@[expose] public section

namespace Optics

noncomputable section

open Polynomial

namespace DCDRSourceBridge

/-!

## A. FMICS'15 multiple-delay source dictionary

-/

/-- FMICS'15's real printed symbols with one natural exponent on each DCDR path.

This dictionary selects `t_{a_i} = 1` in Eq. 3. Its formal-`q` path is therefore
`G_i*q^m_i`; under Physlib's reciprocal legend `q = z⁻¹`, it is `G_i/z^m_i`.
-/
structure MultipleDelaySourceParameters where
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
  /-- Printed upper-path delay exponent `m1`. -/
  m1 : ℕ
  /-- Printed lower-path delay exponent `m2`. -/
  m2 : ℕ
  /-- Printed feedback-path delay exponent `m3`. -/
  m3 : ℕ

/-- Forgetting delays recovers the dictionary at
`Physlib/Optics/Systems/DCDR/SourceBridge.lean:197-213`. -/
def MultipleDelaySourceParameters.toSourceParameters
    (p : MultipleDelaySourceParameters) : SourceParameters where
  G1 := p.G1
  G2 := p.G2
  G3 := p.G3
  k1 := p.k1
  k2 := p.k2

/-- Embed the dictionary at
`Physlib/Optics/Systems/DCDR/SourceBridge.lean:197-213` with every exponent one. -/
def SourceParameters.toMultipleDelaySourceParameters
    (p : SourceParameters) : MultipleDelaySourceParameters where
  G1 := p.G1
  G2 := p.G2
  G3 := p.G3
  k1 := p.k1
  k2 := p.k2
  m1 := 1
  m2 := 1
  m3 := 1

/-- The source domain on which all three printed intensity gains admit faithful square roots. -/
def MultipleDelaySourceParameters.HasNonnegativeGains
    (p : MultipleDelaySourceParameters) : Prop :=
  p.toSourceParameters.HasNonnegativeGains

/-- Map printed intensities to coherent amplitudes and field gains while preserving exponents.

Its source interpretation is restricted to `HasNonnegativeGains`, where the mapped field gains
square back to the printed intensities. This is a symbol dictionary, not a
coherent--incoherent response identity.
-/
def MultipleDelaySourceParameters.toCoherentMultipleDelayParameters
    (p : MultipleDelaySourceParameters) : DCDR.MultipleDelayParameters where
  firstCoupler :=
    { throughAmplitude := Real.sqrt (1 - p.k1)
      crossAmplitude := Real.sqrt p.k1 }
  secondCoupler :=
    { throughAmplitude := Real.sqrt (1 - p.k2)
      crossAmplitude := Real.sqrt p.k2 }
  upperGain := intensityGainToFieldAmplitudeGain p.G1
  lowerGain := intensityGainToFieldAmplitudeGain p.G2
  feedbackGain := intensityGainToFieldAmplitudeGain p.G3
  m1 := p.m1
  m2 := p.m2
  m3 := p.m3

/-- The multiple-delay source map exposes converted field gains and preserves every exponent. -/
lemma MultipleDelaySourceParameters.toCoherentMultipleDelayParameters_data
    (p : MultipleDelaySourceParameters) :
    p.toCoherentMultipleDelayParameters.firstCoupler.throughAmplitude =
        Real.sqrt (1 - p.k1) ∧
      p.toCoherentMultipleDelayParameters.firstCoupler.crossAmplitude = Real.sqrt p.k1 ∧
        p.toCoherentMultipleDelayParameters.secondCoupler.throughAmplitude =
            Real.sqrt (1 - p.k2) ∧
          p.toCoherentMultipleDelayParameters.secondCoupler.crossAmplitude =
              Real.sqrt p.k2 ∧
            p.toCoherentMultipleDelayParameters.upperGain =
                intensityGainToFieldAmplitudeGain p.G1 ∧
              p.toCoherentMultipleDelayParameters.lowerGain =
                  intensityGainToFieldAmplitudeGain p.G2 ∧
                p.toCoherentMultipleDelayParameters.feedbackGain =
                    intensityGainToFieldAmplitudeGain p.G3 ∧
                  p.toCoherentMultipleDelayParameters.m1 = p.m1 ∧
                    p.toCoherentMultipleDelayParameters.m2 = p.m2 ∧
                      p.toCoherentMultipleDelayParameters.m3 = p.m3 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The mapped upper complex field gain squares back to its printed intensity gain. -/
lemma MultipleDelaySourceParameters.toCoherentMultipleDelayParameters_upperGain_sq
    {p : MultipleDelaySourceParameters} (hp : p.HasNonnegativeGains) :
    p.toCoherentMultipleDelayParameters.upperGain ^ 2 = (p.G1 : ℂ) := by
  change 0 ≤ p.G1 ∧ 0 ≤ p.G2 ∧ 0 ≤ p.G3 at hp
  change (Real.sqrt p.G1 : ℂ) ^ 2 = (p.G1 : ℂ)
  exact_mod_cast Real.sq_sqrt hp.1

/-- The mapped lower complex field gain squares back to its printed intensity gain. -/
lemma MultipleDelaySourceParameters.toCoherentMultipleDelayParameters_lowerGain_sq
    {p : MultipleDelaySourceParameters} (hp : p.HasNonnegativeGains) :
    p.toCoherentMultipleDelayParameters.lowerGain ^ 2 = (p.G2 : ℂ) := by
  change 0 ≤ p.G1 ∧ 0 ≤ p.G2 ∧ 0 ≤ p.G3 at hp
  change (Real.sqrt p.G2 : ℂ) ^ 2 = (p.G2 : ℂ)
  exact_mod_cast Real.sq_sqrt hp.2.1

/-- The mapped feedback complex field gain squares back to its printed intensity gain. -/
lemma MultipleDelaySourceParameters.toCoherentMultipleDelayParameters_feedbackGain_sq
    {p : MultipleDelaySourceParameters} (hp : p.HasNonnegativeGains) :
    p.toCoherentMultipleDelayParameters.feedbackGain ^ 2 = (p.G3 : ℂ) := by
  change 0 ≤ p.G1 ∧ 0 ≤ p.G2 ∧ 0 ≤ p.G3 at hp
  change (Real.sqrt p.G3 : ℂ) ^ 2 = (p.G3 : ℂ)
  exact_mod_cast Real.sq_sqrt hp.2.2

/-- Extending and mapping a unit-delay dictionary agrees with the literal coherent embedding. -/
lemma SourceParameters.toMultipleDelaySourceParameters_coherent
    (p : SourceParameters) :
    p.toMultipleDelaySourceParameters.toCoherentMultipleDelayParameters =
      p.toCoherentUnitDelayParameters.toMultipleDelayParameters := by
  rfl

/-- The coefficient of `q^m1` in the printed Theorem 3 numerator. -/
def MultipleDelaySourceParameters.printedUpperCoefficient
    (p : MultipleDelaySourceParameters) : ℝ :=
  (1 - p.k1) * (1 - p.k2) * p.G1

/-- The coefficient of `q^m2` in the printed Theorem 3 numerator. -/
def MultipleDelaySourceParameters.printedLowerCoefficient
    (p : MultipleDelaySourceParameters) : ℝ :=
  p.k1 * p.k2 * p.G2

/-- The coefficient subtracted at `q^(m1+m2+m3)` in the printed numerator. -/
def MultipleDelaySourceParameters.printedCubicCoefficient
    (p : MultipleDelaySourceParameters) : ℝ :=
  (1 - 2 * p.k1) * (1 - 2 * p.k2) * p.G1 * p.G2 * p.G3

/-- The coefficient of `q^(m1+m3)` in the printed Theorem 3 denominator. -/
def MultipleDelaySourceParameters.printedUpperLoopCoefficient
    (p : MultipleDelaySourceParameters) : ℝ :=
  p.k1 * p.k2 * p.G1 * p.G3

/-- The coefficient of `q^(m2+m3)` in the printed Theorem 3 denominator. -/
def MultipleDelaySourceParameters.printedLowerLoopCoefficient
    (p : MultipleDelaySourceParameters) : ℝ :=
  (1 - p.k1) * (1 - p.k2) * p.G2 * p.G3

/-- FMICS'15 Theorem 3's printed incoherent numerator after `T_i = G_i*q^m_i`. -/
def MultipleDelaySourceParameters.printedNumeratorPolynomial
    (p : MultipleDelaySourceParameters) : Polynomial ℂ :=
  C (p.printedUpperCoefficient : ℂ) * X ^ p.m1 +
    C (p.printedLowerCoefficient : ℂ) * X ^ p.m2 -
      C (p.printedCubicCoefficient : ℂ) * X ^ (p.m1 + p.m2 + p.m3)

/-- FMICS'15 Theorem 3's printed incoherent denominator after `T_i = G_i*q^m_i`. -/
def MultipleDelaySourceParameters.printedDenominatorPolynomial
    (p : MultipleDelaySourceParameters) : Polynomial ℂ :=
  1 - C (p.printedUpperLoopCoefficient : ℂ) * X ^ (p.m1 + p.m3) -
    C (p.printedLowerLoopCoefficient : ℂ) * X ^ (p.m2 + p.m3)

/-- The printed Theorem 3 numerator has its three substituted path degrees. -/
lemma MultipleDelaySourceParameters.printedNumeratorPolynomial_natDegree_le
    (p : MultipleDelaySourceParameters) :
    p.printedNumeratorPolynomial.natDegree ≤
      max (max p.m1 p.m2) (p.m1 + p.m2 + p.m3) := by
  have hUpper := Polynomial.natDegree_C_mul_X_pow_le
    (p.printedUpperCoefficient : ℂ) p.m1
  have hLower := Polynomial.natDegree_C_mul_X_pow_le
    (p.printedLowerCoefficient : ℂ) p.m2
  have hCubic := Polynomial.natDegree_C_mul_X_pow_le
    (p.printedCubicCoefficient : ℂ) (p.m1 + p.m2 + p.m3)
  have hDirect :
      (C (p.printedUpperCoefficient : ℂ) * X ^ p.m1 +
        C (p.printedLowerCoefficient : ℂ) * X ^ p.m2).natDegree ≤
        max p.m1 p.m2 :=
    (Polynomial.natDegree_add_le _ _).trans (max_le_max hUpper hLower)
  rw [MultipleDelaySourceParameters.printedNumeratorPolynomial]
  exact (Polynomial.natDegree_sub_le _ _).trans
    (max_le_max hDirect hCubic)

/-- The printed Theorem 3 denominator has its two path-pair degrees. -/
lemma MultipleDelaySourceParameters.printedDenominatorPolynomial_natDegree_le
    (p : MultipleDelaySourceParameters) :
    p.printedDenominatorPolynomial.natDegree ≤
      max (p.m1 + p.m3) (p.m2 + p.m3) := by
  have hUpper := Polynomial.natDegree_C_mul_X_pow_le
    (p.printedUpperLoopCoefficient : ℂ) (p.m1 + p.m3)
  have hLower := Polynomial.natDegree_C_mul_X_pow_le
    (p.printedLowerLoopCoefficient : ℂ) (p.m2 + p.m3)
  rw [MultipleDelaySourceParameters.printedDenominatorPolynomial]
  calc
    _ ≤ max
        (1 - C (p.printedUpperLoopCoefficient : ℂ) *
          X ^ (p.m1 + p.m3)).natDegree
        (C (p.printedLowerLoopCoefficient : ℂ) *
          X ^ (p.m2 + p.m3)).natDegree := Polynomial.natDegree_sub_le _ _
    _ ≤ max (max 0 (p.m1 + p.m3)) (p.m2 + p.m3) :=
      max_le_max
        ((Polynomial.natDegree_sub_le _ _).trans
          (max_le_max (by simp) hUpper)) hLower
    _ = max (p.m1 + p.m3) (p.m2 + p.m3) := by simp

/-- Apply the reciprocal-`z` bound at
`Physlib/Optics/Systems/DelayTransfer/Stability.lean:225-243` to this denominator.

The coordinate legend is `q = z⁻¹`, and the resulting bound is the two path-pair degree shape.
-/
lemma MultipleDelaySourceParameters.finite_zPoles_and_ncard_le_delayShape
    (p : MultipleDelaySourceParameters)
    (response : DelayTransfer.ReducedRationalResponse)
    (hDenominator : response.denominator = p.printedDenominatorPolynomial) :
    response.zPoles.Finite ∧
      response.zPoles.ncard ≤ max (p.m1 + p.m3) (p.m2 + p.m3) := by
  refine ⟨response.finite_zPoles, response.ncard_zPoles_le_natDegree.trans ?_⟩
  rw [hDenominator]
  exact p.printedDenominatorPolynomial_natDegree_le

/-- The unit-delay embedding recovers the printed numerator at
`Physlib/Optics/Systems/DCDR/SourceBridge.lean:310-327`. -/
lemma SourceParameters.toMultipleDelaySourceParameters_printedNumeratorPolynomial
    (p : SourceParameters) :
    p.toMultipleDelaySourceParameters.printedNumeratorPolynomial =
      p.printedNumeratorPolynomial := by
  simp [SourceParameters.toMultipleDelaySourceParameters,
    MultipleDelaySourceParameters.printedNumeratorPolynomial,
    MultipleDelaySourceParameters.printedUpperCoefficient,
    MultipleDelaySourceParameters.printedLowerCoefficient,
    MultipleDelaySourceParameters.printedCubicCoefficient,
    SourceParameters.printedNumeratorPolynomial,
    SourceParameters.printedLinearCoefficient,
    SourceParameters.printedCubicCoefficient]
  ring

/-- The unit-delay embedding recovers the printed denominator at
`Physlib/Optics/Systems/DCDR/SourceBridge.lean:318-332`. -/
lemma SourceParameters.toMultipleDelaySourceParameters_printedDenominatorPolynomial
    (p : SourceParameters) :
    p.toMultipleDelaySourceParameters.printedDenominatorPolynomial =
      p.printedDenominatorPolynomial := by
  simp [SourceParameters.toMultipleDelaySourceParameters,
    MultipleDelaySourceParameters.printedDenominatorPolynomial,
    MultipleDelaySourceParameters.printedUpperLoopCoefficient,
    MultipleDelaySourceParameters.printedLowerLoopCoefficient,
    SourceParameters.printedDenominatorPolynomial,
    SourceParameters.printedLoopCoefficient]
  ring

end DCDRSourceBridge

end

end Optics
