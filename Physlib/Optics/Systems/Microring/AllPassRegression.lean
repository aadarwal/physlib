/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Systems.Microring.AllPass

/-!
# Regression tests for the all-pass microring

## i. Overview

The exact fixture uses the unitary `3-4-5` coupler and field attenuation `1 / 2`. At zero
round-trip phase its loop coefficient is `1 / 2` and the through transfer is `1 / 7`; at phase
`pi` its loop coefficient is `-1 / 2` and the through transfer is `11 / 13`.

The expected values below are obtained by directly expanding the component coefficients and scalar
transfer definition. They do not invoke the general unitary simplification, resonance, or
antiresonance results that these cases are intended to pin.

These are fixed-carrier normalized modal-amplitude checks. They make no frequency-sweep,
dispersion, linewidth, or material-realization claim.

## ii. Key results

- `allPassRegression_resonance_throughTransfer`: the exact resonant transfer is `1 / 7`.
- `allPassRegression_antiresonance_throughTransfer`: the exact antiresonant transfer is `11 / 13`.
- `allPassRegression_resonance_denominator`: the resonant solve denominator is `7 / 10`.
- `allPassRegression_antiresonance_denominator`: the antiresonant solve denominator is `13 / 10`.

## iii. Table of contents

- A. Exact resonance fixture
- B. Exact antiresonance fixture

## iv. References

These exact values are source-neutral regressions for the explicit N5 feedback construction in
`AllPass.lean`.
-/

@[expose] public section

namespace Optics

noncomputable section

namespace AllPass

/-! ## A. Exact resonance fixture -/

/-- A `3-4-5` coupler, half field retention, and zero round-trip phase. -/
def allPassRegressionResonanceParameters : Parameters where
  throughAmplitude := 3 / 5
  crossAmplitude := 4 / 5
  fieldAttenuation := 1 / 2
  roundTripPhase := 0

/-- The resonant regression fixture satisfies the N7 component-validity predicates. -/
lemma allPassRegression_resonance_isValid :
    allPassRegressionResonanceParameters.IsValid := by
  constructor
  · constructor
    · norm_num [allPassRegressionResonanceParameters, DirectionalCoupler.Parameters.IsValid]
    · constructor
      · norm_num [allPassRegressionResonanceParameters,
          DirectionalCoupler.Parameters.IsValid]
      · norm_num [allPassRegressionResonanceParameters,
          DirectionalCoupler.Parameters.IsUnitary,
          DirectionalCoupler.Parameters.powerFactor]
  · norm_num [allPassRegressionResonanceParameters, MatchedPropagation.Parameters.IsValid]

/-- Direct expansion gives the resonant one-pass field coefficient `1 / 2`. -/
lemma allPassRegression_resonance_loopCoefficient :
    allPassRegressionResonanceParameters.loopCoefficient = 1 / 2 := by
  norm_num [allPassRegressionResonanceParameters, Parameters.loopCoefficient,
    Parameters.propagation, MatchedPropagation.transmissionCoefficient,
    MatchedPropagation.carrierPhaseFactor]

/-- Direct expansion gives the resonant feedback denominator `7 / 10`. -/
lemma allPassRegression_resonance_denominator :
    allPassRegressionResonanceParameters.denominator = 7 / 10 := by
  norm_num [allPassRegressionResonanceParameters, Parameters.denominator, Parameters.loopGain,
    Parameters.loopCoefficient, Parameters.propagation,
    MatchedPropagation.transmissionCoefficient, MatchedPropagation.carrierPhaseFactor]

/-- Direct expansion gives the resonant through transfer `1 / 7`. -/
lemma allPassRegression_resonance_throughTransfer :
    throughTransfer allPassRegressionResonanceParameters = 1 / 7 := by
  simp [throughTransfer, allPassRegressionResonanceParameters,
    DirectionalCoupler.crossCoefficient, Parameters.coupler, Parameters.denominator,
    Parameters.loopGain, Parameters.loopCoefficient, Parameters.propagation,
    MatchedPropagation.transmissionCoefficient, MatchedPropagation.carrierPhaseFactor]
  rw [mul_pow, Complex.I_sq]
  norm_num

/-! ## B. Exact antiresonance fixture -/

/-- The same exact fixture with a half-turn round-trip phase. -/
def allPassRegressionAntiresonanceParameters : Parameters where
  throughAmplitude := 3 / 5
  crossAmplitude := 4 / 5
  fieldAttenuation := 1 / 2
  roundTripPhase := ((Real.pi : ℝ) : Real.Angle)

/-- Direct expansion gives the antiresonant one-pass field coefficient `-1 / 2`. -/
lemma allPassRegression_antiresonance_loopCoefficient :
    allPassRegressionAntiresonanceParameters.loopCoefficient = -1 / 2 := by
  simp [allPassRegressionAntiresonanceParameters, Parameters.loopCoefficient,
    Parameters.propagation, MatchedPropagation.transmissionCoefficient,
    MatchedPropagation.carrierPhaseFactor, Real.Angle.toCircle_coe, Circle.coe_exp]
  apply Complex.ext <;> norm_num

/-- Direct expansion gives the antiresonant feedback denominator `13 / 10`. -/
lemma allPassRegression_antiresonance_denominator :
    allPassRegressionAntiresonanceParameters.denominator = 13 / 10 := by
  rw [Parameters.denominator, Parameters.loopGain,
    allPassRegression_antiresonance_loopCoefficient]
  norm_num [allPassRegressionAntiresonanceParameters]

/-- Direct expansion gives the antiresonant through transfer `11 / 13`. -/
lemma allPassRegression_antiresonance_throughTransfer :
    throughTransfer allPassRegressionAntiresonanceParameters = 11 / 13 := by
  rw [throughTransfer, allPassRegression_antiresonance_loopCoefficient,
    allPassRegression_antiresonance_denominator]
  simp [allPassRegressionAntiresonanceParameters, Parameters.coupler,
    DirectionalCoupler.crossCoefficient]
  rw [mul_pow, Complex.I_sq]
  norm_num

end AllPass

end

end Optics
