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

The scalar expected values are obtained by directly expanding the component coefficients and
transfer definition. A separate response fixture solves the N5 channel equations at the zero-phase
point, so changing the explicit feedback pairing can break the check. A second independent fixture
sums the concrete geometric series with loop gain `3 / 10`.

“Resonance” and “antiresonance” below name the zero- and half-turn phase points. These fixtures do
not prove an extremum, minimum, or global resonance characterization.

These are fixed-carrier normalized modal-amplitude checks. They make no frequency-sweep,
dispersion, linewidth, or material-realization claim.

## ii. Key results

- `allPassRegression_resonance_throughTransfer`: the exact resonant transfer is `1 / 7`.
- `allPassRegression_antiresonance_throughTransfer`: the exact antiresonant transfer is `11 / 13`.
- `allPassRegression_resonance_denominator`: the resonant solve denominator is `7 / 10`.
- `allPassRegression_antiresonance_denominator`: the antiresonant solve denominator is `13 / 10`.
- `allPassRegression_resonance_responseTransform_entry`: direct N5 response evaluation.
- `allPassRegression_resonance_roundTripSeries`: direct concrete geometric-series evaluation.
- `allPassRegression_resonance_response_eq_series`: the two independent evaluations agree.

## iii. Table of contents

- A. Exact resonance fixture
- B. Exact antiresonance fixture

## iv. References

These exact values are source-neutral phase-point regressions. The response and series anchors,
rather than the scalar transfer checks alone, pin the explicit N5 feedback construction.
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

/-- The exact zero-phase fixture satisfies the N5 well-posedness gate. -/
lemma allPassRegression_resonance_isWellPosed :
    (netlist allPassRegressionResonanceParameters).IsWellPosed := by
  apply isWellPosed_of_hasNonzeroDenominator
  rw [Parameters.HasNonzeroDenominator,
    allPassRegression_resonance_denominator]
  norm_num

/-- Direct N5 channel elimination gives the exact input-to-through response entry `1 / 7`. -/
lemma allPassRegression_resonance_responseTransform_entry :
    (netlist allPassRegressionResonanceParameters).responseTransform
        allPassRegression_resonance_isWellPosed
        (Outgoing.mk (throughChannel allPassRegressionResonanceParameters))
        (Incident.mk (inputChannel allPassRegressionResonanceParameters)) =
      1 / 7 := by
  let p := allPassRegressionResonanceParameters
  let output := (netlist p).responseTransform
    allPassRegression_resonance_isWellPosed |>.toLinearMap (inputAmplitude p 1)
  have hMember : (inputAmplitude p 1, output) ∈ (netlist p).behavior := by
    rw [← (netlist p).toBehavior_responseTransform
      allPassRegression_resonance_isWellPosed,
      ModeTransform.mem_toBehavior_iff_toLinearMap]
  rcases ((netlist p).mem_behavior_iff_equations (inputAmplitude p 1) output).mp
      hMember with ⟨incident, outgoing, hScattering, hAssembly, hOutput⟩
  have hAssembly' :
      incident = (netlist p).connections.incidentAssembly outgoing (inputAmplitude p 1) := by
    simpa only [PortConnectionFamily.incidentAssembly] using hAssembly
  have hInput := congrArg
    (fun state => state (Incident.mk (couplerChannel p DirectionalCoupler.Port.leftFirst)))
    hAssembly'
  rw [incidentAssembly_apply_leftFirst, inputAmplitude_apply_input] at hInput
  have hCouplerLeft := congrArg
    (fun state => state (Incident.mk (couplerChannel p DirectionalCoupler.Port.leftSecond)))
    hAssembly'
  rw [incidentAssembly_apply_coupler_leftSecond,
    scatteringEquation_propagation_right p incident outgoing hScattering] at hCouplerLeft
  have hPropagationLeft := congrArg
    (fun state => state (Incident.mk (propagationChannel p MatchedPropagation.Port.left)))
    hAssembly'
  rw [incidentAssembly_apply_propagation_left,
    scatteringEquation_coupler_rightSecond p incident outgoing hScattering,
    hInput] at hPropagationLeft
  have hCouplerLeft' := hCouplerLeft
  have hPropagationLeft' := hPropagationLeft
  norm_num [p, allPassRegressionResonanceParameters, Parameters.loopCoefficient,
    Parameters.propagation, MatchedPropagation.transmissionCoefficient,
    MatchedPropagation.carrierPhaseFactor] at hCouplerLeft'
  norm_num [p, allPassRegressionResonanceParameters, Parameters.coupler,
    DirectionalCoupler.crossCoefficient] at hPropagationLeft'
  have hLoopSolution :
      incident (Incident.mk (couplerChannel p DirectionalCoupler.Port.leftSecond)) =
        -(4 / 7 : ℂ) * Complex.I := by
    linear_combination
      (10 / 7 : ℂ) * hCouplerLeft' + (5 / 7 : ℂ) * hPropagationLeft'
  have hThrough := scatteringEquation_coupler_rightFirst p incident outgoing hScattering
  rw [hInput] at hThrough
  have hReadout := congrArg (fun state => state (Outgoing.mk (throughChannel p))) hOutput
  rw [outputReadout_apply_through] at hReadout
  have hOutputCoordinate :
      ((netlist p).responseTransform allPassRegression_resonance_isWellPosed).toLinearMap
          (inputAmplitude p 1) (Outgoing.mk (throughChannel p)) =
        1 / 7 := by
    rw [hReadout, hThrough, hLoopSolution]
    simp [p, allPassRegressionResonanceParameters, Parameters.coupler,
      DirectionalCoupler.crossCoefficient]
    ring_nf
    rw [Complex.I_sq]
    norm_num
  simpa [p, inputAmplitude, Matrix.toLpLin_apply] using hOutputCoordinate

/-- Direct expansion gives the concrete circulation gain `3 / 10`. -/
lemma allPassRegression_resonance_loopGain :
    allPassRegressionResonanceParameters.loopGain = 3 / 10 := by
  norm_num [allPassRegressionResonanceParameters, Parameters.loopGain,
    Parameters.loopCoefficient, Parameters.propagation,
    MatchedPropagation.transmissionCoefficient, MatchedPropagation.carrierPhaseFactor]

/-- The concrete zero-phase circulation gain satisfies the strict series-convergence gate. -/
lemma allPassRegression_resonance_isContractive :
    allPassRegressionResonanceParameters.IsContractive := by
  rw [Parameters.IsContractive, allPassRegression_resonance_loopGain]
  norm_num

/-- Summing the concrete geometric series with ratio `3 / 10` gives `10 / 7`. -/
lemma allPassRegression_resonance_roundTripSeries :
    roundTripSeries allPassRegressionResonanceParameters = 10 / 7 := by
  rw [roundTripSeries, allPassRegression_resonance_loopGain]
  rw [tsum_geometric_of_norm_lt_one (by norm_num : ‖(3 / 10 : ℂ)‖ < 1)]
  apply Complex.ext <;> norm_num

/-- Direct expansion of the concrete convergent-series expression gives `1 / 7`. -/
lemma allPassRegression_resonance_throughTransferSeries :
    throughTransferSeries allPassRegressionResonanceParameters = 1 / 7 := by
  rw [throughTransferSeries, allPassRegression_resonance_loopCoefficient,
    allPassRegression_resonance_roundTripSeries]
  simp [allPassRegressionResonanceParameters, Parameters.coupler,
    DirectionalCoupler.crossCoefficient]
  rw [mul_pow, Complex.I_sq]
  norm_num

/-- The independently evaluated N5 response entry and convergent series agree at the fixture. -/
lemma allPassRegression_resonance_response_eq_series :
    (netlist allPassRegressionResonanceParameters).responseTransform
        allPassRegression_resonance_isWellPosed
        (Outgoing.mk (throughChannel allPassRegressionResonanceParameters))
        (Incident.mk (inputChannel allPassRegressionResonanceParameters)) =
      throughTransferSeries allPassRegressionResonanceParameters := by
  rw [allPassRegression_resonance_responseTransform_entry,
    allPassRegression_resonance_throughTransferSeries]

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
