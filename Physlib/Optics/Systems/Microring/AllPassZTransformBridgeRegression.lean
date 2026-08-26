/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Systems.Microring.AllPassChainRegression
public import Physlib.Optics.Systems.Microring.AllPassMasonRegression
public import Physlib.Optics.Systems.Microring.AllPassZTransformBridge
public import Physlib.Optics.Systems.Microring.AllPassZTransformRegression

/-!
# Regression tests for the all-pass Z-transform bridge

## i. Overview

The exact recurrence values are compared with raw N5 channel elimination, the convergent
circulation series, forward-path Mason enumeration, typed scattering, and backward-first chain
coordinates. A quarter-turn fixture pins the negative-exponential carrier sign at a nonreal point.
A deliberately nonunitary coupler proves that the bridge's unitarity hypothesis is load-bearing.

The value anchors are expanded independently of the general bridge lemmas. They do not establish
an ROC, material delay law, continuous-time realization, reciprocity statement, or electromagnetic
power normalization.

## ii. Key results

- `allPassZRegression_cross_semantics`: independent value agreement across the ring layers.

## iii. Table of contents

- A. Independent cross-semantics agreement
- B. Fixed-carrier phase-sign sentinel
- C. Load-bearing unitary-coupler gate
-/

@[expose] public section

namespace Optics

noncomputable section

namespace AllPass

/-! ## A. Independent cross-semantics agreement -/

/-- At the resonant fixture, direct recurrence-symbol evaluation, raw N5 elimination, the
circulation series, forward-path Mason enumeration, typed scattering, and the backward-first
chain all give `1 / 7`. The proof does not use any general Z-to-ring bridge lemma. -/
lemma allPassZRegression_cross_semantics :
    zTransfer (3 / 5) (1 / 2) 1 =
        (netlist allPassRegressionResonanceParameters).responseTransform
          allPassRegression_resonance_isWellPosed
          (Outgoing.mk (throughChannel allPassRegressionResonanceParameters))
          (Incident.mk (inputChannel allPassRegressionResonanceParameters)) ∧
      zTransfer (3 / 5) (1 / 2) 1 =
        throughTransferSeries allPassRegressionResonanceParameters ∧
      zTransfer (3 / 5) (1 / 2) 1 =
        loopMasonThroughTransfer allPassRegressionResonanceParameters ∧
      zTransfer (3 / 5) (1 / 2) 1 =
        (packagedTwoPortScattering allPassRegressionResonanceParameters
            allPassChainRegression_resonance_hasNonzeroDenominator).leftToRightTransmission
          (ForwardWave.mk ()) (ForwardWave.mk ()) ∧
      zTransfer (3 / 5) (1 / 2) 1 =
        allPassChainRegressionResonanceChain
          (Sum.inr (ForwardWave.mk ())) (Sum.inr (ForwardWave.mk ())) := by
  rw [allPassZRegression_transfer_one,
    allPassRegression_resonance_responseTransform_entry,
    allPassRegression_resonance_throughTransferSeries,
    allPassMasonRegression_loopMasonThroughTransfer,
    packagedTwoPortScattering_leftToRightTransmission_entry,
    allPassRegression_resonance_throughTransfer,
    allPassChainRegression_resonance_chain_inr_inr]
  simp

/-! ## B. Fixed-carrier phase-sign sentinel -/

/-- The `3-4-5` fixture at positive quarter-turn round-trip phase. -/
def allPassZRegressionQuarterTurnParameters : Parameters where
  throughAmplitude := 3 / 5
  crossAmplitude := 4 / 5
  fieldAttenuation := 1 / 2
  roundTripPhase := (((Real.pi / 2 : ℝ)) : Real.Angle)

/-- Positive quarter-turn phase has the negative-exponential carrier factor `-I`. -/
lemma allPassZRegression_quarterTurn_carrierPhaseFactor :
    MatchedPropagation.carrierPhaseFactor
        allPassZRegressionQuarterTurnParameters.roundTripPhase = -Complex.I := by
  change ((-(((Real.pi / 2 : ℝ) : Real.Angle))).toCircle : ℂ) = -Complex.I
  rw [← Real.Angle.coe_neg, Real.Angle.toCircle_coe, Circle.coe_exp]
  convert Complex.exp_neg_pi_div_two_mul_I using 1
  congr 1
  push_cast
  ring

/-- Consequently, the selected Z evaluation point is `I`, so its reciprocal is `-I`. -/
lemma allPassZRegression_quarterTurn_carrierPoint :
    carrierPoint allPassZRegressionQuarterTurnParameters = Complex.I := by
  rw [carrierPoint, allPassZRegression_quarterTurn_carrierPhaseFactor, inv_neg,
    Complex.inv_I]
  ring

/-- The one-pass field coefficient is `-I / 2` at the quarter-turn point. -/
lemma allPassZRegression_quarterTurn_loopCoefficient :
    allPassZRegressionQuarterTurnParameters.loopCoefficient =
      -(1 / 2 : ℂ) * Complex.I := by
  rw [Parameters.loopCoefficient, Parameters.propagation,
    MatchedPropagation.transmissionCoefficient,
    allPassZRegression_quarterTurn_carrierPhaseFactor]
  norm_num [allPassZRegressionQuarterTurnParameters]

/-- The corresponding feedback denominator is `1 + (3 / 10) I`. -/
lemma allPassZRegression_quarterTurn_denominator :
    allPassZRegressionQuarterTurnParameters.denominator =
      1 + (3 / 10 : ℂ) * Complex.I := by
  rw [Parameters.denominator, Parameters.loopGain,
    allPassZRegression_quarterTurn_loopCoefficient]
  norm_num [allPassZRegressionQuarterTurnParameters]
  ring

/-- Direct N7/N5 expansion at the quarter-turn point gives the same nonreal value as the
independently expanded recurrence transfer. -/
lemma allPassZRegression_quarterTurn_throughTransfer :
    throughTransfer allPassZRegressionQuarterTurnParameters =
      75 / 109 + 32 / 109 * Complex.I := by
  rw [throughTransfer, allPassZRegression_quarterTurn_loopCoefficient,
    allPassZRegression_quarterTurn_denominator]
  have hInverse : (1 + (3 / 10 : ℂ) * Complex.I)⁻¹ =
      (100 - 30 * Complex.I) / 109 := by
    apply inv_eq_of_mul_eq_one_right
    field_simp
    ring_nf
    norm_num [Complex.I_sq]
  simp [allPassZRegressionQuarterTurnParameters, Parameters.coupler,
    DirectionalCoupler.crossCoefficient]
  rw [mul_pow, Complex.I_sq]
  conv_lhs =>
    rhs
    rw [div_eq_mul_inv, hInverse]
  ring_nf
  norm_num [Complex.I_sq]
  ring

/-- The independently expanded recurrence and ring responses agree at the nonreal carrier point,
without using the general bridge theorem. -/
lemma allPassZRegression_quarterTurn_agreement :
    zTransfer
        (allPassZRegressionQuarterTurnParameters.throughAmplitude : ℂ)
        (allPassZRegressionQuarterTurnParameters.fieldAttenuation : ℂ)
        (carrierPoint allPassZRegressionQuarterTurnParameters) =
      throughTransfer allPassZRegressionQuarterTurnParameters := by
  rw [allPassZRegression_quarterTurn_carrierPoint,
    allPassZRegression_quarterTurn_throughTransfer]
  simpa [allPassZRegressionQuarterTurnParameters] using allPassZRegression_transfer_I

/-! ## C. Load-bearing unitary-coupler gate -/

/-- A deliberately nonunitary coupler with the same through amplitude and carrier factor as the
resonant fixture. -/
def allPassZRegressionNonunitaryParameters : Parameters where
  throughAmplitude := 3 / 5
  crossAmplitude := 1 / 2
  fieldAttenuation := 1 / 2
  roundTripPhase := 0

/-- Direct N7/N5 evaluation of the nonunitary fixture gives `59 / 140`. -/
lemma allPassZRegression_nonunitary_throughTransfer :
    throughTransfer allPassZRegressionNonunitaryParameters = 59 / 140 := by
  simp [throughTransfer, allPassZRegressionNonunitaryParameters,
    DirectionalCoupler.crossCoefficient, Parameters.coupler, Parameters.denominator,
    Parameters.loopGain, Parameters.loopCoefficient, Parameters.propagation,
    MatchedPropagation.transmissionCoefficient, MatchedPropagation.carrierPhaseFactor]
  rw [mul_pow, Complex.I_sq]
  norm_num

/-- The independently stated recurrence still evaluates to `1 / 7` at `z = 1`. -/
lemma allPassZRegression_nonunitary_zTransfer :
    zTransfer
        (allPassZRegressionNonunitaryParameters.throughAmplitude : ℂ)
        (allPassZRegressionNonunitaryParameters.fieldAttenuation : ℂ) 1 = 1 / 7 := by
  simpa [allPassZRegressionNonunitaryParameters] using allPassZRegression_transfer_one

/-- Without coupler unitarity, the standard recurrence transfer and the N7/N5 ring response need
not agree. This makes the unitarity hypothesis in the production bridge load-bearing. -/
lemma allPassZRegression_nonunitary_transfers_ne :
    zTransfer
        (allPassZRegressionNonunitaryParameters.throughAmplitude : ℂ)
        (allPassZRegressionNonunitaryParameters.fieldAttenuation : ℂ) 1 ≠
      throughTransfer allPassZRegressionNonunitaryParameters := by
  rw [allPassZRegression_nonunitary_zTransfer,
    allPassZRegression_nonunitary_throughTransfer]
  norm_num

end AllPass

end

end Optics
