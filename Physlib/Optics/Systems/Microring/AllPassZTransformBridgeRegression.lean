/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Systems.DelayTransfer.EvaluationRegression
public import Physlib.Optics.Systems.Microring.AllPassChainRegression
public import Physlib.Optics.Systems.Microring.AllPassMasonRegression
public import Physlib.Optics.Systems.Microring.AllPassZTransformBridge
public import Physlib.Optics.Systems.Microring.AllPassZTransformRegression

/-!
# Regression tests for the all-pass Z-transform bridge

## i. Overview

The exact recurrence values are compared with the proof-gated rational/N5F response, raw N5
channel elimination, the convergent circulation series, complete Mason response, typed
scattering, backward-first chain coordinates, and the original relational behavior. A
quarter-turn fixture pins the negative-exponential carrier sign at a nonreal compiled response.
A deliberately nonunitary coupler proves that the bridge's unitarity hypothesis is load-bearing.

The real and nonreal response values have anchors independent of the general bridge lemmas. The
named ROC witness is an absolute-convergence result; no material delay law, continuous-time
realization, reciprocity statement, or electromagnetic power normalization is claimed.

## ii. Key results

- `allPassZRegression_cross_semantics`: exact common-domain agreement across the ring layers.
- `allPassZRegression_quarterTurn_rawN5F_agreement`: nonreal recurrence/compiled-response anchor.

## iii. Table of contents

- A. Independent cross-semantics agreement
- B. Fixed-carrier phase-sign sentinel
- C. Load-bearing unitary-coupler gate

## iv. References

These cross-semantics fixtures are Physlib-original and make no external source-parity claim.
-/

@[expose] public section

namespace Optics

noncomputable section

namespace AllPass

open DelayTransfer
open Physlib.ZTransform

/-!
## A. Independent cross-semantics agreement
-/

/-- The resonant point lies in the named absolute ROC by the strict pole-radius bound. -/
lemma allPassZRegression_one_mem_zTransferROC :
    (1 : ℂ) ∈ zTransferROC (3 / 5) (1 / 2) := by
  apply mem_zTransferROC_of_norm_feedback_lt_norm
  · norm_num
  · norm_num

/-- The exact resonant fixture meets every independently stated common-domain gate. -/
lemma allPassZRegression_resonance_crossSemanticsDomain :
    IsZCrossSemanticsDomain allPassRegressionResonanceParameters 1 where
  isValid := allPassRegression_resonance_isValid
  couplerIsUnitary := allPassRegression_resonance_isValid.1.isUnitary
  isContractive := allPassRegression_resonance_isContractive
  loopCoefficient_eq := by
    rw [allPassRegression_resonance_loopCoefficient]
    norm_num [allPassRegressionResonanceParameters]
  mem_zTransferROC := by
    simpa [allPassRegressionResonanceParameters] using
      allPassZRegression_one_mem_zTransferROC
  throughTransfer_ne_zero := allPassChainRegression_resonance_throughTransfer_ne_zero

/-- At the resonant fixture, the causal transform, rational/N5F response, circulation series, raw
N5 response, complete Mason response, typed scattering, backward-first chain, and original
relational behavior meet at the exact value `1 / 7`. The N5 and circulation values retain their
independent channel-equation and geometric-series anchors. -/
lemma allPassZRegression_cross_semantics :
    let p := allPassRegressionResonanceParameters
    let h := allPassZRegression_resonance_crossSemanticsDomain
    transform
        (causalOutput
          (p.throughAmplitude : ℂ) (p.fieldAttenuation : ℂ) unitImpulse) 1 = 1 / 7 ∧
      reciprocalZThroughResponse p 1 h.mem_reciprocalZResponseDomain = 1 / 7 ∧
      throughTransferSeries p = 1 / 7 ∧
      (netlist p).responseTransform
          (isWellPosed_of_hasNonzeroDenominator p h.hasNonzeroDenominator)
          (Outgoing.mk (throughChannel p)) (Incident.mk (inputChannel p)) = 1 / 7 ∧
      (netlist p).masonResponseTransform
          (Outgoing.mk (throughChannel p)) (Incident.mk (inputChannel p)) = 1 / 7 ∧
      (packagedTwoPortScattering p h.hasNonzeroDenominator).leftToRightTransmission
          (ForwardWave.mk ()) (ForwardWave.mk ()) = 1 / 7 ∧
      backwardFirstChainTransform p h.hasNonzeroDenominator h.throughTransfer_ne_zero
          (Sum.inr (ForwardWave.mk ())) (Sum.inr (ForwardWave.mk ())) = 1 / 7 ∧
      (inputAmplitude p 1,
          (netlist p).masonResponseTransform.toLinearMap (inputAmplitude p 1)) ∈
        (netlist p).behavior := by
  let p := allPassRegressionResonanceParameters
  let h := allPassZRegression_resonance_crossSemanticsDomain
  have hAgreement := zCrossSemantics_agree p 1 h
  have hTransfer :
      zTransfer (p.throughAmplitude : ℂ) (p.fieldAttenuation : ℂ) 1 = 1 / 7 := by
    simpa [p, allPassRegressionResonanceParameters] using allPassZRegression_transfer_one
  refine ⟨hAgreement.causalImpulseResponse.trans hTransfer, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hAgreement.rationalN5F.symm.trans hTransfer
  · simpa [p] using allPassRegression_resonance_throughTransferSeries
  · simpa [p] using allPassRegression_resonance_responseTransform_entry
  · exact hAgreement.completeMason.symm.trans hTransfer
  · exact hAgreement.packagedScattering.symm.trans hTransfer
  · exact hAgreement.backwardFirstChain.symm.trans hTransfer
  · exact hAgreement.relationalBehavior

/-!
## B. Fixed-carrier phase-sign sentinel
-/

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

/-- Direct closed-form expansion of the fixed-carrier through transfer gives the pinned nonreal
value. -/
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

/-- The quarter-turn point belongs to the raw reciprocal-Z compiled-response domain. -/
lemma allPassZRegression_quarterTurn_reciprocalZDomain :
    Complex.I ∈
      (allPassRationalNetlist
        allPassZRegressionQuarterTurnParameters).reciprocalZ.responseDomain := by
  have hParameters : allPassZRegressionQuarterTurnParameters =
      allPassRationalQuadratureParameters := rfl
  rw [hParameters]
  exact allPassRationalNetlistReciprocalZQuadratureDomain

/-- The raw proof-gated reciprocal-Z response, reached through the compiled N7/N5 equations,
has the pinned nonreal value. -/
lemma allPassZRegression_quarterTurn_reciprocalZThroughResponse :
    reciprocalZThroughResponse allPassZRegressionQuarterTurnParameters Complex.I
        allPassZRegression_quarterTurn_reciprocalZDomain =
      75 / 109 + 32 / 109 * Complex.I := by
  simpa [reciprocalZThroughResponse, allPassZRegressionQuarterTurnParameters,
    allPassRationalQuadratureParameters] using
      allPassRationalNetlist_reciprocalZ_quadrature_response_entry

/-- The independently expanded recurrence and raw compiled response agree at the nonreal carrier
point, without either general Z-to-ring bridge theorem. -/
lemma allPassZRegression_quarterTurn_rawN5F_agreement :
    zTransfer
        (allPassZRegressionQuarterTurnParameters.throughAmplitude : ℂ)
        (allPassZRegressionQuarterTurnParameters.fieldAttenuation : ℂ)
        (carrierPoint allPassZRegressionQuarterTurnParameters) =
      reciprocalZThroughResponse allPassZRegressionQuarterTurnParameters Complex.I
        allPassZRegression_quarterTurn_reciprocalZDomain := by
  rw [allPassZRegression_quarterTurn_carrierPoint,
    allPassZRegression_quarterTurn_reciprocalZThroughResponse]
  simpa [allPassZRegressionQuarterTurnParameters] using allPassZRegression_transfer_I

/-- The independently expanded recurrence and closed fixed-carrier response also agree at the
nonreal carrier point, without using the general bridge theorem. -/
lemma allPassZRegression_quarterTurn_agreement :
    zTransfer
        (allPassZRegressionQuarterTurnParameters.throughAmplitude : ℂ)
        (allPassZRegressionQuarterTurnParameters.fieldAttenuation : ℂ)
        (carrierPoint allPassZRegressionQuarterTurnParameters) =
      throughTransfer allPassZRegressionQuarterTurnParameters := by
  rw [allPassZRegression_quarterTurn_carrierPoint,
    allPassZRegression_quarterTurn_throughTransfer]
  simpa [allPassZRegressionQuarterTurnParameters] using allPassZRegression_transfer_I

/-!
## C. Load-bearing unitary-coupler gate
-/

/-- A deliberately nonunitary coupler with the same through amplitude and carrier factor as the
resonant fixture. -/
def allPassZRegressionNonunitaryParameters : Parameters where
  throughAmplitude := 3 / 5
  crossAmplitude := 1 / 2
  fieldAttenuation := 1 / 2
  roundTripPhase := 0

/-- Direct closed-form evaluation of the nonunitary fixture gives `59 / 140`. -/
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
