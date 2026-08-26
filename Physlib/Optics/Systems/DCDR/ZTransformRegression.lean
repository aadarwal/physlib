/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Systems.DCDR.PolesRegression
public import Physlib.Optics.Systems.DCDR.ZTransformBridge

/-!
# Regression tests for the DCDR Z-transform bridge

## i. Overview

The stable common-domain fixture uses exact `3-4-5` couplers, gains `(9/16, 1, 1)`, and `z = 1`.
Its two coherent loop paths cancel, while its direct and three-delay paths add to the response
`-1`. The regression pins the causal transform, reduced quotient, raw reciprocal-Z N5F response,
circulation series, fixed N5 response, complete Mason response, typed packaged scattering, and
original relational behavior at that same exact value.

The nonreal `z = I` anchor expands `q = z⁻¹ = -I` directly and reaches the raw compiled response
without `zCrossSemantics_agree`. The active-amplifier sentinel has loop gain `-4`: its algebraic
transfer is `-67/20`, while Mathlib's totalized nonsummable geometric `tsum` makes the unguarded
circulation expression `1/4`. Thus the contraction/Schur gates can detect a real divergence.

These are algebraic discrete-time fixtures, not physical resonance claims. No coherent--incoherent
equivalence, BIBO conclusion, modal or electromagnetic power statement, Maxwell time-domain
interpretation, reciprocity, physical-frequency interpretation, or HOL-script claim is made.

## ii. Key results

- `DCDR.zRegression_crossSemantics`: every applicable DCDR view is pinned at `-1`.
- `DCDR.zRegression_nonreal_raw_compiled`: the `z = I`, `q = -I` compiled anchor.
- `DCDR.zRegression_active_circulation_ne_transfer`: the load-bearing contraction sentinel.

## iii. Table of contents

- A. Exact stable fixture and rational data
- B. Common-domain gates
- C. Cross-semantics value anchors
- D. Nonreal reciprocal-coordinate anchor
- E. Active-amplifier gate sentinel

## iv. References

These adversarial fixtures are Physlib-original. They exercise the coherent branch without
identifying it with FMICS'15's printed incoherent formula.
-/

@[expose] public section

namespace Optics.DCDR

noncomputable section

open Polynomial
open Physlib.ZTransform

/-!

## A. Exact stable fixture and rational data

-/

/-- The exact unitary `3/5` through, `4/5` cross-amplitude regression coupler. -/
def zRegressionCoupler : DirectionalCoupler.Parameters where
  throughAmplitude := 3 / 5
  crossAmplitude := 4 / 5

/-- A nontrivial stable point whose two coherent feedback-loop paths cancel. -/
def zRegressionParameters : UnitDelayParameters where
  firstCoupler := zRegressionCoupler
  secondCoupler := zRegressionCoupler
  upperGain := 9 / 16
  lowerGain := 1
  feedbackGain := 1

/-- The stable fixture satisfies the rational component family's algebraic validity gate. -/
lemma zRegressionParameters_isAdmissible : zRegressionParameters.IsAdmissible := by
  norm_num [UnitDelayParameters.IsAdmissible, zRegressionParameters]

/-- Direct N7 coefficient expansion shows exact cancellation of the two loop paths. -/
lemma zRegression_loopPolynomial_expansion :
    zRegressionParameters.loopPolynomial = 0 := by
  apply Polynomial.funext
  intro q
  norm_num [UnitDelayParameters.loopPolynomial, UnitDelayParameters.upperPolynomial,
    UnitDelayParameters.lowerPolynomial, UnitDelayParameters.feedbackPolynomial,
    zRegressionParameters, zRegressionCoupler,
    DirectionalCoupler.crossCoefficient]
  right
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The corresponding raw recurrence denominator is the unit polynomial. -/
lemma zRegression_denominatorPolynomial_expansion :
    zRegressionParameters.denominatorPolynomial = 1 := by
  rw [UnitDelayParameters.denominatorPolynomial, zRegression_loopPolynomial_expansion]
  simp

/-- The directly expanded selected numerator retains both one-delay and three-delay paths. -/
lemma zRegression_responseNumeratorPolynomial_expansion :
    zRegressionParameters.responseNumeratorPolynomial =
      C (-7 / 16) * X + C (-9 / 16) * X ^ 3 := by
  apply Polynomial.funext
  intro q
  norm_num [UnitDelayParameters.responseNumeratorPolynomial,
    UnitDelayParameters.directPolynomial, UnitDelayParameters.denominatorPolynomial,
    UnitDelayParameters.loopPolynomial, UnitDelayParameters.feedbackReadoutPolynomial,
    UnitDelayParameters.feedbackDrivePolynomial, UnitDelayParameters.upperPolynomial,
    UnitDelayParameters.lowerPolynomial, UnitDelayParameters.feedbackPolynomial,
    zRegressionParameters, zRegressionCoupler,
    DirectionalCoupler.crossCoefficient]
  ring_nf
  rw [Complex.I_sq, Complex.I_pow_four]
  ring

/-- The displayed stable numerator is nonzero. -/
lemma zRegression_numerator_ne_zero :
    C (-7 / 16 : ℂ) * X + C (-9 / 16) * X ^ 3 ≠ 0 := by
  intro hZero
  have hEvaluation := congrArg (Polynomial.eval 1) hZero
  norm_num at hEvaluation

/-- The exact coprime response retained by the stable regression point. -/
def zRegressionReducedResponse : DelayTransfer.ReducedRationalResponse where
  numerator := C (-7 / 16) * X + C (-9 / 16) * X ^ 3
  denominator := 1
  numerator_ne_zero := zRegression_numerator_ne_zero
  denominator_ne_zero := one_ne_zero
  isCoprime := isCoprime_one_right

/-- The stable regression reduction removes only the unit polynomial. -/
def zRegressionRationalReduction : DelayTransfer.RationalReduction where
  rawNumerator := zRegressionParameters.responseNumeratorPolynomial
  rawDenominator := zRegressionParameters.denominatorPolynomial
  cancelledFactor := 1
  reduced := zRegressionReducedResponse
  cancelledFactor_ne_zero := one_ne_zero
  rawNumerator_eq := by
    rw [zRegression_responseNumeratorPolynomial_expansion]
    simp [zRegressionReducedResponse]
  rawDenominator_eq := by
    rw [zRegression_denominatorPolynomial_expansion]
    simp [zRegressionReducedResponse]

/-- The reduction certificate is tied to the selected DCDR response polynomials. -/
def zRegressionResponseReduction : ResponseReduction zRegressionParameters where
  reduction := zRegressionRationalReduction
  rawNumerator_eq := rfl
  rawDenominator_eq := rfl

/-!

## B. Common-domain gates

-/

/-- The stable recurrence has no retained feedback lags after coherent path cancellation. -/
lemma zRegression_zFeedbackLags_eq_empty :
    zFeedbackLags zRegressionParameters = ∅ := by
  rw [zFeedbackLags, zRegression_loopPolynomial_expansion]
  rfl

/-- The stable recurrence satisfies the strict coefficient-contraction criterion. -/
lemma zRegressionParameters_isZContractive :
    zRegressionParameters.IsZContractive := by
  simp [UnitDelayParameters.IsZContractive, zRegression_zFeedbackLags_eq_empty]

/-- The evaluated fixed-carrier feedback loop vanishes at `z = 1`. -/
lemma zRegression_fixed_loopGain :
    (zRegressionParameters.at (1 : ℂ)).loopGain = 0 := by
  rw [← zRegressionParameters.eval_loopPolynomial,
    zRegression_loopPolynomial_expansion]
  norm_num

/-- The local circulation series is strictly contractive at the selected point. -/
lemma zRegression_fixed_loopIsContractive :
    ‖(zRegressionParameters.at (1 : ℂ)).loopGain‖ < 1 := by
  rw [zRegression_fixed_loopGain]
  norm_num

/-- With no feedback lags, the causal impulse response is the finite feedforward combination. -/
lemma zRegression_causalOutput_eq_delayCombination :
    causalOutput zRegressionParameters unitImpulse =
      delayCombination (zFeedforwardLags zRegressionParameters)
        (zFeedforwardCoefficients zRegressionParameters) unitImpulse := by
  apply eq_of_isRecurrenceSolution
    (zero_notMem_zFeedbackLags zRegressionParameters)
    (causalOutput_isCausal zRegressionParameters unitImpulse)
    (unitImpulse_isCausal.delayCombination _ _)
    (causalOutput_isRecurrenceSolution zRegressionParameters unitImpulse_isCausal)
  rw [IsRecurrenceSolution, zRegression_zFeedbackLags_eq_empty]
  funext n
  simp [delayCombination]

/-- The exact point `z = 1` lies in the named absolute-convergence ROC. -/
lemma zRegression_one_mem_zTransferROC :
    (1 : ℂ) ∈ zTransferROC zRegressionParameters := by
  rw [zTransferROC, iirROC]
  refine ⟨⟨⟨one_ne_zero, summable_seriesTerm_unitImpulse 1⟩,
    ⟨one_ne_zero, ?_⟩⟩, ?_⟩
  · rw [zRegression_causalOutput_eq_delayCombination]
    exact summable_seriesTerm_delayCombination _ _
      (summable_seriesTerm_unitImpulse 1)
  · change 1 - delaySymbol (zFeedbackLags zRegressionParameters)
        (zFeedbackCoefficients zRegressionParameters) (1 : ℂ)⁻¹ ≠ 0
    rw [delaySymbol_zFeedbackCoefficients,
      zRegression_loopPolynomial_expansion]
    norm_num

/-- The unit cancelled factor is nonzero at the selected reciprocal point. -/
lemma zRegression_noPoleCancellation :
    zRegressionRationalReduction.NoPoleCancellation 1 := by
  simp [DelayTransfer.RationalReduction.NoPoleCancellation,
    zRegressionRationalReduction]

/-- The reciprocal point avoids the reduced unit denominator. -/
lemma zRegression_one_mem_reducedEvaluationDomain :
    (1 : ℂ) ∈ zRegressionReducedResponse.evaluationDomain := by
  simp [DelayTransfer.ReducedRationalResponse.evaluationDomain,
    zRegressionReducedResponse]

/-- The unit-denominator reduced response has no reciprocal-coordinate poles. -/
lemma zRegressionReducedResponse_isSchurStable :
    zRegressionReducedResponse.IsSchurStable := by
  intro z hz
  rcases hz with ⟨_hz, hRoot⟩
  change (1 : Polynomial ℂ).eval z⁻¹ = 0 at hRoot
  norm_num at hRoot

/-- The exact stable fixture meets every independently stated common-domain gate. -/
lemma zRegression_crossSemanticsDomain :
    IsZCrossSemanticsDomain zRegressionParameters zRegressionResponseReduction 1 where
  isAdmissible := zRegressionParameters_isAdmissible
  recurrenceIsContractive := zRegressionParameters_isZContractive
  reducedIsSchurStable := zRegressionReducedResponse_isSchurStable
  loopIsContractive := by simpa using zRegression_fixed_loopIsContractive
  mem_zTransferROC := zRegression_one_mem_zTransferROC
  noPoleCancellation := by
    simpa [zRegressionResponseReduction] using zRegression_noPoleCancellation
  mem_reducedEvaluationDomain := by
    simpa [zRegressionResponseReduction, zRegressionRationalReduction] using
      zRegression_one_mem_reducedEvaluationDomain

/-- The fixed `q = 1` presentation has the scalar N5 solve gate supplied by the common domain. -/
lemma zRegression_fixed_hasNonzeroDenominator :
    (zRegressionParameters.at (1 : ℂ)).HasNonzeroDenominator := by
  simpa using zRegression_crossSemanticsDomain.hasNonzeroDenominator

/-- The exact fixed-carrier N5 well-posedness witness for the stable fixture. -/
noncomputable def zRegressionWellPosed :
    (netlist (zRegressionParameters.at (1 : ℂ))).IsWellPosed :=
  isWellPosed_of_hasNonzeroDenominator
    (zRegressionParameters.at (1 : ℂ)) zRegression_fixed_hasNonzeroDenominator

/-!

## C. Cross-semantics value anchors

-/

/-- Direct recurrence-symbol expansion gives the common response value `-1`. -/
lemma zRegression_zTransfer_one : zTransfer zRegressionParameters 1 = -1 := by
  rw [zTransfer_eq_quotient, zRegression_responseNumeratorPolynomial_expansion,
    zRegression_denominatorPolynomial_expansion]
  norm_num

/-- Direct reduced-data expansion gives the common response value `-1`. -/
lemma zRegression_reducedResponse_one : zRegressionReducedResponse.eval 1 = -1 := by
  norm_num [DelayTransfer.ReducedRationalResponse.eval, zRegressionReducedResponse]

/-- Direct compiled rational-data expansion gives the reciprocal-Z response value `-1`. -/
lemma zRegression_rationalZEliminationResponse_one :
    rationalZEliminationResponse zRegressionParameters 1
      zRegression_crossSemanticsDomain.mem_reciprocalZResponseDomain = -1 := by
  rw [rationalZEliminationResponse_eq_responseModel,
    DelayTransfer.RationalModel.eval_eq]
  simp only [responseModel, MvPolynomial.eval_toMvPolynomial]
  rw [zRegression_responseNumeratorPolynomial_expansion,
    zRegression_denominatorPolynomial_expansion]
  norm_num

/-- Direct fixed data show the selected direct gain is `-7/16`. -/
lemma zRegression_fixed_directGain :
    (zRegressionParameters.at (1 : ℂ)).directGain = -7 / 16 := by
  rw [Parameters.directGain, UnitDelayParameters.lowerCoefficient_at,
    UnitDelayParameters.upperCoefficient_at]
  norm_num [UnitDelayParameters.at, zRegressionParameters, zRegressionCoupler,
    DirectionalCoupler.crossCoefficient]
  ring_nf
  rw [Complex.I_sq]
  norm_num

/-- Direct fixed data show the selected feedback readout gain is `-(3/4) I`. -/
  lemma zRegression_fixed_feedbackReadoutGain :
    (zRegressionParameters.at (1 : ℂ)).feedbackReadoutGain =
      -(3 / 4) * Complex.I := by
  rw [Parameters.feedbackReadoutGain, UnitDelayParameters.lowerCoefficient_at,
    UnitDelayParameters.upperCoefficient_at]
  norm_num [UnitDelayParameters.at, zRegressionParameters, zRegressionCoupler,
    DirectionalCoupler.crossCoefficient]
  ring

/-- Direct fixed data show the returning drive gain is `-(3/4) I`. -/
lemma zRegression_fixed_feedbackDrive :
    (zRegressionParameters.at (1 : ℂ)).feedbackDrive =
      -(3 / 4) * Complex.I := by
  rw [Parameters.feedbackDrive, UnitDelayParameters.feedbackCoefficient_at,
    UnitDelayParameters.lowerCoefficient_at, UnitDelayParameters.upperCoefficient_at]
  norm_num [UnitDelayParameters.at, zRegressionParameters, zRegressionCoupler,
    DirectionalCoupler.crossCoefficient]
  ring

/-- Direct geometric-series expansion gives the common circulation value `-1`. -/
lemma zRegression_circulationSeries_one :
    circulationSeries zRegressionParameters 1 = -1 := by
  rw [circulationSeries]
  norm_num
  rw [zRegression_fixed_loopGain,
    tsum_geometric_of_norm_lt_one (by norm_num : ‖(0 : ℂ)‖ < 1),
    zRegression_fixed_directGain, zRegression_fixed_feedbackReadoutGain,
    zRegression_fixed_feedbackDrive]
  ring_nf
  rw [Complex.I_sq]
  norm_num

/-- Direct rational evaluation gives the fixed-carrier coherent transfer value `-1`. -/
lemma zRegression_fixed_transfer :
    transfer (zRegressionParameters.at (1 : ℂ)) = -1 := by
  rw [← responseModel_eval zRegressionParameters 1,
    DelayTransfer.RationalModel.eval_eq]
  simp only [responseModel, MvPolynomial.eval_toMvPolynomial]
  rw [zRegression_responseNumeratorPolynomial_expansion,
    zRegression_denominatorPolynomial_expansion]
  norm_num

/-- Raw N7 elimination gives the selected fixed N5 value `-1`. -/
lemma zRegression_eliminationResponse :
    eliminationResponse (zRegressionParameters.at (1 : ℂ))
      zRegressionWellPosed = -1 := by
  rw [eliminationResponse_eq_transfer]
  exact zRegression_fixed_transfer

/-- G-04 gives the complete extracted Mason response value `-1`. -/
lemma zRegression_masonResponse :
    masonResponse (zRegressionParameters.at (1 : ℂ)) = -1 := by
  rw [masonResponse_eq_eliminationResponse
    (zRegressionParameters.at (1 : ℂ))
      zRegression_fixed_hasNonzeroDenominator]
  exact zRegression_eliminationResponse

/-- Canonical typed packaging preserves the selected N5 entry `-1`. -/
lemma zRegression_packagedScattering_entry :
    ((netlist (zRegressionParameters.at (1 : ℂ))).packagedScattering
      zRegressionWellPosed).toModeTransform
        (outputChannel (zRegressionParameters.at (1 : ℂ)))
        (inputChannel (zRegressionParameters.at (1 : ℂ))) = -1 := by
  exact zRegression_eliminationResponse

/-- Every applicable DCDR cross-semantics view meets at the exact value `-1`.

The proof uses the independent anchors above and does not invoke `zCrossSemantics_agree`.
-/
lemma zRegression_crossSemantics :
    transform (causalOutput zRegressionParameters unitImpulse) 1 = -1 ∧
      zRegressionReducedResponse.eval 1 = -1 ∧
      rationalZEliminationResponse zRegressionParameters 1
        zRegression_crossSemanticsDomain.mem_reciprocalZResponseDomain = -1 ∧
      circulationSeries zRegressionParameters 1 = -1 ∧
      eliminationResponse (zRegressionParameters.at (1 : ℂ))
        zRegressionWellPosed = -1 ∧
      masonResponse (zRegressionParameters.at (1 : ℂ)) = -1 ∧
      ((netlist (zRegressionParameters.at (1 : ℂ))).packagedScattering
        zRegressionWellPosed).toModeTransform
          (outputChannel (zRegressionParameters.at (1 : ℂ)))
          (inputChannel (zRegressionParameters.at (1 : ℂ))) = -1 ∧
      HasSelectedRelationalResponse (zRegressionParameters.at (1 : ℂ)) (-1) := by
  refine ⟨?_, zRegression_reducedResponse_one,
    zRegression_rationalZEliminationResponse_one,
    zRegression_circulationSeries_one, zRegression_eliminationResponse,
    zRegression_masonResponse, zRegression_packagedScattering_entry, ?_⟩
  · rw [transform_causalImpulseResponse_eq_zTransfer
      zRegression_crossSemanticsDomain.mem_zTransferROC]
    exact zRegression_zTransfer_one
  · simpa [zRegression_zTransfer_one] using
      zTransfer_hasSelectedRelationalResponse zRegressionParameters 1
        zRegression_crossSemanticsDomain.hasNonzeroDenominator

/-!

## D. Nonreal reciprocal-coordinate anchor

-/

/-- Direct recurrence data at `z = I`, hence `q = -I`, give `-(7/8) I`. -/
lemma zRegression_stable_zTransfer_I :
    zTransfer stableUnitDelayParameters Complex.I = -(7 / 8) * Complex.I := by
  rw [zTransfer_eq_quotient, Complex.inv_I,
    stable_responseNumeratorPolynomial_expansion,
    stable_denominatorPolynomial_expansion]
  norm_num [stableNumerator, stableDenominator, Complex.I_mul_I]
  rw [show (-Complex.I) ^ 3 = Complex.I by
    norm_num [pow_succ, Complex.I_mul_I]]
  ring

/-- The raw compiled reciprocal-Z response has the same independently expanded nonreal value. -/
lemma zRegression_stable_rawCompiled_I :
    rationalZEliminationResponse stableUnitDelayParameters Complex.I
      stable_I_mem_reciprocalZResponseDomain = -(7 / 8) * Complex.I := by
  rw [rationalZEliminationResponse_eq_responseModel,
    DelayTransfer.RationalModel.eval_eq]
  simp only [responseModel, MvPolynomial.eval_toMvPolynomial]
  rw [Complex.inv_I, stable_responseNumeratorPolynomial_expansion,
    stable_denominatorPolynomial_expansion]
  norm_num [stableNumerator, stableDenominator, Complex.I_mul_I]
  rw [show (-Complex.I) ^ 3 = Complex.I by
    norm_num [pow_succ, Complex.I_mul_I]]
  ring

/-- The nonreal recurrence and raw compiled anchors agree without the cross-semantics bridge. -/
lemma zRegression_nonreal_raw_compiled :
    zTransfer stableUnitDelayParameters Complex.I =
      rationalZEliminationResponse stableUnitDelayParameters Complex.I
        stable_I_mem_reciprocalZResponseDomain := by
  rw [zRegression_stable_zTransfer_I, zRegression_stable_rawCompiled_I]

/-!

## E. Active-amplifier gate sentinel

-/

/-- Direct recurrence-symbol expansion gives the active algebraic value `-67/20`. -/
lemma zRegression_active_zTransfer_one :
    zTransfer unstableAmplifierParameters 1 = -67 / 20 := by
  rw [zTransfer_eq_quotient, unstable_responseNumeratorPolynomial_expansion,
    unstable_denominatorPolynomial_expansion]
  norm_num [unstableNumerator, unstableDenominator]

/-- The active fixed-carrier loop gain at `z = 1` is exactly `-4`. -/
lemma zRegression_active_loopGain :
    (unstableAmplifierParameters.at (1 : ℂ)).loopGain = -4 := by
  rw [← unstableAmplifierParameters.eval_loopPolynomial,
    unstable_loopPolynomial_expansion]
  norm_num

/-- Direct fixed data give the active fixture's direct gain `1/4`. -/
lemma zRegression_active_directGain :
    (unstableAmplifierParameters.at (1 : ℂ)).directGain = 1 / 4 := by
  rw [Parameters.directGain, UnitDelayParameters.lowerCoefficient_at,
    UnitDelayParameters.upperCoefficient_at]
  norm_num [UnitDelayParameters.at, unstableAmplifierParameters,
    poleRegressionCoupler, DirectionalCoupler.crossCoefficient]
  ring_nf
  rw [Complex.I_sq]
  norm_num

/-- The active loop's geometric power sequence is not summable. -/
lemma zRegression_active_geometric_not_summable :
    ¬Summable (fun n : ℕ => (-4 : ℂ) ^ n) := by
  rw [summable_geometric_iff_norm_lt_one]
  norm_num

/-- Mathlib totalizes the active nonsummable geometric `tsum` to zero. -/
lemma zRegression_active_geometric_tsum :
    ∑' n : ℕ, (-4 : ℂ) ^ n = 0 :=
  tsum_eq_zero_of_not_summable zRegression_active_geometric_not_summable

/-- Without the contraction gate, the totalized circulation expression evaluates to `1/4`. -/
lemma zRegression_active_circulationSeries_one :
    circulationSeries unstableAmplifierParameters 1 = 1 / 4 := by
  rw [circulationSeries]
  norm_num
  rw [zRegression_active_loopGain, zRegression_active_geometric_tsum,
    zRegression_active_directGain]
  ring

/-- The active fixture makes the circulation contraction gate visibly load-bearing. -/
lemma zRegression_active_circulation_ne_transfer :
    circulationSeries unstableAmplifierParameters 1 ≠
      zTransfer unstableAmplifierParameters 1 := by
  rw [zRegression_active_circulationSeries_one, zRegression_active_zTransfer_one]
  norm_num

/-- The active response cannot inhabit the common domain because its reduced S4P Schur gate
fails. -/
lemma zRegression_active_not_crossSemanticsDomain :
    ¬IsZCrossSemanticsDomain unstableAmplifierParameters
      unstableResponseReduction 1 := by
  intro hDomain
  exact unstableReducedResponse_not_isSchurStable hDomain.reducedIsSchurStable

end

end Optics.DCDR
