/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Systems.DCDR.PolesRegression
public import Physlib.Optics.Systems.DCDR.ResponseRegression
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
without `zCrossSemantics_agree`. The separate stable point with loop polynomial `-(1/4)q²`
exercises the proved lag-two geometric ROC criterion at `z = 1`. The active-amplifier sentinel has
loop gain `-4`: its algebraic transfer is `-67/20`, while Mathlib's totalized nonsummable geometric
`tsum` makes the unguarded circulation expression `1/4`. Thus the contraction/Schur gates can
detect a real divergence.

These are algebraic discrete-time fixtures, not physical resonance claims. No coherent--incoherent
equivalence, BIBO conclusion, modal or electromagnetic power statement, Maxwell time-domain
interpretation, reciprocity, physical-frequency interpretation, or HOL-script claim is made.
Power would mean normalized modal power, not electromagnetic power before the finite,
common-frequency, Maxwell-qualified, pairwise-integrable, mutually flux-orthogonal,
unit-normalized bridge at
`Physlib/Optics/HarmonicFlux/PropagatingModePower.lean:16-22,60-93`.

## ii. Key results

- `DCDR.zRegression_crossSemantics`: every applicable DCDR view is pinned at `-1`.
- `DCDR.zRegression_stable_one_mem_zTransferROC`: nonzero-loop ROC membership is derived.
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
open Physlib.SignalFlowGraph
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

/-- The stable nonzero-loop fixture retains exactly lag two. -/
lemma zRegression_stable_zFeedbackLags :
    zFeedbackLags stableUnitDelayParameters = {2} := by
  rw [zFeedbackLags, stable_loopPolynomial_expansion]
  ext n
  simp

/-- The retained stable feedback coefficient is the square of `I/2`. -/
lemma zRegression_stable_zFeedbackCoefficient_two :
    zFeedbackCoefficients stableUnitDelayParameters 2 = (Complex.I / 2) ^ 2 := by
  rw [zFeedbackCoefficients, stable_loopPolynomial_expansion]
  norm_num
  rw [div_pow, Complex.I_sq]
  norm_num

/-- The strict lag-two geometric criterion proves that `z = 1` belongs to the actual ROC. -/
lemma zRegression_stable_one_mem_zTransferROC :
    (1 : ℂ) ∈ zTransferROC stableUnitDelayParameters := by
  apply mem_zTransferROC_of_lagTwoGeometric stableUnitDelayParameters (Complex.I / 2) 1
    zRegression_stable_zFeedbackLags zRegression_stable_zFeedbackCoefficient_two
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
lemma zRegression_wellPosed :
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

/-- The raw-equation N5 elimination bridge gives the selected fixed value `-1`. -/
lemma zRegression_eliminationResponse :
    eliminationResponse (zRegressionParameters.at (1 : ℂ))
      zRegression_wellPosed = -1 := by
  exact (eliminationResponse_eq_transfer
    (zRegressionParameters.at (1 : ℂ)) zRegression_fixed_hasNonzeroDenominator).trans
      zRegression_fixed_transfer

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
      zRegression_wellPosed).toModeTransform
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
        zRegression_wellPosed = -1 ∧
      masonResponse (zRegressionParameters.at (1 : ℂ)) = -1 ∧
      ((netlist (zRegressionParameters.at (1 : ℂ))).packagedScattering
        zRegression_wellPosed).toModeTransform
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

/-- Primitive geometric transforms give the lag-two kernel value `4/3` at `z = I`.

This proof expands the kernel itself and does not use the DCDR transfer bridge.
-/
lemma zRegression_stable_lagTwoGeometricImpulse_transform_I :
    transform (lagTwoGeometricImpulse (Complex.I / 2)) Complex.I = 4 / 3 := by
  have hPositive : Complex.I ∈ ROC (geometricSeq (Complex.I / 2)) := by
    rw [ROC_geometricSeq (by norm_num)]
    norm_num
  have hNegative : Complex.I ∈ ROC (geometricSeq (-(Complex.I / 2))) := by
    rw [ROC_geometricSeq (by norm_num)]
    norm_num
  rw [lagTwoGeometricImpulse, transform_const_mul,
    transform_add hPositive.2 hNegative.2,
    transform_geometricSeq (by norm_num) (by norm_num),
    transform_geometricSeq (by norm_num) (by norm_num), Complex.inv_I]
  norm_num [Complex.I_mul_I]

/-- The independently solved nonzero-loop recurrence has transform `-(7/8) I` at `z = I`.

The proof uses only the explicit lag-two kernel, finite-delay transform, and primitive geometric
transform. It does not invoke `transform_causalImpulseResponse_eq_zTransfer` or any rational,
N5, or Mason agreement.
-/
lemma zRegression_stable_causalTransform_I :
    transform (causalOutput stableUnitDelayParameters unitImpulse) Complex.I =
      -(7 / 8) * Complex.I := by
  rw [causalOutput_eq_lagTwoGeometricImpulse stableUnitDelayParameters (Complex.I / 2)
      zRegression_stable_zFeedbackLags zRegression_stable_zFeedbackCoefficient_two]
  rw [transform_delayCombination
    (lagTwoGeometricImpulse_isCausal (Complex.I / 2))
    (summable_seriesTerm_lagTwoGeometricImpulse (by norm_num))]
  rw [delaySymbol_zFeedforwardCoefficients,
    stable_responseNumeratorPolynomial_expansion, Complex.inv_I,
    zRegression_stable_lagTwoGeometricImpulse_transform_I]
  norm_num [stableNumerator, Complex.I_mul_I]
  rw [show (-Complex.I) ^ 3 = Complex.I by
    norm_num [pow_succ, Complex.I_mul_I]]
  ring

/-- The fixed `q = -I` N5 solve gate, expanded from the stable denominator data. -/
lemma zRegression_stable_fixed_hasNonzeroDenominator_I :
    (stableUnitDelayParameters.at (-Complex.I)).HasNonzeroDenominator := by
  rw [Parameters.HasNonzeroDenominator,
    ← stableUnitDelayParameters.eval_denominatorPolynomial,
    stable_denominatorPolynomial_expansion]
  norm_num [stableDenominator, Complex.I_mul_I]

/-- The hand-expanded eight-node state at the nonzero-loop point `q = -I`. -/
def zRegressionStableFixedState : Node → ℂ :=
  ![1, (5 / 4) * Complex.I, 8 / 5, -(1 / 20) * Complex.I,
    -1 / 20, -(61 / 40) * Complex.I, -5 / 4, -(7 / 8) * Complex.I]

/-- All eight raw N5 channel equations hold for the displayed nonzero-loop state. -/
lemma zRegression_stable_fixed_forwardEquations_I :
    ForwardEquations (stableUnitDelayParameters.at (-Complex.I)) 1
      zRegressionStableFixedState := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [zRegressionStableFixedState, UnitDelayParameters.at,
      stableUnitDelayParameters, poleRegressionCoupler,
      Parameters.upperCoefficient, Parameters.lowerCoefficient,
      Parameters.feedbackCoefficient, DirectionalCoupler.crossCoefficient] <;>
    ring

/-- The complete raw N5 relation independently reads `-(7/8) I` at `q = -I`.

The proof lifts the displayed eight-equation state to all component channels and uses behavior
functionality only to identify that realization with the compiled response. It does not invoke
an elimination, rational-response, or Mason equality.
-/
lemma zRegression_stable_eliminationResponse_neg_I :
    eliminationResponse (stableUnitDelayParameters.at (-Complex.I))
        (isWellPosed_of_hasNonzeroDenominator
          (stableUnitDelayParameters.at (-Complex.I))
          zRegression_stable_fixed_hasNonzeroDenominator_I) =
      -(7 / 8) * Complex.I := by
  let p := stableUnitDelayParameters.at (-Complex.I)
  let hWellPosed := isWellPosed_of_hasNonzeroDenominator p
    zRegression_stable_fixed_hasNonzeroDenominator_I
  have hNode : Physlib.SignalFlowGraph.IsNodeSolution (signalFlowGraph p)
      (signalInput 1) zRegressionStableFixedState :=
    (isNodeSolution_iff_forwardEquations p 1 zRegressionStableFixedState).mpr
      zRegression_stable_fixed_forwardEquations_I
  rcases (isNodeSolution_iff_exists_netlistRealization p 1
      zRegressionStableFixedState).mp hNode with
    ⟨incident, outgoing, hScattering, hAssembly, hProjection⟩
  let output := (netlist p).outputReadout.toLinearMap outgoing
  have hMember : (inputAmplitude p 1, output) ∈ (netlist p).behavior := by
    apply ((netlist p).mem_behavior_iff_equations (inputAmplitude p 1) output).mpr
    exact ⟨incident, outgoing, hScattering, hAssembly, rfl⟩
  have hResponseMember : (inputAmplitude p 1, output) ∈
      ((netlist p).responseTransform hWellPosed).toBehavior := by
    rw [(netlist p).toBehavior_responseTransform hWellPosed]
    exact hMember
  have hOutput :=
    ModeTransform.mem_toBehavior_iff_toLinearMap.mp hResponseMember
  have hReadout := congrArg
    (fun value ⇒ value (Outgoing.mk (outputChannel p))) hProjection
  have hOutputValue : output (Outgoing.mk (outputChannel p)) =
      -(7 / 8) * Complex.I := by
    rw [outputReadout_apply_output]
    simpa [zRegressionStableFixedState, forwardState] using hReadout
  have hResponse := responseTransform_apply_inputAmplitude p hWellPosed 1
  calc
    eliminationResponse p hWellPosed =
        output (Outgoing.mk (outputChannel p)) := by
      rw [hOutput]
      simpa using hResponse.symm
    _ = -(7 / 8) * Complex.I := hOutputValue

/-- Nodes of the upper nonzero feedback cycle in the stable eleven-branch graph. -/
def zRegressionStableUpperLoopNodes : Finset Node := {1, 2, 5, 6}

/-- Nodes of the lower nonzero feedback cycle in the stable eleven-branch graph. -/
def zRegressionStableLowerLoopNodes : Finset Node := {1, 3, 4, 6}

/-- The upper cycle permutation `1 -> 2 -> 5 -> 6 -> 1`. -/
def zRegressionStableUpperLoopPermutation : Equiv.Perm Node :=
  [1, 2, 5, 6].formPerm

/-- The lower cycle permutation `1 -> 3 -> 4 -> 6 -> 1`. -/
def zRegressionStableLowerLoopPermutation : Equiv.Perm Node :=
  [1, 3, 4, 6].formPerm

/-- Edge labels selected by the stable upper feedback cycle. -/
def zRegressionStableUpperLoopEdge : Node → Edge := ![0, 8, 1, 0, 0, 6, 7, 0]

/-- Edge labels selected by the stable lower feedback cycle. -/
def zRegressionStableLowerLoopEdge : Node → Edge := ![0, 9, 0, 4, 10, 0, 7, 0]

/-- The dependent upper-cycle edge selection. -/
def zRegressionStableUpperLoopChoice :
    ∀ node ∈ zRegressionStableUpperLoopNodes, Edge :=
  fun node _ ⇒ zRegressionStableUpperLoopEdge node

/-- The dependent lower-cycle edge selection. -/
def zRegressionStableLowerLoopChoice :
    ∀ node ∈ zRegressionStableLowerLoopNodes, Edge :=
  fun node _ ⇒ zRegressionStableLowerLoopEdge node

/-- A selected loop edge records its source and permutation target. -/
private lemma zRegression_stable_selectedEndpoints
    {nodes : Finset Node} {permutation : Equiv.Perm Node}
    {choice : ∀ node ∈ nodes, Edge}
    (hChoice : choice ∈ edgeChoices
      (signalMultigraph (stableUnitDelayParameters.at (-Complex.I))) nodes permutation)
    (node : Node) (hNode : node ∈ nodes) :
    edgeSource (choice node hNode) = node ∧
      edgeTarget (choice node hNode) = permutation node := by
  have hSelected := Finset.mem_pi.mp hChoice node hNode
  simpa [signalMultigraph] using hSelected

/-- A loop-family permutation preserves its declared node set. -/
private lemma zRegression_stable_permutation_mem
    {nodes : Finset Node} {permutation : Equiv.Perm Node}
    (hPermutation : permutation ∈ loopFamilies nodes)
    (node : Node) (hNode : node ∈ nodes) : permutation node ∈ nodes := by
  by_cases hSupport : node ∈ permutation.support
  · exact (mem_loopFamilies.mp hPermutation)
      (Equiv.Perm.apply_mem_support.mpr hSupport)
  · rw [Equiv.Perm.notMem_support.mp hSupport]
    exact hNode

/-- The two retained branches leaving feedback-input node one. -/
private lemma zRegression_stable_edge_from_one (edge : Edge)
    (hSource : edgeSource edge = 1) : edge = 8 ∨ edge = 9 := by
  fin_cases edge <;> simp [edgeSource] at hSource ⊢

/-- The unique retained branch leaving upper launch node two. -/
private lemma zRegression_stable_edge_from_two (edge : Edge)
    (hSource : edgeSource edge = 2) : edge = 1 := by
  fin_cases edge <;> simp [edgeSource] at hSource ⊢

/-- The unique retained branch leaving lower launch node three. -/
private lemma zRegression_stable_edge_from_three (edge : Edge)
    (hSource : edgeSource edge = 3) : edge = 4 := by
  fin_cases edge <;> simp [edgeSource] at hSource ⊢

/-- The two retained branches leaving lower propagation node four. -/
private lemma zRegression_stable_edge_from_four (edge : Edge)
    (hSource : edgeSource edge = 4) : edge = 5 ∨ edge = 10 := by
  fin_cases edge <;> simp [edgeSource] at hSource ⊢

/-- The two retained branches leaving upper propagation node five. -/
private lemma zRegression_stable_edge_from_five (edge : Edge)
    (hSource : edgeSource edge = 5) : edge = 2 ∨ edge = 6 := by
  fin_cases edge <;> simp [edgeSource] at hSource ⊢

/-- The unique retained feedback branch leaves node six. -/
private lemma zRegression_stable_edge_from_six (edge : Edge)
    (hSource : edgeSource edge = 6) : edge = 7 := by
  fin_cases edge <;> simp [edgeSource] at hSource ⊢

/-- No retained branch leaves external output node seven. -/
private lemma zRegression_stable_noEdgeSource_seven (edge : Edge) :
    edgeSource edge ≠ 7 := by
  fin_cases edge <;> simp [edgeSource]

/-- Every nonempty loop-family refinement is one of the two displayed touching cycles. -/
private lemma zRegression_stable_loopFamily_cases
    {nodes : Finset Node} {permutation : Equiv.Perm Node}
    {choice : ∀ node ∈ nodes, Edge} (hNodes : nodes.Nonempty)
    (hPermutation : permutation ∈ loopFamilies nodes)
    (hChoice : choice ∈ edgeChoices
      (signalMultigraph (stableUnitDelayParameters.at (-Complex.I))) nodes permutation) :
    (nodes = zRegressionStableUpperLoopNodes ∧
        permutation = zRegressionStableUpperLoopPermutation) ∨
      (nodes = zRegressionStableLowerLoopNodes ∧
        permutation = zRegressionStableLowerLoopPermutation) := by
  have hChoiceSingular : choice ∈ edgeChoices
      (signalMultigraph responseRegressionSingularParameters) nodes permutation := by
    simpa [signalMultigraph] using hChoice
  obtain ⟨feedbackNode, hFeedbackNode, hFeedbackEdge⟩ :=
    responseRegression_singularEdgeChoice_contains_feedbackEdge hNodes hPermutation
      hChoiceSingular
  have hFeedbackEndpoints :=
    zRegression_stable_selectedEndpoints hChoice feedbackNode hFeedbackNode
  have hFeedbackNodeEq : feedbackNode = 6 := by
    simpa [hFeedbackEdge, edgeSource] using hFeedbackEndpoints.1.symm
  subst feedbackNode
  have h6 : (6 : Node) ∈ nodes := hFeedbackNode
  have hPermutation6 : permutation 6 = 1 := by
    simpa [hFeedbackEdge, edgeTarget] using hFeedbackEndpoints.2.symm
  have h1 : (1 : Node) ∈ nodes := by
    rw [← hPermutation6]
    exact zRegression_stable_permutation_mem hPermutation 6 h6
  have hEndpoints1 := zRegression_stable_selectedEndpoints hChoice 1 h1
  rcases zRegression_stable_edge_from_one _ hEndpoints1.1 with hUpper | hLower
  · have hPermutation1 : permutation 1 = 2 := by
      simpa [hUpper, edgeTarget] using hEndpoints1.2.symm
    have h2 : (2 : Node) ∈ nodes := by
      rw [← hPermutation1]
      exact zRegression_stable_permutation_mem hPermutation 1 h1
    have hEndpoints2 := zRegression_stable_selectedEndpoints hChoice 2 h2
    have hEdge2 := zRegression_stable_edge_from_two _ hEndpoints2.1
    have hPermutation2 : permutation 2 = 5 := by
      simpa [hEdge2, edgeTarget] using hEndpoints2.2.symm
    have h5 : (5 : Node) ∈ nodes := by
      rw [← hPermutation2]
      exact zRegression_stable_permutation_mem hPermutation 2 h2
    have hEndpoints5 := zRegression_stable_selectedEndpoints hChoice 5 h5
    have hEdge5 : choice 5 h5 = 6 := by
      rcases zRegression_stable_edge_from_five _ hEndpoints5.1 with hOutput | hReturn
      · have hPermutation5 : permutation 5 = 7 := by
          simpa [hOutput, edgeTarget] using hEndpoints5.2.symm
        have h7 : (7 : Node) ∈ nodes := by
          rw [← hPermutation5]
          exact zRegression_stable_permutation_mem hPermutation 5 h5
        exact absurd (zRegression_stable_selectedEndpoints hChoice 7 h7).1
          (zRegression_stable_noEdgeSource_seven _)
      · exact hReturn
    have hPermutation5 : permutation 5 = 6 := by
      simpa [hEdge5, edgeTarget] using hEndpoints5.2.symm
    have hMainSubset : zRegressionStableUpperLoopNodes ⊆ nodes := by
      intro node hNode
      simp only [zRegressionStableUpperLoopNodes, Finset.mem_insert,
        Finset.mem_singleton] at hNode
      rcases hNode with rfl | rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact h5
      · exact h6
    have hNoExtra : nodes \ zRegressionStableUpperLoopNodes = ∅ := by
      by_contra hExtra
      have hExtraNonempty : (nodes \ zRegressionStableUpperLoopNodes).Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr hExtra
      obtain ⟨node, hNode, hMax⟩ := Finset.exists_max_image
        (nodes \ zRegressionStableUpperLoopNodes) responseRegressionNodeRank hExtraNonempty
      have hNodeParts := Finset.mem_sdiff.mp hNode
      have hPermutationNodeNodes :=
        zRegression_stable_permutation_mem hPermutation node hNodeParts.1
      have hPermutationNodeNotMain :
          permutation node ∉ zRegressionStableUpperLoopNodes := by
        intro hTarget
        simp only [zRegressionStableUpperLoopNodes, Finset.mem_insert,
          Finset.mem_singleton] at hTarget
        rcases hTarget with hTarget | hTarget | hTarget | hTarget
        · exact hNodeParts.2 (by
            have := permutation.injective (hTarget.trans hPermutation6.symm)
            simp [this, zRegressionStableUpperLoopNodes])
        · exact hNodeParts.2 (by
            have := permutation.injective (hTarget.trans hPermutation1.symm)
            simp [this, zRegressionStableUpperLoopNodes])
        · exact hNodeParts.2 (by
            have := permutation.injective (hTarget.trans hPermutation2.symm)
            simp [this, zRegressionStableUpperLoopNodes])
        · exact hNodeParts.2 (by
            have := permutation.injective (hTarget.trans hPermutation5.symm)
            simp [this, zRegressionStableUpperLoopNodes])
      have hPermutationNode : permutation node ∈
          nodes \ zRegressionStableUpperLoopNodes :=
        Finset.mem_sdiff.mpr ⟨hPermutationNodeNodes, hPermutationNodeNotMain⟩
      have hEndpoints := zRegression_stable_selectedEndpoints hChoice node hNodeParts.1
      have hNotFeedback : choice node hNodeParts.1 ≠ 7 := by
        intro hEdge
        have hNodeEq : node = 6 := by
          simpa [hEdge, edgeSource] using hEndpoints.1.symm
        exact hNodeParts.2 (by simp [hNodeEq, zRegressionStableUpperLoopNodes])
      have hRank := responseRegressionNodeRank_lt (choice node hNodeParts.1) hNotFeedback
      rw [hEndpoints.1, hEndpoints.2] at hRank
      exact (Nat.not_lt_of_ge (hMax (permutation node) hPermutationNode)) hRank
    have hNodesEqual : nodes = zRegressionStableUpperLoopNodes := by
      exact Finset.Subset.antisymm
        (Finset.sdiff_eq_empty_iff_subset.mp hNoExtra) hMainSubset
    have hFixedOutside (node : Node) (hNode : node ∉ zRegressionStableUpperLoopNodes) :
        permutation node = node := by
      apply Equiv.Perm.notMem_support.mp
      intro hSupport
      apply hNode
      rw [← hNodesEqual]
      exact (mem_loopFamilies.mp hPermutation) hSupport
    refine Or.inl ⟨hNodesEqual, Equiv.ext ?_⟩
    intro node
    fin_cases node
    · simpa [zRegressionStableUpperLoopPermutation] using hFixedOutside 0 (by decide)
    · simpa [zRegressionStableUpperLoopPermutation, Equiv.swap_apply_def] using
        hPermutation1
    · simpa [zRegressionStableUpperLoopPermutation, Equiv.swap_apply_def] using
        hPermutation2
    · simpa [zRegressionStableUpperLoopPermutation] using hFixedOutside 3 (by decide)
    · simpa [zRegressionStableUpperLoopPermutation] using hFixedOutside 4 (by decide)
    · simpa [zRegressionStableUpperLoopPermutation, Equiv.swap_apply_def] using
        hPermutation5
    · simpa [zRegressionStableUpperLoopPermutation, Equiv.swap_apply_def] using
        hPermutation6
    · simpa [zRegressionStableUpperLoopPermutation] using hFixedOutside 7 (by decide)
  · have hPermutation1 : permutation 1 = 3 := by
      simpa [hLower, edgeTarget] using hEndpoints1.2.symm
    have h3 : (3 : Node) ∈ nodes := by
      rw [← hPermutation1]
      exact zRegression_stable_permutation_mem hPermutation 1 h1
    have hEndpoints3 := zRegression_stable_selectedEndpoints hChoice 3 h3
    have hEdge3 := zRegression_stable_edge_from_three _ hEndpoints3.1
    have hPermutation3 : permutation 3 = 4 := by
      simpa [hEdge3, edgeTarget] using hEndpoints3.2.symm
    have h4 : (4 : Node) ∈ nodes := by
      rw [← hPermutation3]
      exact zRegression_stable_permutation_mem hPermutation 3 h3
    have hEndpoints4 := zRegression_stable_selectedEndpoints hChoice 4 h4
    have hEdge4 : choice 4 h4 = 10 := by
      rcases zRegression_stable_edge_from_four _ hEndpoints4.1 with hOutput | hReturn
      · have hPermutation4 : permutation 4 = 7 := by
          simpa [hOutput, edgeTarget] using hEndpoints4.2.symm
        have h7 : (7 : Node) ∈ nodes := by
          rw [← hPermutation4]
          exact zRegression_stable_permutation_mem hPermutation 4 h4
        exact absurd (zRegression_stable_selectedEndpoints hChoice 7 h7).1
          (zRegression_stable_noEdgeSource_seven _)
      · exact hReturn
    have hPermutation4 : permutation 4 = 6 := by
      simpa [hEdge4, edgeTarget] using hEndpoints4.2.symm
    have hMainSubset : zRegressionStableLowerLoopNodes ⊆ nodes := by
      intro node hNode
      simp only [zRegressionStableLowerLoopNodes, Finset.mem_insert,
        Finset.mem_singleton] at hNode
      rcases hNode with rfl | rfl | rfl | rfl
      · exact h1
      · exact h3
      · exact h4
      · exact h6
    have hNoExtra : nodes \ zRegressionStableLowerLoopNodes = ∅ := by
      by_contra hExtra
      have hExtraNonempty : (nodes \ zRegressionStableLowerLoopNodes).Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr hExtra
      obtain ⟨node, hNode, hMax⟩ := Finset.exists_max_image
        (nodes \ zRegressionStableLowerLoopNodes) responseRegressionNodeRank hExtraNonempty
      have hNodeParts := Finset.mem_sdiff.mp hNode
      have hPermutationNodeNodes :=
        zRegression_stable_permutation_mem hPermutation node hNodeParts.1
      have hPermutationNodeNotMain :
          permutation node ∉ zRegressionStableLowerLoopNodes := by
        intro hTarget
        simp only [zRegressionStableLowerLoopNodes, Finset.mem_insert,
          Finset.mem_singleton] at hTarget
        rcases hTarget with hTarget | hTarget | hTarget | hTarget
        · exact hNodeParts.2 (by
            have := permutation.injective (hTarget.trans hPermutation6.symm)
            simp [this, zRegressionStableLowerLoopNodes])
        · exact hNodeParts.2 (by
            have := permutation.injective (hTarget.trans hPermutation1.symm)
            simp [this, zRegressionStableLowerLoopNodes])
        · exact hNodeParts.2 (by
            have := permutation.injective (hTarget.trans hPermutation3.symm)
            simp [this, zRegressionStableLowerLoopNodes])
        · exact hNodeParts.2 (by
            have := permutation.injective (hTarget.trans hPermutation4.symm)
            simp [this, zRegressionStableLowerLoopNodes])
      have hPermutationNode : permutation node ∈
          nodes \ zRegressionStableLowerLoopNodes :=
        Finset.mem_sdiff.mpr ⟨hPermutationNodeNodes, hPermutationNodeNotMain⟩
      have hEndpoints := zRegression_stable_selectedEndpoints hChoice node hNodeParts.1
      have hNotFeedback : choice node hNodeParts.1 ≠ 7 := by
        intro hEdge
        have hNodeEq : node = 6 := by
          simpa [hEdge, edgeSource] using hEndpoints.1.symm
        exact hNodeParts.2 (by simp [hNodeEq, zRegressionStableLowerLoopNodes])
      have hRank := responseRegressionNodeRank_lt (choice node hNodeParts.1) hNotFeedback
      rw [hEndpoints.1, hEndpoints.2] at hRank
      exact (Nat.not_lt_of_ge (hMax (permutation node) hPermutationNode)) hRank
    have hNodesEqual : nodes = zRegressionStableLowerLoopNodes := by
      exact Finset.Subset.antisymm
        (Finset.sdiff_eq_empty_iff_subset.mp hNoExtra) hMainSubset
    have hFixedOutside (node : Node) (hNode : node ∉ zRegressionStableLowerLoopNodes) :
        permutation node = node := by
      apply Equiv.Perm.notMem_support.mp
      intro hSupport
      apply hNode
      rw [← hNodesEqual]
      exact (mem_loopFamilies.mp hPermutation) hSupport
    refine Or.inr ⟨hNodesEqual, Equiv.ext ?_⟩
    intro node
    fin_cases node
    · simpa [zRegressionStableLowerLoopPermutation] using hFixedOutside 0 (by decide)
    · simpa [zRegressionStableLowerLoopPermutation, Equiv.swap_apply_def] using
        hPermutation1
    · simpa [zRegressionStableLowerLoopPermutation] using hFixedOutside 2 (by decide)
    · simpa [zRegressionStableLowerLoopPermutation, Equiv.swap_apply_def] using
        hPermutation3
    · simpa [zRegressionStableLowerLoopPermutation, Equiv.swap_apply_def] using
        hPermutation4
    · simpa [zRegressionStableLowerLoopPermutation] using hFixedOutside 5 (by decide)
    · simpa [zRegressionStableLowerLoopPermutation, Equiv.swap_apply_def] using
        hPermutation6
    · simpa [zRegressionStableLowerLoopPermutation] using hFixedOutside 7 (by decide)

/-- The displayed upper permutation is a loop family on its four nodes. -/
lemma zRegression_stable_upperLoopPermutation_mem :
    zRegressionStableUpperLoopPermutation ∈
      loopFamilies zRegressionStableUpperLoopNodes := by
  apply mem_loopFamilies.mpr
  simpa [zRegressionStableUpperLoopPermutation, zRegressionStableUpperLoopNodes] using
    List.support_formPerm_le ([1, 2, 5, 6] : List Node)

/-- The displayed lower permutation is a loop family on its four nodes. -/
lemma zRegression_stable_lowerLoopPermutation_mem :
    zRegressionStableLowerLoopPermutation ∈
      loopFamilies zRegressionStableLowerLoopNodes := by
  apply mem_loopFamilies.mpr
  simpa [zRegressionStableLowerLoopPermutation, zRegressionStableLowerLoopNodes] using
    List.support_formPerm_le ([1, 3, 4, 6] : List Node)

/-- The upper loop has exactly the edge choice `8, 1, 6, 7`. -/
lemma zRegression_stable_upperLoopChoices :
    edgeChoices (signalMultigraph (stableUnitDelayParameters.at (-Complex.I)))
        zRegressionStableUpperLoopNodes zRegressionStableUpperLoopPermutation =
      {zRegressionStableUpperLoopChoice} := by
  decide

/-- The lower loop has exactly the edge choice `9, 4, 10, 7`. -/
lemma zRegression_stable_lowerLoopChoices :
    edgeChoices (signalMultigraph (stableUnitDelayParameters.at (-Complex.I)))
        zRegressionStableLowerLoopNodes zRegressionStableLowerLoopPermutation =
      {zRegressionStableLowerLoopChoice} := by
  decide

/-- The upper family contains one cycle. -/
lemma zRegression_stable_upperLoopCount :
    loopCount zRegressionStableUpperLoopNodes
      zRegressionStableUpperLoopPermutation = 1 := by
  decide

/-- The lower family contains one cycle. -/
lemma zRegression_stable_lowerLoopCount :
    loopCount zRegressionStableLowerLoopNodes
      zRegressionStableLowerLoopPermutation = 1 := by
  decide

/-- Direct multiplication gives upper feedback-loop gain `61/100`. -/
lemma zRegression_stable_upperLoopFamilyGain :
    edgeFamilyGain (signalMultigraph (stableUnitDelayParameters.at (-Complex.I)))
        zRegressionStableUpperLoopNodes zRegressionStableUpperLoopChoice = 61 / 100 := by
  rw [edgeFamilyGain]
  simp only [zRegressionStableUpperLoopChoice]
  rw [Finset.prod_attach]
  simp [zRegressionStableUpperLoopNodes, Finset.prod_insert,
    zRegressionStableUpperLoopEdge, signalMultigraph, edgeGain,
    UnitDelayParameters.at, stableUnitDelayParameters, poleRegressionCoupler,
    Parameters.upperCoefficient, Parameters.feedbackCoefficient,
    DirectionalCoupler.crossCoefficient]
  norm_num [Complex.I_mul_I]

/-- Direct multiplication gives lower feedback-loop gain `-9/25`. -/
lemma zRegression_stable_lowerLoopFamilyGain :
    edgeFamilyGain (signalMultigraph (stableUnitDelayParameters.at (-Complex.I)))
        zRegressionStableLowerLoopNodes zRegressionStableLowerLoopChoice = -9 / 25 := by
  rw [edgeFamilyGain]
  simp only [zRegressionStableLowerLoopChoice]
  rw [Finset.prod_attach]
  simp [zRegressionStableLowerLoopNodes, Finset.prod_insert,
    zRegressionStableLowerLoopEdge, signalMultigraph, edgeGain,
    UnitDelayParameters.at, stableUnitDelayParameters, poleRegressionCoupler,
    Parameters.lowerCoefficient, Parameters.feedbackCoefficient,
    DirectionalCoupler.crossCoefficient]
  norm_num [Complex.I_mul_I]

/-- Every other nonempty node set has zero total loop-family contribution. -/
private lemma zRegression_stable_nonLoopFamilySum_eq_zero
    {nodes : Finset Node} (hNodes : nodes.Nonempty)
    (hNotUpper : nodes ≠ zRegressionStableUpperLoopNodes)
    (hNotLower : nodes ≠ zRegressionStableLowerLoopNodes) :
    (∑ permutation ∈ loopFamilies nodes,
      ∑ choice ∈ edgeChoices
          (signalMultigraph (stableUnitDelayParameters.at (-Complex.I))) nodes permutation,
        (-1 : ℂ) ^ loopCount nodes permutation *
          edgeFamilyGain
            (signalMultigraph (stableUnitDelayParameters.at (-Complex.I))) nodes choice) = 0 := by
  apply Finset.sum_eq_zero
  intro permutation hPermutation
  apply Finset.sum_eq_zero
  intro choice hChoice
  rcases zRegression_stable_loopFamily_cases hNodes hPermutation hChoice with
    hUpper | hLower
  · exact (hNotUpper hUpper.1).elim
  · exact (hNotLower hLower.1).elim

/-- The upper node set contributes the signed gain `-61/100`. -/
lemma zRegression_stable_upperFamilySum :
    (∑ permutation ∈ loopFamilies zRegressionStableUpperLoopNodes,
      ∑ choice ∈ edgeChoices
          (signalMultigraph (stableUnitDelayParameters.at (-Complex.I)))
            zRegressionStableUpperLoopNodes permutation,
        (-1 : ℂ) ^ loopCount zRegressionStableUpperLoopNodes permutation *
          edgeFamilyGain
            (signalMultigraph (stableUnitDelayParameters.at (-Complex.I)))
              zRegressionStableUpperLoopNodes choice) = -61 / 100 := by
  calc
    _ = ∑ choice ∈ edgeChoices
          (signalMultigraph (stableUnitDelayParameters.at (-Complex.I)))
            zRegressionStableUpperLoopNodes zRegressionStableUpperLoopPermutation,
        (-1 : ℂ) ^ loopCount zRegressionStableUpperLoopNodes
            zRegressionStableUpperLoopPermutation *
          edgeFamilyGain
            (signalMultigraph (stableUnitDelayParameters.at (-Complex.I)))
              zRegressionStableUpperLoopNodes choice := by
      apply Finset.sum_eq_single zRegressionStableUpperLoopPermutation
      · intro permutation hPermutation hNotPermutation
        apply Finset.sum_eq_zero
        intro choice hChoice
        rcases zRegression_stable_loopFamily_cases (by decide) hPermutation hChoice with
          hUpper | hLower
        · exact (hNotPermutation hUpper.2).elim
        · exact (by
            have : zRegressionStableUpperLoopNodes ≠
                zRegressionStableLowerLoopNodes := by decide
            exact (this hLower.1).elim)
      · intro hMissing
        exact (hMissing zRegression_stable_upperLoopPermutation_mem).elim
    _ = -61 / 100 := by
      rw [zRegression_stable_upperLoopChoices]
      simp [zRegression_stable_upperLoopCount,
        zRegression_stable_upperLoopFamilyGain]

/-- The lower node set contributes the signed gain `9/25`. -/
lemma zRegression_stable_lowerFamilySum :
    (∑ permutation ∈ loopFamilies zRegressionStableLowerLoopNodes,
      ∑ choice ∈ edgeChoices
          (signalMultigraph (stableUnitDelayParameters.at (-Complex.I)))
            zRegressionStableLowerLoopNodes permutation,
        (-1 : ℂ) ^ loopCount zRegressionStableLowerLoopNodes permutation *
          edgeFamilyGain
            (signalMultigraph (stableUnitDelayParameters.at (-Complex.I)))
              zRegressionStableLowerLoopNodes choice) = 9 / 25 := by
  calc
    _ = ∑ choice ∈ edgeChoices
          (signalMultigraph (stableUnitDelayParameters.at (-Complex.I)))
            zRegressionStableLowerLoopNodes zRegressionStableLowerLoopPermutation,
        (-1 : ℂ) ^ loopCount zRegressionStableLowerLoopNodes
            zRegressionStableLowerLoopPermutation *
          edgeFamilyGain
            (signalMultigraph (stableUnitDelayParameters.at (-Complex.I)))
              zRegressionStableLowerLoopNodes choice := by
      apply Finset.sum_eq_single zRegressionStableLowerLoopPermutation
      · intro permutation hPermutation hNotPermutation
        apply Finset.sum_eq_zero
        intro choice hChoice
        rcases zRegression_stable_loopFamily_cases (by decide) hPermutation hChoice with
          hUpper | hLower
        · exact (by
            have : zRegressionStableLowerLoopNodes ≠
                zRegressionStableUpperLoopNodes := by decide
            exact (this hUpper.1).elim)
        · exact (hNotPermutation hLower.2).elim
      · intro hMissing
        exact (hMissing zRegression_stable_lowerLoopPermutation_mem).elim
    _ = 9 / 25 := by
      rw [zRegression_stable_lowerLoopChoices]
      simp [zRegression_stable_lowerLoopCount,
        zRegression_stable_lowerLoopFamilyGain]

/-- Direct two-cycle enumeration gives every induced edge determinant. -/
lemma zRegression_stable_edgeGraphDetOn (nodes : Finset Node) :
    edgeGraphDetOn
        (signalMultigraph (stableUnitDelayParameters.at (-Complex.I))) nodes =
      1 - (if zRegressionStableUpperLoopNodes ⊆ nodes then 61 / 100 else 0) +
        (if zRegressionStableLowerLoopNodes ⊆ nodes then 9 / 25 else 0) := by
  let contribution : Finset Node → ℂ := fun selected ⇒
    ∑ permutation ∈ loopFamilies selected,
      ∑ choice ∈ edgeChoices
          (signalMultigraph (stableUnitDelayParameters.at (-Complex.I)))
            selected permutation,
        (-1 : ℂ) ^ loopCount selected permutation *
          edgeFamilyGain
            (signalMultigraph (stableUnitDelayParameters.at (-Complex.I))) selected choice
  rw [edgeGraphDetOn]
  change (∑ selected ∈ nodes.powerset, contribution selected) = _
  calc
    (∑ selected ∈ nodes.powerset, contribution selected) =
        ∑ selected ∈ nodes.powerset,
          if selected = ∅ then 1
          else if selected = zRegressionStableUpperLoopNodes then -61 / 100
          else if selected = zRegressionStableLowerLoopNodes then 9 / 25
          else 0 := by
      apply Finset.sum_congr rfl
      intro selected hSelected
      by_cases hEmpty : selected = ∅
      · subst selected
        simp [contribution, loopFamilies_empty, edgeChoices,
          edgeFamilyGain, loopCount]
      · rw [if_neg hEmpty]
        by_cases hUpper : selected = zRegressionStableUpperLoopNodes
        · subst selected
          rw [if_pos rfl]
          exact zRegression_stable_upperFamilySum
        · rw [if_neg hUpper]
          by_cases hLower : selected = zRegressionStableLowerLoopNodes
          · subst selected
            rw [if_pos rfl]
            exact zRegression_stable_lowerFamilySum
          · rw [if_neg hLower]
            exact zRegression_stable_nonLoopFamilySum_eq_zero
              (Finset.nonempty_iff_ne_empty.mpr hEmpty) hUpper hLower
    _ = 1 - (if zRegressionStableUpperLoopNodes ⊆ nodes then 61 / 100 else 0) +
          (if zRegressionStableLowerLoopNodes ⊆ nodes then 9 / 25 else 0) := by
      simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, add_zero,
        Finset.mem_powerset]
      by_cases hUpper : zRegressionStableUpperLoopNodes ⊆ nodes <;>
        by_cases hLower : zRegressionStableLowerLoopNodes ⊆ nodes <;>
        simp [hUpper, hLower]

/-- Supported stable paths use the same four node lists as the topology audit. -/
def zRegressionStableSupportedForwardPaths : Finset (List Node) :=
  (forwardPaths 0 7).filter fun path ⇒
    (refiningEdgeLists
      (signalMultigraph (stableUnitDelayParameters.at (-Complex.I))) path).Nonempty

/-- Exactly four source-to-output paths have eleven-branch refinements. -/
lemma zRegression_stable_supportedForwardPaths :
    zRegressionStableSupportedForwardPaths =
      { [0, 2, 5, 7], [0, 3, 4, 7],
        [0, 2, 5, 6, 1, 3, 4, 7], [0, 3, 4, 6, 1, 2, 5, 7] } := by
  change responseRegressionSupportedForwardPaths = _
  exact responseRegression_supportedForwardPaths

/-- The upper direct path refines to edges zero, one, and two. -/
lemma zRegression_stable_refiningEdges_upper :
    refiningEdgeLists
        (signalMultigraph (stableUnitDelayParameters.at (-Complex.I))) [0, 2, 5, 7] =
      {[0, 1, 2]} := by
  decide

/-- The lower direct path refines to edges three, four, and five. -/
lemma zRegression_stable_refiningEdges_lower :
    refiningEdgeLists
        (signalMultigraph (stableUnitDelayParameters.at (-Complex.I))) [0, 3, 4, 7] =
      {[3, 4, 5]} := by
  decide

/-- The upper-launch feedback-return path has one seven-edge refinement. -/
lemma zRegression_stable_refiningEdges_upperReturn :
    refiningEdgeLists (signalMultigraph (stableUnitDelayParameters.at (-Complex.I)))
        [0, 2, 5, 6, 1, 3, 4, 7] = {[0, 1, 6, 7, 9, 4, 5]} := by
  decide

/-- The lower-launch feedback-return path has one seven-edge refinement. -/
lemma zRegression_stable_refiningEdges_lowerReturn :
    refiningEdgeLists (signalMultigraph (stableUnitDelayParameters.at (-Complex.I)))
        [0, 3, 4, 6, 1, 2, 5, 7] = {[3, 4, 10, 7, 8, 1, 2]} := by
  decide

/-- Direct multiplication gives upper direct-path gain `-(549/1600) I`. -/
lemma zRegression_stable_edgeListGain_upper :
    edgeListGain (signalMultigraph (stableUnitDelayParameters.at (-Complex.I)))
        [0, 1, 2] = -(549 / 1600) * Complex.I := by
  simp [edgeListGain, signalMultigraph, edgeGain, UnitDelayParameters.at,
    stableUnitDelayParameters, poleRegressionCoupler, Parameters.upperCoefficient,
    DirectionalCoupler.crossCoefficient]
  ring

/-- Direct multiplication gives lower direct-path gain `(16/25) I`. -/
lemma zRegression_stable_edgeListGain_lower :
    edgeListGain (signalMultigraph (stableUnitDelayParameters.at (-Complex.I)))
        [3, 4, 5] = (16 / 25) * Complex.I := by
  simp [edgeListGain, signalMultigraph, edgeGain, UnitDelayParameters.at,
    stableUnitDelayParameters, poleRegressionCoupler, Parameters.lowerCoefficient,
    DirectionalCoupler.crossCoefficient]
  norm_num [Complex.I_mul_I]
  ring

/-- The first feedback-return path has gain `-(549/2500) I`. -/
lemma zRegression_stable_edgeListGain_upperReturn :
    edgeListGain (signalMultigraph (stableUnitDelayParameters.at (-Complex.I)))
        [0, 1, 6, 7, 9, 4, 5] = -(549 / 2500) * Complex.I := by
  simp [edgeListGain, signalMultigraph, edgeGain, UnitDelayParameters.at,
    stableUnitDelayParameters, poleRegressionCoupler, Parameters.upperCoefficient,
    Parameters.lowerCoefficient, Parameters.feedbackCoefficient,
    DirectionalCoupler.crossCoefficient]
  norm_num [Complex.I_mul_I]
  ring

/-- The second feedback-return path also has gain `-(549/2500) I`. -/
lemma zRegression_stable_edgeListGain_lowerReturn :
    edgeListGain (signalMultigraph (stableUnitDelayParameters.at (-Complex.I)))
        [3, 4, 10, 7, 8, 1, 2] = -(549 / 2500) * Complex.I := by
  simp [edgeListGain, signalMultigraph, edgeGain, UnitDelayParameters.at,
    stableUnitDelayParameters, poleRegressionCoupler, Parameters.upperCoefficient,
    Parameters.lowerCoefficient, Parameters.feedbackCoefficient,
    DirectionalCoupler.crossCoefficient]
  norm_num [Complex.I_mul_I]
  ring

/-- Removing the upper direct path leaves only the lower-loop cofactor `34/25`. -/
lemma zRegression_stable_upperPathCofactor :
    edgeGraphDetOn (signalMultigraph (stableUnitDelayParameters.at (-Complex.I)))
        (Finset.univ \ [0, 2, 5, 7].toFinset) = 34 / 25 := by
  rw [zRegression_stable_edgeGraphDetOn]
  norm_num [zRegressionStableUpperLoopNodes, zRegressionStableLowerLoopNodes]

/-- Removing the lower direct path leaves only the upper-loop cofactor `39/100`. -/
lemma zRegression_stable_lowerPathCofactor :
    edgeGraphDetOn (signalMultigraph (stableUnitDelayParameters.at (-Complex.I)))
        (Finset.univ \ [0, 3, 4, 7].toFinset) = 39 / 100 := by
  rw [zRegression_stable_edgeGraphDetOn]
  norm_num [zRegressionStableUpperLoopNodes, zRegressionStableLowerLoopNodes]

/-- Each feedback-return path visits every node, so its cofactor is one. -/
lemma zRegression_stable_upperReturnPathCofactor :
    edgeGraphDetOn (signalMultigraph (stableUnitDelayParameters.at (-Complex.I)))
        (Finset.univ \ [0, 2, 5, 6, 1, 3, 4, 7].toFinset) = 1 := by
  rw [zRegression_stable_edgeGraphDetOn]
  norm_num [zRegressionStableUpperLoopNodes, zRegressionStableLowerLoopNodes]

/-- The other feedback-return path also visits every node and has unit cofactor. -/
lemma zRegression_stable_lowerReturnPathCofactor :
    edgeGraphDetOn (signalMultigraph (stableUnitDelayParameters.at (-Complex.I)))
        (Finset.univ \ [0, 3, 4, 6, 1, 2, 5, 7].toFinset) = 1 := by
  rw [zRegression_stable_edgeGraphDetOn]
  norm_num [zRegressionStableUpperLoopNodes, zRegressionStableLowerLoopNodes]

/-- Unsupported paths contribute an empty edge-refinement sum at the stable fixture. -/
lemma zRegression_stable_edgeMasonNumerator_eq_supportedSum :
    edgeMasonNumerator
        (signalMultigraph (stableUnitDelayParameters.at (-Complex.I))) 0 7 =
      ∑ path ∈ zRegressionStableSupportedForwardPaths,
        ∑ edgeList ∈ refiningEdgeLists
            (signalMultigraph (stableUnitDelayParameters.at (-Complex.I))) path,
          edgeListGain
              (signalMultigraph (stableUnitDelayParameters.at (-Complex.I))) edgeList *
            edgeGraphDetOn
              (signalMultigraph (stableUnitDelayParameters.at (-Complex.I)))
                (Finset.univ \ path.toFinset) := by
  rw [edgeMasonNumerator]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro path hPath hUnsupported
  have hEmpty : refiningEdgeLists
      (signalMultigraph (stableUnitDelayParameters.at (-Complex.I))) path = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro hNonempty
    exact hUnsupported (Finset.mem_filter.mpr ⟨hPath, hNonempty⟩)
  simp [hEmpty]

/-- The complete eleven-branch numerator is `-(21/32) I`. -/
lemma zRegression_stable_edgeMasonNumerator :
    edgeMasonNumerator
        (signalMultigraph (stableUnitDelayParameters.at (-Complex.I))) 0 7 =
      -(21 / 32) * Complex.I := by
  rw [zRegression_stable_edgeMasonNumerator_eq_supportedSum,
    zRegression_stable_supportedForwardPaths]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [zRegression_stable_refiningEdges_upper, zRegression_stable_refiningEdges_lower,
    zRegression_stable_refiningEdges_upperReturn,
    zRegression_stable_refiningEdges_lowerReturn]
  simp only [Finset.sum_singleton]
  rw [zRegression_stable_edgeListGain_upper, zRegression_stable_edgeListGain_lower,
    zRegression_stable_edgeListGain_upperReturn,
    zRegression_stable_edgeListGain_lowerReturn,
    zRegression_stable_upperPathCofactor, zRegression_stable_lowerPathCofactor,
    zRegression_stable_upperReturnPathCofactor,
    zRegression_stable_lowerReturnPathCofactor]
  ring

/-- The two touching loops give the complete eleven-branch determinant `3/4`. -/
lemma zRegression_stable_edgeGraphDet :
    edgeGraphDet
        (signalMultigraph (stableUnitDelayParameters.at (-Complex.I))) = 3 / 4 := by
  rw [edgeGraphDet, zRegression_stable_edgeGraphDetOn]
  norm_num [zRegressionStableUpperLoopNodes, zRegressionStableLowerLoopNodes]

/-- Independent eleven-branch Mason enumeration gives `-(7/8) I` at `q = -I`. -/
lemma zRegression_stable_auditedMasonResponse_neg_I :
    auditedMasonResponse (stableUnitDelayParameters.at (-Complex.I)) =
      -(7 / 8) * Complex.I := by
  rw [auditedMasonResponse, zRegression_stable_edgeMasonNumerator,
    zRegression_stable_edgeGraphDet]
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
