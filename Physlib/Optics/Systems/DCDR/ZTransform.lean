/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Mathematics.ZTransform.Existence
public import Physlib.Mathematics.ZTransform.Stability
public import Physlib.Optics.Systems.DCDR.Poles

/-!
# Causal Z-transform semantics of the unit-delay DCDR

## i. Overview

This file attaches an independently constructed causal recurrence to the coherent unit-delay DCDR
rational data. Its feedback coefficients are exactly the coefficients of
`UnitDelayParameters.loopPolynomial`; its feedforward coefficients are exactly those of
`UnitDelayParameters.responseNumeratorPolynomial`. Thus the recurrence transfer is the retained
raw quotient at the reciprocal coordinate `q = z⁻¹`.

The construction follows the neutral recurrence and ROC pattern used by the ring in
`Physlib/Optics/Systems/Microring/AllPassZTransform.lean:193-346`. The DCDR polynomial data and
compiled rational N7/N5 family are defined in
`Physlib/Optics/Systems/DCDR/Poles.lean:144-612`. The named ROC is an absolute-convergence set,
kept distinct from both compiled well-posedness and Schur stability.

No physical resonance, coherent--incoherent equivalence, BIBO conclusion, modal or
electromagnetic power statement, Maxwell time-domain interpretation, reciprocity, physical
frequency interpretation, or claim about the unavailable HOL script is made.
Power would mean normalized modal power, not electromagnetic power before the finite,
common-frequency, Maxwell-qualified, pairwise-integrable, mutually flux-orthogonal,
unit-normalized bridge at
`Physlib/Optics/HarmonicFlux/PropagatingModePower.lean:16-22,60-93`.

## ii. Key results

- `DCDR.causalOutput`: the causal solution selected by the polynomial recurrence.
- `DCDR.zTransferROC`: its named absolute region of convergence.
- `DCDR.mem_zTransferROC_of_lagTwoGeometric`: a strict two-lag geometric bound proves ROC
  membership.
- `DCDR.recurrenceDenominator_ne_zero_of_mem_zTransferROC`: the solve gate extracted from ROC
  membership.
- `DCDR.zTransfer_eq_responseModel`: the recurrence transfer is the unit-delay rational quotient
  at `q = z⁻¹`.
- `DCDR.transform_causalImpulseResponse_eq_zTransfer`: the causal impulse transform equals that
  quotient on the ROC.

## iii. Table of contents

- A. Polynomial recurrence
- B. Transfer and region of convergence
- C. Transform and Schur laws

## iv. References

The causal recurrence bridge is Physlib-original. The neutral Z-transform layer carries the ITP
2014 and JAL 2018 source comparisons. FMICS'15 Theorem 3 supplies the rational DCDR shape, while
the coherent polynomial family here is the source's stated but unprinted coherent branch.
-/

@[expose] public section

namespace Optics.DCDR

noncomputable section

open Polynomial
open Physlib.ZTransform

/-!

## A. Polynomial recurrence

-/

/-- The nonzero feedback lags retained by the coherent loop polynomial. -/
def zFeedbackLags (p : UnitDelayParameters) : Finset ℕ :=
  p.loopPolynomial.support

/-- The nonzero feedforward lags retained by the selected response numerator. -/
def zFeedforwardLags (p : UnitDelayParameters) : Finset ℕ :=
  p.responseNumeratorPolynomial.support

/-- The recurrence feedback coefficients, read directly from the loop polynomial. -/
def zFeedbackCoefficients (p : UnitDelayParameters) : ℕ → ℂ :=
  p.loopPolynomial.coeff

/-- The recurrence feedforward coefficients, read directly from the response numerator. -/
def zFeedforwardCoefficients (p : UnitDelayParameters) : ℕ → ℂ :=
  p.responseNumeratorPolynomial.coeff

/-- The coherent loop has no undelayed feedback coefficient. -/
lemma zero_notMem_zFeedbackLags (p : UnitDelayParameters) :
    (0 : ℕ) ∉ zFeedbackLags p := by
  simp [zFeedbackLags, UnitDelayParameters.loopPolynomial,
    UnitDelayParameters.upperPolynomial, UnitDelayParameters.lowerPolynomial,
    UnitDelayParameters.feedbackPolynomial]

/-- The recurrence feedback symbol is exactly the coherent loop polynomial. -/
lemma delaySymbol_zFeedbackCoefficients (p : UnitDelayParameters) (q : ℂ) :
    delaySymbol (zFeedbackLags p) (zFeedbackCoefficients p) q =
      p.loopPolynomial.eval q := by
  rw [delaySymbol, zFeedbackLags, zFeedbackCoefficients,
    Polynomial.eval_eq_sum, Polynomial.sum_def]

/-- The recurrence feedforward symbol is exactly the selected response numerator. -/
lemma delaySymbol_zFeedforwardCoefficients (p : UnitDelayParameters) (q : ℂ) :
    delaySymbol (zFeedforwardLags p) (zFeedforwardCoefficients p) q =
      p.responseNumeratorPolynomial.eval q := by
  rw [delaySymbol, zFeedforwardLags, zFeedforwardCoefficients,
    Polynomial.eval_eq_sum, Polynomial.sum_def]

/-- The causal impulse kernel for a lag-two feedback coefficient `r ^ 2`.

The average of ratios `r` and `-r` cancels every odd sample. Its even samples are the geometric
sequence with ratio `r ^ 2`.
-/
def lagTwoGeometricImpulse (r : ℂ) : ℤ → ℂ :=
  fun n => (1 / 2) * (geometricSeq r n + geometricSeq (-r) n)

/-- The lag-two geometric impulse kernel is causal. -/
lemma lagTwoGeometricImpulse_isCausal (r : ℂ) : IsCausal (lagTwoGeometricImpulse r) :=
  ((geometricSeq_isCausal r).add (geometricSeq_isCausal (-r))).const_mul (1 / 2)

/-- The lag-two kernel solves `y[n] = r^2 y[n-2] + delta[n]`. -/
lemma lagTwoGeometricImpulse_step (r : ℂ) (n : ℤ) :
    lagTwoGeometricImpulse r n =
      r ^ 2 * lagTwoGeometricImpulse r (n - 2) + unitImpulse n := by
  cases n with
  | ofNat n =>
      rcases n with _ | _ | n
      · norm_num [lagTwoGeometricImpulse, geometricSeq, zScale,
          unitStep, unitImpulse]
      · norm_num [lagTwoGeometricImpulse, geometricSeq, zScale,
          unitStep, unitImpulse]
      · simp only [lagTwoGeometricImpulse]
        have hIndex : Int.ofNat (n + 1 + 1) = Int.ofNat (n + 2) := by
          congr 1
        rw [hIndex]
        simp only [Int.ofNat_eq_natCast]
        have hSub : ((n + 2 : ℕ) : ℤ) - 2 = (n : ℤ) := by omega
        rw [hSub, geometricSeq_natCast, geometricSeq_natCast,
          geometricSeq_natCast, geometricSeq_natCast]
        have hNonzero : ((n + 2 : ℕ) : ℤ) ≠ 0 := by omega
        simp only [unitImpulse, if_neg hNonzero]
        ring
  | negSucc n =>
      simp only [lagTwoGeometricImpulse]
      rw [geometricSeq_isCausal r (Int.negSucc n) (by omega),
        geometricSeq_isCausal (-r) (Int.negSucc n) (by omega),
        geometricSeq_isCausal r (Int.negSucc n - 2) (by omega),
        geometricSeq_isCausal (-r) (Int.negSucc n - 2) (by omega)]
      simp [unitImpulse]

/-- The lag-two geometric kernel has an absolutely convergent transform when
`‖r‖ < ‖z‖`. Equivalently, its lag-two coefficient satisfies `‖r ^ 2‖ < ‖z‖ ^ 2`. -/
lemma summable_seriesTerm_lagTwoGeometricImpulse {r z : ℂ} (hrz : ‖r‖ < ‖z‖) :
    Summable (seriesTerm (lagTwoGeometricImpulse r) z) := by
  have hz : 0 < ‖z‖ := lt_of_le_of_lt (norm_nonneg r) hrz
  have hRatio : ‖r * z⁻¹‖ < 1 := by
    rw [norm_mul, norm_inv, ← div_eq_mul_inv, div_lt_one hz]
    exact hrz
  have hPositive : Summable (seriesTerm (geometricSeq r) z) := by
    have hGeometric : Summable (fun n : ℕ => (r * z⁻¹) ^ n) :=
      summable_geometric_of_norm_lt_one hRatio
    exact hGeometric.congr fun n => by
      rw [seriesTerm, geometricSeq_natCast, mul_pow]
  have hNegative : Summable (seriesTerm (geometricSeq (-r)) z) := by
    have hNegativeRatio : ‖(-r) * z⁻¹‖ < 1 := by simpa using hRatio
    have hGeometric : Summable (fun n : ℕ => ((-r) * z⁻¹) ^ n) :=
      summable_geometric_of_norm_lt_one hNegativeRatio
    exact hGeometric.congr fun n => by
      rw [seriesTerm, geometricSeq_natCast, mul_pow]
  exact summable_seriesTerm_const_mul (1 / 2)
    (summable_seriesTerm_add hPositive hNegative)

/-- The causal output selected by the coherent DCDR polynomial recurrence. -/
def causalOutput (p : UnitDelayParameters) (input : ℤ → ℂ) : ℤ → ℂ :=
  recurrenceSolution (zFeedbackLags p) (zFeedforwardLags p)
    (zFeedbackCoefficients p) (zFeedforwardCoefficients p) input

/-- The constructed DCDR output is causal for every input sequence. -/
lemma causalOutput_isCausal (p : UnitDelayParameters) (input : ℤ → ℂ) :
    IsCausal (causalOutput p input) :=
  recurrenceSolution_isCausal (zFeedbackLags p) (zFeedforwardLags p)
    (zFeedbackCoefficients p) (zFeedforwardCoefficients p) input

/-- A causal input makes the constructed output solve the polynomial recurrence. -/
lemma causalOutput_isRecurrenceSolution (p : UnitDelayParameters) {input : ℤ → ℂ}
    (hInput : IsCausal input) :
    IsRecurrenceSolution (zFeedbackLags p) (zFeedforwardLags p)
      (zFeedbackCoefficients p) (zFeedforwardCoefficients p) input
      (causalOutput p input) :=
  isRecurrenceSolution_recurrenceSolution (zero_notMem_zFeedbackLags p) hInput

/-- A singleton lag-two DCDR recurrence has the finite-feedforward convolution of the lag-two
geometric kernel as its causal impulse response. -/
lemma causalOutput_eq_lagTwoGeometricImpulse (p : UnitDelayParameters) (r : ℂ)
    (hLags : zFeedbackLags p = {2})
    (hCoefficient : zFeedbackCoefficients p 2 = r ^ 2) :
    causalOutput p unitImpulse =
      delayCombination (zFeedforwardLags p) (zFeedforwardCoefficients p)
        (lagTwoGeometricImpulse r) := by
  apply eq_of_isRecurrenceSolution (zero_notMem_zFeedbackLags p)
    (causalOutput_isCausal p unitImpulse)
    ((lagTwoGeometricImpulse_isCausal r).delayCombination _ _)
    (causalOutput_isRecurrenceSolution p unitImpulse_isCausal)
  rw [IsRecurrenceSolution]
  funext n
  simp only [Pi.add_apply, delayCombination]
  rw [hLags, Finset.sum_singleton, hCoefficient]
  calc
    (∑ k ∈ zFeedforwardLags p,
        zFeedforwardCoefficients p k * lagTwoGeometricImpulse r (n - k)) =
        ∑ k ∈ zFeedforwardLags p, zFeedforwardCoefficients p k *
          (r ^ 2 * lagTwoGeometricImpulse r (n - k - 2) +
            unitImpulse (n - k)) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [lagTwoGeometricImpulse_step]
    _ = r ^ 2 *
          (∑ k ∈ zFeedforwardLags p,
            zFeedforwardCoefficients p k * lagTwoGeometricImpulse r (n - 2 - k)) +
        ∑ k ∈ zFeedforwardLags p,
          zFeedforwardCoefficients p k * unitImpulse (n - k) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring

/-!

## B. Transfer and region of convergence

-/

/-- The transfer function of the coherent DCDR polynomial recurrence. -/
def zTransfer (p : UnitDelayParameters) (z : ℂ) : ℂ :=
  transferFunction (zFeedbackLags p) (zFeedforwardLags p)
    (zFeedbackCoefficients p) (zFeedforwardCoefficients p) z

/-- The absolute ROC of the causal DCDR impulse-response transfer relation.

This set intersects the input and output ROCs and removes recurrence-denominator zeros. It is not
identified with the compiled rational response domain or a stability predicate.
-/
def zTransferROC (p : UnitDelayParameters) : Set ℂ :=
  iirROC (zFeedbackLags p) (zFeedbackCoefficients p) unitImpulse
    (causalOutput p unitImpulse)

/-- Strict lag-two geometric decay proves membership in the actual DCDR transfer ROC.

The hypotheses expose the retained lag and its square root. The analytic inequality
`‖r‖ < ‖z‖` is equivalent to `‖r ^ 2‖ < ‖z‖ ^ 2`; it is not an algebraic solve gate.
-/
lemma mem_zTransferROC_of_lagTwoGeometric (p : UnitDelayParameters) (r z : ℂ)
    (hLags : zFeedbackLags p = {2})
    (hCoefficient : zFeedbackCoefficients p 2 = r ^ 2)
    (hrz : ‖r‖ < ‖z‖) : z ∈ zTransferROC p := by
  have hz : z ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt
    (lt_of_le_of_lt (norm_nonneg r) hrz))
  have hOutput : Summable (seriesTerm (causalOutput p unitImpulse) z) := by
    rw [causalOutput_eq_lagTwoGeometricImpulse p r hLags hCoefficient]
    exact summable_seriesTerm_delayCombination _ _
      (summable_seriesTerm_lagTwoGeometricImpulse hrz)
  have hRatio : ‖r * z⁻¹‖ < 1 := by
    rw [norm_mul, norm_inv, ← div_eq_mul_inv,
      div_lt_one (norm_pos_iff.mpr hz)]
    exact hrz
  have hDenominator :
      1 - delaySymbol (zFeedbackLags p) (zFeedbackCoefficients p) z⁻¹ ≠ 0 := by
    rw [hLags, delaySymbol, Finset.sum_singleton, hCoefficient]
    intro hZero
    have hOne : r ^ 2 * z⁻¹ ^ 2 = 1 := (sub_eq_zero.mp hZero).symm
    have hNorm := congrArg norm hOne
    rw [← mul_pow, norm_pow, norm_one] at hNorm
    have hRatioNonneg : 0 ≤ ‖r * z⁻¹‖ := norm_nonneg _
    nlinarith
  exact ⟨⟨⟨hz, summable_seriesTerm_unitImpulse z⟩, ⟨hz, hOutput⟩⟩, hDenominator⟩

/-- Membership in the DCDR transfer ROC includes a nonzero Z coordinate. -/
lemma ne_zero_of_mem_zTransferROC {p : UnitDelayParameters} {z : ℂ}
    (hz : z ∈ zTransferROC p) : z ≠ 0 :=
  hz.1.1.1

/-- ROC membership removes recurrence-denominator zeros in the formal coordinate `q = z⁻¹`. -/
lemma recurrenceDenominator_ne_zero_of_mem_zTransferROC
    {p : UnitDelayParameters} {z : ℂ} (hz : z ∈ zTransferROC p) :
    p.denominatorPolynomial.eval z⁻¹ ≠ 0 := by
  simpa [zTransferROC, iirROC, delaySymbol_zFeedbackCoefficients,
    UnitDelayParameters.denominatorPolynomial] using hz.2

/-- The recurrence transfer is the raw unit-delay quotient at the reciprocal coordinate. -/
lemma zTransfer_eq_quotient (p : UnitDelayParameters) (z : ℂ) :
    zTransfer p z =
      p.responseNumeratorPolynomial.eval z⁻¹ /
        p.denominatorPolynomial.eval z⁻¹ := by
  rw [zTransfer, transferFunction, delaySymbol_zFeedbackCoefficients,
    delaySymbol_zFeedforwardCoefficients, UnitDelayParameters.denominatorPolynomial,
    eval_sub, eval_one]

/-- The recurrence transfer is the retained rational DCDR response model at `q = z⁻¹`. -/
lemma zTransfer_eq_responseModel (p : UnitDelayParameters) (z : ℂ) :
    zTransfer p z = (responseModel p).eval (fun _ : Fin 1 => z⁻¹) := by
  rw [zTransfer_eq_quotient, DelayTransfer.RationalModel.eval_eq]
  simp [responseModel]

/-- Evaluating the recurrence at `q = z⁻¹` gives the fixed-carrier coherent transfer. -/
lemma zTransfer_eq_transfer (p : UnitDelayParameters) (z : ℂ) :
    zTransfer p z = transfer (p.at z⁻¹) := by
  rw [zTransfer_eq_responseModel, responseModel_eval]

/-!

## C. Transform and Schur laws

-/

/-- The causal DCDR recurrence has the division-free transform identity. -/
lemma transform_causalOutput_cleared {p : UnitDelayParameters} {z : ℂ}
    {input : ℤ → ℂ} (hInput : IsCausal input)
    (hInputSummable : Summable (seriesTerm input z))
    (hOutputSummable : Summable (seriesTerm (causalOutput p input) z)) :
    p.denominatorPolynomial.eval z⁻¹ * transform (causalOutput p input) z =
      p.responseNumeratorPolynomial.eval z⁻¹ * transform input z := by
  have h := transform_recurrenceSolution_cleared
    (s := zFeedbackLags p) (t := zFeedforwardLags p)
    (α := zFeedbackCoefficients p) (β := zFeedforwardCoefficients p)
    (zero_notMem_zFeedbackLags p) hInput hInputSummable hOutputSummable
  simpa [causalOutput, delaySymbol_zFeedbackCoefficients,
    delaySymbol_zFeedforwardCoefficients, UnitDelayParameters.denominatorPolynomial] using h

/-- On its named ROC, the transfer is the Z-transform of the causal impulse response. -/
lemma transform_causalImpulseResponse_eq_zTransfer {p : UnitDelayParameters} {z : ℂ}
    (hz : z ∈ zTransferROC p) :
    transform (causalOutput p unitImpulse) z = zTransfer p z := by
  rw [zTransfer]
  rw [transform_eq_transferFunction_mul_of_mem_iirROC unitImpulse_isCausal
    (causalOutput_isCausal p unitImpulse) hz
    (causalOutput_isRecurrenceSolution p unitImpulse_isCausal),
    transform_unitImpulse, mul_one]

/-- The strict coefficient contraction used by the neutral S4 Z-transform Schur criterion. -/
def UnitDelayParameters.IsZContractive (p : UnitDelayParameters) : Prop :=
  ∑ lag ∈ zFeedbackLags p, ‖zFeedbackCoefficients p lag‖ < 1

/-- Coefficient contraction implies Schur stability of the DCDR recurrence feedback symbol.

This uses `Physlib.ZTransform.isSchurStable_of_sum_norm_lt_one`; it does not infer ROC membership.
-/
lemma zFeedback_isSchurStable_of_isZContractive (p : UnitDelayParameters)
    (hContractive : p.IsZContractive) :
    IsSchurStable (zFeedbackLags p) (zFeedbackCoefficients p) :=
  isSchurStable_of_sum_norm_lt_one hContractive

end

end Optics.DCDR
