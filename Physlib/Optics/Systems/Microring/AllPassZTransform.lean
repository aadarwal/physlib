/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Mathematics.ZTransform.Existence

/-!
# Causal Z-transform semantics of the all-pass microring

## i. Overview

This file gives the all-pass ring an independently stated discrete-time semantics. For through
coefficient `t`, one-pass field coefficient `a`, input `x`, and output `y`, the recurrence is

```text
y[n] = t*a*y[n-1] + t*x[n] - a*x[n-1].
```

Its causal solution is constructed by the neutral Z-transform library. The cleared transform law
is proved before division, and the quotient law retains convergence and denominator hypotheses.
The resulting transfer is `(t - a*z⁻¹) / (1 - t*a*z⁻¹)`.

This file stops at the independently stated recurrence and its analytic transform. The separate
`AllPassZTransformBridge` module identifies it with the fixed-carrier optical ring. Nothing here
asserts a material dispersion law, physical group delay, or time-domain Maxwell realization. The
ROC is an absolute-convergence set, and the parameter `a` is a field-amplitude coefficient, not a
power attenuation.

## ii. Key results

- `AllPass.causalOutput`: the constructed causal recurrence solution.
- `AllPass.impulseResponseFormula`: its explicit causal impulse-response formula.
- `AllPass.zTransferROC`: the absolute ROC of the impulse-response transfer relation.
- `AllPass.mem_zTransferROC_of_norm_feedback_lt_norm`: a sufficient exterior-domain result.
- `AllPass.transform_causalOutput_cleared`: the division-free Z-transform law.
- `AllPass.zTransfer_eq`: the exact reciprocal-variable transfer.
- `AllPass.transform_causalImpulseResponse_eq_zTransfer`: the transfer is the transform of the
  causal impulse response on its ROC.

## iii. Table of contents

- A. Independent causal recurrence
- B. Transform laws

## iv. References

This optical recurrence is Physlib-original. The neutral Z-transform layer carries the cited ITP
2014 and JAL 2018 source comparisons; the microring realization is derived separately.
-/

@[expose] public section

namespace Optics

noncomputable section

namespace AllPass

open Physlib.ZTransform

/-! ## A. Independent causal recurrence -/

/-- The strictly positive feedback lag of the one-delay all-pass recurrence. -/
def zFeedbackLags : Finset ℕ := {1}

/-- The undelayed and one-delay feedforward lags of the all-pass recurrence. -/
def zFeedforwardLags : Finset ℕ := {0, 1}

/-- The feedback coefficient `t*a` at lag one. -/
def zFeedbackCoefficients (through attenuation : ℂ) : ℕ → ℂ :=
  fun lag => if lag = 1 then through * attenuation else 0

/-- The feedforward coefficients `t` at lag zero and `-a` at lag one. -/
def zFeedforwardCoefficients (through attenuation : ℂ) : ℕ → ℂ :=
  fun lag => if lag = 0 then through else if lag = 1 then -attenuation else 0

/-- The all-pass feedback lag set excludes the undelayed lag. -/
lemma zero_notMem_zFeedbackLags : (0 : ℕ) ∉ zFeedbackLags := by
  decide

/-- The feedback symbol is `t*a*q`. -/
lemma delaySymbol_zFeedbackCoefficients (through attenuation q : ℂ) :
    delaySymbol zFeedbackLags (zFeedbackCoefficients through attenuation) q =
      through * attenuation * q := by
  simp [zFeedbackLags, zFeedbackCoefficients, delaySymbol]

/-- The feedforward symbol is `t - a*q`. -/
lemma delaySymbol_zFeedforwardCoefficients (through attenuation q : ℂ) :
    delaySymbol zFeedforwardLags (zFeedforwardCoefficients through attenuation) q =
      through - attenuation * q := by
  simp [zFeedforwardLags, zFeedforwardCoefficients, delaySymbol]
  ring

/-- The feedback delay combination is the one-step return multiplied by `t*a`. -/
lemma delayCombination_zFeedbackCoefficients (through attenuation : ℂ) (f : ℤ → ℂ)
    (n : ℤ) :
    delayCombination zFeedbackLags (zFeedbackCoefficients through attenuation) f n =
      through * attenuation * f (n - 1) := by
  simp [delayCombination, zFeedbackLags, zFeedbackCoefficients]

/-- The feedforward delay combination is `t*x[n] - a*x[n-1]`. -/
lemma delayCombination_zFeedforwardCoefficients (through attenuation : ℂ) (f : ℤ → ℂ)
    (n : ℤ) :
    delayCombination zFeedforwardLags (zFeedforwardCoefficients through attenuation) f n =
      through * f n - attenuation * f (n - 1) := by
  simp [delayCombination, zFeedforwardLags, zFeedforwardCoefficients]
  ring

/-- The causal all-pass impulse response written as a direct path minus one delayed geometric
path. -/
def impulseResponseFormula (through attenuation : ℂ) : ℤ → ℂ :=
  fun n => through * geometricSeq (through * attenuation) n -
    attenuation * delay 1 (geometricSeq (through * attenuation)) n

/-- The explicit all-pass impulse-response formula is causal. -/
lemma impulseResponseFormula_isCausal (through attenuation : ℂ) :
    IsCausal (impulseResponseFormula through attenuation) := by
  intro n hn
  rw [impulseResponseFormula, geometricSeq_isCausal _ n hn,
    IsCausal.delay (geometricSeq_isCausal _) 1 n hn]
  ring

/-- The explicit formula obeys the recurrence at every nonnegative index. -/
private lemma impulseResponseFormula_recurrence_natCast (through attenuation : ℂ) (m : ℕ) :
    impulseResponseFormula through attenuation (m : ℤ) =
      through * attenuation * impulseResponseFormula through attenuation ((m : ℤ) - 1) +
        (through * unitImpulse m - attenuation * unitImpulse ((m : ℤ) - 1)) := by
  rcases m with _ | k
  · have hneg1 : geometricSeq (through * attenuation) (-1) = 0 :=
      geometricSeq_isCausal _ (-1) (by norm_num)
    have hneg2 : geometricSeq (through * attenuation) (-2) = 0 :=
      geometricSeq_isCausal _ (-2) (by norm_num)
    have hzero : geometricSeq (through * attenuation) (0 : ℤ) = 1 := by
      simpa using geometricSeq_natCast (through * attenuation) 0
    simp [impulseResponseFormula, delay, unitImpulse, hneg1, hneg2, hzero]
  · rcases k with _ | k
    · have hneg1 : geometricSeq (through * attenuation) (-1) = 0 :=
        geometricSeq_isCausal _ (-1) (by norm_num)
      have hzero : geometricSeq (through * attenuation) (0 : ℤ) = 1 := by
        simpa using geometricSeq_natCast (through * attenuation) 0
      have hone : geometricSeq (through * attenuation) (1 : ℤ) =
          through * attenuation := by
        simpa using geometricSeq_natCast (through * attenuation) 1
      norm_num [impulseResponseFormula, delay, unitImpulse, hneg1, hzero, hone]
      ring
    · have hsub1 : (((k + 2 : ℕ) : ℤ) - 1) = ((k + 1 : ℕ) : ℤ) := by omega
      have hg2 : geometricSeq (through * attenuation) ((k + 2 : ℕ) : ℤ) =
          (through * attenuation) ^ (k + 2) :=
        geometricSeq_natCast _ _
      have hg1 : geometricSeq (through * attenuation) (((k + 2 : ℕ) : ℤ) - 1) =
          (through * attenuation) ^ (k + 1) := by
        rw [hsub1]
        exact geometricSeq_natCast _ _
      have hImpulse : unitImpulse ((k + 2 : ℕ) : ℤ) = 0 := by
        rw [unitImpulse, if_neg (by omega)]
      have hDelayedImpulse : unitImpulse (((k + 2 : ℕ) : ℤ) - 1) = 0 := by
        rw [unitImpulse, if_neg (by omega)]
      simp only [impulseResponseFormula, delay, hg2, hg1,
        hImpulse, hDelayedImpulse, mul_zero, sub_zero, add_zero]
      have hdelay1 : (((k + 1 + 1 : ℕ) : ℤ) - (1 : ℕ)) =
          ((k + 1 : ℕ) : ℤ) := by omega
      have hdelay2 : ((((k + 1 + 1 : ℕ) : ℤ) - 1) - (1 : ℕ)) =
          (k : ℤ) := by omega
      rw [hdelay1, hdelay2, geometricSeq_natCast, geometricSeq_natCast]
      rw [show k + 2 = (k + 1) + 1 by omega, pow_succ, pow_succ]
      ring

/-- The explicit impulse-response formula solves the independently stated all-pass recurrence. -/
lemma impulseResponseFormula_isRecurrenceSolution (through attenuation : ℂ) :
    IsRecurrenceSolution zFeedbackLags zFeedforwardLags
      (zFeedbackCoefficients through attenuation)
      (zFeedforwardCoefficients through attenuation) unitImpulse
      (impulseResponseFormula through attenuation) := by
  funext n
  rw [Pi.add_apply]
  rw [delayCombination_zFeedbackCoefficients,
    delayCombination_zFeedforwardCoefficients]
  rcases lt_or_ge n 0 with hn | hn
  · have hn1 : n - 1 < 0 := by omega
    rw [impulseResponseFormula_isCausal through attenuation n hn,
      impulseResponseFormula_isCausal through attenuation (n - 1) hn1,
      unitImpulse_isCausal n hn, unitImpulse_isCausal (n - 1) hn1]
    ring
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    exact impulseResponseFormula_recurrence_natCast through attenuation m

/-- The causal output selected by the all-pass difference equation. -/
def causalOutput (through attenuation : ℂ) (input : ℤ → ℂ) : ℤ → ℂ :=
  recurrenceSolution zFeedbackLags zFeedforwardLags
    (zFeedbackCoefficients through attenuation)
    (zFeedforwardCoefficients through attenuation) input

/-- The constructed all-pass output is causal for every input sequence. -/
lemma causalOutput_isCausal (through attenuation : ℂ) (input : ℤ → ℂ) :
    IsCausal (causalOutput through attenuation input) := by
  exact recurrenceSolution_isCausal zFeedbackLags zFeedforwardLags
    (zFeedbackCoefficients through attenuation)
    (zFeedforwardCoefficients through attenuation) input

/-- A causal input makes the constructed output solve the stated all-pass recurrence. -/
lemma causalOutput_isRecurrenceSolution (through attenuation : ℂ) {input : ℤ → ℂ}
    (hInput : IsCausal input) :
    IsRecurrenceSolution zFeedbackLags zFeedforwardLags
      (zFeedbackCoefficients through attenuation)
      (zFeedforwardCoefficients through attenuation) input
      (causalOutput through attenuation input) := by
  exact isRecurrenceSolution_recurrenceSolution zero_notMem_zFeedbackLags hInput

/-- The recursively constructed causal impulse response equals its direct geometric formula. -/
lemma causalOutput_unitImpulse_eq_impulseResponseFormula (through attenuation : ℂ) :
    causalOutput through attenuation unitImpulse =
      impulseResponseFormula through attenuation := by
  exact eq_of_isRecurrenceSolution zero_notMem_zFeedbackLags
    (causalOutput_isCausal through attenuation unitImpulse)
    (impulseResponseFormula_isCausal through attenuation)
    (causalOutput_isRecurrenceSolution through attenuation unitImpulse_isCausal)
    (impulseResponseFormula_isRecurrenceSolution through attenuation)

/-! ## B. Transform laws -/

/-- The transfer function attached to the independently stated all-pass recurrence. -/
def zTransfer (through attenuation z : ℂ) : ℂ :=
  transferFunction zFeedbackLags zFeedforwardLags
    (zFeedbackCoefficients through attenuation)
    (zFeedforwardCoefficients through attenuation) z

/-- The absolute region of convergence of the all-pass impulse-response transfer relation.

This is the intersection of the input and output ROCs with the recurrence denominator zeros
removed. It is an analytic condition, not a fixed-frequency network solve predicate.
-/
def zTransferROC (through attenuation : ℂ) : Set ℂ :=
  iirROC zFeedbackLags (zFeedbackCoefficients through attenuation) unitImpulse
    (causalOutput through attenuation unitImpulse)

/-- Membership in the all-pass transfer ROC includes a nonzero evaluation point. -/
lemma ne_zero_of_mem_zTransferROC {through attenuation z : ℂ}
    (hz : z ∈ zTransferROC through attenuation) : z ≠ 0 :=
  hz.1.1.1

/-- Membership in the all-pass transfer ROC removes the recurrence-denominator zeros. -/
lemma recurrenceDenominator_ne_zero_of_mem_zTransferROC {through attenuation z : ℂ}
    (hz : z ∈ zTransferROC through attenuation) :
    1 - through * attenuation * z⁻¹ ≠ 0 := by
  simpa [zTransferROC, iirROC, delaySymbol_zFeedbackCoefficients] using hz.2

/-- Outside the feedback-pole circle, the causal impulse-response transfer belongs to its named
absolute ROC. -/
lemma mem_zTransferROC_of_norm_feedback_lt_norm {through attenuation z : ℂ}
    (hFeedback : through * attenuation ≠ 0)
    (hNorm : ‖through * attenuation‖ < ‖z‖) :
    z ∈ zTransferROC through attenuation := by
  have hz : z ≠ 0 := by
    intro hZero
    rw [hZero, norm_zero] at hNorm
    linarith [norm_nonneg (through * attenuation)]
  have hGeometric : z ∈ ROC (geometricSeq (through * attenuation)) := by
    rw [ROC_geometricSeq hFeedback]
    exact hNorm
  have hDelayed : Summable
      (seriesTerm (delay 1 (geometricSeq (through * attenuation))) z) :=
    summable_seriesTerm_delay 1 hGeometric.2
  have hFormula : Summable (seriesTerm (impulseResponseFormula through attenuation) z) := by
    apply summable_seriesTerm_sub
    · exact summable_seriesTerm_const_mul through hGeometric.2
    · exact summable_seriesTerm_const_mul attenuation hDelayed
  have hDenominator : 1 - through * attenuation * z⁻¹ ≠ 0 := by
    intro hZero
    have hProduct : through * attenuation * z⁻¹ = 1 := by
      linear_combination -hZero
    have hEqual : through * attenuation = z := by
      calc
        through * attenuation = (through * attenuation) * (z⁻¹ * z) := by
          rw [inv_mul_cancel₀ hz, mul_one]
        _ = (through * attenuation * z⁻¹) * z := by ring
        _ = z := by rw [hProduct, one_mul]
    exact (ne_of_lt hNorm) (congrArg norm hEqual)
  rw [zTransferROC]
  refine ⟨⟨⟨hz, summable_seriesTerm_unitImpulse z⟩, ⟨hz, ?_⟩⟩, ?_⟩
  · rw [causalOutput_unitImpulse_eq_impulseResponseFormula]
    exact hFormula
  · simpa [delaySymbol_zFeedbackCoefficients] using hDenominator

/-- The causal all-pass recurrence has the division-free transform identity. -/
lemma transform_causalOutput_cleared {through attenuation z : ℂ} {input : ℤ → ℂ}
    (hInput : IsCausal input) (hInputSummable : Summable (seriesTerm input z))
    (hOutputSummable : Summable
      (seriesTerm (causalOutput through attenuation input) z)) :
    (1 - through * attenuation * z⁻¹) *
        transform (causalOutput through attenuation input) z =
      (through - attenuation * z⁻¹) * transform input z := by
  have h := transform_recurrenceSolution_cleared
    (s := zFeedbackLags) (t := zFeedforwardLags)
    (α := zFeedbackCoefficients through attenuation)
    (β := zFeedforwardCoefficients through attenuation)
    zero_notMem_zFeedbackLags hInput hInputSummable hOutputSummable
  simpa [causalOutput, delaySymbol_zFeedbackCoefficients,
    delaySymbol_zFeedforwardCoefficients] using h

/-- The all-pass recurrence transfer is `(t - a*z⁻¹) / (1 - t*a*z⁻¹)`. -/
lemma zTransfer_eq (through attenuation z : ℂ) :
    zTransfer through attenuation z =
      (through - attenuation * z⁻¹) / (1 - through * attenuation * z⁻¹) := by
  rw [zTransfer, transferFunction, delaySymbol_zFeedbackCoefficients,
    delaySymbol_zFeedforwardCoefficients]

/-- Away from a recurrence-denominator zero, the transfer obeys its cleared equation. -/
lemma recurrenceDenominator_mul_zTransfer {through attenuation z : ℂ}
    (hDenominator : 1 - through * attenuation * z⁻¹ ≠ 0) :
    (1 - through * attenuation * z⁻¹) * zTransfer through attenuation z =
      through - attenuation * z⁻¹ := by
  rw [zTransfer_eq, mul_div_cancel₀ _ hDenominator]

/-- On the convergence and nonzero-denominator domain, the constructed output transform is its
transfer times the input transform. -/
lemma transform_causalOutput {through attenuation z : ℂ} {input : ℤ → ℂ}
    (hInput : IsCausal input) (hInputSummable : Summable (seriesTerm input z))
    (hOutputSummable : Summable
      (seriesTerm (causalOutput through attenuation input) z))
    (hDenominator : 1 - through * attenuation * z⁻¹ ≠ 0) :
    transform (causalOutput through attenuation input) z =
      zTransfer through attenuation z * transform input z := by
  have hDenominator' :
      1 - delaySymbol zFeedbackLags
        (zFeedbackCoefficients through attenuation) z⁻¹ ≠ 0 := by
    simpa [delaySymbol_zFeedbackCoefficients] using hDenominator
  exact transform_recurrenceSolution zero_notMem_zFeedbackLags hInput
    hInputSummable hOutputSummable hDenominator'

/-- On its named ROC, the transfer is exactly the Z-transform of the causal impulse response. -/
lemma transform_causalImpulseResponse_eq_zTransfer {through attenuation z : ℂ}
    (hz : z ∈ zTransferROC through attenuation) :
    transform (causalOutput through attenuation unitImpulse) z =
      zTransfer through attenuation z := by
  rw [zTransfer]
  rw [transform_eq_transferFunction_mul_of_mem_iirROC unitImpulse_isCausal
    (causalOutput_isCausal through attenuation unitImpulse) hz
    (causalOutput_isRecurrenceSolution through attenuation unitImpulse_isCausal),
    transform_unitImpulse, mul_one]

end AllPass

end

end Optics
