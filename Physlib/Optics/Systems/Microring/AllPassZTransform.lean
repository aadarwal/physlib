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
asserts an ROC, summability, material dispersion law, physical group delay, or time-domain
Maxwell realization. The parameter `a` is a field-amplitude coefficient, not a power attenuation.

## ii. Key results

- `AllPass.causalOutput`: the constructed causal recurrence solution.
- `AllPass.transform_causalOutput_cleared`: the division-free Z-transform law.
- `AllPass.zTransfer_eq`: the exact reciprocal-variable transfer.

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

/-! ## B. Transform laws -/

/-- The transfer function attached to the independently stated all-pass recurrence. -/
def zTransfer (through attenuation z : ℂ) : ℂ :=
  transferFunction zFeedbackLags zFeedforwardLags
    (zFeedbackCoefficients through attenuation)
    (zFeedforwardCoefficients through attenuation) z

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

end AllPass

end

end Optics
