/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Systems.Microring.SourceBridge

/-!
# Regression fixtures for microring source bridges

## i. Overview

This file evaluates the DATE'14, SysCon'15, and SFG-TR'14 source-side formulas at exact rational
coupler data. The calculations unfold the source records and formulas directly; they do not use
the bridge theorems being tested.

The SysCon fixture uses through amplitude `3/5`, cross amplitude `4/5`, source scalar `x_r=1/4`,
and the named phases zero and `pi`. Physlib maps `x_r` to its round-trip field attenuation based
on Def. 9's two `sqrt(x_r)` half arcs (`HOL-CORPUS.md:244-247`); this is not a source
field-vs-power classification. A second, valid 3-4-5 fixture witnesses that the previously
recorded but provenance-uncertain Thm. 6 denominator differs from the norm-square of Thm. 5.

## ii. Key results

- `sourceBridgeRegression_dateTwoPortChain_entries`: DATE Thm. 1's four matrix entries.
- `sourceBridgeRegression_dateFourPort_transfers`: DATE Def. 3's exact `R` and `T` values.
- `sourceBridgeRegression_sysCon_resonance_transfer`: SysCon Thm. 5 at zero phase.
- `sourceBridgeRegression_sysCon_resonance_series`: the Def. 9 geometric series independently.
- `sourceBridgeRegression_disputedDenominator_ne_amplitudeDenominator`: the source finding.
- `sourceBridgeRegression_sfg_transfer`: SFG-TR Thm. 7 at the same 3-4-5 data.

## iii. Table of contents

- A. DATE two-port and four-port formulas
- B. SysCon amplitude, power, and series
- C. Provenance-uncertain power-denominator candidate
- D. SFG-TR transfer formula

## iv. References and non-claims

The source statements are transcribed at `HOL-CORPUS.md:194-198`, `HOL-CORPUS.md:244-249`, and
`HOL-CORPUS.md:345-346`. The disputed power denominator is not in that corpus entry; it is a
previously recorded transcription of uncertain provenance. These fixtures do not classify the
discrepancy as a source error. They make no response-extremum, reciprocity, causality, omitted-loss,
bandwidth, dispersion, or measurement-validation claim.
-/

@[expose] public section

namespace Optics

noncomputable section

open scoped ComplexOrder

namespace MicroringSourceBridge

/-! ## A. DATE two-port and four-port formulas -/

/-- Exact DATE data with a half-turn circulation phase and no attenuation. -/
def sourceBridgeRegressionDateParameters : DateParameters where
  reflectivity := 3 / 5
  transmissivity := 4 / 5
  couplingLength := 1
  powerAttenuation := 0
  wavelength := 2
  effectiveIndex := 1

/-- The DATE fixture has unitary 3-4-5 amplitudes. -/
lemma sourceBridgeRegression_date_isUnitary :
    sourceBridgeRegressionDateParameters.IsUnitary := by
  norm_num [sourceBridgeRegressionDateParameters, DateParameters.IsUnitary]

/-- The DATE fixture's source phase is exactly `pi`. -/
lemma sourceBridgeRegression_date_roundTripPhase :
    sourceBridgeRegressionDateParameters.roundTripPhase = Real.pi := by
  rw [DateParameters.roundTripPhase]
  norm_num [sourceBridgeRegressionDateParameters]

/-- The DATE fixture's field attenuation is one. -/
lemma sourceBridgeRegression_date_fieldAttenuation :
    sourceBridgeRegressionDateParameters.fieldAttenuation = 1 := by
  norm_num [DateParameters.fieldAttenuation, sourceBridgeRegressionDateParameters]

/-- Direct expansion pins all four entries of DATE Thm. 1 at the 3-4-5 point. -/
lemma sourceBridgeRegression_dateTwoPortChain_entries :
    dateTwoPortChainMatrix sourceBridgeRegressionDateParameters
        (Sum.inl (BackwardWave.mk ())) (Sum.inl (BackwardWave.mk ())) =
          (5 / 4 : ℂ) * Complex.I ∧
      dateTwoPortChainMatrix sourceBridgeRegressionDateParameters
        (Sum.inl (BackwardWave.mk ())) (Sum.inr (ForwardWave.mk ())) =
          (3 / 4 : ℂ) * Complex.I ∧
      dateTwoPortChainMatrix sourceBridgeRegressionDateParameters
        (Sum.inr (ForwardWave.mk ())) (Sum.inl (BackwardWave.mk ())) =
          -(3 / 4 : ℂ) * Complex.I ∧
      dateTwoPortChainMatrix sourceBridgeRegressionDateParameters
        (Sum.inr (ForwardWave.mk ())) (Sum.inr (ForwardWave.mk ())) =
          -(5 / 4 : ℂ) * Complex.I := by
  constructor
  · norm_num [dateTwoPortChainMatrix, sourceBridgeRegressionDateParameters,
      div_eq_mul_inv]
  · constructor
    · norm_num [dateTwoPortChainMatrix, sourceBridgeRegressionDateParameters,
        div_eq_mul_inv]
      ring
    · constructor
      · norm_num [dateTwoPortChainMatrix, sourceBridgeRegressionDateParameters,
          div_eq_mul_inv]
        ring
      · norm_num [dateTwoPortChainMatrix, sourceBridgeRegressionDateParameters,
          div_eq_mul_inv]

/-- DATE's source fields at `(a,b)=(1,0)` pin the two-port behavior orientation. -/
def sourceBridgeRegressionDateTwoPortFields : DateTwoPortFields where
  input := 1
  backwardInput := 0
  output := (5 / 4 : ℂ) * Complex.I
  forwardOutput := -(3 / 4 : ℂ) * Complex.I

/-- Direct expansion places the exact field fixture in DATE Def. 3's two-port behavior. -/
lemma sourceBridgeRegression_dateTwoPortBehavior :
    dateTwoPortBehavior sourceBridgeRegressionDateParameters
      sourceBridgeRegressionDateTwoPortFields := by
  constructor
  · norm_num [dateTwoPortBehavior, sourceBridgeRegressionDateParameters,
      sourceBridgeRegressionDateTwoPortFields, div_eq_mul_inv]
  · norm_num [dateTwoPortBehavior, sourceBridgeRegressionDateParameters,
      sourceBridgeRegressionDateTwoPortFields, div_eq_mul_inv]
    ring

/-- Direct phase expansion gives the DATE full-round-trip factor `-1`. -/
lemma sourceBridgeRegression_date_phaseFactor :
    sourceBridgeRegressionDateParameters.phaseFactor = -1 := by
  rw [DateParameters.phaseFactor, sourceBridgeRegression_date_roundTripPhase]
  norm_num [MatchedPropagation.carrierPhaseFactor]

/-- Direct phase expansion gives the DATE half-round-trip factor `-I`. -/
lemma sourceBridgeRegression_date_halfPhaseFactor :
    sourceBridgeRegressionDateParameters.halfPhaseFactor = -Complex.I := by
  rw [DateParameters.halfPhaseFactor, sourceBridgeRegression_date_roundTripPhase]
  norm_num [MatchedPropagation.carrierPhaseFactor]

/-- Direct expansion gives DATE's common four-port denominator `34/25`. -/
lemma sourceBridgeRegression_date_denominator :
    sourceBridgeRegressionDateParameters.denominator = 34 / 25 := by
  rw [DateParameters.denominator, sourceBridgeRegression_date_phaseFactor,
    sourceBridgeRegression_date_fieldAttenuation]
  norm_num [sourceBridgeRegressionDateParameters]

/-- Direct expansion gives DATE Def. 3's fields `R=-15/17` and `T=8I/17`. -/
lemma sourceBridgeRegression_dateFourPort_transfers :
    dateForwardTransfer sourceBridgeRegressionDateParameters = -15 / 17 ∧
      dateBackwardTransfer sourceBridgeRegressionDateParameters =
        (8 / 17 : ℂ) * Complex.I := by
  constructor
  · rw [dateForwardTransfer, sourceBridgeRegression_date_denominator,
      sourceBridgeRegression_date_phaseFactor,
      sourceBridgeRegression_date_fieldAttenuation]
    norm_num [sourceBridgeRegressionDateParameters]
  · rw [dateBackwardTransfer, sourceBridgeRegression_date_denominator,
      sourceBridgeRegression_date_halfPhaseFactor,
      sourceBridgeRegression_date_fieldAttenuation]
    norm_num [sourceBridgeRegressionDateParameters]
    ring

/-- Direct expansion pins all four entries of DATE Thm. 2 at the rational fixture. -/
lemma sourceBridgeRegression_dateFourPortChain_entries :
    dateFourPortChainMatrix sourceBridgeRegressionDateParameters 0 0 = -17 / 15 ∧
      dateFourPortChainMatrix sourceBridgeRegressionDateParameters 0 1 =
        (8 / 15 : ℂ) * Complex.I ∧
      dateFourPortChainMatrix sourceBridgeRegressionDateParameters 1 0 =
        -(8 / 15 : ℂ) * Complex.I ∧
      dateFourPortChainMatrix sourceBridgeRegressionDateParameters 1 1 = -17 / 15 := by
  rcases sourceBridgeRegression_dateFourPort_transfers with ⟨hForward, hBackward⟩
  constructor
  · norm_num [dateFourPortChainMatrix, hForward]
  · constructor
    · norm_num [dateFourPortChainMatrix, hForward, hBackward]
      ring
    · constructor
      · norm_num [dateFourPortChainMatrix, hForward, hBackward]
        ring
      · norm_num [dateFourPortChainMatrix, hForward, hBackward]
        field_simp
        rw [Complex.I_sq]
        ring

/-! ## B. SysCon amplitude, power, and series -/

/-- Exact SysCon 3-4-5 data at zero phase and source scalar `x_r=1/4`. -/
def sourceBridgeRegressionSysConParameters : SysConParameters where
  phase := 0
  fieldAttenuation := 1 / 4
  inputCrossAmplitude := 4 / 5
  dropCrossAmplitude := 4 / 5
  inputThroughAmplitude := 3 / 5
  dropThroughAmplitude := 3 / 5

/-- Direct expansion gives the SysCon zero-phase half-arc coefficient `1/2`. -/
lemma sourceBridgeRegression_sysCon_halfArcCoefficient :
    sourceBridgeRegressionSysConParameters.halfArcCoefficient = 1 / 2 := by
  have hSqrt : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
    apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2
    norm_num
  norm_num [SysConParameters.halfArcCoefficient,
    sourceBridgeRegressionSysConParameters,
    MatchedPropagation.carrierPhaseFactor, hSqrt]

/-- Direct expansion gives the SysCon zero-phase loop gain `9/100`. -/
lemma sourceBridgeRegression_sysCon_loopGain :
    sourceBridgeRegressionSysConParameters.loopGain = 9 / 100 := by
  norm_num [SysConParameters.loopGain, sourceBridgeRegressionSysConParameters,
    MatchedPropagation.carrierPhaseFactor]

/-- Direct expansion gives the SysCon zero-phase denominator `91/100`. -/
lemma sourceBridgeRegression_sysCon_denominator :
    sourceBridgeRegressionSysConParameters.denominator = 91 / 100 := by
  rw [SysConParameters.denominator, sourceBridgeRegression_sysCon_loopGain]
  norm_num

/-- Direct expansion gives SysCon Thm. 5's zero-phase drop field `-32/91`. -/
lemma sourceBridgeRegression_sysCon_resonance_transfer :
    sysConDropTransfer sourceBridgeRegressionSysConParameters = -32 / 91 := by
  have hSqrt : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
    apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2
    norm_num
  rw [sysConDropTransfer, sourceBridgeRegression_sysCon_denominator]
  norm_num [sourceBridgeRegressionSysConParameters,
    SysConParameters.halfArcCoefficient,
    MatchedPropagation.carrierPhaseFactor, hSqrt]

/-- Direct use of the concrete geometric sum gives the Def. 9 response `-32/91`. -/
lemma sourceBridgeRegression_sysCon_resonance_series :
    sysConDropResponseSeries sourceBridgeRegressionSysConParameters = -32 / 91 := by
  have hNorm : ‖(9 / 100 : ℂ)‖ < 1 := by norm_num
  rw [sysConDropResponseSeries, sourceBridgeRegression_sysCon_loopGain,
    tsum_geometric_of_norm_lt_one hNorm,
    sourceBridgeRegression_sysCon_halfArcCoefficient]
  norm_num [sourceBridgeRegressionSysConParameters]
  field_simp
  rw [Complex.I_sq]
  ring

/-- Direct norm-square expansion gives the zero-phase drop power `1024/8281`. -/
lemma sourceBridgeRegression_sysCon_resonance_power :
    sysConDropPower sourceBridgeRegressionSysConParameters = 1024 / 8281 := by
  rw [sysConDropPower, sourceBridgeRegression_sysCon_resonance_transfer]
  norm_num [Complex.normSq_apply]

/-- Exact SysCon 3-4-5 data at the named antiresonance. -/
def sourceBridgeRegressionSysConAntiresonance : SysConParameters :=
  { sourceBridgeRegressionSysConParameters with phase := Real.pi }

/-- Direct expansion gives SysCon Thm. 5's antiresonant field `32I/109`. -/
lemma sourceBridgeRegression_sysCon_antiresonance_transfer :
    sysConDropTransfer sourceBridgeRegressionSysConAntiresonance =
      (32 / 109 : ℂ) * Complex.I := by
  have hSqrt : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
    apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2
    norm_num
  norm_num [sysConDropTransfer, SysConParameters.denominator,
    SysConParameters.loopGain, sourceBridgeRegressionSysConAntiresonance,
    sourceBridgeRegressionSysConParameters, MatchedPropagation.carrierPhaseFactor, hSqrt]
  ring

/-- Direct norm-square expansion gives the antiresonant drop power `1024/11881`. -/
lemma sourceBridgeRegression_sysCon_antiresonance_power :
    sysConDropPower sourceBridgeRegressionSysConAntiresonance = 1024 / 11881 := by
  rw [sysConDropPower, sourceBridgeRegression_sysCon_antiresonance_transfer]
  norm_num [Complex.normSq_apply]

/-- Direct expansion gives Def. 11's printed `2*pi` resonance power. -/
lemma sourceBridgeRegression_sysCon_def11_resonance_power :
    sysConDropPower sourceBridgeRegressionSysConParameters.atResonance =
      1024 / 8281 := by
  have hSqrt : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
    apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2
    norm_num
  norm_num [sysConDropPower, sysConDropTransfer, SysConParameters.denominator,
    SysConParameters.loopGain, SysConParameters.atResonance,
    sourceBridgeRegressionSysConParameters, MatchedPropagation.carrierPhaseFactor, hSqrt,
    Complex.normSq_apply]

/-- Direct expansion of Def. 11 gives the same ratio argument as SysCon Thm. 7. -/
lemma sourceBridgeRegression_sysCon_rejection_ratio :
    sysConRejectionRatioInBase 10 sourceBridgeRegressionSysConParameters =
      10 * Real.logb 10 (11881 / 8281) := by
  rw [sysConRejectionRatioInBase, powerRatioInBase,
    sourceBridgeRegression_sysCon_def11_resonance_power]
  have hAntiresonance :
      sysConDropPower sourceBridgeRegressionSysConParameters.atAntiresonance =
        1024 / 11881 := by
    simpa [SysConParameters.atAntiresonance,
      sourceBridgeRegressionSysConAntiresonance] using
        sourceBridgeRegression_sysCon_antiresonance_power
  rw [hAntiresonance]
  norm_num

/-- Direct expansion pins SysCon Thm. 7's base-ten closed form at the 3-4-5 point. -/
lemma sourceBridgeRegression_sysCon_rejection_closedForm :
    sysConRejectionClosedForm 10 sourceBridgeRegressionSysConParameters =
      10 * Real.logb 10 (11881 / 8281) := by
  norm_num [sysConRejectionClosedForm, sourceBridgeRegressionSysConParameters]

/-! ## C. Provenance-uncertain power-denominator candidate -/

/-- A valid rational 3-4-5 coupler point where the two candidate denominators differ. -/
def sourceBridgeRegressionDisputedPowerParameters : SysConParameters where
  phase := Real.pi
  fieldAttenuation := 9 / 16
  inputCrossAmplitude := 3 / 5
  dropCrossAmplitude := 3 / 5
  inputThroughAmplitude := 4 / 5
  dropThroughAmplitude := 4 / 5

/-- The norm-square denominator is exactly `1156/625` at the mismatch point. -/
lemma sourceBridgeRegression_amplitudePowerDenominator :
    sysConAmplitudePowerDenominator sourceBridgeRegressionDisputedPowerParameters =
      1156 / 625 := by
  norm_num [sysConAmplitudePowerDenominator, SysConParameters.realLoopGain,
    sourceBridgeRegressionDisputedPowerParameters]

/-- The provenance-uncertain denominator candidate retains an `exp(-pi)` term. -/
lemma sourceBridgeRegression_disputedPowerDenominator :
    sysConDisputedPowerDenominator sourceBridgeRegressionDisputedPowerParameters =
      256 / 625 + 36 / 25 * Real.exp (-Real.pi) := by
  norm_num [sysConDisputedPowerDenominator, SysConParameters.realLoopGain,
    sourceBridgeRegressionDisputedPowerParameters]

/-- The provenance-uncertain denominator candidate is not the norm-square of Thm. 5. -/
lemma sourceBridgeRegression_disputedDenominator_ne_amplitudeDenominator :
    sysConDisputedPowerDenominator sourceBridgeRegressionDisputedPowerParameters ≠
      sysConAmplitudePowerDenominator sourceBridgeRegressionDisputedPowerParameters := by
  rw [sourceBridgeRegression_disputedPowerDenominator,
    sourceBridgeRegression_amplitudePowerDenominator]
  have hExp : Real.exp (-Real.pi) ≠ 1 := by
    intro hEqual
    have hZero : -Real.pi = 0 := (Real.exp_eq_one_iff (-Real.pi)).mp hEqual
    exact Real.pi_ne_zero (neg_eq_zero.mp hZero)
  intro hEqual
  apply hExp
  linarith

/-! ## D. SFG-TR transfer formula -/

/-- Exact SFG-TR coefficients matching the zero-phase SysCon 3-4-5 point. -/
def sourceBridgeRegressionSfgParameters : SfgParameters where
  roundTripCoefficient := 1 / 4
  inputCrossAmplitude := 4 / 5
  dropCrossAmplitude := 4 / 5
  inputThroughAmplitude := 3 / 5
  dropThroughAmplitude := 3 / 5

/-- Direct expansion gives SFG-TR Thm. 7's add-drop field `-32/91`. -/
lemma sourceBridgeRegression_sfg_transfer :
    sfgAddDropTransfer sourceBridgeRegressionSfgParameters = -32 / 91 := by
  have hRealSqrt : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
    apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2
    norm_num
  have hSqrt : Complex.sqrt (1 / 4) = 1 / 2 := by
    have hNonneg : (0 : ℂ) ≤ 1 / 4 := by
      norm_num [Complex.nonneg_iff]
    calc
      Complex.sqrt (1 / 4) = (Real.sqrt (1 / 4 : ℝ) : ℂ) := by
        rw [Complex.sqrt_of_nonneg hNonneg]
        norm_num
      _ = 1 / 2 := by rw [hRealSqrt]; norm_num
  rw [sfgAddDropTransfer]
  norm_num [sourceBridgeRegressionSfgParameters, hSqrt]

end MicroringSourceBridge

end

end Optics
