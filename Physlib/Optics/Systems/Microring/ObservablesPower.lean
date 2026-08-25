/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Physlib.Optics.Components.DirectionalCouplerPhysicalPower
public import Physlib.Optics.Components.MatchedPropagationPhysicalPower
public import Physlib.Optics.Network.Coherency
public import Physlib.Optics.Systems.Microring.AddDrop

/-!
# Add-drop microring power observables

## i. Overview

This file derives normalized through/drop powers from the N5 add-drop response proved at
`Physlib/Optics/Systems/Microring/AddDrop.lean:635-725` and proves lossless power balance through
N6. The N7 coupler cross coefficient is the pinned `-I * k` at
`Physlib/Optics/Components/DirectionalCoupler.lean:68-70`. Component losslessness is supplied by
`DirectionalCoupler.physicalScattering_isLossless` and
`MatchedPropagation.physicalScattering_isLossless` at
`Physlib/Optics/Components/DirectionalCouplerPhysicalPower.lean:71-75` and
`Physlib/Optics/Components/MatchedPropagationPhysicalPower.lean:84-90`.

System losslessness is obtained only through
`FlatNetlist.externalScatteringMatrix_isLossless_of_components_isLossless`, whose component and
well-posedness gates are at `Physlib/Optics/Network/Conservation.lean:543-553`. Coherent and
incoherent second-order outputs use `FlatNetlist.responseCoherency`, defined at
`Physlib/Optics/Network/Coherency.lean:450-478`.

Resonance and antiresonance below are named phase-factor conditions, not extrema theorems.
Critical coupling and extinction are exact amplitude statements at the named resonance. The
through and drop rejection ratios use `10 * logb 10` for a positive power ratio; their totalized
scalar definitions have no decibel interpretation unless both powers are positive.
Parameter-recovery results require
phase-resolved field data or a stated critical-coupling hypothesis. They do not claim that
intensity-only data identify an amplitude sign or phase.

The underlying `throughTransfer` and `dropTransfer` are totalized algebraic quotients at
`Physlib/Optics/Systems/Microring/AddDropNetwork.lean:275-285`. Consequently `throughPower` and
`dropPower` are totalized squared-modulus objects. The ungated `dropPower_eq_closedForm` is only an
identity between those totalized objects; neither side denotes a physical network response at a
zero feedback denominator or outside component validity. Physical pointwise power claims are
made only through the response-domain-gated N5F results in `ObservablesFrequency`.

Powers are normalized modal powers, not electromagnetic powers without a separate Poynting
normalization. This fixed-frequency file makes no bandwidth, linewidth, quality-factor,
group-delay, dispersion, thermal, nonlinear, fabrication, or free-spectral-range claim. Frequency
response and free spectral range are handled by the proof-gated N5F response in
`ObservablesFrequency`.

## ii. Key results

- `AddDrop.throughPower_eq_closedForm` and `dropPower_eq_closedForm`: exact algebraic power forms.
- `AddDrop.lossless_through_drop_power_balance`: N6-derived one-input power conservation.
- `AddDrop.criticalCoupling_extinction`: the standard resonant extinction result.
- `AddDrop.attenuation_eq_of_antiresonant_field`: gated field-amplitude recovery.
- `AddDrop.dropRejectionRatioDB_eq_logb_sub`: the gated drop-port decibel convention.

## iii. Table of contents

- A. Closed-form through and drop powers
- B. Named phase conditions and critical coupling
- C. Positive-power rejection ratio and parameter recovery
- D. N6 losslessness and coherency

## iv. References

The N5, N6, and N7 declaration locations used by this file are quoted above. Source-parity bridges
and intensity-only identifiability are not claimed here.
-/

@[expose] public section

namespace Optics

noncomputable section

namespace AddDrop

/-! ## A. Closed-form through and drop powers -/

/-- The unit-modulus round-trip phase factor selected by the real phase lift. -/
def Parameters.phaseFactor (p : Parameters) : ℂ :=
  MatchedPropagation.carrierPhaseFactor ((p.roundTripPhase : ℝ) : Real.Angle)

/-- The selected phase factor has real part `cos phi` and imaginary part `-sin phi`. -/
lemma Parameters.phaseFactor_eq_cos_sub_sin_mul_I (p : Parameters) :
    p.phaseFactor =
      (Real.cos p.roundTripPhase : ℂ) -
        (Real.sin p.roundTripPhase : ℂ) * Complex.I := by
  rw [Parameters.phaseFactor, MatchedPropagation.carrierPhaseFactor,
    Real.Angle.coe_toCircle]
  simp [sub_eq_add_neg]

/-- The real squared modulus of the feedback denominator. -/
def Parameters.powerDenominator (p : Parameters) : ℝ :=
  1 + (p.inputThroughAmplitude * p.dropThroughAmplitude * p.fieldAttenuation) ^ 2 -
    2 * p.inputThroughAmplitude * p.dropThroughAmplitude * p.fieldAttenuation *
      Real.cos p.roundTripPhase

/-- The real squared modulus of the conventional through numerator. -/
def Parameters.throughPowerNumerator (p : Parameters) : ℝ :=
  p.inputThroughAmplitude ^ 2 +
    (p.dropThroughAmplitude * p.fieldAttenuation) ^ 2 -
      2 * p.inputThroughAmplitude * p.dropThroughAmplitude * p.fieldAttenuation *
        Real.cos p.roundTripPhase

/-- The real squared modulus of the conventional drop numerator. -/
def Parameters.dropPowerNumerator (p : Parameters) : ℝ :=
  p.inputCrossAmplitude ^ 2 * p.dropCrossAmplitude ^ 2 * p.fieldAttenuation

/-- The totalized squared modulus of the algebraic input-to-through transfer.

It has physical-response meaning only when the network solve and component-validity gates hold.
-/
def throughPower (p : Parameters) : ℝ :=
  Complex.normSq (throughTransfer p)

/-- The totalized squared modulus of the algebraic input-to-drop transfer.

It has physical-response meaning only when the network solve and component-validity gates hold.
-/
def dropPower (p : Parameters) : ℝ :=
  Complex.normSq (dropTransfer p)

/-- Normalized through power is nonnegative. -/
lemma throughPower_nonneg (p : Parameters) : 0 ≤ throughPower p :=
  Complex.normSq_nonneg (throughTransfer p)

/-- Normalized drop power is nonnegative. -/
lemma dropPower_nonneg (p : Parameters) : 0 ≤ dropPower p :=
  Complex.normSq_nonneg (dropTransfer p)

/-- Through power is positive exactly when the totalized through field is nonzero. -/
lemma throughPower_pos_iff (p : Parameters) :
    0 < throughPower p ↔ throughTransfer p ≠ 0 :=
  Complex.normSq_pos

/-- Drop power is positive exactly when the totalized drop field is nonzero. -/
lemma dropPower_pos_iff (p : Parameters) :
    0 < dropPower p ↔ dropTransfer p ≠ 0 :=
  Complex.normSq_pos

/-- Nonnegative attenuation turns the stored round-trip coefficient into the selected phase
factor times the declared field factor. -/
lemma Parameters.roundTripCoefficient_eq_field_mul_phaseFactor (p : Parameters)
    (hAttenuation : 0 ≤ p.fieldAttenuation) :
    p.roundTripCoefficient = (p.fieldAttenuation : ℂ) * p.phaseFactor := by
  simpa only [Parameters.phaseFactor] using
    p.roundTripCoefficient_eq_fieldAttenuation hAttenuation

/-- The N5 feedback denominator has the displayed real squared modulus. -/
lemma Parameters.normSq_denominator (p : Parameters)
    (hAttenuation : 0 ≤ p.fieldAttenuation) :
    Complex.normSq p.denominator = p.powerDenominator := by
  rw [Parameters.denominator, Parameters.loopGain,
    p.roundTripCoefficient_eq_field_mul_phaseFactor hAttenuation,
    p.phaseFactor_eq_cos_sub_sin_mul_I]
  simp [Parameters.powerDenominator, Complex.normSq_apply,
    Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  nlinarith [Real.sin_sq_add_cos_sq p.roundTripPhase]

/-- A nonzero feedback denominator has strictly positive real squared modulus. -/
lemma Parameters.powerDenominator_pos (p : Parameters)
    (hAttenuation : 0 ≤ p.fieldAttenuation)
    (hDenominator : p.HasNonzeroDenominator) : 0 < p.powerDenominator := by
  rw [← p.normSq_denominator hAttenuation]
  exact Complex.normSq_pos.mpr hDenominator

/-- The conventional through numerator has the displayed real squared modulus. -/
lemma Parameters.normSq_throughNumerator (p : Parameters)
    (hAttenuation : 0 ≤ p.fieldAttenuation) :
    Complex.normSq
        ((p.inputThroughAmplitude : ℂ) -
          (p.dropThroughAmplitude : ℂ) * p.roundTripCoefficient) =
      p.throughPowerNumerator := by
  rw [p.roundTripCoefficient_eq_field_mul_phaseFactor hAttenuation,
    p.phaseFactor_eq_cos_sub_sin_mul_I]
  simp [Parameters.throughPowerNumerator, Complex.normSq_apply,
    Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  nlinarith [Real.sin_sq_add_cos_sq p.roundTripPhase]

/-- The conventional drop numerator has the displayed real squared modulus. -/
lemma Parameters.normSq_dropNumerator (p : Parameters)
    (hAttenuation : 0 ≤ p.fieldAttenuation) :
    Complex.normSq
        (-((p.inputCrossAmplitude : ℂ) * (p.dropCrossAmplitude : ℂ) *
          p.firstArcCoefficient)) = p.dropPowerNumerator := by
  rw [Complex.normSq_neg, Complex.normSq_mul, Complex.normSq_mul,
    Complex.normSq_ofReal, Complex.normSq_ofReal, Parameters.firstArcCoefficient,
    MatchedPropagation.normSq_transmissionCoefficient]
  rw [Parameters.firstPropagation, p.halfArcAttenuation_sq hAttenuation]
  simp only [Parameters.dropPowerNumerator]
  ring

/-- Nonzero cross amplitudes and positive field attenuation give a positive drop numerator. -/
lemma Parameters.dropPowerNumerator_pos (p : Parameters)
    (hInputCross : p.inputCrossAmplitude ≠ 0)
    (hDropCross : p.dropCrossAmplitude ≠ 0)
    (hAttenuation : 0 < p.fieldAttenuation) : 0 < p.dropPowerNumerator := by
  rw [Parameters.dropPowerNumerator]
  exact mul_pos (mul_pos (sq_pos_of_ne_zero hInputCross)
    (sq_pos_of_ne_zero hDropCross)) hAttenuation

/-- On the nonzero-denominator algebraic domain, the through amplitude yields the standard
closed-form power. Physical-response meaning additionally requires component validity. -/
theorem throughPower_eq_closedForm (p : Parameters)
    (hInputUnitary : p.inputCoupler.IsUnitary)
    (hAttenuation : 0 ≤ p.fieldAttenuation)
    (hDenominator : p.HasNonzeroDenominator) :
    throughPower p = p.throughPowerNumerator / p.powerDenominator := by
  rw [throughPower, throughTransfer_eq_standard p hInputUnitary hDenominator,
    standardThroughTransfer, Complex.normSq_div,
    p.normSq_throughNumerator hAttenuation,
    p.normSq_denominator hAttenuation]

/-- The totalized drop amplitude yields the standard totalized closed-form quotient.

This algebraic identity needs no solve gate, but neither side is asserted to be a physical response
outside the solve and component-validity domains.
-/
theorem dropPower_eq_closedForm (p : Parameters)
    (hAttenuation : 0 ≤ p.fieldAttenuation) :
    dropPower p = p.dropPowerNumerator / p.powerDenominator := by
  rw [dropPower, dropTransfer_eq_standard, standardDropTransfer,
    Complex.normSq_div, p.normSq_dropNumerator hAttenuation,
    p.normSq_denominator hAttenuation]

/-! ## B. Named phase conditions and critical coupling -/

/-- The named resonance condition: the complete round-trip phase factor is one. -/
def Parameters.IsResonant (p : Parameters) : Prop :=
  p.phaseFactor = 1

/-- The named antiresonance condition: the complete round-trip phase factor is minus one. -/
def Parameters.IsAntiresonant (p : Parameters) : Prop :=
  p.phaseFactor = -1

/-- A zero real phase lift satisfies the named resonance condition. -/
lemma Parameters.isResonant_of_roundTripPhase_eq_zero {p : Parameters}
    (hPhase : p.roundTripPhase = 0) : p.IsResonant := by
  rw [Parameters.IsResonant, Parameters.phaseFactor, hPhase]
  simp [MatchedPropagation.carrierPhaseFactor]

/-- A real phase lift of `pi` satisfies the named antiresonance condition. -/
lemma Parameters.isAntiresonant_of_roundTripPhase_eq_pi {p : Parameters}
    (hPhase : p.roundTripPhase = Real.pi) : p.IsAntiresonant := by
  rw [Parameters.IsAntiresonant, Parameters.phaseFactor, hPhase,
    MatchedPropagation.carrierPhaseFactor, Real.Angle.neg_coe_pi,
    Real.Angle.coe_toCircle]
  simp

/-- The named resonance condition forces the cosine of the selected lift to be one. -/
lemma Parameters.cos_eq_one_of_isResonant {p : Parameters} (hp : p.IsResonant) :
    Real.cos p.roundTripPhase = 1 := by
  have hReal := congrArg Complex.re hp
  simpa [Parameters.IsResonant, p.phaseFactor_eq_cos_sub_sin_mul_I,
    Complex.cos_ofReal_re] using hReal

/-- The named antiresonance condition forces the cosine of the selected lift to be minus one. -/
lemma Parameters.cos_eq_neg_one_of_isAntiresonant {p : Parameters}
    (hp : p.IsAntiresonant) : Real.cos p.roundTripPhase = -1 := by
  have hReal := congrArg Complex.re hp
  simpa [Parameters.IsAntiresonant, p.phaseFactor_eq_cos_sub_sin_mul_I,
    Complex.cos_ofReal_re] using hReal

/-- At named resonance, the power denominator is a real square. -/
lemma Parameters.powerDenominator_of_isResonant {p : Parameters} (hp : p.IsResonant) :
    p.powerDenominator =
      (1 - p.inputThroughAmplitude * p.dropThroughAmplitude * p.fieldAttenuation) ^ 2 := by
  rw [Parameters.powerDenominator, Parameters.cos_eq_one_of_isResonant hp]
  ring

/-- At named antiresonance, the power denominator is a real square. -/
lemma Parameters.powerDenominator_of_isAntiresonant {p : Parameters}
    (hp : p.IsAntiresonant) :
    p.powerDenominator =
      (1 + p.inputThroughAmplitude * p.dropThroughAmplitude * p.fieldAttenuation) ^ 2 := by
  rw [Parameters.powerDenominator, Parameters.cos_eq_neg_one_of_isAntiresonant hp]
  ring

/-- At named resonance, the through-power numerator is a real square. -/
lemma Parameters.throughPowerNumerator_of_isResonant {p : Parameters}
    (hp : p.IsResonant) :
    p.throughPowerNumerator =
      (p.inputThroughAmplitude -
        p.dropThroughAmplitude * p.fieldAttenuation) ^ 2 := by
  rw [Parameters.throughPowerNumerator, Parameters.cos_eq_one_of_isResonant hp]
  ring

/-- At named antiresonance, the through-power numerator is a real square. -/
lemma Parameters.throughPowerNumerator_of_isAntiresonant {p : Parameters}
    (hp : p.IsAntiresonant) :
    p.throughPowerNumerator =
      (p.inputThroughAmplitude +
        p.dropThroughAmplitude * p.fieldAttenuation) ^ 2 := by
  rw [Parameters.throughPowerNumerator,
    Parameters.cos_eq_neg_one_of_isAntiresonant hp]
  ring

/-- The named-resonance through-power response. This is a phase-point identity, not an extremum
claim. -/
lemma throughPower_of_isResonant (p : Parameters)
    (hInputUnitary : p.inputCoupler.IsUnitary)
    (hAttenuation : 0 ≤ p.fieldAttenuation)
    (hDenominator : p.HasNonzeroDenominator) (hResonant : p.IsResonant) :
    throughPower p =
      (p.inputThroughAmplitude -
          p.dropThroughAmplitude * p.fieldAttenuation) ^ 2 /
        (1 - p.inputThroughAmplitude * p.dropThroughAmplitude *
          p.fieldAttenuation) ^ 2 := by
  rw [throughPower_eq_closedForm p hInputUnitary hAttenuation hDenominator,
    Parameters.throughPowerNumerator_of_isResonant hResonant,
    Parameters.powerDenominator_of_isResonant hResonant]

/-- The named-antiresonance through-power response. This is a phase-point identity, not an
extremum claim. -/
lemma throughPower_of_isAntiresonant (p : Parameters)
    (hInputUnitary : p.inputCoupler.IsUnitary)
    (hAttenuation : 0 ≤ p.fieldAttenuation)
    (hDenominator : p.HasNonzeroDenominator) (hAntiresonant : p.IsAntiresonant) :
    throughPower p =
      (p.inputThroughAmplitude +
          p.dropThroughAmplitude * p.fieldAttenuation) ^ 2 /
        (1 + p.inputThroughAmplitude * p.dropThroughAmplitude *
          p.fieldAttenuation) ^ 2 := by
  rw [throughPower_eq_closedForm p hInputUnitary hAttenuation hDenominator,
    Parameters.throughPowerNumerator_of_isAntiresonant hAntiresonant,
    Parameters.powerDenominator_of_isAntiresonant hAntiresonant]

/-- The named-resonance totalized drop-power identity. It is a physical response only on the
solve and component-validity domains. -/
lemma dropPower_of_isResonant (p : Parameters) (hAttenuation : 0 ≤ p.fieldAttenuation)
    (hResonant : p.IsResonant) :
    dropPower p =
      p.dropPowerNumerator /
        (1 - p.inputThroughAmplitude * p.dropThroughAmplitude *
          p.fieldAttenuation) ^ 2 := by
  rw [dropPower_eq_closedForm p hAttenuation,
    Parameters.powerDenominator_of_isResonant hResonant]

/-- The named-antiresonance totalized drop-power identity. It is a physical response only on the
solve and component-validity domains. -/
lemma dropPower_of_isAntiresonant (p : Parameters)
    (hAttenuation : 0 ≤ p.fieldAttenuation) (hAntiresonant : p.IsAntiresonant) :
    dropPower p =
      p.dropPowerNumerator /
        (1 + p.inputThroughAmplitude * p.dropThroughAmplitude *
          p.fieldAttenuation) ^ 2 := by
  rw [dropPower_eq_closedForm p hAttenuation,
    Parameters.powerDenominator_of_isAntiresonant hAntiresonant]

/-- Critical coupling equates the direct through amplitude with the attenuated return amplitude. -/
def Parameters.IsCriticallyCoupled (p : Parameters) : Prop :=
  p.inputThroughAmplitude = p.dropThroughAmplitude * p.fieldAttenuation

/-- At the named resonance, critical coupling gives exact through-port extinction. -/
theorem criticalCoupling_extinction (p : Parameters)
    (hInputUnitary : p.inputCoupler.IsUnitary)
    (hAttenuation : 0 ≤ p.fieldAttenuation)
    (hDenominator : p.HasNonzeroDenominator) (hResonant : p.IsResonant)
    (hCritical : p.IsCriticallyCoupled) :
    throughTransfer p = 0 := by
  rw [throughTransfer_eq_standard p hInputUnitary hDenominator,
    standardThroughTransfer,
    p.roundTripCoefficient_eq_field_mul_phaseFactor hAttenuation,
    hResonant]
  rw [hCritical]
  push_cast
  ring

/-- Critical coupling therefore gives zero normalized through power at the named resonance. -/
lemma criticalCoupling_throughPower_eq_zero (p : Parameters)
    (hInputUnitary : p.inputCoupler.IsUnitary)
    (hAttenuation : 0 ≤ p.fieldAttenuation)
    (hDenominator : p.HasNonzeroDenominator) (hResonant : p.IsResonant)
    (hCritical : p.IsCriticallyCoupled) :
    throughPower p = 0 := by
  rw [throughPower, criticalCoupling_extinction p hInputUnitary hAttenuation
    hDenominator hResonant hCritical, Complex.normSq_zero]

/-- At named resonance, exact through extinction recovers the critical-coupling equality. -/
lemma criticalCoupling_of_extinction (p : Parameters)
    (hInputUnitary : p.inputCoupler.IsUnitary)
    (hAttenuation : 0 ≤ p.fieldAttenuation)
    (hDenominator : p.HasNonzeroDenominator) (hResonant : p.IsResonant)
    (hExtinction : throughTransfer p = 0) :
    p.IsCriticallyCoupled := by
  rw [throughTransfer_eq_standard p hInputUnitary hDenominator,
    standardThroughTransfer,
    p.roundTripCoefficient_eq_field_mul_phaseFactor hAttenuation,
    hResonant] at hExtinction
  have hNumerator := congrArg (fun value : ℂ => value * p.denominator) hExtinction
  rw [div_mul_cancel₀ _ hDenominator, zero_mul] at hNumerator
  rw [Parameters.IsCriticallyCoupled]
  have hNumerator' :
      (p.inputThroughAmplitude : ℂ) -
        ((p.dropThroughAmplitude * p.fieldAttenuation : ℝ) : ℂ) = 0 := by
    simpa only [Complex.ofReal_mul, mul_one] using hNumerator
  exact_mod_cast sub_eq_zero.mp hNumerator'

/-! ## C. Positive-power rejection ratio and parameter recovery -/

/-- Power-ratio decibels, using the convention `10 * logb 10 (numerator / denominator)`.

The function is totalized because `Real.logb` is totalized. A rejection-ratio interpretation is
asserted only by results carrying strictly positive numerator and denominator hypotheses.
-/
def powerRatioDB (numerator denominator : ℝ) : ℝ :=
  10 * Real.logb 10 (numerator / denominator)

/-- On positive powers, the decibel convention is the difference of the two base-ten logarithms. -/
lemma powerRatioDB_eq_logb_sub (numerator denominator : ℝ)
    (hNumerator : 0 < numerator) (hDenominator : 0 < denominator) :
    powerRatioDB numerator denominator =
      10 * (Real.logb 10 numerator - Real.logb 10 denominator) := by
  rw [powerRatioDB, Real.logb_div hNumerator.ne' hDenominator.ne']

/-- The same ring data evaluated at the zero-phase named resonance. -/
def Parameters.atResonance (p : Parameters) : Parameters :=
  { p with roundTripPhase := 0 }

/-- The same ring data evaluated at the half-turn named antiresonance. -/
def Parameters.atAntiresonance (p : Parameters) : Parameters :=
  { p with roundTripPhase := Real.pi }

/-- The zero-phase specialization satisfies the named resonance condition. -/
lemma Parameters.atResonance_isResonant (p : Parameters) : p.atResonance.IsResonant :=
  Parameters.isResonant_of_roundTripPhase_eq_zero rfl

/-- The half-turn specialization satisfies the named antiresonance condition. -/
lemma Parameters.atAntiresonance_isAntiresonant (p : Parameters) :
    p.atAntiresonance.IsAntiresonant :=
  Parameters.isAntiresonant_of_roundTripPhase_eq_pi rfl

/-- Phase specialization leaves the input coupler unchanged. -/
lemma Parameters.atResonance_inputCoupler (p : Parameters) :
    p.atResonance.inputCoupler = p.inputCoupler := rfl

/-- Half-turn specialization leaves the input coupler unchanged. -/
lemma Parameters.atAntiresonance_inputCoupler (p : Parameters) :
    p.atAntiresonance.inputCoupler = p.inputCoupler := rfl

/-- Phase specialization leaves the field attenuation unchanged. -/
lemma Parameters.atResonance_fieldAttenuation (p : Parameters) :
    p.atResonance.fieldAttenuation = p.fieldAttenuation := rfl

/-- Half-turn specialization leaves the field attenuation unchanged. -/
lemma Parameters.atAntiresonance_fieldAttenuation (p : Parameters) :
    p.atAntiresonance.fieldAttenuation = p.fieldAttenuation := rfl

/-- The through-port rejection ratio compares named antiresonant power with named resonant power,
in that order, using the power-ratio decibel convention. -/
def throughRejectionRatioDB (p : Parameters) : ℝ :=
  powerRatioDB (throughPower p.atAntiresonance) (throughPower p.atResonance)

/-- With both solve gates, the rejection ratio is the decibel ratio of the two exact closed-form
power responses. -/
lemma throughRejectionRatioDB_eq_closedForm (p : Parameters)
    (hInputUnitary : p.inputCoupler.IsUnitary)
    (hAttenuation : 0 ≤ p.fieldAttenuation)
    (hResonanceDenominator : p.atResonance.HasNonzeroDenominator)
    (hAntiresonanceDenominator : p.atAntiresonance.HasNonzeroDenominator) :
    throughRejectionRatioDB p =
      powerRatioDB
        ((p.inputThroughAmplitude +
          p.dropThroughAmplitude * p.fieldAttenuation) ^ 2 /
            (1 + p.inputThroughAmplitude * p.dropThroughAmplitude *
              p.fieldAttenuation) ^ 2)
        ((p.inputThroughAmplitude -
          p.dropThroughAmplitude * p.fieldAttenuation) ^ 2 /
            (1 - p.inputThroughAmplitude * p.dropThroughAmplitude *
              p.fieldAttenuation) ^ 2) := by
  rw [throughRejectionRatioDB,
    throughPower_of_isAntiresonant p.atAntiresonance
      (by simpa only [Parameters.atAntiresonance_inputCoupler] using hInputUnitary)
      (by simpa only [Parameters.atAntiresonance_fieldAttenuation] using hAttenuation)
      hAntiresonanceDenominator p.atAntiresonance_isAntiresonant,
    throughPower_of_isResonant p.atResonance
      (by simpa only [Parameters.atResonance_inputCoupler] using hInputUnitary)
      (by simpa only [Parameters.atResonance_fieldAttenuation] using hAttenuation)
      hResonanceDenominator p.atResonance_isResonant]
  rfl

/-- With positive named-point powers, the rejection ratio is the difference of their base-ten
logarithms under the explicit power-ratio convention. -/
lemma throughRejectionRatioDB_eq_logb_sub (p : Parameters)
    (hAntiresonancePower : 0 < throughPower p.atAntiresonance)
    (hResonancePower : 0 < throughPower p.atResonance) :
    throughRejectionRatioDB p =
      10 * (Real.logb 10 (throughPower p.atAntiresonance) -
        Real.logb 10 (throughPower p.atResonance)) := by
  exact powerRatioDB_eq_logb_sub _ _ hAntiresonancePower hResonancePower

/-- The drop-port rejection ratio compares named resonant power with named antiresonant power,
in that order, using the power-ratio decibel convention. -/
def dropRejectionRatioDB (p : Parameters) : ℝ :=
  powerRatioDB (dropPower p.atResonance) (dropPower p.atAntiresonance)

/-- The totalized drop rejection ratio expands to the two named-phase drop-power quotients. -/
lemma dropRejectionRatioDB_eq_closedForm (p : Parameters)
    (hAttenuation : 0 ≤ p.fieldAttenuation) :
    dropRejectionRatioDB p =
      powerRatioDB
        (p.dropPowerNumerator /
          (1 - p.inputThroughAmplitude * p.dropThroughAmplitude *
            p.fieldAttenuation) ^ 2)
        (p.dropPowerNumerator /
          (1 + p.inputThroughAmplitude * p.dropThroughAmplitude *
            p.fieldAttenuation) ^ 2) := by
  rw [dropRejectionRatioDB,
    dropPower_of_isResonant p.atResonance
      (by simpa only [Parameters.atResonance_fieldAttenuation] using hAttenuation)
      p.atResonance_isResonant,
    dropPower_of_isAntiresonant p.atAntiresonance
      (by simpa only [Parameters.atAntiresonance_fieldAttenuation] using hAttenuation)
      p.atAntiresonance_isAntiresonant]
  rfl

/-- With nonzero coupling, positive attenuation, and both physical solve gates, the common drop
numerator cancels and leaves the antiresonant-to-resonant denominator ratio. -/
lemma dropRejectionRatioDB_eq_denominatorRatio (p : Parameters)
    (hAttenuation : 0 < p.fieldAttenuation)
    (hInputCross : p.inputCrossAmplitude ≠ 0)
    (hDropCross : p.dropCrossAmplitude ≠ 0)
    (hResonanceDenominator : p.atResonance.HasNonzeroDenominator)
    (hAntiresonanceDenominator : p.atAntiresonance.HasNonzeroDenominator) :
    dropRejectionRatioDB p =
      powerRatioDB
        ((1 + p.inputThroughAmplitude * p.dropThroughAmplitude *
          p.fieldAttenuation) ^ 2)
        ((1 - p.inputThroughAmplitude * p.dropThroughAmplitude *
          p.fieldAttenuation) ^ 2) := by
  have hNumerator := p.dropPowerNumerator_pos hInputCross hDropCross hAttenuation
  have hResonancePositive :=
    (p.atResonance).powerDenominator_pos
      (by simpa only [Parameters.atResonance_fieldAttenuation] using hAttenuation.le)
      hResonanceDenominator
  rw [(p.atResonance).powerDenominator_of_isResonant
    p.atResonance_isResonant] at hResonancePositive
  have hAntiresonancePositive :=
    (p.atAntiresonance).powerDenominator_pos
      (by simpa only [Parameters.atAntiresonance_fieldAttenuation] using hAttenuation.le)
      hAntiresonanceDenominator
  rw [(p.atAntiresonance).powerDenominator_of_isAntiresonant
    p.atAntiresonance_isAntiresonant] at hAntiresonancePositive
  simp only [Parameters.atResonance] at hResonancePositive
  simp only [Parameters.atAntiresonance] at hAntiresonancePositive
  rw [dropRejectionRatioDB_eq_closedForm p hAttenuation.le]
  apply congrArg (fun ratio => 10 * Real.logb 10 ratio)
  field_simp [hNumerator.ne', hResonancePositive.ne', hAntiresonancePositive.ne']

/-- Under the same positivity and solve hypotheses, the drop rejection ratio is the difference
of base-ten logarithms of its strictly positive denominator squares. -/
lemma dropRejectionRatioDB_eq_logb_sub (p : Parameters)
    (hAttenuation : 0 < p.fieldAttenuation)
    (hInputCross : p.inputCrossAmplitude ≠ 0)
    (hDropCross : p.dropCrossAmplitude ≠ 0)
    (hResonanceDenominator : p.atResonance.HasNonzeroDenominator)
    (hAntiresonanceDenominator : p.atAntiresonance.HasNonzeroDenominator) :
    dropRejectionRatioDB p =
      10 *
        (Real.logb 10
            ((1 + p.inputThroughAmplitude * p.dropThroughAmplitude *
              p.fieldAttenuation) ^ 2) -
          Real.logb 10
            ((1 - p.inputThroughAmplitude * p.dropThroughAmplitude *
              p.fieldAttenuation) ^ 2)) := by
  rw [dropRejectionRatioDB_eq_denominatorRatio p hAttenuation hInputCross hDropCross
    hResonanceDenominator hAntiresonanceDenominator]
  apply powerRatioDB_eq_logb_sub
  · have hPositive :=
      (p.atAntiresonance).powerDenominator_pos
        (by simpa only [Parameters.atAntiresonance_fieldAttenuation] using hAttenuation.le)
        hAntiresonanceDenominator
    rw [(p.atAntiresonance).powerDenominator_of_isAntiresonant
      p.atAntiresonance_isAntiresonant] at hPositive
    simpa only [Parameters.atAntiresonance] using hPositive
  · have hPositive :=
      (p.atResonance).powerDenominator_pos
        (by simpa only [Parameters.atResonance_fieldAttenuation] using hAttenuation.le)
        hResonanceDenominator
    rw [(p.atResonance).powerDenominator_of_isResonant
      p.atResonance_isResonant] at hPositive
    simpa only [Parameters.atResonance] using hPositive

/-- Critical coupling with nonzero drop-coupler through amplitude recovers the round-trip field
attenuation. -/
lemma fieldAttenuation_eq_of_criticalCoupling (p : Parameters)
    (hCritical : p.IsCriticallyCoupled) (hDrop : p.dropThroughAmplitude ≠ 0) :
    p.fieldAttenuation = p.inputThroughAmplitude / p.dropThroughAmplitude := by
  rw [Parameters.IsCriticallyCoupled] at hCritical
  apply (eq_div_iff hDrop).mpr
  simpa only [mul_comm] using hCritical.symm

/-- Input-coupler unitarity and critical coupling recover the squared cross amplitude. -/
lemma inputCrossAmplitude_sq_eq_of_criticalCoupling (p : Parameters)
    (hInputUnitary : p.inputCoupler.IsUnitary) (hCritical : p.IsCriticallyCoupled) :
    p.inputCrossAmplitude ^ 2 =
      1 - (p.dropThroughAmplitude * p.fieldAttenuation) ^ 2 := by
  rw [DirectionalCoupler.Parameters.IsUnitary,
    DirectionalCoupler.Parameters.powerFactor] at hInputUnitary
  rw [Parameters.IsCriticallyCoupled] at hCritical
  change p.inputThroughAmplitude ^ 2 + p.inputCrossAmplitude ^ 2 = 1 at hInputUnitary
  rw [hCritical] at hInputUnitary
  linarith

/-- Nonnegative cross amplitude removes the square-root sign ambiguity in critical-coupling
recovery. -/
lemma inputCrossAmplitude_eq_sqrt_of_criticalCoupling (p : Parameters)
    (hInputUnitary : p.inputCoupler.IsUnitary)
    (hCross : 0 ≤ p.inputCrossAmplitude) (hCritical : p.IsCriticallyCoupled) :
    p.inputCrossAmplitude =
      Real.sqrt (1 - (p.dropThroughAmplitude * p.fieldAttenuation) ^ 2) := by
  rw [← inputCrossAmplitude_sq_eq_of_criticalCoupling p hInputUnitary hCritical,
    Real.sqrt_sq hCross]

/-- Resonant extinction, with the stated normalization and solve gates, recovers the round-trip
field attenuation from the known coupler through amplitudes. -/
lemma fieldAttenuation_eq_of_resonant_extinction (p : Parameters)
    (hInputUnitary : p.inputCoupler.IsUnitary)
    (hAttenuation : 0 ≤ p.fieldAttenuation)
    (hDenominator : p.HasNonzeroDenominator) (hResonant : p.IsResonant)
    (hExtinction : throughTransfer p = 0) (hDrop : p.dropThroughAmplitude ≠ 0) :
    p.fieldAttenuation = p.inputThroughAmplitude / p.dropThroughAmplitude :=
  fieldAttenuation_eq_of_criticalCoupling p
    (criticalCoupling_of_extinction p hInputUnitary hAttenuation hDenominator
      hResonant hExtinction) hDrop

/-- A phase-resolved antiresonant through field recovers attenuation when the displayed
identifiability denominator is nonzero. This does not recover a field sign from intensity data. -/
lemma attenuation_eq_of_antiresonant_field (p : Parameters)
    (hInputUnitary : p.inputCoupler.IsUnitary)
    (hAttenuation : 0 ≤ p.fieldAttenuation)
    (hDenominator : p.HasNonzeroDenominator) (hAntiresonant : p.IsAntiresonant)
    (measuredField : ℝ) (hField : throughTransfer p = measuredField)
    (hIdentifiable :
      p.dropThroughAmplitude *
        (1 - measuredField * p.inputThroughAmplitude) ≠ 0) :
    p.fieldAttenuation =
      (measuredField - p.inputThroughAmplitude) /
        (p.dropThroughAmplitude *
          (1 - measuredField * p.inputThroughAmplitude)) := by
  rw [throughTransfer_eq_standard p hInputUnitary hDenominator,
    standardThroughTransfer] at hField
  have hCleared := congrArg (fun value : ℂ => value * p.denominator) hField
  rw [div_mul_cancel₀ _ hDenominator, Parameters.denominator,
    Parameters.loopGain,
    p.roundTripCoefficient_eq_field_mul_phaseFactor hAttenuation,
    hAntiresonant] at hCleared
  have hRealRaw :
      p.inputThroughAmplitude -
          p.dropThroughAmplitude * (p.fieldAttenuation * (-1)) =
        measuredField *
          (1 - p.inputThroughAmplitude * p.dropThroughAmplitude *
            (p.fieldAttenuation * (-1))) := by
    exact_mod_cast hCleared
  have hReal :
      p.inputThroughAmplitude +
          p.dropThroughAmplitude * p.fieldAttenuation =
        measuredField *
          (1 + p.inputThroughAmplitude * p.dropThroughAmplitude *
            p.fieldAttenuation) := by
    nlinarith [hRealRaw]
  apply (eq_div_iff hIdentifiable).mpr
  nlinarith

/-- Resonant extinction and a nonnegative cross amplitude recover that amplitude from the known
drop-coupler transmission and round-trip attenuation. -/
lemma inputCrossAmplitude_eq_sqrt_of_resonant_extinction (p : Parameters)
    (hInputUnitary : p.inputCoupler.IsUnitary)
    (hCross : 0 ≤ p.inputCrossAmplitude)
    (hAttenuation : 0 ≤ p.fieldAttenuation)
    (hDenominator : p.HasNonzeroDenominator) (hResonant : p.IsResonant)
    (hExtinction : throughTransfer p = 0) :
    p.inputCrossAmplitude =
      Real.sqrt (1 - (p.dropThroughAmplitude * p.fieldAttenuation) ^ 2) := by
  apply inputCrossAmplitude_eq_sqrt_of_criticalCoupling p hInputUnitary hCross
  exact criticalCoupling_of_extinction p hInputUnitary hAttenuation hDenominator
    hResonant hExtinction

/-! ## D. N6 losslessness and coherency -/

/-- Every N7 component of the ring preserves normalized modal power. -/
def Parameters.IsLossless (p : Parameters) : Prop :=
  p.inputCoupler.IsUnitary ∧ p.dropCoupler.IsUnitary ∧ p.fieldAttenuation = 1

/-- Lossless ring parameters classify every concrete N7 component as lossless. -/
lemma components_isLossless (p : Parameters) (hp : p.IsLossless) :
    ∀ component : Component, (componentScattering p component).IsLossless := by
  rcases hp with ⟨hInput, hDrop, hAttenuation⟩
  intro component
  cases component
  · exact DirectionalCoupler.physicalScattering_isLossless p.inputCoupler hInput
  · exact DirectionalCoupler.physicalScattering_isLossless p.dropCoupler hDrop
  · apply MatchedPropagation.physicalScattering_isLossless
    simp [Parameters.firstPropagation, Parameters.halfArcAttenuation, hAttenuation]
  · apply MatchedPropagation.physicalScattering_isLossless
    simp [Parameters.secondPropagation, Parameters.halfArcAttenuation, hAttenuation]

/-- N6 packages the well-posed lossless add-drop response as a lossless external scattering
matrix. -/
lemma externalScatteringMatrix_isLossless (p : Parameters) (hp : p.IsLossless)
    (hDenominator : p.HasNonzeroDenominator) :
    ((netlist p).externalScatteringMatrix
      (isWellPosed_of_hasNonzeroDenominator p hDenominator)).IsLossless := by
  apply (netlist p).externalScatteringMatrix_isLossless_of_components_isLossless
    (isWellPosed_of_hasNonzeroDenominator p hDenominator)
  intro component
  cases component <;> exact components_isLossless p hp _

/-- The N5 response preserves normalized modal power, obtained by unpacking only the N6 external
scattering theorem. -/
lemma responseTransform_isPowerPreserving (p : Parameters) (hp : p.IsLossless)
    (hDenominator : p.HasNonzeroDenominator) :
    ((netlist p).responseTransform
      (isWellPosed_of_hasNonzeroDenominator p hDenominator)).IsPowerPreserving := by
  have hExternal := externalScatteringMatrix_isLossless p hp hDenominator
  rw [ScatteringMatrix.isLossless_iff_isPowerPreserving] at hExternal
  change (((netlist p).responseTransform
    (isWellPosed_of_hasNonzeroDenominator p hDenominator)).reindex
      Incident.channelEquiv Outgoing.channelEquiv).IsPowerPreserving at hExternal
  exact (ModeTransform.isPowerPreserving_reindex_iff Incident.channelEquiv
    Outgoing.channelEquiv ((netlist p).responseTransform
      (isWellPosed_of_hasNonzeroDenominator p hDenominator))).mp hExternal

/-- The four external bus ports of the explicit add-drop network. -/
inductive ExternalPort
  | input
  | through
  | add
  | drop
  deriving DecidableEq

/-- The four external bus ports form a finite family. -/
instance : Fintype ExternalPort where
  elems := {.input, .through, .add, .drop}
  complete port := by cases port <;> simp

/-- The packaged external channel selected by a bus-port label. -/
def externalChannel (p : Parameters) : ExternalPort → (netlist p).ExternalChannel
  | .input => inputChannel p
  | .through => throughChannel p
  | .add => addChannel p
  | .drop => dropChannel p

/-- Distinct bus-port labels select distinct external channels. -/
lemma externalChannel_injective (p : Parameters) : Function.Injective (externalChannel p) := by
  intro first second hChannel
  have hValue := congrArg Subtype.val hChannel
  cases first <;> cases second
  all_goals first | rfl | cases hValue

/-- Every external netlist channel is one of the four bus ports. -/
lemma externalChannel_surjective (p : Parameters) : Function.Surjective (externalChannel p) := by
  rintro ⟨⟨⟨component, port⟩, mode⟩, hExternal⟩
  cases component
  · cases port <;> cases mode
    · exact ⟨.input, Subtype.ext (by rfl)⟩
    · exfalso
      apply hExternal
      exact ⟨⟨Connection.secondToInput, Sum.inr ()⟩, rfl⟩
    · exact ⟨.through, Subtype.ext (by rfl)⟩
    · exfalso
      apply hExternal
      exact ⟨⟨Connection.inputToFirst, Sum.inl ()⟩, rfl⟩
  · cases port <;> cases mode
    · exact ⟨.add, Subtype.ext (by rfl)⟩
    · exfalso
      apply hExternal
      exact ⟨⟨Connection.firstToDrop, Sum.inr ()⟩, rfl⟩
    · exact ⟨.drop, Subtype.ext (by rfl)⟩
    · exfalso
      apply hExternal
      exact ⟨⟨Connection.dropToSecond, Sum.inl ()⟩, rfl⟩
  · cases port <;> cases mode
    · exfalso
      apply hExternal
      exact ⟨⟨Connection.inputToFirst, Sum.inr ()⟩, rfl⟩
    · exfalso
      apply hExternal
      exact ⟨⟨Connection.firstToDrop, Sum.inl ()⟩, rfl⟩
  · cases port <;> cases mode
    · exfalso
      apply hExternal
      exact ⟨⟨Connection.dropToSecond, Sum.inr ()⟩, rfl⟩
    · exfalso
      apply hExternal
      exact ⟨⟨Connection.secondToInput, Sum.inl ()⟩, rfl⟩

/-- The four bus-port labels are exactly the external channel family. -/
noncomputable def externalChannelEquiv (p : Parameters) :
    ExternalPort ≃ (netlist p).ExternalChannel :=
  Equiv.ofBijective (externalChannel p)
    ⟨externalChannel_injective p, externalChannel_surjective p⟩

/-- Bus-port labels transported to nominal incident endpoints. -/
noncomputable def externalIncidentEquiv (p : Parameters) :
    ExternalPort ≃ (netlist p).ExternalIncident :=
  (externalChannelEquiv p).trans Incident.channelEquiv.symm

/-- Bus-port labels transported to nominal outgoing endpoints. -/
noncomputable def externalOutgoingEquiv (p : Parameters) :
    ExternalPort ≃ (netlist p).ExternalOutgoing :=
  (externalChannelEquiv p).trans Outgoing.channelEquiv.symm

/-- The incident endpoint equivalence packages the selected external channel. -/
@[simp]
lemma externalIncidentEquiv_apply (p : Parameters) (port : ExternalPort) :
    externalIncidentEquiv p port = Incident.mk (externalChannel p port) := rfl

/-- The outgoing endpoint equivalence packages the selected external channel. -/
@[simp]
lemma externalOutgoingEquiv_apply (p : Parameters) (port : ExternalPort) :
    externalOutgoingEquiv p port = Outgoing.mk (externalChannel p port) := rfl

/-- A sum over the four named bus ports in their declared order. -/
lemma sum_externalPort (value : ExternalPort → ℝ) :
    ∑ port, value port =
      value .input + value .through + value .add + value .drop := by
  classical
  rw [show (Finset.univ : Finset ExternalPort) = {.input, .through, .add, .drop} by
    ext port
    cases port <;> simp]
  simp only [Finset.mem_insert, reduceCtorEq, Finset.mem_singleton, or_self,
    not_false_eq_true, Finset.sum_insert, Finset.sum_singleton]
  ring

/-- A one-port coherent input has exactly the supplied normalized modal power. -/
lemma inputAmplitude_power (p : Parameters) (amplitude : ℂ) :
    (inputAmplitude p amplitude).power = Complex.normSq amplitude := by
  rw [ModeAmplitude.power_eq_sum_normSq]
  rw [← Fintype.sum_equiv (externalIncidentEquiv p)
    (fun port => Complex.normSq (inputAmplitude p amplitude (externalIncidentEquiv p port)))
    (fun endpoint => Complex.normSq (inputAmplitude p amplitude endpoint))
    (fun _ => rfl)]
  rw [sum_externalPort]
  simp [externalChannel]

/-- N6 coherency transport identifies a coherent output-channel power with the squared modulus
of the N5 response amplitude. -/
lemma coherent_output_channelPower (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator)
    (input : ModeAmplitude (netlist p).ExternalIncident) (port : ExternalPort) :
    ((netlist p).responseCoherency
        (isWellPosed_of_hasNonzeroDenominator p hDenominator)
        (CoherencyMatrix.ofAmplitude input)).channelPower (externalOutgoingEquiv p port) =
      Complex.normSq
        (((netlist p).responseTransform
          (isWellPosed_of_hasNonzeroDenominator p hDenominator)).toLinearMap input
            (externalOutgoingEquiv p port)) := by
  exact CoherencyMatrix.channelPower_map_ofAmplitude input
    ((netlist p).responseTransform
      (isWellPosed_of_hasNonzeroDenominator p hDenominator))
    (externalOutgoingEquiv p port)

/-- N6 coherency transport makes every named output power additive for mutually decorrelated
input data. -/
lemma incoherent_output_channelPower_add (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator)
    (first second : CoherencyMatrix (netlist p).ExternalIncident) (port : ExternalPort) :
    ((netlist p).responseCoherency
        (isWellPosed_of_hasNonzeroDenominator p hDenominator)
        (first.incoherentSum second)).channelPower (externalOutgoingEquiv p port) =
      ((netlist p).responseCoherency
        (isWellPosed_of_hasNonzeroDenominator p hDenominator) first).channelPower
          (externalOutgoingEquiv p port) +
      ((netlist p).responseCoherency
        (isWellPosed_of_hasNonzeroDenominator p hDenominator) second).channelPower
          (externalOutgoingEquiv p port) := by
  exact CoherencyMatrix.channelPower_map_incoherentSum first second
    ((netlist p).responseTransform
      (isWellPosed_of_hasNonzeroDenominator p hDenominator))
    (externalOutgoingEquiv p port)

/-- A global scattering equation gives the input bus's reflected coordinate. -/
lemma scatteringEquation_inputCoupler_leftFirst (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident) :
    outgoing (Outgoing.mk
        (inputCouplerChannel p DirectionalCoupler.Port.leftFirst)) =
      (p.inputThroughAmplitude : ℂ) *
          incident (Incident.mk
            (inputCouplerChannel p DirectionalCoupler.Port.rightFirst)) +
        DirectionalCoupler.crossCoefficient p.inputCoupler *
          incident (Incident.mk
            (inputCouplerChannel p DirectionalCoupler.Port.rightSecond)) := by
  have hPhysical :=
    inputCoupler_physicalBehavior_of_scatteringEquation p incident outgoing hScattering
  have hRaw :=
    (DirectionalCoupler.mem_physicalBehavior_iff p.inputCoupler _ _).mp hPhysical
  rw [DirectionalCoupler.mem_behavior_iff,
    DirectionalCoupler.mixing_toLinearMap_apply,
    DirectionalCoupler.mixing_toLinearMap_apply] at hRaw
  have hCoordinate := congrArg
    (fun amplitude => amplitude (Sum.inl (Outgoing.mk (Sum.inl ())))) hRaw
  exact hCoordinate

/-- A global scattering equation gives the add bus's reflected coordinate. -/
lemma scatteringEquation_dropCoupler_leftFirst (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident) :
    outgoing (Outgoing.mk
        (dropCouplerChannel p DirectionalCoupler.Port.leftFirst)) =
      (p.dropThroughAmplitude : ℂ) *
          incident (Incident.mk
            (dropCouplerChannel p DirectionalCoupler.Port.rightFirst)) +
        DirectionalCoupler.crossCoefficient p.dropCoupler *
          incident (Incident.mk
            (dropCouplerChannel p DirectionalCoupler.Port.rightSecond)) := by
  have hPhysical :=
    dropCoupler_physicalBehavior_of_scatteringEquation p incident outgoing hScattering
  have hRaw :=
    (DirectionalCoupler.mem_physicalBehavior_iff p.dropCoupler _ _).mp hPhysical
  rw [DirectionalCoupler.mem_behavior_iff,
    DirectionalCoupler.mixing_toLinearMap_apply,
    DirectionalCoupler.mixing_toLinearMap_apply] at hRaw
  have hCoordinate := congrArg
    (fun amplitude => amplitude (Sum.inl (Outgoing.mk (Sum.inl ())))) hRaw
  exact hCoordinate

/-- For one-port excitation, the four reverse-circulating incident coordinates satisfy the
homogeneous loop recurrence. -/
lemma reverseLoop_relations (p : Parameters) (amplitude : ℂ)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident)
    (hAssembly : incident = (netlist p).connections.incidentAssembly outgoing
      (inputAmplitude p amplitude)) :
    incident (Incident.mk (secondArcChannel p MatchedPropagation.Port.right)) =
        (p.inputThroughAmplitude : ℂ) *
          incident (Incident.mk
            (inputCouplerChannel p DirectionalCoupler.Port.rightSecond)) ∧
      incident (Incident.mk
          (dropCouplerChannel p DirectionalCoupler.Port.rightSecond)) =
        p.secondArcCoefficient *
          incident (Incident.mk (secondArcChannel p MatchedPropagation.Port.right)) ∧
      incident (Incident.mk (firstArcChannel p MatchedPropagation.Port.right)) =
        (p.dropThroughAmplitude : ℂ) *
          incident (Incident.mk
            (dropCouplerChannel p DirectionalCoupler.Port.rightSecond)) ∧
      incident (Incident.mk
          (inputCouplerChannel p DirectionalCoupler.Port.rightSecond)) =
        p.firstArcCoefficient *
          incident (Incident.mk (firstArcChannel p MatchedPropagation.Port.right)) := by
  have hThrough := congrArg
    (fun state => state (Incident.mk
      (inputCouplerChannel p DirectionalCoupler.Port.rightFirst))) hAssembly
  rw [incidentAssembly_apply_input_rightFirst, inputAmplitude_apply_through] at hThrough
  have hDrop := congrArg
    (fun state => state (Incident.mk
      (dropCouplerChannel p DirectionalCoupler.Port.rightFirst))) hAssembly
  rw [incidentAssembly_apply_drop_rightFirst, inputAmplitude_apply_drop] at hDrop
  have hSecond := congrArg
    (fun state => state (Incident.mk
      (secondArcChannel p MatchedPropagation.Port.right))) hAssembly
  rw [incidentAssembly_apply_secondArc_right,
    scatteringEquation_inputCoupler_leftSecond p incident outgoing hScattering,
    hThrough, mul_zero, zero_add] at hSecond
  have hDropRing := congrArg
    (fun state => state (Incident.mk
      (dropCouplerChannel p DirectionalCoupler.Port.rightSecond))) hAssembly
  rw [incidentAssembly_apply_dropCoupler_rightSecond,
    scatteringEquation_secondArc_left p incident outgoing hScattering] at hDropRing
  have hFirst := congrArg
    (fun state => state (Incident.mk
      (firstArcChannel p MatchedPropagation.Port.right))) hAssembly
  rw [incidentAssembly_apply_firstArc_right,
    scatteringEquation_dropCoupler_leftSecond p incident outgoing hScattering,
    hDrop, mul_zero, zero_add] at hFirst
  have hInputRing := congrArg
    (fun state => state (Incident.mk
      (inputCouplerChannel p DirectionalCoupler.Port.rightSecond))) hAssembly
  rw [incidentAssembly_apply_inputCoupler_rightSecond,
    scatteringEquation_firstArc_left p incident outgoing hScattering] at hInputRing
  exact ⟨hSecond, hDropRing, hFirst, hInputRing⟩

/-- A nonzero feedback denominator forces the reverse input-coupler loop coordinate to vanish. -/
lemma reverseInputIncident_eq_zero (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) (amplitude : ℂ)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident)
    (hAssembly : incident = (netlist p).connections.incidentAssembly outgoing
      (inputAmplitude p amplitude)) :
    incident (Incident.mk
        (inputCouplerChannel p DirectionalCoupler.Port.rightSecond)) = 0 := by
  rcases reverseLoop_relations p amplitude incident outgoing hScattering hAssembly with
    ⟨hSecond, hDropRing, hFirst, hInputRing⟩
  have hProduct : p.denominator *
      incident (Incident.mk
        (inputCouplerChannel p DirectionalCoupler.Port.rightSecond)) = 0 := by
    calc
      _ = incident (Incident.mk
              (inputCouplerChannel p DirectionalCoupler.Port.rightSecond)) -
            p.firstArcCoefficient *
              ((p.dropThroughAmplitude : ℂ) *
                (p.secondArcCoefficient *
                  ((p.inputThroughAmplitude : ℂ) *
                    incident (Incident.mk
                      (inputCouplerChannel p
                        DirectionalCoupler.Port.rightSecond))))) := by
            rw [Parameters.denominator, Parameters.loopGain,
              Parameters.roundTripCoefficient]
            ring
      _ = 0 := by rw [← hSecond, ← hDropRing, ← hFirst, ← hInputRing, sub_self]
  exact (mul_eq_zero.mp hProduct).resolve_left hDenominator

/-- Vanishing of the reverse input-coupler coordinate propagates to the drop coupler. -/
lemma reverseDropIncident_eq_zero (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) (amplitude : ℂ)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident)
    (hAssembly : incident = (netlist p).connections.incidentAssembly outgoing
      (inputAmplitude p amplitude)) :
    incident (Incident.mk
        (dropCouplerChannel p DirectionalCoupler.Port.rightSecond)) = 0 := by
  rcases reverseLoop_relations p amplitude incident outgoing hScattering hAssembly with
    ⟨hSecond, hDropRing, _, _⟩
  have hInputZero := reverseInputIncident_eq_zero p hDenominator amplitude
    incident outgoing hScattering hAssembly
  have hSecondZero :
      incident (Incident.mk (secondArcChannel p MatchedPropagation.Port.right)) = 0 := by
    rw [hSecond, hInputZero, mul_zero]
  rw [hDropRing, hSecondZero, mul_zero]

/-- For one-port excitation, both reverse-circulating bus coordinates vanish at a nonzero
feedback denominator. -/
lemma reverseIncidentCoordinates_eq_zero (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) (amplitude : ℂ)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident)
    (hAssembly : incident = (netlist p).connections.incidentAssembly outgoing
      (inputAmplitude p amplitude)) :
    incident (Incident.mk
        (inputCouplerChannel p DirectionalCoupler.Port.rightSecond)) = 0 ∧
      incident (Incident.mk
        (dropCouplerChannel p DirectionalCoupler.Port.rightSecond)) = 0 := by
  exact ⟨reverseInputIncident_eq_zero p hDenominator amplitude incident outgoing
      hScattering hAssembly,
    reverseDropIncident_eq_zero p hDenominator amplitude incident outgoing
      hScattering hAssembly⟩

/-- External readout returns the outgoing coordinate on the input bus. -/
lemma outputReadout_apply_input (p : Parameters)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex) :
    (netlist p).outputReadout.toLinearMap outgoing (Outgoing.mk (inputChannel p)) =
      outgoing
        (Outgoing.mk (inputCouplerChannel p DirectionalCoupler.Port.leftFirst)) := by
  rw [FlatNetlist.outputReadout,
    (netlist p).connections.externalOutgoingReadout_apply,
    ModeAmplitude.restrictEmbedding_apply]
  rfl

/-- External readout returns the outgoing coordinate on the add bus. -/
lemma outputReadout_apply_add (p : Parameters)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex) :
    (netlist p).outputReadout.toLinearMap outgoing (Outgoing.mk (addChannel p)) =
      outgoing
        (Outgoing.mk (dropCouplerChannel p DirectionalCoupler.Port.leftFirst)) := by
  rw [FlatNetlist.outputReadout,
    (netlist p).connections.externalOutgoingReadout_apply,
    ModeAmplitude.restrictEmbedding_apply]
  rfl

/-- A coherent input on the input bus produces no reflected field on either left bus port. -/
lemma reflected_amplitudes_eq_zero (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) (amplitude : ℂ) :
    ((netlist p).responseTransform
        (isWellPosed_of_hasNonzeroDenominator p hDenominator)).toLinearMap
          (inputAmplitude p amplitude) (Outgoing.mk (inputChannel p)) = 0 ∧
      ((netlist p).responseTransform
        (isWellPosed_of_hasNonzeroDenominator p hDenominator)).toLinearMap
          (inputAmplitude p amplitude) (Outgoing.mk (addChannel p)) = 0 := by
  let hWellPosed := isWellPosed_of_hasNonzeroDenominator p hDenominator
  let output := (netlist p).responseTransform hWellPosed |>.toLinearMap
    (inputAmplitude p amplitude)
  have hMember : (inputAmplitude p amplitude, output) ∈ (netlist p).behavior := by
    rw [← (netlist p).toBehavior_responseTransform hWellPosed,
      ModeTransform.mem_toBehavior_iff_toLinearMap]
  rcases ((netlist p).mem_behavior_iff_equations (inputAmplitude p amplitude) output).mp
      hMember with ⟨incident, outgoing, hScattering, hAssembly, hOutput⟩
  have hAssembly' :
      incident = (netlist p).connections.incidentAssembly outgoing
        (inputAmplitude p amplitude) := by
    simpa only [PortConnectionFamily.incidentAssembly] using hAssembly
  have hReverse := reverseIncidentCoordinates_eq_zero p hDenominator amplitude
    incident outgoing hScattering hAssembly'
  have hThrough := congrArg
    (fun state => state (Incident.mk
      (inputCouplerChannel p DirectionalCoupler.Port.rightFirst))) hAssembly'
  rw [incidentAssembly_apply_input_rightFirst, inputAmplitude_apply_through] at hThrough
  have hDrop := congrArg
    (fun state => state (Incident.mk
      (dropCouplerChannel p DirectionalCoupler.Port.rightFirst))) hAssembly'
  rw [incidentAssembly_apply_drop_rightFirst, inputAmplitude_apply_drop] at hDrop
  have hInputOutgoing :=
    scatteringEquation_inputCoupler_leftFirst p incident outgoing hScattering
  have hAddOutgoing :=
    scatteringEquation_dropCoupler_leftFirst p incident outgoing hScattering
  rw [hThrough, hReverse.1, mul_zero, zero_add] at hInputOutgoing
  rw [hDrop, hReverse.2, mul_zero, zero_add] at hAddOutgoing
  have hInputReadout := congrArg
    (fun state => state (Outgoing.mk (inputChannel p))) hOutput
  have hAddReadout := congrArg
    (fun state => state (Outgoing.mk (addChannel p))) hOutput
  rw [outputReadout_apply_input] at hInputReadout
  rw [outputReadout_apply_add] at hAddReadout
  change
    ((netlist p).responseTransform
        (isWellPosed_of_hasNonzeroDenominator p hDenominator)).toLinearMap
          (inputAmplitude p amplitude) (Outgoing.mk (inputChannel p)) = 0 ∧
      ((netlist p).responseTransform
        (isWellPosed_of_hasNonzeroDenominator p hDenominator)).toLinearMap
          (inputAmplitude p amplitude) (Outgoing.mk (addChannel p)) = 0
  constructor
  · change output (Outgoing.mk (inputChannel p)) = 0
    rw [hInputReadout, hInputOutgoing]
    simp
  · change output (Outgoing.mk (addChannel p)) = 0
    rw [hAddReadout, hAddOutgoing]
    simp

/-- N6 losslessness gives exact through-plus-drop power balance for a coherent one-port input. -/
lemma lossless_response_through_drop_power_balance (p : Parameters) (hp : p.IsLossless)
    (hDenominator : p.HasNonzeroDenominator) (amplitude : ℂ) :
    Complex.normSq
        (((netlist p).responseTransform
          (isWellPosed_of_hasNonzeroDenominator p hDenominator)).toLinearMap
            (inputAmplitude p amplitude) (Outgoing.mk (throughChannel p))) +
      Complex.normSq
        (((netlist p).responseTransform
          (isWellPosed_of_hasNonzeroDenominator p hDenominator)).toLinearMap
            (inputAmplitude p amplitude) (Outgoing.mk (dropChannel p))) =
      Complex.normSq amplitude := by
  have hPower := responseTransform_isPowerPreserving p hp hDenominator
    (inputAmplitude p amplitude)
  rw [ModeAmplitude.power_eq_sum_normSq, ModeAmplitude.power_eq_sum_normSq] at hPower
  rw [← Fintype.sum_equiv (externalOutgoingEquiv p)
    (fun port => Complex.normSq
      (((netlist p).responseTransform
        (isWellPosed_of_hasNonzeroDenominator p hDenominator)).toLinearMap
          (inputAmplitude p amplitude) (externalOutgoingEquiv p port)))
    (fun endpoint => Complex.normSq
      (((netlist p).responseTransform
        (isWellPosed_of_hasNonzeroDenominator p hDenominator)).toLinearMap
          (inputAmplitude p amplitude) endpoint)) (fun _ => rfl)] at hPower
  rw [← Fintype.sum_equiv (externalIncidentEquiv p)
    (fun port => Complex.normSq
      (inputAmplitude p amplitude (externalIncidentEquiv p port)))
    (fun endpoint => Complex.normSq (inputAmplitude p amplitude endpoint))
    (fun _ => rfl)] at hPower
  rw [sum_externalPort, sum_externalPort] at hPower
  simp only [externalOutgoingEquiv_apply, externalIncidentEquiv_apply] at hPower
  simp only [externalChannel] at hPower
  rcases reflected_amplitudes_eq_zero p hDenominator amplitude with
    ⟨hInput, hAdd⟩
  rw [hInput, hAdd] at hPower
  simpa [externalChannel] using hPower

/-- A lossless, well-posed add-drop ring has normalized through and drop powers summing to one. -/
theorem lossless_through_drop_power_balance (p : Parameters) (hp : p.IsLossless)
    (hDenominator : p.HasNonzeroDenominator) :
    throughPower p + dropPower p = 1 := by
  have hPower := lossless_response_through_drop_power_balance p hp hDenominator 1
  rw [response_through p hDenominator, response_drop p hDenominator] at hPower
  simpa [throughPower, dropPower] using hPower

end AddDrop

end

end Optics
