/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Systems.Microring.AddDropRegression
public import Physlib.Optics.Systems.Microring.Observables

/-!
# Regression tests for add-drop microring observables

## i. Overview

The first fixture reuses the explicit response-tested add-drop ring with `3 / 5` through and
`4 / 5` cross amplitudes at both couplers and rational round-trip field attenuation `1 / 4`.
Direct squared-modulus expansion gives through/drop powers `2025 / 8281` and `1024 / 8281` at
the zero-phase point, and `5625 / 11881` and `1024 / 11881` at the half-turn point. The power
checks do not invoke the general closed-form power lemmas.

A second exact fixture has unit field retention and is critically coupled. It specializes the
N6-routed lossless power balance and the parameter-recovery results. A nondispersive model with
group index `2`, round-trip length `3`, and propagation speed `5` pins angular FSR `5 * pi / 3`.

“Resonance” and “antiresonance” name the two phase points only. These regressions do not prove
extrema, linewidth, quality factor, a source-parity bridge, reciprocity, intensity-only sign
identifiability, or validity away from the explicitly gated N5F response domain.

## ii. Key results

- `observablesRegression_resonance_throughPower`: the exact zero-phase through power.
- `observablesRegression_antiresonance_dropPower`: the exact half-turn drop power.
- `observablesRegression_dropRejectionRatioDB`: the pinned drop power-ratio convention.
- `observablesRegression_critical_lossless_powerBalance`: the N6-routed lossless specialization.
- `observablesRegression_angularFSR`: the exact nondispersive FSR.
- `observablesRegression_n5f_resonance_throughPower`: a proof-gated N5F power anchor.

## iii. Table of contents

- A. Hand-expanded named-phase powers
- B. Positive-power rejection ratio
- C. Critical coupling, losslessness, and recovery
- D. Nondispersive free spectral range

## iv. References

These are Physlib regression values for the S-03 and S-05 validation rows. No integrated-
photonics source-parity row is claimed.
-/

@[expose] public section

namespace Optics

noncomputable section

namespace AddDrop

/-!
## A. Hand-expanded named-phase powers
-/

/-- The exact zero-phase fixture satisfies the named resonance condition. -/
lemma observablesRegression_resonance_isResonant :
    addDropRegressionResonanceParameters.IsResonant := by
  apply Parameters.isResonant_of_roundTripPhase_eq_zero
  rfl

/-- The exact half-turn fixture satisfies the named antiresonance condition. -/
lemma observablesRegression_antiresonance_isAntiresonant :
    addDropRegressionAntiresonanceParameters.IsAntiresonant := by
  apply Parameters.isAntiresonant_of_roundTripPhase_eq_pi
  rfl

/-- The zero-phase fixture satisfies the scalar solve gate. -/
lemma observablesRegression_resonance_hasNonzeroDenominator :
    addDropRegressionResonanceParameters.HasNonzeroDenominator := by
  rw [Parameters.HasNonzeroDenominator, addDropRegression_resonance_denominator]
  norm_num

/-- Squared-modulus expansion of the independently pinned response gives the zero-phase through
power `2025 / 8281`. -/
lemma observablesRegression_resonance_throughPower :
    throughPower addDropRegressionResonanceParameters = 2025 / 8281 := by
  rw [throughPower, addDropRegression_resonance_throughTransfer]
  norm_num [Complex.normSq_apply]

/-- Squared-modulus expansion of the independently pinned response gives the zero-phase drop
power `1024 / 8281`. -/
lemma observablesRegression_resonance_dropPower :
    dropPower addDropRegressionResonanceParameters = 1024 / 8281 := by
  rw [dropPower, addDropRegression_resonance_dropTransfer]
  norm_num [Complex.normSq_apply]

/-- Squared-modulus expansion gives the half-turn through power `5625 / 11881`. -/
lemma observablesRegression_antiresonance_throughPower :
    throughPower addDropRegressionAntiresonanceParameters = 5625 / 11881 := by
  rw [throughPower, addDropRegression_antiresonance_throughTransfer]
  norm_num [Complex.normSq_apply]

/-- Squared-modulus expansion gives the half-turn drop power `1024 / 11881`. -/
lemma observablesRegression_antiresonance_dropPower :
    dropPower addDropRegressionAntiresonanceParameters = 1024 / 11881 := by
  rw [dropPower, addDropRegression_antiresonance_dropTransfer]
  norm_num [Complex.normSq_apply]

/-- Direct scalar expansion gives the zero-phase power denominator `8281 / 10000`. -/
lemma observablesRegression_resonance_powerDenominator :
    addDropRegressionResonanceParameters.powerDenominator = 8281 / 10000 := by
  norm_num [Parameters.powerDenominator, addDropRegressionResonanceParameters]

/-- Direct scalar expansion gives the zero-phase through-power numerator `2025 / 10000`. -/
lemma observablesRegression_resonance_throughPowerNumerator :
    addDropRegressionResonanceParameters.throughPowerNumerator = 2025 / 10000 := by
  norm_num [Parameters.throughPowerNumerator, addDropRegressionResonanceParameters]

/-- Direct scalar expansion gives the zero-phase drop-power numerator `1024 / 10000`. -/
lemma observablesRegression_resonance_dropPowerNumerator :
    addDropRegressionResonanceParameters.dropPowerNumerator = 1024 / 10000 := by
  norm_num [Parameters.dropPowerNumerator, addDropRegressionResonanceParameters]

/-- Direct scalar expansion gives the half-turn power denominator `11881 / 10000`. -/
lemma observablesRegression_antiresonance_powerDenominator :
    addDropRegressionAntiresonanceParameters.powerDenominator = 11881 / 10000 := by
  norm_num [Parameters.powerDenominator, addDropRegressionAntiresonanceParameters,
    Real.cos_pi]

/-- Direct scalar expansion gives the half-turn through-power numerator `5625 / 10000`. -/
lemma observablesRegression_antiresonance_throughPowerNumerator :
    addDropRegressionAntiresonanceParameters.throughPowerNumerator = 5625 / 10000 := by
  norm_num [Parameters.throughPowerNumerator, addDropRegressionAntiresonanceParameters,
    Real.cos_pi]

/-- Direct scalar expansion gives the half-turn drop-power numerator `1024 / 10000`. -/
lemma observablesRegression_antiresonance_dropPowerNumerator :
    addDropRegressionAntiresonanceParameters.dropPowerNumerator = 1024 / 10000 := by
  norm_num [Parameters.dropPowerNumerator, addDropRegressionAntiresonanceParameters]

/-- Independent amplitude and scalar expansions agree with the zero-phase through-power formula. -/
lemma observablesRegression_resonance_throughPower_eq_closedForm :
    throughPower addDropRegressionResonanceParameters =
      addDropRegressionResonanceParameters.throughPowerNumerator /
        addDropRegressionResonanceParameters.powerDenominator := by
  rw [observablesRegression_resonance_throughPower,
    observablesRegression_resonance_throughPowerNumerator,
    observablesRegression_resonance_powerDenominator]
  norm_num

/-- Independent amplitude and scalar expansions agree with the zero-phase drop-power formula. -/
lemma observablesRegression_resonance_dropPower_eq_closedForm :
    dropPower addDropRegressionResonanceParameters =
      addDropRegressionResonanceParameters.dropPowerNumerator /
        addDropRegressionResonanceParameters.powerDenominator := by
  rw [observablesRegression_resonance_dropPower,
    observablesRegression_resonance_dropPowerNumerator,
    observablesRegression_resonance_powerDenominator]
  norm_num

/-- Independent amplitude and scalar expansions agree with the half-turn through-power formula. -/
lemma observablesRegression_antiresonance_throughPower_eq_closedForm :
    throughPower addDropRegressionAntiresonanceParameters =
      addDropRegressionAntiresonanceParameters.throughPowerNumerator /
        addDropRegressionAntiresonanceParameters.powerDenominator := by
  rw [observablesRegression_antiresonance_throughPower,
    observablesRegression_antiresonance_throughPowerNumerator,
    observablesRegression_antiresonance_powerDenominator]
  norm_num

/-- Independent amplitude and scalar expansions agree with the half-turn drop-power formula. -/
lemma observablesRegression_antiresonance_dropPower_eq_closedForm :
    dropPower addDropRegressionAntiresonanceParameters =
      addDropRegressionAntiresonanceParameters.dropPowerNumerator /
        addDropRegressionAntiresonanceParameters.powerDenominator := by
  rw [observablesRegression_antiresonance_dropPower,
    observablesRegression_antiresonance_dropPowerNumerator,
    observablesRegression_antiresonance_powerDenominator]
  norm_num

/-!
## B. Positive-power rejection ratio
-/

/-- Phase specialization of the zero-phase fixture is definitionally unchanged. -/
lemma observablesRegression_atResonance :
    addDropRegressionResonanceParameters.atResonance =
      addDropRegressionResonanceParameters := by
  rfl

/-- Half-turn specialization of the zero-phase fixture is the antiresonant fixture. -/
lemma observablesRegression_atAntiresonance :
    addDropRegressionResonanceParameters.atAntiresonance =
      addDropRegressionAntiresonanceParameters := by
  rfl

/-- The named resonant power in the rejection ratio is strictly positive. -/
lemma observablesRegression_resonance_throughPower_pos :
    0 < throughPower addDropRegressionResonanceParameters := by
  rw [observablesRegression_resonance_throughPower]
  norm_num

/-- The named antiresonant power in the rejection ratio is strictly positive. -/
lemma observablesRegression_antiresonance_throughPower_pos :
    0 < throughPower addDropRegressionAntiresonanceParameters := by
  rw [observablesRegression_antiresonance_throughPower]
  norm_num

/-- The named resonant drop power is strictly positive. -/
lemma observablesRegression_resonance_dropPower_pos :
    0 < dropPower addDropRegressionResonanceParameters := by
  rw [observablesRegression_resonance_dropPower]
  norm_num

/-- The named antiresonant drop power is strictly positive. -/
lemma observablesRegression_antiresonance_dropPower_pos :
    0 < dropPower addDropRegressionAntiresonanceParameters := by
  rw [observablesRegression_antiresonance_dropPower]
  norm_num

/-- Direct unfolding pins the rejection ratio as `10 * logb 10` of antiresonant power divided by
resonant power. -/
lemma observablesRegression_rejectionRatioDB :
    throughRejectionRatioDB addDropRegressionResonanceParameters =
      10 * Real.logb 10 ((5625 / 11881) / (2025 / 8281)) := by
  rw [throughRejectionRatioDB, powerRatioDB, observablesRegression_atAntiresonance,
    observablesRegression_atResonance,
    observablesRegression_antiresonance_throughPower,
    observablesRegression_resonance_throughPower]

/-- The positive named powers justify the difference-of-logarithms form of the exact ratio. -/
lemma observablesRegression_rejectionRatioDB_eq_logb_sub :
    throughRejectionRatioDB addDropRegressionResonanceParameters =
      10 * (Real.logb 10 (5625 / 11881) - Real.logb 10 (2025 / 8281)) := by
  rw [observablesRegression_rejectionRatioDB,
    Real.logb_div (by norm_num : (5625 / 11881 : ℝ) ≠ 0)
      (by norm_num : (2025 / 8281 : ℝ) ≠ 0)]

/-- Direct unfolding and cancellation pin the drop rejection ratio to `11881 / 8281`. -/
lemma observablesRegression_dropRejectionRatioDB :
    dropRejectionRatioDB addDropRegressionResonanceParameters =
      10 * Real.logb 10 (11881 / 8281) := by
  rw [dropRejectionRatioDB, powerRatioDB, observablesRegression_atResonance,
    observablesRegression_atAntiresonance,
    observablesRegression_resonance_dropPower,
    observablesRegression_antiresonance_dropPower]
  congr 2
  norm_num

/-- The positive exact denominator powers justify the difference-of-logarithms drop ratio. -/
lemma observablesRegression_dropRejectionRatioDB_eq_logb_sub :
    dropRejectionRatioDB addDropRegressionResonanceParameters =
      10 * (Real.logb 10 11881 - Real.logb 10 8281) := by
  rw [observablesRegression_dropRejectionRatioDB,
    Real.logb_div (by norm_num : (11881 : ℝ) ≠ 0)
      (by norm_num : (8281 : ℝ) ≠ 0)]

/-!
## C. Critical coupling, losslessness, and recovery
-/

/-- A unit-retention, zero-phase `3-4-5` ring used for critical-coupling regression. -/
def observablesRegressionCriticalParameters : Parameters where
  inputThroughAmplitude := 3 / 5
  inputCrossAmplitude := 4 / 5
  dropThroughAmplitude := 3 / 5
  dropCrossAmplitude := 4 / 5
  fieldAttenuation := 1
  roundTripPhase := 0

/-- The critical fixture has two unitary couplers and unit round-trip field retention. -/
lemma observablesRegression_critical_isLossless :
    observablesRegressionCriticalParameters.IsLossless := by
  constructor
  · norm_num [observablesRegressionCriticalParameters, Parameters.inputCoupler,
      DirectionalCoupler.Parameters.IsUnitary, DirectionalCoupler.Parameters.powerFactor]
  · constructor
    · norm_num [observablesRegressionCriticalParameters, Parameters.dropCoupler,
        DirectionalCoupler.Parameters.IsUnitary, DirectionalCoupler.Parameters.powerFactor]
    · rfl

/-- The critical fixture satisfies the complete N7 component-validity predicate. -/
lemma observablesRegression_critical_isValid :
    observablesRegressionCriticalParameters.IsValid := by
  constructor
  · norm_num [observablesRegressionCriticalParameters, Parameters.inputCoupler,
      DirectionalCoupler.Parameters.IsValid, DirectionalCoupler.Parameters.IsUnitary,
      DirectionalCoupler.Parameters.powerFactor]
  · constructor
    · norm_num [observablesRegressionCriticalParameters, Parameters.dropCoupler,
        DirectionalCoupler.Parameters.IsValid, DirectionalCoupler.Parameters.IsUnitary,
        DirectionalCoupler.Parameters.powerFactor]
    · constructor
      · norm_num [observablesRegressionCriticalParameters]
      · constructor
        · norm_num [observablesRegressionCriticalParameters]
        · constructor <;>
            norm_num [observablesRegressionCriticalParameters, Parameters.firstPropagation,
              Parameters.secondPropagation, Parameters.halfArcAttenuation,
              MatchedPropagation.Parameters.IsValid]

/-- Direct expansion gives the critical fixture's feedback denominator `16 / 25`. -/
lemma observablesRegression_critical_denominator :
    observablesRegressionCriticalParameters.denominator = 16 / 25 := by
  norm_num [Parameters.denominator, Parameters.loopGain,
    Parameters.roundTripCoefficient, Parameters.firstArcCoefficient,
    Parameters.secondArcCoefficient, Parameters.firstPropagation,
    Parameters.secondPropagation, Parameters.halfArcAttenuation,
    Parameters.halfArcPhase, MatchedPropagation.transmissionCoefficient,
    MatchedPropagation.carrierPhaseFactor, observablesRegressionCriticalParameters]

/-- The critical fixture satisfies the exact N5 solve gate. -/
lemma observablesRegression_critical_hasNonzeroDenominator :
    observablesRegressionCriticalParameters.HasNonzeroDenominator := by
  rw [Parameters.HasNonzeroDenominator, observablesRegression_critical_denominator]
  norm_num

/-- The critical fixture satisfies the named critical-coupling equality. -/
lemma observablesRegression_critical_isCriticallyCoupled :
    observablesRegressionCriticalParameters.IsCriticallyCoupled := by
  norm_num [Parameters.IsCriticallyCoupled, observablesRegressionCriticalParameters]

/-- The critical fixture satisfies the named resonance condition. -/
lemma observablesRegression_critical_isResonant :
    observablesRegressionCriticalParameters.IsResonant := by
  apply Parameters.isResonant_of_roundTripPhase_eq_zero
  rfl

/-- Primitive expansion of the S2 transfer gives exact through-field extinction at the named
point, independently of the general critical-coupling theorem. -/
lemma observablesRegression_critical_extinction :
    throughTransfer observablesRegressionCriticalParameters = 0 := by
  rw [throughTransfer, observablesRegression_critical_denominator]
  norm_num [observablesRegressionCriticalParameters, Parameters.inputCoupler,
    Parameters.dropCoupler, Parameters.roundTripCoefficient,
    Parameters.firstArcCoefficient, Parameters.secondArcCoefficient,
    Parameters.firstPropagation, Parameters.secondPropagation,
    Parameters.halfArcAttenuation, Parameters.halfArcPhase,
    MatchedPropagation.transmissionCoefficient, MatchedPropagation.carrierPhaseFactor,
    DirectionalCoupler.crossCoefficient]
  rw [mul_pow, Complex.I_sq]
  norm_num

/-- The N6-routed theorem specializes to exact lossless power balance at the critical point. -/
lemma observablesRegression_critical_lossless_powerBalance :
    throughPower observablesRegressionCriticalParameters +
      dropPower observablesRegressionCriticalParameters = 1 := by
  exact lossless_through_drop_power_balance observablesRegressionCriticalParameters
    observablesRegression_critical_isLossless
    observablesRegression_critical_hasNonzeroDenominator

/-- The extinction recovery theorem returns the nonnegative cross amplitude `4 / 5`. -/
lemma observablesRegression_critical_recovers_inputCrossAmplitude :
    observablesRegressionCriticalParameters.inputCrossAmplitude =
      Real.sqrt
        (1 - (observablesRegressionCriticalParameters.dropThroughAmplitude *
          observablesRegressionCriticalParameters.fieldAttenuation) ^ 2) := by
  exact inputCrossAmplitude_eq_sqrt_of_resonant_extinction
    observablesRegressionCriticalParameters observablesRegression_critical_isLossless.1
    (by norm_num [observablesRegressionCriticalParameters])
    (by norm_num [observablesRegressionCriticalParameters])
    observablesRegression_critical_hasNonzeroDenominator
    observablesRegression_critical_isResonant observablesRegression_critical_extinction

/-- The antiresonant phase-resolved field recovers the rational attenuation `1 / 4`. -/
lemma observablesRegression_antiresonance_recovers_attenuation :
    addDropRegressionAntiresonanceParameters.fieldAttenuation =
      ((75 / 109 : ℝ) -
          addDropRegressionAntiresonanceParameters.inputThroughAmplitude) /
        (addDropRegressionAntiresonanceParameters.dropThroughAmplitude *
          (1 - (75 / 109 : ℝ) *
            addDropRegressionAntiresonanceParameters.inputThroughAmplitude)) := by
  apply attenuation_eq_of_antiresonant_field
    addDropRegressionAntiresonanceParameters
    addDropRegression_antiresonance_isValid.1.isUnitary
    addDropRegression_antiresonance_isValid.fieldAttenuation_nonneg
  · rw [Parameters.HasNonzeroDenominator,
      addDropRegression_antiresonance_denominator]
    norm_num
  · exact observablesRegression_antiresonance_isAntiresonant
  · convert addDropRegression_antiresonance_throughTransfer using 1
    all_goals norm_num
  · norm_num [addDropRegressionAntiresonanceParameters]

/-!
## D. Nondispersive free spectral range
-/

/-- A rational nondispersive model with group delay `6 / 5`. -/
def observablesRegressionNondispersiveModel : NondispersiveGroupIndexModel where
  base := addDropRegressionResonanceParameters
  groupIndex := 2
  roundTripLength := 3
  propagationSpeed := 5
  groupIndex_pos := by norm_num
  roundTripLength_pos := by norm_num
  propagationSpeed_pos := by norm_num

/-- Direct expansion gives the rational group delay `6 / 5`. -/
lemma observablesRegression_groupDelay :
    observablesRegressionNondispersiveModel.groupDelay = 6 / 5 := by
  norm_num [NondispersiveGroupIndexModel.groupDelay,
    observablesRegressionNondispersiveModel]

/-- Direct expansion gives angular FSR `5 * pi / 3`. -/
lemma observablesRegression_angularFSR :
    observablesRegressionNondispersiveModel.angularFSR = 5 * Real.pi / 3 := by
  rw [NondispersiveGroupIndexModel.angularFSR, observablesRegression_groupDelay]
  ring

/-- Direct expansion gives ordinary-frequency FSR `5 / 6`. -/
lemma observablesRegression_frequencyFSR :
    observablesRegressionNondispersiveModel.frequencyFSR = 5 / 6 := by
  rw [NondispersiveGroupIndexModel.frequencyFSR, observablesRegression_angularFSR]
  field_simp [Real.pi_ne_zero]
  ring

/-- At zero angular frequency the nondispersive law recovers the zero-phase fixture. -/
lemma observablesRegression_parametersAt_zero :
    observablesRegressionNondispersiveModel.parametersAt 0 =
      addDropRegressionResonanceParameters := by
  simp [NondispersiveGroupIndexModel.parametersAt,
    observablesRegressionNondispersiveModel]

/-- Direct expansion of the affine phase lift gives one full turn at one angular FSR. -/
lemma observablesRegression_parametersAt_oneFSR_roundTripPhase :
    (observablesRegressionNondispersiveModel.parametersAt
      observablesRegressionNondispersiveModel.angularFSR).roundTripPhase =
        2 * Real.pi := by
  rw [NondispersiveGroupIndexModel.parametersAt, observablesRegression_angularFSR,
    observablesRegression_groupDelay]
  simp only [observablesRegressionNondispersiveModel,
    addDropRegressionResonanceParameters]
  ring

/-- The two half arcs at one angular FSR compose to the original quarter-retention loop factor. -/
lemma observablesRegression_parametersAt_oneFSR_roundTripCoefficient :
    (observablesRegressionNondispersiveModel.parametersAt
      observablesRegressionNondispersiveModel.angularFSR).roundTripCoefficient = 1 / 4 := by
  rw [Parameters.roundTripCoefficient_eq_fieldAttenuation _
    (by norm_num [NondispersiveGroupIndexModel.parametersAt,
      observablesRegressionNondispersiveModel, addDropRegressionResonanceParameters])]
  rw [observablesRegression_parametersAt_oneFSR_roundTripPhase]
  simp [NondispersiveGroupIndexModel.parametersAt,
    observablesRegressionNondispersiveModel, addDropRegressionResonanceParameters,
    MatchedPropagation.carrierPhaseFactor, Real.Angle.coe_two_pi]

/-- Direct expansion gives the same nonzero feedback denominator one angular FSR later. -/
lemma observablesRegression_parametersAt_oneFSR_denominator :
    (observablesRegressionNondispersiveModel.parametersAt
      observablesRegressionNondispersiveModel.angularFSR).denominator = 91 / 100 := by
  rw [Parameters.denominator, Parameters.loopGain,
    observablesRegression_parametersAt_oneFSR_roundTripCoefficient]
  norm_num [NondispersiveGroupIndexModel.parametersAt,
    observablesRegressionNondispersiveModel, addDropRegressionResonanceParameters]

/-- Primitive S2 expansion at one angular FSR gives the same through amplitude `45 / 91`. -/
lemma observablesRegression_parametersAt_oneFSR_throughTransfer :
    throughTransfer
        (observablesRegressionNondispersiveModel.parametersAt
          observablesRegressionNondispersiveModel.angularFSR) = 45 / 91 := by
  rw [throughTransfer, observablesRegression_parametersAt_oneFSR_denominator,
    observablesRegression_parametersAt_oneFSR_roundTripCoefficient]
  norm_num [NondispersiveGroupIndexModel.parametersAt,
    observablesRegressionNondispersiveModel, addDropRegressionResonanceParameters,
    Parameters.inputCoupler, DirectionalCoupler.crossCoefficient]
  rw [mul_pow, Complex.I_sq]
  norm_num

/-- Zero angular frequency belongs to the exact physical N5F response domain. -/
lemma observablesRegression_zero_mem_responseDomain :
    0 ∈ (parameterizedNetlist
      observablesRegressionNondispersiveModel.parametersAt).responseDomain := by
  rw [mem_parameterizedNetlist_responseDomain_iff,
    observablesRegression_parametersAt_zero]
  exact ⟨observablesRegression_resonance_hasNonzeroDenominator,
    addDropRegression_resonance_isValid⟩

/-- The same zero-frequency gate is packaged for the named nondispersive network. -/
lemma observablesRegression_zero_mem_networkResponseDomain :
    0 ∈ observablesRegressionNondispersiveModel.network.responseDomain := by
  unfold NondispersiveGroupIndexModel.network
  exact observablesRegression_zero_mem_responseDomain

/-- One angular FSR from zero also belongs to the physical N5F response domain. -/
lemma observablesRegression_oneFSR_mem_networkResponseDomain :
    0 + observablesRegressionNondispersiveModel.angularFSR ∈
      observablesRegressionNondispersiveModel.network.responseDomain := by
  exact observablesRegressionNondispersiveModel.add_angularFSR_mem_responseDomain
    observablesRegression_zero_mem_networkResponseDomain

/-- One angular FSR belongs to the parameterized-netlist response domain used by the fixture. -/
lemma observablesRegression_oneFSR_mem_responseDomain :
    observablesRegressionNondispersiveModel.angularFSR ∈
      (parameterizedNetlist
        observablesRegressionNondispersiveModel.parametersAt).responseDomain := by
  simpa only [zero_add, NondispersiveGroupIndexModel.network] using
    observablesRegression_oneFSR_mem_networkResponseDomain

/-- The proof-gated N5F input-to-through response power at a selected angular frequency. -/
def observablesRegressionN5FThroughPowerAt (angularFrequency : ℝ)
    (hFrequency : angularFrequency ∈
      (parameterizedNetlist
        observablesRegressionNondispersiveModel.parametersAt).responseDomain) : ℝ :=
  Complex.normSq
    ((parameterizedNetlist
      observablesRegressionNondispersiveModel.parametersAt).response hFrequency
      (Outgoing.mk
        (throughChannel
          (observablesRegressionNondispersiveModel.parametersAt angularFrequency)))
      (Incident.mk
        (inputChannel
          (observablesRegressionNondispersiveModel.parametersAt angularFrequency))))

/-- The proof-gated N5F through response has the independently expanded zero-phase power. -/
lemma observablesRegression_n5f_resonance_throughPower :
    Complex.normSq
        ((parameterizedNetlist
          observablesRegressionNondispersiveModel.parametersAt).response
          observablesRegression_zero_mem_responseDomain
          (Outgoing.mk
            (throughChannel
              (observablesRegressionNondispersiveModel.parametersAt 0)))
          (Incident.mk
            (inputChannel
              (observablesRegressionNondispersiveModel.parametersAt 0)))) =
      2025 / 8281 := by
  rw [parameterizedNetlist_response_through_power,
    observablesRegression_parametersAt_zero,
    observablesRegression_resonance_throughPower]

/-- The compact response-power fixture agrees with the direct zero-frequency N5F anchor. -/
lemma observablesRegressionN5FThroughPowerAt_zero :
    observablesRegressionN5FThroughPowerAt 0
      observablesRegression_zero_mem_responseDomain = 2025 / 8281 := by
  exact observablesRegression_n5f_resonance_throughPower

/-- The proof-gated N5F response one angular FSR later has power `2025 / 8281`, by direct
parameter, phase-factor, and S2 transfer expansion rather than the FSR periodicity theorem. -/
lemma observablesRegression_n5f_oneFSR_throughPower :
    observablesRegressionN5FThroughPowerAt
        observablesRegressionNondispersiveModel.angularFSR
        observablesRegression_oneFSR_mem_responseDomain = 2025 / 8281 := by
  unfold observablesRegressionN5FThroughPowerAt
  rw [parameterizedNetlist_response_through_power]
  change Complex.normSq
      (throughTransfer
        (observablesRegressionNondispersiveModel.parametersAt
          observablesRegressionNondispersiveModel.angularFSR)) = _
  rw [observablesRegression_parametersAt_oneFSR_throughTransfer]
  norm_num [Complex.normSq_apply]

/-- The two independently reduced N5F response powers at zero and one FSR are equal. -/
lemma observablesRegression_n5f_oneFSR_throughPower_eq_zero :
    observablesRegressionN5FThroughPowerAt
        observablesRegressionNondispersiveModel.angularFSR
        observablesRegression_oneFSR_mem_responseDomain =
      observablesRegressionN5FThroughPowerAt 0
        observablesRegression_zero_mem_responseDomain := by
  rw [observablesRegression_n5f_oneFSR_throughPower,
    observablesRegressionN5FThroughPowerAt_zero]

end AddDrop

end

end Optics
