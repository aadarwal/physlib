/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Systems.MachZehnder.Basic

/-!
# Symbolic regressions for the Mach--Zehnder interferometer

## i. Overview

These regressions pin row `S-01` at the balanced field-amplitude point. They hand-expand the N7
50:50 coefficient and fixed-carrier phase values before specializing the N5 transfer result, so
the exact negative-quadrature cross phase at
`Physlib/Optics/Components/DirectionalCoupler.lean:68-77` remains observable. The phase-zero
fixture makes the first output dark; the phase-`π` fixture makes the second output dark.

The all-phase power check separately instantiates the N6 conservation route through
`MachZehnder.lossless_single_input_output_power_balance`. It does not establish unitarity by
checking an interferometer-specific response formula. The ratio-shape check independently expands
the balanced amplitude pair and verifies recovery of the arm phase-factor ratio.

This is a Physlib extension regression, not a HOL-corpus parity result. Powers are normalized
modal powers, not electromagnetic powers without a Poynting normalization. The fixtures have no
polarization or dispersion, and loss is absent because both arm amplitude factors are exactly
one.

## ii. Key results

- `machZehnderRegression_phase_zero_output_amplitudes`: the first balanced output is dark.
- `machZehnderRegression_phase_pi_output_amplitudes`: the second balanced output is dark.
- `machZehnderRegression_power_balance`: the two output powers sum to input power at every phase.
- `machZehnderRegression_phase_factor_ratio`: the balanced output ratio identifies arm phase.

## iii. Table of contents

- A. Hand-expanded component values
- B. Exact balanced phase points
- C. N6 power balance and phase-ratio identifiability

## iv. References

Row `S-01` is declared at `goal.md:2482`; the S1 extension milestone is at `goal.md:2150-2160`.
-/

@[expose] public section

namespace Optics

noncomputable section

namespace MachZehnder

/-! ## A. Hand-expanded component values -/

/-- The balanced through coefficient times the pinned N7 cross coefficient is exactly
`-I / 2`. -/
lemma machZehnderRegression_balanced_through_mul_cross :
    (balancedCoupler.throughAmplitude : ℂ) *
        DirectionalCoupler.crossCoefficient balancedCoupler = -Complex.I / 2 := by
  have hSqrtSquare : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  simp only [balancedCoupler, DirectionalCoupler.crossCoefficient,
    Complex.ofReal_div, Complex.ofReal_ofNat]
  ring_nf
  rw [hSqrtSquare]
  ring

/-- Direct expansion of the N7 phase factor gives `1` at zero and `-1` at `π`. -/
lemma machZehnderRegression_carrierPhaseFactor_points :
    MatchedPropagation.carrierPhaseFactor (0 : Real.Angle) = 1 ∧
      MatchedPropagation.carrierPhaseFactor (Real.pi : Real.Angle) = -1 := by
  constructor
  · simp [MatchedPropagation.carrierPhaseFactor]
  · rw [MatchedPropagation.carrierPhaseFactor, Real.Angle.neg_coe_pi,
      Real.Angle.coe_toCircle]
    simp

/-! ## B. Exact balanced phase points -/

/-- Row `S-01`: hand expansion of the N5 transfer at equal zero phases gives a dark first output
and a negative-quadrature second output. -/
theorem machZehnderRegression_phase_zero_output_amplitudes (input : ℂ) :
    ((netlist balancedPhaseZero).responseTransform
          (isWellPosed balancedPhaseZero)).toLinearMap
        (leftInput balancedPhaseZero input 0)
          (externalOutgoingEquiv balancedPhaseZero .outputFirst) = 0 ∧
      ((netlist balancedPhaseZero).responseTransform
          (isWellPosed balancedPhaseZero)).toLinearMap
        (leftInput balancedPhaseZero input 0)
          (externalOutgoingEquiv balancedPhaseZero .outputSecond) =
        -Complex.I * input := by
  rcases output_amplitudes balancedPhaseZero input 0 with ⟨hFirst, hSecond⟩
  have hSqrtSquare : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  constructor
  · refine hFirst.trans ?_
    simp only [balancedPhaseZero, balancedParameters, losslessArm,
      MatchedPropagation.transmissionCoefficient, balancedCoupler,
      DirectionalCoupler.crossCoefficient, mul_zero, add_zero,
      Complex.ofReal_div, Complex.ofReal_ofNat]
    simp only [MatchedPropagation.carrierPhaseFactor, neg_zero, Real.Angle.toCircle_zero,
      Circle.coe_one]
    ring_nf
    rw [hSqrtSquare, Complex.I_sq]
    ring
  · refine hSecond.trans ?_
    simp only [balancedPhaseZero, balancedParameters, losslessArm,
      MatchedPropagation.transmissionCoefficient, balancedCoupler,
      DirectionalCoupler.crossCoefficient, mul_zero, add_zero,
      Complex.ofReal_div, Complex.ofReal_ofNat]
    simp only [MatchedPropagation.carrierPhaseFactor, neg_zero, Real.Angle.toCircle_zero,
      Circle.coe_one]
    ring_nf
    rw [hSqrtSquare]
    norm_num
    ring

/-- The hand-expanded equal-phase fixture has an exactly dark first output. -/
lemma machZehnderRegression_phase_zero_dark_port (input : ℂ) :
    ((netlist balancedPhaseZero).responseTransform
          (isWellPosed balancedPhaseZero)).toLinearMap
        (leftInput balancedPhaseZero input 0)
          (externalOutgoingEquiv balancedPhaseZero .outputFirst) = 0 :=
  (machZehnderRegression_phase_zero_output_amplitudes input).1

/-- Row `S-01`: hand expansion at a lower-arm phase of `π` sends the input to the first output
and makes the second output dark. -/
theorem machZehnderRegression_phase_pi_output_amplitudes (input : ℂ) :
    ((netlist balancedPhasePi).responseTransform
          (isWellPosed balancedPhasePi)).toLinearMap
        (leftInput balancedPhasePi input 0)
          (externalOutgoingEquiv balancedPhasePi .outputFirst) = input ∧
      ((netlist balancedPhasePi).responseTransform
          (isWellPosed balancedPhasePi)).toLinearMap
        (leftInput balancedPhasePi input 0)
          (externalOutgoingEquiv balancedPhasePi .outputSecond) = 0 := by
  rcases output_amplitudes balancedPhasePi input 0 with ⟨hFirst, hSecond⟩
  have hSqrtSquare : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hPi : MatchedPropagation.carrierPhaseFactor (Real.pi : Real.Angle) = -1 := by
    rw [MatchedPropagation.carrierPhaseFactor, Real.Angle.neg_coe_pi,
      Real.Angle.coe_toCircle]
    simp
  constructor
  · refine hFirst.trans ?_
    simp only [balancedPhasePi, balancedParameters, losslessArm,
      MatchedPropagation.transmissionCoefficient, balancedCoupler,
      DirectionalCoupler.crossCoefficient, mul_zero, add_zero,
      Complex.ofReal_div, Complex.ofReal_ofNat]
    rw [show MatchedPropagation.carrierPhaseFactor (0 : Real.Angle) = 1 by
      simp [MatchedPropagation.carrierPhaseFactor], hPi]
    ring_nf
    rw [hSqrtSquare, Complex.I_sq]
    norm_num
    ring
  · refine hSecond.trans ?_
    simp only [balancedPhasePi, balancedParameters, losslessArm,
      MatchedPropagation.transmissionCoefficient, balancedCoupler,
      DirectionalCoupler.crossCoefficient, mul_zero, add_zero,
      Complex.ofReal_div, Complex.ofReal_ofNat]
    rw [show MatchedPropagation.carrierPhaseFactor (0 : Real.Angle) = 1 by
      simp [MatchedPropagation.carrierPhaseFactor], hPi]
    ring_nf

/-- The hand-expanded phase-`π` fixture has an exactly dark second output. -/
lemma machZehnderRegression_phase_pi_dark_port (input : ℂ) :
    ((netlist balancedPhasePi).responseTransform
          (isWellPosed balancedPhasePi)).toLinearMap
        (leftInput balancedPhasePi input 0)
          (externalOutgoingEquiv balancedPhasePi .outputSecond) = 0 :=
  (machZehnderRegression_phase_pi_output_amplitudes input).2

/-! ## C. N6 power balance and phase-ratio identifiability -/

/-- Row `S-01`: an independent specialization of the N6 conservation path gives power balance
for every balanced arm-phase pair. -/
lemma machZehnderRegression_power_balance
    (upperPhase lowerPhase : Real.Angle) (input : ℂ) :
    Complex.normSq
        (((netlist (balancedParameters upperPhase lowerPhase)).responseTransform
            (isWellPosed (balancedParameters upperPhase lowerPhase))).toLinearMap
          (leftInput (balancedParameters upperPhase lowerPhase) input 0)
            (externalOutgoingEquiv (balancedParameters upperPhase lowerPhase) .outputFirst)) +
      Complex.normSq
        (((netlist (balancedParameters upperPhase lowerPhase)).responseTransform
            (isWellPosed (balancedParameters upperPhase lowerPhase))).toLinearMap
          (leftInput (balancedParameters upperPhase lowerPhase) input 0)
            (externalOutgoingEquiv (balancedParameters upperPhase lowerPhase) .outputSecond)) =
      Complex.normSq input := by
  exact lossless_single_input_output_power_balance
    (balancedParameters upperPhase lowerPhase)
    (balancedParameters_isLossless upperPhase lowerPhase) input

/-- The hand-expanded balanced amplitude pair recovers the lower-to-upper arm phase-factor ratio
from the two output coordinates. -/
lemma machZehnderRegression_phase_factor_ratio
    (upperPhase lowerPhase : Real.Angle) (input : ℂ) (hInput : input ≠ 0) :
    let upper := MatchedPropagation.carrierPhaseFactor upperPhase
    let lower := MatchedPropagation.carrierPhaseFactor lowerPhase
    let firstOutput := (upper - lower) * input / 2
    let secondOutput := -Complex.I * (upper + lower) * input / 2
    (-firstOutput + Complex.I * secondOutput) /
        (firstOutput + Complex.I * secondOutput) = lower / upper := by
  dsimp only
  have hUpper : MatchedPropagation.carrierPhaseFactor upperPhase ≠ 0 := by
    intro hZero
    have hNorm := MatchedPropagation.normSq_carrierPhaseFactor upperPhase
    simp [hZero] at hNorm
  ring_nf
  field_simp [hUpper, hInput]
  rw [Complex.I_sq]
  ring

end MachZehnder

end

end Optics
