/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Components.Retarder.Regression
public import Physlib.Optics.Interfaces.PlanarDielectric.SupercriticalFresnelRegression
public import Physlib.Optics.Interfaces.PlanarDielectric.TotalInternalReflectionRetarder

/-!
# Exact regression for total-internal-reflection retardance

## i. Overview

This file supplies two independent regression paths for the total-internal-reflection retarder
bridge.

The first is an exact physically shell-compatible coefficient-design fixture. Its incident-side
admittance and relative refractive index are `sqrt (1 + sqrt 2)`, while its transmitted-side
admittance and index are one. The incident normal factor is `sqrt 2 / 2`; the normalized decay
ratio is that normal factor divided by the incident admittance. The resulting `s` and `p`
reflection phases are exactly `pi / 4` and `pi / 2`, so one reflection has retarder parameter
`-pi / 4`. Self-composition therefore gives a negative quarter-wave plate up to its common unit
Jones phase.

The second path reuses the existing unequal-admittance three-wave boundary fixture and checks that
its stored reflected Jones data is exactly the action of the new diagonal transform. This catches
coefficient ordering or normalization errors independently of the quarter-wave design.

## ii. Key results

- `totalInternalReflectionRetarderRegression_hasCriticalAngleContrast`: the design has the strict
  material contrast required for a critical angle.
- `totalInternalReflectionRetarderRegression_reflectionCoefficients`: the raw Fresnel formulas
  independently reduce to the exact complex coefficients used by the design.
- `totalInternalReflectionRetarderRegression_phaseShifts`: exact `s` and `p` phases.
- `totalInternalReflectionRetarderRegression_transmittedNormalRadicandData`: exact normalized
  negative-radicand compatibility of the incident normal factor and decay ratio.
- `totalInternalReflectionRetarderRegression_relativePhase`: exact physical `p-s` phase.
- `totalInternalReflectionRetarderRegression_retardance`: exact one-bounce retarder parameter.
- `totalInternalReflectionRetarderRegression_comp_self_eq_negativeQuarterWavePlate`: exact
  matrix self-composition law up to common phase.
- `totalInternalReflectionRetarderRegression_comp_self_act_diagonal`: the sign-sensitive
  diagonal-to-positive-quadrature action up to common phase.
- `supercriticalFresnelRegression_reflectedJones_eq_totalInternalReflectionJonesMatrix_act`:
  an independent coefficient-action check on the unequal-admittance boundary fixture.

## iii. Table of contents

- A. Exact admittance design
- B. Exact phases and retardance
- C. Matrix self-composition
- D. Unequal-admittance coefficient-action fixture

## iv. References

The design fixture proves the incident-normal bounds and the normalized negative-radicand shell
identity, but does not construct a complete three-wave boundary configuration or a two-face prism
geometry. Interpreting matrix self-composition as two bounces requires the caller to identify the
intermediate `s`/`p` coordinates externally and to handle inter-bounce path phase. The regression
assigns no circular-polarization handedness name and makes no modal-power claim.

-/

@[expose] public section

namespace Optics

open Electromagnetism Electromagnetism.ThreeDimension Matrix PlanarDielectricInterface
open ClassicalMechanics.ComplexWaveVector
open Electromagnetism.ThreeDimension.ComplexMonochromaticPlaneWave

noncomputable section

/-!

## A. Exact admittance design

-/

/-- The exact incident-side medium for the quarter-wave total-reflection design. -/
def totalInternalReflectionRetarderRegressionNegativeMedium : HomogeneousIsotropicMedium where
  ε := 1 + Real.sqrt 2
  μ := 1
  ε_pos := by positivity
  μ_pos := by norm_num

/-- The exact incident-side admittance of the total-reflection design. -/
def totalInternalReflectionRetarderRegressionAdmittance : ℝ :=
  Real.sqrt (1 + Real.sqrt 2)

/-- The unit-admittance transmitted-side medium of the exact total-reflection design. -/
def totalInternalReflectionRetarderRegressionPositiveMedium : HomogeneousIsotropicMedium where
  ε := 1
  μ := 1
  ε_pos := by norm_num
  μ_pos := by norm_num

/-- The exact incident normal factor `sqrt 2 / 2` of the total-reflection design. -/
def totalInternalReflectionRetarderRegressionIncidentNormalFactor : ℝ :=
  Real.sqrt 2 / 2

/-- The normalized transmitted decay ratio of the exact total-reflection design. -/
def totalInternalReflectionRetarderRegressionDecayRatio : ℝ :=
  totalInternalReflectionRetarderRegressionIncidentNormalFactor /
    totalInternalReflectionRetarderRegressionAdmittance

/-- The exact interface used by the quarter-wave coefficient design. -/
def totalInternalReflectionRetarderRegressionInterface : PlanarDielectricInterface where
  plane := complexDecayRegressionPlane
  negativeMedium := totalInternalReflectionRetarderRegressionNegativeMedium
  positiveMedium := totalInternalReflectionRetarderRegressionPositiveMedium

private lemma totalInternalReflectionRetarderRegression_sqrtTwo_sq :
    (Real.sqrt 2) ^ 2 = 2 :=
  Real.sq_sqrt (by norm_num)

/-- The exact incident-side admittance is strictly positive. -/
lemma totalInternalReflectionRetarderRegressionAdmittance_pos :
    0 < totalInternalReflectionRetarderRegressionAdmittance := by
  exact Real.sqrt_pos_of_pos (by positivity)

private lemma totalInternalReflectionRetarderRegressionAdmittance_sq :
    totalInternalReflectionRetarderRegressionAdmittance ^ 2 = 1 + Real.sqrt 2 := by
  rw [totalInternalReflectionRetarderRegressionAdmittance,
    Real.sq_sqrt (by positivity)]

/-- The exact incident normal factor lies strictly between zero and one. -/
lemma totalInternalReflectionRetarderRegressionIncidentNormalFactor_mem_Ioo :
    totalInternalReflectionRetarderRegressionIncidentNormalFactor ∈ Set.Ioo 0 1 := by
  constructor
  · exact div_pos (Real.sqrt_pos.2 (by norm_num)) (by norm_num)
  · rw [totalInternalReflectionRetarderRegressionIncidentNormalFactor]
    nlinarith [Real.sqrt_two_lt_three_halves]

private lemma totalInternalReflectionRetarderRegressionIncidentNormalFactor_sq :
    totalInternalReflectionRetarderRegressionIncidentNormalFactor ^ 2 = 1 / 2 := by
  rw [totalInternalReflectionRetarderRegressionIncidentNormalFactor, div_pow,
    totalInternalReflectionRetarderRegression_sqrtTwo_sq]
  norm_num

/-- The exact normalized decay ratio is strictly positive. -/
lemma totalInternalReflectionRetarderRegressionDecayRatio_pos :
    0 < totalInternalReflectionRetarderRegressionDecayRatio := by
  exact div_pos totalInternalReflectionRetarderRegressionIncidentNormalFactor_mem_Ioo.1
    totalInternalReflectionRetarderRegressionAdmittance_pos

private lemma totalInternalReflectionRetarderRegressionDecayRatio_sq :
    totalInternalReflectionRetarderRegressionDecayRatio ^ 2 =
      (Real.sqrt 2 - 1) / 2 := by
  rw [totalInternalReflectionRetarderRegressionDecayRatio, div_pow,
    totalInternalReflectionRetarderRegressionIncidentNormalFactor_sq,
    totalInternalReflectionRetarderRegressionAdmittance_sq]
  rw [div_eq_iff (by positivity : 1 + Real.sqrt 2 ≠ 0)]
  nlinarith [totalInternalReflectionRetarderRegression_sqrtTwo_sq]

private lemma totalInternalReflectionRetarderRegression_admittance_mul_decayRatio :
    totalInternalReflectionRetarderRegressionAdmittance *
        totalInternalReflectionRetarderRegressionDecayRatio =
      totalInternalReflectionRetarderRegressionIncidentNormalFactor := by
  rw [totalInternalReflectionRetarderRegressionDecayRatio]
  field_simp [totalInternalReflectionRetarderRegressionAdmittance_pos.ne']

private lemma totalInternalReflectionRetarderRegression_sCoefficient_realIdentity :
    totalInternalReflectionRetarderRegressionAdmittance *
        totalInternalReflectionRetarderRegressionIncidentNormalFactor =
      totalInternalReflectionRetarderRegressionIncidentNormalFactor *
        (totalInternalReflectionRetarderRegressionAdmittance *
            totalInternalReflectionRetarderRegressionIncidentNormalFactor +
          totalInternalReflectionRetarderRegressionDecayRatio) := by
  rw [totalInternalReflectionRetarderRegressionDecayRatio,
    totalInternalReflectionRetarderRegressionIncidentNormalFactor]
  field_simp [totalInternalReflectionRetarderRegressionAdmittance_pos.ne']
  nlinarith [totalInternalReflectionRetarderRegressionAdmittance_sq,
    totalInternalReflectionRetarderRegression_sqrtTwo_sq]

private lemma totalInternalReflectionRetarderRegression_sCoefficient_imagIdentity :
    totalInternalReflectionRetarderRegressionDecayRatio =
      totalInternalReflectionRetarderRegressionIncidentNormalFactor *
        (totalInternalReflectionRetarderRegressionAdmittance *
            totalInternalReflectionRetarderRegressionIncidentNormalFactor -
          totalInternalReflectionRetarderRegressionDecayRatio) := by
  rw [totalInternalReflectionRetarderRegressionDecayRatio,
    totalInternalReflectionRetarderRegressionIncidentNormalFactor]
  field_simp [totalInternalReflectionRetarderRegressionAdmittance_pos.ne']
  nlinarith [totalInternalReflectionRetarderRegressionAdmittance_sq,
    totalInternalReflectionRetarderRegression_sqrtTwo_sq]

/-- The exact incident-side medium has admittance `sqrt (1 + sqrt 2)`. -/
lemma totalInternalReflectionRetarderRegression_negativeAdmittance :
    totalInternalReflectionRetarderRegressionNegativeMedium.waveImpedance⁻¹ =
      totalInternalReflectionRetarderRegressionAdmittance := by
  rw [HomogeneousIsotropicMedium.waveImpedance]
  change (Real.sqrt (1 / (1 + Real.sqrt 2)))⁻¹ =
    Real.sqrt (1 + Real.sqrt 2)
  rw [Real.sqrt_div (by norm_num)]
  simp only [Real.sqrt_one, one_div, inv_inv]

/-- The exact transmitted-side medium has unit admittance. -/
lemma totalInternalReflectionRetarderRegression_positiveAdmittance :
    totalInternalReflectionRetarderRegressionInterface.positiveMedium.waveImpedance⁻¹ = 1 := by
  norm_num [HomogeneousIsotropicMedium.waveImpedance,
    totalInternalReflectionRetarderRegressionInterface,
    totalInternalReflectionRetarderRegressionPositiveMedium]

/-- At unit frequency, the material data, incident normal factor, and normalized decay ratio obey
the exact negative transmitted-normal-radicand shell identity. -/
lemma totalInternalReflectionRetarderRegression_transmittedNormalRadicandData :
    totalInternalReflectionRetarderRegressionInterface.positiveMedium.ε *
          totalInternalReflectionRetarderRegressionInterface.positiveMedium.μ -
        totalInternalReflectionRetarderRegressionInterface.negativeMedium.ε *
          totalInternalReflectionRetarderRegressionInterface.negativeMedium.μ *
          (1 - totalInternalReflectionRetarderRegressionIncidentNormalFactor ^ 2) =
      -(totalInternalReflectionRetarderRegressionDecayRatio ^ 2) := by
  rw [totalInternalReflectionRetarderRegressionIncidentNormalFactor_sq,
    totalInternalReflectionRetarderRegressionDecayRatio_sq]
  norm_num [totalInternalReflectionRetarderRegressionInterface,
    totalInternalReflectionRetarderRegressionNegativeMedium,
    totalInternalReflectionRetarderRegressionPositiveMedium]
  ring

/-- The exact interface has the strict material contrast required for a critical angle. -/
lemma totalInternalReflectionRetarderRegression_hasCriticalAngleContrast :
    totalInternalReflectionRetarderRegressionInterface.HasCriticalAngleContrast := by
  rw [PlanarDielectricInterface.hasCriticalAngleContrast_iff_positive_epsilon_mu_lt_negative]
  norm_num [totalInternalReflectionRetarderRegressionInterface,
    totalInternalReflectionRetarderRegressionNegativeMedium,
    totalInternalReflectionRetarderRegressionPositiveMedium]

/-- The `s` phase arctangent ratio of the design is exactly `sqrt 2 - 1`. -/
lemma totalInternalReflectionRetarderRegression_sRatio :
    (totalInternalReflectionRetarderRegressionInterface.positiveMedium.waveImpedance⁻¹ *
          totalInternalReflectionRetarderRegressionDecayRatio) /
        (totalInternalReflectionRetarderRegressionInterface.negativeMedium.waveImpedance⁻¹ *
          totalInternalReflectionRetarderRegressionIncidentNormalFactor) =
      Real.sqrt 2 - 1 := by
  rw [show totalInternalReflectionRetarderRegressionInterface.negativeMedium =
      totalInternalReflectionRetarderRegressionNegativeMedium by rfl,
    totalInternalReflectionRetarderRegression_positiveAdmittance,
    totalInternalReflectionRetarderRegression_negativeAdmittance]
  rw [one_mul, totalInternalReflectionRetarderRegressionDecayRatio]
  field_simp [totalInternalReflectionRetarderRegressionAdmittance_pos.ne',
    totalInternalReflectionRetarderRegressionIncidentNormalFactor_mem_Ioo.1.ne']
  nlinarith [totalInternalReflectionRetarderRegressionAdmittance_sq,
    totalInternalReflectionRetarderRegression_sqrtTwo_sq]

/-- The `p` phase arctangent ratio of the design is exactly one. -/
lemma totalInternalReflectionRetarderRegression_pRatio :
    (totalInternalReflectionRetarderRegressionInterface.negativeMedium.waveImpedance⁻¹ *
          totalInternalReflectionRetarderRegressionDecayRatio) /
        (totalInternalReflectionRetarderRegressionInterface.positiveMedium.waveImpedance⁻¹ *
          totalInternalReflectionRetarderRegressionIncidentNormalFactor) = 1 := by
  rw [show totalInternalReflectionRetarderRegressionInterface.negativeMedium =
      totalInternalReflectionRetarderRegressionNegativeMedium by rfl,
    totalInternalReflectionRetarderRegression_positiveAdmittance,
    totalInternalReflectionRetarderRegression_negativeAdmittance]
  rw [one_mul, totalInternalReflectionRetarderRegressionDecayRatio]
  field_simp [totalInternalReflectionRetarderRegressionAdmittance_pos.ne',
    totalInternalReflectionRetarderRegressionIncidentNormalFactor_mem_Ioo.1.ne']

/-!

## B. Exact phases and retardance

-/

private lemma totalInternalReflectionRetarderRegression_arctan_sqrtTwo_sub_one :
    Real.arctan (Real.sqrt 2 - 1) = Real.pi / 8 := by
  have hLower : -1 < Real.sqrt 2 - 1 := by
    nlinarith [Real.one_lt_sqrt_two]
  have hUpper : Real.sqrt 2 - 1 < 1 := by
    nlinarith [Real.sqrt_two_lt_three_halves]
  have hFraction : 2 * (Real.sqrt 2 - 1) /
      (1 - (Real.sqrt 2 - 1) ^ 2) = 1 := by
    have hDenominator : 1 - (Real.sqrt 2 - 1) ^ 2 ≠ 0 := by
      have hSquare : (Real.sqrt 2 - 1) ^ 2 < (1 : ℝ) ^ 2 :=
        (sq_lt_sq₀ (by nlinarith [Real.one_lt_sqrt_two]) (by norm_num)).2 hUpper
      nlinarith
    apply (div_eq_iff hDenominator).2
    nlinarith [totalInternalReflectionRetarderRegression_sqrtTwo_sq]
  have hDouble := Real.two_mul_arctan hLower hUpper
  rw [hFraction, Real.arctan_one] at hDouble
  linarith

/-- The exact design has `s` reflection phase `pi / 4` and `p` reflection phase `pi / 2`. -/
lemma totalInternalReflectionRetarderRegression_phaseShifts :
    totalInternalReflectionRetarderRegressionInterface.sTotalInternalReflectionPhaseShift
        totalInternalReflectionRetarderRegressionIncidentNormalFactor
        totalInternalReflectionRetarderRegressionDecayRatio =
        ((Real.pi / 4 : ℝ) : Real.Angle) ∧
      totalInternalReflectionRetarderRegressionInterface.pTotalInternalReflectionPhaseShift
        totalInternalReflectionRetarderRegressionIncidentNormalFactor
        totalInternalReflectionRetarderRegressionDecayRatio =
        ((Real.pi / 2 : ℝ) : Real.Angle) := by
  constructor
  · rw [sTotalInternalReflectionPhaseShift_eq_two_arctan
        totalInternalReflectionRetarderRegressionInterface
          totalInternalReflectionRetarderRegressionIncidentNormalFactor_mem_Ioo.1
          totalInternalReflectionRetarderRegressionDecayRatio_pos,
      totalInternalReflectionRetarderRegression_sRatio,
      totalInternalReflectionRetarderRegression_arctan_sqrtTwo_sub_one,
      ← Real.Angle.coe_nsmul]
    congr 1
    ring
  · rw [pTotalInternalReflectionPhaseShift_eq_two_arctan
        totalInternalReflectionRetarderRegressionInterface
          totalInternalReflectionRetarderRegressionIncidentNormalFactor_mem_Ioo.1
          totalInternalReflectionRetarderRegressionDecayRatio_pos,
      totalInternalReflectionRetarderRegression_pRatio, Real.arctan_one,
      ← Real.Angle.coe_nsmul]
    congr 1
    ring

/-- The exact design has raw reflection coefficients
`(sqrt 2 / 2) * (1 + I)` in `s` and `I` in `p`. -/
lemma totalInternalReflectionRetarderRegression_reflectionCoefficients :
    totalInternalReflectionRetarderRegressionInterface.complexSFresnelReflectionCoefficient
          (totalInternalReflectionRetarderRegressionIncidentNormalFactor : ℂ)
          (-Complex.I * (totalInternalReflectionRetarderRegressionDecayRatio : ℂ)) =
        ((Real.sqrt 2 / 2 : ℝ) : ℂ) * (1 + Complex.I) ∧
      totalInternalReflectionRetarderRegressionInterface.complexPFresnelReflectionCoefficient
          (totalInternalReflectionRetarderRegressionIncidentNormalFactor : ℂ)
          (-Complex.I * (totalInternalReflectionRetarderRegressionDecayRatio : ℂ)) =
        Complex.I := by
  rw [PlanarDielectricInterface.complexSFresnelReflectionCoefficient,
    PlanarDielectricInterface.complexPFresnelReflectionCoefficient,
    PlanarDielectricInterface.complexSFresnelDenominator,
    PlanarDielectricInterface.complexPFresnelDenominator]
  have hNegative :
      totalInternalReflectionRetarderRegressionInterface.negativeMedium.waveImpedance⁻¹ =
        totalInternalReflectionRetarderRegressionAdmittance := by
    exact totalInternalReflectionRetarderRegression_negativeAdmittance
  have hPositive :
      totalInternalReflectionRetarderRegressionInterface.positiveMedium.waveImpedance⁻¹ = 1 := by
    exact totalInternalReflectionRetarderRegression_positiveAdmittance
  rw [hNegative, hPositive]
  constructor
  · have hDenominator :
        (totalInternalReflectionRetarderRegressionAdmittance : ℂ) *
              (totalInternalReflectionRetarderRegressionIncidentNormalFactor : ℂ) +
            (1 : ℂ) *
              (-Complex.I * (totalInternalReflectionRetarderRegressionDecayRatio : ℂ)) ≠ 0 := by
      intro hZero
      have hReal := congrArg Complex.re hZero
      norm_num [Complex.mul_re] at hReal
      rcases hReal with hAdmittance | hIncident
      · exact totalInternalReflectionRetarderRegressionAdmittance_pos.ne' hAdmittance
      · exact totalInternalReflectionRetarderRegressionIncidentNormalFactor_mem_Ioo.1.ne'
          hIncident
    apply (div_eq_iff hDenominator).2
    apply Complex.ext
    · simpa [totalInternalReflectionRetarderRegressionIncidentNormalFactor,
        Complex.mul_re, Complex.mul_im, mul_add] using
        totalInternalReflectionRetarderRegression_sCoefficient_realIdentity
    · simpa [totalInternalReflectionRetarderRegressionIncidentNormalFactor,
        Complex.mul_re, Complex.mul_im, mul_sub, sub_eq_add_neg, mul_add, add_comm] using
        totalInternalReflectionRetarderRegression_sCoefficient_imagIdentity
  · have hADecay :
        (totalInternalReflectionRetarderRegressionAdmittance : ℂ) *
            (totalInternalReflectionRetarderRegressionDecayRatio : ℂ) =
          (totalInternalReflectionRetarderRegressionIncidentNormalFactor : ℂ) := by
      exact_mod_cast totalInternalReflectionRetarderRegression_admittance_mul_decayRatio
    rw [show (totalInternalReflectionRetarderRegressionAdmittance : ℂ) *
          (-Complex.I * (totalInternalReflectionRetarderRegressionDecayRatio : ℂ)) =
        -Complex.I *
          (totalInternalReflectionRetarderRegressionIncidentNormalFactor : ℂ) by
      rw [← hADecay]
      ring]
    have hIncident :
        (totalInternalReflectionRetarderRegressionIncidentNormalFactor : ℂ) ≠ 0 := by
      exact_mod_cast
        totalInternalReflectionRetarderRegressionIncidentNormalFactor_mem_Ioo.1.ne'
    field_simp [hIncident, Complex.I_ne_zero]
    norm_num [Complex.ext_iff, Complex.div_re, Complex.div_im, Complex.normSq]

/-- Squaring the two exact raw reflection coefficients gives `I` in `s` and `-1` in `p`. -/
lemma totalInternalReflectionRetarderRegression_reflectionCoefficientSquares :
    (totalInternalReflectionRetarderRegressionInterface.complexSFresnelReflectionCoefficient
          (totalInternalReflectionRetarderRegressionIncidentNormalFactor : ℂ)
          (-Complex.I * (totalInternalReflectionRetarderRegressionDecayRatio : ℂ))) ^ 2 =
        Complex.I ∧
      (totalInternalReflectionRetarderRegressionInterface.complexPFresnelReflectionCoefficient
          (totalInternalReflectionRetarderRegressionIncidentNormalFactor : ℂ)
          (-Complex.I * (totalInternalReflectionRetarderRegressionDecayRatio : ℂ))) ^ 2 =
        -1 := by
  rw [totalInternalReflectionRetarderRegression_reflectionCoefficients.1,
    totalInternalReflectionRetarderRegression_reflectionCoefficients.2]
  constructor
  · change (((totalInternalReflectionRetarderRegressionIncidentNormalFactor : ℝ) : ℂ) *
      (1 + Complex.I)) ^ 2 = Complex.I
    rw [mul_pow]
    have hIncidentSquare :
        ((totalInternalReflectionRetarderRegressionIncidentNormalFactor ^ 2 : ℝ) : ℂ) =
          (1 / 2 : ℂ) := by
      simpa using congrArg (fun x : ℝ ↦ (x : ℂ))
        totalInternalReflectionRetarderRegressionIncidentNormalFactor_sq
    push_cast at hIncidentSquare
    rw [hIncidentSquare, show (1 + Complex.I) ^ 2 = 2 * Complex.I by
      calc
        (1 + Complex.I) ^ 2 = 1 + 2 * Complex.I + Complex.I ^ 2 := by ring
        _ = 2 * Complex.I := by rw [Complex.I_sq]; ring]
    ring
  · exact Complex.I_sq

/-- The physical reflected `p-s` phase of the exact design is `pi / 4`. -/
lemma totalInternalReflectionRetarderRegression_relativePhase :
    totalInternalReflectionRetarderRegressionInterface.totalInternalReflectionRelativePhase
        totalInternalReflectionRetarderRegressionIncidentNormalFactor
        totalInternalReflectionRetarderRegressionDecayRatio =
      ((Real.pi / 4 : ℝ) : Real.Angle) := by
  rw [totalInternalReflectionRelativePhase_eq_two_arctan_sub
      totalInternalReflectionRetarderRegressionInterface
        totalInternalReflectionRetarderRegressionIncidentNormalFactor_mem_Ioo.1
        totalInternalReflectionRetarderRegressionDecayRatio_pos,
    totalInternalReflectionRetarderRegression_pRatio,
    totalInternalReflectionRetarderRegression_sRatio, Real.arctan_one,
    totalInternalReflectionRetarderRegression_arctan_sqrtTwo_sub_one,
    ← Real.Angle.coe_nsmul, ← Real.Angle.coe_nsmul, ← Real.Angle.coe_sub]
  congr 1
  ring

/-- One reflection in the exact design has retarder parameter `-pi / 4`. -/
lemma totalInternalReflectionRetarderRegression_retardance :
    totalInternalReflectionRetarderRegressionInterface.totalInternalReflectionRetardance
        totalInternalReflectionRetarderRegressionIncidentNormalFactor
        totalInternalReflectionRetarderRegressionDecayRatio =
      ((-Real.pi / 4 : ℝ) : Real.Angle) := by
  rw [totalInternalReflectionRetardance_eq_neg_relativePhase,
    totalInternalReflectionRetarderRegression_relativePhase, ← Real.Angle.coe_neg]
  congr 1
  ring

private lemma totalInternalReflectionRetarderRegression_doubleRetardance :
    totalInternalReflectionRetarderRegressionInterface.totalInternalReflectionRetardance
          totalInternalReflectionRetarderRegressionIncidentNormalFactor
          totalInternalReflectionRetarderRegressionDecayRatio +
        totalInternalReflectionRetarderRegressionInterface.totalInternalReflectionRetardance
          totalInternalReflectionRetarderRegressionIncidentNormalFactor
          totalInternalReflectionRetarderRegressionDecayRatio =
      ((-Real.pi / 2 : ℝ) : Real.Angle) := by
  rw [totalInternalReflectionRetarderRegression_retardance,
    ← Real.Angle.coe_add]
  congr 1
  ring

/-!

## C. Matrix self-composition

-/

/-- Self-composition of the exact design matrix gives a negative quarter-wave plate up to the
common squared `s` reflection phase. -/
lemma totalInternalReflectionRetarderRegression_comp_self_eq_negativeQuarterWavePlate :
    (totalInternalReflectionRetarderRegressionInterface.totalInternalReflectionJonesMatrix
        totalInternalReflectionRetarderRegressionIncidentNormalFactor
        totalInternalReflectionRetarderRegressionDecayRatio).comp
      (totalInternalReflectionRetarderRegressionInterface.totalInternalReflectionJonesMatrix
        totalInternalReflectionRetarderRegressionIncidentNormalFactor
        totalInternalReflectionRetarderRegressionDecayRatio) =
    (JonesMatrix.negativeQuarterWavePlate 0).scale
      ((totalInternalReflectionRetarderRegressionInterface.complexSFresnelReflectionCoefficient
          (totalInternalReflectionRetarderRegressionIncidentNormalFactor : ℂ)
          (-Complex.I * (totalInternalReflectionRetarderRegressionDecayRatio : ℂ))) ^ 2) := by
  simpa using
    totalInternalReflectionJonesMatrix_comp_self_eq_scaled_negativeQuarterWavePlate
      totalInternalReflectionRetarderRegressionInterface
        totalInternalReflectionRetarderRegressionIncidentNormalFactor_mem_Ioo.1
        totalInternalReflectionRetarderRegression_doubleRetardance

/-- The matrix self-composition sends diagonal Jones data to positive quadrature up to its common
squared `s` reflection phase. -/
lemma totalInternalReflectionRetarderRegression_comp_self_act_diagonal :
    ((totalInternalReflectionRetarderRegressionInterface.totalInternalReflectionJonesMatrix
        totalInternalReflectionRetarderRegressionIncidentNormalFactor
        totalInternalReflectionRetarderRegressionDecayRatio).comp
      (totalInternalReflectionRetarderRegressionInterface.totalInternalReflectionJonesMatrix
        totalInternalReflectionRetarderRegressionIncidentNormalFactor
        totalInternalReflectionRetarderRegressionDecayRatio)).act JonesVector.diagonal =
    JonesVector.scale
      ((totalInternalReflectionRetarderRegressionInterface.complexSFresnelReflectionCoefficient
          (totalInternalReflectionRetarderRegressionIncidentNormalFactor : ℂ)
          (-Complex.I * (totalInternalReflectionRetarderRegressionDecayRatio : ℂ))) ^ 2)
      JonesVector.plusIQuadrature := by
  rw [totalInternalReflectionRetarderRegression_comp_self_eq_negativeQuarterWavePlate,
    JonesMatrix.scale_act, JonesMatrix.negativeQuarterWavePlate_zero_act_diagonal]

/-- The common phase of the matrix self-composition disappears from its Mueller action. -/
lemma totalInternalReflectionRetarderRegression_comp_self_mueller :
    ((totalInternalReflectionRetarderRegressionInterface.totalInternalReflectionJonesMatrix
        totalInternalReflectionRetarderRegressionIncidentNormalFactor
        totalInternalReflectionRetarderRegressionDecayRatio).comp
      (totalInternalReflectionRetarderRegressionInterface.totalInternalReflectionJonesMatrix
        totalInternalReflectionRetarderRegressionIncidentNormalFactor
        totalInternalReflectionRetarderRegressionDecayRatio)).mueller =
    (JonesMatrix.negativeQuarterWavePlate 0).mueller := by
  rw [totalInternalReflectionRetarderRegression_comp_self_eq_negativeQuarterWavePlate]
  apply JonesMatrix.mueller_scale_of_norm_eq_one
  have hNorm :
      ‖totalInternalReflectionRetarderRegressionInterface.complexSFresnelReflectionCoefficient
        (totalInternalReflectionRetarderRegressionIncidentNormalFactor : ℂ)
        (-Complex.I * (totalInternalReflectionRetarderRegressionDecayRatio : ℂ))‖ = 1 := by
    simpa using
      PlanarDielectricInterface.complexSFresnelReflectionCoefficient_norm_of_neg_I_mul
        totalInternalReflectionRetarderRegressionInterface
          totalInternalReflectionRetarderRegressionIncidentNormalFactor_mem_Ioo.1
  rw [norm_pow, hNorm]
  norm_num

/-!

## D. Unequal-admittance coefficient-action fixture

-/

private lemma totalInternalReflectionRetarderRegression_planeFrame_axis_zero :
    jonesBoundaryRegressionAxisZero =
      complexDecayRegressionPolarizationFrame.planeFrame.axis 0 := by
  rw [PositiveNormalDecayPolarizationFrame.planeFrame_axis_zero]
  symm
  ext i
  fin_cases i <;>
    simp [PositiveNormalDecayPolarizationFrame.realSAxis,
      complexDecayRegressionPolarizationFrame, positiveNormalDecayRegression,
      positiveNormalDecayRegressionTangentialVector,
      PositiveNormalDecayWaveVector.normalVector,
      complexDecayRegressionPlane, positiveNormalDecayRegressionDirection,
      jonesBoundaryRegressionAxisZero, NormedSpace.normalize,
      EuclideanSpace.norm_eq, Fin.sum_univ_three, crossProduct]

private lemma totalInternalReflectionRetarderRegression_incidentFrame_align :
    jonesBoundaryRegressionIncidentFrame.axis 0 =
      (PlanarDielectricWaveConfiguration.positiveNormalDecayTransmittedPolarizationFrame
        supercriticalFresnelRegressionConfiguration
        supercriticalFresnelRegression_configuration_transmittedNormalRadicand_neg).planeFrame.axis
          0 := by
  rw [supercriticalFresnelRegression_configuration_polarizationFrame]
  exact totalInternalReflectionRetarderRegression_planeFrame_axis_zero

private lemma totalInternalReflectionRetarderRegression_reflectedFrame_align :
    jonesBoundaryRegressionReflectedFrame.axis 0 =
      (PlanarDielectricWaveConfiguration.positiveNormalDecayTransmittedPolarizationFrame
        supercriticalFresnelRegressionConfiguration
        supercriticalFresnelRegression_configuration_transmittedNormalRadicand_neg).planeFrame.axis
          0 := by
  rw [supercriticalFresnelRegression_configuration_polarizationFrame]
  exact totalInternalReflectionRetarderRegression_planeFrame_axis_zero

private lemma totalInternalReflectionRetarderRegression_incidentConnector :
    IsReferencedMaterialJonesWave
      supercriticalFresnelRegressionConfiguration.interface.plane
      supercriticalFresnelRegressionConfiguration.interface.negativeMedium
      supercriticalFresnelRegressionConfiguration.incident jonesBoundaryRegressionIncidentFrame
      supercriticalFresnelRegressionIncidentJones := by
  simpa only [supercriticalFresnelRegressionConfiguration,
    supercriticalFresnelRegressionInterface] using
      supercriticalFresnelRegression_incident_isReferencedMaterialJonesWave

private lemma totalInternalReflectionRetarderRegression_reflectedConnector :
    IsZeroOrReferencedMaterialJonesWave
      supercriticalFresnelRegressionConfiguration.interface.plane
      supercriticalFresnelRegressionConfiguration.interface.negativeMedium
      supercriticalFresnelRegressionConfiguration.reflected jonesBoundaryRegressionReflectedFrame
      supercriticalFresnelRegressionReflectedJones := by
  exact Or.inr (by
    simpa only [supercriticalFresnelRegressionConfiguration,
      supercriticalFresnelRegressionInterface] using
        supercriticalFresnelRegression_reflected_isReferencedMaterialJonesWave)

private lemma totalInternalReflectionRetarderRegression_reflection_guard :
    supercriticalFresnelRegressionConfiguration.reflected.electricAmplitude = 0 ∨
      supercriticalFresnelRegressionConfiguration.interface.plane.normalComponent
          jonesBoundaryRegressionReflectedFrame.propagationVector =
        -supercriticalFresnelRegressionConfiguration.interface.plane.normalComponent
          jonesBoundaryRegressionIncidentFrame.propagationVector := by
  right
  rw [supercriticalFresnelRegression_reflectedNormalComponent,
    supercriticalFresnelRegression_incidentNormalComponent]
  norm_num

private lemma totalInternalReflectionRetarderRegression_incidentNormalComponent_pos :
    0 < supercriticalFresnelRegressionConfiguration.interface.plane.normalComponent
      jonesBoundaryRegressionIncidentFrame.propagationVector := by
  rw [supercriticalFresnelRegression_incidentNormalComponent]
  norm_num

/-- The reflected Jones data in the exact unequal-admittance boundary fixture is the action of
the new total-internal-reflection Jones transform, as derived by the connected electric and
magnetic boundary wrapper. -/
lemma supercriticalFresnelRegression_reflectedJones_eq_totalInternalReflectionJonesMatrix_act :
    supercriticalFresnelRegressionReflectedJones =
      (supercriticalFresnelRegressionInterface.totalInternalReflectionJonesMatrix
        (4 / 5) (4 / 3)).act supercriticalFresnelRegressionIncidentJones := by
  have hConnected :=
    PlanarDielectricWaveConfiguration.reflectedJones_eq_totalInternalReflectionJonesMatrix_act
      (configuration := supercriticalFresnelRegressionConfiguration)
      supercriticalFresnelRegression_exact_hasReferencedJointElectricBalance
      supercriticalFresnelRegression_exact_hasReferencedTangentialMagneticFieldStrengthBalance
      supercriticalFresnelRegression_configuration_transmittedNormalRadicand_neg
      totalInternalReflectionRetarderRegression_incidentConnector
      totalInternalReflectionRetarderRegression_reflectedConnector
      supercriticalFresnelRegression_transmitted_eq_candidate
      totalInternalReflectionRetarderRegression_incidentFrame_align
      (fun _ ↦ totalInternalReflectionRetarderRegression_reflectedFrame_align)
      totalInternalReflectionRetarderRegression_reflection_guard
      totalInternalReflectionRetarderRegression_incidentNormalComponent_pos
  rw [supercriticalFresnelRegression_incidentNormalComponent,
    supercriticalFresnelRegression_configuration_transmittedNormalRadicand] at hConnected
  norm_num [supercriticalFresnelRegressionConfiguration,
    supercriticalFresnelRegressionInterface, supercriticalFresnelRegressionIncidentWave,
    complexDecayRegressionMedium, HomogeneousIsotropicMedium.waveSpeed,
    JonesVector.toMaterialPlaneWave_angularFrequency] at hConnected
  have hSqrtSixteen : Real.sqrt 16 = 4 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 16), Real.sqrt_nonneg 16]
  have hSqrtNine : Real.sqrt 9 = 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 9), Real.sqrt_nonneg 9]
  rw [hSqrtSixteen, hSqrtNine] at hConnected
  exact hConnected

end

end Optics
