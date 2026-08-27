/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.HarmonicFlux.PolarizerModeNormalizationRegression

/-!
# Regression for normalized modal Malus power

## i. Overview

This file applies the independently normalized material-Jones fixture to a horizontal input and a
`π / 4` analyzer. The complex input coordinate `1 + I` has modal and actual incident power two.
The analyzer output has coordinate power and actual outgoing flux one, so the physical flux is
halved exactly; the role signs are pinned by
`polarizerModeNormalizationRegression_incident_integratedMeanNormalFlux`
(`Physlib/Optics/HarmonicFlux/PolarizerModeNormalizationRegression.lean:146`) and
`polarizerModeNormalizationRegression_outgoing_integratedMeanNormalFlux`
(`Physlib/Optics/HarmonicFlux/PolarizerModeNormalizationRegression.lean:117`), together with
`polarizerModeNormalizationRegression_incident_isApertureFluxOrthonormal`
(`Physlib/Optics/HarmonicFlux/PolarizerModeNormalizationRegression.lean:197`) and
`polarizerModeNormalizationRegression_outgoing_isApertureFluxOrthonormal`
(`Physlib/Optics/HarmonicFlux/PolarizerModeNormalizationRegression.lean:180`).

## ii. Key results

- `polarizerModePowerRegression_actualFlux_halved`: actual normalized-flux Malus law.

## iii. Table of contents

- A. Analyzer data and modal powers
- B. Actual incident and outgoing flux

## iv. References

These are exact convention checks for the explicit singleton model. They establish neither modal
completeness nor the fate of the polarizer's rejected polarization.

-/

@[expose] public section

namespace Optics

open Electromagnetism Electromagnetism.ThreeDimension
open MeasureTheory Time

noncomputable section

/-!

## A. Analyzer data and modal powers

-/

/-- The regression input is horizontal linear polarization. -/
def polarizerModePowerRegressionInputAngle : Real.Angle := 0

/-- The regression analyzer is at forty-five degrees. -/
def polarizerModePowerRegressionAnalyzerAngle : Real.Angle := (Real.pi / 4 : ℝ)

/-- The nonreal input coordinate pins coherent carrier phase. -/
def polarizerModePowerRegressionAmplitude : ℂ := 1 + Complex.I

/-- The exact incident modal coordinate has power two. -/
lemma polarizerModePowerRegression_input_power :
    (MaterialJonesMode.amplitude polarizerModePowerRegressionAmplitude).power = 2 := by
  rw [MaterialJonesMode.amplitude_power]
  norm_num [polarizerModePowerRegressionAmplitude, Complex.normSq_apply]

/-- The squared analyzer-axis cosine is one half. -/
lemma polarizerModePowerRegression_axis_cos_sq :
    Real.Angle.cos
      (polarizerModePowerRegressionInputAngle - polarizerModePowerRegressionAnalyzerAngle) ^ 2 =
        1 / 2 := by
  have hangle :
      polarizerModePowerRegressionInputAngle - polarizerModePowerRegressionAnalyzerAngle =
        -((Real.pi / 4 : ℝ) : Real.Angle) := by
    simp [polarizerModePowerRegressionInputAngle,
      polarizerModePowerRegressionAnalyzerAngle]
  rw [hangle, Real.Angle.cos_neg, Real.Angle.cos_coe, Real.cos_pi_div_four]
  have hsqrt : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith

/-- The independently expanded analyzer-output modal coordinate has power one. -/
lemma polarizerModePowerRegression_output_power :
    (JonesMatrix.linearPolarizerOutputAmplitude polarizerModePowerRegressionAmplitude
      polarizerModePowerRegressionAnalyzerAngle polarizerModePowerRegressionInputAngle).power =
        1 := by
  rw [JonesMatrix.linearPolarizerOutputAmplitude, MaterialJonesMode.amplitude_power,
    Complex.normSq_mul, Complex.normSq_ofReal]
  rw [show Real.Angle.cos
      (polarizerModePowerRegressionInputAngle - polarizerModePowerRegressionAnalyzerAngle) *
        Real.Angle.cos
          (polarizerModePowerRegressionInputAngle - polarizerModePowerRegressionAnalyzerAngle) =
      Real.Angle.cos
          (polarizerModePowerRegressionInputAngle - polarizerModePowerRegressionAnalyzerAngle) ^ 2
        by ring, polarizerModePowerRegression_axis_cos_sq]
  norm_num [polarizerModePowerRegressionAmplitude, Complex.normSq_apply]

/-!

## B. Actual incident and outgoing flux

-/

/-- At every period origin, the actual incident normal flux is minus two; its role sign is pinned by
`polarizerModeNormalizationRegression_incident_integratedMeanNormalFlux`
(`Physlib/Optics/HarmonicFlux/PolarizerModeNormalizationRegression.lean:146`) and
`polarizerModeNormalizationRegression_incident_isApertureFluxOrthonormal`
(`Physlib/Optics/HarmonicFlux/PolarizerModeNormalizationRegression.lean:197`). -/
lemma polarizerModePowerRegression_input_actualFlux (startTime : Time) :
    (MaterialJonesMode.linearPolarizationFamily polarizerModePowerRegressionInputAngle
      polarizerModeNormalizationRegressionMedium polarizerModeNormalizationRegressionFrame 1
      (by norm_num)).integratedActualMeanNormalFlux Measure.count
        polarizerModeNormalizationRegressionInputPlane polarizerModeNormalizationRegressionPoint
        (MaterialJonesMode.amplitude polarizerModePowerRegressionAmplitude) startTime = -2 := by
  have h := (MaterialJonesMode.linearPolarizationFamily polarizerModePowerRegressionInputAngle
    polarizerModeNormalizationRegressionMedium polarizerModeNormalizationRegressionFrame 1
    (by norm_num)).incident_integratedActualMeanNormalFlux_eq_neg_power
      (polarizerModeNormalizationRegression_incident_isApertureFluxOrthonormal
        polarizerModePowerRegressionInputAngle)
      (MaterialJonesMode.amplitude polarizerModePowerRegressionAmplitude) startTime
  rw [polarizerModePowerRegression_input_power] at h
  linarith

/-- At every period origin, the actual analyzer-output normal flux is one; its outgoing role sign
is pinned by `polarizerModeNormalizationRegression_outgoing_integratedMeanNormalFlux`
(`Physlib/Optics/HarmonicFlux/PolarizerModeNormalizationRegression.lean:117`) and
`polarizerModeNormalizationRegression_outgoing_isApertureFluxOrthonormal`
(`Physlib/Optics/HarmonicFlux/PolarizerModeNormalizationRegression.lean:180`). -/
lemma polarizerModePowerRegression_output_actualFlux (startTime : Time) :
    (MaterialJonesMode.linearPolarizationFamily polarizerModePowerRegressionAnalyzerAngle
      polarizerModeNormalizationRegressionMedium polarizerModeNormalizationRegressionFrame 1
      (by norm_num)).integratedActualMeanNormalFlux Measure.count
        polarizerModeNormalizationRegressionOutputPlane polarizerModeNormalizationRegressionPoint
        (JonesMatrix.linearPolarizerOutputAmplitude polarizerModePowerRegressionAmplitude
          polarizerModePowerRegressionAnalyzerAngle polarizerModePowerRegressionInputAngle)
        startTime = 1 := by
  calc
    _ = (JonesMatrix.linearPolarizerOutputAmplitude polarizerModePowerRegressionAmplitude
        polarizerModePowerRegressionAnalyzerAngle polarizerModePowerRegressionInputAngle).power :=
      (MaterialJonesMode.linearPolarizationFamily polarizerModePowerRegressionAnalyzerAngle
        polarizerModeNormalizationRegressionMedium polarizerModeNormalizationRegressionFrame 1
        (by norm_num)).outgoing_integratedActualMeanNormalFlux_eq_power
          (polarizerModeNormalizationRegression_outgoing_isApertureFluxOrthonormal
            polarizerModePowerRegressionAnalyzerAngle) _ _
    _ = 1 := polarizerModePowerRegression_output_power

/-- The independently computed actual output flux is one half of the positive incident power; the
role signs are pinned by `polarizerModeNormalizationRegression_incident_integratedMeanNormalFlux`
(`Physlib/Optics/HarmonicFlux/PolarizerModeNormalizationRegression.lean:146`) and
`polarizerModeNormalizationRegression_outgoing_integratedMeanNormalFlux`
(`Physlib/Optics/HarmonicFlux/PolarizerModeNormalizationRegression.lean:117`), together with
`polarizerModeNormalizationRegression_incident_isApertureFluxOrthonormal`
(`Physlib/Optics/HarmonicFlux/PolarizerModeNormalizationRegression.lean:197`) and
`polarizerModeNormalizationRegression_outgoing_isApertureFluxOrthonormal`
(`Physlib/Optics/HarmonicFlux/PolarizerModeNormalizationRegression.lean:180`). -/
lemma polarizerModePowerRegression_actualFlux_halved (startTime : Time) :
    (MaterialJonesMode.linearPolarizationFamily polarizerModePowerRegressionAnalyzerAngle
      polarizerModeNormalizationRegressionMedium polarizerModeNormalizationRegressionFrame 1
      (by norm_num)).integratedActualMeanNormalFlux Measure.count
        polarizerModeNormalizationRegressionOutputPlane polarizerModeNormalizationRegressionPoint
        (JonesMatrix.linearPolarizerOutputAmplitude polarizerModePowerRegressionAmplitude
          polarizerModePowerRegressionAnalyzerAngle polarizerModePowerRegressionInputAngle)
        startTime =
      -(MaterialJonesMode.linearPolarizationFamily polarizerModePowerRegressionInputAngle
        polarizerModeNormalizationRegressionMedium polarizerModeNormalizationRegressionFrame 1
        (by norm_num)).integratedActualMeanNormalFlux Measure.count
          polarizerModeNormalizationRegressionInputPlane
          polarizerModeNormalizationRegressionPoint
          (MaterialJonesMode.amplitude polarizerModePowerRegressionAmplitude) startTime *
        Real.Angle.cos
          (polarizerModePowerRegressionInputAngle - polarizerModePowerRegressionAnalyzerAngle) ^
            2 := by
  rw [polarizerModePowerRegression_output_actualFlux,
    polarizerModePowerRegression_input_actualFlux, polarizerModePowerRegression_axis_cos_sq]
  norm_num

end

end Optics
