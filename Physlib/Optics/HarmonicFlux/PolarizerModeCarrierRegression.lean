/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.HarmonicFlux.PolarizerModePowerRegression

/-!
# Carrier regression for normalized modal Malus power

## i. Overview

This file reaches through the ideal Jones analyzer action and the explicit material-Jones mode
bridge. For the nonreal `1 + I` horizontal input and `π / 4` analyzer of the power regression, it
pins the output Maxwell carrier's complex electric amplitude componentwise as
`(0, (1 + I) / 2, (1 + I) / 2)`.

The result retains coherent complex phase as well as the already checked factor-of-two power
reduction. It therefore catches a carrier bridge that preserves only squared norms or swaps a
transverse polarization coordinate.

## ii. Key results

- `polarizerModeCarrierRegression_output_electricAmplitude`: exact complex carrier sentinel.

## iii. Table of contents

- A. Exact analyzer-output carrier

## iv. References

This is a convention regression for the singleton Maxwell carrier. It adds no completeness,
reflection, absorption, or internal-component field claim.

-/

@[expose] public section

namespace Optics

open Electromagnetism Electromagnetism.ThreeDimension

noncomputable section

/-!

## A. Exact analyzer-output carrier

-/

/-- The analyzer-output Maxwell carrier has coherent electric amplitude
`(0, (1 + I) / 2, (1 + I) / 2)`. -/
lemma polarizerModeCarrierRegression_output_electricAmplitude :
    ((MaterialJonesMode.linearPolarizationFamily polarizerModePowerRegressionAnalyzerAngle
      polarizerModeNormalizationRegressionMedium polarizerModeNormalizationRegressionFrame 1
      (by norm_num)).scaledWave
        (JonesMatrix.linearPolarizerOutputAmplitude polarizerModePowerRegressionAmplitude
          polarizerModePowerRegressionAnalyzerAngle polarizerModePowerRegressionInputAngle)
        ()).electricAmplitude =
      WithLp.toLp 2 ![(0 : ℂ), (1 + Complex.I) / 2, (1 + Complex.I) / 2] := by
  simp only [MaterialJonesMode.linearPolarizationFamily,
    JonesMatrix.linearPolarizerOutputAmplitude,
    PropagatingHarmonicModeFamily.scaledWave, MaterialJonesMode.family,
    MaterialJonesMode.amplitude,
    ComplexMonochromaticPlaneWave.scaleElectricAmplitude_electricAmplitude]
  rw [JonesVector.ofReal_toMaterialPlaneWave_electricAmplitude]
  ext i
  fin_cases i <;>
    simp [PolarizationFrame.embedJones_apply,
      polarizerModeNormalizationRegressionFrame,
      polarizerModePowerRegressionInputAngle, polarizerModePowerRegressionAnalyzerAngle,
      polarizerModePowerRegressionAmplitude,
      JonesVector.linearPolarization, Real.Angle.cos_coe, Real.Angle.sin_coe,
      Real.cos_pi_div_four, Real.sin_pi_div_four]
  all_goals
    have hsqrt : Real.sqrt 2 * Real.sqrt 2 = 2 :=
      Real.mul_self_sqrt (by norm_num)
    apply Complex.ext <;> norm_num <;> nlinarith

end

end Optics
