/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public
import Physlib.Electromagnetism.ThreeDimension.MonochromaticPlaneWave.ComplexMaxwellRegression
public import Physlib.Optics.HarmonicFlux.ComplexMaterialWave

/-!
# Harmonic-flux regressions for complex material plane waves

## i. Overview

This file applies the complex-carrier harmonic-flux connector to the exact transverse TE and TM
Maxwell fixtures with wave vector `(5, 0, -4 I)`, material parameters `ε = μ = 3`, and
positive angular frequency one. At the spatial origin their actual one-period mean Poynting
vectors are respectively

`(5 / 6, 0, 0)` and `(15 / 2, 0, 0)`.

Both are nonzero and orthogonal to the third-coordinate attenuation direction, hence tangent to
constant-depth planes. Positive third-coordinate displacement by `u` scales the TE mean vector by
`exp (-8 * u)`, the square of the carrier's `exp (-4 * u)` amplitude envelope.

## ii. Key results

- `complexDecayRegressionTE_intervalAverage_poyntingVector_origin`: exact TE mean flux.
- `complexDecayRegressionTM_intervalAverage_poyntingVector_origin`: exact TM mean flux.
- `complexDecayRegressionTE_intervalAverage_poyntingVector_depth`: exact squared-envelope decay.

## iii. Table of contents

- A. Reference-amplitude flux
- B. Actual-field mean flux at the origin
- C. Squared-envelope decay

## iv. Scope

These are exact regressions for Physlib's own complex-carrier, medium, and harmonic-flux APIs. The
fixtures already satisfy the source-free macroscopic Maxwell equations, but this file assigns them
no interface, transmitted, outgoing, evanescent-field, Fresnel, total internal reflection,
aperture-power, or modal-power role.
-/

@[expose] public section

namespace Electromagnetism
namespace ThreeDimension

open ClassicalMechanics Matrix MeasureTheory Optics Space Time
open scoped Interval Real

noncomputable section

namespace ComplexMonochromaticPlaneWave

/-!

## A. Reference-amplitude flux

-/

private lemma complexDecayRegressionTE_referenceFlux :
    timeAveragedPoyntingVector complexDecayRegressionTE.electricAmplitude
        (((complexDecayRegressionMedium.μ⁻¹ : ℝ) : ℂ) •
          complexDecayRegressionTE.magneticAmplitude) =
      WithLp.toLp 2 ![(5 / 6 : ℝ), 0, 0] := by
  rw [complexDecayRegressionTE_magneticAmplitude]
  ext i
  fin_cases i <;>
    simp [timeAveragedPoyntingVector, complexDecayRegressionTE,
      complexDecayRegressionMedium, complexCross, ComplexWaveVector.realPart,
      Phasor.conjugateEuclidean, crossProduct]
  all_goals norm_num

private lemma complexDecayRegressionTM_referenceFlux :
    timeAveragedPoyntingVector complexDecayRegressionTM.electricAmplitude
        (((complexDecayRegressionMedium.μ⁻¹ : ℝ) : ℂ) •
          complexDecayRegressionTM.magneticAmplitude) =
      WithLp.toLp 2 ![(15 / 2 : ℝ), 0, 0] := by
  rw [complexDecayRegressionTM_magneticAmplitude]
  ext i
  fin_cases i <;>
    simp [timeAveragedPoyntingVector, complexDecayRegressionTM,
      complexDecayRegressionMedium, complexCross, ComplexWaveVector.realPart,
      Phasor.conjugateEuclidean, crossProduct]
  all_goals norm_num

/-!

## B. Actual-field mean flux at the origin

-/

/-- The exact transverse TE fixture has actual one-period mean Poynting vector `(5 / 6, 0, 0)`
at the spatial origin. -/
lemma complexDecayRegressionTE_intervalAverage_poyntingVector_origin :
    (⨍ time in (0 : Time).val..
        (0 : Time).val + 2 * Real.pi / complexDecayRegressionTE.angularFrequency,
      poyntingVector complexDecayRegressionTE.electricField
        (complexDecayRegressionTE.magneticFieldStrength complexDecayRegressionMedium)
        (time : Time) (0 : Space)) =
      WithLp.toLp 2 ![(5 / 6 : ℝ), 0, 0] := by
  rw [complexDecayRegressionTE.intervalAverage_poyntingVector_eq_spatialFactor_normSq_smul,
    complexDecayRegressionTE_referenceFlux]
  simp [complexDecayRegressionTE, ComplexWaveVector.spatialFactor,
    ComplexWaveVector.spatialPairing, ComplexWaveVector.bilinearDot]

/-- The exact transverse TM fixture has actual one-period mean Poynting vector `(15 / 2, 0, 0)`
at the spatial origin. -/
lemma complexDecayRegressionTM_intervalAverage_poyntingVector_origin :
    (⨍ time in (0 : Time).val..
        (0 : Time).val + 2 * Real.pi / complexDecayRegressionTM.angularFrequency,
      poyntingVector complexDecayRegressionTM.electricField
        (complexDecayRegressionTM.magneticFieldStrength complexDecayRegressionMedium)
        (time : Time) (0 : Space)) =
      WithLp.toLp 2 ![(15 / 2 : ℝ), 0, 0] := by
  rw [complexDecayRegressionTM.intervalAverage_poyntingVector_eq_spatialFactor_normSq_smul,
    complexDecayRegressionTM_referenceFlux]
  simp [complexDecayRegressionTM, ComplexWaveVector.spatialFactor,
    ComplexWaveVector.spatialPairing, ComplexWaveVector.bilinearDot]

/-!

## C. Squared-envelope decay

-/

/-- Positive displacement by `depth` in the fixture's attenuation direction scales the actual TE
one-period mean Poynting vector by `exp (-8 * depth)`, not by the carrier-amplitude factor
`exp (-4 * depth)`. -/
lemma complexDecayRegressionTE_intervalAverage_poyntingVector_depth (depth : ℝ) :
    (⨍ time in (0 : Time).val..
        (0 : Time).val + 2 * Real.pi / complexDecayRegressionTE.angularFrequency,
      poyntingVector complexDecayRegressionTE.electricField
        (complexDecayRegressionTE.magneticFieldStrength complexDecayRegressionMedium)
        (time : Time)
        (ComplexWaveVector.positiveNormalDecayRegressionDisplacement depth +ᵥ (0 : Space))) =
      Real.exp (-8 * depth) • WithLp.toLp 2 ![(5 / 6 : ℝ), 0, 0] := by
  rw [complexDecayRegressionTE.intervalAverage_poyntingVector_eq_spatialFactor_normSq_smul,
    complexDecayRegressionTE_referenceFlux]
  have hdecay : 0 < (4 : ℝ) := by norm_num
  have hspatial : complexDecayRegressionTE.waveVector.spatialFactor
      (ComplexWaveVector.positiveNormalDecayRegressionDisplacement depth +ᵥ (0 : Space)) =
      (Real.exp (-4 * depth) : ℂ) := by
    have h := ComplexWaveVector.positiveNormalDecayRegression_spatialFactor_vadd
      5 4 hdecay depth (0 : Space)
    simpa [complexDecayRegressionTE, complexDecayRegressionWaveVector,
      ComplexWaveVector.spatialFactor, ComplexWaveVector.spatialPairing,
      ComplexWaveVector.bilinearDot] using h
  rw [hspatial]
  have hnormSq : Complex.normSq (Real.exp (-4 * depth) : ℂ) =
      Real.exp (-8 * depth) := by
    rw [Complex.normSq_ofReal, ← Real.exp_add]
    congr 1
    ring
  rw [hnormSq]

end ComplexMonochromaticPlaneWave

end

end ThreeDimension
end Electromagnetism
