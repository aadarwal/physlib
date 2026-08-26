/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.HarmonicFlux.ComplexMaterialWaveRegression
public import Physlib.Optics.HarmonicFlux.PositiveNormalDecay

/-!
# Regressions for positive-normal-decay harmonic flux

## i. Overview

This file fixes two sharp boundaries of the positive-normal-decay mean-flux result using the exact
wave vector `(5, 0, -4 I)` and material parameters `ε = μ = 3`.

First, the transverse TM Maxwell fixture has instantaneous Poynting vector
`(15 / 2, 0, -6)` at phase `pi / 4` and the spatial origin. Its nonzero instantaneous normal
component averages to zero over a period, while its tangential mean remains `(15 / 2, 0, 0)`.

Second, a candidate with the same positive-normal-decay wave vector and material shell but electric
amplitude `(1, 0, 1)` is not bilinearly transverse. Its one-period mean Poynting vector at the
origin is `(5 / 6, 0, -5 / 6)`, so positive-normal-decay geometry and dispersion alone do not force
zero mean normal flux.

## ii. Key results

- `complexDecayRegressionTM_poyntingVector_pi_div_four_origin`: nonzero instantaneous normal flux
  for the transverse TM fixture.
- `complexDecayNontransverseRegression_bilinearDot`: the exact failure of bilinear
  transversality.
- `complexDecayNontransverseRegression_not_isTransverse`: failure of the transverse-wave
  predicate.
- `complexDecayNontransverseRegression_isDispersionMatched`: the counterexample remains on the
  material shell.
- `complexDecayNontransverseRegression_intervalAverage_poyntingVector_origin`: its nonzero mean
  normal flux.

## iii. Table of contents

- A. Transverse instantaneous flux
- B. Nontransverse material-shell fixture
- C. Nontransverse mean flux

## iv. References

These exact regressions test the selected carrier, transversality, material, and
Poynting conventions. They assign no interface boundary condition, transmitted or outgoing role,
Fresnel coefficient, total-internal-reflection balance, aperture power, or modal power.

-/

@[expose] public section

namespace Electromagnetism
namespace ThreeDimension

open ClassicalMechanics Matrix Optics Space Time

noncomputable section

namespace ComplexMonochromaticPlaneWave

/-!

## A. Transverse instantaneous flux

-/

/-- The transverse TM Maxwell fixture has instantaneous Poynting vector
`(15 / 2, 0, -6)` at phase `pi / 4` and the spatial origin. In particular, zero mean normal flux
must not be strengthened to a pointwise statement. -/
lemma complexDecayRegressionTM_poyntingVector_pi_div_four_origin :
    poyntingVector complexDecayRegressionTM.electricField
        (complexDecayRegressionTM.magneticFieldStrength complexDecayRegressionMedium)
        ((Real.pi / 4 : ℝ) : Time) (0 : Space) =
      WithLp.toLp 2 ![(15 / 2 : ℝ), 0, -6] := by
  rw [poyntingVector, complexDecayRegressionTM_electricField,
    magneticFieldStrength, HomogeneousIsotropicMedium.magneticFieldStrength_apply,
    complexDecayRegressionTM_magneticInduction]
  ext i
  fin_cases i <;>
    simp [complexDecayRegressionMedium, complexDecayRegressionDecayFactor,
      complexDecayRegressionPhase, crossProduct, Matrix.cons_val_two, Matrix.head_cons] <;>
    ring_nf
  all_goals rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  all_goals norm_num

/-!

## B. Nontransverse material-shell fixture

-/

/-- A positive-normal-decay, material-shell plane-wave candidate with electric amplitude
`(1, 0, 1)` that deliberately fails bilinear transversality. -/
def complexDecayNontransverseRegression : ComplexMonochromaticPlaneWave where
  angularFrequency := 1
  angularFrequency_pos := by norm_num
  waveVector := complexDecayRegressionWaveVector
  electricAmplitude := WithLp.toLp 2 ![(1 : ℂ), 0, 1]

/-- The nontransverse fixture has exact bilinear electric pairing `5 - 4 I`. -/
lemma complexDecayNontransverseRegression_bilinearDot :
    ComplexWaveVector.bilinearDot complexDecayNontransverseRegression.waveVector
        complexDecayNontransverseRegression.electricAmplitude =
      5 - 4 * Complex.I := by
  simp [complexDecayNontransverseRegression, complexDecayRegressionWaveVector_eq,
    ComplexWaveVector.bilinearDot, Fin.sum_univ_three]
  ring

/-- The nontransverse fixture does not satisfy complex-bilinear electric transversality. -/
lemma complexDecayNontransverseRegression_not_isTransverse :
    ¬ complexDecayNontransverseRegression.IsTransverse := by
  intro h
  rw [IsTransverse, complexDecayNontransverseRegression_bilinearDot] at h
  have hre := congrArg Complex.re h
  norm_num at hre

/-- The nontransverse fixture still lies on the same exact material-dispersion shell as
the transverse TE and TM fixtures. -/
lemma complexDecayNontransverseRegression_isDispersionMatched :
    complexDecayNontransverseRegression.IsDispersionMatched
      complexDecayRegressionMedium := by
  rw [IsDispersionMatched]
  norm_num [complexDecayNontransverseRegression, complexDecayRegressionMedium,
    complexDecayRegression_bilinearSquare]

/-!

## C. Nontransverse mean flux

-/

private lemma complexDecayNontransverseRegression_magneticAmplitude :
    complexDecayNontransverseRegression.magneticAmplitude =
      WithLp.toLp 2 ![0, -5 - 4 * Complex.I, 0] := by
  ext i
  fin_cases i <;>
    simp [magneticAmplitude, complexCross, crossProduct,
      complexDecayNontransverseRegression, complexDecayRegressionWaveVector_eq]
  all_goals ring

private lemma complexDecayNontransverseRegression_referenceFlux :
    timeAveragedPoyntingVector complexDecayNontransverseRegression.electricAmplitude
        (((complexDecayRegressionMedium.μ⁻¹ : ℝ) : ℂ) •
          complexDecayNontransverseRegression.magneticAmplitude) =
      WithLp.toLp 2 ![(5 / 6 : ℝ), 0, -5 / 6] := by
  rw [complexDecayNontransverseRegression_magneticAmplitude]
  ext i
  fin_cases i <;>
    simp [timeAveragedPoyntingVector, complexDecayNontransverseRegression,
      complexDecayRegressionMedium, complexCross, ComplexWaveVector.realPart,
      Phasor.conjugateEuclidean, crossProduct, Complex.mul_re] <;>
    norm_num

/-- The positive-normal-decay, dispersion-matched, nontransverse fixture has actual one-period
mean Poynting vector `(5 / 6, 0, -5 / 6)` at the origin. Its nonzero third component shows that
bilinear transversality is essential to the zero-normal-flux result. -/
lemma complexDecayNontransverseRegression_intervalAverage_poyntingVector_origin :
    (⨍ time in (0 : Time).val..
        (0 : Time).val + 2 * Real.pi / complexDecayNontransverseRegression.angularFrequency,
      poyntingVector complexDecayNontransverseRegression.electricField
        (complexDecayNontransverseRegression.magneticFieldStrength
          complexDecayRegressionMedium)
        (time : Time) (0 : Space)) =
      WithLp.toLp 2 ![(5 / 6 : ℝ), 0, -5 / 6] := by
  rw [intervalAverage_poyntingVector_eq_spatialFactor_normSq_smul,
    complexDecayNontransverseRegression_referenceFlux]
  simp [complexDecayNontransverseRegression, ComplexWaveVector.spatialFactor,
    ComplexWaveVector.spatialPairing, ComplexWaveVector.bilinearDot]

end ComplexMonochromaticPlaneWave

end

end ThreeDimension
end Electromagnetism
