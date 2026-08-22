/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.ClassicalMechanics.WaveEquation.ComplexWaveVectorRegression
public import Physlib.Electromagnetism.ThreeDimension.MonochromaticPlaneWave.ComplexDispersion

/-!
# Regression tests for complex plane-wave dispersion

## i. Overview

This module fixes exact attenuating complex plane-wave data over a homogeneous medium with
`epsilon = mu = 3` and angular frequency one. Its wave vector is

`K = (5, 0, -4 I)`,

so its complex-bilinear square is `9`, while its Hermitian squared norm is `41`. Exact transverse
TE and TM electric amplitudes check the material shell, magnetic-amplitude construction, and
the signed relation `K cross B0 = -9 E0`.

The TM amplitude has bilinear pairing zero with `K` but Hermitian pairing `40`. This explicitly
distinguishes the complex-bilinear transversality used by Maxwell algebra from Hermitian
orthogonality.

The fixture is built from positive-normal decay geometry, but this file assigns it no interface
side, transmitted, outgoing, or evanescent-wave role and makes no Maxwell-field or power claim.

## ii. Key results

- `complexDecayRegression_bilinearSquare`: the material square is `9`.
- `complexDecayRegression_norm_sq`: the Hermitian squared norm is instead `41`.
- `complexDecayRegressionTM_hermitianPairing`: transverse TM data has Hermitian pairing `40`.
- `complexDecayRegressionTE_magneticAmplitude` and
  `complexDecayRegressionTM_magneticAmplitude`: exact compatible magnetic amplitudes.
- `complexDecayRegressionTE_cross_magneticAmplitude` and
  `complexDecayRegressionTM_cross_magneticAmplitude`: exact signed material relations.

## iii. Table of contents

- A. Exact regression data
- B. Bilinear and Hermitian geometry
- C. TE and TM amplitude algebra

## iv. References

This file is an exact regression for Physlib's own complex-wave-vector and plane-wave APIs. No
external formal-development source is copied or translated here.
-/

@[expose] public section

namespace Electromagnetism
namespace ThreeDimension

open InnerProductSpace Matrix ClassicalMechanics

noncomputable section

namespace ComplexMonochromaticPlaneWave

/-!

## A. Exact regression data

-/

/-- The exact homogeneous medium used by the complex-decay regression. -/
def complexDecayRegressionMedium : HomogeneousIsotropicMedium where
  ε := 3
  μ := 3
  ε_pos := by norm_num
  μ_pos := by norm_num

/-- The exact complex wave vector `(5, 0, -4 I)` used by the decay regression. -/
def complexDecayRegressionWaveVector : ComplexWaveVector 3 :=
  (ComplexWaveVector.positiveNormalDecayRegression 5 4 (by norm_num)).waveVector

/-- The TE complex plane-wave candidate with electric amplitude `(0, 1, 0)`. -/
def complexDecayRegressionTE : ComplexMonochromaticPlaneWave where
  angularFrequency := 1
  angularFrequency_pos := by norm_num
  waveVector := complexDecayRegressionWaveVector
  electricAmplitude := WithLp.toLp 2 ![(0 : ℂ), 1, 0]

/-- The TM complex plane-wave candidate with electric amplitude `(4, 0, -5 I)`. -/
def complexDecayRegressionTM : ComplexMonochromaticPlaneWave where
  angularFrequency := 1
  angularFrequency_pos := by norm_num
  waveVector := complexDecayRegressionWaveVector
  electricAmplitude := WithLp.toLp 2 ![(4 : ℂ), 0, -5 * Complex.I]

/-- The regression wave vector has exact coordinates `(5, 0, -4 I)`. -/
lemma complexDecayRegressionWaveVector_eq :
    complexDecayRegressionWaveVector =
      WithLp.toLp 2 ![(5 : ℂ), 0, -4 * Complex.I] := by
  rw [complexDecayRegressionWaveVector,
    ComplexWaveVector.positiveNormalDecayRegression_waveVector]
  ext i
  fin_cases i <;> simp [mul_comm]

/-!

## B. Bilinear and Hermitian geometry

-/

/-- The complex-bilinear square of the regression wave vector is exactly `9`. -/
lemma complexDecayRegression_bilinearSquare :
    ComplexWaveVector.bilinearDot complexDecayRegressionWaveVector
      complexDecayRegressionWaveVector = 9 := by
  rw [complexDecayRegressionWaveVector_eq]
  simp [ComplexWaveVector.bilinearDot, Fin.sum_univ_three]
  ring_nf
  rw [Complex.I_sq]
  norm_num

/-- The Hermitian squared norm of the same regression wave vector is exactly `41`, not `9`. -/
lemma complexDecayRegression_norm_sq :
    ‖complexDecayRegressionWaveVector‖ ^ 2 = 41 := by
  rw [complexDecayRegressionWaveVector_eq, EuclideanSpace.norm_sq_eq]
  simp [Fin.sum_univ_three]
  norm_num

/-- The TE regression amplitude is complex-bilinearly transverse. -/
lemma complexDecayRegressionTE_isTransverse : complexDecayRegressionTE.IsTransverse := by
  rw [IsTransverse]
  simp [complexDecayRegressionTE, complexDecayRegressionWaveVector_eq,
    ComplexWaveVector.bilinearDot, Fin.sum_univ_three]

/-- The TM regression amplitude is complex-bilinearly transverse. -/
lemma complexDecayRegressionTM_isTransverse : complexDecayRegressionTM.IsTransverse := by
  rw [IsTransverse]
  simp [complexDecayRegressionTM, complexDecayRegressionWaveVector_eq,
    ComplexWaveVector.bilinearDot, Fin.sum_univ_three]
  ring_nf
  rw [Complex.I_sq]
  norm_num

/-- The TM amplitude is bilinearly transverse, while its Hermitian pairing with `K` is `40`. -/
lemma complexDecayRegressionTM_hermitianPairing :
    inner ℂ complexDecayRegressionTM.waveVector
      complexDecayRegressionTM.electricAmplitude = 40 := by
  simp [complexDecayRegressionTM, complexDecayRegressionWaveVector_eq,
    PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_three]
  norm_num [map_ofNat]
  ring_nf
  rw [Complex.I_sq]
  norm_num

/-!

## C. TE and TM amplitude algebra

-/

/-- The TE regression candidate lies on the exact bilinear material shell. -/
lemma complexDecayRegressionTE_isDispersionMatched :
    complexDecayRegressionTE.IsDispersionMatched complexDecayRegressionMedium := by
  rw [IsDispersionMatched]
  norm_num [complexDecayRegressionTE, complexDecayRegressionMedium,
    complexDecayRegression_bilinearSquare]

/-- The TM regression candidate lies on the exact bilinear material shell. -/
lemma complexDecayRegressionTM_isDispersionMatched :
    complexDecayRegressionTM.IsDispersionMatched complexDecayRegressionMedium := by
  rw [IsDispersionMatched]
  norm_num [complexDecayRegressionTM, complexDecayRegressionMedium,
    complexDecayRegression_bilinearSquare]

/-- The compatible TE magnetic amplitude is exactly `(4 I, 0, 5)`. -/
lemma complexDecayRegressionTE_magneticAmplitude :
    complexDecayRegressionTE.magneticAmplitude =
      WithLp.toLp 2 ![4 * Complex.I, 0, (5 : ℂ)] := by
  ext i
  fin_cases i <;>
    simp [magneticAmplitude, complexCross, crossProduct, complexDecayRegressionTE,
      complexDecayRegressionWaveVector_eq]

/-- The compatible TM magnetic amplitude is exactly `(0, 9 I, 0)`. -/
lemma complexDecayRegressionTM_magneticAmplitude :
    complexDecayRegressionTM.magneticAmplitude =
      WithLp.toLp 2 ![0, 9 * Complex.I, 0] := by
  ext i
  fin_cases i <;>
    simp [magneticAmplitude, complexCross, crossProduct, complexDecayRegressionTM,
      complexDecayRegressionWaveVector_eq]
  ring

/-- Direct coordinate calculation gives the exact signed TE relation `K cross B0 = -9 E0`. -/
lemma complexDecayRegressionTE_cross_magneticAmplitude :
    complexCross complexDecayRegressionTE.waveVector
        complexDecayRegressionTE.magneticAmplitude =
      -(9 : ℂ) • complexDecayRegressionTE.electricAmplitude := by
  rw [complexDecayRegressionTE_magneticAmplitude]
  ext i
  fin_cases i <;>
    simp [complexDecayRegressionTE, complexDecayRegressionWaveVector_eq,
      complexCross, crossProduct]
  ring_nf
  rw [Complex.I_sq]
  norm_num

/-- Direct coordinate calculation gives the exact signed TM relation `K cross B0 = -9 E0`. -/
lemma complexDecayRegressionTM_cross_magneticAmplitude :
    complexCross complexDecayRegressionTM.waveVector
        complexDecayRegressionTM.magneticAmplitude =
      -(9 : ℂ) • complexDecayRegressionTM.electricAmplitude := by
  rw [complexDecayRegressionTM_magneticAmplitude]
  ext i
  fin_cases i <;>
    simp [complexDecayRegressionTM, complexDecayRegressionWaveVector_eq,
      complexCross, crossProduct]
  all_goals ring_nf
  all_goals rw [Complex.I_sq]
  all_goals norm_num

end ComplexMonochromaticPlaneWave
end
end ThreeDimension
end Electromagnetism
