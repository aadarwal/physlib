/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Electromagnetism.ThreeDimension.MonochromaticPlaneWave.ComplexBoundaryMagnetic
public
import Physlib.Electromagnetism.ThreeDimension.MonochromaticPlaneWave.ComplexDispersionRegression

/-!
# Regressions for complex tangential magnetic boundary amplitudes

## i. Overview

This file fixes the constitutive scale, tangential projection, stored-point reference, and temporal
quadrature conventions of the complex magnetic boundary amplitude API. It uses the existing
positive-normal-decay transverse-electric fixture with

`K = (5, 0, -4 I)`, `E₀ = (0, 1, 0)`, `B₀ = (4 I, 0, 5)`, and `μ = 3`.

Relative to the parallel coordinate plane with stored normal `(0, 0, 1)` and stored point
`(0, 0, 1)`, the tangential `H₀` amplitude is `(4 I / 3, 0, 0)` and its referenced value is
`(4 exp (-4) I / 3, 0, 0)`. Its ordinary real value is zero at time zero and
`(-4 exp (-4) / 3, 0, 0)` one quarter period later. These exact values distinguish `H` from `B`,
fix the attenuation sign in the stored-point factor, and recover the imaginary phasor quadrature
that a single real sample would miss.

## ii. Key results

- `complexBoundaryMagneticRegression_spatialFactor`: exact nontrivial stored-point attenuation.
- `complexBoundaryMagneticRegression_referencedAmplitude`: exact referenced tangential `H₀`.
- `complexBoundaryMagneticRegression_data_zero`: zero initial ordinary real sample.
- `complexBoundaryMagneticRegression_data_pi_div_two`: nonzero quarter-period sample.

## iii. Table of contents

- A. Coordinate plane
- B. Referenced magnetic amplitude
- C. Temporal quadrature samples

## iv. Scope

These exact regressions assign no boundary equality, interface side, surface-source condition,
Fresnel coefficient, observable, or power meaning.
-/

@[expose] public section

namespace Electromagnetism
namespace ThreeDimension

open ClassicalMechanics Matrix Space Time

noncomputable section

namespace ComplexMonochromaticPlaneWave

/-!

## A. Coordinate plane

-/

/-- The positive third-coordinate direction used as the stored plane normal. -/
def complexBoundaryMagneticRegressionNormal : Direction 3 :=
  ⟨⟨![0, 0, 1]⟩, by
    rw [Space.norm_eq]
    simp [Fin.sum_univ_three]⟩

/-- The coordinate plane through `(0, 0, 1)` with stored normal `(0, 0, 1)`. -/
def complexBoundaryMagneticRegressionPlane : OrientedAffineHyperplane 3 where
  point := ⟨![(0 : ℝ), 0, 1]⟩
  normal := complexBoundaryMagneticRegressionNormal

/-- The regression plane's stored normal has exact coordinate vector `(0, 0, 1)`. -/
lemma complexBoundaryMagneticRegressionPlane_normalVector :
    complexBoundaryMagneticRegressionPlane.normalVector =
      WithLp.toLp 2 ![(0 : ℝ), 0, 1] := by
  ext i
  fin_cases i <;>
    simp [complexBoundaryMagneticRegressionPlane, complexBoundaryMagneticRegressionNormal,
      OrientedAffineHyperplane.normalVector]

/-!

## B. Referenced magnetic amplitude

-/

/-- At the stored point `(0, 0, 1)`, the transverse-electric fixture's spatial factor is exactly
the positive real attenuation factor `exp (-4)`. -/
lemma complexBoundaryMagneticRegression_spatialFactor :
    complexDecayRegressionTE.waveVector.spatialFactor
        complexBoundaryMagneticRegressionPlane.point = (Real.exp (-4) : ℂ) := by
  rw [ComplexWaveVector.spatialFactor, Complex.ofReal_exp]
  congr 1
  simp [complexBoundaryMagneticRegressionPlane, complexDecayRegressionTE,
    complexDecayRegressionWaveVector_eq, ComplexWaveVector.spatialPairing,
    ComplexWaveVector.bilinearDot, Fin.sum_univ_three]
  ring_nf
  rw [Complex.I_sq]
  norm_num

/-- The transverse-electric fixture has tangential magnetic-field-strength amplitude
`(4 I / 3, 0, 0)` relative to the coordinate plane. -/
lemma complexBoundaryMagneticRegression_amplitude :
    mediumTangentialMagneticFieldStrengthAmplitude complexBoundaryMagneticRegressionPlane
        complexDecayRegressionMedium complexDecayRegressionTE =
      WithLp.toLp 2 ![(4 / 3 : ℂ) * Complex.I, 0, 0] := by
  rw [mediumTangentialMagneticFieldStrengthAmplitude,
    complexDecayRegressionTE_magneticAmplitude]
  ext i
  fin_cases i <;>
    simp [complexBoundaryMagneticRegressionPlane_normalVector,
      complexDecayRegressionMedium, ComplexWaveVector.hyperplaneTangentialProjection,
      ComplexWaveVector.hyperplaneNormalComponent, ComplexWaveVector.bilinearDot,
      ComplexWaveVector.ofReal, Fin.sum_univ_three]
  all_goals ring

/-- Referencing at `(0, 0, 1)` multiplies the exact tangential magnetic-field-strength amplitude
by the positive attenuation factor `exp (-4)`. -/
lemma complexBoundaryMagneticRegression_referencedAmplitude :
    referencedMediumTangentialMagneticFieldStrengthAmplitude
        complexBoundaryMagneticRegressionPlane complexDecayRegressionMedium
          complexDecayRegressionTE =
      WithLp.toLp 2 ![((4 / 3 * Real.exp (-4) : ℝ) : ℂ) * Complex.I, 0, 0] := by
  rw [referencedMediumTangentialMagneticFieldStrengthAmplitude,
    complexBoundaryMagneticRegression_amplitude,
    complexBoundaryMagneticRegression_spatialFactor]
  ext i
  fin_cases i <;> simp
  ring

/-!

## C. Temporal quadrature samples

-/

/-- The purely imaginary referenced tangential magnetic amplitude has zero ordinary real value at
time zero and the stored point. -/
lemma complexBoundaryMagneticRegression_data_zero :
    mediumTangentialMagneticFieldStrengthData complexBoundaryMagneticRegressionPlane
        complexDecayRegressionMedium complexDecayRegressionTE 0
          complexBoundaryMagneticRegressionPlane.point = 0 := by
  rw [mediumTangentialMagneticFieldStrengthData_point,
    complexBoundaryMagneticRegression_referencedAmplitude]
  have hnegFour : (-4 : ℂ) = ((-4 : ℝ) : ℂ) := by norm_num
  have hexpIm : (Complex.exp (-4 : ℂ)).im = 0 := by
    rw [hnegFour]
    exact Complex.exp_ofReal_im (-4)
  ext i
  fin_cases i <;>
    simp [complexDecayRegressionTE, ComplexWaveVector.realPart, hexpIm]

/-- One quarter period later, the same ordinary real tangential magnetic field is
`(-4 * exp (-4) / 3, 0, 0)`. -/
lemma complexBoundaryMagneticRegression_data_pi_div_two :
    mediumTangentialMagneticFieldStrengthData complexBoundaryMagneticRegressionPlane
        complexDecayRegressionMedium complexDecayRegressionTE
          ((Real.pi / 2 : ℝ) : Time) complexBoundaryMagneticRegressionPlane.point =
      WithLp.toLp 2 ![(-4 * Real.exp (-4) / 3 : ℝ), 0, 0] := by
  rw [mediumTangentialMagneticFieldStrengthData_point,
    complexBoundaryMagneticRegression_referencedAmplitude]
  have hnegFour : (-4 : ℂ) = ((-4 : ℝ) : ℂ) := by norm_num
  have hexpRe : (Complex.exp (-4 : ℂ)).re = Real.exp (-4) := by
    rw [hnegFour]
    exact Complex.exp_ofReal_re (-4)
  have hexpIm : (Complex.exp (-4 : ℂ)).im = 0 := by
    rw [hnegFour]
    exact Complex.exp_ofReal_im (-4)
  ext i
  fin_cases i <;>
    simp [complexDecayRegressionTE, ComplexWaveVector.realPart, Complex.mul_re,
      hexpRe, hexpIm]
  all_goals ring

end ComplexMonochromaticPlaneWave

end
end ThreeDimension
end Electromagnetism
