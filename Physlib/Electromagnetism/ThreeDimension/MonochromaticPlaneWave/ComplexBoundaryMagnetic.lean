/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public
import Physlib.Electromagnetism.ThreeDimension.MonochromaticPlaneWave.ComplexBoundaryExponent

/-!
# Complex tangential magnetic data at a planar boundary

## i. Overview

This file packages the tangential magnetic-field-strength amplitude of one complex plane-wave
candidate relative to an oriented affine hyperplane and a homogeneous isotropic medium. It also
defines the amplitude referenced to the hyperplane's stored point and connects both calculation
objects to the actual ordinary real tangential magnetic field on the plane.

The supplied medium enters through `H₀ = μ⁻¹ B₀`. The wave itself fixes
`B₀ = ω⁻¹ (K cross E₀)` through its existing magnetic amplitude. No transversality,
material dispersion, Maxwell equation, nonzero amplitude, boundary law, interface side, carrier
branch, Fresnel coefficient, observable, or power statement is assumed.

Unlike the joint tangential-`E` and normal-`D` amplitude, tangential `H` alone does not detect the
complete field amplitude. No converse zero criterion is therefore stated. Affine-point
referencing can change the modulus for an attenuating carrier and is not a reference-independent
normalization.

## ii. Key results

- `mediumTangentialMagneticFieldStrengthAmplitude`: tangential complex `H₀` calculation data.
- `referencedMediumTangentialMagneticFieldStrengthAmplitude`: the same amplitude referenced to the
  plane's stored point.
- `mediumTangentialMagneticFieldStrengthData_eq_realPart_smul_amplitude`: connection to the actual
  ordinary real tangential field.
- `mediumTangentialMagneticFieldStrengthData_tangent_vadd_point`: exact affine-plane
  factorization.

## iii. Table of contents

- A. Tangential magnetic amplitudes
- B. Ordinary real tangential magnetic data
- C. Affine-plane realization

## iv. References

The construction uses Physlib's existing complex carrier, isotropic constitutive map, and oriented
hyperplane APIs. No external formal-development source is copied or translated here.
-/

@[expose] public section

namespace Electromagnetism
namespace ThreeDimension

open ClassicalMechanics Space Time

noncomputable section

namespace ComplexMonochromaticPlaneWave

/-!

## A. Tangential magnetic amplitudes

-/

/-- The medium-dependent tangential magnetic-field-strength amplitude of one complex plane-wave
candidate relative to an oriented affine hyperplane. -/
def mediumTangentialMagneticFieldStrengthAmplitude
    (plane : OrientedAffineHyperplane 3) (medium : HomogeneousIsotropicMedium)
    (wave : ComplexMonochromaticPlaneWave) : EuclideanSpace ℂ (Fin 3) :=
  ((medium.μ⁻¹ : ℝ) : ℂ) •
    ComplexWaveVector.hyperplaneTangentialProjection plane wave.magneticAmplitude

/-- The medium-dependent tangential magnetic-field-strength amplitude referenced to the oriented
hyperplane's stored affine point. -/
def referencedMediumTangentialMagneticFieldStrengthAmplitude
    (plane : OrientedAffineHyperplane 3) (medium : HomogeneousIsotropicMedium)
    (wave : ComplexMonochromaticPlaneWave) : EuclideanSpace ℂ (Fin 3) :=
  wave.waveVector.spatialFactor plane.point •
    mediumTangentialMagneticFieldStrengthAmplitude plane medium wave

/-- A zero electric amplitude gives zero tangential magnetic-field-strength amplitude. The
converse is false in general. -/
lemma mediumTangentialMagneticFieldStrengthAmplitude_eq_zero_of_electricAmplitude_eq_zero
    (plane : OrientedAffineHyperplane 3) (medium : HomogeneousIsotropicMedium)
    (wave : ComplexMonochromaticPlaneWave) (hZero : wave.electricAmplitude = 0) :
    mediumTangentialMagneticFieldStrengthAmplitude plane medium wave = 0 := by
  simp [mediumTangentialMagneticFieldStrengthAmplitude, magneticAmplitude, hZero,
    complexCross, ComplexWaveVector.hyperplaneTangentialProjection,
    ComplexWaveVector.hyperplaneNormalComponent]

/-- Affine-point referencing preserves the one-way implication from zero electric amplitude to
zero tangential magnetic-field-strength amplitude. -/
lemma referencedMediumTangentialMagneticFieldStrengthAmplitude_eq_zero_of_electricAmplitude_eq_zero
    (plane : OrientedAffineHyperplane 3) (medium : HomogeneousIsotropicMedium)
    (wave : ComplexMonochromaticPlaneWave) (hZero : wave.electricAmplitude = 0) :
    referencedMediumTangentialMagneticFieldStrengthAmplitude plane medium wave = 0 := by
  rw [referencedMediumTangentialMagneticFieldStrengthAmplitude,
    mediumTangentialMagneticFieldStrengthAmplitude_eq_zero_of_electricAmplitude_eq_zero
      plane medium wave hZero,
    smul_zero]

/-!

## B. Ordinary real tangential magnetic data

-/

/-- The actual ordinary real tangential magnetic-field-strength data of one complex plane-wave
candidate at a supplied time and spatial point. -/
def mediumTangentialMagneticFieldStrengthData
    (plane : OrientedAffineHyperplane 3) (medium : HomogeneousIsotropicMedium)
    (wave : ComplexMonochromaticPlaneWave) (t : Time) (x : Space) :
    EuclideanSpace ℝ (Fin 3) :=
  plane.tangentialProjection (wave.magneticFieldStrength medium t x)

/-- The ordinary real tangential magnetic-field-strength data is the componentwise real
realization of the shared carrier multiplying its medium-dependent complex amplitude. -/
lemma mediumTangentialMagneticFieldStrengthData_eq_realPart_smul_amplitude
    (plane : OrientedAffineHyperplane 3) (medium : HomogeneousIsotropicMedium)
    (wave : ComplexMonochromaticPlaneWave) (t : Time) (x : Space) :
    mediumTangentialMagneticFieldStrengthData plane medium wave t x =
      ComplexWaveVector.realPart
        (wave.carrier t x •
          mediumTangentialMagneticFieldStrengthAmplitude plane medium wave) := by
  rw [mediumTangentialMagneticFieldStrengthData, magneticFieldStrength,
    HomogeneousIsotropicMedium.magneticFieldStrength_apply,
    Space.OrientedAffineHyperplane.tangentialProjection_smul]
  change medium.μ⁻¹ •
      plane.tangentialProjection
        (ComplexWaveVector.realPart (wave.carrier t x • wave.magneticAmplitude)) = _
  rw [ComplexWaveVector.tangentialProjection_realPart_smul]
  ext i
  simp [mediumTangentialMagneticFieldStrengthAmplitude,
    ComplexWaveVector.realPart, Complex.mul_re]
  ring

/-!

## C. Affine-plane realization

-/

private lemma carrier_smul_mediumTangentialMagneticFieldStrengthAmplitude_tangent_vadd_point
    (plane : OrientedAffineHyperplane 3) (medium : HomogeneousIsotropicMedium)
    (wave : ComplexMonochromaticPlaneWave) (t : Time) (v : plane.tangentSubmodule) :
    wave.carrier t ((v : EuclideanSpace ℝ (Fin 3)) +ᵥ plane.point) •
        mediumTangentialMagneticFieldStrengthAmplitude plane medium wave =
      Complex.exp (wave.boundaryExponent plane (t, v)) •
        referencedMediumTangentialMagneticFieldStrengthAmplitude plane medium wave := by
  rw [carrier_tangent_vadd_point]
  simp [referencedMediumTangentialMagneticFieldStrengthAmplitude, smul_smul]

/-- On the affine plane, the actual ordinary real tangential magnetic-field-strength data is the
real realization of one positive-rate exponential character multiplying its stored-point-
referenced complex amplitude. -/
lemma mediumTangentialMagneticFieldStrengthData_tangent_vadd_point
    (plane : OrientedAffineHyperplane 3) (medium : HomogeneousIsotropicMedium)
    (wave : ComplexMonochromaticPlaneWave) (t : Time) (v : plane.tangentSubmodule) :
    mediumTangentialMagneticFieldStrengthData plane medium wave t
        ((v : EuclideanSpace ℝ (Fin 3)) +ᵥ plane.point) =
      ComplexWaveVector.realPart
        (Complex.exp (wave.boundaryExponent plane (t, v)) •
          referencedMediumTangentialMagneticFieldStrengthAmplitude plane medium wave) := by
  rw [mediumTangentialMagneticFieldStrengthData_eq_realPart_smul_amplitude,
    carrier_smul_mediumTangentialMagneticFieldStrengthAmplitude_tangent_vadd_point]

/-- At the stored affine point, the actual ordinary real tangential magnetic-field-strength data
is the referenced amplitude realized with the wave's temporal carrier. -/
lemma mediumTangentialMagneticFieldStrengthData_point
    (plane : OrientedAffineHyperplane 3) (medium : HomogeneousIsotropicMedium)
    (wave : ComplexMonochromaticPlaneWave) (t : Time) :
    mediumTangentialMagneticFieldStrengthData plane medium wave t plane.point =
      ComplexWaveVector.realPart
        (Complex.exp
          ((((wave.angularFrequency * (t : ℝ) : ℝ) : ℂ) * Complex.I)) •
            referencedMediumTangentialMagneticFieldStrengthAmplitude plane medium wave) := by
  simpa only [zero_vadd, boundaryExponent_apply, Submodule.coe_zero,
    ComplexWaveVector.ofReal_zero, ComplexWaveVector.bilinearDot_zero_right, mul_zero, sub_zero]
    using mediumTangentialMagneticFieldStrengthData_tangent_vadd_point
      plane medium wave t (0 : plane.tangentSubmodule)

end ComplexMonochromaticPlaneWave

end
end ThreeDimension
end Electromagnetism
