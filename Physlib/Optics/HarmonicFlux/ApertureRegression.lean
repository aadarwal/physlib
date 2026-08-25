/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Physlib.Optics.HarmonicFlux.Aperture

/-!
# Measured-profile signed-flux regressions

## i. Overview

This file evaluates signed normal flux on a two-cell counting-measure profile domain. The real
envelope is `7 / 5` on the first cell and `1 / 5` on the second, so the positive self-flux
contributions are independently `49 / 50` and `1 / 50`. Their sum is one.
Replacing counting measure by one copy of the first-cell Dirac measure and two copies of the
second-cell Dirac measure changes the same self-pairing to `51 / 50`, so the supplied measure is
load-bearing.

The exact values pin profile-domain integration and the stored-normal sign without describing the
two cells as a geometric surface mesh. Orthogonality and negative-normal extensions are separated
into `ApertureRegressionOrthogonality`.

## ii. Key results

- `apertureFluxRegressionPositive_self`: the two unequal cells integrate to unit positive flux.
- `apertureFluxRegressionPositive_weighted_self`: unequal measure weights give `51 / 50`.

## iii. Table of contents

- A. Two-cell profile data
- B. Exact local and integrated flux values

## iv. References

The finite counting measure is an exact quadrature convention internal to this regression. The
fixture is supplied phasor data, not a claim of Maxwell qualification or geometric surface area.
-/

@[expose] public section

namespace Optics

open ClassicalMechanics Electromagnetism.ThreeDimension MeasureTheory Space

noncomputable section

/-!

## A. Two-cell profile data

-/

/-- The positive third-coordinate normal of the two-cell aperture fixture. -/
def apertureFluxRegressionNormal : Direction 3 :=
  ⟨Space.basis 2, by simp⟩

/-- The oriented coordinate plane of the two-cell aperture fixture. -/
def apertureFluxRegressionPlane : OrientedAffineHyperplane 3 where
  point := 0
  normal := apertureFluxRegressionNormal

/-- The unequal real envelope values `7 / 5` and `1 / 5`. -/
def apertureFluxRegressionEnvelope : Fin 2 → ℂ :=
  ![7 / 5, 1 / 5]

/-- One first-cell Dirac mass and two second-cell Dirac masses. -/
def apertureFluxRegressionWeightedMeasure : Measure (Fin 2) :=
  Measure.dirac 0 + Measure.dirac 1 + Measure.dirac 1

/-- Positive-normal profile with electric phasor along coordinate one and magnetic phasor along
coordinate two. -/
def apertureFluxRegressionPositive : HarmonicFieldProfile (Fin 2) :=
  fun x ↦
    (WithLp.toLp 2 ![apertureFluxRegressionEnvelope x, 0, 0],
      WithLp.toLp 2 ![0, apertureFluxRegressionEnvelope x, 0])

/-!

## B. Exact local and integrated flux values

-/

/-- The first cell contributes `49 / 50` to the positive profile's self-flux. -/
lemma apertureFluxRegressionPositive_density_zero :
    HarmonicFieldProfile.signedNormalFluxDensity apertureFluxRegressionPlane
        apertureFluxRegressionPositive apertureFluxRegressionPositive 0 = 49 / 50 := by
  norm_num [HarmonicFieldProfile.signedNormalFluxDensity,
    HarmonicFieldProfile.mixedNormalFluxDensity, apertureFluxRegressionPlane,
    apertureFluxRegressionNormal, apertureFluxRegressionPositive,
    apertureFluxRegressionEnvelope, OrientedAffineHyperplane.normalVector,
    HarmonicFieldProfile.electricPhasor,
    HarmonicFieldProfile.magneticFieldStrengthPhasor,
    ComplexWaveVector.bilinearDot, ComplexWaveVector.ofReal,
    ComplexMonochromaticPlaneWave.complexCross, Phasor.conjugateEuclidean,
    crossProduct, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.head_cons,
    Complex.star_def, map_div₀, map_ofNat]

/-- The second cell contributes `1 / 50` to the positive profile's self-flux. -/
lemma apertureFluxRegressionPositive_density_one :
    HarmonicFieldProfile.signedNormalFluxDensity apertureFluxRegressionPlane
        apertureFluxRegressionPositive apertureFluxRegressionPositive 1 = 1 / 50 := by
  norm_num [HarmonicFieldProfile.signedNormalFluxDensity,
    HarmonicFieldProfile.mixedNormalFluxDensity, apertureFluxRegressionPlane,
    apertureFluxRegressionNormal, apertureFluxRegressionPositive,
    apertureFluxRegressionEnvelope, OrientedAffineHyperplane.normalVector,
    HarmonicFieldProfile.electricPhasor,
    HarmonicFieldProfile.magneticFieldStrengthPhasor,
    ComplexWaveVector.bilinearDot, ComplexWaveVector.ofReal,
    ComplexMonochromaticPlaneWave.complexCross, Phasor.conjugateEuclidean,
    crossProduct, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.head_cons,
    Complex.star_def, map_div₀, map_ofNat]

/-- The two-cell counting-measure self-pairing of the first positive profile is one. -/
lemma apertureFluxRegressionPositive_self :
    HarmonicFieldProfile.signedNormalFluxPairing Measure.count apertureFluxRegressionPlane
      apertureFluxRegressionPositive apertureFluxRegressionPositive = 1 := by
  norm_num [HarmonicFieldProfile.signedNormalFluxPairing,
    apertureFluxRegressionPositive_density_zero,
    apertureFluxRegressionPositive_density_one, Fin.sum_univ_two]

/-- Unequal cell weights change the same profile's exact self-pairing to `51 / 50`. -/
lemma apertureFluxRegressionPositive_weighted_self :
    HarmonicFieldProfile.signedNormalFluxPairing
        apertureFluxRegressionWeightedMeasure apertureFluxRegressionPlane
        apertureFluxRegressionPositive apertureFluxRegressionPositive = 51 / 50 := by
  rw [HarmonicFieldProfile.signedNormalFluxPairing,
    apertureFluxRegressionWeightedMeasure,
    integral_add_measure Integrable.of_finite Integrable.of_finite,
    integral_add_measure Integrable.of_finite Integrable.of_finite]
  simp [apertureFluxRegressionPositive_density_zero,
    apertureFluxRegressionPositive_density_one]
  norm_num

end

end Optics
