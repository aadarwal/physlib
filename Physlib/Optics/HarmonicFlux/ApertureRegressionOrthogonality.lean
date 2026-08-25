/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.HarmonicFlux.ApertureRegression

/-!
# Signed-flux orthogonality regressions

## i. Overview

This file extends the exact two-cell measured-profile fixture with a quarter-turned positive-normal
profile and a profile obtained by reversing only the original magnetic phasor. The two
positive-normal profiles have unit self-flux and zero cross-pairing. Magnetic reversal gives
signed self-flux minus one and remains orthogonal to the original profile.

The profile signs are computed relative to the stored normal. Incident and outgoing roles are
assigned only in the later finite-mode normalization layer.

## ii. Key results

- `apertureFluxRegressionSecond_self`: the quarter-turned profile has unit positive flux.
- `apertureFluxRegressionNegative_self`: magnetic reversal has unit negative flux.
- `apertureFluxRegressionPositive_second`: the positive profiles are flux-orthogonal.
- `apertureFluxRegressionPositive_negative`: the positive- and negative-normal profiles are
  flux-orthogonal.

## iii. Table of contents

- A. Additional exact profiles
- B. Exact self- and cross-pairings

## iv. References

The finite counting measure is an exact quadrature convention internal to the regression. The
profiles are supplied phasor data, not Maxwell-qualified propagating modes.
-/

@[expose] public section

namespace Optics

open ClassicalMechanics Electromagnetism.ThreeDimension MeasureTheory Space

noncomputable section

/-!

## A. Additional exact profiles

-/

/-- Positive-normal profile with the two transverse coordinate roles quarter-turned. -/
def apertureFluxRegressionSecond : HarmonicFieldProfile (Fin 2) :=
  fun x ↦
    (WithLp.toLp 2 ![0, apertureFluxRegressionEnvelope x, 0],
      WithLp.toLp 2 ![-apertureFluxRegressionEnvelope x, 0, 0])

/-- Negative-normal profile obtained by reversing the first profile's magnetic phasor. -/
def apertureFluxRegressionNegative : HarmonicFieldProfile (Fin 2) :=
  fun x ↦
    (WithLp.toLp 2 ![apertureFluxRegressionEnvelope x, 0, 0],
      WithLp.toLp 2 ![0, -apertureFluxRegressionEnvelope x, 0])

/-!

## B. Exact self- and cross-pairings

-/

/-- The orthogonal positive profile also has unit counting-measure self-flux. -/
lemma apertureFluxRegressionSecond_self :
    HarmonicFieldProfile.signedNormalFluxPairing Measure.count apertureFluxRegressionPlane
      apertureFluxRegressionSecond apertureFluxRegressionSecond = 1 := by
  norm_num [HarmonicFieldProfile.signedNormalFluxPairing,
    HarmonicFieldProfile.signedNormalFluxDensity,
    HarmonicFieldProfile.mixedNormalFluxDensity, apertureFluxRegressionPlane,
    apertureFluxRegressionNormal, apertureFluxRegressionSecond,
    apertureFluxRegressionEnvelope, OrientedAffineHyperplane.normalVector,
    HarmonicFieldProfile.electricPhasor,
    HarmonicFieldProfile.magneticFieldStrengthPhasor,
    ComplexWaveVector.bilinearDot, ComplexWaveVector.ofReal,
    ComplexMonochromaticPlaneWave.complexCross, Phasor.conjugateEuclidean,
    crossProduct, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val_two, Matrix.head_cons, Complex.star_def, map_div₀,
    map_ofNat]

/-- Magnetic reversal gives unit negative self-flux under the same stored normal. -/
lemma apertureFluxRegressionNegative_self :
    HarmonicFieldProfile.signedNormalFluxPairing Measure.count apertureFluxRegressionPlane
      apertureFluxRegressionNegative apertureFluxRegressionNegative = -1 := by
  norm_num [HarmonicFieldProfile.signedNormalFluxPairing,
    HarmonicFieldProfile.signedNormalFluxDensity,
    HarmonicFieldProfile.mixedNormalFluxDensity, apertureFluxRegressionPlane,
    apertureFluxRegressionNormal, apertureFluxRegressionNegative,
    apertureFluxRegressionEnvelope, OrientedAffineHyperplane.normalVector,
    HarmonicFieldProfile.electricPhasor,
    HarmonicFieldProfile.magneticFieldStrengthPhasor,
    ComplexWaveVector.bilinearDot, ComplexWaveVector.ofReal,
    ComplexMonochromaticPlaneWave.complexCross, Phasor.conjugateEuclidean,
    crossProduct, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val_two, Matrix.head_cons, Complex.star_def, map_div₀,
    map_ofNat]

/-- The two positive transverse profiles are mutually flux-orthogonal. -/
lemma apertureFluxRegressionPositive_second :
    HarmonicFieldProfile.signedNormalFluxPairing Measure.count apertureFluxRegressionPlane
      apertureFluxRegressionPositive apertureFluxRegressionSecond = 0 := by
  norm_num [HarmonicFieldProfile.signedNormalFluxPairing,
    HarmonicFieldProfile.signedNormalFluxDensity,
    HarmonicFieldProfile.mixedNormalFluxDensity, apertureFluxRegressionPlane,
    apertureFluxRegressionNormal, apertureFluxRegressionPositive,
    apertureFluxRegressionSecond, apertureFluxRegressionEnvelope,
    OrientedAffineHyperplane.normalVector, ComplexWaveVector.bilinearDot,
    HarmonicFieldProfile.electricPhasor,
    HarmonicFieldProfile.magneticFieldStrengthPhasor,
    ComplexWaveVector.ofReal, ComplexMonochromaticPlaneWave.complexCross,
    Phasor.conjugateEuclidean, crossProduct, Fin.sum_univ_three,
    Fin.sum_univ_two, Matrix.cons_val_two, Matrix.head_cons,
    Complex.star_def, map_div₀, map_ofNat]

/-- The chosen positive- and negative-normal profiles are mutually flux-orthogonal. -/
lemma apertureFluxRegressionPositive_negative :
    HarmonicFieldProfile.signedNormalFluxPairing Measure.count apertureFluxRegressionPlane
      apertureFluxRegressionPositive apertureFluxRegressionNegative = 0 := by
  norm_num [HarmonicFieldProfile.signedNormalFluxPairing,
    HarmonicFieldProfile.signedNormalFluxDensity,
    HarmonicFieldProfile.mixedNormalFluxDensity, apertureFluxRegressionPlane,
    apertureFluxRegressionNormal, apertureFluxRegressionPositive,
    apertureFluxRegressionNegative, apertureFluxRegressionEnvelope,
    OrientedAffineHyperplane.normalVector, ComplexWaveVector.bilinearDot,
    HarmonicFieldProfile.electricPhasor,
    HarmonicFieldProfile.magneticFieldStrengthPhasor,
    ComplexWaveVector.ofReal, ComplexMonochromaticPlaneWave.complexCross,
    Phasor.conjugateEuclidean, crossProduct, Fin.sum_univ_three,
    Fin.sum_univ_two, Matrix.cons_val_two, Matrix.head_cons,
    Complex.star_def, map_div₀, map_ofNat]

end

end Optics
