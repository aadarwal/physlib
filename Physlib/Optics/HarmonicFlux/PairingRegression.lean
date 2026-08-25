/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.HarmonicFlux.Pairing

/-!
# Signed normal-flux pairing regressions

## i. Overview

This file uses an exact one-point profile to pin the factor, slot convention, conjugation, and
stored-normal orientation of `signedNormalFluxDensity`. The electric phasor is the first
coordinate unit vector, the magnetic-field-strength phasor is the second, and the first plane
normal is the third coordinate.

Putting `I` in the first profile scales the pairing by `I`; putting it in the second scales the
pairing by `-I`. This distinguishes the linear-first physics convention from Mathlib's usual
conjugate-first inner-product convention. Reversing only the stored normal negates the result.

## ii. Key results

- `signedNormalFluxDensity_regression_self`: exact self-density `1 / 2`.
- `signedNormalFluxDensity_regression_smul_first`: the first slot is complex-linear.
- `signedNormalFluxDensity_regression_smul_second`: the second slot is conjugate-linear.
- `signedNormalFluxDensity_regression_oppositeNormal`: reversing the normal reverses the sign.

## iii. Table of contents

- A. Exact profile and oriented planes
- B. Pairing convention regressions

## iv. References

The fixture exercises Physlib's own phasor and oriented-plane conventions. It is not a Maxwell
mode, finite aperture, modal-completeness, or total-power model.
-/

@[expose] public section

namespace Optics

open ClassicalMechanics Electromagnetism.ThreeDimension Space

noncomputable section

/-!

## A. Exact profile and oriented planes

-/

/-- The positive third-coordinate normal used by the signed-flux pairing regression. -/
def signedNormalFluxPairingRegressionNormal : Direction 3 :=
  ⟨Space.basis 2, by simp⟩

/-- The negative third-coordinate normal used to detect reversal of the stored orientation. -/
def signedNormalFluxPairingRegressionOppositeNormal : Direction 3 :=
  ⟨-Space.basis 2, by simp⟩

/-- The coordinate plane with stored normal along the positive third coordinate. -/
def signedNormalFluxPairingRegressionPlane : OrientedAffineHyperplane 3 where
  point := 0
  normal := signedNormalFluxPairingRegressionNormal

/-- The same coordinate plane with the stored normal reversed. -/
def signedNormalFluxPairingRegressionOppositePlane : OrientedAffineHyperplane 3 where
  point := 0
  normal := signedNormalFluxPairingRegressionOppositeNormal

/-- A one-point phasor profile with `E = e₁` and `H = e₂`. -/
def signedNormalFluxPairingRegressionProfile : HarmonicFieldProfile Unit :=
  fun _ ↦
    (WithLp.toLp 2 ![(1 : ℂ), 0, 0],
      WithLp.toLp 2 ![(0 : ℂ), 1, 0])

/-!

## B. Pairing convention regressions

-/

/-- The exact self-density is one half along the positive third-coordinate normal. -/
lemma signedNormalFluxDensity_regression_self :
    HarmonicFieldProfile.signedNormalFluxDensity
        signedNormalFluxPairingRegressionPlane
        signedNormalFluxPairingRegressionProfile
        signedNormalFluxPairingRegressionProfile () = 1 / 2 := by
  norm_num [HarmonicFieldProfile.signedNormalFluxDensity,
    HarmonicFieldProfile.mixedNormalFluxDensity,
    signedNormalFluxPairingRegressionPlane,
    signedNormalFluxPairingRegressionNormal,
    signedNormalFluxPairingRegressionProfile,
    HarmonicFieldProfile.electricPhasor,
    HarmonicFieldProfile.magneticFieldStrengthPhasor,
    OrientedAffineHyperplane.normalVector, ComplexWaveVector.bilinearDot,
    ComplexWaveVector.ofReal, ComplexMonochromaticPlaneWave.complexCross,
    Phasor.conjugateEuclidean, crossProduct, Fin.sum_univ_three,
    Matrix.cons_val_two, Matrix.head_cons]

/-- Scaling the first profile by `I` scales the signed-flux density by `I`. -/
lemma signedNormalFluxDensity_regression_smul_first :
    HarmonicFieldProfile.signedNormalFluxDensity
        signedNormalFluxPairingRegressionPlane
        (Complex.I • signedNormalFluxPairingRegressionProfile)
        signedNormalFluxPairingRegressionProfile () = Complex.I / 2 := by
  norm_num [HarmonicFieldProfile.signedNormalFluxDensity,
    HarmonicFieldProfile.mixedNormalFluxDensity,
    signedNormalFluxPairingRegressionPlane,
    signedNormalFluxPairingRegressionNormal,
    signedNormalFluxPairingRegressionProfile,
    HarmonicFieldProfile.electricPhasor,
    HarmonicFieldProfile.magneticFieldStrengthPhasor,
    OrientedAffineHyperplane.normalVector, ComplexWaveVector.bilinearDot,
    ComplexWaveVector.ofReal, ComplexMonochromaticPlaneWave.complexCross,
    Phasor.conjugateEuclidean, crossProduct, Fin.sum_univ_three,
    Matrix.cons_val_two, Matrix.head_cons]
  ring

/-- Scaling the second profile by `I` scales the signed-flux density by `-I`. -/
lemma signedNormalFluxDensity_regression_smul_second :
    HarmonicFieldProfile.signedNormalFluxDensity
        signedNormalFluxPairingRegressionPlane
        signedNormalFluxPairingRegressionProfile
        (Complex.I • signedNormalFluxPairingRegressionProfile) () = -Complex.I / 2 := by
  norm_num [HarmonicFieldProfile.signedNormalFluxDensity,
    HarmonicFieldProfile.mixedNormalFluxDensity,
    signedNormalFluxPairingRegressionPlane,
    signedNormalFluxPairingRegressionNormal,
    signedNormalFluxPairingRegressionProfile,
    HarmonicFieldProfile.electricPhasor,
    HarmonicFieldProfile.magneticFieldStrengthPhasor,
    OrientedAffineHyperplane.normalVector, ComplexWaveVector.bilinearDot,
    ComplexWaveVector.ofReal, ComplexMonochromaticPlaneWave.complexCross,
    Phasor.conjugateEuclidean, crossProduct, Fin.sum_univ_three,
    Matrix.cons_val_two, Matrix.head_cons]
  ring

/-- Reversing only the stored normal reverses the exact self-density. -/
lemma signedNormalFluxDensity_regression_oppositeNormal :
    HarmonicFieldProfile.signedNormalFluxDensity
        signedNormalFluxPairingRegressionOppositePlane
        signedNormalFluxPairingRegressionProfile
        signedNormalFluxPairingRegressionProfile () = -(1 / 2 : ℂ) := by
  norm_num [HarmonicFieldProfile.signedNormalFluxDensity,
    HarmonicFieldProfile.mixedNormalFluxDensity,
    signedNormalFluxPairingRegressionOppositePlane,
    signedNormalFluxPairingRegressionOppositeNormal,
    signedNormalFluxPairingRegressionProfile,
    HarmonicFieldProfile.electricPhasor,
    HarmonicFieldProfile.magneticFieldStrengthPhasor,
    OrientedAffineHyperplane.normalVector, ComplexWaveVector.bilinearDot,
    ComplexWaveVector.ofReal, ComplexMonochromaticPlaneWave.complexCross,
    Phasor.conjugateEuclidean, crossProduct, Fin.sum_univ_three,
    Matrix.cons_val_two, Matrix.head_cons]

end

end Optics
