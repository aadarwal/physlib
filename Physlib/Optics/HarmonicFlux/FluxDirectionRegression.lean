/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.HarmonicFlux.FluxDirection
public import Physlib.Optics.HarmonicFlux.PropagatingModeRegression

/-!
# Regressions for positive harmonic-flux direction

## i. Overview

This file reuses the exact propagating Maxwell fixture with electric phasor `e1 + I e2` and
magnetic-field-strength phasor `-I e1 + e2`. It independently expands their harmonic Poynting
vector to `e0`, then checks positive flux into the plane's positive side and failure into its
negative side.

The calculation never invokes the phase-direction equivalence. It therefore pins the Poynting
cross-product order, conjugation, material `H` convention, and oriented-side sign independently
of the geometric theorem.

## ii. Key results

- `propagatingFluxDirectionRegression_meanPoyntingVector`: the raw phasors give mean flux `e0`.
- `propagatingFluxDirectionRegression_positive`: the fixture has positive flux into the positive
  side.
- `propagatingFluxDirectionRegression_not_negative`: it does not have positive flux into the
  negative side.

## iii. Table of contents

- A. Raw mean-flux vector
- B. Oriented-side sentinels

## iv. References

These are exact regressions for Physlib's peak-phasor and oriented-hyperplane conventions. They do
not assert limiting absorption, radiation, causality, group velocity, or evanescent-wave meaning.
-/

@[expose] public section

namespace Optics

open ClassicalMechanics Electromagnetism Electromagnetism.ThreeDimension Matrix Space

noncomputable section

/-!
## A. Raw mean-flux vector
-/

/-- The fixture's local phasors give the exact time-averaged Poynting vector `e0`. -/
lemma propagatingFluxDirectionRegression_meanPoyntingVector :
    timeAveragedPoyntingVector
        ((propagatingModeRegressionFamily.wave ()).localElectricPhasor
          propagatingModeRegressionPlane.point)
        ((propagatingModeRegressionFamily.wave ()).localMagneticFieldStrengthPhasor
          propagatingModeRegressionFamily.medium propagatingModeRegressionPlane.point) =
      WithLp.toLp 2 ![(1 : ℝ), 0, 0] := by
  have hElectric :
      (propagatingModeRegressionFamily.wave ()).localElectricPhasor
          propagatingModeRegressionPlane.point =
        WithLp.toLp 2 ![(0 : ℂ), 1, Complex.I] := by
    simpa [propagatingModeRegressionPlane, propagatingModeRegressionPoint,
      PropagatingHarmonicModeFamily.modeProfile] using
      propagatingModeRegression_electricPhasor
  have hMagnetic :
      (propagatingModeRegressionFamily.wave ()).localMagneticFieldStrengthPhasor
          propagatingModeRegressionFamily.medium propagatingModeRegressionPlane.point =
        WithLp.toLp 2 ![(0 : ℂ), -Complex.I, 1] := by
    simpa [propagatingModeRegressionPlane, propagatingModeRegressionPoint,
      PropagatingHarmonicModeFamily.modeProfile] using
      propagatingModeRegression_magneticFieldStrengthPhasor
  rw [hElectric, hMagnetic]
  ext i
  fin_cases i <;>
    norm_num [timeAveragedPoyntingVector,
      ComplexMonochromaticPlaneWave.complexCross,
      ComplexWaveVector.realPart, Phasor.conjugateEuclidean,
      crossProduct, Matrix.cons_val_two, Matrix.head_cons]

/-!
## B. Oriented-side sentinels
-/

/-- The raw mean-flux vector has positive-side component one. -/
lemma propagatingFluxDirectionRegression_positiveSideComponent :
    inner ℝ (propagatingModeRegressionPlane.sideNormalVector .positive)
      (timeAveragedPoyntingVector
        ((propagatingModeRegressionFamily.wave ()).localElectricPhasor
          propagatingModeRegressionPlane.point)
        ((propagatingModeRegressionFamily.wave ()).localMagneticFieldStrengthPhasor
          propagatingModeRegressionFamily.medium propagatingModeRegressionPlane.point)) = 1 := by
  rw [propagatingFluxDirectionRegression_meanPoyntingVector,
    propagatingModeRegressionPlane.sideNormalVector_positive]
  norm_num [propagatingModeRegressionPlane, OrientedAffineHyperplane.normalVector,
    PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_three,
    Matrix.cons_val_two, Matrix.head_cons]

/-- The raw mean-flux vector has negative-side component minus one. -/
lemma propagatingFluxDirectionRegression_negativeSideComponent :
    inner ℝ (propagatingModeRegressionPlane.sideNormalVector .negative)
      (timeAveragedPoyntingVector
        ((propagatingModeRegressionFamily.wave ()).localElectricPhasor
          propagatingModeRegressionPlane.point)
        ((propagatingModeRegressionFamily.wave ()).localMagneticFieldStrengthPhasor
          propagatingModeRegressionFamily.medium propagatingModeRegressionPlane.point)) = -1 := by
  rw [propagatingFluxDirectionRegression_meanPoyntingVector,
    propagatingModeRegressionPlane.sideNormalVector_negative]
  norm_num [propagatingModeRegressionPlane, OrientedAffineHyperplane.normalVector,
    PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_three,
    Matrix.cons_val_two, Matrix.head_cons]

/-- The propagating fixture has strictly positive local mean flux into the positive side. -/
lemma propagatingFluxDirectionRegression_positive :
    (propagatingModeRegressionFamily.wave ()).HasPositiveMeanNormalFluxInto
      propagatingModeRegressionFamily.medium propagatingModeRegressionPlane .positive := by
  rw [ComplexMonochromaticPlaneWave.HasPositiveMeanNormalFluxInto,
    propagatingFluxDirectionRegression_positiveSideComponent]
  norm_num

/-- The same fixture does not have positive local mean flux into the negative side. -/
lemma propagatingFluxDirectionRegression_not_negative :
    ¬ (propagatingModeRegressionFamily.wave ()).HasPositiveMeanNormalFluxInto
      propagatingModeRegressionFamily.medium propagatingModeRegressionPlane .negative := by
  rw [ComplexMonochromaticPlaneWave.HasPositiveMeanNormalFluxInto,
    propagatingFluxDirectionRegression_negativeSideComponent]
  norm_num

end

end Optics
