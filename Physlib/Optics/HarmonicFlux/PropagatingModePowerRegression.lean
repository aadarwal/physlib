/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.HarmonicFlux.PropagatingModePower
public import Physlib.Optics.HarmonicFlux.PropagatingModeRegression

/-!
# Regressions for synthesized propagating modal power

## i. Overview

This file drives the singleton propagating Maxwell family with complex modal coordinate
`3 + 4 I`. At the spacetime origin, scaling occurs before ordinary-real realization and produces
electric field `(0, 3, -4)` and magnetic field strength `(0, 4, 3)`. Their instantaneous Poynting
vector is `(25, 0, 0)`.

The sentinel `propagatingModePowerRegression_isApertureFluxOrthonormal` independently pins the
singleton profile's outgoing flux normalization under counting measure. The physical normalization
theorem then gives actual integrated one-period normal flux twenty-five for every period start,
equal to the coordinate power `|3 + 4 I|^2`.

## ii. Key results

- `propagatingModePowerRegression_isApertureFluxOrthonormal`: the physical singleton profile is
  outgoing normalized.
- `propagatingModePowerRegression_electricField_origin`: complex scaling before realization.
- `propagatingModePowerRegression_magneticFieldStrength_origin`: the matching material field.
- `propagatingModePowerRegression_integratedActualMeanNormalFlux`: actual flux equals power 25.

## iii. Table of contents

- A. Normalized physical profile and modal coordinate
- B. Exact synthesized fields
- C. Actual one-period modal power

## iv. References

These are exact Physlib convention checks. Counting measure is a discrete profile weight, not a
claimed geometric aperture-area measure, and the singleton result asserts no mode completeness.
-/

@[expose] public section

namespace Optics

open Electromagnetism Electromagnetism.ThreeDimension
open MeasureTheory Space Time

noncomputable section

/-!

## A. Normalized physical profile and modal coordinate

-/

/-- The physical singleton profile is outgoing flux-orthonormal under counting measure (sentinel:
`propagatingModePowerRegression_isApertureFluxOrthonormal`). -/
lemma propagatingModePowerRegression_isApertureFluxOrthonormal :
    HarmonicFieldProfile.IsApertureFluxOrthonormal Measure.count
      propagatingModeRegressionPlane .outgoing
      (propagatingModeRegressionFamily.modeProfile propagatingModeRegressionPoint) := by
  refine ⟨fun _ _ ↦ Integrable.of_finite, ?_, ?_⟩
  · intro i
    cases i
    exact propagatingModeRegression_integratedMeanNormalFlux
  · intro i j hij
    exact (hij (Subsingleton.elim i j)).elim

/-- The exact complex modal coordinate `3 + 4 I`. -/
def propagatingModePowerRegressionAmplitude : ModeAmplitude Unit :=
  WithLp.toLp 2 fun _ ↦ 3 + 4 * Complex.I

/-- The singleton coordinate has normalized modal power twenty-five. -/
lemma propagatingModePowerRegressionAmplitude_power :
    propagatingModePowerRegressionAmplitude.power = 25 := by
  rw [ModeAmplitude.power_eq_sum_normSq]
  norm_num [propagatingModePowerRegressionAmplitude, Complex.normSq_apply]

/-!

## B. Exact synthesized fields

-/

/-- Complex coefficient scaling before realization gives electric field `(0, 3, -4)` at the
spacetime origin. -/
lemma propagatingModePowerRegression_electricField_origin :
    propagatingModeRegressionFamily.synthesizedElectricField
        propagatingModePowerRegressionAmplitude (0 : Time) (0 : Space) =
      WithLp.toLp 2 ![(0 : ℝ), 3, -4] := by
  have hElectric :
      (propagatingModeRegressionFamily.wave ()).localElectricPhasor 0 =
        WithLp.toLp 2 ![(0 : ℂ), 1, Complex.I] := by
    simpa [HarmonicFieldProfile.electricPhasor,
      PropagatingHarmonicModeFamily.modeProfile, propagatingModeRegressionPoint] using
      propagatingModeRegression_electricPhasor
  rw [propagatingModeRegressionFamily.synthesizedElectricField_eq_realize]
  rw [propagatingModeRegressionFamily.synthesizedProfile_electricPhasor]
  rw [Fintype.sum_unique, hElectric]
  ext i
  fin_cases i <;>
    norm_num [propagatingModePowerRegressionAmplitude,
      propagatingModeRegressionFamily, Phasor.realize]

/-- The matching material magnetic field strength is `(0, 4, 3)` at the spacetime origin. -/
lemma propagatingModePowerRegression_magneticFieldStrength_origin :
    propagatingModeRegressionFamily.synthesizedMagneticFieldStrength
        propagatingModePowerRegressionAmplitude (0 : Time) (0 : Space) =
      WithLp.toLp 2 ![(0 : ℝ), 4, 3] := by
  have hMagnetic :
      (propagatingModeRegressionFamily.wave ()).localMagneticFieldStrengthPhasor
          propagatingModeRegressionFamily.medium 0 =
        WithLp.toLp 2 ![(0 : ℂ), -Complex.I, 1] := by
    simpa [HarmonicFieldProfile.magneticFieldStrengthPhasor,
      PropagatingHarmonicModeFamily.modeProfile, propagatingModeRegressionPoint] using
      propagatingModeRegression_magneticFieldStrengthPhasor
  rw [propagatingModeRegressionFamily.synthesizedMagneticFieldStrength_eq_realize]
  rw [propagatingModeRegressionFamily.synthesizedProfile_magneticFieldStrengthPhasor]
  rw [Fintype.sum_unique, hMagnetic]
  ext i
  fin_cases i <;>
    norm_num [propagatingModePowerRegressionAmplitude,
      propagatingModeRegressionFamily, Phasor.realize]

/-!

## C. Actual one-period modal power

-/

/-- The actual synthesized fields remain a source-free Maxwell solution. -/
lemma propagatingModePowerRegression_isMacroscopicMaxwellSolution :
    propagatingModeRegressionFamily.medium.IsMacroscopicMaxwellSolution
      (propagatingModeRegressionFamily.synthesizedElectricField
        propagatingModePowerRegressionAmplitude)
      (propagatingModeRegressionFamily.synthesizedElectricDisplacement
        propagatingModePowerRegressionAmplitude)
      (propagatingModeRegressionFamily.synthesizedMagneticInduction
        propagatingModePowerRegressionAmplitude)
      (propagatingModeRegressionFamily.synthesizedMagneticFieldStrength
        propagatingModePowerRegressionAmplitude) 0 0 :=
  propagatingModeRegressionFamily.synthesized_isMacroscopicMaxwellSolution
    propagatingModePowerRegressionAmplitude

/-- For every period start, actual integrated one-period normal flux equals coordinate power 25;
its outgoing role sign is pinned by
`propagatingModePowerRegression_isApertureFluxOrthonormal`. -/
lemma propagatingModePowerRegression_integratedActualMeanNormalFlux (startTime : Time) :
    propagatingModeRegressionFamily.integratedActualMeanNormalFlux Measure.count
      propagatingModeRegressionPlane propagatingModeRegressionPoint
      propagatingModePowerRegressionAmplitude startTime = 25 := by
  calc
    _ = propagatingModePowerRegressionAmplitude.power :=
      propagatingModeRegressionFamily.outgoing_integratedActualMeanNormalFlux_eq_power
        propagatingModePowerRegression_isApertureFluxOrthonormal _ _
    _ = 25 := propagatingModePowerRegressionAmplitude_power

end

end Optics
