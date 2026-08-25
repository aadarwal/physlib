/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public
import Physlib.Electromagnetism.ThreeDimension.MonochromaticPlaneWave.ComplexMaxwellRegression
public import Physlib.Optics.HarmonicFlux.PropagatingMode

/-!
# Regressions for Maxwell-qualified propagating mode profiles

## i. Overview

This file packages the existing real-embedding Maxwell fixture as a singleton propagating harmonic
mode family. In the medium `epsilon = mu = 3`, its common frequency is one, its real wave vector is
`3 e0`, and its complex electric amplitude is `e1 + I e2`. At the spatial origin the local
magnetic-field-strength phasor is `-I e1 + e2`, so the exact one-period Poynting mean is `e0`.

Counting measure on the singleton profile domain therefore gives actual integrated mean normal
flux one. The calculation pins the local spatial-factor retention, magnetic-field-strength rather
than magnetic-induction convention, stored-normal orientation, and actual-period connector.

## ii. Key results

- `propagatingModeRegressionFamily`: an exact common-frequency Maxwell family.
- `propagatingModeRegression_electricPhasor`: the local electric phasor.
- `propagatingModeRegression_magneticFieldStrengthPhasor`: the local material `H` phasor.
- `propagatingModeRegression_integral_intervalAverage_normalFlux`: actual integrated flux one.

## iii. Table of contents

- A. Singleton propagating family
- B. Exact local phasors
- C. Actual integrated one-period flux

## iv. References

These are exact regressions for Physlib's own carrier and normalization conventions. The singleton
counting measure is a discrete profile weight, not a claimed geometric aperture-area measure.
-/

@[expose] public section

namespace Optics

open Electromagnetism Electromagnetism.ThreeDimension
open ClassicalMechanics Matrix MeasureTheory Space Time
open scoped Interval Real

noncomputable section

open ComplexMonochromaticPlaneWave PropagatingHarmonicModeFamily

/-!

## A. Singleton propagating family

-/

/-- The singleton common-frequency propagating Maxwell family. -/
def propagatingModeRegressionFamily : PropagatingHarmonicModeFamily Unit where
  medium := complexDecayRegressionMedium
  angularFrequency := 1
  angularFrequency_pos := by norm_num
  wave := fun _ ↦ ComplexMonochromaticPlaneWave.ofReal realEmbeddingRegressionWave
  commonAngularFrequency := by intro i; cases i; rfl
  zeroAttenuation := by
    intro i
    cases i
    exact ComplexWaveVector.attenuationVector_ofReal _
  isTransverse := by
    intro i
    cases i
    rw [ComplexMonochromaticPlaneWave.isTransverse_ofReal_iff]
    constructor <;>
      norm_num [realEmbeddingRegressionWave, MonochromaticPlaneWave.inMedium,
        MonochromaticPlaneWave.propagationVector, PiLp.inner_apply,
        RCLike.inner_apply, Fin.sum_univ_three]
  isDispersionMatched := by
    intro i
    cases i
    rw [ComplexMonochromaticPlaneWave.isDispersionMatched_ofReal_iff]
    exact MonochromaticPlaneWave.inMedium_isDispersionMatched _ _ _ _ _ _

/-- The singleton profile samples the physical fields at the spatial origin. -/
def propagatingModeRegressionPoint : Unit → Space := fun _ ↦ 0

/-- The regression cross-section stores the propagation direction as its positive normal. -/
def propagatingModeRegressionPlane : OrientedAffineHyperplane 3 where
  point := 0
  normal := ⟨Space.basis 0, by simp⟩

/-- The family satisfies the positive propagating dispersion branch at frequency one. -/
lemma propagatingModeRegression_phaseVector_norm_mul_waveSpeed :
    ‖(propagatingModeRegressionFamily.wave ()).waveVector.phaseVector‖ *
        propagatingModeRegressionFamily.medium.waveSpeed = 1 := by
  exact propagatingModeRegressionFamily.wave_phaseVector_norm_mul_waveSpeed ()

/-!

## B. Exact local phasors

-/

/-- At the sampled origin the electric phasor is `e1 + I e2`. -/
lemma propagatingModeRegression_electricPhasor :
    HarmonicFieldProfile.electricPhasor
        (propagatingModeRegressionFamily.modeProfile propagatingModeRegressionPoint ()) () =
      WithLp.toLp 2 ![(0 : ℂ), 1, Complex.I] := by
  ext i
  fin_cases i <;>
    norm_num [PropagatingHarmonicModeFamily.modeProfile,
      propagatingModeRegressionFamily, propagatingModeRegressionPoint,
      ComplexMonochromaticPlaneWave.localElectricPhasor,
      ComplexMonochromaticPlaneWave.ofReal,
      realEmbeddingRegressionWave, MonochromaticPlaneWave.inMedium,
      ComplexWaveVector.spatialFactor, ComplexWaveVector.spatialPairing,
      ComplexWaveVector.bilinearDot, Fin.sum_univ_three,
      ComplexWaveVector.ofReal]

/-- At the sampled origin the material magnetic-field-strength phasor is `-I e1 + e2`. -/
lemma propagatingModeRegression_magneticFieldStrengthPhasor :
    HarmonicFieldProfile.magneticFieldStrengthPhasor
        (propagatingModeRegressionFamily.modeProfile propagatingModeRegressionPoint ()) () =
      WithLp.toLp 2 ![(0 : ℂ), -Complex.I, 1] := by
  ext i
  fin_cases i <;>
    simp [propagatingModeRegressionFamily, propagatingModeRegressionPoint,
      ComplexMonochromaticPlaneWave.localMagneticFieldStrengthPhasor,
      ComplexMonochromaticPlaneWave.ofReal,
      ComplexMonochromaticPlaneWave.magneticAmplitude,
      ComplexMonochromaticPlaneWave.complexCross, crossProduct,
      realEmbeddingRegressionWave, MonochromaticPlaneWave.inMedium,
      MonochromaticPlaneWave.waveVector, MonochromaticPlaneWave.propagationVector,
      complexDecayRegressionMedium, HomogeneousIsotropicMedium.waveSpeed,
      ComplexWaveVector.spatialFactor,
      ComplexWaveVector.spatialPairing, ComplexWaveVector.bilinearDot,
      ComplexWaveVector.ofReal, Matrix.cons_val_two, Matrix.head_cons]

/-!

## C. Actual integrated one-period flux

-/

/-- The singleton profile's local mean flux density along the stored normal is one. -/
lemma propagatingModeRegression_meanNormalFluxDensity :
    HarmonicFieldProfile.meanNormalFluxDensity propagatingModeRegressionPlane
      (propagatingModeRegressionFamily.modeProfile propagatingModeRegressionPoint ()) () = 1 := by
  rw [HarmonicFieldProfile.meanNormalFluxDensity,
    propagatingModeRegression_electricPhasor,
    propagatingModeRegression_magneticFieldStrengthPhasor]
  norm_num [propagatingModeRegressionPlane,
    OrientedAffineHyperplane.normalComponent,
    OrientedAffineHyperplane.normalVector, timeAveragedPoyntingVector,
    ComplexMonochromaticPlaneWave.complexCross, Phasor.conjugateEuclidean,
    ComplexWaveVector.realPart, crossProduct, PiLp.inner_apply,
    RCLike.inner_apply, Fin.sum_univ_three, Matrix.cons_val_two,
    Matrix.head_cons]

/-- The abstract singleton profile has integrated mean normal flux one. -/
lemma propagatingModeRegression_integratedMeanNormalFlux :
    HarmonicFieldProfile.integratedMeanNormalFlux Measure.count
      propagatingModeRegressionPlane
      (propagatingModeRegressionFamily.modeProfile propagatingModeRegressionPoint ()) = 1 := by
  rw [HarmonicFieldProfile.integratedMeanNormalFlux]
  have hpoint : ∀ a : Unit,
      HarmonicFieldProfile.meanNormalFluxDensity propagatingModeRegressionPlane
        (propagatingModeRegressionFamily.modeProfile propagatingModeRegressionPoint ()) a = 1 := by
    intro a
    cases a
    exact propagatingModeRegression_meanNormalFluxDensity
  simp_rw [hpoint]
  norm_num

/-- For every period start, the actual integrated one-period mean normal Poynting flux is one. -/
lemma propagatingModeRegression_integral_intervalAverage_normalFlux (startTime : Time) :
    (∫ a, propagatingModeRegressionPlane.normalComponent
      (⨍ time in startTime.val..startTime.val + 2 * Real.pi,
        poyntingVector (propagatingModeRegressionFamily.wave ()).electricField
          ((propagatingModeRegressionFamily.wave ()).magneticFieldStrength
            propagatingModeRegressionFamily.medium)
          (time : Time) (propagatingModeRegressionPoint a)) ∂Measure.count) = 1 := by
  calc
    _ = HarmonicFieldProfile.integratedMeanNormalFlux Measure.count
        propagatingModeRegressionPlane
        (propagatingModeRegressionFamily.modeProfile propagatingModeRegressionPoint ()) := by
      simpa [propagatingModeRegressionFamily] using
        (integral_intervalAverage_normalFlux_eq_integratedMeanNormalFlux
            propagatingModeRegressionFamily
            Measure.count propagatingModeRegressionPlane propagatingModeRegressionPoint
            () startTime)
    _ = 1 := propagatingModeRegression_integratedMeanNormalFlux

end

end Optics
