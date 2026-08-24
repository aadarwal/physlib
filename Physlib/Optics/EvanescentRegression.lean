/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Evanescent
public import Physlib.Optics.Polarization.PositiveNormalDecayFrameRegression

/-!
# Regression tests for half-space evanescent plane waves

## i. Overview

This file classifies the independent exact complex material-wave fixture

`K = (5, 0, -4 I), E₀ = (4, 0, -5 I)`

as a nonzero half-space evanescent wave into the positive third-coordinate side. Its exact decay
rate is four. The opposite side fails, fixing the side sign rather than merely checking that
attenuation is nonzero.

A second carrier keeps the same angular frequency and on-shell complex wave vector but sets the
electric amplitude to zero. It remains transverse and dispersion matched with the same decay
geometry, yet fails because of the active-field guard. This shows why nonzero amplitude is part of
the optical classification.

## ii. Key results

- `complexDecayRegressionTM_isHalfSpaceEvanescent`: the exact TM field has the positive-side
  classification.
- `complexDecayRegressionTM_halfSpaceDecayRate`: its selected decay rate is exactly four.
- `complexDecayRegressionTM_localElectricPhasor_vadd_sideNormalVector`: the public field wrapper
  gives the exact `exp (-4 u)` scaling.
- `complexDecayRegressionTM_not_isHalfSpaceEvanescent_negative`: the same field does not decay
  into the negative side.
- `complexDecayRegressionZeroAmplitude_not_isHalfSpaceEvanescent`: the on-shell zero-amplitude
  copy is excluded specifically by the active-field requirement.

## iii. Table of contents

- A. Exact side-relative decay geometry
- B. Active TM classification
- C. Zero-amplitude guard

## iv. References

These are exact regressions for Physlib's own complex-wave and half-space evanescence APIs. No
external formal-development source is copied or translated here.
-/

@[expose] public section

namespace Optics

open ClassicalMechanics Electromagnetism Electromagnetism.ThreeDimension InnerProductSpace Space
open ClassicalMechanics.ComplexWaveVector
open Electromagnetism.ThreeDimension.ComplexMonochromaticPlaneWave

noncomputable section

/-!

## A. Exact side-relative decay geometry

-/

/-- The exact complex-decay vector has no attenuation tangent to the coordinate plane. -/
lemma complexDecayRegressionWaveVector_tangentialAttenuation_eq_zero :
    complexDecayRegressionPlane.tangentialProjection
        complexDecayRegressionWaveVector.attenuationVector = 0 := by
  rw [complexDecayRegressionWaveVector,
    PositiveNormalDecayWaveVector.attenuationVector_waveVector,
    positiveNormalDecayRegression_normalVector]
  ext i
  fin_cases i <;>
    simp [complexDecayRegressionPlane, positiveNormalDecayRegressionDirection,
      OrientedAffineHyperplane.tangentialProjection,
      OrientedAffineHyperplane.normalComponent, OrientedAffineHyperplane.normalVector,
      PiLp.inner_apply, RCLike.inner_apply]

/-- The exact attenuation vector has stored-normal component four. -/
lemma complexDecayRegressionWaveVector_normalAttenuation_eq_four :
    complexDecayRegressionPlane.normalComponent
        complexDecayRegressionWaveVector.attenuationVector = 4 := by
  rw [complexDecayRegressionWaveVector,
    PositiveNormalDecayWaveVector.attenuationVector_waveVector,
    positiveNormalDecayRegression_normalVector]
  norm_num [complexDecayRegressionPlane, positiveNormalDecayRegression,
    positiveNormalDecayRegressionDirection, OrientedAffineHyperplane.normalComponent,
    OrientedAffineHyperplane.normalVector, PiLp.inner_apply, RCLike.inner_apply]
  simp

/-- The exact complex-decay vector has attenuation strictly into the positive side. -/
lemma complexDecayRegressionWaveVector_isAttenuationDirectedInto_positive :
    complexDecayRegressionWaveVector.IsAttenuationDirectedInto
      complexDecayRegressionPlane .positive := by
  rw [isAttenuationDirectedInto_positive_iff,
    complexDecayRegressionWaveVector_normalAttenuation_eq_four]
  norm_num

/-- The exact complex-decay vector has no attenuation into the negative side. -/
lemma complexDecayRegressionWaveVector_not_isAttenuationDirectedInto_negative :
    ¬complexDecayRegressionWaveVector.IsAttenuationDirectedInto
      complexDecayRegressionPlane .negative := by
  rw [isAttenuationDirectedInto_negative_iff,
    complexDecayRegressionWaveVector_normalAttenuation_eq_four]
  norm_num

/-!

## B. Active TM classification

-/

/-- The exact TM electric amplitude is nonzero. -/
lemma complexDecayRegressionTM_electricAmplitude_ne_zero :
    complexDecayRegressionTM.electricAmplitude ≠ 0 := by
  intro hZero
  have hFirst := congrArg (fun amplitude ↦ amplitude 0) hZero
  norm_num [complexDecayRegressionTM] at hFirst

/-- The exact TM material carrier is half-space evanescent into the positive coordinate side. -/
lemma complexDecayRegressionTM_isHalfSpaceEvanescent :
    IsHalfSpaceEvanescent complexDecayRegressionPlane .positive
      complexDecayRegressionMedium complexDecayRegressionTM where
  electricAmplitude_ne_zero := complexDecayRegressionTM_electricAmplitude_ne_zero
  isTransverse := complexDecayRegressionTM_isTransverse
  isDispersionMatched := complexDecayRegressionTM_isDispersionMatched
  tangentialAttenuation_eq_zero :=
    complexDecayRegressionWaveVector_tangentialAttenuation_eq_zero
  isAttenuationDirectedInto :=
    complexDecayRegressionWaveVector_isAttenuationDirectedInto_positive

/-- The positive-side decay rate of the exact TM material carrier is four. -/
lemma complexDecayRegressionTM_halfSpaceDecayRate :
    halfSpaceDecayRate complexDecayRegressionPlane .positive complexDecayRegressionTM = 4 := by
  simpa [halfSpaceDecayRate, complexDecayRegressionTM,
    OrientedAffineHyperplane.sideNormalVector,
    OrientedAffineHyperplane.normalComponent] using
    complexDecayRegressionWaveVector_normalAttenuation_eq_four

/-- Positive third-coordinate displacement gives the exact `exp (-4 u)` local electric-phasor
scaling through the named half-space API. -/
lemma complexDecayRegressionTM_localElectricPhasor_vadd_sideNormalVector
    (u : ℝ) (x : Space) :
    complexDecayRegressionTM.localElectricPhasor
        (u • complexDecayRegressionPlane.sideNormalVector .positive +ᵥ x) =
      (Real.exp (-4 * u) : ℂ) • complexDecayRegressionTM.localElectricPhasor x := by
  simpa [complexDecayRegressionTM_halfSpaceDecayRate] using
    complexDecayRegressionTM_isHalfSpaceEvanescent.localElectricPhasor_vadd_sideNormalVector u x

/-- Reversing the selected side rejects the exact TM material carrier. -/
lemma complexDecayRegressionTM_not_isHalfSpaceEvanescent_negative :
    ¬IsHalfSpaceEvanescent complexDecayRegressionPlane .negative
      complexDecayRegressionMedium complexDecayRegressionTM := by
  intro hEvanescent
  exact complexDecayRegressionWaveVector_not_isAttenuationDirectedInto_negative
    hEvanescent.isAttenuationDirectedInto

/-!

## C. Zero-amplitude guard

-/

/-- The on-shell complex-decay carrier with its electric amplitude replaced by zero. -/
def complexDecayRegressionZeroAmplitude : ComplexMonochromaticPlaneWave where
  angularFrequency := complexDecayRegressionTM.angularFrequency
  angularFrequency_pos := complexDecayRegressionTM.angularFrequency_pos
  waveVector := complexDecayRegressionWaveVector
  electricAmplitude := 0

/-- The zero-amplitude copy remains bilinearly transverse. -/
lemma complexDecayRegressionZeroAmplitude_isTransverse :
    complexDecayRegressionZeroAmplitude.IsTransverse := by
  simp [ComplexMonochromaticPlaneWave.IsTransverse, complexDecayRegressionZeroAmplitude]

/-- The zero-amplitude copy remains on the same material shell. -/
lemma complexDecayRegressionZeroAmplitude_isDispersionMatched :
    complexDecayRegressionZeroAmplitude.IsDispersionMatched complexDecayRegressionMedium := by
  have hMatched := complexDecayRegressionTM_isDispersionMatched
  rw [IsDispersionMatched] at hMatched ⊢
  simpa [complexDecayRegressionZeroAmplitude, complexDecayRegressionTM] using hMatched

/-- The zero-amplitude copy retains zero tangential attenuation. -/
lemma complexDecayRegressionZeroAmplitude_tangentialAttenuation_eq_zero :
    complexDecayRegressionPlane.tangentialProjection
        complexDecayRegressionZeroAmplitude.waveVector.attenuationVector = 0 :=
  complexDecayRegressionWaveVector_tangentialAttenuation_eq_zero

/-- The zero-amplitude copy retains strict positive-side attenuation. -/
lemma complexDecayRegressionZeroAmplitude_isAttenuationDirectedInto_positive :
    complexDecayRegressionZeroAmplitude.waveVector.IsAttenuationDirectedInto
      complexDecayRegressionPlane .positive :=
  complexDecayRegressionWaveVector_isAttenuationDirectedInto_positive

/-- Despite satisfying the other four defining conditions, the on-shell zero-amplitude carrier
does not satisfy the active half-space evanescence predicate. -/
lemma complexDecayRegressionZeroAmplitude_not_isHalfSpaceEvanescent :
    ¬IsHalfSpaceEvanescent complexDecayRegressionPlane .positive
      complexDecayRegressionMedium complexDecayRegressionZeroAmplitude := by
  intro hEvanescent
  exact hEvanescent.electricAmplitude_ne_zero rfl

end

end Optics
