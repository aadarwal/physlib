/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.HarmonicFlux.MaterialWave

/-!
# Material plane-wave harmonic-flux regressions

## i. Overview

This file distinguishes instantaneous from time-averaged material plane-wave flux using two
canonical Jones states. The positive-`I` quadrature state has constant instantaneous electric
norm, so its instantaneous Poynting vector always equals the mean-flux vector. By contrast, the
horizontal state has zero instantaneous flux at one quarter period at the spatial origin while
its one-period mean flux is nonzero.

Together these exact results test that harmonic averaging is substantive, while retaining the
repository's algebraic quadrature name rather than assigning a circular-polarization handedness.

## ii. Key results

- `plusIQuadrature_toMaterialPlaneWave_poyntingVector`: constant quadrature-state flux.
- `horizontal_toMaterialPlaneWave_poyntingVector_quarterPeriod_origin`: a zero instantaneous
  linear-state sample.
- `horizontal_toMaterialPlaneWave_intervalAverage_poyntingVector_ne_zero`: the same state's
  nonzero mean flux.

## iii. Table of contents

- A. Constant quadrature-state flux
- B. Instantaneous versus mean linear-state flux

## iv. References

These regressions use arbitrary oriented polarization frames and homogeneous isotropic media.
They introduce no observer-dependent handedness, interface normal, aperture power, modal
normalization, outgoing-wave role, or evanescence claim.

-/

@[expose] public section

namespace Optics

open Electromagnetism Electromagnetism.ThreeDimension InnerProductSpace MeasureTheory Space Time
open scoped Interval Real

noncomputable section

private lemma realizeJones_plusIQuadrature_norm_sq
    {direction : Space.Direction 3} (frame : PolarizationFrame direction) (phase : ℝ) :
    ‖frame.realizeJones JonesVector.plusIQuadrature phase‖ ^ 2 = 1 / 2 := by
  rw [frame.realizeJones_plusIQuadrature, norm_smul, mul_pow,
    norm_sub_sq_real, norm_smul, norm_smul, inner_smul_left, inner_smul_right]
  rw [orthonormal_iff_ite.mp frame.orthonormal_axis 0 1,
    frame.orthonormal_axis.norm_eq_one 0, frame.orthonormal_axis.norm_eq_one 1]
  simp only [Fin.zero_ne_one, if_false, mul_zero, mul_one, sub_zero, Real.norm_eq_abs,
    sq_abs, JonesVector.unitEqualAmplitude_sq]
  rw [show Real.cos phase ^ 2 + Real.sin phase ^ 2 = 1 by
    exact Real.cos_sq_add_sin_sq phase]
  norm_num

/-!

## A. Constant quadrature-state flux

-/

/-- The positive-`I` quadrature state's instantaneous material-wave Poynting vector equals its
mean-flux vector at every time and point. -/
lemma plusIQuadrature_toMaterialPlaneWave_poyntingVector
    (medium : HomogeneousIsotropicMedium)
    {direction : Space.Direction 3} (frame : PolarizationFrame direction)
    (angularFrequency : ℝ) (hω : 0 < angularFrequency)
    (t : Time) (x : Space) :
    ThreeDimension.poyntingVector
        (MonochromaticPlaneWave.electricField
          (JonesVector.plusIQuadrature.toMaterialPlaneWave medium frame angularFrequency hω))
        (MonochromaticPlaneWave.magneticFieldStrength
          (JonesVector.plusIQuadrature.toMaterialPlaneWave medium frame angularFrequency hω)
          medium)
        t x =
      JonesVector.plusIQuadrature.materialPlaneWaveIrradiance medium •
        frame.propagationVector := by
  rw [JonesVector.toMaterialPlaneWave_poyntingVector,
    JonesVector.toMaterialPlaneWave_electricField,
    realizeJones_plusIQuadrature_norm_sq]
  congr 1
  simp [JonesVector.materialPlaneWaveIrradiance, JonesVector.intensity_eq_sum_normSq,
    JonesVector.plusIQuadrature, JonesVector.ofComponents, Fin.sum_univ_two]
  field_simp [medium.waveImpedance_ne_zero]
  ring

/-!

## B. Instantaneous versus mean linear-state flux

-/

/-- The horizontal material wave has zero instantaneous Poynting vector at one quarter period at
the spatial origin. -/
lemma horizontal_toMaterialPlaneWave_poyntingVector_quarterPeriod_origin
    (medium : HomogeneousIsotropicMedium)
    {direction : Space.Direction 3} (frame : PolarizationFrame direction)
    (angularFrequency : ℝ) (hω : 0 < angularFrequency) :
    ThreeDimension.poyntingVector
        (MonochromaticPlaneWave.electricField
          (JonesVector.horizontal.toMaterialPlaneWave medium frame angularFrequency hω))
        (MonochromaticPlaneWave.magneticFieldStrength
          (JonesVector.horizontal.toMaterialPlaneWave medium frame angularFrequency hω) medium)
        ((Real.pi / (2 * angularFrequency) : ℝ) : Time) (0 : Space) = 0 := by
  rw [JonesVector.toMaterialPlaneWave_poyntingVector]
  have hE :
      MonochromaticPlaneWave.electricField
          (JonesVector.horizontal.toMaterialPlaneWave medium frame angularFrequency hω)
          ((Real.pi / (2 * angularFrequency) : ℝ) : Time) (0 : Space) = 0 := by
    rw [JonesVector.toMaterialPlaneWave_electricField]
    have hphase :
        MonochromaticPlaneWave.carrierPhase
            (JonesVector.horizontal.toMaterialPlaneWave medium frame angularFrequency hω)
            ((Real.pi / (2 * angularFrequency) : ℝ) : Time) (0 : Space) =
          Real.pi / 2 := by
      simp only [MonochromaticPlaneWave.carrierPhase,
        JonesVector.toMaterialPlaneWave_angularFrequency, inner_zero_left]
      field_simp [ne_of_gt hω]
      ring
    rw [hphase, frame.realizeJones_eq_sum, Fin.sum_univ_two]
    simp [JonesVector.horizontal, Phasor.realize_eq_re_cos_sub_im_sin]
  rw [hE]
  simp

/-- The horizontal material wave's one-period mean Poynting vector is nonzero, despite its zero
quarter-period instantaneous sample. -/
lemma horizontal_toMaterialPlaneWave_intervalAverage_poyntingVector_ne_zero
    (medium : HomogeneousIsotropicMedium)
    {direction : Space.Direction 3} (frame : PolarizationFrame direction)
    (angularFrequency : ℝ) (hω : 0 < angularFrequency)
    (startTime : Time) (x : Space) :
    (⨍ time in startTime.val..startTime.val + 2 * Real.pi / angularFrequency,
      ThreeDimension.poyntingVector
        (MonochromaticPlaneWave.electricField
          (JonesVector.horizontal.toMaterialPlaneWave medium frame angularFrequency hω))
        (MonochromaticPlaneWave.magneticFieldStrength
          (JonesVector.horizontal.toMaterialPlaneWave medium frame angularFrequency hω) medium)
        (time : Time) x) ≠ 0 := by
  rw [JonesVector.toMaterialPlaneWave_intervalAverage_poyntingVector]
  apply smul_ne_zero
  · apply ne_of_gt
    rw [JonesVector.materialPlaneWaveIrradiance]
    have hintensity : JonesVector.horizontal.intensity = 1 := by
      simp [JonesVector.intensity_eq_sum_normSq, JonesVector.horizontal,
        JonesVector.ofComponents, Fin.sum_univ_two]
    rw [hintensity]
    exact div_pos zero_lt_one (mul_pos zero_lt_two medium.waveImpedance_pos)
  · intro hzero
    have hnorm := frame.propagationVector_norm
    rw [hzero, norm_zero] at hnorm
    norm_num at hnorm

end

end Optics
