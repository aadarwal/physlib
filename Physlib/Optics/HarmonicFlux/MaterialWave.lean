/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.HarmonicFlux.Basic
public import Physlib.Optics.Polarization.MaterialWave

/-!
# Harmonic flux of framed material plane waves

## i. Overview

This file gives raw Jones electric-amplitude data its electromagnetic irradiance interpretation
for the propagating material plane waves constructed by `JonesVector.toMaterialPlaneWave`. With
the peak-phasor convention of `Phasor.realize`, the time-averaged Poynting vector is

`JonesVector.intensity / (2 * medium.waveImpedance)`

times the framed propagation unit vector. The proof first derives this result for the local
electric and magnetic-field-strength phasors. It then retains the complete spatial carrier phase
at an arbitrary point and applies the ordinary-real one-period averaging bridge.

The scalar coefficient is nonnegative, and its equality with the norm of the actual averaged
Poynting vector formally identifies it as material plane-wave irradiance.

## ii. Key results

- `JonesVector.materialPlaneWaveIrradiance`: the impedance-normalized irradiance.
- `PolarizationFrame.timeAveragedPoyntingVector_embedJones_propagationCross`: the local-phasor
  mean-flux identity.
- `JonesVector.toMaterialPlaneWave_poyntingVector`: the exact instantaneous flux identity.
- `JonesVector.toMaterialPlaneWave_intervalAverage_poyntingVector`: the actual-field identity at
  arbitrary space and time origin.
- `JonesVector.norm_toMaterialPlaneWave_intervalAverage_poyntingVector`: irradiance is the norm of
  that mean-flux vector.

## iii. Table of contents

- A. Material plane-wave irradiance
- B. Framed local-phasor flux
- C. Actual material-wave flux
- D. Irradiance as flux magnitude

## iv. References

The medium is the repository's linear, homogeneous, isotropic, nonconducting, nondispersive model,
and the plane wave uses its positive propagation branch. Irradiance here is local flux density for
an infinite monochromatic plane wave, not aperture-integrated or modal power. This file introduces
no interface-normal projection, lossy material, evanescent wave, Fresnel coefficient, or
finite-beam claim. Unguarded convention statement (review only): it assigns no incident or
outgoing wave role.

-/

@[expose] public section

namespace Optics

open ClassicalMechanics Electromagnetism Electromagnetism.ThreeDimension InnerProductSpace Matrix
  MeasureTheory Space Time
open scoped Interval Real

noncomputable section

namespace JonesVector

/-!

## A. Material plane-wave irradiance

-/

/-- The irradiance of a propagating material plane wave whose Jones data stores peak electric
phasor amplitudes.

This is a local flux density. It is not aperture-integrated or normalized modal power. -/
def materialPlaneWaveIrradiance (J : JonesVector)
    (medium : HomogeneousIsotropicMedium) : ℝ :=
  J.intensity / (2 * medium.waveImpedance)

/-- Material plane-wave irradiance is one half the inverse wave impedance times the squared Jones
electric amplitude. -/
lemma materialPlaneWaveIrradiance_eq_half_inv_impedance_mul_intensity
    (J : JonesVector) (medium : HomogeneousIsotropicMedium) :
    J.materialPlaneWaveIrradiance medium =
      (1 / 2 : ℝ) * medium.waveImpedance⁻¹ * J.intensity := by
  rw [materialPlaneWaveIrradiance]
  field_simp [medium.waveImpedance_ne_zero]

/-- Material plane-wave irradiance is nonnegative, including for the zero Jones vector. -/
lemma materialPlaneWaveIrradiance_nonneg (J : JonesVector)
    (medium : HomogeneousIsotropicMedium) :
    0 ≤ J.materialPlaneWaveIrradiance medium := by
  exact div_nonneg J.intensity_nonneg
    (mul_nonneg zero_le_two medium.waveImpedance_pos.le)

end JonesVector

/-!

## B. Framed local-phasor flux

-/

private lemma realPart_ofReal_smul {d : ℕ} (r : ℝ)
    (v : EuclideanSpace ℂ (Fin d)) :
    ComplexWaveVector.realPart ((r : ℂ) • v) =
      r • ComplexWaveVector.realPart v := by
  ext i
  simp [Complex.mul_re]

private lemma imaginaryPart_ofReal_smul {d : ℕ} (r : ℝ)
    (v : EuclideanSpace ℂ (Fin d)) :
    ComplexWaveVector.imaginaryPart ((r : ℂ) • v) =
      r • ComplexWaveVector.imaginaryPart v := by
  ext i
  simp [Complex.mul_im]

namespace PolarizationFrame

variable {direction : Space.Direction 3}

/-- Local Jones electric and material magnetic-field-strength phasors have mean Poynting vector
equal to material irradiance times the framed propagation vector. -/
lemma timeAveragedPoyntingVector_embedJones_propagationCross
    (frame : PolarizationFrame direction) (J : JonesVector)
    (medium : HomogeneousIsotropicMedium) :
    timeAveragedPoyntingVector
        (frame.embedJones J)
        (((medium.waveImpedance⁻¹ : ℝ) : ℂ) •
          frame.embedJones J.propagationCross) =
      J.materialPlaneWaveIrradiance medium • frame.propagationVector := by
  rw [timeAveragedPoyntingVector_eq_quadrature_cross,
    realPart_ofReal_smul, imaginaryPart_ofReal_smul]
  change (1 / 2 : ℝ) •
      (frame.electricReal J ⨯ₑ₃
          (medium.waveImpedance⁻¹ • frame.electricReal J.propagationCross) +
        frame.electricImag J ⨯ₑ₃
          (medium.waveImpedance⁻¹ • frame.electricImag J.propagationCross)) = _
  rw [frame.electricReal_propagationCross, frame.electricImag_propagationCross,
    Space.cross_smul, Space.cross_smul,
    Space.cross_cross_eq_smul_sub_smul', Space.cross_cross_eq_smul_sub_smul',
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    frame.inner_propagationVector_electricReal,
    frame.inner_propagationVector_electricImag]
  simp only [zero_smul, sub_zero]
  rw [smul_smul, smul_smul, ← add_smul, ← mul_add,
    frame.electricReal_norm_sq_add_electricImag_norm_sq, smul_smul]
  rw [JonesVector.materialPlaneWaveIrradiance]
  congr 1
  field_simp [medium.waveImpedance_ne_zero]

end PolarizationFrame

/-!

## C. Actual material-wave flux

-/

namespace JonesVector

/-- The instantaneous Poynting vector of a framed material plane wave points along propagation,
with magnitude equal to inverse impedance times the squared instantaneous electric-field norm. -/
lemma toMaterialPlaneWave_poyntingVector
    (J : JonesVector) (medium : HomogeneousIsotropicMedium)
    {direction : Space.Direction 3} (frame : PolarizationFrame direction)
    (angularFrequency : ℝ) (hω : 0 < angularFrequency)
    (t : Time) (x : Space) :
    ThreeDimension.poyntingVector
        (J.toMaterialPlaneWave medium frame angularFrequency hω).electricField
        ((J.toMaterialPlaneWave medium frame angularFrequency hω).magneticFieldStrength
          medium)
        t x =
      (medium.waveImpedance⁻¹ *
        ‖(J.toMaterialPlaneWave medium frame angularFrequency hω).electricField t x‖ ^ 2) •
        frame.propagationVector := by
  rw [ThreeDimension.poyntingVector,
    J.toMaterialPlaneWave_electricField medium frame angularFrequency hω,
    J.toMaterialPlaneWave_magneticFieldStrength medium frame angularFrequency hω,
    Space.cross_smul, frame.realizeJones_propagationCross,
    Space.cross_cross_eq_smul_sub_smul', real_inner_self_eq_norm_sq,
    frame.inner_propagationVector_realizeJones]
  simp only [zero_smul, sub_zero, smul_smul]

/-- The spatial part of the material plane wave's carrier phase at a selected point. -/
private def materialPlaneWaveSpatialPhaseOffset
    (J : JonesVector) (medium : HomogeneousIsotropicMedium)
    {direction : Space.Direction 3} (frame : PolarizationFrame direction)
    (angularFrequency : ℝ) (hω : 0 < angularFrequency) (x : Space) : ℝ :=
  -((J.toMaterialPlaneWave medium frame angularFrequency hω).waveNumber *
    ⟪x, (J.toMaterialPlaneWave medium frame angularFrequency hω).direction.unit⟫_ℝ)

/-- Jones data rephased to be the local electric phasor at the selected spatial point. -/
private def localMaterialPlaneWaveJones
    (J : JonesVector) (medium : HomogeneousIsotropicMedium)
    {direction : Space.Direction 3} (frame : PolarizationFrame direction)
    (angularFrequency : ℝ) (hω : 0 < angularFrequency) (x : Space) : JonesVector :=
  J.phaseShift
    (J.materialPlaneWaveSpatialPhaseOffset medium frame angularFrequency hω x)

private lemma toMaterialPlaneWave_carrierPhase_eq_time_add_spatialPhase
    (J : JonesVector) (medium : HomogeneousIsotropicMedium)
    {direction : Space.Direction 3} (frame : PolarizationFrame direction)
    (angularFrequency : ℝ) (hω : 0 < angularFrequency)
    (time : ℝ) (x : Space) :
    (J.toMaterialPlaneWave medium frame angularFrequency hω).carrierPhase
        (time : Time) x =
      angularFrequency * time +
        J.materialPlaneWaveSpatialPhaseOffset medium frame angularFrequency hω x := by
  change angularFrequency * time -
      (J.toMaterialPlaneWave medium frame angularFrequency hω).waveNumber *
        ⟪x, (J.toMaterialPlaneWave medium frame angularFrequency hω).direction.unit⟫_ℝ = _
  simp only [materialPlaneWaveSpatialPhaseOffset]
  ring

private lemma toMaterialPlaneWave_electricField_eq_realize_localJones
    (J : JonesVector) (medium : HomogeneousIsotropicMedium)
    {direction : Space.Direction 3} (frame : PolarizationFrame direction)
    (angularFrequency : ℝ) (hω : 0 < angularFrequency)
    (time : ℝ) (x : Space) :
    (J.toMaterialPlaneWave medium frame angularFrequency hω).electricField
        (time : Time) x =
      Phasor.realizeEuclidean
        (frame.embedJones
          (J.localMaterialPlaneWaveJones medium frame angularFrequency hω x))
        (angularFrequency * time) := by
  calc
    _ = frame.realizeJones J
        ((J.toMaterialPlaneWave medium frame angularFrequency hω).carrierPhase
          (time : Time) x) :=
      J.toMaterialPlaneWave_electricField medium frame angularFrequency hω (time : Time) x
    _ = frame.realizeJones J
        (angularFrequency * time +
          J.materialPlaneWaveSpatialPhaseOffset medium frame angularFrequency hω x) := by
      rw [J.toMaterialPlaneWave_carrierPhase_eq_time_add_spatialPhase]
    _ = frame.realizeJones
        (J.localMaterialPlaneWaveJones medium frame angularFrequency hω x)
        (angularFrequency * time) := by
      simpa only [localMaterialPlaneWaveJones] using
        (frame.realizeJones_phaseShift J
          (J.materialPlaneWaveSpatialPhaseOffset medium frame angularFrequency hω x)
          (angularFrequency * time)).symm
    _ = _ := rfl

private lemma toMaterialPlaneWave_magneticFieldStrength_eq_realize_localJones
    (J : JonesVector) (medium : HomogeneousIsotropicMedium)
    {direction : Space.Direction 3} (frame : PolarizationFrame direction)
    (angularFrequency : ℝ) (hω : 0 < angularFrequency)
    (time : ℝ) (x : Space) :
    (J.toMaterialPlaneWave medium frame angularFrequency hω).magneticFieldStrength medium
        (time : Time) x =
      Phasor.realizeEuclidean
        (((medium.waveImpedance⁻¹ : ℝ) : ℂ) •
          frame.embedJones
            (J.localMaterialPlaneWaveJones medium frame angularFrequency hω x).propagationCross)
        (angularFrequency * time) := by
  calc
    _ = medium.waveImpedance⁻¹ •
        frame.realizeJones J.propagationCross
          ((J.toMaterialPlaneWave medium frame angularFrequency hω).carrierPhase
            (time : Time) x) :=
      J.toMaterialPlaneWave_magneticFieldStrength medium frame angularFrequency hω
        (time : Time) x
    _ = medium.waveImpedance⁻¹ •
        frame.realizeJones J.propagationCross
          (angularFrequency * time +
            J.materialPlaneWaveSpatialPhaseOffset medium frame angularFrequency hω x) := by
      rw [J.toMaterialPlaneWave_carrierPhase_eq_time_add_spatialPhase]
    _ = medium.waveImpedance⁻¹ •
        frame.realizeJones
          (J.localMaterialPlaneWaveJones medium frame angularFrequency hω x).propagationCross
          (angularFrequency * time) := by
      congr 1
      simpa only [localMaterialPlaneWaveJones, JonesVector.propagationCross_phaseShift] using
        (frame.realizeJones_phaseShift J.propagationCross
          (J.materialPlaneWaveSpatialPhaseOffset medium frame angularFrequency hω x)
          (angularFrequency * time)).symm
    _ = _ := by
      rw [Phasor.realizeEuclidean_ofReal_smul]
      rfl

/-- At every point and arbitrary period origin, the one-period average of the actual material
plane wave's instantaneous Poynting vector equals its irradiance times its propagation vector.

The proof uses local phasors containing the complete spatial carrier phase at the selected point.
-/
lemma toMaterialPlaneWave_intervalAverage_poyntingVector
    (J : JonesVector) (medium : HomogeneousIsotropicMedium)
    {direction : Space.Direction 3} (frame : PolarizationFrame direction)
    (angularFrequency : ℝ) (hω : 0 < angularFrequency)
    (startTime : Time) (x : Space) :
    (⨍ time in startTime.val..startTime.val + 2 * Real.pi / angularFrequency,
      ThreeDimension.poyntingVector
        (J.toMaterialPlaneWave medium frame angularFrequency hω).electricField
        ((J.toMaterialPlaneWave medium frame angularFrequency hω).magneticFieldStrength
          medium)
        (time : Time) x) =
      J.materialPlaneWaveIrradiance medium • frame.propagationVector := by
  let localJ := J.localMaterialPlaneWaveJones medium frame angularFrequency hω x
  calc
    _ = timeAveragedPoyntingVector
        (frame.embedJones localJ)
        (((medium.waveImpedance⁻¹ : ℝ) : ℂ) •
          frame.embedJones localJ.propagationCross) := by
      apply intervalAverage_poyntingVector_eq_timeAveragedPoyntingVector
        (E := (J.toMaterialPlaneWave medium frame angularFrequency hω).electricField)
        (H := (J.toMaterialPlaneWave medium frame angularFrequency hω).magneticFieldStrength
          medium)
        (frame.embedJones localJ)
        (((medium.waveImpedance⁻¹ : ℝ) : ℂ) •
          frame.embedJones localJ.propagationCross)
        angularFrequency hω startTime x
      · intro time
        simpa only [localJ] using
          J.toMaterialPlaneWave_electricField_eq_realize_localJones medium frame
            angularFrequency hω time x
      · intro time
        simpa only [localJ] using
          J.toMaterialPlaneWave_magneticFieldStrength_eq_realize_localJones medium frame
            angularFrequency hω time x
    _ = localJ.materialPlaneWaveIrradiance medium •
        frame.propagationVector :=
      frame.timeAveragedPoyntingVector_embedJones_propagationCross localJ medium
    _ = J.materialPlaneWaveIrradiance medium •
        frame.propagationVector := by
      simp [materialPlaneWaveIrradiance, localJ, localMaterialPlaneWaveJones]

/-!

## D. Irradiance as flux magnitude

-/

/-- Material plane-wave irradiance is the norm of the actual one-period-averaged Poynting vector.
-/
lemma norm_toMaterialPlaneWave_intervalAverage_poyntingVector
    (J : JonesVector) (medium : HomogeneousIsotropicMedium)
    {direction : Space.Direction 3} (frame : PolarizationFrame direction)
    (angularFrequency : ℝ) (hω : 0 < angularFrequency)
    (startTime : Time) (x : Space) :
    ‖(⨍ time in startTime.val..startTime.val + 2 * Real.pi / angularFrequency,
      ThreeDimension.poyntingVector
        (J.toMaterialPlaneWave medium frame angularFrequency hω).electricField
        ((J.toMaterialPlaneWave medium frame angularFrequency hω).magneticFieldStrength
          medium)
        (time : Time) x)‖ =
      J.materialPlaneWaveIrradiance medium := by
  rw [J.toMaterialPlaneWave_intervalAverage_poyntingVector]
  rw [norm_smul, frame.propagationVector_norm, mul_one, Real.norm_eq_abs,
    abs_of_nonneg (J.materialPlaneWaveIrradiance_nonneg medium)]

end JonesVector

end

end Optics
