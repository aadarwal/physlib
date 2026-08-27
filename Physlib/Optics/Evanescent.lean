/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Electromagnetism.ThreeDimension.MonochromaticPlaneWave.ComplexMaxwell
public import Physlib.Optics.HarmonicFlux.PositiveNormalDecay

/-!
# Half-space evanescent plane waves

## i. Overview

This file gives the optical term *evanescent* a precise side-relative meaning for Physlib's
complex monochromatic material plane waves in lossless homogeneous isotropic media. Relative to
an oriented affine hyperplane and one of its geometric sides, a half-space evanescent wave has a
nonzero electric amplitude, is bilinearly transverse and dispersion matched, has no tangential
attenuation, and its attenuation points strictly into that side. This is the pure-normal case,
not a classification of general lossy waves or waves with tangential attenuation.

Material dispersion then forces the real phase vector to be tangent to the hyperplane. The
attenuation vector is the positive side-relative decay rate times the side normal, so the carrier
is represented by the existing positive-normal-decay data. This bridge supplies exact carrier,
local electric and magnetic phasor, and ordinary electric and magnetic-induction scaling; decay
of the local electric phasor to zero at increasing side depth; the source-free Maxwell equations;
and zero one-period mean Poynting component along the decay direction.

## ii. Key results

- `IsHalfSpaceEvanescent.attenuationVector_eq_halfSpaceDecayRate_smul_sideNormalVector`:
  attenuation is exactly positive and side normal.
- `IsHalfSpaceEvanescent.phaseVector_isTangent`: material dispersion forces tangent phase.
- `IsHalfSpaceEvanescent.positiveNormalDecayData`: bridge to the neutral decay-data API.
- `IsHalfSpaceEvanescent.carrier_vadd_sideNormalVector`: exact complete-carrier decay.
- `IsHalfSpaceEvanescent.localElectricPhasor_vadd_sideNormalVector`: exact amplitude decay.
- `IsHalfSpaceEvanescent.localMagneticFieldStrengthPhasor_vadd_sideNormalVector`: exact material
  magnetic-phasor decay.
- `IsHalfSpaceEvanescent.tendsto_localElectricPhasor_vadd_sideNormalVector_atTop`: vanishing at
  increasing side depth.
- `IsHalfSpaceEvanescent.isMacroscopicMaxwellSolution`: the fixed-medium source-free solution.
- `IsHalfSpaceEvanescent.inner_sideNormalVector_intervalAverage_poyntingVector_eq_zero`: zero
  actual one-period mean flux along the decay direction.

## iii. Table of contents

- A. Half-space evanescence
- B. Positive-normal-decay representation
- C. Field and flux consequences

## iv. References

The predicate classifies an existing globally defined carrier relative to a selected half-space.
It does not replace the field by zero outside that half-space: the same carrier grows under
displacement in the opposite direction. Unguarded convention statement (review only): it assigns
no transmitted, total-internal-reflection, or outgoing wave role. It asserts no interface boundary
condition, causal condition, pointwise zero normal flux, zero tangential flux, aperture power, or
evanescent positive-power port.

-/

@[expose] public section

namespace Optics

open ClassicalMechanics Electromagnetism Electromagnetism.ThreeDimension InnerProductSpace
  MeasureTheory Space Time
open ClassicalMechanics.ComplexWaveVector
open Electromagnetism.ThreeDimension.ComplexMonochromaticPlaneWave
open scoped Interval Real

noncomputable section

/-!

## A. Half-space evanescence

-/

/-- The exponential amplitude-decay rate measured along the unit normal into a selected
geometric side. Positivity is not built into this numerical definition. -/
def halfSpaceDecayRate (plane : OrientedAffineHyperplane 3)
    (side : OrientedAffineHyperplane.Side) (wave : ComplexMonochromaticPlaneWave) : ℝ :=
  inner ℝ (plane.sideNormalVector side) wave.waveVector.attenuationVector

/-- A nonzero complex material plane wave that is evanescent into one geometric half-space.

The wave is a transverse, dispersion-matched electromagnetic carrier. Its attenuation is purely
normal to the selected hyperplane and has strictly positive component into `side`. The predicate
does not construct a half-space-supported field. Unguarded convention statement (review only): it
does not assert an outgoing condition. -/
structure IsHalfSpaceEvanescent
    (plane : OrientedAffineHyperplane 3) (side : OrientedAffineHyperplane.Side)
    (medium : HomogeneousIsotropicMedium) (wave : ComplexMonochromaticPlaneWave) : Prop where
  /-- The electric amplitude is physically active. -/
  electricAmplitude_ne_zero : wave.electricAmplitude ≠ 0
  /-- The electric amplitude is transverse under the complex-bilinear pairing. -/
  isTransverse : wave.IsTransverse
  /-- The complex wave vector lies on the supplied material shell. -/
  isDispersionMatched : wave.IsDispersionMatched medium
  /-- Attenuation has no component tangent to the reference hyperplane. -/
  tangentialAttenuation_eq_zero :
    plane.tangentialProjection wave.waveVector.attenuationVector = 0
  /-- Attenuation points strictly into the selected geometric side. -/
  isAttenuationDirectedInto : wave.waveVector.IsAttenuationDirectedInto plane side

namespace IsHalfSpaceEvanescent

variable {plane : OrientedAffineHyperplane 3} {side : OrientedAffineHyperplane.Side}
  {medium : HomogeneousIsotropicMedium} {wave : ComplexMonochromaticPlaneWave}

/-- A half-space evanescent wave has a strictly positive side-relative decay rate. -/
lemma halfSpaceDecayRate_pos (h : IsHalfSpaceEvanescent plane side medium wave) :
    0 < halfSpaceDecayRate plane side wave := by
  exact (isAttenuationDirectedInto_iff_inner_sideNormalVector
    wave.waveVector plane side).mp h.isAttenuationDirectedInto

/-- The attenuation vector of a half-space evanescent wave is its positive decay rate times the
unit normal into the selected side. -/
lemma attenuationVector_eq_halfSpaceDecayRate_smul_sideNormalVector
    (h : IsHalfSpaceEvanescent plane side medium wave) :
    wave.waveVector.attenuationVector =
      halfSpaceDecayRate plane side wave • plane.sideNormalVector side := by
  have hNormal : wave.waveVector.attenuationVector =
      plane.normalComponent wave.waveVector.attenuationVector • plane.normalVector := by
    calc
      wave.waveVector.attenuationVector =
          plane.tangentialProjection wave.waveVector.attenuationVector +
            plane.normalComponent wave.waveVector.attenuationVector • plane.normalVector :=
        (plane.tangentialProjection_add_normal wave.waveVector.attenuationVector).symm
      _ = plane.normalComponent wave.waveVector.attenuationVector • plane.normalVector := by
        rw [h.tangentialAttenuation_eq_zero, zero_add]
  rw [hNormal]
  cases side <;>
    simp [halfSpaceDecayRate, OrientedAffineHyperplane.sideNormalVector,
      OrientedAffineHyperplane.normalComponent]

/-- Material dispersion and nonzero purely normal attenuation force the phase vector of a
half-space evanescent wave to be tangent to the reference hyperplane. -/
lemma phaseVector_isTangent (h : IsHalfSpaceEvanescent plane side medium wave) :
    plane.IsTangent wave.waveVector.phaseVector := by
  have hOrthogonal :=
    (isDispersionMatched_iff_phase_attenuation wave medium).mp h.isDispersionMatched |>.1
  rw [h.attenuationVector_eq_halfSpaceDecayRate_smul_sideNormalVector,
    real_inner_smul_right] at hOrthogonal
  have hSide :
      inner ℝ wave.waveVector.phaseVector (plane.sideNormalVector side) = 0 :=
    (mul_eq_zero.mp hOrthogonal).resolve_left h.halfSpaceDecayRate_pos.ne'
  cases side <;>
    simpa [OrientedAffineHyperplane.IsTangent,
      OrientedAffineHyperplane.normalComponent,
      OrientedAffineHyperplane.sideNormalVector, real_inner_comm] using hSide

/-!

## B. Positive-normal-decay representation

-/

/-- The proof-bearing positive-normal-decay data canonically extracted from a half-space
evanescent wave. -/
noncomputable def positiveNormalDecayData
    (h : IsHalfSpaceEvanescent plane side medium wave) :
    PositiveNormalDecayWaveVector (plane.sideNormalDirection side) where
  tangentialWaveVector := wave.waveVector.phaseVector
  tangential := by
    rw [← plane.sideNormalVector_eq_repr]
    exact plane.inner_sideNormalVector_eq_zero_of_isTangent side h.phaseVector_isTangent
  decayRate := halfSpaceDecayRate plane side wave
  decayRate_pos := h.halfSpaceDecayRate_pos

/-- The extracted decay data uses the selected side-normal vector. -/
@[simp]
lemma positiveNormalDecayData_normalVector
    (h : IsHalfSpaceEvanescent plane side medium wave) :
    h.positiveNormalDecayData.normalVector = plane.sideNormalVector side := by
  change Space.basis.repr (plane.sideNormalDirection side).unit = plane.sideNormalVector side
  exact (plane.sideNormalVector_eq_repr side).symm

/-- The extracted data has the side-relative half-space decay rate. -/
@[simp]
lemma positiveNormalDecayData_decayRate
    (h : IsHalfSpaceEvanescent plane side medium wave) :
    h.positiveNormalDecayData.decayRate = halfSpaceDecayRate plane side wave := rfl

/-- The extracted positive-normal-decay data represents the original complex wave vector. -/
lemma waveVector_eq_positiveNormalDecayData
    (h : IsHalfSpaceEvanescent plane side medium wave) :
    wave.waveVector = h.positiveNormalDecayData.waveVector := by
  calc
    wave.waveVector = ofPhaseAttenuation wave.waveVector.phaseVector
        wave.waveVector.attenuationVector :=
      (ofPhaseAttenuation_phaseVector_attenuationVector wave.waveVector).symm
    _ = ofPhaseAttenuation wave.waveVector.phaseVector
        (halfSpaceDecayRate plane side wave • plane.sideNormalVector side) := by
      rw [h.attenuationVector_eq_halfSpaceDecayRate_smul_sideNormalVector]
    _ = h.positiveNormalDecayData.waveVector := by
      rw [PositiveNormalDecayWaveVector.waveVector,
        h.positiveNormalDecayData_normalVector]
      rfl

/-!

## C. Field and flux consequences

-/

/-- A half-space evanescent wave is a source-free macroscopic Maxwell solution in its supplied
homogeneous isotropic medium. -/
lemma isMacroscopicMaxwellSolution
    (h : IsHalfSpaceEvanescent plane side medium wave) :
    medium.IsMacroscopicMaxwellSolution wave.electricField
      (wave.electricDisplacement medium) wave.magneticInduction
      (wave.magneticFieldStrength medium) 0 0 := by
  exact wave.isMacroscopicMaxwellSolution medium h.isTransverse h.isDispersionMatched

/-- The local electric phasor of a half-space evanescent wave never vanishes. -/
lemma localElectricPhasor_ne_zero (h : IsHalfSpaceEvanescent plane side medium wave)
    (x : Space) : wave.localElectricPhasor x ≠ 0 := by
  rw [localElectricPhasor]
  exact smul_ne_zero (ComplexWaveVector.spatialFactor_ne_zero wave.waveVector x)
    h.electricAmplitude_ne_zero

/-- Displacement into the selected side scales the complete complex carrier by the exact real
exponential decay factor. -/
lemma carrier_vadd_sideNormalVector
    (h : IsHalfSpaceEvanescent plane side medium wave)
    (u : ℝ) (time : Time) (x : Space) :
    wave.carrier time (u • plane.sideNormalVector side +ᵥ x) =
      (Real.exp (-halfSpaceDecayRate plane side wave * u) : ℂ) * wave.carrier time x := by
  simpa only [h.positiveNormalDecayData_normalVector,
    h.positiveNormalDecayData_decayRate] using
    wave.carrier_vadd_positiveNormalDecay h.positiveNormalDecayData
      h.waveVector_eq_positiveNormalDecayData u time x

/-- Displacement into the selected side scales the local electric phasor by the exact real
exponential decay factor. -/
lemma localElectricPhasor_vadd_sideNormalVector
    (h : IsHalfSpaceEvanescent plane side medium wave) (u : ℝ) (x : Space) :
    wave.localElectricPhasor (u • plane.sideNormalVector side +ᵥ x) =
      (Real.exp (-halfSpaceDecayRate plane side wave * u) : ℂ) •
        wave.localElectricPhasor x := by
  rw [localElectricPhasor, localElectricPhasor,
    h.waveVector_eq_positiveNormalDecayData,
    ← h.positiveNormalDecayData_normalVector,
    h.positiveNormalDecayData.spatialFactor_vadd]
  simp [smul_smul]

/-- Displacement into the selected side scales the local magnetic-field-strength phasor by the
same exact real exponential decay factor. -/
lemma localMagneticFieldStrengthPhasor_vadd_sideNormalVector
    (h : IsHalfSpaceEvanescent plane side medium wave) (u : ℝ) (x : Space) :
    wave.localMagneticFieldStrengthPhasor medium
        (u • plane.sideNormalVector side +ᵥ x) =
      (Real.exp (-halfSpaceDecayRate plane side wave * u) : ℂ) •
        wave.localMagneticFieldStrengthPhasor medium x := by
  rw [localMagneticFieldStrengthPhasor, localMagneticFieldStrengthPhasor,
    h.waveVector_eq_positiveNormalDecayData,
    ← h.positiveNormalDecayData_normalVector,
    h.positiveNormalDecayData.spatialFactor_vadd]
  rw [h.positiveNormalDecayData_decayRate]
  simp only [smul_smul, mul_assoc]

/-- Displacement into the selected side scales the ordinary real electric field by the same
exact amplitude factor. -/
lemma electricField_vadd_sideNormalVector
    (h : IsHalfSpaceEvanescent plane side medium wave)
    (u : ℝ) (time : Time) (x : Space) :
    wave.electricField time (u • plane.sideNormalVector side +ᵥ x) =
      Real.exp (-halfSpaceDecayRate plane side wave * u) • wave.electricField time x := by
  simpa only [h.positiveNormalDecayData_normalVector,
    h.positiveNormalDecayData_decayRate] using
    wave.electricField_vadd_positiveNormalDecay h.positiveNormalDecayData
      h.waveVector_eq_positiveNormalDecayData u time x

/-- Displacement into the selected side scales the ordinary real magnetic induction by the same
exact amplitude factor. -/
lemma magneticInduction_vadd_sideNormalVector
    (h : IsHalfSpaceEvanescent plane side medium wave)
    (u : ℝ) (time : Time) (x : Space) :
    wave.magneticInduction time (u • plane.sideNormalVector side +ᵥ x) =
      Real.exp (-halfSpaceDecayRate plane side wave * u) •
        wave.magneticInduction time x := by
  simpa only [h.positiveNormalDecayData_normalVector,
    h.positiveNormalDecayData_decayRate] using
    wave.magneticInduction_vadd_positiveNormalDecay h.positiveNormalDecayData
      h.waveVector_eq_positiveNormalDecayData u time x

/-- The local electric phasor tends to zero along increasing depth into the selected side. -/
lemma tendsto_localElectricPhasor_vadd_sideNormalVector_atTop
    (h : IsHalfSpaceEvanescent plane side medium wave) (x : Space) :
    Filter.Tendsto
      (fun u : ℝ ↦ wave.localElectricPhasor (u • plane.sideNormalVector side +ᵥ x))
      Filter.atTop (nhds 0) := by
  have hTendsto :=
    (h.positiveNormalDecayData.tendsto_spatialFactor_vadd_atTop x).smul_const
      wave.electricAmplitude
  rw [← h.waveVector_eq_positiveNormalDecayData,
    h.positiveNormalDecayData_normalVector] at hTendsto
  simpa only [localElectricPhasor, zero_smul] using hTendsto

/-- A half-space evanescent wave has zero actual one-period mean Poynting component along its
side-relative decay direction at every point and every period start. -/
lemma inner_sideNormalVector_intervalAverage_poyntingVector_eq_zero
    (h : IsHalfSpaceEvanescent plane side medium wave) (startTime : Time) (x : Space) :
    inner ℝ (plane.sideNormalVector side)
      (⨍ time in startTime.val..startTime.val + 2 * Real.pi / wave.angularFrequency,
        poyntingVector wave.electricField (wave.magneticFieldStrength medium)
          (time : Time) x) = 0 := by
  have hZero :=
    wave.inner_normalVector_intervalAverage_poyntingVector_eq_zero_of_positiveNormalDecay
      medium h.positiveNormalDecayData h.waveVector_eq_positiveNormalDecayData h.isTransverse
      startTime x
  rw [h.positiveNormalDecayData_normalVector] at hZero
  exact hZero

end IsHalfSpaceEvanescent

end

end Optics
