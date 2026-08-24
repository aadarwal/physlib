/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.HarmonicFlux.ComplexMaterialWave
public import Physlib.Optics.HarmonicFlux.MaterialWave
public import Physlib.Optics.Polarization.ReferencedMaterialWave

/-!
# Harmonic flux of plane-referenced material Jones waves

## i. Overview

This file gives the plane-referenced Jones connector its local electromagnetic observable. At the
oriented plane's stored point, a connected complex carrier has the framed Jones electric phasor
and the corresponding inverse-impedance magnetic-field-strength phasor. Its actual one-period
mean Poynting vector is therefore the Jones irradiance in the framed propagation direction.

The guarded connector retains the same result. In its zero-field branch the Jones data vanishes,
so both sides are zero even though the dummy carrier and propagation frame remain unrestricted.

## ii. Key results

- `IsReferencedMaterialJonesWave.intervalAverage_poyntingVector_planePoint`: the actual mean
  Poynting vector of connected carrier data at the reference point.
- `IsReferencedMaterialJonesWave.normalComponent_intervalAverage_poyntingVector_planePoint`:
  its signed stored-normal component.
- `IsZeroOrReferencedMaterialJonesWave.intervalAverage_poyntingVector_planePoint`: the guarded
  vector identity, including a zero field with arbitrary carrier data.
- `IsZeroOrReferencedMaterialJonesWave.normalComponent_intervalAverage_poyntingVector_planePoint`:
  the corresponding guarded normal-flux identity.

## iii. Table of contents

- A. Connected local phasors
- B. Connected mean flux
- C. Guarded mean flux

## iv. Scope

These are local flux-density identities at the stored plane point. They do not state an aperture
integral, assign an interface role to either side, or state a Fresnel power balance.
-/

@[expose] public section

namespace Optics

open ClassicalMechanics Electromagnetism Electromagnetism.ThreeDimension Space Time
open scoped Interval

noncomputable section

namespace IsReferencedMaterialJonesWave

variable {plane : OrientedAffineHyperplane 3} {medium : HomogeneousIsotropicMedium}
  {wave : ComplexMonochromaticPlaneWave} {direction : Space.Direction 3}
  {frame : PolarizationFrame direction} {J : JonesVector}

/-!

## A. Connected local phasors

-/

/-- At the plane's stored point, the local electric phasor is the framed referenced Jones
amplitude. -/
lemma localElectricPhasor_planePoint
    (h : IsReferencedMaterialJonesWave plane medium wave frame J) :
    wave.localElectricPhasor plane.point = frame.embedJones J := by
  simpa [ComplexMonochromaticPlaneWave.localElectricPhasor] using
    h.referencedElectricAmplitude_eq

/-- At the plane's stored point, the local magnetic-field-strength phasor is inverse impedance
times the propagation-quarter-turn Jones amplitude. -/
lemma localMagneticFieldStrengthPhasor_planePoint
    (h : IsReferencedMaterialJonesWave plane medium wave frame J) :
    wave.localMagneticFieldStrengthPhasor medium plane.point =
      (((medium.waveImpedance⁻¹ : ℝ) : ℂ) • frame.embedJones J.propagationCross) := by
  have hCoefficient : medium.μ⁻¹ * medium.waveSpeed⁻¹ = medium.waveImpedance⁻¹ := by
    rw [← mul_inv, medium.μ_mul_waveSpeed]
  rw [ComplexMonochromaticPlaneWave.localMagneticFieldStrengthPhasor]
  calc
    _ = (((medium.μ⁻¹ : ℝ) : ℂ) •
        (wave.waveVector.spatialFactor plane.point • wave.magneticAmplitude)) := by module
    _ = (((medium.μ⁻¹ : ℝ) : ℂ) •
        (((medium.waveSpeed⁻¹ : ℝ) : ℂ) • frame.embedJones J.propagationCross)) := by
      rw [h.referencedMagneticAmplitude]
    _ = _ := by
      rw [smul_smul]
      congr 1
      exact_mod_cast hCoefficient

/-!

## B. Connected mean flux

-/

/-- A referenced propagating material carrier's actual one-period mean Poynting vector at the
plane point is its Jones irradiance in the framed propagation direction. -/
lemma intervalAverage_poyntingVector_planePoint
    (h : IsReferencedMaterialJonesWave plane medium wave frame J)
    (startTime : Time) :
    (⨍ time in startTime.val..startTime.val + 2 * Real.pi / wave.angularFrequency,
      ThreeDimension.poyntingVector wave.electricField (wave.magneticFieldStrength medium)
        (time : Time) plane.point) =
      J.materialPlaneWaveIrradiance medium • frame.propagationVector := by
  rw [wave.intervalAverage_poyntingVector_eq_localPhasors,
    h.localElectricPhasor_planePoint, h.localMagneticFieldStrengthPhasor_planePoint]
  exact frame.timeAveragedPoyntingVector_embedJones_propagationCross J medium

/-- The stored-normal component of a referenced carrier's actual one-period mean Poynting vector
at the plane point is its Jones irradiance times the signed propagation normal. -/
lemma normalComponent_intervalAverage_poyntingVector_planePoint
    (h : IsReferencedMaterialJonesWave plane medium wave frame J)
    (startTime : Time) :
    plane.normalComponent
        (⨍ time in startTime.val..startTime.val + 2 * Real.pi / wave.angularFrequency,
          ThreeDimension.poyntingVector wave.electricField (wave.magneticFieldStrength medium)
            (time : Time) plane.point) =
      J.materialPlaneWaveIrradiance medium *
        plane.normalComponent frame.propagationVector := by
  rw [h.intervalAverage_poyntingVector_planePoint]
  simp [OrientedAffineHyperplane.normalComponent, inner_smul_right]

end IsReferencedMaterialJonesWave

namespace IsZeroOrReferencedMaterialJonesWave

variable {plane : OrientedAffineHyperplane 3} {medium : HomogeneousIsotropicMedium}
  {wave : ComplexMonochromaticPlaneWave} {direction : Space.Direction 3}
  {frame : PolarizationFrame direction} {J : JonesVector}

/-!

## C. Guarded mean flux

-/

/-- The guarded referenced connector gives the same actual one-period mean Poynting vector at the
plane point. Its zero-field branch vanishes independently of the dummy carrier data. -/
lemma intervalAverage_poyntingVector_planePoint
    (h : IsZeroOrReferencedMaterialJonesWave plane medium wave frame J)
    (startTime : Time) :
    (⨍ time in startTime.val..startTime.val + 2 * Real.pi / wave.angularFrequency,
      ThreeDimension.poyntingVector wave.electricField (wave.magneticFieldStrength medium)
        (time : Time) plane.point) =
      J.materialPlaneWaveIrradiance medium • frame.propagationVector := by
  rcases h with ⟨hElectric, hJones⟩ | hMaterial
  · rw [wave.intervalAverage_poyntingVector_eq_localPhasors]
    have hLocalElectric : wave.localElectricPhasor plane.point = 0 := by
      simp [ComplexMonochromaticPlaneWave.localElectricPhasor, hElectric]
    rw [hLocalElectric]
    simp [JonesVector.materialPlaneWaveIrradiance, JonesVector.intensity, hJones]
  · exact hMaterial.intervalAverage_poyntingVector_planePoint startTime

/-- The stored-normal component of a guarded referenced carrier's actual mean Poynting vector at
the plane point is its Jones irradiance times the signed propagation normal. -/
lemma normalComponent_intervalAverage_poyntingVector_planePoint
    (h : IsZeroOrReferencedMaterialJonesWave plane medium wave frame J)
    (startTime : Time) :
    plane.normalComponent
        (⨍ time in startTime.val..startTime.val + 2 * Real.pi / wave.angularFrequency,
          ThreeDimension.poyntingVector wave.electricField (wave.magneticFieldStrength medium)
            (time : Time) plane.point) =
      J.materialPlaneWaveIrradiance medium *
        plane.normalComponent frame.propagationVector := by
  rw [h.intervalAverage_poyntingVector_planePoint]
  simp [OrientedAffineHyperplane.normalComponent, inner_smul_right]

end IsZeroOrReferencedMaterialJonesWave

end

end Optics
