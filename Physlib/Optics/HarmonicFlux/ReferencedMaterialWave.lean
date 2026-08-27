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
- `IsReferencedMaterialJonesWave.electricField_planePoint` and
  `IsReferencedMaterialJonesWave.magneticFieldStrength_planePoint`: the instantaneous actual
  fields in framed Jones form at the reference point.
- `IsReferencedMaterialJonesWave.normalComponent_intervalAverage_poyntingVector_planePoint`:
  its signed stored-normal component.
- `IsZeroOrReferencedMaterialJonesWave.intervalAverage_poyntingVector_planePoint`: the guarded
  vector identity, including a zero field with arbitrary carrier data.
- `IsZeroOrReferencedMaterialJonesWave.normalComponent_intervalAverage_poyntingVector_planePoint`:
  the corresponding guarded normal-flux identity.
- `normalComponent_intervalAverage_poyntingVector_planePoint_eq_ownPeriod` for the guarded
  connector:
  guarded replacement of an external period by the carrier's own period.

## iii. Table of contents

- A. Connected local phasors
- B. Connected actual fields
- C. Connected mean flux
- D. Guarded actual fields and mean flux

## iv. References

These are local flux-density identities at the stored plane point. Unguarded convention statement
(review only): they assign no interface role to either side. They do not state an aperture integral
or a Fresnel power balance.

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

## B. Connected actual fields

-/

/-- At the plane point, the actual electric field is the framed Jones realization at the wave's
instantaneous carrier phase. -/
lemma electricField_planePoint
    (h : IsReferencedMaterialJonesWave plane medium wave frame J) (time : Time) :
    wave.electricField time plane.point =
      frame.realizeJones J (wave.angularFrequency * (time : ℝ)) := by
  rw [wave.electricField_eq_realize_localElectricPhasor (time : ℝ) plane.point,
    h.localElectricPhasor_planePoint]
  rfl

/-- At the plane point, the actual magnetic field strength is inverse impedance times the framed
realization of the propagation-quarter-turn Jones data. -/
lemma magneticFieldStrength_planePoint
    (h : IsReferencedMaterialJonesWave plane medium wave frame J) (time : Time) :
    wave.magneticFieldStrength medium time plane.point =
      medium.waveImpedance⁻¹ •
        frame.realizeJones J.propagationCross (wave.angularFrequency * (time : ℝ)) := by
  rw [wave.magneticFieldStrength_eq_realize_localMagneticFieldStrengthPhasor
    medium (time : ℝ) plane.point, h.localMagneticFieldStrengthPhasor_planePoint]
  exact Phasor.realizeEuclidean_ofReal_smul medium.waveImpedance⁻¹
    (frame.embedJones J.propagationCross) (wave.angularFrequency * (time : ℝ))

/-!

## C. Connected mean flux

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

## D. Guarded actual fields and mean flux

-/

/-- The guarded connector gives the same framed Jones electric-field realization at the plane
point. Its zero-field branch vanishes for arbitrary dummy carrier data. -/
lemma electricField_planePoint
    (h : IsZeroOrReferencedMaterialJonesWave plane medium wave frame J) (time : Time) :
    wave.electricField time plane.point =
      frame.realizeJones J (wave.angularFrequency * (time : ℝ)) := by
  rcases h with ⟨hElectric, hJones⟩ | hMaterial
  · have hLeft : wave.electricField time plane.point = 0 := by
      ext i
      simp [hElectric]
    have hRight : frame.realizeJones J (wave.angularFrequency * (time : ℝ)) = 0 := by
      rw [frame.realizeJones_eq_sum, Fin.sum_univ_two]
      simp [hJones, Phasor.realize]
    rw [hLeft, hRight]
  · exact hMaterial.electricField_planePoint time

/-- The guarded connector gives the same framed Jones magnetic-field-strength realization at the
plane point. Its zero-field branch vanishes for arbitrary dummy carrier data. -/
lemma magneticFieldStrength_planePoint
    (h : IsZeroOrReferencedMaterialJonesWave plane medium wave frame J) (time : Time) :
    wave.magneticFieldStrength medium time plane.point =
      medium.waveImpedance⁻¹ •
        frame.realizeJones J.propagationCross (wave.angularFrequency * (time : ℝ)) := by
  rcases h with ⟨hElectric, hJones⟩ | hMaterial
  · have hLocal : wave.localMagneticFieldStrengthPhasor medium plane.point = 0 := by
      simp [ComplexMonochromaticPlaneWave.localMagneticFieldStrengthPhasor,
        ComplexMonochromaticPlaneWave.magneticAmplitude, hElectric,
        ComplexMonochromaticPlaneWave.complexCross]
    have hLeft : wave.magneticFieldStrength medium time plane.point = 0 := by
      rw [wave.magneticFieldStrength_eq_realize_localMagneticFieldStrengthPhasor
        medium (time : ℝ) plane.point, hLocal]
      ext i
      simp [Phasor.realizeEuclidean, Phasor.realize]
    have hRight : medium.waveImpedance⁻¹ •
        frame.realizeJones J.propagationCross (wave.angularFrequency * (time : ℝ)) = 0 := by
      rw [frame.realizeJones_eq_sum, Fin.sum_univ_two]
      simp [hJones, Phasor.realize]
    rw [hLeft, hRight]
  · exact hMaterial.magneticFieldStrength_planePoint time

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

/-- A guarded referenced wave's normal mean flux over an externally supplied carrier period
equals its own-period normal mean flux whenever the wave is electrically zero or its frequency
matches the supplied frequency.

The zero-field branch places no positivity or equality condition on the external frequency. -/
lemma normalComponent_intervalAverage_poyntingVector_planePoint_eq_ownPeriod
    (h : IsZeroOrReferencedMaterialJonesWave plane medium wave frame J)
    (referenceAngularFrequency : ℝ)
    (hFrequency : wave.electricAmplitude = 0 ∨
      wave.angularFrequency = referenceAngularFrequency)
    (startTime : Time) :
    plane.normalComponent
        (⨍ time in startTime.val..startTime.val + 2 * Real.pi / referenceAngularFrequency,
          ThreeDimension.poyntingVector wave.electricField (wave.magneticFieldStrength medium)
            (time : Time) plane.point) =
      plane.normalComponent
        (⨍ time in startTime.val..startTime.val + 2 * Real.pi / wave.angularFrequency,
          ThreeDimension.poyntingVector wave.electricField (wave.magneticFieldStrength medium)
            (time : Time) plane.point) := by
  rcases hFrequency with hZero | hFrequency
  · have hElectricField : ∀ time : Time, wave.electricField time plane.point = 0 := by
      intro time
      ext i
      simp [hZero]
    have hJones := h.components_eq_zero_of_electricAmplitude_eq_zero hZero
    rw [h.normalComponent_intervalAverage_poyntingVector_planePoint]
    simp [ThreeDimension.poyntingVector, hElectricField,
      OrientedAffineHyperplane.normalComponent, JonesVector.materialPlaneWaveIrradiance,
      JonesVector.intensity, hJones]
  · rw [hFrequency]

end IsZeroOrReferencedMaterialJonesWave

end

end Optics
