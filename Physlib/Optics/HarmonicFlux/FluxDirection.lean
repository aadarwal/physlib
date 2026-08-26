/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.HarmonicFlux.ReferencedMaterialWave

/-!
# Positive mean-flux direction of propagating material waves

## i. Overview

This file gives a local, observable direction predicate for a harmonic carrier: its actual
time-averaged Poynting vector at a reference plane has strictly positive component into a selected
geometric side. For a nonzero-flux referenced material Jones wave, this direction is equivalent
to the already proved strict phase direction.

The equivalence uses the positive-medium result that the mean Poynting vector is the Jones
irradiance times the real propagation vector. Strictly positive irradiance is explicit, so zero
fields and grazing carriers are not silently assigned a direction.

## ii. Key results

- `ComplexMonochromaticPlaneWave.HasPositiveMeanNormalFluxInto`: strict local mean-flux direction.
- `ComplexMonochromaticPlaneWave.hasPositiveMeanNormalFluxInto_iff_intervalAverage`: connection
  to the actual one-period Poynting-vector average.
- `IsReferencedMaterialJonesWave.hasPositiveMeanNormalFluxInto_iff_isPhaseDirectedInto`: flux and
  phase directions agree for a nonzero-flux referenced propagating material Jones wave.

## iii. Table of contents

- A. Positive local mean flux
- B. Referenced material Jones waves

## iv. References

This is a Physlib-original connector between existing field observables and propagation geometry.
It is not a Sommerfeld radiation condition, limiting-absorption theorem, group-velocity or
causality statement, source-selection principle, or evanescent-wave direction convention.
-/

@[expose] public section

namespace Electromagnetism
namespace ThreeDimension

open ClassicalMechanics Optics Space Time
open scoped Interval Real

noncomputable section

namespace ComplexMonochromaticPlaneWave

/-!
## A. Positive local mean flux
-/

/-- The local time-averaged Poynting vector at the plane point has strictly positive component
into a selected geometric side.

The magnetic phasor is magnetic field strength `H`. The strict inequality intentionally excludes
zero-flux and grazing waves. -/
def HasPositiveMeanNormalFluxInto (wave : ComplexMonochromaticPlaneWave)
    (medium : HomogeneousIsotropicMedium) (plane : OrientedAffineHyperplane 3)
    (side : OrientedAffineHyperplane.Side) : Prop :=
  0 < inner ℝ (plane.sideNormalVector side)
    (timeAveragedPoyntingVector (wave.localElectricPhasor plane.point)
      (wave.localMagneticFieldStrengthPhasor medium plane.point))

/-- Positive mean-flux direction in the phasor formula is exactly positivity of the corresponding
actual one-period Poynting-vector average. -/
lemma hasPositiveMeanNormalFluxInto_iff_intervalAverage
    (wave : ComplexMonochromaticPlaneWave) (medium : HomogeneousIsotropicMedium)
    (plane : OrientedAffineHyperplane 3) (side : OrientedAffineHyperplane.Side)
    (startTime : Time) :
    wave.HasPositiveMeanNormalFluxInto medium plane side ↔
      0 < inner ℝ (plane.sideNormalVector side)
        (⨍ time in startTime.val..startTime.val + 2 * Real.pi / wave.angularFrequency,
          ThreeDimension.poyntingVector wave.electricField
            (wave.magneticFieldStrength medium) (time : Time) plane.point) := by
  rw [HasPositiveMeanNormalFluxInto,
    wave.intervalAverage_poyntingVector_eq_localPhasors]

end ComplexMonochromaticPlaneWave

end

end ThreeDimension
end Electromagnetism

namespace Optics

open ClassicalMechanics Electromagnetism Electromagnetism.ThreeDimension Space Time
open scoped Interval Real

noncomputable section

namespace IsReferencedMaterialJonesWave

/-!
## B. Referenced material Jones waves
-/

variable {plane : OrientedAffineHyperplane 3} {medium : HomogeneousIsotropicMedium}
  {wave : ComplexMonochromaticPlaneWave} {direction : Space.Direction 3}
  {frame : PolarizationFrame direction} {J : JonesVector}

/-- At the reference-plane point, the closed phasor Poynting vector of a material Jones wave is
its irradiance in the framed propagation direction. -/
lemma timeAveragedPoyntingVector_planePoint
    (h : IsReferencedMaterialJonesWave plane medium wave frame J) :
    timeAveragedPoyntingVector (wave.localElectricPhasor plane.point)
        (wave.localMagneticFieldStrengthPhasor medium plane.point) =
      J.materialPlaneWaveIrradiance medium • frame.propagationVector := by
  rw [h.localElectricPhasor_planePoint, h.localMagneticFieldStrengthPhasor_planePoint]
  exact frame.timeAveragedPoyntingVector_embedJones_propagationCross J medium

/-- For a nonzero-flux referenced propagating material Jones wave, positive local mean power flow
into a geometric side is equivalent to strict phase direction into that side.

This is a propagating positive-medium result. It does not promote either side condition to a
radiation or limiting-absorption condition. -/
lemma hasPositiveMeanNormalFluxInto_iff_isPhaseDirectedInto
    (h : IsReferencedMaterialJonesWave plane medium wave frame J)
    (side : OrientedAffineHyperplane.Side)
    (hIrradiance : 0 < J.materialPlaneWaveIrradiance medium) :
    wave.HasPositiveMeanNormalFluxInto medium plane side ↔
      wave.waveVector.IsPhaseDirectedInto plane side := by
  rw [ComplexMonochromaticPlaneWave.HasPositiveMeanNormalFluxInto,
    h.timeAveragedPoyntingVector_planePoint, h.isPhaseDirectedInto_iff]
  have hFlux :
      inner ℝ (plane.sideNormalVector side)
          (J.materialPlaneWaveIrradiance medium • frame.propagationVector) =
        J.materialPlaneWaveIrradiance medium *
          (side.sign * plane.normalComponent frame.propagationVector) := by
    simp only [OrientedAffineHyperplane.sideNormalVector,
      OrientedAffineHyperplane.normalComponent, real_inner_smul_left,
      real_inner_smul_right]
  rw [hFlux, mul_pos_iff_of_pos_left hIrradiance]

end IsReferencedMaterialJonesWave

end

end Optics
