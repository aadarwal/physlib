/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.HarmonicFlux.MaterialWave
public import Physlib.SpaceAndTime.Space.OrientedAffineHyperplane

/-!
# Normal flux of framed material plane waves

## i. Overview

This file projects a propagating material plane wave's actual one-period-averaged Poynting vector
onto an oriented plane normal. The stored normal points from the geometric negative side toward
the geometric positive side, so the first result is a signed flux density. Relative to either
geometric side, the same flux is irradiance times the cosine of the propagation direction's
side-relative angle.

## ii. Key results

- `JonesVector.normalComponent_toMaterialPlaneWave_intervalAverage_poyntingVector`: the signed
  stored-normal flux identity.
- `JonesVector.inner_sideNormalVector_toMaterialPlaneWave_intervalAverage_poyntingVector`: the
  side-relative irradiance-times-cosine identity.

## iii. Table of contents

- A. Stored-normal flux
- B. Side-relative flux

## iv. References

The plane and its sides remain purely geometric. Positive stored-normal flux points from the
negative side toward the positive side. Unguarded convention statement (review only): neither
side is assigned an incident, reflected, transmitted, or outgoing role. The identities include
zero Jones data, negative cosine, and grazing incidence. They apply only to the propagating
ordinary-real material wave, not to a complex attenuating or evanescent carrier.

-/

@[expose] public section

namespace Optics

open Electromagnetism Electromagnetism.ThreeDimension MeasureTheory Space Time
open scoped Interval Real

noncomputable section

namespace JonesVector

/-!

## A. Stored-normal flux

-/

/-- The stored-normal component of a propagating material plane wave's actual one-period mean
Poynting vector is its irradiance times the propagation direction's signed normal component.

Positive values point from the plane's geometric negative side toward its positive side. -/
lemma normalComponent_toMaterialPlaneWave_intervalAverage_poyntingVector
    (J : JonesVector) (medium : HomogeneousIsotropicMedium)
    {direction : Space.Direction 3} (frame : PolarizationFrame direction)
    (plane : OrientedAffineHyperplane 3)
    (angularFrequency : ℝ) (hω : 0 < angularFrequency)
    (startTime : Time) (x : Space) :
    plane.normalComponent
        (⨍ time in startTime.val..startTime.val + 2 * Real.pi / angularFrequency,
          ThreeDimension.poyntingVector
            (J.toMaterialPlaneWave medium frame angularFrequency hω).electricField
            ((J.toMaterialPlaneWave medium frame angularFrequency hω).magneticFieldStrength
              medium)
            (time : Time) x) =
      J.materialPlaneWaveIrradiance medium *
        plane.normalComponent frame.propagationVector := by
  rw [J.toMaterialPlaneWave_intervalAverage_poyntingVector]
  simp [OrientedAffineHyperplane.normalComponent, inner_smul_right]

/-!

## B. Side-relative flux

-/

/-- Relative to either geometric side, a propagating material plane wave's actual one-period mean
normal flux density is its irradiance times the cosine of the propagation direction's
side-relative angle.

The cosine retains the sign: obtuse directions give negative flux and grazing directions give
zero. Unguarded convention statement (review only): the selected side is assigned no physical
wave role. -/
lemma inner_sideNormalVector_toMaterialPlaneWave_intervalAverage_poyntingVector
    (J : JonesVector) (medium : HomogeneousIsotropicMedium)
    {direction : Space.Direction 3} (frame : PolarizationFrame direction)
    (plane : OrientedAffineHyperplane 3) (side : OrientedAffineHyperplane.Side)
    (angularFrequency : ℝ) (hω : 0 < angularFrequency)
    (startTime : Time) (x : Space) :
    inner ℝ (plane.sideNormalVector side)
        (⨍ time in startTime.val..startTime.val + 2 * Real.pi / angularFrequency,
          ThreeDimension.poyntingVector
            (J.toMaterialPlaneWave medium frame angularFrequency hω).electricField
            ((J.toMaterialPlaneWave medium frame angularFrequency hω).magneticFieldStrength
              medium)
            (time : Time) x) =
      J.materialPlaneWaveIrradiance medium *
        Real.cos (plane.angleToSide side frame.propagationVector) := by
  rw [J.toMaterialPlaneWave_intervalAverage_poyntingVector, inner_smul_right]
  congr 1
  rw [OrientedAffineHyperplane.sideNormalVector, inner_smul_left]
  change side.sign * plane.normalComponent frame.propagationVector = _
  rw [← plane.cos_angleToSide_mul_norm side frame.propagationVector,
    frame.propagationVector_norm, mul_one]

end JonesVector

end

end Optics
