/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Components.Polarizer.Malus
public import Physlib.Optics.HarmonicFlux.MaterialWave

/-!
# Malus' law for material plane-wave irradiance

## i. Overview

This file gives the ideal linear-polarizer Jones laws their propagating material-plane-wave
interpretation. For the raw Jones output used to construct a plane wave in the same homogeneous
medium and propagation frame, material irradiance obeys Malus' cosine-squared law. The final result
states the same law directly for the actual one-period-averaged Poynting vectors.

## ii. Key results

- `JonesMatrix.linearPolarizer_malus_materialPlaneWaveIrradiance`: material-irradiance Malus law.
- `JonesMatrix.linearPolarizer_act_materialPlaneWaveIrradiance_le`: arbitrary-input irradiance
  contraction.
- `JonesMatrix.linearPolarizer_comp_materialPlaneWaveIrradiance`: sequential-polarizer irradiance.
- `JonesMatrix.linearPolarizer_malus_intervalAverage_poyntingVector`: the actual-field mean-flux
  Malus law.

## iii. Table of contents

- A. Material irradiance
- B. Actual mean Poynting flux

## iv. References

The field-level statement models an ideal zero-thickness analyzer by applying its Jones matrix and
then constructing the output wave with the same medium, propagation frame, angular frequency, and
phase convention as the input wave. It does not model reflection, refraction, fields inside the
component, or the fate of the discarded orthogonal component. In particular, irradiance
contraction is not called electromagnetic passivity or absorption here.

These results concern local flux density for an infinite plane wave. They include zero input but
assert no aperture-integrated power, normalized modal power, or component energy balance.

-/

@[expose] public section

namespace Optics

open Electromagnetism Electromagnetism.ThreeDimension MeasureTheory Space Time
open scoped Interval Real

noncomputable section

namespace JonesMatrix

/-!

## A. Material irradiance

-/

/-- An ideal linear polarizer multiplies a scaled linear input's propagating material-plane-wave
irradiance by the squared cosine of the angle between the input and analyzer axes.

The statement includes a zero input amplitude. -/
lemma linearPolarizer_malus_materialPlaneWaveIrradiance (z : ℂ)
    (analyzer input : Real.Angle) (medium : HomogeneousIsotropicMedium) :
    JonesVector.materialPlaneWaveIrradiance
        ((linearPolarizer analyzer).act
          (JonesVector.scale z (JonesVector.linearPolarization input))) medium =
      JonesVector.materialPlaneWaveIrradiance
          (JonesVector.scale z (JonesVector.linearPolarization input)) medium *
        Real.Angle.cos (input - analyzer) ^ 2 := by
  rw [JonesVector.materialPlaneWaveIrradiance,
    JonesVector.materialPlaneWaveIrradiance, linearPolarizer_malus]
  ring

/-- An ideal linear polarizer cannot increase the propagating material-plane-wave irradiance of
an arbitrary Jones input.

This is an irradiance-contraction result for the selected output-wave model, not a theorem about
absorption, heating, or the total energy balance of a physical polarizer. -/
lemma linearPolarizer_act_materialPlaneWaveIrradiance_le
    (analyzer : Real.Angle) (J : JonesVector)
    (medium : HomogeneousIsotropicMedium) :
    ((linearPolarizer analyzer).act J).materialPlaneWaveIrradiance medium ≤
      J.materialPlaneWaveIrradiance medium := by
  rw [JonesVector.materialPlaneWaveIrradiance,
    JonesVector.materialPlaneWaveIrradiance,
    div_le_div_iff_of_pos_right (mul_pos zero_lt_two medium.waveImpedance_pos)]
  exact linearPolarizer_act_intensity_le analyzer J

/-- After two ideal linear polarizers, the first output's material-plane-wave irradiance is
multiplied by the squared cosine of the angle between their axes. -/
lemma linearPolarizer_comp_materialPlaneWaveIrradiance
    (first second : Real.Angle) (J : JonesVector)
    (medium : HomogeneousIsotropicMedium) :
    JonesVector.materialPlaneWaveIrradiance
        (((linearPolarizer second).comp (linearPolarizer first)).act J) medium =
      ((linearPolarizer first).act J).materialPlaneWaveIrradiance medium *
        Real.Angle.cos (first - second) ^ 2 := by
  rw [JonesVector.materialPlaneWaveIrradiance,
    JonesVector.materialPlaneWaveIrradiance, linearPolarizer_comp_intensity]
  ring

/-!

## B. Actual mean Poynting flux

-/

/-- Applying an ideal linear analyzer to a scaled linear Jones input multiplies the actual
material plane wave's one-period-averaged Poynting vector by the squared cosine of the axis angle.

Both sides use the same homogeneous medium, propagation frame, positive angular frequency,
period origin, and observation point. Thus the theorem models a thin analyzer that changes only
the Jones amplitude; it makes no claim about fields or energy inside the component. -/
lemma linearPolarizer_malus_intervalAverage_poyntingVector
    (z : ℂ) (analyzer input : Real.Angle)
    (medium : HomogeneousIsotropicMedium)
    {direction : Space.Direction 3} (frame : PolarizationFrame direction)
    (angularFrequency : ℝ) (hω : 0 < angularFrequency)
    (startTime : Time) (x : Space) :
    let inputJones := JonesVector.scale z (JonesVector.linearPolarization input)
    let outputJones := (linearPolarizer analyzer).act inputJones
    (⨍ time in startTime.val..startTime.val + 2 * Real.pi / angularFrequency,
      ThreeDimension.poyntingVector
        (outputJones.toMaterialPlaneWave medium frame angularFrequency hω).electricField
        ((outputJones.toMaterialPlaneWave medium frame angularFrequency hω).magneticFieldStrength
          medium)
        (time : Time) x) =
      Real.Angle.cos (input - analyzer) ^ 2 •
        (⨍ time in startTime.val..startTime.val + 2 * Real.pi / angularFrequency,
          ThreeDimension.poyntingVector
            (inputJones.toMaterialPlaneWave medium frame angularFrequency hω).electricField
            ((inputJones.toMaterialPlaneWave medium frame angularFrequency hω).magneticFieldStrength
              medium)
            (time : Time) x) := by
  dsimp only
  rw [JonesVector.toMaterialPlaneWave_intervalAverage_poyntingVector,
    JonesVector.toMaterialPlaneWave_intervalAverage_poyntingVector,
    linearPolarizer_malus_materialPlaneWaveIrradiance]
  rw [smul_smul]
  congr 1
  ring

end JonesMatrix

end

end Optics
