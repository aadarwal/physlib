/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.HarmonicFlux.PolarizerModePower
public import Physlib.Optics.Systems.PolarizerRetarder

/-!
# Physical observables for a polarizer-retarder chain

## i. Overview

This file realizes the ordered ideal polarizer-retarder Jones chain as a complete framed material
plane-wave carrier. The polarizer selects the analyzer amplitude and the retarder changes the
output Jones state without changing its squared raw amplitude. Consequently, material irradiance
and the actual one-period mean Poynting vector obey the same cosine-squared law.

The output carrier is a singleton propagating Maxwell mode, but no flux normalization is built
into its definition. Aperture-integrated normalized power is added separately under explicit E3b
normalization hypotheses.

## ii. Key results

- `MaterialJonesMode.polarizerRetarderOutputFamily`: the retarded analyzer output carrier.
- `JonesMatrix.linearRetarder_comp_linearPolarizer_scaledWave_eq`: exact carrier realization.
- `JonesMatrix.linearRetarder_comp_linearPolarizer_malus_materialPlaneWaveIrradiance`: physical
  irradiance Malus law.
- `JonesMatrix.linearRetarder_comp_linearPolarizer_malus_intervalAverage_poyntingVector`: actual
  one-period mean Poynting-vector law.

## iii. Table of contents

- A. Retarded output family
- B. Exact carrier realization
- C. Irradiance and actual mean flux density

## iv. References

This is an ideal zero-thickness selected-output model. It does not model reflection, rejected
polarization, absorption, heating, internal fields, or a complete physical scattering component.
The results apply to pure scaled linear Jones inputs, not partially polarized or coherency-matrix
mixtures. Raw retarder unitarity alone is not an electromagnetic aperture-power statement.
-/

@[expose] public section

namespace Optics

open Electromagnetism Electromagnetism.ThreeDimension MeasureTheory Space Time
open scoped Interval Real

noncomputable section

namespace MaterialJonesMode

/-!

## A. Retarded output family

-/

/-- The singleton material-Jones family carried by the retarder output of the analyzer axis.

This constructor contains no flux-normalization claim. -/
def polarizerRetarderOutputFamily
    (retarderAxis retardance analyzer : Real.Angle)
    (medium : HomogeneousIsotropicMedium)
    {direction : Space.Direction 3} (frame : PolarizationFrame direction)
    (angularFrequency : ℝ) (hFrequency : 0 < angularFrequency) :
    PropagatingHarmonicModeFamily Unit :=
  family
    ((JonesMatrix.linearRetarder retarderAxis retardance).act
      (JonesVector.linearPolarization analyzer))
    medium frame angularFrequency hFrequency

end MaterialJonesMode

namespace JonesMatrix

/-!

## B. Exact carrier realization

-/

/-- The singleton modal carrier after the analyzer and retarder is exactly the material wave
constructed from the ordered Jones cascade. -/
lemma linearRetarder_comp_linearPolarizer_scaledWave_eq
    (z : ℂ) (retarderAxis retardance analyzer input : Real.Angle)
    (medium : HomogeneousIsotropicMedium)
    {direction : Space.Direction 3} (frame : PolarizationFrame direction)
    (angularFrequency : ℝ) (hFrequency : 0 < angularFrequency) :
    (MaterialJonesMode.polarizerRetarderOutputFamily
      retarderAxis retardance analyzer medium frame angularFrequency hFrequency).scaledWave
        (linearPolarizerOutputAmplitude z analyzer input) () =
      ComplexMonochromaticPlaneWave.ofReal
        ((((linearRetarder retarderAxis retardance).comp
          (linearPolarizer analyzer)).act
            (JonesVector.scale z (JonesVector.linearPolarization input))).toMaterialPlaneWave
              medium frame angularFrequency hFrequency) := by
  rw [MaterialJonesMode.polarizerRetarderOutputFamily,
    linearPolarizerOutputAmplitude, MaterialJonesMode.scaledWave_eq,
    linearRetarder_comp_linearPolarizer_act,
    JonesVector.linearComponent_scale,
    JonesVector.linearComponent_linearPolarization,
    linearRetarder_act_linearPolarization]

/-!

## C. Irradiance and actual mean flux density

-/

/-- A retarder after an ideal linear analyzer leaves the analyzer's material-irradiance Malus
factor unchanged. -/
lemma linearRetarder_comp_linearPolarizer_malus_materialPlaneWaveIrradiance
    (z : ℂ) (retarderAxis retardance analyzer input : Real.Angle)
    (medium : HomogeneousIsotropicMedium) :
    JonesVector.materialPlaneWaveIrradiance
      (((linearRetarder retarderAxis retardance).comp
        (linearPolarizer analyzer)).act
          (JonesVector.scale z (JonesVector.linearPolarization input))) medium =
      JonesVector.materialPlaneWaveIrradiance
        (JonesVector.scale z (JonesVector.linearPolarization input)) medium *
          Real.Angle.cos (input - analyzer) ^ 2 := by
  rw [JonesVector.materialPlaneWaveIrradiance,
    JonesVector.materialPlaneWaveIrradiance, comp_act,
    linearRetarder_act_intensity, linearPolarizer_malus]
  ring

/-- The actual one-period mean Poynting vector after the analyzer-retarder chain obeys the
cosine-squared Malus law.

Both waves use the same medium, propagation frame, positive frequency, time origin, and point. -/
lemma linearRetarder_comp_linearPolarizer_malus_intervalAverage_poyntingVector
    (z : ℂ) (retarderAxis retardance analyzer input : Real.Angle)
    (medium : HomogeneousIsotropicMedium)
    {direction : Space.Direction 3} (frame : PolarizationFrame direction)
    (angularFrequency : ℝ) (hω : 0 < angularFrequency)
    (startTime : Time) (x : Space) :
    let inputJones := JonesVector.scale z (JonesVector.linearPolarization input)
    let outputJones :=
      ((linearRetarder retarderAxis retardance).comp
        (linearPolarizer analyzer)).act inputJones
    let inputWave := inputJones.toMaterialPlaneWave medium frame angularFrequency hω
    let outputWave := outputJones.toMaterialPlaneWave medium frame angularFrequency hω
    (⨍ time in startTime.val..startTime.val + 2 * Real.pi / angularFrequency,
      poyntingVector
        outputWave.electricField (outputWave.magneticFieldStrength medium)
        (time : Time) x) =
      Real.Angle.cos (input - analyzer) ^ 2 •
        (⨍ time in startTime.val..startTime.val + 2 * Real.pi / angularFrequency,
          poyntingVector
            inputWave.electricField (inputWave.magneticFieldStrength medium)
            (time : Time) x) := by
  dsimp only
  rw [JonesVector.toMaterialPlaneWave_intervalAverage_poyntingVector,
    JonesVector.toMaterialPlaneWave_intervalAverage_poyntingVector,
    linearRetarder_comp_linearPolarizer_malus_materialPlaneWaveIrradiance]
  rw [smul_smul]
  congr 1
  ring

end JonesMatrix

end

end Optics
