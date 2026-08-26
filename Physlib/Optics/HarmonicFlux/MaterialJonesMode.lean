/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.HarmonicFlux.PropagatingModeSynthesis
public import Physlib.Optics.Polarization.ReferencedMaterialWave

/-!
# Framed Jones data as one propagating Maxwell mode

## i. Overview

This file supplies an explicit bridge from a framed Jones electric amplitude to a singleton
`PropagatingHarmonicModeFamily`. The stored carrier is the complex embedding of the existing
ordinary-real material plane wave. It therefore has the declared positive frequency, zero
attenuation, electric transversality, material dispersion, and the source-free Maxwell meaning
carried by `PropagatingHarmonicModeFamily`.

`MaterialJonesMode.amplitude z` is the singleton modal coordinate. The main compatibility result
proves that scaling this modal coordinate produces exactly the same complete complex carrier as
first scaling the Jones data by `z` and then constructing its material plane wave. This is an
explicit bridge, not a coercion between raw Jones coordinates and power-normalized modes.

## ii. Key results

- `MaterialJonesMode.family`: the singleton Maxwell-qualified material-Jones family.
- `MaterialJonesMode.amplitude_power`: exact power of the singleton modal coordinate.
- `MaterialJonesMode.scaledWave_eq`: modal and Jones scaling give the same complex carrier.

## iii. Table of contents

- A. Singleton material-Jones mode data
- B. Exact carrier compatibility

## iv. References

The family is not asserted to be flux normalized or complete. Interpreting its coordinate power
as electromagnetic aperture power still requires an `IsApertureFluxOrthonormal` proof for a
declared measured profile and incident or outgoing role.

-/

@[expose] public section

namespace Optics

open Electromagnetism Electromagnetism.ThreeDimension Space

noncomputable section

namespace MaterialJonesMode

/-!

## A. Singleton material-Jones mode data

-/

/-- The singleton propagating Maxwell family carried by framed material Jones data.

No flux normalization is included in this constructor. -/
def family (J : JonesVector) (medium : HomogeneousIsotropicMedium)
    {direction : Space.Direction 3} (frame : PolarizationFrame direction)
    (angularFrequency : ℝ) (hFrequency : 0 < angularFrequency) :
    PropagatingHarmonicModeFamily Unit where
  medium := medium
  angularFrequency := angularFrequency
  angularFrequency_pos := hFrequency
  wave := fun _ => ComplexMonochromaticPlaneWave.ofReal
    (J.toMaterialPlaneWave medium frame angularFrequency hFrequency)
  commonAngularFrequency := by intro i; cases i; rfl
  zeroAttenuation := by
    intro i
    cases i
    exact ClassicalMechanics.ComplexWaveVector.attenuationVector_ofReal _
  isTransverse := by
    intro i
    cases i
    rw [ComplexMonochromaticPlaneWave.isTransverse_ofReal_iff]
    exact J.toMaterialPlaneWave_isTransverse medium frame angularFrequency hFrequency
  isDispersionMatched := by
    intro i
    cases i
    rw [ComplexMonochromaticPlaneWave.isDispersionMatched_ofReal_iff]
    exact MonochromaticPlaneWave.inMedium_isDispersionMatched medium direction angularFrequency
      hFrequency (frame.electricReal J) (frame.electricImag J)

/-- The complex coordinate of a singleton material-Jones mode. -/
def amplitude (z : ℂ) : ModeAmplitude Unit :=
  WithLp.toLp 2 fun _ => z

/-- A singleton material-Jones coordinate carries squared-modulus modal power. -/
lemma amplitude_power (z : ℂ) :
    (amplitude z).power = Complex.normSq z := by
  rw [ModeAmplitude.power_eq_sum_normSq]
  simp [amplitude]

/-!

## B. Exact carrier compatibility

-/

/-- Scaling the singleton modal coordinate gives exactly the carrier obtained by scaling the
underlying Jones data before material-wave construction.

The equality includes the frequency and wave vector as well as the electric amplitude. -/
lemma scaledWave_eq (J : JonesVector) (medium : HomogeneousIsotropicMedium)
    {direction : Space.Direction 3} (frame : PolarizationFrame direction)
    (angularFrequency : ℝ) (hFrequency : 0 < angularFrequency) (z : ℂ) :
    (family J medium frame angularFrequency hFrequency).scaledWave (amplitude z) () =
      ComplexMonochromaticPlaneWave.ofReal
        ((JonesVector.scale z J).toMaterialPlaneWave medium frame angularFrequency hFrequency) := by
  rw [ComplexMonochromaticPlaneWave.mk.injEq]
  refine ⟨rfl, rfl, ?_⟩
  simp only [PropagatingHarmonicModeFamily.scaledWave,
    ComplexMonochromaticPlaneWave.scaleElectricAmplitude_electricAmplitude,
    amplitude, family]
  rw [JonesVector.ofReal_toMaterialPlaneWave_electricAmplitude,
    JonesVector.ofReal_toMaterialPlaneWave_electricAmplitude, frame.embedJones_scale]

end MaterialJonesMode

end

end Optics
