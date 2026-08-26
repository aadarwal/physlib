/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Polarization.HarmonicMaterialWave

/-!
# Fixed-vacuum regression for framed material waves

## i. Overview

This file checks the production bridge from the potential-derived `harmonicWaveX` solution to the
oriented material-wave construction on an exact horizontal fixture. At the spacetime origin, the
electric field points along coordinate one and the constitutive magnetic field strength points
along coordinate two with the inverse wave-speed factor.

## ii. Key results

- `materialWaveRegression_jones`: the amplitude-phase data is the horizontal Jones state.
- `materialWaveRegression_electricField_origin`: the exact electric-field orientation.
- `materialWaveRegression_magneticFieldStrength_origin`: the exact magnetic-field orientation.

## iii. Table of contents

- A. Exact vacuum and Jones data
- B. Exact field values

## iv. References

The fixture checks field orientation and the constitutive `B`-to-`H` bridge. It makes no
irradiance, aperture-power, gauge-potential, handedness, lossy-medium, or evanescent-wave claim.
-/

@[expose] public section

namespace Optics

open Electromagnetism Electromagnetism.ElectromagneticPotential
  Electromagnetism.ThreeDimension Space Time Matrix

noncomputable section

/-!

## A. Exact vacuum and Jones data

-/

/-- The exact free-space data used by the material-wave regression. -/
def materialWaveRegressionFreeSpace : FreeSpace where
  ε₀ := 4
  μ₀ := 1
  ε₀_pos := by norm_num
  μ₀_pos := by norm_num

/-- The horizontal unit electric-amplitude data. -/
def materialWaveRegressionAmplitude : Fin 2 → ℝ := ![1, 0]

/-- Both transverse component phase offsets vanish. -/
def materialWaveRegressionPhaseOffset : Fin 2 → ℝ := 0

/-- The exact amplitude-phase data is the horizontal Jones state. -/
lemma materialWaveRegression_jones :
    JonesVector.ofAmplitudePhase materialWaveRegressionAmplitude
      materialWaveRegressionPhaseOffset = JonesVector.horizontal := by
  ext i
  fin_cases i <;>
    norm_num [JonesVector.ofAmplitudePhase, materialWaveRegressionAmplitude,
      materialWaveRegressionPhaseOffset, JonesVector.horizontal, JonesVector.ofComponents,
      Phasor.ofAmplitudePhase]

/-!

## B. Exact field values

-/

/-- The potential-derived fixture has the expected horizontal electric field at the spacetime
origin. -/
lemma materialWaveRegression_harmonicWaveX_electricField_origin :
    (harmonicWaveX materialWaveRegressionFreeSpace 2 materialWaveRegressionAmplitude
      materialWaveRegressionPhaseOffset).electricField
        materialWaveRegressionFreeSpace.c 0 0 = EuclideanSpace.single 1 1 := by
  rw [harmonicWaveX_electricField_eq_realize
    materialWaveRegressionFreeSpace (by norm_num), materialWaveRegression_jones]
  ext i
  fin_cases i <;>
    simp [JonesVector.realizeHarmonicWaveXFrame, harmonicWaveXCarrierPhase,
      JonesVector.horizontal, JonesVector.ofComponents, Phasor.realize,
      materialWaveRegressionFreeSpace]

/-- At the spacetime origin, the horizontal fixture's electric field is coordinate one. -/
lemma materialWaveRegression_electricField_origin :
    (((JonesVector.ofAmplitudePhase materialWaveRegressionAmplitude
      materialWaveRegressionPhaseOffset).toMaterialPlaneWave
        materialWaveRegressionFreeSpace.toHomogeneousIsotropicMedium
        harmonicWaveXPolarizationFrame
        (harmonicWaveXAngularFrequency materialWaveRegressionFreeSpace 2)
        (harmonicWaveXAngularFrequency_pos materialWaveRegressionFreeSpace
          (by norm_num))).electricField 0 0) = EuclideanSpace.single 1 1 := by
  rw [harmonicWaveX_materialWave_electricField
    materialWaveRegressionFreeSpace (by norm_num)]
  exact materialWaveRegression_harmonicWaveX_electricField_origin

/-- At the spacetime origin, the fixture's magnetic field strength is coordinate two with the
inverse wave-speed factor. -/
lemma materialWaveRegression_magneticFieldStrength_origin :
    (((JonesVector.ofAmplitudePhase materialWaveRegressionAmplitude
      materialWaveRegressionPhaseOffset).toMaterialPlaneWave
        materialWaveRegressionFreeSpace.toHomogeneousIsotropicMedium
        harmonicWaveXPolarizationFrame
        (harmonicWaveXAngularFrequency materialWaveRegressionFreeSpace 2)
        (harmonicWaveXAngularFrequency_pos materialWaveRegressionFreeSpace
          (by norm_num))).magneticFieldStrength
            materialWaveRegressionFreeSpace.toHomogeneousIsotropicMedium 0 0) =
        materialWaveRegressionFreeSpace.c.val⁻¹ • EuclideanSpace.single 2 1 := by
  rw [harmonicWaveX_materialWave_magneticFieldStrength
    materialWaveRegressionFreeSpace (by norm_num)]
  rw [harmonicWaveX_magneticField_eq_cross_electricField
    materialWaveRegressionFreeSpace (by norm_num)]
  rw [materialWaveRegression_harmonicWaveX_electricField_origin]
  simp [harmonicWaveXDirection, crossProduct, materialWaveRegressionFreeSpace, one_div]
  ext i
  fin_cases i <;> simp

end

end Optics
