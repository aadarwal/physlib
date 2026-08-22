/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Polarization.HarmonicWave
public import Physlib.Optics.Polarization.MaterialWave

/-!
# Fixed-vacuum regression for framed material waves

## i. Overview

This file verifies that the general oriented Jones-to-material-wave construction recovers the
existing potential-derived free-space harmonic wave. The regression uses positive wave number,
angular frequency `k * c`, propagation along the first coordinate, and ordered polarization axes
along the second and third coordinates.

The new and old constructions agree on carrier wave number and phase, the complete electric
field, and the complete magnetic induction. The comparison is deliberately between fields: a
Jones vector does not determine an electromagnetic potential without additional gauge data.

## ii. Key results

- `harmonicWaveXPolarizationFrame`: the proof-bearing fixed coordinate frame.
- `harmonicWaveXPolarizationFrame_realizeJones`: agreement of the two Jones realizations.
- `harmonicWaveX_materialWave_waveNumber`: recovery of the positive vacuum wave number.
- `harmonicWaveX_materialWave_carrierPhase`: agreement of carrier phases.
- `harmonicWaveX_materialWave_electricField`: complete electric-field agreement.
- `harmonicWaveX_materialWave_magneticInduction`: complete magnetic-induction agreement.

## iii. Table of contents

- A. Fixed oriented frame
- B. Carrier regression
- C. Electric- and magnetic-field regression

## iv. References

The regression is derived from the two imported Physlib constructions. It does not identify
squared Jones intensity with irradiance or power, reconstruct a gauge potential, introduce
circular-handedness names, or extend either construction to static backgrounds, lossy media, or
evanescent waves.
-/

@[expose] public section

namespace Optics

open Electromagnetism Electromagnetism.ElectromagneticPotential
  Electromagnetism.ThreeDimension Space Time Matrix InnerProductSpace
open MonochromaticPlaneWave

noncomputable section

/-!

## A. Fixed oriented frame

-/

/-- The oriented coordinate polarization frame used by the existing `harmonicWaveX` bridge.

Propagation is along coordinate zero, and the ordered Jones axes are coordinates one and two. -/
def harmonicWaveXPolarizationFrame : PolarizationFrame harmonicWaveXDirection where
  axis := fun i ↦ EuclideanSpace.single i.succ 1
  orthonormal_axis :=
    EuclideanSpace.orthonormal_single.comp Fin.succ (Fin.succ_injective 2)
  orientation := by
    ext i
    fin_cases i <;>
      simp [crossProduct, harmonicWaveXDirection]

/-- General oriented-frame Jones realization specializes to the existing fixed-coordinate
realization. -/
lemma harmonicWaveXPolarizationFrame_realizeJones
    (J : JonesVector) (carrierPhase : ℝ) :
    harmonicWaveXPolarizationFrame.realizeJones J carrierPhase =
      J.realizeHarmonicWaveXFrame carrierPhase := by
  ext k
  fin_cases k <;>
    simp [PolarizationFrame.realizeJones, PolarizationFrame.embedJones,
      PolarizationFrame.complexAxis, harmonicWaveXPolarizationFrame,
      JonesVector.realizeHarmonicWaveXFrame, Phasor.realize]

/-!

## B. Carrier regression

-/

/-- The free-space material-wave specialization recovers the supplied positive wave number. -/
lemma harmonicWaveX_materialWave_waveNumber
    (F : FreeSpace) {waveNumber : ℝ} (hκ : 0 < waveNumber)
    (amplitude phaseOffset : Fin 2 → ℝ) :
    ((JonesVector.ofAmplitudePhase amplitude phaseOffset).toMaterialPlaneWave
      F.toHomogeneousIsotropicMedium harmonicWaveXPolarizationFrame
      (harmonicWaveXAngularFrequency F waveNumber)
      (harmonicWaveXAngularFrequency_pos F hκ)).waveNumber = waveNumber := by
  rw [JonesVector.toMaterialPlaneWave_waveNumber]
  simp only [harmonicWaveXAngularFrequency, F.toHomogeneousIsotropicMedium_waveSpeed]
  field_simp [SpeedOfLight.val_ne_zero]

/-- The free-space material-wave specialization has the existing `harmonicWaveX` carrier phase. -/
lemma harmonicWaveX_materialWave_carrierPhase
    (F : FreeSpace) {waveNumber : ℝ} (hκ : 0 < waveNumber)
    (amplitude phaseOffset : Fin 2 → ℝ) (t : Time) (x : Space) :
    ((JonesVector.ofAmplitudePhase amplitude phaseOffset).toMaterialPlaneWave
      F.toHomogeneousIsotropicMedium harmonicWaveXPolarizationFrame
      (harmonicWaveXAngularFrequency F waveNumber)
      (harmonicWaveXAngularFrequency_pos F hκ)).carrierPhase t x =
        harmonicWaveXCarrierPhase F waveNumber t x := by
  simp [MonochromaticPlaneWave.carrierPhase, JonesVector.toMaterialPlaneWave,
    MonochromaticPlaneWave.inMedium, harmonicWaveXCarrierPhase,
    harmonicWaveXAngularFrequency, harmonicWaveXDirection]
  left
  field_simp [SpeedOfLight.val_ne_zero]
  exact F.toHomogeneousIsotropicMedium_waveSpeed.symm

/-!

## C. Electric- and magnetic-field regression

-/

/-- The oriented material connector specializes in free space to the complete electric field of
the existing potential-derived harmonic wave. -/
lemma harmonicWaveX_materialWave_electricField
    (F : FreeSpace) {waveNumber : ℝ} (hκ : 0 < waveNumber)
    (amplitude phaseOffset : Fin 2 → ℝ) (t : Time) (x : Space) :
    ((JonesVector.ofAmplitudePhase amplitude phaseOffset).toMaterialPlaneWave
      F.toHomogeneousIsotropicMedium harmonicWaveXPolarizationFrame
      (harmonicWaveXAngularFrequency F waveNumber)
      (harmonicWaveXAngularFrequency_pos F hκ)).electricField t x =
        (harmonicWaveX F waveNumber amplitude phaseOffset).electricField F.c t x := by
  rw [JonesVector.toMaterialPlaneWave_electricField,
    harmonicWaveXPolarizationFrame_realizeJones,
    harmonicWaveX_electricField_eq_realize F hκ,
    harmonicWaveX_materialWave_carrierPhase F hκ]

/-- The oriented material connector specializes in free space to the complete magnetic induction
of the existing potential-derived harmonic wave. -/
lemma harmonicWaveX_materialWave_magneticInduction
    (F : FreeSpace) {waveNumber : ℝ} (hκ : 0 < waveNumber)
    (amplitude phaseOffset : Fin 2 → ℝ) (t : Time) (x : Space) :
    ((JonesVector.ofAmplitudePhase amplitude phaseOffset).toMaterialPlaneWave
      F.toHomogeneousIsotropicMedium harmonicWaveXPolarizationFrame
      (harmonicWaveXAngularFrequency F waveNumber)
      (harmonicWaveXAngularFrequency_pos F hκ)).magneticInduction t x =
        (harmonicWaveX F waveNumber amplitude phaseOffset).magneticField F.c t x := by
  let J := JonesVector.ofAmplitudePhase amplitude phaseOffset
  let wave := J.toMaterialPlaneWave F.toHomogeneousIsotropicMedium
    harmonicWaveXPolarizationFrame (harmonicWaveXAngularFrequency F waveNumber)
    (harmonicWaveXAngularFrequency_pos F hκ)
  have hdisp : wave.IsDispersionMatched F.toHomogeneousIsotropicMedium :=
    MonochromaticPlaneWave.inMedium_isDispersionMatched F.toHomogeneousIsotropicMedium
      harmonicWaveXDirection (harmonicWaveXAngularFrequency F waveNumber)
      (harmonicWaveXAngularFrequency_pos F hκ)
      (harmonicWaveXPolarizationFrame.electricReal J)
      (harmonicWaveXPolarizationFrame.electricImag J)
  have hB :=
    IsDispersionMatched.magneticInduction_eq_waveSpeed_inv_smul_cross_electricField
      hdisp t x
  change wave.magneticInduction t x = _
  rw [hB, harmonicWaveX_magneticField_eq_cross_electricField F hκ,
    harmonicWaveX_materialWave_electricField F hκ]
  simp [wave, J, MonochromaticPlaneWave.propagationVector,
    JonesVector.toMaterialPlaneWave, MonochromaticPlaneWave.inMedium,
    harmonicWaveXPolarizationFrame, F.toHomogeneousIsotropicMedium_waveSpeed, one_div]

end

end Optics
