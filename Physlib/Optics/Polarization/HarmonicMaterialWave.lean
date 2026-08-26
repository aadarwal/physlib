/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Polarization.HarmonicWave
public import Physlib.Optics.Polarization.MaterialWave

/-!
# Fixed-frame material realization of the vacuum harmonic wave

## i. Overview

This file connects the existing potential-derived free-space wave `harmonicWaveX` to the oriented
Jones material-wave construction. Propagation is along the first coordinate, and the ordered
Jones axes are the second and third coordinates.

For positive wave number, both constructions have the same carrier wave number and phase. Their
complete electric fields and magnetic inductions agree. Applying the free-space constitutive law
then gives the same magnetic field strength, which is the field used in the Poynting vector.

## ii. Key results

- `harmonicWaveXPolarizationFrame`: the proof-bearing fixed coordinate frame.
- `harmonicWaveX_materialWave_electricField`: complete electric-field agreement.
- `harmonicWaveX_materialWave_magneticInduction`: complete magnetic-induction agreement.
- `harmonicWaveX_materialWave_magneticFieldStrength`: complete magnetic-field-strength agreement.

## iii. Table of contents

- A. Fixed oriented frame
- B. Carrier agreement
- C. Electric and magnetic field agreement

## iv. References

The comparison is between fields. A Jones vector does not reconstruct a gauge potential, and this
module does not identify squared Jones intensity with irradiance or power. The source wave has no
arbitrary static background, lossy-medium, or evanescent-wave extension here.
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

## B. Carrier agreement

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

## C. Electric and magnetic field agreement

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

/-- The free-space material connector and the potential-derived harmonic wave have the same
constitutive magnetic field strength. -/
lemma harmonicWaveX_materialWave_magneticFieldStrength
    (F : FreeSpace) {waveNumber : ℝ} (hκ : 0 < waveNumber)
    (amplitude phaseOffset : Fin 2 → ℝ) (t : Time) (x : Space) :
    ((JonesVector.ofAmplitudePhase amplitude phaseOffset).toMaterialPlaneWave
      F.toHomogeneousIsotropicMedium harmonicWaveXPolarizationFrame
      (harmonicWaveXAngularFrequency F waveNumber)
      (harmonicWaveXAngularFrequency_pos F hκ)).magneticFieldStrength
        F.toHomogeneousIsotropicMedium t x =
      F.μ₀⁻¹ •
        (harmonicWaveX F waveNumber amplitude phaseOffset).magneticField F.c t x := by
  rw [MonochromaticPlaneWave.magneticFieldStrength,
    HomogeneousIsotropicMedium.magneticFieldStrength_apply,
    harmonicWaveX_materialWave_magneticInduction F hκ,
    FreeSpace.toHomogeneousIsotropicMedium_μ]

end

end Optics
