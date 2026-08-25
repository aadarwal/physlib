/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Electromagnetism.ThreeDimension.MonochromaticPlaneWave.ComplexMaxwell

/-!
# Complex-amplitude scaling of monochromatic plane waves

## i. Overview

This file scales the stored complex electric amplitude of a complex monochromatic plane-wave
candidate while keeping its positive angular frequency and complex wave vector fixed. The
compatible magnetic amplitude scales by the same complex coefficient. Transversality, material
dispersion, and the resulting source-free Maxwell qualification are preserved.

Complex scaling here acts on peak phasor data. The constructed electromagnetic fields remain
ordinary real fields, so this file does not assert a complex scalar action on those realized
fields. That distinction is needed when coherent modal coefficients encode both amplitude and
carrier phase.

## ii. Key results

- `ComplexMonochromaticPlaneWave.scaleElectricAmplitude`: scale the stored electric amplitude.
- `scaleElectricAmplitude_magneticAmplitude`: the compatible magnetic amplitude scales equally.
- `IsTransverse.scaleElectricAmplitude`: transverse data remains transverse.
- `isMacroscopicMaxwellSolution_scaleElectricAmplitude`: on-shell scaled data remains a
  fixed-medium Maxwell solution.

## iii. Table of contents

- A. Scaled carrier data
- B. Preserved electromagnetic predicates

## iv. References

This is algebraic infrastructure for Physlib's complex-carrier convention. It introduces no
normalization, propagation-role, modal-completeness, or power claim.
-/

@[expose] public section

namespace Electromagnetism
namespace ThreeDimension

open ClassicalMechanics

noncomputable section

namespace ComplexMonochromaticPlaneWave

/-!

## A. Scaled carrier data

-/

/-- Scale the complex electric amplitude while retaining the carrier frequency and wave vector. -/
def scaleElectricAmplitude (wave : ComplexMonochromaticPlaneWave) (z : ℂ) :
    ComplexMonochromaticPlaneWave where
  angularFrequency := wave.angularFrequency
  angularFrequency_pos := wave.angularFrequency_pos
  waveVector := wave.waveVector
  electricAmplitude := z • wave.electricAmplitude

@[simp]
lemma scaleElectricAmplitude_angularFrequency
    (wave : ComplexMonochromaticPlaneWave) (z : ℂ) :
    (wave.scaleElectricAmplitude z).angularFrequency = wave.angularFrequency := rfl

@[simp]
lemma scaleElectricAmplitude_waveVector
    (wave : ComplexMonochromaticPlaneWave) (z : ℂ) :
    (wave.scaleElectricAmplitude z).waveVector = wave.waveVector := rfl

@[simp]
lemma scaleElectricAmplitude_electricAmplitude
    (wave : ComplexMonochromaticPlaneWave) (z : ℂ) :
    (wave.scaleElectricAmplitude z).electricAmplitude = z • wave.electricAmplitude := rfl

/-- Scaling the electric amplitude scales the compatible magnetic amplitude by the same complex
coefficient. -/
lemma scaleElectricAmplitude_magneticAmplitude
    (wave : ComplexMonochromaticPlaneWave) (z : ℂ) :
    (wave.scaleElectricAmplitude z).magneticAmplitude = z • wave.magneticAmplitude := by
  rw [magneticAmplitude, magneticAmplitude, scaleElectricAmplitude_angularFrequency,
    scaleElectricAmplitude_waveVector, scaleElectricAmplitude_electricAmplitude,
    complexCross_smul_right]
  simp only [smul_smul]
  rw [mul_comm]

/-!

## B. Preserved electromagnetic predicates

-/

/-- Complex electric-amplitude scaling preserves bilinear transversality. -/
lemma IsTransverse.scaleElectricAmplitude {wave : ComplexMonochromaticPlaneWave}
    (h : wave.IsTransverse) (z : ℂ) :
    (wave.scaleElectricAmplitude z).IsTransverse := by
  rw [IsTransverse, scaleElectricAmplitude_waveVector,
    scaleElectricAmplitude_electricAmplitude,
    ComplexWaveVector.bilinearDot_smul_right, h, mul_zero]

/-- Material dispersion is unchanged by electric-amplitude scaling because it depends only on the
carrier frequency and wave vector. -/
lemma isDispersionMatched_scaleElectricAmplitude_iff
    (wave : ComplexMonochromaticPlaneWave) (medium : HomogeneousIsotropicMedium) (z : ℂ) :
    (wave.scaleElectricAmplitude z).IsDispersionMatched medium ↔
      wave.IsDispersionMatched medium := by
  simp only [IsDispersionMatched, scaleElectricAmplitude_waveVector,
    scaleElectricAmplitude_angularFrequency]

/-- Scaling an on-shell transverse carrier produces another source-free macroscopic Maxwell
solution in the same homogeneous isotropic medium. -/
lemma isSourceFreeMacroscopicMaxwell_scaleElectricAmplitude
    (wave : ComplexMonochromaticPlaneWave) (medium : HomogeneousIsotropicMedium)
    (hTransverse : wave.IsTransverse) (hDispersion : wave.IsDispersionMatched medium)
    (z : ℂ) :
    IsSourceFreeMacroscopicMaxwell (wave.scaleElectricAmplitude z).electricField
      ((wave.scaleElectricAmplitude z).electricDisplacement medium)
      (wave.scaleElectricAmplitude z).magneticInduction
      ((wave.scaleElectricAmplitude z).magneticFieldStrength medium) :=
  (wave.scaleElectricAmplitude z).isSourceFreeMacroscopicMaxwell medium
    (hTransverse.scaleElectricAmplitude z)
    ((wave.isDispersionMatched_scaleElectricAmplitude_iff medium z).mpr hDispersion)

/-- Scaling an on-shell transverse carrier preserves its fixed-medium Maxwell-solution status. -/
lemma isMacroscopicMaxwellSolution_scaleElectricAmplitude
    (wave : ComplexMonochromaticPlaneWave) (medium : HomogeneousIsotropicMedium)
    (hTransverse : wave.IsTransverse) (hDispersion : wave.IsDispersionMatched medium)
    (z : ℂ) :
    medium.IsMacroscopicMaxwellSolution (wave.scaleElectricAmplitude z).electricField
      ((wave.scaleElectricAmplitude z).electricDisplacement medium)
      (wave.scaleElectricAmplitude z).magneticInduction
      ((wave.scaleElectricAmplitude z).magneticFieldStrength medium) 0 0 :=
  (wave.scaleElectricAmplitude z).isMacroscopicMaxwellSolution medium
    (hTransverse.scaleElectricAmplitude z)
    ((wave.isDispersionMatched_scaleElectricAmplitude_iff medium z).mpr hDispersion)

end ComplexMonochromaticPlaneWave

end

end ThreeDimension
end Electromagnetism
