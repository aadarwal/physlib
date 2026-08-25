/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.HarmonicFlux.PropagatingMode

/-!
# Maxwell-qualified synthesis of propagating harmonic modes

## i. Overview

This file gives physical meaning to complex `ModeAmplitude` coordinates for a finite
`PropagatingHarmonicModeFamily`. Each coefficient first scales the stored complex electric
amplitude of its carrier. The resulting ordinary-real electric, displacement, magnetic-induction,
and magnetic-field-strength fields are then added.

Complex coefficient scaling occurs before real-field realization. It is therefore not misstated as
a complex scalar action on ordinary-real fields. Every scaled carrier remains transverse and on
the same material shell, and finite superposition proves that the four synthesized fields solve
the source-free macroscopic Maxwell equations in the common medium.

This file establishes the synthesized physical fields. Their local phasor, one-period flux, and
measured modal-power identities are separate follow-ups.

## ii. Key results

- `PropagatingHarmonicModeFamily.scaledWave`: coefficient-scaled carrier data.
- `scaledWave_localElectricPhasor` and `scaledWave_localMagneticFieldStrengthPhasor`: exact local
  complex scaling.
- `synthesizedElectricField`, `synthesizedElectricDisplacement`,
  `synthesizedMagneticInduction`, and `synthesizedMagneticFieldStrength`: finite real fields.
- `synthesized_isMacroscopicMaxwellSolution`: the full fixed-medium Maxwell endpoint.

## iii. Table of contents

- A. Coefficient-scaled carriers
- B. Synthesized ordinary-real fields
- C. Maxwell qualification of finite synthesis

## iv. References

This is Physlib-original normalization infrastructure. It asserts neither modal completeness nor
a geometric aperture measure, interface role, reciprocity, or device losslessness.
-/

@[expose] public section

namespace Optics

open Electromagnetism Electromagnetism.ThreeDimension
open ClassicalMechanics Space

noncomputable section

namespace PropagatingHarmonicModeFamily

variable {ι : Type*} [Fintype ι] (family : PropagatingHarmonicModeFamily ι)

/-!

## A. Coefficient-scaled carriers

-/

/-- Scale each physical carrier by its complex modal coordinate before real-field realization. -/
def scaledWave (amplitude : ModeAmplitude ι) (i : ι) : ComplexMonochromaticPlaneWave :=
  (family.wave i).scaleElectricAmplitude (amplitude i)

omit [Fintype ι] in
/-- A scaled mode's local electric phasor is its modal coordinate times the stored mode phasor. -/
lemma scaledWave_localElectricPhasor (amplitude : ModeAmplitude ι) (i : ι) (x : Space) :
    (family.scaledWave amplitude i).localElectricPhasor x =
      amplitude i • (family.wave i).localElectricPhasor x := by
  simp only [scaledWave, ComplexMonochromaticPlaneWave.localElectricPhasor,
    ComplexMonochromaticPlaneWave.scaleElectricAmplitude_waveVector,
    ComplexMonochromaticPlaneWave.scaleElectricAmplitude_electricAmplitude, smul_smul]
  rw [mul_comm]

omit [Fintype ι] in
/-- A scaled mode's local magnetic-field-strength phasor has the same modal coordinate. -/
lemma scaledWave_localMagneticFieldStrengthPhasor
    (amplitude : ModeAmplitude ι) (i : ι) (x : Space) :
    (family.scaledWave amplitude i).localMagneticFieldStrengthPhasor family.medium x =
      amplitude i •
        (family.wave i).localMagneticFieldStrengthPhasor family.medium x := by
  simp only [scaledWave, ComplexMonochromaticPlaneWave.localMagneticFieldStrengthPhasor,
    ComplexMonochromaticPlaneWave.scaleElectricAmplitude_waveVector,
    ComplexMonochromaticPlaneWave.scaleElectricAmplitude_magneticAmplitude, smul_smul]
  congr 1
  ring

/-!

## B. Synthesized ordinary-real fields

-/

/-- The ordinary-real electric field synthesized from finite complex modal coordinates. -/
def synthesizedElectricField (amplitude : ModeAmplitude ι) : ElectricField :=
  ∑ i, (family.scaledWave amplitude i).electricField

/-- The electric displacement synthesized from the same scaled carriers. -/
def synthesizedElectricDisplacement (amplitude : ModeAmplitude ι) :
    ElectricDisplacementField :=
  ∑ i, (family.scaledWave amplitude i).electricDisplacement family.medium

/-- The magnetic induction synthesized from the same scaled carriers. -/
def synthesizedMagneticInduction (amplitude : ModeAmplitude ι) : MagneticInductionField :=
  ∑ i, (family.scaledWave amplitude i).magneticInduction

/-- The magnetic field strength synthesized from the same scaled carriers. -/
def synthesizedMagneticFieldStrength (amplitude : ModeAmplitude ι) : MagneticFieldStrength :=
  ∑ i, (family.scaledWave amplitude i).magneticFieldStrength family.medium

/-!

## C. Maxwell qualification of finite synthesis

-/

omit [Fintype ι] in
private lemma finset_isMacroscopicMaxwellSolution (amplitude : ModeAmplitude ι)
    (index : Finset ι) :
    family.medium.IsMacroscopicMaxwellSolution
      (∑ i ∈ index, (family.scaledWave amplitude i).electricField)
      (∑ i ∈ index,
        (family.scaledWave amplitude i).electricDisplacement family.medium)
      (∑ i ∈ index, (family.scaledWave amplitude i).magneticInduction)
      (∑ i ∈ index,
        (family.scaledWave amplitude i).magneticFieldStrength family.medium) 0 0 := by
  classical
  induction index using Finset.induction_on with
  | empty => simp
  | @insert i index hi ih =>
      simp only [Finset.sum_insert hi]
      have hwave : family.medium.IsMacroscopicMaxwellSolution
          (family.scaledWave amplitude i).electricField
          ((family.scaledWave amplitude i).electricDisplacement family.medium)
          (family.scaledWave amplitude i).magneticInduction
          ((family.scaledWave amplitude i).magneticFieldStrength family.medium) 0 0 := by
        simpa only [scaledWave] using
          (family.wave i).isMacroscopicMaxwellSolution_scaleElectricAmplitude
            family.medium (family.isTransverse i) (family.isDispersionMatched i) (amplitude i)
      simpa using hwave.add ih

/-- Finite coherent synthesis of a common-frequency propagating mode family remains an
ordinary-real source-free Maxwell solution in the common medium. -/
lemma synthesized_isMacroscopicMaxwellSolution (amplitude : ModeAmplitude ι) :
    family.medium.IsMacroscopicMaxwellSolution
      (family.synthesizedElectricField amplitude)
      (family.synthesizedElectricDisplacement amplitude)
      (family.synthesizedMagneticInduction amplitude)
      (family.synthesizedMagneticFieldStrength amplitude) 0 0 := by
  simpa [synthesizedElectricField, synthesizedElectricDisplacement,
    synthesizedMagneticInduction, synthesizedMagneticFieldStrength] using
    family.finset_isMacroscopicMaxwellSolution amplitude Finset.univ

end PropagatingHarmonicModeFamily

end

end Optics
