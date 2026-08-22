/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Electromagnetism.ThreeDimension.MonochromaticPlaneWave.Maxwell
public import Physlib.Optics.Polarization.Frame

/-!
# Jones realization of material plane waves

## i. Overview

This file connects an oriented Jones polarization frame to the real material plane-wave and
macroscopic Maxwell APIs. A Jones vector supplies a three-dimensional complex electric phasor;
its real and imaginary quadratures are passed to
`MonochromaticPlaneWave.inMedium`. The positive angular frequency is primary, and the existing
electromagnetic constructor fixes the positive material wave number.

The resulting real electric field is exactly the framed Jones realization at the inherited carrier
phase. Orientation also identifies the magnetic quarter-turn: `B` is the inverse wave speed times
the realization of Jones coordinates `(-J₁, J₀)`, and `H` is the inverse wave impedance times the
same realization.

## ii. Key results

- `JonesVector.toMaterialPlaneWave`: the connected material plane-wave constructor.
- `JonesVector.toMaterialPlaneWave_isTransverse`: automatic electric transversality.
- `JonesVector.toMaterialPlaneWave_electricField`: exact complex-phasor realization.
- `JonesVector.toMaterialPlaneWave_magneticInduction`: oriented `B` realization.
- `JonesVector.toMaterialPlaneWave_magneticFieldStrength`: oriented `H` realization.
- `JonesVector.toMaterialPlaneWave_isMacroscopicMaxwellSolution`: the complete source-free
  material solution.
- `JonesVector.toMaterialPlaneWave_electricField_phaseShift`: coherent global Jones phase is a
  time translation of the real field.

## iii. Table of contents

- A. Material plane-wave construction
- B. Polarization and dispersion
- C. Exact field realization
- D. Maxwell solution

## iv. References

The construction is derived from the imported Physlib polarization-frame and material plane-wave
APIs. It permits the zero Jones vector and reconstructs fields, not a gauge potential. Squared
Jones intensity remains a raw electric-amplitude quantity; this file makes no irradiance, power,
handedness, interface, evanescence, finite-beam, dispersive, conducting, or lossy-material claim.
-/

@[expose] public section

namespace Optics

open Electromagnetism Electromagnetism.ThreeDimension Space Time Matrix InnerProductSpace
open MonochromaticPlaneWave

noncomputable section

namespace JonesVector

/-!

## A. Material plane-wave construction

-/

/-- Construct the positive-branch material plane wave carried by framed Jones electric-amplitude
data.

The medium fixes the wave number through its wave speed. The Jones vector may be zero. -/
def toMaterialPlaneWave (J : JonesVector) (medium : HomogeneousIsotropicMedium)
    {direction : Space.Direction 3} (frame : PolarizationFrame direction)
    (angularFrequency : ℝ) (hω : 0 < angularFrequency) : MonochromaticPlaneWave :=
  MonochromaticPlaneWave.inMedium medium direction angularFrequency hω
    (frame.electricReal J) (frame.electricImag J)

/-- The material Jones wave propagates in the frame's specified direction. -/
@[simp]
lemma toMaterialPlaneWave_direction (J : JonesVector) (medium : HomogeneousIsotropicMedium)
    {direction : Space.Direction 3} (frame : PolarizationFrame direction)
    (angularFrequency : ℝ) (hω : 0 < angularFrequency) :
    (J.toMaterialPlaneWave medium frame angularFrequency hω).direction = direction := rfl

/-- The material Jones wave has the supplied positive angular frequency. -/
@[simp]
lemma toMaterialPlaneWave_angularFrequency (J : JonesVector)
    (medium : HomogeneousIsotropicMedium) {direction : Space.Direction 3}
    (frame : PolarizationFrame direction) (angularFrequency : ℝ)
    (hω : 0 < angularFrequency) :
    (J.toMaterialPlaneWave medium frame angularFrequency hω).angularFrequency =
      angularFrequency := rfl

/-- The material Jones wave number is angular frequency divided by material wave speed. -/
@[simp]
lemma toMaterialPlaneWave_waveNumber (J : JonesVector)
    (medium : HomogeneousIsotropicMedium) {direction : Space.Direction 3}
    (frame : PolarizationFrame direction) (angularFrequency : ℝ)
    (hω : 0 < angularFrequency) :
    (J.toMaterialPlaneWave medium frame angularFrequency hω).waveNumber =
      angularFrequency / medium.waveSpeed := rfl

/-- The material Jones wave uses the real part of the framed spatial phasor as its real electric
quadrature. -/
@[simp]
lemma toMaterialPlaneWave_electricReal (J : JonesVector)
    (medium : HomogeneousIsotropicMedium) {direction : Space.Direction 3}
    (frame : PolarizationFrame direction) (angularFrequency : ℝ)
    (hω : 0 < angularFrequency) :
    (J.toMaterialPlaneWave medium frame angularFrequency hω).electricReal =
      frame.electricReal J := rfl

/-- The material Jones wave uses the imaginary part of the framed spatial phasor as its imaginary
electric quadrature. -/
@[simp]
lemma toMaterialPlaneWave_electricImag (J : JonesVector)
    (medium : HomogeneousIsotropicMedium) {direction : Space.Direction 3}
    (frame : PolarizationFrame direction) (angularFrequency : ℝ)
    (hω : 0 < angularFrequency) :
    (J.toMaterialPlaneWave medium frame angularFrequency hω).electricImag =
      frame.electricImag J := rfl

/-- The material Jones wave's Euclidean propagation vector is the frame propagation vector. -/
@[simp]
lemma toMaterialPlaneWave_propagationVector (J : JonesVector)
    (medium : HomogeneousIsotropicMedium) {direction : Space.Direction 3}
    (frame : PolarizationFrame direction) (angularFrequency : ℝ)
    (hω : 0 < angularFrequency) :
    (J.toMaterialPlaneWave medium frame angularFrequency hω).propagationVector =
      frame.propagationVector := rfl

/-!

## B. Polarization and dispersion

-/

/-- Every material plane wave built from an oriented Jones frame is transverse, including the
zero-amplitude wave. -/
lemma toMaterialPlaneWave_isTransverse (J : JonesVector)
    (medium : HomogeneousIsotropicMedium) {direction : Space.Direction 3}
    (frame : PolarizationFrame direction) (angularFrequency : ℝ)
    (hω : 0 < angularFrequency) :
    (J.toMaterialPlaneWave medium frame angularFrequency hω).IsTransverse := by
  exact ⟨frame.inner_propagationVector_electricReal J,
    frame.inner_propagationVector_electricImag J⟩

private lemma toMaterialPlaneWave_isDispersionMatched (J : JonesVector)
    (medium : HomogeneousIsotropicMedium) {direction : Space.Direction 3}
    (frame : PolarizationFrame direction) (angularFrequency : ℝ)
    (hω : 0 < angularFrequency) :
    (J.toMaterialPlaneWave medium frame angularFrequency hω).IsDispersionMatched medium :=
  MonochromaticPlaneWave.inMedium_isDispersionMatched medium direction angularFrequency hω
    (frame.electricReal J) (frame.electricImag J)

/-!

## C. Exact field realization

-/

/-- The real electric field is exactly the framed Jones phasor realized at the material wave's
carrier phase. -/
lemma toMaterialPlaneWave_electricField (J : JonesVector)
    (medium : HomogeneousIsotropicMedium) {direction : Space.Direction 3}
    (frame : PolarizationFrame direction) (angularFrequency : ℝ)
    (hω : 0 < angularFrequency) (t : Time) (x : Space) :
    (J.toMaterialPlaneWave medium frame angularFrequency hω).electricField t x =
      frame.realizeJones J
        ((J.toMaterialPlaneWave medium frame angularFrequency hω).carrierPhase t x) := by
  rw [MonochromaticPlaneWave.electricField_apply, frame.realizeJones_eq]
  rfl

/-- Advancing time by `phase / angularFrequency` advances the material wave's carrier phase by
`phase`. -/
lemma toMaterialPlaneWave_carrierPhase_timeShift (J : JonesVector)
    (medium : HomogeneousIsotropicMedium) {direction : Space.Direction 3}
    (frame : PolarizationFrame direction) (angularFrequency : ℝ)
    (hω : 0 < angularFrequency) (phase : ℝ) (t : Time) (x : Space) :
    (J.toMaterialPlaneWave medium frame angularFrequency hω).carrierPhase
        (t + ((phase / angularFrequency : ℝ) : Time)) x =
      (J.toMaterialPlaneWave medium frame angularFrequency hω).carrierPhase t x + phase := by
  simp only [MonochromaticPlaneWave.carrierPhase, toMaterialPlaneWave_angularFrequency,
    Time.add_val]
  field_simp [ne_of_gt hω]
  ring

/-- A common Jones phase shift is a time translation of the real material electric field, not an
equality at fixed carrier phase. -/
lemma toMaterialPlaneWave_electricField_phaseShift (J : JonesVector)
    (medium : HomogeneousIsotropicMedium) {direction : Space.Direction 3}
    (frame : PolarizationFrame direction) (angularFrequency : ℝ)
    (hω : 0 < angularFrequency) (phase : ℝ) (t : Time) (x : Space) :
    ((J.phaseShift phase).toMaterialPlaneWave medium frame angularFrequency hω).electricField
        t x =
      (J.toMaterialPlaneWave medium frame angularFrequency hω).electricField
        (t + ((phase / angularFrequency : ℝ) : Time)) x := by
  rw [toMaterialPlaneWave_electricField, toMaterialPlaneWave_electricField,
    frame.realizeJones_phaseShift]
  congr 1
  exact (toMaterialPlaneWave_carrierPhase_timeShift J medium frame angularFrequency hω
    phase t x).symm

/-- The magnetic induction is the inverse material wave speed times the framed realization of
the propagation-cross Jones quarter-turn. -/
lemma toMaterialPlaneWave_magneticInduction (J : JonesVector)
    (medium : HomogeneousIsotropicMedium) {direction : Space.Direction 3}
    (frame : PolarizationFrame direction) (angularFrequency : ℝ)
    (hω : 0 < angularFrequency) (t : Time) (x : Space) :
    (J.toMaterialPlaneWave medium frame angularFrequency hω).magneticInduction t x =
      medium.waveSpeed⁻¹ • frame.realizeJones J.propagationCross
        ((J.toMaterialPlaneWave medium frame angularFrequency hω).carrierPhase t x) := by
  have hfield :=
    IsDispersionMatched.magneticInduction_eq_waveSpeed_inv_smul_cross_electricField
      (J.toMaterialPlaneWave_isDispersionMatched medium frame angularFrequency hω) t x
  rw [hfield,
    J.toMaterialPlaneWave_electricField medium frame angularFrequency hω,
    J.toMaterialPlaneWave_propagationVector medium frame angularFrequency hω,
    frame.realizeJones_propagationCross]

/-- The magnetic field strength is the inverse material wave impedance times the framed
realization of the propagation-cross Jones quarter-turn. -/
lemma toMaterialPlaneWave_magneticFieldStrength (J : JonesVector)
    (medium : HomogeneousIsotropicMedium) {direction : Space.Direction 3}
    (frame : PolarizationFrame direction) (angularFrequency : ℝ)
    (hω : 0 < angularFrequency) (t : Time) (x : Space) :
    (J.toMaterialPlaneWave medium frame angularFrequency hω).magneticFieldStrength medium t x =
      medium.waveImpedance⁻¹ • frame.realizeJones J.propagationCross
        ((J.toMaterialPlaneWave medium frame angularFrequency hω).carrierPhase t x) := by
  have hfield :=
    IsDispersionMatched.magneticFieldStrength_eq_waveImpedance_inv_smul_cross_electricField
      (J.toMaterialPlaneWave_isDispersionMatched medium frame angularFrequency hω) t x
  rw [hfield,
    J.toMaterialPlaneWave_electricField medium frame angularFrequency hω,
    J.toMaterialPlaneWave_propagationVector medium frame angularFrequency hω,
    frame.realizeJones_propagationCross]

/-- A common Jones phase shift is the same time translation of the real material magnetic
induction. -/
lemma toMaterialPlaneWave_magneticInduction_phaseShift (J : JonesVector)
    (medium : HomogeneousIsotropicMedium) {direction : Space.Direction 3}
    (frame : PolarizationFrame direction) (angularFrequency : ℝ)
    (hω : 0 < angularFrequency) (phase : ℝ) (t : Time) (x : Space) :
    ((J.phaseShift phase).toMaterialPlaneWave medium frame angularFrequency hω).magneticInduction
        t x =
      (J.toMaterialPlaneWave medium frame angularFrequency hω).magneticInduction
        (t + ((phase / angularFrequency : ℝ) : Time)) x := by
  rw [toMaterialPlaneWave_magneticInduction, toMaterialPlaneWave_magneticInduction,
    JonesVector.propagationCross_phaseShift, frame.realizeJones_phaseShift]
  congr 2
  exact (toMaterialPlaneWave_carrierPhase_timeShift J medium frame angularFrequency hω
    phase t x).symm

/-- A common Jones phase shift is the same time translation of the real material magnetic field
strength. -/
lemma toMaterialPlaneWave_magneticFieldStrength_phaseShift (J : JonesVector)
    (medium : HomogeneousIsotropicMedium) {direction : Space.Direction 3}
    (frame : PolarizationFrame direction) (angularFrequency : ℝ)
    (hω : 0 < angularFrequency) (phase : ℝ) (t : Time) (x : Space) :
    MonochromaticPlaneWave.magneticFieldStrength
        ((J.phaseShift phase).toMaterialPlaneWave medium frame angularFrequency hω) medium t x =
      MonochromaticPlaneWave.magneticFieldStrength
        (J.toMaterialPlaneWave medium frame angularFrequency hω) medium
          (t + ((phase / angularFrequency : ℝ) : Time)) x := by
  rw [toMaterialPlaneWave_magneticFieldStrength, toMaterialPlaneWave_magneticFieldStrength,
    JonesVector.propagationCross_phaseShift, frame.realizeJones_phaseShift]
  congr 2
  exact (toMaterialPlaneWave_carrierPhase_timeShift J medium frame angularFrequency hω
    phase t x).symm

/-!

## D. Maxwell solution

-/

/-- A material Jones wave is a complete source-free solution of the supplied homogeneous
isotropic medium, connecting Jones data to the constitutive and Maxwell predicates. -/
lemma toMaterialPlaneWave_isMacroscopicMaxwellSolution (J : JonesVector)
    (medium : HomogeneousIsotropicMedium) {direction : Space.Direction 3}
    (frame : PolarizationFrame direction) (angularFrequency : ℝ)
    (hω : 0 < angularFrequency) :
    medium.IsMacroscopicMaxwellSolution
      (J.toMaterialPlaneWave medium frame angularFrequency hω).electricField
      ((J.toMaterialPlaneWave medium frame angularFrequency hω).electricDisplacement medium)
      (J.toMaterialPlaneWave medium frame angularFrequency hω).magneticInduction
      ((J.toMaterialPlaneWave medium frame angularFrequency hω).magneticFieldStrength medium)
      0 0 :=
  MonochromaticPlaneWave.isMacroscopicMaxwellSolution
    (J.toMaterialPlaneWave medium frame angularFrequency hω) medium
    (J.toMaterialPlaneWave_isTransverse medium frame angularFrequency hω)
    (J.toMaterialPlaneWave_isDispersionMatched medium frame angularFrequency hω)

end JonesVector

end

end Optics
