/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Electromagnetism.ThreeDimension.MonochromaticPlaneWave.Basic

/-!

# Material dispersion for real monochromatic plane waves

## i. Overview

This module selects the positive-frequency, positive-wave-number material branch of an off-shell
`MonochromaticPlaneWave`. A candidate is dispersion matched to a homogeneous isotropic medium
when `ω = κ v`, where `v` is the medium wave speed. The name describes matching a wave to the
nondispersive material model; it does not claim that the medium itself is frequency dispersive.

The angular-frequency-primary constructor fixes `κ = ω / v`. This choice anticipates planar
interfaces, where a common temporal frequency is preserved while the spatial wave vector changes.
It deliberately permits zero electric amplitude and does not impose transversality.

On a matched carrier, the magnetic induction and field strength obey the propagating-wave ratios
`B = v⁻¹ n × E` and `H = Z⁻¹ n × E`. Maxwell equations remain a separate layer.

## ii. Key results

- `MonochromaticPlaneWave.IsDispersionMatched`: the positive material branch `ω = κ v`.
- `MonochromaticPlaneWave.inMedium`: the angular-frequency-primary matched constructor.
- `MonochromaticPlaneWave.inMedium_isDispersionMatched`: correctness of the constructor.
- `IsDispersionMatched.magneticInduction_eq_waveSpeed_inv_smul_cross_electricField`:
  the on-shell `B/E` ratio.
- `IsDispersionMatched.magneticFieldStrength_eq_waveImpedance_inv_smul_cross_electricField`:
  the on-shell `H/E` ratio.

## iii. Table of contents

- A. Positive-branch dispersion
- B. Canonical fixed-medium carrier
- C. On-shell field ratios

## iv. References

-/

@[expose] public section

namespace Electromagnetism
namespace ThreeDimension
namespace MonochromaticPlaneWave

open Space Time InnerProductSpace Matrix

/-!

## A. Positive-branch dispersion

-/

/-- A monochromatic candidate is dispersion matched to a medium when its positive angular
frequency equals its positive wave number times the material wave speed. -/
def IsDispersionMatched (wave : MonochromaticPlaneWave)
    (medium : HomogeneousIsotropicMedium) : Prop :=
  wave.angularFrequency = wave.waveNumber * medium.waveSpeed

/-- Dispersion matching is equivalent to equality of carrier and material phase velocities. -/
lemma isDispersionMatched_iff_phaseVelocity_eq (wave : MonochromaticPlaneWave)
    (medium : HomogeneousIsotropicMedium) :
    wave.IsDispersionMatched medium ↔ wave.phaseVelocity = medium.waveSpeed := by
  constructor
  · intro h
    rw [phaseVelocity, h]
    field_simp [wave.waveNumber_ne_zero]
  · intro h
    rw [IsDispersionMatched, ← h, wave.waveNumber_mul_phaseVelocity]

/-- Dispersion matching is equivalent to the positive wave-number formula `κ = ω / v`. -/
lemma isDispersionMatched_iff_waveNumber_eq (wave : MonochromaticPlaneWave)
    (medium : HomogeneousIsotropicMedium) :
    wave.IsDispersionMatched medium ↔
      wave.waveNumber = wave.angularFrequency / medium.waveSpeed := by
  rw [IsDispersionMatched]
  constructor
  · intro h
    rw [h]
    field_simp [medium.waveSpeed_ne_zero]
  · intro h
    rw [h]
    field_simp [medium.waveSpeed_ne_zero]

namespace IsDispersionMatched

variable {wave : MonochromaticPlaneWave} {medium : HomogeneousIsotropicMedium}

/-- A dispersion-matched carrier propagates at the material wave speed. -/
lemma phaseVelocity_eq_waveSpeed (h : wave.IsDispersionMatched medium) :
    wave.phaseVelocity = medium.waveSpeed :=
  (isDispersionMatched_iff_phaseVelocity_eq wave medium).mp h

/-- On the positive material branch, `κ / ω = v⁻¹`. -/
lemma waveNumber_div_angularFrequency_eq_waveSpeed_inv
    (h : wave.IsDispersionMatched medium) :
    wave.waveNumber / wave.angularFrequency = medium.waveSpeed⁻¹ := by
  rw [h]
  field_simp [wave.waveNumber_ne_zero, medium.waveSpeed_ne_zero]

/-- Dispersion matching implies the squared relation `κ² = ε μ ω²`. -/
lemma waveNumber_sq (h : wave.IsDispersionMatched medium) :
    wave.waveNumber ^ 2 = medium.ε * medium.μ * wave.angularFrequency ^ 2 := by
  have hsquare := congrArg (fun r : ℝ => r ^ 2) h
  rw [mul_pow, medium.waveSpeed_sq] at hsquare
  field_simp [medium.ε_ne_zero, medium.μ_ne_zero] at hsquare ⊢
  nlinarith

end IsDispersionMatched

/-- The squared material relation recovers dispersion matching because angular frequency, wave
number, and material wave speed are all on their positive branches. -/
lemma isDispersionMatched_of_waveNumber_sq (wave : MonochromaticPlaneWave)
    (medium : HomogeneousIsotropicMedium)
    (h : wave.waveNumber ^ 2 = medium.ε * medium.μ * wave.angularFrequency ^ 2) :
    wave.IsDispersionMatched medium := by
  rw [IsDispersionMatched]
  have hsquare : (wave.waveNumber * medium.waveSpeed) ^ 2 =
      wave.angularFrequency ^ 2 := by
    rw [mul_pow, medium.waveSpeed_sq, h]
    field_simp [medium.ε_ne_zero, medium.μ_ne_zero]
  nlinarith [wave.angularFrequency_pos,
    mul_pos wave.waveNumber_pos medium.waveSpeed_pos]

/-!

## B. Canonical fixed-medium carrier

-/

/-- The monochromatic candidate with prescribed positive angular frequency and the canonical
positive wave number `κ = ω / v` in a homogeneous isotropic medium.

The amplitudes may vanish and need not be transverse. -/
noncomputable def inMedium (medium : HomogeneousIsotropicMedium)
    (direction : Direction 3) (angularFrequency : ℝ) (hω : 0 < angularFrequency)
    (electricReal electricImag : EuclideanSpace ℝ (Fin 3)) : MonochromaticPlaneWave where
  direction := direction
  angularFrequency := angularFrequency
  angularFrequency_pos := hω
  waveNumber := angularFrequency / medium.waveSpeed
  waveNumber_pos := div_pos hω medium.waveSpeed_pos
  electricReal := electricReal
  electricImag := electricImag

/-- The fixed-medium constructor satisfies the positive material dispersion relation. -/
lemma inMedium_isDispersionMatched (medium : HomogeneousIsotropicMedium)
    (direction : Direction 3) (angularFrequency : ℝ) (hω : 0 < angularFrequency)
    (electricReal electricImag : EuclideanSpace ℝ (Fin 3)) :
    IsDispersionMatched
      (inMedium medium direction angularFrequency hω electricReal electricImag) medium := by
  change angularFrequency = (angularFrequency / medium.waveSpeed) * medium.waveSpeed
  field_simp [medium.waveSpeed_ne_zero]

/-- The fixed-medium constructor has phase velocity equal to the material wave speed. -/
lemma inMedium_phaseVelocity_eq_waveSpeed (medium : HomogeneousIsotropicMedium)
    (direction : Direction 3) (angularFrequency : ℝ) (hω : 0 < angularFrequency)
    (electricReal electricImag : EuclideanSpace ℝ (Fin 3)) :
    (inMedium medium direction angularFrequency hω electricReal electricImag).phaseVelocity =
      medium.waveSpeed :=
  IsDispersionMatched.phaseVelocity_eq_waveSpeed
    (inMedium_isDispersionMatched medium direction angularFrequency hω electricReal electricImag)

/-!

## C. On-shell field ratios

-/

namespace IsDispersionMatched

variable {wave : MonochromaticPlaneWave} {medium : HomogeneousIsotropicMedium}

/-- A matched carrier has `B = v⁻¹ n × E`. -/
lemma magneticInduction_eq_waveSpeed_inv_smul_cross_electricField
    (h : wave.IsDispersionMatched medium) (t : Time) (x : Space) :
    wave.magneticInduction t x = medium.waveSpeed⁻¹ •
      (wave.propagationVector ⨯ₑ₃ wave.electricField t x) := by
  rw [wave.magneticInduction_eq_cross_electricField,
    h.waveNumber_div_angularFrequency_eq_waveSpeed_inv]

/-- A matched carrier has `H = Z⁻¹ n × E`. -/
lemma magneticFieldStrength_eq_waveImpedance_inv_smul_cross_electricField
    (h : wave.IsDispersionMatched medium) (t : Time) (x : Space) :
    wave.magneticFieldStrength medium t x = medium.waveImpedance⁻¹ •
      (wave.propagationVector ⨯ₑ₃ wave.electricField t x) := by
  have hcoefficient : medium.μ⁻¹ *
      (wave.waveNumber / wave.angularFrequency) = medium.waveImpedance⁻¹ := by
    rw [h.waveNumber_div_angularFrequency_eq_waveSpeed_inv]
    calc
      medium.μ⁻¹ * medium.waveSpeed⁻¹ =
          (medium.μ * medium.waveSpeed)⁻¹ := by rw [_root_.mul_inv_rev]; ring
      _ = medium.waveImpedance⁻¹ := by rw [medium.μ_mul_waveSpeed]
  rw [magneticFieldStrength, HomogeneousIsotropicMedium.magneticFieldStrength_apply,
    wave.magneticInduction_eq_cross_electricField, smul_smul, hcoefficient]

end IsDispersionMatched

end MonochromaticPlaneWave
end ThreeDimension
end Electromagnetism
