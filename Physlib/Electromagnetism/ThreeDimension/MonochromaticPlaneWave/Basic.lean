/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.ClassicalMechanics.WaveEquation.Basic
public import Physlib.Electromagnetism.Media.HomogeneousIsotropic

/-!

# Real monochromatic plane-wave candidates

## i. Overview

This module defines a purely harmonic real plane-wave candidate in three spatial dimensions. Its
positive angular frequency and positive scalar wave number are independent data, while its
propagation sign is carried by a unit `Space.Direction`. Thus the candidate is off shell: it does
not assume a material dispersion relation or satisfy Maxwell equations merely by construction.

Two real electric quadratures represent a general complex electric amplitude. With carrier phase
`θ = ω t - κ ⟪x, n⟫`, the field convention is
`E = cos θ • electricReal - sin θ • electricImag`. This is the real-field convention compatible
with later realization of a complex amplitude through `Re (z * exp (I * θ))`. The data contains no
additive static field and no separate phase offset, since a phase shift can be absorbed by rotating
the two quadratures.

The magnetic induction is the canonical propagating candidate
`B = (κ / ω) • (n × E)`. That relation is part of this construction; this module does not claim to
derive it from Maxwell equations. A supplied homogeneous isotropic medium constructs `D = ε E`
and `H = B / μ`, but transversality and material dispersion remain separate predicates for the
later Maxwell layer.

All fields and carrier parameters use the raw-real fixed-unit convention of
`HomogeneousIsotropicMedium`. The module makes no statement about physical power, handedness,
group velocity, evanescent fields, finite beams, or gauge potentials.

## ii. Key results

- `MonochromaticPlaneWave.electricField_apply`: exact electric carrier realization.
- `MonochromaticPlaneWave.magneticInduction_eq_cross_electricField`: the constructed `B/E`
  relation.
- `MonochromaticPlaneWave.IsTransverse.electricField`: conditional electric transversality.
- `MonochromaticPlaneWave.magneticInduction_transverse`: unconditional magnetic transversality.
- `MonochromaticPlaneWave.electricField_waveEquation`: propagation at the candidate's phase
  velocity.
- `MonochromaticPlaneWave.isConstitutive`: satisfaction of the supplied medium's constitutive
  equations.

## iii. Table of contents

- A. Off-shell harmonic data
- B. Carrier geometry
- C. Exact field formulas
- D. Transversality
- E. Regularity and wave equations
- F. Constitutive fields

## iv. References

-/

@[expose] public section

namespace Electromagnetism
namespace ThreeDimension

open Space Time InnerProductSpace Matrix ClassicalMechanics

/-!

## A. Off-shell harmonic data

-/

/-- Off-shell real data for a three-dimensional monochromatic plane-wave candidate.

The carrier is purely harmonic with independent positive angular frequency and wave number. The
two electric vectors are the real and imaginary parts of a future complex amplitude; neither
transversality nor material dispersion is stored as an invariant. -/
structure MonochromaticPlaneWave where
  /-- The direction of propagation. -/
  direction : Direction 3
  /-- The positive angular frequency. -/
  angularFrequency : ℝ
  /-- The angular frequency is positive. -/
  angularFrequency_pos : 0 < angularFrequency
  /-- The positive scalar wave number. -/
  waveNumber : ℝ
  /-- The scalar wave number is positive. -/
  waveNumber_pos : 0 < waveNumber
  /-- The real part of the complex electric amplitude. -/
  electricReal : EuclideanSpace ℝ (Fin 3)
  /-- The imaginary part of the complex electric amplitude. -/
  electricImag : EuclideanSpace ℝ (Fin 3)

namespace MonochromaticPlaneWave

/-- The Euclidean unit vector in the propagation direction. -/
noncomputable def propagationVector (wave : MonochromaticPlaneWave) :
    EuclideanSpace ℝ (Fin 3) :=
  Space.basis.repr wave.direction.unit

/-- The Euclidean wave vector `κ n`. -/
noncomputable def waveVector (wave : MonochromaticPlaneWave) :
    EuclideanSpace ℝ (Fin 3) :=
  wave.waveNumber • wave.propagationVector

/-- The phase velocity `ω / κ` represented by the off-shell carrier data. -/
noncomputable def phaseVelocity (wave : MonochromaticPlaneWave) : ℝ :=
  wave.angularFrequency / wave.waveNumber

/-- The carrier phase `ω t - κ ⟪x, n⟫`. -/
noncomputable def carrierPhase (wave : MonochromaticPlaneWave)
    (t : Time) (x : Space) : ℝ :=
  wave.angularFrequency * t - wave.waveNumber * ⟪x, wave.direction.unit⟫_ℝ

/-- The real electric profile as a function of the travelling coordinate. -/
noncomputable def electricProfile (wave : MonochromaticPlaneWave) :
    ℝ → EuclideanSpace ℝ (Fin 3) :=
  fun u => Real.cos (-wave.waveNumber * u) • wave.electricReal -
    Real.sin (-wave.waveNumber * u) • wave.electricImag

/-- The real electric field obtained from the harmonic profile. -/
noncomputable def electricField (wave : MonochromaticPlaneWave) : ElectricField :=
  planeWave wave.electricProfile wave.phaseVelocity wave.direction

/-- The real part of the compatible magnetic-induction amplitude. -/
noncomputable def magneticReal (wave : MonochromaticPlaneWave) :
    EuclideanSpace ℝ (Fin 3) :=
  (wave.waveNumber / wave.angularFrequency) •
    (wave.propagationVector ⨯ₑ₃ wave.electricReal)

/-- The imaginary part of the compatible magnetic-induction amplitude. -/
noncomputable def magneticImag (wave : MonochromaticPlaneWave) :
    EuclideanSpace ℝ (Fin 3) :=
  (wave.waveNumber / wave.angularFrequency) •
    (wave.propagationVector ⨯ₑ₃ wave.electricImag)

/-- The real magnetic-induction profile as a function of the travelling coordinate. -/
noncomputable def magneticProfile (wave : MonochromaticPlaneWave) :
    ℝ → EuclideanSpace ℝ (Fin 3) :=
  fun u => Real.cos (-wave.waveNumber * u) • wave.magneticReal -
    Real.sin (-wave.waveNumber * u) • wave.magneticImag

/-- The magnetic induction compatible with the electric carrier by the built-in propagating-wave
relation `B = (κ / ω) n × E`. -/
noncomputable def magneticInduction (wave : MonochromaticPlaneWave) :
    MagneticInductionField :=
  planeWave wave.magneticProfile wave.phaseVelocity wave.direction

/-- The electric displacement supplied by a homogeneous isotropic medium. -/
noncomputable def electricDisplacement (wave : MonochromaticPlaneWave)
    (medium : HomogeneousIsotropicMedium) : ElectricDisplacementField :=
  medium.electricDisplacement wave.electricField

/-- The magnetic field strength supplied by a homogeneous isotropic medium. -/
noncomputable def magneticFieldStrength (wave : MonochromaticPlaneWave)
    (medium : HomogeneousIsotropicMedium) : MagneticFieldStrength :=
  medium.magneticFieldStrength wave.magneticInduction

/-- Both electric quadrature amplitudes are transverse to the propagation direction. -/
def IsTransverse (wave : MonochromaticPlaneWave) : Prop :=
  ⟪wave.propagationVector, wave.electricReal⟫_ℝ = 0 ∧
  ⟪wave.propagationVector, wave.electricImag⟫_ℝ = 0

/-!

## B. Carrier geometry

-/

/-- Positive angular frequency is nonzero. -/
lemma angularFrequency_ne_zero (wave : MonochromaticPlaneWave) :
    wave.angularFrequency ≠ 0 :=
  ne_of_gt wave.angularFrequency_pos

/-- Positive scalar wave number is nonzero. -/
lemma waveNumber_ne_zero (wave : MonochromaticPlaneWave) :
    wave.waveNumber ≠ 0 :=
  ne_of_gt wave.waveNumber_pos

/-- The Euclidean propagation vector has unit norm. -/
lemma propagationVector_norm (wave : MonochromaticPlaneWave) :
    ‖wave.propagationVector‖ = 1 := by
  simp [propagationVector, wave.direction.norm]

/-- The norm of the wave vector is the positive scalar wave number. -/
lemma waveVector_norm (wave : MonochromaticPlaneWave) :
    ‖wave.waveVector‖ = wave.waveNumber := by
  rw [waveVector, norm_smul, wave.propagationVector_norm, mul_one,
    Real.norm_eq_abs, abs_of_pos wave.waveNumber_pos]

/-- The phase velocity is positive. -/
lemma phaseVelocity_pos (wave : MonochromaticPlaneWave) :
    0 < wave.phaseVelocity :=
  div_pos wave.angularFrequency_pos wave.waveNumber_pos

/-- The phase velocity is nonzero. -/
lemma phaseVelocity_ne_zero (wave : MonochromaticPlaneWave) :
    wave.phaseVelocity ≠ 0 :=
  ne_of_gt wave.phaseVelocity_pos

/-- Wave number times phase velocity equals angular frequency. -/
lemma waveNumber_mul_phaseVelocity (wave : MonochromaticPlaneWave) :
    wave.waveNumber * wave.phaseVelocity = wave.angularFrequency := by
  rw [phaseVelocity]
  field_simp [wave.waveNumber_ne_zero]

/-- The carrier phase is the angular-frequency term minus the wave-vector pairing. -/
lemma carrierPhase_eq_waveVector (wave : MonochromaticPlaneWave)
    (t : Time) (x : Space) :
    wave.carrierPhase t x =
      wave.angularFrequency * t - ⟪Space.basis.repr x, wave.waveVector⟫_ℝ := by
  simp [carrierPhase, waveVector, propagationVector, inner_smul_right]

/-- The carrier phase is minus wave number times the travelling coordinate used by
`ClassicalMechanics.planeWave`. -/
lemma carrierPhase_eq_travellingCoordinate (wave : MonochromaticPlaneWave)
    (t : Time) (x : Space) :
    wave.carrierPhase t x =
      -wave.waveNumber * (⟪x, wave.direction.unit⟫_ℝ - wave.phaseVelocity * t) := by
  rw [carrierPhase]
  calc
    wave.angularFrequency * t - wave.waveNumber * ⟪x, wave.direction.unit⟫_ℝ =
        wave.waveNumber * wave.phaseVelocity * t -
          wave.waveNumber * ⟪x, wave.direction.unit⟫_ℝ := by
      rw [wave.waveNumber_mul_phaseVelocity]
    _ = -wave.waveNumber *
        (⟪x, wave.direction.unit⟫_ℝ - wave.phaseVelocity * t) := by ring

/-!

## C. Exact field formulas

-/

/-- Evaluating the electric profile at the travelling coordinate gives the direct carrier
formula. -/
lemma electricProfile_travellingCoordinate (wave : MonochromaticPlaneWave)
    (t : Time) (x : Space) :
    wave.electricProfile
      (⟪x, wave.direction.unit⟫_ℝ - wave.phaseVelocity * t) =
        Real.cos (wave.carrierPhase t x) • wave.electricReal -
          Real.sin (wave.carrierPhase t x) • wave.electricImag := by
  rw [electricProfile, wave.carrierPhase_eq_travellingCoordinate]

/-- The real electric field is the cosine real quadrature minus the sine imaginary quadrature. -/
lemma electricField_apply (wave : MonochromaticPlaneWave) (t : Time) (x : Space) :
    wave.electricField t x =
      Real.cos (wave.carrierPhase t x) • wave.electricReal -
      Real.sin (wave.carrierPhase t x) • wave.electricImag := by
  rw [electricField, planeWave_eq]
  exact wave.electricProfile_travellingCoordinate t x

/-- The magnetic profile is `(κ / ω) n × E` at every travelling coordinate. -/
lemma magneticProfile_eq_cross_electricProfile (wave : MonochromaticPlaneWave) (u : ℝ) :
    wave.magneticProfile u = (wave.waveNumber / wave.angularFrequency) •
      (wave.propagationVector ⨯ₑ₃ wave.electricProfile u) := by
  have hcross : wave.propagationVector ⨯ₑ₃ wave.electricProfile u =
      Real.cos (-wave.waveNumber * u) •
          (wave.propagationVector ⨯ₑ₃ wave.electricReal) -
        Real.sin (-wave.waveNumber * u) •
          (wave.propagationVector ⨯ₑ₃ wave.electricImag) := by
    rw [electricProfile, sub_eq_add_neg, Space.cross_add]
    rw [show -(Real.sin (-wave.waveNumber * u) • wave.electricImag) =
      (-Real.sin (-wave.waveNumber * u)) • wave.electricImag by simp]
    rw [Space.cross_smul, Space.cross_smul]
    simp
  rw [magneticProfile, magneticReal, magneticImag, hcross]
  simp [smul_smul, mul_comm]

/-- The magnetic induction has the same carrier with its compatible magnetic quadratures. -/
lemma magneticInduction_apply (wave : MonochromaticPlaneWave) (t : Time) (x : Space) :
    wave.magneticInduction t x =
      Real.cos (wave.carrierPhase t x) • wave.magneticReal -
      Real.sin (wave.carrierPhase t x) • wave.magneticImag := by
  rw [magneticInduction, planeWave_eq, magneticProfile,
    ← wave.carrierPhase_eq_travellingCoordinate]

/-- The constructed magnetic induction is `(κ / ω)` times propagation direction crossed with the
electric field. This relation is built into the candidate rather than derived from Maxwell
equations. -/
lemma magneticInduction_eq_cross_electricField (wave : MonochromaticPlaneWave)
    (t : Time) (x : Space) :
    wave.magneticInduction t x = (wave.waveNumber / wave.angularFrequency) •
      (wave.propagationVector ⨯ₑ₃ wave.electricField t x) := by
  rw [magneticInduction, electricField, planeWave_eq, planeWave_eq]
  exact wave.magneticProfile_eq_cross_electricProfile _

/-!

## D. Transversality

-/

namespace IsTransverse

/-- Transversality includes the real electric quadrature. -/
lemma electricReal (wave : MonochromaticPlaneWave) (h : wave.IsTransverse) :
    ⟪wave.propagationVector, wave.electricReal⟫_ℝ = 0 :=
  h.1

/-- Transversality includes the imaginary electric quadrature. -/
lemma electricImag (wave : MonochromaticPlaneWave) (h : wave.IsTransverse) :
    ⟪wave.propagationVector, wave.electricImag⟫_ℝ = 0 :=
  h.2

/-- A transverse wave has transverse electric profile at every travelling coordinate. -/
lemma electricProfile (wave : MonochromaticPlaneWave) (h : wave.IsTransverse) (u : ℝ) :
    ⟪wave.propagationVector, wave.electricProfile u⟫_ℝ = 0 := by
  rw [MonochromaticPlaneWave.electricProfile, inner_sub_right,
    inner_smul_right, inner_smul_right, h.1, h.2]
  simp

/-- A transverse wave has pointwise transverse electric field. -/
lemma electricField (wave : MonochromaticPlaneWave) (h : wave.IsTransverse)
    (t : Time) (x : Space) :
    ⟪wave.propagationVector, wave.electricField t x⟫_ℝ = 0 := by
  rw [MonochromaticPlaneWave.electricField, planeWave_eq]
  exact electricProfile wave h _

end IsTransverse

/-- The constructed magnetic induction is transverse for every electric amplitude. -/
lemma magneticInduction_transverse (wave : MonochromaticPlaneWave)
    (t : Time) (x : Space) :
    ⟪wave.propagationVector, wave.magneticInduction t x⟫_ℝ = 0 := by
  rw [wave.magneticInduction_eq_cross_electricField, inner_smul_right,
    Space.inner_self_cross]
  simp

/-!

## E. Regularity and wave equations

-/

/-- The electric profile is differentiable to every finite or infinite order. -/
lemma electricProfile_contDiff (wave : MonochromaticPlaneWave) (n : WithTop ℕ∞) :
    ContDiff ℝ n wave.electricProfile := by
  unfold electricProfile
  fun_prop

/-- The magnetic profile is differentiable to every finite or infinite order. -/
lemma magneticProfile_contDiff (wave : MonochromaticPlaneWave) (n : WithTop ℕ∞) :
    ContDiff ℝ n wave.magneticProfile := by
  unfold magneticProfile
  fun_prop

/-- The electric field is jointly differentiable to every finite or infinite order. -/
lemma electricField_contDiff (wave : MonochromaticPlaneWave) (n : WithTop ℕ∞) :
    ContDiff ℝ n ↿wave.electricField := by
  unfold electricField planeWave electricProfile
  fun_prop

/-- The magnetic induction is jointly differentiable to every finite or infinite order. -/
lemma magneticInduction_contDiff (wave : MonochromaticPlaneWave) (n : WithTop ℕ∞) :
    ContDiff ℝ n ↿wave.magneticInduction := by
  unfold magneticInduction planeWave magneticProfile
  fun_prop

/-- The constitutive electric displacement is jointly differentiable to every order. -/
lemma electricDisplacement_contDiff (wave : MonochromaticPlaneWave)
    (medium : HomogeneousIsotropicMedium) (n : WithTop ℕ∞) :
    ContDiff ℝ n ↿(wave.electricDisplacement medium) :=
  (wave.electricField_contDiff n).const_smul medium.ε

/-- The constitutive magnetic field strength is jointly differentiable to every order. -/
lemma magneticFieldStrength_contDiff (wave : MonochromaticPlaneWave)
    (medium : HomogeneousIsotropicMedium) (n : WithTop ℕ∞) :
    ContDiff ℝ n ↿(wave.magneticFieldStrength medium) :=
  (wave.magneticInduction_contDiff n).const_smul medium.μ⁻¹

/-- The electric field satisfies the classical wave equation at the candidate's phase velocity.
This does not identify that velocity with a material wave speed. -/
lemma electricField_waveEquation (wave : MonochromaticPlaneWave)
    (t : Time) (x : Space) :
    WaveEquation wave.electricField t x wave.phaseVelocity :=
  planeWave_waveEquation wave.phaseVelocity wave.direction wave.electricProfile
    (wave.electricProfile_contDiff 2) t x

/-- The magnetic induction satisfies the classical wave equation at the candidate's phase
velocity. This does not identify that velocity with a material wave speed. -/
lemma magneticInduction_waveEquation (wave : MonochromaticPlaneWave)
    (t : Time) (x : Space) :
    WaveEquation wave.magneticInduction t x wave.phaseVelocity :=
  planeWave_waveEquation wave.phaseVelocity wave.direction wave.magneticProfile
    (wave.magneticProfile_contDiff 2) t x

/-!

## F. Constitutive fields

-/

/-- The canonically constructed `E`, `D`, `B`, and `H` fields satisfy the supplied homogeneous
isotropic medium's constitutive equations. This is not a Maxwell-equation result. -/
lemma isConstitutive (wave : MonochromaticPlaneWave)
    (medium : HomogeneousIsotropicMedium) :
    medium.IsConstitutive wave.electricField (wave.electricDisplacement medium)
      wave.magneticInduction (wave.magneticFieldStrength medium) :=
  medium.isConstitutive_electricDisplacement_magneticFieldStrength
    wave.electricField wave.magneticInduction

end MonochromaticPlaneWave
end ThreeDimension
end Electromagnetism
