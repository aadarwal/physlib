/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.HarmonicFlux.Basic
public import Physlib.SpaceAndTime.Space.OrientedAffineHyperplane

/-!
# Signed normal-flux pairing of harmonic field profiles

## i. Overview

This file defines the local Hermitian signed-normal-flux pairing of two supplied electric- and
magnetic-field-strength phasor profiles. Relative to an oriented plane with stored unit normal
`n`, the convention is linear in the first profile and conjugate-linear in the second:

`(1 / 4) * n dot (E₁ cross conj H₂ + conj E₂ cross H₁)`.

The self-pairing is proved equal, as a complex number with zero imaginary part, to the stored-
normal component of the existing time-averaged Poynting expression. Integration over a specified
measured profile domain and finite-mode normalization are separate later layers. The profile type
does not encode a carrier frequency or Maxwell qualification.

## ii. Key results

- `signedNormalFluxDensity_eq_explicit`: the displayed two-cross-term formula.
- `signedNormalFluxDensity_conj_symm`: Hermitian conjugate symmetry.
- `signedNormalFluxDensity_self`: self-pairing is the local closed mean-normal-flux expression.

## iii. Table of contents

- A. Harmonic field profiles
- B. Mixed and Hermitian normal-flux densities
- C. Self-pairing and time-averaged Poynting flux

## iv. References

This is Physlib-original infrastructure around the existing peak-phasor Poynting convention. It
does not formalize a result from the audited HOL optics corpus. The profiles are supplied data:
this file proves no Maxwell qualification, modal completeness, or power conservation. Unguarded
convention statement (review only): it assigns the profiles no wave role.
-/

@[expose] public section

namespace Optics

open ClassicalMechanics Electromagnetism.ThreeDimension InnerProductSpace Space
open scoped ComplexConjugate

noncomputable section

/-!

## A. Harmonic field profiles

-/

/-- Local electric and magnetic-field-strength phasors over a profile-coordinate type.

The coordinate type may later carry a measured aperture or waveguide cross-section. Common
frequency is part of the interpretation of a supplied family, not stored as a redundant scalar
in every local profile value. -/
abbrev HarmonicFieldProfile (A : Type*) :=
  A → EuclideanSpace ℂ (Fin 3) × EuclideanSpace ℂ (Fin 3)

namespace HarmonicFieldProfile

/-- The local electric phasor of a harmonic field profile. -/
def electricPhasor {A : Type*} (profile : HarmonicFieldProfile A) (x : A) :
    EuclideanSpace ℂ (Fin 3) :=
  (profile x).1

/-- The local magnetic-field-strength phasor of a harmonic field profile. -/
def magneticFieldStrengthPhasor {A : Type*} (profile : HarmonicFieldProfile A) (x : A) :
    EuclideanSpace ℂ (Fin 3) :=
  (profile x).2

@[simp]
lemma electricPhasor_zero {A : Type*} (x : A) :
    (0 : HarmonicFieldProfile A).electricPhasor x = 0 := rfl

@[simp]
lemma magneticFieldStrengthPhasor_zero {A : Type*} (x : A) :
    (0 : HarmonicFieldProfile A).magneticFieldStrengthPhasor x = 0 := rfl

@[simp]
lemma electricPhasor_add {A : Type*} (first second : HarmonicFieldProfile A) (x : A) :
    (first + second).electricPhasor x =
      first.electricPhasor x + second.electricPhasor x := rfl

@[simp]
lemma magneticFieldStrengthPhasor_add {A : Type*}
    (first second : HarmonicFieldProfile A) (x : A) :
    (first + second).magneticFieldStrengthPhasor x =
      first.magneticFieldStrengthPhasor x + second.magneticFieldStrengthPhasor x := rfl

@[simp]
lemma electricPhasor_smul {A : Type*} (z : ℂ) (profile : HarmonicFieldProfile A) (x : A) :
    (z • profile).electricPhasor x = z • profile.electricPhasor x := rfl

@[simp]
lemma magneticFieldStrengthPhasor_smul {A : Type*} (z : ℂ)
    (profile : HarmonicFieldProfile A) (x : A) :
    (z • profile).magneticFieldStrengthPhasor x =
      z • profile.magneticFieldStrengthPhasor x := rfl

/-!

## B. Mixed and Hermitian normal-flux densities

-/

/-- The ordered mixed normal-flux density from the first electric phasor and the second
magnetic-field-strength phasor.

This one-sided complex quantity is an algebraic ingredient, not by itself a real power density.
-/
def mixedNormalFluxDensity {A : Type*} (plane : OrientedAffineHyperplane 3)
    (first second : HarmonicFieldProfile A) (x : A) : ℂ :=
  ComplexWaveVector.bilinearDot (ComplexWaveVector.ofReal plane.normalVector)
    (ComplexMonochromaticPlaneWave.complexCross (first.electricPhasor x)
      (Phasor.conjugateEuclidean (second.magneticFieldStrengthPhasor x)))

/-- The Hermitian signed normal-flux density, linear in the first profile and conjugate-linear in
the second profile. -/
def signedNormalFluxDensity {A : Type*} (plane : OrientedAffineHyperplane 3)
    (first second : HarmonicFieldProfile A) (x : A) : ℂ :=
  (1 / 4 : ℂ) *
    (mixedNormalFluxDensity plane first second x +
      star (mixedNormalFluxDensity plane second first x))

/-- The Hermitian signed normal-flux density has the explicit two-cross-term form. -/
lemma signedNormalFluxDensity_eq_explicit {A : Type*}
    (plane : OrientedAffineHyperplane 3) (first second : HarmonicFieldProfile A) (x : A) :
    signedNormalFluxDensity plane first second x =
      (1 / 4 : ℂ) *
        (ComplexWaveVector.bilinearDot (ComplexWaveVector.ofReal plane.normalVector)
            (ComplexMonochromaticPlaneWave.complexCross (first.electricPhasor x)
              (Phasor.conjugateEuclidean (second.magneticFieldStrengthPhasor x))) +
          ComplexWaveVector.bilinearDot (ComplexWaveVector.ofReal plane.normalVector)
            (ComplexMonochromaticPlaneWave.complexCross
              (Phasor.conjugateEuclidean (second.electricPhasor x))
              (first.magneticFieldStrengthPhasor x))) := by
  unfold signedNormalFluxDensity mixedNormalFluxDensity
  rw [← ComplexWaveVector.bilinearDot_ofReal_conjugateEuclidean,
    Phasor.conjugateEuclidean_complexCross,
    Phasor.conjugateEuclidean_conjugateEuclidean]

/-- The signed normal-flux density is Hermitian under exchange of its two profiles. -/
lemma signedNormalFluxDensity_conj_symm {A : Type*}
    (plane : OrientedAffineHyperplane 3) (first second : HarmonicFieldProfile A) (x : A) :
    signedNormalFluxDensity plane first second x =
      star (signedNormalFluxDensity plane second first x) := by
  simp [signedNormalFluxDensity]
  ring

/-!

## C. Self-pairing and time-averaged Poynting flux

-/

/-- A profile's self-pairing is the real stored-normal component of its local time-averaged
Poynting vector, embedded in the complex numbers. -/
lemma signedNormalFluxDensity_self {A : Type*} (plane : OrientedAffineHyperplane 3)
    (profile : HarmonicFieldProfile A) (x : A) :
    signedNormalFluxDensity plane profile profile x =
      (plane.normalComponent
        (timeAveragedPoyntingVector (profile.electricPhasor x)
          (profile.magneticFieldStrengthPhasor x)) : ℂ) := by
  have hnormal :
      plane.normalComponent
          (timeAveragedPoyntingVector (profile.electricPhasor x)
            (profile.magneticFieldStrengthPhasor x)) =
        (1 / 2 : ℝ) * (mixedNormalFluxDensity plane profile profile x).re := by
    rw [timeAveragedPoyntingVector, OrientedAffineHyperplane.normalComponent,
      inner_smul_right, ComplexWaveVector.inner_realPart_eq_bilinearDot_re]
    rfl
  rw [hnormal]
  unfold signedNormalFluxDensity
  apply Complex.ext
  · simp
    ring
  · simp

end HarmonicFieldProfile

end

end Optics
