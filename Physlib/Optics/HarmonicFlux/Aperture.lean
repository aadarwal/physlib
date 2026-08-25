/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.HarmonicFlux.PairingAlgebra

/-!
# Integrated signed normal flux on a measured profile domain

## i. Overview

This file integrates the local Hermitian signed-normal-flux density over an explicitly supplied
measure on a profile-coordinate type. The measure may represent a pulled-back area measure, a
finite-cell quadrature measure, or another declared profile weight. No geometric surface measure
is inferred from the coordinate type.

On integrable profile pairs, the integrated pairing is additive in each profile, complex-linear in
its first profile, and conjugate-linear in its second. Its self-pairing is the complex embedding of
the integral of the existing local time-averaged Poynting normal component. Pairwise integrability
is named explicitly for later finite-mode normalization; a nonintegrable Bochner integral has no
physical power interpretation.

## ii. Key results

- `signedNormalFluxPairing_conj_symm`: integrated Hermitian conjugate symmetry.
- `signedNormalFluxPairing_self`: self-pairing is integrated mean normal Poynting flux.
- `signedNormalFluxPairing_add_left` and `signedNormalFluxPairing_add_right`: integrability-gated
  additivity.
- `signedNormalFluxPairing_smul_left` and `signedNormalFluxPairing_smul_right`: the exact slot
  convention.

## iii. Table of contents

- A. Measured profile integrals
- B. Integrated Hermitian and self-pairing laws
- C. Integrability-qualified sesquilinear laws

## iv. References

This is Physlib-original normalization infrastructure. A supplied measure fixes the integration
convention; the results claim neither a Maxwell mode nor completeness of a finite mode family.
-/

@[expose] public section

namespace Optics

open MeasureTheory Space
open scoped ComplexConjugate

noncomputable section

namespace HarmonicFieldProfile

/-!

## A. Measured profile integrals

-/

/-- The Hermitian signed normal-flux pairing integrated over a specified profile measure. -/
def signedNormalFluxPairing {A : Type*} [MeasurableSpace A] (measure : Measure A)
    (plane : OrientedAffineHyperplane 3) (first second : HarmonicFieldProfile A) : ℂ :=
  ∫ x, signedNormalFluxDensity plane first second x ∂measure

/-- Pairwise integrability of the signed normal-flux density over a specified profile measure. -/
def IsSignedNormalFluxIntegrable {A : Type*} [MeasurableSpace A] (measure : Measure A)
    (plane : OrientedAffineHyperplane 3) (first second : HarmonicFieldProfile A) : Prop :=
  Integrable (fun x ↦ signedNormalFluxDensity plane first second x) measure

/-- The stored-normal component of the local time-averaged Poynting vector. -/
def meanNormalFluxDensity {A : Type*} (plane : OrientedAffineHyperplane 3)
    (profile : HarmonicFieldProfile A) (x : A) : ℝ :=
  plane.normalComponent
    (timeAveragedPoyntingVector (profile.electricPhasor x)
      (profile.magneticFieldStrengthPhasor x))

/-- The time-averaged signed normal flux integrated over a specified profile measure.

Its physical interpretation requires integrability; later normalized-family data supplies that
hypothesis rather than relying on the Bochner integral's nonintegrable default. -/
def integratedMeanNormalFlux {A : Type*} [MeasurableSpace A] (measure : Measure A)
    (plane : OrientedAffineHyperplane 3) (profile : HarmonicFieldProfile A) : ℝ :=
  ∫ x, meanNormalFluxDensity plane profile x ∂measure

/-!

## B. Integrated Hermitian and self-pairing laws

-/

/-- The integrated signed normal-flux pairing is Hermitian under exchange of profiles. -/
lemma signedNormalFluxPairing_conj_symm {A : Type*} [MeasurableSpace A]
    (measure : Measure A) (plane : OrientedAffineHyperplane 3)
    (first second : HarmonicFieldProfile A) :
    signedNormalFluxPairing measure plane first second =
      star (signedNormalFluxPairing measure plane second first) := by
  calc
    signedNormalFluxPairing measure plane first second =
        ∫ x, star (signedNormalFluxDensity plane second first x) ∂measure := by
          apply integral_congr_ae
          filter_upwards [] with x
          exact signedNormalFluxDensity_conj_symm plane first second x
    _ = _ := integral_conj

/-- Integrated self-pairing is the complex embedding of integrated mean normal Poynting flux. -/
lemma signedNormalFluxPairing_self {A : Type*} [MeasurableSpace A]
    (measure : Measure A) (plane : OrientedAffineHyperplane 3)
    (profile : HarmonicFieldProfile A) :
    signedNormalFluxPairing measure plane profile profile =
      (integratedMeanNormalFlux measure plane profile : ℂ) := by
  rw [signedNormalFluxPairing, integratedMeanNormalFlux, ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [] with x
  exact signedNormalFluxDensity_self plane profile x

/-- Pairwise integrability supplies integrability of the corresponding real mean-flux density. -/
lemma integrable_meanNormalFluxDensity_of_self {A : Type*} [MeasurableSpace A]
    {measure : Measure A} {plane : OrientedAffineHyperplane 3}
    {profile : HarmonicFieldProfile A}
    (h : IsSignedNormalFluxIntegrable measure plane profile profile) :
    Integrable (meanNormalFluxDensity plane profile) measure := by
  have hre := h.re
  apply hre.congr
  filter_upwards [] with x
  rw [signedNormalFluxDensity_self]
  rfl

/-!

## C. Integrability-qualified sesquilinear laws

-/

/-- The integrated pairing is additive in its first profile when both summands are integrable. -/
lemma signedNormalFluxPairing_add_left {A : Type*} [MeasurableSpace A]
    (measure : Measure A) (plane : OrientedAffineHyperplane 3)
    (first second third : HarmonicFieldProfile A)
    (hFirst : IsSignedNormalFluxIntegrable measure plane first third)
    (hSecond : IsSignedNormalFluxIntegrable measure plane second third) :
    signedNormalFluxPairing measure plane (first + second) third =
      signedNormalFluxPairing measure plane first third +
        signedNormalFluxPairing measure plane second third := by
  rw [signedNormalFluxPairing]
  simp_rw [signedNormalFluxDensity_add_left]
  exact integral_add hFirst hSecond

/-- The integrated pairing is additive in its second profile when both summands are integrable. -/
lemma signedNormalFluxPairing_add_right {A : Type*} [MeasurableSpace A]
    (measure : Measure A) (plane : OrientedAffineHyperplane 3)
    (first second third : HarmonicFieldProfile A)
    (hSecond : IsSignedNormalFluxIntegrable measure plane first second)
    (hThird : IsSignedNormalFluxIntegrable measure plane first third) :
    signedNormalFluxPairing measure plane first (second + third) =
      signedNormalFluxPairing measure plane first second +
        signedNormalFluxPairing measure plane first third := by
  rw [signedNormalFluxPairing]
  simp_rw [signedNormalFluxDensity_add_right]
  exact integral_add hSecond hThird

/-- The integrated pairing is complex-linear in its first profile. -/
lemma signedNormalFluxPairing_smul_left {A : Type*} [MeasurableSpace A]
    (measure : Measure A) (plane : OrientedAffineHyperplane 3) (z : ℂ)
    (first second : HarmonicFieldProfile A) :
    signedNormalFluxPairing measure plane (z • first) second =
      z * signedNormalFluxPairing measure plane first second := by
  simp_rw [signedNormalFluxPairing, signedNormalFluxDensity_smul_left, ← smul_eq_mul,
    integral_smul]

/-- The integrated pairing is conjugate-linear in its second profile. -/
lemma signedNormalFluxPairing_smul_right {A : Type*} [MeasurableSpace A]
    (measure : Measure A) (plane : OrientedAffineHyperplane 3) (z : ℂ)
    (first second : HarmonicFieldProfile A) :
    signedNormalFluxPairing measure plane first (z • second) =
      star z * signedNormalFluxPairing measure plane first second := by
  calc
    signedNormalFluxPairing measure plane first (z • second) =
        star (signedNormalFluxPairing measure plane (z • second) first) :=
      signedNormalFluxPairing_conj_symm _ _ _ _
    _ = star (z * signedNormalFluxPairing measure plane second first) := by
      rw [signedNormalFluxPairing_smul_left]
    _ = star z * star (signedNormalFluxPairing measure plane second first) :=
      map_mul (starRingEnd ℂ) _ _
    _ = _ := by
      rw [← signedNormalFluxPairing_conj_symm measure plane first second]

end HarmonicFieldProfile

end

end Optics
