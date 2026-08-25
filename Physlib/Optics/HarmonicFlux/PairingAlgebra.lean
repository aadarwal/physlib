/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.HarmonicFlux.Pairing

/-!
# Sesquilinear algebra of signed normal-flux density

## i. Overview

This file proves the pointwise additivity and scalar laws of the Hermitian signed-normal-flux
density. The convention is complex-linear in the first supplied harmonic field profile and
conjugate-linear in the second.

These laws are pointwise and need no integrability hypothesis. Their measured integral is
additive only when the corresponding integrands are integrable; that qualified layer belongs in
`Aperture`.

## ii. Key results

- `signedNormalFluxDensity_add_left` and `signedNormalFluxDensity_add_right`: pointwise additivity.
- `signedNormalFluxDensity_smul_left`: complex linearity in the first profile.
- `signedNormalFluxDensity_smul_right`: conjugate linearity in the second profile.

## iii. Table of contents

- A. Pointwise additive laws
- B. Pointwise scalar laws

## iv. References

This is Physlib-original algebra around the signed normal-flux density. It supplies no integration,
Maxwell qualification, modal completeness, or power-conservation claim.
-/

@[expose] public section

namespace Optics

open Space
open scoped ComplexConjugate

noncomputable section

namespace HarmonicFieldProfile

/-!

## A. Pointwise additive laws

-/

/-- Signed normal-flux density is additive in its first profile. -/
lemma signedNormalFluxDensity_add_left {A : Type*} (plane : OrientedAffineHyperplane 3)
    (first second third : HarmonicFieldProfile A) (x : A) :
    signedNormalFluxDensity plane (first + second) third x =
      signedNormalFluxDensity plane first third x +
        signedNormalFluxDensity plane second third x := by
  simp [signedNormalFluxDensity, mixedNormalFluxDensity,
    Phasor.conjugateEuclidean_add,
    Electromagnetism.ThreeDimension.ComplexMonochromaticPlaneWave.complexCross_add_left,
    Electromagnetism.ThreeDimension.ComplexMonochromaticPlaneWave.complexCross_add_right,
    ClassicalMechanics.ComplexWaveVector.bilinearDot_add_right]
  ring

/-- Signed normal-flux density is additive in its second profile. -/
lemma signedNormalFluxDensity_add_right {A : Type*} (plane : OrientedAffineHyperplane 3)
    (first second third : HarmonicFieldProfile A) (x : A) :
    signedNormalFluxDensity plane first (second + third) x =
      signedNormalFluxDensity plane first second x +
        signedNormalFluxDensity plane first third x := by
  calc
    signedNormalFluxDensity plane first (second + third) x =
        star (signedNormalFluxDensity plane (second + third) first x) :=
      signedNormalFluxDensity_conj_symm _ _ _ _
    _ = star (signedNormalFluxDensity plane second first x +
        signedNormalFluxDensity plane third first x) := by
      rw [signedNormalFluxDensity_add_left]
    _ = star (signedNormalFluxDensity plane second first x) +
        star (signedNormalFluxDensity plane third first x) :=
      map_add (starRingEnd ℂ) _ _
    _ = _ := by
      rw [← signedNormalFluxDensity_conj_symm plane first second,
        ← signedNormalFluxDensity_conj_symm plane first third]

/-!

## B. Pointwise scalar laws

-/

/-- Signed normal-flux density is complex-linear in its first profile. -/
lemma signedNormalFluxDensity_smul_left {A : Type*} (plane : OrientedAffineHyperplane 3)
    (z : ℂ) (first second : HarmonicFieldProfile A) (x : A) :
    signedNormalFluxDensity plane (z • first) second x =
      z * signedNormalFluxDensity plane first second x := by
  simp [signedNormalFluxDensity, mixedNormalFluxDensity,
    Phasor.conjugateEuclidean_smul,
    Electromagnetism.ThreeDimension.ComplexMonochromaticPlaneWave.complexCross_smul_left,
    Electromagnetism.ThreeDimension.ComplexMonochromaticPlaneWave.complexCross_smul_right,
    ClassicalMechanics.ComplexWaveVector.bilinearDot_smul_right]
  ring

/-- Signed normal-flux density is conjugate-linear in its second profile. -/
lemma signedNormalFluxDensity_smul_right {A : Type*} (plane : OrientedAffineHyperplane 3)
    (z : ℂ) (first second : HarmonicFieldProfile A) (x : A) :
    signedNormalFluxDensity plane first (z • second) x =
      star z * signedNormalFluxDensity plane first second x := by
  calc
    signedNormalFluxDensity plane first (z • second) x =
        star (signedNormalFluxDensity plane (z • second) first x) :=
      signedNormalFluxDensity_conj_symm _ _ _ _
    _ = star (z * signedNormalFluxDensity plane second first x) := by
      rw [signedNormalFluxDensity_smul_left]
    _ = star z * star (signedNormalFluxDensity plane second first x) :=
      map_mul (starRingEnd ℂ) _ _
    _ = _ := by
      rw [← signedNormalFluxDensity_conj_symm plane first second]

end HarmonicFieldProfile

end

end Optics
