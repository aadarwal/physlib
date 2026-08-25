/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.HarmonicFlux.Aperture
public import Physlib.Optics.Mode.Basic

/-!
# Coherent synthesis of finite harmonic field-mode families

## i. Overview

This file synthesizes a harmonic field profile from finitely many supplied profiles and complex
`ModeAmplitude` coordinates. It then expands the measured signed-normal-flux pairing of two
synthesized profiles into the complete double sum of modal cross terms.

The expansion assumes pairwise integrability but no orthogonality or normalization. Keeping every
cross term prevents individual unit normalization from being mistaken for coherent modal
orthogonality. The finite family describes only its synthesis image; no spanning or electromagnetic
modal-completeness claim is made.

## ii. Key results

- `modeSynthesis`: the complex-linear synthesis map from modal coordinates to field profiles.
- `signedNormalFluxDensity_modeSynthesis`: the pointwise double-sum expansion.
- `signedNormalFluxPairing_modeSynthesis`: the integrated coherent cross-term expansion.

## iii. Table of contents

- A. Finite coherent synthesis
- B. Pointwise cross-term expansion
- C. Integrated cross-term expansion

## iv. References

This is Physlib-original bridge infrastructure. It uses the explicitly supplied profile family and
measure and does not assert Maxwell qualification, mode completeness, or physical device
losslessness.
-/

@[expose] public section

namespace Optics

open MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace HarmonicFieldProfile

/-!

## A. Finite coherent synthesis

-/

/-- Coherent synthesis of a finite harmonic field-profile family from complex modal amplitudes. -/
def modeSynthesis {A ι : Type*} [Fintype ι] (modes : ι → HarmonicFieldProfile A) :
    ModeAmplitude ι →ₗ[ℂ] HarmonicFieldProfile A where
  toFun amplitude := ∑ i, amplitude i • modes i
  map_add' := by
    intro first second
    ext x <;> simp [Finset.sum_add_distrib, add_smul]
  map_smul' := by
    intro z amplitude
    ext x <;> simp [Finset.smul_sum, smul_smul]

/-!

## B. Pointwise cross-term expansion

-/

private lemma signedNormalFluxDensity_finsetSum_left {A ι : Type*}
    (plane : Space.OrientedAffineHyperplane 3) (index : Finset ι)
    (profiles : ι → HarmonicFieldProfile A) (second : HarmonicFieldProfile A) (x : A) :
    signedNormalFluxDensity plane (∑ i ∈ index, profiles i) second x =
      ∑ i ∈ index, signedNormalFluxDensity plane (profiles i) second x := by
  classical
  induction index using Finset.induction_on with
  | empty =>
      simp [signedNormalFluxDensity, mixedNormalFluxDensity,
        Electromagnetism.ThreeDimension.ComplexMonochromaticPlaneWave.complexCross,
        ClassicalMechanics.ComplexWaveVector.bilinearDot, crossProduct, Fin.sum_univ_three]
  | @insert i index hi ih =>
      rw [Finset.sum_insert hi, signedNormalFluxDensity_add_left,
        Finset.sum_insert hi, ih]

private lemma signedNormalFluxDensity_finsetSum_right {A ι : Type*}
    (plane : Space.OrientedAffineHyperplane 3) (first : HarmonicFieldProfile A)
    (index : Finset ι) (profiles : ι → HarmonicFieldProfile A) (x : A) :
    signedNormalFluxDensity plane first (∑ i ∈ index, profiles i) x =
      ∑ i ∈ index, signedNormalFluxDensity plane first (profiles i) x := by
  classical
  induction index using Finset.induction_on with
  | empty =>
      simp [signedNormalFluxDensity, mixedNormalFluxDensity,
        Electromagnetism.ThreeDimension.ComplexMonochromaticPlaneWave.complexCross,
        ClassicalMechanics.ComplexWaveVector.bilinearDot, crossProduct, Fin.sum_univ_three]
  | @insert i index hi ih =>
      rw [Finset.sum_insert hi, signedNormalFluxDensity_add_right,
        Finset.sum_insert hi, ih]

/-- The local signed-normal-flux density of two synthesized profiles is the complete double sum
of modal cross terms. -/
lemma signedNormalFluxDensity_modeSynthesis {A ι : Type*} [Fintype ι]
    (plane : Space.OrientedAffineHyperplane 3) (modes : ι → HarmonicFieldProfile A)
    (first second : ModeAmplitude ι) (x : A) :
    signedNormalFluxDensity plane (modeSynthesis modes first)
        (modeSynthesis modes second) x =
      ∑ i, ∑ j, (first i * star (second j)) *
        signedNormalFluxDensity plane (modes i) (modes j) x := by
  classical
  change signedNormalFluxDensity plane (∑ i, first i • modes i)
      (∑ i, second i • modes i) x = _
  rw [signedNormalFluxDensity_finsetSum_left]
  apply Finset.sum_congr rfl
  intro i _
  rw [signedNormalFluxDensity_smul_left,
    signedNormalFluxDensity_finsetSum_right, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [signedNormalFluxDensity_smul_right]
  ring

/-!

## C. Integrated cross-term expansion

-/

/-- The measured signed-normal-flux pairing of synthesized profiles is the complete double sum
of integrated modal cross terms. -/
lemma signedNormalFluxPairing_modeSynthesis {A ι : Type*} [MeasurableSpace A] [Fintype ι]
    (measure : Measure A) (plane : Space.OrientedAffineHyperplane 3)
    (modes : ι → HarmonicFieldProfile A)
    (hIntegrable : ∀ i j, IsSignedNormalFluxIntegrable measure plane (modes i) (modes j))
    (first second : ModeAmplitude ι) :
    signedNormalFluxPairing measure plane (modeSynthesis modes first)
        (modeSynthesis modes second) =
      ∑ i, ∑ j, (first i * star (second j)) *
        signedNormalFluxPairing measure plane (modes i) (modes j) := by
  classical
  rw [signedNormalFluxPairing]
  simp_rw [signedNormalFluxDensity_modeSynthesis]
  rw [integral_finsetSum Finset.univ]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum Finset.univ]
    · apply Finset.sum_congr rfl
      intro j _
      rw [integral_const_mul]
      rfl
    · intro j _
      exact (hIntegrable i j).const_mul (first i * star (second j))
  · intro i _
    apply integrable_finsetSum Finset.univ
    intro j _
    exact (hIntegrable i j).const_mul (first i * star (second j))

end HarmonicFieldProfile

end

end Optics
