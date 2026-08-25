/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.HarmonicFlux.PropagatingModeSynthesis

/-!
# Common-frequency realization of synthesized propagating modes

## i. Overview

This file identifies the local phasor profile of the Maxwell-qualified fields synthesized from a
finite `PropagatingHarmonicModeFamily`. Because complex modal coordinates scale each carrier before
ordinary-real realization, the synthesized electric and magnetic-field-strength fields are
realized from the corresponding coherent phasor sums at the family's common positive frequency.

This is a field-realization result. One-period flux, profile integration, orthogonality,
normalization, and geometric aperture interpretation are separate layers.

## ii. Key results

- `PropagatingHarmonicModeFamily.synthesizedProfile`: the coherent global phasor profile.
- `synthesizedElectricField_eq_realize`: exact electric common-frequency realization.
- `synthesizedMagneticFieldStrength_eq_realize`: exact magnetic common-frequency realization.

## iii. Table of contents

- A. Synthesized phasor profile
- B. Common-frequency realization

## iv. References

This is Physlib-original normalization infrastructure. It introduces no modal completeness,
geometric aperture, interface role, reciprocity, or device-losslessness claim.
-/

@[expose] public section

namespace Optics

open Electromagnetism Electromagnetism.ThreeDimension
open Space Time
open ComplexMonochromaticPlaneWave

noncomputable section

namespace PropagatingHarmonicModeFamily

variable {ι : Type*} [Fintype ι] (family : PropagatingHarmonicModeFamily ι)

private lemma fst_fintypeSum {κ A B : Type*} [Fintype κ]
    [AddCommMonoid A] [AddCommMonoid B] (value : κ → A × B) :
    (∑ i, value i).1 = ∑ i, (value i).1 := by
  classical
  induction (Finset.univ : Finset κ) using Finset.induction_on with
  | empty => simp
  | @insert i index hi ih => simp [Finset.sum_insert hi, ih]

private lemma snd_fintypeSum {κ A B : Type*} [Fintype κ]
    [AddCommMonoid A] [AddCommMonoid B] (value : κ → A × B) :
    (∑ i, value i).2 = ∑ i, (value i).2 := by
  classical
  induction (Finset.univ : Finset κ) using Finset.induction_on with
  | empty => simp
  | @insert i index hi ih => simp [Finset.sum_insert hi, ih]

/-!

## A. Synthesized phasor profile

-/

/-- The coherent global phasor profile synthesized from finite modal coordinates. -/
def synthesizedProfile (amplitude : ModeAmplitude ι) : HarmonicFieldProfile Space :=
  HarmonicFieldProfile.modeSynthesis (family.modeProfile id) amplitude

/-- The synthesized electric phasor is the finite sum of coefficient-scaled mode phasors. -/
lemma synthesizedProfile_electricPhasor (amplitude : ModeAmplitude ι) (x : Space) :
    (family.synthesizedProfile amplitude).electricPhasor x =
      ∑ i, amplitude i • (family.wave i).localElectricPhasor x := by
  classical
  simp [synthesizedProfile, HarmonicFieldProfile.modeSynthesis,
    HarmonicFieldProfile.electricPhasor, modeProfile, fst_fintypeSum]

/-- The synthesized magnetic-field-strength phasor is the matching finite scaled sum. -/
lemma synthesizedProfile_magneticFieldStrengthPhasor
    (amplitude : ModeAmplitude ι) (x : Space) :
    (family.synthesizedProfile amplitude).magneticFieldStrengthPhasor x =
      ∑ i, amplitude i •
        (family.wave i).localMagneticFieldStrengthPhasor family.medium x := by
  classical
  simp [synthesizedProfile, HarmonicFieldProfile.modeSynthesis,
    HarmonicFieldProfile.magneticFieldStrengthPhasor, modeProfile, snd_fintypeSum]

private lemma realizeEuclidean_finsetSum {κ : Type*} (index : Finset κ)
    (phasor : κ → EuclideanSpace ℂ (Fin 3)) (phase : ℝ) :
    Phasor.realizeEuclidean (∑ i ∈ index, phasor i) phase =
      ∑ i ∈ index, Phasor.realizeEuclidean (phasor i) phase := by
  classical
  induction index using Finset.induction_on with
  | empty =>
      ext i
      simp [Phasor.realize]
  | @insert i index hi ih =>
      simp only [Finset.sum_insert hi]
      rw [Phasor.realizeEuclidean_add, ih]

/-!

## B. Common-frequency realization

-/

/-- The synthesized ordinary-real electric field realizes the coherent electric phasor sum at the
common carrier frequency. -/
lemma synthesizedElectricField_eq_realize (amplitude : ModeAmplitude ι)
    (time : ℝ) (x : Space) :
    family.synthesizedElectricField amplitude (time : Time) x =
      Phasor.realizeEuclidean
        ((family.synthesizedProfile amplitude).electricPhasor x)
        (family.angularFrequency * time) := by
  classical
  calc
    _ = ∑ i, (family.scaledWave amplitude i).electricField (time : Time) x := by
      simp [synthesizedElectricField]
    _ = ∑ i, Phasor.realizeEuclidean
        ((family.scaledWave amplitude i).localElectricPhasor x)
        ((family.scaledWave amplitude i).angularFrequency * time) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (family.scaledWave amplitude i).electricField_eq_realize_localElectricPhasor time x
    _ = ∑ i, Phasor.realizeEuclidean
        (amplitude i • (family.wave i).localElectricPhasor x)
        (family.angularFrequency * time) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [family.scaledWave_localElectricPhasor,
        scaledWave, scaleElectricAmplitude_angularFrequency,
        family.commonAngularFrequency i]
    _ = _ := by
      rw [family.synthesizedProfile_electricPhasor]
      exact (realizeEuclidean_finsetSum Finset.univ
        (fun i ↦ amplitude i • (family.wave i).localElectricPhasor x)
        (family.angularFrequency * time)).symm

/-- The synthesized ordinary-real magnetic field strength realizes the matching coherent phasor
sum at the common carrier frequency. -/
lemma synthesizedMagneticFieldStrength_eq_realize (amplitude : ModeAmplitude ι)
    (time : ℝ) (x : Space) :
    family.synthesizedMagneticFieldStrength amplitude (time : Time) x =
      Phasor.realizeEuclidean
        ((family.synthesizedProfile amplitude).magneticFieldStrengthPhasor x)
        (family.angularFrequency * time) := by
  classical
  calc
    _ = ∑ i, (family.scaledWave amplitude i).magneticFieldStrength family.medium
        (time : Time) x := by simp [synthesizedMagneticFieldStrength]
    _ = ∑ i, Phasor.realizeEuclidean
        ((family.scaledWave amplitude i).localMagneticFieldStrengthPhasor family.medium x)
        ((family.scaledWave amplitude i).angularFrequency * time) := by
      apply Finset.sum_congr rfl
      intro i _
      exact magneticFieldStrength_eq_realize_localMagneticFieldStrengthPhasor
        (family.scaledWave amplitude i) family.medium time x
    _ = ∑ i, Phasor.realizeEuclidean
        (amplitude i •
          (family.wave i).localMagneticFieldStrengthPhasor family.medium x)
        (family.angularFrequency * time) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [family.scaledWave_localMagneticFieldStrengthPhasor,
        scaledWave, scaleElectricAmplitude_angularFrequency,
        family.commonAngularFrequency i]
    _ = _ := by
      rw [family.synthesizedProfile_magneticFieldStrengthPhasor]
      exact (realizeEuclidean_finsetSum Finset.univ
        (fun i ↦ amplitude i •
          (family.wave i).localMagneticFieldStrengthPhasor family.medium x)
        (family.angularFrequency * time)).symm

end PropagatingHarmonicModeFamily

end

end Optics
