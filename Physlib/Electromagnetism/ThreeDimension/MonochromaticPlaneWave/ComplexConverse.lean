/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Electromagnetism.ThreeDimension.MonochromaticPlaneWave.ComplexMaxwell

/-!
# Maxwell converses for complex-amplitude plane waves

## i. Overview

This module proves converses from the ordinary real Maxwell fields of a
`ComplexMonochromaticPlaneWave` back to its complex calculation data. Gauss's electric law forces
the electric amplitude to be transverse under the complex-bilinear pairing. The source-free
Ampere--Maxwell law then forces the complex material shell whenever the electric amplitude is
nonzero.

The nonzero hypothesis is necessary only for recovering dispersion. If the electric amplitude
vanishes, all four constructed fields vanish and solve the source-free Maxwell equations for every
positive frequency and every complex wave vector. Transversality still holds in that degenerate
case.

The proofs recover complex amplitude equations by sampling the ordinary real carrier at a fixed
spatial point at time zero and one quarter-period. Because the spatial factor never vanishes,
those two real equations determine the real and imaginary parts. No Fourier uniqueness,
propagation branch, or attenuation restriction is used.

These converses characterize only the plane-wave candidate family defined in `ComplexBasic`.
They are not a completeness theorem for arbitrary Maxwell fields and make no interface, outgoing,
evanescent-wave, power, potential, or gauge claim.

## ii. Key results

- `ComplexMonochromaticPlaneWave.isTransverse_of_isSourceFreeMacroscopicMaxwell`: Gauss's law
  forces complex-bilinear transversality.
- `ComplexMonochromaticPlaneWave.isSourceFreeMacroscopicMaxwell_of_electricAmplitude_eq_zero`:
  the zero-amplitude degeneracy.
- `ComplexMonochromaticPlaneWave.isDispersionMatched_of_isSourceFreeMacroscopicMaxwell`: a
  nonzero Maxwell candidate lies on the complex material shell.
- `ComplexMonochromaticPlaneWave.isSourceFreeMacroscopicMaxwell_iff`: the guarded
  characterization.

## iii. Table of contents

- A. Carrier sampling
- B. Transversality converse
- C. Dispersion converse
- D. Characterization

## iv. References

This file combines the complex-carrier, calculus, dispersion, and macroscopic-Maxwell APIs already
present in Physlib. No external formal-development source is copied or translated here.
-/

@[expose] public section

namespace Electromagnetism
namespace ThreeDimension

open Space Time ClassicalMechanics

noncomputable section

namespace ComplexMonochromaticPlaneWave

/-!

## A. Carrier sampling

-/

/-- One quarter of the positive carrier period. -/
private def quarterPeriod (wave : ComplexMonochromaticPlaneWave) : Time :=
  (Real.pi / (2 * wave.angularFrequency) : ℝ)

private lemma carrier_quarterPeriod (wave : ComplexMonochromaticPlaneWave) (x : Space) :
    wave.carrier (quarterPeriod wave) x =
      Complex.I * wave.carrier 0 x := by
  unfold quarterPeriod
  rw [carrier, carrier]
  have hphase : wave.angularFrequency *
      (Real.pi / (2 * wave.angularFrequency)) = Real.pi / 2 := by
    field_simp [wave.angularFrequency_ne_zero]
  rw [hphase]
  norm_num

private lemma complex_eq_zero_of_carrier_re_eq_zero
    (wave : ComplexMonochromaticPlaneWave) (x : Space) (z : ℂ)
    (h : ∀ t : Time, (wave.carrier t x * z).re = 0) : z = 0 := by
  have hzero := h 0
  have hquarter := h (quarterPeriod wave)
  rw [wave.carrier_quarterPeriod] at hquarter
  have himProduct : (wave.carrier 0 x * z).im = 0 := by
    have hneg : -(wave.carrier 0 x * z).im = 0 := by
      simpa [Complex.mul_re, mul_assoc] using hquarter
    exact neg_eq_zero.mp hneg
  have hproduct : wave.carrier 0 x * z = 0 := Complex.ext hzero himProduct
  exact (mul_eq_zero.mp hproduct).resolve_left (wave.carrier_ne_zero 0 x)

/-!

## B. Transversality converse

-/

/-- Source-free Maxwell equations force complex-bilinear electric transversality. No nonzero
electric-amplitude hypothesis is needed. -/
lemma isTransverse_of_isSourceFreeMacroscopicMaxwell
    (wave : ComplexMonochromaticPlaneWave) (medium : HomogeneousIsotropicMedium)
    (hMaxwell : IsSourceFreeMacroscopicMaxwell wave.electricField
      (wave.electricDisplacement medium) wave.magneticInduction
      (wave.magneticFieldStrength medium)) :
    wave.IsTransverse := by
  unfold IsTransverse
  have hscaled : -Complex.I *
      ComplexWaveVector.bilinearDot wave.waveVector wave.electricAmplitude = 0 := by
    apply complex_eq_zero_of_carrier_re_eq_zero wave (0 : Space)
    intro t
    have hGauss := hMaxwell.gaussLawElectric t (0 : Space)
    rw [wave.electricDisplacement_div] at hGauss
    have hre := (mul_eq_zero.mp hGauss).resolve_left medium.ε_ne_zero
    simpa [mul_assoc, mul_comm, mul_left_comm] using hre
  exact (mul_eq_zero.mp hscaled).resolve_left (by norm_num)

/-!

## C. Dispersion converse

-/

private lemma ampereAmplitude_of_isSourceFreeMacroscopicMaxwell
    (wave : ComplexMonochromaticPlaneWave) (medium : HomogeneousIsotropicMedium)
    (hMaxwell : IsSourceFreeMacroscopicMaxwell wave.electricField
      (wave.electricDisplacement medium) wave.magneticInduction
      (wave.magneticFieldStrength medium)) :
    ((medium.μ⁻¹ : ℝ) : ℂ) •
        ((-Complex.I) • complexCross wave.waveVector wave.magneticAmplitude) =
      (medium.ε : ℂ) •
        ((Complex.I * (wave.angularFrequency : ℂ)) • wave.electricAmplitude) := by
  ext i
  apply sub_eq_zero.mp
  apply complex_eq_zero_of_carrier_re_eq_zero wave (0 : Space)
  intro t
  have hAmpere := hMaxwell.ampereMaxwellLaw t (0 : Space)
  rw [wave.magneticFieldStrength_curl,
    wave.electricDisplacement_timeDeriv] at hAmpere
  have hi := congrArg (fun v : EuclideanSpace ℝ (Fin 3) ↦ v i) hAmpere
  simp [realFieldOfAmplitude_apply] at hi ⊢
  linear_combination hi

private lemma waveVector_cross_magneticAmplitude_of_isSourceFreeMacroscopicMaxwell
    (wave : ComplexMonochromaticPlaneWave) (medium : HomogeneousIsotropicMedium)
    (hMaxwell : IsSourceFreeMacroscopicMaxwell wave.electricField
      (wave.electricDisplacement medium) wave.magneticInduction
      (wave.magneticFieldStrength medium)) :
    complexCross wave.waveVector wave.magneticAmplitude =
      -((medium.ε * medium.μ * wave.angularFrequency : ℝ) : ℂ) •
        wave.electricAmplitude := by
  have hAmplitude :=
    ampereAmplitude_of_isSourceFreeMacroscopicMaxwell wave medium hMaxwell
  ext i
  have hi := congrArg (fun v : EuclideanSpace ℂ (Fin 3) ↦ v i) hAmplitude
  simp only [PiLp.smul_apply, smul_eq_mul] at hi ⊢
  push_cast at hi ⊢
  field_simp [medium.μ_ne_zero] at hi
  linear_combination -hi

/-- If the electric amplitude vanishes, the canonical ordinary real fields solve the source-free
Maxwell equations for every positive frequency and complex wave vector. -/
lemma isSourceFreeMacroscopicMaxwell_of_electricAmplitude_eq_zero
    (wave : ComplexMonochromaticPlaneWave) (medium : HomogeneousIsotropicMedium)
    (hZero : wave.electricAmplitude = 0) :
    IsSourceFreeMacroscopicMaxwell wave.electricField
      (wave.electricDisplacement medium) wave.magneticInduction
      (wave.magneticFieldStrength medium) := by
  have hE : wave.electricField = 0 := by
    ext t x i
    simp [electricField_apply, hZero]
  have hAmplitude : wave.magneticAmplitude = 0 := by
    rw [magneticAmplitude, hZero]
    ext i
    fin_cases i <;> simp [complexCross, crossProduct]
  have hB : wave.magneticInduction = 0 := by
    ext t x i
    simp [magneticInduction_apply, hAmplitude]
  simp [electricDisplacement, magneticFieldStrength, hE, hB]

/-- A source-free Maxwell candidate with nonzero electric amplitude satisfies the
complex-bilinear material dispersion relation. -/
lemma isDispersionMatched_of_isSourceFreeMacroscopicMaxwell
    (wave : ComplexMonochromaticPlaneWave) (medium : HomogeneousIsotropicMedium)
    (hMaxwell : IsSourceFreeMacroscopicMaxwell wave.electricField
      (wave.electricDisplacement medium) wave.magneticInduction
      (wave.magneticFieldStrength medium))
    (hNonzero : wave.electricAmplitude ≠ 0) :
    wave.IsDispersionMatched medium := by
  have hTransverse :=
    wave.isTransverse_of_isSourceFreeMacroscopicMaxwell medium hMaxwell
  exact wave.isDispersionMatched_of_waveVector_cross_magneticAmplitude medium hTransverse
    (waveVector_cross_magneticAmplitude_of_isSourceFreeMacroscopicMaxwell wave medium hMaxwell)
    hNonzero

/-!

## D. Characterization

-/

/-- For a candidate with nonzero electric amplitude, the canonical ordinary real fields solve
the source-free Maxwell equations exactly when the amplitude is bilinearly transverse and the
carrier lies on the complex material shell. -/
lemma isSourceFreeMacroscopicMaxwell_iff
    (wave : ComplexMonochromaticPlaneWave) (medium : HomogeneousIsotropicMedium)
    (hNonzero : wave.electricAmplitude ≠ 0) :
    IsSourceFreeMacroscopicMaxwell wave.electricField
        (wave.electricDisplacement medium) wave.magneticInduction
        (wave.magneticFieldStrength medium) ↔
      wave.IsTransverse ∧ wave.IsDispersionMatched medium := by
  constructor
  · intro hMaxwell
    exact ⟨wave.isTransverse_of_isSourceFreeMacroscopicMaxwell medium hMaxwell,
      wave.isDispersionMatched_of_isSourceFreeMacroscopicMaxwell medium hMaxwell hNonzero⟩
  · rintro ⟨hTransverse, hDispersion⟩
    exact wave.isSourceFreeMacroscopicMaxwell medium hTransverse hDispersion

end ComplexMonochromaticPlaneWave
end
end ThreeDimension
end Electromagnetism
