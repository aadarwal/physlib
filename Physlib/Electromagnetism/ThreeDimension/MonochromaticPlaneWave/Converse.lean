/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Electromagnetism.ThreeDimension.MonochromaticPlaneWave.Maxwell

/-!

# Maxwell converses for real monochromatic plane waves

## i. Overview

This module proves converses to the forward monochromatic Maxwell construction. Gauss's electric
law forces both electric quadratures to be transverse, without any nonzero-amplitude assumption.
The Ampère--Maxwell law additionally forces the positive material dispersion relation whenever at
least one electric quadrature is nonzero.

The nonzero hypothesis is necessary only for recovering dispersion. If both electric quadratures
vanish, then all four constructed fields vanish and solve the source-free Maxwell equations for
every positive angular frequency and wave number. Transversality still holds in that degenerate
case.

The proofs isolate the quadratures at two explicit travelling-profile coordinates. They do not use
Fourier uniqueness or assume linear independence of the two amplitudes. These converses concern
only the purely harmonic family defined in `MonochromaticPlaneWave.Basic`; they are not a
completeness theorem for arbitrary Maxwell fields.

## ii. Key results

- `MonochromaticPlaneWave.isTransverse_of_isSourceFreeMacroscopicMaxwell`: Maxwell forces
  transversality.
- `MonochromaticPlaneWave.isSourceFreeMacroscopicMaxwell_of_electricQuadratures_eq_zero`: the
  zero-amplitude degeneracy.
- `MonochromaticPlaneWave.isDispersionMatched_of_isSourceFreeMacroscopicMaxwell`: a nonzero
  Maxwell carrier is dispersion matched.
- `MonochromaticPlaneWave.isSourceFreeMacroscopicMaxwell_iff`: characterization of nonzero
  candidates by transversality and dispersion.

## iii. Table of contents

- A. Carrier sampling
- B. Transversality converse
- C. Dispersion converse
- D. Characterization

## iv. References

-/

@[expose] public section

namespace Electromagnetism
namespace ThreeDimension
namespace MonochromaticPlaneWave

open Space Time InnerProductSpace Matrix

/-!

## A. Carrier sampling

-/

private lemma travellingCoordinate_direction_smul (wave : MonochromaticPlaneWave) (u : ℝ) :
    ⟪u • wave.direction.unit, wave.direction.unit⟫_ℝ -
      wave.phaseVelocity * (0 : Time) = u := by
  rw [inner_smul_left, real_inner_self_eq_norm_sq, wave.direction.norm]
  simp

private lemma electricProfile_fderiv_zero (wave : MonochromaticPlaneWave) :
    fderiv ℝ wave.electricProfile 0 1 = wave.waveNumber • wave.electricImag := by
  rw [wave.electricProfile_fderiv]
  simp

private lemma electricProfile_fderiv_real_sample (wave : MonochromaticPlaneWave) :
    fderiv ℝ wave.electricProfile (-Real.pi / (2 * wave.waveNumber)) 1 =
      wave.waveNumber • wave.electricReal := by
  rw [wave.electricProfile_fderiv]
  have hphase : -wave.waveNumber * (-Real.pi / (2 * wave.waveNumber)) =
      Real.pi / 2 := by
    field_simp [wave.waveNumber_ne_zero]
  rw [hphase, Real.sin_pi_div_two, Real.cos_pi_div_two]
  simp

private lemma electricProfile_fderiv_transverse_of_maxwell
    (wave : MonochromaticPlaneWave) (medium : HomogeneousIsotropicMedium)
    (hMaxwell : IsSourceFreeMacroscopicMaxwell wave.electricField
      (wave.electricDisplacement medium) wave.magneticInduction
      (wave.magneticFieldStrength medium)) (u : ℝ) :
    ⟪wave.propagationVector, fderiv ℝ wave.electricProfile u 1⟫_ℝ = 0 := by
  have hGauss := hMaxwell.gaussLawElectric (0 : Time) (u • wave.direction.unit)
  rw [wave.electricDisplacement_div medium,
    wave.travellingCoordinate_direction_smul] at hGauss
  exact (mul_eq_zero.mp hGauss).resolve_left medium.ε_ne_zero

/-!

## B. Transversality converse

-/

/-- Source-free Maxwell equations force both electric quadratures of the purely harmonic
candidate to be transverse. No nonzero-amplitude hypothesis is needed. -/
lemma isTransverse_of_isSourceFreeMacroscopicMaxwell (wave : MonochromaticPlaneWave)
    (medium : HomogeneousIsotropicMedium)
    (hMaxwell : IsSourceFreeMacroscopicMaxwell wave.electricField
      (wave.electricDisplacement medium) wave.magneticInduction
      (wave.magneticFieldStrength medium)) :
    wave.IsTransverse := by
  constructor
  · have hreal := electricProfile_fderiv_transverse_of_maxwell wave medium hMaxwell
      (-Real.pi / (2 * wave.waveNumber))
    rw [wave.electricProfile_fderiv_real_sample, inner_smul_right] at hreal
    exact (mul_eq_zero.mp hreal).resolve_left wave.waveNumber_ne_zero
  · have himag := electricProfile_fderiv_transverse_of_maxwell wave medium hMaxwell 0
    rw [wave.electricProfile_fderiv_zero, inner_smul_right] at himag
    exact (mul_eq_zero.mp himag).resolve_left wave.waveNumber_ne_zero

/-!

## C. Dispersion converse

-/

private lemma ampereCoefficient_of_maxwell (wave : MonochromaticPlaneWave)
    (medium : HomogeneousIsotropicMedium)
    (hMaxwell : IsSourceFreeMacroscopicMaxwell wave.electricField
      (wave.electricDisplacement medium) wave.magneticInduction
      (wave.magneticFieldStrength medium)) (u : ℝ)
    (hprofile : fderiv ℝ wave.electricProfile u 1 ≠ 0) :
    medium.μ⁻¹ * (wave.waveNumber / wave.angularFrequency) =
      medium.ε * wave.phaseVelocity := by
  have hTransverse := wave.isTransverse_of_isSourceFreeMacroscopicMaxwell medium hMaxwell
  have hprofileTransverse := hTransverse.electricProfile_fderiv wave u
  have hAmpere := hMaxwell.ampereMaxwellLaw (0 : Time) (u • wave.direction.unit)
  rw [wave.magneticFieldStrength_curl, wave.electricDisplacement_timeDeriv,
    wave.travellingCoordinate_direction_smul,
    wave.magneticProfile_fderiv_eq_cross_electricProfile_fderiv,
    Space.cross_smul,
    wave.propagationVector_cross_cross _ hprofileTransverse] at hAmpere
  simp only [smul_neg, smul_smul, neg_smul] at hAmpere
  exact smul_left_injective ℝ hprofile (neg_inj.mp hAmpere)

private lemma waveNumber_sq_of_magneticCoefficient_eq (wave : MonochromaticPlaneWave)
    (medium : HomogeneousIsotropicMedium)
    (h : medium.μ⁻¹ * (wave.waveNumber / wave.angularFrequency) =
      medium.ε * wave.phaseVelocity) :
    wave.waveNumber ^ 2 = medium.ε * medium.μ * wave.angularFrequency ^ 2 := by
  rw [phaseVelocity] at h
  field_simp [medium.μ_ne_zero, wave.angularFrequency_ne_zero,
    wave.waveNumber_ne_zero] at h
  nlinarith

private lemma electricProfile_fderiv_zero_ne_of_electricImag_ne
    (wave : MonochromaticPlaneWave) (h : wave.electricImag ≠ 0) :
    fderiv ℝ wave.electricProfile 0 1 ≠ 0 := by
  rw [wave.electricProfile_fderiv_zero]
  exact smul_ne_zero wave.waveNumber_ne_zero h

private lemma electricProfile_fderiv_real_sample_ne_of_electricReal_ne
    (wave : MonochromaticPlaneWave) (h : wave.electricReal ≠ 0) :
    fderiv ℝ wave.electricProfile (-Real.pi / (2 * wave.waveNumber)) 1 ≠ 0 := by
  rw [wave.electricProfile_fderiv_real_sample]
  exact smul_ne_zero wave.waveNumber_ne_zero h

/-- If both electric quadratures vanish, the canonical fields solve the source-free Maxwell
equations for arbitrary positive carrier frequency and wave number. -/
lemma isSourceFreeMacroscopicMaxwell_of_electricQuadratures_eq_zero
    (wave : MonochromaticPlaneWave) (medium : HomogeneousIsotropicMedium)
    (hReal : wave.electricReal = 0) (hImag : wave.electricImag = 0) :
    IsSourceFreeMacroscopicMaxwell wave.electricField
      (wave.electricDisplacement medium) wave.magneticInduction
      (wave.magneticFieldStrength medium) := by
  have hE : wave.electricField = 0 := by
    ext t x
    rw [wave.electricField_apply, hReal, hImag]
    simp
  have hB : wave.magneticInduction = 0 := by
    ext t x
    rw [wave.magneticInduction_eq_cross_electricField, hE]
    simp
  simp [electricDisplacement, magneticFieldStrength, hE, hB]

/-- A source-free Maxwell candidate with at least one nonzero electric quadrature satisfies the
positive material dispersion relation. -/
lemma isDispersionMatched_of_isSourceFreeMacroscopicMaxwell
    (wave : MonochromaticPlaneWave) (medium : HomogeneousIsotropicMedium)
    (hMaxwell : IsSourceFreeMacroscopicMaxwell wave.electricField
      (wave.electricDisplacement medium) wave.magneticInduction
      (wave.magneticFieldStrength medium))
    (hNonzero : wave.electricReal ≠ 0 ∨ wave.electricImag ≠ 0) :
    wave.IsDispersionMatched medium := by
  apply wave.isDispersionMatched_of_waveNumber_sq medium
  apply wave.waveNumber_sq_of_magneticCoefficient_eq medium
  rcases hNonzero with hreal | himag
  · exact ampereCoefficient_of_maxwell wave medium hMaxwell
      (-Real.pi / (2 * wave.waveNumber))
      (wave.electricProfile_fderiv_real_sample_ne_of_electricReal_ne hreal)
  · exact ampereCoefficient_of_maxwell wave medium hMaxwell 0
      (wave.electricProfile_fderiv_zero_ne_of_electricImag_ne himag)

/-!

## D. Characterization

-/

/-- For a candidate with nonzero electric amplitude, the canonical fields solve source-free
Maxwell equations exactly when the amplitudes are transverse and the carrier is dispersion
matched to the medium. -/
lemma isSourceFreeMacroscopicMaxwell_iff (wave : MonochromaticPlaneWave)
    (medium : HomogeneousIsotropicMedium)
    (hNonzero : wave.electricReal ≠ 0 ∨ wave.electricImag ≠ 0) :
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

end MonochromaticPlaneWave
end ThreeDimension
end Electromagnetism
