/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.HarmonicFlux.Basic
public import Physlib.Optics.Polarization.ComplexRealization

/-!
# Harmonic flux of complex material plane waves

## i. Overview

This file connects an off-shell complex monochromatic plane-wave carrier to local electric and
magnetic-field-strength phasors. At a selected point, both phasors retain the complete complex
spatial factor. Their one-period phasor average therefore equals the average of the actual
ordinary-real instantaneous Poynting vector.

The reference-amplitude form exposes the squared modulus of the spatial factor explicitly. Thus
an amplitude envelope scaled by `exp (-alpha * u)` scales mean flux by `exp (-2 * alpha * u)`.

## ii. Key results

- `ComplexMonochromaticPlaneWave.localElectricPhasor`: the local electric peak phasor.
- `ComplexMonochromaticPlaneWave.localMagneticFieldStrengthPhasor`: the local material `H`
  peak phasor.
- `ComplexMonochromaticPlaneWave.intervalAverage_poyntingVector_eq_localPhasors`: the actual-field
  one-period averaging connector.
- `ComplexMonochromaticPlaneWave.intervalAverage_poyntingVector_add_eq_localPhasors`: the
  equal-frequency two-carrier superposition connector.
- `ComplexMonochromaticPlaneWave.intervalAverage_poyntingVector_eq_spatialFactor_normSq_smul`:
  the stored-reference-amplitude form.

## iii. Table of contents

- A. Local material phasors
- B. Actual-field harmonic flux

## iv. Scope

These identities are local, kinematic, and off shell. They allow zero electric amplitude and
require no transversality, dispersion, Maxwell, passivity, conservation, or nonnegativity
hypothesis. The reference amplitudes depend on the selected spatial origin and carrier phase, and
the squared local spatial envelope is not an intrinsic normalization.

The carrier type still supplies its built-in Faraday-compatible magnetic amplitude
`B₀ = omega⁻¹ (K cross E₀)`; “off shell” means that no full material-dispersion or Maxwell predicate
is assumed here.

The results are flux-density identities, not aperture-integrated or modal power. They introduce
no interface side, incident, reflected, transmitted, outgoing, evanescent, Fresnel, total internal
reflection, or half-space-support claim; the ordinary-real fields remain globally defined.
-/

@[expose] public section

namespace Electromagnetism
namespace ThreeDimension

open ClassicalMechanics Matrix MeasureTheory Optics Space Time
open scoped Interval Real

noncomputable section

namespace ComplexMonochromaticPlaneWave

/-!

## A. Local material phasors

-/

/-- The local electric peak phasor, including the complete complex spatial factor at the selected
point. -/
def localElectricPhasor (wave : ComplexMonochromaticPlaneWave) (x : Space) :
    EuclideanSpace ℂ (Fin 3) :=
  wave.waveVector.spatialFactor x • wave.electricAmplitude

/-- The local magnetic-field-strength peak phasor, including the complete complex spatial factor
and the homogeneous isotropic material relation `H₀ = μ⁻¹ B₀`. -/
def localMagneticFieldStrengthPhasor (wave : ComplexMonochromaticPlaneWave)
    (medium : HomogeneousIsotropicMedium) (x : Space) : EuclideanSpace ℂ (Fin 3) :=
  wave.waveVector.spatialFactor x •
    (((medium.μ⁻¹ : ℝ) : ℂ) • wave.magneticAmplitude)

private lemma realFieldOfAmplitude_eq_realize_localPhasor
    (wave : ComplexMonochromaticPlaneWave) (amplitude : EuclideanSpace ℂ (Fin 3))
    (time : ℝ) (x : Space) :
    wave.realFieldOfAmplitude amplitude (time : Time) x =
      Phasor.realizeEuclidean (wave.waveVector.spatialFactor x • amplitude)
        (wave.angularFrequency * time) := by
  rw [Phasor.realizeEuclidean_eq_realPart_exp_smul]
  simp only [realFieldOfAmplitude, carrier, smul_smul]

/-- The actual ordinary-real electric field is the realization of the local electric phasor at
the positive-frequency carrier phase. -/
lemma electricField_eq_realize_localElectricPhasor (wave : ComplexMonochromaticPlaneWave)
    (time : ℝ) (x : Space) :
    wave.electricField (time : Time) x =
      Phasor.realizeEuclidean (wave.localElectricPhasor x)
        (wave.angularFrequency * time) := by
  exact realFieldOfAmplitude_eq_realize_localPhasor wave wave.electricAmplitude time x

/-- The actual ordinary-real magnetic field strength is the realization of its local material
phasor at the positive-frequency carrier phase. -/
lemma magneticFieldStrength_eq_realize_localMagneticFieldStrengthPhasor
    (wave : ComplexMonochromaticPlaneWave) (medium : HomogeneousIsotropicMedium)
    (time : ℝ) (x : Space) :
    wave.magneticFieldStrength medium (time : Time) x =
      Phasor.realizeEuclidean (wave.localMagneticFieldStrengthPhasor medium x)
        (wave.angularFrequency * time) := by
  calc
    wave.magneticFieldStrength medium (time : Time) x =
        medium.μ⁻¹ • wave.realFieldOfAmplitude wave.magneticAmplitude (time : Time) x := rfl
    _ = medium.μ⁻¹ •
        Phasor.realizeEuclidean
          (wave.waveVector.spatialFactor x • wave.magneticAmplitude)
          (wave.angularFrequency * time) := by
      rw [realFieldOfAmplitude_eq_realize_localPhasor]
    _ = Phasor.realizeEuclidean (wave.localMagneticFieldStrengthPhasor medium x)
        (wave.angularFrequency * time) := by
      have hcomm : wave.waveVector.spatialFactor x •
          (((medium.μ⁻¹ : ℝ) : ℂ) • wave.magneticAmplitude) =
        ((medium.μ⁻¹ : ℝ) : ℂ) •
          (wave.waveVector.spatialFactor x • wave.magneticAmplitude) := by
        simp only [smul_smul]
        rw [mul_comm]
      rw [localMagneticFieldStrengthPhasor, hcomm]
      exact (Phasor.realizeEuclidean_ofReal_smul medium.μ⁻¹
        (wave.waveVector.spatialFactor x • wave.magneticAmplitude)
        (wave.angularFrequency * time)).symm

/-!

## B. Actual-field harmonic flux

-/

/-- The one-period average of the actual instantaneous Poynting vector equals the harmonic-flux
formula evaluated on the complete local electric and magnetic-field-strength phasors. -/
lemma intervalAverage_poyntingVector_eq_localPhasors
    (wave : ComplexMonochromaticPlaneWave) (medium : HomogeneousIsotropicMedium)
    (startTime : Time) (x : Space) :
    (⨍ time in startTime.val..startTime.val + 2 * Real.pi / wave.angularFrequency,
      poyntingVector wave.electricField (wave.magneticFieldStrength medium)
        (time : Time) x) =
      timeAveragedPoyntingVector (wave.localElectricPhasor x)
        (wave.localMagneticFieldStrengthPhasor medium x) := by
  apply intervalAverage_poyntingVector_eq_timeAveragedPoyntingVector
    (wave.localElectricPhasor x) (wave.localMagneticFieldStrengthPhasor medium x)
    wave.angularFrequency wave.angularFrequency_pos startTime x
  · exact fun time ↦ wave.electricField_eq_realize_localElectricPhasor time x
  · exact fun time ↦
      wave.magneticFieldStrength_eq_realize_localMagneticFieldStrengthPhasor medium time x

/-- The one-period average of the actual Poynting vector of two coherently superposed
equal-frequency carriers is the harmonic-flux expression for the sums of their complete local
phasors.

Both magnetic field strengths use the same supplied medium. The result requires no Maxwell,
transversality, dispersion, or nonzero-amplitude hypothesis. -/
lemma intervalAverage_poyntingVector_add_eq_localPhasors
    (firstWave secondWave : ComplexMonochromaticPlaneWave)
    (medium : HomogeneousIsotropicMedium)
    (hFrequency : secondWave.angularFrequency = firstWave.angularFrequency)
    (startTime : Time) (x : Space) :
    (⨍ time in startTime.val..startTime.val + 2 * Real.pi / firstWave.angularFrequency,
      poyntingVector (firstWave.electricField + secondWave.electricField)
        (firstWave.magneticFieldStrength medium + secondWave.magneticFieldStrength medium)
        (time : Time) x) =
      timeAveragedPoyntingVector
        (firstWave.localElectricPhasor x + secondWave.localElectricPhasor x)
        (firstWave.localMagneticFieldStrengthPhasor medium x +
          secondWave.localMagneticFieldStrengthPhasor medium x) := by
  apply intervalAverage_poyntingVector_eq_timeAveragedPoyntingVector
    (firstWave.localElectricPhasor x + secondWave.localElectricPhasor x)
    (firstWave.localMagneticFieldStrengthPhasor medium x +
      secondWave.localMagneticFieldStrengthPhasor medium x)
    firstWave.angularFrequency firstWave.angularFrequency_pos startTime x
  · intro time
    simp only [Pi.add_apply]
    rw [firstWave.electricField_eq_realize_localElectricPhasor,
      secondWave.electricField_eq_realize_localElectricPhasor, hFrequency,
      Phasor.realizeEuclidean_add]
  · intro time
    simp only [Pi.add_apply]
    rw [firstWave.magneticFieldStrength_eq_realize_localMagneticFieldStrengthPhasor,
      secondWave.magneticFieldStrength_eq_realize_localMagneticFieldStrengthPhasor,
      hFrequency, Phasor.realizeEuclidean_add]

/-- The actual one-period mean Poynting vector equals the reference-amplitude harmonic flux scaled
by the squared modulus of the complete spatial factor at the observation point.

The reference electric and magnetic amplitudes use the carrier's selected spatial origin and
phase convention; the squared spatial envelope must not be discarded for an attenuating
carrier. -/
lemma intervalAverage_poyntingVector_eq_spatialFactor_normSq_smul
    (wave : ComplexMonochromaticPlaneWave) (medium : HomogeneousIsotropicMedium)
    (startTime : Time) (x : Space) :
    (⨍ time in startTime.val..startTime.val + 2 * Real.pi / wave.angularFrequency,
      poyntingVector wave.electricField (wave.magneticFieldStrength medium)
        (time : Time) x) =
      Complex.normSq (wave.waveVector.spatialFactor x) •
        timeAveragedPoyntingVector wave.electricAmplitude
          (((medium.μ⁻¹ : ℝ) : ℂ) • wave.magneticAmplitude) := by
  rw [wave.intervalAverage_poyntingVector_eq_localPhasors]
  exact timeAveragedPoyntingVector_smul
    (wave.waveVector.spatialFactor x) wave.electricAmplitude
    (((medium.μ⁻¹ : ℝ) : ℂ) • wave.magneticAmplitude)

end ComplexMonochromaticPlaneWave

end

end ThreeDimension
end Electromagnetism
