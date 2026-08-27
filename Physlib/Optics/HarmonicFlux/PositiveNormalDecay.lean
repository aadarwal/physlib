/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.HarmonicFlux.ComplexMaterialWave

/-!
# Harmonic flux of positive-normal-decay plane waves

## i. Overview

This file proves the role-neutral algebra behind vanishing mean flux along the decay direction.
For a complex wave vector `K = q - I * alpha * n` whose real phase vector `q` is tangent to the
unit direction `n`, a bilinearly transverse electric amplitude has zero normal component of

`(1 / 2) Re (E₀ cross conj H₀)`

when `H₀` is any real scalar multiple of `K cross E₀`. The scalar may vanish or have either
sign. Material dispersion and the Maxwell equations are not used in this cancellation.

The result is then connected to the actual one-period mean Poynting vector of the ordinary-real
fields constructed by `ComplexMonochromaticPlaneWave`. At every observation point, the complete
spatial envelope multiplies zero.

## ii. Key results

- The role-neutral peak-phasor cancellation:
  `inner_normalVector_timeAveragedPoyntingVector_complexCross_eq_zero`.
- The actual-field one-period result at every point and period start:
  `inner_normalVector_intervalAverage_poyntingVector_eq_zero_of_positiveNormalDecay`.

## iii. Table of contents

- A. Positive-normal-decay phasor algebra
- B. Actual-field mean flux

## iv. References

This Physlib-original cancellation result uses the complex-wave-vector convention documented in
`ComplexWaveVector`. The conclusion is a local time-averaged flux-density statement. It does not
say that the instantaneous normal Poynting vector vanishes, and it permits nonzero tangential mean
flux. It supplies no material dispersion, Maxwell, interface, Fresnel,
total-internal-reflection, conservation, half-space-support, aperture-power, or modal-power
conclusion. Unguarded convention statement (review only): it assigns no incident, reflected,
transmitted, or outgoing wave role. The carrier remains globally defined and grows under
displacement opposite to its positive decay direction.
-/

@[expose] public section

namespace ClassicalMechanics

open Electromagnetism Electromagnetism.ThreeDimension InnerProductSpace Matrix Optics Space
open scoped ComplexConjugate

noncomputable section

namespace ComplexWaveVector
namespace PositiveNormalDecayWaveVector

/-!

## A. Positive-normal-decay phasor algebra

-/

private lemma conjugateEuclidean_waveVector
    {normal : Direction 3} (data : PositiveNormalDecayWaveVector normal) :
    Phasor.conjugateEuclidean data.waveVector =
      ofReal data.tangentialWaveVector +
        Complex.I • ofReal (data.decayRate • data.normalVector) := by
  ext i
  simp [waveVector, ofPhaseAttenuation, Phasor.conjugateEuclidean]

private lemma bilinearDot_electric_conjugateWaveVector
    {normal : Direction 3} (data : PositiveNormalDecayWaveVector normal)
    (electricAmplitude : EuclideanSpace ℂ (Fin 3))
    (hTransverse : bilinearDot data.waveVector electricAmplitude = 0) :
    bilinearDot electricAmplitude (Phasor.conjugateEuclidean data.waveVector) =
      2 * Complex.I * (data.decayRate : ℂ) *
        bilinearDot (ofReal data.normalVector) electricAmplitude := by
  have hTransverse' :
      bilinearDot (ofReal data.tangentialWaveVector) electricAmplitude -
          Complex.I * (data.decayRate : ℂ) *
            bilinearDot (ofReal data.normalVector) electricAmplitude = 0 := by
    rw [waveVector, ofPhaseAttenuation, bilinearDot_sub_left,
      bilinearDot_smul_left, ofReal_smul, bilinearDot_smul_left] at hTransverse
    simpa [mul_assoc] using hTransverse
  rw [conjugateEuclidean_waveVector, bilinearDot_add_right,
    bilinearDot_smul_right, ofReal_smul, bilinearDot_smul_right,
    bilinearDot_comm electricAmplitude (ofReal data.tangentialWaveVector),
    bilinearDot_comm electricAmplitude (ofReal data.normalVector)]
  linear_combination hTransverse'

private lemma bilinearDot_normal_conjugateWaveVector
    {normal : Direction 3} (data : PositiveNormalDecayWaveVector normal) :
    bilinearDot (ofReal data.normalVector)
        (Phasor.conjugateEuclidean data.waveVector) =
      Complex.I * (data.decayRate : ℂ) := by
  rw [conjugateEuclidean_waveVector, bilinearDot_add_right,
    bilinearDot_smul_right, ofReal_smul, bilinearDot_smul_right, bilinearDot_ofReal]
  have htangent :
      inner ℝ data.normalVector data.tangentialWaveVector = 0 := data.tangential
  have hnormal : inner ℝ data.normalVector data.normalVector = 1 := by
    rw [real_inner_self_eq_norm_sq, data.normalVector_norm]
    norm_num
  rw [bilinearDot_ofReal, htangent, hnormal]
  simp

private lemma bilinearDot_self_conjugateEuclidean_im
    (v : EuclideanSpace ℂ (Fin 3)) :
    (bilinearDot v (Phasor.conjugateEuclidean v)).im = 0 := by
  rw [bilinearDot, Complex.im_sum]
  apply Finset.sum_eq_zero
  intro i _
  simp [Phasor.conjugateEuclidean, Complex.mul_im]
  ring

private lemma referenceFlux_normal_re_eq_zero
    {normal : Direction 3} (data : PositiveNormalDecayWaveVector normal)
    (electricAmplitude : EuclideanSpace ℂ (Fin 3))
    (hTransverse : bilinearDot data.waveVector electricAmplitude = 0) :
    (bilinearDot (ofReal data.normalVector)
      (ComplexMonochromaticPlaneWave.complexCross electricAmplitude
        (Phasor.conjugateEuclidean
          (ComplexMonochromaticPlaneWave.complexCross
            data.waveVector electricAmplitude)))).re = 0 := by
  rw [Phasor.conjugateEuclidean_complexCross,
    ComplexMonochromaticPlaneWave.complexCross_complexCross,
    bilinearDot_sub_right, bilinearDot_smul_right, bilinearDot_smul_right,
    bilinearDot_normal_conjugateWaveVector,
    bilinearDot_electric_conjugateWaveVector data electricAmplitude hTransverse,
    ComplexWaveVector.bilinearDot_ofReal_conjugateEuclidean]
  have hnormIm := bilinearDot_self_conjugateEuclidean_im electricAmplitude
  simp [Complex.mul_re, hnormIm]
  ring

/-- A bilinearly transverse electric phasor whose magnetic phasor is a real scalar multiple of
`K cross E₀` has zero mean Poynting component along a positive-normal-decay direction.

Neither the real magnetic scale nor the electric phasor is required to be nonzero. The proof uses
no material-dispersion, Maxwell, interface, or power-normalization hypothesis. -/
lemma inner_normalVector_timeAveragedPoyntingVector_complexCross_eq_zero
    {normal : Direction 3} (data : PositiveNormalDecayWaveVector normal)
    (electricPhasor : EuclideanSpace ℂ (Fin 3)) (magneticScale : ℝ)
    (hTransverse : bilinearDot data.waveVector electricPhasor = 0) :
    inner ℝ data.normalVector
      (Optics.timeAveragedPoyntingVector electricPhasor
        ((magneticScale : ℂ) •
          ComplexMonochromaticPlaneWave.complexCross data.waveVector electricPhasor)) = 0 := by
  rw [Optics.timeAveragedPoyntingVector, inner_smul_right,
    inner_realPart_eq_bilinearDot_re, Phasor.conjugateEuclidean_smul,
    Phasor.conjugateEuclidean_complexCross,
    ComplexMonochromaticPlaneWave.complexCross_smul_right, bilinearDot_smul_right]
  have hcore := referenceFlux_normal_re_eq_zero data electricPhasor hTransverse
  rw [Phasor.conjugateEuclidean_complexCross] at hcore
  simp [Complex.mul_re, hcore]

end PositiveNormalDecayWaveVector
end ComplexWaveVector

end
end ClassicalMechanics

namespace Electromagnetism
namespace ThreeDimension

open ClassicalMechanics InnerProductSpace Matrix MeasureTheory Optics Space Time
open scoped Interval Real

noncomputable section

namespace ComplexMonochromaticPlaneWave

/-!

## B. Actual-field mean flux

-/

/-- A bilinearly transverse complex plane wave with positive-normal-decay wave-vector data has
zero actual one-period mean Poynting component along the decay direction at every point and every
period start.

The conclusion uses the supplied homogeneous isotropic medium only to form `H = μ⁻¹ B`. It does
not require material dispersion or assert that the wave solves Maxwell's equations. -/
lemma inner_normalVector_intervalAverage_poyntingVector_eq_zero_of_positiveNormalDecay
    (wave : ComplexMonochromaticPlaneWave) (medium : HomogeneousIsotropicMedium)
    {normal : Direction 3}
    (data : ComplexWaveVector.PositiveNormalDecayWaveVector normal)
    (hWaveVector : wave.waveVector = data.waveVector)
    (hTransverse : wave.IsTransverse) (startTime : Time) (x : Space) :
    inner ℝ data.normalVector
      (⨍ time in startTime.val..startTime.val + 2 * Real.pi / wave.angularFrequency,
        poyntingVector wave.electricField (wave.magneticFieldStrength medium)
          (time : Time) x) = 0 := by
  rw [wave.intervalAverage_poyntingVector_eq_spatialFactor_normSq_smul,
    inner_smul_right]
  have hTransverse' :
      ComplexWaveVector.bilinearDot data.waveVector wave.electricAmplitude = 0 := by
    change ComplexWaveVector.bilinearDot wave.waveVector wave.electricAmplitude = 0
      at hTransverse
    rwa [hWaveVector] at hTransverse
  have hmagnetic :
      (((medium.μ⁻¹ : ℝ) : ℂ) • wave.magneticAmplitude) =
        ((medium.μ⁻¹ * wave.angularFrequency⁻¹ : ℝ) : ℂ) •
          complexCross data.waveVector wave.electricAmplitude := by
    rw [magneticAmplitude, hWaveVector]
    simp only [smul_smul]
    congr 1
    push_cast
    rfl
  rw [hmagnetic,
    data.inner_normalVector_timeAveragedPoyntingVector_complexCross_eq_zero
      wave.electricAmplitude (medium.μ⁻¹ * wave.angularFrequency⁻¹) hTransverse']
  simp only [mul_zero]

end ComplexMonochromaticPlaneWave

end

end ThreeDimension
end Electromagnetism
