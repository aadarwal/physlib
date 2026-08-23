/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.ClassicalMechanics.WaveEquation.ComplexWaveVector.Hyperplane
public import Physlib.Electromagnetism.ThreeDimension.MonochromaticPlaneWave.ComplexBridge
public import Physlib.Electromagnetism.ThreeDimension.MonochromaticPlaneWave.Dispersion

/-!
# Material dispersion for complex-amplitude plane waves

## i. Overview

This module states the homogeneous-isotropic material dispersion shell for a
`ComplexMonochromaticPlaneWave`. The defining square is the complex-bilinear pairing
`K dot K = epsilon * mu * omega ^ 2`; it is not the Hermitian square norm of `K`.
The name describes matching a carrier to the nondispersive material model; it does not assert
frequency-dependent material response.

For the convention `K = q - I * a`, matching is equivalent to the two real conditions
`q dot a = 0` and `‖q‖ ^ 2 - ‖a‖ ^ 2 = epsilon * mu * omega ^ 2`. Thus attenuating solutions use a
signed difference of phase and attenuation squares. The predicate permits a zero electric
amplitude and does not impose transversality.

Unlike the existing real carrier's positive-branch predicate, the complex square does not select
a propagation direction, square-root branch, interface side, transmitted or outgoing role, or
evanescent-wave interpretation. Maxwell equations and electromagnetic power remain later layers.

## ii. Key results

- `ComplexMonochromaticPlaneWave.IsDispersionMatched`: the complex-bilinear material shell.
- `ComplexMonochromaticPlaneWave.isDispersionMatched_iff_phase_attenuation`: its exact real
  phase--attenuation decomposition.
- `IsDispersionMatched.hyperplaneNormalComponent_sq`: the oriented normal-root equation at a
  chosen neutral hyperplane.
- `IsDispersionMatched.waveVector_ne_zero`: material matching forces a nonzero wave vector.
- `IsDispersionMatched.phaseVector_norm_mul_waveSpeed`: a matched carrier with zero attenuation
  satisfies `‖q‖ * v = omega`.
- `IsDispersionMatched.waveVector_cross_cross_electricAmplitude`: the transverse on-shell vector
  triple-product identity.
- `IsDispersionMatched.waveVector_cross_magneticAmplitude`: its built-in magnetic-amplitude
  consequence with the exact single-frequency factor.
- `ComplexMonochromaticPlaneWave.isDispersionMatched_of_waveVector_cross_magneticAmplitude`: the
  guarded converse from the transverse magnetic-amplitude relation.
- `ComplexMonochromaticPlaneWave.isDispersionMatched_ofReal_iff`: exact agreement with the
  existing positive-branch predicate on embedded real waves.

## iii. Table of contents

- A. Complex material dispersion
- B. Phase and attenuation decomposition
- C. On-shell algebra
- D. Exact real-wave bridge

## iv. References

This file extends Physlib's existing real material-dispersion definition and complex-wave-vector
algebra. No external formal-development source is copied or translated here.
-/

@[expose] public section

namespace Electromagnetism
namespace ThreeDimension

open Space Time InnerProductSpace Matrix ClassicalMechanics

noncomputable section

namespace ComplexMonochromaticPlaneWave

/-!

## A. Complex material dispersion

-/

/-- A complex-amplitude plane-wave candidate is dispersion matched to a homogeneous isotropic
medium when the complex-bilinear square of its wave vector equals
`epsilon * mu * omega ^ 2`.

This condition selects a material shell only. It requires neither electric transversality nor a
square-root or interface branch. -/
def IsDispersionMatched (wave : ComplexMonochromaticPlaneWave)
    (medium : HomogeneousIsotropicMedium) : Prop :=
  ComplexWaveVector.bilinearDot wave.waveVector wave.waveVector =
    ((medium.ε * medium.μ * wave.angularFrequency ^ 2 : ℝ) : ℂ)

/-!

## B. Phase and attenuation decomposition

-/

private lemma bilinearDot_ofPhaseAttenuation_self_eq_ofReal_iff
    (q a : WaveVector 3) (s : ℝ) :
    ComplexWaveVector.bilinearDot (ComplexWaveVector.ofPhaseAttenuation q a)
        (ComplexWaveVector.ofPhaseAttenuation q a) = (s : ℂ) ↔
      ⟪q, a⟫_ℝ = 0 ∧ ‖q‖ ^ 2 - ‖a‖ ^ 2 = s := by
  rw [ComplexWaveVector.bilinearDot_ofPhaseAttenuation_self,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  constructor
  · intro h
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    norm_num [← Complex.ofReal_pow, ← Complex.ofReal_mul] at hre him
    constructor
    · linarith
    · exact hre
  · rintro ⟨horthogonal, hnorm⟩
    apply Complex.ext
    · norm_num [← Complex.ofReal_pow, ← Complex.ofReal_mul]
      exact hnorm
    · norm_num [← Complex.ofReal_pow, ← Complex.ofReal_mul, horthogonal]

/-- Complex material dispersion is equivalent to orthogonality of phase and attenuation vectors
together with their signed squared-norm relation. -/
lemma isDispersionMatched_iff_phase_attenuation (wave : ComplexMonochromaticPlaneWave)
    (medium : HomogeneousIsotropicMedium) :
    wave.IsDispersionMatched medium ↔
      ⟪wave.waveVector.phaseVector, wave.waveVector.attenuationVector⟫_ℝ = 0 ∧
        ‖wave.waveVector.phaseVector‖ ^ 2 -
            ‖wave.waveVector.attenuationVector‖ ^ 2 =
          medium.ε * medium.μ * wave.angularFrequency ^ 2 := by
  unfold IsDispersionMatched
  conv_lhs =>
    rw [← ComplexWaveVector.ofPhaseAttenuation_phaseVector_attenuationVector wave.waveVector]
  exact bilinearDot_ofPhaseAttenuation_self_eq_ofReal_iff _ _ _

/-!

## C. On-shell algebra

-/

namespace IsDispersionMatched

variable {wave : ComplexMonochromaticPlaneWave} {medium : HomogeneousIsotropicMedium}

/-- Relative to an oriented affine hyperplane, the squared complex normal component of a
dispersion-matched wave vector is the material square minus its tangential bilinear square.

This identity does not select either square root or assign an interface propagation role. -/
lemma hyperplaneNormalComponent_sq (h : wave.IsDispersionMatched medium)
    (plane : OrientedAffineHyperplane 3) :
    ComplexWaveVector.hyperplaneNormalComponent plane wave.waveVector ^ 2 =
      ((medium.ε * medium.μ * wave.angularFrequency ^ 2 : ℝ) : ℂ) -
        ComplexWaveVector.bilinearDot
          (ComplexWaveVector.hyperplaneTangentialProjection plane wave.waveVector)
          (ComplexWaveVector.hyperplaneTangentialProjection plane wave.waveVector) := by
  rw [← h, ComplexWaveVector.bilinearDot_self_eq_tangential_add_normal_sq
    plane wave.waveVector]
  ring

/-- The bilinear square of a dispersion-matched wave vector is nonzero. -/
lemma bilinearDot_waveVector_self_ne_zero (h : wave.IsDispersionMatched medium) :
    ComplexWaveVector.bilinearDot wave.waveVector wave.waveVector ≠ 0 := by
  rw [h]
  exact_mod_cast ne_of_gt (mul_pos (mul_pos medium.ε_pos medium.μ_pos)
    (sq_pos_of_pos wave.angularFrequency_pos))

/-- A dispersion-matched complex wave vector is nonzero. -/
lemma waveVector_ne_zero (h : wave.IsDispersionMatched medium) :
    wave.waveVector ≠ 0 := by
  intro hzero
  apply h.bilinearDot_waveVector_self_ne_zero
  rw [hzero, ComplexWaveVector.bilinearDot_zero_left]

/-- A dispersion-matched carrier with zero attenuation has phase-vector magnitude satisfying
`‖q‖ * v = omega`.

This result selects the positive phase-magnitude root using the positivity of angular frequency
and wave speed. It assigns no interface side, propagation direction, group velocity, or power
role. -/
lemma phaseVector_norm_mul_waveSpeed
    (h : wave.IsDispersionMatched medium)
    (hAttenuation : wave.waveVector.attenuationVector = 0) :
    ‖wave.waveVector.phaseVector‖ * medium.waveSpeed = wave.angularFrequency := by
  have hNormSq :
      ‖wave.waveVector.phaseVector‖ ^ 2 =
        medium.ε * medium.μ * wave.angularFrequency ^ 2 := by
    have hReal :=
      (isDispersionMatched_iff_phase_attenuation wave medium).mp h
    simpa [hAttenuation] using hReal.2
  have hProductSq :
      (‖wave.waveVector.phaseVector‖ * medium.waveSpeed) ^ 2 =
        wave.angularFrequency ^ 2 := by
    rw [mul_pow, medium.waveSpeed_sq, hNormSq]
    field_simp [medium.ε_ne_zero, medium.μ_ne_zero]
  have hProductNonneg :
      0 ≤ ‖wave.waveVector.phaseVector‖ * medium.waveSpeed :=
    mul_nonneg (norm_nonneg _) medium.waveSpeed_nonneg
  nlinarith [wave.angularFrequency_pos]

/-- A dispersion-matched carrier with zero attenuation has phase-vector magnitude `omega / v`. -/
lemma phaseVector_norm_eq_angularFrequency_div_waveSpeed
    (h : wave.IsDispersionMatched medium)
    (hAttenuation : wave.waveVector.attenuationVector = 0) :
    ‖wave.waveVector.phaseVector‖ = wave.angularFrequency / medium.waveSpeed := by
  rw [eq_div_iff medium.waveSpeed_ne_zero]
  exact h.phaseVector_norm_mul_waveSpeed hAttenuation

/-- For a transverse dispersion-matched amplitude,
`K cross (K cross E0) = -(epsilon * mu * omega ^ 2) E0`. -/
lemma waveVector_cross_cross_electricAmplitude
    (h : wave.IsDispersionMatched medium) (hTransverse : wave.IsTransverse) :
    complexCross wave.waveVector
        (complexCross wave.waveVector wave.electricAmplitude) =
      -((medium.ε * medium.μ * wave.angularFrequency ^ 2 : ℝ) : ℂ) •
        wave.electricAmplitude := by
  rw [complexCross_complexCross]
  change ComplexWaveVector.bilinearDot wave.waveVector wave.electricAmplitude = 0 at hTransverse
  rw [hTransverse, h]
  simp

/-- For a transverse dispersion-matched amplitude,
`K cross B0 = -(epsilon * mu * omega) E0`. -/
lemma waveVector_cross_magneticAmplitude
    (h : wave.IsDispersionMatched medium) (hTransverse : wave.IsTransverse) :
    complexCross wave.waveVector wave.magneticAmplitude =
      -((medium.ε * medium.μ * wave.angularFrequency : ℝ) : ℂ) •
        wave.electricAmplitude := by
  rw [magneticAmplitude, complexCross_smul_right,
    h.waveVector_cross_cross_electricAmplitude hTransverse, smul_smul]
  congr 1
  push_cast
  field_simp [wave.angularFrequency_ne_zero]

end IsDispersionMatched

/-- A nonzero transverse amplitude satisfying the material magnetic-amplitude relation lies on
the complex-bilinear material shell. -/
lemma isDispersionMatched_of_waveVector_cross_magneticAmplitude
    (wave : ComplexMonochromaticPlaneWave) (medium : HomogeneousIsotropicMedium)
    (hTransverse : wave.IsTransverse)
    (hAmpere : complexCross wave.waveVector wave.magneticAmplitude =
      -((medium.ε * medium.μ * wave.angularFrequency : ℝ) : ℂ) •
        wave.electricAmplitude)
    (hNonzero : wave.electricAmplitude ≠ 0) :
    wave.IsDispersionMatched medium := by
  rw [magneticAmplitude, complexCross_smul_right,
    complexCross_complexCross] at hAmpere
  change ComplexWaveVector.bilinearDot wave.waveVector wave.electricAmplitude = 0
    at hTransverse
  rw [hTransverse] at hAmpere
  simp only [zero_smul, zero_sub, smul_neg, smul_smul] at hAmpere
  rw [← neg_smul] at hAmpere
  have hCoefficient :
      (wave.angularFrequency : ℂ)⁻¹ *
          ComplexWaveVector.bilinearDot wave.waveVector wave.waveVector =
        ((medium.ε * medium.μ * wave.angularFrequency : ℝ) : ℂ) := by
    exact neg_inj.mp ((smul_left_inj hNonzero).mp hAmpere)
  rw [IsDispersionMatched]
  field_simp [wave.angularFrequency_ne_zero] at hCoefficient
  calc
    ComplexWaveVector.bilinearDot wave.waveVector wave.waveVector =
        (wave.angularFrequency : ℂ) *
          ((medium.ε * medium.μ * wave.angularFrequency : ℝ) : ℂ) := hCoefficient
    _ = ((medium.ε * medium.μ * wave.angularFrequency ^ 2 : ℝ) : ℂ) := by
      push_cast
      ring

/-!

## D. Exact real-wave bridge

-/

/-- An embedded real-quadrature wave satisfies the complex material shell exactly when it
satisfies the existing positive-branch real dispersion predicate. -/
lemma isDispersionMatched_ofReal_iff (wave : MonochromaticPlaneWave)
    (medium : HomogeneousIsotropicMedium) :
    (ofReal wave).IsDispersionMatched medium ↔ wave.IsDispersionMatched medium := by
  constructor
  · intro h
    apply MonochromaticPlaneWave.isDispersionMatched_of_waveNumber_sq wave medium
    rw [IsDispersionMatched, ofReal_waveVector,
      ComplexWaveVector.bilinearDot_ofReal, real_inner_self_eq_norm_sq,
      wave.waveVector_norm] at h
    exact_mod_cast h
  · intro h
    rw [IsDispersionMatched, ofReal_waveVector,
      ComplexWaveVector.bilinearDot_ofReal, real_inner_self_eq_norm_sq,
      wave.waveVector_norm]
    exact_mod_cast MonochromaticPlaneWave.IsDispersionMatched.waveNumber_sq h

end ComplexMonochromaticPlaneWave
end
end ThreeDimension
end Electromagnetism
