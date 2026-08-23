/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.ClassicalMechanics.WaveEquation.ComplexWaveVector.Hyperplane
public import Physlib.Electromagnetism.ThreeDimension.MonochromaticPlaneWave.ComplexBasic

/-!
# Boundary exponents of complex plane waves

## i. Overview

This file restricts the carrier of one off-shell complex-amplitude electromagnetic plane-wave
candidate to an oriented affine hyperplane. Time and tangent displacement form a real vector
space, and the variable part of the restricted carrier is represented by the exponential of a
complex-valued real-linear functional. The spatial factor at the hyperplane's stored point remains
in the coefficient.

Equality of two boundary exponents is equivalent to equality of their angular frequencies and of
their complex wave-vector pairings against every real tangent displacement. Equivalently, their
full complex hyperplane-tangential wave-vector projections agree. The complex equality captures
both tangential phase and tangential attenuation data. This is an algebraic characterization, not
a conservation law: it assumes no boundary condition or noncancellation hypothesis and does not
conclude that two wave vectors are equal.

The construction assumes no transversality, material dispersion, Maxwell equation, interface
medium, wave role, half-space support, incoming or outgoing direction, decay branch, Fresnel
coefficient, irradiance, or power normalization.

## ii. Key results

- `ComplexMonochromaticPlaneWave.boundaryExponent_boundaryTimeProbe_im_pos`: every stored wave has
  positive boundary-exponent rate along the common unit-time probe.
- `ComplexMonochromaticPlaneWave.boundaryExponent_eq_iff`: equality of boundary exponents separates
  angular frequency from all tangent wave-vector pairings.
- `boundaryExponent_eq_iff_angularFrequency_and_tangentialProjection_eq`:
  the same equality packaged by the complex hyperplane-tangential projection.
- `ComplexMonochromaticPlaneWave.carrier_tangent_vadd_point`: exact factorization of the carrier on
  the affine plane into its boundary exponential and stored-point spatial factor.

## iii. Table of contents

- A. Boundary exponent functional
- B. Equality and positive rate
- C. Affine-plane carrier factorization

## iv. References

The construction uses Physlib's existing complex carrier convention and oriented affine
hyperplane geometry. No external formal-development source is copied or translated here.
-/

@[expose] public section

namespace Electromagnetism
namespace ThreeDimension

open Space Time ClassicalMechanics

noncomputable section

namespace ComplexMonochromaticPlaneWave

/-!

## A. Boundary exponent functional

-/

/-- Time paired with a displacement in an oriented hyperplane's real tangent submodule. -/
abbrev BoundaryParameter (plane : OrientedAffineHyperplane 3) :=
  Time × plane.tangentSubmodule

/-- The complex-valued real-linear exponent of a complex plane-wave carrier restricted to an
oriented affine hyperplane.

For time `t` and tangent displacement `v`, its value is
`I * omega * t - I * (K dot v)`. The affine point contributes to the carrier coefficient rather
than this linear exponent. -/
def boundaryExponent (plane : OrientedAffineHyperplane 3)
    (wave : ComplexMonochromaticPlaneWave) : BoundaryParameter plane →ₗ[ℝ] ℂ where
  toFun tv :=
    ((wave.angularFrequency * (tv.1 : ℝ) : ℝ) : ℂ) * Complex.I -
      Complex.I * ComplexWaveVector.bilinearDot wave.waveVector
        (ComplexWaveVector.ofReal (tv.2 : EuclideanSpace ℝ (Fin 3)))
  map_add' u v := by
    simp only [Prod.fst_add, Prod.snd_add, Time.add_val]
    have huv :
        ((u.2 + v.2 : plane.tangentSubmodule) : EuclideanSpace ℝ (Fin 3)) =
          (u.2 : EuclideanSpace ℝ (Fin 3)) +
            (v.2 : EuclideanSpace ℝ (Fin 3)) := rfl
    rw [huv, ComplexWaveVector.ofReal_add,
      ComplexWaveVector.bilinearDot_add_right]
    push_cast
    ring_nf
  map_smul' c v := by
    simp only [Prod.smul_fst, Prod.smul_snd, Time.smul_real_val,
      RingHom.id_apply]
    have hcv :
        ((c • v.2 : plane.tangentSubmodule) : EuclideanSpace ℝ (Fin 3)) =
          c • (v.2 : EuclideanSpace ℝ (Fin 3)) := rfl
    rw [hcv, ComplexWaveVector.ofReal_smul,
      ComplexWaveVector.bilinearDot_smul_right]
    push_cast
    simp only [Complex.real_smul]
    ring_nf

/-- Evaluation formula for the boundary exponent. -/
@[simp]
lemma boundaryExponent_apply (plane : OrientedAffineHyperplane 3)
    (wave : ComplexMonochromaticPlaneWave) (t : Time) (v : plane.tangentSubmodule) :
    wave.boundaryExponent plane (t, v) =
      ((wave.angularFrequency * (t : ℝ) : ℝ) : ℂ) * Complex.I -
        Complex.I * ComplexWaveVector.bilinearDot wave.waveVector
          (ComplexWaveVector.ofReal (v : EuclideanSpace ℝ (Fin 3))) := rfl

/-- The unit positive-time and zero-tangent parameter used to read off angular frequency. -/
def boundaryTimeProbe (plane : OrientedAffineHyperplane 3) : BoundaryParameter plane :=
  (1, 0)

/-!

## B. Equality and positive rate

-/

/-- The imaginary boundary-exponent rate along the unit-time probe is the angular frequency. -/
@[simp]
lemma boundaryExponent_boundaryTimeProbe_im
    (plane : OrientedAffineHyperplane 3) (wave : ComplexMonochromaticPlaneWave) :
    (wave.boundaryExponent plane (boundaryTimeProbe plane)).im = wave.angularFrequency := by
  simp [boundaryTimeProbe, boundaryExponent]

/-- The boundary exponent has positive imaginary rate along the common unit-time probe. -/
lemma boundaryExponent_boundaryTimeProbe_im_pos
    (plane : OrientedAffineHyperplane 3) (wave : ComplexMonochromaticPlaneWave) :
    0 < (wave.boundaryExponent plane (boundaryTimeProbe plane)).im := by
  simpa using wave.angularFrequency_pos

private lemma angularFrequency_eq_of_boundaryExponent_eq
    (plane : OrientedAffineHyperplane 3) (wave₁ wave₂ : ComplexMonochromaticPlaneWave)
    (h : wave₁.boundaryExponent plane = wave₂.boundaryExponent plane) :
    wave₁.angularFrequency = wave₂.angularFrequency := by
  have hprobe := DFunLike.congr_fun h (boundaryTimeProbe plane)
  simpa using congrArg Complex.im hprobe

private lemma bilinearDot_tangent_eq_of_boundaryExponent_eq
    (plane : OrientedAffineHyperplane 3) (wave₁ wave₂ : ComplexMonochromaticPlaneWave)
    (h : wave₁.boundaryExponent plane = wave₂.boundaryExponent plane)
    (v : plane.tangentSubmodule) :
    ComplexWaveVector.bilinearDot wave₁.waveVector
        (ComplexWaveVector.ofReal (v : EuclideanSpace ℝ (Fin 3))) =
      ComplexWaveVector.bilinearDot wave₂.waveVector
        (ComplexWaveVector.ofReal (v : EuclideanSpace ℝ (Fin 3))) := by
  have hv := DFunLike.congr_fun h ((0 : Time), v)
  have hv' :
      -Complex.I * ComplexWaveVector.bilinearDot wave₁.waveVector
          (ComplexWaveVector.ofReal (v : EuclideanSpace ℝ (Fin 3))) =
        -Complex.I * ComplexWaveVector.bilinearDot wave₂.waveVector
          (ComplexWaveVector.ofReal (v : EuclideanSpace ℝ (Fin 3))) := by
    simpa using hv
  exact mul_left_cancel₀ (neg_ne_zero.mpr Complex.I_ne_zero) hv'

/-- Boundary exponents are equal exactly when angular frequency and every tangent wave-vector
pairing are equal. -/
lemma boundaryExponent_eq_iff
    (plane : OrientedAffineHyperplane 3) (wave₁ wave₂ : ComplexMonochromaticPlaneWave) :
    wave₁.boundaryExponent plane = wave₂.boundaryExponent plane ↔
      wave₁.angularFrequency = wave₂.angularFrequency ∧
        ∀ v : plane.tangentSubmodule,
          ComplexWaveVector.bilinearDot wave₁.waveVector
              (ComplexWaveVector.ofReal (v : EuclideanSpace ℝ (Fin 3))) =
            ComplexWaveVector.bilinearDot wave₂.waveVector
              (ComplexWaveVector.ofReal (v : EuclideanSpace ℝ (Fin 3))) := by
  constructor
  · intro h
    exact ⟨angularFrequency_eq_of_boundaryExponent_eq plane wave₁ wave₂ h,
      bilinearDot_tangent_eq_of_boundaryExponent_eq plane wave₁ wave₂ h⟩
  · rintro ⟨hfrequency, htangent⟩
    apply LinearMap.ext
    rintro ⟨t, v⟩
    rw [boundaryExponent_apply, boundaryExponent_apply, hfrequency, htangent]

/-- Boundary exponents are equal exactly when angular frequency and complex
hyperplane-tangential wave-vector projection are equal. -/
lemma boundaryExponent_eq_iff_angularFrequency_and_tangentialProjection_eq
    (plane : OrientedAffineHyperplane 3)
    (wave₁ wave₂ : ComplexMonochromaticPlaneWave) :
    wave₁.boundaryExponent plane = wave₂.boundaryExponent plane ↔
      wave₁.angularFrequency = wave₂.angularFrequency ∧
        ComplexWaveVector.hyperplaneTangentialProjection plane wave₁.waveVector =
          ComplexWaveVector.hyperplaneTangentialProjection plane wave₂.waveVector := by
  rw [boundaryExponent_eq_iff,
    ComplexWaveVector.hyperplaneTangentialProjection_eq_iff_bilinearDot_eq_on_tangent]

/-!

## C. Affine-plane carrier factorization

-/

/-- On a tangent displacement of the stored affine point, the carrier is the boundary exponential
times the spatial factor at that point. -/
lemma carrier_tangent_vadd_point
    (plane : OrientedAffineHyperplane 3) (wave : ComplexMonochromaticPlaneWave)
    (t : Time) (v : plane.tangentSubmodule) :
    wave.carrier t ((v : EuclideanSpace ℝ (Fin 3)) +ᵥ plane.point) =
      Complex.exp (wave.boundaryExponent plane (t, v)) *
        wave.waveVector.spatialFactor plane.point := by
  rw [carrier, ComplexWaveVector.spatialFactor_vadd, ← mul_assoc,
    ← Complex.exp_add]
  congr 1
  simp only [boundaryExponent_apply]
  ring_nf

end ComplexMonochromaticPlaneWave

end
end ThreeDimension
end Electromagnetism
