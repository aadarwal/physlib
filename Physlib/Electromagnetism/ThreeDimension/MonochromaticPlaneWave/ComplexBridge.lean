/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Electromagnetism.ThreeDimension.MonochromaticPlaneWave.Basic
public import Physlib.Electromagnetism.ThreeDimension.MonochromaticPlaneWave.ComplexBasic

/-!
# Bridge from real-quadrature to complex-amplitude plane waves

## i. Overview

This file embeds the existing real-quadrature `MonochromaticPlaneWave` into
`ComplexMonochromaticPlaneWave` and proves that the two representations construct exactly the same
ordinary real electromagnetic fields.

The embedded spatial wave vector is the componentwise complexification of the existing real
vector `kappa * n`. The electric amplitude is `electricReal + I * electricImag`. With Physlib's
carrier convention, componentwise real realization therefore gives
`cos theta * electricReal - sin theta * electricImag`. The magnetic amplitude remains derived from
the complex relation `B0 = omega⁻¹ (K cross E0)`; a theorem proves that it is exactly the
complexification of the two existing magnetic quadratures rather than storing that agreement as
an assumption.

The bridge proves equality of `E`, `D`, `B`, and `H`. It does not claim equality of hidden complex
states, potentials, gauges, power normalizations, or any interface interpretation.

## ii. Key results

- `ComplexMonochromaticPlaneWave.ofReal`: embed an existing real-quadrature wave.
- `ComplexMonochromaticPlaneWave.ofReal_electricAmplitude_ne_zero_iff`: the embedded complex
  amplitude is nonzero exactly when at least one real quadrature is nonzero.
- `ComplexMonochromaticPlaneWave.ofReal_carrier`: exact carrier-phase agreement.
- `ComplexMonochromaticPlaneWave.ofReal_electricField`: exact electric-field agreement.
- `ComplexMonochromaticPlaneWave.isTransverse_ofReal_iff`: exact agreement of the real and
  complex-bilinear transversality predicates.
- `ComplexMonochromaticPlaneWave.ofReal_magneticAmplitude`: derive the existing magnetic
  quadratures from the complex cross-product law.
- `ComplexMonochromaticPlaneWave.ofReal_magneticInduction`: exact magnetic-induction agreement.
- `ComplexMonochromaticPlaneWave.ofReal_electricDisplacement` and
  `ComplexMonochromaticPlaneWave.ofReal_magneticFieldStrength`: exact constitutive-field agreement.

## iii. Table of contents

- A. Real-wave embedding
- B. Carrier agreement
- C. Electric-field agreement
- D. Magnetic-field agreement
- E. Constitutive-field agreement

## iv. References

This is an internal representation theorem between Physlib definitions. No external
formal-development source is copied or translated here.
-/

@[expose] public section

namespace Electromagnetism
namespace ThreeDimension
namespace ComplexMonochromaticPlaneWave

open Space Time InnerProductSpace Matrix ClassicalMechanics

noncomputable section

/-!

## A. Real-wave embedding

-/

/-- Embed an existing real-quadrature monochromatic plane wave as complex wave-vector and
electric-amplitude data. -/
def ofReal (wave : MonochromaticPlaneWave) : ComplexMonochromaticPlaneWave where
  angularFrequency := wave.angularFrequency
  angularFrequency_pos := wave.angularFrequency_pos
  waveVector := ComplexWaveVector.ofReal wave.waveVector
  electricAmplitude := ComplexWaveVector.ofReal wave.electricReal +
    Complex.I • ComplexWaveVector.ofReal wave.electricImag

/-- The embedded complex wave vector is exactly the complexification of the real wave vector. -/
@[simp]
lemma ofReal_waveVector (wave : MonochromaticPlaneWave) :
    (ofReal wave).waveVector = ComplexWaveVector.ofReal wave.waveVector := rfl

/-- The embedded wave has the existing angular frequency. -/
@[simp]
lemma ofReal_angularFrequency (wave : MonochromaticPlaneWave) :
    (ofReal wave).angularFrequency = wave.angularFrequency := rfl

/-- The embedded electric amplitude combines the existing real and imaginary quadratures. -/
@[simp]
lemma ofReal_electricAmplitude (wave : MonochromaticPlaneWave) :
    (ofReal wave).electricAmplitude = ComplexWaveVector.ofReal wave.electricReal +
      Complex.I • ComplexWaveVector.ofReal wave.electricImag := rfl

private lemma ofReal_electricAmplitude_eq_zero_iff (wave : MonochromaticPlaneWave) :
    (ofReal wave).electricAmplitude = 0 ↔
      wave.electricReal = 0 ∧ wave.electricImag = 0 := by
  rw [ofReal_electricAmplitude]
  constructor
  · intro h
    constructor
    · ext i
      have hi := congrArg (fun v : EuclideanSpace ℂ (Fin 3) ↦ (v i).re) h
      simpa using hi
    · ext i
      have hi := congrArg (fun v : EuclideanSpace ℂ (Fin 3) ↦ (v i).im) h
      simpa using hi
  · rintro ⟨hReal, hImag⟩
    simp [hReal, hImag]

/-- The embedded complex electric amplitude is nonzero exactly when at least one real quadrature
is nonzero. -/
lemma ofReal_electricAmplitude_ne_zero_iff (wave : MonochromaticPlaneWave) :
    (ofReal wave).electricAmplitude ≠ 0 ↔
      wave.electricReal ≠ 0 ∨ wave.electricImag ≠ 0 := by
  rw [ne_eq, ofReal_electricAmplitude_eq_zero_iff, not_and_or]

/-- The embedded bilinear electric pairing packages the real pairings of both quadratures. -/
lemma bilinearDot_ofReal_electricAmplitude (wave : MonochromaticPlaneWave) :
    ComplexWaveVector.bilinearDot (ofReal wave).waveVector
        (ofReal wave).electricAmplitude =
      (⟪wave.waveVector, wave.electricReal⟫_ℝ : ℂ) +
        Complex.I * (⟪wave.waveVector, wave.electricImag⟫_ℝ : ℂ) := by
  rw [ofReal_waveVector, ofReal_electricAmplitude,
    ComplexWaveVector.bilinearDot_add_right,
    ComplexWaveVector.bilinearDot_smul_right,
    ComplexWaveVector.bilinearDot_ofReal,
    ComplexWaveVector.bilinearDot_ofReal]

/-- The embedded complex amplitude is bilinearly transverse exactly when both existing real
quadratures are transverse to the propagation direction. -/
lemma isTransverse_ofReal_iff (wave : MonochromaticPlaneWave) :
    (ofReal wave).IsTransverse ↔ wave.IsTransverse := by
  rw [IsTransverse, bilinearDot_ofReal_electricAmplitude]
  constructor
  · intro h
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    norm_num at hre him
    rw [MonochromaticPlaneWave.waveVector, inner_smul_left] at hre him
    exact ⟨(mul_eq_zero.mp hre).resolve_left wave.waveNumber_ne_zero,
      (mul_eq_zero.mp him).resolve_left wave.waveNumber_ne_zero⟩
  · rintro ⟨hreal, himag⟩
    rw [MonochromaticPlaneWave.waveVector, inner_smul_left, inner_smul_left,
      hreal, himag]
    simp

/-!

## B. Carrier agreement

-/

/-- Spatial pairing of an embedded real wave vector is the real Euclidean wave-vector pairing. -/
lemma ofReal_spatialPairing (wave : MonochromaticPlaneWave) (x : Space) :
    (ofReal wave).waveVector.spatialPairing x =
      (⟪Space.basis.repr x, wave.waveVector⟫_ℝ : ℂ) := by
  rw [ComplexWaveVector.spatialPairing, ofReal_waveVector,
    ComplexWaveVector.bilinearDot_ofReal, real_inner_comm]

/-- The embedded wave has exactly the existing real carrier phase. -/
lemma ofReal_carrier (wave : MonochromaticPlaneWave) (t : Time) (x : Space) :
    (ofReal wave).carrier t x =
      Complex.exp ((wave.carrierPhase t x : ℂ) * Complex.I) := by
  rw [carrier_eq_exp, ofReal_spatialPairing, wave.carrierPhase_eq_waveVector]
  simp only [ofReal]
  congr 2
  push_cast
  rfl

/-!

## C. Electric-field agreement

-/

/-- Realizing a complex carrier against real and imaginary vector quadratures gives the cosine
real quadrature minus the sine imaginary quadrature. -/
lemma realPart_exp_mul_ofReal_add_I_smul_ofReal (carrierPhase : ℝ)
    (u v : EuclideanSpace ℝ (Fin 3)) :
    ComplexWaveVector.realPart
      (Complex.exp ((carrierPhase : ℂ) * Complex.I) •
        (ComplexWaveVector.ofReal u + Complex.I • ComplexWaveVector.ofReal v)) =
      Real.cos carrierPhase • u - Real.sin carrierPhase • v := by
  ext i
  simp [ComplexWaveVector.realPart, ComplexWaveVector.ofReal, Complex.mul_re,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, sub_eq_add_neg]

/-- The electric field of an embedded wave is exactly the existing real electric field. -/
lemma ofReal_electricField (wave : MonochromaticPlaneWave) :
    (ofReal wave).electricField = wave.electricField := by
  funext t x
  rw [wave.electricField_apply]
  simp only [electricField, realFieldOfAmplitude, ofReal_carrier,
    ofReal_electricAmplitude]
  exact realPart_exp_mul_ofReal_add_I_smul_ofReal (wave.carrierPhase t x)
    wave.electricReal wave.electricImag

/-!

## D. Magnetic-field agreement

-/

/-- The magnetic amplitude derived from the embedded complex data is exactly the combination of
the existing real magnetic quadratures. -/
lemma ofReal_magneticAmplitude (wave : MonochromaticPlaneWave) :
    (ofReal wave).magneticAmplitude =
      ComplexWaveVector.ofReal wave.magneticReal +
        Complex.I • ComplexWaveVector.ofReal wave.magneticImag := by
  rw [magneticAmplitude, ofReal_waveVector, ofReal_electricAmplitude,
    MonochromaticPlaneWave.waveVector, ComplexWaveVector.ofReal_smul,
    complexCross_smul_left, complexCross_add_right, complexCross_smul_right,
    complexCross_ofReal, complexCross_ofReal, MonochromaticPlaneWave.magneticReal,
    MonochromaticPlaneWave.magneticImag, ComplexWaveVector.ofReal_smul,
    ComplexWaveVector.ofReal_smul]
  ext i
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    ComplexWaveVector.ofReal_apply, ofReal]
  push_cast
  ring

/-- The magnetic induction of an embedded wave is exactly the existing real magnetic induction. -/
lemma ofReal_magneticInduction (wave : MonochromaticPlaneWave) :
    (ofReal wave).magneticInduction = wave.magneticInduction := by
  funext t x
  rw [wave.magneticInduction_apply]
  simp only [magneticInduction, realFieldOfAmplitude, ofReal_carrier,
    ofReal_magneticAmplitude]
  exact realPart_exp_mul_ofReal_add_I_smul_ofReal (wave.carrierPhase t x)
    wave.magneticReal wave.magneticImag

/-!

## E. Constitutive-field agreement

-/

/-- The electric displacement of an embedded wave is exactly the existing constitutive field. -/
lemma ofReal_electricDisplacement (wave : MonochromaticPlaneWave)
    (medium : HomogeneousIsotropicMedium) :
    (ofReal wave).electricDisplacement medium = wave.electricDisplacement medium := by
  rw [electricDisplacement, MonochromaticPlaneWave.electricDisplacement,
    ofReal_electricField]

/-- The magnetic field strength of an embedded wave is exactly the existing constitutive field. -/
lemma ofReal_magneticFieldStrength (wave : MonochromaticPlaneWave)
    (medium : HomogeneousIsotropicMedium) :
    (ofReal wave).magneticFieldStrength medium = wave.magneticFieldStrength medium := by
  rw [magneticFieldStrength, MonochromaticPlaneWave.magneticFieldStrength,
    ofReal_magneticInduction]

end

end ComplexMonochromaticPlaneWave
end ThreeDimension
end Electromagnetism
