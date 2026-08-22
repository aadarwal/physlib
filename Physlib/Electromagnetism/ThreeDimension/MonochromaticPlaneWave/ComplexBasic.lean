/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.ClassicalMechanics.WaveEquation.ComplexWaveVector
public import Physlib.Electromagnetism.Media.HomogeneousIsotropic

/-!
# Real electromagnetic fields from complex plane-wave data

## i. Overview

This file defines an off-shell monochromatic plane-wave candidate with a positive real angular
frequency, a complex spatial wave vector, and a complex electric amplitude. The complex data is
calculation data for constructing ordinary real `E`, `D`, `B`, and `H` fields; it is not a second
complex Maxwell theory or a competing Optics phasor, Jones, coherency, or modal state API.

The carrier convention is
`exp (I * omega * t) * exp (-I * (K dot x))`, equivalently
`exp (I * (omega * t - K dot x))`. The spatial factor is the one defined by
`ClassicalMechanics.ComplexWaveVector`, so its phase/attenuation decomposition and exact decay
laws are reused directly. Physical fields are obtained by taking componentwise real parts.

The stored electric amplitude is the coefficient relative to the selected spatial origin and
carrier phase. Translating that reference changes the coefficient by a complex spatial factor and,
for attenuating wave vectors, can change its modulus. It is not an intrinsic normalized Jones
amplitude, irradiance, or power.

The magnetic-induction amplitude is the Faraday-compatible candidate
`B0 = omega⁻¹ (K cross E0)`. This relation is built into the construction. Transversality,
material dispersion, and Maxwell satisfaction remain separate later results.

No interface side, square-root branch, transmitted or outgoing role, evanescent-wave role,
electromagnetic power, handedness, finite-beam, or gauge interpretation is assigned here.

## ii. Key results

- `ComplexMonochromaticPlaneWave.carrier_eq_exp`: the connected carrier convention.
- `ComplexMonochromaticPlaneWave.realFieldOfAmplitude`: the shared real-field realization spine.
- `ComplexMonochromaticPlaneWave.electricField_apply`: componentwise real electric realization.
- `ComplexMonochromaticPlaneWave.IsTransverse`: complex-bilinear electric transversality.
- `ComplexMonochromaticPlaneWave.angularFrequency_smul_magneticAmplitude`: the built-in
  Faraday-amplitude relation without division.
- `ComplexMonochromaticPlaneWave.bilinearDot_waveVector_magneticAmplitude`: built-in magnetic
  transversality.
- `ComplexMonochromaticPlaneWave.carrier_vadd_positiveNormalDecay`: exact carrier decay inherited
  from complex-wave-vector geometry.
- `ComplexMonochromaticPlaneWave.isConstitutive`: the four real fields obey the supplied material
  constitutive relations.

## iii. Table of contents

- A. Complex-amplitude carrier data
- B. Complex cross product
- C. Carrier geometry
- D. Real electromagnetic fields
- E. Positive-normal decay
- F. Constitutive fields

## iv. References

The construction extends the existing Physlib monochromatic carrier convention. No external
formal-development source is copied or translated here.
-/

@[expose] public section

namespace Electromagnetism
namespace ThreeDimension

open Space Time Matrix InnerProductSpace ClassicalMechanics

noncomputable section

/-!

## A. Complex-amplitude carrier data

-/

/-- Off-shell data for a real electromagnetic plane-wave candidate constructed from complex
spatial and electric amplitudes.

The angular frequency is positive. The complex wave vector and electric amplitude are otherwise
independent: transversality, material dispersion, and Maxwell equations are not structure
invariants. -/
structure ComplexMonochromaticPlaneWave where
  /-- The positive real angular frequency. -/
  angularFrequency : ℝ
  /-- The angular frequency is strictly positive. -/
  angularFrequency_pos : 0 < angularFrequency
  /-- The complex spatial wave vector. -/
  waveVector : ComplexWaveVector 3
  /-- The complex electric-field amplitude relative to the selected spatial origin and carrier
  phase. -/
  electricAmplitude : EuclideanSpace ℂ (Fin 3)

namespace ComplexMonochromaticPlaneWave

/-!

## B. Complex cross product

-/

/-- The complex-bilinear coordinate cross product on three-dimensional complex Euclidean
vectors. -/
def complexCross (u v : EuclideanSpace ℂ (Fin 3)) : EuclideanSpace ℂ (Fin 3) :=
  WithLp.toLp 2 (crossProduct u v)

@[simp]
lemma complexCross_apply (u v : EuclideanSpace ℂ (Fin 3)) (i : Fin 3) :
    complexCross u v i = crossProduct u v i := rfl

/-- The complex cross product is additive in its second argument. -/
lemma complexCross_add_right (u v w : EuclideanSpace ℂ (Fin 3)) :
    complexCross u (v + w) = complexCross u v + complexCross u w := by
  ext i
  fin_cases i <;> simp [complexCross, crossProduct] <;> ring

/-- The complex cross product commutes with complex scaling in its second argument. -/
lemma complexCross_smul_right (c : ℂ) (u v : EuclideanSpace ℂ (Fin 3)) :
    complexCross u (c • v) = c • complexCross u v := by
  ext i
  fin_cases i <;> simp [complexCross, crossProduct]

/-- The complex cross product commutes with complex scaling in its first argument. -/
lemma complexCross_smul_left (c : ℂ) (u v : EuclideanSpace ℂ (Fin 3)) :
    complexCross (c • u) v = c • complexCross u v := by
  ext i
  fin_cases i <;> simp [complexCross, crossProduct]

/-- Componentwise complexification commutes with the three-dimensional real cross product. -/
lemma complexCross_ofReal (u v : WaveVector 3) :
    complexCross (ComplexWaveVector.ofReal u) (ComplexWaveVector.ofReal v) =
      ComplexWaveVector.ofReal (u ⨯ₑ₃ v) := by
  ext i
  fin_cases i <;>
    simp [complexCross, ComplexWaveVector.ofReal, crossProduct]

/-- The complex-bilinear pairing of a vector with its cross product is zero. -/
lemma bilinearDot_self_complexCross (u v : EuclideanSpace ℂ (Fin 3)) :
    ComplexWaveVector.bilinearDot u (complexCross u v) = 0 := by
  exact dot_self_cross u v

/-- The complex vector triple-product identity. -/
lemma complexCross_complexCross (u v w : EuclideanSpace ℂ (Fin 3)) :
    complexCross u (complexCross v w) =
      ComplexWaveVector.bilinearDot u w • v -
        ComplexWaveVector.bilinearDot u v • w := by
  ext i
  fin_cases i <;>
    simp [complexCross, ComplexWaveVector.bilinearDot, Fin.sum_univ_three,
      crossProduct] <;>
    ring

/-!

## C. Carrier geometry

-/

/-- The complex carrier coefficient using Physlib's positive-time, negative-space convention.

Its two factors keep temporal oscillation separate from the shared complex-wave-vector spatial
factor. -/
def carrier (wave : ComplexMonochromaticPlaneWave) (t : Time) (x : Space) : ℂ :=
  Complex.exp (((wave.angularFrequency * t : ℝ) : ℂ) * Complex.I) *
    wave.waveVector.spatialFactor x

/-- The complex carrier is equivalently one exponential of `I * (omega * t - K dot x)`. -/
lemma carrier_eq_exp (wave : ComplexMonochromaticPlaneWave) (t : Time) (x : Space) :
    wave.carrier t x = Complex.exp
      ((((wave.angularFrequency * t : ℝ) : ℂ) - wave.waveVector.spatialPairing x) *
        Complex.I) := by
  rw [carrier, ComplexWaveVector.spatialFactor, ← Complex.exp_add]
  congr 1
  ring

/-- Positive angular frequency is nonzero. -/
lemma angularFrequency_ne_zero (wave : ComplexMonochromaticPlaneWave) :
    wave.angularFrequency ≠ 0 :=
  ne_of_gt wave.angularFrequency_pos

/-- The complex carrier never vanishes. -/
lemma carrier_ne_zero (wave : ComplexMonochromaticPlaneWave) (t : Time) (x : Space) :
    wave.carrier t x ≠ 0 := by
  exact mul_ne_zero (Complex.exp_ne_zero _) (wave.waveVector.spatialFactor_ne_zero x)

/-- A real displacement multiplies the carrier by its complex spatial displacement factor. -/
lemma carrier_vadd (wave : ComplexMonochromaticPlaneWave)
    (v : WaveVector 3) (t : Time) (x : Space) :
    wave.carrier t (v +ᵥ x) =
      Complex.exp (-Complex.I *
        ComplexWaveVector.bilinearDot wave.waveVector (ComplexWaveVector.ofReal v)) *
        wave.carrier t x := by
  rw [carrier, carrier, ComplexWaveVector.spatialFactor_vadd]
  ring

/-!

## D. Real electromagnetic fields

-/

/-- Construct an ordinary real vector field by taking the componentwise real part of the shared
complex carrier times a supplied complex amplitude.

This is an electromagnetic calculation spine for real fields, not a bundled phasor state or a
complex Maxwell field. -/
def realFieldOfAmplitude (wave : ComplexMonochromaticPlaneWave)
    (amplitude : EuclideanSpace ℂ (Fin 3)) : Time → Space → EuclideanSpace ℝ (Fin 3) :=
  fun t x ↦ ComplexWaveVector.realPart (wave.carrier t x • amplitude)

/-- The ordinary real electric field obtained from the stored electric amplitude. -/
def electricField (wave : ComplexMonochromaticPlaneWave) : ElectricField :=
  wave.realFieldOfAmplitude wave.electricAmplitude

/-- The magnetic-induction amplitude fixed by the candidate harmonic Faraday relation
`B0 = omega⁻¹ (K cross E0)`. -/
def magneticAmplitude (wave : ComplexMonochromaticPlaneWave) : EuclideanSpace ℂ (Fin 3) :=
  (wave.angularFrequency : ℂ)⁻¹ • complexCross wave.waveVector wave.electricAmplitude

/-- Multiplying the compatible magnetic amplitude by angular frequency recovers the wave vector
crossed with the electric amplitude. -/
lemma angularFrequency_smul_magneticAmplitude (wave : ComplexMonochromaticPlaneWave) :
    (wave.angularFrequency : ℂ) • wave.magneticAmplitude =
      complexCross wave.waveVector wave.electricAmplitude := by
  rw [magneticAmplitude, smul_smul]
  have hfrequency : (wave.angularFrequency : ℂ) ≠ 0 := by
    exact_mod_cast wave.angularFrequency_ne_zero
  rw [mul_inv_cancel₀ hfrequency, one_smul]

/-- The ordinary real magnetic induction obtained from the shared carrier and the constructed
magnetic amplitude. -/
def magneticInduction (wave : ComplexMonochromaticPlaneWave) : MagneticInductionField :=
  wave.realFieldOfAmplitude wave.magneticAmplitude

/-- The electric displacement supplied by a homogeneous isotropic medium. -/
def electricDisplacement (wave : ComplexMonochromaticPlaneWave)
    (medium : HomogeneousIsotropicMedium) : ElectricDisplacementField :=
  medium.electricDisplacement wave.electricField

/-- The magnetic field strength supplied by a homogeneous isotropic medium. -/
def magneticFieldStrength (wave : ComplexMonochromaticPlaneWave)
    (medium : HomogeneousIsotropicMedium) : MagneticFieldStrength :=
  medium.magneticFieldStrength wave.magneticInduction

/-- A field constructed from a complex amplitude is realized componentwise. -/
@[simp]
lemma realFieldOfAmplitude_apply (wave : ComplexMonochromaticPlaneWave)
    (amplitude : EuclideanSpace ℂ (Fin 3)) (t : Time) (x : Space) (i : Fin 3) :
    wave.realFieldOfAmplitude amplitude t x i = (wave.carrier t x * amplitude i).re := rfl

/-- Electric-field realization is componentwise real part of carrier times amplitude. -/
@[simp]
lemma electricField_apply (wave : ComplexMonochromaticPlaneWave)
    (t : Time) (x : Space) (i : Fin 3) :
    wave.electricField t x i = (wave.carrier t x * wave.electricAmplitude i).re := rfl

/-- Magnetic-induction realization is componentwise real part of carrier times amplitude. -/
@[simp]
lemma magneticInduction_apply (wave : ComplexMonochromaticPlaneWave)
    (t : Time) (x : Space) (i : Fin 3) :
    wave.magneticInduction t x i = (wave.carrier t x * wave.magneticAmplitude i).re := rfl

/-- The electric amplitude is transverse under the complex-bilinear wave-vector pairing. -/
def IsTransverse (wave : ComplexMonochromaticPlaneWave) : Prop :=
  ComplexWaveVector.bilinearDot wave.waveVector wave.electricAmplitude = 0

/-- The electric field is the carrier-real-part weighted real amplitude minus the
carrier-imaginary-part weighted imaginary amplitude. -/
lemma electricField_eq_carrier_re_smul_realPart_sub_carrier_im_smul_imaginaryPart
    (wave : ComplexMonochromaticPlaneWave) (t : Time) (x : Space) :
    wave.electricField t x =
      (wave.carrier t x).re • ComplexWaveVector.realPart wave.electricAmplitude -
        (wave.carrier t x).im • ComplexWaveVector.imaginaryPart wave.electricAmplitude := by
  ext i
  simp [Complex.mul_re]

/-- The magnetic amplitude is bilinearly transverse to the complex wave vector without an
electric-transversality hypothesis. -/
lemma bilinearDot_waveVector_magneticAmplitude (wave : ComplexMonochromaticPlaneWave) :
    ComplexWaveVector.bilinearDot wave.waveVector wave.magneticAmplitude = 0 := by
  rw [magneticAmplitude, ComplexWaveVector.bilinearDot_smul_right,
    bilinearDot_self_complexCross, mul_zero]

/-!

## E. Positive-normal decay

-/

/-- If the wave vector is supplied by positive-normal decay data, displacement in that direction
multiplies the complete carrier by the exact real decay factor. -/
lemma carrier_vadd_positiveNormalDecay (wave : ComplexMonochromaticPlaneWave)
    {normal : Direction 3} (data : ComplexWaveVector.PositiveNormalDecayWaveVector normal)
    (hwaveVector : wave.waveVector = data.waveVector) (u : ℝ) (t : Time) (x : Space) :
    wave.carrier t (u • data.normalVector +ᵥ x) =
      (Real.exp (-data.decayRate * u) : ℂ) * wave.carrier t x := by
  rw [carrier, carrier, hwaveVector, data.spatialFactor_vadd]
  ring

/-- Positive-normal decay of the complex wave vector gives the same exact real scaling to every
real field constructed from the shared carrier. -/
lemma realFieldOfAmplitude_vadd_positiveNormalDecay (wave : ComplexMonochromaticPlaneWave)
    (amplitude : EuclideanSpace ℂ (Fin 3))
    {normal : Direction 3} (data : ComplexWaveVector.PositiveNormalDecayWaveVector normal)
    (hwaveVector : wave.waveVector = data.waveVector) (u : ℝ) (t : Time) (x : Space) :
    wave.realFieldOfAmplitude amplitude t (u • data.normalVector +ᵥ x) =
      Real.exp (-data.decayRate * u) • wave.realFieldOfAmplitude amplitude t x := by
  ext i
  simp only [realFieldOfAmplitude_apply, PiLp.smul_apply, smul_eq_mul]
  rw [wave.carrier_vadd_positiveNormalDecay data hwaveVector]
  rw [mul_assoc, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- Positive-normal decay of the complex wave vector gives the same exact real scaling of the
physical electric field. -/
lemma electricField_vadd_positiveNormalDecay (wave : ComplexMonochromaticPlaneWave)
    {normal : Direction 3} (data : ComplexWaveVector.PositiveNormalDecayWaveVector normal)
    (hwaveVector : wave.waveVector = data.waveVector) (u : ℝ) (t : Time) (x : Space) :
    wave.electricField t (u • data.normalVector +ᵥ x) =
      Real.exp (-data.decayRate * u) • wave.electricField t x := by
  exact wave.realFieldOfAmplitude_vadd_positiveNormalDecay
    wave.electricAmplitude data hwaveVector u t x

/-- Positive-normal decay of the complex wave vector gives the same exact real scaling of the
physical magnetic induction. -/
lemma magneticInduction_vadd_positiveNormalDecay (wave : ComplexMonochromaticPlaneWave)
    {normal : Direction 3} (data : ComplexWaveVector.PositiveNormalDecayWaveVector normal)
    (hwaveVector : wave.waveVector = data.waveVector) (u : ℝ) (t : Time) (x : Space) :
    wave.magneticInduction t (u • data.normalVector +ᵥ x) =
      Real.exp (-data.decayRate * u) • wave.magneticInduction t x := by
  exact wave.realFieldOfAmplitude_vadd_positiveNormalDecay
    wave.magneticAmplitude data hwaveVector u t x

/-!

## F. Constitutive fields

-/

/-- The canonically constructed real `E`, `D`, `B`, and `H` fields obey the supplied homogeneous
isotropic medium's constitutive equations. This does not assert any Maxwell equation. -/
lemma isConstitutive (wave : ComplexMonochromaticPlaneWave)
    (medium : HomogeneousIsotropicMedium) :
    medium.IsConstitutive wave.electricField (wave.electricDisplacement medium)
      wave.magneticInduction (wave.magneticFieldStrength medium) :=
  medium.isConstitutive_electricDisplacement_magneticFieldStrength
    wave.electricField wave.magneticInduction

end ComplexMonochromaticPlaneWave

end

end ThreeDimension
end Electromagnetism
