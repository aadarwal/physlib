/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.ClassicalMechanics.WaveEquation.HarmonicWave

/-!
# Complex wave vectors and spatial decay

## i. Overview

This file extends real wave vectors with complex spatial wave vectors. A complex wave vector is
decomposed as `k = q - I * a`, where `q` is its real phase vector and `a` is its real attenuation
vector. Its pairing is the complex-bilinear coordinate dot product, with no conjugation in either
slot. This distinction is essential: the Hermitian inner product does not express either complex
transversality or the plane-wave dispersion relation.

The spatial factor follows Physlib's positive-time, negative-space convention,
`exp (-I * (k dot x))`. Under the decomposition above it factors as
`exp (-a dot x) * exp (-I * (q dot x))`. Consequently the vector
`q - I * alpha * n`, for positive `alpha` and a unit direction `n` transverse to `q`, decays by
the real factor `exp (-alpha * u)` after displacement by `u` in the positive `n` direction.

The decay construction is interface-independent. It does not identify a half-space, select a
square-root branch, describe a transmitted wave, or make a power-flow claim.

## ii. Key results

- `ComplexWaveVector.ofPhaseAttenuation`: construct `q - I * a`.
- `ComplexWaveVector.ofPhaseAttenuation_phaseVector_attenuationVector`: reconstruct a vector from
  its phase and attenuation vectors.
- `ComplexWaveVector.spatialFactor_ofPhaseAttenuation`: separate decay and phase.
- `PositiveNormalDecayWaveVector.spatialFactor_vadd`: exact positive-normal decay.
- `PositiveNormalDecayWaveVector.tendsto_spatialFactor_vadd_atTop`: decay to zero at increasing
  depth.

## iii. Table of contents

- A. Complex Euclidean wave vectors
- B. Bilinear pairing
- C. Phase and attenuation decomposition
- D. Spatial factors
- E. Positive-normal decay data

## iv. References

The definitions use the existing Physlib carrier convention and Mathlib's complex exponential.
No external formal-development source is copied or translated here.
-/

@[expose] public section

namespace ClassicalMechanics

open Space InnerProductSpace Matrix

noncomputable section

/-!

## A. Complex Euclidean wave vectors

-/

/-- A complex wave vector in `d`-dimensional Euclidean coordinates. -/
abbrev ComplexWaveVector (d : ℕ := 3) := EuclideanSpace ℂ (Fin d)

namespace ComplexWaveVector

variable {d : ℕ}

/-- Regard a real wave vector componentwise as a complex wave vector. -/
def ofReal (v : WaveVector d) : ComplexWaveVector d :=
  WithLp.toLp 2 fun i ↦ (v i : ℂ)

/-- The componentwise real part of a complex wave vector. -/
def realPart (k : ComplexWaveVector d) : WaveVector d :=
  WithLp.toLp 2 fun i ↦ (k i).re

/-- The componentwise imaginary part of a complex wave vector. -/
def imaginaryPart (k : ComplexWaveVector d) : WaveVector d :=
  WithLp.toLp 2 fun i ↦ (k i).im

@[simp]
lemma ofReal_apply (v : WaveVector d) (i : Fin d) :
    ofReal v i = (v i : ℂ) := rfl

@[simp]
lemma realPart_apply (k : ComplexWaveVector d) (i : Fin d) :
    realPart k i = (k i).re := rfl

@[simp]
lemma imaginaryPart_apply (k : ComplexWaveVector d) (i : Fin d) :
    imaginaryPart k i = (k i).im := rfl

@[simp]
lemma realPart_ofReal (v : WaveVector d) :
    realPart (ofReal v) = v := by
  ext i
  simp

@[simp]
lemma imaginaryPart_ofReal (v : WaveVector d) :
    imaginaryPart (ofReal v) = 0 := by
  ext i
  simp

@[simp]
lemma ofReal_zero : ofReal (0 : WaveVector d) = 0 := by
  ext i
  simp

@[simp]
lemma ofReal_add (u v : WaveVector d) :
    ofReal (u + v) = ofReal u + ofReal v := by
  ext i
  simp

/-- Real scalar multiplication commutes with componentwise complexification. -/
lemma ofReal_smul (c : ℝ) (v : WaveVector d) :
    ofReal (c • v) = (c : ℂ) • ofReal v := by
  ext i
  simp

/-!

## B. Bilinear pairing

-/

/-- The complex-bilinear Euclidean coordinate pairing, with no conjugation in either slot.

This is deliberately not `inner ℂ`: the Hermitian inner product conjugates one slot and is not
the pairing used in complex plane-wave transversality or dispersion. -/
def bilinearDot (u v : ComplexWaveVector d) : ℂ :=
  ∑ i, u i * v i

/-- The bilinear pairing is symmetric. -/
lemma bilinearDot_comm (u v : ComplexWaveVector d) :
    bilinearDot u v = bilinearDot v u := by
  simp only [bilinearDot]
  apply Finset.sum_congr rfl
  intro i _
  ring

@[simp]
lemma bilinearDot_zero_left (v : ComplexWaveVector d) :
    bilinearDot 0 v = 0 := by
  simp [bilinearDot]

@[simp]
lemma bilinearDot_zero_right (u : ComplexWaveVector d) :
    bilinearDot u 0 = 0 := by
  rw [bilinearDot_comm, bilinearDot_zero_left]

/-- The bilinear pairing is additive in its first slot. -/
lemma bilinearDot_add_left (u v w : ComplexWaveVector d) :
    bilinearDot (u + v) w = bilinearDot u w + bilinearDot v w := by
  simp [bilinearDot, Finset.sum_add_distrib, add_mul]

/-- The bilinear pairing is additive in its second slot. -/
lemma bilinearDot_add_right (u v w : ComplexWaveVector d) :
    bilinearDot u (v + w) = bilinearDot u v + bilinearDot u w := by
  rw [bilinearDot_comm, bilinearDot_add_left, bilinearDot_comm u v,
    bilinearDot_comm u w]

/-- The bilinear pairing commutes with subtraction in its second slot. -/
lemma bilinearDot_sub_right (u v w : ComplexWaveVector d) :
    bilinearDot u (v - w) = bilinearDot u v - bilinearDot u w := by
  exact dotProduct_sub u v w

/-- The bilinear pairing commutes with subtraction in its first slot. -/
lemma bilinearDot_sub_left (u v w : ComplexWaveVector d) :
    bilinearDot (u - v) w = bilinearDot u w - bilinearDot v w := by
  rw [bilinearDot_comm, bilinearDot_sub_right, bilinearDot_comm u w,
    bilinearDot_comm v w]

/-- The bilinear pairing commutes with complex scaling in its first slot. -/
lemma bilinearDot_smul_left (c : ℂ) (u v : ComplexWaveVector d) :
    bilinearDot (c • u) v = c * bilinearDot u v := by
  rw [bilinearDot, bilinearDot, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [PiLp.smul_apply, smul_eq_mul]
  ring

/-- The bilinear pairing commutes with complex scaling in its second slot. -/
lemma bilinearDot_smul_right (c : ℂ) (u v : ComplexWaveVector d) :
    bilinearDot u (c • v) = c * bilinearDot u v := by
  rw [bilinearDot_comm, bilinearDot_smul_left, bilinearDot_comm]

/-- Complexification turns the bilinear complex pairing into the real Euclidean inner product. -/
lemma bilinearDot_ofReal (u v : WaveVector d) :
    bilinearDot (ofReal u) (ofReal v) = (⟪u, v⟫_ℝ : ℂ) := by
  rw [bilinearDot, PiLp.inner_apply, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [RCLike.inner_apply, mul_comm]

/-!

## C. Phase and attenuation decomposition

-/

/-- The real phase vector of a complex wave vector. -/
def phaseVector (k : ComplexWaveVector d) : WaveVector d :=
  realPart k

/-- The real attenuation vector of a complex wave vector.

The sign is chosen so that `k = phaseVector k - I * attenuationVector k`. -/
def attenuationVector (k : ComplexWaveVector d) : WaveVector d :=
  -imaginaryPart k

/-- Construct the complex wave vector `q - I * a` from real phase and attenuation vectors. -/
def ofPhaseAttenuation (q a : WaveVector d) : ComplexWaveVector d :=
  ofReal q - Complex.I • ofReal a

@[simp]
lemma ofPhaseAttenuation_apply (q a : WaveVector d) (i : Fin d) :
    ofPhaseAttenuation q a i = (q i : ℂ) - Complex.I * (a i : ℂ) := rfl

@[simp]
lemma phaseVector_ofPhaseAttenuation (q a : WaveVector d) :
    phaseVector (ofPhaseAttenuation q a) = q := by
  ext i
  simp [phaseVector]

@[simp]
lemma attenuationVector_ofPhaseAttenuation (q a : WaveVector d) :
    attenuationVector (ofPhaseAttenuation q a) = a := by
  ext i
  simp [attenuationVector]

/-- Every complex wave vector is reconstructed from its phase and attenuation vectors. -/
@[simp]
lemma ofPhaseAttenuation_phaseVector_attenuationVector (k : ComplexWaveVector d) :
    ofPhaseAttenuation k.phaseVector k.attenuationVector = k := by
  ext i
  simp [ofPhaseAttenuation, phaseVector, attenuationVector, realPart, imaginaryPart]
  apply Complex.ext <;> simp

/-- A complexified real vector has itself as phase vector. -/
@[simp]
lemma phaseVector_ofReal (q : WaveVector d) :
    phaseVector (ofReal q) = q := by
  exact realPart_ofReal q

/-- A complexified real vector has zero attenuation. -/
@[simp]
lemma attenuationVector_ofReal (q : WaveVector d) :
    attenuationVector (ofReal q) = 0 := by
  simp [attenuationVector]

/-- Pairing `q - I * a` with a real vector gives its phase pairing minus `I` times its
attenuation pairing. -/
lemma bilinearDot_ofPhaseAttenuation_ofReal (q a x : WaveVector d) :
    bilinearDot (ofPhaseAttenuation q a) (ofReal x) =
      (⟪q, x⟫_ℝ : ℂ) - Complex.I * (⟪a, x⟫_ℝ : ℂ) := by
  rw [ofPhaseAttenuation, bilinearDot_sub_left,
    bilinearDot_smul_left, bilinearDot_ofReal, bilinearDot_ofReal]

/-- The bilinear square of `q - I * a` has its real quadratic part and imaginary mixed part
explicit. -/
lemma bilinearDot_ofPhaseAttenuation_self (q a : WaveVector d) :
    bilinearDot (ofPhaseAttenuation q a) (ofPhaseAttenuation q a) =
      (⟪q, q⟫_ℝ : ℂ) - (⟪a, a⟫_ℝ : ℂ) -
        2 * Complex.I * (⟪q, a⟫_ℝ : ℂ) := by
  rw [ofPhaseAttenuation, bilinearDot_sub_left, bilinearDot_sub_right,
    bilinearDot_sub_right, bilinearDot_smul_left, bilinearDot_smul_right,
    bilinearDot_smul_left, bilinearDot_smul_right, bilinearDot_ofReal,
    bilinearDot_ofReal, bilinearDot_ofReal, bilinearDot_ofReal, real_inner_comm a q]
  apply Complex.ext
  · simp [mul_comm]
  · simp [mul_comm]
    ring

/-!

## D. Spatial factors

-/

/-- The bilinear pairing of a complex wave vector with a point's real spatial coordinates. -/
def spatialPairing (k : ComplexWaveVector d) (x : Space d) : ℂ :=
  bilinearDot k (ofReal (Space.basis.repr x))

/-- The spatial plane-wave factor `exp (-I * (k dot x))`.

It is the spatial part of the full carrier `exp (I * (omega * t - k dot x))`. -/
def spatialFactor (k : ComplexWaveVector d) (x : Space d) : ℂ :=
  Complex.exp (-Complex.I * k.spatialPairing x)

/-- Spatial pairing respects displacement of a point by a real coordinate vector. -/
lemma spatialPairing_vadd (k : ComplexWaveVector d) (v : WaveVector d) (x : Space d) :
    k.spatialPairing (v +ᵥ x) =
      bilinearDot k (ofReal v) + k.spatialPairing x := by
  rw [spatialPairing, spatialPairing]
  have hrepr : Space.basis.repr (v +ᵥ x) = v + Space.basis.repr x := by
    ext i
    simp
  rw [hrepr, ofReal_add, bilinearDot_add_right]

/-- A real displacement multiplies the spatial factor by the corresponding displacement
factor. -/
lemma spatialFactor_vadd (k : ComplexWaveVector d) (v : WaveVector d) (x : Space d) :
    k.spatialFactor (v +ᵥ x) =
      Complex.exp (-Complex.I * bilinearDot k (ofReal v)) * k.spatialFactor x := by
  rw [spatialFactor, spatialFactor, spatialPairing_vadd, mul_add, Complex.exp_add]

/-- The spatial pairing of phase-attenuation data separates into real phase and attenuation
pairings. -/
lemma spatialPairing_ofPhaseAttenuation (q a : WaveVector d) (x : Space d) :
    spatialPairing (ofPhaseAttenuation q a) x =
      (⟪q, Space.basis.repr x⟫_ℝ : ℂ) -
        Complex.I * (⟪a, Space.basis.repr x⟫_ℝ : ℂ) := by
  exact bilinearDot_ofPhaseAttenuation_ofReal q a (Space.basis.repr x)

/-- The spatial factor of `q - I * a` is a real decay envelope times a unit-modulus phase. -/
lemma spatialFactor_ofPhaseAttenuation (q a : WaveVector d) (x : Space d) :
    spatialFactor (ofPhaseAttenuation q a) x =
      (Real.exp (-⟪a, Space.basis.repr x⟫_ℝ) : ℂ) *
        Complex.exp (-Complex.I * (⟪q, Space.basis.repr x⟫_ℝ : ℂ)) := by
  rw [spatialFactor, spatialPairing_ofPhaseAttenuation]
  calc
    Complex.exp (-Complex.I *
        ((⟪q, Space.basis.repr x⟫_ℝ : ℂ) -
          Complex.I * (⟪a, Space.basis.repr x⟫_ℝ : ℂ))) =
      Complex.exp (((-⟪a, Space.basis.repr x⟫_ℝ : ℝ) : ℂ) +
        -Complex.I * (⟪q, Space.basis.repr x⟫_ℝ : ℂ)) := by
      congr 1
      apply Complex.ext <;> simp
    _ = Complex.exp (((-⟪a, Space.basis.repr x⟫_ℝ : ℝ) : ℂ)) *
        Complex.exp (-Complex.I * (⟪q, Space.basis.repr x⟫_ℝ : ℂ)) := by
      rw [Complex.exp_add]
    _ = (Real.exp (-⟪a, Space.basis.repr x⟫_ℝ) : ℂ) *
        Complex.exp (-Complex.I * (⟪q, Space.basis.repr x⟫_ℝ : ℂ)) := by
      rw [Complex.ofReal_exp]

/-- The norm of a phase-attenuation spatial factor is exactly its real decay envelope. -/
lemma norm_spatialFactor_ofPhaseAttenuation (q a : WaveVector d) (x : Space d) :
    ‖spatialFactor (ofPhaseAttenuation q a) x‖ =
      Real.exp (-⟪a, Space.basis.repr x⟫_ℝ) := by
  rw [spatialFactor_ofPhaseAttenuation, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le]
  have hphase :
      -Complex.I * (⟪q, Space.basis.repr x⟫_ℝ : ℂ) =
        ((-⟪q, Space.basis.repr x⟫_ℝ : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hphase, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- A spatial plane-wave factor never vanishes. -/
lemma spatialFactor_ne_zero (k : ComplexWaveVector d) (x : Space d) :
    k.spatialFactor x ≠ 0 := by
  exact Complex.exp_ne_zero _

/-!

## E. Positive-normal decay data

-/

/-- Data for a complex wave vector with positive exponential decay along a selected direction.

The real phase vector is transverse to `normal`, and the attenuation vector is the positive scalar
`decayRate` times that direction. This is local decay geometry, not an interface-side or outgoing-
power convention. -/
structure PositiveNormalDecayWaveVector (normal : Direction d) where
  /-- The real wave-vector component transverse to the decay direction. -/
  tangentialWaveVector : WaveVector d
  /-- The phase vector is transverse to the selected normal direction. -/
  tangential :
    ⟪Space.basis.repr normal.unit, tangentialWaveVector⟫_ℝ = 0
  /-- The positive exponential decay rate. -/
  decayRate : ℝ
  /-- The decay rate is strictly positive. -/
  decayRate_pos : 0 < decayRate

namespace PositiveNormalDecayWaveVector

variable {normal : Direction d}

/-- The Euclidean coordinate vector of the selected unit decay direction. -/
def normalVector (_data : PositiveNormalDecayWaveVector normal) : WaveVector d :=
  Space.basis.repr normal.unit

/-- The complex wave vector `q - I * alpha * n` selected by positive-normal decay data. -/
def waveVector (data : PositiveNormalDecayWaveVector normal) : ComplexWaveVector d :=
  ofPhaseAttenuation data.tangentialWaveVector (data.decayRate • data.normalVector)

/-- Positive-normal decay data has the supplied tangential vector as its phase vector. -/
@[simp]
lemma phaseVector_waveVector (data : PositiveNormalDecayWaveVector normal) :
    data.waveVector.phaseVector = data.tangentialWaveVector := by
  simp [waveVector]

/-- Positive-normal decay data has attenuation `alpha * n`. -/
@[simp]
lemma attenuationVector_waveVector (data : PositiveNormalDecayWaveVector normal) :
    data.waveVector.attenuationVector = data.decayRate • data.normalVector := by
  simp [waveVector]

/-- The selected normal coordinate vector has unit norm. -/
lemma normalVector_norm (data : PositiveNormalDecayWaveVector normal) :
    ‖data.normalVector‖ = 1 := by
  simp [normalVector, normal.norm]

/-- Bilinear pairing with the selected unit normal is `-I * alpha`. -/
lemma bilinearDot_waveVector_normalVector (data : PositiveNormalDecayWaveVector normal) :
    bilinearDot data.waveVector (ofReal data.normalVector) =
      -Complex.I * (data.decayRate : ℂ) := by
  rw [waveVector, bilinearDot_ofPhaseAttenuation_ofReal]
  have htangent :
      ⟪data.tangentialWaveVector, data.normalVector⟫_ℝ = 0 := by
    rw [real_inner_comm]
    exact data.tangential
  have hnormal : ⟪data.normalVector, data.normalVector⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, data.normalVector_norm]
    norm_num
  rw [htangent, inner_smul_left, hnormal]
  simp

/-- The complex bilinear square is `|q|^2 - alpha^2`. -/
lemma bilinearDot_waveVector_self (data : PositiveNormalDecayWaveVector normal) :
    bilinearDot data.waveVector data.waveVector =
      ((‖data.tangentialWaveVector‖ ^ 2 - data.decayRate ^ 2 : ℝ) : ℂ) := by
  rw [waveVector, bilinearDot_ofPhaseAttenuation_self]
  have htangent :
      ⟪data.tangentialWaveVector, data.normalVector⟫_ℝ = 0 := by
    rw [real_inner_comm]
    exact data.tangential
  have hattenuation :
      ⟪data.decayRate • data.normalVector,
        data.decayRate • data.normalVector⟫_ℝ = data.decayRate ^ 2 := by
    rw [real_inner_self_eq_norm_sq, norm_smul, data.normalVector_norm, mul_one,
      Real.norm_eq_abs, abs_of_pos data.decayRate_pos]
  rw [hattenuation, inner_smul_right, htangent, real_inner_self_eq_norm_sq]
  push_cast
  ring

/-- Displacement by `u` along the selected normal multiplies the spatial factor by
`exp (-alpha * u)`. -/
lemma spatialFactor_vadd (data : PositiveNormalDecayWaveVector normal)
    (u : ℝ) (x : Space d) :
    data.waveVector.spatialFactor (u • data.normalVector +ᵥ x) =
      (Real.exp (-data.decayRate * u) : ℂ) * data.waveVector.spatialFactor x := by
  rw [ComplexWaveVector.spatialFactor_vadd, ofReal_smul,
    bilinearDot_smul_right, data.bilinearDot_waveVector_normalVector]
  have hexponent :
      -Complex.I * ((u : ℂ) * (-Complex.I * (data.decayRate : ℂ))) =
        ((-data.decayRate * u : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [mul_comm]
  rw [hexponent, ← Complex.ofReal_exp]

/-- The spatial-factor norm decays by `exp (-alpha * u)` after positive-normal displacement. -/
lemma norm_spatialFactor_vadd (data : PositiveNormalDecayWaveVector normal)
    (u : ℝ) (x : Space d) :
    ‖data.waveVector.spatialFactor (u • data.normalVector +ᵥ x)‖ =
      Real.exp (-data.decayRate * u) * ‖data.waveVector.spatialFactor x‖ := by
  rw [data.spatialFactor_vadd, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le]

/-- Along increasing positive-normal depth, the spatial factor tends to zero. -/
lemma tendsto_spatialFactor_vadd_atTop (data : PositiveNormalDecayWaveVector normal)
    (x : Space d) :
    Filter.Tendsto
      (fun u : ℝ ↦ data.waveVector.spatialFactor (u • data.normalVector +ᵥ x))
      Filter.atTop (nhds 0) := by
  have hscale : Filter.Tendsto (fun u : ℝ ↦ data.decayRate * u)
      Filter.atTop Filter.atTop :=
    (Filter.tendsto_const_mul_atTop_of_pos data.decayRate_pos).2 Filter.tendsto_id
  have hdecayRaw := Real.tendsto_exp_neg_atTop_nhds_zero.comp hscale
  change Filter.Tendsto (fun u : ℝ ↦ Real.exp (-(data.decayRate * u)))
    Filter.atTop (nhds 0) at hdecayRaw
  have hdecay : Filter.Tendsto (fun u : ℝ ↦ Real.exp (-data.decayRate * u))
      Filter.atTop (nhds 0) := by
    simpa only [neg_mul] using hdecayRaw
  have hcomplex := hdecay.ofReal.mul_const (data.waveVector.spatialFactor x)
  simpa only [Complex.ofReal_zero, zero_mul] using hcomplex.congr'
    (Filter.Eventually.of_forall fun u ↦ (data.spatialFactor_vadd u x).symm)

end PositiveNormalDecayWaveVector

end ComplexWaveVector

end

end ClassicalMechanics
