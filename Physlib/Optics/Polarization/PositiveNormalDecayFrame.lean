/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Electromagnetism.ThreeDimension.MonochromaticPlaneWave.ComplexBasic
public import Physlib.Optics.Polarization.PlanarFrame
public import Physlib.SpaceAndTime.Space.OrientedAffineHyperplaneCrossProduct

/-!
# Polarization frames for positive-normal-decay waves

## i. Overview

This file defines the complex-bilinear `s`/`p` polarization frame carried by a positive-normal-
decay wave vector

`K = q - I * alpha * n`

on a positive real bilinear shell `K dot K = beta^2`. Its convention is

```text
s = normalize (n cross q), p = (K cross s) / beta, Jones order = (s, p).
```

For Physlib's carrier `exp (I * omega * t - I * K dot x)`, the negative-imaginary normal part
of `K` produces decay under increasing positive-normal displacement.

The axes are orthonormal for the complex-bilinear pairing used by plane-wave transversality:
`s dot s = p dot p = 1` and `s dot p = 0`. They are not a Hermitian orthonormal frame. In
particular, the squared Hermitian norm of `p` is strictly greater than one whenever the decay rate
is positive. Consequently this type is deliberately distinct from `PolarizationFrame`, and its
Jones embedding has no intensity- or power-preservation claim.

The real `s` axis and the real in-plane `p` axis still form an ordinary `PolarizationFrame` about
the selected normal. This retained plane frame will support interface-tangential boundary
coordinates without misclassifying the full complex `p` vector as a real propagation frame.

## ii. Key results

- `PositiveNormalDecayPolarizationFrame.bilinearDot_axis`: bilinear orthonormality of the complex
  axes.
- `PositiveNormalDecayPolarizationFrame.bilinearDot_waveVector_axis`: both axes are transverse to
  the complex wave vector.
- `PositiveNormalDecayPolarizationFrame.complexCross_waveVector_sAxis` and
  `PositiveNormalDecayPolarizationFrame.complexCross_waveVector_pAxis`: the shell-wavenumber
  quarter-turn identities.
- `PositiveNormalDecayPolarizationFrame.bilinearDot_axis_embedJones`: recovery of the two raw
  `s`/`p` amplitudes.
- `PositiveNormalDecayPolarizationFrame.embedJones_jonesCoordinates_of_transverse`: every
  bilinearly transverse electric amplitude is reconstructed from its unique raw `s`/`p`
  coordinates.
- `PositiveNormalDecayPolarizationFrame.existsUnique_embedJones_iff_bilinearDot_waveVector_eq_zero`:
  the embedded Jones plane is exactly the bilinearly transverse plane.
- `PositiveNormalDecayPolarizationFrame.complexCross_waveVector_embedJones`: the connected Jones
  quarter-turn identity.
- `PositiveNormalDecayPolarizationFrame.norm_pAxis_sq_eq_one_add`: the explicit Hermitian norm
  excess that prevents reuse of an ordinary polarization-frame norm theorem.

## iii. Table of contents

- A. Positive-normal-decay polarization data
- B. Real plane axes
- C. Complex-bilinear axes
- D. Raw Jones embedding
- E. Hermitian norm diagnostic
- F. Interface-plane components

## iv. References

The construction combines Physlib's positive-normal-decay wave-vector, complex-bilinear cross-
product, and real polarization-frame APIs. No external formal-development source is copied or
translated here.
-/

@[expose] public section

namespace Optics

open ClassicalMechanics Electromagnetism Electromagnetism.ThreeDimension Space Matrix
  InnerProductSpace
open ClassicalMechanics.ComplexWaveVector
open Electromagnetism.ThreeDimension.ComplexMonochromaticPlaneWave

noncomputable section

/-!

## A. Positive-normal-decay polarization data

-/

/-- A complex-bilinear polarization frame for positive-normal-decay data on a positive real
shell-wavenumber square.

The stored `waveNumber` is the positive real value `beta` satisfying `K dot K = beta^2`. It is
not the Hermitian norm of `K`; a medium-specific connector may identify it with a material
wavenumber. -/
structure PositiveNormalDecayPolarizationFrame (normal : Space.Direction 3) where
  /-- The positive-normal-decay wave-vector data. -/
  data : PositiveNormalDecayWaveVector normal
  /-- The positive real shell wavenumber used to normalize the complex `p` axis. -/
  waveNumber : ℝ
  /-- The shell wavenumber is strictly positive. -/
  waveNumber_pos : 0 < waveNumber
  /-- The complex-bilinear wave-vector square equals the shell wavenumber squared. -/
  bilinearSquare :
    bilinearDot data.waveVector data.waveVector = (waveNumber : ℂ) ^ 2

namespace PositiveNormalDecayPolarizationFrame

variable {normal : Space.Direction 3}

/-- The shell wavenumber is nonzero. -/
lemma waveNumber_ne_zero (frame : PositiveNormalDecayPolarizationFrame normal) :
    frame.waveNumber ≠ 0 :=
  ne_of_gt frame.waveNumber_pos

/-- The tangential phase magnitude satisfies `|q|^2 = beta^2 + alpha^2`. -/
lemma tangentialWaveVector_norm_sq_eq
    (frame : PositiveNormalDecayPolarizationFrame normal) :
    ‖frame.data.tangentialWaveVector‖ ^ 2 =
      frame.waveNumber ^ 2 + frame.data.decayRate ^ 2 := by
  have hSquare := frame.bilinearSquare
  rw [frame.data.bilinearDot_waveVector_self] at hSquare
  norm_cast at hSquare
  nlinarith

/-- Positive decay on a positive bilinear shell forces a nonzero tangential phase vector. -/
lemma tangentialWaveVector_ne_zero
    (frame : PositiveNormalDecayPolarizationFrame normal) :
    frame.data.tangentialWaveVector ≠ 0 := by
  intro hZero
  have hNorm : ‖frame.data.tangentialWaveVector‖ = 0 := norm_eq_zero.mpr hZero
  have hWaveNumberSquare : 0 < frame.waveNumber ^ 2 := sq_pos_of_pos frame.waveNumber_pos
  have hMagnitude := frame.tangentialWaveVector_norm_sq_eq
  rw [hNorm, zero_pow (by norm_num)] at hMagnitude
  nlinarith

/-!

## B. Real plane axes

-/

/-- The real `s` axis `normalize (n cross q)` selected by the decay normal and tangential phase
vector. -/
noncomputable def realSAxis (frame : PositiveNormalDecayPolarizationFrame normal) :
    WaveVector 3 :=
  NormedSpace.normalize
    (frame.data.normalVector ⨯ₑ₃ frame.data.tangentialWaveVector)

private lemma normalVector_cross_tangentialWaveVector_ne_zero
    (frame : PositiveNormalDecayPolarizationFrame normal) :
    frame.data.normalVector ⨯ₑ₃ frame.data.tangentialWaveVector ≠ 0 := by
  intro hCross
  have hInner := Space.inner_cross_cross frame.data.normalVector
    frame.data.tangentialWaveVector frame.data.normalVector
      frame.data.tangentialWaveVector
  rw [hCross] at hInner
  simp only [inner_zero_left] at hInner
  have hNormal : inner ℝ frame.data.normalVector frame.data.normalVector = 1 := by
    rw [real_inner_self_eq_norm_sq, frame.data.normalVector_norm]
    norm_num
  have hTangent :
      inner ℝ frame.data.normalVector frame.data.tangentialWaveVector = 0 :=
    frame.data.tangential
  rw [hNormal, hTangent, one_mul, zero_mul, sub_zero,
    real_inner_self_eq_norm_sq] at hInner
  have hNorm : ‖frame.data.tangentialWaveVector‖ = 0 := by
    nlinarith [norm_nonneg frame.data.tangentialWaveVector]
  exact frame.tangentialWaveVector_ne_zero (norm_eq_zero.mp hNorm)

/-- The real `s` axis has unit norm. -/
lemma realSAxis_norm (frame : PositiveNormalDecayPolarizationFrame normal) :
    ‖frame.realSAxis‖ = 1 := by
  exact NormedSpace.norm_normalize frame.normalVector_cross_tangentialWaveVector_ne_zero

/-- The real `s` axis is transverse to the selected normal. -/
lemma inner_normalVector_realSAxis
    (frame : PositiveNormalDecayPolarizationFrame normal) :
    inner ℝ frame.data.normalVector frame.realSAxis = 0 := by
  rw [realSAxis, NormedSpace.normalize, real_inner_smul_right,
    Space.inner_self_cross, mul_zero]

/-- The real `s` axis is transverse to the tangential phase vector. -/
lemma inner_tangentialWaveVector_realSAxis
    (frame : PositiveNormalDecayPolarizationFrame normal) :
    inner ℝ frame.data.tangentialWaveVector frame.realSAxis = 0 := by
  rw [realSAxis, NormedSpace.normalize, real_inner_smul_right,
    Space.inner_cross_self, mul_zero]

/-- The ordinary real plane frame whose first axis is the decay-selected `s` axis and whose
second axis is `n cross s`.

This frame is about the normal direction, not about the complex wave vector. -/
noncomputable def planeFrame (frame : PositiveNormalDecayPolarizationFrame normal) :
    PolarizationFrame normal :=
  PolarizationFrame.ofAxisZero normal frame.realSAxis frame.realSAxis_norm
    frame.inner_normalVector_realSAxis

/-- The real in-plane `p` axis `n cross s`. -/
noncomputable def planePAxis (frame : PositiveNormalDecayPolarizationFrame normal) :
    WaveVector 3 :=
  frame.planeFrame.axis 1

@[simp]
lemma planeFrame_axis_zero (frame : PositiveNormalDecayPolarizationFrame normal) :
    frame.planeFrame.axis 0 = frame.realSAxis := rfl

@[simp]
lemma planeFrame_axis_one (frame : PositiveNormalDecayPolarizationFrame normal) :
    frame.planeFrame.axis 1 = frame.planePAxis := rfl

/-- The real in-plane `p` axis is the normal crossed with the real `s` axis. -/
lemma planePAxis_eq_normalVector_cross_realSAxis
    (frame : PositiveNormalDecayPolarizationFrame normal) :
    frame.planePAxis = frame.data.normalVector ⨯ₑ₃ frame.realSAxis := rfl

/-!

## C. Complex-bilinear axes

-/

/-- The real `s` axis regarded as a complex vector. -/
noncomputable def sAxis (frame : PositiveNormalDecayPolarizationFrame normal) :
    ComplexWaveVector 3 :=
  ofReal frame.realSAxis

/-- The complex `p` axis `(K cross s) / beta`, normalized for the bilinear shell. -/
noncomputable def pAxis (frame : PositiveNormalDecayPolarizationFrame normal) :
    ComplexWaveVector 3 :=
  (frame.waveNumber : ℂ)⁻¹ • complexCross frame.data.waveVector frame.sAxis

/-- The ordered complex polarization axes, with index zero equal to `s` and index one equal to
`p`. -/
noncomputable def axis (frame : PositiveNormalDecayPolarizationFrame normal)
    (i : Fin 2) : ComplexWaveVector 3 :=
  ![frame.sAxis, frame.pAxis] i

@[simp]
lemma axis_zero (frame : PositiveNormalDecayPolarizationFrame normal) :
    frame.axis 0 = frame.sAxis := rfl

@[simp]
lemma axis_one (frame : PositiveNormalDecayPolarizationFrame normal) :
    frame.axis 1 = frame.pAxis := rfl

/-- The complex `s` axis has bilinear square one. -/
lemma bilinearDot_sAxis_self (frame : PositiveNormalDecayPolarizationFrame normal) :
    bilinearDot frame.sAxis frame.sAxis = 1 := by
  rw [sAxis, bilinearDot_ofReal, real_inner_self_eq_norm_sq, frame.realSAxis_norm]
  norm_num

/-- The complex wave vector is bilinearly transverse to the `s` axis. -/
lemma bilinearDot_waveVector_sAxis
    (frame : PositiveNormalDecayPolarizationFrame normal) :
    bilinearDot frame.data.waveVector frame.sAxis = 0 := by
  rw [PositiveNormalDecayWaveVector.waveVector, sAxis,
    bilinearDot_ofPhaseAttenuation_ofReal,
    inner_smul_left, frame.inner_tangentialWaveVector_realSAxis,
    frame.inner_normalVector_realSAxis]
  simp

/-- The complex wave vector is bilinearly transverse to the `p` axis. -/
lemma bilinearDot_waveVector_pAxis
    (frame : PositiveNormalDecayPolarizationFrame normal) :
    bilinearDot frame.data.waveVector frame.pAxis = 0 := by
  rw [pAxis, bilinearDot_smul_right, bilinearDot_self_complexCross, mul_zero]

/-- The complex `s` and `p` axes are bilinearly orthogonal. -/
lemma bilinearDot_sAxis_pAxis
    (frame : PositiveNormalDecayPolarizationFrame normal) :
    bilinearDot frame.sAxis frame.pAxis = 0 := by
  rw [pAxis, bilinearDot_smul_right, bilinearDot_complexCross_self, mul_zero]

/-- The complex `p` axis has bilinear square one. -/
lemma bilinearDot_pAxis_self (frame : PositiveNormalDecayPolarizationFrame normal) :
    bilinearDot frame.pAxis frame.pAxis = 1 := by
  rw [pAxis, bilinearDot_smul_left, bilinearDot_smul_right,
    bilinearDot_complexCross_complexCross, frame.bilinearSquare,
    frame.bilinearDot_sAxis_self, frame.bilinearDot_waveVector_sAxis,
    bilinearDot_comm frame.sAxis frame.data.waveVector,
    frame.bilinearDot_waveVector_sAxis]
  field_simp [frame.waveNumber_ne_zero]
  ring

/-- The ordered complex axes are orthonormal for the complex-bilinear pairing. -/
lemma bilinearDot_axis (frame : PositiveNormalDecayPolarizationFrame normal) (i j : Fin 2) :
    bilinearDot (frame.axis i) (frame.axis j) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j
  · simpa using frame.bilinearDot_sAxis_self
  · simpa using frame.bilinearDot_sAxis_pAxis
  · rw [bilinearDot_comm]
    simpa using frame.bilinearDot_sAxis_pAxis
  · simpa using frame.bilinearDot_pAxis_self

/-- Both complex polarization axes are bilinearly transverse to the wave vector. -/
lemma bilinearDot_waveVector_axis
    (frame : PositiveNormalDecayPolarizationFrame normal) (i : Fin 2) :
    bilinearDot frame.data.waveVector (frame.axis i) = 0 := by
  fin_cases i
  · exact frame.bilinearDot_waveVector_sAxis
  · exact frame.bilinearDot_waveVector_pAxis

/-- Crossing the wave vector with `s` gives `beta p`. -/
lemma complexCross_waveVector_sAxis
    (frame : PositiveNormalDecayPolarizationFrame normal) :
    complexCross frame.data.waveVector frame.sAxis =
      (frame.waveNumber : ℂ) • frame.pAxis := by
  rw [pAxis, smul_smul]
  field_simp [frame.waveNumber_ne_zero]
  simp

/-- Crossing the wave vector with `p` gives `-beta s`. -/
lemma complexCross_waveVector_pAxis
    (frame : PositiveNormalDecayPolarizationFrame normal) :
    complexCross frame.data.waveVector frame.pAxis =
      -(frame.waveNumber : ℂ) • frame.sAxis := by
  rw [pAxis, complexCross_smul_right, complexCross_complexCross,
    frame.bilinearDot_waveVector_sAxis, frame.bilinearSquare]
  simp only [zero_smul, zero_sub, smul_neg, smul_smul]
  field_simp [frame.waveNumber_ne_zero]
  simp

/-- Crossing `s` with `p` recovers the wave vector divided by `beta`. -/
lemma complexCross_sAxis_pAxis
    (frame : PositiveNormalDecayPolarizationFrame normal) :
    complexCross frame.sAxis frame.pAxis =
      (frame.waveNumber : ℂ)⁻¹ • frame.data.waveVector := by
  rw [pAxis, complexCross_smul_right, complexCross_complexCross,
    frame.bilinearDot_sAxis_self,
    bilinearDot_comm frame.sAxis frame.data.waveVector,
    frame.bilinearDot_waveVector_sAxis]
  simp

/-- Crossing the wave vector with an arbitrary amplitude is determined by its bilinear `s` and
`p` coordinates. -/
lemma complexCross_waveVector_eq_axis_pairings
    (frame : PositiveNormalDecayPolarizationFrame normal)
    (electricAmplitude : ComplexWaveVector 3) :
    complexCross frame.data.waveVector electricAmplitude =
      (frame.waveNumber : ℂ) •
        (bilinearDot frame.sAxis electricAmplitude • frame.pAxis -
          bilinearDot frame.pAxis electricAmplitude • frame.sAxis) := by
  have hTriple := complexCross_complexCross_left frame.sAxis frame.pAxis electricAmplitude
  rw [frame.complexCross_sAxis_pAxis, complexCross_smul_left] at hTriple
  rw [← hTriple, smul_smul]
  field_simp [frame.waveNumber_ne_zero]
  simp

/-!

## D. Raw Jones embedding

-/

/-- Embed raw two-component `s`/`p` amplitudes in the complex-bilinear decay frame.

This map is an amplitude-coordinate embedding. It does not preserve the standard Jones intensity
as the Hermitian norm of the resulting three-vector. -/
noncomputable def embedJones (frame : PositiveNormalDecayPolarizationFrame normal)
    (J : JonesVector) : ComplexWaveVector 3 :=
  ∑ i : Fin 2, J.components i • frame.axis i

/-- Extract the raw `s`/`p` coordinates of a complex electric amplitude by bilinear pairing with
the two axes. -/
noncomputable def jonesCoordinates
    (frame : PositiveNormalDecayPolarizationFrame normal)
    (electricAmplitude : ComplexWaveVector 3) : JonesVector :=
  JonesVector.ofComponents (bilinearDot frame.sAxis electricAmplitude)
    (bilinearDot frame.pAxis electricAmplitude)

@[simp]
lemma jonesCoordinates_components_zero
    (frame : PositiveNormalDecayPolarizationFrame normal)
    (electricAmplitude : ComplexWaveVector 3) :
    (frame.jonesCoordinates electricAmplitude).components 0 =
      bilinearDot frame.sAxis electricAmplitude := rfl

@[simp]
lemma jonesCoordinates_components_one
    (frame : PositiveNormalDecayPolarizationFrame normal)
    (electricAmplitude : ComplexWaveVector 3) :
    (frame.jonesCoordinates electricAmplitude).components 1 =
      bilinearDot frame.pAxis electricAmplitude := rfl

/-- The raw Jones embedding is the explicit `s` plus `p` amplitude decomposition. -/
lemma embedJones_eq (frame : PositiveNormalDecayPolarizationFrame normal)
    (J : JonesVector) :
    frame.embedJones J =
      J.components 0 • frame.sAxis + J.components 1 • frame.pAxis := by
  rw [embedJones, Fin.sum_univ_two]
  rfl

/-- Zero raw `s` and `p` amplitudes embed as the zero electric amplitude. -/
@[simp]
lemma embedJones_ofComponents_zero_zero
    (frame : PositiveNormalDecayPolarizationFrame normal) :
    frame.embedJones (JonesVector.ofComponents 0 0) = 0 := by
  rw [frame.embedJones_eq]
  simp

/-- Bilinear pairing with an axis recovers the corresponding raw Jones amplitude. -/
lemma bilinearDot_axis_embedJones
    (frame : PositiveNormalDecayPolarizationFrame normal) (J : JonesVector) (i : Fin 2) :
    bilinearDot (frame.axis i) (frame.embedJones J) = J.components i := by
  rw [frame.embedJones_eq, bilinearDot_add_right, bilinearDot_smul_right,
    bilinearDot_smul_right]
  fin_cases i
  · simp [axis, frame.bilinearDot_sAxis_self, frame.bilinearDot_sAxis_pAxis]
  · simp [axis, bilinearDot_comm frame.pAxis frame.sAxis,
      frame.bilinearDot_sAxis_pAxis, frame.bilinearDot_pAxis_self]

/-- The raw Jones embedding is injective. -/
lemma embedJones_injective (frame : PositiveNormalDecayPolarizationFrame normal) :
    Function.Injective frame.embedJones := by
  intro first second hEqual
  ext i
  rw [← frame.bilinearDot_axis_embedJones first i,
    ← frame.bilinearDot_axis_embedJones second i, hEqual]

/-- Crossing by the non-null wave vector is injective on its bilinearly transverse plane. -/
lemma eq_of_bilinearDot_waveVector_eq_zero_of_complexCross_waveVector_eq
    (frame : PositiveNormalDecayPolarizationFrame normal)
    {first second : ComplexWaveVector 3}
    (hFirst : bilinearDot frame.data.waveVector first = 0)
    (hSecond : bilinearDot frame.data.waveVector second = 0)
    (hCross : complexCross frame.data.waveVector first =
      complexCross frame.data.waveVector second) :
    first = second := by
  have hDifferenceDot :
      bilinearDot frame.data.waveVector (first - second) = 0 := by
    rw [bilinearDot_sub_right, hFirst, hSecond, sub_zero]
  have hDifferenceCross :
      complexCross frame.data.waveVector (first - second) = 0 := by
    rw [complexCross_sub_right, hCross, sub_self]
  have hDoubleCross :=
    complexCross_complexCross frame.data.waveVector frame.data.waveVector (first - second)
  rw [hDifferenceCross, hDifferenceDot, frame.bilinearSquare] at hDoubleCross
  have hScaled : ((frame.waveNumber : ℂ) ^ 2) • (first - second) = 0 := by
    simpa [complexCross] using hDoubleCross
  have hWaveNumber : (frame.waveNumber : ℂ) ≠ 0 := by
    exact_mod_cast frame.waveNumber_ne_zero
  rcases smul_eq_zero.mp hScaled with hScale | hDifference
  · exact (pow_ne_zero 2 hWaveNumber hScale).elim
  · exact sub_eq_zero.mp hDifference

/-- Extracting coordinates after embedding recovers the original raw Jones vector. -/
@[simp]
lemma jonesCoordinates_embedJones
    (frame : PositiveNormalDecayPolarizationFrame normal) (J : JonesVector) :
    frame.jonesCoordinates (frame.embedJones J) = J := by
  ext i
  fin_cases i
  · exact frame.bilinearDot_axis_embedJones J 0
  · exact frame.bilinearDot_axis_embedJones J 1

/-- Every embedded raw Jones amplitude is bilinearly transverse to the complex wave vector. -/
lemma bilinearDot_waveVector_embedJones
    (frame : PositiveNormalDecayPolarizationFrame normal) (J : JonesVector) :
    bilinearDot frame.data.waveVector (frame.embedJones J) = 0 := by
  rw [frame.embedJones_eq, bilinearDot_add_right, bilinearDot_smul_right,
    bilinearDot_smul_right, frame.bilinearDot_waveVector_sAxis,
    frame.bilinearDot_waveVector_pAxis]
  simp

/-- Crossing the wave vector with an embedded Jones amplitude is the shell wavenumber times
the embedded coordinate quarter-turn. -/
lemma complexCross_waveVector_embedJones
    (frame : PositiveNormalDecayPolarizationFrame normal) (J : JonesVector) :
    complexCross frame.data.waveVector (frame.embedJones J) =
      (frame.waveNumber : ℂ) • frame.embedJones J.propagationCross := by
  rw [frame.embedJones_eq, complexCross_add_right, complexCross_smul_right,
    complexCross_smul_right, frame.complexCross_waveVector_sAxis,
    frame.complexCross_waveVector_pAxis, frame.embedJones_eq]
  simp only [JonesVector.propagationCross_components_zero,
    JonesVector.propagationCross_components_one]
  module

/-- Every bilinearly transverse electric amplitude is reconstructed from its raw `s`/`p`
coordinates. -/
lemma embedJones_jonesCoordinates_of_transverse
    (frame : PositiveNormalDecayPolarizationFrame normal)
    (electricAmplitude : ComplexWaveVector 3)
    (hTransverse : bilinearDot frame.data.waveVector electricAmplitude = 0) :
    frame.embedJones (frame.jonesCoordinates electricAmplitude) = electricAmplitude := by
  apply frame.eq_of_bilinearDot_waveVector_eq_zero_of_complexCross_waveVector_eq
  · exact frame.bilinearDot_waveVector_embedJones _
  · exact hTransverse
  rw [frame.complexCross_waveVector_embedJones,
    frame.complexCross_waveVector_eq_axis_pairings, frame.embedJones_eq]
  simp only [JonesVector.propagationCross_components_zero,
    JonesVector.propagationCross_components_one,
    frame.jonesCoordinates_components_zero, frame.jonesCoordinates_components_one]
  module

/-- Every bilinearly transverse electric amplitude has unique raw `s`/`p` coordinates. -/
lemma existsUnique_embedJones_of_bilinearDot_waveVector_eq_zero
    (frame : PositiveNormalDecayPolarizationFrame normal)
    (electricAmplitude : ComplexWaveVector 3)
    (hTransverse : bilinearDot frame.data.waveVector electricAmplitude = 0) :
    ∃! J : JonesVector, frame.embedJones J = electricAmplitude := by
  refine ⟨frame.jonesCoordinates electricAmplitude,
    frame.embedJones_jonesCoordinates_of_transverse electricAmplitude hTransverse, ?_⟩
  intro J hJ
  rw [← frame.jonesCoordinates_embedJones J, hJ]

/-- A complex electric amplitude has unique raw `s`/`p` coordinates exactly when it is
bilinearly transverse to the wave vector. -/
lemma existsUnique_embedJones_iff_bilinearDot_waveVector_eq_zero
    (frame : PositiveNormalDecayPolarizationFrame normal)
    (electricAmplitude : ComplexWaveVector 3) :
    (∃! J : JonesVector, frame.embedJones J = electricAmplitude) ↔
      bilinearDot frame.data.waveVector electricAmplitude = 0 := by
  constructor
  · rintro ⟨J, rfl, _⟩
    exact frame.bilinearDot_waveVector_embedJones J
  · exact frame.existsUnique_embedJones_of_bilinearDot_waveVector_eq_zero electricAmplitude

/-!

## E. Hermitian norm diagnostic

-/

private lemma inner_waveVector_sAxis
    (frame : PositiveNormalDecayPolarizationFrame normal) :
    inner ℂ frame.data.waveVector frame.sAxis = 0 := by
  have hTransverse := congrArg star frame.bilinearDot_waveVector_sAxis
  simpa [sAxis, bilinearDot, PiLp.inner_apply, RCLike.inner_apply, mul_comm] using
    hTransverse

/-- The complex cross `K cross s` has Hermitian squared norm equal to the Hermitian squared norm
of `K`. -/
lemma norm_complexCross_waveVector_sAxis_sq
    (frame : PositiveNormalDecayPolarizationFrame normal) :
    ‖complexCross frame.data.waveVector frame.sAxis‖ ^ 2 =
      ‖frame.data.waveVector‖ ^ 2 := by
  have hSAxis : inner ℂ frame.sAxis frame.sAxis = 1 := by
    change inner ℂ (frame.planeFrame.complexAxis 0)
      (frame.planeFrame.complexAxis 0) = 1
    rw [frame.planeFrame.inner_complexAxis, frame.planeFrame_axis_zero,
      real_inner_self_eq_norm_sq, frame.realSAxis_norm]
    norm_num
  calc
    ‖complexCross frame.data.waveVector frame.sAxis‖ ^ 2 =
        (inner ℂ (complexCross frame.data.waveVector frame.sAxis)
          (complexCross frame.data.waveVector frame.sAxis)).re :=
      InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) _
    _ = (inner ℂ frame.data.waveVector frame.data.waveVector).re := by
      rw [inner_complexCross_complexCross, hSAxis,
        frame.inner_waveVector_sAxis]
      simp
    _ = ‖frame.data.waveVector‖ ^ 2 :=
      (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) frame.data.waveVector).symm

/-- The Hermitian squared norm of the complex `p` axis is
`(|q|^2 + alpha^2) / beta^2`. -/
lemma norm_pAxis_sq (frame : PositiveNormalDecayPolarizationFrame normal) :
    ‖frame.pAxis‖ ^ 2 =
      (‖frame.data.tangentialWaveVector‖ ^ 2 + frame.data.decayRate ^ 2) /
        frame.waveNumber ^ 2 := by
  rw [pAxis, norm_smul, mul_pow, frame.norm_complexCross_waveVector_sAxis_sq,
    frame.data.norm_waveVector_sq]
  simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos frame.waveNumber_pos]
  field_simp [frame.waveNumber_ne_zero]

/-- The Hermitian squared norm of the complex `p` axis is
`1 + 2 (alpha / beta)^2`, rather than one. -/
lemma norm_pAxis_sq_eq_one_add (frame : PositiveNormalDecayPolarizationFrame normal) :
    ‖frame.pAxis‖ ^ 2 =
      1 + 2 * (frame.data.decayRate / frame.waveNumber) ^ 2 := by
  rw [frame.norm_pAxis_sq, frame.tangentialWaveVector_norm_sq_eq]
  field_simp [frame.waveNumber_ne_zero]
  ring

/-- Positive normal decay makes the complex `p` axis strictly longer than one in Hermitian
squared norm, despite its bilinear square being one. -/
lemma one_lt_norm_pAxis_sq (frame : PositiveNormalDecayPolarizationFrame normal) :
    1 < ‖frame.pAxis‖ ^ 2 := by
  rw [frame.norm_pAxis_sq_eq_one_add]
  have hRatio : 0 < frame.data.decayRate / frame.waveNumber :=
    div_pos frame.data.decayRate_pos frame.waveNumber_pos
  nlinarith [sq_pos_of_pos hRatio]

/-!

## F. Interface-plane components

-/

/-- The complex normal component of the normalized wave vector `K / beta` relative to a plane
whose stored normal is the decay direction. -/
noncomputable def normalizedWaveVectorNormalComponent
    (plane : OrientedAffineHyperplane 3)
    (frame : PositiveNormalDecayPolarizationFrame plane.normal) : ℂ :=
  (frame.waveNumber : ℂ)⁻¹ * hyperplaneNormalComponent plane frame.data.waveVector

/-- The normalized normal component is the negative-imaginary decay ratio
`-I * alpha / beta`. -/
lemma normalizedWaveVectorNormalComponent_eq_neg_I_mul
    (plane : OrientedAffineHyperplane 3)
    (frame : PositiveNormalDecayPolarizationFrame plane.normal) :
    frame.normalizedWaveVectorNormalComponent plane =
      -Complex.I * ((frame.data.decayRate / frame.waveNumber : ℝ) : ℂ) := by
  rw [normalizedWaveVectorNormalComponent, hyperplaneNormalComponent, bilinearDot_comm]
  change (frame.waveNumber : ℂ)⁻¹ *
      bilinearDot frame.data.waveVector (ofReal frame.data.normalVector) = _
  rw [frame.data.bilinearDot_waveVector_normalVector]
  push_cast
  field_simp [frame.waveNumber_ne_zero]

/-- The complex `p` axis splits into its negative-imaginary in-plane component and its positive
real normal component. -/
lemma pAxis_eq_tangential_add_normal
    (plane : OrientedAffineHyperplane 3)
    (frame : PositiveNormalDecayPolarizationFrame plane.normal) :
    frame.pAxis =
      ((frame.waveNumber : ℂ)⁻¹ *
          (-Complex.I * (frame.data.decayRate : ℂ))) • ofReal frame.planePAxis +
        ((frame.waveNumber : ℂ)⁻¹ *
          (‖frame.data.tangentialWaveVector‖ : ℂ)) •
            ofReal frame.data.normalVector := by
  have hTangent :
      plane.IsTangent frame.data.tangentialWaveVector :=
    frame.data.tangential
  have hNormalVector : frame.data.normalVector = plane.normalVector := rfl
  have hTangentialCross :
      frame.data.tangentialWaveVector ⨯ₑ₃ frame.realSAxis =
        ‖frame.data.tangentialWaveVector‖ • frame.data.normalVector := by
    simpa [realSAxis, hNormalVector] using
      plane.tangent_cross_normalize_normalVector_cross
        frame.data.tangentialWaveVector frame.tangentialWaveVector_ne_zero hTangent
  have hNormalCross :
      frame.data.normalVector ⨯ₑ₃ frame.realSAxis = frame.planePAxis :=
    frame.planePAxis_eq_normalVector_cross_realSAxis.symm
  rw [pAxis, PositiveNormalDecayWaveVector.waveVector, ofPhaseAttenuation, sAxis,
    complexCross_sub_left, complexCross_smul_left, complexCross_ofReal,
    complexCross_ofReal, hTangentialCross, Space.smul_cross, hNormalCross,
    ofReal_smul, ofReal_smul]
  module

/-- The real in-plane `p` axis has the sign `n cross s = -normalize q`. -/
lemma planePAxis_eq_neg_normalize_tangentialWaveVector
    (plane : OrientedAffineHyperplane 3)
    (frame : PositiveNormalDecayPolarizationFrame plane.normal) :
    frame.planePAxis = -NormedSpace.normalize frame.data.tangentialWaveVector := by
  have hTangent :
      plane.IsTangent frame.data.tangentialWaveVector :=
    frame.data.tangential
  have hNormalVector : frame.data.normalVector = plane.normalVector := rfl
  rw [frame.planePAxis_eq_normalVector_cross_realSAxis, realSAxis, hNormalVector]
  exact plane.normalVector_cross_normalize_normalVector_cross
    frame.data.tangentialWaveVector hTangent

/-- The complex `s` axis has zero normal component relative to the decay-normal plane. -/
@[simp]
lemma hyperplaneNormalComponent_sAxis
    (plane : OrientedAffineHyperplane 3)
    (frame : PositiveNormalDecayPolarizationFrame plane.normal) :
    hyperplaneNormalComponent plane frame.sAxis = 0 := by
  rw [hyperplaneNormalComponent, sAxis, bilinearDot_ofReal]
  exact_mod_cast frame.inner_normalVector_realSAxis

/-- Tangential projection fixes the complex `s` axis. -/
@[simp]
lemma hyperplaneTangentialProjection_sAxis
    (plane : OrientedAffineHyperplane 3)
    (frame : PositiveNormalDecayPolarizationFrame plane.normal) :
    hyperplaneTangentialProjection plane frame.sAxis = frame.sAxis := by
  simp [hyperplaneTangentialProjection]

/-- The complex `p` axis has normal component `|q| / beta`. -/
lemma hyperplaneNormalComponent_pAxis
    (plane : OrientedAffineHyperplane 3)
    (frame : PositiveNormalDecayPolarizationFrame plane.normal) :
    hyperplaneNormalComponent plane frame.pAxis =
      ((‖frame.data.tangentialWaveVector‖ / frame.waveNumber : ℝ) : ℂ) := by
  rw [frame.pAxis_eq_tangential_add_normal plane, hyperplaneNormalComponent,
    bilinearDot_add_right, bilinearDot_smul_right, bilinearDot_smul_right,
    bilinearDot_ofReal, bilinearDot_ofReal]
  have hPlanePAxis : inner ℝ plane.normalVector frame.planePAxis = 0 := by
    change inner ℝ frame.planeFrame.propagationVector (frame.planeFrame.axis 1) = 0
    exact frame.planeFrame.inner_propagationVector_axis 1
  have hNormal : inner ℝ plane.normalVector frame.data.normalVector = 1 := by
    change inner ℝ plane.normalVector plane.normalVector = 1
    exact plane.inner_normalVector_self
  rw [hPlanePAxis, hNormal]
  push_cast
  field_simp [frame.waveNumber_ne_zero]
  ring

/-- Tangential projection of the complex `p` axis is its normalized complex normal factor times
the real in-plane `p` axis. -/
lemma hyperplaneTangentialProjection_pAxis
    (plane : OrientedAffineHyperplane 3)
    (frame : PositiveNormalDecayPolarizationFrame plane.normal) :
    hyperplaneTangentialProjection plane frame.pAxis =
      frame.normalizedWaveVectorNormalComponent plane • ofReal frame.planePAxis := by
  have hPlanePAxis : plane.IsTangent frame.planePAxis := by
    change inner ℝ frame.planeFrame.propagationVector (frame.planeFrame.axis 1) = 0
    exact frame.planeFrame.inner_propagationVector_axis 1
  have hNormalProjection :
      plane.tangentialProjection frame.data.normalVector = 0 := by
    change plane.tangentialProjection plane.normalVector = 0
    exact plane.tangentialProjection_normalVector
  rw [frame.pAxis_eq_tangential_add_normal plane,
    hyperplaneTangentialProjection_add,
    hyperplaneTangentialProjection_smul, hyperplaneTangentialProjection_smul,
    hyperplaneTangentialProjection_ofReal, hyperplaneTangentialProjection_ofReal,
    plane.tangentialProjection_eq_self_of_isTangent frame.planePAxis hPlanePAxis,
    hNormalProjection, ofReal_zero, smul_zero, add_zero,
    frame.normalizedWaveVectorNormalComponent_eq_neg_I_mul plane]
  push_cast
  field_simp [frame.waveNumber_ne_zero]

/-- Convert full-vector `s`/`p` amplitudes to the fixed-plane tangential coordinates. -/
noncomputable def tangentialJones
    (plane : OrientedAffineHyperplane 3)
    (frame : PositiveNormalDecayPolarizationFrame plane.normal)
    (J : JonesVector) : JonesVector :=
  JonesVector.ofComponents (J.components 0)
    (frame.normalizedWaveVectorNormalComponent plane * J.components 1)

/-- Tangential projection of an embedded Jones amplitude is its fixed-plane Jones embedding with
the complex normal factor applied to the `p` coordinate. -/
lemma hyperplaneTangentialProjection_embedJones
    (plane : OrientedAffineHyperplane 3)
    (frame : PositiveNormalDecayPolarizationFrame plane.normal) (J : JonesVector) :
    hyperplaneTangentialProjection plane (frame.embedJones J) =
      frame.planeFrame.embedJones (frame.tangentialJones plane J) := by
  rw [frame.embedJones_eq, hyperplaneTangentialProjection_add,
    hyperplaneTangentialProjection_smul, hyperplaneTangentialProjection_smul,
    frame.hyperplaneTangentialProjection_sAxis plane,
    frame.hyperplaneTangentialProjection_pAxis plane,
    PolarizationFrame.embedJones, Fin.sum_univ_two, sAxis]
  change _ = J.components 0 • ofReal frame.realSAxis +
    (frame.normalizedWaveVectorNormalComponent plane * J.components 1) •
      ofReal frame.planePAxis
  module

/-- Tangential projection of the embedded coordinate quarter-turn has fixed-plane coordinates
`(-J_p, zeta J_s)`, where `zeta` is the normalized complex normal component. -/
lemma hyperplaneTangentialProjection_embedJones_propagationCross
    (plane : OrientedAffineHyperplane 3)
    (frame : PositiveNormalDecayPolarizationFrame plane.normal) (J : JonesVector) :
    hyperplaneTangentialProjection plane (frame.embedJones J.propagationCross) =
      frame.planeFrame.embedJones
        (JonesVector.ofComponents (-J.components 1)
          (frame.normalizedWaveVectorNormalComponent plane * J.components 0)) := by
  rw [frame.hyperplaneTangentialProjection_embedJones]
  congr 1

end PositiveNormalDecayPolarizationFrame

end

end Optics
