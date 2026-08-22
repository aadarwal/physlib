/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Components.Polarizer.Malus
public import Physlib.Optics.Polarization.LinearStokes
public import Physlib.Optics.Polarization.Mueller.Trace

/-!
# Mueller representation of an ideal linear polarizer

## i. Overview

This file proves the coherently Jones-induced Mueller representation of an ideal linear polarizer.
Its raw Mueller matrix is one half of the outer product of the transmitted axis's unit Stokes
vector. Consequently, arbitrary raw Stokes input leaves along that axis with scalar

`q = (S₀ + ⟨nθ, p⟩) / 2`,

where `nθ = (cos (2 • θ), sin (2 • θ), 0)` and `p` is the input polarization vector.
The result is derived from the shared Jones-induced Mueller construction and its Pauli trace
formula, not installed as an independent component law.

An arbitrary raw `MuellerMatrix` is not thereby Jones-induced or physically admissible. The
results here also do not identify raw Stokes intensity with electromagnetic irradiance or modal
power.

## ii. Key results

- `StokesVector.linearPolarizerOutputIntensity`: the transmitted raw Stokes scalar `q`.
- `JonesMatrix.linearPolarizer_mueller_entries`: the rank-one Stokes outer-product matrix.
- `JonesMatrix.linearPolarizer_mueller_act`: the arbitrary raw-Stokes action.
- `JonesMatrix.linearPolarizer_mueller_scaled_linearPolarization`: the Jones/Mueller commuting
  formula for a scaled linear input.

## iii. Table of contents

- A. Transmitted Stokes scalar
- B. Induced Mueller matrix and arbitrary action
- C. Connected representation checks

## iv. References

The matrix is derived from the imported Physlib Pauli trace formula for deterministic
Jones-induced Mueller transformations.
-/

@[expose] public section

namespace Optics

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace StokesVector

/-!

## A. Transmitted Stokes scalar
-/

/-- The raw output-intensity coordinate selected by a linear polarizer at angle `θ`.

It is one half of the input intensity plus the Euclidean projection of the input polarization
coordinates onto the polarizer's equatorial Stokes direction. -/
def linearPolarizerOutputIntensity (S : StokesVector) (θ : Real.Angle) : ℝ :=
  (S.intensity + inner ℝ (linearPolarizationDirection θ) S.polarization) / 2

/-- The transmitted Stokes scalar written in the three declared polarization coordinates. -/
lemma linearPolarizerOutputIntensity_eq (S : StokesVector) (θ : Real.Angle) :
    S.linearPolarizerOutputIntensity θ =
      (S.intensity + Real.Angle.cos (2 • θ) * S.polarization 0 +
        Real.Angle.sin (2 • θ) * S.polarization 1) / 2 := by
  simp [linearPolarizerOutputIntensity, linearPolarizationDirection,
    PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply]
  ring

/-- A zero-polarization Stokes input leaves half its raw intensity coordinate after an ideal
linear polarizer. -/
@[simp]
lemma linearPolarizerOutputIntensity_ofIntensityPolarization_zero
    (s₀ : ℝ) (θ : Real.Angle) :
    (ofIntensityPolarization s₀ 0).linearPolarizerOutputIntensity θ = s₀ / 2 := by
  simp [linearPolarizerOutputIntensity]

/-- The transmitted Stokes scalar is one half of the Euclidean dot product between the transmitted
unit Stokes state and the input. -/
lemma half_linearPolarization_stokes_dot_eq_outputIntensity
    (S : StokesVector) (θ : Real.Angle) :
    (1 / 2 : ℝ) * ((JonesVector.linearPolarization θ).stokes ⬝ᵥ S) =
      S.linearPolarizerOutputIntensity θ := by
  rw [JonesVector.stokes_linearPolarization]
  simp only [dotProduct, Fintype.sum_sum_type, Finset.univ_unique,
    Fin.default_eq_zero, Finset.sum_singleton, Fin.sum_univ_three]
  simp [linearPolarizerOutputIntensity, linearPolarizationDirection,
    PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply,
    ofIntensityPolarization, intensity, polarization]
  ring

end StokesVector

namespace JonesMatrix

/-!

## B. Induced Mueller matrix and arbitrary action
-/

/-- The induced Mueller matrix of an ideal linear polarizer is one half of the outer product of
its transmitted unit Stokes state. -/
lemma linearPolarizer_mueller_entries (θ : Real.Angle) :
    (linearPolarizer θ).mueller.entries =
      (1 / 2 : ℝ) • Matrix.vecMulVec
        (JonesVector.linearPolarization θ).stokes
        (JonesVector.linearPolarization θ).stokes := by
  ext i j
  apply Complex.ofReal_injective
  rw [mueller_trace_formula]
  rcases i with i | i <;> rcases j with j | j
  all_goals fin_cases i <;> fin_cases j
  all_goals
    simp [linearPolarizer, JonesVector.linearPolarization,
      JonesVector.ofComponents_zero, JonesVector.ofComponents_one,
      PauliMatrix.pauliMatrix, stokesPauliIndexEquiv, Matrix.mul_apply,
      Matrix.trace, Matrix.vecMulVec, Matrix.vecMul, Matrix.vecHead,
      Matrix.vecTail, Matrix.conjTranspose_apply, Fin.sum_univ_two,
      Pi.star_apply, RCLike.star_def, Complex.conj_ofReal]
    ring_nf

/-- An induced ideal-polarizer Mueller entry is one half of the product of the corresponding
transmitted-axis Stokes coordinates. -/
lemma linearPolarizer_mueller_apply (θ : Real.Angle) (i j : StokesIndex) :
    (linearPolarizer θ).mueller.entries i j =
      (1 / 2 : ℝ) * (JonesVector.linearPolarization θ).stokes i *
        (JonesVector.linearPolarization θ).stokes j := by
  rw [linearPolarizer_mueller_entries]
  simp only [one_div, Matrix.vecMulVec, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  ring

/-- An ideal-polarizer Mueller action is a rank-one projection onto the transmitted unit Stokes
state. -/
lemma linearPolarizer_mueller_act_outerProduct (θ : Real.Angle) (S : StokesVector) :
    (linearPolarizer θ).mueller.act S =
      ((1 / 2 : ℝ) * ((JonesVector.linearPolarization θ).stokes ⬝ᵥ S)) •
        (JonesVector.linearPolarization θ).stokes := by
  rw [MuellerMatrix.act, linearPolarizer_mueller_entries]
  change WithLp.toLp 2
      (((1 / 2 : ℝ) • Matrix.vecMulVec
        (JonesVector.linearPolarization θ).stokes
        (JonesVector.linearPolarization θ).stokes) *ᵥ S) = _
  rw [Matrix.smul_mulVec, Matrix.vecMulVec_mulVec]
  ext i
  simp only [one_div, op_smul_eq_smul, Pi.smul_apply, smul_eq_mul, PiLp.smul_apply]
  ring

/-- An ideal linear polarizer sends arbitrary raw Stokes data to the transmitted equatorial
direction, scaled by the selected output-intensity coordinate. -/
lemma linearPolarizer_mueller_act (θ : Real.Angle) (S : StokesVector) :
    (linearPolarizer θ).mueller.act S =
      StokesVector.ofIntensityPolarization
        (S.linearPolarizerOutputIntensity θ)
        (S.linearPolarizerOutputIntensity θ •
          StokesVector.linearPolarizationDirection θ) := by
  rw [linearPolarizer_mueller_act_outerProduct,
    StokesVector.half_linearPolarization_stokes_dot_eq_outputIntensity,
    JonesVector.smul_stokes_linearPolarization]

/-!

## C. Connected representation checks
-/

/-- A zero-polarization Stokes input emerges with half its raw intensity and polarization along
the transmitted Stokes direction. -/
lemma linearPolarizer_mueller_act_zeroPolarization (θ : Real.Angle) (s₀ : ℝ) :
    (linearPolarizer θ).mueller.act
        (StokesVector.ofIntensityPolarization s₀ 0) =
      StokesVector.ofIntensityPolarization (s₀ / 2)
        ((s₀ / 2) • StokesVector.linearPolarizationDirection θ) := by
  rw [linearPolarizer_mueller_act,
    StokesVector.linearPolarizerOutputIntensity_ofIntensityPolarization_zero]

/-- The induced Mueller action on a scaled linear Jones input agrees with the exact coherent
Malus output through the common Jones-to-Stokes bridge. -/
lemma linearPolarizer_mueller_scaled_linearPolarization (z : ℂ)
    (analyzer input : Real.Angle) :
    (linearPolarizer analyzer).mueller.act
        (JonesVector.scale z (JonesVector.linearPolarization input)).stokes =
      (JonesVector.scale
        (z * (Real.Angle.cos (input - analyzer) : ℂ))
        (JonesVector.linearPolarization analyzer)).stokes := by
  rw [mueller_jones, linearPolarizer_act_scaled_linearPolarization]

/-- The Stokes-intensity coordinate of a scaled linear input obeys Malus' squared-cosine law under
the induced Mueller action. -/
lemma linearPolarizer_mueller_scaled_linearPolarization_intensity (z : ℂ)
    (analyzer input : Real.Angle) :
    ((linearPolarizer analyzer).mueller.act
        (JonesVector.scale z (JonesVector.linearPolarization input)).stokes).intensity =
      (JonesVector.scale z (JonesVector.linearPolarization input)).stokes.intensity *
        Real.Angle.cos (input - analyzer) ^ 2 := by
  rw [mueller_jones, JonesVector.stokes_intensity_eq_intensity,
    JonesVector.stokes_intensity_eq_intensity, linearPolarizer_malus]

end JonesMatrix

end

end Optics
