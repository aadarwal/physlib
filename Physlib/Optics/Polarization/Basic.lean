/-
Copyright (c) 2025 Zhi Kai Pong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhi Kai Pong, Aadarsh Agarwal
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Jones polarization foundations

## i. Overview

This file defines phasors and Jones data for coherent monochromatic polarization. A phasor `z` is
realized with the convention `Re (z * exp ((carrierPhase : ℂ) * I))`. A Jones vector contains the
two raw complex electric-field amplitudes in a fixed transverse basis, while a Jones matrix acts on
those amplitudes.

The Jones wrappers are deliberately distinct from the power-normalized finite-mode API. Their
underlying Euclidean vector and matrix are available only through explicit fields; there are no
coercions to `ModeAmplitude` or `ModeTransform`. The squared Jones intensity defined here is an
electric-amplitude-squared quantity, not electromagnetic irradiance or modal power. Those
interpretations require later impedance, field-profile, and Poynting-flux normalization theorems.

## ii. Main definitions

- `Phasor.realize`: the real signal associated with a phasor and carrier phase.
- `Phasor.ofAmplitudePhase`: a phasor constructed from a real amplitude and phase.
- `JonesVector`: two raw transverse electric-field phasors.
- `JonesVector.intensity`: the squared Euclidean norm of a Jones vector.
- `JonesMatrix`: a wrapped `2 x 2` complex matrix.
- `JonesMatrix.act`: the action of a Jones matrix on a Jones vector.

## iii. Scope

This file contains no electromagnetic field equations and makes no claim that a Jones vector alone
determines a propagation direction, medium, carrier frequency, or gauge potential. The bridge to
the existing real harmonic Maxwell solution belongs in a later Optics module importing both APIs.
-/

@[expose] public section

namespace Optics

noncomputable section

/-! ## A. Phasors and the realization convention -/

/-- A complex amplitude for a fixed-frequency harmonic quantity. -/
abbrev Phasor := ℂ

/-- The real value of a phasor at the given carrier phase.

The convention is `Re (z * exp ((carrierPhase : ℂ) * I))`. -/
def Phasor.realize (z : Phasor) (carrierPhase : ℝ) : ℝ :=
  (z * Complex.exp ((carrierPhase : ℂ) * Complex.I)).re

/-- The phasor with the given real amplitude and phase offset. The amplitude is allowed to be
signed, so this representation is not unique. -/
def Phasor.ofAmplitudePhase (amplitude phase : ℝ) : Phasor :=
  (amplitude : ℂ) * Complex.exp ((phase : ℂ) * Complex.I)

/-- Realizing an amplitude-phase phasor gives the corresponding shifted cosine. -/
lemma Phasor.realize_ofAmplitudePhase (amplitude phase carrierPhase : ℝ) :
    (Phasor.ofAmplitudePhase amplitude phase).realize carrierPhase =
      amplitude * Real.cos (carrierPhase + phase) := by
  rw [Phasor.realize, Phasor.ofAmplitudePhase, mul_assoc, ← Complex.exp_add]
  have hphase : (phase : ℂ) * Complex.I + (carrierPhase : ℂ) * Complex.I =
      ((carrierPhase + phase : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hphase, Complex.mul_re, Complex.exp_ofReal_mul_I_re]
  simp

/-! ## B. Jones vectors and squared intensity -/

/-- Two raw complex electric-field amplitudes in a fixed transverse polarization basis.

This wrapper intentionally has no coercion to `EuclideanSpace` or to a power-normalized optical
mode amplitude. -/
@[ext]
structure JonesVector where
  /-- The two raw transverse electric-field phasors. -/
  components : EuclideanSpace ℂ (Fin 2)

namespace JonesVector

/-- Construct a Jones vector from a real amplitude and phase for each transverse component. -/
def ofAmplitudePhase (amplitude phase : Fin 2 → ℝ) : JonesVector :=
  ⟨WithLp.toLp 2 fun i ↦ Phasor.ofAmplitudePhase (amplitude i) (phase i)⟩

/-- A component of `ofAmplitudePhase` is the corresponding scalar amplitude-phase phasor. -/
@[simp]
lemma ofAmplitudePhase_components (amplitude phase : Fin 2 → ℝ) (i : Fin 2) :
    (ofAmplitudePhase amplitude phase).components i =
      Phasor.ofAmplitudePhase (amplitude i) (phase i) := rfl

/-- Realize both components of a Jones vector at a common carrier phase. -/
def realize (J : JonesVector) (carrierPhase : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 fun i ↦ Phasor.realize (J.components i) carrierPhase

/-- Jones-vector realization is componentwise phasor realization. -/
@[simp]
lemma realize_apply (J : JonesVector) (carrierPhase : ℝ) (i : Fin 2) :
    J.realize carrierPhase i = Phasor.realize (J.components i) carrierPhase := rfl

/-- A Jones vector built from amplitudes and phases realizes componentwise as shifted cosines. -/
lemma realize_ofAmplitudePhase_apply (amplitude phase : Fin 2 → ℝ)
    (carrierPhase : ℝ) (i : Fin 2) :
    (ofAmplitudePhase amplitude phase).realize carrierPhase i =
      amplitude i * Real.cos (carrierPhase + phase i) := by
  simp [Phasor.realize_ofAmplitudePhase]

/-- The squared Jones intensity parameter.

This is the squared `L²` norm of the raw electric-field phasors. It is not, by itself,
electromagnetic irradiance or power. -/
def intensity (J : JonesVector) : ℝ :=
  ‖J.components‖ ^ 2

/-- Squared Jones intensity is the sum of the squared moduli of its two components. -/
lemma intensity_eq_sum_normSq (J : JonesVector) :
    J.intensity = ∑ i, Complex.normSq (J.components i) := by
  simp [intensity, EuclideanSpace.norm_sq_eq, Complex.normSq_eq_norm_sq]

/-- Squared Jones intensity is nonnegative. -/
lemma intensity_nonneg (J : JonesVector) : 0 ≤ J.intensity :=
  sq_nonneg ‖J.components‖

/-- Scale every component of a Jones vector by the same complex scalar. -/
def scale (z : ℂ) (J : JonesVector) : JonesVector :=
  ⟨z • J.components⟩

/-- Scaling a Jones vector scales its squared intensity by the scalar's squared modulus. -/
lemma intensity_scale (z : ℂ) (J : JonesVector) :
    (scale z J).intensity = Complex.normSq z * J.intensity := by
  rw [intensity, scale, norm_smul, mul_pow, Complex.sq_norm]
  rfl

/-- Scaling by a unit-modulus scalar leaves squared Jones intensity unchanged. -/
lemma intensity_scale_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) (J : JonesVector) :
    (scale z J).intensity = J.intensity := by
  rw [intensity_scale, ← Complex.sq_norm, hz]
  simp

/-- Apply the same phase shift to both Jones components. -/
def phaseShift (phase : ℝ) (J : JonesVector) : JonesVector :=
  scale (Complex.exp ((phase : ℂ) * Complex.I)) J

/-- A global phase shift leaves squared Jones intensity unchanged. -/
@[simp]
lemma intensity_phaseShift (phase : ℝ) (J : JonesVector) :
    (phaseShift phase J).intensity = J.intensity := by
  apply intensity_scale_of_norm_eq_one
  exact Complex.norm_exp_ofReal_mul_I phase

/-- The squared Jones intensity of amplitude-phase data is the sum of the squared real
amplitudes. -/
lemma intensity_ofAmplitudePhase (amplitude phase : Fin 2 → ℝ) :
    (ofAmplitudePhase amplitude phase).intensity = ∑ i, amplitude i ^ 2 := by
  rw [intensity_eq_sum_normSq]
  apply Finset.sum_congr rfl
  intro i _
  rw [ofAmplitudePhase_components, Phasor.ofAmplitudePhase, Complex.normSq_mul,
    Complex.normSq_ofReal, ← Complex.sq_norm, Complex.norm_exp_ofReal_mul_I]
  ring

end JonesVector

/-! ## C. Jones matrices -/

/-- A wrapped `2 x 2` complex matrix acting on raw Jones electric-field amplitudes.

Rows index output polarization components and columns index input polarization components. This
wrapper intentionally has no coercion to `Matrix` or to a power-normalized mode transform. -/
@[ext]
structure JonesMatrix where
  /-- The entries of the Jones matrix, with output rows and input columns. -/
  entries : Matrix (Fin 2) (Fin 2) ℂ

namespace JonesMatrix

/-- Apply a Jones matrix to a Jones vector. -/
def act (M : JonesMatrix) (J : JonesVector) : JonesVector :=
  ⟨Matrix.toEuclideanLin M.entries J.components⟩

/-- The Jones-matrix action is ordinary matrix-vector multiplication componentwise. -/
lemma act_components (M : JonesMatrix) (J : JonesVector) (i : Fin 2) :
    (M.act J).components i = ∑ j, M.entries i j * J.components j := by
  rfl

/-- The identity Jones matrix. -/
def identity : JonesMatrix :=
  ⟨1⟩

/-- Compose two Jones matrices, with `M.comp N` acting first by `N` and then by `M`. -/
def comp (M N : JonesMatrix) : JonesMatrix :=
  ⟨M.entries * N.entries⟩

/-- The identity Jones matrix acts as the identity on Jones vectors. -/
@[simp]
lemma identity_act (J : JonesVector) : identity.act J = J := by
  ext
  simp [identity, act]

/-- Jones-matrix composition agrees with sequential action on Jones vectors. -/
lemma comp_act (M N : JonesMatrix) (J : JonesVector) :
    (M.comp N).act J = M.act (N.act J) := by
  ext
  simp [comp, act, Matrix.mulVec_mulVec]

end JonesMatrix

end

end Optics
