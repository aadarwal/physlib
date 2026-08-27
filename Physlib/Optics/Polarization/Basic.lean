/-
Copyright (c) 2025 Zhi Kai Pong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhi Kai Pong, Aadarsh Agarwal
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint

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
- `Phasor.realizeEuclidean`: componentwise realization of a complex Euclidean phasor array.
- `Phasor.conjugateEuclidean`: componentwise conjugation of a complex Euclidean phasor array.
- `Phasor.conjugateEuclidean_add`, `Phasor.conjugateEuclidean_smul`, and
  `Phasor.conjugateEuclidean_conjugateEuclidean`: its additive, conjugate-scalar, and involution
  laws.
- `Phasor.ofAmplitudePhase`: a phasor constructed from a real amplitude and phase.
- `JonesVector`: two raw transverse electric-field phasors.
- `JonesVector.ofComponents`: a Jones vector constructed from two complex components.
- `JonesVector.intensity`: the squared Euclidean norm of a Jones vector.
- `JonesVector.horizontal`, `vertical`, `diagonal`, `antidiagonal`, `plusIQuadrature`, and
  `minusIQuadrature`: normalized canonical coordinate states. Unguarded convention statement
  (review only): these states have no circular-handedness names in this API.
- `JonesMatrix`: a wrapped `2 x 2` complex matrix.
- `JonesMatrix.act`: the action of a Jones matrix on a Jones vector.
- `JonesMatrix.scale`: common complex scaling of every Jones-matrix entry.
- `JonesMatrix.IsUnitary`: algebraic unitarity in the selected Jones coordinate basis.

## iii. Scope

This file contains no electromagnetic field equations and makes no claim that a Jones vector alone
determines a propagation direction, medium, carrier frequency, or gauge potential. The bridge to
the existing real harmonic Maxwell solution belongs in a later Optics module importing both APIs.
-/

@[expose] public section

namespace Optics

noncomputable section

open Matrix
open scoped ComplexConjugate

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

/-- Phasor realization is the cosine-weighted real part minus the sine-weighted imaginary part. -/
lemma Phasor.realize_eq_re_cos_sub_im_sin (z : Phasor) (carrierPhase : ℝ) :
    z.realize carrierPhase =
      z.re * Real.cos carrierPhase - z.im * Real.sin carrierPhase := by
  rw [Phasor.realize, Complex.mul_re, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im]

/-- Multiplying a phasor by a positive-exponential phase advances its realized carrier phase. -/
lemma Phasor.realize_exp_mul (z : Phasor) (phase carrierPhase : ℝ) :
    Phasor.realize (Complex.exp ((phase : ℂ) * Complex.I) * z) carrierPhase =
      Phasor.realize z (carrierPhase + phase) := by
  rw [Phasor.realize, Phasor.realize]
  have hphase : (phase : ℂ) * Complex.I + (carrierPhase : ℂ) * Complex.I =
      ((carrierPhase + phase : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  apply congrArg Complex.re
  calc
    Complex.exp ((phase : ℂ) * Complex.I) * z *
        Complex.exp ((carrierPhase : ℂ) * Complex.I) =
      z * (Complex.exp ((phase : ℂ) * Complex.I) *
        Complex.exp ((carrierPhase : ℂ) * Complex.I)) := by ring
    _ = z * Complex.exp
        ((phase : ℂ) * Complex.I + (carrierPhase : ℂ) * Complex.I) := by
      rw [Complex.exp_add]
    _ = z * Complex.exp (((carrierPhase + phase : ℝ) : ℂ) * Complex.I) := by
      rw [hphase]

/-! ### A.1. Euclidean phasor arrays -/

/-- Realize a complex Euclidean phasor array componentwise at one common carrier phase. -/
def Phasor.realizeEuclidean {d : ℕ} (amplitude : EuclideanSpace ℂ (Fin d))
    (carrierPhase : ℝ) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 fun i ↦ Phasor.realize (amplitude i) carrierPhase

/-- Componentwise Euclidean realization agrees with scalar phasor realization. -/
@[simp]
lemma Phasor.realizeEuclidean_apply {d : ℕ} (amplitude : EuclideanSpace ℂ (Fin d))
    (carrierPhase : ℝ) (i : Fin d) :
    Phasor.realizeEuclidean amplitude carrierPhase i =
      Phasor.realize (amplitude i) carrierPhase := rfl

/-- Real scalar multiplication commutes with componentwise Euclidean phasor realization. -/
lemma Phasor.realizeEuclidean_ofReal_smul {d : ℕ} (r : ℝ)
    (amplitude : EuclideanSpace ℂ (Fin d)) (carrierPhase : ℝ) :
    Phasor.realizeEuclidean ((r : ℂ) • amplitude) carrierPhase =
      r • Phasor.realizeEuclidean amplitude carrierPhase := by
  ext i
  simp [Phasor.realize, Complex.mul_re]
  ring

/-- Componentwise Euclidean phasor realization preserves addition at one common carrier phase. -/
lemma Phasor.realizeEuclidean_add {d : ℕ}
    (first second : EuclideanSpace ℂ (Fin d)) (carrierPhase : ℝ) :
    Phasor.realizeEuclidean (first + second) carrierPhase =
      Phasor.realizeEuclidean first carrierPhase +
        Phasor.realizeEuclidean second carrierPhase := by
  ext i
  simp [Phasor.realize, add_mul]

/-- A componentwise Euclidean phasor realization repeats after one carrier cycle. -/
lemma Phasor.realizeEuclidean_add_two_pi {d : ℕ}
    (amplitude : EuclideanSpace ℂ (Fin d)) (carrierPhase : ℝ) :
    Phasor.realizeEuclidean amplitude (carrierPhase + 2 * Real.pi) =
      Phasor.realizeEuclidean amplitude carrierPhase := by
  ext i
  simp only [Phasor.realizeEuclidean_apply,
    Phasor.realize_eq_re_cos_sub_im_sin, Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- Componentwise Euclidean phasor realization depends continuously on the carrier phase. -/
lemma Phasor.continuous_realizeEuclidean {d : ℕ}
    (amplitude : EuclideanSpace ℂ (Fin d)) :
    Continuous (Phasor.realizeEuclidean amplitude) := by
  rw [continuous_iff_continuousAt]
  intro phase
  apply (PiLp.continuous_toLp 2 _).continuousAt.comp
  rw [continuousAt_pi]
  intro i
  simp only [Phasor.realize]
  fun_prop

/-- Conjugate every component of a complex Euclidean phasor array. -/
def Phasor.conjugateEuclidean {d : ℕ} (amplitude : EuclideanSpace ℂ (Fin d)) :
    EuclideanSpace ℂ (Fin d) :=
  WithLp.toLp 2 fun i ↦ star (amplitude i)

/-- Componentwise Euclidean conjugation agrees with scalar complex conjugation. -/
@[simp]
lemma Phasor.conjugateEuclidean_apply {d : ℕ}
    (amplitude : EuclideanSpace ℂ (Fin d)) (i : Fin d) :
    Phasor.conjugateEuclidean amplitude i = star (amplitude i) := rfl

/-- Componentwise Euclidean conjugation preserves zero. -/
@[simp]
lemma Phasor.conjugateEuclidean_zero {d : ℕ} :
    Phasor.conjugateEuclidean (0 : EuclideanSpace ℂ (Fin d)) = 0 := by
  ext i
  simp

/-- Componentwise Euclidean conjugation distributes over addition. -/
lemma Phasor.conjugateEuclidean_add {d : ℕ}
    (first second : EuclideanSpace ℂ (Fin d)) :
    Phasor.conjugateEuclidean (first + second) =
      Phasor.conjugateEuclidean first + Phasor.conjugateEuclidean second := by
  ext i
  simp

/-- Componentwise Euclidean conjugation turns complex scaling into conjugate scaling. -/
lemma Phasor.conjugateEuclidean_smul {d : ℕ} (z : ℂ)
    (amplitude : EuclideanSpace ℂ (Fin d)) :
    Phasor.conjugateEuclidean (z • amplitude) =
      star z • Phasor.conjugateEuclidean amplitude := by
  ext i
  simp

/-- Applying componentwise Euclidean conjugation twice returns the original phasor array. -/
@[simp]
lemma Phasor.conjugateEuclidean_conjugateEuclidean {d : ℕ}
    (amplitude : EuclideanSpace ℂ (Fin d)) :
    Phasor.conjugateEuclidean (Phasor.conjugateEuclidean amplitude) = amplitude := by
  ext i
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

/-- Construct a Jones vector from its first and second complex components. -/
def ofComponents (first second : ℂ) : JonesVector :=
  ⟨WithLp.toLp 2 ![first, second]⟩

/-- The first component of a Jones vector constructed from two complex amplitudes. -/
@[simp]
lemma ofComponents_zero (first second : ℂ) :
    (ofComponents first second).components 0 = first := rfl

/-- The second component of a Jones vector constructed from two complex amplitudes. -/
@[simp]
lemma ofComponents_one (first second : ℂ) :
    (ofComponents first second).components 1 = second := rfl

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

/-- A common Jones phase shift advances the realized carrier phase without discarding coherent
field information. -/
lemma realize_phaseShift (phase carrierPhase : ℝ) (J : JonesVector) :
    (phaseShift phase J).realize carrierPhase = J.realize (carrierPhase + phase) := by
  ext i
  rw [realize_apply, realize_apply]
  exact Phasor.realize_exp_mul (J.components i) phase carrierPhase

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

/-! ### B.1. Canonical normalized coordinate states -/

/-- The real amplitude for each component of a unit-intensity equal-amplitude Jones state. -/
noncomputable def unitEqualAmplitude : ℝ :=
  Real.sqrt 2 / 2

/-- The squared equal-component amplitude is one half. -/
lemma unitEqualAmplitude_sq : unitEqualAmplitude ^ 2 = 1 / 2 := by
  rw [unitEqualAmplitude, div_pow, Real.sq_sqrt (by norm_num)]
  norm_num

/-- Multiplying the equal-component amplitude by itself gives one half. -/
@[simp]
lemma unitEqualAmplitude_mul_self : unitEqualAmplitude * unitEqualAmplitude = 1 / 2 := by
  rw [← pow_two, unitEqualAmplitude_sq]

/-- The unit Jones state in the first declared transverse coordinate, called horizontal relative
to the chosen coordinate frame. -/
def horizontal : JonesVector :=
  ofComponents 1 0

/-- The unit Jones state in the second declared transverse coordinate, called vertical relative
to the chosen coordinate frame. -/
def vertical : JonesVector :=
  ofComponents 0 1

/-- The unit Jones state with equal positive real components, called diagonal relative to the
chosen coordinate frame. -/
noncomputable def diagonal : JonesVector :=
  ofComponents unitEqualAmplitude unitEqualAmplitude

/-- The unit Jones state with equal-magnitude opposite real components, called antidiagonal
relative to the chosen coordinate frame. -/
noncomputable def antidiagonal : JonesVector :=
  ofComponents unitEqualAmplitude (-unitEqualAmplitude)

/-- The unit quadrature Jones state whose second component is `I` times its first component.

Unguarded convention statement (review only): this algebraic definition assigns no
circular-polarization handedness name. -/
noncomputable def plusIQuadrature : JonesVector :=
  ofComponents unitEqualAmplitude (Complex.I * unitEqualAmplitude)

/-- The unit quadrature Jones state whose second component is `-I` times its first component.

Unguarded convention statement (review only): this algebraic definition assigns no
circular-polarization handedness name. -/
noncomputable def minusIQuadrature : JonesVector :=
  ofComponents unitEqualAmplitude (-Complex.I * unitEqualAmplitude)

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

/-- Multiply every Jones-matrix entry by a common complex scalar. -/
def scale (z : ℂ) (M : JonesMatrix) : JonesMatrix :=
  ⟨z • M.entries⟩

/-- The entries of a scaled Jones matrix are scaled entrywise. -/
@[simp]
lemma scale_entries (z : ℂ) (M : JonesMatrix) :
    (M.scale z).entries = z • M.entries := rfl

/-- Common scaling of a Jones matrix commutes with its action on Jones vectors. -/
lemma scale_act (z : ℂ) (M : JonesMatrix) (J : JonesVector) :
    (M.scale z).act J = JonesVector.scale z (M.act J) := by
  ext i
  simp [scale, act, JonesVector.scale, Matrix.mulVec]

/-- Jones-matrix action commutes with common scaling of the input Jones vector. -/
lemma act_scale (M : JonesMatrix) (z : ℂ) (J : JonesVector) :
    M.act (JonesVector.scale z J) = JonesVector.scale z (M.act J) := by
  ext i
  simp [act, JonesVector.scale, Matrix.mulVec]

/-- The identity Jones matrix. -/
def identity : JonesMatrix :=
  ⟨1⟩

/-- Compose two Jones matrices, with `M.comp N` acting first by `N` and then by `M`. -/
def comp (M N : JonesMatrix) : JonesMatrix :=
  ⟨M.entries * N.entries⟩

/-- Algebraic unitarity of a Jones matrix in the selected orthonormal coordinate basis.

This predicate concerns the squared norm of the raw Jones amplitudes. On its own it makes no
claim about electromagnetic irradiance, Poynting flux, or normalized modal power. -/
def IsUnitary (M : JonesMatrix) : Prop :=
  M.entries ∈ Matrix.unitaryGroup (Fin 2) ℂ

/-- The identity Jones matrix is unitary. -/
@[simp]
lemma isUnitary_identity : identity.IsUnitary := by
  simp [IsUnitary, identity]

/-- A cascade of unitary Jones matrices is unitary. -/
lemma IsUnitary.comp {M N : JonesMatrix} (hM : M.IsUnitary) (hN : N.IsUnitary) :
    (M.comp N).IsUnitary :=
  mul_mem hM hN

/-- A unitary Jones matrix preserves squared raw Jones amplitude. -/
lemma IsUnitary.act_intensity {M : JonesMatrix} (hM : M.IsUnitary) (J : JonesVector) :
    (M.act J).intensity = J.intensity := by
  have hunit : M.entriesᴴ * M.entries = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp hM
  have hcomp : (Matrix.toLpLin 2 2 M.entries).adjoint.comp
      (Matrix.toLpLin 2 2 M.entries) = LinearMap.id := by
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
      ← Matrix.toLpLin_mul_same, hunit, Matrix.toLpLin_one]
  rw [JonesVector.intensity, JonesVector.intensity,
    norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ)]
  apply congrArg Complex.re
  calc
    inner ℂ ((Matrix.toLpLin 2 2 M.entries) J.components)
        ((Matrix.toLpLin 2 2 M.entries) J.components) =
        inner ℂ (((Matrix.toLpLin 2 2 M.entries).adjoint.comp
          (Matrix.toLpLin 2 2 M.entries)) J.components) J.components := by
      rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left]
    _ = inner ℂ J.components J.components := by rw [hcomp, LinearMap.id_apply]

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
