/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Power-normalized optical modes

## i. Overview

This file defines families of complex optical mode amplitudes and the matrices that
act on them at a fixed frequency. The amplitudes use the power-normalized convention: the squared
modulus of a component is its contribution to the total modal power. Consequently, a matrix is
called power-preserving when it preserves the sum of these squared moduli for every input. The
power and losslessness terminology in this file is internal to that normalization convention.

## ii. Scope and conventions

`ModeAmplitude` uses Mathlib's complex `EuclideanSpace`, whose `L²` inner product is the natural
one for a finite family of mutually power-orthogonal channels. Evanescent or non-power-orthogonal
modes require a more general flux pairing. Finite power-orthogonal radiation channels fit this
API, while an unmodeled radiation continuum requires an integration layer.

The index type may encode ports, propagation directions, polarizations, spatial modes, or a
combination of these. A `ModeTransform ι κ` has input modes indexed by `ι` and output modes
indexed by `κ`; its row index is therefore an output mode and its column index is an input mode. A
`ScatteringMatrix ι` uses the same channel index set for distinct incident and outgoing amplitude
spaces.

## iii. Main definitions

- `ModeAmplitude`: a complex Euclidean space of power-normalized mode amplitudes.
- `ModeAmplitude.power`: the total modal power.
- `ModeTransform`: a matrix mapping input mode amplitudes to output mode amplitudes.
- `ModeTransform.toLinearMap`: the induced linear map between mode-amplitude spaces.
- `ModeTransform.IsPowerPreserving`: a transform preserves total modal power.
- `ModeTransform.IsPassive`: a transform does not increase total modal power.
- `ScatteringMatrix`: a wrapped square transform from incident to outgoing amplitudes.
- `ScatteringMatrix.IsLossless`: a scattering matrix is unitary.

## iv. Future connections

These definitions are independent of how a mode is obtained from an electromagnetic field. Later
files can connect the normalization convention to Poynting flux and use the resulting scattering
matrices to assemble optical networks. That bridge is required before interpreting modal power
preservation as a theorem about physical electromagnetic energy flux.

-/

@[expose] public section

namespace Optics

open Matrix
open scoped ComplexConjugate

noncomputable section

/-! ## A. Mode amplitudes and power -/

/-- The complex Euclidean space of amplitudes for optical modes indexed by `ι`.

The amplitudes are interpreted using a power-normalized convention. -/
abbrev ModeAmplitude (ι : Type*) := EuclideanSpace ℂ ι

/-- The total power carried by a finite family of power-normalized mode amplitudes. This is the
squared `L²` norm of the amplitude vector. -/
def ModeAmplitude.power {ι : Type*} [Fintype ι] (a : ModeAmplitude ι) : ℝ :=
  ‖a‖ ^ 2

/-- Total modal power is the sum of the squared moduli of the component amplitudes. -/
lemma ModeAmplitude.power_eq_sum_normSq {ι : Type*} [Fintype ι] (a : ModeAmplitude ι) :
    a.power = ∑ i, Complex.normSq (a i) := by
  simp [ModeAmplitude.power, EuclideanSpace.norm_sq_eq, Complex.normSq_eq_norm_sq]

/-- The total modal power is nonnegative. -/
lemma ModeAmplitude.power_nonneg {ι : Type*} [Fintype ι] (a : ModeAmplitude ι) :
    0 ≤ a.power := sq_nonneg ‖a‖

/-- A finite mode amplitude has zero total power exactly when every amplitude is zero. -/
@[simp]
lemma ModeAmplitude.power_eq_zero_iff {ι : Type*} [Fintype ι] (a : ModeAmplitude ι) :
    a.power = 0 ↔ a = 0 := by simp [ModeAmplitude.power]

/-- Scaling all mode amplitudes scales their total power by the squared modulus of the scalar. -/
lemma ModeAmplitude.power_smul {ι : Type*} [Fintype ι] (z : ℂ) (a : ModeAmplitude ι) :
    (z • a).power = Complex.normSq z * a.power := by
  rw [ModeAmplitude.power, norm_smul, mul_pow, Complex.sq_norm]
  rfl

/-- Modal power, cast to `ℂ`, is the Hermitian inner product of an amplitude with itself. -/
lemma ModeAmplitude.ofReal_power_eq_inner_self {ι : Type*} [Fintype ι]
    (a : ModeAmplitude ι) : Complex.ofReal a.power = inner ℂ a a := by
  simp [ModeAmplitude.power, inner_self_eq_norm_sq_to_K]

/-! ## B. Mode transforms -/

/-- A complex matrix mapping mode amplitudes indexed by `ι` to amplitudes indexed by `κ`.

Rows are indexed by output modes and columns by input modes. The action on amplitudes is
`T.toLinearMap a`; componentwise, it is `T *ᵥ WithLp.ofLp a`. -/
abbrev ModeTransform (ι κ : Type*) := Matrix κ ι ℂ

/-- The linear map between mode-amplitude spaces induced by a mode transform. -/
abbrev ModeTransform.toLinearMap {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (T : ModeTransform ι κ) : ModeAmplitude ι →ₗ[ℂ] ModeAmplitude κ :=
  Matrix.toEuclideanLin T

/-- A mode transform is power-preserving when it preserves total modal power for every input. -/
def ModeTransform.IsPowerPreserving {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (T : ModeTransform ι κ) : Prop :=
  ∀ a : ModeAmplitude ι, ModeAmplitude.power (T.toLinearMap a) = a.power

/-- A mode transform is passive when it never increases total modal power. -/
def ModeTransform.IsPassive {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (T : ModeTransform ι κ) : Prop :=
  ∀ a : ModeAmplitude ι, ModeAmplitude.power (T.toLinearMap a) ≤ a.power

/- The ambient norm inherited by the matrix alias is an entrywise norm, not the induced
operator norm on mode amplitudes. Consequently, passivity should not be rewritten as `‖T‖ ≤ 1`
without a separate operator-norm bridge. -/

/-- The identity mode transform preserves power. -/
@[simp]
lemma ModeTransform.isPowerPreserving_one {ι : Type*} [Fintype ι] [DecidableEq ι] :
    IsPowerPreserving (1 : ModeTransform ι ι) := by
  simp [IsPowerPreserving]

/-- A cascade of power-preserving mode transforms is power-preserving. -/
lemma ModeTransform.IsPowerPreserving.mul {ι κ μ : Type*} [Fintype ι] [Fintype κ]
    [Fintype μ] [DecidableEq ι] [DecidableEq κ]
    {T : ModeTransform ι κ} {U : ModeTransform κ μ}
    (hU : U.IsPowerPreserving) (hT : T.IsPowerPreserving) :
    ModeTransform.IsPowerPreserving (U * T) := by
  intro a
  simpa only [ModeTransform.toLinearMap, Matrix.toLpLin_mul_same, LinearMap.comp_apply]
    using (hU (T.toLinearMap a)).trans (hT a)

/-- A cascade of passive mode transforms is passive. -/
lemma ModeTransform.IsPassive.mul {ι κ μ : Type*} [Fintype ι] [Fintype κ]
    [Fintype μ] [DecidableEq ι] [DecidableEq κ]
    {T : ModeTransform ι κ} {U : ModeTransform κ μ}
    (hU : U.IsPassive) (hT : T.IsPassive) : ModeTransform.IsPassive (U * T) := by
  intro a
  simpa only [ModeTransform.toLinearMap, Matrix.toLpLin_mul_same, LinearMap.comp_apply]
    using (hU (T.toLinearMap a)).trans (hT a)

/-- A power-preserving mode transform is passive. -/
lemma ModeTransform.IsPowerPreserving.isPassive {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ]
    {T : ModeTransform ι κ} (hT : T.IsPowerPreserving) : T.IsPassive :=
  fun a => (hT a).le

/-- A mode transform satisfying the isometry equation `Tᴴ * T = 1` preserves power. -/
lemma ModeTransform.isPowerPreserving_of_conjTranspose_mul_self {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {T : ModeTransform ι κ}
    (hT : Tᴴ * T = 1) : T.IsPowerPreserving := by
  have hcomp : (Matrix.toEuclideanLin T).adjoint.comp (Matrix.toEuclideanLin T) =
      LinearMap.id := by
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
      ← Matrix.toLpLin_mul_same, hT]
    simpa only using (Matrix.toLpLin_one (n := ι) (R := ℂ) 2)
  intro a
  apply Complex.ofReal_injective
  rw [ModeAmplitude.ofReal_power_eq_inner_self, ModeAmplitude.ofReal_power_eq_inner_self]
  calc
    inner ℂ (T.toLinearMap a) (T.toLinearMap a) =
        inner ℂ ((T.toLinearMap.adjoint.comp T.toLinearMap) a) a := by
      rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left]
    _ = inner ℂ a a := by rw [hcomp, LinearMap.id_apply]

/-! ## C. Scattering matrices -/

/-- A scattering matrix from incident to outgoing amplitudes on channels indexed by `ι`.

The wrapper prevents scattering devices from inheriting matrix multiplication: reflective
multiport devices compose through network equations rather than ordinary cascade multiplication.
The common index labels physically distinct incident and outgoing coordinate spaces. -/
structure ScatteringMatrix (ι : Type*) where
  /-- The underlying linear transform from incident amplitudes to outgoing amplitudes. -/
  toModeTransform : ModeTransform ι ι

/-- A scattering matrix is lossless when it is unitary.

For a complete modeled family of mutually power-orthogonal propagating channels, this condition
implies conservation of total incident power. Absorption, or omission of radiation channels or
physical ports, generally leaves only a passive reduced scattering matrix. -/
def ScatteringMatrix.IsLossless {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : ScatteringMatrix ι) : Prop :=
  S.toModeTransform ∈ Matrix.unitaryGroup ι ℂ

/-- A lossless scattering matrix preserves total modal power. -/
lemma ScatteringMatrix.IsLossless.isPowerPreserving {ι : Type*}
    [Fintype ι] [DecidableEq ι] {S : ScatteringMatrix ι} (hS : S.IsLossless) :
    ModeTransform.IsPowerPreserving S.toModeTransform := by
  apply ModeTransform.isPowerPreserving_of_conjTranspose_mul_self
  rw [← star_eq_conjTranspose]
  exact Matrix.mem_unitaryGroup_iff'.mp hS

/-- A lossless scattering matrix is passive. -/
lemma ScatteringMatrix.IsLossless.isPassive {ι : Type*}
    [Fintype ι] [DecidableEq ι] {S : ScatteringMatrix ι} (hS : S.IsLossless) :
    ModeTransform.IsPassive S.toModeTransform := hS.isPowerPreserving.isPassive

end

end Optics
