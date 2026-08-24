/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Mathlib.Analysis.InnerProductSpace.Positive

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
- `ModeAmplitude.directSum`: the parallel concatenation of two mode-amplitude families.
- `ModeAmplitude.directSumLinearEquiv`: the algebraic identification of a pair with its disjoint
  sum.
- `ModeTransform`: a matrix mapping input mode amplitudes to output mode amplitudes.
- `ModeTransform.toLinearMap`: the induced linear map between mode-amplitude spaces.
- `ModeTransform.IsPowerPreserving`: a transform preserves total modal power.
- `ModeTransform.IsPassive`: a transform does not increase total modal power.
- `ModeTransform.directSum`: the block-diagonal parallel composition of two transforms.
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
open scoped ComplexConjugate ComplexOrder

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

/-- The parallel concatenation of two disjoint families of mode amplitudes. -/
def ModeAmplitude.directSum {ι μ : Type*} (a : ModeAmplitude ι) (b : ModeAmplitude μ) :
    ModeAmplitude (ι ⊕ μ) :=
  WithLp.toLp 2 (Sum.elim (WithLp.ofLp a) (WithLp.ofLp b))

/-- A direct-sum amplitude restricts to its first family on the left summand. -/
@[simp]
lemma ModeAmplitude.directSum_apply_inl {ι μ : Type*} (a : ModeAmplitude ι)
    (b : ModeAmplitude μ) (i : ι) : a.directSum b (Sum.inl i) = a i := rfl

/-- A direct-sum amplitude restricts to its second family on the right summand. -/
@[simp]
lemma ModeAmplitude.directSum_apply_inr {ι μ : Type*} (a : ModeAmplitude ι)
    (b : ModeAmplitude μ) (i : μ) : a.directSum b (Sum.inr i) = b i := rfl

/-- The restriction of a direct-sum amplitude to its left index family. -/
def ModeAmplitude.restrictInl {ι μ : Type*} (a : ModeAmplitude (ι ⊕ μ)) : ModeAmplitude ι :=
  WithLp.toLp 2 (WithLp.ofLp a ∘ Sum.inl)

/-- The restriction of a direct-sum amplitude to its right index family. -/
def ModeAmplitude.restrictInr {ι μ : Type*} (a : ModeAmplitude (ι ⊕ μ)) : ModeAmplitude μ :=
  WithLp.toLp 2 (WithLp.ofLp a ∘ Sum.inr)

/-- Restriction to the left summand evaluates at the corresponding sum index. -/
@[simp]
lemma ModeAmplitude.restrictInl_apply {ι μ : Type*} (a : ModeAmplitude (ι ⊕ μ)) (i : ι) :
    a.restrictInl i = a (Sum.inl i) := rfl

/-- Restriction to the right summand evaluates at the corresponding sum index. -/
@[simp]
lemma ModeAmplitude.restrictInr_apply {ι μ : Type*} (a : ModeAmplitude (ι ⊕ μ)) (i : μ) :
    a.restrictInr i = a (Sum.inr i) := rfl

/-- Complex-linear restriction from a sum-indexed amplitude to its left family. -/
def ModeAmplitude.restrictInlLinearMap {ι μ : Type*} :
    ModeAmplitude (ι ⊕ μ) →ₗ[ℂ] ModeAmplitude ι where
  toFun := ModeAmplitude.restrictInl
  map_add' first second := by
    apply WithLp.ofLp_injective 2
    funext index
    rfl
  map_smul' scalar amplitude := by
    apply WithLp.ofLp_injective 2
    funext index
    rfl

/-- Complex-linear restriction from a sum-indexed amplitude to its right family. -/
def ModeAmplitude.restrictInrLinearMap {ι μ : Type*} :
    ModeAmplitude (ι ⊕ μ) →ₗ[ℂ] ModeAmplitude μ where
  toFun := ModeAmplitude.restrictInr
  map_add' first second := by
    apply WithLp.ofLp_injective 2
    funext index
    rfl
  map_smul' scalar amplitude := by
    apply WithLp.ofLp_injective 2
    funext index
    rfl

/-- Bundled left restriction agrees with coordinate restriction. -/
@[simp]
lemma ModeAmplitude.restrictInlLinearMap_apply {ι μ : Type*}
    (amplitude : ModeAmplitude (ι ⊕ μ)) :
    (ModeAmplitude.restrictInlLinearMap :
      ModeAmplitude (ι ⊕ μ) →ₗ[ℂ] ModeAmplitude ι) amplitude =
        amplitude.restrictInl := rfl

/-- Bundled right restriction agrees with coordinate restriction. -/
@[simp]
lemma ModeAmplitude.restrictInrLinearMap_apply {ι μ : Type*}
    (amplitude : ModeAmplitude (ι ⊕ μ)) :
    (ModeAmplitude.restrictInrLinearMap :
      ModeAmplitude (ι ⊕ μ) →ₗ[ℂ] ModeAmplitude μ) amplitude =
        amplitude.restrictInr := rfl

/-- Restriction to the left summand recovers the first direct-sum amplitude. -/
@[simp]
lemma ModeAmplitude.restrictInl_directSum {ι μ : Type*} (a : ModeAmplitude ι)
    (b : ModeAmplitude μ) : (a.directSum b).restrictInl = a := rfl

/-- Restriction to the right summand recovers the second direct-sum amplitude. -/
@[simp]
lemma ModeAmplitude.restrictInr_directSum {ι μ : Type*} (a : ModeAmplitude ι)
    (b : ModeAmplitude μ) : (a.directSum b).restrictInr = b := rfl

/-- Every amplitude on a sum-indexed family is the direct sum of its two restrictions. -/
@[simp]
lemma ModeAmplitude.directSum_restrict {ι μ : Type*} (a : ModeAmplitude (ι ⊕ μ)) :
    a.restrictInl.directSum a.restrictInr = a := by
  apply WithLp.ofLp_injective 2
  funext i
  rcases i with i | i <;> rfl

/-- The complex-linear equivalence between a pair of amplitude families and their disjoint sum.

This is an algebraic equivalence, not a normed equivalence: the product space carries its standard
product norm rather than the disjoint sum's `L²` norm.
-/
def ModeAmplitude.directSumLinearEquiv {ι μ : Type*} :
    (ModeAmplitude ι × ModeAmplitude μ) ≃ₗ[ℂ] ModeAmplitude (ι ⊕ μ) where
  toFun pair := pair.1.directSum pair.2
  invFun amplitude := (amplitude.restrictInl, amplitude.restrictInr)
  left_inv pair := by
    ext <;> rfl
  right_inv := ModeAmplitude.directSum_restrict
  map_add' first second := by
    apply WithLp.ofLp_injective 2
    funext index
    rcases index with index | index <;> rfl
  map_smul' scalar amplitude := by
    apply WithLp.ofLp_injective 2
    funext index
    rcases index with index | index <;> rfl

/-- The direct-sum linear equivalence joins its two input amplitude families. -/
@[simp]
lemma ModeAmplitude.directSumLinearEquiv_apply {ι μ : Type*}
    (amplitudes : ModeAmplitude ι × ModeAmplitude μ) :
    ModeAmplitude.directSumLinearEquiv amplitudes = amplitudes.1.directSum amplitudes.2 := rfl

/-- The inverse direct-sum linear equivalence returns both coordinate restrictions. -/
@[simp]
lemma ModeAmplitude.directSumLinearEquiv_symm_apply {ι μ : Type*}
    (amplitude : ModeAmplitude (ι ⊕ μ)) :
    ModeAmplitude.directSumLinearEquiv.symm amplitude =
      (amplitude.restrictInl, amplitude.restrictInr) := rfl

/-- The power of two disjoint mode-amplitude families is the sum of their powers. -/
lemma ModeAmplitude.power_directSum {ι μ : Type*} [Fintype ι] [Fintype μ]
    (a : ModeAmplitude ι) (b : ModeAmplitude μ) :
    (a.directSum b).power = a.power + b.power := by
  simp only [ModeAmplitude.power_eq_sum_normSq, Fintype.sum_sum_type,
    ModeAmplitude.directSum_apply_inl, ModeAmplitude.directSum_apply_inr]

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

/-- The block-diagonal parallel composition of transforms on disjoint input and output modes.

This operation places two independent transforms side by side. It is not a summing junction or a
feedback interconnection. -/
def ModeTransform.directSum {ι κ μ ν : Type*} (T : ModeTransform ι κ)
    (U : ModeTransform μ ν) : ModeTransform (ι ⊕ μ) (κ ⊕ ν) :=
  Matrix.fromBlocks T 0 0 U

/-- A transform assembled from four blocks acts by the corresponding two coupled block
equations. -/
lemma ModeTransform.fromBlocks_apply {ι κ μ ν : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype μ] [DecidableEq μ]
    (A : ModeTransform ι κ) (B : ModeTransform μ κ)
    (C : ModeTransform ι ν) (D : ModeTransform μ ν)
    (a : ModeAmplitude ι) (b : ModeAmplitude μ) :
    ModeTransform.toLinearMap
        (Matrix.fromBlocks A B C D : ModeTransform (ι ⊕ μ) (κ ⊕ ν)) (a.directSum b) =
      (A.toLinearMap a + B.toLinearMap b).directSum
        (C.toLinearMap a + D.toLinearMap b) := by
  apply WithLp.ofLp_injective 2
  funext i
  rcases i with i | i
  · simp [ModeAmplitude.directSum, Matrix.toLpLin_apply, Matrix.fromBlocks_mulVec]
  · simp [ModeAmplitude.directSum, Matrix.toLpLin_apply, Matrix.fromBlocks_mulVec]

/-- A block-diagonal transform acts independently on the two direct-sum amplitude families. -/
lemma ModeTransform.directSum_apply {ι κ μ ν : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype μ] [DecidableEq μ] (T : ModeTransform ι κ) (U : ModeTransform μ ν)
    (a : ModeAmplitude ι) (b : ModeAmplitude μ) :
    (T.directSum U).toLinearMap (a.directSum b) =
      (T.toLinearMap a).directSum (U.toLinearMap b) := by
  apply WithLp.ofLp_injective 2
  funext i
  rcases i with i | i
  · simp [ModeTransform.directSum, ModeAmplitude.directSum, Matrix.toLpLin_apply,
      Matrix.fromBlocks_mulVec]
  · simp [ModeTransform.directSum, ModeAmplitude.directSum, Matrix.toLpLin_apply,
      Matrix.fromBlocks_mulVec]

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

/-- Parallel composition preserves power when each independent transform preserves power. -/
lemma ModeTransform.IsPowerPreserving.directSum {ι κ μ ν : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [Fintype μ] [DecidableEq μ] [Fintype ν]
    {T : ModeTransform ι κ} {U : ModeTransform μ ν} (hT : T.IsPowerPreserving)
    (hU : U.IsPowerPreserving) : (T.directSum U).IsPowerPreserving := by
  intro x
  rw [← ModeAmplitude.directSum_restrict x, ModeTransform.directSum_apply]
  simpa only [ModeAmplitude.power_directSum] using
    congrArg₂ (· + ·) (hT x.restrictInl) (hU x.restrictInr)

/-- Parallel composition is passive when each independent transform is passive. -/
lemma ModeTransform.IsPassive.directSum {ι κ μ ν : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [Fintype μ] [DecidableEq μ] [Fintype ν]
    {T : ModeTransform ι κ} {U : ModeTransform μ ν} (hT : T.IsPassive)
    (hU : U.IsPassive) : (T.directSum U).IsPassive := by
  intro x
  rw [← ModeAmplitude.directSum_restrict x, ModeTransform.directSum_apply]
  simpa only [ModeAmplitude.power_directSum] using
    add_le_add (hT x.restrictInl) (hU x.restrictInr)

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

/-- A finite mode transform preserves power exactly when its columns satisfy the isometry equation
`Tᴴ * T = 1`. -/
lemma ModeTransform.isPowerPreserving_iff_conjTranspose_mul_self {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (T : ModeTransform ι κ) : T.IsPowerPreserving ↔ Tᴴ * T = 1 := by
  constructor
  · intro hT
    have hnorm : ∀ a : ModeAmplitude ι, ‖T.toLinearMap a‖ = ‖a‖ := by
      intro a
      apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      simpa only [ModeAmplitude.power] using hT a
    have hinner : ∀ a b : ModeAmplitude ι,
        inner ℂ (T.toLinearMap a) (T.toLinearMap b) = inner ℂ a b :=
      (LinearMap.norm_map_iff_inner_map_map T.toLinearMap).mp hnorm
    apply Matrix.toEuclideanLin.injective
    rw [Matrix.toLpLin_mul_same, Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
      Matrix.toLpLin_one]
    apply LinearMap.ext
    intro a
    apply ext_inner_right ℂ
    intro b
    rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left, LinearMap.id_apply]
    exact hinner a b
  · exact ModeTransform.isPowerPreserving_of_conjTranspose_mul_self

/-- The quadratic form of the passivity defect `1 - Tᴴ * T` is input power minus output power. -/
lemma ModeTransform.re_inner_one_sub_conjTranspose_mul_self {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (T : ModeTransform ι κ) (a : ModeAmplitude ι) :
    RCLike.re (inner ℂ (Matrix.toEuclideanLin (1 - Tᴴ * T) a) a) =
      a.power - (T.toLinearMap a).power := by
  simp only [map_sub, Matrix.toLpLin_one, LinearMap.sub_apply, LinearMap.id_apply,
    Matrix.toLpLin_mul_same, LinearMap.comp_apply,
    Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  rw [inner_sub_left, LinearMap.adjoint_inner_left, inner_self_eq_norm_sq_to_K,
    inner_self_eq_norm_sq_to_K]
  norm_cast

/-- A finite mode transform is passive exactly when its input-side defect matrix
`1 - Tᴴ * T` is positive semidefinite. -/
lemma ModeTransform.isPassive_iff_posSemidef_one_sub_conjTranspose_mul_self {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (T : ModeTransform ι κ) : T.IsPassive ↔ (1 - Tᴴ * T).PosSemidef := by
  rw [← Matrix.isPositive_toEuclideanLin_iff]
  constructor
  · intro hT
    refine ⟨Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (Matrix.isHermitian_one.sub (Matrix.isHermitian_conjTranspose_mul_self T)), ?_⟩
    intro a
    rw [ModeTransform.re_inner_one_sub_conjTranspose_mul_self]
    exact sub_nonneg.mpr (hT a)
  · intro hT a
    have ha := hT.re_inner_nonneg_left a
    rw [ModeTransform.re_inner_one_sub_conjTranspose_mul_self] at ha
    exact sub_nonneg.mp ha

/-- A square finite mode transform preserves power exactly when it belongs to the unitary group. -/
lemma ModeTransform.isPowerPreserving_iff_mem_unitaryGroup {ι : Type*}
    [Fintype ι] [DecidableEq ι] (T : ModeTransform ι ι) :
    T.IsPowerPreserving ↔ T ∈ Matrix.unitaryGroup ι ℂ := by
  rw [ModeTransform.isPowerPreserving_iff_conjTranspose_mul_self,
    Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]

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

/-- A scattering matrix is lossless exactly when its underlying mode transform preserves power. -/
lemma ScatteringMatrix.isLossless_iff_isPowerPreserving {ι : Type*}
    [Fintype ι] [DecidableEq ι] (S : ScatteringMatrix ι) :
    S.IsLossless ↔ ModeTransform.IsPowerPreserving S.toModeTransform := by
  rw [ModeTransform.isPowerPreserving_iff_mem_unitaryGroup]
  rfl

/-- The independent parallel composition of two scattering matrices on disjoint channels. -/
def ScatteringMatrix.directSum {ι μ : Type*} (S : ScatteringMatrix ι)
    (R : ScatteringMatrix μ) : ScatteringMatrix (ι ⊕ μ) where
  toModeTransform := S.toModeTransform.directSum R.toModeTransform

/-- The independent parallel composition of lossless scattering matrices is lossless. -/
lemma ScatteringMatrix.IsLossless.directSum {ι μ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype μ] [DecidableEq μ]
    {S : ScatteringMatrix ι} {R : ScatteringMatrix μ} (hS : S.IsLossless)
    (hR : R.IsLossless) : (S.directSum R).IsLossless := by
  rw [ScatteringMatrix.isLossless_iff_isPowerPreserving]
  exact hS.isPowerPreserving.directSum hR.isPowerPreserving

end

end Optics
