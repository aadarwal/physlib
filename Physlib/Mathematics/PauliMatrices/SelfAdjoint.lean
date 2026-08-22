/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.Matrix.PosDef
public import Physlib.Mathematics.PauliMatrices.Basic
/-!

# Self-adjoint Pauli matrices

This file develops the real Pauli basis of self-adjoint `2 × 2` complex matrices. It gives
trace-based coordinates and the basis-fixed, Relativity-independent scalar-vector decomposition of
such matrices.

## Main definitions

- `pauliSelfAdjoint`: the Pauli matrices as self-adjoint matrices.
- `pauliBasis`: the real Pauli basis of self-adjoint matrices.
- `pauliCoeffEquiv`: the real-linear coordinate equivalence induced by that basis.
- `pauliCoeff`, `scalarCoeff`, and `vectorCoeff`: explicit coordinates in that basis.
- `vectorPart` and `pauliRadius`: the spatial Pauli part and its Euclidean length.
- `posSemidef_iff_pauliRadius_le_scalarCoeff`: the positive-semidefinite Pauli cone.
-/

@[expose] public section

noncomputable section

namespace PauliMatrix

open Matrix Module KroneckerDelta
open scoped ComplexOrder

/-! ## A. The real Pauli basis -/

/-- The trace of a pauli-matrix multiplied by a self-adjoint `2×2` matrix is real. -/
lemma trace_pauliMatrix_mul_selfAdjoint_re (μ : Fin 1 ⊕ Fin 3)
    (A : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) :
    (Matrix.trace (pauliMatrix μ * A.1)).re = Matrix.trace (pauliMatrix μ * A.1) := by
  rw [← Complex.conj_eq_iff_re, starRingEnd_apply, ← trace_conjTranspose, conjTranspose_mul,
    pauliMatrix_selfAdjoint μ, ← star_eq_conjTranspose, A.2, trace_mul_comm]

open Complex

/-- Two `2×2` self-adjoint matrices are equal if the (complex) traces of each matrix multiplied by
  each of the Pauli-matrices are equal. -/
lemma selfAdjoint_ext_complex {A B : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)}
    (h0 : Matrix.trace (σ0 * A.1) = Matrix.trace (σ0 * B.1))
    (h1 : Matrix.trace (σ1 * A.1) = Matrix.trace (σ1 * B.1))
    (h2 : Matrix.trace (σ2 * A.1) = Matrix.trace (σ2 * B.1))
    (h3 : Matrix.trace (σ3 * A.1) = Matrix.trace (σ3 * B.1)) : A = B := by
  ext i j
  rw [eta_fin_two A.1, eta_fin_two B.1] at h0 h1 h2 h3
  simp only [Fin.isValue, pauliMatrix_inl_zero_eq_one, one_mul, trace_fin_two_of] at h0
  simp only [pauliMatrix, Fin.isValue, cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd, vecMul_cons,
    head_cons, zero_smul, tail_cons, one_smul, empty_vecMul, add_zero, zero_add, empty_mul,
    Equiv.symm_apply_apply, trace_fin_two_of] at h1
  simp only [pauliMatrix, Fin.isValue, cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd, vecMul_cons,
    head_cons, zero_smul, tail_cons, neg_smul, smul_cons, smul_eq_mul, smul_empty, neg_cons,
    neg_empty, empty_vecMul, add_zero, zero_add, empty_mul, Equiv.symm_apply_apply,
    trace_fin_two_of] at h2
  simp only [pauliMatrix, Fin.isValue, cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd, vecMul_cons,
    head_cons, one_smul, tail_cons, zero_smul, empty_vecMul, add_zero, neg_smul, neg_cons,
    neg_empty, zero_add, empty_mul, Equiv.symm_apply_apply, trace_fin_two_of] at h3
  match i, j with
  | 0, 0 =>
    linear_combination (norm := ring_nf) (h0 + h3) / 2
  | 0, 1 =>
    linear_combination (norm := ring_nf) (h1 - I * h2) / 2
    simp
  | 1, 0 =>
    linear_combination (norm := ring_nf) (h1 + I * h2) / 2
    simp
  | 1, 1 =>
    linear_combination (norm := ring_nf) (h0 - h3) / 2

/-- Two `2×2` self-adjoint matrices are equal if the real traces of each matrix multiplied by
  each of the Pauli-matrices are equal. -/
lemma selfAdjoint_ext {A B : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)}
    (h0 : ((Matrix.trace (σ0 * A.1))).re = ((Matrix.trace (σ0 * B.1))).re)
    (h1 : ((Matrix.trace (σ1 * A.1))).re = ((Matrix.trace (σ1 * B.1))).re)
    (h2 : ((Matrix.trace (σ2 * A.1))).re = ((Matrix.trace (σ2 * B.1))).re)
    (h3 : ((Matrix.trace (σ3 * A.1))).re = ((Matrix.trace (σ3 * B.1))).re) :
    A = B := by
  have h0' := congrArg ofRealHom h0
  have h1' := congrArg ofRealHom h1
  have h2' := congrArg ofRealHom h2
  have h3' := congrArg ofRealHom h3
  rw [ofRealHom_eq_coe, ofRealHom_eq_coe] at h0' h1' h2' h3'
  rw [trace_pauliMatrix_mul_selfAdjoint_re _ A,
    trace_pauliMatrix_mul_selfAdjoint_re _ B] at h0' h1' h2' h3'
  exact selfAdjoint_ext_complex h0' h1' h2' h3'

/-- An auxiliary function which on `i : Fin 1 ⊕ Fin 3` returns the corresponding
Pauli matrix as a self-adjoint matrix. -/
def pauliSelfAdjoint (i : Fin 1 ⊕ Fin 3) :
    selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ) :=
  ⟨pauliMatrix i, pauliMatrix_selfAdjoint i⟩

/-- The Pauli matrices are linearly independent. -/
lemma pauliSelfAdjoint_linearly_independent : LinearIndependent ℝ pauliSelfAdjoint := by
  apply Fintype.linearIndependent_iff.mpr
  intro g hg
  simp only [Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
    Finset.sum_singleton] at hg
  rw [Fin.sum_univ_three] at hg
  simp only [Fin.isValue, pauliSelfAdjoint] at hg
  intro i
  have h1 := congrArg (fun A => Matrix.trace (pauliMatrix i * A.1)) hg
  simp only [Fin.isValue, AddSubgroup.coe_add, selfAdjoint.val_smul, mul_add,
    Algebra.mul_smul_comm, trace_add, trace_smul, ZeroMemClass.coe_zero, mul_zero,
    trace_zero] at h1
  fin_cases i <;> simpa [pauliMatrix, kroneckerDelta] using h1

/-- Pauli matrices are orthogonal with respect to the trace pairing: `tr(σ_μ σ_ν) = 2 δ_μν`. -/
@[simp]
lemma trace_pauliMatrix_mul_pauliMatrix (μ ν : Fin 1 ⊕ Fin 3) :
    Matrix.trace (pauliMatrix μ * pauliMatrix ν) = ((2 * kroneckerDelta μ ν : ℕ) : ℂ) := by
  fin_cases μ <;> fin_cases ν <;> simp [kroneckerDelta, pauliMatrix] <;> norm_num

/-- The four real Pauli coefficients of a self-adjoint `2 × 2` matrix. -/
noncomputable def pauliCoeff
    (A : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) :
    Fin 1 ⊕ Fin 3 → ℝ
  | Sum.inl 0 => 1 / 2 * (Matrix.trace (σ0 * A.1)).re
  | Sum.inr 0 => 1 / 2 * (Matrix.trace (σ1 * A.1)).re
  | Sum.inr 1 => 1 / 2 * (Matrix.trace (σ2 * A.1)).re
  | Sum.inr 2 => 1 / 2 * (Matrix.trace (σ3 * A.1)).re

/-- Every self-adjoint `2 × 2` matrix is its Pauli decomposition. -/
lemma sum_pauliCoeff
    (A : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) :
    ∑ i, pauliCoeff A i • pauliSelfAdjoint i = A := by
  simp only [Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
    Finset.sum_singleton, Fin.sum_univ_three, pauliCoeff]
  apply selfAdjoint_ext
  · simp only [pauliSelfAdjoint, AddSubgroup.coe_add, selfAdjoint.val_smul, mul_add,
      Algebra.mul_smul_comm, trace_add, trace_smul, σ0_σ0_trace, real_smul, ofReal_mul,
      σ0_σ1_trace, smul_zero, σ0_σ2_trace, add_zero,
      σ0_σ3_trace, mul_re, re_ofNat,
      ofReal_re, im_ofNat, ofReal_im, mul_zero, sub_zero,
      mul_im, zero_mul]
    ring
  · simp only [pauliSelfAdjoint, AddSubgroup.coe_add, selfAdjoint.val_smul, mul_add,
      Algebra.mul_smul_comm, trace_add, trace_smul, σ1_σ0_trace, smul_zero,
      σ1_σ1_trace, real_smul, ofReal_mul, σ1_σ2_trace,
      add_zero, σ1_σ3_trace, zero_add, mul_re, re_ofNat,
      ofReal_re, im_ofNat, ofReal_im,
      mul_zero, sub_zero, mul_im, zero_mul]
    ring
  · simp only [pauliSelfAdjoint, AddSubgroup.coe_add, selfAdjoint.val_smul, mul_add,
      Algebra.mul_smul_comm, trace_add, trace_smul, σ2_σ0_trace, smul_zero,
      σ2_σ1_trace, σ2_σ2_trace, real_smul, ofReal_mul,
      zero_add, σ2_σ3_trace, add_zero, mul_re, re_ofNat,
      ofReal_re, im_ofNat, ofReal_im,
      mul_zero, sub_zero, mul_im, zero_mul]
    ring
  · simp only [pauliSelfAdjoint, AddSubgroup.coe_add, selfAdjoint.val_smul, mul_add,
      Algebra.mul_smul_comm, trace_add, trace_smul, σ3_σ0_trace, smul_zero,
      σ3_σ1_trace, σ3_σ2_trace, add_zero, σ3_σ3_trace, real_smul, ofReal_mul,
      zero_add, mul_re, re_ofNat,
      ofReal_re, im_ofNat, ofReal_im,
      mul_zero, sub_zero, mul_im, zero_mul]
    ring

/-- Every self-adjoint `2 × 2` matrix is a real linear combination of the Pauli matrices. -/
lemma eq_sum_pauli
    (A : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) :
    A = ∑ i, pauliCoeff A i • pauliSelfAdjoint i :=
  (sum_pauliCoeff A).symm

/-- The Pauli matrices span all self-adjoint matrices. -/
lemma pauliSelfAdjoint_span :
    ⊤ ≤ Submodule.span ℝ (Set.range pauliSelfAdjoint) := by
  refine (Submodule.top_le_span_range_iff_forall_exists_fun ℝ).mpr ?_
  intro A
  exact ⟨pauliCoeff A, sum_pauliCoeff A⟩

/-- The basis of `selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)` formed by Pauli matrices. -/
def pauliBasis :
    Basis (Fin 1 ⊕ Fin 3) ℝ (selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) :=
  Basis.mk pauliSelfAdjoint_linearly_independent pauliSelfAdjoint_span

/-! ## B. Pauli coordinates of self-adjoint `2 × 2` matrices -/

/-- The real-linear Pauli-coordinate equivalence for self-adjoint `2 × 2` complex matrices. -/
noncomputable def pauliCoeffEquiv :
    selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ) ≃ₗ[ℝ] (Fin 1 ⊕ Fin 3 → ℝ) :=
  pauliBasis.equivFun

/-- The bundled Pauli-coordinate equivalence returns the half-trace coefficients. -/
@[simp]
lemma pauliCoeffEquiv_apply
    (A : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) (μ : Fin 1 ⊕ Fin 3) :
    pauliCoeffEquiv A μ = pauliCoeff A μ := by
  change pauliBasis.equivFun A μ = pauliCoeff A μ
  have h : pauliBasis.equivFun A = pauliCoeff A := by
    apply pauliBasis.equivFun.symm.injective
    rw [LinearEquiv.symm_apply_apply, Module.Basis.equivFun_symm_apply]
    simpa only [pauliBasis, Module.Basis.coe_mk] using (sum_pauliCoeff A).symm
  exact congrFun h μ

/-- Pauli coefficients preserve addition of self-adjoint matrices. -/
@[simp]
lemma pauliCoeff_add (A B : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ))
    (μ : Fin 1 ⊕ Fin 3) :
    pauliCoeff (A + B) μ = pauliCoeff A μ + pauliCoeff B μ := by
  rw [← pauliCoeffEquiv_apply, LinearEquiv.map_add]
  simp only [Pi.add_apply, pauliCoeffEquiv_apply]

/-- Pauli coefficients preserve real scalar multiplication. -/
@[simp]
lemma pauliCoeff_smul (r : ℝ) (A : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ))
    (μ : Fin 1 ⊕ Fin 3) :
    pauliCoeff (r • A) μ = r * pauliCoeff A μ := by
  rw [← pauliCoeffEquiv_apply, LinearEquiv.map_smul]
  simp only [Pi.smul_apply, smul_eq_mul, pauliCoeffEquiv_apply]

/-- Every Pauli coefficient of the zero self-adjoint matrix vanishes. -/
@[simp]
lemma pauliCoeff_zero (μ : Fin 1 ⊕ Fin 3) :
    pauliCoeff (0 : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) μ = 0 := by
  rw [← pauliCoeffEquiv_apply, LinearEquiv.map_zero]
  rfl

/-- Reconstructing arbitrary Pauli coordinates forms their real linear combination of the Pauli
matrices. -/
lemma pauliCoeffEquiv_symm_apply (c : Fin 1 ⊕ Fin 3 → ℝ) :
    pauliCoeffEquiv.symm c = ∑ μ, c μ • pauliSelfAdjoint μ := by
  change pauliBasis.equivFun.symm c = _
  rw [Module.Basis.equivFun_symm_apply]
  simp only [pauliBasis, Module.Basis.coe_mk]

/-- The Pauli coefficient of a Pauli basis matrix is its Kronecker coordinate. -/
@[simp]
lemma pauliCoeff_pauliSelfAdjoint (μ ν : Fin 1 ⊕ Fin 3) :
    pauliCoeff (pauliSelfAdjoint μ) ν = if μ = ν then 1 else 0 := by
  rw [← pauliCoeffEquiv_apply]
  change pauliBasis.equivFun (pauliSelfAdjoint μ) ν = _
  simpa only [pauliBasis, Module.Basis.coe_mk] using
    Module.Basis.equivFun_self pauliBasis μ ν

/-- The coefficient of the identity in the Pauli decomposition. -/
noncomputable def scalarCoeff
    (A : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) : ℝ :=
  pauliCoeff A (Sum.inl 0)

/-- The three spatial Pauli coefficients. -/
noncomputable def vectorCoeff
    (A : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) : Fin 3 → ℝ :=
  fun i => pauliCoeff A (Sum.inr i)

/-- The traceless Pauli-vector part `a · σ`. -/
noncomputable def vectorPart
    (A : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  vectorMatrix (vectorCoeff A)

/-- The Euclidean length of the spatial Pauli coefficients. -/
noncomputable def pauliRadius
    (A : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) : ℝ :=
  Real.sqrt (∑ i : Fin 3, vectorCoeff A i ^ 2)

/-- The Pauli radius is the square root of the squared Euclidean length of the
spatial Pauli coefficients. -/
lemma pauliRadius_sq
    (A : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) :
    pauliRadius A ^ 2 =
      ∑ i : Fin 3, vectorCoeff A i ^ 2 := by
  rw [pauliRadius, Real.sq_sqrt]
  positivity

@[simp]
lemma pauliRadius_nonneg
    (A : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) :
    0 ≤ pauliRadius A :=
  Real.sqrt_nonneg _

/-! ### B.1. Scalar-vector decomposition -/

/-- A self-adjoint matrix is its scalar part plus its Pauli-vector part. -/
lemma matrix_eq_scalar_add_vector
    (A : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) :
    A.val = (scalarCoeff A : ℂ) • 1 + vectorPart A := by
  have h := congrArg
    (fun B : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ) => B.val)
    (sum_pauliCoeff A)
  simp only [Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero,
    Finset.sum_singleton, Fin.sum_univ_three, pauliSelfAdjoint,
    AddSubgroup.coe_add, selfAdjoint.val_smul] at h
  rw [← h]
  simp [scalarCoeff, vectorPart, vectorMatrix, vectorCoeff,
    Fin.sum_univ_three, pauliMatrix_inl_zero_eq_one]

/-- The trace of a self-adjoint matrix is twice its scalar Pauli coefficient. -/
lemma trace_eq_two_mul_scalarCoeff
    (A : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) :
    Matrix.trace A.1 = 2 * scalarCoeff A := by
  have htrace :
      ((Matrix.trace A.1).re : ℂ) = Matrix.trace A.1 := by
    simpa [pauliMatrix_inl_zero_eq_one] using
      trace_pauliMatrix_mul_selfAdjoint_re (Sum.inl 0) A
  rw [scalarCoeff, pauliCoeff]
  simp only [pauliMatrix_inl_zero_eq_one, one_mul]
  calc
    Matrix.trace A.1 = ((Matrix.trace A.1).re : ℂ) := htrace.symm
    _ = 2 * ((1 / 2 * (Matrix.trace A.1).re : ℝ) : ℂ) := by
      push_cast
      ring

/-- The Pauli-vector part has zero trace. -/
@[simp]
lemma trace_vectorPart
    (A : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) :
    Matrix.trace (vectorPart A) = 0 := by
  have h := congrArg Matrix.trace (matrix_eq_scalar_add_vector A)
  simp only [trace_add, trace_smul, smul_eq_mul, Matrix.trace_one, Fintype.card_fin,
    Nat.cast_ofNat, trace_eq_two_mul_scalarCoeff A] at h
  linear_combination -h

/-- The square of the vector part of a self-adjoint matrix is its squared
Pauli radius times the identity. -/
lemma vectorPart_sq
    (A : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) :
    vectorPart A * vectorPart A =
      (pauliRadius A ^ 2 : ℝ) • 1 := by
  rw [vectorPart, vectorMatrix_sq, ← pauliRadius_sq]

/-! ## C. Positive semidefinite Pauli coordinates -/

/-- The Pauli-vector part of a self-adjoint matrix is Hermitian. -/
lemma vectorPart_isHermitian
    (A : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) :
    (vectorPart A).IsHermitian := by
  have hself : IsSelfAdjoint (scalarCoeff A : ℂ) := by
    rw [isSelfAdjoint_iff]
    exact Complex.conj_ofReal _
  have hscalar :
      (((scalarCoeff A : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))).IsHermitian :=
    Matrix.isHermitian_one.smul hself
  have hV : vectorPart A = A.val - (scalarCoeff A : ℂ) • 1 := by
    rw [matrix_eq_scalar_add_vector]
    abel
  rw [hV]
  exact A.property.sub hscalar

/-- The determinant of a self-adjoint `2 × 2` matrix is the squared scalar Pauli coefficient
minus the squared Pauli radius. -/
lemma det_eq_scalarCoeff_sq_sub_pauliRadius_sq
    (A : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) :
    Matrix.det A.val =
      ((scalarCoeff A ^ 2 - pauliRadius A ^ 2 : ℝ) : ℂ) := by
  have hr : (pauliRadius A : ℂ) ^ 2 =
      ∑ i : Fin 3, (vectorCoeff A i : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, pauliRadius_sq]
    simp only [Complex.ofReal_sum, Complex.ofReal_pow]
  rw [matrix_eq_scalar_add_vector, Matrix.det_fin_two]
  push_cast
  rw [hr]
  simp [vectorPart, vectorMatrix, Fin.sum_univ_three, pauliMatrix]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- A zero Pauli radius forces the Pauli-vector part to vanish. -/
lemma vectorPart_eq_zero_of_pauliRadius_eq_zero
    (A : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ))
    (h : pauliRadius A = 0) : vectorPart A = 0 := by
  apply Matrix.conjTranspose_mul_self_eq_zero.mp
  rw [(vectorPart_isHermitian A).eq, vectorPart_sq, h]
  simp

/-- The Pauli radius times the identity plus the Pauli-vector part is positive semidefinite. -/
lemma pauliRadius_one_add_vectorPart_posSemidef
    (A : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) :
    ((pauliRadius A : ℂ) • 1 + vectorPart A).PosSemidef := by
  let r : ℝ := pauliRadius A
  let V : Matrix (Fin 2) (Fin 2) ℂ := vectorPart A
  have hr : 0 ≤ r := pauliRadius_nonneg A
  change ((r : ℂ) • 1 + V).PosSemidef
  by_cases hr0 : r = 0
  · have hV0 : V = 0 := vectorPart_eq_zero_of_pauliRadius_eq_zero A hr0
    rw [hr0, Complex.ofReal_zero, zero_smul, hV0, add_zero]
    exact Matrix.PosSemidef.zero
  · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
    let B : Matrix (Fin 2) (Fin 2) ℂ := (r : ℂ) • 1 + V
    have hBherm : B.IsHermitian := by
      apply Matrix.IsHermitian.add
      · apply Matrix.isHermitian_one.smul
        rw [isSelfAdjoint_iff]
        exact Complex.conj_ofReal _
      · exact vectorPart_isHermitian A
    have hB_sq : B * B = (2 * r : ℝ) • B := by
      dsimp [B, V]
      rw [add_mul, mul_add, mul_add, vectorPart_sq]
      simp only [Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one, smul_add]
      module
    have hBB : (Bᴴ * B).PosSemidef :=
      Matrix.posSemidef_conjTranspose_mul_self B
    rw [hBherm.eq, hB_sq] at hBB
    have hs := hBB.smul (show (0 : ℝ) ≤ (2 * r)⁻¹ by positivity)
    have htwo : (2 * r : ℝ) ≠ 0 := mul_ne_zero two_ne_zero hr0
    have heq : (2 * r : ℝ)⁻¹ • ((2 * r : ℝ) • B) = B := by
      rw [smul_smul, inv_mul_cancel₀ htwo, one_smul]
    change B.PosSemidef
    rw [← heq]
    exact hs

/-- A self-adjoint `2 × 2` complex matrix is positive semidefinite exactly when its Pauli radius
is at most its scalar Pauli coefficient. -/
lemma posSemidef_iff_pauliRadius_le_scalarCoeff
    (A : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) :
    A.val.PosSemidef ↔ pauliRadius A ≤ scalarCoeff A := by
  constructor
  · intro hA
    have htrace := hA.trace_nonneg
    rw [trace_eq_two_mul_scalarCoeff] at htrace
    have h2c : 0 ≤ 2 * scalarCoeff A := Complex.zero_le_real.mp (by
      simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using htrace)
    have hc : 0 ≤ scalarCoeff A := by linarith
    have hdet := hA.det_nonneg
    rw [det_eq_scalarCoeff_sq_sub_pauliRadius_sq] at hdet
    have hsq : pauliRadius A ^ 2 ≤ scalarCoeff A ^ 2 := by
      have hreal : 0 ≤ scalarCoeff A ^ 2 - pauliRadius A ^ 2 :=
        Complex.zero_le_real.mp hdet
      linarith
    nlinarith [pauliRadius_nonneg A]
  · intro hrc
    let c : ℝ := scalarCoeff A
    let r : ℝ := pauliRadius A
    let V : Matrix (Fin 2) (Fin 2) ℂ := vectorPart A
    rw [matrix_eq_scalar_add_vector]
    change ((c : ℂ) • 1 + V).PosSemidef
    have hdecomp :
        (c : ℂ) • 1 + V = ((c - r : ℝ) : ℂ) • 1 + ((r : ℂ) • 1 + V) := by
      module
    rw [hdecomp]
    apply Matrix.PosSemidef.add
    · apply Matrix.PosSemidef.one.smul
      exact Complex.zero_le_real.mpr (sub_nonneg.mpr hrc)
    · exact pauliRadius_one_add_vectorPart_posSemidef A

end PauliMatrix
