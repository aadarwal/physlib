/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Physlib.Mathematics.PauliMatrices.SelfAdjoint
public import Physlib.Relativity.MinkowskiMatrix
/-!

# Covariant self-adjoint Pauli matrices

This file develops the covariant Pauli basis, in which the three spatial Pauli matrices are
negated, and relates it to the contravariant basis using the Minkowski metric.

-/

@[expose] public section

noncomputable section

namespace PauliMatrix

open Matrix Module KroneckerDelta Complex

/-! ## A. The covariant Pauli basis -/

/-- An auxiliary function which on `i : Fin 1 ⊕ Fin 3` returns the corresponding
  Pauli-matrix as a self-adjoint matrix with a minus sign for `Sum.inr _`. -/
def pauliSelfAdjoint' (i : Fin 1 ⊕ Fin 3) : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ) :=
  match i with
  | Sum.inl 0 => ⟨σ0, pauliMatrix_selfAdjoint _⟩
  | Sum.inr 0 => ⟨-σ1, by rw [AddSubgroup.neg_mem_iff]; exact pauliMatrix_selfAdjoint _⟩
  | Sum.inr 1 => ⟨-σ2, by rw [AddSubgroup.neg_mem_iff]; exact pauliMatrix_selfAdjoint _⟩
  | Sum.inr 2 => ⟨-σ3, by rw [AddSubgroup.neg_mem_iff]; exact pauliMatrix_selfAdjoint _⟩

/-- Trace orthogonality of the covariant Pauli basis:
  `tr (σ'_a σ'_b) = 2 δ_{a b}`. -/
lemma trace_pauliSelfAdjoint'_mul (a b : Fin 1 ⊕ Fin 3) :
    Matrix.trace ((pauliSelfAdjoint' a).1 * (pauliSelfAdjoint' b).1) =
      if a = b then 2 else 0 := by
  rcases a with a | a <;> rcases b with b | b <;>
    fin_cases a <;> fin_cases b <;>
    simp only [pauliSelfAdjoint', Matrix.neg_mul, Matrix.mul_neg,
      Matrix.trace_neg, neg_neg, trace_pauliMatrix_mul_pauliMatrix,
      KroneckerDelta.kroneckerDelta] <;>
    simp

/-- The trace pairing of a covariant Pauli matrix with an arbitrary matrix, expressed through the
matrix entries. -/
lemma trace_pauliSelfAdjoint'_mul_apply (l : Fin 1 ⊕ Fin 3)
    (N : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.trace ((pauliSelfAdjoint' l).1 * N) =
      match l with
      | Sum.inl 0 => N 0 0 + N 1 1
      | Sum.inr 0 => -(N 0 1 + N 1 0)
      | Sum.inr 1 => -(Complex.I * (N 0 1 - N 1 0))
      | Sum.inr 2 => -(N 0 0 - N 1 1) := by
  rcases l with l | l <;> fin_cases l <;>
    simp [pauliSelfAdjoint', pauliMatrix, Matrix.trace, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.diag] <;>
    ring

/-- The Pauli matrices where `σi` are negated are linearly independent. -/
lemma pauliSelfAdjoint'_linearly_independent : LinearIndependent ℝ pauliSelfAdjoint' := by
  apply Fintype.linearIndependent_iff.mpr
  intro g hg
  simp only [Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
    Finset.sum_singleton] at hg
  rw [Fin.sum_univ_three] at hg
  simp only [Fin.isValue, pauliSelfAdjoint'] at hg
  intro i
  have h1 := congrArg (fun A => (Matrix.trace (pauliMatrix i * A.1))) hg
  simp [-real_smul, mul_add] at h1
  fin_cases i <;> simpa [pauliMatrix, kroneckerDelta] using h1

/-- The Pauli matrices where `σi` are negated span all Self-adjoint matrices. -/
lemma pauliSelfAdjoint'_span : ⊤ ≤ Submodule.span ℝ (Set.range pauliSelfAdjoint') := by
  refine (Submodule.top_le_span_range_iff_forall_exists_fun ℝ).mpr ?_
  intro A
  let c : Fin 1 ⊕ Fin 3 → ℝ := fun i =>
    match i with
    | Sum.inl 0 => 1/2 * (Matrix.trace (σ0 * A.1)).re
    | Sum.inr 0 => - 1/2 * (Matrix.trace (σ1 * A.1)).re
    | Sum.inr 1 => - 1/2 * (Matrix.trace (σ2 * A.1)).re
    | Sum.inr 2 => - 1/2 * (Matrix.trace (σ3 * A.1)).re
  use c
  simp only [one_div, Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
    Finset.sum_singleton, Fin.sum_univ_three, c]
  apply selfAdjoint_ext
  · simp only [pauliSelfAdjoint', AddSubgroup.coe_add, selfAdjoint.val_smul, smul_neg, mul_add,
    Algebra.mul_smul_comm, mul_neg, trace_add, trace_smul, σ0_σ0_trace, real_smul, ofReal_mul,
    ofReal_inv, ofReal_ofNat, trace_neg, σ0_σ1_trace, smul_zero, neg_zero, σ0_σ2_trace, add_zero,
    σ0_σ3_trace, mul_re, inv_re, re_ofNat, normSq_ofNat, div_self_mul_self', ofReal_re, inv_im,
    im_ofNat, zero_div, ofReal_im, mul_zero, sub_zero, mul_im, zero_mul]
    ring
  · simp only [pauliSelfAdjoint', AddSubgroup.coe_add, selfAdjoint.val_smul, smul_neg, mul_add,
    Algebra.mul_smul_comm, mul_neg, trace_add, trace_smul, σ1_σ0_trace, smul_zero, trace_neg,
    σ1_σ1_trace, real_smul, ofReal_mul, ofReal_div, ofReal_neg, ofReal_one, ofReal_ofNat,
    σ1_σ2_trace, neg_zero, add_zero, σ1_σ3_trace, zero_add, neg_re, mul_re, div_ofNat_re, one_re,
    ofReal_re, div_ofNat_im, neg_im, one_im, zero_div, ofReal_im, mul_zero, sub_zero, re_ofNat,
    mul_im, zero_mul, im_ofNat]
    ring
  · simp only [pauliSelfAdjoint', AddSubgroup.coe_add, selfAdjoint.val_smul, smul_neg, mul_add,
    Algebra.mul_smul_comm, mul_neg, trace_add, trace_smul, σ2_σ0_trace, smul_zero, trace_neg,
    σ2_σ1_trace, neg_zero, σ2_σ2_trace, real_smul, ofReal_mul, ofReal_div, ofReal_neg, ofReal_one,
    ofReal_ofNat, zero_add, σ2_σ3_trace, add_zero, neg_re, mul_re, div_ofNat_re, one_re, ofReal_re,
    div_ofNat_im, neg_im, one_im, zero_div, ofReal_im, mul_zero, sub_zero, re_ofNat, mul_im,
    zero_mul, im_ofNat]
    ring
  · simp only [pauliSelfAdjoint', AddSubgroup.coe_add, selfAdjoint.val_smul, smul_neg, mul_add,
    Algebra.mul_smul_comm, mul_neg, trace_add, trace_smul, σ3_σ0_trace, smul_zero, trace_neg,
    σ3_σ1_trace, neg_zero, σ3_σ2_trace, add_zero, σ3_σ3_trace, real_smul, ofReal_mul, ofReal_div,
    ofReal_neg, ofReal_one, ofReal_ofNat, zero_add, neg_re, mul_re, div_ofNat_re, one_re, ofReal_re,
    div_ofNat_im, neg_im, one_im, zero_div, ofReal_im, mul_zero, sub_zero, re_ofNat, mul_im,
    zero_mul, im_ofNat]
    ring

/-- The basis of `selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)` formed by Pauli matrices
  where the `1, 2, 3` pauli matrices are negated. These can be thought of as the
  covariant Pauli-matrices. -/
def pauliBasis' : Basis (Fin 1 ⊕ Fin 3) ℝ (selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) :=
  Basis.mk pauliSelfAdjoint'_linearly_independent pauliSelfAdjoint'_span

/-! ## B. Coordinates in the covariant Pauli basis -/

/-- The decomposition of a self-adjoint matrix into the Pauli matrices (where `σi` are negated). -/
lemma pauliBasis'_decomp (M : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) :
    M = (1/2 * (Matrix.trace (σ0 * M.1)).re) • pauliBasis' (Sum.inl 0)
    + (-1/2 * (Matrix.trace (σ1 * M.1)).re) • pauliBasis' (Sum.inr 0)
    + (-1/2 * (Matrix.trace (σ2 * M.1)).re) • pauliBasis' (Sum.inr 1)
    + (-1/2 * (Matrix.trace (σ3 * M.1)).re) • pauliBasis' (Sum.inr 2) := by
  apply selfAdjoint_ext
  · simp only [Fin.isValue, one_div, pauliBasis', Basis.coe_mk, pauliSelfAdjoint',
    AddSubgroup.coe_add, selfAdjoint.val_smul, smul_neg, mul_add, Algebra.mul_smul_comm, mul_neg,
    trace_add, trace_smul, σ0_σ0_trace, real_smul, ofReal_mul, ofReal_inv, ofReal_ofNat, trace_neg,
    σ0_σ1_trace, smul_zero, neg_zero, add_zero, σ0_σ2_trace, σ0_σ3_trace, mul_re, inv_re, re_ofNat,
    normSq_ofNat, div_self_mul_self', ofReal_re, inv_im, im_ofNat, zero_div, ofReal_im, mul_zero,
    sub_zero, mul_im, zero_mul]
    ring
  · simp only [Fin.isValue, one_div, pauliBasis', Basis.coe_mk, pauliSelfAdjoint',
    AddSubgroup.coe_add, selfAdjoint.val_smul, smul_neg, mul_add, Algebra.mul_smul_comm, mul_neg,
    trace_add, trace_smul, σ1_σ0_trace, smul_zero, trace_neg, σ1_σ1_trace, real_smul, ofReal_mul,
    ofReal_div, ofReal_neg, ofReal_one, ofReal_ofNat, zero_add, σ1_σ2_trace, neg_zero, add_zero,
    σ1_σ3_trace, neg_re, mul_re, div_ofNat_re, one_re, ofReal_re, div_ofNat_im, neg_im, one_im,
    zero_div, ofReal_im, mul_zero, sub_zero, re_ofNat, mul_im, zero_mul, im_ofNat]
    ring
  · simp only [Fin.isValue, one_div, pauliBasis', Basis.coe_mk, pauliSelfAdjoint',
    AddSubgroup.coe_add, selfAdjoint.val_smul, smul_neg, mul_add, Algebra.mul_smul_comm, mul_neg,
    trace_add, trace_smul, σ2_σ0_trace, smul_zero, trace_neg, σ2_σ1_trace, neg_zero, add_zero,
    σ2_σ2_trace, real_smul, ofReal_mul, ofReal_div, ofReal_neg, ofReal_one, ofReal_ofNat, zero_add,
    σ2_σ3_trace, neg_re, mul_re, div_ofNat_re, one_re, ofReal_re, div_ofNat_im, neg_im, one_im,
    zero_div, ofReal_im, mul_zero, sub_zero, re_ofNat, mul_im, zero_mul, im_ofNat]
    ring
  · simp only [Fin.isValue, one_div, pauliBasis', Basis.coe_mk, pauliSelfAdjoint',
    AddSubgroup.coe_add, selfAdjoint.val_smul, smul_neg, mul_add, Algebra.mul_smul_comm, mul_neg,
    trace_add, trace_smul, σ3_σ0_trace, smul_zero, trace_neg, σ3_σ1_trace, neg_zero, add_zero,
    σ3_σ2_trace, σ3_σ3_trace, real_smul, ofReal_mul, ofReal_div, ofReal_neg, ofReal_one,
    ofReal_ofNat, zero_add, neg_re, mul_re, div_ofNat_re, one_re, ofReal_re, div_ofNat_im, neg_im,
    one_im, zero_div, ofReal_im, mul_zero, sub_zero, re_ofNat, mul_im, zero_mul, im_ofNat]
    ring

/-- The component of a self-adjoint matrix in the direction `σ0` under
  the basis formed by the covariant Pauli matrices. -/
@[simp]
lemma pauliBasis'_repr_inl_0 (M : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) :
    pauliBasis'.repr M (Sum.inl 0) = 1 / 2 * Matrix.trace (σ0 * M.1) := by
  have hM : M = ∑ i, pauliBasis'.repr M i • pauliBasis' i :=
    (Basis.sum_repr pauliBasis' M).symm
  simp only [Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
    Finset.sum_singleton, Fin.sum_univ_three] at hM
  have h0 := congrArg (fun A => Matrix.trace (σ0 * A.1)/ 2) hM
  simp only [Fin.isValue, pauliBasis', Basis.mk_repr, Basis.coe_mk, pauliSelfAdjoint',
    AddSubgroup.coe_add, selfAdjoint.val_smul, smul_neg, mul_add, Algebra.mul_smul_comm, mul_neg,
    trace_add, trace_smul, σ0_σ0_trace, real_smul, trace_neg, σ0_σ1_trace, smul_zero, neg_zero,
    σ0_σ2_trace, add_zero, σ0_σ3_trace, isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, IsUnit.mul_div_cancel_right] at h0
  linear_combination (norm := ring_nf) -h0
  simp [pauliBasis']

/-- The component of a self-adjoint matrix in the direction `-σ1` under
  the basis formed by the covariant Pauli matrices. -/
@[simp]
lemma pauliBasis'_repr_inr_0 (M : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) :
    pauliBasis'.repr M (Sum.inr 0) = - 1 / 2 * Matrix.trace (σ1 * M.1) := by
  have hM : M = ∑ i, pauliBasis'.repr M i • pauliBasis' i :=
    (Basis.sum_repr pauliBasis' M).symm
  simp only [Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
    Finset.sum_singleton, Fin.sum_univ_three] at hM
  have h0 := congrArg (fun A => - Matrix.trace (σ1 * A.1)/ 2) hM
  simp only [Fin.isValue, pauliBasis', Basis.mk_repr, Basis.coe_mk, pauliSelfAdjoint',
    AddSubgroup.coe_add, selfAdjoint.val_smul, smul_neg, mul_add, Algebra.mul_smul_comm, mul_neg,
    trace_add, trace_smul, σ1_σ0_trace, smul_zero, trace_neg, σ1_σ1_trace, real_smul, σ1_σ2_trace,
    neg_zero, add_zero, σ1_σ3_trace, zero_add, neg_neg, isUnit_iff_ne_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, IsUnit.mul_div_cancel_right] at h0
  linear_combination (norm := ring_nf) -h0
  simp [pauliBasis']

/-- The component of a self-adjoint matrix in the direction `-σ2` under
  the basis formed by the covariant Pauli matrices. -/
@[simp]
lemma pauliBasis'_repr_inr_1 (M : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) :
    pauliBasis'.repr M (Sum.inr 1) = - 1 / 2 * Matrix.trace (σ2 * M.1) := by
  have hM : M = ∑ i, pauliBasis'.repr M i • pauliBasis' i :=
    (Basis.sum_repr pauliBasis' M).symm
  simp only [Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
    Finset.sum_singleton, Fin.sum_univ_three] at hM
  have h0 := congrArg (fun A => - Matrix.trace (σ2 * A.1)/ 2) hM
  simp only [Fin.isValue, pauliBasis', Basis.mk_repr, Basis.coe_mk, pauliSelfAdjoint',
    AddSubgroup.coe_add, selfAdjoint.val_smul, smul_neg, mul_add, Algebra.mul_smul_comm, mul_neg,
    trace_add, trace_smul, σ2_σ0_trace, smul_zero, trace_neg, σ2_σ1_trace, neg_zero, σ2_σ2_trace,
    real_smul, zero_add, σ2_σ3_trace, add_zero, neg_neg, isUnit_iff_ne_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, IsUnit.mul_div_cancel_right] at h0
  linear_combination (norm := ring_nf) -h0
  simp [pauliBasis']

/-- The component of a self-adjoint matrix in the direction `-σ3` under
  the basis formed by the covariant Pauli matrices. -/
@[simp]
lemma pauliBasis'_repr_inr_2 (M : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) :
    pauliBasis'.repr M (Sum.inr 2) = - 1 / 2 * Matrix.trace (σ3 * M.1) := by
  have hM : M = ∑ i, pauliBasis'.repr M i • pauliBasis' i :=
    (Basis.sum_repr pauliBasis' M).symm
  simp only [Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
    Finset.sum_singleton, Fin.sum_univ_three] at hM
  have h0 := congrArg (fun A => - Matrix.trace (σ3 * A.1)/ 2) hM
  simp only [Fin.isValue, pauliBasis', Basis.mk_repr, Basis.coe_mk, pauliSelfAdjoint',
    AddSubgroup.coe_add, selfAdjoint.val_smul, smul_neg, mul_add, Algebra.mul_smul_comm, mul_neg,
    trace_add, trace_smul, σ3_σ0_trace, smul_zero, trace_neg, σ3_σ1_trace, neg_zero, σ3_σ2_trace,
    add_zero, σ3_σ3_trace, real_smul, zero_add, neg_neg, isUnit_iff_ne_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, IsUnit.mul_div_cancel_right] at h0
  linear_combination (norm := ring_nf) -h0
  simp only [pauliBasis', Basis.mk_repr, Fin.isValue, sub_self]

/-! ## C. Relation to the Minkowski metric -/

/-- The relationship between the basis `pauliBasis` of contravariant Pauli-matrices and the basis
  `pauliBasis'` of covariant Pauli matrices is by multiplication by the Minkowski matrix. -/
lemma pauliBasis_minkowskiMetric_pauliBasis' (i : Fin 1 ⊕ Fin 3) :
    pauliBasis i = minkowskiMatrix i i • pauliBasis' i := by
  fin_cases i <;>
    simp [pauliSelfAdjoint', pauliSelfAdjoint, pauliBasis, pauliBasis',
      minkowskiMatrix.inr_i_inr_i, Subtype.ext_iff, NegMemClass.coe_neg, neg_neg]

end PauliMatrix
