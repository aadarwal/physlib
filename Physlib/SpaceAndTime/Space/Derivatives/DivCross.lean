/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.SpaceAndTime.Space.CrossProduct
public import Physlib.SpaceAndTime.Space.Derivatives.Div

/-!
# Divergence in an oriented three-dimensional frame

## i. Overview

This file expresses the divergence of a differentiable vector field in an arbitrary ordered
three-dimensional frame. Multiplication by the frame's oriented volume converts the divergence
into the sum of three directional derivatives paired with the corresponding oriented cofactors.

The frame is not required to be orthogonal, normalized, or nondegenerate. This pointwise identity
is the differential algebra behind affine-box divergence formulas.

## ii. Key results

- `div_mul_inner_cross_eq_sum_inner_fderiv`: divergence times the oriented frame volume is the
  sum of the three cofactor-weighted directional derivatives.

## iii. Table of contents

- A. Divergence in an oriented frame

## iv. References

This is neutral vector-calculus infrastructure.
-/

@[expose] public section

open Matrix

namespace Space

noncomputable section

/-! ## A. Divergence in an oriented frame -/

/-- Divergence times the oriented volume of an ordered frame equals the sum of the field's
directional derivatives paired with the three oriented cofactors. -/
lemma div_mul_inner_cross_eq_sum_inner_fderiv
    (field : Space → EuclideanSpace ℝ (Fin 3)) (x : Space)
    (first second third : Space) (hf : DifferentiableAt ℝ field x) :
    (∇ ⬝ field) x * inner ℝ (basis.repr first)
        (basis.repr second ⨯ₑ₃ basis.repr third) =
      inner ℝ (fderiv ℝ field x first)
          (basis.repr second ⨯ₑ₃ basis.repr third) +
        inner ℝ (fderiv ℝ field x second)
          (basis.repr third ⨯ₑ₃ basis.repr first) +
        inner ℝ (fderiv ℝ field x third)
          (basis.repr first ⨯ₑ₃ basis.repr second) := by
  have hCoordinate (i j : Fin 3) :
      ∂[i] (fun y ↦ field y j) x = ∂[i] field x j := by
    rw [deriv_eq_fderiv_basis, deriv_eq_fderiv_basis]
    change fderiv ℝ (EuclideanSpace.proj j ∘ field) x (basis i) = _
    rw [fderiv_comp x (EuclideanSpace.proj j).differentiableAt hf]
    simp [-EuclideanSpace.coe_proj, ← deriv_eq_fderiv_basis]
  rw [fderiv_eq_sum_deriv field x first,
    fderiv_eq_sum_deriv field x second,
    fderiv_eq_sum_deriv field x third]
  simp only [div, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    crossProduct, WithLp.equiv_apply, WithLp.equiv_symm_apply,
    LinearMap.mk₂_apply, Fin.sum_univ_three, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, basis_repr_apply, PiLp.add_apply,
    PiLp.smul_apply, smul_eq_mul]
  simp_rw [hCoordinate]
  ring

end
end Space
