/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Congruence maps on self-adjoint complex matrices

## i. Overview

This file bundles the matrix congruence `C ↦ A * C * Aᴴ` as a real-linear map between spaces of
self-adjoint complex matrices. The construction permits rectangular `A`, so it applies both to
changes within one finite coordinate space and to amplitude maps between different finite spaces.

## ii. Main definitions

- `Matrix.selfAdjointCongruence`: real-linear congruence by a complex matrix.

## iii. Main results

- `Matrix.selfAdjointCongruence_one`: congruence by the identity is the identity map.
- `Matrix.selfAdjointCongruence_mul`: matrix multiplication corresponds to composition.
- `Matrix.selfAdjointCongruence_smul`: scalar multiplication contributes squared modulus.
-/

@[expose] public section

open scoped ComplexConjugate

noncomputable section

namespace Matrix

/-!
## A. Self-adjoint congruence
-/

/-- The real-linear map on self-adjoint complex matrices induced by `C ↦ A * C * Aᴴ`.

The input matrix is indexed by `ι`, the output matrix by `κ`, and the rows of `A` are output
coordinates while its columns are input coordinates. -/
def selfAdjointCongruence {ι κ : Type*} [Fintype ι]
    (A : Matrix κ ι ℂ) :
    selfAdjoint (Matrix ι ι ℂ) →ₗ[ℝ] selfAdjoint (Matrix κ κ ℂ) where
  toFun C := ⟨A * C.val * Aᴴ, selfAdjoint.mem_iff.mpr <| by
    have hC : C.valᴴ = C.val := by
      have h := selfAdjoint.mem_iff.mp C.property
      simpa only [Matrix.star_eq_conjTranspose] using h
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hC, Matrix.mul_assoc]⟩
  map_add' C D := Subtype.ext <| by
    change A * (C.val + D.val) * Aᴴ = A * C.val * Aᴴ + A * D.val * Aᴴ
    rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' r C := Subtype.ext <| by simp

/-- The matrix underlying self-adjoint congruence is `A * C * Aᴴ`. -/
@[simp]
lemma selfAdjointCongruence_apply_val {ι κ : Type*} [Fintype ι]
    (A : Matrix κ ι ℂ) (C : selfAdjoint (Matrix ι ι ℂ)) :
    (selfAdjointCongruence A C).val = A * C.val * Aᴴ := rfl

/-- Congruence by the identity matrix is the identity real-linear map. -/
@[simp]
lemma selfAdjointCongruence_one {ι : Type*} [Fintype ι] [DecidableEq ι] :
    selfAdjointCongruence (1 : Matrix ι ι ℂ) = LinearMap.id := by
  apply LinearMap.ext
  intro C
  apply Subtype.ext
  simp

/-- Congruence by a product is composition of the two congruence maps. -/
lemma selfAdjointCongruence_mul {ι κ μ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix κ ι ℂ) (B : Matrix μ κ ℂ) :
    selfAdjointCongruence (B * A) =
      (selfAdjointCongruence B).comp (selfAdjointCongruence A) := by
  apply LinearMap.ext
  intro C
  apply Subtype.ext
  change (B * A) * C.val * (B * A)ᴴ = B * (A * C.val * Aᴴ) * Bᴴ
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- Scaling a congruence matrix by `z` scales the induced real-linear map by `normSq z`. -/
lemma selfAdjointCongruence_smul {ι κ : Type*} [Fintype ι]
    (z : ℂ) (A : Matrix κ ι ℂ) :
    selfAdjointCongruence (z • A) = Complex.normSq z • selfAdjointCongruence A := by
  apply LinearMap.ext
  intro C
  apply Subtype.ext
  ext i j
  simp only [selfAdjointCongruence_apply_val, LinearMap.smul_apply, selfAdjoint.val_smul,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.conjTranspose_smul, Matrix.smul_apply,
    smul_eq_mul]
  change conj z * (z * (A * C.val * Aᴴ) i j) =
    (Complex.normSq z : ℂ) * (A * C.val * Aᴴ) i j
  rw [← mul_assoc, ← Complex.normSq_eq_conj_mul_self]

end Matrix

end
