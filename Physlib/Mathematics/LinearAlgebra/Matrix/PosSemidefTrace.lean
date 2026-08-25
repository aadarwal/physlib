/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Mathlib.Analysis.Matrix.PosDef

/-!
# Traces of products of positive-semidefinite matrices

## i. Overview

A product of two positive-semidefinite matrices need not itself be positive semidefinite, and
need not even be Hermitian, but its trace is always nonnegative. This file proves that fact for
complex matrices on a finite index type.

## ii. Main results

- `Matrix.PosSemidef.trace_mul_nonneg`: the trace of a product of positive-semidefinite complex
  matrices is nonnegative.

## iii. Scope

This file is about matrices only. It carries no physical interpretation and imports nothing from
the physics hierarchy. The proof diagonalizes the right factor by its eigenvector unitary and uses
that congruence preserves positive semidefiniteness, so every diagonal weight and every eigenvalue
in the resulting sum is nonnegative.

## iv. Table of contents

- A. Traces of products

-/

@[expose] public section

open scoped ComplexOrder

namespace Matrix

noncomputable section

/-!

## A. Traces of products

-/

/-- The trace of a product of positive-semidefinite complex matrices is nonnegative. -/
lemma PosSemidef.trace_mul_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    {left right : Matrix ι ι ℂ} (hLeft : left.PosSemidef) (hRight : right.PosSemidef) :
    0 ≤ (left * right).trace := by
  classical
  have hCongruence :
      ((hRight.1.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ * left *
        (hRight.1.eigenvectorUnitary : Matrix ι ι ℂ)).PosSemidef := by
    simpa only [Matrix.conjTranspose_conjTranspose] using
      hLeft.conjTranspose_mul_mul_same (hRight.1.eigenvectorUnitary : Matrix ι ι ℂ)
  have hRightEq :
      right = (hRight.1.eigenvectorUnitary : Matrix ι ι ℂ) *
          Matrix.diagonal (fun index : ι => ((hRight.1.eigenvalues index : ℝ) : ℂ)) *
            (hRight.1.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ := by
    conv_lhs => rw [hRight.1.spectral_theorem]
    rfl
  have hReassociate :
      left * ((hRight.1.eigenvectorUnitary : Matrix ι ι ℂ) *
          Matrix.diagonal (fun index : ι => ((hRight.1.eigenvalues index : ℝ) : ℂ)) *
            (hRight.1.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ) =
        left * (hRight.1.eigenvectorUnitary : Matrix ι ι ℂ) *
            Matrix.diagonal (fun index : ι => ((hRight.1.eigenvalues index : ℝ) : ℂ)) *
          (hRight.1.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ := by
    simp only [Matrix.mul_assoc]
  have hCycle :
      (hRight.1.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ *
          (left * (hRight.1.eigenvectorUnitary : Matrix ι ι ℂ) *
            Matrix.diagonal (fun index : ι => ((hRight.1.eigenvalues index : ℝ) : ℂ))) =
        (hRight.1.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ * left *
            (hRight.1.eigenvectorUnitary : Matrix ι ι ℂ) *
          Matrix.diagonal (fun index : ι => ((hRight.1.eigenvalues index : ℝ) : ℂ)) := by
    simp only [Matrix.mul_assoc]
  rw [hRightEq, hReassociate, Matrix.trace_mul_comm, hCycle]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_diagonal]
  refine Finset.sum_nonneg fun index _ => ?_
  refine mul_nonneg hCongruence.diag_nonneg ?_
  exact Complex.nonneg_iff.mpr ⟨by simpa using hRight.eigenvalues_nonneg index, by simp⟩

end

end Matrix
