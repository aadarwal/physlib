/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Finite matrix rank criteria

## i. Overview

This file supplies elementary finite matrix-rank criteria that are useful across physics
APIs but are not currently packaged by Mathlib in the required forms.

## ii. Key results

- `Matrix.rank_eq_zero_iff`: a finite matrix has rank zero exactly when it is the zero matrix.
- `Matrix.rank_eq_card_iff_det_ne_zero`: a square finite matrix over a field has full rank exactly
  when its determinant is nonzero.
- `Matrix.rank_eq_one_iff_ne_zero_and_det_eq_zero`: a two-by-two matrix over a field has rank one
  exactly when it is nonzero and singular.

## iii. Table of contents

- A. Rank criteria

## iv. References

These results follow from the existing linear-map range and determinant criteria for finite matrix
rank.
-/

@[expose] public section

namespace Matrix

/-!

## A. Rank criteria

-/

/-- A matrix with a finite column index over a field has rank zero exactly when it is zero. -/
lemma rank_eq_zero_iff {K m n : Type*} [Field K] [Fintype n] [DecidableEq n]
    (A : Matrix m n K) : A.rank = 0 ↔ A = 0 := by
  rw [Matrix.rank, Submodule.finrank_eq_zero, LinearMap.range_eq_bot]
  change Matrix.toLin' A = 0 ↔ A = 0
  exact LinearEquiv.map_eq_zero_iff Matrix.toLin'

/-- A square finite matrix over a field has full rank exactly when its determinant is nonzero. -/
lemma rank_eq_card_iff_det_ne_zero {K n : Type*} [Field K] [Fintype n] [DecidableEq n]
    (A : Matrix n n K) : A.rank = Fintype.card n ↔ A.det ≠ 0 := by
  constructor
  · intro h
    have hli : LinearIndependent K A.col := by
      rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank,
        ← A.rank_eq_finrank_span_cols]
      exact h.symm
    have hunit : IsUnit A := Matrix.linearIndependent_cols_iff_isUnit.mp hli
    exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det A).mp hunit)
  · exact Matrix.rank_of_det_ne_zero

/-- A two-by-two matrix over a field has rank one exactly when it is nonzero and singular. -/
lemma rank_eq_one_iff_ne_zero_and_det_eq_zero {K : Type*} [Field K]
    (A : Matrix (Fin 2) (Fin 2) K) :
    A.rank = 1 ↔ A ≠ 0 ∧ A.det = 0 := by
  constructor
  · intro hrank
    constructor
    · intro hzero
      rw [hzero, Matrix.rank_zero] at hrank
      omega
    · by_contra hdet
      have hfull : A.rank = 2 := by
        simpa using (Matrix.rank_eq_card_iff_det_ne_zero A).mpr hdet
      omega
  · rintro ⟨hnonzero, hdet⟩
    have hrank_ne_zero : A.rank ≠ 0 := by
      intro hrank
      exact hnonzero ((Matrix.rank_eq_zero_iff A).mp hrank)
    have hrank_ne_two : A.rank ≠ 2 := by
      intro hrank
      have hdet_ne : A.det ≠ 0 :=
        (Matrix.rank_eq_card_iff_det_ne_zero A).mp (by simpa using hrank)
      exact hdet_ne hdet
    have hrank_le_two : A.rank ≤ 2 := Matrix.rank_le_width A
    omega

end Matrix
