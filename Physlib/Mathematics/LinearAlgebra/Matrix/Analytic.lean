/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Analytic families of complex matrices

## i. Overview

A family of complex matrices depending on a parameter is treated entrywise: the family is regular
when each of its entries is. This file records that the finite algebraic matrix operations
preserve entrywise analyticity, and that the total matrix inverse does so wherever the determinant
does not vanish.

Everything is stated entrywise rather than for the matrix as a point of a normed space. The
determinant and the adjugate are finite signed sums of products of entries, so no inverse-function
theorem is used for them; only the reciprocal of the determinant needs a nonvanishing hypothesis,
and that is exactly Mathlib's determinant/adjugate presentation `Matrix.inv_def` of the total
inverse. Away from a vanishing determinant nothing here claims that the total inverse is an
inverse.

## ii. Main results

- `analyticAt_matrix_mul_entry`: entries of a product of entrywise-analytic families are analytic.
- `analyticAt_matrix_det`: the determinant of an entrywise-analytic square family is analytic.
- `analyticAt_matrix_adjugate_entry`: adjugate entries of an entrywise-analytic square family are
  analytic.
- `analyticAt_matrix_inv_entry`: inverse entries are analytic wherever the determinant is nonzero.
-/

@[expose] public section

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-!
## A. Products
-/

/-- Entries of a product of two entrywise-analytic matrix families are analytic. -/
lemma analyticAt_matrix_mul_entry {ι κ μ : Type*} [Fintype κ]
    {left : E → Matrix ι κ ℂ} {right : E → Matrix κ μ ℂ} {point : E}
    (hLeft : ∀ row column, AnalyticAt ℂ (fun x => left x row column) point)
    (hRight : ∀ row column, AnalyticAt ℂ (fun x => right x row column) point)
    (row : ι) (column : μ) :
    AnalyticAt ℂ (fun x => (left x * right x) row column) point := by
  simp only [Matrix.mul_apply]
  exact Finset.analyticAt_fun_sum _ fun middle _ =>
    (hLeft row middle).mul (hRight middle column)

/-!
## B. Determinant and adjugate
-/

/-- The determinant of an entrywise-analytic square-matrix family is analytic.

The determinant is a finite signed sum of products of entries, so this needs no nonvanishing
hypothesis.
-/
lemma analyticAt_matrix_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    {family : E → Matrix ι ι ℂ} {point : E}
    (hEntries : ∀ row column, AnalyticAt ℂ (fun x => family x row column) point) :
    AnalyticAt ℂ (fun x => (family x).det) point := by
  simp only [Matrix.det_apply']
  exact Finset.analyticAt_fun_sum _ fun _ _ =>
    analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun _ _ => hEntries _ _)

/-- Entries of the adjugate of an entrywise-analytic square-matrix family are analytic. -/
lemma analyticAt_matrix_adjugate_entry {ι : Type*} [Fintype ι] [DecidableEq ι]
    {family : E → Matrix ι ι ℂ} {point : E}
    (hEntries : ∀ row column, AnalyticAt ℂ (fun x => family x row column) point)
    (row column : ι) :
    AnalyticAt ℂ (fun x => (family x).adjugate row column) point := by
  simp only [Matrix.adjugate_apply]
  refine analyticAt_matrix_det fun first second => ?_
  by_cases hRow : first = column
  · subst hRow
    simpa only [Matrix.updateRow_self] using analyticAt_const
  · simpa only [Matrix.updateRow_ne hRow] using hEntries first second

/-!
## C. The total inverse away from a vanishing determinant
-/

/-- Entries of the total inverse of an entrywise-analytic square-matrix family are analytic
wherever the determinant does not vanish.

This is exactly `Matrix.inv_def`: away from a vanishing determinant the total inverse is a
reciprocal determinant times a polynomial adjugate. Nothing is claimed about it elsewhere.
-/
lemma analyticAt_matrix_inv_entry {ι : Type*} [Fintype ι] [DecidableEq ι]
    {family : E → Matrix ι ι ℂ} {point : E}
    (hEntries : ∀ row column, AnalyticAt ℂ (fun x => family x row column) point)
    (hDet : (family point).det ≠ 0) (row column : ι) :
    AnalyticAt ℂ (fun x => (family x)⁻¹ row column) point := by
  simp only [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv, smul_eq_mul]
  exact ((analyticAt_matrix_det hEntries).inv hDet).mul
    (analyticAt_matrix_adjugate_entry hEntries row column)

end
