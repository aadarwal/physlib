/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Physlib.Mathematics.LinearAlgebra.Matrix.SelfAdjoint

/-!
# Optical coherency matrices

## i. Overview

This file defines general optical coherency data as a complex positive-semidefinite matrix. Unlike
a Jones vector, a coherency matrix can represent partially polarized light. The definition is
generic in its index type so the same object can retain polarization coherences both within and
between optical modes.

## ii. Key results

- `CoherencyMatrix`: a complex matrix together with positive semidefiniteness.
- `CoherencyMatrix.toSelfAdjoint`: coherency data as a bundled self-adjoint matrix.
- `CoherencyMatrix.trace`: the real, nonnegative trace of finite coherency data.
- `CoherencyMatrix.map`: the transformation `C ↦ A * C * Aᴴ` induced by a linear amplitude map.
- `PolarizationCoherency`: coherency data on two polarization coordinates.
- `MultimodePolarizationCoherency`: joint mode-polarization coherency data.

## iii. Table of contents

- A. General coherency data
- B. Diagonal and trace observables
- C. Linear transformation of coherency data
- D. Polarization specializations

## iv. References

No Jones-purity or rank-one assumption is stored here. Pure-state constructions and their rank,
determinant, and phase-invariance results belong in a later module that imports the Jones API.
Finiteness assumptions occur only on operations that form finite sums; they are not fields of the
coherency structure.

-/

@[expose] public section

namespace Optics

open Matrix
open scoped ComplexConjugate ComplexOrder

noncomputable section

/-!
## A. General coherency data
-/

/-- A complex positive-semidefinite matrix describing optical second-order coherences.

The index type is unrestricted. In particular, using a product of mode and polarization indices
retains off-diagonal cross-mode coherences. -/
@[ext]
structure CoherencyMatrix (ι : Type*) where
  /-- The complex matrix of pairwise coherences. -/
  toMatrix : Matrix ι ι ℂ
  /-- The coherency matrix is positive semidefinite. -/
  posSemidef : toMatrix.PosSemidef

namespace CoherencyMatrix

/-- A coherency matrix is Hermitian. -/
lemma isHermitian {ι : Type*} (C : CoherencyMatrix ι) : C.toMatrix.IsHermitian :=
  C.posSemidef.isHermitian

/-- Bundle a coherency matrix as a self-adjoint matrix. -/
def toSelfAdjoint {ι : Type*} (C : CoherencyMatrix ι) :
    selfAdjoint (Matrix ι ι ℂ) :=
  ⟨C.toMatrix, C.isHermitian⟩

/-- The matrix underlying the self-adjoint form of coherency data is unchanged. -/
@[simp]
lemma toSelfAdjoint_val {ι : Type*} (C : CoherencyMatrix ι) :
    C.toSelfAdjoint.val = C.toMatrix := rfl

/-!
## B. Diagonal and trace observables
-/

/-- Every diagonal entry of a coherency matrix is nonnegative in Mathlib's scoped complex star
order. -/
lemma diagonal_nonneg {ι : Type*} (C : CoherencyMatrix ι) (i : ι) :
    0 ≤ C.toMatrix i i :=
  C.posSemidef.diag_nonneg

/-- The real part of every diagonal coherency entry is nonnegative. -/
lemma diagonal_re_nonneg {ι : Type*} (C : CoherencyMatrix ι) (i : ι) :
    0 ≤ (C.toMatrix i i).re :=
  (Complex.nonneg_iff.mp (C.diagonal_nonneg i)).1

/-- Every diagonal coherency entry has zero imaginary part. -/
lemma diagonal_im_eq_zero {ι : Type*} (C : CoherencyMatrix ι) (i : ι) :
    (C.toMatrix i i).im = 0 :=
  (Complex.nonneg_iff.mp (C.diagonal_nonneg i)).2.symm

/-- The real trace of a finite coherency matrix. -/
def trace {ι : Type*} [Fintype ι] (C : CoherencyMatrix ι) : ℝ :=
  (Matrix.trace C.toMatrix).re

/-- The trace of a finite coherency matrix is nonnegative. -/
lemma trace_nonneg {ι : Type*} [Fintype ι] (C : CoherencyMatrix ι) : 0 ≤ C.trace :=
  (Complex.nonneg_iff.mp C.posSemidef.trace_nonneg).1

/-- Casting the real coherency trace to `ℂ` recovers the matrix trace. -/
@[simp]
lemma coe_trace {ι : Type*} [Fintype ι] (C : CoherencyMatrix ι) :
    (C.trace : ℂ) = Matrix.trace C.toMatrix := by
  exact (Complex.eq_re_of_ofReal_le C.posSemidef.trace_nonneg).symm

/-!
## C. Linear transformation of coherency data
-/

/-- Transform coherency data by the linear amplitude map `A`, sending `C` to `A * C * Aᴴ`. -/
def map {ι κ : Type*} [Fintype ι] [Finite κ]
    (C : CoherencyMatrix ι) (A : Matrix κ ι ℂ) : CoherencyMatrix κ where
  toMatrix := A * C.toMatrix * Aᴴ
  posSemidef := C.posSemidef.mul_mul_conjTranspose_same A

/-- The matrix underlying a mapped coherency is `A * C * Aᴴ`. -/
@[simp]
lemma map_toMatrix {ι κ : Type*} [Fintype ι] [Finite κ]
    (C : CoherencyMatrix ι) (A : Matrix κ ι ℂ) :
    (C.map A).toMatrix = A * C.toMatrix * Aᴴ := rfl

/-- The self-adjoint form of coherency transport is the common self-adjoint congruence map. -/
@[simp]
lemma map_toSelfAdjoint {ι κ : Type*} [Fintype ι] [Finite κ]
    (C : CoherencyMatrix ι) (A : Matrix κ ι ℂ) :
    (C.map A).toSelfAdjoint = Matrix.selfAdjointCongruence A C.toSelfAdjoint := by
  apply Subtype.ext
  rfl

/-- The identity amplitude map leaves coherency data unchanged. -/
@[simp]
lemma map_one {ι : Type*} [Fintype ι] [DecidableEq ι] (C : CoherencyMatrix ι) :
    C.map (1 : Matrix ι ι ℂ) = C := by
  ext
  simp

/-- Mapping coherency data through a cascade agrees with mapping through each stage in sequence. -/
@[simp]
lemma map_map {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Finite μ]
    (C : CoherencyMatrix ι) (A : Matrix κ ι ℂ) (B : Matrix μ κ ℂ) :
    (C.map A).map B = C.map (B * A) := by
  ext
  simp [Matrix.mul_assoc]

end CoherencyMatrix

/-!
## D. Polarization specializations
-/

/-- Coherency data for two polarization coordinates. -/
abbrev PolarizationCoherency := CoherencyMatrix (Fin 2)

/-- Joint coherency data on optical modes and two polarization coordinates.

Because the matrix uses the combined index, entries between distinct modes remain available rather
than being discarded into separate per-mode polarization matrices. -/
abbrev MultimodePolarizationCoherency (ι : Type*) := CoherencyMatrix (ι × Fin 2)

end

end Optics
