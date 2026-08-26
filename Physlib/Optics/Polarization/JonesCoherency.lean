/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Physlib.Optics.Polarization.Basic
public import Physlib.Optics.Polarization.Coherency

/-!
# Pure polarization coherency

## i. Overview

This file embeds a coherent Jones vector into the general positive-semidefinite coherency API. Its
coherency matrix is the outer product `J * Jᴴ`, so it has rank at most one and is unchanged by a
global unit-modulus phase. A nonzero Jones vector represents a fully polarized state; the zero
vector maps to zero coherency and has no polarization direction. Jones-matrix action agrees with
conjugation of coherency data.

For nonzero Jones vectors, the construction represents fully polarized light. General
`PolarizationCoherency` values need not arise from a Jones vector and can represent partially
polarized light.

## ii. Key results

- `JonesVector.coherency`: the pure coherency matrix of a Jones vector.
- `JonesVector.coherency_trace`: pure coherency trace equals squared Jones intensity.
- `JonesVector.coherency_scale_of_norm_eq_one`: global unit-phase invariance.
- `JonesMatrix.act_coherency`: Jones action commutes with coherency transport.

## iii. Table of contents

- A. Pure coherency data
- B. Global phase
- C. Jones transformations

## iv. References

-/

@[expose] public section

namespace Optics

open Matrix
open scoped ComplexConjugate ComplexOrder

noncomputable section

/-!
## A. Pure coherency data
-/

namespace JonesVector

/-- The Jones outer-product coherency matrix associated with a Jones vector.

Its entries are `J i * star (J j)`. Positive semidefiniteness is part of the returned general
`PolarizationCoherency`, so the construction remains distinct from an arbitrary complex matrix.
For the zero Jones vector this is zero coherency, which has no polarization direction.
-/
def coherency (J : JonesVector) : PolarizationCoherency where
  toMatrix := Matrix.vecMulVec J.components (star J.components)
  posSemidef := Matrix.posSemidef_vecMulVec_self_star J.components

/-- The matrix underlying pure Jones coherency is its outer product. -/
@[simp]
lemma coherency_toMatrix (J : JonesVector) :
    J.coherency.toMatrix = Matrix.vecMulVec J.components (star J.components) := rfl

/-- A pure coherency entry is the corresponding Jones outer-product entry. -/
@[simp]
lemma coherency_apply (J : JonesVector) (i j : Fin 2) :
    J.coherency.toMatrix i j = J.components i * star (J.components j) := rfl

/-- The matrix rank of pure Jones coherency is at most one. -/
lemma coherency_rank_le_one (J : JonesVector) : J.coherency.toMatrix.rank ≤ 1 := by
  simpa using Matrix.rank_vecMulVec_le J.components (star J.components)

/-- The determinant of a pure Jones coherency matrix vanishes. -/
lemma coherency_det_eq_zero (J : JonesVector) : J.coherency.toMatrix.det = 0 := by
  simpa using Matrix.det_vecMulVec J.components (star J.components)

/-- The trace of pure Jones coherency equals the squared Jones intensity. -/
@[simp]
lemma coherency_trace (J : JonesVector) : J.coherency.trace = J.intensity := by
  apply Complex.ofReal_injective
  rw [CoherencyMatrix.coe_trace, coherency_toMatrix, Matrix.trace_vecMulVec,
    JonesVector.intensity_eq_sum_normSq]
  simp [dotProduct, Complex.mul_conj]

/-!
## B. Global phase
-/

/-- Scaling a Jones vector scales its pure coherency matrix by the squared scalar modulus. -/
lemma coherency_scale_toMatrix (z : ℂ) (J : JonesVector) :
    (scale z J).coherency.toMatrix =
      (Complex.normSq z : ℂ) • J.coherency.toMatrix := by
  ext i j
  change (z * J.components i) * star (z * J.components j) =
    (Complex.normSq z : ℂ) * (J.components i * star (J.components j))
  rw [star_mul]
  change (z * J.components i) * (star (J.components j) * (starRingEnd ℂ) z) = _
  rw [← Complex.mul_conj]
  ring

/-- Scaling a Jones vector by a unit-modulus scalar leaves pure coherency unchanged. -/
lemma coherency_scale_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) (J : JonesVector) :
    (scale z J).coherency = J.coherency := by
  apply CoherencyMatrix.ext
  rw [coherency_scale_toMatrix, ← Complex.sq_norm, hz]
  norm_num

/-- A global Jones phase shift leaves pure coherency unchanged. -/
@[simp]
lemma coherency_phaseShift (phase : ℝ) (J : JonesVector) :
    (phaseShift phase J).coherency = J.coherency := by
  apply coherency_scale_of_norm_eq_one
  exact Complex.norm_exp_ofReal_mul_I phase

end JonesVector

/-!
## C. Jones transformations
-/

namespace JonesMatrix

/-- Taking pure coherency after a Jones action agrees with conjugating the input coherency by the
Jones matrix. -/
lemma act_coherency (M : JonesMatrix) (J : JonesVector) :
    (M.act J).coherency = J.coherency.map M.entries := by
  apply CoherencyMatrix.ext
  change Matrix.vecMulVec (M.entries *ᵥ J.components)
      (star (M.entries *ᵥ J.components)) =
    M.entries * Matrix.vecMulVec J.components (star J.components) * M.entriesᴴ
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← Matrix.star_mulVec]

end JonesMatrix

end

end Optics
