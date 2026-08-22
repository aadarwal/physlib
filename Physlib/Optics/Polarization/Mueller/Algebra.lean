/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Polarization.Mueller.Basic

/-!
# Algebra of Jones-induced Mueller matrices

This file proves that the transported Stokes action respects the identity, Jones cascades, and
common complex scaling. Scalar covariance is stated first for arbitrary scalars; global phase
invariance is its unit-modulus corollary.
-/

@[expose] public section

namespace Optics

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace JonesMatrix

/-!
## A. Identity, cascades, and common scalar phase
-/

/-- The identity Jones matrix induces the identity self-adjoint congruence. -/
@[simp]
lemma selfAdjointMap_identity : identity.selfAdjointMap = LinearMap.id := by
  rw [selfAdjointMap, identity, Matrix.selfAdjointCongruence_one]

/-- Jones composition induces composition of the self-adjoint congruence maps. -/
lemma selfAdjointMap_comp (M N : JonesMatrix) :
    (M.comp N).selfAdjointMap = M.selfAdjointMap.comp N.selfAdjointMap := by
  rw [selfAdjointMap, selfAdjointMap, selfAdjointMap, comp,
    Matrix.selfAdjointCongruence_mul]

/-- Common Jones scaling scales self-adjoint congruence by squared modulus. -/
lemma selfAdjointMap_scale (z : ℂ) (M : JonesMatrix) :
    (M.scale z).selfAdjointMap = Complex.normSq z • M.selfAdjointMap := by
  rw [selfAdjointMap, selfAdjointMap, scale_entries,
    Matrix.selfAdjointCongruence_smul]

/-- The identity Jones matrix induces the identity Stokes action. -/
@[simp]
lemma stokesLinearMap_identity : identity.stokesLinearMap = LinearMap.id := by
  rw [stokesLinearMap, selfAdjointMap_identity]
  ext S
  simp

/-- Jones composition induces composition of the transported Stokes actions. -/
lemma stokesLinearMap_comp (M N : JonesMatrix) :
    (M.comp N).stokesLinearMap = M.stokesLinearMap.comp N.stokesLinearMap := by
  rw [stokesLinearMap, selfAdjointMap_comp, LinearEquiv.conj_comp]
  rfl

/-- Common Jones scaling scales the transported Stokes action by squared modulus. -/
lemma stokesLinearMap_scale (z : ℂ) (M : JonesMatrix) :
    (M.scale z).stokesLinearMap = Complex.normSq z • M.stokesLinearMap := by
  rw [stokesLinearMap, selfAdjointMap_scale]
  apply LinearMap.ext
  intro S
  simp [stokesLinearMap]

/-- The identity Jones matrix induces the identity Mueller matrix. -/
@[simp]
lemma mueller_identity : identity.mueller = MuellerMatrix.identity := by
  apply MuellerMatrix.ext
  rw [mueller, stokesLinearMap_identity, Matrix.toLpLin_symm_id]
  rfl

/-- Jones composition induces composition of the corresponding Mueller matrices. -/
lemma mueller_comp (M N : JonesMatrix) :
    (M.comp N).mueller = M.mueller.comp N.mueller := by
  apply MuellerMatrix.ext
  rw [mueller, stokesLinearMap_comp, Matrix.toLpLin_symm_comp]
  rfl

/-- Common Jones scaling scales the induced Mueller matrix by squared modulus. -/
lemma mueller_scale (z : ℂ) (M : JonesMatrix) :
    (M.scale z).mueller = M.mueller.scale (Complex.normSq z) := by
  apply MuellerMatrix.ext
  rw [mueller, stokesLinearMap_scale]
  exact LinearEquiv.map_smul (Matrix.toLpLin 2 2).symm
    (Complex.normSq z) M.stokesLinearMap

/-- A common unit-modulus Jones-matrix phase does not change its induced Mueller matrix. -/
lemma mueller_scale_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) (M : JonesMatrix) :
    (M.scale z).mueller = M.mueller := by
  rw [mueller_scale, ← Complex.sq_norm, hz]
  apply MuellerMatrix.ext
  simp [MuellerMatrix.scale]

end JonesMatrix

end

end Optics
