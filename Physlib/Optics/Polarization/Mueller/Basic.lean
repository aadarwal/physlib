/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Polarization.JonesStokes

/-!
# Deterministic Jones-induced Mueller transformations

## i. Overview

This file transports Jones-matrix congruence `C ↦ M * C * Mᴴ` through the real Stokes-coordinate
equivalence. The resulting real `4 × 4` matrix acts on raw Stokes data and is proved to agree with
both coherency transport and Jones-vector action.

`MuellerMatrix` is only a typed carrier for a real matrix in the selected Stokes basis. An arbitrary
value of this type is not thereby physically admissible or Jones-induced. The construction
`JonesMatrix.mueller` describes deterministic, nondepolarizing Jones optics, including singular
elements such as ideal polarizers. General depolarizing transformations require a later positive,
and where appropriate completely positive, map on coherency data.

Later modules derive the Pauli trace formula, functorial laws, and the normalized consequences of
algebraic Jones unitarity. Those consequences are not yet theorems about irradiance, Poynting
flux, or normalized modal power.

## ii. Main definitions

- `MuellerMatrix`: a wrapped real `4 × 4` matrix in the selected Stokes basis.
- `JonesMatrix.selfAdjointMap`: Jones congruence on arbitrary self-adjoint matrices.
- `JonesMatrix.stokesLinearMap`: the transported real-linear Stokes action.
- `JonesMatrix.mueller`: the real matrix representing that action.

## iii. Main results

- `JonesMatrix.mueller_coherency` and `JonesMatrix.mueller_jones`: the two commuting squares.
- `JonesMatrix.mueller_isPhysical`: preservation of the physical Stokes cone.
- `JonesMatrix.actPhysicalStokes`: the induced map on physical Stokes data.

## iv. Conventions

Rows of a Mueller matrix index output Stokes coordinates and columns index input coordinates. The
later trace-formula module uses `stokesPauliIndexEquiv` to supply the audited order
`(σ₀, σ₃, σ₁, σ₂)`. In particular, the third polarization coordinate's sign is already fixed by
the repository's Stokes convention; no extra sign is inserted in that formula.
-/

@[expose] public section

namespace Optics

open Matrix
open scoped ComplexConjugate

noncomputable section

/-!
## A. Raw Mueller matrices
-/

/-- A real `4 × 4` matrix acting on Stokes coordinates.

Rows index output coordinates and columns index input coordinates. This wrapper alone certifies
neither physical admissibility nor Jones inducibility. -/
@[ext]
structure MuellerMatrix where
  /-- The real matrix entries in the selected Stokes-coordinate basis. -/
  entries : Matrix StokesIndex StokesIndex ℝ

namespace MuellerMatrix

/-- Apply a raw Mueller matrix to Stokes coordinates. -/
def act (L : MuellerMatrix) (S : StokesVector) : StokesVector :=
  Matrix.toLpLin 2 2 L.entries S

/-- A Mueller action is ordinary matrix-vector multiplication in Stokes coordinates. -/
lemma act_apply (L : MuellerMatrix) (S : StokesVector) (i : StokesIndex) :
    L.act S i = ∑ j, L.entries i j * S j := by
  rfl

/-- The identity raw Mueller matrix. -/
def identity : MuellerMatrix :=
  ⟨1⟩

/-- Compose Mueller matrices, applying `K` first and then `L`. -/
def comp (L K : MuellerMatrix) : MuellerMatrix :=
  ⟨L.entries * K.entries⟩

/-- Scale every entry of a raw Mueller matrix by the same real scalar. -/
def scale (r : ℝ) (L : MuellerMatrix) : MuellerMatrix :=
  ⟨r • L.entries⟩

/-- The entries of a scaled Mueller matrix are scaled entrywise. -/
@[simp]
lemma scale_entries (r : ℝ) (L : MuellerMatrix) :
    (L.scale r).entries = r • L.entries := rfl

/-- The identity raw Mueller matrix acts identically on Stokes vectors. -/
@[simp]
lemma identity_act (S : StokesVector) : identity.act S = S := by
  simp [identity, act]

/-- Mueller composition agrees with sequential Stokes action. -/
lemma comp_act (L K : MuellerMatrix) (S : StokesVector) :
    (L.comp K).act S = L.act (K.act S) := by
  simp [comp, act, Matrix.toLpLin_mul_same]

/-- Scaling a Mueller matrix scales its Stokes action. -/
lemma scale_act (r : ℝ) (L : MuellerMatrix) (S : StokesVector) :
    (L.scale r).act S = r • L.act S := by
  simp [scale, act]

end MuellerMatrix

/-!
## B. Jones-induced Stokes action
-/

namespace JonesMatrix

/-- Jones congruence on arbitrary self-adjoint `2 × 2` complex matrices. -/
noncomputable def selfAdjointMap (M : JonesMatrix) :
    selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ) →ₗ[ℝ]
      selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ) :=
  Matrix.selfAdjointCongruence M.entries

/-- Jones congruence has underlying matrix `M * C * Mᴴ`. -/
@[simp]
lemma selfAdjointMap_apply_val (M : JonesMatrix)
    (C : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) :
    (M.selfAdjointMap C).val = M.entries * C.val * M.entriesᴴ := rfl

/-- The real-linear Stokes action induced by Jones congruence. -/
noncomputable def stokesLinearMap (M : JonesMatrix) : StokesVector →ₗ[ℝ] StokesVector :=
  selfAdjointStokesEquiv.conj M.selfAdjointMap

/-- The raw Mueller matrix induced by a Jones matrix. -/
noncomputable def mueller (M : JonesMatrix) : MuellerMatrix :=
  ⟨(Matrix.toLpLin 2 2).symm M.stokesLinearMap⟩

/-- The induced Mueller entries use the standard coordinate basis of Stokes space. -/
lemma mueller_entries_eq_toMatrix (M : JonesMatrix) :
    M.mueller.entries = LinearMap.toMatrix
      (EuclideanSpace.basisFun StokesIndex ℝ).toBasis
      (EuclideanSpace.basisFun StokesIndex ℝ).toBasis M.stokesLinearMap := rfl

/-- An induced Mueller entry is the corresponding output coordinate on an input basis vector. -/
lemma mueller_apply (M : JonesMatrix) (i j : StokesIndex) :
    M.mueller.entries i j = M.stokesLinearMap (EuclideanSpace.single j 1) i := by
  rw [mueller_entries_eq_toMatrix, LinearMap.toMatrix_apply]
  simp

/-- Induced Mueller action is the transported real-linear Stokes action. -/
@[simp]
lemma mueller_act (M : JonesMatrix) (S : StokesVector) :
    M.mueller.act S = M.stokesLinearMap S := by
  change Matrix.toLpLin 2 2 ((Matrix.toLpLin 2 2).symm M.stokesLinearMap) S = _
  rw [LinearEquiv.apply_symm_apply]

/-- Stokes action is Jones congruence transported through the Stokes equivalence. -/
lemma stokesLinearMap_apply (M : JonesMatrix) (S : StokesVector) :
    M.stokesLinearMap S = selfAdjointStokesEquiv (M.selfAdjointMap S.toSelfAdjoint) := rfl

/-- Reconstructing after induced Stokes action gives Jones congruence of the reconstructed input. -/
lemma mueller_act_toSelfAdjoint (M : JonesMatrix) (S : StokesVector) :
    (M.mueller.act S).toSelfAdjoint.val =
      M.entries * S.toSelfAdjoint.val * M.entriesᴴ := by
  rw [mueller_act, stokesLinearMap_apply, StokesVector.toSelfAdjoint,
    selfAdjointStokesEquiv.symm_apply_apply]
  rfl

/-- Mueller action commutes with coherency transport and Stokes extraction. -/
lemma mueller_coherency (M : JonesMatrix) (C : PolarizationCoherency) :
    M.mueller.act C.stokes = PolarizationCoherency.stokes (C.map M.entries) := by
  rw [mueller_act, stokesLinearMap_apply, PolarizationCoherency.stokes]
  apply congrArg selfAdjointStokesEquiv
  apply Subtype.ext
  simp

/-- Mueller action agrees with Jones action after Stokes extraction. -/
lemma mueller_jones (M : JonesMatrix) (J : JonesVector) :
    M.mueller.act J.stokes = (M.act J).stokes := by
  rw [JonesVector.stokes, mueller_coherency, ← M.act_coherency]
  rfl

/-!
## C. Physical Stokes data
-/

/-- Every Jones-induced Mueller action preserves the physical Stokes cone.

No unitarity or invertibility hypothesis is needed: congruence preserves positive
semidefiniteness, and singular Jones matrices remain deterministic nondepolarizing elements. -/
lemma mueller_isPhysical (M : JonesMatrix) {S : StokesVector} (hS : S.IsPhysical) :
    (M.mueller.act S).IsPhysical := by
  let P : PhysicalStokesVector := ⟨S, hS⟩
  have hmapped := PolarizationCoherency.stokes_isPhysical (P.coherency.map M.entries)
  rw [← M.mueller_coherency P.coherency, P.coherency_stokes] at hmapped
  exact hmapped

/-- The Jones-induced action on physical Stokes data. -/
noncomputable def actPhysicalStokes (M : JonesMatrix)
    (S : PhysicalStokesVector) : PhysicalStokesVector :=
  ⟨M.mueller.act S.val, M.mueller_isPhysical S.property⟩

/-- The raw Stokes vector underlying physical Jones-induced action. -/
@[simp]
lemma actPhysicalStokes_val (M : JonesMatrix) (S : PhysicalStokesVector) :
    (M.actPhysicalStokes S).val = M.mueller.act S.val := rfl
end JonesMatrix

end

end Optics
