/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Mathematics.PauliMatrices.SelfAdjoint
public import Physlib.Optics.Polarization.Coherency

/-!
# Stokes polarization coordinates

## i. Overview

This file defines real Stokes coordinates for arbitrary self-adjoint `2 × 2` complex matrices and
identifies positive-semidefinite polarization coherency matrices with the physical Stokes cone.
The total-intensity coordinate is separated from the three polarization coordinates by the index
type `Fin 1 ⊕ Fin 3`.

The convention is fixed algebraically by
`S₀ = 2 c₀`, `S₁ = 2 c₃`, `S₂ = 2 c₁`, and `S₃ = 2 c₂`, where the `cᵢ` are the neutral Pauli
coefficients. Thus reconstruction is
`(S₀ σ₀ + S₁ σ₃ + S₂ σ₁ + S₃ σ₂) / 2`. The final coordinate is not assigned a right- or
left-circular name here; that physical naming also depends on observer and handedness conventions.

## ii. Key results

- `StokesVector`: four real Stokes coordinates with an `L²` norm.
- `selfAdjointStokesEquiv`: the real-linear Stokes coordinates of a self-adjoint matrix.
- `StokesVector.toSelfAdjoint`: reconstruction from arbitrary raw Stokes data.
- `StokesVector.IsPhysical`: the closed cone `‖polarization‖ ≤ intensity`.
- `PhysicalStokesVector`: raw Stokes data restricted to that cone.
- `coherencyStokesEquiv`: the equivalence between coherency matrices and physical Stokes data.

## iii. Table of contents

- A. Raw Stokes coordinates
- B. Reconstruction and observables
- C. The physical Stokes cone
- D. Physical Stokes data and coherency matrices

## iv. References

Every raw Stokes vector reconstructs a self-adjoint matrix, but only physical Stokes data
reconstructs a positive-semidefinite coherency matrix. The physical cone is not a vector subspace,
so its correspondence with coherency matrices is an ordinary equivalence, not a linear one.
-/

@[expose] public section

namespace Optics

open Matrix
open scoped ComplexOrder

noncomputable section

/-!

## A. Raw Stokes coordinates

-/

/-- The index type separating Stokes intensity from the three polarization coordinates. -/
abbrev StokesIndex := Fin 1 ⊕ Fin 3

/-- Four real Stokes coordinates equipped with their Euclidean structure. -/
abbrev StokesVector := EuclideanSpace ℝ StokesIndex

/-- The coordinate permutation from Stokes order `(S₀, S₁, S₂, S₃)` to the neutral Pauli order
`(c₀, c₁, c₂, c₃)`. -/
def stokesPauliIndexEquiv : StokesIndex ≃ (Fin 1 ⊕ Fin 3) where
  toFun
    | Sum.inl 0 => Sum.inl 0
    | Sum.inr 0 => Sum.inr 2
    | Sum.inr 1 => Sum.inr 0
    | Sum.inr 2 => Sum.inr 1
  invFun
    | Sum.inl 0 => Sum.inl 0
    | Sum.inr 0 => Sum.inr 1
    | Sum.inr 1 => Sum.inr 2
    | Sum.inr 2 => Sum.inr 0
  left_inv i := by rcases i with i | i <;> fin_cases i <;> rfl
  right_inv i := by rcases i with i | i <;> fin_cases i <;> rfl

/-- Convert neutral half-trace Pauli coordinates to doubled, reordered Stokes coordinates. -/
noncomputable def pauliStokesEquiv :
    ((Fin 1 ⊕ Fin 3) → ℝ) ≃ₗ[ℝ] StokesVector where
  toFun c := (WithLp.toLp 2 (fun μ => 2 * c (stokesPauliIndexEquiv μ)) : StokesVector)
  invFun S := fun μ => S (stokesPauliIndexEquiv.symm μ) / 2
  left_inv c := by
    funext μ
    change 2 * c (stokesPauliIndexEquiv (stokesPauliIndexEquiv.symm μ)) / 2 = c μ
    rw [stokesPauliIndexEquiv.apply_symm_apply]
    ring
  right_inv S := by
    ext μ
    change 2 * (S (stokesPauliIndexEquiv.symm (stokesPauliIndexEquiv μ)) / 2) = S μ
    rw [stokesPauliIndexEquiv.symm_apply_apply]
    ring
  map_add' c d := by
    ext μ
    change 2 * (c (stokesPauliIndexEquiv μ) + d (stokesPauliIndexEquiv μ)) =
      2 * c (stokesPauliIndexEquiv μ) + 2 * d (stokesPauliIndexEquiv μ)
    ring
  map_smul' r c := by
    ext μ
    change 2 * (r * c (stokesPauliIndexEquiv μ)) = r * (2 * c (stokesPauliIndexEquiv μ))
    ring

/-- Stokes coordinates are twice the corresponding reordered Pauli coordinates. -/
@[simp]
lemma pauliStokesEquiv_apply (c : (Fin 1 ⊕ Fin 3) → ℝ) (μ : StokesIndex) :
    pauliStokesEquiv c μ = 2 * c (stokesPauliIndexEquiv μ) := rfl

/-- Recovering Pauli coordinates from Stokes data divides the corresponding coordinate by two. -/
@[simp]
lemma pauliStokesEquiv_symm_apply (S : StokesVector) (μ : Fin 1 ⊕ Fin 3) :
    pauliStokesEquiv.symm S μ = S (stokesPauliIndexEquiv.symm μ) / 2 := rfl

/-- The real-linear equivalence taking a self-adjoint `2 × 2` matrix to its Stokes coordinates. -/
noncomputable def selfAdjointStokesEquiv :
    selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ) ≃ₗ[ℝ] StokesVector :=
  PauliMatrix.pauliCoeffEquiv.trans pauliStokesEquiv

/-- Stokes coordinates explicitly use the doubled and reordered Pauli coefficients. -/
lemma selfAdjointStokesEquiv_apply
    (A : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) (μ : StokesIndex) :
    selfAdjointStokesEquiv A μ =
      2 * PauliMatrix.pauliCoeff A (stokesPauliIndexEquiv μ) := by
  simp [selfAdjointStokesEquiv]

/-- The zeroth Stokes coordinate is twice the scalar Pauli coefficient. -/
@[simp]
lemma selfAdjointStokesEquiv_inl_zero
    (A : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) :
    selfAdjointStokesEquiv A (Sum.inl 0) = 2 * PauliMatrix.scalarCoeff A := by
  rw [selfAdjointStokesEquiv_apply]
  rfl

/-- The first polarization Stokes coordinate is twice the third spatial Pauli coefficient. -/
@[simp]
lemma selfAdjointStokesEquiv_inr_zero
    (A : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) :
    selfAdjointStokesEquiv A (Sum.inr 0) = 2 * PauliMatrix.vectorCoeff A 2 := by
  rw [selfAdjointStokesEquiv_apply]
  rfl

/-- The second polarization Stokes coordinate is twice the first spatial Pauli coefficient. -/
@[simp]
lemma selfAdjointStokesEquiv_inr_one
    (A : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) :
    selfAdjointStokesEquiv A (Sum.inr 1) = 2 * PauliMatrix.vectorCoeff A 0 := by
  rw [selfAdjointStokesEquiv_apply]
  rfl

/-- The third polarization Stokes coordinate is twice the second spatial Pauli coefficient. -/
@[simp]
lemma selfAdjointStokesEquiv_inr_two
    (A : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) :
    selfAdjointStokesEquiv A (Sum.inr 2) = 2 * PauliMatrix.vectorCoeff A 1 := by
  rw [selfAdjointStokesEquiv_apply]
  rfl

/-- Each Pauli basis matrix maps to twice the correspondingly ordered Stokes coordinate vector. -/
lemma selfAdjointStokesEquiv_pauliSelfAdjoint (μ : StokesIndex) :
    selfAdjointStokesEquiv
      (PauliMatrix.pauliSelfAdjoint (stokesPauliIndexEquiv μ)) =
      EuclideanSpace.single μ 2 := by
  ext ν
  rw [selfAdjointStokesEquiv_apply, PauliMatrix.pauliCoeff_pauliSelfAdjoint]
  simp only [PiLp.single_apply]
  by_cases h : μ = ν
  · subst h
    simp
  · have he : stokesPauliIndexEquiv μ ≠ stokesPauliIndexEquiv ν :=
      stokesPauliIndexEquiv.injective.ne h
    simp [he, Ne.symm h]

/-- The identity Pauli basis matrix occupies only the zeroth Stokes coordinate, with value two. -/
@[simp]
lemma selfAdjointStokesEquiv_pauliSelfAdjoint_inl_zero :
    selfAdjointStokesEquiv (PauliMatrix.pauliSelfAdjoint (Sum.inl 0)) =
      EuclideanSpace.single (Sum.inl 0) 2 := by
  simpa [stokesPauliIndexEquiv] using
    selfAdjointStokesEquiv_pauliSelfAdjoint (Sum.inl 0)

/-- The first Pauli basis matrix occupies the second polarization Stokes coordinate. -/
@[simp]
lemma selfAdjointStokesEquiv_pauliSelfAdjoint_inr_zero :
    selfAdjointStokesEquiv (PauliMatrix.pauliSelfAdjoint (Sum.inr 0)) =
      EuclideanSpace.single (Sum.inr 1) 2 := by
  simpa [stokesPauliIndexEquiv] using
    selfAdjointStokesEquiv_pauliSelfAdjoint (Sum.inr 1)

/-- The second Pauli basis matrix occupies the third polarization Stokes coordinate. -/
@[simp]
lemma selfAdjointStokesEquiv_pauliSelfAdjoint_inr_one :
    selfAdjointStokesEquiv (PauliMatrix.pauliSelfAdjoint (Sum.inr 1)) =
      EuclideanSpace.single (Sum.inr 2) 2 := by
  simpa [stokesPauliIndexEquiv] using
    selfAdjointStokesEquiv_pauliSelfAdjoint (Sum.inr 2)

/-- The third Pauli basis matrix occupies the first polarization Stokes coordinate. -/
@[simp]
lemma selfAdjointStokesEquiv_pauliSelfAdjoint_inr_two :
    selfAdjointStokesEquiv (PauliMatrix.pauliSelfAdjoint (Sum.inr 2)) =
      EuclideanSpace.single (Sum.inr 0) 2 := by
  simpa [stokesPauliIndexEquiv] using
    selfAdjointStokesEquiv_pauliSelfAdjoint (Sum.inr 0)

namespace StokesVector

/-!

## B. Reconstruction and observables

-/

/-- Reconstruct the self-adjoint `2 × 2` matrix represented by arbitrary raw Stokes data. -/
noncomputable def toSelfAdjoint (S : StokesVector) :
    selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ) :=
  selfAdjointStokesEquiv.symm S

/-- A reconstructed matrix has half the corresponding Stokes coordinate as its Pauli
coefficient. -/
@[simp]
lemma toSelfAdjoint_pauliCoeff (S : StokesVector) (μ : Fin 1 ⊕ Fin 3) :
    PauliMatrix.pauliCoeff S.toSelfAdjoint μ =
      S (stokesPauliIndexEquiv.symm μ) / 2 := by
  have h := congrArg (fun T : StokesVector => T (stokesPauliIndexEquiv.symm μ))
    (selfAdjointStokesEquiv.apply_symm_apply S)
  rw [selfAdjointStokesEquiv_apply] at h
  rw [stokesPauliIndexEquiv.apply_symm_apply] at h
  change 2 * PauliMatrix.pauliCoeff S.toSelfAdjoint μ =
    S (stokesPauliIndexEquiv.symm μ) at h
  calc
    PauliMatrix.pauliCoeff S.toSelfAdjoint μ =
        (2 * PauliMatrix.pauliCoeff S.toSelfAdjoint μ) / 2 := by
      ring
    _ = S (stokesPauliIndexEquiv.symm μ) / 2 := by rw [h]

/-- Reconstruction is the explicitly ordered Pauli expansion
`(S₀ σ₀ + S₁ σ₃ + S₂ σ₁ + S₃ σ₂) / 2`. -/
lemma toSelfAdjoint_eq_sum_pauli (S : StokesVector) :
    S.toSelfAdjoint =
      (S (Sum.inl 0) / 2) • PauliMatrix.pauliSelfAdjoint (Sum.inl 0) +
      (S (Sum.inr 1) / 2) • PauliMatrix.pauliSelfAdjoint (Sum.inr 0) +
      (S (Sum.inr 2) / 2) • PauliMatrix.pauliSelfAdjoint (Sum.inr 1) +
      (S (Sum.inr 0) / 2) • PauliMatrix.pauliSelfAdjoint (Sum.inr 2) := by
  rw [PauliMatrix.eq_sum_pauli S.toSelfAdjoint]
  simp only [Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero,
    Finset.sum_singleton, Fin.sum_univ_three]
  simp [stokesPauliIndexEquiv]
  abel

/-- The total-intensity coordinate of a Stokes vector. -/
def intensity (S : StokesVector) : ℝ :=
  S (Sum.inl 0)

/-- The three polarization coordinates of a Stokes vector. -/
def polarization (S : StokesVector) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 fun i => S (Sum.inr i)

/-- The polarization projection returns the three spatial Stokes coordinates. -/
@[simp]
lemma polarization_apply (S : StokesVector) (i : Fin 3) :
    S.polarization i = S (Sum.inr i) := rfl

/-- Construct Stokes data from its total intensity and three polarization coordinates. -/
def ofIntensityPolarization (s₀ : ℝ) (p : EuclideanSpace ℝ (Fin 3)) : StokesVector :=
  WithLp.toLp 2 (Sum.elim (fun _ => s₀) p)

/-- The intensity of Stokes data constructed from separate observables is the supplied intensity. -/
@[simp]
lemma intensity_ofIntensityPolarization (s₀ : ℝ) (p : EuclideanSpace ℝ (Fin 3)) :
    (ofIntensityPolarization s₀ p).intensity = s₀ := rfl

/-- The polarization of Stokes data constructed from separate observables is the supplied vector. -/
@[simp]
lemma polarization_ofIntensityPolarization (s₀ : ℝ) (p : EuclideanSpace ℝ (Fin 3)) :
    (ofIntensityPolarization s₀ p).polarization = p := by
  ext i
  rfl

/-- Reassembling a Stokes vector from its intensity and polarization returns the original data. -/
@[simp]
lemma ofIntensityPolarization_intensity_polarization (S : StokesVector) :
    ofIntensityPolarization S.intensity S.polarization = S := by
  ext μ
  rcases μ with μ | μ
  · fin_cases μ
    rfl
  · rfl

/-- The intensity of self-adjoint Stokes coordinates is twice the scalar Pauli coefficient. -/
@[simp]
lemma intensity_selfAdjointStokesEquiv
    (A : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) :
    (selfAdjointStokesEquiv A).intensity = 2 * PauliMatrix.scalarCoeff A :=
  selfAdjointStokesEquiv_inl_zero A

/-- Casting Stokes intensity to `ℂ` gives the trace of its reconstructed self-adjoint matrix. -/
lemma coe_intensity_eq_trace_toSelfAdjoint (S : StokesVector) :
    (S.intensity : ℂ) = Matrix.trace S.toSelfAdjoint.val := by
  have h := intensity_selfAdjointStokesEquiv S.toSelfAdjoint
  rw [StokesVector.toSelfAdjoint, selfAdjointStokesEquiv.apply_symm_apply] at h
  calc
    (S.intensity : ℂ) = ((2 * PauliMatrix.scalarCoeff S.toSelfAdjoint : ℝ) : ℂ) := by
      exact congrArg Complex.ofReal h
    _ = Matrix.trace S.toSelfAdjoint.val := by
      rw [PauliMatrix.trace_eq_two_mul_scalarCoeff]
      push_cast
      rfl

/-- The polarization norm of self-adjoint Stokes coordinates is twice the Pauli radius. -/
lemma polarization_norm_selfAdjointStokesEquiv
    (A : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) :
    ‖(selfAdjointStokesEquiv A).polarization‖ = 2 * PauliMatrix.pauliRadius A := by
  have hsq : ‖(selfAdjointStokesEquiv A).polarization‖ ^ 2 =
      (2 * PauliMatrix.pauliRadius A) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, mul_pow, PauliMatrix.pauliRadius_sq,
      Fin.sum_univ_three, Fin.sum_univ_three]
    simp only [polarization_apply, selfAdjointStokesEquiv_inr_zero,
      selfAdjointStokesEquiv_inr_one, selfAdjointStokesEquiv_inr_two]
    ring
  nlinarith [norm_nonneg (selfAdjointStokesEquiv A).polarization,
    PauliMatrix.pauliRadius_nonneg A]

/-- The scalar Pauli coefficient of a reconstructed Stokes vector is half its intensity. -/
@[simp]
lemma scalarCoeff_toSelfAdjoint (S : StokesVector) :
    PauliMatrix.scalarCoeff S.toSelfAdjoint = S.intensity / 2 := by
  rw [PauliMatrix.scalarCoeff, intensity]
  simp [stokesPauliIndexEquiv]

/-- The first spatial Pauli coefficient is half the second polarization Stokes coordinate. -/
@[simp]
lemma vectorCoeff_toSelfAdjoint_zero (S : StokesVector) :
    PauliMatrix.vectorCoeff S.toSelfAdjoint 0 = S (Sum.inr 1) / 2 := by
  simp [PauliMatrix.vectorCoeff, stokesPauliIndexEquiv]

/-- The second spatial Pauli coefficient is half the third polarization Stokes coordinate. -/
@[simp]
lemma vectorCoeff_toSelfAdjoint_one (S : StokesVector) :
    PauliMatrix.vectorCoeff S.toSelfAdjoint 1 = S (Sum.inr 2) / 2 := by
  simp [PauliMatrix.vectorCoeff, stokesPauliIndexEquiv]

/-- The third spatial Pauli coefficient is half the first polarization Stokes coordinate. -/
@[simp]
lemma vectorCoeff_toSelfAdjoint_two (S : StokesVector) :
    PauliMatrix.vectorCoeff S.toSelfAdjoint 2 = S (Sum.inr 0) / 2 := by
  simp [PauliMatrix.vectorCoeff, stokesPauliIndexEquiv]

/-- Entrywise Stokes reconstruction in the selected Pauli-positive convention. -/
lemma toSelfAdjoint_val_eq_matrix (S : StokesVector) :
    S.toSelfAdjoint.val =
      !![(((S (Sum.inl 0) + S (Sum.inr 0)) / 2 : ℝ) : ℂ),
          ((S (Sum.inr 1) : ℂ) - Complex.I * (S (Sum.inr 2) : ℂ)) / 2;
        ((S (Sum.inr 1) : ℂ) + Complex.I * (S (Sum.inr 2) : ℂ)) / 2,
          (((S (Sum.inl 0) - S (Sum.inr 0)) / 2 : ℝ) : ℂ)] := by
  rw [toSelfAdjoint_eq_sum_pauli]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [PauliMatrix.pauliSelfAdjoint, PauliMatrix.pauliMatrix] <;> ring

/-- The Pauli radius of a reconstructed Stokes vector is half the norm of its polarization
coordinates. -/
lemma pauliRadius_toSelfAdjoint (S : StokesVector) :
    PauliMatrix.pauliRadius S.toSelfAdjoint = ‖S.polarization‖ / 2 := by
  have hsq : PauliMatrix.pauliRadius S.toSelfAdjoint ^ 2 = (‖S.polarization‖ / 2) ^ 2 := by
    rw [PauliMatrix.pauliRadius_sq, div_pow, EuclideanSpace.real_norm_sq_eq,
      Fin.sum_univ_three, Fin.sum_univ_three]
    simp only [PauliMatrix.vectorCoeff]
    simp [stokesPauliIndexEquiv, polarization_apply]
    ring
  nlinarith [PauliMatrix.pauliRadius_nonneg S.toSelfAdjoint, norm_nonneg S.polarization]

/-- The determinant of a reconstructed Stokes matrix is one quarter of the difference between
intensity squared and the squared polarization norm. -/
lemma det_toSelfAdjoint (S : StokesVector) :
    Matrix.det S.toSelfAdjoint.val =
      (((S.intensity ^ 2 - ‖S.polarization‖ ^ 2) / 4 : ℝ) : ℂ) := by
  rw [PauliMatrix.det_eq_scalarCoeff_sq_sub_pauliRadius_sq,
    scalarCoeff_toSelfAdjoint, pauliRadius_toSelfAdjoint]
  push_cast
  ring

/-!

## C. The physical Stokes cone

-/

/-- A Stokes vector is physical when the polarization norm does not exceed total intensity. -/
def IsPhysical (S : StokesVector) : Prop :=
  ‖S.polarization‖ ≤ S.intensity

/-- Physical Stokes data has nonnegative intensity. -/
lemma IsPhysical.intensity_nonneg {S : StokesVector} (hS : S.IsPhysical) :
    0 ≤ S.intensity :=
  (norm_nonneg S.polarization).trans hS

/-- A physical Stokes vector with zero intensity is the zero vector. -/
lemma IsPhysical.eq_zero_of_intensity_eq_zero {S : StokesVector}
    (hS : S.IsPhysical) (h0 : S.intensity = 0) : S = 0 := by
  have hnorm : ‖S.polarization‖ = 0 :=
    le_antisymm (h0 ▸ hS) (norm_nonneg S.polarization)
  have hp : S.polarization = 0 := norm_eq_zero.mp hnorm
  ext μ
  rcases μ with μ | μ
  · fin_cases μ
    simpa [intensity] using h0
  · have hi := congrArg (fun P : EuclideanSpace ℝ (Fin 3) => P μ) hp
    simpa [polarization] using hi

/-- A reconstructed Stokes matrix is positive semidefinite exactly for physical Stokes data. -/
lemma toSelfAdjoint_posSemidef_iff (S : StokesVector) :
    S.toSelfAdjoint.val.PosSemidef ↔ S.IsPhysical := by
  rw [PauliMatrix.posSemidef_iff_pauliRadius_le_scalarCoeff,
    pauliRadius_toSelfAdjoint, scalarCoeff_toSelfAdjoint]
  constructor <;> intro h
  · exact (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).mp h
  · exact (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).mpr h

end StokesVector

/-- Extracting Stokes coordinates after raw self-adjoint reconstruction is the identity. -/
@[simp]
lemma selfAdjointStokesEquiv_toSelfAdjoint (S : StokesVector) :
    selfAdjointStokesEquiv S.toSelfAdjoint = S :=
  selfAdjointStokesEquiv.apply_symm_apply S

/-- Reconstructing after extracting Stokes coordinates is the identity on self-adjoint matrices. -/
@[simp]
lemma StokesVector.toSelfAdjoint_selfAdjointStokesEquiv
    (A : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) :
    (selfAdjointStokesEquiv A).toSelfAdjoint = A :=
  selfAdjointStokesEquiv.symm_apply_apply A

namespace StokesVector

/-- A standard Stokes-coordinate basis vector reconstructs as one half of its reordered Pauli
matrix. -/
lemma toSelfAdjoint_single (j : StokesIndex) :
    StokesVector.toSelfAdjoint (EuclideanSpace.single j 1 : StokesVector) =
      (1 / 2 : ℝ) • PauliMatrix.pauliSelfAdjoint (stokesPauliIndexEquiv j) := by
  apply selfAdjointStokesEquiv.injective
  rw [selfAdjointStokesEquiv_toSelfAdjoint, LinearEquiv.map_smul,
    selfAdjointStokesEquiv_pauliSelfAdjoint]
  ext i
  by_cases h : j = i
  · subst h
    simp
  · simp [h]

/-- Stokes data with zero polarization reconstructs as a scalar multiple of the identity matrix. -/
lemma toSelfAdjoint_ofIntensityPolarization_zero (s : ℝ) :
    (StokesVector.ofIntensityPolarization s 0).toSelfAdjoint.val =
      (s / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [StokesVector.toSelfAdjoint_val_eq_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [StokesVector.ofIntensityPolarization]

end StokesVector

/-- Positive semidefiniteness is exactly physicality of the corresponding Stokes coordinates. -/
lemma posSemidef_iff_selfAdjointStokesEquiv_isPhysical
    (A : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) :
    A.val.PosSemidef ↔ (selfAdjointStokesEquiv A).IsPhysical := by
  simpa [StokesVector.toSelfAdjoint] using
    StokesVector.toSelfAdjoint_posSemidef_iff (selfAdjointStokesEquiv A)

/-- Physical Stokes vectors, namely the closed cone `‖polarization‖ ≤ intensity`. -/
abbrev PhysicalStokesVector := {S : StokesVector // S.IsPhysical}

/-!

## D. Physical Stokes data and coherency matrices

-/

namespace PolarizationCoherency

/-- The physical Stokes vector of a polarization coherency matrix. -/
noncomputable def stokes (C : PolarizationCoherency) : StokesVector :=
  selfAdjointStokesEquiv C.toSelfAdjoint

/-- Reconstructing the self-adjoint matrix of extracted Stokes data recovers the coherency
matrix's self-adjoint form. -/
@[simp]
lemma stokes_toSelfAdjoint (C : PolarizationCoherency) :
    C.stokes.toSelfAdjoint = C.toSelfAdjoint := by
  simp [stokes, StokesVector.toSelfAdjoint]

/-- Stokes data extracted from a coherency matrix is physical. -/
lemma stokes_isPhysical (C : PolarizationCoherency) : C.stokes.IsPhysical := by
  rw [← StokesVector.toSelfAdjoint_posSemidef_iff]
  simpa using C.posSemidef

/-- Stokes intensity equals the real trace of the coherency matrix. -/
@[simp]
lemma stokes_intensity_eq_trace (C : PolarizationCoherency) :
    C.stokes.intensity = C.trace := by
  have hintensity : C.stokes.intensity =
      2 * PauliMatrix.scalarCoeff C.toSelfAdjoint := by
    change selfAdjointStokesEquiv C.toSelfAdjoint (Sum.inl 0) =
      2 * PauliMatrix.pauliCoeff C.toSelfAdjoint (Sum.inl 0)
    rw [selfAdjointStokesEquiv_apply]
    rfl
  apply Complex.ofReal_injective
  rw [hintensity, CoherencyMatrix.coe_trace, ← C.toSelfAdjoint_val,
    PauliMatrix.trace_eq_two_mul_scalarCoeff]
  push_cast
  rfl

end PolarizationCoherency

namespace PhysicalStokesVector

/-- Reconstruct a polarization coherency matrix from physical Stokes data. -/
noncomputable def coherency (S : PhysicalStokesVector) : PolarizationCoherency where
  toMatrix := S.val.toSelfAdjoint.val
  posSemidef := (StokesVector.toSelfAdjoint_posSemidef_iff S.val).mpr S.property

/-- The matrix reconstructed from physical Stokes data is its raw self-adjoint reconstruction. -/
@[simp]
lemma coherency_toMatrix (S : PhysicalStokesVector) :
    S.coherency.toMatrix = S.val.toSelfAdjoint.val := rfl

/-- Extracting Stokes data after coherency reconstruction recovers the physical Stokes vector. -/
@[simp]
lemma coherency_stokes (S : PhysicalStokesVector) : S.coherency.stokes = S.val := by
  change selfAdjointStokesEquiv S.coherency.toSelfAdjoint = S.val
  have hself : S.coherency.toSelfAdjoint = S.val.toSelfAdjoint := by
    apply Subtype.ext
    rfl
  rw [hself, StokesVector.toSelfAdjoint, selfAdjointStokesEquiv.apply_symm_apply]

end PhysicalStokesVector

namespace PolarizationCoherency

/-- Reconstructing coherency from its physical Stokes data recovers the coherency matrix. -/
@[simp]
lemma stokes_coherency (C : PolarizationCoherency) :
    PhysicalStokesVector.coherency
      (⟨C.stokes, C.stokes_isPhysical⟩ : PhysicalStokesVector) = C := by
  apply CoherencyMatrix.ext
  change (selfAdjointStokesEquiv.symm
    (selfAdjointStokesEquiv C.toSelfAdjoint)).val = C.toMatrix
  rw [selfAdjointStokesEquiv.symm_apply_apply]
  rfl

end PolarizationCoherency

/-- Polarization coherency matrices are equivalent to the physical Stokes cone. -/
noncomputable def coherencyStokesEquiv : PolarizationCoherency ≃ PhysicalStokesVector where
  toFun C := ⟨C.stokes, C.stokes_isPhysical⟩
  invFun S := S.coherency
  left_inv C := C.stokes_coherency
  right_inv S := Subtype.ext S.coherency_stokes

/-- Applying the coherency-to-Stokes equivalence after physical reconstruction is the identity. -/
@[simp]
lemma coherencyStokesEquiv_apply_coherency (S : PhysicalStokesVector) :
    coherencyStokesEquiv S.coherency = S :=
  coherencyStokesEquiv.apply_symm_apply S

/-- The Stokes vector underlying the coherency-to-Stokes equivalence is direct extraction. -/
@[simp]
lemma coherencyStokesEquiv_apply_val (C : PolarizationCoherency) :
    (coherencyStokesEquiv C).val = C.stokes := rfl

/-- The inverse coherency-to-Stokes equivalence is physical Stokes reconstruction. -/
lemma coherencyStokesEquiv_symm_apply (S : PhysicalStokesVector) :
    coherencyStokesEquiv.symm S = S.coherency := rfl

end

end Optics
