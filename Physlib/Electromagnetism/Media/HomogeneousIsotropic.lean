/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Electromagnetism.Basic
public import Physlib.Electromagnetism.Dynamics.Basic

/-!

# Homogeneous isotropic electromagnetic media

## i. Overview

This module defines the first material model used by the electromagnetic and optical APIs. A
`HomogeneousIsotropicMedium` has positive scalar permittivity and permeability. These constants
encode a linear, homogeneous, isotropic, nonconducting, and nondispersive model; the type is not a
model of conducting, dispersive, anisotropic, inhomogeneous, or nonlinear media. No conductivity
or complex or dispersive material loss is represented.
Here nonconducting means that the material has no constitutive Ohmic-current term; a later Maxwell
predicate may still carry an independently supplied free current.

The module also names the standard `E`, `D`, `B`, and `H` field roles, defines the isotropic
constitutive fields `D = ε E` and `H = B / μ`, and derives the medium wave speed, wave impedance,
and explicitly relative refractive indices. Maxwell equations are deliberately defined in a
separate module: constitutive equations alone are not Maxwell equations.

All constants, fields, speed values, and impedance values in this first model use raw real values
in one fixed, coherent rationalized unit convention. The Lean types do not encode physical
dimensions. The field-role abbreviations are definitionally equal to the existing raw field types;
they give semantic names, not type-level separation between `E`, `D`, `B`, and `H`. The fields `ε`
and `μ` are absolute material constants in that convention, not relative permittivity or relative
permeability.

## ii. Key results

- `HomogeneousIsotropicMedium`: positive scalar permittivity and permeability data.
- `HomogeneousIsotropicMedium.electricDisplacement`: the constitutive field `D = ε E`.
- `HomogeneousIsotropicMedium.magneticFieldStrength`: the constitutive field `H = B / μ`.
- `HomogeneousIsotropicMedium.IsConstitutive`: the separate four-field constitutive predicate.
- `HomogeneousIsotropicMedium.waveSpeed`: the speed `1 / √(ε μ)`.
- `HomogeneousIsotropicMedium.waveImpedance`: the impedance `√(μ / ε)`.
- `FreeSpace.toHomogeneousIsotropicMedium`: free space as a medium specialization.

## iii. Table of contents

- A. Electromagnetic field roles
- B. Homogeneous isotropic media
  - B.1. Positivity properties
- C. Constitutive fields
  - C.1. Constitutive relations
  - C.2. Linearity of constitutive relations
- D. Wave parameters
  - D.1. Wave speed
  - D.2. Wave impedance
  - D.3. Refractive indices
- E. Free-space specialization

## iv. References

-/

@[expose] public section

namespace Electromagnetism

/-!

## A. Electromagnetic field roles

-/

/-- An electric displacement field `D` has the same pointwise value type as an electric field.
Its distinct name records its role in macroscopic Maxwell equations. -/
abbrev ElectricDisplacementField (d : ℕ := 3) := ElectricField d

/-- A magnetic induction field `B` is the existing `MagneticField` viewed in its macroscopic
field role. -/
abbrev MagneticInductionField (d : ℕ := 3) := MagneticField d

/-- A magnetic field strength `H` has the same pointwise value type as magnetic induction. Its
distinct name records its role in macroscopic Maxwell equations. -/
abbrev MagneticFieldStrength (d : ℕ := 3) := MagneticField d

/-!

## B. Homogeneous isotropic media

-/

/-- A linear, homogeneous, isotropic, nonconducting, and nondispersive electromagnetic medium.
The constant scalar permittivity and permeability are required to be positive. -/
structure HomogeneousIsotropicMedium where
  /-- The scalar electric permittivity of the medium. -/
  ε : ℝ
  /-- The scalar magnetic permeability of the medium. -/
  μ : ℝ
  /-- The permittivity is strictly positive. -/
  ε_pos : 0 < ε
  /-- The permeability is strictly positive. -/
  μ_pos : 0 < μ

namespace HomogeneousIsotropicMedium

variable (𝓜 : HomogeneousIsotropicMedium)

/-!

### B.1. Positivity properties

-/

@[simp]
lemma ε_nonneg : 0 ≤ 𝓜.ε := le_of_lt 𝓜.ε_pos

@[simp]
lemma μ_nonneg : 0 ≤ 𝓜.μ := le_of_lt 𝓜.μ_pos

@[simp]
lemma ε_ne_zero : 𝓜.ε ≠ 0 := ne_of_gt 𝓜.ε_pos

@[simp]
lemma μ_ne_zero : 𝓜.μ ≠ 0 := ne_of_gt 𝓜.μ_pos

/-!

## C. Constitutive fields

-/

/-- The real-linear constitutive map from electric field to electric displacement, `D = ε E`. -/
def electricDisplacement : ElectricField d →ₗ[ℝ] ElectricDisplacementField d where
  toFun E := 𝓜.ε • E
  map_add' E F := by simp [smul_add]
  map_smul' a E := by simp [smul_smul, mul_comm]

/-- The real-linear constitutive map from magnetic induction to magnetic field strength,
`H = B / μ`. -/
noncomputable def magneticFieldStrength :
    MagneticInductionField d →ₗ[ℝ] MagneticFieldStrength d where
  toFun B := 𝓜.μ⁻¹ • B
  map_add' B C := by simp [smul_add]
  map_smul' a B := by simp [smul_smul, mul_comm]

@[simp]
lemma electricDisplacement_apply (E : ElectricField d) (t : Time) (x : Space d) :
    𝓜.electricDisplacement E t x = 𝓜.ε • E t x := rfl

@[simp]
lemma magneticFieldStrength_apply (B : MagneticInductionField d) (t : Time) (x : Space d) :
    𝓜.magneticFieldStrength B t x = 𝓜.μ⁻¹ • B t x := rfl

/-- The magnetic induction reconstructed from the constitutive field strength satisfies
`B = μ H`. -/
lemma permeability_smul_magneticFieldStrength (B : MagneticInductionField d) :
    𝓜.μ • 𝓜.magneticFieldStrength B = B := by
  ext t x i
  simp [magneticFieldStrength, smul_smul, 𝓜.μ_ne_zero]

/-!

### C.1. Constitutive relations

-/

/-- The four fields obey the homogeneous isotropic constitutive relations when `D = ε E` and
`B = μ H`. This predicate does not include any Maxwell equation. -/
def IsConstitutive (E : ElectricField d) (D : ElectricDisplacementField d)
    (B : MagneticInductionField d) (H : MagneticFieldStrength d) : Prop :=
  D = 𝓜.electricDisplacement E ∧ B = 𝓜.μ • H

/-- The constitutive fields constructed from any `E` and `B` obey the constitutive relations. -/
lemma isConstitutive_electricDisplacement_magneticFieldStrength
    (E : ElectricField d) (B : MagneticInductionField d) :
    𝓜.IsConstitutive E (𝓜.electricDisplacement E) B (𝓜.magneticFieldStrength B) :=
  ⟨rfl, (𝓜.permeability_smul_magneticFieldStrength B).symm⟩

/-!

### C.2. Linearity of constitutive relations

-/

namespace IsConstitutive

/-- Zero fields obey the homogeneous constitutive relations. -/
@[simp]
lemma zero : 𝓜.IsConstitutive (0 : ElectricField d) 0 0 0 := by
  simp [IsConstitutive]

/-- Constitutive fields are closed under addition in a fixed medium. -/
lemma add {E₁ E₂ : ElectricField d} {D₁ D₂ : ElectricDisplacementField d}
    {B₁ B₂ : MagneticInductionField d} {H₁ H₂ : MagneticFieldStrength d}
    (h₁ : 𝓜.IsConstitutive E₁ D₁ B₁ H₁)
    (h₂ : 𝓜.IsConstitutive E₂ D₂ B₂ H₂) :
    𝓜.IsConstitutive (E₁ + E₂) (D₁ + D₂) (B₁ + B₂) (H₁ + H₂) := by
  constructor
  · rw [h₁.1, h₂.1, map_add]
  · rw [h₁.2, h₂.2, smul_add]

/-- Constitutive fields are closed under real scalar multiplication. -/
lemma smul {E : ElectricField d} {D : ElectricDisplacementField d}
    {B : MagneticInductionField d} {H : MagneticFieldStrength d}
    (h : 𝓜.IsConstitutive E D B H) (a : ℝ) :
    𝓜.IsConstitutive (a • E) (a • D) (a • B) (a • H) := by
  constructor
  · rw [h.1, map_smul]
  · rw [h.2]
    simp [smul_smul, mul_comm]

end IsConstitutive

/-!

## D. Wave parameters

### D.1. Wave speed

-/

/-- The wave speed `1 / √(ε μ)` in the medium. -/
noncomputable def waveSpeed : ℝ := 1 / √(𝓜.ε * 𝓜.μ)

lemma waveSpeed_pos : 0 < 𝓜.waveSpeed := by
  exact div_pos zero_lt_one (Real.sqrt_pos_of_pos (mul_pos 𝓜.ε_pos 𝓜.μ_pos))

@[simp]
lemma waveSpeed_nonneg : 0 ≤ 𝓜.waveSpeed := le_of_lt 𝓜.waveSpeed_pos

@[simp]
lemma waveSpeed_ne_zero : 𝓜.waveSpeed ≠ 0 := ne_of_gt 𝓜.waveSpeed_pos

/-- The squared wave speed is `1 / (ε μ)`. -/
lemma waveSpeed_sq : 𝓜.waveSpeed ^ 2 = 1 / (𝓜.ε * 𝓜.μ) := by
  rw [waveSpeed, sq, div_eq_mul_inv]
  field_simp
  exact (Real.sqrt_eq_iff_eq_sq (mul_nonneg 𝓜.ε_nonneg 𝓜.μ_nonneg) (by positivity)).mp rfl

/-!

### D.2. Wave impedance

-/

/-- The wave impedance `√(μ / ε)` in the medium. -/
noncomputable def waveImpedance : ℝ := √(𝓜.μ / 𝓜.ε)

lemma waveImpedance_pos : 0 < 𝓜.waveImpedance := by
  exact Real.sqrt_pos.2 (div_pos 𝓜.μ_pos 𝓜.ε_pos)

@[simp]
lemma waveImpedance_nonneg : 0 ≤ 𝓜.waveImpedance := le_of_lt 𝓜.waveImpedance_pos

@[simp]
lemma waveImpedance_ne_zero : 𝓜.waveImpedance ≠ 0 := ne_of_gt 𝓜.waveImpedance_pos

/-- The squared wave impedance is `μ / ε`. -/
lemma waveImpedance_sq : 𝓜.waveImpedance ^ 2 = 𝓜.μ / 𝓜.ε := by
  exact Real.sq_sqrt (le_of_lt (div_pos 𝓜.μ_pos 𝓜.ε_pos))

/-- Permeability times wave speed equals wave impedance. -/
lemma μ_mul_waveSpeed : 𝓜.μ * 𝓜.waveSpeed = 𝓜.waveImpedance := by
  have hsq : (𝓜.μ * 𝓜.waveSpeed) ^ 2 = 𝓜.waveImpedance ^ 2 := by
    rw [mul_pow, 𝓜.waveSpeed_sq, 𝓜.waveImpedance_sq]
    field_simp
  have hp : 0 < 𝓜.μ * 𝓜.waveSpeed := mul_pos 𝓜.μ_pos 𝓜.waveSpeed_pos
  nlinarith [hp, 𝓜.waveImpedance_pos]

/-- Permittivity, wave speed, and wave impedance satisfy `ε v Z = 1`. -/
lemma ε_mul_waveSpeed_mul_waveImpedance :
    𝓜.ε * 𝓜.waveSpeed * 𝓜.waveImpedance = 1 := by
  rw [← 𝓜.μ_mul_waveSpeed]
  calc
    𝓜.ε * 𝓜.waveSpeed * (𝓜.μ * 𝓜.waveSpeed) =
        (𝓜.ε * 𝓜.μ) * 𝓜.waveSpeed ^ 2 := by ring
    _ = 1 := by rw [𝓜.waveSpeed_sq]; field_simp

/-!

### D.3. Refractive indices

-/

/-- The refractive index of `𝓜` relative to `reference`, defined as the reference wave speed
divided by the wave speed in `𝓜`. The medium `𝓜` is the target medium. -/
noncomputable def refractiveIndexRelativeTo (reference : HomogeneousIsotropicMedium) : ℝ :=
  reference.waveSpeed / 𝓜.waveSpeed

lemma refractiveIndexRelativeTo_pos (reference : HomogeneousIsotropicMedium) :
    0 < 𝓜.refractiveIndexRelativeTo reference :=
  div_pos reference.waveSpeed_pos 𝓜.waveSpeed_pos

@[simp]
lemma refractiveIndexRelativeTo_ne_zero (reference : HomogeneousIsotropicMedium) :
    𝓜.refractiveIndexRelativeTo reference ≠ 0 :=
  ne_of_gt (𝓜.refractiveIndexRelativeTo_pos reference)

/-- The squared relative refractive index is the target-to-reference ratio of `ε μ`. -/
lemma refractiveIndexRelativeTo_sq (reference : HomogeneousIsotropicMedium) :
    𝓜.refractiveIndexRelativeTo reference ^ 2 =
      (𝓜.ε * 𝓜.μ) / (reference.ε * reference.μ) := by
  rw [refractiveIndexRelativeTo, div_pow, reference.waveSpeed_sq, 𝓜.waveSpeed_sq]
  field_simp

@[simp]
lemma refractiveIndexRelativeTo_self : 𝓜.refractiveIndexRelativeTo 𝓜 = 1 := by
  exact div_self 𝓜.waveSpeed_ne_zero

end HomogeneousIsotropicMedium

/-!

## E. Free-space specialization

-/

namespace FreeSpace

/-- The homogeneous isotropic medium whose permittivity and permeability are those of free
space. -/
def toHomogeneousIsotropicMedium (𝓕 : FreeSpace) : HomogeneousIsotropicMedium where
  ε := 𝓕.ε₀
  μ := 𝓕.μ₀
  ε_pos := 𝓕.ε₀_pos
  μ_pos := 𝓕.μ₀_pos

@[simp]
lemma toHomogeneousIsotropicMedium_ε (𝓕 : FreeSpace) :
    𝓕.toHomogeneousIsotropicMedium.ε = 𝓕.ε₀ := rfl

@[simp]
lemma toHomogeneousIsotropicMedium_μ (𝓕 : FreeSpace) :
    𝓕.toHomogeneousIsotropicMedium.μ = 𝓕.μ₀ := rfl

/-- The wave speed of the medium specialization agrees with the existing free-space speed. -/
lemma toHomogeneousIsotropicMedium_waveSpeed (𝓕 : FreeSpace) :
    𝓕.toHomogeneousIsotropicMedium.waveSpeed = (𝓕.c : ℝ) := rfl

end FreeSpace

namespace HomogeneousIsotropicMedium

variable (𝓜 : HomogeneousIsotropicMedium)

/-- The refractive index of `𝓜` relative to the specified free space. -/
noncomputable def refractiveIndexRelativeToFreeSpace (𝓕 : FreeSpace) : ℝ :=
  𝓜.refractiveIndexRelativeTo 𝓕.toHomogeneousIsotropicMedium

lemma refractiveIndexRelativeToFreeSpace_eq (𝓕 : FreeSpace) :
    𝓜.refractiveIndexRelativeToFreeSpace 𝓕 = (𝓕.c : ℝ) / 𝓜.waveSpeed := rfl

lemma refractiveIndexRelativeToFreeSpace_pos (𝓕 : FreeSpace) :
    0 < 𝓜.refractiveIndexRelativeToFreeSpace 𝓕 :=
  𝓜.refractiveIndexRelativeTo_pos 𝓕.toHomogeneousIsotropicMedium

@[simp]
lemma refractiveIndexRelativeToFreeSpace_ne_zero (𝓕 : FreeSpace) :
    𝓜.refractiveIndexRelativeToFreeSpace 𝓕 ≠ 0 :=
  ne_of_gt (𝓜.refractiveIndexRelativeToFreeSpace_pos 𝓕)

/-- The free-space specialization has refractive index one relative to the same free space. -/
@[simp]
lemma refractiveIndexRelativeToFreeSpace_toHomogeneousIsotropicMedium (𝓕 : FreeSpace) :
    𝓕.toHomogeneousIsotropicMedium.refractiveIndexRelativeToFreeSpace 𝓕 = 1 :=
  refractiveIndexRelativeTo_self _

end HomogeneousIsotropicMedium

end Electromagnetism
