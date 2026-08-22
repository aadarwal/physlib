/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Electromagnetism.Media.HomogeneousIsotropic
public import Physlib.SpaceAndTime.Space.Derivatives.Curl

/-!

# Macroscopic Maxwell equations in three dimensions

## i. Overview

This module defines the differential macroscopic Maxwell equations for explicit electric field
`E`, electric displacement `D`, magnetic induction `B`, magnetic field strength `H`, free charge
density, and free current density. Material polarization and magnetization are represented through
`D` and `H`; they are not duplicated as bound-source terms on the right-hand sides.

The constitutive equations are deliberately separate. `IsMacroscopicMaxwell` states the four
medium-independent field equations, while
`HomogeneousIsotropicMedium.IsMacroscopicMaxwellSolution` connects them to the constitutive model
from `Electromagnetism.Media.HomogeneousIsotropic`.

Joint differentiability in time and space is part of the predicate. Physlib's differential
operators are totalized, so this regularity makes the linearity theorems honest rather than relying
on derivative identities outside their mathematical hypotheses.

## ii. Key results

- `IsMacroscopicMaxwell`: the four macroscopic field equations and their regularity.
- `IsMacroscopicMaxwell.add`: superposition with added free sources.
- `IsMacroscopicMaxwell.smul`: real scaling of fields and free sources.
- `IsSourceFreeMacroscopicMaxwell`: the specialization with vanishing free sources.
- `HomogeneousIsotropicMedium.IsMacroscopicMaxwellSolution`: Maxwell and constitutive equations
  for one fixed medium.

## iii. Table of contents

- A. Macroscopic Maxwell equations
  - A.1. Named projections
  - A.2. Linearity
- B. Source-free equations
- C. Homogeneous isotropic medium solutions

## iv. References

- J. D. Jackson, *Classical Electrodynamics*, third edition, section 6.6.

-/

@[expose] public section

namespace Electromagnetism
namespace ThreeDimension

open Space Time

/-!

## A. Macroscopic Maxwell equations

-/

/-- The differentiable, pointwise macroscopic Maxwell equations. The source arguments are free
charge and free current; bound material response is already represented by `D` and `H`. -/
def IsMacroscopicMaxwell (E : ElectricField) (D : ElectricDisplacementField)
    (B : MagneticInductionField) (H : MagneticFieldStrength)
    (ρFree : ChargeDensity) (JFree : CurrentDensity) : Prop :=
  Differentiable ℝ ↿E ∧
  Differentiable ℝ ↿D ∧
  Differentiable ℝ ↿B ∧
  Differentiable ℝ ↿H ∧
  (∀ t x, (∇ ⬝ D t) x = ρFree t x) ∧
  (∀ t x, (∇ ⬝ B t) x = 0) ∧
  (∀ t x, (∇ ⨯ H t) x = JFree t x + ∂ₜ (fun s => D s x) t) ∧
  ∀ t x, (∇ ⨯ E t) x = -∂ₜ (fun s => B s x) t

namespace IsMacroscopicMaxwell

variable {E E₁ E₂ : ElectricField} {D D₁ D₂ : ElectricDisplacementField}
  {B B₁ B₂ : MagneticInductionField} {H H₁ H₂ : MagneticFieldStrength}
  {ρFree ρFree₁ ρFree₂ : ChargeDensity} {JFree JFree₁ JFree₂ : CurrentDensity}

/-!

### A.1. Named projections

-/

/-- The electric field in a macroscopic Maxwell solution is jointly differentiable. -/
lemma electricField_differentiable (h : IsMacroscopicMaxwell E D B H ρFree JFree) :
    Differentiable ℝ ↿E := h.1

/-- The electric displacement in a macroscopic Maxwell solution is jointly differentiable. -/
lemma electricDisplacement_differentiable (h : IsMacroscopicMaxwell E D B H ρFree JFree) :
    Differentiable ℝ ↿D := h.2.1

/-- The magnetic induction in a macroscopic Maxwell solution is jointly differentiable. -/
lemma magneticInduction_differentiable (h : IsMacroscopicMaxwell E D B H ρFree JFree) :
    Differentiable ℝ ↿B := h.2.2.1

/-- The magnetic field strength in a macroscopic Maxwell solution is jointly differentiable. -/
lemma magneticFieldStrength_differentiable (h : IsMacroscopicMaxwell E D B H ρFree JFree) :
    Differentiable ℝ ↿H := h.2.2.2.1

/-- Gauss's law for electric displacement. -/
lemma gaussLawElectric (h : IsMacroscopicMaxwell E D B H ρFree JFree)
    (t : Time) (x : Space) : (∇ ⬝ D t) x = ρFree t x := h.2.2.2.2.1 t x

/-- Gauss's law for magnetic induction. -/
lemma gaussLawMagnetic (h : IsMacroscopicMaxwell E D B H ρFree JFree)
    (t : Time) (x : Space) : (∇ ⬝ B t) x = 0 := h.2.2.2.2.2.1 t x

/-- The Ampère--Maxwell law for magnetic field strength and electric displacement. -/
lemma ampereMaxwellLaw (h : IsMacroscopicMaxwell E D B H ρFree JFree)
    (t : Time) (x : Space) :
    (∇ ⨯ H t) x = JFree t x + ∂ₜ (fun s => D s x) t := h.2.2.2.2.2.2.1 t x

/-- Faraday's law for electric field and magnetic induction. -/
lemma faradayLaw (h : IsMacroscopicMaxwell E D B H ρFree JFree)
    (t : Time) (x : Space) :
    (∇ ⨯ E t) x = -∂ₜ (fun s => B s x) t := h.2.2.2.2.2.2.2 t x

/-!

### A.2. Linearity

-/

/-- The zero fields and zero free sources satisfy the macroscopic Maxwell equations. -/
@[simp]
lemma zero : IsMacroscopicMaxwell (0 : ElectricField) 0 0 0 0 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change Differentiable ℝ (fun _ : Time × Space => (0 : EuclideanSpace ℝ (Fin 3)))
    fun_prop
  · change Differentiable ℝ (fun _ : Time × Space => (0 : EuclideanSpace ℝ (Fin 3)))
    fun_prop
  · change Differentiable ℝ (fun _ : Time × Space => (0 : EuclideanSpace ℝ (Fin 3)))
    fun_prop
  · change Differentiable ℝ (fun _ : Time × Space => (0 : EuclideanSpace ℝ (Fin 3)))
    fun_prop
  all_goals simp

/-- Macroscopic Maxwell solutions are closed under addition, with their free sources added. -/
lemma add (h₁ : IsMacroscopicMaxwell E₁ D₁ B₁ H₁ ρFree₁ JFree₁)
    (h₂ : IsMacroscopicMaxwell E₂ D₂ B₂ H₂ ρFree₂ JFree₂) :
    IsMacroscopicMaxwell (E₁ + E₂) (D₁ + D₂) (B₁ + B₂) (H₁ + H₂)
      (ρFree₁ + ρFree₂) (JFree₁ + JFree₂) := by
  refine ⟨h₁.electricField_differentiable.add h₂.electricField_differentiable,
    h₁.electricDisplacement_differentiable.add h₂.electricDisplacement_differentiable,
    h₁.magneticInduction_differentiable.add h₂.magneticInduction_differentiable,
    h₁.magneticFieldStrength_differentiable.add h₂.magneticFieldStrength_differentiable,
    ?_, ?_, ?_, ?_⟩
  · intro t x
    rw [show (D₁ + D₂) t = D₁ t + D₂ t by rfl,
      Space.div_add (D₁ t) (D₂ t)
        (h₁.electricDisplacement_differentiable.comp (f := fun x => (t, x)) (by fun_prop))
        (h₂.electricDisplacement_differentiable.comp (f := fun x => (t, x)) (by fun_prop))]
    simp only [Pi.add_apply]
    rw [h₁.gaussLawElectric, h₂.gaussLawElectric]
  · intro t x
    rw [show (B₁ + B₂) t = B₁ t + B₂ t by rfl,
      Space.div_add (B₁ t) (B₂ t)
        (h₁.magneticInduction_differentiable.comp (f := fun x => (t, x)) (by fun_prop))
        (h₂.magneticInduction_differentiable.comp (f := fun x => (t, x)) (by fun_prop))]
    simp only [Pi.add_apply]
    rw [h₁.gaussLawMagnetic, h₂.gaussLawMagnetic, add_zero]
  · intro t x
    rw [show (H₁ + H₂) t = H₁ t + H₂ t by rfl,
      Space.curl_add (H₁ t) (H₂ t)
        (h₁.magneticFieldStrength_differentiable.comp (f := fun x => (t, x)) (by fun_prop))
        (h₂.magneticFieldStrength_differentiable.comp (f := fun x => (t, x)) (by fun_prop))]
    simp only [Pi.add_apply]
    rw [h₁.ampereMaxwellLaw, h₂.ampereMaxwellLaw, Time.deriv_add]
    · abel
    · exact h₁.electricDisplacement_differentiable.comp
        (f := fun s => (s, x)) (by fun_prop) |>.differentiableAt
    · exact h₂.electricDisplacement_differentiable.comp
        (f := fun s => (s, x)) (by fun_prop) |>.differentiableAt
  · intro t x
    rw [show (E₁ + E₂) t = E₁ t + E₂ t by rfl,
      Space.curl_add (E₁ t) (E₂ t)
        (h₁.electricField_differentiable.comp (f := fun x => (t, x)) (by fun_prop))
        (h₂.electricField_differentiable.comp (f := fun x => (t, x)) (by fun_prop))]
    simp only [Pi.add_apply]
    rw [h₁.faradayLaw, h₂.faradayLaw, Time.deriv_add]
    · abel
    · exact h₁.magneticInduction_differentiable.comp
        (f := fun s => (s, x)) (by fun_prop) |>.differentiableAt
    · exact h₂.magneticInduction_differentiable.comp
        (f := fun s => (s, x)) (by fun_prop) |>.differentiableAt

/-- Macroscopic Maxwell solutions are closed under real scalar multiplication. -/
lemma smul (h : IsMacroscopicMaxwell E D B H ρFree JFree) (a : ℝ) :
    IsMacroscopicMaxwell (a • E) (a • D) (a • B) (a • H) (a • ρFree) (a • JFree) := by
  refine ⟨h.electricField_differentiable.const_smul a,
    h.electricDisplacement_differentiable.const_smul a,
    h.magneticInduction_differentiable.const_smul a,
    h.magneticFieldStrength_differentiable.const_smul a, ?_, ?_, ?_, ?_⟩
  · intro t x
    rw [show (a • D) t = a • D t by rfl,
      Space.div_smul (D t) a
        (h.electricDisplacement_differentiable.comp (f := fun x => (t, x)) (by fun_prop))]
    simp only [Pi.smul_apply]
    rw [h.gaussLawElectric]
  · intro t x
    rw [show (a • B) t = a • B t by rfl,
      Space.div_smul (B t) a
        (h.magneticInduction_differentiable.comp (f := fun x => (t, x)) (by fun_prop))]
    simp only [Pi.smul_apply]
    rw [h.gaussLawMagnetic]
    simp
  · intro t x
    rw [show (a • H) t = a • H t by rfl,
      Space.curl_smul (H t) a
        (h.magneticFieldStrength_differentiable.comp (f := fun x => (t, x)) (by fun_prop))]
    simp only [Pi.smul_apply]
    rw [h.ampereMaxwellLaw, Time.deriv_smul]
    · simp only [smul_add]
    · exact h.electricDisplacement_differentiable.comp
        (f := fun s => (s, x)) (by fun_prop)
  · intro t x
    rw [show (a • E) t = a • E t by rfl,
      Space.curl_smul (E t) a
        (h.electricField_differentiable.comp (f := fun x => (t, x)) (by fun_prop))]
    simp only [Pi.smul_apply]
    rw [h.faradayLaw, Time.deriv_smul]
    · simp
    · exact h.magneticInduction_differentiable.comp
        (f := fun s => (s, x)) (by fun_prop)

end IsMacroscopicMaxwell

/-!

## B. Source-free equations

-/

/-- The macroscopic Maxwell equations with vanishing free charge and free current. Material
response may still be present through `D` and `H`. -/
def IsSourceFreeMacroscopicMaxwell (E : ElectricField) (D : ElectricDisplacementField)
    (B : MagneticInductionField) (H : MagneticFieldStrength) : Prop :=
  IsMacroscopicMaxwell E D B H 0 0

namespace IsSourceFreeMacroscopicMaxwell

variable {E : ElectricField} {D : ElectricDisplacementField}
  {B : MagneticInductionField} {H : MagneticFieldStrength}

/-- The zero fields satisfy the source-free macroscopic Maxwell equations. -/
@[simp]
lemma zero : IsSourceFreeMacroscopicMaxwell (0 : ElectricField) 0 0 0 :=
  IsMacroscopicMaxwell.zero

/-- Source-free macroscopic Maxwell solutions are closed under addition. -/
lemma add {E₁ E₂ : ElectricField} {D₁ D₂ : ElectricDisplacementField}
    {B₁ B₂ : MagneticInductionField} {H₁ H₂ : MagneticFieldStrength}
    (h₁ : IsSourceFreeMacroscopicMaxwell E₁ D₁ B₁ H₁)
    (h₂ : IsSourceFreeMacroscopicMaxwell E₂ D₂ B₂ H₂) :
    IsSourceFreeMacroscopicMaxwell (E₁ + E₂) (D₁ + D₂) (B₁ + B₂) (H₁ + H₂) := by
  simpa [IsSourceFreeMacroscopicMaxwell] using IsMacroscopicMaxwell.add h₁ h₂

/-- Source-free macroscopic Maxwell solutions are closed under real scalar multiplication. -/
lemma smul (h : IsSourceFreeMacroscopicMaxwell E D B H) (a : ℝ) :
    IsSourceFreeMacroscopicMaxwell (a • E) (a • D) (a • B) (a • H) := by
  simpa [IsSourceFreeMacroscopicMaxwell] using IsMacroscopicMaxwell.smul h a

/-- In a source-free solution, electric displacement is divergence-free. -/
lemma gaussLawElectric (h : IsSourceFreeMacroscopicMaxwell E D B H)
    (t : Time) (x : Space) : (∇ ⬝ D t) x = 0 :=
  IsMacroscopicMaxwell.gaussLawElectric h t x

/-- Gauss's law for magnetic induction is unchanged in a source-free solution. -/
lemma gaussLawMagnetic (h : IsSourceFreeMacroscopicMaxwell E D B H)
    (t : Time) (x : Space) : (∇ ⬝ B t) x = 0 :=
  IsMacroscopicMaxwell.gaussLawMagnetic h t x

/-- In a source-free solution, the curl of `H` equals the time derivative of `D`. -/
lemma ampereMaxwellLaw (h : IsSourceFreeMacroscopicMaxwell E D B H)
    (t : Time) (x : Space) : (∇ ⨯ H t) x = ∂ₜ (fun s => D s x) t := by
  simpa using IsMacroscopicMaxwell.ampereMaxwellLaw h t x

/-- Faraday's law is unchanged in a source-free solution. -/
lemma faradayLaw (h : IsSourceFreeMacroscopicMaxwell E D B H)
    (t : Time) (x : Space) : (∇ ⨯ E t) x = -∂ₜ (fun s => B s x) t :=
  IsMacroscopicMaxwell.faradayLaw h t x

end IsSourceFreeMacroscopicMaxwell

end ThreeDimension

/-!

## C. Homogeneous isotropic medium solutions

-/

namespace HomogeneousIsotropicMedium

/-- The macroscopic Maxwell equations together with the constitutive equations of the fixed
homogeneous isotropic medium `𝓜`. -/
def IsMacroscopicMaxwellSolution (𝓜 : HomogeneousIsotropicMedium) (E : ElectricField)
    (D : ElectricDisplacementField) (B : MagneticInductionField)
    (H : MagneticFieldStrength) (ρFree : ChargeDensity) (JFree : CurrentDensity) : Prop :=
  𝓜.IsConstitutive E D B H ∧
  ThreeDimension.IsMacroscopicMaxwell E D B H ρFree JFree

namespace IsMacroscopicMaxwellSolution

variable {𝓜 : HomogeneousIsotropicMedium}
  {E E₁ E₂ : ElectricField} {D D₁ D₂ : ElectricDisplacementField}
  {B B₁ B₂ : MagneticInductionField} {H H₁ H₂ : MagneticFieldStrength}
  {ρFree ρFree₁ ρFree₂ : ChargeDensity} {JFree JFree₁ JFree₂ : CurrentDensity}

/-- The fields in a medium solution satisfy its constitutive equations. -/
lemma constitutive (h : 𝓜.IsMacroscopicMaxwellSolution E D B H ρFree JFree) :
    𝓜.IsConstitutive E D B H := h.1

/-- A medium solution satisfies the medium-independent macroscopic Maxwell equations. -/
lemma maxwellEquations (h : 𝓜.IsMacroscopicMaxwellSolution E D B H ρFree JFree) :
    ThreeDimension.IsMacroscopicMaxwell E D B H ρFree JFree := h.2

/-- Canonical constitutive fields form a medium solution whenever they satisfy the macroscopic
Maxwell equations. -/
lemma of_maxwellEquations
    (h : ThreeDimension.IsMacroscopicMaxwell E (𝓜.electricDisplacement E) B
      (𝓜.magneticFieldStrength B) ρFree JFree) :
    𝓜.IsMacroscopicMaxwellSolution E (𝓜.electricDisplacement E) B
      (𝓜.magneticFieldStrength B) ρFree JFree :=
  ⟨𝓜.isConstitutive_electricDisplacement_magneticFieldStrength E B, h⟩

/-- The zero fields and zero free sources solve the fixed-medium equations. -/
@[simp]
lemma zero : 𝓜.IsMacroscopicMaxwellSolution (0 : ElectricField) 0 0 0 0 0 :=
  ⟨HomogeneousIsotropicMedium.IsConstitutive.zero 𝓜,
    ThreeDimension.IsMacroscopicMaxwell.zero⟩

/-- Solutions in one homogeneous isotropic medium are closed under addition. -/
lemma add (h₁ : 𝓜.IsMacroscopicMaxwellSolution E₁ D₁ B₁ H₁ ρFree₁ JFree₁)
    (h₂ : 𝓜.IsMacroscopicMaxwellSolution E₂ D₂ B₂ H₂ ρFree₂ JFree₂) :
    𝓜.IsMacroscopicMaxwellSolution (E₁ + E₂) (D₁ + D₂) (B₁ + B₂) (H₁ + H₂)
      (ρFree₁ + ρFree₂) (JFree₁ + JFree₂) :=
  ⟨HomogeneousIsotropicMedium.IsConstitutive.add 𝓜 h₁.1 h₂.1,
    ThreeDimension.IsMacroscopicMaxwell.add h₁.2 h₂.2⟩

/-- Solutions in one homogeneous isotropic medium are closed under real scalar multiplication. -/
lemma smul (h : 𝓜.IsMacroscopicMaxwellSolution E D B H ρFree JFree) (a : ℝ) :
    𝓜.IsMacroscopicMaxwellSolution (a • E) (a • D) (a • B) (a • H)
      (a • ρFree) (a • JFree) :=
  ⟨HomogeneousIsotropicMedium.IsConstitutive.smul 𝓜 h.1 a,
    ThreeDimension.IsMacroscopicMaxwell.smul h.2 a⟩

end IsMacroscopicMaxwellSolution
end HomogeneousIsotropicMedium
end Electromagnetism
