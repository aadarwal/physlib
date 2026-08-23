/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Electromagnetism.ThreeDimension.MacroscopicMaxwellEquations

/-!

# Electromagnetic energy in three dimensions

## i. Overview

This module derives the local differential balance of electromagnetic energy from the
three-dimensional macroscopic Maxwell equations. The Poynting vector is defined as `E × H`; the
Maxwell equations first give its divergence as the sum of free-current work and two field-storage
terms. The constitutive equations of a fixed homogeneous isotropic medium then identify those
storage terms with the time derivative of a nonnegative energy density.

All fields here are instantaneous real fields. The results are pointwise and do not assert an
integrated conservation law, boundary flux, time average, irradiance, or modal power. The stored
energy formula uses the fixed positive, homogeneous, isotropic, nonconducting, and nondispersive
medium model. Free current remains an independently supplied source, while bound material response
is represented by `D` and `H`.

## ii. Key results

- `ThreeDimension.poyntingVector`: the instantaneous flux density `E × H`.
- `ThreeDimension.IsMacroscopicMaxwell.poyntingVector_div`: the sourced local work identity.
- `HomogeneousIsotropicMedium.energyDensity`: stored field energy density in a fixed medium.
- `HomogeneousIsotropicMedium.IsConstitutive.energyDensity_eq_inner`: the conventional
  `1 / 2 * (E · D + B · H)` form.
- `HomogeneousIsotropicMedium.IsConstitutive.energyDensity_timeDeriv`: the constitutive time
  derivative identity.
- `HomogeneousIsotropicMedium.IsMacroscopicMaxwellSolution.poyntingTheorem`: the local Poynting
  theorem.

## iii. Table of contents

- A. Poynting vector
- B. Sourced local work identity
- C. Stored energy in a fixed medium
  - C.1. Constitutive forms
- D. Local Poynting theorem

## iv. References

The results are derived from the macroscopic Maxwell and constitutive equations formalized in the
imported modules.

-/

@[expose] public section

namespace Electromagnetism

open Space Time Matrix

namespace ThreeDimension

/-!

## A. Poynting vector

-/

/-- The instantaneous electromagnetic energy-flux density `E × H`.

This definition fixes the cross-product order. By itself it does not assert Maxwell's equations,
an outward direction, a boundary flux, irradiance, or power. -/
def poyntingVector (E : ElectricField) (H : MagneticFieldStrength) :
    Time → Space → EuclideanSpace ℝ (Fin 3) := fun t x => E t x ⨯ₑ₃ H t x

/-!

## B. Sourced local work identity

-/

namespace IsMacroscopicMaxwell

variable {E : ElectricField} {D : ElectricDisplacementField}
  {B : MagneticInductionField} {H : MagneticFieldStrength}
  {ρFree : ChargeDensity} {JFree : CurrentDensity}

/-- Maxwell's curl laws express the divergence of `E × H` as free-current work and field-storage
terms. This is a local differential identity and uses no constitutive equation. -/
lemma poyntingVector_div (h : IsMacroscopicMaxwell E D B H ρFree JFree)
    (t : Time) (x : Space) :
    (∇ ⬝ poyntingVector E H t) x =
      - inner ℝ (E t x) (JFree t x) -
        inner ℝ (E t x) (∂ₜ (fun s => D s x) t) -
          inner ℝ (H t x) (∂ₜ (fun s => B s x) t) := by
  have hE : Differentiable ℝ (E t) :=
    h.electricField_differentiable.comp (f := fun y => (t, y)) (by fun_prop)
  have hH : Differentiable ℝ (H t) :=
    h.magneticFieldStrength_differentiable.comp (f := fun y => (t, y)) (by fun_prop)
  change (∇ ⬝ (fun y => E t y ⨯ₑ₃ H t y)) x = _
  rw [Space.div_cross_apply (E t) (H t) x (hE x) (hH x),
    h.faradayLaw t x, h.ampereMaxwellLaw t x]
  simp only [inner_neg_right, inner_add_right]
  ring

end IsMacroscopicMaxwell
end ThreeDimension

/-!

## C. Stored energy in a fixed medium

-/

namespace HomogeneousIsotropicMedium

/-- The instantaneous stored electromagnetic energy per unit volume in a fixed medium.

This is the energy density for the positive, homogeneous, isotropic, nonconducting, and
nondispersive constitutive model. It is not a definition for lossy or dispersive media. -/
noncomputable def energyDensity (𝓜 : HomogeneousIsotropicMedium)
    (E : ElectricField) (H : MagneticFieldStrength) : Time → Space → ℝ :=
  fun t x =>
    (1 / 2) *
      (𝓜.ε * inner ℝ (E t x) (E t x) + 𝓜.μ * inner ℝ (H t x) (H t x))

/-- The stored electromagnetic energy density in a fixed medium is nonnegative. -/
lemma energyDensity_nonneg (𝓜 : HomogeneousIsotropicMedium) (E : ElectricField)
    (H : MagneticFieldStrength) (t : Time) (x : Space) :
    0 ≤ 𝓜.energyDensity E H t x := by
  unfold energyDensity
  exact mul_nonneg (by norm_num)
    (add_nonneg (mul_nonneg 𝓜.ε_nonneg real_inner_self_nonneg)
      (mul_nonneg 𝓜.μ_nonneg real_inner_self_nonneg))

/-!

### C.1. Constitutive forms

-/

namespace IsConstitutive

variable {𝓜 : HomogeneousIsotropicMedium}
  {E : ElectricField} {D : ElectricDisplacementField}
  {B : MagneticInductionField} {H : MagneticFieldStrength}

/-- Under the constitutive equations, the stored energy density has the conventional symmetric
form `1 / 2 * (E · D + B · H)`. -/
lemma energyDensity_eq_inner (h : 𝓜.IsConstitutive E D B H)
    (t : Time) (x : Space) :
    𝓜.energyDensity E H t x =
      (1 / 2) *
        (inner ℝ (E t x) (D t x) + inner ℝ (B t x) (H t x)) := by
  rw [h.1, h.2]
  unfold energyDensity
  simp only [electricDisplacement_apply, Pi.smul_apply, inner_smul_left,
    inner_smul_right, conj_trivial]

/-- In a fixed medium, the time derivative of stored energy is the sum of the electric and
magnetic field-storage terms. Only pointwise time differentiability of `E` and `H` is needed. -/
lemma energyDensity_timeDeriv (h : 𝓜.IsConstitutive E D B H) (t : Time) (x : Space)
    (hE : DifferentiableAt ℝ (fun s => E s x) t)
    (hH : DifferentiableAt ℝ (fun s => H s x) t) :
    ∂ₜ (fun s => 𝓜.energyDensity E H s x) t =
      inner ℝ (E t x) (∂ₜ (fun s => D s x) t) +
        inner ℝ (H t x) (∂ₜ (fun s => B s x) t) := by
  rw [h.1, h.2]
  unfold energyDensity
  simp only [electricDisplacement_apply, Pi.smul_apply]
  have hEE : DifferentiableAt ℝ (fun s => inner ℝ (E s x) (E s x)) t := hE.inner ℝ hE
  have hHH : DifferentiableAt ℝ (fun s => inner ℝ (H s x) (H s x)) t := hH.inner ℝ hH
  have hεEE : DifferentiableAt ℝ (fun s => 𝓜.ε * inner ℝ (E s x) (E s x)) t :=
    hEE.const_mul 𝓜.ε
  have hμHH : DifferentiableAt ℝ (fun s => 𝓜.μ * inner ℝ (H s x) (H s x)) t :=
    hHH.const_mul 𝓜.μ
  have hsum : DifferentiableAt ℝ
      (fun s => 𝓜.ε * inner ℝ (E s x) (E s x) +
        𝓜.μ * inner ℝ (H s x) (H s x)) t :=
    hεEE.add hμHH
  rw [Time.deriv_eq, fderiv_const_mul hsum,
    fderiv_fun_add hεEE hμHH, fderiv_const_mul hEE, fderiv_const_mul hHH]
  simp only [_root_.smul_apply, _root_.add_apply, smul_eq_mul]
  rw [fderiv_inner_apply (𝕜 := ℝ) hE hE,
    fderiv_inner_apply (𝕜 := ℝ) hH hH,
    Time.deriv_eq, fderiv_fun_const_smul hE,
    Time.deriv_eq, fderiv_fun_const_smul hH]
  simp only [_root_.smul_apply, inner_smul_right]
  rw [real_inner_comm ((fderiv ℝ (fun s => E s x) t) 1) (E t x),
    real_inner_comm ((fderiv ℝ (fun s => H s x) t) 1) (H t x)]
  ring

end IsConstitutive

/-!

## D. Local Poynting theorem

-/

namespace IsMacroscopicMaxwellSolution

variable {𝓜 : HomogeneousIsotropicMedium}
  {E : ElectricField} {D : ElectricDisplacementField}
  {B : MagneticInductionField} {H : MagneticFieldStrength}
  {ρFree : ChargeDensity} {JFree : CurrentDensity}

/-- The local Poynting theorem in a fixed homogeneous isotropic medium: the increase in stored
field energy plus outward energy-flux divergence equals minus the work density delivered to free
current. This is a pointwise differential balance, not an integrated conservation theorem. -/
theorem poyntingTheorem
    (h : 𝓜.IsMacroscopicMaxwellSolution E D B H ρFree JFree)
    (t : Time) (x : Space) :
    ∂ₜ (fun s => 𝓜.energyDensity E H s x) t +
        (∇ ⬝ ThreeDimension.poyntingVector E H t) x =
      - inner ℝ (E t x) (JFree t x) := by
  have hE : DifferentiableAt ℝ (fun s => E s x) t :=
    (h.maxwellEquations.electricField_differentiable.comp
      (f := fun s => (s, x)) (by fun_prop)).differentiableAt
  have hH : DifferentiableAt ℝ (fun s => H s x) t :=
    (h.maxwellEquations.magneticFieldStrength_differentiable.comp
      (f := fun s => (s, x)) (by fun_prop)).differentiableAt
  rw [h.constitutive.energyDensity_timeDeriv t x hE hH,
    h.maxwellEquations.poyntingVector_div]
  ring

/-- At a point where the free current vanishes, the local increase in stored field energy is the
negative divergence of the Poynting vector. Free charge need not vanish for this conclusion. -/
lemma poyntingTheorem_of_freeCurrent_eq_zero
    (h : 𝓜.IsMacroscopicMaxwellSolution E D B H ρFree JFree)
    (t : Time) (x : Space) (hJ : JFree t x = 0) :
    ∂ₜ (fun s => 𝓜.energyDensity E H s x) t +
        (∇ ⬝ ThreeDimension.poyntingVector E H t) x = 0 := by
  rw [h.poyntingTheorem, hJ]
  simp

/-- A source-free fixed-medium Maxwell solution obeys the local electromagnetic energy
conservation equation. -/
lemma poyntingTheorem_sourceFree
    (h : 𝓜.IsMacroscopicMaxwellSolution E D B H 0 0)
    (t : Time) (x : Space) :
    ∂ₜ (fun s => 𝓜.energyDensity E H s x) t +
        (∇ ⬝ ThreeDimension.poyntingVector E H t) x = 0 :=
  h.poyntingTheorem_of_freeCurrent_eq_zero t x rfl

end IsMacroscopicMaxwellSolution
end HomogeneousIsotropicMedium
end Electromagnetism
