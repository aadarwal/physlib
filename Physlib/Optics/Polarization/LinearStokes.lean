/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Polarization.JonesStokes
public import Physlib.Optics.Polarization.Linear

/-!
# Stokes coordinates of linear Jones polarization

## i. Overview

This file connects the angle-parametrized linear Jones states to raw Stokes coordinates. A Jones
axis at angle `θ` maps to the unit equatorial Stokes direction
`(cos (2 • θ), sin (2 • θ), 0)`. The doubled angle is expressed intrinsically in
`Real.Angle`, without choosing a discontinuous real representative.

## ii. Key results

- `StokesVector.linearPolarizationDirection`: the equatorial unit direction at doubled angle.
- `StokesVector.norm_linearPolarizationDirection`: unit normalization.
- `JonesVector.stokes_linearPolarization`: the exact Jones-to-Stokes formula.

## iii. Table of contents

- A. Equatorial Stokes directions
- B. Jones-to-Stokes formulas

## iv. References

The formulas are derived from the imported Physlib Jones-to-Stokes convention.
-/

@[expose] public section

namespace Optics

open Matrix

noncomputable section

namespace StokesVector

/-!

## A. Equatorial Stokes directions
-/

/-- The unit equatorial Stokes direction corresponding to a linear Jones axis at angle `θ`. -/
def linearPolarizationDirection (θ : Real.Angle) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![Real.Angle.cos (2 • θ), Real.Angle.sin (2 • θ), 0]

/-- The first coordinate of the equatorial linear-polarization Stokes direction. -/
@[simp]
lemma linearPolarizationDirection_zero (θ : Real.Angle) :
    linearPolarizationDirection θ 0 = Real.Angle.cos (2 • θ) := rfl

/-- The second coordinate of the equatorial linear-polarization Stokes direction. -/
@[simp]
lemma linearPolarizationDirection_one (θ : Real.Angle) :
    linearPolarizationDirection θ 1 = Real.Angle.sin (2 • θ) := rfl

/-- The third coordinate of the equatorial linear-polarization Stokes direction is zero. -/
@[simp]
lemma linearPolarizationDirection_two (θ : Real.Angle) :
    linearPolarizationDirection θ 2 = 0 := rfl

/-- An equatorial linear-polarization Stokes direction has unit Euclidean norm. -/
@[simp]
lemma norm_linearPolarizationDirection (θ : Real.Angle) :
    ‖linearPolarizationDirection θ‖ = 1 := by
  have hsq : ‖linearPolarizationDirection θ‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
    simp [linearPolarizationDirection]
  nlinarith [norm_nonneg (linearPolarizationDirection θ)]

end StokesVector

namespace JonesVector

/-!

## B. Jones-to-Stokes formulas
-/

/-- A normalized linear Jones state has unit intensity and the doubled-angle equatorial Stokes
direction. -/
lemma stokes_linearPolarization (θ : Real.Angle) :
    (linearPolarization θ).stokes =
      StokesVector.ofIntensityPolarization 1
        (StokesVector.linearPolarizationDirection θ) := by
  ext μ
  rcases μ with μ | μ
  · fin_cases μ
    change (linearPolarization θ).stokes.intensity =
      (StokesVector.ofIntensityPolarization 1
        (StokesVector.linearPolarizationDirection θ)).intensity
    simp
  · fin_cases μ
    · simp [StokesVector.ofIntensityPolarization,
        StokesVector.linearPolarizationDirection]
      rw [two_nsmul, Real.Angle.cos_add]
    · simp [StokesVector.ofIntensityPolarization,
        StokesVector.linearPolarizationDirection, Real.Angle.sin_two_nsmul,
        nsmul_eq_mul]
      ring
    · simp [StokesVector.ofIntensityPolarization,
        StokesVector.linearPolarizationDirection]

/-- Real scaling of a normalized linear state's Stokes vector scales its intensity and equatorial
polarization direction together. -/
lemma smul_stokes_linearPolarization (q : ℝ) (θ : Real.Angle) :
    q • (linearPolarization θ).stokes =
      StokesVector.ofIntensityPolarization q
        (q • StokesVector.linearPolarizationDirection θ) := by
  rw [stokes_linearPolarization]
  ext μ
  rcases μ with μ | μ
  · fin_cases μ
    simp [StokesVector.ofIntensityPolarization]
  · simp [StokesVector.ofIntensityPolarization]

end JonesVector

end

end Optics
