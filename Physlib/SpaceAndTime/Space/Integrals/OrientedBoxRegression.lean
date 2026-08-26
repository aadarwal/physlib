/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.SpaceAndTime.Space.Integrals.OrientedBox

/-!
# Affine oriented-box divergence regression

## i. Overview

This file checks `integral3_div_affineBox` on a genuinely skew frame. The ordered directions are
`(2, 1, 0)`, `(0, 1, 0)`, and `(0, 0, 1)`, so their signed volume is `2` and the second cofactor is
the oblique vector `(-1, 2, 0)`. The polynomial field is
`F(x) = (x₀², x₁, x₂)`.

On the unit coordinate box, the volume integral is computed independently as `8`. The three
opposing-face pairs are also computed independently and contribute `4`, `2`, and `2`. Thus the
fixture catches omitted Jacobian factors, reordered cofactors, and coordinate transposition before
the production divergence theorem is invoked.

## ii. Key results

- `volumeIntegral_exact`: the pulled-back divergence integral is exactly `8`.
- `firstFacePair_exact`, `secondFacePair_exact`, and `thirdFacePair_exact`: the three oriented
  face-pair fluxes are `4`, `2`, and `2`.
- `swappedVolumeIntegral_exact`: exchanging the first two frame directions changes the signed
  volume integral from `8` to `-8`.
- `production_and_exact`: the production theorem agrees with the independent exact computations.

## iii. Table of contents

- A. Skew polynomial fixture
- B. Independent volume and face computations
- C. Production-theorem sentinel

## iv. References

This is a Physlib-original adversarial regression for the neutral oriented-box calculus layer.
-/

@[expose] public section

open Matrix MeasureTheory
open scoped Interval

namespace Space
namespace AffineBoxDivergenceRegression

noncomputable section

/-! ## A. Skew polynomial fixture -/

/-- The origin used as the affine-box center. -/
def center : Space :=
  ⟨![(0 : ℝ), 0, 0]⟩

/-- The skew first frame direction `(2, 1, 0)`. -/
def first : Space :=
  ⟨![(2 : ℝ), 1, 0]⟩

/-- The second frame direction `(0, 1, 0)`. -/
def second : Space :=
  ⟨![(0 : ℝ), 1, 0]⟩

/-- The third frame direction `(0, 0, 1)`. -/
def third : Space :=
  ⟨![(0 : ℝ), 0, 1]⟩

/-- The first coordinate vector in the field's Euclidean codomain. -/
def outputZero : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![(1 : ℝ), 0, 0]

/-- The second coordinate vector in the field's Euclidean codomain. -/
def outputOne : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![(0 : ℝ), 1, 0]

/-- The third coordinate vector in the field's Euclidean codomain. -/
def outputTwo : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![(0 : ℝ), 0, 1]

/-- The polynomial field `F(x) = (x₀², x₁, x₂)` used by the regression. -/
def field (x : Space) : EuclideanSpace ℝ (Fin 3) :=
  (x 0) ^ 2 • outputZero + x 1 • outputOne + x 2 • outputTwo

/-- The regression field is continuously differentiable. -/
lemma field_contDiff : ContDiff ℝ 1 field := by
  unfold field
  fun_prop

/-- The skew frame has signed volume `2`. -/
lemma orientedVolume :
    inner ℝ (basis.repr first) (basis.repr second ⨯ₑ₃ basis.repr third) = 2 := by
  norm_num [first, second, third, crossProduct, PiLp.inner_apply,
    Fin.sum_univ_three, RCLike.inner_apply, basis_repr_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

/-- The divergence of the polynomial fixture is `2 x₀ + 2`. -/
lemma field_divergence (x : Space) : (∇ ⬝ field) x = 2 * x 0 + 2 := by
  norm_num [field, outputZero, outputOne, outputTwo, div,
    Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two]
  simp [deriv_component_sq]
  ring

/-- Coordinates of the skew affine-box parameterization. -/
lemma point_apply (u v w : ℝ) :
    affineBoxPoint center first second third u v w =
      ⟨![2 * u, u + v, w]⟩ := by
  ext i
  fin_cases i <;> (
    simp [affineBoxPoint, center, first, second, third] <;>
    ring)

/-- The pulled-back divergence integral over the unit coordinate box. -/
def volumeIntegral : ℝ :=
  ∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, ∫ w in (0 : ℝ)..1,
    (∇ ⬝ field) (affineBoxPoint center first second third u v w) *
      inner ℝ (basis.repr first) (basis.repr second ⨯ₑ₃ basis.repr third)

/-- The pulled-back divergence integral after exchanging the first two frame directions. -/
def swappedVolumeIntegral : ℝ :=
  ∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, ∫ w in (0 : ℝ)..1,
    (∇ ⬝ field) (affineBoxPoint center second first third u v w) *
      inner ℝ (basis.repr second) (basis.repr first ⨯ₑ₃ basis.repr third)

/-- The upper-minus-lower flux through the first-coordinate face pair. -/
def firstFacePair : ℝ :=
  ((∫ v in (0 : ℝ)..1, ∫ w in (0 : ℝ)..1,
        inner ℝ (field (affineBoxPoint center first second third 1 v w))
          (basis.repr second ⨯ₑ₃ basis.repr third)) -
    ∫ v in (0 : ℝ)..1, ∫ w in (0 : ℝ)..1,
        inner ℝ (field (affineBoxPoint center first second third 0 v w))
          (basis.repr second ⨯ₑ₃ basis.repr third))

/-- The upper-minus-lower flux through the second-coordinate face pair. -/
def secondFacePair : ℝ :=
  ((∫ u in (0 : ℝ)..1, ∫ w in (0 : ℝ)..1,
        inner ℝ (field (affineBoxPoint center first second third u 1 w))
          (basis.repr third ⨯ₑ₃ basis.repr first)) -
    ∫ u in (0 : ℝ)..1, ∫ w in (0 : ℝ)..1,
        inner ℝ (field (affineBoxPoint center first second third u 0 w))
          (basis.repr third ⨯ₑ₃ basis.repr first))

/-- The upper-minus-lower flux through the third-coordinate face pair. -/
def thirdFacePair : ℝ :=
  ((∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1,
        inner ℝ (field (affineBoxPoint center first second third u v 1))
          (basis.repr first ⨯ₑ₃ basis.repr second)) -
    ∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1,
        inner ℝ (field (affineBoxPoint center first second third u v 0))
          (basis.repr first ⨯ₑ₃ basis.repr second))

/-- The total flux through all six oriented faces of the skew box. -/
def boundaryFlux : ℝ :=
  firstFacePair + secondFacePair + thirdFacePair

/-! ## B. Independent volume and face computations -/

/-- The field pairs with the first cofactor as `(2u)²`. -/
lemma firstFaceDensity (u v w : ℝ) :
    inner ℝ (field (affineBoxPoint center first second third u v w))
        (basis.repr second ⨯ₑ₃ basis.repr third) =
      (2 * u) ^ 2 := by
  rw [point_apply]
  norm_num [field, outputZero, outputOne, outputTwo, second, third,
    crossProduct, PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply,
    basis_repr_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two]

/-- The field pairs with the oblique second cofactor as `-(2u)² + 2(u+v)`. -/
lemma secondFaceDensity (u v w : ℝ) :
    inner ℝ (field (affineBoxPoint center first second third u v w))
        (basis.repr third ⨯ₑ₃ basis.repr first) =
      -(2 * u) ^ 2 + 2 * (u + v) := by
  rw [point_apply]
  norm_num [field, outputZero, outputOne, outputTwo, first, third,
    crossProduct, PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply,
    basis_repr_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two]

/-- The field pairs with the third cofactor as `2w`. -/
lemma thirdFaceDensity (u v w : ℝ) :
    inner ℝ (field (affineBoxPoint center first second third u v w))
        (basis.repr first ⨯ₑ₃ basis.repr second) =
      2 * w := by
  rw [point_apply]
  norm_num [field, outputZero, outputOne, outputTwo, first, second,
    crossProduct, PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply,
    basis_repr_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two]

/-- Exchanging the first two frame directions negates the signed volume. -/
lemma swappedOrientedVolume :
    inner ℝ (basis.repr second) (basis.repr first ⨯ₑ₃ basis.repr third) = -2 := by
  norm_num [first, second, third, crossProduct, PiLp.inner_apply,
    Fin.sum_univ_three, RCLike.inner_apply, basis_repr_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

/-- Coordinates of the affine parameterization after exchanging the first two directions. -/
lemma swappedPoint_apply (u v w : ℝ) :
    affineBoxPoint center second first third u v w =
      ⟨![2 * v, u + v, w]⟩ := by
  ext i
  fin_cases i <;> (
    simp [affineBoxPoint, center, first, second, third] <;>
    ring)

/-- Direct integration gives signed volume integral `8`. -/
lemma volumeIntegral_exact : volumeIntegral = 8 := by
  unfold volumeIntegral
  simp_rw [field_divergence, point_apply, orientedVolume]
  simp only [Matrix.cons_val_zero]
  ring_nf
  norm_num

/-- Direct integration after the coordinate swap gives the opposite signed volume `-8`. -/
lemma swappedVolumeIntegral_exact : swappedVolumeIntegral = -8 := by
  unfold swappedVolumeIntegral
  simp_rw [field_divergence, swappedPoint_apply, swappedOrientedVolume]
  simp only [Matrix.cons_val_zero]
  ring_nf
  norm_num

/-- Direct face integration gives first-pair flux `4`. -/
lemma firstFacePair_exact : firstFacePair = 4 := by
  unfold firstFacePair
  simp_rw [firstFaceDensity]
  norm_num

/-- Direct face integration gives second-pair flux `2`. -/
lemma secondFacePair_exact : secondFacePair = 2 := by
  unfold secondFacePair
  simp_rw [secondFaceDensity]
  ring_nf
  norm_num
  rw [intervalIntegral.integral_sub
      (Continuous.intervalIntegrable (by fun_prop) 0 1)
      (Continuous.intervalIntegrable (by fun_prop) 0 1),
    intervalIntegral.integral_add
      (Continuous.intervalIntegrable (by fun_prop) 0 1)
      (Continuous.intervalIntegrable (by fun_prop) 0 1)]
  norm_num

/-- Direct face integration gives third-pair flux `2`. -/
lemma thirdFacePair_exact : thirdFacePair = 2 := by
  unfold thirdFacePair
  simp_rw [thirdFaceDensity]
  norm_num

/-- The independently evaluated six-face flux is `8`. -/
lemma boundaryFlux_exact : boundaryFlux = 8 := by
  rw [boundaryFlux, firstFacePair_exact, secondFacePair_exact, thirdFacePair_exact]
  norm_num

/-- The independent volume and boundary evaluations agree. -/
lemma independent_balance : volumeIntegral = boundaryFlux := by
  rw [volumeIntegral_exact, boundaryFlux_exact]

/-! ## C. Production-theorem sentinel -/

/-- The production divergence theorem agrees with both independent exact evaluations on the skew
fixture. -/
lemma production_and_exact :
    volumeIntegral = boundaryFlux ∧ volumeIntegral = 8 ∧ boundaryFlux = 8 := by
  refine ⟨?_, volumeIntegral_exact, boundaryFlux_exact⟩
  unfold volumeIntegral boundaryFlux firstFacePair secondFacePair thirdFacePair
  simpa using integral3_div_affineBox field center first second third
    0 0 0 1 1 1 (by norm_num) (by norm_num) (by norm_num) field_contDiff

end
end AffineBoxDivergenceRegression
end Space
