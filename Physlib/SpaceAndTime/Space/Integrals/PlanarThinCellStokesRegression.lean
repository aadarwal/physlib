/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.SpaceAndTime.Space.Integrals.PlanarThinCellStokes

/-!
# Oriented planar Stokes regression

## i. Overview

This file checks the orientation of `integral2_inner_curl_planarRectangle` on the coordinate
rectangle spanned by the first tangent direction and the positive third-coordinate normal. The
field `F(x) = x₂ e₁` has curl `e₂`, so pairing with `e₃ × e₁` gives `+1`. Reversing the ordered
surface frame gives `-1`.

The boundary integrals are evaluated independently. On the square `[-1, 1]²`, the upper and
lower tangent edges contribute `2` and `-2`, while both normal edges vanish. Thus the oriented
circulation and curl flux are both exactly `4`.

## ii. Key results

- `planarThinCellStokesRegression_density`: the selected orientation has curl density `+1`.
- `planarThinCellStokesRegression_oppositeDensity`: reversing the orientation gives `-1`.
- `planarThinCellStokesRegression_exact`: the production Stokes identity has value `4` on both
  sides.

## iii. Table of contents

- A. Coordinate fixture
- B. Orientation and integral sentinels

## iv. References

This is a Physlib-original adversarial regression for the oriented E4b calculus layer.
-/

@[expose] public section

open Matrix MeasureTheory
open scoped Interval

namespace Space

noncomputable section

/-! ## A. Coordinate fixture -/

/-- The origin used as the center of the regression rectangle. -/
def planarThinCellStokesRegressionCenter : Space :=
  ⟨![(0 : ℝ), 0, 0]⟩

/-- The positive first-coordinate tangent of the regression rectangle. -/
def planarThinCellStokesRegressionTangent : Space :=
  ⟨![(1 : ℝ), 0, 0]⟩

/-- The positive third-coordinate normal of the regression rectangle. -/
def planarThinCellStokesRegressionNormal : Space :=
  ⟨![(0 : ℝ), 0, 1]⟩

/-- The positive first-coordinate output vector of the regression field. -/
def planarThinCellStokesRegressionOutput : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![(1 : ℝ), 0, 0]

/-- The affine coordinate field `F(x) = x₂ e₁` used to pin the curl orientation. -/
def planarThinCellStokesRegressionField (x : Space) : EuclideanSpace ℝ (Fin 3) :=
  x 2 • planarThinCellStokesRegressionOutput

/-- The affine regression field is smooth. -/
lemma planarThinCellStokesRegressionField_contDiff :
    ContDiff ℝ 1 planarThinCellStokesRegressionField := by
  unfold planarThinCellStokesRegressionField
  exact (eval_contDiff (d := 3) (n := 1) 2).smul_const
    planarThinCellStokesRegressionOutput

/-- The curl flux through the oriented coordinate square `[-1, 1]²`. -/
def planarThinCellStokesRegressionCurlFlux : ℝ :=
  ∫ u in (-1 : ℝ)..1, ∫ v in (-1 : ℝ)..1,
    inner ℝ
      ((∇ ⨯ planarThinCellStokesRegressionField)
        (planarRectanglePoint planarThinCellStokesRegressionCenter
          planarThinCellStokesRegressionTangent
          planarThinCellStokesRegressionNormal u v))
      (basis.repr planarThinCellStokesRegressionNormal ⨯ₑ₃
        basis.repr planarThinCellStokesRegressionTangent)

/-- The clockwise boundary circulation of the coordinate square `[-1, 1]²`. -/
def planarThinCellStokesRegressionCirculation : ℝ :=
  ((∫ u in (-1 : ℝ)..1,
        inner ℝ
          (planarThinCellStokesRegressionField
            (planarRectanglePoint planarThinCellStokesRegressionCenter
              planarThinCellStokesRegressionTangent
              planarThinCellStokesRegressionNormal u 1))
          (basis.repr planarThinCellStokesRegressionTangent)) -
      ∫ u in (-1 : ℝ)..1,
        inner ℝ
          (planarThinCellStokesRegressionField
            (planarRectanglePoint planarThinCellStokesRegressionCenter
              planarThinCellStokesRegressionTangent
              planarThinCellStokesRegressionNormal u (-1)))
          (basis.repr planarThinCellStokesRegressionTangent)) +
    (∫ v in (-1 : ℝ)..1,
      inner ℝ
        (planarThinCellStokesRegressionField
          (planarRectanglePoint planarThinCellStokesRegressionCenter
            planarThinCellStokesRegressionTangent
            planarThinCellStokesRegressionNormal (-1) v))
        (basis.repr planarThinCellStokesRegressionNormal)) -
  (∫ v in (-1 : ℝ)..1,
    inner ℝ
      (planarThinCellStokesRegressionField
        (planarRectanglePoint planarThinCellStokesRegressionCenter
          planarThinCellStokesRegressionTangent
          planarThinCellStokesRegressionNormal 1 v))
      (basis.repr planarThinCellStokesRegressionNormal))

/-! ## B. Orientation and integral sentinels -/

/-- The curl density is `+1` when the surface orientation is normal cross tangent. -/
lemma planarThinCellStokesRegression_density (x : Space) :
    inner ℝ ((∇ ⨯ planarThinCellStokesRegressionField) x)
      (basis.repr planarThinCellStokesRegressionNormal ⨯ₑ₃
        basis.repr planarThinCellStokesRegressionTangent) = 1 := by
  simp [planarThinCellStokesRegressionField, planarThinCellStokesRegressionNormal,
    planarThinCellStokesRegressionTangent, planarThinCellStokesRegressionOutput,
    curl, deriv_component, crossProduct,
    PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, basis_repr_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

/-- Reversing the ordered surface frame reverses the curl-density sign. -/
lemma planarThinCellStokesRegression_oppositeDensity (x : Space) :
    inner ℝ ((∇ ⨯ planarThinCellStokesRegressionField) x)
      (basis.repr planarThinCellStokesRegressionTangent ⨯ₑ₃
        basis.repr planarThinCellStokesRegressionNormal) = -1 := by
  simp [planarThinCellStokesRegressionField, planarThinCellStokesRegressionNormal,
    planarThinCellStokesRegressionTangent, planarThinCellStokesRegressionOutput,
    curl, deriv_component, crossProduct,
    PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, basis_repr_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

/-- The explicitly oriented boundary circulation on the square `[-1, 1]²` is `4`. -/
lemma planarThinCellStokesRegression_circulation :
    planarThinCellStokesRegressionCirculation = 4 := by
  norm_num [planarThinCellStokesRegressionField, planarThinCellStokesRegressionCenter,
    planarThinCellStokesRegressionTangent, planarThinCellStokesRegressionNormal,
    planarThinCellStokesRegressionOutput, planarThinCellStokesRegressionCirculation,
    planarRectanglePoint, PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply,
    basis_repr_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

/-- The production Stokes identity and the independently evaluated boundary both have value `4`
on the coordinate fixture. -/
lemma planarThinCellStokesRegression_exact :
    planarThinCellStokesRegressionCurlFlux = 4 := by
  unfold planarThinCellStokesRegressionCurlFlux
  rw [integral2_inner_curl_planarRectangle
    planarThinCellStokesRegressionField
    planarThinCellStokesRegressionCenter
    planarThinCellStokesRegressionTangent
    planarThinCellStokesRegressionNormal (-1) (-1) 1 1
    planarThinCellStokesRegressionField_contDiff]
  have hCirculation := planarThinCellStokesRegression_circulation
  unfold planarThinCellStokesRegressionCirculation at hCirculation
  linear_combination hCirculation

end
end Space
