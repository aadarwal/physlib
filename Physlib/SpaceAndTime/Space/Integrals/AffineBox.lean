/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.SpaceAndTime.Space.Derivatives.Basic

/-!
# Affine boxes in Space

## i. Overview

This file defines the three-coordinate affine box parameterization used by oriented divergence and
thin-pillbox formulas. It proves the coordinate-direction derivative and the corresponding chain
rule for pairing a differentiable vector field with a fixed output direction.

The ordered spatial directions are not required to be orthogonal, normalized, or independent.
Integration and orientation laws belong to downstream modules.

## ii. Key results

- `affineBoxPoint`: the affine three-coordinate box parameterization.
- `fderiv_affineBoxCoordinatePoint`: its derivative in any coordinate direction.
- `fderiv_inner_affineBoxCoordinatePoint`: the chain rule for a fixed-direction field pairing.

## iii. Table of contents

- A. Affine box geometry
- B. Directional derivatives of field pairings

## iv. References

This is neutral geometry and calculus infrastructure for integral identities in `Space`.
-/

@[expose] public section

open Matrix

namespace Space

noncomputable section

/-!
## A. Affine box geometry
-/

/-- The point with affine coordinates `(u, v, w)` in the ordered spatial frame
`(first, second, third)` about `center`. -/
def affineBoxPoint (center first second third : Space)
    (u v w : ℝ) : Space :=
  center + u • first + v • second + w • third

/-- The affine box parameterization with its three coordinates bundled as a `Fin 3` function. -/
def affineBoxCoordinatePoint (center first second third : Space)
    (p : Fin 3 → ℝ) : Space :=
  affineBoxPoint center first second third (p 0) (p 1) (p 2)

/-- The derivative of the bundled affine box parameterization in coordinate `i` is the `i`th
ordered frame direction. -/
@[simp]
lemma fderiv_affineBoxCoordinatePoint (center first second third : Space)
    (q : Fin 3 → ℝ) (i : Fin 3) :
    fderiv ℝ (affineBoxCoordinatePoint center first second third) q
        (Pi.single i 1) = ![first, second, third] i := by
  unfold affineBoxCoordinatePoint affineBoxPoint
  rw [fderiv_fun_add (by fun_prop) (by fun_prop),
    fderiv_fun_add (by fun_prop) (by fun_prop),
    fderiv_fun_add (by fun_prop) (by fun_prop), fderiv_fun_const,
    fderiv_smul_const (by fun_prop), fderiv_smul_const (by fun_prop),
    fderiv_smul_const (by fun_prop)]
  have hId : DifferentiableAt ℝ (fun p : Fin 3 → ℝ ↦ p) q := by
    fun_prop
  fin_cases i <;> simp [fderiv_apply hId]

/-!
## B. Directional derivatives of field pairings
-/

/-- Differentiating a fixed-direction field pairing in box coordinate `i` differentiates the
field in the corresponding ordered spatial direction. -/
lemma fderiv_inner_affineBoxCoordinatePoint
    (field : Space → EuclideanSpace ℝ (Fin 3))
    (center first second third : Space)
    (direction : EuclideanSpace ℝ (Fin 3)) (q : Fin 3 → ℝ) (i : Fin 3)
    (hf : DifferentiableAt ℝ field
      (affineBoxCoordinatePoint center first second third q)) :
    fderiv ℝ
        (fun p : Fin 3 → ℝ ↦ inner ℝ
          (field (affineBoxCoordinatePoint center first second third p)) direction)
        q (Pi.single i 1) =
      inner ℝ
        (fderiv ℝ field (affineBoxCoordinatePoint center first second third q)
          (![first, second, third] i)) direction := by
  have hPoint : DifferentiableAt ℝ
      (affineBoxCoordinatePoint center first second third) q := by
    unfold affineBoxCoordinatePoint affineBoxPoint
    fun_prop
  have hPullback : DifferentiableAt ℝ
      (fun p : Fin 3 → ℝ ↦
        field (affineBoxCoordinatePoint center first second third p)) q :=
    hf.comp q hPoint
  have hDerivative :
      fderiv ℝ
          (fun p : Fin 3 → ℝ ↦
            field (affineBoxCoordinatePoint center first second third p)) q
          (Pi.single i 1) =
        fderiv ℝ field (affineBoxCoordinatePoint center first second third q)
          (![first, second, third] i) := by
    change (fderiv ℝ
      (field ∘ affineBoxCoordinatePoint center first second third) q)
        (Pi.single i 1) = _
    rw [fderiv_comp q hf hPoint, ContinuousLinearMap.comp_apply,
      fderiv_affineBoxCoordinatePoint]
  rw [fderiv_inner_apply (𝕜 := ℝ) hPullback
    (differentiableAt_const direction)]
  simp only [fderiv_fun_const, Pi.zero_apply, _root_.zero_apply,
    inner_zero_right, zero_add]
  rw [hDerivative]

end
end Space
