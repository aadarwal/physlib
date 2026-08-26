/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.SpaceAndTime.Space.Derivatives.Basic

/-!
# Affine oriented rectangles in Space

## i. Overview

This file defines the two-coordinate affine rectangle parameterization used by planar Stokes and
divergence formulas. It proves the two coordinate-direction derivatives and the corresponding
chain rules for pairing a differentiable vector field with a fixed output direction.

The ordered spatial directions are not required to be orthogonal or normalized. Orientation and
integration laws belong to downstream modules.

## ii. Key results

- `planarRectanglePoint`: the affine two-coordinate rectangle parameterization.
- `fderiv_planarRectanglePoint_first`, `fderiv_planarRectanglePoint_second`: its coordinate
  derivatives.
- `fderiv_inner_planarRectanglePoint_first`, `fderiv_inner_planarRectanglePoint_second`: chain
  rules for fixed-direction field pairings.

## iii. Table of contents

- A. Affine rectangle geometry
- B. Directional derivatives of field pairings

## iv. References

This is neutral geometry and calculus infrastructure for integral identities in `Space`.
-/

@[expose] public section

namespace Space

noncomputable section

/-! ## A. Affine rectangle geometry -/

/-- The point with affine coordinates `(u, v)` in the ordered spatial frame `(first, second)`
about `center`. -/
def planarRectanglePoint (center first second : Space) (u v : ℝ) : Space :=
  center + u • first + v • second

/-- The derivative of the planar rectangle parameterization in its first coordinate. -/
@[simp]
lemma fderiv_planarRectanglePoint_first (center first second : Space) (p : ℝ × ℝ) :
    fderiv ℝ (fun q : ℝ × ℝ ↦ planarRectanglePoint center first second q.1 q.2) p (1, 0) =
      first := by
  unfold planarRectanglePoint
  rw [fderiv_fun_add (by fun_prop) (by fun_prop),
    fderiv_fun_add (by fun_prop) (by fun_prop), fderiv_fun_const,
    fderiv_smul_const (by fun_prop), fderiv_smul_const (by fun_prop)]
  rw [fderiv_fst, fderiv_snd]
  simp

/-- The derivative of the planar rectangle parameterization in its second coordinate. -/
@[simp]
lemma fderiv_planarRectanglePoint_second (center first second : Space) (p : ℝ × ℝ) :
    fderiv ℝ (fun q : ℝ × ℝ ↦ planarRectanglePoint center first second q.1 q.2) p (0, 1) =
      second := by
  unfold planarRectanglePoint
  rw [fderiv_fun_add (by fun_prop) (by fun_prop),
    fderiv_fun_add (by fun_prop) (by fun_prop), fderiv_fun_const,
    fderiv_smul_const (by fun_prop), fderiv_smul_const (by fun_prop)]
  rw [fderiv_fst, fderiv_snd]
  simp

/-! ## B. Directional derivatives of field pairings -/

/-- Differentiating a field pairing along the first rectangle coordinate differentiates the field
in the first spatial direction. -/
lemma fderiv_inner_planarRectanglePoint_first
    (field : Space → EuclideanSpace ℝ (Fin 3)) (center first second : Space)
    (direction : EuclideanSpace ℝ (Fin 3)) (p : ℝ × ℝ)
    (hf : DifferentiableAt ℝ field
      (planarRectanglePoint center first second p.1 p.2)) :
    fderiv ℝ
        (fun q : ℝ × ℝ ↦ inner ℝ
          (field (planarRectanglePoint center first second q.1 q.2)) direction)
        p (1, 0) =
      inner ℝ
        (fderiv ℝ field (planarRectanglePoint center first second p.1 p.2) first)
        direction := by
  have hPoint : DifferentiableAt ℝ
      (fun q : ℝ × ℝ ↦ planarRectanglePoint center first second q.1 q.2) p :=
    by
      change DifferentiableAt ℝ
        (fun q : ℝ × ℝ ↦ center + q.1 • first + q.2 • second) p
      fun_prop
  have hPullback : DifferentiableAt ℝ
      (fun q : ℝ × ℝ ↦ field (planarRectanglePoint center first second q.1 q.2)) p :=
    hf.comp p hPoint
  have hDerivative :
      fderiv ℝ
          (fun q : ℝ × ℝ ↦ field (planarRectanglePoint center first second q.1 q.2))
          p (1, 0) =
        fderiv ℝ field (planarRectanglePoint center first second p.1 p.2) first := by
    change (fderiv ℝ
      (field ∘ fun q : ℝ × ℝ ↦ planarRectanglePoint center first second q.1 q.2)
      p) (1, 0) = _
    rw [fderiv_comp p hf hPoint, ContinuousLinearMap.comp_apply,
      fderiv_planarRectanglePoint_first]
  rw [fderiv_inner_apply (𝕜 := ℝ) hPullback (differentiableAt_const direction)]
  simp only [fderiv_fun_const, Pi.zero_apply, _root_.zero_apply,
    inner_zero_right, zero_add]
  rw [hDerivative]

/-- Differentiating a field pairing along the second rectangle coordinate differentiates the
field in the second spatial direction. -/
lemma fderiv_inner_planarRectanglePoint_second
    (field : Space → EuclideanSpace ℝ (Fin 3)) (center first second : Space)
    (direction : EuclideanSpace ℝ (Fin 3)) (p : ℝ × ℝ)
    (hf : DifferentiableAt ℝ field
      (planarRectanglePoint center first second p.1 p.2)) :
    fderiv ℝ
        (fun q : ℝ × ℝ ↦ inner ℝ
          (field (planarRectanglePoint center first second q.1 q.2)) direction)
        p (0, 1) =
      inner ℝ
        (fderiv ℝ field (planarRectanglePoint center first second p.1 p.2) second)
        direction := by
  have hPoint : DifferentiableAt ℝ
      (fun q : ℝ × ℝ ↦ planarRectanglePoint center first second q.1 q.2) p :=
    by
      change DifferentiableAt ℝ
        (fun q : ℝ × ℝ ↦ center + q.1 • first + q.2 • second) p
      fun_prop
  have hPullback : DifferentiableAt ℝ
      (fun q : ℝ × ℝ ↦ field (planarRectanglePoint center first second q.1 q.2)) p :=
    hf.comp p hPoint
  have hDerivative :
      fderiv ℝ
          (fun q : ℝ × ℝ ↦ field (planarRectanglePoint center first second q.1 q.2))
          p (0, 1) =
        fderiv ℝ field (planarRectanglePoint center first second p.1 p.2) second := by
    change (fderiv ℝ
      (field ∘ fun q : ℝ × ℝ ↦ planarRectanglePoint center first second q.1 q.2)
      p) (0, 1) = _
    rw [fderiv_comp p hf hPoint, ContinuousLinearMap.comp_apply,
      fderiv_planarRectanglePoint_second]
  rw [fderiv_inner_apply (𝕜 := ℝ) hPullback (differentiableAt_const direction)]
  simp only [fderiv_fun_const, Pi.zero_apply, _root_.zero_apply,
    inner_zero_right, zero_add]
  rw [hDerivative]

end
end Space
