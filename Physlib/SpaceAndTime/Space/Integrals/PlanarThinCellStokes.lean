/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import Physlib.SpaceAndTime.Space.Derivatives.Curl
public import Physlib.SpaceAndTime.Space.Integrals.OrientedRectangle

/-!
# Oriented Stokes identities for planar thin cells

## i. Overview

This file derives the circulation identity for an affine rectangle in `Space` from Mathlib's
two-dimensional divergence theorem. The rectangle is parameterized by two spatial directions;
their ordered cross product fixes the surface orientation. The result is a classical identity for
one smooth ambient field. A discontinuous interface field must instead be treated on its two
half-rectangles, with the carrier traces retained as boundary terms.

No Maxwell equation, surface-current law, one-sided extension theorem, or thin-cell limit is
claimed here. In particular, this file does not provide the three-dimensional pillbox divergence
identity or the bridge from differential or weak Maxwell equations to the literal thin-cell
integral-Maxwell predicate.

## ii. Key results

- `integral2_inner_curl_planarRectangle`: curl flux equals the explicitly oriented circulation.

## iii. Table of contents

- A. Oriented rectangular Stokes identity

## iv. References

This is neutral integration infrastructure for the E4b Maxwell boundary derivation.
-/

@[expose] public section

open Matrix MeasureTheory
open scoped Interval

namespace Space

noncomputable section

/-!
## A. Oriented rectangular Stokes identity
-/

/-- The coordinate divergence used for the clockwise rectangle boundary is the curl flux through
the oriented surface `second × first`. -/
lemma planarRectangle_divergence_eq_inner_curl
    (field : Space → EuclideanSpace ℝ (Fin 3)) (center first second : Space)
    (p : ℝ × ℝ)
    (hf : DifferentiableAt ℝ field
      (planarRectanglePoint center first second p.1 p.2)) :
    fderiv ℝ
          (fun q : ℝ × ℝ ↦ -inner ℝ
            (field (planarRectanglePoint center first second q.1 q.2))
            (basis.repr second)) p (1, 0) +
        fderiv ℝ
          (fun q : ℝ × ℝ ↦ inner ℝ
            (field (planarRectanglePoint center first second q.1 q.2))
            (basis.repr first)) p (0, 1) =
      inner ℝ
        ((∇ ⨯ field) (planarRectanglePoint center first second p.1 p.2))
        (basis.repr second ⨯ₑ₃ basis.repr first) := by
  rw [fderiv_fun_neg, _root_.neg_apply,
    fderiv_inner_planarRectanglePoint_first field center first second
      (basis.repr second) p hf,
    fderiv_inner_planarRectanglePoint_second field center first second
      (basis.repr first) p hf,
    inner_curl_cross_eq field
      (planarRectanglePoint center first second p.1 p.2) second first hf]
  ring

/-- The curl flux through an affine rectangle equals its clockwise circulation.

The coordinate order is `(first, second)`, while the displayed surface orientation is
`second × first`. Consequently, the boundary runs along `first` on the upper edge, against
`first` on the lower edge, along `second` on the left edge, and against `second` on the right
edge. This is the orientation used by planar thin loops with `first` tangent to the carrier and
`second` pointing from the negative side to the positive side. -/
lemma integral2_inner_curl_planarRectangle
    (field : Space → EuclideanSpace ℝ (Fin 3))
    (center first second : Space) (a₁ a₂ b₁ b₂ : ℝ)
    (hfield : ContDiff ℝ 1 field) :
    (∫ u in a₁..b₁, ∫ v in a₂..b₂,
        inner ℝ
          ((∇ ⨯ field) (planarRectanglePoint center first second u v))
          (basis.repr second ⨯ₑ₃ basis.repr first)) =
      (((∫ u in a₁..b₁,
            inner ℝ (field (planarRectanglePoint center first second u b₂))
              (basis.repr first)) -
          ∫ u in a₁..b₁,
            inner ℝ (field (planarRectanglePoint center first second u a₂))
              (basis.repr first)) +
        ∫ v in a₂..b₂,
          inner ℝ (field (planarRectanglePoint center first second a₁ v))
            (basis.repr second)) -
      ∫ v in a₂..b₂,
        inner ℝ (field (planarRectanglePoint center first second b₁ v))
          (basis.repr second) := by
  let point : ℝ × ℝ → Space := fun p ↦
    planarRectanglePoint center first second p.1 p.2
  let normalPairing : ℝ × ℝ → ℝ := fun p ↦
    -inner ℝ (field (point p)) (basis.repr second)
  let tangentPairing : ℝ × ℝ → ℝ := fun p ↦
    inner ℝ (field (point p)) (basis.repr first)
  have hPoint : ContDiff ℝ 1 point := by
    dsimp only [point, planarRectanglePoint]
    fun_prop
  have hPullback : ContDiff ℝ 1 (fun p ↦ field (point p)) :=
    hfield.comp hPoint
  have hNormalPairing : ContDiff ℝ 1 normalPairing := by
    exact (hPullback.inner ℝ contDiff_const).neg
  have hTangentPairing : ContDiff ℝ 1 tangentPairing := by
    exact hPullback.inner ℝ contDiff_const
  have hDerivativeContinuous : Continuous fun p : ℝ × ℝ ↦
      fderiv ℝ normalPairing p (1, 0) +
        fderiv ℝ tangentPairing p (0, 1) := by
    fun_prop
  have hGreen := MeasureTheory.integral2_divergence_prod_of_hasFDerivAt
    normalPairing tangentPairing
    (fun p ↦ fderiv ℝ normalPairing p)
    (fun p ↦ fderiv ℝ tangentPairing p)
    a₁ a₂ b₁ b₂
    hNormalPairing.continuous.continuousOn
    hTangentPairing.continuous.continuousOn
    (fun p _ ↦ (hNormalPairing.differentiable (by norm_num) p).hasFDerivAt)
    (fun p _ ↦ (hTangentPairing.differentiable (by norm_num) p).hasFDerivAt)
    (hDerivativeContinuous.continuousOn.integrableOn_compact
      (isCompact_uIcc.prod isCompact_uIcc))
  calc
    (∫ u in a₁..b₁, ∫ v in a₂..b₂,
        inner ℝ
          ((∇ ⨯ field) (planarRectanglePoint center first second u v))
          (basis.repr second ⨯ₑ₃ basis.repr first)) =
        ∫ u in a₁..b₁, ∫ v in a₂..b₂,
          fderiv ℝ normalPairing (u, v) (1, 0) +
            fderiv ℝ tangentPairing (u, v) (0, 1) := by
      apply intervalIntegral.integral_congr
      intro u _
      apply intervalIntegral.integral_congr
      intro v _
      simpa only [normalPairing, tangentPairing, point] using
        (planarRectangle_divergence_eq_inner_curl field center first second (u, v)
          (hfield.differentiable (by norm_num)
            (planarRectanglePoint center first second u v))).symm
    _ = _ := by
      rw [hGreen]
      dsimp only [normalPairing, tangentPairing, point]
      rw [intervalIntegral.integral_neg, intervalIntegral.integral_neg]
      ring

end
end Space
