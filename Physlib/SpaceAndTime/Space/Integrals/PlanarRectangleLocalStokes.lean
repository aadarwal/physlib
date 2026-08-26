/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.SpaceAndTime.Space.Integrals.PlanarThinCellStokes

/-!
# Local-regularity Stokes identities for affine rectangles

## i. Overview

This file gives the oriented affine-rectangle Stokes identity under hypotheses local to the
parameterized rectangle. It requires continuity and differentiability only on that compact
rectangle, together with integrability of the pulled-back curl density. This is the form needed
when two independently extended fields are used on the two halves of an interface-crossing thin
cell.

The theorem does not construct a closed-side extension from one-sided trace data. A consumer must
supply a field defined on the carrier as well as on its selected half-rectangle, and prove the
local regularity record for that extension.

## ii. Key results

- `PlanarRectangleStokesRegularity`: local continuity, differentiability, and curl-integrability.
- `PlanarRectangleStokesRegularity.of_differentiable`: a global differentiability convenience
  constructor retaining an explicit curl-integrability premise.
- `integral2_inner_curl_planarRectangle_of_localRegularity`: oriented Stokes under the local
  regularity record.

## iii. Table of contents

- A. Local rectangle regularity
- B. Local oriented Stokes theorem

## iv. References

This is neutral calculus infrastructure for the E4b half-rectangle construction.
-/

@[expose] public section

open Matrix MeasureTheory
open scoped Interval

namespace Space

noncomputable section

/-!
## A. Local rectangle regularity
-/

/-- Regularity of one ambient vector field on one parameterized affine rectangle.

Differentiability is required on the closed parameter rectangle so the displayed curl density
agrees pointwise with the coordinate derivatives used in the integral. No behavior away from the
rectangle is constrained. -/
structure PlanarRectangleStokesRegularity
    (field : Space → EuclideanSpace ℝ (Fin 3))
    (center first second : Space) (a₁ a₂ b₁ b₂ : ℝ) : Prop where
  /-- The pulled-back field is continuous on the unordered closed parameter rectangle. -/
  continuousOn : ContinuousOn
    (fun p : ℝ × ℝ ↦ field (planarRectanglePoint center first second p.1 p.2))
    ([[a₁, b₁]] ×ˢ [[a₂, b₂]])
  /-- The ambient field is differentiable at every point of the closed rectangle. -/
  differentiableAt : ∀ p ∈ ([[a₁, b₁]] ×ˢ [[a₂, b₂]]),
    DifferentiableAt ℝ field (planarRectanglePoint center first second p.1 p.2)
  /-- The oriented curl-density pullback is integrable on the parameter rectangle. -/
  curlIntegrable : IntegrableOn
    (fun p : ℝ × ℝ ↦ inner ℝ
      ((∇ ⨯ field) (planarRectanglePoint center first second p.1 p.2))
      (basis.repr second ⨯ₑ₃ basis.repr first))
    ([[a₁, b₁]] ×ˢ [[a₂, b₂]])

namespace PlanarRectangleStokesRegularity

/-- A globally differentiable field supplies the local continuity and differentiability fields;
curl integrability on the selected rectangle remains explicit. -/
lemma of_differentiable
    (field : Space → EuclideanSpace ℝ (Fin 3))
    (center first second : Space) (a₁ a₂ b₁ b₂ : ℝ)
    (hfield : Differentiable ℝ field)
    (hcurl : IntegrableOn
      (fun p : ℝ × ℝ ↦ inner ℝ
        ((∇ ⨯ field) (planarRectanglePoint center first second p.1 p.2))
        (basis.repr second ⨯ₑ₃ basis.repr first))
      ([[a₁, b₁]] ×ˢ [[a₂, b₂]])) :
    PlanarRectangleStokesRegularity
      field center first second a₁ a₂ b₁ b₂ where
  continuousOn := by
    exact (hfield.continuous.comp
      (by
        change Continuous fun p : ℝ × ℝ ↦
          center + p.1 • first + p.2 • second
        fun_prop)).continuousOn
  differentiableAt := fun p _ ↦ hfield (planarRectanglePoint center first second p.1 p.2)
  curlIntegrable := hcurl

end PlanarRectangleStokesRegularity

/-!
## B. Local oriented Stokes theorem
-/

/-- The curl flux through an affine rectangle equals its clockwise circulation under regularity
confined to that rectangle.

The coordinate order is `(first, second)` and the displayed surface orientation is
`second × first`, exactly as in `integral2_inner_curl_planarRectangle`. -/
lemma integral2_inner_curl_planarRectangle_of_localRegularity
    (field : Space → EuclideanSpace ℝ (Fin 3))
    (center first second : Space) (a₁ a₂ b₁ b₂ : ℝ)
    (regularity : PlanarRectangleStokesRegularity
      field center first second a₁ a₂ b₁ b₂) :
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
  have hNormalContinuous : ContinuousOn normalPairing
      ([[a₁, b₁]] ×ˢ [[a₂, b₂]]) := by
    exact (regularity.continuousOn.inner continuousOn_const).neg
  have hTangentContinuous : ContinuousOn tangentPairing
      ([[a₁, b₁]] ×ˢ [[a₂, b₂]]) := by
    exact regularity.continuousOn.inner continuousOn_const
  have hPointDifferentiable (p : ℝ × ℝ) : DifferentiableAt ℝ point p := by
    dsimp only [point, planarRectanglePoint]
    fun_prop
  have hNormalDifferentiable (p : ℝ × ℝ)
      (hp : p ∈ ([[a₁, b₁]] ×ˢ [[a₂, b₂]])) :
      DifferentiableAt ℝ normalPairing p := by
    dsimp only [normalPairing]
    exact ((regularity.differentiableAt p hp).comp p
      (hPointDifferentiable p) |>.inner ℝ (differentiableAt_const _)).neg
  have hTangentDifferentiable (p : ℝ × ℝ)
      (hp : p ∈ ([[a₁, b₁]] ×ˢ [[a₂, b₂]])) :
      DifferentiableAt ℝ tangentPairing p := by
    dsimp only [tangentPairing]
    exact (regularity.differentiableAt p hp).comp p
      (hPointDifferentiable p) |>.inner ℝ (differentiableAt_const _)
  have hDerivativeIntegrable : IntegrableOn
      (fun p : ℝ × ℝ ↦
        fderiv ℝ normalPairing p (1, 0) +
          fderiv ℝ tangentPairing p (0, 1))
      ([[a₁, b₁]] ×ˢ [[a₂, b₂]]) := by
    refine regularity.curlIntegrable.congr_fun (fun p hp ↦ ?_)
      (measurableSet_uIcc.prod measurableSet_uIcc)
    exact (planarRectangle_divergence_eq_inner_curl field center first second p
      (regularity.differentiableAt p hp)).symm
  have hGreen := MeasureTheory.integral2_divergence_prod_of_hasFDerivAt
    normalPairing tangentPairing
    (fun p ↦ fderiv ℝ normalPairing p)
    (fun p ↦ fderiv ℝ tangentPairing p)
    a₁ a₂ b₁ b₂ hNormalContinuous hTangentContinuous
    (fun p hp ↦ (hNormalDifferentiable p
      ⟨Set.Ioo_subset_Icc_self hp.1, Set.Ioo_subset_Icc_self hp.2⟩).hasFDerivAt)
    (fun p hp ↦ (hTangentDifferentiable p
      ⟨Set.Ioo_subset_Icc_self hp.1, Set.Ioo_subset_Icc_self hp.2⟩).hasFDerivAt)
    hDerivativeIntegrable
  calc
    (∫ u in a₁..b₁, ∫ v in a₂..b₂,
        inner ℝ
          ((∇ ⨯ field) (planarRectanglePoint center first second u v))
          (basis.repr second ⨯ₑ₃ basis.repr first)) =
        ∫ u in a₁..b₁, ∫ v in a₂..b₂,
          fderiv ℝ normalPairing (u, v) (1, 0) +
            fderiv ℝ tangentPairing (u, v) (0, 1) := by
      apply intervalIntegral.integral_congr
      intro u hu
      apply intervalIntegral.integral_congr
      intro v hv
      exact (planarRectangle_divergence_eq_inner_curl field center first second (u, v)
        (regularity.differentiableAt (u, v) ⟨hu, hv⟩)).symm
    _ = _ := by
      rw [hGreen]
      dsimp only [normalPairing, tangentPairing, point]
      rw [intervalIntegral.integral_neg, intervalIntegral.integral_neg]
      ring

end
end Space
