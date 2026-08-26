/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Mathematics.Distribution.CoordinateHyperplaneDelta
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Coordinate Heaviside distributions

## i. Overview

This file identifies the distributional normal derivative of the positive coordinate
half-space with the independently defined Lebesgue distribution on its boundary hyperplane.
The vector `+e_last` points into the positive half-space; this file does not assign it the
outward-boundary-normal convention used by an oriented region.

## ii. Key results

- `Distribution.fderivD_heavisideStep_last_apply`: pointwise boundary-delta evaluation.
- `Distribution.heavisideNormalDerivative_eq_coordinateHyperplaneDelta`: equality of the
  Heaviside normal derivative and the boundary delta.

## iii. Table of contents

- A. Distributional derivative of the Heaviside step

## iv. References

This is neutral distribution theory. No electromagnetic boundary law is assumed here.
-/

@[expose] public section

open MeasureTheory SchwartzMap
open scoped SchwartzMap

namespace Physlib
namespace Distribution

noncomputable section

/-!
## A. Distributional derivative of the Heaviside step
-/

/-- The distributional derivative of the positive-last-coordinate Heaviside distribution,
evaluated in the inward-pointing positive last-coordinate direction, is the independently defined
boundary hyperplane delta. -/
lemma fderivD_heavisideStep_last_apply (d : ℕ)
    (η : SchwartzMap (EuclideanSpace ℝ (Fin d.succ)) ℝ) :
    fderivD ℝ (heavisideStep d) η
        (coordinateNormalEmbedding d (Fin.last d) 1) =
      coordinateHyperplaneDelta d (Fin.last d) η := by
  let i : Fin d.succ := Fin.last d
  let normal : EuclideanSpace ℝ (Fin d.succ) := coordinateNormalEmbedding d i 1
  let g : ℝ × EuclideanSpace ℝ (Fin d) → ℝ := fun p =>
    fderiv ℝ η (coordinateNormalLine d i p.2 p.1) normal
  have hcomp := ((coordinateSplit_measurePreserving d i).symm.integrable_comp_emb
      (coordinateSplit d i).symm.measurableEmbedding).mpr
        (integrable_fderiv_coordinateNormal d i η)
  rw [Measure.volume_eq_prod] at hcomp
  have hgProd : Integrable g
      ((volume : Measure ℝ).prod (volume : Measure (EuclideanSpace ℝ (Fin d)))) := by
    refine hcomp.congr ?_
    filter_upwards with p
    simp only [g, normal, Function.comp_apply, coordinateNormalLine_eq_split_symm]
  have hChange :
      ∫ y in {y : EuclideanSpace ℝ (Fin d.succ) | 0 < y i},
          fderiv ℝ η y normal =
        ∫ p in {p : ℝ × EuclideanSpace ℝ (Fin d) | 0 < p.1}, g p := by
    have h := (coordinateSplit_measurePreserving d i).setIntegral_preimage_emb
      (coordinateSplit d i).measurableEmbedding g
      {p : ℝ × EuclideanSpace ℝ (Fin d) | 0 < p.1}
    simpa [g, coordinateNormalLine_eq_split_symm] using h
  have hFubini :
      ∫ p in {p : ℝ × EuclideanSpace ℝ (Fin d) | 0 < p.1}, g p =
        ∫ x : EuclideanSpace ℝ (Fin d),
          ∫ r in Set.Ioi (0 : ℝ), g (r, x) := by
    have hset : {p : ℝ × EuclideanSpace ℝ (Fin d) | 0 < p.1} =
        Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (EuclideanSpace ℝ (Fin d))) := by
      ext p
      simp
    rw [hset, Measure.volume_eq_prod]
    calc
      _ = ∫ p : EuclideanSpace ℝ (Fin d) × ℝ in
          Set.univ ×ˢ Set.Ioi (0 : ℝ), g p.swap
          ∂((volume : Measure (EuclideanSpace ℝ (Fin d))).prod (volume : Measure ℝ)) := by
        exact (MeasureTheory.setIntegral_prod_swap
          (Set.Ioi (0 : ℝ)) (Set.univ : Set (EuclideanSpace ℝ (Fin d))) g).symm
      _ = _ := by
        rw [MeasureTheory.setIntegral_prod]
        · simp
        · exact hgProd.integrableOn.swap
  rw [fderivD_apply, heavisideStep_apply, coordinateHyperplaneDelta_apply]
  simp only [evalCLM_apply_apply, fderivCLM_apply]
  change -(∫ y in {y : EuclideanSpace ℝ (Fin d.succ) | 0 < y i},
      fderiv ℝ η y normal) = _
  rw [hChange, hFubini]
  simp_rw [g, normal, integral_Ioi_fderiv_coordinateNormalLine]
  simp only [integral_neg, neg_neg, i]

/-- The scalar distribution obtained by differentiating the positive-last-coordinate Heaviside
distribution in its positive coordinate-normal direction. -/
def heavisideNormalDerivative (d : ℕ) :
    Physlib.Distribution ℝ (EuclideanSpace ℝ (Fin d.succ)) ℝ :=
  let ev :
      (EuclideanSpace ℝ (Fin d.succ) →L[ℝ] ℝ) →L[ℝ] ℝ := {
    toFun u := u (coordinateNormalEmbedding d (Fin.last d) 1)
    map_add' u v := by simp
    map_smul' c u := by simp
  }
  ev.comp (fderivD ℝ (heavisideStep d))

@[simp]
lemma heavisideNormalDerivative_apply (d : ℕ)
    (η : SchwartzMap (EuclideanSpace ℝ (Fin d.succ)) ℝ) :
    heavisideNormalDerivative d η =
      fderivD ℝ (heavisideStep d) η
        (coordinateNormalEmbedding d (Fin.last d) 1) :=
  rfl

/-- The positive coordinate-normal derivative of the Heaviside distribution is the boundary
hyperplane delta as an equality of scalar distributions. -/
lemma heavisideNormalDerivative_eq_coordinateHyperplaneDelta (d : ℕ) :
    heavisideNormalDerivative d = coordinateHyperplaneDelta d (Fin.last d) := by
  ext η
  exact fderivD_heavisideStep_last_apply d η

end
end Distribution
end Physlib
