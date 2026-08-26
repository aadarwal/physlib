/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Mathematics.Distribution.CoordinateHyperplaneDelta

/-!
# Coordinate Heaviside distributions

## i. Overview

This file identifies the distributional normal derivative of the positive coordinate
half-space with the independently defined Lebesgue distribution on its boundary hyperplane.
The selected positive coordinate vector points into the positive half-space; this file does not
assign it the outward-boundary-normal convention used by an oriented region.

## ii. Key results

- `Distribution.coordinateHeavisideStep`: the positive half-space distribution selected by any
  coordinate.
- `Distribution.fderivD_coordinateHeavisideStep_apply`: pointwise boundary-delta evaluation.
- `Distribution.coordinateHeavisideNormalDerivative_eq_coordinateHyperplaneDelta`: equality of the
  selected-coordinate derivative distribution and boundary delta.
- `Distribution.fderivD_heavisideStep_last_apply`: compatibility with the original last-coordinate
  definition.
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

/-- The scalar distribution integrating a Schwartz map over the open positive half-space selected
by coordinate `i`. -/
def coordinateHeavisideStep (d : ℕ) (i : Fin d.succ) :
    Physlib.Distribution ℝ (EuclideanSpace ℝ (Fin d.succ)) ℝ := by
  refine mkCLMtoNormedSpace
    (fun η ↦ ∫ x in {x : EuclideanSpace ℝ (Fin d.succ) | 0 < x i}, η x) ?_ ?_ ?_
  · intro η₁ η₂
    simp only [add_apply]
    rw [MeasureTheory.integral_add]
    · exact (integrable η₁).integrableOn
    · exact (integrable η₂).integrableOn
  · intro a η
    simp only [smul_apply, RingHom.id_apply]
    rw [MeasureTheory.integral_smul]
  · have hμ : (volume (α := EuclideanSpace ℝ (Fin d.succ))).HasTemperateGrowth := by
      infer_instance
    rcases hμ.exists_integrable with ⟨n, h⟩
    let m := (n, 0)
    use Finset.Iic m, 2 ^ n *
      ∫ x, (1 + ‖x‖) ^ (-(n : ℝ)) ∂(volume : Measure (EuclideanSpace ℝ (Fin d.succ)))
    refine ⟨by positivity, fun η ↦ (norm_integral_le_integral_norm _).trans ?_⟩
    trans ∫ x, ‖η x‖ ∂(volume : Measure (EuclideanSpace ℝ (Fin d.succ)))
    · refine setIntegral_le_integral ?_ ?_
      · have hi := integrable η (μ := volume)
        fun_prop
      · filter_upwards with x
        simp
    · have h' : ∀ x, ‖η x‖ ≤ (1 + ‖x‖) ^ (-(n : ℝ)) *
          (2 ^ n * ((Finset.Iic m).sup
            (fun m' ↦ SchwartzMap.seminorm ℝ m'.1 m'.2) η)) := by
        intro x
        rw [Real.rpow_neg (by positivity), ← div_eq_inv_mul,
          le_div_iff₀' (by positivity), Real.rpow_natCast]
        simpa using one_add_le_sup_seminorm_apply
          (m := m) (k := n) (n := 0) le_rfl le_rfl η x
      apply (integral_mono (by simpa using η.integrable_pow_mul volume 0) _ h').trans
      · unfold schwartzSeminormFamily
        rw [integral_mul_const, ← mul_assoc, mul_comm (2 ^ n)]
      · apply h.mul_const

@[simp]
lemma coordinateHeavisideStep_apply (d : ℕ) (i : Fin d.succ)
    (η : SchwartzMap (EuclideanSpace ℝ (Fin d.succ)) ℝ) :
    coordinateHeavisideStep d i η =
      ∫ x in {x : EuclideanSpace ℝ (Fin d.succ) | 0 < x i}, η x :=
  rfl

/-- The selected-coordinate definition recovers the original positive-last-coordinate Heaviside
distribution. -/
lemma coordinateHeavisideStep_last (d : ℕ) :
    coordinateHeavisideStep d (Fin.last d) = heavisideStep d := by
  ext η
  rw [coordinateHeavisideStep_apply, heavisideStep_apply]

/-- The distributional derivative of the selected positive-coordinate Heaviside distribution,
evaluated in its inward-pointing positive coordinate direction, is the independently defined
boundary hyperplane delta. -/
lemma fderivD_coordinateHeavisideStep_apply (d : ℕ) (i : Fin d.succ)
    (η : SchwartzMap (EuclideanSpace ℝ (Fin d.succ)) ℝ) :
    fderivD ℝ (coordinateHeavisideStep d i) η
        (coordinateNormalEmbedding d i 1) =
      coordinateHyperplaneDelta d i η := by
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
  rw [fderivD_apply, coordinateHeavisideStep_apply, coordinateHyperplaneDelta_apply]
  simp only [evalCLM_apply_apply, fderivCLM_apply]
  change -(∫ y in {y : EuclideanSpace ℝ (Fin d.succ) | 0 < y i},
      fderiv ℝ η y normal) = _
  rw [hChange, hFubini]
  simp_rw [g, normal, integral_Ioi_fderiv_coordinateNormalLine]
  simp only [integral_neg, neg_neg]

/-- The distributional derivative of the positive-last-coordinate Heaviside distribution,
evaluated in the inward-pointing positive last-coordinate direction, is the independently defined
boundary hyperplane delta. -/
lemma fderivD_heavisideStep_last_apply (d : ℕ)
    (η : SchwartzMap (EuclideanSpace ℝ (Fin d.succ)) ℝ) :
    fderivD ℝ (heavisideStep d) η
        (coordinateNormalEmbedding d (Fin.last d) 1) =
      coordinateHyperplaneDelta d (Fin.last d) η := by
  rw [← coordinateHeavisideStep_last]
  exact fderivD_coordinateHeavisideStep_apply d (Fin.last d) η

/-- The scalar distribution obtained by differentiating a selected-coordinate Heaviside
distribution in its positive coordinate-normal direction. -/
def coordinateHeavisideNormalDerivative (d : ℕ) (i : Fin d.succ) :
    Physlib.Distribution ℝ (EuclideanSpace ℝ (Fin d.succ)) ℝ :=
  let ev :
      (EuclideanSpace ℝ (Fin d.succ) →L[ℝ] ℝ) →L[ℝ] ℝ := {
    toFun u := u (coordinateNormalEmbedding d i 1)
    map_add' u v := by simp
    map_smul' c u := by simp
  }
  ev.comp (fderivD ℝ (coordinateHeavisideStep d i))

@[simp]
lemma coordinateHeavisideNormalDerivative_apply (d : ℕ) (i : Fin d.succ)
    (η : SchwartzMap (EuclideanSpace ℝ (Fin d.succ)) ℝ) :
    coordinateHeavisideNormalDerivative d i η =
      fderivD ℝ (coordinateHeavisideStep d i) η (coordinateNormalEmbedding d i 1) :=
  rfl

/-- The selected positive coordinate-normal derivative of the Heaviside distribution is the
corresponding boundary hyperplane delta. -/
lemma coordinateHeavisideNormalDerivative_eq_coordinateHyperplaneDelta
    (d : ℕ) (i : Fin d.succ) :
    coordinateHeavisideNormalDerivative d i = coordinateHyperplaneDelta d i := by
  ext η
  exact fderivD_coordinateHeavisideStep_apply d i η

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
