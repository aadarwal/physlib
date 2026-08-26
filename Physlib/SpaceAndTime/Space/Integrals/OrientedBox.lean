/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.SpaceAndTime.Space.Derivatives.DivCross
public import Physlib.SpaceAndTime.Space.Integrals.AffineBox
public import Physlib.SpaceAndTime.Space.Integrals.CoordinateBox

/-!
# Divergence over affine oriented boxes in Space

## i. Overview

This file pulls the three-dimensional divergence theorem back along an arbitrary ordered affine
box parameterization. The volume integrand retains the signed frame determinant, while each pair
of opposite faces is paired with its corresponding oriented cofactor.

The three frame directions need not be orthogonal, normalized, or independent. Consequently the
formula remains a signed identity for reversed or degenerate frames; it does not silently replace
the oriented determinant or cofactors by absolute areas.

This is neutral smooth-bulk calculus. It does not state a Maxwell equation, specialize the box to
`PlanarPillboxFamily`, combine independent half-space fields, represent carrier-supported sheet
sources, or prove a shrinking-cell limit.

## ii. Key results

- `integral3_div_affineBox`: the divergence integral over an affine box equals the sum of its three
  ordered pairs of cofactor-weighted face fluxes.

## iii. Table of contents

- A. Affine-box divergence theorem

## iv. References

This is a coordinate specialization of the divergence theorem.
-/

@[expose] public section

open Matrix MeasureTheory
open scoped Interval

namespace Space

noncomputable section

/-! ## A. Affine-box divergence theorem -/

/-- The integral of divergence over an ordered affine box, including its signed frame determinant,
equals the sum of the outward oriented fluxes through the three pairs of opposite faces.

The face orders are `(second, third)`, `(first, third)`, and `(first, second)`. The second pair uses
the cofactor `third × first`, so all three upper-minus-lower pairs follow the same orientation. -/
lemma integral3_div_affineBox
    (field : Space → EuclideanSpace ℝ (Fin 3))
    (center first second third : Space)
    (a₁ a₂ a₃ b₁ b₂ b₃ : ℝ)
    (ha₁ : a₁ ≤ b₁) (ha₂ : a₂ ≤ b₂) (ha₃ : a₃ ≤ b₃)
    (hfield : ContDiff ℝ 1 field) :
    (∫ u in a₁..b₁, ∫ v in a₂..b₂, ∫ w in a₃..b₃,
        (∇ ⬝ field) (affineBoxPoint center first second third u v w) *
          inner ℝ (basis.repr first)
            (basis.repr second ⨯ₑ₃ basis.repr third)) =
      ((∫ v in a₂..b₂, ∫ w in a₃..b₃,
            inner ℝ (field (affineBoxPoint center first second third b₁ v w))
              (basis.repr second ⨯ₑ₃ basis.repr third)) -
        ∫ v in a₂..b₂, ∫ w in a₃..b₃,
            inner ℝ (field (affineBoxPoint center first second third a₁ v w))
              (basis.repr second ⨯ₑ₃ basis.repr third)) +
      ((∫ u in a₁..b₁, ∫ w in a₃..b₃,
            inner ℝ (field (affineBoxPoint center first second third u b₂ w))
              (basis.repr third ⨯ₑ₃ basis.repr first)) -
        ∫ u in a₁..b₁, ∫ w in a₃..b₃,
            inner ℝ (field (affineBoxPoint center first second third u a₂ w))
              (basis.repr third ⨯ₑ₃ basis.repr first)) +
      ((∫ u in a₁..b₁, ∫ v in a₂..b₂,
            inner ℝ (field (affineBoxPoint center first second third u v b₃))
              (basis.repr first ⨯ₑ₃ basis.repr second)) -
        ∫ u in a₁..b₁, ∫ v in a₂..b₂,
            inner ℝ (field (affineBoxPoint center first second third u v a₃))
              (basis.repr first ⨯ₑ₃ basis.repr second)) := by
  let point : (Fin 3 → ℝ) → Space :=
    affineBoxCoordinatePoint center first second third
  let cofactor : Fin 3 → EuclideanSpace ℝ (Fin 3) :=
    ![basis.repr second ⨯ₑ₃ basis.repr third,
      basis.repr third ⨯ₑ₃ basis.repr first,
      basis.repr first ⨯ₑ₃ basis.repr second]
  let flux : Fin 3 → (Fin 3 → ℝ) → ℝ := fun i q ↦
    inner ℝ (field (point q)) (cofactor i)
  let lower : Fin 3 → ℝ := ![a₁, a₂, a₃]
  let upper : Fin 3 → ℝ := ![b₁, b₂, b₃]
  have hPoint : ContDiff ℝ 1 point := by
    change ContDiff ℝ 1 (fun p : Fin 3 → ℝ ↦
      center + p 0 • first + p 1 • second + p 2 • third)
    fun_prop
  have hPullback : ContDiff ℝ 1 (fun q ↦ field (point q)) :=
    hfield.comp hPoint
  have hFlux (i : Fin 3) : ContDiff ℝ 1 (flux i) :=
    hPullback.inner ℝ contDiff_const
  have hBounds : lower ≤ upper := by
    intro i
    fin_cases i <;> simpa [lower, upper]
  have hDiagonal (q : Fin 3 → ℝ) :
      (∑ i, fderiv ℝ (flux i) q (Pi.single i 1)) =
        (∇ ⬝ field) (point q) * inner ℝ (basis.repr first)
          (basis.repr second ⨯ₑ₃ basis.repr third) := by
    rw [Fin.sum_univ_three]
    change
      fderiv ℝ
          (fun p : Fin 3 → ℝ ↦ inner ℝ
            (field (affineBoxCoordinatePoint center first second third p))
            (basis.repr second ⨯ₑ₃ basis.repr third)) q (Pi.single 0 1) +
        fderiv ℝ
          (fun p : Fin 3 → ℝ ↦ inner ℝ
            (field (affineBoxCoordinatePoint center first second third p))
            (basis.repr third ⨯ₑ₃ basis.repr first)) q (Pi.single 1 1) +
        fderiv ℝ
          (fun p : Fin 3 → ℝ ↦ inner ℝ
            (field (affineBoxCoordinatePoint center first second third p))
            (basis.repr first ⨯ₑ₃ basis.repr second)) q (Pi.single 2 1) = _
    have hfPoint : DifferentiableAt ℝ field
        (affineBoxCoordinatePoint center first second third q) :=
      hfield.differentiable (by norm_num) _
    rw [fderiv_inner_affineBoxCoordinatePoint field center first second third
        (basis.repr second ⨯ₑ₃ basis.repr third) q 0 hfPoint,
      fderiv_inner_affineBoxCoordinatePoint field center first second third
        (basis.repr third ⨯ₑ₃ basis.repr first) q 1 hfPoint,
      fderiv_inner_affineBoxCoordinatePoint field center first second third
        (basis.repr first ⨯ₑ₃ basis.repr second) q 2 hfPoint]
    simpa [point] using
      (div_mul_inner_cross_eq_sum_inner_fderiv field
        (affineBoxCoordinatePoint center first second third q)
        first second third hfPoint).symm
  have hDiagonalContinuous : Continuous fun q : Fin 3 → ℝ ↦
      ∑ i, fderiv ℝ (flux i) q (Pi.single i 1) := by
    apply continuous_finsetSum
    intro i hi
    have hFderiv := (hFlux i).continuous_fderiv (by norm_num)
    fun_prop
  have hGauss := MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable'
    (n := 2) lower upper hBounds flux (fun i q ↦ fderiv ℝ (flux i) q)
    (∅ : Set (Fin 3 → ℝ)) Set.countable_empty
    (fun i ↦ (hFlux i).continuous.continuousOn)
    (fun q hq i ↦ (hFlux i).differentiable (by norm_num) q |>.hasFDerivAt)
    (hDiagonalContinuous.continuousOn.integrableOn_compact isCompact_Icc)
  have hVolume :
      (∫ q in Set.Icc lower upper,
          ∑ i, fderiv ℝ (flux i) q (Pi.single i 1)) =
        ∫ u in a₁..b₁, ∫ v in a₂..b₂, ∫ w in a₃..b₃,
          (∇ ⬝ field) (affineBoxPoint center first second third u v w) *
            inner ℝ (basis.repr first)
              (basis.repr second ⨯ₑ₃ basis.repr third) := by
    rw [finThree_setIntegral_Icc_eq_iterated _ hDiagonalContinuous
      a₁ a₂ a₃ b₁ b₂ b₃ ha₁ ha₂ ha₃]
    apply intervalIntegral.integral_congr
    intro u hu
    apply intervalIntegral.integral_congr
    intro v hv
    apply intervalIntegral.integral_congr
    intro w hw
    simpa only [lower, upper, point, affineBoxCoordinatePoint,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] using
      hDiagonal ![u, v, w]
  have hFace0Upper :
      (∫ x in Set.Icc (lower ∘ (0 : Fin 3).succAbove)
          (upper ∘ (0 : Fin 3).succAbove),
        flux 0 ((0 : Fin 3).insertNth (upper 0) x)) =
        ∫ v in a₂..b₂, ∫ w in a₃..b₃,
          inner ℝ (field (affineBoxPoint center first second third b₁ v w))
            (basis.repr second ⨯ₑ₃ basis.repr third) := by
    simpa only [lower, upper, flux, point, cofactor,
      affineBoxCoordinatePoint, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      Function.comp_apply] using
      (finThree_faceZero_setIntegral_Icc_eq_iterated
        (flux 0) (hFlux 0).continuous b₁
        a₁ a₂ a₃ b₁ b₂ b₃ ha₂ ha₃)
  have hFace0Lower :
      (∫ x in Set.Icc (lower ∘ (0 : Fin 3).succAbove)
          (upper ∘ (0 : Fin 3).succAbove),
        flux 0 ((0 : Fin 3).insertNth (lower 0) x)) =
        ∫ v in a₂..b₂, ∫ w in a₃..b₃,
          inner ℝ (field (affineBoxPoint center first second third a₁ v w))
            (basis.repr second ⨯ₑ₃ basis.repr third) := by
    simpa only [lower, upper, flux, point, cofactor,
      affineBoxCoordinatePoint, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      Function.comp_apply] using
      (finThree_faceZero_setIntegral_Icc_eq_iterated
        (flux 0) (hFlux 0).continuous a₁
        a₁ a₂ a₃ b₁ b₂ b₃ ha₂ ha₃)
  have hFace1Upper :
      (∫ x in Set.Icc (lower ∘ (1 : Fin 3).succAbove)
          (upper ∘ (1 : Fin 3).succAbove),
        flux 1 ((1 : Fin 3).insertNth (upper 1) x)) =
        ∫ u in a₁..b₁, ∫ w in a₃..b₃,
          inner ℝ (field (affineBoxPoint center first second third u b₂ w))
            (basis.repr third ⨯ₑ₃ basis.repr first) := by
    simpa only [lower, upper, flux, point, cofactor,
      affineBoxCoordinatePoint, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      Function.comp_apply] using
      (finThree_faceOne_setIntegral_Icc_eq_iterated
        (flux 1) (hFlux 1).continuous b₂
        a₁ a₂ a₃ b₁ b₂ b₃ ha₁ ha₃)
  have hFace1Lower :
      (∫ x in Set.Icc (lower ∘ (1 : Fin 3).succAbove)
          (upper ∘ (1 : Fin 3).succAbove),
        flux 1 ((1 : Fin 3).insertNth (lower 1) x)) =
        ∫ u in a₁..b₁, ∫ w in a₃..b₃,
          inner ℝ (field (affineBoxPoint center first second third u a₂ w))
            (basis.repr third ⨯ₑ₃ basis.repr first) := by
    simpa only [lower, upper, flux, point, cofactor,
      affineBoxCoordinatePoint, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      Function.comp_apply] using
      (finThree_faceOne_setIntegral_Icc_eq_iterated
        (flux 1) (hFlux 1).continuous a₂
        a₁ a₂ a₃ b₁ b₂ b₃ ha₁ ha₃)
  have hFace2Upper :
      (∫ x in Set.Icc (lower ∘ (2 : Fin 3).succAbove)
          (upper ∘ (2 : Fin 3).succAbove),
        flux 2 ((2 : Fin 3).insertNth (upper 2) x)) =
        ∫ u in a₁..b₁, ∫ v in a₂..b₂,
          inner ℝ (field (affineBoxPoint center first second third u v b₃))
            (basis.repr first ⨯ₑ₃ basis.repr second) := by
    simpa only [lower, upper, flux, point, cofactor,
      affineBoxCoordinatePoint, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      Function.comp_apply] using
      (finThree_faceTwo_setIntegral_Icc_eq_iterated
        (flux 2) (hFlux 2).continuous b₃
        a₁ a₂ a₃ b₁ b₂ b₃ ha₁ ha₂)
  have hFace2Lower :
      (∫ x in Set.Icc (lower ∘ (2 : Fin 3).succAbove)
          (upper ∘ (2 : Fin 3).succAbove),
        flux 2 ((2 : Fin 3).insertNth (lower 2) x)) =
        ∫ u in a₁..b₁, ∫ v in a₂..b₂,
          inner ℝ (field (affineBoxPoint center first second third u v a₃))
            (basis.repr first ⨯ₑ₃ basis.repr second) := by
    simpa only [lower, upper, flux, point, cofactor,
      affineBoxCoordinatePoint, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      Function.comp_apply] using
      (finThree_faceTwo_setIntegral_Icc_eq_iterated
        (flux 2) (hFlux 2).continuous a₃
        a₁ a₂ a₃ b₁ b₂ b₃ ha₁ ha₂)
  rw [← hVolume, hGauss, Fin.sum_univ_three,
    hFace0Upper, hFace0Lower, hFace1Upper, hFace1Lower,
    hFace2Upper, hFace2Lower]

end
end Space
