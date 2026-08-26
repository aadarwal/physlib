/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Mathematics.Distribution.CoordinateHyperplane

/-!
# Coordinate hyperplane delta distributions

## i. Overview

This file defines integration over a coordinate hyperplane as a scalar distribution and proves
the one-dimensional normal-line calculus used by the Heaviside derivative.

## ii. Key results

- `Distribution.coordinateHyperplaneDelta`: integration over a coordinate hyperplane.
- `Distribution.integral_Ioi_fderiv_coordinateNormalLine`: the normal half-line integral.

## iii. Table of contents

- A. Coordinate hyperplane delta
- B. Normal-line calculus

## iv. References

This is neutral distribution and integration theory.
-/

@[expose] public section

open MeasureTheory SchwartzMap
open scoped SchwartzMap

namespace Physlib
namespace Distribution

noncomputable section

/-!
## A. Coordinate hyperplane delta
-/

/-- Restrict a Schwartz function to a coordinate hyperplane. -/
def coordinateHyperplaneRestriction (d : ℕ) (i : Fin d.succ) :
    𝓢(EuclideanSpace ℝ (Fin d.succ), ℝ) →L[ℝ] 𝓢(EuclideanSpace ℝ (Fin d), ℝ) :=
  SchwartzMap.compCLMOfAntilipschitz ℝ
    (coordinateHyperplaneEmbeddingLI d i).toContinuousLinearMap.hasTemperateGrowth
    (coordinateHyperplaneEmbeddingLI d i).antilipschitz

@[simp]
lemma coordinateHyperplaneRestriction_apply (d : ℕ) (i : Fin d.succ)
    (η : 𝓢(EuclideanSpace ℝ (Fin d.succ), ℝ)) (x : EuclideanSpace ℝ (Fin d)) :
    coordinateHyperplaneRestriction d i η x = η (coordinateHyperplaneEmbedding d i x) :=
  rfl

/-- The scalar distribution obtained by integrating a test function over the coordinate
hyperplane `x i = 0`, with the Euclidean Lebesgue measure on the retained coordinates. -/
def coordinateHyperplaneDelta (d : ℕ) (i : Fin d.succ) :
    Physlib.Distribution ℝ (EuclideanSpace ℝ (Fin d.succ)) ℝ :=
  (Distribution.const ℝ (EuclideanSpace ℝ (Fin d)) (1 : ℝ)).comp
    (coordinateHyperplaneRestriction d i)

/-- Evaluating the coordinate-hyperplane delta is Lebesgue integration of the restricted test
function over the retained coordinates. -/
@[simp]
lemma coordinateHyperplaneDelta_apply (d : ℕ) (i : Fin d.succ)
    (η : 𝓢(EuclideanSpace ℝ (Fin d.succ), ℝ)) :
    coordinateHyperplaneDelta d i η =
      ∫ x : EuclideanSpace ℝ (Fin d), η (coordinateHyperplaneEmbedding d i x) := by
  rw [coordinateHyperplaneDelta, ContinuousLinearMap.comp_apply,
    Distribution.const_apply]
  simp

/-- In one ambient dimension, the coordinate-hyperplane delta evaluates at the origin. -/
lemma coordinateHyperplaneDelta_zero_apply
    (η : SchwartzMap (EuclideanSpace ℝ (Fin 1)) ℝ) :
    coordinateHyperplaneDelta 0 (Fin.last 0) η = η 0 := by
  rw [coordinateHyperplaneDelta_apply, volume_euclideanSpace_eq_dirac]
  simp

/-- In one ambient dimension, the coordinate-hyperplane delta is the Dirac delta at the origin. -/
lemma coordinateHyperplaneDelta_zero :
    coordinateHyperplaneDelta 0 (Fin.last 0) =
      Distribution.diracDelta ℝ (0 : EuclideanSpace ℝ (Fin 1)) := by
  ext η
  change coordinateHyperplaneDelta 0 (Fin.last 0) η = η 0
  exact coordinateHyperplaneDelta_zero_apply η

/-!
## B. Normal-line calculus
-/

/-- Restrict a Schwartz function to one affine selected-coordinate normal line. -/
def coordinateNormalLineRestriction (d : ℕ) (i : Fin d.succ)
    (x : EuclideanSpace ℝ (Fin d)) :
    𝓢(EuclideanSpace ℝ (Fin d.succ), ℝ) →L[ℝ] 𝓢(ℝ, ℝ) :=
  SchwartzMap.compCLMOfAntilipschitz ℝ
    ((coordinateNormalEmbeddingLI d i).toContinuousLinearMap.hasTemperateGrowth.add
      (Function.HasTemperateGrowth.const (coordinateHyperplaneEmbedding d i x)))
    (coordinateNormalLine_isometry d i x).antilipschitz

@[simp]
lemma coordinateNormalLineRestriction_apply (d : ℕ) (i : Fin d.succ)
    (x : EuclideanSpace ℝ (Fin d))
    (η : 𝓢(EuclideanSpace ℝ (Fin d.succ), ℝ)) (r : ℝ) :
    coordinateNormalLineRestriction d i x η r = η (coordinateNormalLine d i x r) :=
  rfl

/-- The derivative of a test function restricted to a selected normal line is its ambient
Fréchet derivative applied to the positive coordinate-normal vector. -/
lemma deriv_coordinateNormalLineRestriction (d : ℕ) (i : Fin d.succ)
    (x : EuclideanSpace ℝ (Fin d))
    (η : SchwartzMap (EuclideanSpace ℝ (Fin d.succ)) ℝ) (r : ℝ) :
    deriv (coordinateNormalLineRestriction d i x η) r =
      fderiv ℝ η (coordinateNormalLine d i x r) (coordinateNormalEmbedding d i 1) := by
  have hline : DifferentiableAt ℝ (coordinateNormalLine d i x) r := by
    change DifferentiableAt ℝ
      (fun t => (coordinateNormalEmbeddingLI d i).toContinuousLinearMap t +
        coordinateHyperplaneEmbedding d i x) r
    fun_prop
  change deriv (fun t => η (coordinateNormalLine d i x t)) r = _
  rw [← fderiv_apply_one_eq_deriv,
    fderiv_fun_comp _ η.differentiableAt hline]
  simp only [ContinuousLinearMap.comp_apply]
  rw [fderiv_coordinateNormalLine_apply]

/-- Integrating the selected normal derivative of a Schwartz function over the positive
half-line returns the negative boundary value. -/
lemma integral_Ioi_fderiv_coordinateNormalLine (d : ℕ) (i : Fin d.succ)
    (x : EuclideanSpace ℝ (Fin d))
    (η : SchwartzMap (EuclideanSpace ℝ (Fin d.succ)) ℝ) :
    ∫ r in Set.Ioi (0 : ℝ),
        fderiv ℝ η (coordinateNormalLine d i x r) (coordinateNormalEmbedding d i 1) =
      -η (coordinateHyperplaneEmbedding d i x) := by
  let line : SchwartzMap ℝ ℝ := coordinateNormalLineRestriction d i x η
  calc
    _ = ∫ r in Set.Ioi (0 : ℝ), deriv line r := by
      congr 1
      funext r
      exact (deriv_coordinateNormalLineRestriction d i x η r).symm
    _ = -line 0 := by
      rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
        (f := fun r => line r) (m := 0)]
      · simp
      · exact ContinuousAt.continuousWithinAt (by fun_prop)
      · exact fun r _ => DifferentiableAt.hasDerivAt (by fun_prop)
      · exact (integrable ((SchwartzMap.derivCLM ℝ ℝ) line)).integrableOn
      · exact Filter.Tendsto.mono_left line.toZeroAtInfty.zero_at_infty'
          atTop_le_cocompact
    _ = -η (coordinateHyperplaneEmbedding d i x) := by
      simp [line, coordinateNormalLine]

/-- The selected coordinate-normal derivative of a Schwartz function is Lebesgue integrable. -/
lemma integrable_fderiv_coordinateNormal (d : ℕ) (i : Fin d.succ)
    (η : SchwartzMap (EuclideanSpace ℝ (Fin d.succ)) ℝ) :
    Integrable
      (fun y => fderiv ℝ η y (coordinateNormalEmbedding d i 1)) volume := by
  let μ : Measure (EuclideanSpace ℝ (Fin d.succ)) := volume
  change Integrable
    (fun y => fderiv ℝ η y (coordinateNormalEmbedding d i 1)) μ
  refine (integrable (μ := μ)
    ((SchwartzMap.evalCLM ℝ (EuclideanSpace ℝ (Fin d.succ)) ℝ
      (coordinateNormalEmbedding d i 1))
        ((SchwartzMap.fderivCLM ℝ (EuclideanSpace ℝ (Fin d.succ)) ℝ) η))).congr ?_
  filter_upwards with y
  simp only [evalCLM_apply_apply, fderivCLM_apply]

end
end Distribution
end Physlib
