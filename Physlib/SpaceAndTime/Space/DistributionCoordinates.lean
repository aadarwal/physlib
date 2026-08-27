/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Mathematics.Distribution.Basic
public import Physlib.SpaceAndTime.Space.Derivatives.Basic

/-!
# Tempered distributions in standard space coordinates

## i. Overview

This file transports tempered distributions on finite-dimensional Euclidean coordinate space to
Physlib's `Space d` through its standard orthonormal basis. It also identifies spatial coordinate
derivatives with the corresponding Euclidean directional derivatives.

## ii. Key results

- `Space.basisCoordinateSchwartz`: pull a spatial Schwartz test back to Euclidean coordinates.
- `Space.distributionOfEuclideanCoordinates`: view a Euclidean distribution as a distribution on
  `Space d`.
- `Space.distDeriv_distributionOfEuclideanCoordinates_apply`: coordinate-derivative covariance.

## iii. Table of contents

- A. Coordinate transport
- B. Coordinate derivatives

## iv. References

This is neutral distribution infrastructure. It does not introduce a boundary, a jump, or a
physical field equation.
-/

@[expose] public section

open SchwartzMap

namespace Space

noncomputable section

/-!
## A. Coordinate transport
-/

/-- Pull a Schwartz test on `Space d` back along the inverse of its standard orthonormal coordinate
map. -/
def basisCoordinateSchwartz (d : ℕ) :
    SchwartzMap (Space d) ℝ →L[ℝ] SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
    Space.basis.repr.toContinuousLinearEquiv.symm

@[simp]
lemma basisCoordinateSchwartz_apply (d : ℕ) (η : SchwartzMap (Space d) ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    basisCoordinateSchwartz d η x = η (Space.basis.repr.symm x) :=
  rfl

/-- Transport a Euclidean-coordinate distribution to `Space d` by pulling back its test
functions through the standard orthonormal coordinates. -/
def distributionOfEuclideanCoordinates {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (d : ℕ) (u : (EuclideanSpace ℝ (Fin d)) →d[ℝ] F) : (Space d) →d[ℝ] F :=
  u.comp (basisCoordinateSchwartz d)

@[simp]
lemma distributionOfEuclideanCoordinates_apply {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (d : ℕ) (u : (EuclideanSpace ℝ (Fin d)) →d[ℝ] F)
    (η : SchwartzMap (Space d) ℝ) :
    distributionOfEuclideanCoordinates d u η = u (basisCoordinateSchwartz d η) :=
  rfl

/-!
## B. Coordinate derivatives
-/

/-- Transport through the standard orthonormal coordinates intertwines a spatial coordinate
derivative with the corresponding Euclidean directional derivative. -/
lemma distDeriv_distributionOfEuclideanCoordinates_apply {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {d : ℕ} (i : Fin d)
    (u : (EuclideanSpace ℝ (Fin d)) →d[ℝ] F) (η : SchwartzMap (Space d) ℝ) :
    distDeriv i (distributionOfEuclideanCoordinates d u) η =
      Physlib.Distribution.fderivD ℝ u (basisCoordinateSchwartz d η)
        (Space.basis.repr (Space.basis i)) := by
  rw [distDeriv_apply, Physlib.Distribution.fderivD_apply,
    distributionOfEuclideanCoordinates_apply, Physlib.Distribution.fderivD_apply]
  congr 2
  ext x
  simp only [SchwartzMap.evalCLM_apply_apply, SchwartzMap.fderivCLM_apply]
  change fderiv ℝ η (Space.basis.repr.symm x) (Space.basis i) =
    fderiv ℝ (fun y => η (Space.basis.repr.symm y)) x
      (Space.basis.repr (Space.basis i))
  conv_rhs =>
    rw [fderiv_fun_comp _ η.differentiableAt (by fun_prop)]
  simp

end
end Space
