/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Mathematics.Distribution.Heaviside
public import Physlib.SpaceAndTime.Space.DistributionCoordinates
public import Physlib.SpaceAndTime.Space.OrientedAffineHyperplaneDistribution

/-!
# A constant jump across an oriented coordinate hyperplane

## i. Overview

This file realizes a positive-side constant field as a sidewise function distribution across the
standard oriented coordinate hyperplane. Its distributional derivative in the stored positive
normal direction is the corresponding hyperplane-supported sheet with the same coefficient.

The result is deliberately limited to a coordinate hyperplane through the origin and a constant
positive-side value with zero negative-side value. It does not state a derivative formula for
variable side functions, supply one-sided traces, or assume a physical interface law.

## ii. Key results

- `Space.coordinateHeavisideDistribution`: the Euclidean coordinate Heaviside distribution
  transported to `Space`.
- `Space.distDeriv_coordinateHeavisideDistribution`: its coordinate derivative is the transported
  coordinate-hyperplane delta.
- `Space.coordinateHyperplaneSheet_eq_pushforward_const`: the constant sheet agrees with the
  transported generic hyperplane pushforward.
- `OrientedAffineHyperplane.distOfSidewiseFunction_coordinatePositiveConstant`: the independent
  sidewise realization of a constant positive-side field.
- `OrientedAffineHyperplane.distDeriv_coordinatePositiveConstant`: its exact sheet derivative.

## iii. Table of contents

- A. Coordinate Heaviside and sheet distributions
- B. Constant sidewise jump

## iv. References

This is neutral distribution theory. No Maxwell equation, surface source, or finite-sheet premise
is used or derived.
-/

@[expose] public section

open MeasureTheory SchwartzMap

namespace Space

noncomputable section

/-!
## A. Coordinate Heaviside and sheet distributions
-/

/-- The selected-coordinate Euclidean Heaviside distribution transported through the standard
orthonormal coordinates of `Space d.succ`. -/
def coordinateHeavisideDistribution (d : ℕ) (i : Fin d.succ) :
    (Space d.succ) →d[ℝ] ℝ :=
  distributionOfEuclideanCoordinates d.succ
    (Physlib.Distribution.coordinateHeavisideStep d i)

/-- The selected-coordinate Euclidean hyperplane delta transported through the standard
orthonormal coordinates of `Space d.succ`. -/
def coordinateHyperplaneDeltaDistribution (d : ℕ) (i : Fin d.succ) :
    (Space d.succ) →d[ℝ] ℝ :=
  distributionOfEuclideanCoordinates d.succ
    (Physlib.Distribution.coordinateHyperplaneDelta d i)

/-- The transported coordinate Heaviside distribution integrates a spatial test over the strict
positive coordinate half-space. -/
@[simp]
lemma coordinateHeavisideDistribution_apply (d : ℕ) (i : Fin d.succ)
    (η : SchwartzMap (Space d.succ) ℝ) :
    coordinateHeavisideDistribution d i η =
      ∫ x in {x : Space d.succ | 0 < x i}, η x := by
  let s : Set (EuclideanSpace ℝ (Fin d.succ)) := {x | 0 < x i}
  have h := Space.basis.measurePreserving_repr.setIntegral_preimage_emb
    Space.basis.repr.toHomeomorph.measurableEmbedding
    (fun x : EuclideanSpace ℝ (Fin d.succ) => η (Space.basis.repr.symm x)) s
  simpa [coordinateHeavisideDistribution,
    Physlib.Distribution.coordinateHeavisideStep_apply, s] using h.symm

/-- The transported coordinate-hyperplane delta integrates a spatial test over the standard
coordinate parameterization of the selected hyperplane. -/
@[simp]
lemma coordinateHyperplaneDeltaDistribution_apply (d : ℕ) (i : Fin d.succ)
    (η : SchwartzMap (Space d.succ) ℝ) :
    coordinateHyperplaneDeltaDistribution d i η =
      ∫ x : EuclideanSpace ℝ (Fin d),
        η (Space.basis.repr.symm
          (Physlib.Distribution.coordinateHyperplaneEmbedding d i x)) := by
  rw [coordinateHyperplaneDeltaDistribution, distributionOfEuclideanCoordinates_apply,
    Physlib.Distribution.coordinateHyperplaneDelta_apply]
  rfl

/-- A standard spatial basis vector has the selected Euclidean coordinate representation. -/
lemma basis_repr_basis_eq_coordinateNormalEmbedding (d : ℕ) (i : Fin d.succ) :
    Space.basis.repr (Space.basis i) =
      Physlib.Distribution.coordinateNormalEmbedding d i 1 := by
  ext j
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
  · simp [Physlib.Distribution.coordinateNormalEmbedding]
  · simp [Physlib.Distribution.coordinateNormalEmbedding]

/-- The positive coordinate derivative of the transported Heaviside distribution is the
transported coordinate-hyperplane delta. -/
lemma distDeriv_coordinateHeavisideDistribution (d : ℕ) (i : Fin d.succ) :
    distDeriv i (coordinateHeavisideDistribution d i) =
      coordinateHyperplaneDeltaDistribution d i := by
  ext η
  rw [coordinateHeavisideDistribution,
    distDeriv_distributionOfEuclideanCoordinates_apply,
    basis_repr_basis_eq_coordinateNormalEmbedding,
    Physlib.Distribution.fderivD_coordinateHeavisideStep_apply]
  rfl

/-- The `F`-valued positive-coordinate Heaviside distribution with constant value `c`. -/
def coordinatePositiveConstantDistribution {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (d : ℕ) (i : Fin d.succ) (c : F) :
    (Space d.succ) →d[ℝ] F :=
  (coordinateHeavisideDistribution d i).smulRight c

/-- The `F`-valued sheet distribution on a selected coordinate hyperplane with coefficient `c`. -/
def coordinateHyperplaneSheet {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (d : ℕ) (i : Fin d.succ) (c : F) : (Space d.succ) →d[ℝ] F :=
  (coordinateHyperplaneDeltaDistribution d i).smulRight c

/-- A constant-coefficient spatial sheet is the coordinate transport of the generic pushforward
of the constant tangential distribution. This connects the constant-jump construction to the
surface-density API used by later nonconstant sheets. -/
lemma coordinateHyperplaneSheet_eq_pushforward_const {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (d : ℕ) (i : Fin d.succ) (c : F) :
    coordinateHyperplaneSheet d i c =
      distributionOfEuclideanCoordinates d.succ
        (Physlib.Distribution.coordinateHyperplanePushforward d i
          (Physlib.Distribution.const ℝ (EuclideanSpace ℝ (Fin d)) c)) := by
  ext η
  rw [coordinateHyperplaneSheet, ContinuousLinearMap.smulRight_apply,
    coordinateHyperplaneDeltaDistribution_apply,
    distributionOfEuclideanCoordinates_apply,
    Physlib.Distribution.coordinateHyperplanePushforward_apply,
    Physlib.Distribution.const_apply, ← integral_smul_const]
  simp only [Physlib.Distribution.coordinateHyperplaneRestriction_apply,
    basisCoordinateSchwartz_apply]

/-- Differentiating the `F`-valued positive-coordinate constant distribution gives the selected
hyperplane sheet with coefficient `c`. -/
lemma distDeriv_coordinatePositiveConstantDistribution {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (d : ℕ) (i : Fin d.succ) (c : F) :
    distDeriv i (coordinatePositiveConstantDistribution d i c) =
      coordinateHyperplaneSheet d i c := by
  calc
    _ = (distDeriv i (coordinateHeavisideDistribution d i)).smulRight c := by
      ext η
      rw [coordinatePositiveConstantDistribution, distDeriv_apply,
        Physlib.Distribution.fderivD_apply]
      simp only [ContinuousLinearMap.smulRight_apply]
      rw [distDeriv_apply, Physlib.Distribution.fderivD_apply]
      simp
    _ = _ := by
      rw [distDeriv_coordinateHeavisideDistribution]
      rfl

/-!
## B. Constant sidewise jump
-/

namespace OrientedAffineHyperplane

/-- The sidewise constant field which vanishes on the negative side and equals `c` on the
positive side. -/
def coordinatePositiveConstantField {F : Type} [Zero F] {d : ℕ} (c : F) :
    Side → Space d → F
  | .negative => fun _ => 0
  | .positive => fun _ => c

/-- Both ambient extensions of a coordinate positive-side constant field are distribution
bounded. -/
lemma coordinatePositiveConstantField_isDistBounded {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {d : ℕ} (c : F) :
    ∀ side, IsDistBounded (coordinatePositiveConstantField (d := d) c side) := by
  intro side
  cases side
  · change IsDistBounded (fun _ : Space d => (0 : F))
    fun_prop
  · change IsDistBounded (fun _ : Space d => c)
    fun_prop

/-- The independent sidewise-function construction of a coordinate positive-side constant field
is its transported vector-valued Heaviside distribution. -/
lemma distOfSidewiseFunction_coordinatePositiveConstant {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (d : ℕ) (i : Fin d.succ) (c : F) :
    (coordinateHyperplane i).distOfSidewiseFunction
        (coordinatePositiveConstantField c)
        (coordinatePositiveConstantField_isDistBounded c) =
      coordinatePositiveConstantDistribution d i c := by
  ext η
  rw [distOfSidewiseFunction_apply, coordinatePositiveConstantDistribution]
  simp only [coordinatePositiveConstantField,
    ContinuousLinearMap.smulRight_apply]
  rw [coordinateHeavisideDistribution_apply, ← integral_smul_const]
  simp [openHalfSpace]

/-- The positive coordinate derivative of an independently defined constant sidewise field is
the selected hyperplane sheet carrying its positive-minus-negative coefficient `c`. -/
lemma distDeriv_coordinatePositiveConstant {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] (d : ℕ) (i : Fin d.succ) (c : F) :
    distDeriv i
        ((coordinateHyperplane i).distOfSidewiseFunction
          (coordinatePositiveConstantField c)
          (coordinatePositiveConstantField_isDistBounded c)) =
      coordinateHyperplaneSheet d i c := by
  rw [distOfSidewiseFunction_coordinatePositiveConstant,
    distDeriv_coordinatePositiveConstantDistribution]

end OrientedAffineHyperplane

end
end Space
