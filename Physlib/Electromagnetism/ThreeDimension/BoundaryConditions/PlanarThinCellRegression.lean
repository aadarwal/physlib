/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Mathlib.Analysis.SpecialFunctions.NonIntegrable
public import Physlib.Electromagnetism.ThreeDimension.BoundaryConditions.PlanarThinCell

/-!
# Planar Maxwell thin-cell regressions

## i. Overview

This file instantiates the thin-cell derivation on the coordinate plane `z = 0`. Both bulk sides
carry constant fields, while the carrier carries nonzero free surface charge and current. The
fixture is chosen so the electric-displacement jump is `5` and the magnetic-field-strength jump
produces surface current `(-3, 2, 0)`.

All four finite Maxwell laws are checked on the actual path, face, and volume integrals. The
regularity record then supplies only the genuinely residual limits; the principal and sheet
limits are recovered through the production trace/continuity lemmas.

## ii. Key results

- `planarThinCellRegression_isIntegralMaxwell`: the literal finite integral laws.
- `planarThinCellRegression_regular`: the reduced thin-cell regularity contract.
- `planarThinCellRegression_isBoundary`: all four sourceful jump laws.

## iii. Table of contents

- A. Coordinate geometry and shrinking cells
- B. Constant fields and sources
- C. Literal integral laws
- D. Derived boundary laws

## iv. References

This is a Physlib-original adversarial regression for the E4b derivation.
-/

@[expose] public section

namespace Electromagnetism
namespace ThreeDimension

open Filter Matrix Space Time

noncomputable section

/-! ## A. Coordinate geometry and shrinking cells -/

/-- The positive third-coordinate unit normal. -/
def planarThinCellRegressionNormal : Direction 3 where
  unit := ⟨![0, 0, 1]⟩
  norm := by
    rw [Space.norm_eq]
    simp [Fin.sum_univ_three]

/-- The oriented coordinate plane `z = 0`. -/
def planarThinCellRegressionPlane : OrientedAffineHyperplane 3 where
  point := ⟨![(0 : ℝ), 0, 0]⟩
  normal := planarThinCellRegressionNormal

/-- The origin bundled as a carrier point of the regression plane. -/
def planarThinCellRegressionPoint : planarThinCellRegressionPlane.carrier :=
  ⟨planarThinCellRegressionPlane.point,
    planarThinCellRegressionPlane.point_mem_carrier⟩

/-- The positive first-coordinate unit tangent. -/
def planarThinCellRegressionTangent : planarThinCellRegressionPlane.tangentSubmodule :=
  ⟨WithLp.toLp 2 ![(1 : ℝ), 0, 0], by
    apply (planarThinCellRegressionPlane.mem_tangentSubmodule _).mpr
    change inner ℝ (WithLp.toLp 2 ![(0 : ℝ), 0, 1])
      (WithLp.toLp 2 ![(1 : ℝ), 0, 0]) = 0
    simp [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply]⟩

/-- The positive reciprocal scale used as the principal radius. -/
def planarThinCellRegressionRadius (scale : ℕ) : ℝ :=
  1 / ((scale : ℝ) + 1)

/-- The squared reciprocal scale used as the normal half-thickness. -/
def planarThinCellRegressionHalfThickness (scale : ℕ) : ℝ :=
  planarThinCellRegressionRadius scale ^ 2

/-- Every regression radius is positive. -/
lemma planarThinCellRegressionRadius_pos (scale : ℕ) :
    0 < planarThinCellRegressionRadius scale := by
  rw [planarThinCellRegressionRadius]
  positivity

/-- Every regression half-thickness is positive. -/
lemma planarThinCellRegressionHalfThickness_pos (scale : ℕ) :
    0 < planarThinCellRegressionHalfThickness scale := by
  exact sq_pos_of_pos (planarThinCellRegressionRadius_pos scale)

/-- The regression radius tends to zero. -/
lemma planarThinCellRegressionRadius_tendsto :
    Tendsto planarThinCellRegressionRadius atTop (nhds 0) := by
  change Tendsto (fun scale : ℕ ↦ 1 / ((scale : ℝ) + 1)) atTop (nhds 0)
  exact tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)

/-- The regression half-thickness tends to zero. -/
lemma planarThinCellRegressionHalfThickness_tendsto :
    Tendsto planarThinCellRegressionHalfThickness atTop (nhds 0) := by
  change Tendsto (fun scale ↦ planarThinCellRegressionRadius scale ^ 2) atTop (nhds 0)
  simpa using planarThinCellRegressionRadius_tendsto.pow 2

/-- The regression half-thickness divided by its radius tends to zero. -/
lemma planarThinCellRegressionAspect_tendsto :
    Tendsto (fun scale ↦ planarThinCellRegressionHalfThickness scale /
      planarThinCellRegressionRadius scale) atTop (nhds 0) := by
  convert planarThinCellRegressionRadius_tendsto using 1
  funext scale
  rw [planarThinCellRegressionHalfThickness, pow_two]
  field_simp [(planarThinCellRegressionRadius_pos scale).ne']

/-- The common shrinking scale used by every regression pillbox and loop. -/
def planarThinCellRegressionScale : PlanarThinScale where
  radius := planarThinCellRegressionRadius
  halfThickness := planarThinCellRegressionHalfThickness
  radius_pos := planarThinCellRegressionRadius_pos
  halfThickness_pos := planarThinCellRegressionHalfThickness_pos
  radius_tendsto_zero := planarThinCellRegressionRadius_tendsto
  halfThickness_tendsto_zero := planarThinCellRegressionHalfThickness_tendsto
  halfThickness_div_radius_tendsto_zero := planarThinCellRegressionAspect_tendsto

/-- The regression pillbox uses the first coordinate tangent and its oriented quarter-turn. -/
def planarThinCellRegressionPillbox : PlanarPillboxFamily planarThinCellRegressionPlane where
  toPlanarThinScale := planarThinCellRegressionScale
  tangent := planarThinCellRegressionTangent
  tangent_norm := by
    change ‖WithLp.toLp 2 ![(1 : ℝ), 0, 0]‖ = 1
    rw [EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_three]

/-- The oriented quarter-turn of the first coordinate tangent is the second coordinate tangent. -/
lemma planarThinCellRegression_quarterTurn :
    (planarThinCellRegressionPlane.quarterTurnTangent
      planarThinCellRegressionTangent : EuclideanSpace ℝ (Fin 3)) =
      WithLp.toLp 2 ![(0 : ℝ), 1, 0] := by
  ext i
  fin_cases i <;>
    norm_num [OrientedAffineHyperplane.quarterTurnTangent,
      OrientedAffineHyperplane.normalVector, planarThinCellRegressionPlane,
      planarThinCellRegressionNormal, planarThinCellRegressionTangent,
      crossProduct, basis_repr_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two]

/-- A coordinate vector supported only in the third coordinate is normal to the regression
plane. -/
lemma planarThinCellRegression_pureNormal_eq_smul (value : ℝ) :
    WithLp.toLp 2 ![(0 : ℝ), 0, value] =
      value • planarThinCellRegressionPlane.normalVector := by
  ext i
  fin_cases i <;>
    norm_num [OrientedAffineHyperplane.normalVector,
      planarThinCellRegressionPlane, planarThinCellRegressionNormal,
      basis_repr_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two]

/-- A pure-normal regression vector has zero pairing with every loop surface normal. -/
lemma planarThinCellRegression_pureNormal_pairing (value : ℝ)
    (tangent : planarThinCellRegressionPlane.tangentSubmodule) :
    inner ℝ (WithLp.toLp 2 ![(0 : ℝ), 0, value])
      (planarThinCellRegressionPlane.normalVector ⨯ₑ₃
        (tangent : EuclideanSpace ℝ (Fin 3))) = 0 := by
  rw [planarThinCellRegression_pureNormal_eq_smul, inner_smul_left,
    Space.inner_self_cross, mul_zero]

/-- The regression uses the same shrinking scale for every tangent-indexed thin loop. -/
def planarThinCellRegressionLoop
    (tangent : planarThinCellRegressionPlane.tangentSubmodule) :
    PlanarThinLoopFamily planarThinCellRegressionPlane tangent where
  toPlanarThinScale := planarThinCellRegressionScale

/-- The complete family of regression pillboxes and thin loops. -/
def planarThinCellRegressionCells : PlanarMaxwellThinCells planarThinCellRegressionPlane where
  pillbox := fun _ ↦ planarThinCellRegressionPillbox
  loop := fun _ tangent ↦ planarThinCellRegressionLoop tangent

/-! ## B. Constant fields and sources -/

/-- A spatially and temporally constant vector field. -/
def planarThinCellRegressionConstantVectorField (v : EuclideanSpace ℝ (Fin 3)) :
    Time → Space → EuclideanSpace ℝ (Fin 3) :=
  fun _ _ ↦ v

/-- A constant vector field is spatially continuous at every carrier point. -/
lemma planarThinCellRegressionConstantVectorField_continuousAt
    (v : EuclideanSpace ℝ (Fin 3)) (t : Time)
    (x : planarThinCellRegressionPlane.carrier) :
    ContinuousAt (planarThinCellRegressionConstantVectorField v t) (x : Space) := by
  change ContinuousAt (fun _ : Space ↦ v) x
  fun_prop

/-- Negative-side electric field. -/
def planarThinCellRegressionElectricNegative : ElectricField :=
  planarThinCellRegressionConstantVectorField (WithLp.toLp 2 ![(1 : ℝ), 2, 0])

/-- Positive-side electric field, equal to the negative-side value. -/
def planarThinCellRegressionElectricPositive : ElectricField :=
  planarThinCellRegressionElectricNegative

/-- Negative-side electric displacement. -/
def planarThinCellRegressionDisplacementNegative : ElectricDisplacementField :=
  planarThinCellRegressionConstantVectorField (WithLp.toLp 2 ![(0 : ℝ), 0, 6])

/-- Positive-side electric displacement with normal jump `5`. -/
def planarThinCellRegressionDisplacementPositive : ElectricDisplacementField :=
  planarThinCellRegressionConstantVectorField (WithLp.toLp 2 ![(0 : ℝ), 0, 11])

/-- The common magnetic induction on both sides. -/
def planarThinCellRegressionInduction : MagneticInductionField :=
  planarThinCellRegressionConstantVectorField (WithLp.toLp 2 ![(0 : ℝ), 0, 2])

/-- Negative-side magnetic field strength. -/
def planarThinCellRegressionMagneticNegative : MagneticFieldStrength :=
  planarThinCellRegressionConstantVectorField (WithLp.toLp 2 ![(1 : ℝ), 1, 0])

/-- Positive-side magnetic field strength with tangent jump `(2, 3, 0)`. -/
def planarThinCellRegressionMagneticPositive : MagneticFieldStrength :=
  planarThinCellRegressionConstantVectorField (WithLp.toLp 2 ![(3 : ℝ), 4, 0])

/-- The negative-side macroscopic trace package. -/
def planarThinCellRegressionNegative :
    PlanarMacroscopicSideFields planarThinCellRegressionPlane .negative :=
  PlanarMacroscopicSideFields.ofFields planarThinCellRegressionPlane .negative
    planarThinCellRegressionElectricNegative planarThinCellRegressionDisplacementNegative
    planarThinCellRegressionInduction planarThinCellRegressionMagneticNegative
    (by intros; apply planarThinCellRegressionConstantVectorField_continuousAt)
    (by intros; apply planarThinCellRegressionConstantVectorField_continuousAt)
    (by intros; apply planarThinCellRegressionConstantVectorField_continuousAt)
    (by intros; apply planarThinCellRegressionConstantVectorField_continuousAt)

/-- The positive-side macroscopic trace package. -/
def planarThinCellRegressionPositive :
    PlanarMacroscopicSideFields planarThinCellRegressionPlane .positive :=
  PlanarMacroscopicSideFields.ofFields planarThinCellRegressionPlane .positive
    planarThinCellRegressionElectricPositive planarThinCellRegressionDisplacementPositive
    planarThinCellRegressionInduction planarThinCellRegressionMagneticPositive
    (by
      intro t x
      simpa [planarThinCellRegressionElectricPositive,
        planarThinCellRegressionElectricNegative] using
        planarThinCellRegressionConstantVectorField_continuousAt
          (WithLp.toLp 2 ![(1 : ℝ), 2, 0]) t x)
    (by intros; apply planarThinCellRegressionConstantVectorField_continuousAt)
    (by intros; apply planarThinCellRegressionConstantVectorField_continuousAt)
    (by intros; apply planarThinCellRegressionConstantVectorField_continuousAt)

/-- The two independent constant bulk-side packages. -/
def planarThinCellRegressionFields :
    PlanarMacroscopicTwoSidedFields planarThinCellRegressionPlane where
  negative := planarThinCellRegressionNegative
  positive := planarThinCellRegressionPositive

/-- Zero bulk free charge and current on both open sides. -/
def planarThinCellRegressionBulkSources :
    PlanarMaxwellBulkSources planarThinCellRegressionPlane where
  chargeDensity :=
    { negative := fun _ _ ↦ 0
      positive := fun _ _ ↦ 0 }
  currentDensity :=
    { negative := fun _ _ ↦ 0
      positive := fun _ _ ↦ 0 }

/-- Constant free surface charge equal to the normal displacement jump. -/
def planarThinCellRegressionSurfaceCharge :
    PlanarFreeSurfaceChargeDensity planarThinCellRegressionPlane :=
  fun _ _ ↦ 5

/-- The coordinate vector `(-3, 2, 0)` bundled in the carrier tangent plane. -/
def planarThinCellRegressionSurfaceCurrentVector :
    planarThinCellRegressionPlane.tangentSubmodule :=
  ⟨WithLp.toLp 2 ![(-3 : ℝ), 2, 0], by
    apply (planarThinCellRegressionPlane.mem_tangentSubmodule _).mpr
    change inner ℝ (WithLp.toLp 2 ![(0 : ℝ), 0, 1])
      (WithLp.toLp 2 ![(-3 : ℝ), 2, 0]) = 0
    simp [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply]⟩

/-- Constant free surface current equal to `normal cross (H_positive - H_negative)`. -/
def planarThinCellRegressionSurfaceCurrent :
    PlanarFreeSurfaceCurrentDensity planarThinCellRegressionPlane :=
  fun _ _ ↦ planarThinCellRegressionSurfaceCurrentVector

/-- The regression surface charge is spatially continuous. -/
lemma planarThinCellRegressionSurfaceCharge_continuousAt
    (t : Time) (x : planarThinCellRegressionPlane.carrier) :
    ContinuousAt (planarThinCellRegressionSurfaceCharge t) x := by
  change ContinuousAt (fun _ : planarThinCellRegressionPlane.carrier ↦ (5 : ℝ)) x
  fun_prop

/-- The regression surface current is spatially continuous. -/
lemma planarThinCellRegressionSurfaceCurrent_continuousAt
    (t : Time) (x : planarThinCellRegressionPlane.carrier) :
    ContinuousAt (planarThinCellRegressionSurfaceCurrent t) x := by
  change ContinuousAt
    (fun _ : planarThinCellRegressionPlane.carrier ↦
      planarThinCellRegressionSurfaceCurrentVector) x
  fun_prop

/-! ## C. Literal integral laws -/

/-- A normalized average of a constant over a positive symmetric interval is that constant. -/
lemma planarThinCellRegression_normalizedIntervalAverage_const
    {radius value : ℝ} (hRadius : 0 < radius) :
    normalizedIntervalAverage radius (fun _ ↦ value) = value := by
  rw [normalizedIntervalAverage, intervalIntegral.integral_const]
  field_simp [hRadius.ne']
  ring

/-- A normalized iterated-square average of a constant is that constant. -/
lemma planarThinCellRegression_normalizedSquareAverage_const
    {radius value : ℝ} (hRadius : 0 < radius) :
    normalizedSquareAverage radius (fun _ _ ↦ value) = value := by
  rw [normalizedSquareAverage]
  have hInner : (fun _ : ℝ ↦ normalizedIntervalAverage radius (fun _ : ℝ ↦ value)) =
      fun _ ↦ value := by
    funext u
    exact planarThinCellRegression_normalizedIntervalAverage_const hRadius
  rw [hInner]
  exact planarThinCellRegression_normalizedIntervalAverage_const hRadius

/-- A constant totalized onto the negative open half-interval remains interval-integrable. -/
lemma planarThinCellRegression_negativeHalfIntegrable
    {halfThickness value : ℝ} (hHalfThickness : 0 < halfThickness) :
    IntervalIntegrable (fun w : ℝ ↦ if w < 0 then value else 0)
      MeasureTheory.volume (-halfThickness) 0 := by
  have hConstant : IntervalIntegrable (fun _ : ℝ ↦ value)
      MeasureTheory.volume (-halfThickness) 0 := intervalIntegrable_const
  refine hConstant.congr_uIoo ?_
  intro w hw
  rw [Set.uIoo_of_le (neg_nonpos.mpr hHalfThickness.le)] at hw
  simp [hw.2]

/-- A constant totalized onto the positive open half-interval remains interval-integrable. -/
lemma planarThinCellRegression_positiveHalfIntegrable
    {halfThickness value : ℝ} (hHalfThickness : 0 < halfThickness) :
    IntervalIntegrable (fun w : ℝ ↦ if 0 < w then value else 0)
      MeasureTheory.volume 0 halfThickness := by
  have hConstant : IntervalIntegrable (fun _ : ℝ ↦ value)
      MeasureTheory.volume 0 halfThickness := intervalIntegrable_const
  refine hConstant.congr_uIoo ?_
  intro w hw
  rw [Set.uIoo_of_le hHalfThickness.le] at hw
  simp [hw.1]

/-- Pairing a totalized negative-side constant vector with a fixed normal is integrable. -/
lemma planarThinCellRegression_negativeHalfInnerIntegrable
    {halfThickness : ℝ} (hHalfThickness : 0 < halfThickness)
    (value normal : EuclideanSpace ℝ (Fin 3)) :
    IntervalIntegrable
      (fun w : ℝ ↦ inner ℝ (if w < 0 then value else 0) normal)
      MeasureTheory.volume (-halfThickness) 0 := by
  have hFunction :
      (fun w : ℝ ↦ inner ℝ (if w < 0 then value else 0) normal) =
        fun w ↦ if w < 0 then inner ℝ value normal else 0 := by
    funext w
    by_cases hw : w < 0 <;> simp [hw]
  rw [hFunction]
  exact planarThinCellRegression_negativeHalfIntegrable hHalfThickness

/-- Pairing a totalized positive-side constant vector with a fixed normal is integrable. -/
lemma planarThinCellRegression_positiveHalfInnerIntegrable
    {halfThickness : ℝ} (hHalfThickness : 0 < halfThickness)
    (value normal : EuclideanSpace ℝ (Fin 3)) :
    IntervalIntegrable
      (fun w : ℝ ↦ inner ℝ (if 0 < w then value else 0) normal)
      MeasureTheory.volume 0 halfThickness := by
  have hFunction :
      (fun w : ℝ ↦ inner ℝ (if 0 < w then value else 0) normal) =
        fun w ↦ if 0 < w then inner ℝ value normal else 0 := by
    funext w
    by_cases hw : 0 < w <;> simp [hw]
  rw [hFunction]
  exact planarThinCellRegression_positiveHalfIntegrable hHalfThickness

/-- Two constant open-side pullbacks satisfy the split-normal integrability contract. -/
lemma planarThinCellRegression_splitNormalIntegrable
    {halfThickness negative positive : ℝ} (hHalfThickness : 0 < halfThickness) :
    SplitNormalIntegrable halfThickness
      (fun w ↦ if w < 0 then negative else 0)
      (fun w ↦ if 0 < w then positive else 0) :=
  ⟨planarThinCellRegression_negativeHalfIntegrable hHalfThickness,
    planarThinCellRegression_positiveHalfIntegrable hHalfThickness⟩

/-- Pairings of constant open-side vector pullbacks satisfy split-normal integrability. -/
lemma planarThinCellRegression_splitNormalInnerIntegrable
    {halfThickness : ℝ} (hHalfThickness : 0 < halfThickness)
    (negative positive normal : EuclideanSpace ℝ (Fin 3)) :
    SplitNormalIntegrable halfThickness
      (fun w ↦ inner ℝ (if w < 0 then negative else 0) normal)
      (fun w ↦ inner ℝ (if 0 < w then positive else 0) normal) :=
  ⟨planarThinCellRegression_negativeHalfInnerIntegrable
      hHalfThickness negative normal,
    planarThinCellRegression_positiveHalfInnerIntegrable
      hHalfThickness positive normal⟩

/-- Constant open-side pullbacks satisfy every level of split-rectangle integrability. -/
lemma planarThinCellRegression_splitRectangleIntegrable
    {radius halfThickness negative positive : ℝ}
    (hHalfThickness : 0 < halfThickness) :
    SplitRectangleIntegrable radius halfThickness
      (fun _ w ↦ if w < 0 then negative else 0)
      (fun _ w ↦ if 0 < w then positive else 0) := by
  constructor
  · intro u
    exact planarThinCellRegression_splitNormalIntegrable hHalfThickness
  · exact intervalIntegrable_const

/-- Pairings of constant open-side vector pullbacks satisfy split-rectangle integrability. -/
lemma planarThinCellRegression_splitRectangleInnerIntegrable
    {radius halfThickness : ℝ} (hHalfThickness : 0 < halfThickness)
    (negative positive normal : EuclideanSpace ℝ (Fin 3)) :
    SplitRectangleIntegrable radius halfThickness
      (fun _ w ↦ inner ℝ (if w < 0 then negative else 0) normal)
      (fun _ w ↦ inner ℝ (if 0 < w then positive else 0) normal) := by
  constructor
  · intro u
    exact planarThinCellRegression_splitNormalInnerIntegrable
      hHalfThickness negative positive normal
  · exact intervalIntegrable_const

/-- Constant open-side pullbacks satisfy every level of split-box integrability. -/
lemma planarThinCellRegression_splitBoxIntegrable
    {radius halfThickness negative positive : ℝ}
    (hHalfThickness : 0 < halfThickness) :
    SplitBoxIntegrable radius halfThickness
      (fun _ _ w ↦ if w < 0 then negative else 0)
      (fun _ _ w ↦ if 0 < w then positive else 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro u v
    exact planarThinCellRegression_splitNormalIntegrable hHalfThickness
  · intro u
    exact intervalIntegrable_const
  · exact intervalIntegrable_const

/-- The explicit integrability contract rejects the singular pullback `w⁻¹`; its totalized
interval integral therefore cannot manufacture a regression Maxwell premise. -/
lemma planarThinCellRegression_inv_not_integrable :
    ¬ SymmetricIntervalIntegrable 1 (fun w : ℝ ↦ w⁻¹) := by
  norm_num [SymmetricIntervalIntegrable]

/-- The positive displacement principal-face average is exactly `11`. -/
lemma planarThinCellRegression_displacementPositiveFace
    (t : Time) (x : planarThinCellRegressionPlane.carrier) (scale : ℕ) :
    planarThinCellRegressionPillbox.sideFaceAverage .positive
      planarThinCellRegressionFields.positive.electricDisplacement t x scale = 11 := by
  simpa [PlanarPillboxFamily.sideFaceAverage, planarThinCellRegressionPillbox,
    planarThinCellRegressionScale, planarThinCellRegressionFields,
    planarThinCellRegressionPositive, PlanarMacroscopicSideFields.ofFields,
    planarThinCellRegressionDisplacementPositive,
    planarThinCellRegressionConstantVectorField,
    OrientedAffineHyperplane.restrictFieldToSide,
    OrientedAffineHyperplane.normalVector, planarThinCellRegressionPlane,
    planarThinCellRegressionNormal, PiLp.inner_apply, Fin.sum_univ_three,
    RCLike.inner_apply] using
    (planarThinCellRegression_normalizedSquareAverage_const
      (planarThinCellRegressionRadius_pos scale) (value := (11 : ℝ)))

/-- The negative displacement principal-face average is exactly `6`. -/
lemma planarThinCellRegression_displacementNegativeFace
    (t : Time) (x : planarThinCellRegressionPlane.carrier) (scale : ℕ) :
    planarThinCellRegressionPillbox.sideFaceAverage .negative
      planarThinCellRegressionFields.negative.electricDisplacement t x scale = 6 := by
  simpa [PlanarPillboxFamily.sideFaceAverage, planarThinCellRegressionPillbox,
    planarThinCellRegressionScale, planarThinCellRegressionFields,
    planarThinCellRegressionNegative, PlanarMacroscopicSideFields.ofFields,
    planarThinCellRegressionDisplacementNegative,
    planarThinCellRegressionConstantVectorField,
    OrientedAffineHyperplane.restrictFieldToSide,
    OrientedAffineHyperplane.normalVector, planarThinCellRegressionPlane,
    planarThinCellRegressionNormal, PiLp.inner_apply, Fin.sum_univ_three,
    RCLike.inner_apply] using
    (planarThinCellRegression_normalizedSquareAverage_const
      (planarThinCellRegressionRadius_pos scale) (value := (6 : ℝ)))

/-- Either magnetic-induction principal face has normalized value `2`. -/
lemma planarThinCellRegression_inductionFace
    (side : OrientedAffineHyperplane.Side) (t : Time)
    (x : planarThinCellRegressionPlane.carrier) (scale : ℕ) :
    planarThinCellRegressionPillbox.sideFaceAverage side
      (match side with
        | .negative => planarThinCellRegressionFields.negative.magneticInduction
        | .positive => planarThinCellRegressionFields.positive.magneticInduction)
      t x scale = 2 := by
  cases side <;>
    simpa [PlanarPillboxFamily.sideFaceAverage, planarThinCellRegressionPillbox,
      planarThinCellRegressionScale, planarThinCellRegressionFields,
      planarThinCellRegressionNegative, planarThinCellRegressionPositive,
      PlanarMacroscopicSideFields.ofFields, planarThinCellRegressionInduction,
      planarThinCellRegressionConstantVectorField,
      OrientedAffineHyperplane.restrictFieldToSide,
      OrientedAffineHyperplane.normalVector, planarThinCellRegressionPlane,
      planarThinCellRegressionNormal, PiLp.inner_apply, Fin.sum_univ_three,
      RCLike.inner_apply] using
      (planarThinCellRegression_normalizedSquareAverage_const
        (planarThinCellRegressionRadius_pos scale) (value := (2 : ℝ)))

/-- The surface-charge face average is exactly its constant value `5`. -/
lemma planarThinCellRegression_surfaceChargeFace
    (t : Time) (x : planarThinCellRegressionPlane.carrier) (scale : ℕ) :
    planarThinCellRegressionPillbox.surfaceFaceAverage
      planarThinCellRegressionSurfaceCharge t x scale = 5 := by
  change normalizedSquareAverage (planarThinCellRegressionRadius scale)
    (fun _ _ ↦ (5 : ℝ)) = 5
  exact planarThinCellRegression_normalizedSquareAverage_const
    (planarThinCellRegressionRadius_pos scale)

/-- Either electric principal-edge average is the same constant tangent pairing. -/
lemma planarThinCellRegression_electricLongEdge
    (side : OrientedAffineHyperplane.Side)
    (tangent : planarThinCellRegressionPlane.tangentSubmodule)
    (t : Time) (x : planarThinCellRegressionPlane.carrier) (scale : ℕ) :
    (planarThinCellRegressionLoop tangent).sideLongEdgeAverage side
      (match side with
        | .negative => planarThinCellRegressionFields.negative.electricField
        | .positive => planarThinCellRegressionFields.positive.electricField)
      t x scale =
        inner ℝ (WithLp.toLp 2 ![(1 : ℝ), 2, 0])
          (tangent : EuclideanSpace ℝ (Fin 3)) := by
  cases side <;>
    simpa [PlanarThinLoopFamily.sideLongEdgeAverage, planarThinCellRegressionLoop,
      planarThinCellRegressionScale, planarThinCellRegressionFields,
      planarThinCellRegressionNegative, planarThinCellRegressionPositive,
      PlanarMacroscopicSideFields.ofFields, planarThinCellRegressionElectricNegative,
      planarThinCellRegressionElectricPositive,
      planarThinCellRegressionConstantVectorField,
      OrientedAffineHyperplane.restrictFieldToSide] using
      (planarThinCellRegression_normalizedIntervalAverage_const
        (planarThinCellRegressionRadius_pos scale)
        (value := inner ℝ (WithLp.toLp 2 ![(1 : ℝ), 2, 0])
          (tangent : EuclideanSpace ℝ (Fin 3))))

/-- The negative magnetic principal-edge average is its constant tangent pairing. -/
lemma planarThinCellRegression_magneticNegativeLongEdge
    (tangent : planarThinCellRegressionPlane.tangentSubmodule)
    (t : Time) (x : planarThinCellRegressionPlane.carrier) (scale : ℕ) :
    (planarThinCellRegressionLoop tangent).sideLongEdgeAverage .negative
      planarThinCellRegressionFields.negative.magneticFieldStrength t x scale =
        inner ℝ (WithLp.toLp 2 ![(1 : ℝ), 1, 0])
          (tangent : EuclideanSpace ℝ (Fin 3)) := by
  simpa [PlanarThinLoopFamily.sideLongEdgeAverage, planarThinCellRegressionLoop,
    planarThinCellRegressionScale, planarThinCellRegressionFields,
    planarThinCellRegressionNegative, PlanarMacroscopicSideFields.ofFields,
    planarThinCellRegressionMagneticNegative,
    planarThinCellRegressionConstantVectorField,
    OrientedAffineHyperplane.restrictFieldToSide] using
    (planarThinCellRegression_normalizedIntervalAverage_const
      (planarThinCellRegressionRadius_pos scale)
      (value := inner ℝ (WithLp.toLp 2 ![(1 : ℝ), 1, 0])
        (tangent : EuclideanSpace ℝ (Fin 3))))

/-- The positive magnetic principal-edge average is its constant tangent pairing. -/
lemma planarThinCellRegression_magneticPositiveLongEdge
    (tangent : planarThinCellRegressionPlane.tangentSubmodule)
    (t : Time) (x : planarThinCellRegressionPlane.carrier) (scale : ℕ) :
    (planarThinCellRegressionLoop tangent).sideLongEdgeAverage .positive
      planarThinCellRegressionFields.positive.magneticFieldStrength t x scale =
        inner ℝ (WithLp.toLp 2 ![(3 : ℝ), 4, 0])
          (tangent : EuclideanSpace ℝ (Fin 3)) := by
  simpa [PlanarThinLoopFamily.sideLongEdgeAverage, planarThinCellRegressionLoop,
    planarThinCellRegressionScale, planarThinCellRegressionFields,
    planarThinCellRegressionPositive, PlanarMacroscopicSideFields.ofFields,
    planarThinCellRegressionMagneticPositive,
    planarThinCellRegressionConstantVectorField,
    OrientedAffineHyperplane.restrictFieldToSide] using
    (planarThinCellRegression_normalizedIntervalAverage_const
      (planarThinCellRegressionRadius_pos scale)
      (value := inner ℝ (WithLp.toLp 2 ![(3 : ℝ), 4, 0])
        (tangent : EuclideanSpace ℝ (Fin 3))))

/-- The surface-current line average is its constant oriented tangent pairing. -/
lemma planarThinCellRegression_surfaceCurrentLine
    (tangent : planarThinCellRegressionPlane.tangentSubmodule)
    (t : Time) (x : planarThinCellRegressionPlane.carrier) (scale : ℕ) :
    (planarThinCellRegressionLoop tangent).surfaceLineAverage
      planarThinCellRegressionSurfaceCurrent t x scale =
        inner ℝ
          (planarThinCellRegressionSurfaceCurrentVector : EuclideanSpace ℝ (Fin 3))
          (planarThinCellRegressionPlane.normalVector ⨯ₑ₃
            (tangent : EuclideanSpace ℝ (Fin 3))) := by
  change normalizedIntervalAverage (planarThinCellRegressionRadius scale) (fun _ ↦
    inner ℝ
      (planarThinCellRegressionSurfaceCurrentVector : EuclideanSpace ℝ (Fin 3))
      (planarThinCellRegressionPlane.normalVector ⨯ₑ₃
        (tangent : EuclideanSpace ℝ (Fin 3)))) = _
  exact planarThinCellRegression_normalizedIntervalAverage_const
    (planarThinCellRegressionRadius_pos scale)

/-- The constant magnetic jump and surface current have the required oriented tangent pairing. -/
lemma planarThinCellRegression_magneticJump_pairing
    (tangent : planarThinCellRegressionPlane.tangentSubmodule) :
    inner ℝ (WithLp.toLp 2 ![(3 : ℝ), 4, 0])
          (tangent : EuclideanSpace ℝ (Fin 3)) -
        inner ℝ (WithLp.toLp 2 ![(1 : ℝ), 1, 0])
          (tangent : EuclideanSpace ℝ (Fin 3)) =
      inner ℝ
        (planarThinCellRegressionSurfaceCurrentVector : EuclideanSpace ℝ (Fin 3))
        (planarThinCellRegressionPlane.normalVector ⨯ₑ₃
          (tangent : EuclideanSpace ℝ (Fin 3))) := by
  simp [planarThinCellRegressionSurfaceCurrentVector,
    OrientedAffineHyperplane.normalVector, planarThinCellRegressionPlane,
    planarThinCellRegressionNormal, crossProduct, basis_repr_apply,
    PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  ring

/-- The two short-edge electric circulations cancel exactly. -/
lemma planarThinCellRegression_electricShortEdges
    (tangent : planarThinCellRegressionPlane.tangentSubmodule)
    (t : Time) (x : planarThinCellRegressionPlane.carrier) (scale : ℕ) :
    (planarThinCellRegressionLoop tangent).shortEdgeAverage
      planarThinCellRegressionFields.electricFieldFamily t x scale = 0 := by
  simp [PlanarThinLoopFamily.shortEdgeAverage, planarThinCellRegressionLoop,
    planarThinCellRegressionScale, PlanarMacroscopicTwoSidedFields.electricFieldFamily,
    planarThinCellRegressionFields, planarThinCellRegressionNegative,
    planarThinCellRegressionPositive, PlanarMacroscopicSideFields.ofFields,
    planarThinCellRegressionElectricNegative, planarThinCellRegressionElectricPositive,
    planarThinCellRegressionConstantVectorField,
    OrientedAffineHyperplane.restrictFieldToSide,
    OrientedAffineHyperplane.negativeSideSample,
    OrientedAffineHyperplane.positiveSideSample,
    OrientedAffineHyperplane.normalVector, planarThinCellRegressionPlane,
    planarThinCellRegressionNormal, PiLp.inner_apply, Fin.sum_univ_three,
    RCLike.inner_apply]

/-- The two short-edge magnetic-field-strength circulations cancel exactly. -/
lemma planarThinCellRegression_magneticShortEdges
    (tangent : planarThinCellRegressionPlane.tangentSubmodule)
    (t : Time) (x : planarThinCellRegressionPlane.carrier) (scale : ℕ) :
    (planarThinCellRegressionLoop tangent).shortEdgeAverage
      planarThinCellRegressionFields.magneticFieldStrengthFamily t x scale = 0 := by
  simp [PlanarThinLoopFamily.shortEdgeAverage, planarThinCellRegressionLoop,
    planarThinCellRegressionScale,
    PlanarMacroscopicTwoSidedFields.magneticFieldStrengthFamily,
    planarThinCellRegressionFields, planarThinCellRegressionNegative,
    planarThinCellRegressionPositive, PlanarMacroscopicSideFields.ofFields,
    planarThinCellRegressionMagneticNegative, planarThinCellRegressionMagneticPositive,
    planarThinCellRegressionConstantVectorField,
    OrientedAffineHyperplane.restrictFieldToSide,
    OrientedAffineHyperplane.negativeSideSample,
    OrientedAffineHyperplane.positiveSideSample,
    OrientedAffineHyperplane.normalVector, planarThinCellRegressionPlane,
    planarThinCellRegressionNormal, PiLp.inner_apply, Fin.sum_univ_three,
    RCLike.inner_apply]

/-- The pure-normal displacement has zero flux through every lateral pillbox face. -/
lemma planarThinCellRegression_displacementLateral
    (t : Time) (x : planarThinCellRegressionPlane.carrier) (scale : ℕ) :
    planarThinCellRegressionPillbox.lateralFaceAverage
      planarThinCellRegressionFields.electricDisplacementFamily t x scale = 0 := by
  simp [PlanarPillboxFamily.lateralFaceAverage, planarThinCellRegressionPillbox,
    planarThinCellRegressionScale,
    PlanarMacroscopicTwoSidedFields.electricDisplacementFamily,
    planarThinCellRegressionFields, planarThinCellRegressionNegative,
    planarThinCellRegressionPositive, PlanarMacroscopicSideFields.ofFields,
    planarThinCellRegressionDisplacementNegative,
    planarThinCellRegressionDisplacementPositive,
    planarThinCellRegressionConstantVectorField,
    OrientedAffineHyperplane.restrictFieldToSide,
    OrientedAffineHyperplane.negativeSideSample,
    OrientedAffineHyperplane.positiveSideSample,
    planarThinCellRegressionTangent,
    PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply]

/-- The pure-normal induction has zero flux through every lateral pillbox face. -/
lemma planarThinCellRegression_inductionLateral
    (t : Time) (x : planarThinCellRegressionPlane.carrier) (scale : ℕ) :
    planarThinCellRegressionPillbox.lateralFaceAverage
      planarThinCellRegressionFields.magneticInductionFamily t x scale = 0 := by
  simp [PlanarPillboxFamily.lateralFaceAverage, planarThinCellRegressionPillbox,
    planarThinCellRegressionScale, PlanarMacroscopicTwoSidedFields.magneticInductionFamily,
    planarThinCellRegressionFields, planarThinCellRegressionNegative,
    planarThinCellRegressionPositive, PlanarMacroscopicSideFields.ofFields,
    planarThinCellRegressionInduction, planarThinCellRegressionConstantVectorField,
    OrientedAffineHyperplane.restrictFieldToSide,
    OrientedAffineHyperplane.negativeSideSample,
    OrientedAffineHyperplane.positiveSideSample,
    planarThinCellRegressionTangent,
    PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply]

/-- The zero bulk charge has zero normalized pillbox volume. -/
lemma planarThinCellRegression_chargeVolume
    (t : Time) (x : planarThinCellRegressionPlane.carrier) (scale : ℕ) :
    planarThinCellRegressionPillbox.volumeAverage
      planarThinCellRegressionBulkSources.chargeDensity t x scale = 0 := by
  simp [PlanarPillboxFamily.volumeAverage, planarThinCellRegressionPillbox,
    planarThinCellRegressionScale, planarThinCellRegressionBulkSources,
    splitNormalIntegral, OrientedAffineHyperplane.negativeSideSample,
    OrientedAffineHyperplane.positiveSideSample]

/-- The zero bulk current has zero normalized thin-loop flux. -/
lemma planarThinCellRegression_currentFlux
    (tangent : planarThinCellRegressionPlane.tangentSubmodule)
    (t : Time) (x : planarThinCellRegressionPlane.carrier) (scale : ℕ) :
    (planarThinCellRegressionLoop tangent).spanningSurfaceAverage
      planarThinCellRegressionBulkSources.currentDensity t x scale = 0 := by
  simp [PlanarThinLoopFamily.spanningSurfaceAverage, planarThinCellRegressionLoop,
    planarThinCellRegressionScale, planarThinCellRegressionBulkSources,
    splitNormalIntegral, OrientedAffineHyperplane.negativeSideSample,
    OrientedAffineHyperplane.positiveSideSample]

/-- The pure-normal, time-constant induction has zero flux through every thin-loop surface. -/
lemma planarThinCellRegression_inductionFlux
    (tangent : planarThinCellRegressionPlane.tangentSubmodule)
    (t : Time) (x : planarThinCellRegressionPlane.carrier) (scale : ℕ) :
    (planarThinCellRegressionLoop tangent).spanningSurfaceAverage
      planarThinCellRegressionFields.magneticInductionFamily t x scale = 0 := by
  have hNegative (u w : ℝ) :
      inner ℝ
        (planarThinCellRegressionPlane.negativeSideSample
          planarThinCellRegressionFields.magneticInductionFamily.negative
          t x (u • tangent) w)
        (planarThinCellRegressionPlane.normalVector ⨯ₑ₃
          (tangent : EuclideanSpace ℝ (Fin 3))) = 0 := by
    simp only [OrientedAffineHyperplane.negativeSideSample]
    split
    · change inner ℝ (WithLp.toLp 2 ![(0 : ℝ), 0, 2])
        (planarThinCellRegressionPlane.normalVector ⨯ₑ₃
          (tangent : EuclideanSpace ℝ (Fin 3))) = 0
      exact planarThinCellRegression_pureNormal_pairing 2 tangent
    · simp
  have hPositive (u w : ℝ) :
      inner ℝ
        (planarThinCellRegressionPlane.positiveSideSample
          planarThinCellRegressionFields.magneticInductionFamily.positive
          t x (u • tangent) w)
        (planarThinCellRegressionPlane.normalVector ⨯ₑ₃
          (tangent : EuclideanSpace ℝ (Fin 3))) = 0 := by
    simp only [OrientedAffineHyperplane.positiveSideSample]
    split
    · change inner ℝ (WithLp.toLp 2 ![(0 : ℝ), 0, 2])
        (planarThinCellRegressionPlane.normalVector ⨯ₑ₃
          (tangent : EuclideanSpace ℝ (Fin 3))) = 0
      exact planarThinCellRegression_pureNormal_pairing 2 tangent
    · simp
  rw [PlanarThinLoopFamily.spanningSurfaceAverage]
  simp_rw [hNegative, hPositive]
  simp [splitNormalIntegral]

/-- The pure-normal, time-constant displacement has zero flux through every thin-loop surface. -/
lemma planarThinCellRegression_displacementFlux
    (tangent : planarThinCellRegressionPlane.tangentSubmodule)
    (t : Time) (x : planarThinCellRegressionPlane.carrier) (scale : ℕ) :
    (planarThinCellRegressionLoop tangent).spanningSurfaceAverage
      planarThinCellRegressionFields.electricDisplacementFamily t x scale = 0 := by
  have hNegative (u w : ℝ) :
      inner ℝ
        (planarThinCellRegressionPlane.negativeSideSample
          planarThinCellRegressionFields.electricDisplacementFamily.negative
          t x (u • tangent) w)
        (planarThinCellRegressionPlane.normalVector ⨯ₑ₃
          (tangent : EuclideanSpace ℝ (Fin 3))) = 0 := by
    simp only [OrientedAffineHyperplane.negativeSideSample]
    split
    · change inner ℝ (WithLp.toLp 2 ![(0 : ℝ), 0, 6])
        (planarThinCellRegressionPlane.normalVector ⨯ₑ₃
          (tangent : EuclideanSpace ℝ (Fin 3))) = 0
      exact planarThinCellRegression_pureNormal_pairing 6 tangent
    · simp
  have hPositive (u w : ℝ) :
      inner ℝ
        (planarThinCellRegressionPlane.positiveSideSample
          planarThinCellRegressionFields.electricDisplacementFamily.positive
          t x (u • tangent) w)
        (planarThinCellRegressionPlane.normalVector ⨯ₑ₃
          (tangent : EuclideanSpace ℝ (Fin 3))) = 0 := by
    simp only [OrientedAffineHyperplane.positiveSideSample]
    split
    · change inner ℝ (WithLp.toLp 2 ![(0 : ℝ), 0, 11])
        (planarThinCellRegressionPlane.normalVector ⨯ₑ₃
          (tangent : EuclideanSpace ℝ (Fin 3))) = 0
      exact planarThinCellRegression_pureNormal_pairing 11 tangent
    · simp
  rw [PlanarThinLoopFamily.spanningSurfaceAverage]
  simp_rw [hNegative, hPositive]
  simp [splitNormalIntegral]

/-- Both actual regression fluxes are time-constant, so their witnessed derivatives vanish. -/
def planarThinCellRegressionFluxRates :
    PlanarMaxwellThinCellFluxRates
      planarThinCellRegressionFields planarThinCellRegressionCells where
  magneticFluxRate := fun _ _ _ _ ↦ 0
  magneticFlux_hasDerivAt := by
    intro t x tangent scale
    have hFlux :
        (fun s : ℝ ↦ (planarThinCellRegressionCells.loop x tangent).spanningSurfaceAverage
          planarThinCellRegressionFields.magneticInductionFamily
          (Time.toRealCLE.symm s) x scale) = fun _ ↦ 0 := by
      funext s
      exact planarThinCellRegression_inductionFlux tangent
        (Time.toRealCLE.symm s) x scale
    rw [hFlux]
    exact hasDerivAt_const (Time.toRealCLE t) 0
  electricFluxRate := fun _ _ _ _ ↦ 0
  electricFlux_hasDerivAt := by
    intro t x tangent scale
    have hFlux :
        (fun s : ℝ ↦ (planarThinCellRegressionCells.loop x tangent).spanningSurfaceAverage
          planarThinCellRegressionFields.electricDisplacementFamily
          (Time.toRealCLE.symm s) x scale) = fun _ ↦ 0 := by
      funext s
      exact planarThinCellRegression_displacementFlux tangent
        (Time.toRealCLE.symm s) x scale
    rw [hFlux]
    exact hasDerivAt_const (Time.toRealCLE t) 0

/-- Both electric-Gauss principal faces have genuinely integrable constant pullbacks. -/
lemma planarThinCellRegression_electricGaussPrincipal_integrable
    (t : Time) (x : planarThinCellRegressionPlane.carrier) (scale : ℕ) :
    planarThinCellRegressionPillbox.SideFaceIntegrable .positive
        planarThinCellRegressionFields.positive.electricDisplacement t x scale ∧
      planarThinCellRegressionPillbox.SideFaceIntegrable .negative
        planarThinCellRegressionFields.negative.electricDisplacement t x scale := by
  simp [PlanarPillboxFamily.SideFaceIntegrable, IteratedSquareIntegrable,
    SymmetricIntervalIntegrable, planarThinCellRegressionPillbox,
    planarThinCellRegressionScale, planarThinCellRegressionFields,
    planarThinCellRegressionPositive, planarThinCellRegressionNegative,
    PlanarMacroscopicSideFields.ofFields,
    planarThinCellRegressionDisplacementPositive,
    planarThinCellRegressionDisplacementNegative,
    planarThinCellRegressionConstantVectorField,
    OrientedAffineHyperplane.restrictFieldToSide]

/-- The four electric-displacement lateral-face pullbacks are genuinely integrable. -/
lemma planarThinCellRegression_electricGaussLateral_integrable
    (t : Time) (x : planarThinCellRegressionPlane.carrier) (scale : ℕ) :
    planarThinCellRegressionPillbox.LateralFacesIntegrable
      planarThinCellRegressionFields.electricDisplacementFamily t x scale := by
  simp [PlanarPillboxFamily.LateralFacesIntegrable, SplitRectangleIntegrable,
    SplitNormalIntegrable, SymmetricIntervalIntegrable,
    planarThinCellRegressionPillbox, planarThinCellRegressionScale,
    PlanarMacroscopicTwoSidedFields.electricDisplacementFamily,
    planarThinCellRegressionFields, planarThinCellRegressionPositive,
    planarThinCellRegressionNegative, PlanarMacroscopicSideFields.ofFields,
    planarThinCellRegressionDisplacementPositive,
    planarThinCellRegressionDisplacementNegative,
    planarThinCellRegressionConstantVectorField,
    OrientedAffineHyperplane.restrictFieldToSide,
    OrientedAffineHyperplane.negativeSideSample,
    OrientedAffineHyperplane.positiveSideSample]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact planarThinCellRegression_negativeHalfInnerIntegrable
      (planarThinCellRegressionHalfThickness_pos scale) _ _
  · exact planarThinCellRegression_positiveHalfInnerIntegrable
      (planarThinCellRegressionHalfThickness_pos scale) _ _
  · exact planarThinCellRegression_negativeHalfInnerIntegrable
      (planarThinCellRegressionHalfThickness_pos scale) _ _
  · exact planarThinCellRegression_positiveHalfInnerIntegrable
      (planarThinCellRegressionHalfThickness_pos scale) _ _

/-- The zero bulk-charge pullback is genuinely integrable on every regression pillbox. -/
lemma planarThinCellRegression_electricGaussVolume_integrable
    (t : Time) (x : planarThinCellRegressionPlane.carrier) (scale : ℕ) :
    planarThinCellRegressionPillbox.VolumeIntegrable
      planarThinCellRegressionBulkSources.chargeDensity t x scale := by
  simp [PlanarPillboxFamily.VolumeIntegrable, SplitBoxIntegrable,
    SplitNormalIntegrable, SymmetricIntervalIntegrable,
    planarThinCellRegressionPillbox, planarThinCellRegressionScale,
    planarThinCellRegressionBulkSources,
    OrientedAffineHyperplane.negativeSideSample,
    OrientedAffineHyperplane.positiveSideSample]

/-- The constant free-surface-charge pullback is genuinely integrable. -/
lemma planarThinCellRegression_electricGaussSheet_integrable
    (t : Time) (x : planarThinCellRegressionPlane.carrier) (scale : ℕ) :
    planarThinCellRegressionPillbox.SurfaceFaceIntegrable
      planarThinCellRegressionSurfaceCharge t x scale := by
  simp [PlanarPillboxFamily.SurfaceFaceIntegrable, IteratedSquareIntegrable,
    SymmetricIntervalIntegrable, planarThinCellRegressionPillbox,
    planarThinCellRegressionScale, planarThinCellRegressionSurfaceCharge]

/-- All magnetic-Gauss face pullbacks are genuinely integrable. -/
lemma planarThinCellRegression_magneticGauss_integrable
    (t : Time) (x : planarThinCellRegressionPlane.carrier) (scale : ℕ) :
    planarThinCellRegressionPillbox.SideFaceIntegrable .positive
        planarThinCellRegressionFields.positive.magneticInduction t x scale ∧
      planarThinCellRegressionPillbox.SideFaceIntegrable .negative
          planarThinCellRegressionFields.negative.magneticInduction t x scale ∧
        planarThinCellRegressionPillbox.LateralFacesIntegrable
          planarThinCellRegressionFields.magneticInductionFamily t x scale := by
  have hPrincipal :
      planarThinCellRegressionPillbox.SideFaceIntegrable .positive
          planarThinCellRegressionFields.positive.magneticInduction t x scale ∧
        planarThinCellRegressionPillbox.SideFaceIntegrable .negative
          planarThinCellRegressionFields.negative.magneticInduction t x scale := by
    simp [PlanarPillboxFamily.SideFaceIntegrable, IteratedSquareIntegrable,
      SymmetricIntervalIntegrable, planarThinCellRegressionPillbox,
      planarThinCellRegressionScale, planarThinCellRegressionFields,
      planarThinCellRegressionPositive, planarThinCellRegressionNegative,
      PlanarMacroscopicSideFields.ofFields, planarThinCellRegressionInduction,
      planarThinCellRegressionConstantVectorField,
      OrientedAffineHyperplane.restrictFieldToSide]
  refine ⟨hPrincipal.1, hPrincipal.2, ?_⟩
  simp [PlanarPillboxFamily.LateralFacesIntegrable, SplitRectangleIntegrable,
    SplitNormalIntegrable, SymmetricIntervalIntegrable,
    planarThinCellRegressionPillbox, planarThinCellRegressionScale,
    PlanarMacroscopicTwoSidedFields.magneticInductionFamily,
    planarThinCellRegressionFields, planarThinCellRegressionPositive,
    planarThinCellRegressionNegative, PlanarMacroscopicSideFields.ofFields,
    planarThinCellRegressionInduction, planarThinCellRegressionConstantVectorField,
    OrientedAffineHyperplane.restrictFieldToSide,
    OrientedAffineHyperplane.negativeSideSample,
    OrientedAffineHyperplane.positiveSideSample]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    first
    | exact planarThinCellRegression_negativeHalfInnerIntegrable
        (planarThinCellRegressionHalfThickness_pos scale) _ _
    | exact planarThinCellRegression_positiveHalfInnerIntegrable
        (planarThinCellRegressionHalfThickness_pos scale) _ _

/-- Every electric-field edge pullback in the regression thin loop is integrable. -/
lemma planarThinCellRegression_faradayCirculation_integrable
    (t : Time) (x : planarThinCellRegressionPlane.carrier)
    (tangent : planarThinCellRegressionPlane.tangentSubmodule) (scale : ℕ) :
    (planarThinCellRegressionLoop tangent).SideLongEdgeIntegrable .positive
        planarThinCellRegressionFields.positive.electricField t x scale ∧
      (planarThinCellRegressionLoop tangent).SideLongEdgeIntegrable .negative
          planarThinCellRegressionFields.negative.electricField t x scale ∧
        (planarThinCellRegressionLoop tangent).ShortEdgesIntegrable
          planarThinCellRegressionFields.electricFieldFamily t x scale := by
  have hLong :
      (planarThinCellRegressionLoop tangent).SideLongEdgeIntegrable .positive
          planarThinCellRegressionFields.positive.electricField t x scale ∧
        (planarThinCellRegressionLoop tangent).SideLongEdgeIntegrable .negative
          planarThinCellRegressionFields.negative.electricField t x scale := by
    simp [PlanarThinLoopFamily.SideLongEdgeIntegrable,
      SymmetricIntervalIntegrable, planarThinCellRegressionLoop,
      planarThinCellRegressionScale, planarThinCellRegressionFields,
      planarThinCellRegressionPositive, planarThinCellRegressionNegative,
      PlanarMacroscopicSideFields.ofFields,
      planarThinCellRegressionElectricPositive,
      planarThinCellRegressionElectricNegative,
      planarThinCellRegressionConstantVectorField,
      OrientedAffineHyperplane.restrictFieldToSide]
  refine ⟨hLong.1, hLong.2, ?_⟩
  change SplitNormalIntegrable (planarThinCellRegressionHalfThickness scale)
      (fun w ↦ inner ℝ (if w < 0 then WithLp.toLp 2 ![(1 : ℝ), 2, 0] else 0)
        planarThinCellRegressionPlane.normalVector)
      (fun w ↦ inner ℝ (if 0 < w then WithLp.toLp 2 ![(1 : ℝ), 2, 0] else 0)
        planarThinCellRegressionPlane.normalVector) ∧
    SplitNormalIntegrable (planarThinCellRegressionHalfThickness scale)
      (fun w ↦ inner ℝ (if w < 0 then WithLp.toLp 2 ![(1 : ℝ), 2, 0] else 0)
        planarThinCellRegressionPlane.normalVector)
      (fun w ↦ inner ℝ (if 0 < w then WithLp.toLp 2 ![(1 : ℝ), 2, 0] else 0)
        planarThinCellRegressionPlane.normalVector)
  constructor <;>
    exact planarThinCellRegression_splitNormalInnerIntegrable
      (planarThinCellRegressionHalfThickness_pos scale) _ _ _

/-- The magnetic-flux pullbacks in every regression thin loop are integrable. -/
lemma planarThinCellRegression_faradayFlux_integrable
    (t : Time) (x : planarThinCellRegressionPlane.carrier)
    (tangent : planarThinCellRegressionPlane.tangentSubmodule) (scale : ℕ) :
    (planarThinCellRegressionLoop tangent).SpanningSurfaceIntegrable
      planarThinCellRegressionFields.magneticInductionFamily t x scale := by
  simp [PlanarThinLoopFamily.SpanningSurfaceIntegrable,
    SplitRectangleIntegrable, SplitNormalIntegrable,
    SymmetricIntervalIntegrable, planarThinCellRegressionLoop,
    planarThinCellRegressionScale,
    PlanarMacroscopicTwoSidedFields.magneticInductionFamily,
    planarThinCellRegressionFields, planarThinCellRegressionPositive,
    planarThinCellRegressionNegative, PlanarMacroscopicSideFields.ofFields,
    planarThinCellRegressionInduction, planarThinCellRegressionConstantVectorField,
    OrientedAffineHyperplane.restrictFieldToSide,
    OrientedAffineHyperplane.negativeSideSample,
    OrientedAffineHyperplane.positiveSideSample]
  exact planarThinCellRegression_splitNormalInnerIntegrable
    (planarThinCellRegressionHalfThickness_pos scale) _ _ _

/-- Every magnetic-field-strength edge pullback in the regression thin loop is integrable. -/
lemma planarThinCellRegression_ampereCirculation_integrable
    (t : Time) (x : planarThinCellRegressionPlane.carrier)
    (tangent : planarThinCellRegressionPlane.tangentSubmodule) (scale : ℕ) :
    (planarThinCellRegressionLoop tangent).SideLongEdgeIntegrable .positive
        planarThinCellRegressionFields.positive.magneticFieldStrength t x scale ∧
      (planarThinCellRegressionLoop tangent).SideLongEdgeIntegrable .negative
          planarThinCellRegressionFields.negative.magneticFieldStrength t x scale ∧
        (planarThinCellRegressionLoop tangent).ShortEdgesIntegrable
          planarThinCellRegressionFields.magneticFieldStrengthFamily t x scale := by
  have hLong :
      (planarThinCellRegressionLoop tangent).SideLongEdgeIntegrable .positive
          planarThinCellRegressionFields.positive.magneticFieldStrength t x scale ∧
        (planarThinCellRegressionLoop tangent).SideLongEdgeIntegrable .negative
          planarThinCellRegressionFields.negative.magneticFieldStrength t x scale := by
    simp [PlanarThinLoopFamily.SideLongEdgeIntegrable,
      SymmetricIntervalIntegrable, planarThinCellRegressionLoop,
      planarThinCellRegressionScale, planarThinCellRegressionFields,
      planarThinCellRegressionPositive, planarThinCellRegressionNegative,
      PlanarMacroscopicSideFields.ofFields,
      planarThinCellRegressionMagneticPositive,
      planarThinCellRegressionMagneticNegative,
      planarThinCellRegressionConstantVectorField,
      OrientedAffineHyperplane.restrictFieldToSide]
  refine ⟨hLong.1, hLong.2, ?_⟩
  change SplitNormalIntegrable (planarThinCellRegressionHalfThickness scale)
      (fun w ↦ inner ℝ (if w < 0 then WithLp.toLp 2 ![(1 : ℝ), 1, 0] else 0)
        planarThinCellRegressionPlane.normalVector)
      (fun w ↦ inner ℝ (if 0 < w then WithLp.toLp 2 ![(3 : ℝ), 4, 0] else 0)
        planarThinCellRegressionPlane.normalVector) ∧
    SplitNormalIntegrable (planarThinCellRegressionHalfThickness scale)
      (fun w ↦ inner ℝ (if w < 0 then WithLp.toLp 2 ![(1 : ℝ), 1, 0] else 0)
        planarThinCellRegressionPlane.normalVector)
      (fun w ↦ inner ℝ (if 0 < w then WithLp.toLp 2 ![(3 : ℝ), 4, 0] else 0)
        planarThinCellRegressionPlane.normalVector)
  constructor <;>
    exact planarThinCellRegression_splitNormalInnerIntegrable
      (planarThinCellRegressionHalfThickness_pos scale) _ _ _

/-- The bulk-current and electric-flux pullbacks in every regression thin loop are integrable. -/
lemma planarThinCellRegression_ampereFlux_integrable
    (t : Time) (x : planarThinCellRegressionPlane.carrier)
    (tangent : planarThinCellRegressionPlane.tangentSubmodule) (scale : ℕ) :
    (planarThinCellRegressionLoop tangent).SpanningSurfaceIntegrable
        planarThinCellRegressionBulkSources.currentDensity t x scale ∧
      (planarThinCellRegressionLoop tangent).SpanningSurfaceIntegrable
        planarThinCellRegressionFields.electricDisplacementFamily t x scale := by
  constructor
  · simp [PlanarThinLoopFamily.SpanningSurfaceIntegrable,
      SplitRectangleIntegrable, SplitNormalIntegrable,
      SymmetricIntervalIntegrable, planarThinCellRegressionLoop,
      planarThinCellRegressionScale, planarThinCellRegressionBulkSources,
      OrientedAffineHyperplane.negativeSideSample,
      OrientedAffineHyperplane.positiveSideSample]
  · simp [PlanarThinLoopFamily.SpanningSurfaceIntegrable,
      SplitRectangleIntegrable, SplitNormalIntegrable,
      SymmetricIntervalIntegrable, planarThinCellRegressionLoop,
      planarThinCellRegressionScale,
      PlanarMacroscopicTwoSidedFields.electricDisplacementFamily,
      planarThinCellRegressionFields, planarThinCellRegressionPositive,
      planarThinCellRegressionNegative, PlanarMacroscopicSideFields.ofFields,
      planarThinCellRegressionDisplacementPositive,
      planarThinCellRegressionDisplacementNegative,
      planarThinCellRegressionConstantVectorField,
      OrientedAffineHyperplane.restrictFieldToSide,
      OrientedAffineHyperplane.negativeSideSample,
      OrientedAffineHyperplane.positiveSideSample]
    exact planarThinCellRegression_splitNormalInnerIntegrable
      (planarThinCellRegressionHalfThickness_pos scale) _ _ _

/-- The constant surface-current line pullback is integrable. -/
lemma planarThinCellRegression_ampereSheet_integrable
    (t : Time) (x : planarThinCellRegressionPlane.carrier)
    (tangent : planarThinCellRegressionPlane.tangentSubmodule) (scale : ℕ) :
    (planarThinCellRegressionLoop tangent).SurfaceLineIntegrable
      planarThinCellRegressionSurfaceCurrent t x scale := by
  simp [PlanarThinLoopFamily.SurfaceLineIntegrable,
    SymmetricIntervalIntegrable, planarThinCellRegressionLoop,
    planarThinCellRegressionScale, planarThinCellRegressionSurfaceCurrent]

/-- Every literal path, face, and volume integral in the regression Maxwell laws has an explicit
integrability witness. -/
lemma planarThinCellRegressionIntegrable :
    ArePlanarMaxwellThinCellTermsIntegrable planarThinCellRegressionFields
      planarThinCellRegressionBulkSources planarThinCellRegressionSurfaceCharge
      planarThinCellRegressionSurfaceCurrent planarThinCellRegressionCells where
  electricGaussPrincipal := planarThinCellRegression_electricGaussPrincipal_integrable
  electricGaussLateral := planarThinCellRegression_electricGaussLateral_integrable
  electricGaussVolume := planarThinCellRegression_electricGaussVolume_integrable
  electricGaussSheet := planarThinCellRegression_electricGaussSheet_integrable
  magneticGauss := planarThinCellRegression_magneticGauss_integrable
  faradayCirculation := planarThinCellRegression_faradayCirculation_integrable
  faradayFlux := planarThinCellRegression_faradayFlux_integrable
  ampereCirculation := planarThinCellRegression_ampereCirculation_integrable
  ampereFlux := planarThinCellRegression_ampereFlux_integrable
  ampereSheet := planarThinCellRegression_ampereSheet_integrable

/-- The coordinate fixture satisfies all four literal finite integral Maxwell laws. Every term is
the actual path, face, or volume integral displayed by the production predicate. -/
lemma planarThinCellRegression_isIntegralMaxwell :
    IsPlanarIntegralMacroscopicMaxwell planarThinCellRegressionFields
      planarThinCellRegressionBulkSources planarThinCellRegressionSurfaceCharge
      planarThinCellRegressionSurfaceCurrent planarThinCellRegressionCells
      planarThinCellRegressionFluxRates where
  integrable := planarThinCellRegressionIntegrable
  electricGauss := by
    intro t x scale
    simp only [planarThinCellRegressionCells]
    rw [planarThinCellRegression_displacementPositiveFace,
      planarThinCellRegression_displacementNegativeFace,
      planarThinCellRegression_displacementLateral,
      planarThinCellRegression_chargeVolume,
      planarThinCellRegression_surfaceChargeFace]
    norm_num
  magneticGauss := by
    intro t x scale
    simp only [planarThinCellRegressionCells]
    rw [planarThinCellRegression_inductionFace .positive,
      planarThinCellRegression_inductionFace .negative,
      planarThinCellRegression_inductionLateral]
    norm_num
  faraday := by
    intro t x tangent scale
    simp only [planarThinCellRegressionCells]
    rw [planarThinCellRegression_electricLongEdge .positive,
      planarThinCellRegression_electricLongEdge .negative,
      planarThinCellRegression_electricShortEdges]
    change _ = -(0 : ℝ)
    ring
  ampereMaxwell := by
    intro t x tangent scale
    simp only [planarThinCellRegressionCells]
    rw [planarThinCellRegression_magneticPositiveLongEdge,
      planarThinCellRegression_magneticNegativeLongEdge,
      planarThinCellRegression_magneticShortEdges,
      planarThinCellRegression_currentFlux,
      planarThinCellRegression_surfaceCurrentLine]
    change _ = 0 + 0 + _
    simpa using planarThinCellRegression_magneticJump_pairing tangent

/-! ## D. Derived boundary laws -/

/-- The coordinate fixture satisfies the reduced regularity contract. Principal and sheet limits
are deliberately absent here: the production theorem derives them from the stored traces and
source continuity. -/
lemma planarThinCellRegression_regular :
    HasPlanarMaxwellThinCellRegularity
      planarThinCellRegression_isIntegralMaxwell where
  surfaceCharge_continuousAt := planarThinCellRegressionSurfaceCharge_continuousAt
  surfaceCurrent_continuousAt := planarThinCellRegressionSurfaceCurrent_continuousAt
  electricGauss_lateral := by
    intro t x
    have hSequence :
        (fun scale ↦ (planarThinCellRegressionCells.pillbox x).lateralFaceAverage
          planarThinCellRegressionFields.electricDisplacementFamily t x scale) =
          fun _ ↦ 0 := by
      funext scale
      simpa only [planarThinCellRegressionCells] using
        planarThinCellRegression_displacementLateral t x scale
    rw [hSequence]
    exact tendsto_const_nhds
  electricGauss_bulk := by
    intro t x
    have hSequence :
        (fun scale ↦ (planarThinCellRegressionCells.pillbox x).volumeAverage
          planarThinCellRegressionBulkSources.chargeDensity t x scale) =
          fun _ ↦ 0 := by
      funext scale
      simpa only [planarThinCellRegressionCells] using
        planarThinCellRegression_chargeVolume t x scale
    rw [hSequence]
    exact tendsto_const_nhds
  magneticGauss_lateral := by
    intro t x
    have hSequence :
        (fun scale ↦ (planarThinCellRegressionCells.pillbox x).lateralFaceAverage
          planarThinCellRegressionFields.magneticInductionFamily t x scale) =
          fun _ ↦ 0 := by
      funext scale
      simpa only [planarThinCellRegressionCells] using
        planarThinCellRegression_inductionLateral t x scale
    rw [hSequence]
    exact tendsto_const_nhds
  faraday_shortEdges := by
    intro t x tangent
    have hSequence :
        (fun scale ↦ (planarThinCellRegressionCells.loop x tangent).shortEdgeAverage
          planarThinCellRegressionFields.electricFieldFamily t x scale) =
          fun _ ↦ 0 := by
      funext scale
      simpa only [planarThinCellRegressionCells] using
        planarThinCellRegression_electricShortEdges tangent t x scale
    rw [hSequence]
    exact tendsto_const_nhds
  faraday_magneticFluxRate := by
    intro t x tangent
    change Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (nhds 0)
    exact tendsto_const_nhds
  ampere_shortEdges := by
    intro t x tangent
    have hSequence :
        (fun scale ↦ (planarThinCellRegressionCells.loop x tangent).shortEdgeAverage
          planarThinCellRegressionFields.magneticFieldStrengthFamily t x scale) =
          fun _ ↦ 0 := by
      funext scale
      simpa only [planarThinCellRegressionCells] using
        planarThinCellRegression_magneticShortEdges tangent t x scale
    rw [hSequence]
    exact tendsto_const_nhds
  ampere_bulkCurrent := by
    intro t x tangent
    have hSequence :
        (fun scale ↦ (planarThinCellRegressionCells.loop x tangent).spanningSurfaceAverage
          planarThinCellRegressionBulkSources.currentDensity t x scale) =
          fun _ ↦ 0 := by
      funext scale
      simpa only [planarThinCellRegressionCells] using
        planarThinCellRegression_currentFlux tangent t x scale
    rw [hSequence]
    exact tendsto_const_nhds
  ampere_electricFluxRate := by
    intro t x tangent
    change Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (nhds 0)
    exact tendsto_const_nhds

/-- The actual integral laws and reduced regularity derive all four sourceful planar Maxwell jump
laws for the coordinate fixture. -/
lemma planarThinCellRegression_isBoundary :
    IsPlanarMacroscopicBoundary
      planarThinCellRegressionFields.negative.trace
      planarThinCellRegressionFields.positive.trace
      planarThinCellRegressionSurfaceCharge
      planarThinCellRegressionSurfaceCurrent :=
  planarThinCellRegression_regular.isPlanarMacroscopicBoundary

/-- The derived electric-displacement jump has the pinned positive-minus-negative sign `11 - 6 =
5`. -/
lemma planarThinCellRegression_derivedDisplacementJump
    (t : Time) (x : planarThinCellRegressionPlane.carrier) :
    planarThinCellRegressionPlane.normalComponent
          (planarThinCellRegressionFields.positive.trace.electricDisplacement t x) -
        planarThinCellRegressionPlane.normalComponent
          (planarThinCellRegressionFields.negative.trace.electricDisplacement t x) = 5 := by
  simpa [planarThinCellRegressionSurfaceCharge] using
    planarThinCellRegression_regular.normalElectricDisplacement t x

/-- The derived Ampere jump has the pinned orientation `n cross (H_positive - H_negative) =
(-3, 2, 0)`. -/
lemma planarThinCellRegression_derivedMagneticJump
    (t : Time) (x : planarThinCellRegressionPlane.carrier) :
    planarThinCellRegressionPlane.normalVector ⨯ₑ₃
        (planarThinCellRegressionFields.positive.trace.magneticFieldStrength t x -
          planarThinCellRegressionFields.negative.trace.magneticFieldStrength t x) =
      WithLp.toLp 2 ![(-3 : ℝ), 2, 0] := by
  simpa [planarThinCellRegressionSurfaceCurrent,
    planarThinCellRegressionSurfaceCurrentVector] using
    planarThinCellRegression_regular.tangentialMagneticFieldStrength t x

end
end ThreeDimension
end Electromagnetism
