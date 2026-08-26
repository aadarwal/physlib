/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Electromagnetism.ThreeDimension.BoundaryConditions.OneSidedTrace

/-!
# One-sided planar trace regressions

## i. Overview

The shifted coordinate-plane fixture pins both selected-side approach directions. At logarithmic
parameter zero, the positive approach is one unit above the carrier and the negative approach is
one unit below it.

Two independent constant side extensions then carry deliberately incompatible boundary values.
Each ambient extension satisfies the source-free differential macroscopic Maxwell equations and
has the required one-sided trace, but the pair does not satisfy the source-free planar boundary
predicate. This negative control is important for E4b: genuine trace existence and separate
sidewise Maxwell equations must not silently manufacture jump laws.

## ii. Key results

- `oneSidedTraceRegression_positiveApproach`: the positive approach has the expected coordinate.
- `oneSidedTraceRegression_negativeApproach`: the negative approach has the expected coordinate.
- `oneSidedTraceRegression_negativeExtension_isSourceFreeMaxwell`: the negative extension solves
  the differential source-free equations.
- `oneSidedTraceRegression_positiveExtension_isSourceFreeMaxwell`: the positive extension solves
  the differential source-free equations.
- `oneSidedTraceRegression_not_sourceFreeBoundary`: two regular side traces need not obey a jump
  law.

## iii. Table of contents

- A. Oriented approach fixture
- B. Independent side traces

## iv. References

This is a Physlib-original regression for the E4b trace layer.
-/

@[expose] public section

namespace Electromagnetism
namespace ThreeDimension

open Space Time

noncomputable section

/-! ## A. Oriented approach fixture -/

/-- The positive third-coordinate direction used by the one-sided trace fixture. -/
def oneSidedTraceRegressionNormal : Direction 3 where
  unit := ⟨![0, 0, 1]⟩
  norm := by
    rw [Space.norm_eq]
    simp [Fin.sum_univ_three]

/-- The coordinate plane through `(0, 0, 1)` with normal in the positive third direction. -/
def oneSidedTraceRegressionPlane : OrientedAffineHyperplane 3 where
  point := ⟨![(0 : ℝ), 0, 1]⟩
  normal := oneSidedTraceRegressionNormal

/-- The stored point bundled in the regression plane's carrier. -/
def oneSidedTraceRegressionBoundaryPoint : oneSidedTraceRegressionPlane.carrier :=
  ⟨oneSidedTraceRegressionPlane.point,
    oneSidedTraceRegressionPlane.point_mem_carrier⟩

/-- At logarithmic parameter zero, the positive approach is one unit above the plane. -/
lemma oneSidedTraceRegression_positiveApproach :
    oneSidedTraceRegressionPlane.sideApproachPoint .positive
      oneSidedTraceRegressionBoundaryPoint 0 = ⟨![(0 : ℝ), 0, 2]⟩ := by
  ext i
  fin_cases i <;>
    norm_num [OrientedAffineHyperplane.sideApproachPoint,
      OrientedAffineHyperplane.sideNormalVector,
      OrientedAffineHyperplane.normalVector, oneSidedTraceRegressionPlane,
      oneSidedTraceRegressionNormal, oneSidedTraceRegressionBoundaryPoint]

/-- At logarithmic parameter zero, the negative approach is one unit below the plane. -/
lemma oneSidedTraceRegression_negativeApproach :
    oneSidedTraceRegressionPlane.sideApproachPoint .negative
      oneSidedTraceRegressionBoundaryPoint 0 = ⟨![(0 : ℝ), 0, 0]⟩ := by
  ext i
  fin_cases i <;>
    norm_num [OrientedAffineHyperplane.sideApproachPoint,
      OrientedAffineHyperplane.sideNormalVector,
      OrientedAffineHyperplane.normalVector, oneSidedTraceRegressionPlane,
      oneSidedTraceRegressionNormal, oneSidedTraceRegressionBoundaryPoint]

/-! ## B. Independent side traces -/

/-- A spatially and temporally constant vector field used by the independent-side regression. -/
private def constantVectorField (v : EuclideanSpace ℝ (Fin 3)) :
    Time → Space → EuclideanSpace ℝ (Fin 3) :=
  fun _ _ ↦ v

/-- Any four constant macroscopic fields solve the source-free differential Maxwell equations. -/
private lemma constantVectorFields_isSourceFreeMaxwell
    (E D B H : EuclideanSpace ℝ (Fin 3)) :
    IsSourceFreeMacroscopicMaxwell (constantVectorField E) (constantVectorField D)
      (constantVectorField B) (constantVectorField H) := by
  refine ⟨by fun_prop, by fun_prop, by fun_prop, by fun_prop, ?_, ?_, ?_, ?_⟩
  all_goals intro t x
  all_goals simp [constantVectorField]

/-- The constant electric field used on the negative side. -/
private def negativeElectricField : ElectricField :=
  constantVectorField (WithLp.toLp 2 ![(1 : ℝ), 0, 0])

/-- The constant electric displacement used on the negative side. -/
private def negativeElectricDisplacement : ElectricDisplacementField :=
  constantVectorField (WithLp.toLp 2 ![(0 : ℝ), 0, 3])

/-- The constant magnetic induction used on the negative side. -/
private def negativeMagneticInduction : MagneticInductionField :=
  constantVectorField (WithLp.toLp 2 ![(0 : ℝ), 0, 7])

/-- The constant magnetic field strength used on the negative side. -/
private def negativeMagneticFieldStrength : MagneticFieldStrength :=
  constantVectorField (WithLp.toLp 2 ![(13 : ℝ), 0, 0])

/-- The constant electric field used on the positive side. -/
private def positiveElectricField : ElectricField :=
  constantVectorField (WithLp.toLp 2 ![(2 : ℝ), 0, 0])

/-- The constant electric displacement used on the positive side. -/
private def positiveElectricDisplacement : ElectricDisplacementField :=
  constantVectorField (WithLp.toLp 2 ![(0 : ℝ), 0, 5])

/-- The constant magnetic induction used on the positive side. -/
private def positiveMagneticInduction : MagneticInductionField :=
  constantVectorField (WithLp.toLp 2 ![(0 : ℝ), 0, 11])

/-- The constant magnetic field strength used on the positive side. -/
private def positiveMagneticFieldStrength : MagneticFieldStrength :=
  constantVectorField (WithLp.toLp 2 ![(17 : ℝ), 0, 0])

/-- Constant negative-side fields with a unit tangential electric trace. -/
def oneSidedTraceRegressionNegative :
    PlanarMacroscopicSideFields oneSidedTraceRegressionPlane .negative :=
  PlanarMacroscopicSideFields.ofFields oneSidedTraceRegressionPlane .negative
    negativeElectricField negativeElectricDisplacement negativeMagneticInduction
    negativeMagneticFieldStrength
    (by intros; fun_prop) (by intros; fun_prop) (by intros; fun_prop) (by intros; fun_prop)

/-- Constant positive-side fields whose tangential electric trace differs from the negative side. -/
def oneSidedTraceRegressionPositive :
    PlanarMacroscopicSideFields oneSidedTraceRegressionPlane .positive :=
  PlanarMacroscopicSideFields.ofFields oneSidedTraceRegressionPlane .positive
    positiveElectricField positiveElectricDisplacement positiveMagneticInduction
    positiveMagneticFieldStrength
    (by intros; fun_prop) (by intros; fun_prop) (by intros; fun_prop) (by intros; fun_prop)

/-- The ambient negative-side extension solves source-free differential Maxwell. -/
lemma oneSidedTraceRegression_negativeExtension_isSourceFreeMaxwell :
    IsSourceFreeMacroscopicMaxwell negativeElectricField negativeElectricDisplacement
      negativeMagneticInduction negativeMagneticFieldStrength :=
  constantVectorFields_isSourceFreeMaxwell _ _ _ _

/-- The ambient positive-side extension solves source-free differential Maxwell. -/
lemma oneSidedTraceRegression_positiveExtension_isSourceFreeMaxwell :
    IsSourceFreeMacroscopicMaxwell positiveElectricField positiveElectricDisplacement
      positiveMagneticInduction positiveMagneticFieldStrength :=
  constantVectorFields_isSourceFreeMaxwell _ _ _ _

/-- The deliberately incompatible pair of regular one-sided trace packages. -/
def oneSidedTraceRegressionTwoSided :
    PlanarMacroscopicTwoSidedFields oneSidedTraceRegressionPlane where
  negative := oneSidedTraceRegressionNegative
  positive := oneSidedTraceRegressionPositive

/-- Trace existence on both open sides does not imply the source-free planar jump laws. -/
lemma oneSidedTraceRegression_not_sourceFreeBoundary :
    ¬ IsSourceFreePlanarMacroscopicBoundary
      oneSidedTraceRegressionTwoSided.negative.trace
      oneSidedTraceRegressionTwoSided.positive.trace := by
  intro hBoundary
  have hTangential := hBoundary.tangentialElectricField 0
    oneSidedTraceRegressionBoundaryPoint
  have hCoordinate := congrArg
    (fun v : oneSidedTraceRegressionPlane.tangentSubmodule ↦
      (v : EuclideanSpace ℝ (Fin 3)) 0) hTangential
  norm_num [oneSidedTraceRegressionTwoSided, oneSidedTraceRegressionNegative,
    oneSidedTraceRegressionPositive, PlanarMacroscopicSideFields.ofFields,
    PlanarMacroscopicTrace.ofFields, OrientedAffineHyperplane.projectionToTangent,
    OrientedAffineHyperplane.tangentialProjection,
    OrientedAffineHyperplane.normalComponent,
    OrientedAffineHyperplane.normalVector, oneSidedTraceRegressionPlane,
    oneSidedTraceRegressionNormal] at hCoordinate

end
end ThreeDimension
end Electromagnetism
