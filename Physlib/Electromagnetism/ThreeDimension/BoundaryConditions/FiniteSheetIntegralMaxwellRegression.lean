/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Electromagnetism.ThreeDimension.BoundaryConditions.FiniteSheetIntegralMaxwell
public import Physlib.Electromagnetism.ThreeDimension.BoundaryConditions.OneSidedTraceRegression
public import Physlib.Electromagnetism.ThreeDimension.BoundaryConditions.PlanarThinCellRegression

/-!
# Finite-sheet integral Maxwell regressions

## i. Overview

The positive fixture reuses the coordinate thin cells but starts one level earlier: two ambient
constant fields independently satisfy differential Maxwell on the two sides, while the finite
carrier premise identifies their nonzero displacement and magnetic-strength jumps with literal
surface charge and current integrals. The production bridge then reconstructs the integral laws.

The hostile fixture keeps the separately valid sidewise differential Maxwell fields from the
one-sided-trace regression but supplies zero sheet sources. Its retained carrier terms are
nonzero, so the sheet premise and the corresponding source-free integral laws fail. This pins the
fact that sidewise smooth Maxwell equations alone do not manufacture an interface law.

## ii. Key results

- `planarFiniteSheetRegression_premise`: the nonzero-sheet coordinate fixture satisfies the
  explicit finite-sheet premise.
- `planarFiniteSheetRegression_integralMaxwell_from_premise`: the production bridge reconstructs
  its four finite integral laws.
- `planarFiniteSheetHostile_not_premise`: incompatible source-free side fields violate the
  finite-sheet identification.
- `planarFiniteSheetHostile_not_integralMaxwell`: the corresponding literal integral law fails.

## iii. Table of contents

- A. Positive sidewise Maxwell fixture
- B. Positive finite-sheet premise
- C. Reconstructed integral and boundary laws
- D. Hostile source-free control

## iv. References

These are Physlib-original E4b regressions. They exercise the explicit premise separating
classical sidewise differential Maxwell equations from a finite sheet-source model.
-/

@[expose] public section

open Matrix MeasureTheory
open scoped Interval

namespace Electromagnetism
namespace ThreeDimension

open Space Time

noncomputable section

/-! ## A. Positive sidewise Maxwell fixture -/

/-- The coordinate thin-cell fields, regarded as two independent source-free ambient Maxwell
extensions. -/
def planarFiniteSheetRegressionSidewise :
    PlanarSidewiseMacroscopicMaxwell planarThinCellRegressionPlane where
  negativeElectricField := planarThinCellRegressionElectricNegative
  negativeElectricDisplacement := planarThinCellRegressionDisplacementNegative
  negativeMagneticInduction := planarThinCellRegressionInduction
  negativeMagneticFieldStrength := planarThinCellRegressionMagneticNegative
  negativeChargeDensity := 0
  negativeCurrentDensity := 0
  negativeMaxwell := by
    change IsSourceFreeMacroscopicMaxwell
      (planarThinCellRegressionConstantVectorField (WithLp.toLp 2 ![(1 : ℝ), 2, 0]))
      (planarThinCellRegressionConstantVectorField (WithLp.toLp 2 ![(0 : ℝ), 0, 6]))
      (planarThinCellRegressionConstantVectorField (WithLp.toLp 2 ![(0 : ℝ), 0, 2]))
      (planarThinCellRegressionConstantVectorField (WithLp.toLp 2 ![(1 : ℝ), 1, 0]))
    simpa only [show planarThinCellRegressionConstantVectorField =
      oneSidedTraceRegressionConstantVectorField by rfl] using
      oneSidedTraceRegression_constantFields_isSourceFreeMaxwell
        (WithLp.toLp 2 ![(1 : ℝ), 2, 0]) (WithLp.toLp 2 ![(0 : ℝ), 0, 6])
        (WithLp.toLp 2 ![(0 : ℝ), 0, 2]) (WithLp.toLp 2 ![(1 : ℝ), 1, 0])
  positiveElectricField := planarThinCellRegressionElectricPositive
  positiveElectricDisplacement := planarThinCellRegressionDisplacementPositive
  positiveMagneticInduction := planarThinCellRegressionInduction
  positiveMagneticFieldStrength := planarThinCellRegressionMagneticPositive
  positiveChargeDensity := 0
  positiveCurrentDensity := 0
  positiveMaxwell := by
    change IsSourceFreeMacroscopicMaxwell
      (planarThinCellRegressionConstantVectorField (WithLp.toLp 2 ![(1 : ℝ), 2, 0]))
      (planarThinCellRegressionConstantVectorField (WithLp.toLp 2 ![(0 : ℝ), 0, 11]))
      (planarThinCellRegressionConstantVectorField (WithLp.toLp 2 ![(0 : ℝ), 0, 2]))
      (planarThinCellRegressionConstantVectorField (WithLp.toLp 2 ![(3 : ℝ), 4, 0]))
    simpa only [show planarThinCellRegressionConstantVectorField =
      oneSidedTraceRegressionConstantVectorField by rfl] using
      oneSidedTraceRegression_constantFields_isSourceFreeMaxwell
        (WithLp.toLp 2 ![(1 : ℝ), 2, 0]) (WithLp.toLp 2 ![(0 : ℝ), 0, 11])
        (WithLp.toLp 2 ![(0 : ℝ), 0, 2]) (WithLp.toLp 2 ![(3 : ℝ), 4, 0])

/-- The fields selected from the positive sidewise fixture are exactly the existing coordinate
thin-cell fields. -/
lemma planarFiniteSheetRegressionSidewise_fields :
    planarFiniteSheetRegressionSidewise.fields = planarThinCellRegressionFields := by
  rfl

/-- The bulk sources selected from the positive sidewise fixture are exactly the existing zero
bulk sources. -/
lemma planarFiniteSheetRegressionSidewise_sources :
    planarFiniteSheetRegressionSidewise.sources = planarThinCellRegressionBulkSources := by
  rfl

/-- The existing constant-flux-rate witness, typed over the sidewise fixture. -/
def planarFiniteSheetRegressionFluxRates :
    PlanarMaxwellThinCellFluxRates planarFiniteSheetRegressionSidewise.fields
      planarThinCellRegressionCells :=
  planarThinCellRegressionFluxRates

/-! ## B. Positive finite-sheet premise -/

/-- Two constant ambient vector fields have the local split-pillbox regularity and lateral
integrability required by the finite-sheet premise. -/
private lemma planarFiniteSheetRegression_constantDivergenceRegularity
    (negativeValue positiveValue : EuclideanSpace ℝ (Fin 3))
    (t : Time) (x : planarThinCellRegressionPlane.carrier) (scale : ℕ) :
    ∃ negativeExceptionalSet positiveExceptionalSet : Set (Fin 3 → ℝ),
      planarThinCellRegressionPillbox.DivergenceRegularity
        (planarThinCellRegressionConstantVectorField negativeValue)
        (planarThinCellRegressionConstantVectorField positiveValue)
        t x scale negativeExceptionalSet positiveExceptionalSet := by
  refine ⟨∅, ∅, ⟨⟨?_, ?_⟩, ?_, ?_⟩⟩
  · apply AffineBoxDivergenceRegularity.of_differentiable
    · change Differentiable ℝ (fun _ : Space ↦ negativeValue)
      fun_prop
    · have hDivergence (y : Space) :
          (∇ ⬝ planarThinCellRegressionConstantVectorField negativeValue t) y = 0 := by
        change (∇ ⬝ (fun _ : Space ↦ negativeValue)) y = 0
        simp
      simp_rw [hDivergence, zero_mul]
      exact continuous_const.continuousOn.integrableOn_compact isCompact_Icc
  · apply AffineBoxDivergenceRegularity.of_differentiable
    · change Differentiable ℝ (fun _ : Space ↦ positiveValue)
      fun_prop
    · have hDivergence (y : Space) :
          (∇ ⬝ planarThinCellRegressionConstantVectorField positiveValue t) y = 0 := by
        change (∇ ⬝ (fun _ : Space ↦ positiveValue)) y = 0
        simp
      simp_rw [hDivergence, zero_mul]
      exact continuous_const.continuousOn.integrableOn_compact isCompact_Icc
  · unfold planarThinCellRegressionConstantVectorField
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      change IntervalIntegrable (fun _ : ℝ ↦ _) volume _ _ <;>
      exact intervalIntegrable_const
  · unfold planarThinCellRegressionConstantVectorField
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      change IntervalIntegrable (fun _ : ℝ ↦ _) volume _ _ <;>
      exact intervalIntegrable_const

/-- Two constant ambient vector fields have the local split-rectangle Stokes regularity required
by the finite-sheet premise. -/
private lemma planarFiniteSheetRegression_constantStokesRegularity
    (negativeValue positiveValue : EuclideanSpace ℝ (Fin 3))
    (t : Time) (x : planarThinCellRegressionPlane.carrier)
    (tangent : planarThinCellRegressionPlane.tangentSubmodule) (scale : ℕ) :
    PlanarSplitRectangleStokesRegularity
      (planarThinCellRegressionConstantVectorField negativeValue t)
      (planarThinCellRegressionConstantVectorField positiveValue t) (x : Space)
      (planarThinCellRegressionLoop tangent).tangentDirection
      (planarThinCellRegressionLoop tangent).normalDirection
      ((planarThinCellRegressionLoop tangent).radius scale)
      ((planarThinCellRegressionLoop tangent).halfThickness scale) := by
  constructor
  · apply PlanarRectangleStokesRegularity.of_differentiable
    · change Differentiable ℝ (fun _ : Space ↦ negativeValue)
      fun_prop
    · have hCurl (y : Space) :
          (∇ ⨯ planarThinCellRegressionConstantVectorField negativeValue t) y = 0 := by
        change (∇ ⨯ (fun _ : Space ↦ negativeValue)) y = 0
        simp
      simp_rw [hCurl, inner_zero_left]
      exact continuous_const.continuousOn.integrableOn_compact
        (isCompact_uIcc.prod isCompact_uIcc)
  · apply PlanarRectangleStokesRegularity.of_differentiable
    · change Differentiable ℝ (fun _ : Space ↦ positiveValue)
      fun_prop
    · have hCurl (y : Space) :
          (∇ ⨯ planarThinCellRegressionConstantVectorField positiveValue t) y = 0 := by
        change (∇ ⨯ (fun _ : Space ↦ positiveValue)) y = 0
        simp
      simp_rw [hCurl, inner_zero_left]
      exact continuous_const.continuousOn.integrableOn_compact
        (isCompact_uIcc.prod isCompact_uIcc)

/-- The normalized retained face term of two constant fields is their normal-component
difference. -/
private lemma planarFiniteSheetRegression_constantCarrierFace
    (negativeValue positiveValue : EuclideanSpace ℝ (Fin 3))
    (t : Time) (x : planarThinCellRegressionPlane.carrier) (scale : ℕ) :
    ((2 * planarThinCellRegressionPillbox.radius scale) ^ 2)⁻¹ *
        affineSplitBoxCarrierJump
          (planarThinCellRegressionConstantVectorField negativeValue t)
          (planarThinCellRegressionConstantVectorField positiveValue t) (x : Space)
          planarThinCellRegressionPillbox.tangentDirection
          planarThinCellRegressionPillbox.quarterTurnDirection
          planarThinCellRegressionPillbox.normalDirection
          (planarThinCellRegressionPillbox.radius scale) =
      inner ℝ (positiveValue - negativeValue)
        planarThinCellRegressionPlane.normalVector := by
  unfold affineSplitBoxCarrierJump planarThinCellRegressionConstantVectorField
  rw [planarThinCellRegressionPillbox.principalFaceNormal]
  simp_rw [intervalIntegral.integral_const]
  rw [inner_sub_left]
  have hRadius : planarThinCellRegressionPillbox.radius scale ≠ 0 := by
    simpa [planarThinCellRegressionPillbox, planarThinCellRegressionScale] using
      (planarThinCellRegressionRadius_pos scale).ne'
  have hTwoRadius : 2 * planarThinCellRegressionPillbox.radius scale ≠ 0 :=
    mul_ne_zero (by norm_num) hRadius
  have hCancel : ((2 * planarThinCellRegressionPillbox.radius scale) ^ 2)⁻¹ *
      (2 * planarThinCellRegressionPillbox.radius scale) ^ 2 = 1 :=
    inv_mul_cancel₀ (pow_ne_zero 2 hTwoRadius)
  calc
    _ = (((2 * planarThinCellRegressionPillbox.radius scale) ^ 2)⁻¹ *
          (2 * planarThinCellRegressionPillbox.radius scale) ^ 2) *
        (inner ℝ positiveValue planarThinCellRegressionPlane.normalVector -
          inner ℝ negativeValue planarThinCellRegressionPlane.normalVector) := by ring
    _ = _ := by rw [hCancel, one_mul]

/-- The normalized retained carrier-line term of two constant fields is their difference paired
with the loop tangent. -/
private lemma planarFiniteSheetRegression_constantCarrierLine
    (negativeValue positiveValue : EuclideanSpace ℝ (Fin 3))
    (t : Time) (x : planarThinCellRegressionPlane.carrier)
    (tangent : planarThinCellRegressionPlane.tangentSubmodule) (scale : ℕ) :
    (2 * (planarThinCellRegressionLoop tangent).radius scale)⁻¹ *
        planarSplitRectangleCarrierJump
          (planarThinCellRegressionConstantVectorField negativeValue t)
          (planarThinCellRegressionConstantVectorField positiveValue t) (x : Space)
          (planarThinCellRegressionLoop tangent).tangentDirection
          (planarThinCellRegressionLoop tangent).normalDirection
          ((planarThinCellRegressionLoop tangent).radius scale) =
      inner ℝ (positiveValue - negativeValue)
        (tangent : EuclideanSpace ℝ (Fin 3)) := by
  unfold planarSplitRectangleCarrierJump planarThinCellRegressionConstantVectorField
  simp_rw [intervalIntegral.integral_const]
  rw [show basis.repr (planarThinCellRegressionLoop tangent).tangentDirection =
    (tangent : EuclideanSpace ℝ (Fin 3)) by rfl, inner_sub_left]
  have hRadius : (planarThinCellRegressionLoop tangent).radius scale ≠ 0 := by
    simpa [planarThinCellRegressionLoop, planarThinCellRegressionScale] using
      (planarThinCellRegressionRadius_pos scale).ne'
  have hTwoRadius : 2 * (planarThinCellRegressionLoop tangent).radius scale ≠ 0 :=
    mul_ne_zero (by norm_num) hRadius
  have hCancel : (2 * (planarThinCellRegressionLoop tangent).radius scale)⁻¹ *
      (2 * (planarThinCellRegressionLoop tangent).radius scale) = 1 :=
    inv_mul_cancel₀ hTwoRadius
  calc
    _ = ((2 * (planarThinCellRegressionLoop tangent).radius scale)⁻¹ *
          (2 * (planarThinCellRegressionLoop tangent).radius scale)) *
        (inner ℝ positiveValue (tangent : EuclideanSpace ℝ (Fin 3)) -
          inner ℝ negativeValue (tangent : EuclideanSpace ℝ (Fin 3))) := by ring
    _ = _ := by rw [hCancel, one_mul]

/-- Zero scalar density is integrable at the two iterated levels of either pillbox half-volume. -/
private lemma planarFiniteSheetRegression_zeroHalfVolumeIntegrable
    (t : Time) (x : planarThinCellRegressionPlane.carrier) (scale : ℕ)
    (lower upper : ℝ) :
    planarThinCellRegressionPillbox.AmbientHalfVolumeIntegrable
      (0 : ChargeDensity) t x scale lower upper := by
  refine ⟨?_, ?_⟩
  · intro u
    simp only [Pi.zero_apply, intervalIntegral.integral_zero]
    exact intervalIntegrable_const
  · simp only [Pi.zero_apply, intervalIntegral.integral_zero]
    exact intervalIntegrable_const

/-- Zero vector density is integrable at both iterated levels of either thin-loop half-surface. -/
private lemma planarFiniteSheetRegression_zeroHalfSpanningIntegrable
    (t : Time) (x : planarThinCellRegressionPlane.carrier)
    (tangent : planarThinCellRegressionPlane.tangentSubmodule) (scale : ℕ)
    (lower upper : ℝ) :
    (planarThinCellRegressionLoop tangent).AmbientHalfSpanningIntegrable
      (fun _ _ ↦ (0 : EuclideanSpace ℝ (Fin 3))) t x scale lower upper := by
  constructor
  · intro u
    simp only [inner_zero_left]
    exact intervalIntegrable_const
  · simp only [inner_zero_left, intervalIntegral.integral_zero]
    exact intervalIntegrable_const

/-- The nonzero-sheet coordinate fixture satisfies the explicit finite-sheet premise. -/
lemma planarFiniteSheetRegression_premise :
    HasPlanarFiniteSheetMaxwellPremise planarFiniteSheetRegressionSidewise
      planarThinCellRegressionSurfaceCharge planarThinCellRegressionSurfaceCurrent
      planarThinCellRegressionCells planarFiniteSheetRegressionFluxRates where
  integrable := by
    simpa only [planarFiniteSheetRegressionSidewise_fields,
      planarFiniteSheetRegressionSidewise_sources] using planarThinCellRegressionIntegrable
  electricDisplacementDivergence := by
    intro t x scale
    exact planarFiniteSheetRegression_constantDivergenceRegularity
      (WithLp.toLp 2 ![(0 : ℝ), 0, 6]) (WithLp.toLp 2 ![(0 : ℝ), 0, 11]) t x scale
  negativeChargeVolume := by
    intro t x scale
    exact planarFiniteSheetRegression_zeroHalfVolumeIntegrable t x scale
      (-planarThinCellRegressionPillbox.halfThickness scale) 0
  positiveChargeVolume := by
    intro t x scale
    exact planarFiniteSheetRegression_zeroHalfVolumeIntegrable t x scale 0
      (planarThinCellRegressionPillbox.halfThickness scale)
  electricCarrierFace := by
    intro t x scale
    calc
      _ = inner ℝ
          (WithLp.toLp 2 ![(0 : ℝ), 0, 11] - WithLp.toLp 2 ![(0 : ℝ), 0, 6])
          planarThinCellRegressionPlane.normalVector :=
        planarFiniteSheetRegression_constantCarrierFace _ _ t x scale
      _ = 5 := by
        norm_num [OrientedAffineHyperplane.normalVector, planarThinCellRegressionPlane,
          planarThinCellRegressionNormal, PiLp.inner_apply, Fin.sum_univ_three,
          RCLike.inner_apply, Matrix.cons_val_two]
      _ = _ := (planarThinCellRegression_surfaceChargeFace t x scale).symm
  magneticInductionDivergence := by
    intro t x scale
    exact planarFiniteSheetRegression_constantDivergenceRegularity
      (WithLp.toLp 2 ![(0 : ℝ), 0, 2]) (WithLp.toLp 2 ![(0 : ℝ), 0, 2]) t x scale
  magneticCarrierFace := by
    intro t x scale
    calc
      _ = inner ℝ
          (WithLp.toLp 2 ![(0 : ℝ), 0, 2] - WithLp.toLp 2 ![(0 : ℝ), 0, 2])
          planarThinCellRegressionPlane.normalVector :=
        planarFiniteSheetRegression_constantCarrierFace _ _ t x scale
      _ = 0 := by simp
  electricFieldStokes := by
    intro t x tangent scale
    exact planarFiniteSheetRegression_constantStokesRegularity
      (WithLp.toLp 2 ![(1 : ℝ), 2, 0]) (WithLp.toLp 2 ![(1 : ℝ), 2, 0])
      t x tangent scale
  electricCarrierLine := by
    intro t x tangent scale
    calc
      _ = inner ℝ
          (WithLp.toLp 2 ![(1 : ℝ), 2, 0] - WithLp.toLp 2 ![(1 : ℝ), 2, 0])
          (tangent : EuclideanSpace ℝ (Fin 3)) :=
        planarFiniteSheetRegression_constantCarrierLine _ _ t x tangent scale
      _ = 0 := by simp
  negativeMagneticRateFlux := by
    intro t x tangent scale
    simpa [planarFiniteSheetRegressionSidewise, planarThinCellRegressionInduction,
      planarThinCellRegressionConstantVectorField, planarThinCellRegressionCells] using
      planarFiniteSheetRegression_zeroHalfSpanningIntegrable t x tangent scale
        (-(planarThinCellRegressionLoop tangent).halfThickness scale) 0
  positiveMagneticRateFlux := by
    intro t x tangent scale
    simpa [planarFiniteSheetRegressionSidewise, planarThinCellRegressionInduction,
      planarThinCellRegressionConstantVectorField, planarThinCellRegressionCells] using
      planarFiniteSheetRegression_zeroHalfSpanningIntegrable t x tangent scale 0
        ((planarThinCellRegressionLoop tangent).halfThickness scale)
  magneticFluxInterchange := by
    intro t x tangent scale
    simp [planarFiniteSheetRegressionFluxRates, planarThinCellRegressionFluxRates,
      planarFiniteSheetRegressionSidewise, planarThinCellRegressionInduction,
      planarThinCellRegressionConstantVectorField, planarSplitRectangleFlux]
  magneticFieldStokes := by
    intro t x tangent scale
    exact planarFiniteSheetRegression_constantStokesRegularity
      (WithLp.toLp 2 ![(1 : ℝ), 1, 0]) (WithLp.toLp 2 ![(3 : ℝ), 4, 0])
      t x tangent scale
  negativeCurrentFlux := by
    intro t x tangent scale
    exact planarFiniteSheetRegression_zeroHalfSpanningIntegrable t x tangent scale
      (-(planarThinCellRegressionLoop tangent).halfThickness scale) 0
  positiveCurrentFlux := by
    intro t x tangent scale
    exact planarFiniteSheetRegression_zeroHalfSpanningIntegrable t x tangent scale 0
      ((planarThinCellRegressionLoop tangent).halfThickness scale)
  negativeElectricRateFlux := by
    intro t x tangent scale
    simpa [planarFiniteSheetRegressionSidewise,
      planarThinCellRegressionDisplacementNegative,
      planarThinCellRegressionConstantVectorField, planarThinCellRegressionCells] using
      planarFiniteSheetRegression_zeroHalfSpanningIntegrable t x tangent scale
        (-(planarThinCellRegressionLoop tangent).halfThickness scale) 0
  positiveElectricRateFlux := by
    intro t x tangent scale
    simpa [planarFiniteSheetRegressionSidewise,
      planarThinCellRegressionDisplacementPositive,
      planarThinCellRegressionConstantVectorField, planarThinCellRegressionCells] using
      planarFiniteSheetRegression_zeroHalfSpanningIntegrable t x tangent scale 0
        ((planarThinCellRegressionLoop tangent).halfThickness scale)
  electricFluxInterchange := by
    intro t x tangent scale
    simp [planarFiniteSheetRegressionFluxRates, planarThinCellRegressionFluxRates,
      planarFiniteSheetRegressionSidewise, planarThinCellRegressionDisplacementNegative,
      planarThinCellRegressionDisplacementPositive,
      planarThinCellRegressionConstantVectorField, planarSplitRectangleFlux]
  magneticCarrierLine := by
    intro t x tangent scale
    calc
      _ = inner ℝ
          (WithLp.toLp 2 ![(3 : ℝ), 4, 0] - WithLp.toLp 2 ![(1 : ℝ), 1, 0])
          (tangent : EuclideanSpace ℝ (Fin 3)) :=
        planarFiniteSheetRegression_constantCarrierLine _ _ t x tangent scale
      _ = inner ℝ
          (planarThinCellRegressionSurfaceCurrentVector : EuclideanSpace ℝ (Fin 3))
          (planarThinCellRegressionPlane.normalVector ⨯ₑ₃
            (tangent : EuclideanSpace ℝ (Fin 3))) := by
        simpa only [inner_sub_left] using
          planarThinCellRegression_magneticJump_pairing tangent
      _ = _ := (planarThinCellRegression_surfaceCurrentLine tangent t x scale).symm

/-! ## C. Reconstructed integral and boundary laws -/

/-- The production finite-sheet bridge reconstructs all four literal integral Maxwell laws for
the positive fixture. -/
lemma planarFiniteSheetRegression_integralMaxwell_from_premise :
    IsPlanarIntegralMacroscopicMaxwell planarFiniteSheetRegressionSidewise.fields
      planarFiniteSheetRegressionSidewise.sources planarThinCellRegressionSurfaceCharge
      planarThinCellRegressionSurfaceCurrent planarThinCellRegressionCells
      planarFiniteSheetRegressionFluxRates :=
  planarFiniteSheetRegression_premise.isPlanarIntegralMacroscopicMaxwell

/-- The reconstructed integral laws and the existing thin-cell regularity derive the full
sourceful planar boundary law without assuming a pointwise jump. -/
lemma planarFiniteSheetRegression_boundary_from_premise :
    IsPlanarMacroscopicBoundary
      planarFiniteSheetRegressionSidewise.fields.negative.trace
      planarFiniteSheetRegressionSidewise.fields.positive.trace
      planarThinCellRegressionSurfaceCharge planarThinCellRegressionSurfaceCurrent := by
  apply planarFiniteSheetRegression_premise.isPlanarMacroscopicBoundary
  have hFields := planarFiniteSheetRegressionSidewise_fields
  have hSources := planarFiniteSheetRegressionSidewise_sources
  cases hFields
  cases hSources
  exact planarThinCellRegression_regular

/-! ## D. Hostile source-free control -/

/-- The coordinate zero vector used by the hostile fixture is the additive zero. -/
private lemma planarFiniteSheetRegression_zeroVector :
    WithLp.toLp 2 ![(0 : ℝ), 0, 0] = (0 : EuclideanSpace ℝ (Fin 3)) := by
  ext i
  fin_cases i <;> rfl

/-- Two source-free sidewise Maxwell extensions with a unit tangential electric-field mismatch.
All other fields and both bulk sources vanish. -/
def planarFiniteSheetHostileSidewise :
    PlanarSidewiseMacroscopicMaxwell planarThinCellRegressionPlane where
  negativeElectricField :=
    planarThinCellRegressionConstantVectorField (WithLp.toLp 2 ![(1 : ℝ), 0, 0])
  negativeElectricDisplacement :=
    planarThinCellRegressionConstantVectorField (WithLp.toLp 2 ![(0 : ℝ), 0, 0])
  negativeMagneticInduction :=
    planarThinCellRegressionConstantVectorField (WithLp.toLp 2 ![(0 : ℝ), 0, 0])
  negativeMagneticFieldStrength :=
    planarThinCellRegressionConstantVectorField (WithLp.toLp 2 ![(0 : ℝ), 0, 0])
  negativeChargeDensity := 0
  negativeCurrentDensity := 0
  negativeMaxwell := by
    change IsSourceFreeMacroscopicMaxwell
      (planarThinCellRegressionConstantVectorField (WithLp.toLp 2 ![(1 : ℝ), 0, 0]))
      (planarThinCellRegressionConstantVectorField (WithLp.toLp 2 ![(0 : ℝ), 0, 0]))
      (planarThinCellRegressionConstantVectorField (WithLp.toLp 2 ![(0 : ℝ), 0, 0]))
      (planarThinCellRegressionConstantVectorField (WithLp.toLp 2 ![(0 : ℝ), 0, 0]))
    simpa only [show planarThinCellRegressionConstantVectorField =
      oneSidedTraceRegressionConstantVectorField by rfl] using
      oneSidedTraceRegression_constantFields_isSourceFreeMaxwell
        (WithLp.toLp 2 ![(1 : ℝ), 0, 0]) (WithLp.toLp 2 ![(0 : ℝ), 0, 0])
        (WithLp.toLp 2 ![(0 : ℝ), 0, 0]) (WithLp.toLp 2 ![(0 : ℝ), 0, 0])
  positiveElectricField :=
    planarThinCellRegressionConstantVectorField (WithLp.toLp 2 ![(2 : ℝ), 0, 0])
  positiveElectricDisplacement :=
    planarThinCellRegressionConstantVectorField (WithLp.toLp 2 ![(0 : ℝ), 0, 0])
  positiveMagneticInduction :=
    planarThinCellRegressionConstantVectorField (WithLp.toLp 2 ![(0 : ℝ), 0, 0])
  positiveMagneticFieldStrength :=
    planarThinCellRegressionConstantVectorField (WithLp.toLp 2 ![(0 : ℝ), 0, 0])
  positiveChargeDensity := 0
  positiveCurrentDensity := 0
  positiveMaxwell := by
    change IsSourceFreeMacroscopicMaxwell
      (planarThinCellRegressionConstantVectorField (WithLp.toLp 2 ![(2 : ℝ), 0, 0]))
      (planarThinCellRegressionConstantVectorField (WithLp.toLp 2 ![(0 : ℝ), 0, 0]))
      (planarThinCellRegressionConstantVectorField (WithLp.toLp 2 ![(0 : ℝ), 0, 0]))
      (planarThinCellRegressionConstantVectorField (WithLp.toLp 2 ![(0 : ℝ), 0, 0]))
    simpa only [show planarThinCellRegressionConstantVectorField =
      oneSidedTraceRegressionConstantVectorField by rfl] using
      oneSidedTraceRegression_constantFields_isSourceFreeMaxwell
        (WithLp.toLp 2 ![(2 : ℝ), 0, 0]) (WithLp.toLp 2 ![(0 : ℝ), 0, 0])
        (WithLp.toLp 2 ![(0 : ℝ), 0, 0]) (WithLp.toLp 2 ![(0 : ℝ), 0, 0])

/-- The hostile control supplies no carrier-supported free charge. -/
def planarFiniteSheetHostileSurfaceCharge :
    PlanarFreeSurfaceChargeDensity planarThinCellRegressionPlane := 0

/-- The hostile control supplies no carrier-supported free current. -/
def planarFiniteSheetHostileSurfaceCurrent :
    PlanarFreeSurfaceCurrentDensity planarThinCellRegressionPlane := 0

/-- The zero displacement and induction fields give zero witnessed thin-loop flux rates. -/
def planarFiniteSheetHostileFluxRates :
    PlanarMaxwellThinCellFluxRates planarFiniteSheetHostileSidewise.fields
      planarThinCellRegressionCells where
  magneticFluxRate := fun _ _ _ _ ↦ 0
  magneticFlux_hasDerivAt := by
    intro t x tangent scale
    have hFlux :
        (fun s : ℝ ↦ (planarThinCellRegressionCells.loop x tangent).spanningSurfaceAverage
          planarFiniteSheetHostileSidewise.fields.magneticInductionFamily
          (Time.toRealCLE.symm s) x scale) = fun _ ↦ 0 := by
      funext s
      simp [PlanarThinLoopFamily.spanningSurfaceAverage, splitNormalIntegral,
        PlanarMacroscopicTwoSidedFields.magneticInductionFamily,
        PlanarSidewiseMacroscopicMaxwell.fields,
        IsMacroscopicMaxwell.toPlanarMacroscopicSideFields,
        PlanarMacroscopicSideFields.ofFields, planarFiniteSheetHostileSidewise,
        OrientedAffineHyperplane.restrictFieldToSide,
        OrientedAffineHyperplane.negativeSideSample,
        OrientedAffineHyperplane.positiveSideSample,
        planarThinCellRegressionConstantVectorField,
        planarFiniteSheetRegression_zeroVector]
    rw [hFlux]
    exact hasDerivAt_const (Time.toRealCLE t) 0
  electricFluxRate := fun _ _ _ _ ↦ 0
  electricFlux_hasDerivAt := by
    intro t x tangent scale
    have hFlux :
        (fun s : ℝ ↦ (planarThinCellRegressionCells.loop x tangent).spanningSurfaceAverage
          planarFiniteSheetHostileSidewise.fields.electricDisplacementFamily
          (Time.toRealCLE.symm s) x scale) = fun _ ↦ 0 := by
      funext s
      simp [PlanarThinLoopFamily.spanningSurfaceAverage, splitNormalIntegral,
        PlanarMacroscopicTwoSidedFields.electricDisplacementFamily,
        PlanarSidewiseMacroscopicMaxwell.fields,
        IsMacroscopicMaxwell.toPlanarMacroscopicSideFields,
        PlanarMacroscopicSideFields.ofFields, planarFiniteSheetHostileSidewise,
        OrientedAffineHyperplane.restrictFieldToSide,
        OrientedAffineHyperplane.negativeSideSample,
        OrientedAffineHyperplane.positiveSideSample,
        planarThinCellRegressionConstantVectorField,
        planarFiniteSheetRegression_zeroVector]
    rw [hFlux]
    exact hasDerivAt_const (Time.toRealCLE t) 0

/-- The incompatible source-free side fields do not satisfy the finite-sheet identification. -/
lemma planarFiniteSheetHostile_not_premise :
    ¬ HasPlanarFiniteSheetMaxwellPremise planarFiniteSheetHostileSidewise
      planarFiniteSheetHostileSurfaceCharge planarFiniteSheetHostileSurfaceCurrent
      planarThinCellRegressionCells planarFiniteSheetHostileFluxRates := by
  intro premise
  have hCarrier := premise.electricCarrierLine (0 : Time)
    planarThinCellRegressionPoint planarThinCellRegressionTangent 0
  change (2 * (planarThinCellRegressionLoop planarThinCellRegressionTangent).radius 0)⁻¹ *
      planarSplitRectangleCarrierJump
        (planarThinCellRegressionConstantVectorField (WithLp.toLp 2 ![(1 : ℝ), 0, 0]) 0)
        (planarThinCellRegressionConstantVectorField (WithLp.toLp 2 ![(2 : ℝ), 0, 0]) 0)
        (planarThinCellRegressionPoint : Space)
        (planarThinCellRegressionLoop planarThinCellRegressionTangent).tangentDirection
        (planarThinCellRegressionLoop planarThinCellRegressionTangent).normalDirection
        ((planarThinCellRegressionLoop planarThinCellRegressionTangent).radius 0) = 0 at hCarrier
  rw [planarFiniteSheetRegression_constantCarrierLine] at hCarrier
  norm_num [planarThinCellRegressionTangent, PiLp.inner_apply, Fin.sum_univ_three,
    RCLike.inner_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two] at hCarrier

/-- The hostile thin loop has unit normalized electric circulation, fixed independently of the
integral Maxwell predicate. -/
lemma planarFiniteSheetHostile_electricCirculation_eq_one :
    (planarThinCellRegressionLoop planarThinCellRegressionTangent).sideLongEdgeAverage .positive
          planarFiniteSheetHostileSidewise.fields.positive.electricField 0
          planarThinCellRegressionPoint 0 -
        (planarThinCellRegressionLoop planarThinCellRegressionTangent).sideLongEdgeAverage .negative
          planarFiniteSheetHostileSidewise.fields.negative.electricField 0
          planarThinCellRegressionPoint 0 +
        (planarThinCellRegressionLoop planarThinCellRegressionTangent).shortEdgeAverage
          planarFiniteSheetHostileSidewise.fields.electricFieldFamily 0
          planarThinCellRegressionPoint 0 = 1 := by
  change (planarThinCellRegressionLoop planarThinCellRegressionTangent).sideLongEdgeAverage
        .positive (planarThinCellRegressionPlane.restrictFieldToSide .positive
          (planarThinCellRegressionConstantVectorField (WithLp.toLp 2 ![(2 : ℝ), 0, 0])))
        0 planarThinCellRegressionPoint 0 -
      (planarThinCellRegressionLoop planarThinCellRegressionTangent).sideLongEdgeAverage
        .negative (planarThinCellRegressionPlane.restrictFieldToSide .negative
          (planarThinCellRegressionConstantVectorField (WithLp.toLp 2 ![(1 : ℝ), 0, 0])))
        0 planarThinCellRegressionPoint 0 +
      (planarThinCellRegressionLoop planarThinCellRegressionTangent).shortEdgeAverage
        (OrientedAffineHyperplane.TwoSidedField.ofFields planarThinCellRegressionPlane
          (planarThinCellRegressionConstantVectorField (WithLp.toLp 2 ![(1 : ℝ), 0, 0]))
          (planarThinCellRegressionConstantVectorField (WithLp.toLp 2 ![(2 : ℝ), 0, 0])))
        0 planarThinCellRegressionPoint 0 = 1
  have hDecomposition :=
    PlanarThinLoopFamily.circulation_eq_normalized_curlFlux_add_carrierJump
      (planarThinCellRegressionLoop planarThinCellRegressionTangent)
      (planarThinCellRegressionConstantVectorField (WithLp.toLp 2 ![(1 : ℝ), 0, 0]))
      (planarThinCellRegressionConstantVectorField (WithLp.toLp 2 ![(2 : ℝ), 0, 0]))
      (0 : Time) planarThinCellRegressionPoint (0 : ℕ)
      (planarFiniteSheetRegression_constantStokesRegularity
        (WithLp.toLp 2 ![(1 : ℝ), 0, 0]) (WithLp.toLp 2 ![(2 : ℝ), 0, 0])
        (0 : Time) planarThinCellRegressionPoint planarThinCellRegressionTangent (0 : ℕ))
  rw [hDecomposition]
  have hCurl : planarSplitRectangleCurlFlux
      (planarThinCellRegressionConstantVectorField (WithLp.toLp 2 ![(1 : ℝ), 0, 0]) 0)
      (planarThinCellRegressionConstantVectorField (WithLp.toLp 2 ![(2 : ℝ), 0, 0]) 0)
      (planarThinCellRegressionPoint : Space)
      (planarThinCellRegressionLoop planarThinCellRegressionTangent).tangentDirection
      (planarThinCellRegressionLoop planarThinCellRegressionTangent).normalDirection
      ((planarThinCellRegressionLoop planarThinCellRegressionTangent).radius 0)
      ((planarThinCellRegressionLoop planarThinCellRegressionTangent).halfThickness 0) = 0 := by
    unfold planarSplitRectangleCurlFlux planarThinCellRegressionConstantVectorField
    simp
  rw [hCurl, zero_add, planarFiniteSheetRegression_constantCarrierLine]
  norm_num [planarThinCellRegressionTangent, PiLp.inner_apply, Fin.sum_univ_three,
    RCLike.inner_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two]

/-- The literal source-free Faraday law fails for the hostile sidewise fields, even though each
ambient side separately satisfies differential Maxwell. -/
lemma planarFiniteSheetHostile_not_integralMaxwell :
    ¬ IsPlanarIntegralMacroscopicMaxwell planarFiniteSheetHostileSidewise.fields
      planarFiniteSheetHostileSidewise.sources planarFiniteSheetHostileSurfaceCharge
      planarFiniteSheetHostileSurfaceCurrent planarThinCellRegressionCells
      planarFiniteSheetHostileFluxRates := by
  intro hIntegral
  have hFaraday := hIntegral.faraday (0 : Time) planarThinCellRegressionPoint
    planarThinCellRegressionTangent 0
  have hZero :
      (planarThinCellRegressionLoop planarThinCellRegressionTangent).sideLongEdgeAverage .positive
            planarFiniteSheetHostileSidewise.fields.positive.electricField 0
            planarThinCellRegressionPoint 0 -
          (planarThinCellRegressionLoop planarThinCellRegressionTangent).sideLongEdgeAverage
            .negative planarFiniteSheetHostileSidewise.fields.negative.electricField 0
            planarThinCellRegressionPoint 0 +
          (planarThinCellRegressionLoop planarThinCellRegressionTangent).shortEdgeAverage
            planarFiniteSheetHostileSidewise.fields.electricFieldFamily 0
            planarThinCellRegressionPoint 0 = 0 := by
    simpa [planarFiniteSheetHostileFluxRates, planarThinCellRegressionCells] using hFaraday
  linarith [planarFiniteSheetHostile_electricCirculation_eq_one, hZero]

end
end ThreeDimension
end Electromagnetism
