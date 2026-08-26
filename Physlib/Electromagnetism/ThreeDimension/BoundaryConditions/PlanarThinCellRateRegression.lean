/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Electromagnetism.ThreeDimension.BoundaryConditions.PlanarThinCellRegression

/-!
# Time-dependent planar Maxwell thin-cell regression

## i. Overview

This file strengthens the coordinate thin-cell regression with fields whose magnetic-induction and
electric-displacement fluxes are affine in time. Spatially linear electric and magnetic fields
independently supply the compensating finite-loop circulations. The resulting literal integral
Maxwell predicate therefore detects Faraday's leading minus and the Ampere--Maxwell displacement
current plus sign; the static regression cannot distinguish either sign.

The fixture is only an adversarial sign test. It does not claim that the finite integral laws follow
from differential Maxwell equations.

## ii. Key results

- `planarThinCellRateRegression_magneticFluxRate_ne_zero`: the witnessed magnetic-flux rate is
  nonzero on the coordinate tangent.
- `planarThinCellRateRegression_electricFluxRate_ne_zero`: the witnessed displacement-flux rate is
  nonzero on the coordinate tangent.
- `planarThinCellRateRegression_isIntegralMaxwell`: the literal four-law finite-cell predicate.

## iii. Table of contents

- A. Affine-time fields
- B. Exact finite-loop values
- C. Integrability and Maxwell signs

## iv. References

This is a Physlib-original adversarial regression for the E4b derivation.
-/

@[expose] public section

namespace Electromagnetism
namespace ThreeDimension

open Filter Matrix Space Time

noncomputable section

/-!
## A. Affine-time fields
-/

/-- The first coordinate vector used by the compensating circulations. -/
def planarThinCellRateRegressionCirculationVector : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![(1 : ℝ), 0, 0]

/-- The second coordinate vector used by the time-dependent surface fluxes. -/
def planarThinCellRateRegressionFluxVector : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![(0 : ℝ), 1, 0]

/-- The flux vector paired with `normal cross tangent` equals the circulation-vector pairing. -/
lemma planarThinCellRateRegression_fluxPairing
    (tangent : planarThinCellRegressionPlane.tangentSubmodule) :
    inner ℝ planarThinCellRateRegressionFluxVector
        (planarThinCellRegressionPlane.normalVector ⨯ₑ₃
          (tangent : EuclideanSpace ℝ (Fin 3))) =
      inner ℝ planarThinCellRateRegressionCirculationVector
        (tangent : EuclideanSpace ℝ (Fin 3)) := by
  simp [planarThinCellRateRegressionFluxVector,
    planarThinCellRateRegressionCirculationVector,
    OrientedAffineHyperplane.normalVector, planarThinCellRegressionPlane,
    planarThinCellRegressionNormal, crossProduct, basis_repr_apply,
    PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

/-- Every multiple of the circulation vector has zero normal pairing. -/
@[simp]
lemma planarThinCellRateRegression_circulationVector_normalPairing (amplitude : ℝ) :
    inner ℝ (amplitude • planarThinCellRateRegressionCirculationVector)
      planarThinCellRegressionPlane.normalVector = 0 := by
  simp [inner_smul_left, planarThinCellRateRegressionCirculationVector,
    OrientedAffineHyperplane.normalVector, planarThinCellRegressionPlane,
    planarThinCellRegressionNormal, PiLp.inner_apply,
    Fin.sum_univ_three, RCLike.inner_apply]

/-- Electric field linear in signed normal coordinate, chosen for Faraday's minus sign. -/
def planarThinCellRateRegressionElectric : ElectricField :=
  fun _ x ↦ -(planarThinCellRegressionPlane.signedNormalCoordinate x) •
    planarThinCellRateRegressionCirculationVector

/-- Electric displacement affine in time with slope twice the flux vector. -/
def planarThinCellRateRegressionDisplacement : ElectricDisplacementField :=
  fun t _ ↦ (2 * Time.toRealCLE t) • planarThinCellRateRegressionFluxVector

/-- Magnetic induction affine in time with slope the flux vector. -/
def planarThinCellRateRegressionInduction : MagneticInductionField :=
  fun t _ ↦ Time.toRealCLE t • planarThinCellRateRegressionFluxVector

/-- Magnetic field strength linear in signed normal coordinate, chosen for the
Ampere--Maxwell plus sign. -/
def planarThinCellRateRegressionMagnetic : MagneticFieldStrength :=
  fun _ x ↦ (2 * planarThinCellRegressionPlane.signedNormalCoordinate x) •
    planarThinCellRateRegressionCirculationVector

/-- Every rate-regression field is spatially continuous at the carrier. -/
lemma planarThinCellRateRegression_continuousAt
    (t : Time) (x : planarThinCellRegressionPlane.carrier) :
    ContinuousAt (planarThinCellRateRegressionElectric t) (x : Space) ∧
      ContinuousAt (planarThinCellRateRegressionDisplacement t) (x : Space) ∧
      ContinuousAt (planarThinCellRateRegressionInduction t) (x : Space) ∧
      ContinuousAt (planarThinCellRateRegressionMagnetic t) (x : Space) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold planarThinCellRateRegressionElectric
      OrientedAffineHyperplane.signedNormalCoordinate
    fun_prop
  · unfold planarThinCellRateRegressionDisplacement
    fun_prop
  · unfold planarThinCellRateRegressionInduction
    fun_prop
  · unfold planarThinCellRateRegressionMagnetic
      OrientedAffineHyperplane.signedNormalCoordinate
    fun_prop

/-- One selected side of the globally defined affine-time fields. -/
def planarThinCellRateRegressionSide (side : OrientedAffineHyperplane.Side) :
    PlanarMacroscopicSideFields planarThinCellRegressionPlane side :=
  PlanarMacroscopicSideFields.ofFields planarThinCellRegressionPlane side
    planarThinCellRateRegressionElectric planarThinCellRateRegressionDisplacement
    planarThinCellRateRegressionInduction planarThinCellRateRegressionMagnetic
    (fun t x ↦ (planarThinCellRateRegression_continuousAt t x).1)
    (fun t x ↦ (planarThinCellRateRegression_continuousAt t x).2.1)
    (fun t x ↦ (planarThinCellRateRegression_continuousAt t x).2.2.1)
    (fun t x ↦ (planarThinCellRateRegression_continuousAt t x).2.2.2)

/-- The identical ambient affine-time fields restricted independently to both open sides. -/
def planarThinCellRateRegressionFields :
    PlanarMacroscopicTwoSidedFields planarThinCellRegressionPlane where
  negative := planarThinCellRateRegressionSide .negative
  positive := planarThinCellRateRegressionSide .positive

/-- Zero bulk free charge and current for the rate sign fixture. -/
def planarThinCellRateRegressionBulkSources :
    PlanarMaxwellBulkSources planarThinCellRegressionPlane :=
  planarThinCellRegressionBulkSources

/-!
## B. Exact finite-loop values
-/

/-- Integrating constants on the two open half-intervals gives the half-thickness times their sum.
The endpoints remain unassigned to either open side. -/
lemma planarThinCellRateRegression_splitNormalIntegral_const
    {halfThickness negative positive : ℝ} (hHalfThickness : 0 < halfThickness) :
    splitNormalIntegral halfThickness
        (fun w ↦ if w < 0 then negative else 0)
        (fun w ↦ if 0 < w then positive else 0) =
      halfThickness * (negative + positive) := by
  have hNegative :
      (∫ w in -halfThickness..0, if w < 0 then negative else 0) =
        ∫ _ in -halfThickness..0, negative := by
    apply intervalIntegral.integral_congr_uIoo
    intro w hw
    rw [Set.uIoo_of_le (neg_nonpos.mpr hHalfThickness.le)] at hw
    simp [hw.2]
  have hPositive :
      (∫ w in 0..halfThickness, if 0 < w then positive else 0) =
        ∫ _ in 0..halfThickness, positive := by
    apply intervalIntegral.integral_congr_uIoo
    intro w hw
    rw [Set.uIoo_of_le hHalfThickness.le] at hw
    simp [hw.1]
  rw [splitNormalIntegral, hNegative, hPositive,
    intervalIntegral.integral_const, intervalIntegral.integral_const]
  ring

/-- The split normal integral of one fixed vector pairing is twice the half-thickness times that
pairing. -/
lemma planarThinCellRateRegression_splitNormalIntegral_inner_smul
    {halfThickness amplitude : ℝ} (hHalfThickness : 0 < halfThickness)
    (value normal : EuclideanSpace ℝ (Fin 3)) :
    splitNormalIntegral halfThickness
        (fun w ↦ inner ℝ (if w < 0 then amplitude • value else 0) normal)
        (fun w ↦ inner ℝ (if 0 < w then amplitude • value else 0) normal) =
      2 * halfThickness * amplitude * inner ℝ value normal := by
  have hNegative (w : ℝ) :
      inner ℝ (if w < 0 then amplitude • value else 0) normal =
        if w < 0 then amplitude * inner ℝ value normal else 0 := by
    by_cases hw : w < 0 <;> simp [hw, inner_smul_left]
  have hPositive (w : ℝ) :
      inner ℝ (if 0 < w then amplitude • value else 0) normal =
        if 0 < w then amplitude * inner ℝ value normal else 0 := by
    by_cases hw : 0 < w <;> simp [hw, inner_smul_left]
  unfold splitNormalIntegral
  simp_rw [hNegative, hPositive]
  have hIntegral := planarThinCellRateRegression_splitNormalIntegral_const
    hHalfThickness
    (negative := amplitude * inner ℝ value normal)
    (positive := amplitude * inner ℝ value normal)
  unfold splitNormalIntegral at hIntegral
  convert hIntegral using 1
  all_goals ring

/-- Open-side vector pullbacks orthogonal to the plane normal satisfy the split-normal
integrability contract. -/
lemma planarThinCellRateRegression_splitNormalInnerIntegrable_of_pairing_eq_zero
    {halfThickness : ℝ} (negative positive : ℝ → EuclideanSpace ℝ (Fin 3))
    (hNegative : ∀ w, inner ℝ (negative w)
      planarThinCellRegressionPlane.normalVector = 0)
    (hPositive : ∀ w, inner ℝ (positive w)
      planarThinCellRegressionPlane.normalVector = 0) :
    SplitNormalIntegrable halfThickness
      (fun w ↦ inner ℝ (if w < 0 then negative w else 0)
        planarThinCellRegressionPlane.normalVector)
      (fun w ↦ inner ℝ (if 0 < w then positive w else 0)
        planarThinCellRegressionPlane.normalVector) := by
  have hNegativeFunction :
      (fun w ↦ inner ℝ (if w < 0 then negative w else 0)
        planarThinCellRegressionPlane.normalVector) = fun _ ↦ 0 := by
    funext w
    by_cases hw : w < 0 <;> simp [hw, hNegative]
  have hPositiveFunction :
      (fun w ↦ inner ℝ (if 0 < w then positive w else 0)
        planarThinCellRegressionPlane.normalVector) = fun _ ↦ 0 := by
    funext w
    by_cases hw : 0 < w <;> simp [hw, hPositive]
  rw [hNegativeFunction, hPositiveFunction]
  exact ⟨intervalIntegrable_const, intervalIntegrable_const⟩

/-- The normalized spanning-surface flux of a spatially constant multiple of the flux vector. -/
lemma planarThinCellRateRegression_spanningSurfaceAverage
    (amplitude : Time → ℝ)
    (tangent : planarThinCellRegressionPlane.tangentSubmodule)
    (t : Time) (x : planarThinCellRegressionPlane.carrier) (scale : ℕ) :
    (planarThinCellRegressionLoop tangent).spanningSurfaceAverage
        (OrientedAffineHyperplane.TwoSidedField.ofField
          planarThinCellRegressionPlane
          (fun time _ ↦ amplitude time • planarThinCellRateRegressionFluxVector))
        t x scale =
      2 * planarThinCellRegressionHalfThickness scale * amplitude t *
        inner ℝ planarThinCellRateRegressionCirculationVector
          (tangent : EuclideanSpace ℝ (Fin 3)) := by
  have hSplit (u : ℝ) :
      splitNormalIntegral (planarThinCellRegressionHalfThickness scale)
          (fun w ↦ inner ℝ
            (planarThinCellRegressionPlane.negativeSideSample
              (OrientedAffineHyperplane.TwoSidedField.ofField
                planarThinCellRegressionPlane
                (fun time _ ↦ amplitude time • planarThinCellRateRegressionFluxVector)).negative
              t x (u • tangent) w)
            (planarThinCellRegressionPlane.normalVector ⨯ₑ₃
              (tangent : EuclideanSpace ℝ (Fin 3))))
          (fun w ↦ inner ℝ
            (planarThinCellRegressionPlane.positiveSideSample
              (OrientedAffineHyperplane.TwoSidedField.ofField
                planarThinCellRegressionPlane
                (fun time _ ↦ amplitude time • planarThinCellRateRegressionFluxVector)).positive
              t x (u • tangent) w)
            (planarThinCellRegressionPlane.normalVector ⨯ₑ₃
              (tangent : EuclideanSpace ℝ (Fin 3)))) =
        2 * planarThinCellRegressionHalfThickness scale * amplitude t *
          inner ℝ planarThinCellRateRegressionCirculationVector
            (tangent : EuclideanSpace ℝ (Fin 3)) := by
    calc
      _ = 2 * planarThinCellRegressionHalfThickness scale * amplitude t *
          inner ℝ planarThinCellRateRegressionFluxVector
            (planarThinCellRegressionPlane.normalVector ⨯ₑ₃
              (tangent : EuclideanSpace ℝ (Fin 3))) := by
        simpa only [OrientedAffineHyperplane.negativeSideSample,
          OrientedAffineHyperplane.positiveSideSample,
          OrientedAffineHyperplane.TwoSidedField.ofField,
          OrientedAffineHyperplane.restrictFieldToSide, dite_eq_ite] using
          (planarThinCellRateRegression_splitNormalIntegral_inner_smul
            (planarThinCellRegressionHalfThickness_pos scale)
            (amplitude := amplitude t) planarThinCellRateRegressionFluxVector
            (planarThinCellRegressionPlane.normalVector ⨯ₑ₃
              (tangent : EuclideanSpace ℝ (Fin 3))))
      _ = _ := by rw [planarThinCellRateRegression_fluxPairing]
  rw [PlanarThinLoopFamily.spanningSurfaceAverage]
  simp only [planarThinCellRegressionLoop, planarThinCellRegressionScale]
  simp_rw [hSplit]
  rw [intervalIntegral.integral_const]
  field_simp [(planarThinCellRegressionRadius_pos scale).ne']
  ring

/-- The magnetic flux is affine in the real time coordinate. -/
lemma planarThinCellRateRegression_magneticFlux
    (tangent : planarThinCellRegressionPlane.tangentSubmodule)
    (t : Time) (x : planarThinCellRegressionPlane.carrier) (scale : ℕ) :
    (planarThinCellRegressionLoop tangent).spanningSurfaceAverage
        planarThinCellRateRegressionFields.magneticInductionFamily t x scale =
      2 * planarThinCellRegressionHalfThickness scale * Time.toRealCLE t *
        inner ℝ planarThinCellRateRegressionCirculationVector
          (tangent : EuclideanSpace ℝ (Fin 3)) := by
  change (planarThinCellRegressionLoop tangent).spanningSurfaceAverage
      (OrientedAffineHyperplane.TwoSidedField.ofField
        planarThinCellRegressionPlane planarThinCellRateRegressionInduction) t x scale = _
  unfold planarThinCellRateRegressionInduction
  exact planarThinCellRateRegression_spanningSurfaceAverage Time.toRealCLE tangent t x scale

/-- The electric-displacement flux is affine in time with twice the magnetic slope. -/
lemma planarThinCellRateRegression_electricFlux
    (tangent : planarThinCellRegressionPlane.tangentSubmodule)
    (t : Time) (x : planarThinCellRegressionPlane.carrier) (scale : ℕ) :
    (planarThinCellRegressionLoop tangent).spanningSurfaceAverage
        planarThinCellRateRegressionFields.electricDisplacementFamily t x scale =
      4 * planarThinCellRegressionHalfThickness scale * Time.toRealCLE t *
        inner ℝ planarThinCellRateRegressionCirculationVector
          (tangent : EuclideanSpace ℝ (Fin 3)) := by
  change (planarThinCellRegressionLoop tangent).spanningSurfaceAverage
      (OrientedAffineHyperplane.TwoSidedField.ofField
        planarThinCellRegressionPlane planarThinCellRateRegressionDisplacement) t x scale = _
  unfold planarThinCellRateRegressionDisplacement
  convert planarThinCellRateRegression_spanningSurfaceAverage
      (fun time ↦ 2 * Time.toRealCLE time) tangent t x scale using 1
  all_goals ring

/-- The positive-side electric long edge has value `-h` times the circulation pairing. -/
lemma planarThinCellRateRegression_electricPositiveLongEdge
    (tangent : planarThinCellRegressionPlane.tangentSubmodule)
    (t : Time) (x : planarThinCellRegressionPlane.carrier) (scale : ℕ) :
    (planarThinCellRegressionLoop tangent).sideLongEdgeAverage .positive
        planarThinCellRateRegressionFields.positive.electricField t x scale =
      -planarThinCellRegressionHalfThickness scale *
        inner ℝ planarThinCellRateRegressionCirculationVector
          (tangent : EuclideanSpace ℝ (Fin 3)) := by
  simpa [PlanarThinLoopFamily.sideLongEdgeAverage,
    planarThinCellRegressionLoop, planarThinCellRegressionScale,
    planarThinCellRateRegressionFields, planarThinCellRateRegressionSide,
    PlanarMacroscopicSideFields.ofFields, planarThinCellRateRegressionElectric,
    OrientedAffineHyperplane.restrictFieldToSide, inner_smul_left] using
    (planarThinCellRegression_normalizedIntervalAverage_const
      (planarThinCellRegressionRadius_pos scale)
      (value := -planarThinCellRegressionHalfThickness scale *
        inner ℝ planarThinCellRateRegressionCirculationVector
          (tangent : EuclideanSpace ℝ (Fin 3))))

/-- The negative-side electric long edge has value `h` times the circulation pairing. -/
lemma planarThinCellRateRegression_electricNegativeLongEdge
    (tangent : planarThinCellRegressionPlane.tangentSubmodule)
    (t : Time) (x : planarThinCellRegressionPlane.carrier) (scale : ℕ) :
    (planarThinCellRegressionLoop tangent).sideLongEdgeAverage .negative
        planarThinCellRateRegressionFields.negative.electricField t x scale =
      planarThinCellRegressionHalfThickness scale *
        inner ℝ planarThinCellRateRegressionCirculationVector
          (tangent : EuclideanSpace ℝ (Fin 3)) := by
  simpa [PlanarThinLoopFamily.sideLongEdgeAverage,
    planarThinCellRegressionLoop, planarThinCellRegressionScale,
    planarThinCellRateRegressionFields, planarThinCellRateRegressionSide,
    PlanarMacroscopicSideFields.ofFields, planarThinCellRateRegressionElectric,
    OrientedAffineHyperplane.restrictFieldToSide, inner_smul_left] using
    (planarThinCellRegression_normalizedIntervalAverage_const
      (planarThinCellRegressionRadius_pos scale)
      (value := planarThinCellRegressionHalfThickness scale *
        inner ℝ planarThinCellRateRegressionCirculationVector
          (tangent : EuclideanSpace ℝ (Fin 3))))

/-- The positive-side magnetic long edge has value `2h` times the circulation pairing. -/
lemma planarThinCellRateRegression_magneticPositiveLongEdge
    (tangent : planarThinCellRegressionPlane.tangentSubmodule)
    (t : Time) (x : planarThinCellRegressionPlane.carrier) (scale : ℕ) :
    (planarThinCellRegressionLoop tangent).sideLongEdgeAverage .positive
        planarThinCellRateRegressionFields.positive.magneticFieldStrength t x scale =
      2 * planarThinCellRegressionHalfThickness scale *
        inner ℝ planarThinCellRateRegressionCirculationVector
          (tangent : EuclideanSpace ℝ (Fin 3)) := by
  simpa [PlanarThinLoopFamily.sideLongEdgeAverage,
    planarThinCellRegressionLoop, planarThinCellRegressionScale,
    planarThinCellRateRegressionFields, planarThinCellRateRegressionSide,
    PlanarMacroscopicSideFields.ofFields, planarThinCellRateRegressionMagnetic,
    OrientedAffineHyperplane.restrictFieldToSide, inner_smul_left] using
    (planarThinCellRegression_normalizedIntervalAverage_const
      (planarThinCellRegressionRadius_pos scale)
      (value := 2 * planarThinCellRegressionHalfThickness scale *
        inner ℝ planarThinCellRateRegressionCirculationVector
          (tangent : EuclideanSpace ℝ (Fin 3))))

/-- The negative-side magnetic long edge has value `-2h` times the circulation pairing. -/
lemma planarThinCellRateRegression_magneticNegativeLongEdge
    (tangent : planarThinCellRegressionPlane.tangentSubmodule)
    (t : Time) (x : planarThinCellRegressionPlane.carrier) (scale : ℕ) :
    (planarThinCellRegressionLoop tangent).sideLongEdgeAverage .negative
        planarThinCellRateRegressionFields.negative.magneticFieldStrength t x scale =
      -2 * planarThinCellRegressionHalfThickness scale *
        inner ℝ planarThinCellRateRegressionCirculationVector
          (tangent : EuclideanSpace ℝ (Fin 3)) := by
  simpa [PlanarThinLoopFamily.sideLongEdgeAverage,
    planarThinCellRegressionLoop, planarThinCellRegressionScale,
    planarThinCellRateRegressionFields, planarThinCellRateRegressionSide,
    PlanarMacroscopicSideFields.ofFields, planarThinCellRateRegressionMagnetic,
    OrientedAffineHyperplane.restrictFieldToSide, inner_smul_left] using
    (planarThinCellRegression_normalizedIntervalAverage_const
      (planarThinCellRegressionRadius_pos scale)
      (value := -2 * planarThinCellRegressionHalfThickness scale *
        inner ℝ planarThinCellRateRegressionCirculationVector
          (tangent : EuclideanSpace ℝ (Fin 3))))

/-- A two-sided field valued in multiples of the circulation vector has zero short-edge
circulation. -/
lemma planarThinCellRateRegression_shortEdgeAverage_smul
    (amplitude : Time → Space → ℝ)
    (tangent : planarThinCellRegressionPlane.tangentSubmodule)
    (t : Time) (x : planarThinCellRegressionPlane.carrier) (scale : ℕ) :
    (planarThinCellRegressionLoop tangent).shortEdgeAverage
      (OrientedAffineHyperplane.TwoSidedField.ofField planarThinCellRegressionPlane
        (fun time point ↦ amplitude time point •
          planarThinCellRateRegressionCirculationVector)) t x scale = 0 := by
  have hNegative (offset : planarThinCellRegressionPlane.tangentSubmodule) (w : ℝ) :
      inner ℝ
          (planarThinCellRegressionPlane.negativeSideSample
            (OrientedAffineHyperplane.TwoSidedField.ofField planarThinCellRegressionPlane
              (fun time point ↦ amplitude time point •
                planarThinCellRateRegressionCirculationVector)).negative
            t x offset w)
          planarThinCellRegressionPlane.normalVector = 0 := by
    rw [OrientedAffineHyperplane.negativeSideSample]
    split
    · exact planarThinCellRateRegression_circulationVector_normalPairing _
    · simp
  have hPositive (offset : planarThinCellRegressionPlane.tangentSubmodule) (w : ℝ) :
      inner ℝ
          (planarThinCellRegressionPlane.positiveSideSample
            (OrientedAffineHyperplane.TwoSidedField.ofField planarThinCellRegressionPlane
              (fun time point ↦ amplitude time point •
                planarThinCellRateRegressionCirculationVector)).positive
            t x offset w)
          planarThinCellRegressionPlane.normalVector = 0 := by
    rw [OrientedAffineHyperplane.positiveSideSample]
    split
    · exact planarThinCellRateRegression_circulationVector_normalPairing _
    · simp
  rw [PlanarThinLoopFamily.shortEdgeAverage]
  simp only [planarThinCellRegressionLoop, planarThinCellRegressionScale]
  simp_rw [hNegative, hPositive]
  simp [splitNormalIntegral]

/-- Both short electric edges have zero normal pairing. -/
lemma planarThinCellRateRegression_electricShortEdges
    (tangent : planarThinCellRegressionPlane.tangentSubmodule)
    (t : Time) (x : planarThinCellRegressionPlane.carrier) (scale : ℕ) :
    (planarThinCellRegressionLoop tangent).shortEdgeAverage
      planarThinCellRateRegressionFields.electricFieldFamily t x scale = 0 := by
  change (planarThinCellRegressionLoop tangent).shortEdgeAverage
    (OrientedAffineHyperplane.TwoSidedField.ofField planarThinCellRegressionPlane
      planarThinCellRateRegressionElectric) t x scale = 0
  unfold planarThinCellRateRegressionElectric
  exact planarThinCellRateRegression_shortEdgeAverage_smul
    (fun _ point ↦ -planarThinCellRegressionPlane.signedNormalCoordinate point)
    tangent t x scale

/-- Both short magnetic-field-strength edges have zero normal pairing. -/
lemma planarThinCellRateRegression_magneticShortEdges
    (tangent : planarThinCellRegressionPlane.tangentSubmodule)
    (t : Time) (x : planarThinCellRegressionPlane.carrier) (scale : ℕ) :
    (planarThinCellRegressionLoop tangent).shortEdgeAverage
      planarThinCellRateRegressionFields.magneticFieldStrengthFamily t x scale = 0 := by
  change (planarThinCellRegressionLoop tangent).shortEdgeAverage
    (OrientedAffineHyperplane.TwoSidedField.ofField planarThinCellRegressionPlane
      planarThinCellRateRegressionMagnetic) t x scale = 0
  unfold planarThinCellRateRegressionMagnetic
  exact planarThinCellRateRegression_shortEdgeAverage_smul
    (fun _ point ↦ 2 * planarThinCellRegressionPlane.signedNormalCoordinate point)
    tangent t x scale

/-- A spatially constant two-sided vector field has zero net lateral pillbox flux. -/
lemma planarThinCellRateRegression_lateralFaceAverage_const
    {P : Type*} (value : P → EuclideanSpace ℝ (Fin 3)) (parameter : P)
    (x : planarThinCellRegressionPlane.carrier) (scale : ℕ) :
    planarThinCellRegressionPillbox.lateralFaceAverage
        (OrientedAffineHyperplane.TwoSidedField.ofField
          planarThinCellRegressionPlane (fun p ↦ fun _ ↦ value p))
        parameter x scale = 0 := by
  have hSplit (offset : planarThinCellRegressionPlane.tangentSubmodule)
      (normal : EuclideanSpace ℝ (Fin 3)) :
      splitNormalIntegral (planarThinCellRegressionHalfThickness scale)
          (fun w ↦ inner ℝ
            (planarThinCellRegressionPlane.negativeSideSample
              (OrientedAffineHyperplane.TwoSidedField.ofField
                planarThinCellRegressionPlane (fun p ↦ fun _ ↦ value p)).negative
              parameter x offset w) normal)
          (fun w ↦ inner ℝ
            (planarThinCellRegressionPlane.positiveSideSample
              (OrientedAffineHyperplane.TwoSidedField.ofField
                planarThinCellRegressionPlane (fun p ↦ fun _ ↦ value p)).positive
              parameter x offset w) normal) =
        2 * planarThinCellRegressionHalfThickness scale * inner ℝ (value parameter) normal := by
    simpa only [OrientedAffineHyperplane.negativeSideSample,
      OrientedAffineHyperplane.positiveSideSample,
      OrientedAffineHyperplane.TwoSidedField.ofField,
      OrientedAffineHyperplane.restrictFieldToSide, dite_eq_ite, one_smul, mul_one] using
      (planarThinCellRateRegression_splitNormalIntegral_inner_smul
        (planarThinCellRegressionHalfThickness_pos scale)
        (amplitude := 1) (value parameter) normal)
  rw [PlanarPillboxFamily.lateralFaceAverage]
  simp only [planarThinCellRegressionPillbox, planarThinCellRegressionScale]
  simp_rw [hSplit]
  simp only [intervalIntegral.integral_const]
  ring

/-- The rate-regression displacement has zero net lateral pillbox flux. -/
lemma planarThinCellRateRegression_displacementLateral
    (t : Time) (x : planarThinCellRegressionPlane.carrier) (scale : ℕ) :
    planarThinCellRegressionPillbox.lateralFaceAverage
      planarThinCellRateRegressionFields.electricDisplacementFamily t x scale = 0 := by
  change planarThinCellRegressionPillbox.lateralFaceAverage
    (OrientedAffineHyperplane.TwoSidedField.ofField planarThinCellRegressionPlane
      planarThinCellRateRegressionDisplacement) t x scale = 0
  unfold planarThinCellRateRegressionDisplacement
  exact planarThinCellRateRegression_lateralFaceAverage_const
    (fun time ↦ (2 * Time.toRealCLE time) • planarThinCellRateRegressionFluxVector)
    t x scale

/-- The rate-regression induction has zero net lateral pillbox flux. -/
lemma planarThinCellRateRegression_inductionLateral
    (t : Time) (x : planarThinCellRegressionPlane.carrier) (scale : ℕ) :
    planarThinCellRegressionPillbox.lateralFaceAverage
      planarThinCellRateRegressionFields.magneticInductionFamily t x scale = 0 := by
  change planarThinCellRegressionPillbox.lateralFaceAverage
    (OrientedAffineHyperplane.TwoSidedField.ofField planarThinCellRegressionPlane
      planarThinCellRateRegressionInduction) t x scale = 0
  unfold planarThinCellRateRegressionInduction
  exact planarThinCellRateRegression_lateralFaceAverage_const
    (fun time ↦ Time.toRealCLE time • planarThinCellRateRegressionFluxVector)
    t x scale

/-- Every principal displacement face has zero normal flux. -/
lemma planarThinCellRateRegression_displacementFace
    (side : OrientedAffineHyperplane.Side) (t : Time)
    (x : planarThinCellRegressionPlane.carrier) (scale : ℕ) :
    planarThinCellRegressionPillbox.sideFaceAverage side
        (match side with
          | .negative => planarThinCellRateRegressionFields.negative.electricDisplacement
          | .positive => planarThinCellRateRegressionFields.positive.electricDisplacement)
        t x scale = 0 := by
  cases side <;>
    simp [PlanarPillboxFamily.sideFaceAverage, planarThinCellRegressionPillbox,
      planarThinCellRegressionScale, planarThinCellRateRegressionFields,
      planarThinCellRateRegressionSide, PlanarMacroscopicSideFields.ofFields,
      planarThinCellRateRegressionDisplacement,
      OrientedAffineHyperplane.restrictFieldToSide,
      OrientedAffineHyperplane.normalVector, planarThinCellRegressionPlane,
      planarThinCellRegressionNormal, planarThinCellRateRegressionFluxVector,
      normalizedSquareAverage, normalizedIntervalAverage,
      PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply]

/-- Every principal induction face has zero normal flux. -/
lemma planarThinCellRateRegression_inductionFace
    (side : OrientedAffineHyperplane.Side) (t : Time)
    (x : planarThinCellRegressionPlane.carrier) (scale : ℕ) :
    planarThinCellRegressionPillbox.sideFaceAverage side
        (match side with
          | .negative => planarThinCellRateRegressionFields.negative.magneticInduction
          | .positive => planarThinCellRateRegressionFields.positive.magneticInduction)
        t x scale = 0 := by
  cases side <;>
    simp [PlanarPillboxFamily.sideFaceAverage, planarThinCellRegressionPillbox,
      planarThinCellRegressionScale, planarThinCellRateRegressionFields,
      planarThinCellRateRegressionSide, PlanarMacroscopicSideFields.ofFields,
      planarThinCellRateRegressionInduction,
      OrientedAffineHyperplane.restrictFieldToSide,
      OrientedAffineHyperplane.normalVector, planarThinCellRegressionPlane,
      planarThinCellRegressionNormal, planarThinCellRateRegressionFluxVector,
      normalizedSquareAverage, normalizedIntervalAverage,
      PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply]

/-- The zero surface charge has zero normalized principal-face average. -/
lemma planarThinCellRateRegression_zeroSurfaceChargeFace
    (t : Time) (x : planarThinCellRegressionPlane.carrier) (scale : ℕ) :
    planarThinCellRegressionPillbox.surfaceFaceAverage
      (0 : PlanarFreeSurfaceChargeDensity planarThinCellRegressionPlane) t x scale = 0 := by
  change normalizedSquareAverage (planarThinCellRegressionRadius scale) (fun _ _ ↦ 0) = 0
  exact planarThinCellRegression_normalizedSquareAverage_const
    (planarThinCellRegressionRadius_pos scale)

/-- The zero surface current has zero normalized boundary-line average. -/
lemma planarThinCellRateRegression_zeroSurfaceCurrentLine
    (tangent : planarThinCellRegressionPlane.tangentSubmodule)
    (t : Time) (x : planarThinCellRegressionPlane.carrier) (scale : ℕ) :
    (planarThinCellRegressionLoop tangent).surfaceLineAverage
      (0 : PlanarFreeSurfaceCurrentDensity planarThinCellRegressionPlane) t x scale = 0 := by
  unfold PlanarThinLoopFamily.surfaceLineAverage
  change normalizedIntervalAverage (planarThinCellRegressionRadius scale)
      (fun _ ↦ inner ℝ (0 : EuclideanSpace ℝ (Fin 3))
        (planarThinCellRegressionPlane.normalVector ⨯ₑ₃
          (tangent : EuclideanSpace ℝ (Fin 3)))) = 0
  simp only [inner_zero_left]
  exact planarThinCellRegression_normalizedIntervalAverage_const
    (planarThinCellRegressionRadius_pos scale)

/-- The actual affine-time surface fluxes have their displayed nonzero derivatives. -/
def planarThinCellRateRegressionFluxRates :
    PlanarMaxwellThinCellFluxRates
      planarThinCellRateRegressionFields planarThinCellRegressionCells where
  magneticFluxRate := fun _ _ tangent scale ↦
    2 * planarThinCellRegressionHalfThickness scale *
      inner ℝ planarThinCellRateRegressionCirculationVector
        (tangent : EuclideanSpace ℝ (Fin 3))
  magneticFlux_hasDerivAt := by
    intro t x tangent scale
    have hFlux :
        (fun s : ℝ ↦ (planarThinCellRegressionCells.loop x tangent).spanningSurfaceAverage
          planarThinCellRateRegressionFields.magneticInductionFamily
          (Time.toRealCLE.symm s) x scale) =
          fun s ↦ 2 * planarThinCellRegressionHalfThickness scale * s *
            inner ℝ planarThinCellRateRegressionCirculationVector
              (tangent : EuclideanSpace ℝ (Fin 3)) := by
      funext s
      simpa only [planarThinCellRegressionCells, ContinuousLinearEquiv.apply_symm_apply] using
        planarThinCellRateRegression_magneticFlux tangent (Time.toRealCLE.symm s) x scale
    rw [hFlux]
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id (Time.toRealCLE t)).const_mul
        (2 * planarThinCellRegressionHalfThickness scale)).mul_const
          (inner ℝ planarThinCellRateRegressionCirculationVector
            (tangent : EuclideanSpace ℝ (Fin 3)))
  electricFluxRate := fun _ _ tangent scale ↦
    4 * planarThinCellRegressionHalfThickness scale *
      inner ℝ planarThinCellRateRegressionCirculationVector
        (tangent : EuclideanSpace ℝ (Fin 3))
  electricFlux_hasDerivAt := by
    intro t x tangent scale
    have hFlux :
        (fun s : ℝ ↦ (planarThinCellRegressionCells.loop x tangent).spanningSurfaceAverage
          planarThinCellRateRegressionFields.electricDisplacementFamily
          (Time.toRealCLE.symm s) x scale) =
          fun s ↦ 4 * planarThinCellRegressionHalfThickness scale * s *
            inner ℝ planarThinCellRateRegressionCirculationVector
              (tangent : EuclideanSpace ℝ (Fin 3)) := by
      funext s
      simpa only [planarThinCellRegressionCells, ContinuousLinearEquiv.apply_symm_apply] using
        planarThinCellRateRegression_electricFlux tangent (Time.toRealCLE.symm s) x scale
    rw [hFlux]
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id (Time.toRealCLE t)).const_mul
        (4 * planarThinCellRegressionHalfThickness scale)).mul_const
          (inner ℝ planarThinCellRateRegressionCirculationVector
            (tangent : EuclideanSpace ℝ (Fin 3)))

/-- The magnetic-flux derivative is nonzero on the coordinate tangent at every finite scale. -/
lemma planarThinCellRateRegression_magneticFluxRate_ne_zero
    (t : Time) (x : planarThinCellRegressionPlane.carrier) (scale : ℕ) :
    planarThinCellRateRegressionFluxRates.magneticFluxRate t x
      planarThinCellRegressionTangent scale ≠ 0 := by
  have hPairing : inner ℝ planarThinCellRateRegressionCirculationVector
      (planarThinCellRegressionTangent : EuclideanSpace ℝ (Fin 3)) = 1 := by
    change inner ℝ (WithLp.toLp 2 ![(1 : ℝ), 0, 0])
      (WithLp.toLp 2 ![(1 : ℝ), 0, 0]) = 1
    rw [PiLp.inner_apply]
    norm_num [Fin.sum_univ_three, RCLike.inner_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  rw [show planarThinCellRateRegressionFluxRates.magneticFluxRate t x
      planarThinCellRegressionTangent scale =
      2 * planarThinCellRegressionHalfThickness scale by
    simp [planarThinCellRateRegressionFluxRates, hPairing]]
  exact mul_ne_zero (by norm_num)
    (planarThinCellRegressionHalfThickness_pos scale).ne'

/-- The displacement-flux derivative is nonzero on the coordinate tangent at every finite scale. -/
lemma planarThinCellRateRegression_electricFluxRate_ne_zero
    (t : Time) (x : planarThinCellRegressionPlane.carrier) (scale : ℕ) :
    planarThinCellRateRegressionFluxRates.electricFluxRate t x
      planarThinCellRegressionTangent scale ≠ 0 := by
  have hPairing : inner ℝ planarThinCellRateRegressionCirculationVector
      (planarThinCellRegressionTangent : EuclideanSpace ℝ (Fin 3)) = 1 := by
    change inner ℝ (WithLp.toLp 2 ![(1 : ℝ), 0, 0])
      (WithLp.toLp 2 ![(1 : ℝ), 0, 0]) = 1
    rw [PiLp.inner_apply]
    norm_num [Fin.sum_univ_three, RCLike.inner_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  rw [show planarThinCellRateRegressionFluxRates.electricFluxRate t x
      planarThinCellRegressionTangent scale =
      4 * planarThinCellRegressionHalfThickness scale by
    simp [planarThinCellRateRegressionFluxRates, hPairing]]
  exact mul_ne_zero (by norm_num)
    (planarThinCellRegressionHalfThickness_pos scale).ne'

/-!
## C. Integrability and Maxwell signs
-/

/-- Both electric-displacement principal faces are integrable in the rate fixture. -/
private lemma planarThinCellRateRegression_electricGaussPrincipal_integrable
    (t : Time) (x : planarThinCellRegressionPlane.carrier) (scale : ℕ) :
    planarThinCellRegressionPillbox.SideFaceIntegrable .positive
        planarThinCellRateRegressionFields.positive.electricDisplacement t x scale ∧
      planarThinCellRegressionPillbox.SideFaceIntegrable .negative
        planarThinCellRateRegressionFields.negative.electricDisplacement t x scale := by
  simp [PlanarPillboxFamily.SideFaceIntegrable, IteratedSquareIntegrable,
    SymmetricIntervalIntegrable, planarThinCellRegressionPillbox,
    planarThinCellRegressionScale, planarThinCellRateRegressionFields,
    planarThinCellRateRegressionSide, PlanarMacroscopicSideFields.ofFields,
    planarThinCellRateRegressionDisplacement,
    OrientedAffineHyperplane.restrictFieldToSide]

/-- The electric-displacement lateral faces are integrable in the rate fixture. -/
private lemma planarThinCellRateRegression_electricGaussLateral_integrable
    (t : Time) (x : planarThinCellRegressionPlane.carrier) (scale : ℕ) :
    planarThinCellRegressionPillbox.LateralFacesIntegrable
      planarThinCellRateRegressionFields.electricDisplacementFamily t x scale := by
  simp [PlanarPillboxFamily.LateralFacesIntegrable, SplitRectangleIntegrable,
    SplitNormalIntegrable, SymmetricIntervalIntegrable,
    planarThinCellRegressionPillbox, planarThinCellRegressionScale,
    PlanarMacroscopicTwoSidedFields.electricDisplacementFamily,
    planarThinCellRateRegressionFields, planarThinCellRateRegressionSide,
    PlanarMacroscopicSideFields.ofFields, planarThinCellRateRegressionDisplacement,
    OrientedAffineHyperplane.restrictFieldToSide,
    OrientedAffineHyperplane.negativeSideSample,
    OrientedAffineHyperplane.positiveSideSample]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    first
    | exact planarThinCellRegression_negativeHalfInnerIntegrable
        (planarThinCellRegressionHalfThickness_pos scale) _ _
    | exact planarThinCellRegression_positiveHalfInnerIntegrable
        (planarThinCellRegressionHalfThickness_pos scale) _ _

/-- The zero bulk-charge volume is integrable in the rate fixture. -/
private lemma planarThinCellRateRegression_electricGaussVolume_integrable
    (t : Time) (x : planarThinCellRegressionPlane.carrier) (scale : ℕ) :
    planarThinCellRegressionPillbox.VolumeIntegrable
      planarThinCellRateRegressionBulkSources.chargeDensity t x scale := by
  simpa [planarThinCellRateRegressionBulkSources] using
    planarThinCellRegression_electricGaussVolume_integrable t x scale

/-- The zero surface-charge face is integrable in the rate fixture. -/
private lemma planarThinCellRateRegression_electricGaussSheet_integrable
    (t : Time) (x : planarThinCellRegressionPlane.carrier) (scale : ℕ) :
    planarThinCellRegressionPillbox.SurfaceFaceIntegrable
      (0 : PlanarFreeSurfaceChargeDensity planarThinCellRegressionPlane) t x scale := by
  simp [PlanarPillboxFamily.SurfaceFaceIntegrable, IteratedSquareIntegrable,
    SymmetricIntervalIntegrable, planarThinCellRegressionPillbox,
    planarThinCellRegressionScale]

/-- Every magnetic-Gauss face is integrable in the rate fixture. -/
private lemma planarThinCellRateRegression_magneticGauss_integrable
    (t : Time) (x : planarThinCellRegressionPlane.carrier) (scale : ℕ) :
    planarThinCellRegressionPillbox.SideFaceIntegrable .positive
        planarThinCellRateRegressionFields.positive.magneticInduction t x scale ∧
      planarThinCellRegressionPillbox.SideFaceIntegrable .negative
          planarThinCellRateRegressionFields.negative.magneticInduction t x scale ∧
        planarThinCellRegressionPillbox.LateralFacesIntegrable
          planarThinCellRateRegressionFields.magneticInductionFamily t x scale := by
  have hPrincipal :
      planarThinCellRegressionPillbox.SideFaceIntegrable .positive
          planarThinCellRateRegressionFields.positive.magneticInduction t x scale ∧
        planarThinCellRegressionPillbox.SideFaceIntegrable .negative
          planarThinCellRateRegressionFields.negative.magneticInduction t x scale := by
    simp [PlanarPillboxFamily.SideFaceIntegrable, IteratedSquareIntegrable,
      SymmetricIntervalIntegrable, planarThinCellRegressionPillbox,
      planarThinCellRegressionScale, planarThinCellRateRegressionFields,
      planarThinCellRateRegressionSide, PlanarMacroscopicSideFields.ofFields,
      planarThinCellRateRegressionInduction,
      OrientedAffineHyperplane.restrictFieldToSide]
  refine ⟨hPrincipal.1, hPrincipal.2, ?_⟩
  simp [PlanarPillboxFamily.LateralFacesIntegrable, SplitRectangleIntegrable,
    SplitNormalIntegrable, SymmetricIntervalIntegrable,
    planarThinCellRegressionPillbox, planarThinCellRegressionScale,
    PlanarMacroscopicTwoSidedFields.magneticInductionFamily,
    planarThinCellRateRegressionFields, planarThinCellRateRegressionSide,
    PlanarMacroscopicSideFields.ofFields, planarThinCellRateRegressionInduction,
    OrientedAffineHyperplane.restrictFieldToSide,
    OrientedAffineHyperplane.negativeSideSample,
    OrientedAffineHyperplane.positiveSideSample]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    first
    | exact planarThinCellRegression_negativeHalfInnerIntegrable
        (planarThinCellRegressionHalfThickness_pos scale) _ _
    | exact planarThinCellRegression_positiveHalfInnerIntegrable
        (planarThinCellRegressionHalfThickness_pos scale) _ _

/-- Every electric circulation pullback is integrable in the rate fixture. -/
private lemma planarThinCellRateRegression_faradayCirculation_integrable
    (t : Time) (x : planarThinCellRegressionPlane.carrier)
    (tangent : planarThinCellRegressionPlane.tangentSubmodule) (scale : ℕ) :
    (planarThinCellRegressionLoop tangent).SideLongEdgeIntegrable .positive
        planarThinCellRateRegressionFields.positive.electricField t x scale ∧
      (planarThinCellRegressionLoop tangent).SideLongEdgeIntegrable .negative
          planarThinCellRateRegressionFields.negative.electricField t x scale ∧
        (planarThinCellRegressionLoop tangent).ShortEdgesIntegrable
          planarThinCellRateRegressionFields.electricFieldFamily t x scale := by
  simp [PlanarThinLoopFamily.SideLongEdgeIntegrable,
    PlanarThinLoopFamily.ShortEdgesIntegrable, SymmetricIntervalIntegrable,
    SplitNormalIntegrable, planarThinCellRegressionLoop, planarThinCellRegressionScale,
    PlanarMacroscopicTwoSidedFields.electricFieldFamily,
    planarThinCellRateRegressionFields, planarThinCellRateRegressionSide,
    PlanarMacroscopicSideFields.ofFields, planarThinCellRateRegressionElectric,
    OrientedAffineHyperplane.restrictFieldToSide,
    OrientedAffineHyperplane.negativeSideSample,
    OrientedAffineHyperplane.positiveSideSample,
    OrientedAffineHyperplane.signedNormalCoordinate_sidePoint]
  exact planarThinCellRateRegression_splitNormalInnerIntegrable_of_pairing_eq_zero
    (fun v ↦ -(v • planarThinCellRateRegressionCirculationVector))
    (fun v ↦ -(v • planarThinCellRateRegressionCirculationVector))
    (by intro v; simp [inner_neg_left])
    (by intro v; simp [inner_neg_left])

/-- The induction spanning surface is integrable in the rate fixture. -/
private lemma planarThinCellRateRegression_faradayFlux_integrable
    (t : Time) (x : planarThinCellRegressionPlane.carrier)
    (tangent : planarThinCellRegressionPlane.tangentSubmodule) (scale : ℕ) :
    (planarThinCellRegressionLoop tangent).SpanningSurfaceIntegrable
      planarThinCellRateRegressionFields.magneticInductionFamily t x scale := by
  simp [PlanarThinLoopFamily.SpanningSurfaceIntegrable,
    SplitRectangleIntegrable, SplitNormalIntegrable, SymmetricIntervalIntegrable,
    planarThinCellRegressionLoop, planarThinCellRegressionScale,
    PlanarMacroscopicTwoSidedFields.magneticInductionFamily,
    planarThinCellRateRegressionFields, planarThinCellRateRegressionSide,
    PlanarMacroscopicSideFields.ofFields, planarThinCellRateRegressionInduction,
    OrientedAffineHyperplane.restrictFieldToSide,
    OrientedAffineHyperplane.negativeSideSample,
    OrientedAffineHyperplane.positiveSideSample]
  exact planarThinCellRegression_splitNormalInnerIntegrable
    (planarThinCellRegressionHalfThickness_pos scale) _ _ _

/-- Every magnetic-field circulation pullback is integrable in the rate fixture. -/
private lemma planarThinCellRateRegression_ampereCirculation_integrable
    (t : Time) (x : planarThinCellRegressionPlane.carrier)
    (tangent : planarThinCellRegressionPlane.tangentSubmodule) (scale : ℕ) :
    (planarThinCellRegressionLoop tangent).SideLongEdgeIntegrable .positive
        planarThinCellRateRegressionFields.positive.magneticFieldStrength t x scale ∧
      (planarThinCellRegressionLoop tangent).SideLongEdgeIntegrable .negative
          planarThinCellRateRegressionFields.negative.magneticFieldStrength t x scale ∧
        (planarThinCellRegressionLoop tangent).ShortEdgesIntegrable
          planarThinCellRateRegressionFields.magneticFieldStrengthFamily t x scale := by
  simp [PlanarThinLoopFamily.SideLongEdgeIntegrable,
    PlanarThinLoopFamily.ShortEdgesIntegrable, SymmetricIntervalIntegrable,
    SplitNormalIntegrable, planarThinCellRegressionLoop, planarThinCellRegressionScale,
    PlanarMacroscopicTwoSidedFields.magneticFieldStrengthFamily,
    planarThinCellRateRegressionFields, planarThinCellRateRegressionSide,
    PlanarMacroscopicSideFields.ofFields, planarThinCellRateRegressionMagnetic,
    OrientedAffineHyperplane.restrictFieldToSide,
    OrientedAffineHyperplane.negativeSideSample,
    OrientedAffineHyperplane.positiveSideSample,
    OrientedAffineHyperplane.signedNormalCoordinate_sidePoint]
  exact planarThinCellRateRegression_splitNormalInnerIntegrable_of_pairing_eq_zero
    (fun v ↦ (2 * v) • planarThinCellRateRegressionCirculationVector)
    (fun v ↦ (2 * v) • planarThinCellRateRegressionCirculationVector)
    (by intro v; simp)
    (by intro v; simp)

/-- Both Ampere--Maxwell spanning-surface pullbacks are integrable in the rate fixture. -/
private lemma planarThinCellRateRegression_ampereFlux_integrable
    (t : Time) (x : planarThinCellRegressionPlane.carrier)
    (tangent : planarThinCellRegressionPlane.tangentSubmodule) (scale : ℕ) :
    (planarThinCellRegressionLoop tangent).SpanningSurfaceIntegrable
        planarThinCellRateRegressionBulkSources.currentDensity t x scale ∧
      (planarThinCellRegressionLoop tangent).SpanningSurfaceIntegrable
        planarThinCellRateRegressionFields.electricDisplacementFamily t x scale := by
  constructor
  · simpa [planarThinCellRateRegressionBulkSources] using
      (planarThinCellRegression_ampereFlux_integrable t x tangent scale).1
  · simp [PlanarThinLoopFamily.SpanningSurfaceIntegrable,
      SplitRectangleIntegrable, SplitNormalIntegrable, SymmetricIntervalIntegrable,
      planarThinCellRegressionLoop, planarThinCellRegressionScale,
      PlanarMacroscopicTwoSidedFields.electricDisplacementFamily,
      planarThinCellRateRegressionFields, planarThinCellRateRegressionSide,
      PlanarMacroscopicSideFields.ofFields, planarThinCellRateRegressionDisplacement,
      OrientedAffineHyperplane.restrictFieldToSide,
      OrientedAffineHyperplane.negativeSideSample,
      OrientedAffineHyperplane.positiveSideSample]
    exact planarThinCellRegression_splitNormalInnerIntegrable
      (planarThinCellRegressionHalfThickness_pos scale) _ _ _

/-- The zero surface-current line is integrable in the rate fixture. -/
private lemma planarThinCellRateRegression_ampereSheet_integrable
    (t : Time) (x : planarThinCellRegressionPlane.carrier)
    (tangent : planarThinCellRegressionPlane.tangentSubmodule) (scale : ℕ) :
    (planarThinCellRegressionLoop tangent).SurfaceLineIntegrable
      (0 : PlanarFreeSurfaceCurrentDensity planarThinCellRegressionPlane) t x scale := by
  simp [PlanarThinLoopFamily.SurfaceLineIntegrable, SymmetricIntervalIntegrable,
    planarThinCellRegressionLoop, planarThinCellRegressionScale]

/-- Every literal pullback in the affine-time sign fixture is integrable. -/
lemma planarThinCellRateRegressionIntegrable :
    ArePlanarMaxwellThinCellTermsIntegrable planarThinCellRateRegressionFields
      planarThinCellRateRegressionBulkSources 0 0 planarThinCellRegressionCells where
  electricGaussPrincipal := planarThinCellRateRegression_electricGaussPrincipal_integrable
  electricGaussLateral := planarThinCellRateRegression_electricGaussLateral_integrable
  electricGaussVolume := planarThinCellRateRegression_electricGaussVolume_integrable
  electricGaussSheet := planarThinCellRateRegression_electricGaussSheet_integrable
  magneticGauss := planarThinCellRateRegression_magneticGauss_integrable
  faradayCirculation := planarThinCellRateRegression_faradayCirculation_integrable
  faradayFlux := planarThinCellRateRegression_faradayFlux_integrable
  ampereCirculation := planarThinCellRateRegression_ampereCirculation_integrable
  ampereFlux := planarThinCellRateRegression_ampereFlux_integrable
  ampereSheet := planarThinCellRateRegression_ampereSheet_integrable

/-- The affine-time fixture satisfies the literal finite integral Maxwell laws. Its nonzero rates
make the Faraday minus and Ampere--Maxwell displacement-current plus signs load-bearing. -/
lemma planarThinCellRateRegression_isIntegralMaxwell :
    IsPlanarIntegralMacroscopicMaxwell planarThinCellRateRegressionFields
      planarThinCellRateRegressionBulkSources 0 0 planarThinCellRegressionCells
      planarThinCellRateRegressionFluxRates where
  integrable := planarThinCellRateRegressionIntegrable
  electricGauss := by
    intro t x scale
    simp only [planarThinCellRegressionCells]
    rw [planarThinCellRateRegression_displacementFace .positive,
      planarThinCellRateRegression_displacementFace .negative,
      planarThinCellRateRegression_displacementLateral]
    rw [show planarThinCellRegressionPillbox.volumeAverage
        planarThinCellRateRegressionBulkSources.chargeDensity t x scale = 0 by
      simpa [planarThinCellRateRegressionBulkSources] using
        planarThinCellRegression_chargeVolume t x scale]
    rw [planarThinCellRateRegression_zeroSurfaceChargeFace]
    ring
  magneticGauss := by
    intro t x scale
    simp only [planarThinCellRegressionCells]
    rw [planarThinCellRateRegression_inductionFace .positive,
      planarThinCellRateRegression_inductionFace .negative,
      planarThinCellRateRegression_inductionLateral]
    ring
  faraday := by
    intro t x tangent scale
    simp only [planarThinCellRegressionCells]
    rw [planarThinCellRateRegression_electricPositiveLongEdge,
      planarThinCellRateRegression_electricNegativeLongEdge,
      planarThinCellRateRegression_electricShortEdges]
    rw [show planarThinCellRateRegressionFluxRates.magneticFluxRate t x tangent scale =
      2 * planarThinCellRegressionHalfThickness scale *
        inner ℝ planarThinCellRateRegressionCirculationVector
          (tangent : EuclideanSpace ℝ (Fin 3)) by rfl]
    ring
  ampereMaxwell := by
    intro t x tangent scale
    simp only [planarThinCellRegressionCells]
    rw [planarThinCellRateRegression_magneticPositiveLongEdge,
      planarThinCellRateRegression_magneticNegativeLongEdge,
      planarThinCellRateRegression_magneticShortEdges]
    rw [show (planarThinCellRegressionLoop tangent).spanningSurfaceAverage
        planarThinCellRateRegressionBulkSources.currentDensity t x scale = 0 by
      simpa [planarThinCellRateRegressionBulkSources] using
        planarThinCellRegression_currentFlux tangent t x scale]
    rw [show planarThinCellRateRegressionFluxRates.electricFluxRate t x tangent scale =
      4 * planarThinCellRegressionHalfThickness scale *
        inner ℝ planarThinCellRateRegressionCirculationVector
          (tangent : EuclideanSpace ℝ (Fin 3)) by rfl,
      planarThinCellRateRegression_zeroSurfaceCurrentLine]
    ring

end
end ThreeDimension
end Electromagnetism
