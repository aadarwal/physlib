/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Electromagnetism.ThreeDimension.BoundaryConditions.FiniteSheetPremise
public import Physlib.Electromagnetism.ThreeDimension.BoundaryConditions.PlanarThinCell

/-!
# Integral Maxwell laws from the planar finite-sheet premise

## i. Overview

This file combines independent sidewise differential Maxwell equations, the explicit finite-sheet
carrier identifications, and the local split-cell calculus. The result is the existing
`IsPlanarIntegralMacroscopicMaxwell` predicate for the actual finite pillboxes and loops.

The proof order is deliberately one-way: the finite-sheet premise gives the four integral laws,
and the existing thin-cell theorem derives the pointwise boundary jumps. No pointwise jump law is
assumed. Deriving the finite-sheet premise itself from weak or measure-valued Maxwell equations
remains future work.

## ii. Key results

- `HasPlanarFiniteSheetMaxwellPremise.electricGauss`: finite electric Gauss law.
- `HasPlanarFiniteSheetMaxwellPremise.magneticGauss`: finite magnetic Gauss law.
- `HasPlanarFiniteSheetMaxwellPremise.faraday`: finite Faraday law.
- `HasPlanarFiniteSheetMaxwellPremise.ampereMaxwell`: finite Ampere--Maxwell law.
- `HasPlanarFiniteSheetMaxwellPremise.isPlanarIntegralMacroscopicMaxwell`: the four-law package.
- `HasPlanarFiniteSheetMaxwellPremise.isPlanarMacroscopicBoundary`: the conditional E4b chain
  from sidewise differential fields and a finite-sheet premise to the pointwise jump predicate.

## iii. Table of contents

- A. Finite divergence laws
- B. Finite circulation laws
- C. Integral and boundary packages

## iv. References

This is a Physlib-original E4b derivation. The audited formal-optics corpus stipulates the planar
boundary predicate rather than deriving it from Maxwell's equations.
-/

@[expose] public section

open Matrix

namespace Electromagnetism
namespace ThreeDimension

open Space Time

noncomputable section

namespace HasPlanarFiniteSheetMaxwellPremise

variable {plane : OrientedAffineHyperplane 3}
  {sidewise : PlanarSidewiseMacroscopicMaxwell plane}
  {surfaceCharge : PlanarFreeSurfaceChargeDensity plane}
  {surfaceCurrent : PlanarFreeSurfaceCurrentDensity plane}
  {cells : PlanarMaxwellThinCells plane}
  {rates : PlanarMaxwellThinCellFluxRates sidewise.fields cells}

/-! ## A. Finite divergence laws -/

/-- The electric-displacement pillbox obeys the literal finite electric Gauss law under the
explicit finite-sheet premise. -/
lemma electricGauss
    (premise : HasPlanarFiniteSheetMaxwellPremise sidewise surfaceCharge surfaceCurrent
      cells rates)
    (t : Time) (x : plane.carrier) (scale : ℕ) :
    (cells.pillbox x).sideFaceAverage .positive
          sidewise.fields.positive.electricDisplacement t x scale -
        (cells.pillbox x).sideFaceAverage .negative
          sidewise.fields.negative.electricDisplacement t x scale +
        (cells.pillbox x).lateralFaceAverage
          sidewise.fields.electricDisplacementFamily t x scale =
      (cells.pillbox x).volumeAverage sidewise.sources.chargeDensity t x scale +
        (cells.pillbox x).surfaceFaceAverage surfaceCharge t x scale := by
  rcases premise.electricDisplacementDivergence t x scale with
    ⟨negativeExceptionalSet, positiveExceptionalSet, regularity⟩
  change (cells.pillbox x).sideFaceAverage .positive
        (plane.restrictFieldToSide .positive sidewise.positiveElectricDisplacement) t x scale -
      (cells.pillbox x).sideFaceAverage .negative
        (plane.restrictFieldToSide .negative sidewise.negativeElectricDisplacement) t x scale +
      (cells.pillbox x).lateralFaceAverage
        (OrientedAffineHyperplane.TwoSidedField.ofFields plane
          sidewise.negativeElectricDisplacement sidewise.positiveElectricDisplacement)
        t x scale = _
  rw [(cells.pillbox x).flux_eq_normalized_bulkDivergence_add_carrierJump
    sidewise.negativeElectricDisplacement sidewise.positiveElectricDisplacement t x scale
    negativeExceptionalSet positiveExceptionalSet regularity]
  rw [mul_add, premise.electricGaussBulk t x scale,
    premise.electricCarrierFace t x scale]

/-- The magnetic-induction pillbox obeys the literal finite magnetic Gauss law under the explicit
finite-sheet premise, including the zero magnetic-sheet identification. -/
lemma magneticGauss
    (premise : HasPlanarFiniteSheetMaxwellPremise sidewise surfaceCharge surfaceCurrent
      cells rates)
    (t : Time) (x : plane.carrier) (scale : ℕ) :
    (cells.pillbox x).sideFaceAverage .positive
          sidewise.fields.positive.magneticInduction t x scale -
        (cells.pillbox x).sideFaceAverage .negative
          sidewise.fields.negative.magneticInduction t x scale +
        (cells.pillbox x).lateralFaceAverage
          sidewise.fields.magneticInductionFamily t x scale = 0 := by
  rcases premise.magneticInductionDivergence t x scale with
    ⟨negativeExceptionalSet, positiveExceptionalSet, regularity⟩
  change (cells.pillbox x).sideFaceAverage .positive
        (plane.restrictFieldToSide .positive sidewise.positiveMagneticInduction) t x scale -
      (cells.pillbox x).sideFaceAverage .negative
        (plane.restrictFieldToSide .negative sidewise.negativeMagneticInduction) t x scale +
      (cells.pillbox x).lateralFaceAverage
        (OrientedAffineHyperplane.TwoSidedField.ofFields plane
          sidewise.negativeMagneticInduction sidewise.positiveMagneticInduction)
        t x scale = _
  rw [(cells.pillbox x).flux_eq_normalized_bulkDivergence_add_carrierJump
    sidewise.negativeMagneticInduction sidewise.positiveMagneticInduction t x scale
    negativeExceptionalSet positiveExceptionalSet regularity]
  rw [mul_add, magneticGaussBulk (sidewise := sidewise) (cells := cells) t x scale,
    premise.magneticCarrierFace t x scale]
  ring

/-! ## B. Finite circulation laws -/

/-- The electric-field thin loop obeys the literal finite Faraday law under the explicit
finite-sheet premise. -/
lemma faraday
    (premise : HasPlanarFiniteSheetMaxwellPremise sidewise surfaceCharge surfaceCurrent
      cells rates)
    (t : Time) (x : plane.carrier) (tangent : plane.tangentSubmodule) (scale : ℕ) :
    (cells.loop x tangent).sideLongEdgeAverage .positive
          sidewise.fields.positive.electricField t x scale -
        (cells.loop x tangent).sideLongEdgeAverage .negative
          sidewise.fields.negative.electricField t x scale +
        (cells.loop x tangent).shortEdgeAverage
          sidewise.fields.electricFieldFamily t x scale =
      -rates.magneticFluxRate t x tangent scale := by
  change (cells.loop x tangent).sideLongEdgeAverage .positive
        (plane.restrictFieldToSide .positive sidewise.positiveElectricField) t x scale -
      (cells.loop x tangent).sideLongEdgeAverage .negative
        (plane.restrictFieldToSide .negative sidewise.negativeElectricField) t x scale +
      (cells.loop x tangent).shortEdgeAverage
        (OrientedAffineHyperplane.TwoSidedField.ofFields plane
          sidewise.negativeElectricField sidewise.positiveElectricField) t x scale = _
  rw [(cells.loop x tangent).circulation_eq_normalized_curlFlux_add_carrierJump
    sidewise.negativeElectricField sidewise.positiveElectricField t x scale
    (premise.electricFieldStokes t x tangent scale)]
  rw [mul_add, premise.faradayBulk t x tangent scale,
    premise.electricCarrierLine t x tangent scale]
  ring

/-- The magnetic-field-strength thin loop obeys the literal finite Ampere--Maxwell law under the
explicit finite-sheet premise. -/
lemma ampereMaxwell
    (premise : HasPlanarFiniteSheetMaxwellPremise sidewise surfaceCharge surfaceCurrent
      cells rates)
    (t : Time) (x : plane.carrier) (tangent : plane.tangentSubmodule) (scale : ℕ) :
    (cells.loop x tangent).sideLongEdgeAverage .positive
          sidewise.fields.positive.magneticFieldStrength t x scale -
        (cells.loop x tangent).sideLongEdgeAverage .negative
          sidewise.fields.negative.magneticFieldStrength t x scale +
        (cells.loop x tangent).shortEdgeAverage
          sidewise.fields.magneticFieldStrengthFamily t x scale =
      (cells.loop x tangent).spanningSurfaceAverage sidewise.sources.currentDensity t x scale +
        rates.electricFluxRate t x tangent scale +
        (cells.loop x tangent).surfaceLineAverage surfaceCurrent t x scale := by
  change (cells.loop x tangent).sideLongEdgeAverage .positive
        (plane.restrictFieldToSide .positive sidewise.positiveMagneticFieldStrength) t x scale -
      (cells.loop x tangent).sideLongEdgeAverage .negative
        (plane.restrictFieldToSide .negative sidewise.negativeMagneticFieldStrength) t x scale +
      (cells.loop x tangent).shortEdgeAverage
        (OrientedAffineHyperplane.TwoSidedField.ofFields plane
          sidewise.negativeMagneticFieldStrength sidewise.positiveMagneticFieldStrength)
        t x scale = _
  rw [(cells.loop x tangent).circulation_eq_normalized_curlFlux_add_carrierJump
    sidewise.negativeMagneticFieldStrength sidewise.positiveMagneticFieldStrength t x scale
    (premise.magneticFieldStokes t x tangent scale)]
  rw [mul_add, premise.ampereMaxwellBulk t x tangent scale,
    premise.magneticCarrierLine t x tangent scale]

/-! ## C. Integral and boundary packages -/

/-- Sidewise differential Maxwell fields satisfying the explicit finite-sheet premise obey all
four literal finite integral Maxwell laws. -/
lemma isPlanarIntegralMacroscopicMaxwell
    (premise : HasPlanarFiniteSheetMaxwellPremise sidewise surfaceCharge surfaceCurrent
      cells rates) :
    IsPlanarIntegralMacroscopicMaxwell sidewise.fields sidewise.sources surfaceCharge
      surfaceCurrent cells rates where
  integrable := premise.integrable
  electricGauss := premise.electricGauss
  magneticGauss := premise.magneticGauss
  faraday := premise.faraday
  ampereMaxwell := premise.ampereMaxwell

/-- Under the explicit finite-sheet premise and the existing thin-cell limiting regularity, the
sidewise differential Maxwell fields satisfy the full sourceful planar boundary law.

The premise appears explicitly: this result does not derive a sheet model from classical smooth
Maxwell equations alone. -/
theorem isPlanarMacroscopicBoundary
    (premise : HasPlanarFiniteSheetMaxwellPremise sidewise surfaceCharge surfaceCurrent
      cells rates)
    (regularity : HasPlanarMaxwellThinCellRegularity
      premise.isPlanarIntegralMacroscopicMaxwell) :
    IsPlanarMacroscopicBoundary sidewise.fields.negative.trace
      sidewise.fields.positive.trace surfaceCharge surfaceCurrent :=
  regularity.isPlanarMacroscopicBoundary

end HasPlanarFiniteSheetMaxwellPremise

end
end ThreeDimension
end Electromagnetism
