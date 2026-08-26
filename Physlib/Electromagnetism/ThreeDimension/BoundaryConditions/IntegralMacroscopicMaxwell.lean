/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Electromagnetism.ThreeDimension.BoundaryConditions.OneSidedTrace
public import Physlib.SpaceAndTime.Space.Integrals.PlanarThinCell

/-!
# Integral macroscopic Maxwell laws on planar thin cells

## i. Overview

This file states the finite integral Maxwell laws on explicit shrinking planar pillboxes and thin
loops. Every boundary, bulk, and sheet term is an actual interval, square, rectangle, or box
integral from `Space.Integrals.PlanarThinCell`. Cross-interface faces are split into negative- and
positive-side integrals, so neither bulk field is assigned to the carrier.

Faraday's leading minus and the three Ampere--Maxwell plus signs occur literally in
`IsPlanarIntegralMacroscopicMaxwell`. The time derivatives of magnetic and electric flux are
witnessed by `HasDerivAt`; Mathlib's totalized derivative is not used. The predicate also carries
integrability of every displayed iterated pullback, preventing a nonintegrable term from silently
becoming a zero Bochner integral.

The total sourceful integral balance remains an explicit physical premise. Two independent smooth
sidewise differential Maxwell solutions cannot produce a carrier-supported charge or current
sheet. A future weak or measure-valued Maxwell layer may construct this premise; the current E4b
slice derives the local jump laws from it under separately stated thin-cell limits.

## ii. Key results

- `PlanarMaxwellBulkSources`: two-sided bulk free charge and free current.
- `PlanarMaxwellThinCells`: the shrinking pillbox and loop geometry.
- `PlanarMaxwellThinCellFluxRates`: witnessed derivatives of actual cell fluxes.
- `ArePlanarMaxwellThinCellTermsIntegrable`: integrability of every displayed pullback.
- `IsPlanarIntegralMacroscopicMaxwell`: the four sourceful finite integral laws.
- `IsPlanarIntegralMacroscopicMaxwell.toBalances`: their neutral normalized-balance form.

## iii. Table of contents

- A. Sources and thin-cell geometry
- B. Witnessed flux derivatives
- C. Integrability of the displayed terms
- D. Integral Maxwell laws
- E. Neutral normalized balances

## iv. References

This is a Physlib-original E4b foundation. The standard integral Maxwell laws motivate the
predicate; no audited external formal-optics development supplies this derivation layer.
-/

@[expose] public section

namespace Electromagnetism
namespace ThreeDimension

open Space Time

noncomputable section

/-! ## A. Sources and thin-cell geometry -/

/-- Bulk free electric charge and current on the two open half-spaces.

Carrier-supported free charge and current are represented separately by
`PlanarFreeSurfaceChargeDensity` and `PlanarFreeSurfaceCurrentDensity`. -/
structure PlanarMaxwellBulkSources (plane : OrientedAffineHyperplane 3) where
  /-- Free electric charge density on the two bulk sides. -/
  chargeDensity : plane.TwoSidedField Time ℝ
  /-- Free electric current density on the two bulk sides. -/
  currentDensity : plane.TwoSidedField Time (EuclideanSpace ℝ (Fin 3))

/-- Shrinking pillbox and tangent-indexed thin-loop families at every carrier point. -/
structure PlanarMaxwellThinCells (plane : OrientedAffineHyperplane 3) where
  /-- Pillbox geometry used by the two Gauss laws. -/
  pillbox : plane.carrier → PlanarPillboxFamily plane
  /-- Thin-loop geometry used by Faraday and Ampere--Maxwell. -/
  loop : (x : plane.carrier) → (tangent : plane.tangentSubmodule) →
    PlanarThinLoopFamily plane tangent

/-! ## B. Witnessed flux derivatives -/

/-- Derivatives in time of the actual normalized magnetic and electric flux integrals through
every thin loop. -/
structure PlanarMaxwellThinCellFluxRates {plane : OrientedAffineHyperplane 3}
    (fields : PlanarMacroscopicTwoSidedFields plane)
    (cells : PlanarMaxwellThinCells plane) where
  /-- Time derivative of the magnetic-induction flux through a thin loop. -/
  magneticFluxRate : Time → (x : plane.carrier) →
    plane.tangentSubmodule → ℕ → ℝ
  /-- The magnetic rate is the derivative of the actual normalized magnetic flux. -/
  magneticFlux_hasDerivAt : ∀ t x tangent scale,
    HasDerivAt
      (fun s ↦ (cells.loop x tangent).spanningSurfaceAverage
        fields.magneticInductionFamily s x scale)
      (magneticFluxRate t x tangent scale) t
  /-- Time derivative of the electric-displacement flux through a thin loop. -/
  electricFluxRate : Time → (x : plane.carrier) →
    plane.tangentSubmodule → ℕ → ℝ
  /-- The electric rate is the derivative of the actual normalized electric flux. -/
  electricFlux_hasDerivAt : ∀ t x tangent scale,
    HasDerivAt
      (fun s ↦ (cells.loop x tangent).spanningSurfaceAverage
        fields.electricDisplacementFamily s x scale)
      (electricFluxRate t x tangent scale) t

/-! ## C. Integrability of the displayed terms -/

/-- Integrability of every path, face, and volume pullback occurring in the planar integral
Maxwell laws.

These hypotheses are intentionally explicit because interval and Bochner integrals in Mathlib are
totalized. The nested predicates require integrability at every displayed level. -/
structure ArePlanarMaxwellThinCellTermsIntegrable {plane : OrientedAffineHyperplane 3}
    (fields : PlanarMacroscopicTwoSidedFields plane)
    (sources : PlanarMaxwellBulkSources plane)
    (surfaceCharge : PlanarFreeSurfaceChargeDensity plane)
    (surfaceCurrent : PlanarFreeSurfaceCurrentDensity plane)
    (cells : PlanarMaxwellThinCells plane) : Prop where
  /-- Electric-displacement principal faces are integrable. -/
  electricGaussPrincipal : ∀ t x scale,
    (cells.pillbox x).SideFaceIntegrable .positive
        fields.positive.electricDisplacement t x scale ∧
      (cells.pillbox x).SideFaceIntegrable .negative
        fields.negative.electricDisplacement t x scale
  /-- Electric-displacement lateral faces are integrable. -/
  electricGaussLateral : ∀ t x scale,
    (cells.pillbox x).LateralFacesIntegrable
      fields.electricDisplacementFamily t x scale
  /-- Bulk free-charge volumes are integrable. -/
  electricGaussVolume : ∀ t x scale,
    (cells.pillbox x).VolumeIntegrable sources.chargeDensity t x scale
  /-- Free surface-charge faces are integrable. -/
  electricGaussSheet : ∀ t x scale,
    (cells.pillbox x).SurfaceFaceIntegrable surfaceCharge t x scale
  /-- Magnetic-induction principal and lateral faces are integrable. -/
  magneticGauss : ∀ t x scale,
    (cells.pillbox x).SideFaceIntegrable .positive
        fields.positive.magneticInduction t x scale ∧
      (cells.pillbox x).SideFaceIntegrable .negative
        fields.negative.magneticInduction t x scale ∧
      (cells.pillbox x).LateralFacesIntegrable fields.magneticInductionFamily t x scale
  /-- Electric-field long and short edges are integrable. -/
  faradayCirculation : ∀ t x tangent scale,
    (cells.loop x tangent).SideLongEdgeIntegrable .positive
        fields.positive.electricField t x scale ∧
      (cells.loop x tangent).SideLongEdgeIntegrable .negative
        fields.negative.electricField t x scale ∧
      (cells.loop x tangent).ShortEdgesIntegrable fields.electricFieldFamily t x scale
  /-- Magnetic-induction spanning-surface pullbacks are integrable. -/
  faradayFlux : ∀ t x tangent scale,
    (cells.loop x tangent).SpanningSurfaceIntegrable
      fields.magneticInductionFamily t x scale
  /-- Magnetic-field-strength long and short edges are integrable. -/
  ampereCirculation : ∀ t x tangent scale,
    (cells.loop x tangent).SideLongEdgeIntegrable .positive
        fields.positive.magneticFieldStrength t x scale ∧
      (cells.loop x tangent).SideLongEdgeIntegrable .negative
        fields.negative.magneticFieldStrength t x scale ∧
      (cells.loop x tangent).ShortEdgesIntegrable
        fields.magneticFieldStrengthFamily t x scale
  /-- Bulk-current and electric-displacement spanning surfaces are integrable. -/
  ampereFlux : ∀ t x tangent scale,
    (cells.loop x tangent).SpanningSurfaceIntegrable sources.currentDensity t x scale ∧
      (cells.loop x tangent).SpanningSurfaceIntegrable
        fields.electricDisplacementFamily t x scale
  /-- Free surface-current line pullbacks are integrable. -/
  ampereSheet : ∀ t x tangent scale,
    (cells.loop x tangent).SurfaceLineIntegrable surfaceCurrent t x scale

/-! ## D. Integral Maxwell laws -/

/-- The four finite integral macroscopic Maxwell laws on every shrinking planar cell.

The equations are normalized by the principal face area or long-edge length. This common nonzero
factor does not alter the integral law and makes the subsequent thin-cell limits finite. -/
structure IsPlanarIntegralMacroscopicMaxwell {plane : OrientedAffineHyperplane 3}
    (fields : PlanarMacroscopicTwoSidedFields plane)
    (sources : PlanarMaxwellBulkSources plane)
    (surfaceCharge : PlanarFreeSurfaceChargeDensity plane)
    (surfaceCurrent : PlanarFreeSurfaceCurrentDensity plane)
    (cells : PlanarMaxwellThinCells plane)
    (rates : PlanarMaxwellThinCellFluxRates fields cells) : Prop where
  /-- Every integral appearing below has its required integrability witnesses. -/
  integrable : ArePlanarMaxwellThinCellTermsIntegrable
    fields sources surfaceCharge surfaceCurrent cells
  /-- Electric Gauss law, including bulk and carrier-supported free charge. -/
  electricGauss : ∀ t x scale,
    (cells.pillbox x).sideFaceAverage .positive
          fields.positive.electricDisplacement t x scale -
        (cells.pillbox x).sideFaceAverage .negative
          fields.negative.electricDisplacement t x scale +
        (cells.pillbox x).lateralFaceAverage
          fields.electricDisplacementFamily t x scale =
      (cells.pillbox x).volumeAverage sources.chargeDensity t x scale +
        (cells.pillbox x).surfaceFaceAverage surfaceCharge t x scale
  /-- Magnetic Gauss law, with no magnetic charge in the bulk or on the carrier. -/
  magneticGauss : ∀ t x scale,
    (cells.pillbox x).sideFaceAverage .positive
          fields.positive.magneticInduction t x scale -
        (cells.pillbox x).sideFaceAverage .negative
          fields.negative.magneticInduction t x scale +
        (cells.pillbox x).lateralFaceAverage fields.magneticInductionFamily t x scale = 0
  /-- Faraday's law with its literal leading minus on the magnetic-flux rate. -/
  faraday : ∀ t x tangent scale,
    (cells.loop x tangent).sideLongEdgeAverage .positive
          fields.positive.electricField t x scale -
        (cells.loop x tangent).sideLongEdgeAverage .negative
          fields.negative.electricField t x scale +
        (cells.loop x tangent).shortEdgeAverage fields.electricFieldFamily t x scale =
      -rates.magneticFluxRate t x tangent scale
  /-- Ampere--Maxwell law with literal plus signs for bulk current, displacement-flux rate, and
  carrier-supported free current. -/
  ampereMaxwell : ∀ t x tangent scale,
    (cells.loop x tangent).sideLongEdgeAverage .positive
          fields.positive.magneticFieldStrength t x scale -
        (cells.loop x tangent).sideLongEdgeAverage .negative
          fields.negative.magneticFieldStrength t x scale +
        (cells.loop x tangent).shortEdgeAverage
          fields.magneticFieldStrengthFamily t x scale =
      (cells.loop x tangent).spanningSurfaceAverage sources.currentDensity t x scale +
        rates.electricFluxRate t x tangent scale +
        (cells.loop x tangent).surfaceLineAverage surfaceCurrent t x scale

/-! ## E. Neutral normalized balances -/

/-- The four normalized finite-cell balances extracted from literal integral Maxwell laws. -/
structure PlanarMaxwellThinCellBalances (plane : OrientedAffineHyperplane 3) where
  /-- Normalized electric-displacement pillbox balances. -/
  electricGauss : Time → plane.carrier → NormalizedThinCellBalance
  /-- Normalized magnetic-induction pillbox balances. -/
  magneticGauss : Time → plane.carrier → NormalizedThinCellBalance
  /-- Normalized electric-field thin-loop balances for every tangent direction. -/
  faraday : Time → plane.carrier → plane.tangentSubmodule → NormalizedThinCellBalance
  /-- Normalized magnetic-field-strength thin-loop balances for every tangent direction. -/
  ampereMaxwell : Time → plane.carrier → plane.tangentSubmodule →
    NormalizedThinCellBalance

namespace IsPlanarIntegralMacroscopicMaxwell

/-- Forget the displayed integrands after an integral Maxwell proof has fixed every term and sign.
This is an internal bridge to the neutral limit algebra, not a user-supplied physics premise. -/
def toBalances {plane : OrientedAffineHyperplane 3}
    {fields : PlanarMacroscopicTwoSidedFields plane}
    {sources : PlanarMaxwellBulkSources plane}
    {surfaceCharge : PlanarFreeSurfaceChargeDensity plane}
    {surfaceCurrent : PlanarFreeSurfaceCurrentDensity plane}
    {cells : PlanarMaxwellThinCells plane}
    {rates : PlanarMaxwellThinCellFluxRates fields cells}
    (maxwell : IsPlanarIntegralMacroscopicMaxwell
      fields sources surfaceCharge surfaceCurrent cells rates) :
    PlanarMaxwellThinCellBalances plane where
  electricGauss t x :=
    { positiveBoundary := fun scale ↦
        (cells.pillbox x).sideFaceAverage .positive
          fields.positive.electricDisplacement t x scale
      negativeBoundary := fun scale ↦
        (cells.pillbox x).sideFaceAverage .negative
          fields.negative.electricDisplacement t x scale
      remainder := fun scale ↦
        (cells.pillbox x).lateralFaceAverage
          fields.electricDisplacementFamily t x scale
      bulk := fun scale ↦
        (cells.pillbox x).volumeAverage sources.chargeDensity t x scale
      surface := fun scale ↦
        (cells.pillbox x).surfaceFaceAverage surfaceCharge t x scale
      balance := maxwell.electricGauss t x }
  magneticGauss t x :=
    { positiveBoundary := fun scale ↦
        (cells.pillbox x).sideFaceAverage .positive
          fields.positive.magneticInduction t x scale
      negativeBoundary := fun scale ↦
        (cells.pillbox x).sideFaceAverage .negative
          fields.negative.magneticInduction t x scale
      remainder := fun scale ↦
        (cells.pillbox x).lateralFaceAverage fields.magneticInductionFamily t x scale
      bulk := 0
      surface := 0
      balance := by
        intro scale
        simpa using maxwell.magneticGauss t x scale }
  faraday t x tangent :=
    { positiveBoundary := fun scale ↦
        (cells.loop x tangent).sideLongEdgeAverage .positive
          fields.positive.electricField t x scale
      negativeBoundary := fun scale ↦
        (cells.loop x tangent).sideLongEdgeAverage .negative
          fields.negative.electricField t x scale
      remainder := fun scale ↦
        (cells.loop x tangent).shortEdgeAverage fields.electricFieldFamily t x scale
      bulk := fun scale ↦ -rates.magneticFluxRate t x tangent scale
      surface := 0
      balance := by
        intro scale
        simpa using maxwell.faraday t x tangent scale }
  ampereMaxwell t x tangent :=
    { positiveBoundary := fun scale ↦
        (cells.loop x tangent).sideLongEdgeAverage .positive
          fields.positive.magneticFieldStrength t x scale
      negativeBoundary := fun scale ↦
        (cells.loop x tangent).sideLongEdgeAverage .negative
          fields.negative.magneticFieldStrength t x scale
      remainder := fun scale ↦
        (cells.loop x tangent).shortEdgeAverage
          fields.magneticFieldStrengthFamily t x scale
      bulk := fun scale ↦
        (cells.loop x tangent).spanningSurfaceAverage sources.currentDensity t x scale +
          rates.electricFluxRate t x tangent scale
      surface := fun scale ↦
        (cells.loop x tangent).surfaceLineAverage surfaceCurrent t x scale
      balance := maxwell.ampereMaxwell t x tangent }

end IsPlanarIntegralMacroscopicMaxwell

end
end ThreeDimension
end Electromagnetism
