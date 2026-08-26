/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Electromagnetism.ThreeDimension.BoundaryConditions.IntegralMacroscopicMaxwell
public import Physlib.SpaceAndTime.Space.OrientedAffineHyperplaneCrossProduct

/-!
# Boundary laws from planar integral Maxwell thin cells

## i. Overview

This file states the regularity and limiting contract for the actual integral terms in
`IsPlanarIntegralMacroscopicMaxwell`. Principal face and edge averages converge to the genuine
one-sided traces, short-edge and lateral-face terms vanish, regular bulk charge/current and
time-varying flux contributions vanish after normalization, and sheet-source averages converge to
the supplied carrier sources.

The four pointwise jump laws then follow from the neutral thin-cell limit lemma. Tangential
electric continuity is recovered from every tangent pairing. The Ampere--Maxwell scalar relation
is reconstructed as `normalVector cross (H_positive - H_negative) = surfaceCurrent` by oriented
cross-product geometry.

The regularity hypotheses are about fixed actual integrals and witnessed flux rates. They cannot
be manufactured by defining a free remainder sequence from the desired jump. This file does not
claim that pointwise side traces alone prove these hypotheses; the relevant boundedness,
source-sheet regularity, and time/integral interchange remain explicit.

## ii. Key results

- `HasPlanarMaxwellThinCellRegularity`: limits of the fixed integral Maxwell terms.
- `HasPlanarMaxwellThinCellRegularity.tangentialElectricField`: Faraday thin-loop consequence.
- `HasPlanarMaxwellThinCellRegularity.normalElectricDisplacement`: electric Gauss consequence.
- `HasPlanarMaxwellThinCellRegularity.normalMagneticInduction`: magnetic Gauss consequence.
- `HasPlanarMaxwellThinCellRegularity.tangentialMagneticFieldStrength`: Ampere consequence.
- `HasPlanarMaxwellThinCellRegularity.isPlanarMacroscopicBoundary`: the four-law result.

## iii. Table of contents

- A. Thin-cell regularity
- B. Derived planar boundary laws

## iv. References

This formalizes the standard thin-loop and pillbox derivation as a Physlib-original foundation.
The audited formal-optics corpus stipulates its boundary predicate instead of deriving it.
-/

@[expose] public section

namespace Electromagnetism
namespace ThreeDimension

open Space Time Matrix

noncomputable section

/-! ## A. Thin-cell regularity -/

/-- Limit hypotheses for the fixed terms of a planar integral Maxwell law.

Integrability is already part of `maxwell`. The five convergence statements for each cell identify
the principal averages with one-sided traces, make regular lateral/bulk terms vanish, and identify
the sheet average with the local carrier source. -/
structure HasPlanarMaxwellThinCellRegularity {plane : OrientedAffineHyperplane 3}
    {fields : PlanarMacroscopicTwoSidedFields plane}
    {sources : PlanarMaxwellBulkSources plane}
    {surfaceCharge : PlanarFreeSurfaceChargeDensity plane}
    {surfaceCurrent : PlanarFreeSurfaceCurrentDensity plane}
    {cells : PlanarMaxwellThinCells plane}
    {rates : PlanarMaxwellThinCellFluxRates fields cells}
    (maxwell : IsPlanarIntegralMacroscopicMaxwell
      fields sources surfaceCharge surfaceCurrent cells rates) : Prop where
  /-- Electric Gauss pillboxes converge to the normal-D traces and free surface charge. -/
  electricGauss : ∀ t x,
    (maxwell.toBalances.electricGauss t x).HasBoundaryLimits
      (plane.normalComponent (fields.positive.trace.electricDisplacement t x))
      (plane.normalComponent (fields.negative.trace.electricDisplacement t x))
      (surfaceCharge t x)
  /-- Magnetic Gauss pillboxes converge to the normal-B traces with exactly zero magnetic source. -/
  magneticGauss : ∀ t x,
    (maxwell.toBalances.magneticGauss t x).HasBoundaryLimits
      (plane.normalComponent (fields.positive.trace.magneticInduction t x))
      (plane.normalComponent (fields.negative.trace.magneticInduction t x)) 0
  /-- Faraday loops converge to all tangent electric pairings, while the witnessed normalized
  magnetic-flux rate vanishes. -/
  faraday : ∀ t x tangent,
    (maxwell.toBalances.faraday t x tangent).HasBoundaryLimits
      (inner ℝ (fields.positive.trace.electricField t x)
        (tangent : EuclideanSpace ℝ (Fin 3)))
      (inner ℝ (fields.negative.trace.electricField t x)
        (tangent : EuclideanSpace ℝ (Fin 3))) 0
  /-- Ampere--Maxwell loops converge to all tangent magnetic pairings and the oriented line
  pairing of the free surface current. -/
  ampereMaxwell : ∀ t x tangent,
    (maxwell.toBalances.ampereMaxwell t x tangent).HasBoundaryLimits
      (inner ℝ (fields.positive.trace.magneticFieldStrength t x)
        (tangent : EuclideanSpace ℝ (Fin 3)))
      (inner ℝ (fields.negative.trace.magneticFieldStrength t x)
        (tangent : EuclideanSpace ℝ (Fin 3)))
      (inner ℝ (surfaceCurrent t x : EuclideanSpace ℝ (Fin 3))
        (plane.normalVector ⨯ₑ₃ (tangent : EuclideanSpace ℝ (Fin 3))))

namespace HasPlanarMaxwellThinCellRegularity

variable {plane : OrientedAffineHyperplane 3}
  {fields : PlanarMacroscopicTwoSidedFields plane}
  {sources : PlanarMaxwellBulkSources plane}
  {surfaceCharge : PlanarFreeSurfaceChargeDensity plane}
  {surfaceCurrent : PlanarFreeSurfaceCurrentDensity plane}
  {cells : PlanarMaxwellThinCells plane}
  {rates : PlanarMaxwellThinCellFluxRates fields cells}
  {maxwell : IsPlanarIntegralMacroscopicMaxwell
    fields sources surfaceCharge surfaceCurrent cells rates}

/-! ## B. Derived planar boundary laws -/

/-- Faraday thin-loop balances give equality of the two tangential electric-field traces. -/
lemma tangentialElectricField
    (regularity : HasPlanarMaxwellThinCellRegularity maxwell)
    (t : Time) (x : plane.carrier) :
    plane.projectionToTangent (fields.negative.trace.electricField t x) =
      plane.projectionToTangent (fields.positive.trace.electricField t x) := by
  apply Subtype.ext
  change plane.tangentialProjection (fields.negative.trace.electricField t x) =
    plane.tangentialProjection (fields.positive.trace.electricField t x)
  apply (plane.tangentialProjection_eq_iff_inner_eq_on_tangent _ _).mpr
  intro tangent
  exact ((maxwell.toBalances.faraday t x tangent).boundary_eq_of_surface_tendsto_zero
    (regularity.faraday t x tangent)).symm

/-- Electric Gauss pillboxes give the positive-minus-negative normal-D jump. -/
lemma normalElectricDisplacement
    (regularity : HasPlanarMaxwellThinCellRegularity maxwell)
    (t : Time) (x : plane.carrier) :
    plane.normalComponent (fields.positive.trace.electricDisplacement t x) -
        plane.normalComponent (fields.negative.trace.electricDisplacement t x) =
      surfaceCharge t x :=
  (maxwell.toBalances.electricGauss t x).boundaryJump_eq_surfaceLimit
    (regularity.electricGauss t x)

/-- Magnetic Gauss pillboxes give continuity of the normal-B trace. -/
lemma normalMagneticInduction
    (regularity : HasPlanarMaxwellThinCellRegularity maxwell)
    (t : Time) (x : plane.carrier) :
    plane.normalComponent (fields.negative.trace.magneticInduction t x) =
      plane.normalComponent (fields.positive.trace.magneticInduction t x) :=
  ((maxwell.toBalances.magneticGauss t x).boundary_eq_of_surface_tendsto_zero
    (regularity.magneticGauss t x)).symm

/-- Ampere--Maxwell thin-loop balances give the tangent free-current jump of magnetic field
strength. -/
lemma tangentialMagneticFieldStrength
    (regularity : HasPlanarMaxwellThinCellRegularity maxwell)
    (t : Time) (x : plane.carrier) :
    plane.normalVector ⨯ₑ₃
        (fields.positive.trace.magneticFieldStrength t x -
          fields.negative.trace.magneticFieldStrength t x) =
      (surfaceCurrent t x : EuclideanSpace ℝ (Fin 3)) := by
  apply plane.normalVector_cross_eq_of_tangent_pairings _ _
  · exact (plane.mem_tangentSubmodule (surfaceCurrent t x)).mp (surfaceCurrent t x).property
  · intro tangent
    simpa only [inner_sub_left] using
      (maxwell.toBalances.ampereMaxwell t x tangent).boundaryJump_eq_surfaceLimit
        (regularity.ampereMaxwell t x tangent)

/-- The four finite integral Maxwell laws and their thin-cell regularity imply the full sourceful
planar boundary law. -/
theorem isPlanarMacroscopicBoundary
    (regularity : HasPlanarMaxwellThinCellRegularity maxwell) :
    IsPlanarMacroscopicBoundary fields.negative.trace fields.positive.trace
      surfaceCharge surfaceCurrent := by
  intro t x
  exact ⟨regularity.tangentialElectricField t x,
    regularity.normalElectricDisplacement t x,
    regularity.normalMagneticInduction t x,
    regularity.tangentialMagneticFieldStrength t x⟩

/-- With vanishing free surface charge and current, the integral Maxwell derivation gives the
zero-free-surface-source planar boundary law. Bulk sources remain governed by their vanishing
thin-cell limits. -/
theorem isSourceFreePlanarMacroscopicBoundary
    {maxwell : IsPlanarIntegralMacroscopicMaxwell fields sources 0 0 cells rates}
    (regularity : HasPlanarMaxwellThinCellRegularity maxwell) :
    IsSourceFreePlanarMacroscopicBoundary fields.negative.trace fields.positive.trace :=
  regularity.isPlanarMacroscopicBoundary

end HasPlanarMaxwellThinCellRegularity

end
end ThreeDimension
end Electromagnetism
