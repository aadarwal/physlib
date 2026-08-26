/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Electromagnetism.ThreeDimension.BoundaryConditions.IntegralMacroscopicMaxwell
public import Physlib.SpaceAndTime.Space.Integrals.PlanarThinCellConvergence
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

The principal limits are proved from full one-sided traces, and the sheet limits are proved from
spatial continuity on the carrier. Explicit integrability remains essential for both. The
remaining regularity hypotheses concern fixed lateral/bulk integrals and witnessed flux rates;
they cannot be manufactured by defining a free remainder sequence from the desired jump.

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

open Filter Space Time Matrix

noncomputable section

/-! ## A. Thin-cell regularity -/

/-- Limit hypotheses for the fixed terms of a planar integral Maxwell law.

Integrability is already part of `maxwell`. Full one-sided traces derive the principal limits, and
carrier continuity derives the sheet limits. This structure retains only source continuity and
the genuinely conditional lateral, bulk, and time-rate limits. -/
structure HasPlanarMaxwellThinCellRegularity {plane : OrientedAffineHyperplane 3}
    {fields : PlanarMacroscopicTwoSidedFields plane}
    {sources : PlanarMaxwellBulkSources plane}
    {surfaceCharge : PlanarFreeSurfaceChargeDensity plane}
    {surfaceCurrent : PlanarFreeSurfaceCurrentDensity plane}
    {cells : PlanarMaxwellThinCells plane}
    {rates : PlanarMaxwellThinCellFluxRates fields cells}
    (maxwell : IsPlanarIntegralMacroscopicMaxwell
      fields sources surfaceCharge surfaceCurrent cells rates) : Prop where
  /-- Free surface charge is spatially continuous at every carrier point. -/
  surfaceCharge_continuousAt : ∀ t x, ContinuousAt (surfaceCharge t) x
  /-- Free surface current is spatially continuous at every carrier point. -/
  surfaceCurrent_continuousAt : ∀ t x, ContinuousAt (surfaceCurrent t) x
  /-- The normalized electric-displacement lateral flux vanishes. -/
  electricGauss_lateral : ∀ t x,
    Tendsto (fun scale ↦ (cells.pillbox x).lateralFaceAverage
      fields.electricDisplacementFamily t x scale) atTop (nhds 0)
  /-- The normalized regular bulk-charge volume vanishes. -/
  electricGauss_bulk : ∀ t x,
    Tendsto (fun scale ↦
      (cells.pillbox x).volumeAverage sources.chargeDensity t x scale) atTop (nhds 0)
  /-- The normalized magnetic-induction lateral flux vanishes. -/
  magneticGauss_lateral : ∀ t x,
    Tendsto (fun scale ↦ (cells.pillbox x).lateralFaceAverage
      fields.magneticInductionFamily t x scale) atTop (nhds 0)
  /-- The normalized electric-field short-edge circulation vanishes. -/
  faraday_shortEdges : ∀ t x tangent,
    Tendsto (fun scale ↦ (cells.loop x tangent).shortEdgeAverage
      fields.electricFieldFamily t x scale) atTop (nhds 0)
  /-- The witnessed normalized magnetic-flux rate vanishes. -/
  faraday_magneticFluxRate : ∀ t x tangent,
    Tendsto (fun scale ↦ rates.magneticFluxRate t x tangent scale) atTop (nhds 0)
  /-- The normalized magnetic-field-strength short-edge circulation vanishes. -/
  ampere_shortEdges : ∀ t x tangent,
    Tendsto (fun scale ↦ (cells.loop x tangent).shortEdgeAverage
      fields.magneticFieldStrengthFamily t x scale) atTop (nhds 0)
  /-- The normalized regular bulk-current spanning-surface flux vanishes. -/
  ampere_bulkCurrent : ∀ t x tangent,
    Tendsto (fun scale ↦ (cells.loop x tangent).spanningSurfaceAverage
      sources.currentDensity t x scale) atTop (nhds 0)
  /-- The witnessed normalized electric-displacement flux rate vanishes. -/
  ampere_electricFluxRate : ∀ t x tangent,
    Tendsto (fun scale ↦ rates.electricFluxRate t x tangent scale) atTop (nhds 0)

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

/-- The electric Gauss boundary-limit package follows from the two displacement traces, the
stored lateral/bulk limits, and continuity of the surface charge. -/
lemma electricGauss_hasBoundaryLimits
    (regularity : HasPlanarMaxwellThinCellRegularity maxwell)
    (t : Time) (x : plane.carrier) :
    (maxwell.toBalances.electricGauss t x).HasBoundaryLimits
      (plane.normalComponent (fields.positive.trace.electricDisplacement t x))
      (plane.normalComponent (fields.negative.trace.electricDisplacement t x))
      (surfaceCharge t x) := by
  refine ⟨?_, ?_, regularity.electricGauss_lateral t x,
    regularity.electricGauss_bulk t x, ?_⟩
  · simpa [IsPlanarIntegralMacroscopicMaxwell.toBalances,
      OrientedAffineHyperplane.normalComponent] using
      (cells.pillbox x).sideFaceAverage_tendsto_trace .positive
        fields.positive.electricDisplacement fields.positive.trace.electricDisplacement
        fields.positive.electricDisplacement_hasTrace t x
        (fun scale ↦ (maxwell.integrable.electricGaussPrincipal t x scale).1)
  · simpa [IsPlanarIntegralMacroscopicMaxwell.toBalances,
      OrientedAffineHyperplane.normalComponent] using
      (cells.pillbox x).sideFaceAverage_tendsto_trace .negative
        fields.negative.electricDisplacement fields.negative.trace.electricDisplacement
        fields.negative.electricDisplacement_hasTrace t x
        (fun scale ↦ (maxwell.integrable.electricGaussPrincipal t x scale).2)
  · simpa [IsPlanarIntegralMacroscopicMaxwell.toBalances] using
      (cells.pillbox x).surfaceFaceAverage_tendsto_of_continuousAt
      surfaceCharge t x (regularity.surfaceCharge_continuousAt t x)
      (maxwell.integrable.electricGaussSheet t x)

/-- The magnetic Gauss boundary-limit package follows from the two induction traces and the
stored lateral limit; its bulk and sheet terms are identically zero. -/
lemma magneticGauss_hasBoundaryLimits
    (regularity : HasPlanarMaxwellThinCellRegularity maxwell)
    (t : Time) (x : plane.carrier) :
    (maxwell.toBalances.magneticGauss t x).HasBoundaryLimits
      (plane.normalComponent (fields.positive.trace.magneticInduction t x))
      (plane.normalComponent (fields.negative.trace.magneticInduction t x)) 0 := by
  refine ⟨?_, ?_, regularity.magneticGauss_lateral t x,
    tendsto_const_nhds, tendsto_const_nhds⟩
  · simpa [IsPlanarIntegralMacroscopicMaxwell.toBalances,
      OrientedAffineHyperplane.normalComponent] using
      (cells.pillbox x).sideFaceAverage_tendsto_trace .positive
        fields.positive.magneticInduction fields.positive.trace.magneticInduction
        fields.positive.magneticInduction_hasTrace t x
        (fun scale ↦ (maxwell.integrable.magneticGauss t x scale).1)
  · simpa [IsPlanarIntegralMacroscopicMaxwell.toBalances,
      OrientedAffineHyperplane.normalComponent] using
      (cells.pillbox x).sideFaceAverage_tendsto_trace .negative
        fields.negative.magneticInduction fields.negative.trace.magneticInduction
        fields.negative.magneticInduction_hasTrace t x
        (fun scale ↦ (maxwell.integrable.magneticGauss t x scale).2.1)

/-- The Faraday boundary-limit package follows from the electric traces and the stored
short-edge and magnetic-flux-rate limits. -/
lemma faraday_hasBoundaryLimits
    (regularity : HasPlanarMaxwellThinCellRegularity maxwell)
    (t : Time) (x : plane.carrier) (tangent : plane.tangentSubmodule) :
    (maxwell.toBalances.faraday t x tangent).HasBoundaryLimits
      (inner ℝ (fields.positive.trace.electricField t x)
        (tangent : EuclideanSpace ℝ (Fin 3)))
      (inner ℝ (fields.negative.trace.electricField t x)
        (tangent : EuclideanSpace ℝ (Fin 3))) 0 := by
  refine ⟨?_, ?_, regularity.faraday_shortEdges t x tangent,
    ?_, tendsto_const_nhds⟩
  · simpa [IsPlanarIntegralMacroscopicMaxwell.toBalances] using
      (cells.loop x tangent).sideLongEdgeAverage_tendsto_trace .positive
      fields.positive.electricField fields.positive.trace.electricField
      fields.positive.electricField_hasTrace t x
      (fun scale ↦ (maxwell.integrable.faradayCirculation t x tangent scale).1)
  · simpa [IsPlanarIntegralMacroscopicMaxwell.toBalances] using
      (cells.loop x tangent).sideLongEdgeAverage_tendsto_trace .negative
      fields.negative.electricField fields.negative.trace.electricField
      fields.negative.electricField_hasTrace t x
      (fun scale ↦ (maxwell.integrable.faradayCirculation t x tangent scale).2.1)
  · simpa [IsPlanarIntegralMacroscopicMaxwell.toBalances] using
      (regularity.faraday_magneticFluxRate t x tangent).neg

/-- The Ampere--Maxwell boundary-limit package follows from the magnetic traces, separately
vanishing regular current and displacement-rate terms, and continuity of the surface current. -/
lemma ampereMaxwell_hasBoundaryLimits
    (regularity : HasPlanarMaxwellThinCellRegularity maxwell)
    (t : Time) (x : plane.carrier) (tangent : plane.tangentSubmodule) :
    (maxwell.toBalances.ampereMaxwell t x tangent).HasBoundaryLimits
      (inner ℝ (fields.positive.trace.magneticFieldStrength t x)
        (tangent : EuclideanSpace ℝ (Fin 3)))
      (inner ℝ (fields.negative.trace.magneticFieldStrength t x)
        (tangent : EuclideanSpace ℝ (Fin 3)))
      (inner ℝ (surfaceCurrent t x : EuclideanSpace ℝ (Fin 3))
        (plane.normalVector ⨯ₑ₃ (tangent : EuclideanSpace ℝ (Fin 3)))) := by
  refine ⟨?_, ?_, regularity.ampere_shortEdges t x tangent, ?_, ?_⟩
  · simpa [IsPlanarIntegralMacroscopicMaxwell.toBalances] using
      (cells.loop x tangent).sideLongEdgeAverage_tendsto_trace .positive
      fields.positive.magneticFieldStrength fields.positive.trace.magneticFieldStrength
      fields.positive.magneticFieldStrength_hasTrace t x
      (fun scale ↦ (maxwell.integrable.ampereCirculation t x tangent scale).1)
  · simpa [IsPlanarIntegralMacroscopicMaxwell.toBalances] using
      (cells.loop x tangent).sideLongEdgeAverage_tendsto_trace .negative
      fields.negative.magneticFieldStrength fields.negative.trace.magneticFieldStrength
      fields.negative.magneticFieldStrength_hasTrace t x
      (fun scale ↦ (maxwell.integrable.ampereCirculation t x tangent scale).2.1)
  · simpa [IsPlanarIntegralMacroscopicMaxwell.toBalances] using
      (regularity.ampere_bulkCurrent t x tangent).add
      (regularity.ampere_electricFluxRate t x tangent)
  · simpa [IsPlanarIntegralMacroscopicMaxwell.toBalances] using
      (cells.loop x tangent).surfaceLineAverage_tendsto_of_continuousAt
      surfaceCurrent t x (regularity.surfaceCurrent_continuousAt t x)
      (maxwell.integrable.ampereSheet t x tangent)

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
    (regularity.faraday_hasBoundaryLimits t x tangent)).symm

/-- Electric Gauss pillboxes give the positive-minus-negative normal-D jump. -/
lemma normalElectricDisplacement
    (regularity : HasPlanarMaxwellThinCellRegularity maxwell)
    (t : Time) (x : plane.carrier) :
    plane.normalComponent (fields.positive.trace.electricDisplacement t x) -
        plane.normalComponent (fields.negative.trace.electricDisplacement t x) =
      surfaceCharge t x :=
  (maxwell.toBalances.electricGauss t x).boundaryJump_eq_surfaceLimit
    (regularity.electricGauss_hasBoundaryLimits t x)

/-- Magnetic Gauss pillboxes give continuity of the normal-B trace. -/
lemma normalMagneticInduction
    (regularity : HasPlanarMaxwellThinCellRegularity maxwell)
    (t : Time) (x : plane.carrier) :
    plane.normalComponent (fields.negative.trace.magneticInduction t x) =
      plane.normalComponent (fields.positive.trace.magneticInduction t x) :=
  ((maxwell.toBalances.magneticGauss t x).boundary_eq_of_surface_tendsto_zero
    (regularity.magneticGauss_hasBoundaryLimits t x)).symm

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
        (regularity.ampereMaxwell_hasBoundaryLimits t x tangent)

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
