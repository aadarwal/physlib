/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Electromagnetism.ThreeDimension.BoundaryConditions.IntegralMacroscopicMaxwell
public import Physlib.SpaceAndTime.Space.OrientedAffineHyperplaneCrossProduct

/-!
# Planar Maxwell thin-cell limits

## i. Overview

This file states the exact limit contract between explicit Maxwell pillbox/thin-loop integrals and
the one-sided boundary traces. Four normalized balances correspond to electric Gauss, magnetic
Gauss, Faraday, and Ampere--Maxwell cells. Their actual principal integrals converge to the
appropriate positive- and negative-side trace pairings, lateral and nonsingular bulk terms vanish,
and their actual surface-source integrals converge to the local free surface sources.

The four jump laws are then consequences of the common neutral limit theorem. Tangential electric
continuity is obtained from all tangent pairings. The magnetic-current law first derives the
scalar Ampere loop relation for every tangent direction and then reconstructs
`normalVector cross (H_positive - H_negative)` by oriented cross-product geometry.

The principal and surface sequences come from `PlanarMaxwellThinCellIntegrals`; they are not free
stand-ins for the desired trace values. The lateral and nonsingular bulk sequences remain explicit
data until a differential-to-integral calculus layer constructs those integrands. Merely possessing
one-sided traces or sidewise differential Maxwell solutions does not construct the balances or
prove their limits.

## ii. Key results

- `HasPlanarMaxwellThinCellLimits`: their independent identifications with traces and sources.
- `HasPlanarMaxwellThinCellLimits.isPlanarMacroscopicBoundary`: all four local jump laws.
- `HasPlanarMaxwellThinCellLimits.isSourceFreePlanarMacroscopicBoundary`: the zero-source case.

## iii. Table of contents

- A. Thin-cell trace limits
- B. Derived planar boundary laws

## iv. References

This is a Physlib-original foundation for E4b. The standard thin-loop and pillbox derivation is
not present in the audited formal-optics corpus.
-/

@[expose] public section

namespace Electromagnetism
namespace ThreeDimension

open Space Time Matrix

noncomputable section

/-! ## A. Thin-cell trace limits -/

/-- The limit and source identifications for four planar Maxwell finite-cell balance families.

The bulk field/source and lateral terms are represented by the `bulk` and `remainder` sequences of
each balance and must tend to zero after normalization. The principal and surface limits below are
fixed by the one-sided traces and supplied free surface sources; none is a jump-law hypothesis. -/
structure HasPlanarMaxwellThinCellLimits {plane : OrientedAffineHyperplane 3}
    (fields : PlanarMacroscopicTwoSidedFields plane)
    (surfaceCharge : PlanarFreeSurfaceChargeDensity plane)
    (surfaceCurrent : PlanarFreeSurfaceCurrentDensity plane)
    (integrals : PlanarMaxwellThinCellIntegrals fields surfaceCharge surfaceCurrent) : Prop where
  /-- Electric Gauss pillboxes converge to the two normal-D traces and the free surface charge. -/
  electricGauss : ∀ t x,
    (integrals.toBalances.electricGauss t x).HasBoundaryLimits
      (plane.normalComponent (fields.positive.trace.electricDisplacement t x))
      (plane.normalComponent (fields.negative.trace.electricDisplacement t x))
      (surfaceCharge t x)
  /-- Magnetic Gauss pillboxes converge to the two normal-B traces with no magnetic surface
  charge. -/
  magneticGauss : ∀ t x,
    (integrals.toBalances.magneticGauss t x).HasBoundaryLimits
      (plane.normalComponent (fields.positive.trace.magneticInduction t x))
      (plane.normalComponent (fields.negative.trace.magneticInduction t x)) 0
  /-- Faraday loops converge to electric-field pairings along every tangent direction, while the
  normalized magnetic-flux time derivative vanishes. -/
  faraday : ∀ t x tangent,
    (integrals.toBalances.faraday t x tangent).HasBoundaryLimits
      (inner ℝ (fields.positive.trace.electricField t x)
        (tangent : EuclideanSpace ℝ (Fin 3)))
      (inner ℝ (fields.negative.trace.electricField t x)
        (tangent : EuclideanSpace ℝ (Fin 3))) 0
  /-- Ampere--Maxwell loops converge to magnetic-field pairings and to the surface-current flux
  through the oriented spanning-surface normal `normalVector cross tangent`. -/
  ampereMaxwell : ∀ t x tangent,
    (integrals.toBalances.ampereMaxwell t x tangent).HasBoundaryLimits
      (inner ℝ (fields.positive.trace.magneticFieldStrength t x)
        (tangent : EuclideanSpace ℝ (Fin 3)))
      (inner ℝ (fields.negative.trace.magneticFieldStrength t x)
        (tangent : EuclideanSpace ℝ (Fin 3)))
      (inner ℝ (surfaceCurrent t x : EuclideanSpace ℝ (Fin 3))
        (plane.normalVector ⨯ₑ₃ (tangent : EuclideanSpace ℝ (Fin 3))))

namespace HasPlanarMaxwellThinCellLimits

variable {plane : OrientedAffineHyperplane 3}
  {fields : PlanarMacroscopicTwoSidedFields plane}
  {surfaceCharge : PlanarFreeSurfaceChargeDensity plane}
  {surfaceCurrent : PlanarFreeSurfaceCurrentDensity plane}
  {integrals : PlanarMaxwellThinCellIntegrals fields surfaceCharge surfaceCurrent}

/-! ## B. Derived planar boundary laws -/

/-- Faraday thin-loop balances give equality of the two tangential electric-field traces. -/
lemma tangentialElectricField
    (h : HasPlanarMaxwellThinCellLimits fields surfaceCharge surfaceCurrent integrals)
    (t : Time) (x : plane.carrier) :
    plane.projectionToTangent (fields.negative.trace.electricField t x) =
      plane.projectionToTangent (fields.positive.trace.electricField t x) := by
  apply Subtype.ext
  change plane.tangentialProjection (fields.negative.trace.electricField t x) =
    plane.tangentialProjection (fields.positive.trace.electricField t x)
  apply (plane.tangentialProjection_eq_iff_inner_eq_on_tangent _ _).mpr
  intro tangent
  exact ((integrals.toBalances.faraday t x tangent).boundary_eq_of_surface_tendsto_zero
    (h.faraday t x tangent)).symm

/-- Electric Gauss pillbox balances give the positive-minus-negative normal-D jump. -/
lemma normalElectricDisplacement
    (h : HasPlanarMaxwellThinCellLimits fields surfaceCharge surfaceCurrent integrals)
    (t : Time) (x : plane.carrier) :
    plane.normalComponent (fields.positive.trace.electricDisplacement t x) -
        plane.normalComponent (fields.negative.trace.electricDisplacement t x) =
      surfaceCharge t x :=
  (integrals.toBalances.electricGauss t x).boundaryJump_eq_surfaceLimit
    (h.electricGauss t x)

/-- Magnetic Gauss pillbox balances give continuity of the normal-B trace. -/
lemma normalMagneticInduction
    (h : HasPlanarMaxwellThinCellLimits fields surfaceCharge surfaceCurrent integrals)
    (t : Time) (x : plane.carrier) :
    plane.normalComponent (fields.negative.trace.magneticInduction t x) =
      plane.normalComponent (fields.positive.trace.magneticInduction t x) :=
  ((integrals.toBalances.magneticGauss t x).boundary_eq_of_surface_tendsto_zero
    (h.magneticGauss t x)).symm

/-- Ampere--Maxwell thin-loop balances give the tangent free-current jump of magnetic field
strength. -/
lemma tangentialMagneticFieldStrength
    (h : HasPlanarMaxwellThinCellLimits fields surfaceCharge surfaceCurrent integrals)
    (t : Time) (x : plane.carrier) :
    plane.normalVector ⨯ₑ₃
        (fields.positive.trace.magneticFieldStrength t x -
          fields.negative.trace.magneticFieldStrength t x) =
      (surfaceCurrent t x : EuclideanSpace ℝ (Fin 3)) := by
  apply plane.normalVector_cross_eq_of_tangent_pairings _ _
  · exact (plane.mem_tangentSubmodule (surfaceCurrent t x)).mp (surfaceCurrent t x).property
  · intro tangent
    simpa only [inner_sub_left] using
      (integrals.toBalances.ampereMaxwell t x tangent).boundaryJump_eq_surfaceLimit
        (h.ampereMaxwell t x tangent)

/-- Four convergent Maxwell thin-cell balances imply the full sourceful planar boundary law. -/
lemma isPlanarMacroscopicBoundary
    (h : HasPlanarMaxwellThinCellLimits fields surfaceCharge surfaceCurrent integrals) :
    IsPlanarMacroscopicBoundary fields.negative.trace fields.positive.trace
      surfaceCharge surfaceCurrent := by
  intro t x
  exact ⟨h.tangentialElectricField t x, h.normalElectricDisplacement t x,
    h.normalMagneticInduction t x, h.tangentialMagneticFieldStrength t x⟩

/-- With vanishing free surface charge and current, four convergent Maxwell thin-cell balances
imply the source-free planar boundary law. -/
lemma isSourceFreePlanarMacroscopicBoundary
    {integrals : PlanarMaxwellThinCellIntegrals fields 0 0}
    (h : HasPlanarMaxwellThinCellLimits fields 0 0 integrals) :
    IsSourceFreePlanarMacroscopicBoundary fields.negative.trace fields.positive.trace :=
  h.isPlanarMacroscopicBoundary

end HasPlanarMaxwellThinCellLimits

end
end ThreeDimension
end Electromagnetism
