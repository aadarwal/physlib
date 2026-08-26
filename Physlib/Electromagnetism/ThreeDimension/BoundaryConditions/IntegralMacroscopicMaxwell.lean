/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Electromagnetism.ThreeDimension.BoundaryConditions.OneSidedTrace
public import Physlib.SpaceAndTime.Space.Integrals.PlanarThinCell

/-!
# Integral macroscopic Maxwell data on planar thin cells

## i. Overview

This file connects explicit planar thin-loop and pillbox averages to four finite-scale Maxwell
balances. Positive- and negative-side principal terms are actual normalized interval or square
integrals of the corresponding local fields. Free surface charge and current terms are actual
normalized integrals of the supplied carrier sources.

The remaining lateral and nonsingular bulk terms are stored explicitly. They stand respectively
for the short-edge/lateral-face integrals and for the volume-source or time-varying-flux terms.
Every balance is required at each finite scale before any limiting argument. The next layer states
the uniform limit hypotheses needed to show these remainder and bulk terms vanish.

This module does not derive the finite balances from differential Maxwell equations, Stokes, or
the divergence theorem. It therefore exposes the precise remaining foundation boundary rather
than hiding it inside a local jump predicate.

## ii. Key results

- `PlanarMaxwellThinCellIntegrals`: explicit cell geometry, integral principal/source terms, and
  finite-scale Maxwell balances.
- `PlanarMaxwellThinCellIntegrals.toBalances`: the common normalized-balance representation used
  by the limit theorem.

## iii. Table of contents

- A. Maxwell thin-cell balance families
- B. Explicit integral data
- C. Common normalized balances

## iv. References

This is a Physlib-original E4b foundation. No audited external formal-optics source supplies this
integral interface.
-/

@[expose] public section

namespace Electromagnetism
namespace ThreeDimension

open Space Time

noncomputable section

/-! ## A. Maxwell thin-cell balance families -/

/-- The four normalized finite-cell balance families used in the planar Maxwell jump derivation.

The electric and magnetic Gauss families are pillbox balances. The Faraday and Ampere--Maxwell
families are thin-loop balances indexed additionally by a tangent direction. -/
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

/-! ## B. Explicit integral data -/

/-- Explicit principal/source integrals and finite-scale Maxwell balances for shrinking planar
pillboxes and thin loops.

The stored `remainder` functions are normalized lateral-face or short-edge integrals. The stored
`bulk` functions are normalized volume-source or time-varying-flux integrals. Their concrete
integrands remain visible as data until the differential-to-integral calculus layer constructs
them. -/
structure PlanarMaxwellThinCellIntegrals {plane : OrientedAffineHyperplane 3}
    (fields : PlanarMacroscopicTwoSidedFields plane)
    (surfaceCharge : PlanarFreeSurfaceChargeDensity plane)
    (surfaceCurrent : PlanarFreeSurfaceCurrentDensity plane) where
  /-- Shrinking pillbox geometry at every carrier point. -/
  pillbox : plane.carrier → PlanarPillboxFamily plane
  /-- Shrinking thin-loop geometry at every carrier point and tangent direction. -/
  loop : (x : plane.carrier) → (tangent : plane.tangentSubmodule) →
    PlanarThinLoopFamily plane tangent
  /-- Normalized lateral electric-displacement flux. -/
  electricGaussRemainder : Time → plane.carrier → ℕ → ℝ
  /-- Normalized nonsingular bulk free-charge contribution. -/
  electricGaussBulk : Time → plane.carrier → ℕ → ℝ
  /-- Electric Gauss balance at every finite pillbox scale. -/
  electricGaussBalance : ∀ t x scale,
    (pillbox x).sideFaceAverage .positive fields.positive.electricDisplacement t x scale -
        (pillbox x).sideFaceAverage .negative fields.negative.electricDisplacement t x scale +
      electricGaussRemainder t x scale =
        electricGaussBulk t x scale +
          (pillbox x).surfaceFaceAverage surfaceCharge t x scale
  /-- Normalized lateral magnetic-induction flux. -/
  magneticGaussRemainder : Time → plane.carrier → ℕ → ℝ
  /-- Normalized bulk magnetic-divergence contribution. -/
  magneticGaussBulk : Time → plane.carrier → ℕ → ℝ
  /-- Magnetic Gauss balance at every finite pillbox scale. -/
  magneticGaussBalance : ∀ t x scale,
    (pillbox x).sideFaceAverage .positive fields.positive.magneticInduction t x scale -
        (pillbox x).sideFaceAverage .negative fields.negative.magneticInduction t x scale +
      magneticGaussRemainder t x scale = magneticGaussBulk t x scale + 0
  /-- Normalized short-edge electric circulation. -/
  faradayRemainder : Time → (x : plane.carrier) → plane.tangentSubmodule → ℕ → ℝ
  /-- Normalized negative time derivative of magnetic flux. -/
  faradayBulk : Time → (x : plane.carrier) → plane.tangentSubmodule → ℕ → ℝ
  /-- Faraday balance at every finite thin-loop scale. -/
  faradayBalance : ∀ t x tangent scale,
    (loop x tangent).sideLongEdgeAverage .positive fields.positive.electricField t x scale -
        (loop x tangent).sideLongEdgeAverage .negative fields.negative.electricField t x scale +
      faradayRemainder t x tangent scale = faradayBulk t x tangent scale + 0
  /-- Normalized short-edge magnetic-field-strength circulation. -/
  ampereMaxwellRemainder : Time → (x : plane.carrier) →
    plane.tangentSubmodule → ℕ → ℝ
  /-- Normalized bulk free-current plus electric-displacement-flux contribution. -/
  ampereMaxwellBulk : Time → (x : plane.carrier) →
    plane.tangentSubmodule → ℕ → ℝ
  /-- Ampere--Maxwell balance at every finite thin-loop scale. -/
  ampereMaxwellBalance : ∀ t x tangent scale,
    (loop x tangent).sideLongEdgeAverage .positive
          fields.positive.magneticFieldStrength t x scale -
        (loop x tangent).sideLongEdgeAverage .negative
          fields.negative.magneticFieldStrength t x scale +
      ampereMaxwellRemainder t x tangent scale =
        ampereMaxwellBulk t x tangent scale +
          (loop x tangent).surfaceLineAverage surfaceCurrent t x scale

namespace PlanarMaxwellThinCellIntegrals

/-! ## C. Common normalized balances -/

/-- Forget the integrands while retaining the five exact normalized terms of each Maxwell cell
balance. The principal and surface sequences remain definitionally the explicit integrals above. -/
def toBalances {plane : OrientedAffineHyperplane 3}
    {fields : PlanarMacroscopicTwoSidedFields plane}
    {surfaceCharge : PlanarFreeSurfaceChargeDensity plane}
    {surfaceCurrent : PlanarFreeSurfaceCurrentDensity plane}
    (integrals : PlanarMaxwellThinCellIntegrals fields surfaceCharge surfaceCurrent) :
    PlanarMaxwellThinCellBalances plane where
  electricGauss t x :=
    { positiveBoundary := fun scale ↦
        (integrals.pillbox x).sideFaceAverage .positive
          fields.positive.electricDisplacement t x scale
      negativeBoundary := fun scale ↦
        (integrals.pillbox x).sideFaceAverage .negative
          fields.negative.electricDisplacement t x scale
      remainder := integrals.electricGaussRemainder t x
      bulk := integrals.electricGaussBulk t x
      surface := fun scale ↦
        (integrals.pillbox x).surfaceFaceAverage surfaceCharge t x scale
      balance := integrals.electricGaussBalance t x }
  magneticGauss t x :=
    { positiveBoundary := fun scale ↦
        (integrals.pillbox x).sideFaceAverage .positive
          fields.positive.magneticInduction t x scale
      negativeBoundary := fun scale ↦
        (integrals.pillbox x).sideFaceAverage .negative
          fields.negative.magneticInduction t x scale
      remainder := integrals.magneticGaussRemainder t x
      bulk := integrals.magneticGaussBulk t x
      surface := 0
      balance := integrals.magneticGaussBalance t x }
  faraday t x tangent :=
    { positiveBoundary := fun scale ↦
        (integrals.loop x tangent).sideLongEdgeAverage .positive
          fields.positive.electricField t x scale
      negativeBoundary := fun scale ↦
        (integrals.loop x tangent).sideLongEdgeAverage .negative
          fields.negative.electricField t x scale
      remainder := integrals.faradayRemainder t x tangent
      bulk := integrals.faradayBulk t x tangent
      surface := 0
      balance := integrals.faradayBalance t x tangent }
  ampereMaxwell t x tangent :=
    { positiveBoundary := fun scale ↦
        (integrals.loop x tangent).sideLongEdgeAverage .positive
          fields.positive.magneticFieldStrength t x scale
      negativeBoundary := fun scale ↦
        (integrals.loop x tangent).sideLongEdgeAverage .negative
          fields.negative.magneticFieldStrength t x scale
      remainder := integrals.ampereMaxwellRemainder t x tangent
      bulk := integrals.ampereMaxwellBulk t x tangent
      surface := fun scale ↦
        (integrals.loop x tangent).surfaceLineAverage surfaceCurrent t x scale
      balance := integrals.ampereMaxwellBalance t x tangent }

end PlanarMaxwellThinCellIntegrals

end
end ThreeDimension
end Electromagnetism
