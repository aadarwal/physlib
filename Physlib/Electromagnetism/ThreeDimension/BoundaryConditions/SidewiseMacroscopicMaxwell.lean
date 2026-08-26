/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Electromagnetism.ThreeDimension.BoundaryConditions.IntegralMacroscopicMaxwell

/-!
# Independent sidewise macroscopic Maxwell extensions

## i. Overview

This file bundles two independent globally differentiable macroscopic Maxwell solutions around an
oriented plane. The negative extension supplies data only on the negative open half-space, and the
positive extension supplies data only on the positive open half-space. Their carrier values become
the corresponding genuine one-sided traces.

The two extensions need not agree on the carrier. In particular, this structure contains no sheet
source, integral balance, interface jump law, constitutive matching, or relation between its two
Maxwell solutions. A separate finite-sheet premise is required to connect their retained carrier
terms to surface charge and current.

## ii. Key results

- `PlanarSidewiseMacroscopicMaxwell`: two independent differential Maxwell extensions.
- `PlanarSidewiseMacroscopicMaxwell.fields`: their selected-side fields and traces.
- `PlanarSidewiseMacroscopicMaxwell.sources`: their selected-side bulk free sources.

## iii. Table of contents

- A. Sidewise differential Maxwell data
- B. Selected-side fields and sources

## iv. References

This is Physlib-original infrastructure for the E4b finite-sheet derivation.
-/

@[expose] public section

namespace Electromagnetism
namespace ThreeDimension

open Space Time

noncomputable section

/-!
## A. Sidewise differential Maxwell data
-/

/-- Two independent globally differentiable macroscopic Maxwell extensions, one for each open
half-space of an oriented plane.

Values of either extension outside its selected half-space are auxiliary regular extensions used
by the local calculus theorems; they have no physical side assignment. -/
structure PlanarSidewiseMacroscopicMaxwell (plane : OrientedAffineHyperplane 3) where
  /-- Electric field of the negative-side extension. -/
  negativeElectricField : ElectricField
  /-- Electric displacement of the negative-side extension. -/
  negativeElectricDisplacement : ElectricDisplacementField
  /-- Magnetic induction of the negative-side extension. -/
  negativeMagneticInduction : MagneticInductionField
  /-- Magnetic field strength of the negative-side extension. -/
  negativeMagneticFieldStrength : MagneticFieldStrength
  /-- Free charge density of the negative-side extension. -/
  negativeChargeDensity : ChargeDensity
  /-- Free current density of the negative-side extension. -/
  negativeCurrentDensity : CurrentDensity
  /-- The negative-side ambient extension satisfies differential macroscopic Maxwell. -/
  negativeMaxwell : IsMacroscopicMaxwell negativeElectricField negativeElectricDisplacement
    negativeMagneticInduction negativeMagneticFieldStrength negativeChargeDensity
    negativeCurrentDensity
  /-- Electric field of the positive-side extension. -/
  positiveElectricField : ElectricField
  /-- Electric displacement of the positive-side extension. -/
  positiveElectricDisplacement : ElectricDisplacementField
  /-- Magnetic induction of the positive-side extension. -/
  positiveMagneticInduction : MagneticInductionField
  /-- Magnetic field strength of the positive-side extension. -/
  positiveMagneticFieldStrength : MagneticFieldStrength
  /-- Free charge density of the positive-side extension. -/
  positiveChargeDensity : ChargeDensity
  /-- Free current density of the positive-side extension. -/
  positiveCurrentDensity : CurrentDensity
  /-- The positive-side ambient extension satisfies differential macroscopic Maxwell. -/
  positiveMaxwell : IsMacroscopicMaxwell positiveElectricField positiveElectricDisplacement
    positiveMagneticInduction positiveMagneticFieldStrength positiveChargeDensity
    positiveCurrentDensity

namespace PlanarSidewiseMacroscopicMaxwell

/-!
## B. Selected-side fields and sources
-/

/-- Restrict the two ambient Maxwell extensions to their selected open half-spaces and retain
their genuine one-sided carrier traces. -/
def fields {plane : OrientedAffineHyperplane 3}
    (maxwell : PlanarSidewiseMacroscopicMaxwell plane) :
    PlanarMacroscopicTwoSidedFields plane where
  negative := maxwell.negativeMaxwell.toPlanarMacroscopicSideFields plane .negative
  positive := maxwell.positiveMaxwell.toPlanarMacroscopicSideFields plane .positive

/-- Restrict the two ambient free-source extensions to their selected open half-spaces. -/
def sources {plane : OrientedAffineHyperplane 3}
    (maxwell : PlanarSidewiseMacroscopicMaxwell plane) :
    PlanarMaxwellBulkSources plane where
  chargeDensity := OrientedAffineHyperplane.TwoSidedField.ofFields plane
    maxwell.negativeChargeDensity maxwell.positiveChargeDensity
  currentDensity := OrientedAffineHyperplane.TwoSidedField.ofFields plane
    maxwell.negativeCurrentDensity maxwell.positiveCurrentDensity

end PlanarSidewiseMacroscopicMaxwell

end
end ThreeDimension
end Electromagnetism
