/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Electromagnetism.ThreeDimension.BoundaryConditions.PlanarThinCell
public import Physlib.Electromagnetism.ThreeDimension.MonochromaticPlaneWave.ComplexCalculus
public import Physlib.Optics.Interfaces.PlanarDielectric.WaveBoundary

/-!
# Integral Maxwell realization of a planar dielectric boundary

## i. Overview

This file restricts the explicit three-wave planar-dielectric fields to the two geometric open
half-spaces. Their global smoothness supplies genuine one-sided traces, and those traces are
definitionally the pointwise negative and positive traces used by the existing optical boundary
predicate.

Consequently, a literal planar integral Maxwell law for these side fields, together with the
production thin-cell regularity contract, proves
`PlanarDielectricWaveConfiguration.IsLocalBoundary`. The integral law remains an explicit premise:
ordinary sidewise differential Maxwell equations cannot create carrier-supported surface charge
or current.

## ii. Key results

- `PlanarDielectricWaveConfiguration.negativeSideFields`: the incident-plus-reflected open-side
  fields and traces.
- `PlanarDielectricWaveConfiguration.positiveSideFields`: the transmitted open-side fields and
  traces.
- `PlanarDielectricWaveConfiguration.isLocalBoundary_of_integralMaxwell`: the E4b-to-E4a bridge.

## iii. Table of contents

- A. One-sided field packages
- B. Integral Maxwell boundary realization

## iv. References

This is a Physlib-original bridge. The audited HOL interface development states its local boundary
predicate rather than deriving it from integral Maxwell laws.
-/

@[expose] public section

namespace Optics

open Electromagnetism Electromagnetism.ThreeDimension Space Time
open Electromagnetism.ThreeDimension.ComplexMonochromaticPlaneWave

noncomputable section

namespace PlanarDielectricWaveConfiguration

/-!
## A. One-sided field packages
-/

/-- The incident-plus-reflected fields restricted to the interface's negative open half-space,
with their genuine one-sided traces. -/
def negativeSideFields (configuration : PlanarDielectricWaveConfiguration) :
    PlanarMacroscopicSideFields configuration.interface.plane .negative :=
  PlanarMacroscopicSideFields.ofFields configuration.interface.plane .negative
    (configuration.incident.electricField + configuration.reflected.electricField)
    (configuration.incident.electricDisplacement configuration.interface.negativeMedium +
      configuration.reflected.electricDisplacement configuration.interface.negativeMedium)
    (configuration.incident.magneticInduction + configuration.reflected.magneticInduction)
    (configuration.incident.magneticFieldStrength configuration.interface.negativeMedium +
      configuration.reflected.magneticFieldStrength configuration.interface.negativeMedium)
    (by
      intro t x
      exact (((configuration.incident.electricField_contDiff 1).differentiable
          (by norm_num)).comp (f := fun y ↦ (t, y)) (by fun_prop)
          (x : Space)).continuousAt.add
        (((configuration.reflected.electricField_contDiff 1).differentiable
          (by norm_num)).comp (f := fun y ↦ (t, y)) (by fun_prop)
          (x : Space)).continuousAt)
    (by
      intro t x
      exact (((configuration.incident.electricDisplacement_contDiff
          configuration.interface.negativeMedium 1).differentiable
          (by norm_num)).comp (f := fun y ↦ (t, y)) (by fun_prop)
          (x : Space)).continuousAt.add
        (((configuration.reflected.electricDisplacement_contDiff
          configuration.interface.negativeMedium 1).differentiable
          (by norm_num)).comp (f := fun y ↦ (t, y)) (by fun_prop)
          (x : Space)).continuousAt)
    (by
      intro t x
      exact (((configuration.incident.magneticInduction_contDiff 1).differentiable
          (by norm_num)).comp (f := fun y ↦ (t, y)) (by fun_prop)
          (x : Space)).continuousAt.add
        (((configuration.reflected.magneticInduction_contDiff 1).differentiable
          (by norm_num)).comp (f := fun y ↦ (t, y)) (by fun_prop)
          (x : Space)).continuousAt)
    (by
      intro t x
      exact (((configuration.incident.magneticFieldStrength_contDiff
          configuration.interface.negativeMedium 1).differentiable
          (by norm_num)).comp (f := fun y ↦ (t, y)) (by fun_prop)
          (x : Space)).continuousAt.add
        (((configuration.reflected.magneticFieldStrength_contDiff
          configuration.interface.negativeMedium 1).differentiable
          (by norm_num)).comp (f := fun y ↦ (t, y)) (by fun_prop)
          (x : Space)).continuousAt)

/-- The transmitted fields restricted to the interface's positive open half-space, with their
genuine one-sided traces. -/
def positiveSideFields (configuration : PlanarDielectricWaveConfiguration) :
    PlanarMacroscopicSideFields configuration.interface.plane .positive :=
  PlanarMacroscopicSideFields.ofFields configuration.interface.plane .positive
    configuration.transmitted.electricField
    (configuration.transmitted.electricDisplacement configuration.interface.positiveMedium)
    configuration.transmitted.magneticInduction
    (configuration.transmitted.magneticFieldStrength configuration.interface.positiveMedium)
    (fun t x ↦
      (((configuration.transmitted.electricField_contDiff 1).differentiable
        (by norm_num)).comp (f := fun y ↦ (t, y)) (by fun_prop)
        (x : Space)).continuousAt)
    (fun t x ↦
      (((configuration.transmitted.electricDisplacement_contDiff
        configuration.interface.positiveMedium 1).differentiable
        (by norm_num)).comp (f := fun y ↦ (t, y)) (by fun_prop)
        (x : Space)).continuousAt)
    (fun t x ↦
      (((configuration.transmitted.magneticInduction_contDiff 1).differentiable
        (by norm_num)).comp (f := fun y ↦ (t, y)) (by fun_prop)
        (x : Space)).continuousAt)
    (fun t x ↦
      (((configuration.transmitted.magneticFieldStrength_contDiff
        configuration.interface.positiveMedium 1).differentiable
        (by norm_num)).comp (f := fun y ↦ (t, y)) (by fun_prop)
        (x : Space)).continuousAt)

/-- The two explicit optical sides as one macroscopic two-sided trace package. -/
def twoSidedFields (configuration : PlanarDielectricWaveConfiguration) :
    PlanarMacroscopicTwoSidedFields configuration.interface.plane where
  negative := configuration.negativeSideFields
  positive := configuration.positiveSideFields

/-!
## B. Integral Maxwell boundary realization
-/

/-- Literal integral Maxwell laws for the explicit three-wave side fields imply the optical local
boundary predicate under the corresponding thin-cell regularity hypotheses.

The result assumes neither one-sided illumination nor a propagation branch. It derives the local
four-law boundary predicate only; all later phase-matching and Fresnel conclusions retain their
existing hypotheses. -/
lemma isLocalBoundary_of_integralMaxwell
    (configuration : PlanarDielectricWaveConfiguration)
    {sources : PlanarMaxwellBulkSources configuration.interface.plane}
    {surfaceCharge : PlanarFreeSurfaceChargeDensity configuration.interface.plane}
    {surfaceCurrent : PlanarFreeSurfaceCurrentDensity configuration.interface.plane}
    {cells : PlanarMaxwellThinCells configuration.interface.plane}
    {rates : PlanarMaxwellThinCellFluxRates configuration.twoSidedFields cells}
    {maxwell : IsPlanarIntegralMacroscopicMaxwell configuration.twoSidedFields
      sources surfaceCharge surfaceCurrent cells rates}
    (regularity : HasPlanarMaxwellThinCellRegularity maxwell) :
    configuration.IsLocalBoundary surfaceCharge surfaceCurrent := by
  simpa [IsLocalBoundary, twoSidedFields, negativeSideFields, positiveSideFields,
    negativeTrace, positiveTrace, PlanarMacroscopicSideFields.ofFields] using
    regularity.isPlanarMacroscopicBoundary

end PlanarDielectricWaveConfiguration

end
end Optics
