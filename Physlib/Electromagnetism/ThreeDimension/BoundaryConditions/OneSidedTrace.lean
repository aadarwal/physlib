/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Electromagnetism.ThreeDimension.BoundaryConditions.Planar
public import Physlib.Electromagnetism.ThreeDimension.MacroscopicMaxwellEquations
public import Physlib.SpaceAndTime.Space.OrientedAffineHyperplaneTrace

/-!
# One-sided planar macroscopic traces

## i. Overview

This file uses the dimension-generic half-space trace API to distinguish a macroscopic field
defined on one open side of an oriented plane from its limiting boundary value. The trace uses the
complete selected-side neighborhood filter, not merely a chosen normal ray.

`PlanarMacroscopicSideFields` packages local `E`, `D`, `B`, and `H` fields on one open half-space,
one boundary trace, and four full half-space convergence statements. Two such packages form
`PlanarMacroscopicTwoSidedFields`. A constructor restricts globally defined fields, and a
differentiable macroscopic Maxwell solution supplies the continuity needed by that constructor.

This is trace and regularity infrastructure for E4b. It proves no jump condition, integral
Maxwell equation, Stokes theorem, divergence theorem, thin-loop limit, pillbox limit, or surface-
source law. Pointwise traces alone are also not strong enough to exchange a thin-region limit with
an integral. In particular, the differential Maxwell predicate on either side alone does not
relate the two traces.

## ii. Key results

- `PlanarMacroscopicSideFields`: four local macroscopic fields and their trace data.
- `IsMacroscopicMaxwell.toPlanarMacroscopicSideFields`: a differentiable Maxwell solution gives
  one-sided trace data for either side.
- `PlanarMacroscopicTwoSidedFields`: independently supplied negative- and positive-side data.

## iii. Table of contents

- A. Macroscopic side data
- B. Differential Maxwell trace data

## iv. References

This is a Physlib foundation for the Maxwell-to-boundary derivation required by `goal.md` E4b.
No external formal-development source supplies this trace layer.
-/

@[expose] public section

namespace Electromagnetism
namespace ThreeDimension

open Space Time

noncomputable section

/-! ## A. Macroscopic side data -/

/-- The four macroscopic fields on one open half-space together with their one-sided trace. -/
structure PlanarMacroscopicSideFields (plane : OrientedAffineHyperplane 3)
    (side : OrientedAffineHyperplane.Side) where
  /-- Electric field on the selected open half-space. -/
  electricField : plane.SideField side Time (EuclideanSpace ℝ (Fin 3))
  /-- Electric displacement on the selected open half-space. -/
  electricDisplacement : plane.SideField side Time (EuclideanSpace ℝ (Fin 3))
  /-- Magnetic induction on the selected open half-space. -/
  magneticInduction : plane.SideField side Time (EuclideanSpace ℝ (Fin 3))
  /-- Magnetic field strength on the selected open half-space. -/
  magneticFieldStrength : plane.SideField side Time (EuclideanSpace ℝ (Fin 3))
  /-- Limiting values of all four fields on the carrier. -/
  trace : PlanarMacroscopicTrace plane
  /-- The electric field tends to its stored trace. -/
  electricField_hasTrace : plane.HasOneSidedTrace electricField trace.electricField
  /-- The electric displacement tends to its stored trace. -/
  electricDisplacement_hasTrace :
    plane.HasOneSidedTrace electricDisplacement trace.electricDisplacement
  /-- The magnetic induction tends to its stored trace. -/
  magneticInduction_hasTrace :
    plane.HasOneSidedTrace magneticInduction trace.magneticInduction
  /-- The magnetic field strength tends to its stored trace. -/
  magneticFieldStrength_hasTrace :
    plane.HasOneSidedTrace magneticFieldStrength trace.magneticFieldStrength

namespace PlanarMacroscopicSideFields

/-- Restrict four globally defined fields to one side and use their pointwise carrier values as
the trace, under explicit spatial continuity at that carrier. -/
def ofFields (plane : OrientedAffineHyperplane 3) (side : OrientedAffineHyperplane.Side)
    (E : ElectricField) (D : ElectricDisplacementField) (B : MagneticInductionField)
    (H : MagneticFieldStrength)
    (hE : ∀ (t : Time) (x : plane.carrier), ContinuousAt (E t) (x : Space))
    (hD : ∀ (t : Time) (x : plane.carrier), ContinuousAt (D t) (x : Space))
    (hB : ∀ (t : Time) (x : plane.carrier), ContinuousAt (B t) (x : Space))
    (hH : ∀ (t : Time) (x : plane.carrier), ContinuousAt (H t) (x : Space)) :
    PlanarMacroscopicSideFields plane side where
  electricField := plane.restrictFieldToSide side E
  electricDisplacement := plane.restrictFieldToSide side D
  magneticInduction := plane.restrictFieldToSide side B
  magneticFieldStrength := plane.restrictFieldToSide side H
  trace := PlanarMacroscopicTrace.ofFields plane E D B H
  electricField_hasTrace := plane.hasOneSidedTrace_restrict side E hE
  electricDisplacement_hasTrace := plane.hasOneSidedTrace_restrict side D hD
  magneticInduction_hasTrace := plane.hasOneSidedTrace_restrict side B hB
  magneticFieldStrength_hasTrace := plane.hasOneSidedTrace_restrict side H hH

end PlanarMacroscopicSideFields

/-- Independent negative- and positive-side macroscopic fields with one-sided carrier traces. -/
structure PlanarMacroscopicTwoSidedFields (plane : OrientedAffineHyperplane 3) where
  /-- Fields and traces approached from the negative open half-space. -/
  negative : PlanarMacroscopicSideFields plane .negative
  /-- Fields and traces approached from the positive open half-space. -/
  positive : PlanarMacroscopicSideFields plane .positive

/-! ## B. Differential Maxwell trace data -/

namespace IsMacroscopicMaxwell

/-- A differentiable macroscopic Maxwell solution, regarded as a global extension of one side,
supplies one-sided trace data on either side of any oriented plane.

This result uses only Maxwell's stored differentiability fields. It does not derive a relation
between independently supplied negative- and positive-side solutions. -/
def toPlanarMacroscopicSideFields {E : ElectricField} {D : ElectricDisplacementField}
    {B : MagneticInductionField} {H : MagneticFieldStrength}
    {rhoFree : ChargeDensity} {JFree : CurrentDensity}
    (h : IsMacroscopicMaxwell E D B H rhoFree JFree)
    (plane : OrientedAffineHyperplane 3) (side : OrientedAffineHyperplane.Side) :
    PlanarMacroscopicSideFields plane side :=
  PlanarMacroscopicSideFields.ofFields plane side E D B H
    (fun t x ↦
      ((h.electricField_differentiable.comp
        (f := fun x ↦ (t, x)) (by fun_prop)) (x : Space)).continuousAt)
    (fun t x ↦
      (h.electricDisplacement_differentiable.comp
        (f := fun x ↦ (t, x)) (by fun_prop) (x : Space)).continuousAt)
    (fun t x ↦
      (h.magneticInduction_differentiable.comp
        (f := fun x ↦ (t, x)) (by fun_prop) (x : Space)).continuousAt)
    (fun t x ↦
      (h.magneticFieldStrength_differentiable.comp
        (f := fun x ↦ (t, x)) (by fun_prop) (x : Space)).continuousAt)

end IsMacroscopicMaxwell

end
end ThreeDimension
end Electromagnetism
