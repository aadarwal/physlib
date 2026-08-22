/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Electromagnetism.Media.HomogeneousIsotropic
public import Physlib.SpaceAndTime.Space.CrossProduct
public import Physlib.SpaceAndTime.Space.OrientedAffineHyperplane

/-!
# Pointwise planar macroscopic boundary conditions

## i. Overview

This file states the four pointwise macroscopic electromagnetic boundary laws across an oriented
affine plane. Boundary values are ordinary real `E`, `D`, `B`, and `H` data on the plane carrier.
The negative-to-positive jump convention is

```text
n · (D_positive - D_negative) = surfaceCharge,
n × (H_positive - H_negative) = surfaceCurrent.
```

Tangential `E` and normal `B` are continuous. The surface current is intrinsically tangent to the
plane. Only free electric surface charge and current are represented; there is no magnetic surface
charge or current.

These declarations state local boundary conditions but do not derive them from integral Maxwell
equations. `PlanarMacroscopicTrace` contains pointwise restriction data, not an analytic one-sided
trace of a field defined only on an open half-space. The zero-free-surface-source specialization
does not assert the absence of bound polarization charge, bulk sources, or constitutive material
response.

## ii. Key results

- `PlanarMacroscopicTrace`: pointwise boundary values of the four macroscopic fields.
- `PlanarMacroscopicTrace.ofFields`: restriction of four globally defined fields to a plane.
- `IsPlanarMacroscopicBoundary`: the four local laws with free electric surface sources.
- `IsSourceFreePlanarMacroscopicBoundary`: the specialization with zero free surface sources.
- `IsSourceFreePlanarMacroscopicBoundary.tangentialMagneticFieldStrength`: continuity of
  tangential `H` derived from the zero-current cross-product law.

## iii. Table of contents

- A. Pointwise planar field data
- B. Local boundary laws
- C. Zero free surface sources

## iv. References

The sign convention is fixed independently against the standard macroscopic jump laws before any
optical wave role is assigned. No external formal-development source is copied or translated here.
-/

@[expose] public section

namespace Electromagnetism
namespace ThreeDimension

open Space Time Matrix

noncomputable section

/-!

## A. Pointwise planar field data

-/

/-- Pointwise boundary values of the four macroscopic electromagnetic fields on an oriented
affine plane.

This is restriction data on the plane carrier, not an analytic trace produced from fields defined
only on one side. -/
structure PlanarMacroscopicTrace (plane : OrientedAffineHyperplane 3) where
  /-- Boundary values of the electric field. -/
  electricField : Time → plane.carrier → EuclideanSpace ℝ (Fin 3)
  /-- Boundary values of the electric displacement. -/
  electricDisplacement : Time → plane.carrier → EuclideanSpace ℝ (Fin 3)
  /-- Boundary values of the magnetic induction. -/
  magneticInduction : Time → plane.carrier → EuclideanSpace ℝ (Fin 3)
  /-- Boundary values of the magnetic field strength. -/
  magneticFieldStrength : Time → plane.carrier → EuclideanSpace ℝ (Fin 3)

namespace PlanarMacroscopicTrace

/-- Restrict four globally defined macroscopic fields pointwise to an oriented plane. -/
def ofFields (plane : OrientedAffineHyperplane 3) (E : ElectricField)
    (D : ElectricDisplacementField) (B : MagneticInductionField)
    (H : MagneticFieldStrength) : PlanarMacroscopicTrace plane where
  electricField t x := E t x
  electricDisplacement t x := D t x
  magneticInduction t x := B t x
  magneticFieldStrength t x := H t x

end PlanarMacroscopicTrace

/-- A free electric surface-charge density on an oriented affine plane. -/
abbrev PlanarFreeSurfaceChargeDensity (plane : OrientedAffineHyperplane 3) :=
  Time → plane.carrier → ℝ

/-- A free electric surface-current density on an oriented affine plane.

Its values are bundled tangent vectors, so tangency is part of the source type. -/
abbrev PlanarFreeSurfaceCurrentDensity (plane : OrientedAffineHyperplane 3) :=
  Time → plane.carrier → plane.tangentSubmodule

/-!

## B. Local boundary laws

-/

/-- The four pointwise macroscopic boundary laws across an oriented affine plane.

The normal points from the negative trace toward the positive trace. The jump convention is
positive minus negative, so `n × (H_positive - H_negative) = surfaceCurrent` and
`n · (D_positive - D_negative) = surfaceCharge`. Only free electric surface sources are included;
no derivation from integral Maxwell equations is asserted. -/
def IsPlanarMacroscopicBoundary {plane : OrientedAffineHyperplane 3}
    (negativeTrace positiveTrace : PlanarMacroscopicTrace plane)
    (surfaceCharge : PlanarFreeSurfaceChargeDensity plane)
    (surfaceCurrent : PlanarFreeSurfaceCurrentDensity plane) : Prop :=
  ∀ t x,
    plane.projectionToTangent (negativeTrace.electricField t x) =
      plane.projectionToTangent (positiveTrace.electricField t x) ∧
    plane.normalComponent (positiveTrace.electricDisplacement t x) -
        plane.normalComponent (negativeTrace.electricDisplacement t x) = surfaceCharge t x ∧
    plane.normalComponent (negativeTrace.magneticInduction t x) =
      plane.normalComponent (positiveTrace.magneticInduction t x) ∧
    plane.normalVector ⨯ₑ₃
        (positiveTrace.magneticFieldStrength t x -
          negativeTrace.magneticFieldStrength t x) =
      (surfaceCurrent t x : EuclideanSpace ℝ (Fin 3))

namespace IsPlanarMacroscopicBoundary

variable {plane : OrientedAffineHyperplane 3}
  {negativeTrace positiveTrace : PlanarMacroscopicTrace plane}
  {surfaceCharge : PlanarFreeSurfaceChargeDensity plane}
  {surfaceCurrent : PlanarFreeSurfaceCurrentDensity plane}

/-- The tangential electric-field boundary law. -/
lemma tangentialElectricField
    (h : IsPlanarMacroscopicBoundary negativeTrace positiveTrace
      surfaceCharge surfaceCurrent) (t : Time) (x : plane.carrier) :
    plane.projectionToTangent (negativeTrace.electricField t x) =
      plane.projectionToTangent (positiveTrace.electricField t x) :=
  (h t x).1

/-- The normal electric-displacement jump law. -/
lemma normalElectricDisplacement
    (h : IsPlanarMacroscopicBoundary negativeTrace positiveTrace
      surfaceCharge surfaceCurrent) (t : Time) (x : plane.carrier) :
    plane.normalComponent (positiveTrace.electricDisplacement t x) -
        plane.normalComponent (negativeTrace.electricDisplacement t x) = surfaceCharge t x :=
  (h t x).2.1

/-- The normal magnetic-induction boundary law. -/
lemma normalMagneticInduction
    (h : IsPlanarMacroscopicBoundary negativeTrace positiveTrace
      surfaceCharge surfaceCurrent) (t : Time) (x : plane.carrier) :
    plane.normalComponent (negativeTrace.magneticInduction t x) =
      plane.normalComponent (positiveTrace.magneticInduction t x) :=
  (h t x).2.2.1

/-- The tangential magnetic-field-strength jump law. -/
lemma tangentialMagneticFieldStrength
    (h : IsPlanarMacroscopicBoundary negativeTrace positiveTrace
      surfaceCharge surfaceCurrent) (t : Time) (x : plane.carrier) :
    plane.normalVector ⨯ₑ₃
        (positiveTrace.magneticFieldStrength t x -
          negativeTrace.magneticFieldStrength t x) =
      (surfaceCurrent t x : EuclideanSpace ℝ (Fin 3)) :=
  (h t x).2.2.2

end IsPlanarMacroscopicBoundary

/-!

## C. Zero free surface sources

-/

/-- The pointwise planar boundary laws with no free electric surface charge or current.

This specialization does not remove bound polarization charge, bulk sources, or material response,
and it does not assert a derivation from integral Maxwell equations. -/
def IsSourceFreePlanarMacroscopicBoundary {plane : OrientedAffineHyperplane 3}
    (negativeTrace positiveTrace : PlanarMacroscopicTrace plane) : Prop :=
  IsPlanarMacroscopicBoundary negativeTrace positiveTrace 0 0

namespace IsSourceFreePlanarMacroscopicBoundary

variable {plane : OrientedAffineHyperplane 3}
  {negativeTrace positiveTrace : PlanarMacroscopicTrace plane}

/-- With no free surface sources, the tangential electric fields agree. -/
lemma tangentialElectricField
    (h : IsSourceFreePlanarMacroscopicBoundary negativeTrace positiveTrace)
    (t : Time) (x : plane.carrier) :
    plane.projectionToTangent (negativeTrace.electricField t x) =
      plane.projectionToTangent (positiveTrace.electricField t x) :=
  IsPlanarMacroscopicBoundary.tangentialElectricField h t x

/-- With no free surface charge, the normal electric displacements agree. -/
lemma normalElectricDisplacement
    (h : IsSourceFreePlanarMacroscopicBoundary negativeTrace positiveTrace)
    (t : Time) (x : plane.carrier) :
    plane.normalComponent (negativeTrace.electricDisplacement t x) =
      plane.normalComponent (positiveTrace.electricDisplacement t x) := by
  have hjump := IsPlanarMacroscopicBoundary.normalElectricDisplacement h t x
  exact (sub_eq_zero.mp (by simpa using hjump)).symm

/-- With no free surface sources, the normal magnetic inductions agree. -/
lemma normalMagneticInduction
    (h : IsSourceFreePlanarMacroscopicBoundary negativeTrace positiveTrace)
    (t : Time) (x : plane.carrier) :
    plane.normalComponent (negativeTrace.magneticInduction t x) =
      plane.normalComponent (positiveTrace.magneticInduction t x) :=
  IsPlanarMacroscopicBoundary.normalMagneticInduction h t x

/-- With no free surface current, the tangential magnetic-field strengths agree. -/
lemma tangentialMagneticFieldStrength
    (h : IsSourceFreePlanarMacroscopicBoundary negativeTrace positiveTrace)
    (t : Time) (x : plane.carrier) :
    plane.projectionToTangent (negativeTrace.magneticFieldStrength t x) =
      plane.projectionToTangent (positiveTrace.magneticFieldStrength t x) := by
  symm
  rw [← sub_eq_zero, ← map_sub]
  apply Subtype.ext
  simp only [plane.coe_projectionToTangent, Submodule.coe_zero]
  let v := positiveTrace.magneticFieldStrength t x -
    negativeTrace.magneticFieldStrength t x
  have hcross : plane.normalVector ⨯ₑ₃ v = 0 :=
    IsPlanarMacroscopicBoundary.tangentialMagneticFieldStrength h t x
  have hdouble := congrArg (fun w ↦ plane.normalVector ⨯ₑ₃ w) hcross
  have hcrossZero :
      plane.normalVector ⨯ₑ₃ (0 : EuclideanSpace ℝ (Fin 3)) = 0 := by
    simpa only [zero_smul] using
      cross_smul plane.normalVector plane.normalVector 0
  rw [Space.cross_cross_eq_smul_sub_smul',
    plane.inner_normalVector_self, one_smul, hcrossZero] at hdouble
  have hv : v = plane.normalComponent v • plane.normalVector :=
    (sub_eq_zero.mp hdouble).symm
  have htangent : plane.tangentialProjection v = 0 := by
    rw [hv, plane.tangentialProjection_smul,
      plane.tangentialProjection_normalVector, smul_zero]
  simpa only [v] using htangent

end IsSourceFreePlanarMacroscopicBoundary

end
end ThreeDimension
end Electromagnetism
