/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Electromagnetism.Media.HomogeneousIsotropic
public import Physlib.SpaceAndTime.Space.OrientedAffineHyperplane

/-!
# Planar dielectric interfaces

## i. Overview

This file assigns two homogeneous isotropic media to the geometric sides of an oriented affine
plane. The negative-side medium is medium 1, the positive-side medium is medium 2, and the stored
normal points from medium 1 toward medium 2. Equal media are allowed.

The structure supplies only interface geometry and material assignment. Unguarded convention
statement (review only): it assigns no incident, reflected, or transmitted wave role and selects
no propagation or decay branch. It stores no boundary condition, common frequency, phase-matching
condition, Fresnel coefficient, irradiance, or power normalization.

## ii. Key results

- `PlanarDielectricInterface`: an oriented plane with one medium assigned to each side.
- `PlanarDielectricInterface.medium`: the medium selected by a geometric side.

## iii. Table of contents

- A. Planar dielectric interfaces

## iv. References

The construction combines Physlib's existing homogeneous-isotropic-medium and oriented-affine-
hyperplane APIs. No external formal-development source is copied or translated here.
-/

@[expose] public section

namespace Optics

open Electromagnetism Space

/-!

## A. Planar dielectric interfaces

-/

/-- A planar interface between two homogeneous isotropic dielectric media.

The negative-side medium is medium 1, the positive-side medium is medium 2, and the oriented
plane's normal points from medium 1 toward medium 2. Equal media are allowed. -/
structure PlanarDielectricInterface where
  /-- The oriented geometric interface plane. -/
  plane : OrientedAffineHyperplane 3
  /-- Medium 1, assigned to the geometric negative side. -/
  negativeMedium : HomogeneousIsotropicMedium
  /-- Medium 2, assigned to the geometric positive side. -/
  positiveMedium : HomogeneousIsotropicMedium

namespace PlanarDielectricInterface

/-- The material medium assigned to a selected geometric side of a planar dielectric interface. -/
def medium (interface : PlanarDielectricInterface) : OrientedAffineHyperplane.Side →
    HomogeneousIsotropicMedium
  | .negative => interface.negativeMedium
  | .positive => interface.positiveMedium

@[simp]
lemma medium_negative (interface : PlanarDielectricInterface) :
    interface.medium .negative = interface.negativeMedium := rfl

@[simp]
lemma medium_positive (interface : PlanarDielectricInterface) :
    interface.medium .positive = interface.positiveMedium := rfl

end PlanarDielectricInterface

end Optics
