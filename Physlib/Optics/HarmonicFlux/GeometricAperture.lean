/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Physlib.SpaceAndTime.Space.OrientedAffineHyperplane

/-!
# Geometric aperture area measure

## i. Overview

This file represents an aperture as a measurable spatial region contained in the carrier of an
oriented affine plane. Its area measure is the two-dimensional Hausdorff measure of ambient
three-dimensional Euclidean space restricted to that region.

Unlike an arbitrary profile weight, this uses Mathlib's geometric two-dimensional Hausdorff
measure; restriction localizes it to the supplied measurable aperture region. A later field
connector may integrate directly on ambient `Space`; points outside the aperture have zero
measure. No parameterized-surface pullback or Jacobian theorem is asserted here.

Unguarded convention statement (review only): this file does not select an incident or outgoing
role. It does not orient the scalar area measure or assert regularity of the region boundary.
Orientation enters only when a flux integrand pairs with the plane's stored normal.

## ii. Key results

- `GeometricAperture`: a measurable spatial region contained in an oriented plane.
- `GeometricAperture.areaMeasure`: restricted two-dimensional Hausdorff measure.
- `areaMeasure_apply`: evaluation on a measurable set.
- `ae_mem_carrier`: area-almost every point lies in the plane carrier.

## iii. Table of contents

- A. Planar aperture regions
- B. Canonical geometric area measure

## iv. References

The measure is Mathlib's normalized Hausdorff measure. Its use as the E3b aperture measure is a
Physlib-original connector relative to the audited HOL optics corpus.
-/

@[expose] public section

namespace Optics

open MeasureTheory Space Set

noncomputable section

/-!

## A. Planar aperture regions

-/

/-- A measurable spatial aperture region lying in one oriented affine plane. -/
structure GeometricAperture where
  /-- The oriented affine plane carrying the aperture. -/
  plane : OrientedAffineHyperplane 3
  /-- The spatial aperture region. -/
  region : Set Space
  /-- The aperture region is measurable in ambient Euclidean space. -/
  measurableSet_region : MeasurableSet region
  /-- Every aperture point lies in the plane carrier. -/
  region_subset_carrier : region ⊆ plane.carrier

namespace GeometricAperture

/-!

## B. Canonical geometric area measure

-/

/-- The geometric aperture-area measure: ambient two-dimensional Hausdorff measure restricted to
the measurable planar region. -/
def areaMeasure (aperture : GeometricAperture) : Measure Space :=
  (μH[2] : Measure Space).restrict aperture.region

/-- On a measurable set, aperture area is its two-dimensional Hausdorff measure after intersection
with the aperture region. -/
lemma areaMeasure_apply (aperture : GeometricAperture) {s : Set Space}
    (hs : MeasurableSet s) :
    aperture.areaMeasure s = (μH[2] : Measure Space) (s ∩ aperture.region) := by
  rw [areaMeasure, Measure.restrict_apply hs]

/-- The total aperture area is the two-dimensional Hausdorff measure of its region. -/
lemma areaMeasure_univ (aperture : GeometricAperture) :
    aperture.areaMeasure Set.univ = (μH[2] : Measure Space) aperture.region := by
  rw [areaMeasure, Measure.restrict_apply_univ]

/-- Aperture-area-almost every spatial point belongs to the declared aperture region. -/
lemma ae_mem_region (aperture : GeometricAperture) :
    ∀ᵐ x ∂aperture.areaMeasure, x ∈ aperture.region := by
  exact ae_restrict_mem aperture.measurableSet_region

/-- Aperture-area-almost every spatial point lies in the carrier of the stored plane. -/
lemma ae_mem_carrier (aperture : GeometricAperture) :
    ∀ᵐ x ∂aperture.areaMeasure, x ∈ aperture.plane.carrier :=
  aperture.ae_mem_region.mono aperture.region_subset_carrier

end GeometricAperture

end

end Optics
