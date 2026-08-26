/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.SpaceAndTime.Space.OrientedAffineHyperplane

/-!
# One-sided traces at oriented affine hyperplanes

## i. Overview

A field on one open half-space has a one-sided trace when it converges through the complete
half-space neighborhood filter at every carrier point. The local field is genuinely defined only
on the selected open half-space. Its source filter is the pullback of the ambient neighborhood
filter along the subtype inclusion; pushing that filter back into the ambient space gives exactly
`nhdsWithin` the selected open half-space.

The logarithmic normal approach from `OrientedAffineHyperplane` is a useful witness inside this
filter, but it does not define the trace. Consequently, convergence along that one ray follows
from a one-sided trace and is not mistaken for full half-space convergence.

The parameter type is arbitrary. In electromagnetism it is instantiated by time, while the same
API can describe static fields or parameterized families. This file supplies no integral theorem,
jump condition, surface-source law, or regularity strong enough to exchange limits and integrals.

## ii. Key results

- `OrientedAffineHyperplane.oneSidedNhds`: the full selected-half-space neighborhood filter.
- `OrientedAffineHyperplane.map_oneSidedNhds`: its ambient image is `nhdsWithin` the half-space.
- `OrientedAffineHyperplane.HasOneSidedTrace`: convergence through that full filter.
- `OrientedAffineHyperplane.TwoSidedField`: independent fields on the two open half-spaces.
- `OrientedAffineHyperplane.HasOneSidedTrace.unique`: uniqueness of the trace.
- `OrientedAffineHyperplane.HasOneSidedTrace.tendsto_sideApproach`: a trace controls the normal
  approach as a corollary.
- `OrientedAffineHyperplane.hasOneSidedTrace_restrict`: continuity of an ambient extension gives
  the expected one-sided trace.

## iii. Table of contents

- A. Half-space neighborhood filters
- B. One-sided traces
- C. Restrictions of ambient fields
- D. Two-sided fields

## iv. References

This is a Physlib topology foundation. No external formal-development source is copied or
translated here.
-/

@[expose] public section

namespace Space
namespace OrientedAffineHyperplane

open Filter

noncomputable section

variable {d : ℕ}

/-! ## A. Half-space neighborhood filters -/

/-- A parameterized field whose spatial domain is one selected open half-space. -/
abbrev SideField (plane : OrientedAffineHyperplane d) (side : Side)
    (P V : Type*) :=
  P → plane.openHalfSpace side → V

/-- A parameterized field stored on an oriented hyperplane's carrier. -/
abbrev BoundaryField (plane : OrientedAffineHyperplane d) (P V : Type*) :=
  P → plane.carrier → V

/-- The complete one-sided neighborhood filter at a carrier point.

It is the pullback of the ambient neighborhood filter to the selected open half-space. Its
ambient image is `nhdsWithin` that half-space, as stated by `map_oneSidedNhds`. -/
def oneSidedNhds (plane : OrientedAffineHyperplane d) (side : Side)
    (x : plane.carrier) : Filter (plane.openHalfSpace side) :=
  comap ((↑) : plane.openHalfSpace side → Space d) (nhds (x : Space d))

/-- Pushing the one-sided filter into ambient space gives the half-space neighborhood filter. -/
lemma map_oneSidedNhds (plane : OrientedAffineHyperplane d) (side : Side)
    (x : plane.carrier) :
    map ((↑) : plane.openHalfSpace side → Space d) (plane.oneSidedNhds side x) =
      nhdsWithin (x : Space d) (plane.openHalfSpace side) := by
  rw [oneSidedNhds, Filter.subtype_coe_map_comap, nhdsWithin]

/-- The complete selected-side neighborhood filter at a carrier point is nontrivial. -/
lemma oneSidedNhds_neBot (plane : OrientedAffineHyperplane d) (side : Side)
    (x : plane.carrier) : NeBot (plane.oneSidedNhds side x) := by
  rw [oneSidedNhds, ← mem_closure_iff_comap_neBot]
  exact plane.mem_closure_openHalfSpace_of_mem_carrier side x

/-- The logarithmic normal approach tends through the complete selected-side neighborhood
filter. -/
lemma tendsto_sideApproach_oneSidedNhds (plane : OrientedAffineHyperplane d)
    (side : Side) (x : plane.carrier) :
    Tendsto (plane.sideApproach side x) atTop (plane.oneSidedNhds side x) := by
  rw [oneSidedNhds, tendsto_comap_iff]
  change Tendsto (plane.sideApproachPoint side x) atTop (nhds (x : Space d))
  exact plane.tendsto_sideApproachPoint_atTop side x

/-! ## B. One-sided traces -/

/-- A local side field converges through the full selected-half-space neighborhood filter to a
supplied boundary field. -/
def HasOneSidedTrace {P V : Type*} [TopologicalSpace V]
    (plane : OrientedAffineHyperplane d) {side : Side}
    (field : plane.SideField side P V) (trace : plane.BoundaryField P V) : Prop :=
  ∀ p x, Tendsto (field p) (plane.oneSidedNhds side x) (nhds (trace p x))

namespace HasOneSidedTrace

variable {P V : Type*} [TopologicalSpace V]
  {plane : OrientedAffineHyperplane d} {side : Side}
  {field : plane.SideField side P V}
  {first second : plane.BoundaryField P V}

/-- A local side field has at most one trace through the full half-space neighborhood filter. -/
lemma unique [T2Space V] (hFirst : plane.HasOneSidedTrace field first)
    (hSecond : plane.HasOneSidedTrace field second) : first = second := by
  funext p x
  let _ : NeBot (plane.oneSidedNhds side x) := plane.oneSidedNhds_neBot side x
  exact tendsto_nhds_unique (hFirst p x) (hSecond p x)

/-- A full one-sided trace controls the selected normal approach as a corollary. -/
lemma tendsto_sideApproach (h : plane.HasOneSidedTrace field first)
    (p : P) (x : plane.carrier) :
    Tendsto (fun u : ℝ ↦ field p (plane.sideApproach side x u)) atTop
      (nhds (first p x)) :=
  (h p x).comp (plane.tendsto_sideApproach_oneSidedNhds side x)

end HasOneSidedTrace

/-! ## C. Restrictions of ambient fields -/

/-- Restrict an ambient parameterized field to one selected open half-space. -/
def restrictFieldToSide {P V : Type*} (plane : OrientedAffineHyperplane d)
    (side : Side) (field : P → Space d → V) : plane.SideField side P V :=
  fun p x ↦ field p x

/-- Restrict an ambient parameterized field to an oriented hyperplane's carrier. -/
def restrictFieldToBoundary {P V : Type*} (plane : OrientedAffineHyperplane d)
    (field : P → Space d → V) : plane.BoundaryField P V :=
  fun p x ↦ field p x

/-- Spatial continuity at every carrier point gives the expected full one-sided trace. -/
lemma hasOneSidedTrace_restrict {P V : Type*} [TopologicalSpace V]
    (plane : OrientedAffineHyperplane d) (side : Side)
    (field : P → Space d → V)
    (hContinuous : ∀ (p : P) (x : plane.carrier),
      ContinuousAt (field p) (x : Space d)) :
    plane.HasOneSidedTrace (plane.restrictFieldToSide side field)
      (plane.restrictFieldToBoundary field) := by
  intro p x
  exact (hContinuous p x).tendsto.comp Filter.tendsto_comap

/-! ## D. Two-sided fields -/

/-- Independent parameterized fields on the two open half-spaces of an oriented hyperplane. -/
structure TwoSidedField (plane : OrientedAffineHyperplane d) (P V : Type*) where
  /-- The field on the negative open half-space. -/
  negative : plane.SideField .negative P V
  /-- The field on the positive open half-space. -/
  positive : plane.SideField .positive P V

namespace TwoSidedField

/-- Restrict one ambient field to both open half-spaces. -/
def ofField {P V : Type*} (plane : OrientedAffineHyperplane d)
    (field : P → Space d → V) : plane.TwoSidedField P V where
  negative := plane.restrictFieldToSide .negative field
  positive := plane.restrictFieldToSide .positive field

end TwoSidedField

end
end OrientedAffineHyperplane
end Space
