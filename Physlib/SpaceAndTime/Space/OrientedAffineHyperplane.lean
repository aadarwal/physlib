/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.SpaceAndTime.Space.Module

/-!
# Oriented affine hyperplanes in space

## i. Overview

An `OrientedAffineHyperplane` is specified by one point and a unit normal direction. Its signed
normal coordinate is positive in the direction of the stored normal and negative in the opposite
direction. The zero set is the hyperplane carrier. The two open half-spaces exclude that carrier,
whereas both closed half-spaces contain it.

The normal points from the geometric negative side toward the geometric positive side. These side
names carry no material-medium, incident, reflected, transmitted, outgoing, or power meaning.
Later interface structures may assign such roles explicitly.

Vectors are split into their scalar normal component and their tangential projection. Tangent
vectors are also bundled as the kernel submodule of the normal-component linear map, and the
explicit projection is bundled as a linear map into that submodule. The construction is
dimension-generic and uses the coordinate vector space acting on `Space d`, so it can be reused by
planar boundaries, waveguides, and phase-matching arguments.

## ii. Key results

- `OrientedAffineHyperplane.signedNormalCoordinate_vadd`: signed-coordinate translation.
- `OrientedAffineHyperplane.normalComponent_tangentialProjection`: the tangential projection is
  tangent.
- `OrientedAffineHyperplane.tangentialProjection_add_normal`: exact vector decomposition.
- `OrientedAffineHyperplane.tangentSubmodule`: tangent displacements as a real submodule.
- `OrientedAffineHyperplane.eq_normalComponent_smul_normalVector_of_inner_eq_zero_on_tangent`:
  a vector pairing to zero with every tangent vector is its explicit normal projection.
- `OrientedAffineHyperplane.exists_tangent_vadd_eq_of_mem_carrier`: every carrier point is a
  tangential displacement of the stored point.
- `OrientedAffineHyperplane.signedNormalCoordinate_sideRay`: exact side-normal parameterization.

## iii. Table of contents

- A. Oriented hyperplanes and sides
- B. Signed normal geometry
- C. Half-spaces
- D. Tangent submodule, projection, and carrier parameterization

## iv. References

The construction uses Physlib's existing affine-space action and direction API. No external
formal-development source is copied or translated here.
-/

@[expose] public section

namespace Space

open InnerProductSpace

noncomputable section

/-!

## A. Oriented hyperplanes and sides

-/

/-- A dimension-generic affine hyperplane specified by a point and an oriented unit normal.

The stored normal points from the geometric negative side toward the geometric positive side.
No physical interface role is assigned to either side. -/
structure OrientedAffineHyperplane (d : ℕ := 3) where
  /-- A point on the affine hyperplane. -/
  point : Space d
  /-- The unit normal oriented from the negative side toward the positive side. -/
  normal : Direction d

namespace OrientedAffineHyperplane

/-- Either geometric side of an oriented affine hyperplane. -/
inductive Side
  | negative
  | positive
  deriving DecidableEq

namespace Side

/-- The scalar sign of a hyperplane side relative to the stored normal. -/
def sign : Side → ℝ
  | negative => -1
  | positive => 1

@[simp]
lemma sign_negative : negative.sign = -1 := rfl

@[simp]
lemma sign_positive : positive.sign = 1 := rfl

/-- The square of either side sign is one. -/
lemma sign_sq (side : Side) : side.sign ^ 2 = 1 := by
  cases side <;> norm_num [sign]

end Side

variable {d : ℕ}

/-!

## B. Signed normal geometry

-/

/-- The Euclidean coordinate vector of an oriented hyperplane's unit normal. -/
def normalVector (plane : OrientedAffineHyperplane d) : EuclideanSpace ℝ (Fin d) :=
  Space.basis.repr plane.normal.unit

/-- The coordinate normal of an oriented hyperplane has unit norm. -/
lemma normalVector_norm (plane : OrientedAffineHyperplane d) :
    ‖plane.normalVector‖ = 1 := by
  simpa [normalVector] using plane.normal.norm

/-- The coordinate normal of an oriented hyperplane is nonzero. -/
lemma normalVector_ne_zero (plane : OrientedAffineHyperplane d) :
    plane.normalVector ≠ 0 := by
  intro h
  have hnorm := plane.normalVector_norm
  simp [h] at hnorm

/-- The coordinate normal has real inner square one. -/
lemma inner_normalVector_self (plane : OrientedAffineHyperplane d) :
    inner ℝ plane.normalVector plane.normalVector = 1 := by
  rw [real_inner_self_eq_norm_sq, plane.normalVector_norm]
  norm_num

/-- The signed coordinate of a point along an oriented hyperplane's stored normal.

It is zero on the carrier, positive on the positive side, and negative on the negative side. -/
def signedNormalCoordinate (plane : OrientedAffineHyperplane d) (x : Space d) : ℝ :=
  inner ℝ plane.normalVector (x -ᵥ plane.point)

/-- The scalar normal component of a displacement vector. -/
def normalComponent (plane : OrientedAffineHyperplane d)
    (v : EuclideanSpace ℝ (Fin d)) : ℝ :=
  inner ℝ plane.normalVector v

/-- The scalar normal component as a real-linear map. -/
def normalComponentLinearMap (plane : OrientedAffineHyperplane d) :
    EuclideanSpace ℝ (Fin d) →ₗ[ℝ] ℝ :=
  (innerSL ℝ plane.normalVector).toLinearMap

@[simp]
lemma normalComponentLinearMap_apply (plane : OrientedAffineHyperplane d)
    (v : EuclideanSpace ℝ (Fin d)) :
    plane.normalComponentLinearMap v = plane.normalComponent v := rfl

/-- The unit coordinate normal pointing into a selected geometric side. -/
def sideNormalVector (plane : OrientedAffineHyperplane d) (side : Side) :
    EuclideanSpace ℝ (Fin d) :=
  side.sign • plane.normalVector

/-- The positive-side normal vector is the stored normal vector. -/
@[simp]
lemma sideNormalVector_positive (plane : OrientedAffineHyperplane d) :
    plane.sideNormalVector .positive = plane.normalVector := by
  simp [sideNormalVector]

/-- The negative-side normal vector is the negative stored normal vector. -/
@[simp]
lemma sideNormalVector_negative (plane : OrientedAffineHyperplane d) :
    plane.sideNormalVector .negative = -plane.normalVector := by
  simp [sideNormalVector]

/-- The unit spatial direction pointing into a selected geometric side. -/
def sideNormalDirection (plane : OrientedAffineHyperplane d) (side : Side) : Direction d where
  unit := side.sign • plane.normal.unit
  norm := by
    rw [norm_smul, plane.normal.norm, mul_one, Real.norm_eq_abs]
    cases side <;> norm_num [Side.sign]

/-- The coordinate vector of a side-normal direction is the corresponding side-normal vector. -/
lemma sideNormalVector_eq_repr (plane : OrientedAffineHyperplane d) (side : Side) :
    plane.sideNormalVector side = Space.basis.repr (plane.sideNormalDirection side).unit := by
  simp [sideNormalVector, sideNormalDirection, normalVector]

/-- Every side-normal coordinate vector has unit norm. -/
lemma sideNormalVector_norm (plane : OrientedAffineHyperplane d) (side : Side) :
    ‖plane.sideNormalVector side‖ = 1 := by
  rw [sideNormalVector, norm_smul, plane.normalVector_norm, mul_one, Real.norm_eq_abs]
  cases side <;> norm_num [Side.sign]

@[simp]
lemma signedNormalCoordinate_point (plane : OrientedAffineHyperplane d) :
    plane.signedNormalCoordinate plane.point = 0 := by
  simp [signedNormalCoordinate]

/-- Translating a point adds the displacement's normal component to its signed coordinate. -/
lemma signedNormalCoordinate_vadd (plane : OrientedAffineHyperplane d)
    (v : EuclideanSpace ℝ (Fin d)) (x : Space d) :
    plane.signedNormalCoordinate (v +ᵥ x) =
      plane.normalComponent v + plane.signedNormalCoordinate x := by
  simp only [signedNormalCoordinate, normalComponent, vadd_vsub_assoc]
  rw [inner_add_right]

/-!

## C. Half-spaces

-/

/-- The point set carried by an oriented affine hyperplane. -/
def carrier (plane : OrientedAffineHyperplane d) : Set (Space d) :=
  {x | plane.signedNormalCoordinate x = 0}

/-- The open half-space on a selected side of an oriented hyperplane.

The carrier is excluded. -/
def openHalfSpace (plane : OrientedAffineHyperplane d) (side : Side) : Set (Space d) :=
  {x | 0 < side.sign * plane.signedNormalCoordinate x}

/-- The closed half-space on a selected side of an oriented hyperplane.

The carrier belongs to both closed half-spaces. -/
def closedHalfSpace (plane : OrientedAffineHyperplane d) (side : Side) : Set (Space d) :=
  {x | 0 ≤ side.sign * plane.signedNormalCoordinate x}

@[simp]
lemma mem_carrier (plane : OrientedAffineHyperplane d) (x : Space d) :
    x ∈ plane.carrier ↔ plane.signedNormalCoordinate x = 0 :=
  Iff.rfl

/-- The stored point belongs to the hyperplane carrier. -/
lemma point_mem_carrier (plane : OrientedAffineHyperplane d) :
    plane.point ∈ plane.carrier := by
  simp

/-- The hyperplane carrier is contained in either closed half-space. -/
lemma carrier_subset_closedHalfSpace (plane : OrientedAffineHyperplane d) (side : Side) :
    plane.carrier ⊆ plane.closedHalfSpace side := by
  intro x hx
  change 0 ≤ side.sign * plane.signedNormalCoordinate x
  rw [(plane.mem_carrier x).mp hx, mul_zero]

/-- A carrier point belongs to neither open half-space. -/
lemma not_mem_openHalfSpace_of_mem_carrier (plane : OrientedAffineHyperplane d) (side : Side)
    {x : Space d} (h : x ∈ plane.carrier) :
    x ∉ plane.openHalfSpace side := by
  change ¬ 0 < side.sign * plane.signedNormalCoordinate x
  rw [(plane.mem_carrier x).mp h, mul_zero]
  exact lt_irrefl 0

/-- The hyperplane carrier is the intersection of its two closed half-spaces. -/
lemma carrier_eq_closedHalfSpace_inter (plane : OrientedAffineHyperplane d) :
    plane.carrier =
      plane.closedHalfSpace .negative ∩ plane.closedHalfSpace .positive := by
  ext x
  simp only [carrier, closedHalfSpace, Set.mem_ofPred_eq, Set.mem_inter_iff,
    Side.sign_negative, Side.sign_positive, neg_one_mul, one_mul]
  constructor
  · intro h
    simp [h]
  · intro h
    exact le_antisymm (neg_nonneg.mp h.1) h.2

/-- A side-normal ray based at the stored point has its expected signed coordinate. -/
lemma signedNormalCoordinate_sideRay (plane : OrientedAffineHyperplane d)
    (side : Side) (u : ℝ) :
    plane.signedNormalCoordinate
        (u • plane.sideNormalVector side +ᵥ plane.point) = side.sign * u := by
  rw [plane.signedNormalCoordinate_vadd, signedNormalCoordinate_point, add_zero,
    normalComponent, sideNormalVector, inner_smul_right, inner_smul_right,
    plane.inner_normalVector_self]
  ring

/-- Every positive displacement along a side normal lies in that side's open half-space. -/
lemma sideRay_mem_openHalfSpace (plane : OrientedAffineHyperplane d)
    (side : Side) (u : ℝ) (hu : 0 < u) :
    u • plane.sideNormalVector side +ᵥ plane.point ∈ plane.openHalfSpace side := by
  change 0 < side.sign * plane.signedNormalCoordinate
    (u • plane.sideNormalVector side +ᵥ plane.point)
  rw [plane.signedNormalCoordinate_sideRay]
  calc
    0 < side.sign ^ 2 * u := by rw [side.sign_sq, one_mul]; exact hu
    _ = side.sign * (side.sign * u) := by ring

/-!

## D. Tangent submodule, projection, and carrier parameterization

-/

/-- The projection of a displacement vector tangent to an oriented hyperplane. -/
def tangentialProjection (plane : OrientedAffineHyperplane d)
    (v : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  v - plane.normalComponent v • plane.normalVector

/-- A displacement vector is tangent to an oriented hyperplane when its normal component
vanishes. -/
def IsTangent (plane : OrientedAffineHyperplane d)
    (v : EuclideanSpace ℝ (Fin d)) : Prop :=
  plane.normalComponent v = 0

/-- The real submodule of displacement vectors tangent to an oriented affine hyperplane. -/
def tangentSubmodule (plane : OrientedAffineHyperplane d) :
    Submodule ℝ (EuclideanSpace ℝ (Fin d)) :=
  plane.normalComponentLinearMap.ker

@[simp]
lemma mem_tangentSubmodule (plane : OrientedAffineHyperplane d)
    (v : EuclideanSpace ℝ (Fin d)) :
    v ∈ plane.tangentSubmodule ↔ plane.IsTangent v := by
  rfl

/-- A tangent vector is orthogonal to the unit normal pointing into either side. -/
lemma inner_sideNormalVector_eq_zero_of_isTangent (plane : OrientedAffineHyperplane d)
    (side : Side) {v : EuclideanSpace ℝ (Fin d)} (h : plane.IsTangent v) :
    inner ℝ (plane.sideNormalVector side) v = 0 := by
  cases side <;> simpa [sideNormalVector, IsTangent, normalComponent] using h

/-- The tangential projection has zero normal component. -/
@[simp]
lemma normalComponent_tangentialProjection (plane : OrientedAffineHyperplane d)
    (v : EuclideanSpace ℝ (Fin d)) :
    plane.normalComponent (plane.tangentialProjection v) = 0 := by
  rw [normalComponent, tangentialProjection, inner_sub_right, inner_smul_right,
    plane.inner_normalVector_self, mul_one]
  simp [normalComponent]

/-- Every tangential projection is tangent to the hyperplane. -/
lemma isTangent_tangentialProjection (plane : OrientedAffineHyperplane d)
    (v : EuclideanSpace ℝ (Fin d)) :
    plane.IsTangent (plane.tangentialProjection v) := by
  exact plane.normalComponent_tangentialProjection v

/-- A vector is the sum of its tangential projection and normal projection. -/
lemma tangentialProjection_add_normal (plane : OrientedAffineHyperplane d)
    (v : EuclideanSpace ℝ (Fin d)) :
    plane.tangentialProjection v + plane.normalComponent v • plane.normalVector = v := by
  simp [tangentialProjection]

/-- Tangential projection commutes with vector addition. -/
lemma tangentialProjection_add (plane : OrientedAffineHyperplane d)
    (u v : EuclideanSpace ℝ (Fin d)) :
    plane.tangentialProjection (u + v) =
      plane.tangentialProjection u + plane.tangentialProjection v := by
  simp only [tangentialProjection, normalComponent, inner_add_right, add_smul]
  module

/-- Tangential projection commutes with real scalar multiplication. -/
lemma tangentialProjection_smul (plane : OrientedAffineHyperplane d)
    (c : ℝ) (v : EuclideanSpace ℝ (Fin d)) :
    plane.tangentialProjection (c • v) = c • plane.tangentialProjection v := by
  simp [tangentialProjection, normalComponent, inner_smul_right, smul_sub, smul_smul]

/-- Tangential projection fixes vectors already tangent to the hyperplane. -/
lemma tangentialProjection_eq_self_of_isTangent (plane : OrientedAffineHyperplane d)
    (v : EuclideanSpace ℝ (Fin d)) (h : plane.IsTangent v) :
    plane.tangentialProjection v = v := by
  change plane.normalComponent v = 0 at h
  rw [tangentialProjection, h]
  simp

/-- The real-linear projection from displacement vectors to the tangent submodule. -/
def projectionToTangent (plane : OrientedAffineHyperplane d) :
    EuclideanSpace ℝ (Fin d) →ₗ[ℝ] plane.tangentSubmodule where
  toFun v := ⟨plane.tangentialProjection v, plane.isTangent_tangentialProjection v⟩
  map_add' u v := Subtype.ext (plane.tangentialProjection_add u v)
  map_smul' c v := Subtype.ext (plane.tangentialProjection_smul c v)

@[simp]
lemma coe_projectionToTangent (plane : OrientedAffineHyperplane d)
    (v : EuclideanSpace ℝ (Fin d)) :
    (plane.projectionToTangent v : EuclideanSpace ℝ (Fin d)) =
      plane.tangentialProjection v := rfl

@[simp]
lemma projectionToTangent_coe (plane : OrientedAffineHyperplane d)
    (v : plane.tangentSubmodule) :
    plane.projectionToTangent (v : EuclideanSpace ℝ (Fin d)) = v := by
  apply Subtype.ext
  exact plane.tangentialProjection_eq_self_of_isTangent v
    ((plane.mem_tangentSubmodule v).mp v.property)

/-- A real vector pairing to zero with every tangent vector is its own normal component times
the oriented unit normal. -/
lemma eq_normalComponent_smul_normalVector_of_inner_eq_zero_on_tangent
    (plane : OrientedAffineHyperplane d) (w : EuclideanSpace ℝ (Fin d))
    (h : ∀ v : plane.tangentSubmodule,
      inner ℝ w (v : EuclideanSpace ℝ (Fin d)) = 0) :
    w = plane.normalComponent w • plane.normalVector := by
  have hproj := h (plane.projectionToTangent w)
  simp only [coe_projectionToTangent] at hproj
  have hinner : inner ℝ (plane.tangentialProjection w)
      (plane.tangentialProjection w) = 0 := by
    have htangent := plane.normalComponent_tangentialProjection w
    simp only [normalComponent] at htangent
    calc
      inner ℝ (plane.tangentialProjection w) (plane.tangentialProjection w) =
          inner ℝ (w - plane.normalComponent w • plane.normalVector)
            (plane.tangentialProjection w) := rfl
      _ = inner ℝ w (plane.tangentialProjection w) -
          inner ℝ (plane.normalComponent w • plane.normalVector)
            (plane.tangentialProjection w) := by rw [inner_sub_left]
      _ = 0 := by rw [hproj, inner_smul_left, conj_trivial, htangent, mul_zero, sub_zero]
  have hprojection : plane.tangentialProjection w = 0 :=
    inner_self_eq_zero.mp hinner
  calc
    w = plane.tangentialProjection w +
        plane.normalComponent w • plane.normalVector :=
      (plane.tangentialProjection_add_normal w).symm
    _ = plane.normalComponent w • plane.normalVector := by rw [hprojection, zero_add]

/-- A tangent displacement of the stored point belongs to the hyperplane carrier. -/
lemma tangent_vadd_point_mem_carrier (plane : OrientedAffineHyperplane d)
    (v : EuclideanSpace ℝ (Fin d)) (h : plane.IsTangent v) :
    v +ᵥ plane.point ∈ plane.carrier := by
  rw [plane.mem_carrier, plane.signedNormalCoordinate_vadd,
    plane.signedNormalCoordinate_point]
  simpa [IsTangent] using h

/-- Every carrier point is a tangent displacement of the stored point. -/
lemma exists_tangent_vadd_eq_of_mem_carrier (plane : OrientedAffineHyperplane d)
    (x : Space d) (h : x ∈ plane.carrier) :
    ∃ v : EuclideanSpace ℝ (Fin d), plane.IsTangent v ∧ x = v +ᵥ plane.point := by
  refine ⟨x -ᵥ plane.point, ?_, (vsub_vadd x plane.point).symm⟩
  change plane.signedNormalCoordinate x = 0
  exact (plane.mem_carrier x).mp h

end OrientedAffineHyperplane

end

end Space
