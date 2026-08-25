/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Physlib.Optics.Basic

/-!
# Paraxial and physical rays

## i. Overview

Geometrical optics is developed here at two separated levels, in the sense of the optics API's
layering note.

A `MeridionalRay` is a physical ray in a plane containing the optical axis: a base point together
with a unit propagation direction, the direction recorded by the signed angle it makes with the
axis. `MeridionalRay.IsForward` distinguishes directions with positive axial component. The
plane-to-plane transport formula is total, while `MeridionalRay.basePoint_transport` identifies it
with exact rectilinear motion under the necessary non-grazing hypothesis.

A `ParaxialRay` is the reduced meridional coordinate `(height, angle)` at a reference plane. The
paraxial transport and interface laws are stated on `ParaxialRay` as *model* laws, following the
usual small-angle convention, and are never presented as consequences of the exact geometry.

The connection between the two levels is made quantitative rather than assumed. Section E proves
that the paraxial free-space law is the first-order form of exact rectilinear transport, that the
paraxial refraction law `n₁ θ₁ = n₀ θ₀` differs from exact Snell refraction by at most a stated
cubic term, and that the exactly refracted angle has the paraxial angle ratio as its limit on the
axis. This is the content the source development postulates outright.

Conventions are fixed once here and used unchanged by every later ray module.

- The optical axis is the second coordinate direction, whose positive direction is the reference
  forward direction. A ray need not point forward; that physical guard is
  `MeridionalRay.IsForward`. Ray height is the first coordinate, positive on one fixed side of the
  axis.
- A ray angle is the signed angle between the propagation direction and the axis, so that the
  propagation direction of a meridional ray is `(sin θ, cos θ)`.
- A surface radius of curvature is positive when the centre of curvature lies on the outgoing
  side of the surface, which is downstream in the locally folded coordinate after the interface.
  Comparing signed radii with a source using convex/concave labels therefore needs an explicit
  convention map.
- Reflection uses the *folded* convention: after a mirror the axis is re-referenced to the new
  propagation direction. A plane mirror therefore acts as the identity on `(height, angle)`, and
  a mirror does not change the refractive index. The explicit output-angle coordinate reversal,
  which sends the folded plane-mirror output `θ` to `-θ`, is recorded in
  `Physlib.Optics.Rays.Transfer`.

Explicit non-claims. No electromagnetic field, irradiance, polarization, or power is assigned to a
ray here; a ray carries only a position and a direction. At a grazing angle, real division and
`tan` are totalized algebraically, so the unguarded transport definition is not a physical
intersection theorem. The paraxial interface laws for curved surfaces are model laws: this file
proves the small-angle bridge for planar refraction and for free-space transport only, and makes
no claim that the spherical-surface laws have been derived from an exact surface geometry. Nothing
here connects a ray to the wave or electromagnetic models in `Physlib.Optics.Polarization` or
`Physlib.Electromagnetism`. Section F supplies signed meridional data for a future bridge to exact
interface geometry, but does not identify it with E5b's unoriented Euclidean angle.

## ii. Key results

- `Optics.MeridionalRay.norm_direction`: a ray direction is a unit vector.
- `Optics.MeridionalRay.IsForward`: the direction has strictly positive axial component.
- `Optics.MeridionalRay.basePoint_transport`: non-grazing transport moves the base point along the
  unit direction by the signed line parameter that advances the axial coordinate as stated.
- `Optics.ParaxialGap.rayBehavior_iff_eq_transport`: the relational free-space law is the graph of
  the paraxial transport map.
- `Optics.ParaxialInterface.exists_rayBehavior` and
  `Optics.ParaxialInterface.rayBehavior_unique`: a valid interface transports every incoming ray
  coordinate to exactly one outgoing ray coordinate.
- `Optics.ParaxialGap.tendsto_transport_height_error`: the paraxial free-space law reproduces
  exact rectilinear transport to first order in the ray angle.
- `Optics.abs_paraxialSnell_sub_le`: exact Snell refraction implies the paraxial refraction law up
  to an explicit cubic error.
- `Optics.tendsto_exactRefractionAngle_div`: the principal-branch Snell expression has paraxial
  angle ratio `n₀ / n₁` in the limit on the axis.
- `Optics.MeridionalRay.cos_signedIncidenceAngle`: the cosine bridge between the signed
  meridional difference and the direction-normal inner product.

## iii. Table of contents

- A. Paraxial ray coordinates
- B. Meridional rays and exact rectilinear propagation
- C. Homogeneous gaps and paraxial transport
- D. Refracting and reflecting interfaces
- E. The paraxial regime
- F. Hook for the exact-incidence bridge

## iv. References

- B. E. A. Saleh and M. C. Teich, *Fundamentals of Photonics*, 3rd edition, chapter 1, for the ray
  coordinate, sign, and folded-reflection conventions and the component laws.
- M. U. Siddique, *Formal Analysis of Geometrical Optics using Theorem Proving*, PhD thesis,
  Concordia University, 2015, chapter 3, for the corresponding postulated ray behaviours.

-/

@[expose] public section

namespace Optics

noncomputable section

open Filter Real

open scoped Topology

/-!

## A. Paraxial ray coordinates

-/

/-- The paraxial meridional coordinate of a ray at a reference plane: its signed transverse
height, and the signed angle its propagation direction makes with the optical axis.

This is a reduced coordinate, not a physical ray. It records no base point along the axis; the
reference plane is supplied by the context in which the coordinate is used.
-/
@[ext]
structure ParaxialRay where
  /-- The signed transverse distance from the optical axis at the reference plane. -/
  height : ℝ
  /-- The signed angle between the propagation direction and the optical axis. -/
  angle : ℝ

namespace ParaxialRay

/-- The column vector `![height, angle]` of a paraxial ray coordinate.

Ray-transfer matrices act on this vector, so the column ordering fixed here is the ordering used
by every ray-transfer matrix in `Physlib.Optics.Rays.Transfer`.
-/
def toVec (r : ParaxialRay) : Fin 2 → ℝ := ![r.height, r.angle]

/-- The paraxial ray coordinate read off a column vector in the `![height, angle]` ordering. -/
def ofVec (v : Fin 2 → ℝ) : ParaxialRay := ⟨v 0, v 1⟩

@[simp]
lemma toVec_zero (r : ParaxialRay) : r.toVec 0 = r.height := rfl

@[simp]
lemma toVec_one (r : ParaxialRay) : r.toVec 1 = r.angle := rfl

@[simp]
lemma ofVec_height (v : Fin 2 → ℝ) : (ofVec v).height = v 0 := rfl

@[simp]
lemma ofVec_angle (v : Fin 2 → ℝ) : (ofVec v).angle = v 1 := rfl

@[simp]
lemma ofVec_toVec (r : ParaxialRay) : ofVec r.toVec = r := rfl

@[simp]
lemma toVec_ofVec (v : Fin 2 → ℝ) : (ofVec v).toVec = v := by
  funext i
  fin_cases i <;> rfl

/-- Paraxial ray coordinates are equivalent to column vectors in the `![height, angle]`
ordering. -/
def vecEquiv : ParaxialRay ≃ (Fin 2 → ℝ) where
  toFun := toVec
  invFun := ofVec
  left_inv := ofVec_toVec
  right_inv := toVec_ofVec

end ParaxialRay

/-!

## B. Meridional rays and exact rectilinear propagation

-/

/-- A physical ray in a meridional plane, that is, a plane containing the optical axis.

The ray is recorded by a base point, given by its transverse height and its position along the
axis, together with the signed angle its propagation direction makes with the axis. The direction
itself is recovered as a unit vector by `MeridionalRay.direction`.
-/
@[ext]
structure MeridionalRay where
  /-- The signed transverse distance of the base point from the optical axis. -/
  height : ℝ
  /-- The position of the base point along the optical axis. -/
  axialPosition : ℝ
  /-- The signed angle between the propagation direction and the optical axis. -/
  angle : ℝ

namespace MeridionalRay

/-- A meridional ray points forward when its direction has strictly positive axial component. -/
def IsForward (r : MeridionalRay) : Prop := 0 < cos r.angle

/-- The unit propagation direction of a meridional ray, in `(transverse, axial)` components. -/
def direction (r : MeridionalRay) : EuclideanSpace ℝ (Fin 2) := !₂[sin r.angle, cos r.angle]

/-- The base point of a meridional ray, in `(transverse, axial)` components. -/
def basePoint (r : MeridionalRay) : EuclideanSpace ℝ (Fin 2) := !₂[r.height, r.axialPosition]

@[simp]
lemma direction_zero (r : MeridionalRay) : r.direction 0 = sin r.angle := rfl

@[simp]
lemma direction_one (r : MeridionalRay) : r.direction 1 = cos r.angle := rfl

@[simp]
lemma basePoint_zero (r : MeridionalRay) : r.basePoint 0 = r.height := rfl

@[simp]
lemma basePoint_one (r : MeridionalRay) : r.basePoint 1 = r.axialPosition := rfl

/-- The propagation direction of a meridional ray is a unit vector.

This is what makes the ray angle an angle: it is the only datum in the direction.
-/
lemma norm_direction (r : MeridionalRay) : ‖r.direction‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs, sin_sq_add_cos_sq]

/-- The total plane-to-plane transport formula for a meridional ray across signed axial distance
`d`.

The transverse height advances by `d * tan angle`; the corresponding paraxial law replaces
`tan angle` by `angle`. When `cos angle ≠ 0`, `basePoint_transport` proves that this is exact
rectilinear geometry with signed line parameter `d / cos angle`. At a grazing angle the real
functions are totalized, and this definition carries no physical intersection claim.
-/
def transport (d : ℝ) (r : MeridionalRay) : MeridionalRay where
  height := r.height + d * tan r.angle
  axialPosition := r.axialPosition + d
  angle := r.angle

@[simp]
lemma transport_angle (d : ℝ) (r : MeridionalRay) : (r.transport d).angle = r.angle := rfl

@[simp]
lemma transport_height (d : ℝ) (r : MeridionalRay) :
    (r.transport d).height = r.height + d * tan r.angle := rfl

@[simp]
lemma transport_axialPosition (d : ℝ) (r : MeridionalRay) :
    (r.transport d).axialPosition = r.axialPosition + d := rfl

/-- Non-grazing transport moves the base point along the unit propagation direction.

The signed line parameter is `d / cos angle`, which advances the axial coordinate by `d`. It is a
nonnegative forward arclength when `r.IsForward` and `0 ≤ d`. The hypothesis here only excludes
rays perpendicular to the axis; direction and distance signs remain explicit.
-/
lemma basePoint_transport (r : MeridionalRay) (hcos : cos r.angle ≠ 0) (d : ℝ) :
    (r.transport d).basePoint = r.basePoint + (d / cos r.angle) • r.direction := by
  have hcancel : d / cos r.angle * cos r.angle = d := div_mul_cancel₀ d hcos
  ext i
  fin_cases i
  · simp only [basePoint, transport, direction, Fin.zero_eta, PiLp.toLp_apply,
      Matrix.cons_val_zero, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, tan_eq_sin_div_cos]
    ring
  · simp only [basePoint, transport, direction, Fin.mk_one, PiLp.toLp_apply,
      Matrix.cons_val_one, Matrix.cons_val_zero, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      hcancel]

/-- Forward transport across a nonnegative axial distance has a nonnegative line parameter. -/
lemma transportParameter_nonneg (r : MeridionalRay) (hForward : r.IsForward) {d : ℝ}
    (hd : 0 ≤ d) : 0 ≤ d / cos r.angle :=
  div_nonneg hd hForward.le

/-- The paraxial coordinate of a meridional ray at its own reference plane. -/
def toParaxial (r : MeridionalRay) : ParaxialRay := ⟨r.height, r.angle⟩

@[simp]
lemma toParaxial_height (r : MeridionalRay) : r.toParaxial.height = r.height := rfl

@[simp]
lemma toParaxial_angle (r : MeridionalRay) : r.toParaxial.angle = r.angle := rfl

end MeridionalRay

/-!

## C. Homogeneous gaps and paraxial transport

-/

/-- A traversed segment of homogeneous medium along the optical axis, recorded by its refractive
index and its axial length.

This is the ray-optical analogue of a free-space section. The name avoids the vacuum constants
`Physlib.Electromagnetism.Dynamics.Basic.FreeSpace`, and the index is allowed to be any positive
real, not only one.
-/
@[ext]
structure ParaxialGap where
  /-- The refractive index of the homogeneous medium filling the gap. -/
  index : ℝ
  /-- The axial length of the gap. -/
  length : ℝ

namespace ParaxialGap

/-- Validity of a homogeneous gap: a positive refractive index and a nonnegative axial length. -/
structure IsValid (g : ParaxialGap) : Prop where
  /-- A physical medium has a positive refractive index. -/
  index_pos : 0 < g.index
  /-- A gap is traversed downstream, so its axial length is nonnegative. -/
  length_nonneg : 0 ≤ g.length

/-- Paraxial transport of a ray coordinate across a homogeneous gap.

The angle is unchanged, because a homogeneous medium does not bend a ray, and the height advances
by `length * angle`. This is the small-angle form of `MeridionalRay.transport`; section E bounds
the difference.
-/
def transport (g : ParaxialGap) (r : ParaxialRay) : ParaxialRay where
  height := r.height + g.length * r.angle
  angle := r.angle

@[simp]
lemma transport_height (g : ParaxialGap) (r : ParaxialRay) :
    (g.transport r).height = r.height + g.length * r.angle := rfl

@[simp]
lemma transport_angle (g : ParaxialGap) (r : ParaxialRay) : (g.transport r).angle = r.angle := rfl

/-- The behaviour of a paraxial ray across a homogeneous gap, stated relationally as a condition
on an incoming and an outgoing ray coordinate.

Stating the law as a relation rather than as a function is what allows a system to be assembled
from component behaviours before any matrix is introduced.
-/
def RayBehavior (g : ParaxialGap) (r₀ r₁ : ParaxialRay) : Prop :=
  r₁.height = r₀.height + g.length * r₀.angle ∧ r₁.angle = r₀.angle

/-- The relational free-space law is exactly the graph of the paraxial transport map. -/
lemma rayBehavior_iff_eq_transport (g : ParaxialGap) (r₀ r₁ : ParaxialRay) :
    g.RayBehavior r₀ r₁ ↔ r₁ = g.transport r₀ := by
  constructor
  · rintro ⟨hHeight, hAngle⟩
    exact ParaxialRay.ext hHeight hAngle
  · rintro rfl
    exact ⟨rfl, rfl⟩

/-- A homogeneous gap transports every incoming ray coordinate to some outgoing one. -/
lemma exists_rayBehavior (g : ParaxialGap) (r₀ : ParaxialRay) :
    ∃ r₁, g.RayBehavior r₀ r₁ :=
  ⟨g.transport r₀, ⟨rfl, rfl⟩⟩

/-- The outgoing ray coordinate across a homogeneous gap is unique. -/
lemma rayBehavior_unique (g : ParaxialGap) (r₀ r₁ r₁' : ParaxialRay)
    (h : g.RayBehavior r₀ r₁) (h' : g.RayBehavior r₀ r₁') : r₁ = r₁' := by
  rw [g.rayBehavior_iff_eq_transport] at h h'
  rw [h, h']

end ParaxialGap

/-!

## D. Refracting and reflecting interfaces

-/

/-- The paraxial interfaces between two homogeneous gaps.

The six constructors are those of the source development. `prescribed` is the escape hatch for a
component whose paraxial matrix is known but not derived here; its validity condition below
requires the entries to satisfy the index-ratio determinant law, which the source does not
impose.

Radii of curvature are signed, positive when the centre of curvature lies on the outgoing side of
the surface, as fixed in the module documentation.
-/
inductive ParaxialInterface where
  /-- Refraction at a plane surface separating two media. -/
  | planeRefracting : ParaxialInterface
  /-- Refraction at a spherical surface of signed radius `radius`. -/
  | sphericalRefracting (radius : ℝ) : ParaxialInterface
  /-- Reflection at a plane mirror, in the folded convention. -/
  | planeMirror : ParaxialInterface
  /-- Reflection at a spherical mirror of signed radius `radius`, in the folded convention. -/
  | sphericalMirror (radius : ℝ) : ParaxialInterface
  /-- Reflection at a phase-conjugating mirror, which reverses the ray angle. -/
  | phaseConjugate : ParaxialInterface
  /-- A component with prescribed paraxial matrix entries `a`, `b`, `c`, `d`. -/
  | prescribed (a b c d : ℝ) : ParaxialInterface

namespace ParaxialInterface

/-- Validity of an interface carrying a ray from a medium of index `n₀` into a medium of index
`n₁`.

Both indices are positive. A curved surface needs a nonzero radius. A mirror does not change the
medium, so it forces `n₁ = n₀`. A prescribed component must satisfy the index-ratio determinant
law; this hypothesis is stronger than the source, which leaves the entries free.
-/
def IsValid (n₀ n₁ : ℝ) : ParaxialInterface → Prop
  | planeRefracting => 0 < n₀ ∧ 0 < n₁
  | sphericalRefracting radius => 0 < n₀ ∧ 0 < n₁ ∧ radius ≠ 0
  | planeMirror => 0 < n₀ ∧ n₁ = n₀
  | sphericalMirror radius => 0 < n₀ ∧ n₁ = n₀ ∧ radius ≠ 0
  | phaseConjugate => 0 < n₀ ∧ n₁ = n₀
  | prescribed a b c d => 0 < n₀ ∧ 0 < n₁ ∧ a * d - b * c = n₀ / n₁

/-- A valid interface has a positive incoming refractive index. -/
lemma index_pos_left {n₀ n₁ : ℝ} {i : ParaxialInterface} (h : i.IsValid n₀ n₁) : 0 < n₀ := by
  cases i <;> exact h.1

/-- A valid interface has a positive outgoing refractive index. -/
lemma index_pos_right {n₀ n₁ : ℝ} {i : ParaxialInterface} (h : i.IsValid n₀ n₁) : 0 < n₁ := by
  cases i with
  | planeRefracting => exact h.2
  | sphericalRefracting radius => exact h.2.1
  | planeMirror => rw [h.2]; exact h.1
  | sphericalMirror radius => rw [h.2.1]; exact h.1
  | phaseConjugate => rw [h.2]; exact h.1
  | prescribed a b c d => exact h.2.1

/-- The behaviour of a paraxial ray at an interface, stated relationally.

Every case is a model law of paraxial optics, in the sign and folding conventions fixed in the
module documentation. The refracting cases encode paraxial Snell refraction; section E bounds
their deviation from exact Snell refraction at a plane surface. The mirror cases are stated in the
folded convention, so a plane mirror leaves both entries unchanged.
-/
def RayBehavior (n₀ n₁ : ℝ) : ParaxialInterface → ParaxialRay → ParaxialRay → Prop
  | planeRefracting, r₀, r₁ =>
      r₁.height = r₀.height ∧ n₁ * r₁.angle = n₀ * r₀.angle
  | sphericalRefracting radius, r₀, r₁ =>
      r₁.height = r₀.height ∧
        n₁ * r₁.angle = n₀ * r₀.angle - (n₁ - n₀) * r₀.height / radius
  | planeMirror, r₀, r₁ =>
      r₁.height = r₀.height ∧ r₁.angle = r₀.angle
  | sphericalMirror radius, r₀, r₁ =>
      r₁.height = r₀.height ∧ r₁.angle = r₀.angle - 2 * r₀.height / radius
  | phaseConjugate, r₀, r₁ =>
      r₁.height = r₀.height ∧ r₁.angle = -r₀.angle
  | prescribed a b c d, r₀, r₁ =>
      r₁.height = a * r₀.height + b * r₀.angle ∧ r₁.angle = c * r₀.height + d * r₀.angle

/-- A valid interface transports every incoming ray coordinate to at least one outgoing one.

Existence is where the positivity of the outgoing index is used: the refracting laws determine the
outgoing angle only after division by `n₁`.
-/
lemma exists_rayBehavior {n₀ n₁ : ℝ} {i : ParaxialInterface} (h : i.IsValid n₀ n₁)
    (r₀ : ParaxialRay) : ∃ r₁, i.RayBehavior n₀ n₁ r₀ r₁ := by
  have hn₁ : n₁ ≠ 0 := (index_pos_right h).ne'
  cases i with
  | planeRefracting =>
      exact ⟨⟨r₀.height, n₀ * r₀.angle / n₁⟩, rfl, by field_simp⟩
  | sphericalRefracting radius =>
      exact ⟨⟨r₀.height, (n₀ * r₀.angle - (n₁ - n₀) * r₀.height / radius) / n₁⟩, rfl, by
        field_simp⟩
  | planeMirror => exact ⟨⟨r₀.height, r₀.angle⟩, rfl, rfl⟩
  | sphericalMirror radius => exact ⟨⟨r₀.height, r₀.angle - 2 * r₀.height / radius⟩, rfl, rfl⟩
  | phaseConjugate => exact ⟨⟨r₀.height, -r₀.angle⟩, rfl, rfl⟩
  | prescribed a b c d =>
      exact ⟨⟨a * r₀.height + b * r₀.angle, c * r₀.height + d * r₀.angle⟩, rfl, rfl⟩

/-- The outgoing ray coordinate at a valid interface is unique.

Together with `exists_rayBehavior` this says that a valid interface has a well-defined action on
ray coordinates, which `Physlib.Optics.Rays.Transfer` realises as a matrix.
-/
lemma rayBehavior_unique {n₀ n₁ : ℝ} {i : ParaxialInterface} (h : i.IsValid n₀ n₁)
    (r₀ r₁ r₁' : ParaxialRay) (hb : i.RayBehavior n₀ n₁ r₀ r₁)
    (hb' : i.RayBehavior n₀ n₁ r₀ r₁') : r₁ = r₁' := by
  have hn₁ : n₁ ≠ 0 := (index_pos_right h).ne'
  cases i with
  | planeRefracting =>
      exact ParaxialRay.ext (hb.1.trans hb'.1.symm)
        (mul_left_cancel₀ hn₁ (hb.2.trans hb'.2.symm))
  | sphericalRefracting radius =>
      exact ParaxialRay.ext (hb.1.trans hb'.1.symm)
        (mul_left_cancel₀ hn₁ (hb.2.trans hb'.2.symm))
  | planeMirror => exact ParaxialRay.ext (hb.1.trans hb'.1.symm) (hb.2.trans hb'.2.symm)
  | sphericalMirror radius =>
      exact ParaxialRay.ext (hb.1.trans hb'.1.symm) (hb.2.trans hb'.2.symm)
  | phaseConjugate => exact ParaxialRay.ext (hb.1.trans hb'.1.symm) (hb.2.trans hb'.2.symm)
  | prescribed a b c d =>
      exact ParaxialRay.ext (hb.1.trans hb'.1.symm) (hb.2.trans hb'.2.symm)

end ParaxialInterface

/-!

## E. The paraxial regime

-/

/-- The tangent function agrees with its argument to first order at zero.

This is the analytic content of the paraxial free-space law: replacing `tan θ` by `θ` in exact
rectilinear transport commits an error that is `o (θ)`.
-/
lemma tendsto_tan_sub_self_div :
    Tendsto (fun θ : ℝ => (tan θ - θ) / θ) (𝓝[≠] 0) (𝓝 0) := by
  have hcos : cos (0 : ℝ) ≠ 0 := by norm_num
  have hderiv : HasDerivAt (fun θ : ℝ => tan θ - θ) 0 0 := by
    have h := (hasDerivAt_tan hcos).sub (hasDerivAt_id' (x := (0 : ℝ)))
    have hval : (1 : ℝ) / cos (0 : ℝ) ^ 2 - 1 = 0 := by norm_num
    rw [hval] at h
    exact h
  have hslope := hderiv.tendsto_slope
  refine hslope.congr fun θ => ?_
  simp [slope_def_field]

/-- Exact Snell refraction at a plane surface implies the paraxial refraction law up to an
explicit cubic error in the two angles.

No smallness hypothesis is needed for the bound itself; it is informative exactly when both angles
are small, which is the paraxial regime.
-/
lemma abs_paraxialSnell_sub_le {n₀ n₁ θ₀ θ₁ : ℝ} (hn₀ : 0 ≤ n₀) (hn₁ : 0 ≤ n₁)
    (hSnell : n₀ * sin θ₀ = n₁ * sin θ₁) :
    |n₀ * θ₀ - n₁ * θ₁| ≤ (n₀ * |θ₀| ^ 3 + n₁ * |θ₁| ^ 3) / 6 := by
  have hrewrite : n₀ * θ₀ - n₁ * θ₁ = n₀ * (θ₀ - sin θ₀) - n₁ * (θ₁ - sin θ₁) := by
    linear_combination hSnell
  calc |n₀ * θ₀ - n₁ * θ₁|
      = |n₀ * (θ₀ - sin θ₀) - n₁ * (θ₁ - sin θ₁)| := by rw [hrewrite]
    _ ≤ |n₀ * (θ₀ - sin θ₀)| + |n₁ * (θ₁ - sin θ₁)| := by
        simpa [sub_eq_add_neg, abs_neg] using
          abs_add_le (n₀ * (θ₀ - sin θ₀)) (-(n₁ * (θ₁ - sin θ₁)))
    _ = n₀ * |θ₀ - sin θ₀| + n₁ * |θ₁ - sin θ₁| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hn₀, abs_of_nonneg hn₁]
    _ ≤ n₀ * (|θ₀| ^ 3 / 6) + n₁ * (|θ₁| ^ 3 / 6) := by
        gcongr
        · exact abs_sub_sin_le θ₀
        · exact abs_sub_sin_le θ₁
    _ = (n₀ * |θ₀| ^ 3 + n₁ * |θ₁| ^ 3) / 6 := by ring

/-- The principal-branch angle obtained by algebraically solving the sine form of Snell refraction.

Off the range where Snell refraction has a solution this returns the clamped value supplied by
`Real.arcsin`; `sin_exactRefractionAngle` states the exact Snell law under the hypothesis that
excludes total internal reflection. This definition is total even at `n₁ = 0`, where Lean's field
division is algebraically totalized and no physical refraction meaning is claimed. Physical uses
must separately supply positive medium indices and the intended propagation branch.
-/
def exactRefractionAngle (n₀ n₁ θ : ℝ) : ℝ := arcsin (n₀ / n₁ * sin θ)

/-- The exactly refracted angle satisfies Snell's law, provided the refraction ratio stays in
range, which is the condition excluding total internal reflection. -/
lemma sin_exactRefractionAngle {n₀ n₁ θ : ℝ} (hn₁ : n₁ ≠ 0) (h : |n₀ / n₁ * sin θ| ≤ 1) :
    n₀ * sin θ = n₁ * sin (exactRefractionAngle n₀ n₁ θ) := by
  have h₁ : -1 ≤ n₀ / n₁ * sin θ := neg_le_of_abs_le h
  have h₂ : n₀ / n₁ * sin θ ≤ 1 := le_of_abs_le h
  rw [exactRefractionAngle, sin_arcsin h₁ h₂]
  field_simp

/-- The paraxial angle ratio is the exact refraction ratio in the limit on the axis.

The paraxial law `n₁ θ₁ = n₀ θ₀` says the angle ratio is `n₀ / n₁`; this is exactly the analytic
limit of the principal-branch expression as the incident angle tends to zero. The identity is
stated for arbitrary real parameters using Lean's totalized division. Interpreting it as physical
refraction additionally requires positive indices; the theorem itself selects no outgoing ray.
-/
lemma tendsto_exactRefractionAngle_div (n₀ n₁ : ℝ) :
    Tendsto (fun θ : ℝ => exactRefractionAngle n₀ n₁ θ / θ) (𝓝[≠] 0) (𝓝 (n₀ / n₁)) := by
  have hinner : HasDerivAt (fun θ : ℝ => n₀ / n₁ * sin θ) (n₀ / n₁) 0 := by
    simpa using (Real.hasDerivAt_sin (0 : ℝ)).const_mul (n₀ / n₁)
  have houter : HasDerivAt arcsin 1 (n₀ / n₁ * sin (0 : ℝ)) := by
    rw [sin_zero, mul_zero]
    have h := hasDerivAt_arcsin (x := (0 : ℝ)) (by norm_num) (by norm_num)
    have hval : (1 : ℝ) / √(1 - (0 : ℝ) ^ 2) = 1 := by norm_num
    rw [hval] at h
    exact h
  have hcomp : HasDerivAt (fun θ : ℝ => exactRefractionAngle n₀ n₁ θ) (n₀ / n₁) 0 := by
    have h := houter.comp 0 hinner
    rw [one_mul] at h
    exact h
  have hslope := hcomp.tendsto_slope
  refine hslope.congr fun θ => ?_
  simp [slope_def_field, exactRefractionAngle]

namespace ParaxialGap

/-- The paraxial free-space law reproduces exact rectilinear transport to first order in the ray
angle.

The numerator is the difference between the height reached by exact transport of a meridional ray
and the height given by the paraxial law across a gap of the same axial length. Dividing by the
ray angle and letting it tend to zero returns zero, so the paraxial law is correct to first order
in the angle and its error is `o (angle)`.
-/
lemma tendsto_transport_height_error (g : ParaxialGap) (y z : ℝ) :
    Tendsto (fun θ : ℝ =>
        (((MeridionalRay.mk y z θ).transport g.length).height -
          (g.transport (MeridionalRay.mk y z θ).toParaxial).height) / θ)
      (𝓝[≠] 0) (𝓝 0) := by
  have hmul := tendsto_tan_sub_self_div.const_mul g.length
  rw [mul_zero] at hmul
  refine hmul.congr fun θ => ?_
  simp only [MeridionalRay.transport_height, transport_height, MeridionalRay.toParaxial_height,
    MeridionalRay.toParaxial_angle]
  ring

end ParaxialGap

/-!

## F. Hook for the exact-incidence bridge

-/

/-- The unit normal of a meridional plane section whose normal is tilted by `normalAngle` from the
optical axis, in `(transverse, axial)` components. -/
def meridionalSurfaceNormal (normalAngle : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  !₂[sin normalAngle, cos normalAngle]

/-- A meridional surface normal is a unit vector. -/
lemma norm_meridionalSurfaceNormal (normalAngle : ℝ) :
    ‖meridionalSurfaceNormal normalAngle‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs, sin_sq_add_cos_sq,
    meridionalSurfaceNormal]

namespace MeridionalRay

/-- The signed difference between a meridional ray angle and a plane-normal angle.

This is the named hook for the cross-lane bridge that `goal.md` §H.5 R1 asks for, between the
paraxial ray angle used here and the exact geometric incidence directions of E5b. That bridge
cannot live in this module, whose layering rule forbids importing `Physlib.Optics.Interfaces`.
The objects it needs from the ray side are `Optics.MeridionalRay.direction`,
`Optics.meridionalSurfaceNormal` and this signed difference, tied together by
`Optics.MeridionalRay.cos_signedIncidenceAngle` below. The E5b angle is an unoriented Euclidean
angle in `[0, π]`, so equality of these real numbers is not asserted. A bridge must use the cosine
identity together with explicit range and side conventions. The target is
`Physlib.Optics.Interfaces.PlanarDielectric.AngularGeometry`, which measures its incident and
transmitted phase angles from the normal into the *positive* side and its reflected phase angle
from the normal into the *negative* side. Reconciling those side choices with the single normal
angle used here is the first thing that bridge has to fix.
-/
def signedIncidenceAngle (r : MeridionalRay) (normalAngle : ℝ) : ℝ := r.angle - normalAngle

@[simp]
lemma signedIncidenceAngle_zero (r : MeridionalRay) : r.signedIncidenceAngle 0 = r.angle := by
  simp [signedIncidenceAngle]

/-- The cosine of the signed meridional angle difference is the inner product of the ray direction
and the meridional surface normal.

This is the dimension-two identity that a later range-guarded bridge to E5b's unoriented angle must
pass through. Equality of cosines alone does not identify the two angle values.
-/
lemma cos_signedIncidenceAngle (r : MeridionalRay) (normalAngle : ℝ) :
    cos (r.signedIncidenceAngle normalAngle) =
      inner ℝ r.direction (meridionalSurfaceNormal normalAngle) := by
  rw [signedIncidenceAngle, cos_sub, PiLp.inner_apply]
  simp [Fin.sum_univ_two, direction, meridionalSurfaceNormal, RCLike.inner_apply]
  ring

end MeridionalRay

end

end Optics
