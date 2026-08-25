/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Rays.Basic

/-!
# Regression tests for paraxial and physical rays

## i. Overview

Exact rational fixtures pin the sign, ordering, and index conventions of the paraxial ray laws,
and identity limits pin the degenerate cases every later ray module inherits.

The refracting fixtures are chosen so that an inverted index ratio, a dropped index step, or a
flipped curvature sign changes the stated value. The converging-surface fixture in particular
records the physical requirement that a surface with a positive radius and a positive index step
bends an axis-parallel ray *towards* the axis, so its outgoing angle is negative.

The final section checks the exact-versus-paraxial bridge in the direction physics fixes: over a
gap the paraxial law strictly underestimates the height reached by a ray at a positive angle,
because `θ < tan θ`.

## ii. Key results

- `Optics.raysBasicRegression_transport`: gap transport in the fixed coordinate ordering.
- `Optics.raysBasicRegression_planeRefracting`: the index ratio is `n₀ / n₁`, not its inverse.
- `Optics.raysBasicRegression_sphericalRefracting_converging`: a converging surface bends an
  axis-parallel ray towards the axis.
- `Optics.raysBasicRegression_sphericalMirror_focal`: a concave mirror of radius `R` focuses an
  axis-parallel ray at `R / 2`.
- `Optics.raysBasicRegression_phaseConjugate_ne_planeMirror`: the folded plane mirror and the
  phase-conjugating mirror are different components.
- `Optics.raysBasicRegression_paraxial_height_lt_exact`: the paraxial gap law underestimates the
  exactly transported height at a positive ray angle.

## iii. Table of contents

- A. Gap transport sentinels
- B. Interface sign and convention sentinels
- C. Identity and zero limits
- D. Exact-versus-paraxial sentinels

## iv. References

The fixtures use only the public declarations of `Physlib.Optics.Rays.Basic`; their coefficients
make no material, dispersion, or fabrication claim.

-/

@[expose] public section

namespace Optics

noncomputable section

open Real

/-!

## A. Gap transport sentinels

-/

/-- A homogeneous gap of index `3 / 2` and axial length `3`. -/
def raysBasicRegressionGap : ParaxialGap := ⟨3 / 2, 3⟩

/-- The regression gap is a valid homogeneous gap. -/
lemma raysBasicRegressionGap_isValid : raysBasicRegressionGap.IsValid where
  index_pos := by norm_num [raysBasicRegressionGap]
  length_nonneg := by norm_num [raysBasicRegressionGap]

/-- An incoming ray coordinate of height `1` and angle `1 / 10`. -/
def raysBasicRegressionRay : ParaxialRay := ⟨1, 1 / 10⟩

/-- Transport across the regression gap raises the height by `length * angle` and leaves the angle
alone. Exchanging the two coordinates or the two factors changes this value. -/
lemma raysBasicRegression_transport :
    raysBasicRegressionGap.transport raysBasicRegressionRay = ⟨13 / 10, 1 / 10⟩ := by
  simp only [ParaxialGap.transport, raysBasicRegressionGap, raysBasicRegressionRay]
  norm_num

/-- The transported coordinate is reached through the relational gap law, not only through the
transport map. -/
lemma raysBasicRegression_transport_rayBehavior :
    raysBasicRegressionGap.RayBehavior raysBasicRegressionRay ⟨13 / 10, 1 / 10⟩ := by
  rw [ParaxialGap.rayBehavior_iff_eq_transport, raysBasicRegression_transport]

/-!

## B. Interface sign and convention sentinels

-/

/-- Plane refraction from index `1` into index `3 / 2` scales the angle by `n₀ / n₁ = 2 / 3`.

An inverted index ratio would give the angle `3 / 20` instead of `1 / 15`.
-/
lemma raysBasicRegression_planeRefracting :
    ParaxialInterface.planeRefracting.RayBehavior 1 (3 / 2) raysBasicRegressionRay
      ⟨1, 1 / 15⟩ := by
  refine ⟨rfl, ?_⟩
  norm_num [raysBasicRegressionRay]

/-- Plane refraction is a valid interface between the two regression indices. -/
lemma raysBasicRegression_planeRefracting_isValid :
    ParaxialInterface.planeRefracting.IsValid 1 (3 / 2) := by
  constructor <;> norm_num

/-- The refracted coordinate is the only one satisfying the relational interface law. -/
lemma raysBasicRegression_planeRefracting_unique (r₁ : ParaxialRay)
    (h : ParaxialInterface.planeRefracting.RayBehavior 1 (3 / 2) raysBasicRegressionRay r₁) :
    r₁ = ⟨1, 1 / 15⟩ :=
  ParaxialInterface.rayBehavior_unique raysBasicRegression_planeRefracting_isValid
    raysBasicRegressionRay r₁ ⟨1, 1 / 15⟩ h raysBasicRegression_planeRefracting

/-- A spherical surface of positive radius `1` separating index `1` from index `3 / 2` bends an
axis-parallel ray at height `1` to the angle `-1 / 3`.

The sign is the physical content: a converging surface sends the ray towards the axis. Dropping
the index step, or flipping the curvature sign, reverses it.
-/
lemma raysBasicRegression_sphericalRefracting_converging :
    (ParaxialInterface.sphericalRefracting 1).RayBehavior 1 (3 / 2) ⟨1, 0⟩ ⟨1, -1 / 3⟩ := by
  refine ⟨rfl, ?_⟩
  norm_num

/-- The converging-surface fixture has a strictly negative outgoing angle. -/
lemma raysBasicRegression_sphericalRefracting_angle_neg :
    (⟨1, -1 / 3⟩ : ParaxialRay).angle < 0 := by norm_num

/-- A concave mirror of radius `2` sends an axis-parallel ray at height `1` to the angle `-1`, so
it crosses the axis one unit downstream, at the focal distance `R / 2`. -/
lemma raysBasicRegression_sphericalMirror_focal :
    (ParaxialInterface.sphericalMirror 2).RayBehavior 1 1 ⟨1, 0⟩ ⟨1, -1⟩ := by
  refine ⟨rfl, ?_⟩
  norm_num

/-- The folded plane mirror leaves a ray angle alone, while the phase-conjugating mirror reverses
it, so the two components are not interchangeable. -/
lemma raysBasicRegression_phaseConjugate_ne_planeMirror :
    ParaxialInterface.phaseConjugate.RayBehavior 1 1 raysBasicRegressionRay ⟨1, -1 / 10⟩ ∧
      ¬ ParaxialInterface.planeMirror.RayBehavior 1 1 raysBasicRegressionRay ⟨1, -1 / 10⟩ := by
  refine ⟨⟨rfl, by norm_num [raysBasicRegressionRay]⟩, ?_⟩
  rintro ⟨-, hAngle⟩
  norm_num [raysBasicRegressionRay] at hAngle

/-- A prescribed component is valid only when its entries obey the index-ratio determinant law;
the identity entries are valid exactly between equal indices. -/
lemma raysBasicRegression_prescribed_isValid :
    (ParaxialInterface.prescribed 1 0 0 1).IsValid 2 2 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  norm_num

/-- Identity entries are not a valid prescribed component across an index step, because their
determinant is `1` rather than `n₀ / n₁`. -/
lemma raysBasicRegression_prescribed_not_isValid :
    ¬ (ParaxialInterface.prescribed 1 0 0 1).IsValid 1 (3 / 2) := by
  rintro ⟨-, -, hDet⟩
  norm_num at hDet

/-!

## C. Identity and zero limits

-/

/-- A gap of zero length transports every ray coordinate to itself. -/
lemma raysBasicRegression_transport_length_zero (n : ℝ) (r : ParaxialRay) :
    (⟨n, 0⟩ : ParaxialGap).transport r = r := by
  ext <;> simp [ParaxialGap.transport]

/-- Plane refraction between equal indices leaves the ray coordinate unchanged. -/
lemma raysBasicRegression_planeRefracting_matched {n : ℝ} (hn : n ≠ 0) (r₀ r₁ : ParaxialRay)
    (h : ParaxialInterface.planeRefracting.RayBehavior n n r₀ r₁) : r₁ = r₀ :=
  ParaxialRay.ext h.1 (mul_left_cancel₀ hn h.2)

/-- A spherical surface between equal indices leaves the ray coordinate unchanged, whatever its
radius: with no index step there is nothing to refract. -/
lemma raysBasicRegression_sphericalRefracting_matched {n radius : ℝ} (hn : n ≠ 0)
    (r₀ r₁ : ParaxialRay)
    (h : (ParaxialInterface.sphericalRefracting radius).RayBehavior n n r₀ r₁) : r₁ = r₀ := by
  refine ParaxialRay.ext h.1 (mul_left_cancel₀ hn ?_)
  rw [h.2]
  ring

/-- Between equal indices the exactly refracted angle is the incident angle, for any incident
angle in the principal range. This is the identity limit of `Optics.exactRefractionAngle`. -/
lemma raysBasicRegression_exactRefractionAngle_matched {n θ : ℝ} (hn : n ≠ 0)
    (h₁ : -(π / 2) ≤ θ) (h₂ : θ ≤ π / 2) : exactRefractionAngle n n θ = θ := by
  rw [exactRefractionAngle, div_self hn, one_mul, arcsin_sin h₁ h₂]

/-!

## D. Exact-versus-paraxial sentinels

-/

/-- Over a gap of positive length the paraxial law strictly underestimates the height reached by
exact rectilinear transport of a ray at a positive angle, because `θ < tan θ`.

This fixes the direction of the small-angle error proved in `Physlib.Optics.Rays.Basic`; a sign
slip in the bridge would reverse it.
-/
lemma raysBasicRegression_paraxial_height_lt_exact (g : ParaxialGap) (y z θ : ℝ)
    (hLength : 0 < g.length) (hPos : 0 < θ) (hRange : θ < π / 2) :
    (g.transport (MeridionalRay.mk y z θ).toParaxial).height <
      ((MeridionalRay.mk y z θ).transport g.length).height := by
  have hTan : θ < tan θ := lt_tan hPos hRange
  simp only [ParaxialGap.transport_height, MeridionalRay.toParaxial_height,
    MeridionalRay.toParaxial_angle, MeridionalRay.transport_height]
  nlinarith

/-- The cubic paraxial-Snell bound specialised to a refraction from index `1` into index `3 / 2`,
exercising `Optics.abs_paraxialSnell_sub_le` through its public statement. -/
lemma raysBasicRegression_snellBound {θ₀ θ₁ : ℝ} (h : 1 * sin θ₀ = 3 / 2 * sin θ₁) :
    |1 * θ₀ - 3 / 2 * θ₁| ≤ (1 * |θ₀| ^ 3 + 3 / 2 * |θ₁| ^ 3) / 6 :=
  abs_paraxialSnell_sub_le (by norm_num) (by norm_num) h

end

end Optics
