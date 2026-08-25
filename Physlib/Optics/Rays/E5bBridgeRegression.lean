/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Rays.E5bBridge

/-!
# Regression tests for the ray-to-interface bridge

## i. Overview

The fixture is the exact `3-4-5` direction `(3/5, 0, 4/5)` against a third-coordinate interface
normal, the same numbers the incidence-frame regressions of
`Physlib.Optics.Polarization` use. It is rebuilt here rather than imported, so that this file
depends only on the bridge.

Two things are checked that a purely symbolic statement would not catch. The constructed ambient
direction really is `(3/5, 0, 4/5)`, so the angle convention is pinned to actual coordinates rather
than to a name. And the reflected direction really is `(3/5, 0, -4/5)`, the mirror image through
the interface, whose angle *to the opposite side* is the same as the incident angle to the incoming
side — which is the exact content of the folded plane-mirror law, on a fixture where a sign error
would be visible as a changed coordinate.

## ii. Key results

- `Optics.e5bBridgeRegression_direction`: the constructed direction is `(3/5, 0, 4/5)`.
- `Optics.e5bBridgeRegression_angleToSide`: its interface-side angle is the fixture angle.
- `Optics.e5bBridgeRegression_reflected_direction`: the reflected direction is `(3/5, 0, -4/5)`.
- `Optics.e5bBridgeRegression_reflected_angleToSide`: the reflected ray makes the same angle into
  the outgoing side.
- `Optics.e5bBridgeRegression_incidenceTangent`: the canonical tangent constructed from the
  fixture phase vector is the fixture tangent.
- `Optics.e5bBridgeRegression_meridionalPlane_proper`: the meridional plane is a proper subspace,
  so it is a genuine constraint.

## iii. Table of contents

- A. The fixture
- B. Incidence
- C. Reflection
- D. The canonical tangent and the meridional plane

## iv. References

The fixture uses only the public declarations of `Physlib.Optics.Rays.E5bBridge`.

-/

@[expose] public section

namespace Optics

noncomputable section

open Real Space

/-!

## A. The fixture

-/

/-- The positive third-coordinate interface normal of the regression fixture. -/
def e5bBridgeRegressionNormal : Space.Direction 3 :=
  ⟨⟨![0, 0, 1]⟩, by
    rw [Space.norm_eq]
    simp [Fin.sum_univ_three]⟩

/-- The oriented coordinate interface of the regression fixture. -/
def e5bBridgeRegressionPlane : OrientedAffineHyperplane 3 where
  point := 0
  normal := e5bBridgeRegressionNormal

/-- The first-coordinate tangent axis of the regression fixture. -/
def e5bBridgeRegressionTangent : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 ![1, 0, 0]

/-- The fixture tangent is a unit vector. -/
lemma e5bBridgeRegressionTangent_norm : ‖e5bBridgeRegressionTangent‖ = 1 := by
  rw [e5bBridgeRegressionTangent, EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_three]

/-- The fixture tangent lies in the interface. -/
lemma e5bBridgeRegressionTangent_normalComponent :
    e5bBridgeRegressionPlane.normalComponent e5bBridgeRegressionTangent = 0 := by
  rw [OrientedAffineHyperplane.normalComponent, OrientedAffineHyperplane.normalVector,
    e5bBridgeRegressionPlane, e5bBridgeRegressionNormal, e5bBridgeRegressionTangent]
  simp [PiLp.inner_apply, Fin.sum_univ_three, Space.basis]

/-- The fixture incidence angle, whose cosine is `4 / 5` and whose sine is `3 / 5`. -/
def e5bBridgeRegressionAngle : ℝ := arccos (4 / 5)

/-- The fixture angle has cosine `4 / 5`. -/
@[simp]
lemma e5bBridgeRegression_cos : cos e5bBridgeRegressionAngle = 4 / 5 := by
  rw [e5bBridgeRegressionAngle, Real.cos_arccos] <;> norm_num

/-- The fixture angle has sine `3 / 5`, the `3-4-5` relation. -/
@[simp]
lemma e5bBridgeRegression_sin : sin e5bBridgeRegressionAngle = 3 / 5 := by
  rw [e5bBridgeRegressionAngle, Real.sin_arccos]
  rw [show (1 : ℝ) - (4 / 5) ^ 2 = (3 / 5) ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

/-- The fixture angle lies in the range where the unoriented interface angle can equal it. -/
lemma e5bBridgeRegressionAngle_mem :
    0 ≤ e5bBridgeRegressionAngle ∧ e5bBridgeRegressionAngle ≤ π :=
  ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩

/-!

## B. Incidence

-/

/-- **The constructed ambient direction is exactly `(3/5, 0, 4/5)`.**

This pins the angle convention to coordinates. A side or sign error would move the `4/5` component
onto the wrong axis or flip it.
-/
lemma e5bBridgeRegression_direction :
    meridionalDirection e5bBridgeRegressionPlane .positive e5bBridgeRegressionTangent
        e5bBridgeRegressionAngle = WithLp.toLp 2 ![3 / 5, 0, 4 / 5] := by
  rw [meridionalDirection, e5bBridgeRegression_cos, e5bBridgeRegression_sin,
    OrientedAffineHyperplane.sideNormalVector_positive, OrientedAffineHyperplane.normalVector,
    e5bBridgeRegressionPlane, e5bBridgeRegressionNormal, e5bBridgeRegressionTangent]
  ext i
  fin_cases i <;> simp [Space.basis]

/-- The constructed direction is a unit vector. -/
lemma e5bBridgeRegression_direction_norm :
    ‖meridionalDirection e5bBridgeRegressionPlane .positive e5bBridgeRegressionTangent
      e5bBridgeRegressionAngle‖ = 1 :=
  norm_meridionalDirection _ _ _ _ e5bBridgeRegressionTangent_norm
    e5bBridgeRegressionTangent_normalComponent

/-- **The interface-side angle of the fixture direction is the fixture angle.** -/
lemma e5bBridgeRegression_angleToSide :
    e5bBridgeRegressionPlane.angleToSide .positive
        (meridionalDirection e5bBridgeRegressionPlane .positive e5bBridgeRegressionTangent
          e5bBridgeRegressionAngle) = e5bBridgeRegressionAngle :=
  angleToSide_meridionalDirection _ _ _ _ e5bBridgeRegressionTangent_norm
    e5bBridgeRegressionTangent_normalComponent e5bBridgeRegressionAngle_mem.1
    e5bBridgeRegressionAngle_mem.2

/-!

## C. Reflection

-/

/-- **The reflected direction is exactly `(3/5, 0, -4/5)`**, the mirror image of the incident
direction through the interface. -/
lemma e5bBridgeRegression_reflected_direction :
    e5bBridgeRegressionPlane.vectorReflection
        (meridionalDirection e5bBridgeRegressionPlane .positive e5bBridgeRegressionTangent
          e5bBridgeRegressionAngle) = WithLp.toLp 2 ![3 / 5, 0, -(4 / 5)] := by
  rw [vectorReflection_meridionalDirection _ _ _ _ e5bBridgeRegressionTangent_normalComponent,
    meridionalDirection, e5bBridgeRegression_cos, e5bBridgeRegression_sin,
    OrientedAffineHyperplane.sideNormalVector_opposite,
    OrientedAffineHyperplane.sideNormalVector_positive, OrientedAffineHyperplane.normalVector,
    e5bBridgeRegressionPlane, e5bBridgeRegressionNormal, e5bBridgeRegressionTangent]
  ext i
  fin_cases i <;> simp [Space.basis]

/-- **The reflected ray makes the same angle into the outgoing side.**

This is the folded plane-mirror law on the fixture: the incident direction makes the fixture angle
with the positive-side normal, and the reflected direction makes the same angle with the
negative-side normal. Re-referencing the axis is the exchange of sides.
-/
lemma e5bBridgeRegression_reflected_angleToSide :
    e5bBridgeRegressionPlane.angleToSide .negative
        (e5bBridgeRegressionPlane.vectorReflection
          (meridionalDirection e5bBridgeRegressionPlane .positive e5bBridgeRegressionTangent
            e5bBridgeRegressionAngle)) = e5bBridgeRegressionAngle :=
  angleToSide_vectorReflection_meridionalDirection _ _ _ _ e5bBridgeRegressionTangent_norm
    e5bBridgeRegressionTangent_normalComponent e5bBridgeRegressionAngle_mem.1
    e5bBridgeRegressionAngle_mem.2

/-!

## D. The canonical tangent and the meridional plane

-/

/-- The fixture incident phase vector, the exact `3-4-5` direction. -/
def e5bBridgeRegressionPhase : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 ![3 / 5, 0, 4 / 5]

/-- The tangential projection of the fixture phase vector is `(3/5, 0, 0)`. -/
lemma e5bBridgeRegression_tangentialProjection :
    e5bBridgeRegressionPlane.tangentialProjection e5bBridgeRegressionPhase =
      WithLp.toLp 2 ![3 / 5, 0, 0] := by
  rw [OrientedAffineHyperplane.tangentialProjection, OrientedAffineHyperplane.normalComponent,
    OrientedAffineHyperplane.normalVector, e5bBridgeRegressionPlane, e5bBridgeRegressionNormal,
    e5bBridgeRegressionPhase]
  ext i
  fin_cases i <;> simp [Space.basis, PiLp.inner_apply, Fin.sum_univ_three]

/-- That projection is `3 / 5` times the fixture tangent. -/
lemma e5bBridgeRegression_tangentialProjection_smul :
    e5bBridgeRegressionPlane.tangentialProjection e5bBridgeRegressionPhase =
      (3 / 5 : ℝ) • e5bBridgeRegressionTangent := by
  rw [e5bBridgeRegression_tangentialProjection, e5bBridgeRegressionTangent]
  ext i
  fin_cases i <;> simp

/-- Its norm is `3 / 5`. -/
lemma e5bBridgeRegression_tangentialProjection_norm :
    ‖e5bBridgeRegressionPlane.tangentialProjection e5bBridgeRegressionPhase‖ = 3 / 5 := by
  rw [e5bBridgeRegression_tangentialProjection_smul, norm_smul,
    e5bBridgeRegressionTangent_norm, mul_one, Real.norm_eq_abs]
  norm_num

/-- The fixture is not at normal incidence. -/
lemma e5bBridgeRegression_tangentialProjection_ne_zero :
    e5bBridgeRegressionPlane.tangentialProjection e5bBridgeRegressionPhase ≠ 0 := by
  intro hzero
  have hnorm := e5bBridgeRegression_tangentialProjection_norm
  rw [hzero, norm_zero] at hnorm
  norm_num at hnorm

/-- **The canonical tangent constructed from the fixture phase vector is the fixture tangent.**

This ties the general construction of section F to coordinates: the normalised tangential
projection of `(3/5, 0, 4/5)` against a third-coordinate normal is exactly `(1, 0, 0)`.
-/
lemma e5bBridgeRegression_incidenceTangent :
    incidenceTangent e5bBridgeRegressionPlane e5bBridgeRegressionPhase =
      e5bBridgeRegressionTangent := by
  rw [incidenceTangent, e5bBridgeRegression_tangentialProjection_norm,
    e5bBridgeRegression_tangentialProjection_smul, smul_smul,
    show ((3 : ℝ) / 5)⁻¹ * (3 / 5) = 1 by norm_num, one_smul]

/-- **The meridional plane is a proper subspace.**

The second coordinate axis is not in it, so the plane is a genuine constraint on the three phase
vectors rather than a statement that holds vacuously.
-/
lemma e5bBridgeRegression_meridionalPlane_proper :
    WithLp.toLp 2 ![(0 : ℝ), 1, 0] ∉
      meridionalPlaneSpan e5bBridgeRegressionPlane e5bBridgeRegressionPhase := by
  rw [meridionalPlaneSpan, e5bBridgeRegression_incidenceTangent, Submodule.mem_span_pair]
  rintro ⟨a, b, hab⟩
  have h := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 1) hab
  rw [e5bBridgeRegressionTangent, OrientedAffineHyperplane.normalVector,
    e5bBridgeRegressionPlane, e5bBridgeRegressionNormal] at h
  simp [Space.basis] at h

end

end Optics
