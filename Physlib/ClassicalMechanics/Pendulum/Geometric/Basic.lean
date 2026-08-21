/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.SpaceAndTime.Space.Basic
public import Mathlib.Geometry.Manifold.Instances.Sphere
/-!

# Configuration space of the simple gravity pendulum

## i. Overview

The configuration space of a simple pendulum constrained to a plane is the circle
`S¹`: the bob is a fixed distance from the pivot, so its position is determined by an
angle. Mathlib already provides this manifold as `Circle`, the unit circle in `ℂ`, with
an analytic `ChartedSpace` / `IsManifold` structure modelled on
`EuclideanSpace ℝ (Fin 1)`.

This file wraps `Circle` as `ConfigurationSpace`, records the homeomorphism with `S¹`,
and embeds a configuration of rod length `ℓ` into two-dimensional Physlib `Space`.
The embedding uses the standard pendulum chart: the angle `θ` is measured from the
downward vertical, the pivot is at the origin, and the positive `y`-axis points up, so
the bob at angle `θ` sits at `(ℓ sin θ, -ℓ cos θ)`.

The Euler–Lagrange operator in Physlib is defined on Hilbert-space-valued
trajectories, not on `S¹` itself. Dynamics therefore still use the angular chart
`EuclideanSpace ℝ (Fin 1)` in `SimplePendulum.lean`; this file is the geometric model
that chart simplifies.

## ii. Key results

- `ConfigurationSpace` : the circle of possible rod directions.
- `ConfigurationSpace.valHomeomorphism` : identification with Mathlib `Circle`.
- `ConfigurationSpace.ofAngle` : the configuration `Circle.exp θ`.
- `ConfigurationSpace.toSpace` : the position of the bob in `Space 2`.
- `toSpace_ofAngle` : `toSpace ℓ (ofAngle θ)` is `(ℓ sin θ, -ℓ cos θ)`.

## iii. Table of contents

- A. The configuration space type
- B. Topology and identification with `Circle`
- C. Manifold structure
- D. The angular chart
- E. Map to physical space

## iv. References

- Landau & Lifshitz, Mechanics, 3rd ed., §5.
- Mathlib, `Geometry.Manifold.Instances.Sphere` (`Circle`).

-/

open scoped Manifold

@[expose]
public noncomputable section

namespace ClassicalMechanics
namespace SimplePendulum

/-!
## A. The configuration space type

-/

/-- The configuration space of a planar simple pendulum: the circle `S¹` of possible
  directions of the rod. -/
structure ConfigurationSpace where
  /-- The underlying point of Mathlib's unit circle in `ℂ`. -/
  val : Circle

namespace ConfigurationSpace

@[ext]
lemma ext {x y : ConfigurationSpace} (h : x.val = y.val) : x = y := by
  cases x
  cases y
  subst h
  rfl

/-!
## B. Topology and identification with `Circle`

-/

instance : TopologicalSpace ConfigurationSpace :=
  TopologicalSpace.induced ConfigurationSpace.val inferInstance

/-- The identification of configuration space with Mathlib `Circle`. -/
def valEquiv : ConfigurationSpace ≃ Circle where
  toFun := ConfigurationSpace.val
  invFun z := ⟨z⟩
  left_inv x := by cases x; rfl
  right_inv z := rfl

/-- Configuration space is homeomorphic to the unit circle. -/
def valHomeomorphism : ConfigurationSpace ≃ₜ Circle where
  toEquiv := valEquiv
  continuous_toFun := continuous_induced_dom
  continuous_invFun := by
    apply continuous_induced_rng.mpr
    exact continuous_id

instance : T2Space ConfigurationSpace := valHomeomorphism.symm.t2Space

instance : SecondCountableTopology ConfigurationSpace :=
  valHomeomorphism.secondCountableTopology

instance : Nonempty ConfigurationSpace := ⟨⟨1⟩⟩

/-!
## C. Manifold structure

The charted-space and analytic-manifold structures are those of `Circle`, transported
along `valHomeomorphism`.

-/

instance : ChartedSpace (EuclideanSpace ℝ (Fin 1)) ConfigurationSpace :=
  valHomeomorphism.symm.chartedSpace

/-- The circle `S¹` is an analytic one-manifold; this is the geometric configuration
  space of the pendulum. -/
lemma circle_isManifold : IsManifold (𝓡 1) ω Circle := inferInstance

/-!
## D. The angular chart

`Circle.exp θ = e^{iθ}` is the standard covering `ℝ → S¹`. The pendulum convention
measures `θ` from the downward vertical.

-/

/-- The configuration at angular coordinate `θ` (from the downward vertical). -/
def ofAngle (θ : ℝ) : ConfigurationSpace := ⟨Circle.exp θ⟩

/-- The configuration corresponding to a one-dimensional Euclidean chart value. -/
def ofCoord (x : EuclideanSpace ℝ (Fin 1)) : ConfigurationSpace := ofAngle (x 0)

lemma ofAngle_zero : ofAngle 0 = ⟨1⟩ := by
  simp [ofAngle]

lemma coe_ofAngle (θ : ℝ) : (ofAngle θ).val = Circle.exp θ := rfl

lemma ofAngle_re (θ : ℝ) : ((ofAngle θ).val : ℂ).re = Real.cos θ := by
  simp [ofAngle, Circle.coe_exp, Complex.exp_mul_I, Complex.cos_ofReal_re]

lemma ofAngle_im (θ : ℝ) : ((ofAngle θ).val : ℂ).im = Real.sin θ := by
  simp [ofAngle, Circle.coe_exp, Complex.exp_mul_I, Complex.sin_ofReal_re]

/-!
## E. Map to physical space

The pivot is the origin of `Space 2`, with the first coordinate horizontal and the
second coordinate upward. A rod of length `ℓ` at angle `θ` places the bob at
`(ℓ sin θ, -ℓ cos θ)`.

-/

/-- The position of the bob in the plane, for a rod of length `ℓ`. -/
def toSpace (ℓ : ℝ) (q : ConfigurationSpace) : Space 2 :=
  ⟨![ℓ * (q.val : ℂ).im, -ℓ * (q.val : ℂ).re]⟩

lemma toSpace_apply_zero (ℓ : ℝ) (q : ConfigurationSpace) :
    (toSpace ℓ q) 0 = ℓ * (q.val : ℂ).im := rfl

lemma toSpace_apply_one (ℓ : ℝ) (q : ConfigurationSpace) :
    (toSpace ℓ q) 1 = -ℓ * (q.val : ℂ).re := rfl

/-- Cartesian coordinates of the bob in the standard pendulum chart. -/
lemma toSpace_ofAngle (ℓ θ : ℝ) :
    toSpace ℓ (ofAngle θ) = ⟨![ℓ * Real.sin θ, -ℓ * Real.cos θ]⟩ := by
  ext i
  fin_cases i <;> simp [toSpace, ofAngle_im, ofAngle_re]

lemma toSpace_ofAngle_horizontal (ℓ θ : ℝ) :
    toSpace ℓ (ofAngle θ) 0 = ℓ * Real.sin θ := by
  simp [toSpace_ofAngle]

lemma toSpace_ofAngle_vertical (ℓ θ : ℝ) :
    toSpace ℓ (ofAngle θ) 1 = -ℓ * Real.cos θ := by
  simp [toSpace_ofAngle]

/-- At `θ = 0` the bob hangs straight down, at `(0, -ℓ)`. -/
lemma toSpace_ofAngle_zero (ℓ : ℝ) :
    toSpace ℓ (ofAngle 0) = ⟨![0, -ℓ]⟩ := by
  simp [toSpace_ofAngle]

end ConfigurationSpace

end SimplePendulum
end ClassicalMechanics

end
