/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.SpaceAndTime.Space.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Geometry.Manifold.Instances.Sphere
/-!

# Configuration space of the simple pendulum

## i. Overview

A simple pendulum is a bob fixed to one end of a rigid massless rod of length `ℓ`, the other end
of which is pinned at a pivot, swinging in a vertical plane under gravity. Its position is fixed by
the angle of the rod from the downward vertical, and two angles that differ by a full turn describe
the same position. The configuration space is therefore a circle.

We record a configuration by its angle modulo `2π`, i.e. by an element of `Real.Angle`, as the
sliding pendulum does (`Physlib.ClassicalMechanics.Pendulum.SlidingPendulum`). The circle carries
the structure of a compact analytic one-dimensional manifold; we obtain it by identifying the
configuration space with Mathlib's unit circle `Circle` and pulling back its charts. The real-valued
angle that is used to write down the dynamics is a lift of the configuration to the universal cover
`ℝ → ConfigurationSpace`; it is not a chart, and two lifts differing by `2π n` describe the same
motion. Finally the position of the bob in the plane is recorded by `toSpace ℓ`, which sends the
configuration at angle `θ` to `(ℓ sin θ, -ℓ cos θ)`: the pivot is the origin and the second axis
points upwards.

## ii. Key results

- `ConfigurationSpace` : the configuration space of the planar simple pendulum.
- `ConfigurationSpace.circleHomeomorph` : its identification with the unit circle.
- `ConfigurationSpace.instChartedSpace`, `ConfigurationSpace.instIsManifold` : the analytic
  manifold structure, pulled back from `Circle`.
- `ConfigurationSpace.ofAngle` : the angular lift `ℝ → ConfigurationSpace`, periodic with period
  `2π`, continuous and surjective.
- `ConfigurationSpace.toSpace` : the position of the bob in `Space 2`, with
  `toSpace_ofAngle` and the rod-length constraint `toSpace_norm`.

## iii. Table of contents

- A. The configuration space type
- B. Topology and identification with the unit circle
- C. Manifold structure
- D. The angular lift
- E. Map to physical space

## iv. References

- Landau & Lifshitz, Mechanics, 3rd ed., §5, Problems 1–3 (pendulum configurations).
- Mathlib, `Mathlib.Geometry.Manifold.Instances.Sphere` (the manifold structure on `Circle`).

-/

@[expose] public section

noncomputable section

open scoped Manifold ContDiff

namespace ClassicalMechanics
namespace SimplePendulum

/-!

## A. The configuration space type

A configuration is the angle of the rod from the downward vertical, taken modulo a full turn.

-/

/-- The configuration space of the planar simple pendulum: the angle of the rod from the downward
  vertical, modulo `2π`. -/
structure ConfigurationSpace where
  /-- The angle of the rod from the downward vertical, modulo `2π`. -/
  angle : Real.Angle

namespace ConfigurationSpace

/-- Two configurations are equal precisely when their angles are equal. -/
@[ext]
lemma ext {p q : ConfigurationSpace} (h : p.angle = q.angle) : p = q := by
  cases p; cases q; cases h; rfl

/-!

## B. Topology and identification with the unit circle

The topology is that of `Real.Angle`; composing with Mathlib's identification of `Real.Angle`
(the additive circle of period `2π`) with the unit circle `Circle ⊆ ℂ` gives a homeomorphism
`ConfigurationSpace ≃ₜ Circle`, through which the circle's compactness and Hausdorff property
transfer.

-/

/-- The identification of the configuration space with `Real.Angle`. -/
def angleEquiv : ConfigurationSpace ≃ Real.Angle where
  toFun := angle
  invFun φ := ⟨φ⟩
  left_inv q := by cases q; rfl
  right_inv φ := rfl

/-- The topology of the configuration space, induced from `Real.Angle`. -/
instance instTopologicalSpace : TopologicalSpace ConfigurationSpace :=
  TopologicalSpace.induced angle inferInstance

/-- The identification with `Real.Angle` as a homeomorphism. -/
def angleHomeomorph : ConfigurationSpace ≃ₜ Real.Angle where
  toEquiv := angleEquiv
  continuous_toFun := continuous_induced_dom
  continuous_invFun := continuous_induced_rng.mpr continuous_id

/-- The point of the unit circle `e^{iθ}` corresponding to a configuration at angle `θ`. -/
def toCircle (q : ConfigurationSpace) : Circle := q.angle.toCircle

/-- The identification of the configuration space with the unit circle. -/
def circleHomeomorph : ConfigurationSpace ≃ₜ Circle :=
  angleHomeomorph.trans AddCircle.homeomorphCircle'

/-- The identification with the unit circle is given by `ConfigurationSpace.toCircle`. -/
lemma circleHomeomorph_apply (q : ConfigurationSpace) : circleHomeomorph q = q.toCircle := rfl

/-- The configuration space is Hausdorff, being homeomorphic to the unit circle. -/
instance instT2Space : T2Space ConfigurationSpace := circleHomeomorph.symm.t2Space

/-- The configuration space is compact, being homeomorphic to the unit circle. -/
instance instCompactSpace : CompactSpace ConfigurationSpace := circleHomeomorph.symm.compactSpace

/-- The configuration space is second countable, being homeomorphic to the unit circle. -/
instance instSecondCountableTopology : SecondCountableTopology ConfigurationSpace :=
  circleHomeomorph.secondCountableTopology

end ConfigurationSpace
end SimplePendulum
end ClassicalMechanics

end
