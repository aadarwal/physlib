/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.SpaceAndTime.Space.Integrals.ThinCellLimit
public import Physlib.SpaceAndTime.Space.OrientedAffineHyperplaneCrossProduct
public import Physlib.SpaceAndTime.Space.OrientedAffineHyperplaneTrace
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Planar thin-loop and pillbox averages

## i. Overview

This file gives explicit shrinking planar cell geometry and the normalized principal averages used
by thin-loop and pillbox arguments. A side sample is genuinely a point of the selected open
half-space. A boundary sample remains in the carrier. Long-edge averages pair a side field with a
chosen tangent direction. Face averages use that tangent and its oriented quarter-turn
`normalVector cross tangent`; their physical area Jacobian cancels in the normalized average.

The file does not state Stokes, divergence, or Maxwell laws. It also does not prove that the
averages converge to one-sided traces: that requires uniform thin-cell control stronger than a
pointwise trace and is therefore an explicit hypothesis in the electromagnetic consumer.

## ii. Key results

- `OrientedAffineHyperplane.tangentPoint`: a carrier point displaced tangentially.
- `OrientedAffineHyperplane.sidePoint`: a positive-distance sample in one open half-space.
- `OrientedAffineHyperplane.quarterTurnTangent`: the oriented in-plane quarter-turn.
- `PlanarThinLoopFamily.sideLongEdgeAverage`: an actual normalized long-edge integral.
- `PlanarPillboxFamily.sideFaceAverage`: an actual normalized principal-face integral.

## iii. Table of contents

- A. Normalized interval and square averages
- B. Planar sample geometry
- C. Thin-loop families
- D. Pillbox families

## iv. References

This is neutral geometry and integration infrastructure for the E4b Maxwell boundary derivation.
-/

@[expose] public section

open Filter
open Matrix
open scoped Interval

namespace Space

noncomputable section

/-! ## A. Normalized interval and square averages -/

/-- The interval integral over `[-radius, radius]`, divided by its signed length `2 * radius`.

The definition is total at `radius = 0`; thin-cell families separately require positive radii. -/
def normalizedIntervalAverage (radius : ℝ) (f : ℝ → ℝ) : ℝ :=
  (2 * radius)⁻¹ * ∫ u in -radius..radius, f u

/-- The iterated normalized square average over `[-radius, radius]²`. -/
def normalizedSquareAverage (radius : ℝ) (f : ℝ → ℝ → ℝ) : ℝ :=
  normalizedIntervalAverage radius fun u ↦ normalizedIntervalAverage radius (f u)

namespace OrientedAffineHyperplane

/-! ## B. Planar sample geometry -/

/-- A carrier point displaced by a bundled tangent vector remains in the carrier. -/
def tangentPoint {d : ℕ} (plane : OrientedAffineHyperplane d) (x : plane.carrier)
    (offset : plane.tangentSubmodule) : plane.carrier :=
  ⟨(offset : EuclideanSpace ℝ (Fin d)) +ᵥ (x : Space d), by
    rw [plane.mem_carrier, plane.signedNormalCoordinate_vadd,
      (plane.mem_carrier (x : Space d)).mp x.property, add_zero]
    exact (plane.mem_tangentSubmodule offset).mp offset.property⟩

/-- A tangentially displaced carrier point, moved a positive distance into one selected side. -/
def sidePoint {d : ℕ} (plane : OrientedAffineHyperplane d) (side : Side)
    (x : plane.carrier) (offset : plane.tangentSubmodule) (height : ℝ)
    (hHeight : 0 < height) : plane.openHalfSpace side :=
  ⟨((offset : EuclideanSpace ℝ (Fin d)) + height • plane.sideNormalVector side) +ᵥ
      (x : Space d), by
    change 0 < side.sign * plane.signedNormalCoordinate
      (((offset : EuclideanSpace ℝ (Fin d)) + height • plane.sideNormalVector side) +ᵥ
        (x : Space d))
    rw [plane.signedNormalCoordinate_vadd,
      (plane.mem_carrier (x : Space d)).mp x.property, add_zero,
      normalComponent, inner_add_right, inner_smul_right]
    have hOffset : inner ℝ plane.normalVector
        (offset : EuclideanSpace ℝ (Fin d)) = 0 :=
      (plane.mem_tangentSubmodule offset).mp offset.property
    rw [hOffset, zero_add]
    change 0 < side.sign * (height * plane.normalComponent (plane.sideNormalVector side))
    rw [plane.normalComponent_sideNormalVector]
    nlinarith [side.sign_sq]⟩

/-- The oriented in-plane quarter-turn of a bundled tangent vector. -/
def quarterTurnTangent (plane : OrientedAffineHyperplane 3)
    (tangent : plane.tangentSubmodule) : plane.tangentSubmodule :=
  ⟨plane.normalVector ⨯ₑ₃ (tangent : EuclideanSpace ℝ (Fin 3)), by
    change plane.normalComponent
      (plane.normalVector ⨯ₑ₃ (tangent : EuclideanSpace ℝ (Fin 3))) = 0
    exact Space.inner_self_cross plane.normalVector tangent⟩

end OrientedAffineHyperplane

/-! ## C. Thin-loop families -/

/-- A sequence of planar thin loops shrinking to one carrier point along a fixed tangent
direction. -/
structure PlanarThinLoopFamily (plane : OrientedAffineHyperplane 3)
    (tangent : plane.tangentSubmodule) where
  /-- Half-length of the two principal tangent edges. -/
  radius : ℕ → ℝ
  /-- Distance of each principal edge from the carrier. -/
  halfThickness : ℕ → ℝ
  /-- Every principal half-length is positive. -/
  radius_pos : ∀ scale, 0 < radius scale
  /-- Every half-thickness is positive. -/
  halfThickness_pos : ∀ scale, 0 < halfThickness scale
  /-- The principal half-length shrinks to zero. -/
  radius_tendsto_zero : Tendsto radius atTop (nhds 0)
  /-- The half-thickness shrinks to zero. -/
  halfThickness_tendsto_zero : Tendsto halfThickness atTop (nhds 0)

namespace PlanarThinLoopFamily

/-- The normalized principal-edge integral of a selected-side vector field, oriented along the
stored tangent direction. -/
def sideLongEdgeAverage {plane : OrientedAffineHyperplane 3}
    {tangent : plane.tangentSubmodule} (loop : PlanarThinLoopFamily plane tangent)
    (side : OrientedAffineHyperplane.Side)
    {P : Type*} (field : plane.SideField side P (EuclideanSpace ℝ (Fin 3)))
    (parameter : P) (x : plane.carrier) (scale : ℕ) : ℝ :=
  normalizedIntervalAverage (loop.radius scale) fun u ↦
    inner ℝ
      (field parameter
        (plane.sidePoint side x (u • tangent) (loop.halfThickness scale)
          (loop.halfThickness_pos scale)))
      (tangent : EuclideanSpace ℝ (Fin 3))

/-- The normalized boundary-line integral of a tangent vector source against the oriented
spanning-surface normal `normalVector cross tangent`. -/
def surfaceLineAverage {plane : OrientedAffineHyperplane 3}
    {tangent : plane.tangentSubmodule} (loop : PlanarThinLoopFamily plane tangent)
    {P : Type*} (source : plane.BoundaryField P plane.tangentSubmodule)
    (parameter : P) (x : plane.carrier) (scale : ℕ) : ℝ :=
  normalizedIntervalAverage (loop.radius scale) fun u ↦
    inner ℝ
      (source parameter (plane.tangentPoint x (u • tangent)) :
        EuclideanSpace ℝ (Fin 3))
      (plane.normalVector ⨯ₑ₃ (tangent : EuclideanSpace ℝ (Fin 3)))

end PlanarThinLoopFamily

/-! ## D. Pillbox families -/

/-- A sequence of planar pillboxes shrinking to one carrier point. The stored unit tangent and its
oriented quarter-turn parameterize the principal faces. -/
structure PlanarPillboxFamily (plane : OrientedAffineHyperplane 3) where
  /-- A selected unit tangent direction used to parameterize both principal faces. -/
  tangent : plane.tangentSubmodule
  /-- The selected tangent has unit norm. -/
  tangent_norm : ‖(tangent : EuclideanSpace ℝ (Fin 3))‖ = 1
  /-- Half-width of each principal square face. -/
  radius : ℕ → ℝ
  /-- Distance of each principal face from the carrier. -/
  halfThickness : ℕ → ℝ
  /-- Every face half-width is positive. -/
  radius_pos : ∀ scale, 0 < radius scale
  /-- Every half-thickness is positive. -/
  halfThickness_pos : ∀ scale, 0 < halfThickness scale
  /-- The face half-width shrinks to zero. -/
  radius_tendsto_zero : Tendsto radius atTop (nhds 0)
  /-- The half-thickness shrinks to zero. -/
  halfThickness_tendsto_zero : Tendsto halfThickness atTop (nhds 0)

namespace PlanarPillboxFamily

/-- The normalized principal-face flux average of a selected-side vector field against the stored
negative-to-positive normal. -/
def sideFaceAverage {plane : OrientedAffineHyperplane 3}
    (pillbox : PlanarPillboxFamily plane)
    (side : OrientedAffineHyperplane.Side)
    {P : Type*} (field : plane.SideField side P (EuclideanSpace ℝ (Fin 3)))
    (parameter : P) (x : plane.carrier) (scale : ℕ) : ℝ :=
  normalizedSquareAverage (pillbox.radius scale) fun u v ↦
    inner ℝ plane.normalVector
      (field parameter
        (plane.sidePoint side x
          (u • pillbox.tangent + v • plane.quarterTurnTangent pillbox.tangent)
          (pillbox.halfThickness scale) (pillbox.halfThickness_pos scale)))

/-- The normalized boundary-face average of a scalar surface source. -/
def surfaceFaceAverage {plane : OrientedAffineHyperplane 3}
    (pillbox : PlanarPillboxFamily plane)
    {P : Type*} (source : plane.BoundaryField P ℝ)
    (parameter : P) (x : plane.carrier) (scale : ℕ) : ℝ :=
  normalizedSquareAverage (pillbox.radius scale) fun u v ↦
    source parameter
      (plane.tangentPoint x
        (u • pillbox.tangent + v • plane.quarterTurnTangent pillbox.tangent))

end PlanarPillboxFamily

end
end Space
