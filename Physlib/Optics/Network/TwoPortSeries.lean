/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.TwoPortScatteringChain

/-!
# Singular-safe series composition of two-port scattering behaviors

## i. Overview

Two scattering devices in series share one complete backward-first travelling-wave state. This
file defines their external scattering behavior by relationally composing the two backward-first
behaviors and then returning to scattering coordinates. No inverse is used: the relation remains
meaningful when the internal feedback equations have no solution or several solutions.

Scope:

The middle mode family is identified literally. A relabeling, phase-gauge change, or reference-
plane adapter must be supplied before composition when the two middle boundaries use different
coordinates. The travelling-wave ordering is the convention registered by
`TwoPortScatteringChain`. This file does not assert functionality, passivity, losslessness,
reciprocity, causality, associativity, an identity law, or a physical device realization.
Agreement with the independent
`FlatNetlist`/N5H composition route has not yet been proved; that is the open X-01 bridge.

## ii. Key results

- `TwoPortScatteringBehavior.redhefferSeries`: singular-safe external series behavior.
- `TwoPortScatteringTransform.redhefferSeriesBehavior`: the series behavior of two transform
  graphs.
- `TwoPortScatteringTransform.mem_toBackwardFirst_redhefferSeriesBehavior_iff`: the four exact
  component equations with an existential internal state.

## iii. Table of contents

- A. Relational two-port series composition
- B. Transform graphs and the internal equations

## iv. References

This singular-safe composition API is Physlib-original; no external source is used here.

-/

@[expose] public section

namespace Optics

noncomputable section

universe u v w

/-!

## A. Relational two-port series composition

-/

namespace TwoPortScatteringBehavior

variable {ι : Type u} {κ : Type v} {μ : Type w}

/-- The singular-safe external behavior of two scattering relations connected in series.

The complete right state of `first` is identified with the complete left state of `second` in
backward-first coordinates. This is the relational foundation of the Redheffer product.
-/
def redhefferSeries (first : TwoPortScatteringBehavior ι κ)
    (second : TwoPortScatteringBehavior κ μ) : TwoPortScatteringBehavior ι μ :=
  BackwardFirstTwoPortBehavior.toScattering
    (LinearBehavior.series
      (TwoPortScatteringBehavior.toBackwardFirst first)
      (TwoPortScatteringBehavior.toBackwardFirst second))

/-- Returning a relational series composition to backward-first coordinates exposes ordinary
relational series composition. -/
@[simp]
lemma toBackwardFirst_redhefferSeries (first : TwoPortScatteringBehavior ι κ)
    (second : TwoPortScatteringBehavior κ μ) :
    TwoPortScatteringBehavior.toBackwardFirst (redhefferSeries first second) =
      LinearBehavior.series
        (TwoPortScatteringBehavior.toBackwardFirst first)
        (TwoPortScatteringBehavior.toBackwardFirst second) := by
  unfold redhefferSeries
  rw [BackwardFirstTwoPortBehavior.toBackwardFirst_toScattering]

/-- Relational series membership means that one complete middle travelling-wave state satisfies
both component behaviors. -/
lemma mem_toBackwardFirst_redhefferSeries_iff
    (first : TwoPortScatteringBehavior ι κ)
    (second : TwoPortScatteringBehavior κ μ)
    (left : BackwardFirstTravellingWaveState ι)
    (right : BackwardFirstTravellingWaveState μ) :
    (left, right) ∈
        TwoPortScatteringBehavior.toBackwardFirst (redhefferSeries first second) ↔
      ∃ middle : BackwardFirstTravellingWaveState κ,
        (left, middle) ∈ TwoPortScatteringBehavior.toBackwardFirst first ∧
          (middle, right) ∈ TwoPortScatteringBehavior.toBackwardFirst second := by
  rw [toBackwardFirst_redhefferSeries, LinearBehavior.mem_series_iff]

end TwoPortScatteringBehavior

/-!

## B. Transform graphs and the internal equations

-/

namespace TwoPortScatteringTransform

variable {ι : Type u} {κ : Type v} {μ : Type w}

/-- The singular-safe series behavior of two typed scattering transforms.

The definition uses only their independently meaningful graph behaviors. It does not assume that
the connected external relation is functional.
-/
def redhefferSeriesBehavior [Fintype ι] [Fintype κ] [Fintype μ]
    (first : TwoPortScatteringTransform ι κ)
    (second : TwoPortScatteringTransform κ μ) : TwoPortScatteringBehavior ι μ :=
  TwoPortScatteringBehavior.redhefferSeries
    (first.toBehavior : TwoPortScatteringBehavior ι κ)
    (second.toBehavior : TwoPortScatteringBehavior κ μ)

/-- In backward-first coordinates, transform-level series behavior is exactly the relational
series of the two regrouped transform graphs. -/
@[simp]
lemma toBackwardFirst_redhefferSeriesBehavior [Fintype ι] [Fintype κ] [Fintype μ]
    (first : TwoPortScatteringTransform ι κ)
    (second : TwoPortScatteringTransform κ μ) :
    TwoPortScatteringBehavior.toBackwardFirst
        (first.redhefferSeriesBehavior second) =
      first.toBackwardFirstBehavior.series second.toBackwardFirstBehavior := by
  rw [redhefferSeriesBehavior, TwoPortScatteringBehavior.toBackwardFirst_redhefferSeries]
  rfl

/-- Membership in the singular-safe series behavior is exactly the four component scattering
equations for one existential internal backward/forward state. -/
lemma mem_toBackwardFirst_redhefferSeriesBehavior_iff
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype μ] [DecidableEq μ]
    (first : TwoPortScatteringTransform ι κ)
    (second : TwoPortScatteringTransform κ μ)
    (left : BackwardFirstTravellingWaveState ι)
    (right : BackwardFirstTravellingWaveState μ) :
    (left, right) ∈ TwoPortScatteringBehavior.toBackwardFirst
        (first.redhefferSeriesBehavior second) ↔
      ∃ middle : BackwardFirstTravellingWaveState κ,
        (left.restrictInl =
            first.leftReflection.toLinearMap left.restrictInr +
              first.rightToLeftTransmission.toLinearMap middle.restrictInl ∧
          middle.restrictInr =
            first.leftToRightTransmission.toLinearMap left.restrictInr +
              first.rightReflection.toLinearMap middle.restrictInl) ∧
        (middle.restrictInl =
            second.leftReflection.toLinearMap middle.restrictInr +
              second.rightToLeftTransmission.toLinearMap right.restrictInl ∧
          right.restrictInr =
            second.leftToRightTransmission.toLinearMap middle.restrictInr +
              second.rightReflection.toLinearMap right.restrictInl) := by
  rw [toBackwardFirst_redhefferSeriesBehavior, LinearBehavior.mem_series_iff]
  constructor
  · rintro ⟨middle, hFirst, hSecond⟩
    exact ⟨middle,
      (first.mem_toBackwardFirstBehavior_iff_blockEquations left middle).mp hFirst,
      (second.mem_toBackwardFirstBehavior_iff_blockEquations middle right).mp hSecond⟩
  · rintro ⟨middle, hFirst, hSecond⟩
    exact ⟨middle,
      (first.mem_toBackwardFirstBehavior_iff_blockEquations left middle).mpr hFirst,
      (second.mem_toBackwardFirstBehavior_iff_blockEquations middle right).mpr hSecond⟩

end TwoPortScatteringTransform

end


end Optics
