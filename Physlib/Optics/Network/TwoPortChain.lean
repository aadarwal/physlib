/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.TwoPortBehavior

/-!
# Chain transforms derived from two-port behaviors

## i. Overview

A backward-first two-port behavior is relational and need not define a map from its left state to
its right state. This file makes left-to-right functionality an explicit proof gate. Given that
proof and a finite left-mode family, `leftToRightChainTransform` extracts the unique matrix whose
graph is the behavior.

Relational series composition then yields ordinary matrix multiplication, with the later component
on the left.

## ii. Key results

- `BackwardFirstTwoPortBehavior.HasLeftToRightChainView`: the proof gate for a chain transform.
- `BackwardFirstTwoPortBehavior.leftToRightChainTransform`: the matrix derived from a functional
  behavior.
- `BackwardFirstTwoPortBehavior.toBehavior_leftToRightChainTransform`: graph reconstruction.
- `BackwardFirstTwoPortBehavior.leftToRightChainTransform_toBehavior`: transform round trip.
- `BackwardFirstTwoPortBehavior.leftToRightChainTransform_unique`: uniqueness of extraction.
- `BackwardFirstTwoPortBehavior.leftToRightChainTransform_series`: relational series becomes
  matrix cascade.

## iii. Table of contents

- A. Behavior-derived chain transforms
- B. Chain transforms under series composition

## iv. References

These are fixed-frequency complex-linear semantics. This file does not infer chain functionality
from a scattering matrix and introduces no block inverse. Such an inference requires an appropriate
transmission-block hypothesis.

Series composition identifies the complete middle state literally. Different labels, direction
orders, phase gauges, or reference planes require an explicit adapter behavior.

-/

@[expose] public section

namespace Optics

noncomputable section

universe u v w

/-- A left-to-right chain transform in backward-first reference-plane coordinates.

Its defining equation is `(aR, bR) = K (bL, aL)`: rows index the right state and columns index
the left state.
-/
abbrev BackwardFirstChainTransform (ι : Type u) (κ : Type v) :=
  ModeTransform (BackwardWave ι ⊕ ForwardWave ι) (BackwardWave κ ⊕ ForwardWave κ)

namespace BackwardFirstTwoPortBehavior

variable {ι : Type u} {κ : Type v} {μ : Type w}

/-!

## A. Behavior-derived chain transforms

-/

/-- A two-port behavior has a left-to-right chain view when every left state determines exactly one
right state. -/
abbrev HasLeftToRightChainView (behavior : BackwardFirstTwoPortBehavior ι κ) : Prop :=
  behavior.IsFunctional

/-- The left-to-right chain transform derived from a functional two-port behavior.

The proof requirement prevents a partial or multivalued two-port relation from being treated as a
matrix. Rows index the backward-first right state and columns index the backward-first left state.
In named scattering variables its defining equation is `(aR, bR) = K (bL, aL)`.
-/
noncomputable def leftToRightChainTransform [Fintype ι] [DecidableEq ι]
    (behavior : BackwardFirstTwoPortBehavior ι κ)
    (hChain : behavior.HasLeftToRightChainView) : BackwardFirstChainTransform ι κ :=
  behavior.toModeTransform hChain

/-- The derived chain transform induces the linear map extracted from the behavior. -/
@[simp]
lemma toLinearMap_leftToRightChainTransform [Fintype ι] [DecidableEq ι]
    (behavior : BackwardFirstTwoPortBehavior ι κ)
    (hChain : behavior.HasLeftToRightChainView) :
    (behavior.leftToRightChainTransform hChain).toLinearMap =
      behavior.toLinearMap hChain :=
  behavior.toLinearMap_toModeTransform hChain

/-- A pair satisfies a functional two-port behavior exactly when the derived chain transform maps
its left state to its right state. -/
lemma mem_iff_eq_leftToRightChainTransform [Fintype ι] [DecidableEq ι]
    (behavior : BackwardFirstTwoPortBehavior ι κ)
    (hChain : behavior.HasLeftToRightChainView)
    (left : BackwardFirstTravellingWaveState ι)
    (right : BackwardFirstTravellingWaveState κ) :
    (left, right) ∈ behavior ↔
      right = (behavior.leftToRightChainTransform hChain).toLinearMap left :=
  behavior.mem_iff_eq_toModeTransform hChain left right

/-- The graph of the derived chain transform recovers the entire functional two-port behavior. -/
@[simp]
lemma toBehavior_leftToRightChainTransform [Fintype ι] [DecidableEq ι]
    (behavior : BackwardFirstTwoPortBehavior ι κ)
    (hChain : behavior.HasLeftToRightChainView) :
    (behavior.leftToRightChainTransform hChain).toBehavior = behavior :=
  behavior.toBehavior_toModeTransform hChain

/-- The derived chain transform is the unique mode transform whose graph is the functional
two-port behavior. -/
lemma leftToRightChainTransform_unique [Fintype ι] [DecidableEq ι]
    (behavior : BackwardFirstTwoPortBehavior ι κ)
    (hChain : behavior.HasLeftToRightChainView)
    (transform : BackwardFirstChainTransform ι κ)
    (hTransform : transform.toBehavior = behavior) :
    behavior.leftToRightChainTransform hChain = transform :=
  behavior.toModeTransform_unique hChain transform hTransform

/-- Extracting the chain transform from a transform's graph recovers that transform. -/
@[simp]
lemma leftToRightChainTransform_toBehavior [Fintype ι] [DecidableEq ι]
    (transform : BackwardFirstChainTransform ι κ) :
    leftToRightChainTransform transform.toBehavior transform.toBehavior_isFunctional = transform :=
  LinearBehavior.toModeTransform_toBehavior transform

/-!

## B. Chain transforms under series composition

-/

/-- A series composition of left-to-right chain views has the product chain transform, with the
later component on the left.

Relational series identifies the complete middle state literally. Different middle labels,
direction order, phase gauge, or reference plane require an explicit adapter behavior first.
-/
lemma leftToRightChainTransform_series [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (first : BackwardFirstTwoPortBehavior ι κ)
    (second : BackwardFirstTwoPortBehavior κ μ)
    (hFirst : first.HasLeftToRightChainView)
    (hSecond : second.HasLeftToRightChainView) :
    leftToRightChainTransform (first.series second) (hFirst.series hSecond) =
      second.leftToRightChainTransform hSecond * first.leftToRightChainTransform hFirst :=
  LinearBehavior.toModeTransform_series first second hFirst hSecond

end BackwardFirstTwoPortBehavior

end

end Optics
