/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.TwoPortRedhefferRealization

/-!
# Behavior-derived Redheffer star product

## i. Overview

The singular-safe relational series behavior is functional whenever its named internal feedback
pivot is bijective. This file extracts the unique typed scattering transform from that relation
and identifies it with the previously proved four-block formula.

Scope:

`redhefferStar` is proof-gated and composes reflective scattering systems. It is not ordinary
matrix multiplication, a chain-matrix product, a reciprocity statement, or a convergence result.
The gate is sufficient for external functionality; no converse, minimality, associativity, or
identity theorem is asserted.
Agreement with the independent `FlatNetlist`/N5H elimination route has not yet been proved; that
is the open X-01 bridge.

## ii. Key results

- `TwoPortScatteringTransform.isFunctional_redhefferSeriesBehavior`: functionality from the
  explicit pivot gate.
- `TwoPortScatteringTransform.redhefferStar`: the behavior-derived scattering transform.
- `TwoPortScatteringTransform.toBehavior_redhefferStar`: exact relational reconstruction.
- `TwoPortScatteringTransform.redhefferStar_eq_blockFormula`: equality with the noncommutative
  block formula.

## iii. Table of contents

- A. Functional extraction
- B. Agreement with the block formula

## iv. References

This behavior-derived construction is Physlib-original; no external source is used here.

-/

@[expose] public section

namespace Optics

noncomputable section

universe u v w

namespace TwoPortScatteringTransform

variable {ι : Type u} {κ : Type v} {μ : Type w}

/-!

## A. Functional extraction

-/

/-- Bijectivity of the declared internal feedback block makes the external series behavior
functional. -/
lemma isFunctional_redhefferSeriesBehavior
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype μ] [DecidableEq μ]
    (first : TwoPortScatteringTransform ι κ)
    (second : TwoPortScatteringTransform κ μ)
    (hFeedback : first.HasBijectiveRedhefferFeedback second) :
    (first.redhefferSeriesBehavior second).IsFunctional := by
  rw [← first.toBehavior_redhefferBlockFormula second hFeedback]
  exact (first.redhefferBlockFormula second hFeedback).toBehavior_isFunctional

/-- The unique typed scattering transform extracted from relational series composition under the
explicit internal feedback-block gate. -/
noncomputable def redhefferStar
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype μ] [DecidableEq μ]
    (first : TwoPortScatteringTransform ι κ)
    (second : TwoPortScatteringTransform κ μ)
    (hFeedback : first.HasBijectiveRedhefferFeedback second) :
    TwoPortScatteringTransform ι μ :=
  (first.redhefferSeriesBehavior second).toModeTransform
    (first.isFunctional_redhefferSeriesBehavior second hFeedback)

/-- The behavior-derived star product reconstructs the entire singular-safe series behavior. -/
@[simp]
lemma toBehavior_redhefferStar
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype μ] [DecidableEq μ]
    (first : TwoPortScatteringTransform ι κ)
    (second : TwoPortScatteringTransform κ μ)
    (hFeedback : first.HasBijectiveRedhefferFeedback second) :
    (first.redhefferStar second hFeedback).toBehavior =
      first.redhefferSeriesBehavior second :=
  LinearBehavior.toBehavior_toModeTransform _ _

/-!

## B. Agreement with the block formula

-/

/-- The behavior-derived Redheffer star product equals the exact proof-gated four-block formula. -/
lemma redhefferStar_eq_blockFormula
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype μ] [DecidableEq μ]
    (first : TwoPortScatteringTransform ι κ)
    (second : TwoPortScatteringTransform κ μ)
    (hFeedback : first.HasBijectiveRedhefferFeedback second) :
    first.redhefferStar second hFeedback =
      first.redhefferBlockFormula second hFeedback :=
  LinearBehavior.toModeTransform_unique
    (first.redhefferSeriesBehavior second)
    (first.isFunctional_redhefferSeriesBehavior second hFeedback)
    (first.redhefferBlockFormula second hFeedback)
    (first.toBehavior_redhefferBlockFormula second hFeedback)

end TwoPortScatteringTransform

end


end Optics
