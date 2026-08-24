/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Mode.Basic

/-!
# Implicit linear optical behaviors

## i. Overview

An optical component can impose a linear relation between input and output amplitudes without
making either side a function of the other. This file represents such a behavior as a
complex submodule of paired mode-amplitude spaces. Ordinary linear maps and finite mode transforms
embed as graph behaviors.

Series composition uses an existential intermediate amplitude to identify the first behavior's
output with the second behavior's input. Parallel composition places two independent behaviors on
disjoint sum-indexed mode families. For behaviors constructed as graphs, the graph theorems prove
that these relational operations recover ordinary linear-map composition and block-diagonal
mode-transform composition.

## ii. Scope

The behavior type and its relational compositions require no finite index types, matrix inverse,
or unique-solvability hypothesis. They are fixed-frequency complex-linear semantics only: no
causality, delay, source, termination, passivity, electromagnetic normalization, or physical
realization is included. Parallel composition does not duplicate or sum an amplitude, and it does
not reuse one amplitude as more than one input.

## iii. Key definitions and results

- `LinearBehavior`: a complex submodule of paired input and output mode amplitudes.
- `LinearBehavior.ofLinearMap`: the graph behavior of a complex-linear map.
- `ModeTransform.toBehavior`: the graph behavior induced by a finite mode transform.
- `LinearBehavior.identity`: equality between input and output amplitudes.
- `LinearBehavior.series`: relational series composition.
- `LinearBehavior.parallel`: independent behavior on disjoint mode families.
- `ModeTransform.toBehavior_mul`: matrix cascade agrees with relational series composition.
- `ModeTransform.toBehavior_directSum`: block-diagonal action agrees with relational parallel
  composition.

## iv. Table of contents

- A. Behaviors and functional graphs
- B. Identity and series composition
- C. Parallel composition

-/

@[expose] public section

namespace Optics

noncomputable section

universe u v w x

/-!

## A. Behaviors and functional graphs

-/

/-- A complex-linear relation between input and output optical mode amplitudes.

Membership of `(input, output)` means that the paired amplitudes satisfy the component behavior.
-/
abbrev LinearBehavior (ι : Type u) (κ : Type v) :=
  Submodule ℂ (ModeAmplitude ι × ModeAmplitude κ)

namespace LinearBehavior

variable {ι : Type u} {κ : Type v} {μ : Type w} {ν : Type x}

/-- The behavior consisting of the graph of a complex-linear map. -/
def ofLinearMap (map : ModeAmplitude ι →ₗ[ℂ] ModeAmplitude κ) : LinearBehavior ι κ :=
  map.graph

/-- A pair is in a linear-map behavior exactly when its output is the map applied to its
input. -/
@[simp]
lemma mem_ofLinearMap_iff (map : ModeAmplitude ι →ₗ[ℂ] ModeAmplitude κ)
    (input : ModeAmplitude ι) (output : ModeAmplitude κ) :
    (input, output) ∈ ofLinearMap map ↔ output = map input := Iff.rfl

/-- Distinct complex-linear maps have distinct graph constructions. -/
lemma ofLinearMap_injective :
    Function.Injective
      (ofLinearMap : (ModeAmplitude ι →ₗ[ℂ] ModeAmplitude κ) → LinearBehavior ι κ) := by
  intro first second hBehavior
  apply LinearMap.ext
  intro input
  have hMember : (input, first input) ∈ ofLinearMap second := by
    rw [← hBehavior]
    simp
  exact (mem_ofLinearMap_iff second input (first input)).mp hMember

end LinearBehavior

namespace ModeTransform

variable {ι : Type u} {κ : Type v} {μ : Type w}

/-- The graph behavior induced by a mode transform with a finite input family. -/
def toBehavior [Fintype ι] (transform : ModeTransform ι κ) : LinearBehavior ι κ := by
  classical
  exact LinearBehavior.ofLinearMap transform.toLinearMap

/-- A pair is in a mode-transform behavior exactly when its output is the matrix action on
its input. -/
@[simp]
lemma mem_toBehavior_iff [Fintype ι]
    (transform : ModeTransform ι κ) (input : ModeAmplitude ι) (output : ModeAmplitude κ) :
    (input, output) ∈ transform.toBehavior ↔
      output = WithLp.toLp 2 (Matrix.mulVec transform (WithLp.ofLp input)) := by
  classical
  rfl

/-- With a chosen decidable input indexing, transform-behavior membership is exactly application
of the transform's bundled complex-linear map. -/
lemma mem_toBehavior_iff_toLinearMap [Fintype ι] [DecidableEq ι]
    (transform : ModeTransform ι κ) (input : ModeAmplitude ι) (output : ModeAmplitude κ) :
    (input, output) ∈ transform.toBehavior ↔ output = transform.toLinearMap input := by
  rw [mem_toBehavior_iff]
  rfl

/-- Distinct mode transforms on a finite input family have distinct graph constructions. -/
lemma toBehavior_injective [Fintype ι] :
    Function.Injective (toBehavior : ModeTransform ι κ → LinearBehavior ι κ) := by
  classical
  intro first second hBehavior
  apply Matrix.toEuclideanLin.injective
  exact LinearBehavior.ofLinearMap_injective (by simpa only [toBehavior] using hBehavior)

end ModeTransform

namespace LinearBehavior

variable {ι : Type u} {κ : Type v} {μ : Type w} {ν : Type x}

/-!

## B. Identity and series composition

-/

/-- The identity behavior, relating an amplitude only to itself. -/
def identity : LinearBehavior ι ι :=
  ofLinearMap LinearMap.id

/-- An input and output satisfy the identity behavior exactly when they are equal. -/
@[simp]
lemma mem_identity_iff (input output : ModeAmplitude ι) :
    (input, output) ∈ (identity : LinearBehavior ι ι) ↔ output = input := by
  simp [identity]

/-- Relational series composition, with an existential intermediate amplitude hidden.

`first.series second` means that `first` acts before `second`.
-/
def series (first : LinearBehavior ι κ) (second : LinearBehavior κ μ) :
    LinearBehavior ι μ where
  carrier := { pair | ∃ middle, (pair.1, middle) ∈ first ∧ (middle, pair.2) ∈ second }
  zero_mem' := ⟨0, first.zero_mem, second.zero_mem⟩
  add_mem' := by
    rintro ⟨input₁, output₁⟩ ⟨input₂, output₂⟩
      ⟨middle₁, hFirst₁, hSecond₁⟩ ⟨middle₂, hFirst₂, hSecond₂⟩
    exact ⟨middle₁ + middle₂, first.add_mem hFirst₁ hFirst₂,
      second.add_mem hSecond₁ hSecond₂⟩
  smul_mem' scalar := by
    rintro ⟨input, output⟩ ⟨middle, hFirst, hSecond⟩
    exact ⟨scalar • middle, first.smul_mem scalar hFirst, second.smul_mem scalar hSecond⟩

/-- A pair satisfies a series composition exactly when some intermediate amplitude satisfies both
component behaviors. -/
@[simp]
lemma mem_series_iff (first : LinearBehavior ι κ) (second : LinearBehavior κ μ)
    (input : ModeAmplitude ι) (output : ModeAmplitude μ) :
    (input, output) ∈ first.series second ↔
      ∃ middle, (input, middle) ∈ first ∧ (middle, output) ∈ second := Iff.rfl

/-- The identity behavior is a left identity for series composition. -/
@[simp]
lemma identity_series (behavior : LinearBehavior ι κ) :
    (identity : LinearBehavior ι ι).series behavior = behavior := by
  ext ⟨input, output⟩
  constructor
  · rintro ⟨middle, hIdentity, hBehavior⟩
    rw [mem_identity_iff] at hIdentity
    subst middle
    exact hBehavior
  · intro hBehavior
    exact ⟨input, by simp, hBehavior⟩

/-- The identity behavior is a right identity for series composition. -/
@[simp]
lemma series_identity (behavior : LinearBehavior ι κ) :
    behavior.series (identity : LinearBehavior κ κ) = behavior := by
  ext ⟨input, output⟩
  constructor
  · rintro ⟨middle, hBehavior, hIdentity⟩
    rw [mem_identity_iff] at hIdentity
    change output = middle at hIdentity
    change (input, middle) ∈ behavior at hBehavior
    rw [hIdentity]
    exact hBehavior
  · intro hBehavior
    exact ⟨output, hBehavior, by simp⟩

/-- Relational series composition is associative. -/
lemma series_assoc (first : LinearBehavior ι κ) (second : LinearBehavior κ μ)
    (third : LinearBehavior μ ν) :
    (first.series second).series third = first.series (second.series third) := by
  ext ⟨input, output⟩
  constructor
  · rintro ⟨later, ⟨earlier, hFirst, hSecond⟩, hThird⟩
    exact ⟨earlier, hFirst, later, hSecond, hThird⟩
  · rintro ⟨earlier, hFirst, later, hSecond, hThird⟩
    exact ⟨later, ⟨earlier, hFirst, hSecond⟩, hThird⟩

/-- Series composition of graph behaviors is the graph of linear-map composition. -/
lemma ofLinearMap_series (first : ModeAmplitude ι →ₗ[ℂ] ModeAmplitude κ)
    (second : ModeAmplitude κ →ₗ[ℂ] ModeAmplitude μ) :
    (ofLinearMap first).series (ofLinearMap second) =
      ofLinearMap (second.comp first) := by
  ext ⟨input, output⟩
  simp

end LinearBehavior

namespace ModeTransform

variable {ι : Type u} {κ : Type v} {μ : Type w}

/-- The identity mode transform induces the identity behavior. -/
@[simp]
lemma toBehavior_one [Fintype ι] [DecidableEq ι] :
    ModeTransform.toBehavior (1 : ModeTransform ι ι) =
      (LinearBehavior.identity : LinearBehavior ι ι) := by
  ext ⟨input, output⟩
  rw [mem_toBehavior_iff, LinearBehavior.mem_identity_iff]
  simp

/-- Relational series composition of mode-transform graphs agrees with matrix cascade order. -/
lemma toBehavior_mul [Fintype ι] [Fintype κ]
    (first : ModeTransform ι κ) (second : ModeTransform κ μ) :
    first.toBehavior.series second.toBehavior =
      ModeTransform.toBehavior (second * first) := by
  classical
  simpa only [toBehavior, ModeTransform.toLinearMap, Matrix.toLpLin_mul_same] using
    LinearBehavior.ofLinearMap_series first.toLinearMap second.toLinearMap

end ModeTransform

namespace LinearBehavior

variable {ι : Type u} {κ : Type v} {μ : Type w} {ν : Type x}

/-!

## C. Parallel composition

-/

/-- Parallel composition of two independent behaviors on disjoint mode families.

The left behavior acts on the left input and output branches, while the right behavior acts on the
right branches. No amplitude is duplicated or identified between the two behaviors.
-/
def parallel (left : LinearBehavior ι κ) (right : LinearBehavior μ ν) :
    LinearBehavior (ι ⊕ μ) (κ ⊕ ν) where
  carrier := { pair |
    (pair.1.restrictInl, pair.2.restrictInl) ∈ left ∧
      (pair.1.restrictInr, pair.2.restrictInr) ∈ right }
  zero_mem' := by
    constructor
    · change ((ModeAmplitude.restrictInlLinearMap :
          ModeAmplitude (ι ⊕ μ) →ₗ[ℂ] ModeAmplitude ι) 0,
        (ModeAmplitude.restrictInlLinearMap :
          ModeAmplitude (κ ⊕ ν) →ₗ[ℂ] ModeAmplitude κ) 0) ∈ left
      rw [map_zero, map_zero]
      exact left.zero_mem
    · change ((ModeAmplitude.restrictInrLinearMap :
          ModeAmplitude (ι ⊕ μ) →ₗ[ℂ] ModeAmplitude μ) 0,
        (ModeAmplitude.restrictInrLinearMap :
          ModeAmplitude (κ ⊕ ν) →ₗ[ℂ] ModeAmplitude ν) 0) ∈ right
      rw [map_zero, map_zero]
      exact right.zero_mem
  add_mem' := by
    rintro ⟨input₁, output₁⟩ ⟨input₂, output₂⟩
      ⟨hLeft₁, hRight₁⟩ ⟨hLeft₂, hRight₂⟩
    constructor
    · change ((ModeAmplitude.restrictInlLinearMap :
          ModeAmplitude (ι ⊕ μ) →ₗ[ℂ] ModeAmplitude ι) (input₁ + input₂),
        (ModeAmplitude.restrictInlLinearMap :
          ModeAmplitude (κ ⊕ ν) →ₗ[ℂ] ModeAmplitude κ) (output₁ + output₂)) ∈ left
      rw [map_add, map_add]
      exact left.add_mem hLeft₁ hLeft₂
    · change ((ModeAmplitude.restrictInrLinearMap :
          ModeAmplitude (ι ⊕ μ) →ₗ[ℂ] ModeAmplitude μ) (input₁ + input₂),
        (ModeAmplitude.restrictInrLinearMap :
          ModeAmplitude (κ ⊕ ν) →ₗ[ℂ] ModeAmplitude ν) (output₁ + output₂)) ∈ right
      rw [map_add, map_add]
      exact right.add_mem hRight₁ hRight₂
  smul_mem' scalar := by
    rintro ⟨input, output⟩ ⟨hLeft, hRight⟩
    constructor
    · change ((ModeAmplitude.restrictInlLinearMap :
          ModeAmplitude (ι ⊕ μ) →ₗ[ℂ] ModeAmplitude ι) (scalar • input),
        (ModeAmplitude.restrictInlLinearMap :
          ModeAmplitude (κ ⊕ ν) →ₗ[ℂ] ModeAmplitude κ) (scalar • output)) ∈ left
      rw [map_smul, map_smul]
      exact left.smul_mem scalar hLeft
    · change ((ModeAmplitude.restrictInrLinearMap :
          ModeAmplitude (ι ⊕ μ) →ₗ[ℂ] ModeAmplitude μ) (scalar • input),
        (ModeAmplitude.restrictInrLinearMap :
          ModeAmplitude (κ ⊕ ν) →ₗ[ℂ] ModeAmplitude ν) (scalar • output)) ∈ right
      rw [map_smul, map_smul]
      exact right.smul_mem scalar hRight

/-- A pair satisfies a parallel composition exactly when its left and right coordinate restriction
satisfy the corresponding component behaviors. -/
@[simp]
lemma mem_parallel_iff (left : LinearBehavior ι κ) (right : LinearBehavior μ ν)
    (input : ModeAmplitude (ι ⊕ μ)) (output : ModeAmplitude (κ ⊕ ν)) :
    (input, output) ∈ left.parallel right ↔
      (input.restrictInl, output.restrictInl) ∈ left ∧
        (input.restrictInr, output.restrictInr) ∈ right := Iff.rfl

end LinearBehavior

namespace ModeTransform

variable {ι : Type u} {κ : Type v} {μ : Type w} {ν : Type x}

/-- Relational parallel composition of transform graphs agrees with block-diagonal direct sum. -/
lemma toBehavior_directSum [Fintype ι] [Fintype μ]
    (left : ModeTransform ι κ) (right : ModeTransform μ ν) :
    left.toBehavior.parallel right.toBehavior = (left.directSum right).toBehavior := by
  classical
  ext ⟨input, output⟩
  constructor
  · rintro ⟨hLeft, hRight⟩
    change output.restrictInl = left.toLinearMap input.restrictInl at hLeft
    change output.restrictInr = right.toLinearMap input.restrictInr at hRight
    change output = (left.directSum right).toLinearMap input
    calc
      output = output.restrictInl.directSum output.restrictInr :=
        (ModeAmplitude.directSum_restrict output).symm
      _ = (left.toLinearMap input.restrictInl).directSum
          (right.toLinearMap input.restrictInr) := congrArg₂ ModeAmplitude.directSum hLeft hRight
      _ = (left.directSum right).toLinearMap
          (input.restrictInl.directSum input.restrictInr) :=
        (ModeTransform.directSum_apply left right input.restrictInl input.restrictInr).symm
      _ = (left.directSum right).toLinearMap input := by
        rw [ModeAmplitude.directSum_restrict]
  · intro hTransform
    change output = (left.directSum right).toLinearMap input at hTransform
    have hAction :
        (left.directSum right).toLinearMap input =
          (left.toLinearMap input.restrictInl).directSum
            (right.toLinearMap input.restrictInr) := by
      simpa only [ModeAmplitude.directSum_restrict] using
        ModeTransform.directSum_apply left right input.restrictInl input.restrictInr
    constructor
    · change output.restrictInl = left.toLinearMap input.restrictInl
      exact congrArg ModeAmplitude.restrictInl (hTransform.trans hAction)
    · change output.restrictInr = right.toLinearMap input.restrictInr
      exact congrArg ModeAmplitude.restrictInr (hTransform.trans hAction)

end ModeTransform

end

end Optics
