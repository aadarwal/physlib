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

A behavior is functional when every input has exactly one output. For such a behavior, Mathlib's
vertical-line theorem supplies a proof-required complex-linear map whose graph is the original
behavior. No inverse or finite-dimensional hypothesis is required. When the input-mode family is
finite, the same functional behavior also determines a unique mode-transform matrix.

Series composition uses an existential intermediate amplitude to identify the first behavior's
output with the second behavior's input. Parallel composition places two independent behaviors on
disjoint sum-indexed mode families. `feedbackSolutions` retains every state satisfying a forward
behavior and a return behavior, without requiring existence or uniqueness. For behaviors
constructed as graphs, the graph theorems prove that series and parallel recover ordinary
linear-map composition and block-diagonal mode-transform composition.

## ii. Scope

The behavior type and its relational compositions require no finite index types, matrix inverse,
or unique-solvability hypothesis. They are fixed-frequency complex-linear semantics only: no
causality, delay, source, termination, passivity, electromagnetic normalization, or physical
realization is included. Parallel composition does not duplicate or sum an amplitude, and it does
not reuse one amplitude as more than one input. A feedback-solution relation is not an inverse or a
well-posedness assertion.

## iii. Key definitions and results

- `LinearBehavior`: a complex submodule of paired input and output mode amplitudes.
- `LinearBehavior.ofLinearMap`: the graph behavior of a complex-linear map.
- `LinearBehavior.IsFunctional`: total, single-valued behavior.
- `LinearBehavior.toLinearMap`: the proof-required linear map of a functional behavior.
- `LinearBehavior.toModeTransform`: the proof-required finite matrix of a functional behavior.
- `ModeTransform.toBehavior`: the graph behavior induced by a finite mode transform.
- `ModeTransform.toBehavior_isFunctional`: every mode-transform behavior is functional.
- `LinearBehavior.identity`: equality between input and output amplitudes.
- `LinearBehavior.series`: relational series composition.
- `LinearBehavior.parallel`: independent behavior on disjoint mode families.
- `LinearBehavior.feedbackSolutions`: all states satisfying a forward and return relation.
- `ModeTransform.toBehavior_mul`: matrix cascade agrees with relational series composition.
- `ModeTransform.toBehavior_directSum`: block-diagonal action agrees with relational parallel
  composition.

## iv. Table of contents

- A. Behaviors and functional graphs
- B. Identity and series composition
- C. Parallel composition
- D. Feedback-solution relations

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

/-- A behavior is total when every input amplitude is related to at least one output amplitude. -/
def IsTotal (behavior : LinearBehavior ι κ) : Prop :=
  ∀ input, ∃ output, (input, output) ∈ behavior

/-- A behavior is single-valued when one input amplitude cannot have two distinct outputs. -/
def IsSingleValued (behavior : LinearBehavior ι κ) : Prop :=
  ∀ ⦃input output₁ output₂⦄,
    (input, output₁) ∈ behavior → (input, output₂) ∈ behavior → output₁ = output₂

/-- A functional behavior is both total and single-valued. -/
def IsFunctional (behavior : LinearBehavior ι κ) : Prop :=
  behavior.IsTotal ∧ behavior.IsSingleValued

/-- A linear-map graph is total. -/
lemma isTotal_ofLinearMap (map : ModeAmplitude ι →ₗ[ℂ] ModeAmplitude κ) :
    (ofLinearMap map).IsTotal := by
  intro input
  exact ⟨map input, by simp⟩

/-- A linear-map graph is single-valued. -/
lemma isSingleValued_ofLinearMap (map : ModeAmplitude ι →ₗ[ℂ] ModeAmplitude κ) :
    (ofLinearMap map).IsSingleValued := by
  intro input output₁ output₂ hOutput₁ hOutput₂
  rw [mem_ofLinearMap_iff] at hOutput₁ hOutput₂
  exact hOutput₁.trans hOutput₂.symm

/-- A linear-map graph is functional. -/
lemma isFunctional_ofLinearMap (map : ModeAmplitude ι →ₗ[ℂ] ModeAmplitude κ) :
    (ofLinearMap map).IsFunctional :=
  ⟨isTotal_ofLinearMap map, isSingleValued_ofLinearMap map⟩

/-- Every functional behavior is the graph of a complex-linear map. -/
lemma exists_eq_ofLinearMap (behavior : LinearBehavior ι κ)
    (hFunctional : behavior.IsFunctional) :
    ∃ map : ModeAmplitude ι →ₗ[ℂ] ModeAmplitude κ, behavior = ofLinearMap map := by
  rcases hFunctional with ⟨hTotal, hSingleValued⟩
  have hBijective : Function.Bijective (Prod.fst ∘ behavior.subtype) := by
    constructor
    · rintro ⟨⟨input₁, output₁⟩, hFirst⟩
        ⟨⟨input₂, output₂⟩, hSecond⟩ hInput
      change input₁ = input₂ at hInput
      subst input₂
      apply Subtype.ext
      exact Prod.ext rfl (hSingleValued hFirst hSecond)
    · intro input
      rcases hTotal input with ⟨output, hOutput⟩
      exact ⟨⟨(input, output), hOutput⟩, rfl⟩
  simpa only [ofLinearMap] using Submodule.exists_eq_graph hBijective

/-- The complex-linear map whose graph is a functional behavior.

The proof requirement prevents a relation that is not total or is multivalued from being treated
as a linear input-output map.
-/
noncomputable def toLinearMap (behavior : LinearBehavior ι κ)
    (hFunctional : behavior.IsFunctional) :
    ModeAmplitude ι →ₗ[ℂ] ModeAmplitude κ :=
  Classical.choose (exists_eq_ofLinearMap behavior hFunctional)

/-- Re-embedding the extracted linear map recovers the functional behavior exactly. -/
@[simp]
lemma ofLinearMap_toLinearMap (behavior : LinearBehavior ι κ)
    (hFunctional : behavior.IsFunctional) :
    ofLinearMap (behavior.toLinearMap hFunctional) = behavior :=
  (Classical.choose_spec (exists_eq_ofLinearMap behavior hFunctional)).symm

/-- Membership in a functional behavior is exactly evaluation of its extracted linear map. -/
lemma mem_iff_eq_toLinearMap (behavior : LinearBehavior ι κ)
    (hFunctional : behavior.IsFunctional) (input : ModeAmplitude ι)
    (output : ModeAmplitude κ) :
    (input, output) ∈ behavior ↔ output = behavior.toLinearMap hFunctional input := by
  constructor
  · intro hMember
    apply (mem_ofLinearMap_iff _ _ _).mp
    rw [ofLinearMap_toLinearMap]
    exact hMember
  · intro hOutput
    rw [← ofLinearMap_toLinearMap behavior hFunctional]
    exact (mem_ofLinearMap_iff _ _ _).mpr hOutput

/-- Extracting the canonical graph behavior recovers the original linear map. -/
@[simp]
lemma toLinearMap_ofLinearMap (map : ModeAmplitude ι →ₗ[ℂ] ModeAmplitude κ)
    (hFunctional : (ofLinearMap map).IsFunctional) :
    (ofLinearMap map).toLinearMap hFunctional = map := by
  apply ofLinearMap_injective
  rw [ofLinearMap_toLinearMap]

/-- The finite mode-transform matrix whose graph is a functional behavior.

The proof requirement excludes partial or multivalued relations. Finite input modes and a chosen
decidable equality supply the matrix representation of the extracted complex-linear map.
-/
noncomputable def toModeTransform [Fintype ι] [DecidableEq ι]
    (behavior : LinearBehavior ι κ) (hFunctional : behavior.IsFunctional) :
    ModeTransform ι κ :=
  Matrix.toEuclideanLin.symm (behavior.toLinearMap hFunctional)

/-- The mode transform extracted from a behavior induces its extracted complex-linear map. -/
@[simp]
lemma toLinearMap_toModeTransform [Fintype ι] [DecidableEq ι]
    (behavior : LinearBehavior ι κ) (hFunctional : behavior.IsFunctional) :
    (behavior.toModeTransform hFunctional).toLinearMap = behavior.toLinearMap hFunctional :=
  Matrix.toEuclideanLin.apply_symm_apply (behavior.toLinearMap hFunctional)

/-- Membership in a functional finite-input behavior is evaluation of its extracted mode
transform. -/
lemma mem_iff_eq_toModeTransform [Fintype ι] [DecidableEq ι]
    (behavior : LinearBehavior ι κ) (hFunctional : behavior.IsFunctional)
    (input : ModeAmplitude ι) (output : ModeAmplitude κ) :
    (input, output) ∈ behavior ↔
      output = (behavior.toModeTransform hFunctional).toLinearMap input :=
  (behavior.mem_iff_eq_toLinearMap hFunctional input output).trans
    (by rw [toLinearMap_toModeTransform])

/-- A behavior is functional exactly when it is the graph of a unique complex-linear map. -/
lemma isFunctional_iff_existsUnique_eq_ofLinearMap (behavior : LinearBehavior ι κ) :
    behavior.IsFunctional ↔
      ∃! map : ModeAmplitude ι →ₗ[ℂ] ModeAmplitude κ, behavior = ofLinearMap map := by
  constructor
  · intro hFunctional
    refine ⟨behavior.toLinearMap hFunctional,
      (ofLinearMap_toLinearMap behavior hFunctional).symm, ?_⟩
    intro map hMap
    apply ofLinearMap_injective
    rw [← hMap, ofLinearMap_toLinearMap]
  · rintro ⟨map, hMap, _⟩
    rw [hMap]
    exact isFunctional_ofLinearMap map

end LinearBehavior

namespace ModeTransform

variable {ι : Type u} {κ : Type v} {μ : Type w}

/-- The graph behavior induced by a mode transform with a finite input family. -/
def toBehavior [Fintype ι] (transform : ModeTransform ι κ) : LinearBehavior ι κ := by
  classical
  exact LinearBehavior.ofLinearMap transform.toLinearMap

/-- Every mode transform induces a functional graph behavior. -/
lemma toBehavior_isFunctional [Fintype ι] (transform : ModeTransform ι κ) :
    transform.toBehavior.IsFunctional := by
  classical
  simpa only [toBehavior] using
    LinearBehavior.isFunctional_ofLinearMap transform.toLinearMap

/-- Extracting the linear map of a mode-transform behavior recovers its bundled linear map. -/
@[simp]
lemma toLinearMap_toBehavior [Fintype ι] [DecidableEq ι] (transform : ModeTransform ι κ)
    (hFunctional : transform.toBehavior.IsFunctional) :
    transform.toBehavior.toLinearMap hFunctional = transform.toLinearMap := by
  classical
  apply LinearBehavior.ofLinearMap_injective
  rw [LinearBehavior.ofLinearMap_toLinearMap]
  rfl

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

variable {ι : Type u} {κ : Type v}

/-- Re-embedding the mode transform extracted from a functional finite-input behavior recovers
the behavior. -/
@[simp]
lemma toBehavior_toModeTransform [Fintype ι] [DecidableEq ι]
    (behavior : LinearBehavior ι κ) (hFunctional : behavior.IsFunctional) :
    (behavior.toModeTransform hFunctional).toBehavior = behavior := by
  change ofLinearMap (behavior.toModeTransform hFunctional).toLinearMap = behavior
  rw [toLinearMap_toModeTransform, ofLinearMap_toLinearMap]

/-- The extracted mode transform is the unique transform whose graph is the functional behavior. -/
lemma toModeTransform_unique [Fintype ι] [DecidableEq ι]
    (behavior : LinearBehavior ι κ) (hFunctional : behavior.IsFunctional)
    (transform : ModeTransform ι κ) (hTransform : transform.toBehavior = behavior) :
    behavior.toModeTransform hFunctional = transform := by
  apply ModeTransform.toBehavior_injective
  rw [toBehavior_toModeTransform, hTransform]

/-- Extracting a mode transform from its graph recovers the original transform. -/
@[simp]
lemma toModeTransform_toBehavior [Fintype ι] [DecidableEq ι]
    (transform : ModeTransform ι κ) :
    transform.toBehavior.toModeTransform transform.toBehavior_isFunctional = transform :=
  toModeTransform_unique transform.toBehavior transform.toBehavior_isFunctional transform rfl

end LinearBehavior

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

/-- The identity behavior is functional. -/
lemma isFunctional_identity : (identity : LinearBehavior ι ι).IsFunctional :=
  isFunctional_ofLinearMap LinearMap.id

/-- Extracting the identity behavior gives the identity linear map. -/
@[simp]
lemma toLinearMap_identity (hFunctional : (identity : LinearBehavior ι ι).IsFunctional) :
    (identity : LinearBehavior ι ι).toLinearMap hFunctional = LinearMap.id := by
  simpa only [identity] using
    toLinearMap_ofLinearMap
      (LinearMap.id : ModeAmplitude ι →ₗ[ℂ] ModeAmplitude ι) hFunctional

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

/-- A series composition of total behaviors is total. -/
lemma IsTotal.series {first : LinearBehavior ι κ} {second : LinearBehavior κ μ}
    (hFirst : first.IsTotal) (hSecond : second.IsTotal) :
    (first.series second).IsTotal := by
  intro input
  rcases hFirst input with ⟨middle, hFirstMember⟩
  rcases hSecond middle with ⟨output, hSecondMember⟩
  exact ⟨output, middle, hFirstMember, hSecondMember⟩

/-- Series composition preserves single-valuedness. -/
lemma IsSingleValued.series {first : LinearBehavior ι κ} {second : LinearBehavior κ μ}
    (hFirst : first.IsSingleValued) (hSecond : second.IsSingleValued) :
    (first.series second).IsSingleValued := by
  rintro input output₁ output₂ ⟨middle₁, hFirst₁, hSecond₁⟩
    ⟨middle₂, hFirst₂, hSecond₂⟩
  have hMiddle : middle₁ = middle₂ := hFirst hFirst₁ hFirst₂
  subst middle₂
  exact hSecond hSecond₁ hSecond₂

/-- A series composition of functional behaviors is functional. -/
lemma IsFunctional.series {first : LinearBehavior ι κ} {second : LinearBehavior κ μ}
    (hFirst : first.IsFunctional) (hSecond : second.IsFunctional) :
    (first.series second).IsFunctional :=
  ⟨hFirst.1.series hSecond.1, hFirst.2.series hSecond.2⟩

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

/-- Extracting a functional series composition gives ordinary linear-map composition in the same
behavioral series order: `first` acts before `second`. -/
lemma toLinearMap_series (first : LinearBehavior ι κ) (second : LinearBehavior κ μ)
    (hFirst : first.IsFunctional) (hSecond : second.IsFunctional) :
    (first.series second).toLinearMap (hFirst.series hSecond) =
      (second.toLinearMap hSecond).comp (first.toLinearMap hFirst) := by
  apply ofLinearMap_injective
  rw [ofLinearMap_toLinearMap, ← ofLinearMap_series,
    ofLinearMap_toLinearMap, ofLinearMap_toLinearMap]

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

/-- Extracting the mode transform of a functional series composition gives the matrix product with
the later behavior on the left. -/
lemma toModeTransform_series [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (first : LinearBehavior ι κ) (second : LinearBehavior κ μ)
    (hFirst : first.IsFunctional) (hSecond : second.IsFunctional) :
    (first.series second).toModeTransform (hFirst.series hSecond) =
      second.toModeTransform hSecond * first.toModeTransform hFirst := by
  apply ModeTransform.toBehavior_injective
  rw [toBehavior_toModeTransform, ← ModeTransform.toBehavior_mul,
    toBehavior_toModeTransform, toBehavior_toModeTransform]

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

/-- A parallel composition of total behaviors is total. -/
lemma IsTotal.parallel {left : LinearBehavior ι κ} {right : LinearBehavior μ ν}
    (hLeft : left.IsTotal) (hRight : right.IsTotal) :
    (left.parallel right).IsTotal := by
  intro input
  rcases hLeft input.restrictInl with ⟨leftOutput, hLeftMember⟩
  rcases hRight input.restrictInr with ⟨rightOutput, hRightMember⟩
  exact ⟨leftOutput.directSum rightOutput, hLeftMember, hRightMember⟩

/-- Parallel composition preserves single-valuedness. -/
lemma IsSingleValued.parallel {left : LinearBehavior ι κ} {right : LinearBehavior μ ν}
    (hLeft : left.IsSingleValued) (hRight : right.IsSingleValued) :
    (left.parallel right).IsSingleValued := by
  rintro input output₁ output₂ ⟨hLeft₁, hRight₁⟩ ⟨hLeft₂, hRight₂⟩
  have hLeftOutput : output₁.restrictInl = output₂.restrictInl := hLeft hLeft₁ hLeft₂
  have hRightOutput : output₁.restrictInr = output₂.restrictInr := hRight hRight₁ hRight₂
  calc
    output₁ = output₁.restrictInl.directSum output₁.restrictInr :=
      (ModeAmplitude.directSum_restrict output₁).symm
    _ = output₂.restrictInl.directSum output₂.restrictInr :=
      congrArg₂ ModeAmplitude.directSum hLeftOutput hRightOutput
    _ = output₂ := ModeAmplitude.directSum_restrict output₂

/-- A parallel composition of functional behaviors is functional. -/
lemma IsFunctional.parallel {left : LinearBehavior ι κ} {right : LinearBehavior μ ν}
    (hLeft : left.IsFunctional) (hRight : right.IsFunctional) :
    (left.parallel right).IsFunctional :=
  ⟨hLeft.1.parallel hRight.1, hLeft.2.parallel hRight.2⟩

/-- Extracting a functional parallel composition acts independently on the two restricted input
branches. -/
lemma toLinearMap_parallel_apply (left : LinearBehavior ι κ) (right : LinearBehavior μ ν)
    (hLeft : left.IsFunctional) (hRight : right.IsFunctional)
    (input : ModeAmplitude (ι ⊕ μ)) :
    (left.parallel right).toLinearMap (hLeft.parallel hRight) input =
      (left.toLinearMap hLeft input.restrictInl).directSum
        (right.toLinearMap hRight input.restrictInr) := by
  symm
  apply (mem_iff_eq_toLinearMap _ _ _ _).mp
  constructor
  · exact (mem_iff_eq_toLinearMap _ _ _ _).mpr rfl
  · exact (mem_iff_eq_toLinearMap _ _ _ _).mpr rfl

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

namespace LinearBehavior

variable {ι : Type u} {κ : Type v} {μ : Type w}

/-!

## D. Feedback-solution relations

-/

/-- The linear map extracting the incident/outgoing pair from an external-input/solution pair. -/
def feedbackForwardStateMap :
    (ModeAmplitude μ × ModeAmplitude (ι ⊕ κ)) →ₗ[ℂ]
      (ModeAmplitude ι × ModeAmplitude κ) where
  toFun := fun pair => (pair.2.restrictInl, pair.2.restrictInr)
  map_add' := by
    intro first second
    apply Prod.ext
    · apply WithLp.ofLp_injective 2
      funext index
      rfl
    · apply WithLp.ofLp_injective 2
      funext index
      rfl
  map_smul' := by
    intro scalar pair
    apply Prod.ext
    · apply WithLp.ofLp_injective 2
      funext index
      rfl
    · apply WithLp.ofLp_injective 2
      funext index
      rfl

/-- The linear map presenting `outgoing ⊕ external` and incident amplitudes to a return
behavior. -/
def feedbackReturnStateMap :
    (ModeAmplitude μ × ModeAmplitude (ι ⊕ κ)) →ₗ[ℂ]
      (ModeAmplitude (κ ⊕ μ) × ModeAmplitude ι) where
  toFun := fun pair => (pair.2.restrictInr.directSum pair.1, pair.2.restrictInl)
  map_add' := by
    intro first second
    apply Prod.ext
    · apply WithLp.ofLp_injective 2
      funext index
      rcases index with index | index <;> rfl
    · apply WithLp.ofLp_injective 2
      funext index
      rfl
  map_smul' := by
    intro scalar pair
    apply Prod.ext
    · apply WithLp.ofLp_injective 2
      funext index
      rcases index with index | index <;> rfl
    · apply WithLp.ofLp_injective 2
      funext index
      rfl

/-- The relation retaining every state that simultaneously satisfies a forward behavior and a
return behavior.

The external input has modes `μ`. A returned state has incident coordinates `ι` in its left
summand and outgoing coordinates `κ` in its right summand. The forward relation is tested on the
incident/outgoing pair, while the return relation receives `outgoing ⊕ external` and must
reproduce the incident amplitude. This construction asserts neither existence nor uniqueness of a
state.
-/
def feedbackSolutions (forward : LinearBehavior ι κ)
    (returnBehavior : LinearBehavior (κ ⊕ μ) ι) : LinearBehavior μ (ι ⊕ κ) :=
  forward.comap feedbackForwardStateMap ⊓
    returnBehavior.comap feedbackReturnStateMap

/-- Feedback-solution membership states the forward and return constraints on the two state
summands. -/
@[simp]
lemma mem_feedbackSolutions_iff (forward : LinearBehavior ι κ)
    (returnBehavior : LinearBehavior (κ ⊕ μ) ι) (input : ModeAmplitude μ)
    (state : ModeAmplitude (ι ⊕ κ)) :
    (input, state) ∈ forward.feedbackSolutions returnBehavior ↔
      (state.restrictInl, state.restrictInr) ∈ forward ∧
        (state.restrictInr.directSum input, state.restrictInl) ∈ returnBehavior := by
  simp only [feedbackSolutions, Submodule.mem_inf, Submodule.mem_comap]
  rfl

/-- On an explicitly joined state, feedback-solution membership is exactly the forward relation
and the return relation fed by `outgoing ⊕ external`. -/
lemma mem_feedbackSolutions_directSum_iff (forward : LinearBehavior ι κ)
    (returnBehavior : LinearBehavior (κ ⊕ μ) ι) (input : ModeAmplitude μ)
    (incident : ModeAmplitude ι) (outgoing : ModeAmplitude κ) :
    (input, incident.directSum outgoing) ∈ forward.feedbackSolutions returnBehavior ↔
      (incident, outgoing) ∈ forward ∧
        (outgoing.directSum input, incident) ∈ returnBehavior := by
  rw [mem_feedbackSolutions_iff, ModeAmplitude.restrictInl_directSum,
    ModeAmplitude.restrictInr_directSum]

end LinearBehavior

end

end Optics
