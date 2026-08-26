/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.TwoPortChainScattering

/-!
# Finite folds of backward-first two-port chains

## i. Overview

A list of backward-first chain transforms is ordered from the input side to the output side.
Consequently, the head acts first and every later transform multiplies on the left. For example,
`fold [first, second] = second * first`.

The relational companion uses `LinearBehavior.series` in the same order. Its chain extraction is
proved by induction from
`BackwardFirstTwoPortBehavior.leftToRightChainTransform_series` at
`Physlib/Optics/Network/TwoPortChain.lean:149-160`. A proof-carrying scattering wrapper then states
the same agreement on the exact domain where every scattering element has bijective right-to-left
transmission.

## ii. Key results

- `BackwardFirstChainTransform.fold`: the output-side-on-the-left matrix fold.
- `BackwardFirstTwoPortBehavior.seriesFold`: relational series in input-to-output list order.
- `BackwardFirstChainTransform.leftToRightChainTransform_seriesFold`: extraction of a graph fold.
- `ChainableTwoPortScattering.behaviorFold_eq_chainFold_toBehavior`: certified scattering
  behavior equals the folded chain graph.
- `BackwardFirstChainTransform.fold_replicate`: a constant list folds to a matrix power.

## iii. Table of contents

- A. Relational and matrix folds
- B. Certified scattering folds

## iv. References and non-claims

The fold is neutral N3T machinery and is Physlib-original. It introduces no ring, propagation,
source-parity, termination, passivity, reciprocity, causality, or electromagnetic claim. The
bijective transmission certificate is only a coordinate-solvability gate; it is not inferred from
any physical condition.
-/

@[expose] public section

namespace Optics

noncomputable section

universe u

/-!

## A. Relational and matrix folds

-/

namespace BackwardFirstTwoPortBehavior

/-- Relational series composition in input-side-to-output-side list order.

The head behavior acts first. The empty list is the identity behavior.
-/
def seriesFold {ι : Type u} :
    List (BackwardFirstTwoPortBehavior ι ι) → BackwardFirstTwoPortBehavior ι ι
  | [] => LinearBehavior.identity
  | first :: rest => first.series (seriesFold rest)

/-- A list of functional chain views has a functional relational series fold. -/
lemma seriesFold_hasLeftToRightChainView {ι : Type u}
    (behaviors : List (BackwardFirstTwoPortBehavior ι ι))
    (hBehaviors : ∀ behavior ∈ behaviors, behavior.HasLeftToRightChainView) :
    (seriesFold behaviors).HasLeftToRightChainView := by
  induction behaviors with
  | nil => exact LinearBehavior.isFunctional_identity
  | cons first rest ih =>
      exact (hBehaviors first (by simp)).series
        (ih fun behavior hBehavior => hBehaviors behavior (by simp [hBehavior]))

end BackwardFirstTwoPortBehavior

namespace BackwardFirstChainTransform

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Fold chain transforms listed from the input side to the output side.

The recursion `fold (first :: rest) = fold rest * first` places later devices on the left. The
empty list is the identity transform.
-/
def fold : List (BackwardFirstChainTransform ι ι) → BackwardFirstChainTransform ι ι
  | [] => 1
  | first :: rest => fold rest * first

/-- Folding concatenated input-to-output lists puts the second sublist on the left. -/
lemma fold_append (first second : List (BackwardFirstChainTransform ι ι)) :
    fold (first ++ second) = fold second * fold first := by
  induction first with
  | nil => simp [fold]
  | cons head tail ih =>
      rw [List.cons_append, fold, ih, fold]
      exact Matrix.mul_assoc _ _ _

/-- A constant list of chain transforms folds to the corresponding matrix power. -/
lemma fold_replicate (chain : BackwardFirstChainTransform ι ι) (count : ℕ) :
    fold (List.replicate count chain) = chain ^ count := by
  induction count with
  | zero => simp [fold]
  | succ count ih =>
      rw [List.replicate_succ, fold, ih, pow_succ]

omit [DecidableEq ι] in
/-- The graph-series fold of a transform list is functional. -/
lemma seriesFold_map_toBehavior_hasLeftToRightChainView
    (chains : List (BackwardFirstChainTransform ι ι)) :
    (BackwardFirstTwoPortBehavior.seriesFold
      (chains.map ModeTransform.toBehavior)).HasLeftToRightChainView := by
  induction chains with
  | nil => exact LinearBehavior.isFunctional_identity
  | cons first rest ih =>
      exact first.toBehavior_isFunctional.series ih

/-- Extracting the graph-series fold gives the output-side-on-the-left matrix fold.

The induction step is exactly
`BackwardFirstTwoPortBehavior.leftToRightChainTransform_series` from
`Physlib/Optics/Network/TwoPortChain.lean:149-160`.
-/
lemma leftToRightChainTransform_seriesFold
    (chains : List (BackwardFirstChainTransform ι ι)) :
    BackwardFirstTwoPortBehavior.leftToRightChainTransform
        (BackwardFirstTwoPortBehavior.seriesFold
          (chains.map ModeTransform.toBehavior))
        (seriesFold_map_toBehavior_hasLeftToRightChainView chains) =
      fold chains := by
  induction chains with
  | nil =>
      change BackwardFirstTwoPortBehavior.leftToRightChainTransform
        LinearBehavior.identity LinearBehavior.isFunctional_identity =
          (1 : BackwardFirstChainTransform ι ι)
      apply BackwardFirstTwoPortBehavior.leftToRightChainTransform_unique
      exact ModeTransform.toBehavior_one
  | cons first rest ih =>
      let hFirst : BackwardFirstTwoPortBehavior.HasLeftToRightChainView
          first.toBehavior :=
        first.toBehavior_isFunctional
      let hRest := seriesFold_map_toBehavior_hasLeftToRightChainView rest
      have hProof : seriesFold_map_toBehavior_hasLeftToRightChainView (first :: rest) =
          hFirst.series hRest := Subsingleton.elim _ _
      rw [hProof]
      change BackwardFirstTwoPortBehavior.leftToRightChainTransform
          (first.toBehavior.series
            (BackwardFirstTwoPortBehavior.seriesFold
              (rest.map ModeTransform.toBehavior)))
          (hFirst.series hRest) = _
      rw [BackwardFirstTwoPortBehavior.leftToRightChainTransform_series
          first.toBehavior
          (BackwardFirstTwoPortBehavior.seriesFold
            (rest.map ModeTransform.toBehavior)) hFirst hRest,
        ih, BackwardFirstTwoPortBehavior.leftToRightChainTransform_toBehavior]
      rfl

/-- Relational series of transform graphs equals the graph of their matrix fold. -/
lemma seriesFold_map_toBehavior_eq_fold_toBehavior
    (chains : List (BackwardFirstChainTransform ι ι)) :
    BackwardFirstTwoPortBehavior.seriesFold
        (chains.map ModeTransform.toBehavior) =
      (fold chains).toBehavior := by
  let hChain := seriesFold_map_toBehavior_hasLeftToRightChainView chains
  calc
    BackwardFirstTwoPortBehavior.seriesFold
        (chains.map ModeTransform.toBehavior) =
        (BackwardFirstTwoPortBehavior.leftToRightChainTransform
          (BackwardFirstTwoPortBehavior.seriesFold
            (chains.map ModeTransform.toBehavior)) hChain).toBehavior :=
      (BackwardFirstTwoPortBehavior.toBehavior_leftToRightChainTransform _ _).symm
    _ = (fold chains).toBehavior := by
      rw [leftToRightChainTransform_seriesFold]

end BackwardFirstChainTransform

/-!

## B. Certified scattering folds

-/

/-- A two-port scattering transform carrying the exact certificate needed for a chain view. -/
structure ChainableTwoPortScattering (ι : Type u) [Fintype ι] [DecidableEq ι] where
  /-- The typed incident-to-outgoing scattering transform. -/
  scattering : TwoPortScatteringTransform ι ι
  /-- Bijectivity of the right-incident-to-left-outgoing transmission block. -/
  hasBijectiveRightToLeftTransmission :
    scattering.HasBijectiveRightToLeftTransmission

namespace ChainableTwoPortScattering

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- The backward-first relational behavior of a certified scattering element. -/
def behavior (element : ChainableTwoPortScattering ι) :
    BackwardFirstTwoPortBehavior ι ι :=
  element.scattering.toBackwardFirstBehavior

/-- The behavior-derived chain transform of a certified scattering element. -/
noncomputable def chainTransform (element : ChainableTwoPortScattering ι) :
    BackwardFirstChainTransform ι ι :=
  element.scattering.toBackwardFirstChainTransform
    element.hasBijectiveRightToLeftTransmission

/-- The certified element's chain graph is its original backward-first scattering behavior. -/
@[simp]
lemma toBehavior_chainTransform (element : ChainableTwoPortScattering ι) :
    element.chainTransform.toBehavior = element.behavior :=
  TwoPortScatteringTransform.toBehavior_toBackwardFirstChainTransform _ _

/-- Relational series of certified scattering elements in input-to-output list order. -/
def behaviorFold (elements : List (ChainableTwoPortScattering ι)) :
    BackwardFirstTwoPortBehavior ι ι :=
  BackwardFirstTwoPortBehavior.seriesFold (elements.map behavior)

/-- Matrix fold of certified scattering elements in input-to-output list order. -/
noncomputable def chainFold (elements : List (ChainableTwoPortScattering ι)) :
    BackwardFirstChainTransform ι ι :=
  BackwardFirstChainTransform.fold (elements.map chainTransform)

/-- The certified relational cascade is exactly the graph of its folded chain transform. -/
lemma behaviorFold_eq_chainFold_toBehavior
    (elements : List (ChainableTwoPortScattering ι)) :
    behaviorFold elements = (chainFold elements).toBehavior := by
  change BackwardFirstTwoPortBehavior.seriesFold (elements.map behavior) =
    (BackwardFirstChainTransform.fold (elements.map chainTransform)).toBehavior
  rw [← BackwardFirstChainTransform.seriesFold_map_toBehavior_eq_fold_toBehavior]
  induction elements with
  | nil => rfl
  | cons element rest ih =>
      simp only [List.map_cons, BackwardFirstTwoPortBehavior.seriesFold]
      rw [← toBehavior_chainTransform element, ih]

/-- The certified relational cascade has a left-to-right chain view. -/
lemma behaviorFold_hasLeftToRightChainView
    (elements : List (ChainableTwoPortScattering ι)) :
    (behaviorFold elements).HasLeftToRightChainView := by
  rw [behaviorFold_eq_chainFold_toBehavior]
  exact (chainFold elements).toBehavior_isFunctional

/-- Chain extraction of a certified relational cascade recovers its matrix fold. -/
lemma leftToRightChainTransform_behaviorFold
    (elements : List (ChainableTwoPortScattering ι)) :
    BackwardFirstTwoPortBehavior.leftToRightChainTransform
        (behaviorFold elements) (behaviorFold_hasLeftToRightChainView elements) =
      chainFold elements := by
  exact BackwardFirstTwoPortBehavior.leftToRightChainTransform_unique
    (behaviorFold elements) (behaviorFold_hasLeftToRightChainView elements)
    (chainFold elements) (behaviorFold_eq_chainFold_toBehavior elements).symm

end ChainableTwoPortScattering

end

end Optics
