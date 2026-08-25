/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.Hierarchical
public import Physlib.Optics.Network.TwoPortRedhefferStar
public import Physlib.Optics.Network.TwoPortSeriesNetlistBehavior

/-!
# Redheffer composition as a canonical flat-netlist response

## i. Overview

This file closes the local two-device part of X-01 by identifying both the N5H relational closure
and the proof-gated N5 elimination response of the canonical netlist with typed Redheffer
composition. The broader system/Mason cross-semantics oracle remains separate.

## ii. Key results

- `TwoPortSeriesNetlist.externalCloseBehavior_eq_redhefferSeriesBehavior`: N5H closure agrees with
  singular-safe Redheffer composition.
- `TwoPortSeriesNetlist.responseTransform_reindex_eq_redhefferStar`: N5 elimination agrees with
  the behavior-derived Redheffer star product on their common proof-gated domain.

## iii. Table of contents

- A. Relational composition agreement
- B. Functional response agreement

## iv. References

This cross-semantics bridge is Physlib-original; no external source is used here.

-/

@[expose] public section

namespace Optics

noncomputable section

universe u

namespace TwoPortSeriesNetlist

variable {left middle right : Type u}

/-!

## A. Relational composition agreement

-/

/-- Closing the independently assembled component behavior by the canonical middle connection is
exactly singular-safe relational Redheffer composition, in typed outer coordinates. -/
lemma externalCloseBehavior_eq_redhefferSeriesBehavior
    [Fintype left] [DecidableEq left] [Fintype middle] [DecidableEq middle]
    [Fintype right] [DecidableEq right]
    (first : ScatteringMatrix (left ⊕ middle))
    (second : ScatteringMatrix (middle ⊕ right)) :
    ((netlist first second).connections.closeBehavior
      (netlist first second).componentBehavior).reindex
        (externalIncidentEquiv first second) (externalOutgoingEquiv first second) =
      first.toTwoPortScatteringTransform.redhefferSeriesBehavior
        second.toTwoPortScatteringTransform := by
  rw [← (netlist first second).behavior_eq_closeBehavior]
  exact externalBehavior_eq_redhefferSeriesBehavior first second

/-!

## B. Functional response agreement

-/

/-- Relabeling the N5 response graph to typed outer coordinates recovers the external netlist
behavior from which that response was extracted. -/
lemma toBehavior_responseTransform_reindex
    [Fintype left] [DecidableEq left] [Fintype middle] [DecidableEq middle]
    [Fintype right] [DecidableEq right]
    (first : ScatteringMatrix (left ⊕ middle))
    (second : ScatteringMatrix (middle ⊕ right))
    (hWellPosed : (netlist first second).IsWellPosed) :
    (((netlist first second).responseTransform hWellPosed).reindex
      (externalIncidentEquiv first second)
      (externalOutgoingEquiv first second)).toBehavior = externalBehavior first second := by
  rw [ModeTransform.toBehavior_reindex, externalBehavior]
  ext state
  rcases state with ⟨input, output⟩
  rw [LinearBehavior.mem_reindex_iff, LinearBehavior.mem_reindex_iff]
  have hGraph := (netlist first second).toBehavior_responseTransform hWellPosed
  constructor
  · intro hMember
    exact hGraph ▸ hMember
  · intro hMember
    exact hGraph.symm ▸ hMember

/-- On the common well-posed domain, N5 elimination of the canonical flat netlist is exactly the
behavior-derived Redheffer star product after the canonical external-coordinate relabeling. -/
lemma responseTransform_reindex_eq_redhefferStar
    [Fintype left] [DecidableEq left] [Fintype middle] [DecidableEq middle]
    [Fintype right] [DecidableEq right]
    (first : ScatteringMatrix (left ⊕ middle))
    (second : ScatteringMatrix (middle ⊕ right))
    (hWellPosed : (netlist first second).IsWellPosed)
    (hFeedback : first.toTwoPortScatteringTransform.HasBijectiveRedhefferFeedback
      second.toTwoPortScatteringTransform) :
    ((netlist first second).responseTransform hWellPosed).reindex
        (externalIncidentEquiv first second) (externalOutgoingEquiv first second) =
      first.toTwoPortScatteringTransform.redhefferStar
        second.toTwoPortScatteringTransform hFeedback := by
  apply ModeTransform.toBehavior_injective
  calc
    (((netlist first second).responseTransform hWellPosed).reindex
        (externalIncidentEquiv first second)
        (externalOutgoingEquiv first second)).toBehavior = externalBehavior first second :=
      toBehavior_responseTransform_reindex first second hWellPosed
    _ = first.toTwoPortScatteringTransform.redhefferSeriesBehavior
          second.toTwoPortScatteringTransform :=
      externalBehavior_eq_redhefferSeriesBehavior first second
    _ = (first.toTwoPortScatteringTransform.redhefferStar
          second.toTwoPortScatteringTransform hFeedback).toBehavior :=
      (TwoPortScatteringTransform.toBehavior_redhefferStar _ _ hFeedback).symm

end TwoPortSeriesNetlist

end

end Optics
