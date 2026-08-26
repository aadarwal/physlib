/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.FlatNetlistEliminationRegression
public import Physlib.Optics.Network.FlatNetlistMason

/-!
# Regression tests for flat-netlist Mason agreement

## i. Overview

The well-posed shared-link fixture has a nonreal, nonsymmetric feedback matrix. Its displayed
inverse and external response pin an internal Mason gain and both directions of the assembled
external response. The unequal values `6` and `2` detect source/sink transposition.

The pre-existing singular shared-link fixture is the negative control: its extracted graph
determinant vanishes exactly where the relational netlist is not well posed. No totalized inverse
or Mason response is assigned solution semantics there.

## ii. Scope

These are hostile algebraic fixtures, not passive or physically normalized optical systems. The
regression checks the matrix-level N5/Mason bridge; it does not provide a ring, DCDR, edge-identity,
frequency-domain, or Z-transform cross-semantics result.

## iii. Table of contents

- A. Nonsymmetric well-posed response
- B. Singular determinant gate

-/

@[expose] public section

namespace Optics

noncomputable section

/-!

## A. Nonsymmetric well-posed response

-/

/-- Aggregate channels in the well-posed fixture are finite. -/
local instance flatNetlistMasonRegressionChannelFintype :
    Fintype flatNetlistEliminationRegression.Channel := by
  change Fintype (Σ _ : (Σ _ : Bool, Bool), Unit)
  infer_instance

/-- Aggregate channels in the well-posed fixture have decidable equality. -/
local instance flatNetlistMasonRegressionChannelDecidableEq :
    DecidableEq flatNetlistEliminationRegression.Channel := Classical.decEq _

/-- Connected channels in the well-posed fixture are finite. -/
local instance flatNetlistMasonRegressionConnectedChannelFintype :
    Fintype flatNetlistEliminationRegression.ConnectedChannel := by
  change Fintype (Σ _ : Unit, Unit ⊕ Unit)
  infer_instance

/-- Connected channels in the well-posed fixture have decidable equality. -/
local instance flatNetlistMasonRegressionConnectedChannelDecidableEq :
    DecidableEq flatNetlistEliminationRegression.ConnectedChannel := Classical.decEq _

/-- The extracted graph system matrix is the independently displayed feedback matrix. -/
lemma flatNetlistMasonRegression_systemMatrix_eq :
    Physlib.SignalFlowGraph.systemMatrix
        flatNetlistEliminationRegression.feedbackSignalFlowGraph =
      flatNetlistEliminationRegressionFeedback := by
  rw [flatNetlistEliminationRegression.systemMatrix_feedbackSignalFlowGraph,
    flatNetlistEliminationRegression_feedbackOperator_eq]

/-- Mason's graph-determinant gate holds for the nonsymmetric fixture. -/
lemma flatNetlistMasonRegression_graphDet_ne_zero :
    Physlib.SignalFlowGraph.graphDet
        flatNetlistEliminationRegression.feedbackSignalFlowGraph ≠ 0 :=
  (FlatNetlist.isWellPosed_iff_feedbackSignalFlowGraph_graphDet_ne_zero
    flatNetlistEliminationRegression).mp flatNetlistEliminationRegression_isWellPosed

/-- The internal gain from the second external incident node to the first link node is `3 / 2`.
This pins the source-to-sink order against the displayed inverse. -/
lemma flatNetlistMasonRegression_internal_gain :
    flatNetlistEliminationRegression.feedbackMasonTransform
        (Incident.mk flatNetlistEliminationRegressionALink)
        (Incident.mk flatNetlistEliminationRegressionBExternal) = 3 / 2 := by
  rw [flatNetlistEliminationRegression.feedbackMasonTransform_eq_feedbackInverse
      flatNetlistEliminationRegression_isWellPosed,
    flatNetlistEliminationRegression_feedbackInverse_eq]
  norm_num [flatNetlistEliminationRegressionInverse]

/-- The Mason-assembled response from the second exposed input to the first exposed output is
exactly `6`. -/
lemma flatNetlistMasonRegression_response_b_to_a :
    flatNetlistEliminationRegression.masonResponseTransform
        (Outgoing.mk flatNetlistEliminationRegressionExternalA)
        (Incident.mk flatNetlistEliminationRegressionExternalB) = 6 := by
  rw [← flatNetlistEliminationRegression.responseTransform_eq_masonResponseTransform
      flatNetlistEliminationRegression_isWellPosed,
    flatNetlistEliminationRegression_responseTransform_eq]
  norm_num [flatNetlistEliminationRegressionResponse]

/-- The reverse Mason-assembled response is exactly `2`, detecting a transposed external
response. -/
lemma flatNetlistMasonRegression_response_a_to_b :
    flatNetlistEliminationRegression.masonResponseTransform
        (Outgoing.mk flatNetlistEliminationRegressionExternalB)
        (Incident.mk flatNetlistEliminationRegressionExternalA) = 2 := by
  rw [← flatNetlistEliminationRegression.responseTransform_eq_masonResponseTransform
      flatNetlistEliminationRegression_isWellPosed,
    flatNetlistEliminationRegression_responseTransform_eq]
  norm_num [flatNetlistEliminationRegressionResponse]

/-!

## B. Singular determinant gate

-/

/-- Aggregate channels in the singular fixture are finite. -/
local instance flatNetlistMasonSingularChannelFintype :
    Fintype flatNetlistRegression.Channel :=
  Fintype.ofEquiv flatNetlistRegressionComponents.IndexedChannel
    flatNetlistRegressionComponents.channelEquiv

/-- Aggregate channels in the singular fixture have decidable equality. -/
local instance flatNetlistMasonSingularChannelDecidableEq :
    DecidableEq flatNetlistRegression.Channel := Classical.decEq _

/-- Connected channels in the singular fixture are finite. -/
local instance flatNetlistMasonSingularConnectedChannelFintype :
    Fintype flatNetlistRegression.ConnectedChannel := by
  change Fintype (Σ _ : Unit, Unit ⊕ Unit)
  infer_instance

/-- Connected channels in the singular fixture have decidable equality. -/
local instance flatNetlistMasonSingularConnectedChannelDecidableEq :
    DecidableEq flatNetlistRegression.ConnectedChannel := Classical.decEq _

/-- The singular relation's extracted graph determinant vanishes; the Mason denominator gate is
therefore not silently discharged by Mathlib's total inverse. -/
lemma flatNetlistMasonRegression_singular_graphDet_eq_zero :
    Physlib.SignalFlowGraph.graphDet flatNetlistRegression.feedbackSignalFlowGraph = 0 := by
  by_contra hGraphDet
  exact flatNetlistRegression_not_isWellPosed
    (flatNetlistRegression.isWellPosed_iff_feedbackSignalFlowGraph_graphDet_ne_zero.mpr hGraphDet)

end

end Optics
