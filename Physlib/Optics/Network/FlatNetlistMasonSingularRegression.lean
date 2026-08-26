/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.FlatNetlistEliminationRegression
public import Physlib.Optics.Network.FlatNetlistMason

/-!
# Singular regression for flat-netlist Mason extraction

## i. Overview

The pre-existing singular shared-link fixture is the negative control for the N5/Mason bridge.
Its extracted graph determinant is proved zero directly from its known noninjective feedback
operator, without appealing to the well-posedness/graph-determinant equivalence.

## ii. Scope

The result gives no solved-response meaning to the totalized inverse or Mason quotient at the zero
denominator. It is an algebraic failure sentinel, not a physical optical model.

## iii. Table of contents

- A. The singular determinant

-/

@[expose] public section

namespace Optics

noncomputable section

/-!

## A. The singular determinant

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

/-- The singular relation's extracted graph determinant vanishes by direct linear algebra from
its known noninjective feedback operator. This does not use the generic well-posedness/graph-
determinant equivalence, so that equivalence is not its own negative regression oracle. -/
lemma flatNetlistMasonRegression_singular_graphDet_eq_zero :
    Physlib.SignalFlowGraph.graphDet flatNetlistRegression.feedbackSignalFlowGraph = 0 := by
  rw [flatNetlistRegression.graphDet_feedbackSignalFlowGraph]
  by_contra hDet
  have hUnitDet : IsUnit flatNetlistRegression.feedbackOperator.det :=
    isUnit_iff_ne_zero.mpr hDet
  have hUnit : IsUnit flatNetlistRegression.feedbackOperator :=
    flatNetlistRegression.feedbackOperator.isUnit_iff_isUnit_det.mpr hUnitDet
  have hBijective : Function.Bijective flatNetlistRegression.feedbackOperator.toLinearMap :=
    (ModeTransform.toLinearMap_bijective_iff_isUnit _).mpr hUnit
  exact flatNetlistRegression_feedbackOperator_not_injective hBijective.1

end

end Optics
