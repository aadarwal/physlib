/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.TwoPortScattering

/-!
# Regression tests for the typed two-port scattering adapter

## i. Overview

A raw two-port scattering matrix with four distinct nonreal entries is carried through the public
`ScatteringMatrix` adapter. Exact block checks catch left/right reversal, incident/outgoing
reversal, row/column transposition, conjugation, and an incorrectly oriented reindexing.

## ii. Scope

The fixture is an algebraic orientation sentinel. Its coefficients make no losslessness,
passivity, reciprocity, or physical-realization claim.

## iii. Table of contents

- A. Four-block adapter sentinel

-/

@[expose] public section

namespace Optics

noncomputable section

/-!

## A. Four-block adapter sentinel

-/

/-- A raw scattering matrix whose four distinct nonreal entries expose every two-port block. -/
def twoPortScatteringRegressionRaw : ScatteringMatrix (Unit ⊕ Unit) where
  toModeTransform
    | Sum.inl _, Sum.inl _ => 1 + Complex.I
    | Sum.inl _, Sum.inr _ => 2 - Complex.I
    | Sum.inr _, Sum.inl _ => 3 + 2 * Complex.I
    | Sum.inr _, Sum.inr _ => 4 - 3 * Complex.I

/-- The adapter preserves the raw left-reflection entry. -/
lemma twoPortScatteringRegression_leftReflection :
    twoPortScatteringRegressionRaw.toTwoPortScatteringTransform
        (Sum.inl (Outgoing.mk ())) (Sum.inl (Incident.mk ())) =
      1 + Complex.I := by
  rw [ScatteringMatrix.toTwoPortScatteringTransform_apply_inl_inl]
  rfl

/-- The adapter preserves the raw right-to-left transmission entry. -/
lemma twoPortScatteringRegression_rightToLeftTransmission :
    twoPortScatteringRegressionRaw.toTwoPortScatteringTransform
        (Sum.inl (Outgoing.mk ())) (Sum.inr (Incident.mk ())) =
      2 - Complex.I := by
  rw [ScatteringMatrix.toTwoPortScatteringTransform_apply_inl_inr]
  rfl

/-- The adapter preserves the raw left-to-right transmission entry. -/
lemma twoPortScatteringRegression_leftToRightTransmission :
    twoPortScatteringRegressionRaw.toTwoPortScatteringTransform
        (Sum.inr (Outgoing.mk ())) (Sum.inl (Incident.mk ())) =
      3 + 2 * Complex.I := by
  rw [ScatteringMatrix.toTwoPortScatteringTransform_apply_inr_inl]
  rfl

/-- The adapter preserves the raw right-reflection entry. -/
lemma twoPortScatteringRegression_rightReflection :
    twoPortScatteringRegressionRaw.toTwoPortScatteringTransform
        (Sum.inr (Outgoing.mk ())) (Sum.inr (Incident.mk ())) =
      4 - 3 * Complex.I := by
  rw [ScatteringMatrix.toTwoPortScatteringTransform_apply_inr_inr]
  rfl

/-- Recombining the typed two-port labels recovers the oriented raw fixture exactly. -/
lemma twoPortScatteringRegression_roundTrip :
    twoPortScatteringRegressionRaw.toTwoPortScatteringTransform.reindex
        Incident.splitSumEquiv.symm Outgoing.splitSumEquiv.symm =
      twoPortScatteringRegressionRaw.toOrientedModeTransform := by
  exact TwoPortScatteringTransform.reindex_symm_ofOriented
    twoPortScatteringRegressionRaw.toOrientedModeTransform

end

end Optics
