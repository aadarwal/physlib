/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.TwoPortBehaviorRegression
public import Physlib.Optics.Network.TwoPortChain

/-!
# Regression tests for two-port chain extraction

## i. Overview

The perfect-through fixture gives a positive chain-extraction case: its regrouped behavior extracts
the identity transform. An asymmetric through fixture independently pins the two transmission
gains after regrouping. The zero-scattering fixture gives the corresponding negative case: a
functional scattering behavior need not have a left-to-right chain view.

Two nonsymmetric chain transforms then check series order. The later transform appears on the left
of the matrix product, and the reverse product is independently rejected at an exact entry.

## ii. Scope

These are algebraic fixed-frequency fixtures. Their scalar coordinates do not carry a field,
power, passivity, reciprocity, propagation-phase, termination, or physical-realization claim.

## iii. Table of contents

- A. Positive and negative chain extraction
- B. Nonsymmetric chain-series order

-/

@[expose] public section

namespace Optics

noncomputable section

/-!

## A. Positive and negative chain extraction

-/

/-- Perfect-through scattering has a left-to-right chain view. -/
lemma twoPortChainRegressionPerfectThrough_hasChainView :
    twoPortBehaviorRegressionPerfectThrough.toBackwardFirst.HasLeftToRightChainView := by
  rw [twoPortBehaviorRegressionPerfectThrough_toBackwardFirst]
  exact LinearBehavior.isFunctional_identity

/-- Extracting the regrouped perfect-through behavior gives the identity chain transform. -/
lemma twoPortChainRegressionPerfectThrough_chainTransform :
    BackwardFirstTwoPortBehavior.leftToRightChainTransform
      twoPortBehaviorRegressionPerfectThrough.toBackwardFirst
      twoPortChainRegressionPerfectThrough_hasChainView = 1 := by
  exact BackwardFirstTwoPortBehavior.leftToRightChainTransform_unique
    twoPortBehaviorRegressionPerfectThrough.toBackwardFirst
    twoPortChainRegressionPerfectThrough_hasChainView 1 (by
      rw [ModeTransform.toBehavior_one,
        twoPortBehaviorRegressionPerfectThrough_toBackwardFirst])

/-- An asymmetric scattering transform with leftward gain two and rightward gain three. -/
def twoPortChainRegressionAsymmetricScattering :
    ModeTransform (Incident Unit ⊕ Incident Unit) (Outgoing Unit ⊕ Outgoing Unit)
  | Sum.inl _, Sum.inl _ => 0
  | Sum.inl _, Sum.inr _ => 2
  | Sum.inr _, Sum.inl _ => 3
  | Sum.inr _, Sum.inr _ => 0

/-- The asymmetric transform presented as a scattering-coordinate behavior. -/
def twoPortChainRegressionAsymmetricScatteringBehavior :
    TwoPortScatteringBehavior Unit Unit :=
  twoPortChainRegressionAsymmetricScattering.toBehavior

/-- The left-outgoing coordinate of the asymmetric scattering transform has gain two from the
right-incident coordinate. -/
@[simp]
lemma twoPortChainRegressionAsymmetricScattering_left_action
    (incident : ModeAmplitude (Incident Unit ⊕ Incident Unit)) :
    (twoPortChainRegressionAsymmetricScattering.toLinearMap incident)
        (Sum.inl (Outgoing.mk ())) =
      2 * incident (Sum.inr (Incident.mk ())) := by
  norm_num [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    twoPortChainRegressionAsymmetricScattering, Fintype.sum_sum_type]
  rw [← Incident.channelEquiv.symm.sum_comp]
  simp

/-- The right-outgoing coordinate of the asymmetric scattering transform has gain three from the
left-incident coordinate. -/
@[simp]
lemma twoPortChainRegressionAsymmetricScattering_right_action
    (incident : ModeAmplitude (Incident Unit ⊕ Incident Unit)) :
    (twoPortChainRegressionAsymmetricScattering.toLinearMap incident)
        (Sum.inr (Outgoing.mk ())) =
      3 * incident (Sum.inl (Incident.mk ())) := by
  norm_num [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    twoPortChainRegressionAsymmetricScattering, Fintype.sum_sum_type]
  rw [← Incident.channelEquiv.symm.sum_comp]
  simp

/-- The expected backward-first chain transform of the asymmetric scattering fixture. -/
def twoPortChainRegressionAsymmetricChain :
    ModeTransform (BackwardWave Unit ⊕ ForwardWave Unit)
      (BackwardWave Unit ⊕ ForwardWave Unit)
  | Sum.inl _, Sum.inl _ => 1 / 2
  | Sum.inl _, Sum.inr _ => 0
  | Sum.inr _, Sum.inl _ => 0
  | Sum.inr _, Sum.inr _ => 3

/-- The backward coordinate of the expected asymmetric chain transform has gain one half. -/
@[simp]
lemma twoPortChainRegressionAsymmetricChain_backward_action
    (left : BackwardFirstTravellingWaveState Unit) :
    (twoPortChainRegressionAsymmetricChain.toLinearMap left)
        (Sum.inl (BackwardWave.mk ())) =
      (1 / 2 : ℂ) * left (Sum.inl (BackwardWave.mk ())) := by
  norm_num [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    twoPortChainRegressionAsymmetricChain, Fintype.sum_sum_type,
    BackwardWave.fintype_card, ForwardWave.fintype_card]
  rw [← BackwardWave.channelEquiv.symm.sum_comp]
  simp

/-- The forward coordinate of the expected asymmetric chain transform has gain three. -/
@[simp]
lemma twoPortChainRegressionAsymmetricChain_forward_action
    (left : BackwardFirstTravellingWaveState Unit) :
    (twoPortChainRegressionAsymmetricChain.toLinearMap left)
        (Sum.inr (ForwardWave.mk ())) =
      3 * left (Sum.inr (ForwardWave.mk ())) := by
  norm_num [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    twoPortChainRegressionAsymmetricChain, Fintype.sum_sum_type,
    BackwardWave.fintype_card, ForwardWave.fintype_card]
  rw [← ForwardWave.channelEquiv.symm.sum_comp]
  simp

/-- Membership in the asymmetric scattering graph implies membership in its expected regrouped
chain graph. -/
lemma twoPortChainRegressionAsymmetricScattering_mem_expected
    (left right : BackwardFirstTravellingWaveState Unit)
    (hScattering : scatteringBackwardFirstLinearEquiv.symm (left, right) ∈
      twoPortChainRegressionAsymmetricScatteringBehavior) :
    (left, right) ∈ twoPortChainRegressionAsymmetricChain.toBehavior := by
  unfold twoPortChainRegressionAsymmetricScatteringBehavior at hScattering
  rw [ModeTransform.mem_toBehavior_iff_toLinearMap] at hScattering ⊢
  rw [scatteringBackwardFirstLinearEquiv_symm_apply] at hScattering
  apply WithLp.ofLp_injective 2
  funext index
  rcases index with ⟨⟨⟩⟩ | ⟨⟨⟩⟩
  · have hLeft := congrArg
      (fun outgoing : ModeAmplitude (Outgoing Unit ⊕ Outgoing Unit) =>
        outgoing (Sum.inl (Outgoing.mk ()))) hScattering
    rw [twoPortChainRegressionAsymmetricScattering_left_action] at hLeft
    change left (Sum.inl (BackwardWave.mk ())) =
      2 * right (Sum.inl (BackwardWave.mk ())) at hLeft
    rw [twoPortChainRegressionAsymmetricChain_backward_action]
    calc
      right (Sum.inl (BackwardWave.mk ())) =
          (1 / 2 : ℂ) * (2 * right (Sum.inl (BackwardWave.mk ()))) := by ring
      _ = (1 / 2 : ℂ) * left (Sum.inl (BackwardWave.mk ())) := by rw [← hLeft]
  · have hRight := congrArg
      (fun outgoing : ModeAmplitude (Outgoing Unit ⊕ Outgoing Unit) =>
        outgoing (Sum.inr (Outgoing.mk ()))) hScattering
    rw [twoPortChainRegressionAsymmetricScattering_right_action] at hRight
    change right (Sum.inr (ForwardWave.mk ())) =
      3 * left (Sum.inr (ForwardWave.mk ())) at hRight
    rw [twoPortChainRegressionAsymmetricChain_forward_action]
    exact hRight

/-- Membership in the expected asymmetric chain graph implies membership in its scattering graph
after ungrouping. -/
lemma twoPortChainRegressionAsymmetricChain_mem_scattering
    (left right : BackwardFirstTravellingWaveState Unit)
    (hChain : (left, right) ∈ twoPortChainRegressionAsymmetricChain.toBehavior) :
    scatteringBackwardFirstLinearEquiv.symm (left, right) ∈
      twoPortChainRegressionAsymmetricScatteringBehavior := by
  unfold twoPortChainRegressionAsymmetricScatteringBehavior
  rw [ModeTransform.mem_toBehavior_iff_toLinearMap] at hChain ⊢
  rw [scatteringBackwardFirstLinearEquiv_symm_apply]
  apply WithLp.ofLp_injective 2
  funext index
  rcases index with ⟨⟨⟩⟩ | ⟨⟨⟩⟩
  · have hBackward := congrArg
      (fun state : BackwardFirstTravellingWaveState Unit =>
        state (Sum.inl (BackwardWave.mk ()))) hChain
    rw [twoPortChainRegressionAsymmetricChain_backward_action] at hBackward
    rw [twoPortChainRegressionAsymmetricScattering_left_action]
    change left (Sum.inl (BackwardWave.mk ())) =
      2 * right (Sum.inl (BackwardWave.mk ()))
    calc
      left (Sum.inl (BackwardWave.mk ())) =
          2 * ((1 / 2 : ℂ) * left (Sum.inl (BackwardWave.mk ()))) := by ring
      _ = 2 * right (Sum.inl (BackwardWave.mk ())) := by rw [← hBackward]
  · have hForward := congrArg
      (fun state : BackwardFirstTravellingWaveState Unit =>
        state (Sum.inr (ForwardWave.mk ()))) hChain
    rw [twoPortChainRegressionAsymmetricChain_forward_action] at hForward
    rw [twoPortChainRegressionAsymmetricScattering_right_action]
    exact hForward

/-- Regrouping the asymmetric scattering graph gives its expected backward-first chain graph. -/
lemma twoPortChainRegressionAsymmetricScattering_toBackwardFirst :
    twoPortChainRegressionAsymmetricScatteringBehavior.toBackwardFirst =
        twoPortChainRegressionAsymmetricChain.toBehavior := by
  ext ⟨left, right⟩
  rw [TwoPortScatteringBehavior.mem_toBackwardFirst_iff]
  exact ⟨twoPortChainRegressionAsymmetricScattering_mem_expected left right,
    twoPortChainRegressionAsymmetricChain_mem_scattering left right⟩

/-- The asymmetric scattering graph has a left-to-right chain view. -/
lemma twoPortChainRegressionAsymmetricScattering_hasChainView :
    twoPortChainRegressionAsymmetricScatteringBehavior.toBackwardFirst.HasLeftToRightChainView := by
  rw [twoPortChainRegressionAsymmetricScattering_toBackwardFirst]
  exact twoPortChainRegressionAsymmetricChain.toBehavior_isFunctional

/-- Chain extraction recovers both asymmetric transmission gains in their intended coordinates. -/
lemma twoPortChainRegressionAsymmetricScattering_chainTransform :
    BackwardFirstTwoPortBehavior.leftToRightChainTransform
      twoPortChainRegressionAsymmetricScatteringBehavior.toBackwardFirst
      twoPortChainRegressionAsymmetricScattering_hasChainView =
        twoPortChainRegressionAsymmetricChain := by
  exact BackwardFirstTwoPortBehavior.leftToRightChainTransform_unique
    twoPortChainRegressionAsymmetricScatteringBehavior.toBackwardFirst
    twoPortChainRegressionAsymmetricScattering_hasChainView
    twoPortChainRegressionAsymmetricChain
    twoPortChainRegressionAsymmetricScattering_toBackwardFirst.symm

/-- The zero scattering graph has no left-to-right chain view. -/
lemma twoPortChainRegressionZeroScattering_not_hasChainView :
    ¬twoPortBehaviorRegressionZeroScattering.toBackwardFirst.HasLeftToRightChainView := by
  intro hChain
  exact twoPortBehaviorRegressionZeroScattering_not_backwardFirstSingleValued hChain.2

/-!

## B. Nonsymmetric chain-series order

-/

/-- The first nonsymmetric backward-first chain transform. -/
def twoPortChainRegressionFirst :
    ModeTransform (BackwardWave Unit ⊕ ForwardWave Unit)
      (BackwardWave Unit ⊕ ForwardWave Unit)
  | Sum.inl _, Sum.inl _ => 1
  | Sum.inl _, Sum.inr _ => 2
  | Sum.inr _, Sum.inl _ => 0
  | Sum.inr _, Sum.inr _ => 1

/-- The second nonsymmetric backward-first chain transform. -/
def twoPortChainRegressionSecond :
    ModeTransform (BackwardWave Unit ⊕ ForwardWave Unit)
      (BackwardWave Unit ⊕ ForwardWave Unit)
  | Sum.inl _, Sum.inl _ => 1
  | Sum.inl _, Sum.inr _ => 0
  | Sum.inr _, Sum.inl _ => 3
  | Sum.inr _, Sum.inr _ => 1

/-- The first transform presented as a relational two-port behavior. -/
def twoPortChainRegressionFirstBehavior : BackwardFirstTwoPortBehavior Unit Unit :=
  twoPortChainRegressionFirst.toBehavior

/-- The second transform presented as a relational two-port behavior. -/
def twoPortChainRegressionSecondBehavior : BackwardFirstTwoPortBehavior Unit Unit :=
  twoPortChainRegressionSecond.toBehavior

/-- The first graph behavior has a left-to-right chain view. -/
lemma twoPortChainRegressionFirstBehavior_hasChainView :
    twoPortChainRegressionFirstBehavior.HasLeftToRightChainView :=
  twoPortChainRegressionFirst.toBehavior_isFunctional

/-- The second graph behavior has a left-to-right chain view. -/
lemma twoPortChainRegressionSecondBehavior_hasChainView :
    twoPortChainRegressionSecondBehavior.HasLeftToRightChainView :=
  twoPortChainRegressionSecond.toBehavior_isFunctional

/-- Extracting the first transform's graph behavior recovers that transform. -/
lemma twoPortChainRegressionFirstBehavior_chainTransform :
    BackwardFirstTwoPortBehavior.leftToRightChainTransform
      twoPortChainRegressionFirstBehavior
      twoPortChainRegressionFirstBehavior_hasChainView =
        twoPortChainRegressionFirst := by
  exact BackwardFirstTwoPortBehavior.leftToRightChainTransform_unique
    twoPortChainRegressionFirstBehavior
    twoPortChainRegressionFirstBehavior_hasChainView
    twoPortChainRegressionFirst rfl

/-- Extracting the second transform's graph behavior recovers that transform. -/
lemma twoPortChainRegressionSecondBehavior_chainTransform :
    BackwardFirstTwoPortBehavior.leftToRightChainTransform
      twoPortChainRegressionSecondBehavior
      twoPortChainRegressionSecondBehavior_hasChainView =
        twoPortChainRegressionSecond := by
  exact BackwardFirstTwoPortBehavior.leftToRightChainTransform_unique
    twoPortChainRegressionSecondBehavior
    twoPortChainRegressionSecondBehavior_hasChainView
    twoPortChainRegressionSecond rfl

/-- Extracting the chain transform of the relational series gives later-times-earlier order. -/
lemma twoPortChainRegression_series_chainTransform :
    BackwardFirstTwoPortBehavior.leftToRightChainTransform
      (twoPortChainRegressionFirstBehavior.series
        twoPortChainRegressionSecondBehavior)
      (twoPortChainRegressionFirstBehavior_hasChainView.series
        twoPortChainRegressionSecondBehavior_hasChainView) =
      twoPortChainRegressionSecond * twoPortChainRegressionFirst := by
  calc
    _ = BackwardFirstTwoPortBehavior.leftToRightChainTransform
          twoPortChainRegressionSecondBehavior
          twoPortChainRegressionSecondBehavior_hasChainView *
        BackwardFirstTwoPortBehavior.leftToRightChainTransform
          twoPortChainRegressionFirstBehavior
          twoPortChainRegressionFirstBehavior_hasChainView :=
      BackwardFirstTwoPortBehavior.leftToRightChainTransform_series
        twoPortChainRegressionFirstBehavior
        twoPortChainRegressionSecondBehavior
        twoPortChainRegressionFirstBehavior_hasChainView
        twoPortChainRegressionSecondBehavior_hasChainView
    _ = _ := by
      rw [twoPortChainRegressionSecondBehavior_chainTransform,
        twoPortChainRegressionFirstBehavior_chainTransform]

/-- The later-times-earlier cascade product has exact upper-left entry one. -/
lemma twoPortChainRegression_later_left_product_entry :
    (twoPortChainRegressionSecond * twoPortChainRegressionFirst)
      (Sum.inl (BackwardWave.mk ())) (Sum.inl (BackwardWave.mk ())) = 1 := by
  simp [Matrix.mul_apply, twoPortChainRegressionFirst,
    twoPortChainRegressionSecond, Fintype.sum_sum_type,
    BackwardWave.fintype_card]

/-- The reverse product has exact upper-left entry seven. -/
lemma twoPortChainRegression_reverse_product_entry :
    (twoPortChainRegressionFirst * twoPortChainRegressionSecond)
      (Sum.inl (BackwardWave.mk ())) (Sum.inl (BackwardWave.mk ())) = 7 := by
  norm_num [Matrix.mul_apply, twoPortChainRegressionFirst,
    twoPortChainRegressionSecond, Fintype.sum_sum_type,
    BackwardWave.fintype_card, ForwardWave.fintype_card]

/-- The exact later-times-earlier chain cascade is not the reverse matrix product. -/
lemma twoPortChainRegression_series_chainTransform_ne_reverse :
    BackwardFirstTwoPortBehavior.leftToRightChainTransform
      (twoPortChainRegressionFirstBehavior.series
        twoPortChainRegressionSecondBehavior)
      (twoPortChainRegressionFirstBehavior_hasChainView.series
        twoPortChainRegressionSecondBehavior_hasChainView) ≠
      twoPortChainRegressionFirst * twoPortChainRegressionSecond := by
  rw [twoPortChainRegression_series_chainTransform]
  intro hProducts
  have hEntry := congrFun
    (congrFun hProducts (Sum.inl (BackwardWave.mk ())))
      (Sum.inl (BackwardWave.mk ()))
  rw [twoPortChainRegression_later_left_product_entry,
    twoPortChainRegression_reverse_product_entry] at hEntry
  norm_num at hEntry

end

end Optics
