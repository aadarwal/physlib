/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.ScatteringComponentFamily

/-!
# Regression tests for typed scattering-component families

## i. Overview

This file assembles two genuinely heterogeneous scattering components. The first has one local
port carrying one mode. The second reuses the same local port label but carries two modes. Their
component tags therefore have to survive aggregate-port construction to keep the physical ports
and all three channels distinct.

The scalar block and every entry of a nonsymmetric two-mode block are distinct and nonreal. Exact
tests pin the dependent-sum reassociation, both cross-component zero directions, row/column
orientation through nominal incident and outgoing endpoints, and the action on an input supported
at every aggregate channel.

## ii. Scope

The arbitrary complex coefficients are algebraic sentinels. They make no losslessness, passivity,
reciprocity, physical-realizability, source, detector, interconnection, or feedback claim.
Cross-component zeros express absence of direct component scattering before wiring; they do not
model termination or absorption.

## iii. Table of contents

- A. A heterogeneous two-component fixture
- B. Aggregate channel reassociation
- C. Exact block-diagonal entries
- D. Mixed-amplitude action

-/

@[expose] public section

namespace Optics

noncomputable section

/-!

## A. A heterogeneous two-component fixture

-/

/-- The first component has one mode, while the second has two modes on the same local port
label. -/
abbrev scatteringComponentFamilyRegressionPortFamily : Bool → PortModeFamily
  | false =>
      { Port := Unit
        Mode := fun _ => Unit }
  | true =>
      { Port := Unit
        Mode := fun _ => Bool }

/-- The scalar and nonsymmetric two-mode scattering laws used by the component-family regression. -/
def scatteringComponentFamilyRegressionScattering :
    (component : Bool) →
      ScatteringMatrix (scatteringComponentFamilyRegressionPortFamily component).Channel
  | false =>
      { toModeTransform := fun _ _ => 1 + 2 * Complex.I }
  | true =>
      { toModeTransform := fun output input =>
          match output.2, input.2 with
          | false, false => 3 - Complex.I
          | false, true => 4 + 2 * Complex.I
          | true, false => 5 - 3 * Complex.I
          | true, true => 6 + 4 * Complex.I }

/-- The heterogeneous two-component scattering family. -/
abbrev scatteringComponentFamilyRegression : ScatteringComponentFamily where
  Component := Bool
  portFamily := scatteringComponentFamilyRegressionPortFamily
  scattering := scatteringComponentFamilyRegressionScattering

/-- The scalar component's only local channel. -/
abbrev scatteringComponentFamilyRegressionScalarLocal :
    (scatteringComponentFamilyRegression.portFamily false).Channel := ⟨(), ()⟩

/-- The first local channel of the two-mode component. -/
abbrev scatteringComponentFamilyRegressionLeftLocal :
    (scatteringComponentFamilyRegression.portFamily true).Channel := ⟨(), false⟩

/-- The second local channel of the two-mode component. -/
abbrev scatteringComponentFamilyRegressionRightLocal :
    (scatteringComponentFamilyRegression.portFamily true).Channel := ⟨(), true⟩

/-- The scalar component's local channel type has exactly its displayed channel. -/
local instance scatteringComponentFamilyRegressionScalarLocalUnique :
    Unique (scatteringComponentFamilyRegression.portFamily false).Channel where
  default := scatteringComponentFamilyRegressionScalarLocal
  uniq := by
    rintro ⟨port, mode⟩
    cases port
    cases mode
    rfl

/-- The aggregate channel owned by the scalar component. -/
abbrev scatteringComponentFamilyRegressionScalar :
    scatteringComponentFamilyRegression.aggregatePortModeFamily.Channel :=
  ⟨⟨false, ()⟩, ()⟩

/-- The first aggregate channel owned by the two-mode component. -/
abbrev scatteringComponentFamilyRegressionLeft :
    scatteringComponentFamilyRegression.aggregatePortModeFamily.Channel :=
  ⟨⟨true, ()⟩, false⟩

/-- The second aggregate channel owned by the two-mode component. -/
abbrev scatteringComponentFamilyRegressionRight :
    scatteringComponentFamilyRegression.aggregatePortModeFamily.Channel :=
  ⟨⟨true, ()⟩, true⟩

/-- Every local channel family in the regression is finite. -/
local instance scatteringComponentFamilyRegressionLocalChannelFintype (component : Bool) :
    Fintype (scatteringComponentFamilyRegression.portFamily component).Channel := by
  cases component <;> infer_instance

/-- Every local channel family in the regression has decidable equality. -/
local instance scatteringComponentFamilyRegressionLocalChannelDecidableEq (component : Bool) :
    DecidableEq (scatteringComponentFamilyRegression.portFamily component).Channel := by
  cases component <;> infer_instance

/-- The aggregate regression channels are finite by their explicit reassociation with local
component channels. -/
local instance scatteringComponentFamilyRegressionAggregateChannelFintype :
    Fintype scatteringComponentFamilyRegression.aggregatePortModeFamily.Channel :=
  Fintype.ofEquiv scatteringComponentFamilyRegression.IndexedChannel
    scatteringComponentFamilyRegression.channelEquiv

/-- Aggregate regression channels inherit decidable equality from indexed local channels. -/
local instance scatteringComponentFamilyRegressionAggregateChannelDecidableEq :
    DecidableEq scatteringComponentFamilyRegression.aggregatePortModeFamily.Channel :=
  Classical.decEq _

/-!

## B. Aggregate channel reassociation

-/

/-- Reassociation sends the scalar local channel to the explicitly tagged aggregate channel. -/
lemma scatteringComponentFamilyRegression_channelEquiv_scalar :
    scatteringComponentFamilyRegression.channelEquiv
        ⟨false, scatteringComponentFamilyRegressionScalarLocal⟩ =
      scatteringComponentFamilyRegressionScalar := rfl

/-- Reassociation sends the first two-mode local channel to its aggregate channel. -/
lemma scatteringComponentFamilyRegression_channelEquiv_left :
    scatteringComponentFamilyRegression.channelEquiv
        ⟨true, scatteringComponentFamilyRegressionLeftLocal⟩ =
      scatteringComponentFamilyRegressionLeft := rfl

/-- Reassociation sends the second two-mode local channel to its aggregate channel. -/
lemma scatteringComponentFamilyRegression_channelEquiv_right :
    scatteringComponentFamilyRegression.channelEquiv
        ⟨true, scatteringComponentFamilyRegressionRightLocal⟩ =
      scatteringComponentFamilyRegressionRight := rfl

/-- The scalar aggregate channel differs from the first two-mode channel. -/
@[simp]
lemma scatteringComponentFamilyRegression_scalar_ne_left :
    scatteringComponentFamilyRegressionScalar ≠
      scatteringComponentFamilyRegressionLeft := by
  intro h
  have hComponent := congrArg (fun channel => channel.1.1) h
  simp at hComponent

/-- The scalar aggregate channel differs from the second two-mode channel. -/
@[simp]
lemma scatteringComponentFamilyRegression_scalar_ne_right :
    scatteringComponentFamilyRegressionScalar ≠
      scatteringComponentFamilyRegressionRight := by
  intro h
  have hComponent := congrArg (fun channel => channel.1.1) h
  simp at hComponent

/-- The two local modes remain distinct after aggregate channel reassociation. -/
@[simp]
lemma scatteringComponentFamilyRegression_left_ne_right :
    scatteringComponentFamilyRegressionLeft ≠
      scatteringComponentFamilyRegressionRight := by
  intro h
  have hMode : HEq (false : Bool) true := (Sigma.mk.inj_iff.mp h).2
  exact Bool.noConfusion (eq_of_heq hMode)

/-!

## C. Exact block-diagonal entries

-/

/-- The scalar component retains its nonreal scattering coefficient. -/
lemma scatteringComponentFamilyRegression_entry_scalar :
    scatteringComponentFamilyRegression.assembledScatteringMatrix.toOrientedModeTransform
        (Outgoing.mk scatteringComponentFamilyRegressionScalar)
        (Incident.mk scatteringComponentFamilyRegressionScalar) =
      1 + 2 * Complex.I := by
  rw [ScatteringMatrix.toOrientedModeTransform_apply]
  exact scatteringComponentFamilyRegression.assembledScatteringMatrix_entry_same
    false scatteringComponentFamilyRegressionScalarLocal
      scatteringComponentFamilyRegressionScalarLocal

/-- The upper-left entry of the two-mode component retains its local coefficient. -/
lemma scatteringComponentFamilyRegression_entry_left_left :
    scatteringComponentFamilyRegression.assembledScatteringMatrix.toOrientedModeTransform
        (Outgoing.mk scatteringComponentFamilyRegressionLeft)
        (Incident.mk scatteringComponentFamilyRegressionLeft) =
      3 - Complex.I := by
  rw [ScatteringMatrix.toOrientedModeTransform_apply]
  exact scatteringComponentFamilyRegression.assembledScatteringMatrix_entry_same
    true scatteringComponentFamilyRegressionLeftLocal
      scatteringComponentFamilyRegressionLeftLocal

/-- The upper-right entry of the two-mode component fixes its row/column orientation. -/
lemma scatteringComponentFamilyRegression_entry_left_right :
    scatteringComponentFamilyRegression.assembledScatteringMatrix.toOrientedModeTransform
        (Outgoing.mk scatteringComponentFamilyRegressionLeft)
        (Incident.mk scatteringComponentFamilyRegressionRight) =
      4 + 2 * Complex.I := by
  rw [ScatteringMatrix.toOrientedModeTransform_apply]
  exact scatteringComponentFamilyRegression.assembledScatteringMatrix_entry_same
    true scatteringComponentFamilyRegressionLeftLocal
      scatteringComponentFamilyRegressionRightLocal

/-- The lower-left entry differs from the upper-right entry and catches transposition. -/
lemma scatteringComponentFamilyRegression_entry_right_left :
    scatteringComponentFamilyRegression.assembledScatteringMatrix.toOrientedModeTransform
        (Outgoing.mk scatteringComponentFamilyRegressionRight)
        (Incident.mk scatteringComponentFamilyRegressionLeft) =
      5 - 3 * Complex.I := by
  rw [ScatteringMatrix.toOrientedModeTransform_apply]
  exact scatteringComponentFamilyRegression.assembledScatteringMatrix_entry_same
    true scatteringComponentFamilyRegressionRightLocal
      scatteringComponentFamilyRegressionLeftLocal

/-- The lower-right entry of the two-mode component retains its local coefficient. -/
lemma scatteringComponentFamilyRegression_entry_right_right :
    scatteringComponentFamilyRegression.assembledScatteringMatrix.toOrientedModeTransform
        (Outgoing.mk scatteringComponentFamilyRegressionRight)
        (Incident.mk scatteringComponentFamilyRegressionRight) =
      6 + 4 * Complex.I := by
  rw [ScatteringMatrix.toOrientedModeTransform_apply]
  exact scatteringComponentFamilyRegression.assembledScatteringMatrix_entry_same
    true scatteringComponentFamilyRegressionRightLocal
      scatteringComponentFamilyRegressionRightLocal

/-- The scalar component does not scatter directly into the two-mode component. -/
lemma scatteringComponentFamilyRegression_entry_left_scalar :
    scatteringComponentFamilyRegression.assembledScatteringMatrix.toOrientedModeTransform
        (Outgoing.mk scatteringComponentFamilyRegressionLeft)
        (Incident.mk scatteringComponentFamilyRegressionScalar) = 0 := by
  rw [ScatteringMatrix.toOrientedModeTransform_apply]
  exact scatteringComponentFamilyRegression.assembledScatteringMatrix_entry_of_ne
    (by decide) scatteringComponentFamilyRegressionLeftLocal
      scatteringComponentFamilyRegressionScalarLocal

/-- The scalar component also has no direct input into the second two-mode output. -/
lemma scatteringComponentFamilyRegression_entry_right_scalar :
    scatteringComponentFamilyRegression.assembledScatteringMatrix.toOrientedModeTransform
        (Outgoing.mk scatteringComponentFamilyRegressionRight)
        (Incident.mk scatteringComponentFamilyRegressionScalar) = 0 := by
  rw [ScatteringMatrix.toOrientedModeTransform_apply]
  exact scatteringComponentFamilyRegression.assembledScatteringMatrix_entry_of_ne
    (by decide) scatteringComponentFamilyRegressionRightLocal
      scatteringComponentFamilyRegressionScalarLocal

/-- The first two-mode input has no direct output in the scalar component. -/
lemma scatteringComponentFamilyRegression_entry_scalar_left :
    scatteringComponentFamilyRegression.assembledScatteringMatrix.toOrientedModeTransform
        (Outgoing.mk scatteringComponentFamilyRegressionScalar)
        (Incident.mk scatteringComponentFamilyRegressionLeft) = 0 := by
  rw [ScatteringMatrix.toOrientedModeTransform_apply]
  exact scatteringComponentFamilyRegression.assembledScatteringMatrix_entry_of_ne
    (by decide) scatteringComponentFamilyRegressionScalarLocal
      scatteringComponentFamilyRegressionLeftLocal

/-- The two-mode component does not scatter directly into the scalar component. -/
lemma scatteringComponentFamilyRegression_entry_scalar_right :
    scatteringComponentFamilyRegression.assembledScatteringMatrix.toOrientedModeTransform
        (Outgoing.mk scatteringComponentFamilyRegressionScalar)
        (Incident.mk scatteringComponentFamilyRegressionRight) = 0 := by
  rw [ScatteringMatrix.toOrientedModeTransform_apply]
  exact scatteringComponentFamilyRegression.assembledScatteringMatrix_entry_of_ne
    (by decide) scatteringComponentFamilyRegressionScalarLocal
      scatteringComponentFamilyRegressionRightLocal

/-!

## D. Mixed-amplitude action

-/

/-- An aggregate incident amplitude with a nonzero coefficient on every component channel. -/
def scatteringComponentFamilyRegressionInput :
    ModeAmplitude scatteringComponentFamilyRegression.aggregatePortModeFamily.Channel :=
  PiLp.single 2 scatteringComponentFamilyRegressionScalar (2 - Complex.I) +
    PiLp.single 2 scatteringComponentFamilyRegressionLeft (1 + Complex.I) +
      PiLp.single 2 scatteringComponentFamilyRegressionRight (3 + 2 * Complex.I)

/-- The mixed input retains its scalar-component coefficient. -/
@[simp]
lemma scatteringComponentFamilyRegressionInput_scalar :
    scatteringComponentFamilyRegressionInput scatteringComponentFamilyRegressionScalar =
      2 - Complex.I := by
  simp [scatteringComponentFamilyRegressionInput]

/-- The mixed input retains its first two-mode coefficient. -/
@[simp]
lemma scatteringComponentFamilyRegressionInput_left :
    scatteringComponentFamilyRegressionInput scatteringComponentFamilyRegressionLeft =
      1 + Complex.I := by
  simp [scatteringComponentFamilyRegressionInput]

/-- The mixed input retains its second two-mode coefficient. -/
@[simp]
lemma scatteringComponentFamilyRegressionInput_right :
    scatteringComponentFamilyRegressionInput scatteringComponentFamilyRegressionRight =
      3 + 2 * Complex.I := by
  simp [scatteringComponentFamilyRegressionInput]

/-- The restriction of the mixed input to the two-mode component, in local channel coordinates. -/
def scatteringComponentFamilyRegressionTwoModeInput :
    ModeAmplitude (scatteringComponentFamilyRegression.portFamily true).Channel :=
  WithLp.toLp 2 fun channel =>
    if channel.2 then 3 + 2 * Complex.I else 1 + Complex.I

/-- Restricting the aggregate input to the two-mode component recovers both local coefficients. -/
lemma scatteringComponentFamilyRegressionInput_restrict_twoMode :
    scatteringComponentFamilyRegressionInput.restrictEmbedding
        (scatteringComponentFamilyRegression.componentChannelEmbedding true) =
      scatteringComponentFamilyRegressionTwoModeInput := by
  apply WithLp.ofLp_injective 2
  funext channel
  rcases channel with ⟨port, mode⟩
  cases port
  cases mode
  · change scatteringComponentFamilyRegressionInput
      scatteringComponentFamilyRegressionLeft = 1 + Complex.I
    exact scatteringComponentFamilyRegressionInput_left
  · change scatteringComponentFamilyRegressionInput
      scatteringComponentFamilyRegressionRight = 3 + 2 * Complex.I
    exact scatteringComponentFamilyRegressionInput_right

/-- The scalar block acts only on the scalar input coefficient. -/
lemma scatteringComponentFamilyRegression_action_scalar :
    scatteringComponentFamilyRegression.assembledScatteringMatrix.toModeTransform.toLinearMap
        scatteringComponentFamilyRegressionInput scatteringComponentFamilyRegressionScalar =
      4 + 3 * Complex.I := by
  change scatteringComponentFamilyRegression.assembledScatteringMatrix.toModeTransform.toLinearMap
      scatteringComponentFamilyRegressionInput
        (scatteringComponentFamilyRegression.componentChannelEmbedding false
          scatteringComponentFamilyRegressionScalarLocal) = _
  rw [scatteringComponentFamilyRegression.assembledScatteringMatrix_apply_component]
  have hInput :
      scatteringComponentFamilyRegressionInput.restrictEmbedding
          (scatteringComponentFamilyRegression.componentChannelEmbedding false) =
        WithLp.toLp 2 (fun _ => 2 - Complex.I) := by
    apply WithLp.ofLp_injective 2
    funext channel
    rcases channel with ⟨port, mode⟩
    cases port
    cases mode
    change scatteringComponentFamilyRegressionInput
        scatteringComponentFamilyRegressionScalar = 2 - Complex.I
    exact scatteringComponentFamilyRegressionInput_scalar
  rw [hInput]
  simp only [ModeTransform.toLinearMap, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    Fintype.sum_unique]
  change (1 + 2 * Complex.I) * (2 - Complex.I) = 4 + 3 * Complex.I
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The first two-mode output uses its nonsymmetric local matrix row and no scalar input. -/
lemma scatteringComponentFamilyRegression_action_left :
    scatteringComponentFamilyRegression.assembledScatteringMatrix.toModeTransform.toLinearMap
        scatteringComponentFamilyRegressionInput scatteringComponentFamilyRegressionLeft =
      12 + 16 * Complex.I := by
  change scatteringComponentFamilyRegression.assembledScatteringMatrix.toModeTransform.toLinearMap
      scatteringComponentFamilyRegressionInput
        (scatteringComponentFamilyRegression.componentChannelEmbedding true
          scatteringComponentFamilyRegressionLeftLocal) = _
  rw [scatteringComponentFamilyRegression.assembledScatteringMatrix_apply_component,
    scatteringComponentFamilyRegressionInput_restrict_twoMode]
  simp only [ModeTransform.toLinearMap, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    Fintype.sum_sigma, Fintype.sum_unique, Fintype.sum_bool]
  change (4 + 2 * Complex.I) * (3 + 2 * Complex.I) +
      (3 - Complex.I) * (1 + Complex.I) = 12 + 16 * Complex.I
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The second two-mode output uses the distinct lower row and no scalar input. -/
lemma scatteringComponentFamilyRegression_action_right :
    scatteringComponentFamilyRegression.assembledScatteringMatrix.toModeTransform.toLinearMap
        scatteringComponentFamilyRegressionInput scatteringComponentFamilyRegressionRight =
      18 + 26 * Complex.I := by
  change scatteringComponentFamilyRegression.assembledScatteringMatrix.toModeTransform.toLinearMap
      scatteringComponentFamilyRegressionInput
        (scatteringComponentFamilyRegression.componentChannelEmbedding true
          scatteringComponentFamilyRegressionRightLocal) = _
  rw [scatteringComponentFamilyRegression.assembledScatteringMatrix_apply_component,
    scatteringComponentFamilyRegressionInput_restrict_twoMode]
  simp only [ModeTransform.toLinearMap, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    Fintype.sum_sigma, Fintype.sum_unique, Fintype.sum_bool]
  change (6 + 4 * Complex.I) * (3 + 2 * Complex.I) +
      (5 - 3 * Complex.I) * (1 + Complex.I) = 18 + 26 * Complex.I
  ring_nf
  rw [Complex.I_sq]
  ring

end

end Optics
