/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Components.DirectionalCouplerPhysicalRegression
public import Physlib.Optics.Network.ScatteringComponentFamily

/-!
# Component-family regression for the physical directional coupler

## i. Overview

This file inserts the physical four-port coupler into a one-component
`ScatteringComponentFamily`. Aggregate fixtures pin physical-port restriction, assembled action,
order-free componentwise membership, assembled-graph membership, and wrong-phase rejection.

## ii. Key results

- `directionalCouplerPhysicalFamilyRegression_assembled_action`: exact assembled action.
- `directionalCouplerPhysicalFamilyRegression_componentwise_mem`: order-free local membership.
- `directionalCouplerPhysicalFamilyRegression_wrong_not_componentwise`: hostile local rejection.

## iii. Table of contents

- A. One-component family and aggregate states
- B. Component restrictions and assembled action
- C. Relational membership and hostile rejection

## iv. References

This is a source-neutral network-integration regression.
-/

@[expose] public section

namespace Optics
noncomputable section
namespace DirectionalCoupler
/-!
## A. One-component family and aggregate states
-/
/-- A one-component family using the public four-port scattering law directly. -/
abbrev directionalCouplerPhysicalRegressionComponentFamily : ScatteringComponentFamily where
  Component := Unit
  portFamily := fun _ => portFamily Unit
  scattering := fun _ => physicalScattering directionalCouplerRegressionParameters Unit

/-- The aggregate one-component physical channel family is finite. -/
local instance : Fintype
    directionalCouplerPhysicalRegressionComponentFamily.aggregatePortModeFamily.Channel :=
  Fintype.ofEquiv directionalCouplerPhysicalRegressionComponentFamily.IndexedChannel
    directionalCouplerPhysicalRegressionComponentFamily.channelEquiv
/-- The aggregate channel coordinates carry decidable equality. -/
local instance : DecidableEq
    directionalCouplerPhysicalRegressionComponentFamily.aggregatePortModeFamily.Channel :=
  directionalCouplerPhysicalRegressionComponentFamily.channelEquiv.symm.decidableEq

/-- The aggregate incident fixture obtained by adding the unique component tag. -/
def directionalCouplerPhysicalFamilyRegressionIncident :
    ModeAmplitude (Incident
      directionalCouplerPhysicalRegressionComponentFamily.aggregatePortModeFamily.Channel) :=
  WithLp.toLp 2 fun
    | ⟨⟨⟨(), port⟩, mode⟩⟩ =>
        directionalCouplerPhysicalRegressionIncident (Incident.mk ⟨port, mode⟩)

/-- The aggregate exact output obtained by adding the unique component tag. -/
def directionalCouplerPhysicalFamilyRegressionOutgoing :
    ModeAmplitude (Outgoing
      directionalCouplerPhysicalRegressionComponentFamily.aggregatePortModeFamily.Channel) :=
  WithLp.toLp 2 fun
    | ⟨⟨⟨(), port⟩, mode⟩⟩ =>
        directionalCouplerPhysicalRegressionOutgoing (Outgoing.mk ⟨port, mode⟩)

/-- The aggregate wrong-phase output obtained by adding the unique component tag. -/
def directionalCouplerPhysicalFamilyRegressionWrongOutgoing :
    ModeAmplitude (Outgoing
      directionalCouplerPhysicalRegressionComponentFamily.aggregatePortModeFamily.Channel) :=
  WithLp.toLp 2 fun
    | ⟨⟨⟨(), port⟩, mode⟩⟩ =>
        directionalCouplerPhysicalRegressionWrongPhase (Outgoing.mk ⟨port, mode⟩)

/-- The component embedding retains the first physical left port. -/
lemma directionalCouplerPhysicalFamilyRegression_embedding_leftFirst :
    directionalCouplerPhysicalRegressionComponentFamily.componentChannelEmbedding ()
        ⟨Port.leftFirst, ()⟩ =
      ⟨⟨(), Port.leftFirst⟩, ()⟩ := rfl

/-!
## B. Component restrictions and assembled action
-/
/-- Restricting the aggregate incident state recovers the local physical fixture. -/
lemma directionalCouplerPhysicalFamilyRegression_incident_restrict :
    directionalCouplerPhysicalFamilyRegressionIncident.restrictEmbedding
        (Incident.relabelEmbedding
          (directionalCouplerPhysicalRegressionComponentFamily.componentChannelEmbedding ())) =
      directionalCouplerPhysicalRegressionIncident := by
  apply WithLp.ofLp_injective 2
  funext input
  rcases input with ⟨⟨port, mode⟩⟩
  rfl

/-- Restricting the aggregate exact output recovers the local physical fixture. -/
lemma directionalCouplerPhysicalFamilyRegression_outgoing_restrict :
    directionalCouplerPhysicalFamilyRegressionOutgoing.restrictEmbedding
        (Outgoing.relabelEmbedding
          (directionalCouplerPhysicalRegressionComponentFamily.componentChannelEmbedding ())) =
      directionalCouplerPhysicalRegressionOutgoing := by
  apply WithLp.ofLp_injective 2
  funext output
  rcases output with ⟨⟨port, mode⟩⟩
  rfl

/-- Restricting the hostile aggregate output recovers the local wrong-phase fixture. -/
lemma directionalCouplerPhysicalFamilyRegression_wrong_restrict :
    directionalCouplerPhysicalFamilyRegressionWrongOutgoing.restrictEmbedding
        (Outgoing.relabelEmbedding
          (directionalCouplerPhysicalRegressionComponentFamily.componentChannelEmbedding ())) =
      directionalCouplerPhysicalRegressionWrongPhase := by
  apply WithLp.ofLp_injective 2
  funext output
  rcases output with ⟨⟨port, mode⟩⟩
  rfl

/-- The assembled scattering matrix produces the exact aggregate output. -/
lemma directionalCouplerPhysicalFamilyRegression_assembled_action :
    ModeTransform.toLinearMap (ScatteringMatrix.toOrientedModeTransform
        (ScatteringComponentFamily.assembledScatteringMatrix
          directionalCouplerPhysicalRegressionComponentFamily))
        directionalCouplerPhysicalFamilyRegressionIncident =
      directionalCouplerPhysicalFamilyRegressionOutgoing := by
  apply WithLp.ofLp_injective 2
  funext endpoint
  rcases endpoint with ⟨⟨⟨component, port⟩, mode⟩⟩
  rcases component with ⟨⟩
  have hLocal := congrArg
    (fun amplitude => amplitude (Outgoing.mk ⟨port, mode⟩))
    (ScatteringComponentFamily.assembledScatteringMatrix_toOrientedModeTransform_apply_component
      directionalCouplerPhysicalRegressionComponentFamily
      directionalCouplerPhysicalFamilyRegressionIncident ())
  rw [directionalCouplerPhysicalFamilyRegression_incident_restrict,
    directionalCouplerPhysicalRegression_scattering_action] at hLocal
  exact hLocal

/-!
## C. Relational membership and hostile rejection
-/
/-- The aggregate state satisfies the order-free local component relation. -/
lemma directionalCouplerPhysicalFamilyRegression_componentwise_mem :
    (directionalCouplerPhysicalFamilyRegressionIncident,
      directionalCouplerPhysicalFamilyRegressionOutgoing) ∈
        ScatteringComponentFamily.componentwiseBehavior
          directionalCouplerPhysicalRegressionComponentFamily := by
  rw [ScatteringComponentFamily.mem_componentwiseBehavior_iff_equations]
  intro component
  rcases component with ⟨⟩
  rw [directionalCouplerPhysicalFamilyRegression_incident_restrict,
    directionalCouplerPhysicalFamilyRegression_outgoing_restrict]
  exact directionalCouplerPhysicalRegression_scattering_action.symm

/-- The aggregate state belongs to the assembled scattering graph. -/
lemma directionalCouplerPhysicalFamilyRegression_assembled_mem :
    (directionalCouplerPhysicalFamilyRegressionIncident,
      directionalCouplerPhysicalFamilyRegressionOutgoing) ∈
        ModeTransform.toBehavior (ScatteringMatrix.toOrientedModeTransform
          (ScatteringComponentFamily.assembledScatteringMatrix
            directionalCouplerPhysicalRegressionComponentFamily)) := by
  rw [ModeTransform.mem_toBehavior_iff_toLinearMap]
  exact directionalCouplerPhysicalFamilyRegression_assembled_action.symm

/-- The wrong-phase aggregate output violates the local component relation. -/
lemma directionalCouplerPhysicalFamilyRegression_wrong_not_componentwise :
    (directionalCouplerPhysicalFamilyRegressionIncident,
      directionalCouplerPhysicalFamilyRegressionWrongOutgoing) ∉
        ScatteringComponentFamily.componentwiseBehavior
          directionalCouplerPhysicalRegressionComponentFamily := by
  intro hWrong
  have hLocal :=
    (ScatteringComponentFamily.mem_componentwiseBehavior_iff_equations
      directionalCouplerPhysicalRegressionComponentFamily
      directionalCouplerPhysicalFamilyRegressionIncident
      directionalCouplerPhysicalFamilyRegressionWrongOutgoing).mp hWrong ()
  rw [directionalCouplerPhysicalFamilyRegression_incident_restrict,
    directionalCouplerPhysicalFamilyRegression_wrong_restrict,
    directionalCouplerPhysicalRegression_scattering_action] at hLocal
  apply directionalCouplerPhysicalRegression_wrongPhase_not_mem
  rw [hLocal]
  exact directionalCouplerPhysicalRegression_mem

/-- The wrong-phase aggregate output also violates the assembled scattering graph. -/
lemma directionalCouplerPhysicalFamilyRegression_wrong_not_assembled :
    (directionalCouplerPhysicalFamilyRegressionIncident,
      directionalCouplerPhysicalFamilyRegressionWrongOutgoing) ∉
        ModeTransform.toBehavior (ScatteringMatrix.toOrientedModeTransform
          (ScatteringComponentFamily.assembledScatteringMatrix
            directionalCouplerPhysicalRegressionComponentFamily)) := by
  rw [
    ← ScatteringComponentFamily.componentwiseBehavior_eq_assembledScatteringMatrix_toBehavior]
  exact directionalCouplerPhysicalFamilyRegression_wrong_not_componentwise

end DirectionalCoupler
end
end Optics
