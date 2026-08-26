/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Components.MatchedPropagationPhysicalRegression
public import Physlib.Optics.Network.ScatteringComponentFamily

/-!
# Component-family regression for physical matched propagation

## i. Overview

This file inserts fixed-carrier physical scattering into a one-component
`ScatteringComponentFamily`. Direct aggregate fixtures pin component restriction, assembled
action, graph membership, and rejection of a wrong-phase output.

## ii. Key results

- `matchedPropagationPhysicalFamilyRegression_assembled_action`: exact assembled scattering action.
- `matchedPropagationPhysicalFamilyRegression_assembled_mem`: assembled-graph membership.
- `matchedPropagationPhysicalFamilyRegression_wrong_not_componentwise`: hostile local rejection.

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
namespace MatchedPropagation
/-!
## A. One-component family and aggregate states
-/

/-- A one-component family using the public physical ports and scattering law directly. -/
abbrev matchedPropagationPhysicalRegressionComponentFamily : ScatteringComponentFamily where
  Component := Unit
  portFamily := fun _ => portFamily (Fin 2)
  scattering := fun _ =>
    physicalScattering matchedPropagationRegressionParameters (Fin 2)

/-- The aggregate one-component physical channel family is finite. -/
local instance : Fintype
    matchedPropagationPhysicalRegressionComponentFamily.aggregatePortModeFamily.Channel :=
  Fintype.ofEquiv matchedPropagationPhysicalRegressionComponentFamily.IndexedChannel
    matchedPropagationPhysicalRegressionComponentFamily.channelEquiv
/-- The aggregate channel coordinates carry decidable equality. -/
local instance : DecidableEq
    matchedPropagationPhysicalRegressionComponentFamily.aggregatePortModeFamily.Channel :=
  matchedPropagationPhysicalRegressionComponentFamily.channelEquiv.symm.decidableEq

/-- The aggregate incident state obtained by adding the unique component tag. -/
def matchedPropagationPhysicalFamilyRegressionIncident :
    ModeAmplitude (Incident
      matchedPropagationPhysicalRegressionComponentFamily.aggregatePortModeFamily.Channel) :=
  WithLp.toLp 2 fun
    | ⟨⟨⟨(), port⟩, mode⟩⟩ =>
        matchedPropagationPhysicalRegressionIncident (Incident.mk ⟨port, mode⟩)
/-- The aggregate exact output obtained by adding the unique component tag. -/
def matchedPropagationPhysicalFamilyRegressionOutgoing :
    ModeAmplitude (Outgoing
      matchedPropagationPhysicalRegressionComponentFamily.aggregatePortModeFamily.Channel) :=
  WithLp.toLp 2 fun
    | ⟨⟨⟨(), port⟩, mode⟩⟩ =>
        matchedPropagationPhysicalRegressionOutgoing (Outgoing.mk ⟨port, mode⟩)

/-- The aggregate wrong-phase output obtained by adding the unique component tag. -/
def matchedPropagationPhysicalFamilyRegressionWrongOutgoing :
    ModeAmplitude (Outgoing
      matchedPropagationPhysicalRegressionComponentFamily.aggregatePortModeFamily.Channel) :=
  WithLp.toLp 2 fun
    | ⟨⟨⟨(), port⟩, mode⟩⟩ =>
        matchedPropagationPhysicalRegressionWrongPhase (Outgoing.mk ⟨port, mode⟩)

/-- The component embedding retains the left physical port and its local mode. -/
lemma matchedPropagationPhysicalFamilyRegression_embedding_left :
    matchedPropagationPhysicalRegressionComponentFamily.componentChannelEmbedding ()
        ⟨Port.left, (0 : Fin 2)⟩ =
      ⟨⟨(), Port.left⟩, (0 : Fin 2)⟩ := rfl
/-!
## B. Component restrictions and assembled action
-/

/-- Restricting the aggregate incident state recovers the local physical incident fixture. -/
lemma matchedPropagationPhysicalFamilyRegression_incident_restrict :
    matchedPropagationPhysicalFamilyRegressionIncident.restrictEmbedding
        (Incident.relabelEmbedding
          (matchedPropagationPhysicalRegressionComponentFamily.componentChannelEmbedding ())) =
      matchedPropagationPhysicalRegressionIncident := by
  apply WithLp.ofLp_injective 2
  funext input
  rcases input with ⟨⟨port, mode⟩⟩
  rfl

/-- Restricting the aggregate exact output recovers the local physical output fixture. -/
lemma matchedPropagationPhysicalFamilyRegression_outgoing_restrict :
    matchedPropagationPhysicalFamilyRegressionOutgoing.restrictEmbedding
        (Outgoing.relabelEmbedding
          (matchedPropagationPhysicalRegressionComponentFamily.componentChannelEmbedding ())) =
      matchedPropagationPhysicalRegressionOutgoing := by
  apply WithLp.ofLp_injective 2
  funext output
  rcases output with ⟨⟨port, mode⟩⟩
  rfl

/-- Restricting the hostile aggregate output recovers the local wrong-phase fixture. -/
lemma matchedPropagationPhysicalFamilyRegression_wrong_restrict :
    matchedPropagationPhysicalFamilyRegressionWrongOutgoing.restrictEmbedding
        (Outgoing.relabelEmbedding
          (matchedPropagationPhysicalRegressionComponentFamily.componentChannelEmbedding ())) =
      matchedPropagationPhysicalRegressionWrongPhase := by
  apply WithLp.ofLp_injective 2
  funext output
  rcases output with ⟨⟨port, mode⟩⟩
  rfl

/-- The assembled scattering matrix produces the exact aggregate output. -/
lemma matchedPropagationPhysicalFamilyRegression_assembled_action :
    ModeTransform.toLinearMap
        (ScatteringMatrix.toOrientedModeTransform
          matchedPropagationPhysicalRegressionComponentFamily.assembledScatteringMatrix)
        matchedPropagationPhysicalFamilyRegressionIncident =
      matchedPropagationPhysicalFamilyRegressionOutgoing := by
  apply WithLp.ofLp_injective 2
  funext endpoint
  rcases endpoint with ⟨⟨⟨component, port⟩, mode⟩⟩
  rcases component with ⟨⟩
  have hLocal := congrArg
    (fun amplitude => amplitude (Outgoing.mk ⟨port, mode⟩))
    (ScatteringComponentFamily.assembledScatteringMatrix_toOrientedModeTransform_apply_component
        matchedPropagationPhysicalRegressionComponentFamily
        matchedPropagationPhysicalFamilyRegressionIncident ())
  rw [matchedPropagationPhysicalFamilyRegression_incident_restrict,
    matchedPropagationPhysicalRegression_scattering_action] at hLocal
  exact hLocal

/-!
## C. Relational membership and hostile rejection
-/

/-- The exact aggregate state satisfies the order-free local component relation. -/
lemma matchedPropagationPhysicalFamilyRegression_componentwise_mem :
    (matchedPropagationPhysicalFamilyRegressionIncident,
      matchedPropagationPhysicalFamilyRegressionOutgoing) ∈
        matchedPropagationPhysicalRegressionComponentFamily.componentwiseBehavior := by
  rw [ScatteringComponentFamily.mem_componentwiseBehavior_iff_equations]
  intro component
  rcases component with ⟨⟩
  rw [matchedPropagationPhysicalFamilyRegression_incident_restrict,
    matchedPropagationPhysicalFamilyRegression_outgoing_restrict]
  exact matchedPropagationPhysicalRegression_scattering_action.symm

/-- The exact aggregate state belongs to the assembled scattering graph. -/
lemma matchedPropagationPhysicalFamilyRegression_assembled_mem :
    (matchedPropagationPhysicalFamilyRegressionIncident,
      matchedPropagationPhysicalFamilyRegressionOutgoing) ∈
        ModeTransform.toBehavior
          (ScatteringMatrix.toOrientedModeTransform
            matchedPropagationPhysicalRegressionComponentFamily.assembledScatteringMatrix) := by
  rw [ModeTransform.mem_toBehavior_iff_toLinearMap]
  exact matchedPropagationPhysicalFamilyRegression_assembled_action.symm

/-- The directly defined wrong-phase aggregate output violates the local component relation. -/
lemma matchedPropagationPhysicalFamilyRegression_wrong_not_componentwise :
    (matchedPropagationPhysicalFamilyRegressionIncident,
      matchedPropagationPhysicalFamilyRegressionWrongOutgoing) ∉
        matchedPropagationPhysicalRegressionComponentFamily.componentwiseBehavior := by
  intro hWrong
  have hLocal :=
    (ScatteringComponentFamily.mem_componentwiseBehavior_iff_equations
      matchedPropagationPhysicalRegressionComponentFamily
      matchedPropagationPhysicalFamilyRegressionIncident
      matchedPropagationPhysicalFamilyRegressionWrongOutgoing).mp hWrong ()
  rw [matchedPropagationPhysicalFamilyRegression_incident_restrict,
    matchedPropagationPhysicalFamilyRegression_wrong_restrict,
    matchedPropagationPhysicalRegression_scattering_action] at hLocal
  apply matchedPropagationPhysicalRegression_wrongPhase_not_mem
  rw [hLocal]
  exact matchedPropagationPhysicalRegression_mem

/-- The wrong-phase aggregate output also violates the assembled scattering graph. -/
lemma matchedPropagationPhysicalFamilyRegression_wrong_not_assembled :
    (matchedPropagationPhysicalFamilyRegressionIncident,
      matchedPropagationPhysicalFamilyRegressionWrongOutgoing) ∉
        ModeTransform.toBehavior
          (ScatteringMatrix.toOrientedModeTransform
            matchedPropagationPhysicalRegressionComponentFamily.assembledScatteringMatrix) := by
  rw [←
    ScatteringComponentFamily.componentwiseBehavior_eq_assembledScatteringMatrix_toBehavior]
  exact matchedPropagationPhysicalFamilyRegression_wrong_not_componentwise

end MatchedPropagation
end
end Optics
