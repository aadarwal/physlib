/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Components.MatchedPropagationPhysical
public import Physlib.Optics.Components.MatchedPropagationRegression

/-!
# Regression tests for matched-propagation physical ports

## i. Overview

The existing two-mode phase fixture is transported through the public physical-port equivalences.
The regression pins left and right port ownership, checks independent physical-behavior membership,
evaluates the physical oriented scattering action, and places the exact state in its realized graph.
Two outputs defined directly in physical labels reject the opposite phase sign and same-side
routing without reusing the coordinate transport in their definitions.

## ii. Key results

- `matchedPropagationPhysicalRegression_mem`: independent physical-behavior membership.
- `matchedPropagationPhysicalRegression_wrongPhase_not_mem`: physical wrong-phase rejection.
- `matchedPropagationPhysicalRegression_sameSide_not_mem`: physical same-side rejection.
- `matchedPropagationPhysicalRegression_scattering_action`: exact physical scattering action.
- `matchedPropagationPhysicalRegression_realized_mem`: exact realized-graph membership.

## iii. Table of contents

- A. Physical-coordinate fixture
- B. Physical behavior and scattering

## iv. References

This is a source-neutral coordinate and integration regression.
-/

@[expose] public section

namespace Optics

noncomputable section

namespace MatchedPropagation

/-!

## A. Physical-coordinate fixture

-/

/-- The hostile incident state transported to the owned physical ports. -/
def matchedPropagationPhysicalRegressionIncident :
    ModeAmplitude (Incident ((portFamily (Fin 2)).Channel)) :=
  ModeAmplitude.reindex (incidentChannelEquiv (Fin 2))
    matchedPropagationRegressionIncident

/-- The exact hostile outgoing state transported to the owned physical ports. -/
def matchedPropagationPhysicalRegressionOutgoing :
    ModeAmplitude (Outgoing ((portFamily (Fin 2)).Channel)) :=
  ModeAmplitude.reindex (outgoingChannelEquiv (Fin 2))
    matchedPropagationRegressionOutgoing

/-- The false opposite-phase output, defined directly in physical port and mode labels. -/
def matchedPropagationPhysicalRegressionWrongPhase :
    ModeAmplitude (Outgoing ((portFamily (Fin 2)).Channel)) :=
  WithLp.toLp 2 fun output =>
    let mode : Fin 2 := output.channel.2
    match output.channel.1 with
    | Port.left => if mode = 0 then 0 else 1 + 3 * Complex.I
    | Port.right => if mode = 0 then -2 + Complex.I else 0

/-- The false same-side output, defined directly in physical port and mode labels. -/
def matchedPropagationPhysicalRegressionSameSide :
    ModeAmplitude (Outgoing ((portFamily (Fin 2)).Channel)) :=
  WithLp.toLp 2 fun output =>
    let mode : Fin 2 := output.channel.2
    match output.channel.1 with
    | Port.left => if mode = 0 then 2 - Complex.I else 0
    | Port.right => if mode = 0 then 0 else -1 - 3 * Complex.I

/-- The first left physical incident coordinate is exactly `2 + 4I`. -/
lemma matchedPropagationPhysicalRegression_incident_left_zero :
    matchedPropagationPhysicalRegressionIncident
        (Incident.mk ⟨Port.left, (0 : Fin 2)⟩) = 2 + 4 * Complex.I := by
  rw [← incidentChannelEquiv_apply_inl,
    matchedPropagationPhysicalRegressionIncident, ModeAmplitude.reindex_apply,
    Equiv.symm_apply_apply]
  norm_num [matchedPropagationRegressionIncident]

/-- The second right physical incident coordinate is exactly `6 - 2I`. -/
lemma matchedPropagationPhysicalRegression_incident_right_one :
    matchedPropagationPhysicalRegressionIncident
        (Incident.mk ⟨Port.right, (1 : Fin 2)⟩) = 6 - 2 * Complex.I := by
  rw [← incidentChannelEquiv_apply_inr,
    matchedPropagationPhysicalRegressionIncident, ModeAmplitude.reindex_apply,
    Equiv.symm_apply_apply]
  norm_num [matchedPropagationRegressionIncident]

/-- Pulling the direct physical wrong-phase fixture back recovers the raw hostile output. -/
lemma matchedPropagationPhysicalRegression_wrongPhase_pullback :
    ModeAmplitude.reindex (outgoingChannelEquiv (Fin 2)).symm
        matchedPropagationPhysicalRegressionWrongPhase =
      matchedPropagationRegressionWrongPhase := by
  apply WithLp.ofLp_injective 2
  funext endpoint
  change matchedPropagationPhysicalRegressionWrongPhase
      (outgoingChannelEquiv (Fin 2) endpoint) =
    matchedPropagationRegressionWrongPhase endpoint
  rcases endpoint with endpoint | endpoint <;>
    rcases endpoint with ⟨mode⟩ <;> fin_cases mode <;>
    simp only [outgoingChannelEquiv_apply_inl, outgoingChannelEquiv_apply_inr] <;>
    norm_num [
      matchedPropagationPhysicalRegressionWrongPhase, matchedPropagationRegressionWrongPhase]

/-- Pulling the direct physical same-side fixture back recovers the raw hostile output. -/
lemma matchedPropagationPhysicalRegression_sameSide_pullback :
    ModeAmplitude.reindex (outgoingChannelEquiv (Fin 2)).symm
        matchedPropagationPhysicalRegressionSameSide =
      matchedPropagationRegressionSameSide := by
  apply WithLp.ofLp_injective 2
  funext endpoint
  change matchedPropagationPhysicalRegressionSameSide
      (outgoingChannelEquiv (Fin 2) endpoint) =
    matchedPropagationRegressionSameSide endpoint
  rcases endpoint with endpoint | endpoint <;>
    rcases endpoint with ⟨mode⟩ <;> fin_cases mode <;>
    simp only [outgoingChannelEquiv_apply_inl, outgoingChannelEquiv_apply_inr] <;>
    norm_num [
      matchedPropagationPhysicalRegressionSameSide, matchedPropagationRegressionSameSide]

/-!

## B. Physical behavior and scattering

-/

/-- The exact state belongs directly to the independent physical-port behavior. -/
lemma matchedPropagationPhysicalRegression_mem :
    (matchedPropagationPhysicalRegressionIncident,
      matchedPropagationPhysicalRegressionOutgoing) ∈
        physicalBehavior matchedPropagationRegressionParameters := by
  rw [mem_physicalBehavior_iff, matchedPropagationPhysicalRegressionIncident,
    matchedPropagationPhysicalRegressionOutgoing,
    ModeAmplitude.reindex_symm_reindex, ModeAmplitude.reindex_symm_reindex]
  exact matchedPropagationRegression_mem

/-- The independent physical behavior rejects the directly defined opposite-phase output. -/
lemma matchedPropagationPhysicalRegression_wrongPhase_not_mem :
    (matchedPropagationPhysicalRegressionIncident,
      matchedPropagationPhysicalRegressionWrongPhase) ∉
        physicalBehavior matchedPropagationRegressionParameters := by
  intro hWrong
  rw [mem_physicalBehavior_iff, matchedPropagationPhysicalRegressionIncident,
    ModeAmplitude.reindex_symm_reindex,
    matchedPropagationPhysicalRegression_wrongPhase_pullback] at hWrong
  exact matchedPropagationRegression_wrongPhase_not_mem hWrong

/-- The independent physical behavior rejects the directly defined same-side output. -/
lemma matchedPropagationPhysicalRegression_sameSide_not_mem :
    (matchedPropagationPhysicalRegressionIncident,
      matchedPropagationPhysicalRegressionSameSide) ∉
        physicalBehavior matchedPropagationRegressionParameters := by
  intro hWrong
  rw [mem_physicalBehavior_iff, matchedPropagationPhysicalRegressionIncident,
    ModeAmplitude.reindex_symm_reindex,
    matchedPropagationPhysicalRegression_sameSide_pullback] at hWrong
  exact matchedPropagationRegression_sameSide_not_mem hWrong

/-- The physical oriented scattering law produces the exact physical-port output. -/
lemma matchedPropagationPhysicalRegression_scattering_action :
    ModeTransform.toLinearMap
        (ScatteringMatrix.toOrientedModeTransform
          (physicalScattering matchedPropagationRegressionParameters (Fin 2)))
        matchedPropagationPhysicalRegressionIncident =
      matchedPropagationPhysicalRegressionOutgoing := by
  rw [physicalScattering_toOrientedModeTransform,
    matchedPropagationPhysicalRegressionIncident,
    ModeTransform.toLinearMap_reindex_apply,
    matchedPropagationRegression_scattering_action,
    matchedPropagationPhysicalRegressionOutgoing]

/-- The exact physical state belongs to the realized oriented scattering graph. -/
lemma matchedPropagationPhysicalRegression_realized_mem :
    (matchedPropagationPhysicalRegressionIncident,
      matchedPropagationPhysicalRegressionOutgoing) ∈
        ModeTransform.toBehavior
          (ScatteringMatrix.toOrientedModeTransform
            (physicalScattering matchedPropagationRegressionParameters (Fin 2))) := by
  rw [ModeTransform.mem_toBehavior_iff_toLinearMap]
  exact matchedPropagationPhysicalRegression_scattering_action.symm

end MatchedPropagation
end
end Optics
