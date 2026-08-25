/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Components.DirectionalCouplerPhysical
public import Physlib.Optics.Components.DirectionalCouplerRegression

/-!
# Regression tests for physical-port directional coupling

## i. Overview

The algebraic `3–4–5` fixture is transported to four owned ports, while hostile phase and
same-side outputs are defined directly in those physical labels. Exact coordinates pin all four
ports. Independent behavior membership, both hostile rejections, physical scattering action, and
realized-graph membership test the ownership layer rather than merely constructing its types.

## ii. Key results

- `directionalCouplerPhysicalRegression_mem`: direct physical-behavior membership.
- `directionalCouplerPhysicalRegression_wrongPhase_not_mem`: physical phase rejection.
- `directionalCouplerPhysicalRegression_sameSide_not_mem`: physical routing rejection.
- `directionalCouplerPhysicalRegression_scattering_action`: exact physical scattering action.
- `directionalCouplerPhysicalRegression_realized_mem`: physical realized-graph membership.

## iii. Table of contents

- A. Physical-coordinate fixture
- B. Physical behavior and scattering

## iv. References

This is a source-neutral coordinate and ownership regression.
-/

@[expose] public section

namespace Optics

noncomputable section

namespace DirectionalCoupler

/-! ## A. Physical-coordinate fixture -/

/-- The exact incident fixture transported to the four owned physical ports. -/
def directionalCouplerPhysicalRegressionIncident :
    ModeAmplitude (Incident ((portFamily Unit).Channel)) :=
  ModeAmplitude.reindex (incidentChannelEquiv Unit) directionalCouplerRegressionIncident

/-- The exact output fixture transported to the four owned physical ports. -/
def directionalCouplerPhysicalRegressionOutgoing :
    ModeAmplitude (Outgoing ((portFamily Unit).Channel)) :=
  ModeAmplitude.reindex (outgoingChannelEquiv Unit) directionalCouplerRegressionOutgoing

/-- The opposite-cross-phase output, defined directly in physical port labels. -/
def directionalCouplerPhysicalRegressionWrongPhase :
    ModeAmplitude (Outgoing ((portFamily Unit).Channel)) :=
  WithLp.toLp 2 fun output =>
    match output.channel.1 with
    | Port.leftFirst => (9 + 16 * Complex.I) / 5
    | Port.leftSecond => (12 + 12 * Complex.I) / 5
    | Port.rightFirst => (3 + 8 * Complex.I) / 5
    | Port.rightSecond => (6 + 4 * Complex.I) / 5

/-- The same-side output, defined directly in physical port labels. -/
def directionalCouplerPhysicalRegressionSameSide :
    ModeAmplitude (Outgoing ((portFamily Unit).Channel)) :=
  WithLp.toLp 2 fun output =>
    match output.channel.1 with
    | Port.leftFirst => (3 - 8 * Complex.I) / 5
    | Port.leftSecond => (6 - 4 * Complex.I) / 5
    | Port.rightFirst => (9 - 16 * Complex.I) / 5
    | Port.rightSecond => (12 - 12 * Complex.I) / 5

/-- The first left physical incident port contains amplitude one. -/
lemma directionalCouplerPhysicalRegression_incident_leftFirst :
    directionalCouplerPhysicalRegressionIncident
      (Incident.mk ⟨Port.leftFirst, ()⟩) = 1 := rfl
/-- The second left physical incident port contains amplitude two. -/
lemma directionalCouplerPhysicalRegression_incident_leftSecond :
    directionalCouplerPhysicalRegressionIncident
      (Incident.mk ⟨Port.leftSecond, ()⟩) = 2 := rfl
/-- The first right physical incident port contains amplitude three. -/
lemma directionalCouplerPhysicalRegression_incident_rightFirst :
    directionalCouplerPhysicalRegressionIncident
      (Incident.mk ⟨Port.rightFirst, ()⟩) = 3 := rfl
/-- The second right physical incident port contains amplitude four. -/
lemma directionalCouplerPhysicalRegression_incident_rightSecond :
    directionalCouplerPhysicalRegressionIncident
      (Incident.mk ⟨Port.rightSecond, ()⟩) = 4 := rfl
/-- The first left physical output has its exact mixed amplitude. -/
lemma directionalCouplerPhysicalRegression_outgoing_leftFirst :
    directionalCouplerPhysicalRegressionOutgoing
      (Outgoing.mk ⟨Port.leftFirst, ()⟩) = (9 - 16 * Complex.I) / 5 := rfl
/-- The second left physical output has its exact mixed amplitude. -/
lemma directionalCouplerPhysicalRegression_outgoing_leftSecond :
    directionalCouplerPhysicalRegressionOutgoing
      (Outgoing.mk ⟨Port.leftSecond, ()⟩) = (12 - 12 * Complex.I) / 5 := rfl
/-- The first right physical output has its exact mixed amplitude. -/
lemma directionalCouplerPhysicalRegression_outgoing_rightFirst :
    directionalCouplerPhysicalRegressionOutgoing
      (Outgoing.mk ⟨Port.rightFirst, ()⟩) = (3 - 8 * Complex.I) / 5 := rfl
/-- The second right physical output has its exact mixed amplitude. -/
lemma directionalCouplerPhysicalRegression_outgoing_rightSecond :
    directionalCouplerPhysicalRegressionOutgoing
      (Outgoing.mk ⟨Port.rightSecond, ()⟩) = (6 - 4 * Complex.I) / 5 := rfl

/-- Pulling the direct physical wrong-phase fixture back recovers the raw hostile output. -/
lemma directionalCouplerPhysicalRegression_wrongPhase_pullback :
    ModeAmplitude.reindex (outgoingChannelEquiv Unit).symm
        directionalCouplerPhysicalRegressionWrongPhase =
      directionalCouplerRegressionWrongPhase := by
  apply WithLp.ofLp_injective 2
  funext endpoint
  rcases endpoint with endpoint | endpoint <;>
    rcases endpoint with ⟨channel⟩ <;>
    rcases channel with ⟨⟩ | ⟨⟩ <;>
    norm_num [ModeAmplitude.reindex_apply, outgoingChannelEquiv, channelEquiv,
      directionalCouplerPhysicalRegressionWrongPhase, directionalCouplerRegressionWrongPhase]

/-- Pulling the direct physical same-side fixture back recovers the raw hostile output. -/
lemma directionalCouplerPhysicalRegression_sameSide_pullback :
    ModeAmplitude.reindex (outgoingChannelEquiv Unit).symm
        directionalCouplerPhysicalRegressionSameSide =
      directionalCouplerRegressionSameSide := by
  apply WithLp.ofLp_injective 2
  funext endpoint
  rcases endpoint with endpoint | endpoint <;>
    rcases endpoint with ⟨channel⟩ <;>
    rcases channel with ⟨⟩ | ⟨⟩ <;>
    norm_num [ModeAmplitude.reindex_apply, outgoingChannelEquiv, channelEquiv,
      directionalCouplerPhysicalRegressionSameSide, directionalCouplerRegressionSameSide]

/-! ## B. Physical behavior and scattering -/

/-- The exact state satisfies the independently transported physical behavior. -/
lemma directionalCouplerPhysicalRegression_mem :
    (directionalCouplerPhysicalRegressionIncident,
      directionalCouplerPhysicalRegressionOutgoing) ∈
        physicalBehavior directionalCouplerRegressionParameters := by
  rw [mem_physicalBehavior_iff, directionalCouplerPhysicalRegressionIncident,
    directionalCouplerPhysicalRegressionOutgoing,
    ModeAmplitude.reindex_symm_reindex, ModeAmplitude.reindex_symm_reindex]
  exact directionalCouplerRegression_mem

/-- The physical behavior rejects the directly specified opposite-cross-phase output. -/
lemma directionalCouplerPhysicalRegression_wrongPhase_not_mem :
    (directionalCouplerPhysicalRegressionIncident,
      directionalCouplerPhysicalRegressionWrongPhase) ∉
        physicalBehavior directionalCouplerRegressionParameters := by
  intro hWrong
  rw [mem_physicalBehavior_iff, directionalCouplerPhysicalRegressionIncident,
    ModeAmplitude.reindex_symm_reindex,
    directionalCouplerPhysicalRegression_wrongPhase_pullback] at hWrong
  exact directionalCouplerRegression_wrongPhase_not_mem hWrong

/-- The physical behavior rejects the directly specified same-side output. -/
lemma directionalCouplerPhysicalRegression_sameSide_not_mem :
    (directionalCouplerPhysicalRegressionIncident,
      directionalCouplerPhysicalRegressionSameSide) ∉
        physicalBehavior directionalCouplerRegressionParameters := by
  intro hWrong
  rw [mem_physicalBehavior_iff, directionalCouplerPhysicalRegressionIncident,
    ModeAmplitude.reindex_symm_reindex,
    directionalCouplerPhysicalRegression_sameSide_pullback] at hWrong
  exact directionalCouplerRegression_sameSide_not_mem hWrong

/-- The oriented physical scattering action produces the exact four-port output. -/
lemma directionalCouplerPhysicalRegression_scattering_action :
    ModeTransform.toLinearMap
        (ScatteringMatrix.toOrientedModeTransform
          (physicalScattering directionalCouplerRegressionParameters Unit))
        directionalCouplerPhysicalRegressionIncident =
      directionalCouplerPhysicalRegressionOutgoing := by
  rw [physicalScattering_toOrientedModeTransform,
    directionalCouplerPhysicalRegressionIncident,
    ModeTransform.toLinearMap_reindex_apply,
    directionalCouplerRegression_scattering_action,
    directionalCouplerPhysicalRegressionOutgoing]

/-- The exact physical state belongs to the realized oriented scattering graph. -/
lemma directionalCouplerPhysicalRegression_realized_mem :
    (directionalCouplerPhysicalRegressionIncident,
      directionalCouplerPhysicalRegressionOutgoing) ∈
        ModeTransform.toBehavior
          (ScatteringMatrix.toOrientedModeTransform
            (physicalScattering directionalCouplerRegressionParameters Unit)) := by
  rw [ModeTransform.mem_toBehavior_iff_toLinearMap]
  exact directionalCouplerPhysicalRegression_scattering_action.symm

end DirectionalCoupler
end
end Optics
