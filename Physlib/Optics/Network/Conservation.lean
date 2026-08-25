/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Mode.Rephase
public import Physlib.Optics.Network.FlatNetlistElimination

/-!
# Conservation under optical interconnection

## i. Overview

A flat scattering netlist is built from component laws `S`, internal routing `C`, external
incident injection `E_in`, and external outgoing readout `E_outᴴ`. This file proves that the
power bookkeeping of the wiring layer is exact, and that passivity and losslessness of the
complete external response are consequences of the same properties of the components.

The single identity behind every result is the internal connection power balance

```text
‖a‖² + ‖y‖² = ‖b‖² + ‖u‖²,
```

valid for every complete solution state `(a, b)` of the network equations with external input `u`
and external output `y`. It holds because the wiring layer neither duplicates nor discards a
channel: internal routing is a partial isometry whose input coordinates are exactly the connected
outgoing channels, external exposure covers exactly the complementary channels, and the two
incident-side ranges are orthogonal. Adding a component power inequality `‖b‖ ≤ ‖a‖` or an
equality `‖b‖ = ‖a‖` to that balance immediately gives `‖y‖ ≤ ‖u‖` or `‖y‖ = ‖u‖`.

## ii. Scope and non-claims

Every power here is `ModeAmplitude.power`, the normalized modal power of
`Physlib/Optics/Mode/Basic.lean`, whose defining convention is quoted at
`Physlib/Optics/Mode/Basic.lean:78`. It becomes electromagnetic power only after a Poynting-flux
normalization theorem, which this file does not supply and does not assume.

This file does not claim reciprocity, causality, frequency dependence, or that the external
scattering matrix of section E is a physically paired time-reversed port set. The external
incident and external outgoing index types are the nominally distinct wrappers
`Incident netlist.ExternalChannel` and `Outgoing netlist.ExternalChannel` of one and the same
channel type, so the identification used in section E is the canonical identity-on-channels
relabelling `Incident.channelEquiv` (`Physlib/Optics/Network/Port.lean:130`) and
`Outgoing.channelEquiv` (`Physlib/Optics/Network/Port.lean:222`), not a physical port pairing.

External-channel completeness is structural rather than hypothetical here: `ExternalChannel` is
defined as the exact set-theoretic complement of the connected range at
`Physlib/Optics/Network/ExternalChannel.lean:83`, and the resolution of the identity used below
is the already-proved
`PortConnectionFamily.outgoingRangeProjector_add_externalRangeProjector`.

Rephasing results are stated as gauge invariance of the physical predicates of a fixed response
transform. A covariance theorem transporting a whole netlist along an arbitrary channel-end phase
gauge is not available, because matched-gauge covariance of connection routing is still an open
N2a item; nothing here assumes it.

## iii. Key definitions and results

- `ScatteringComponentFamily.power_eq_sum_component`: aggregate modal power is the sum of the
  component-restricted powers.
- `ScatteringComponentFamily.assembledScatteringMatrix_isPassive` and
  `ScatteringComponentFamily.assembledScatteringMatrix_isPowerPreserving`: componentwise
  classification closes under block-diagonal assembly.
- `PortConnectionFamily.power_restrictEmbedding_connected_add_external`: connected and external
  outgoing coordinates split ambient outgoing power exactly once.
- `FlatNetlist.power_balance`: the internal connection power balance.
- `FlatNetlist.power_le_of_isPassive` and `FlatNetlist.responseTransform_isPassive`: passivity
  closure.
- `FlatNetlist.power_eq_of_isPowerPreserving` and
  `FlatNetlist.responseTransform_isPowerPreserving`: losslessness of the complete external
  response.
- `FlatNetlist.externalScatteringMatrix` and
  `FlatNetlist.externalScatteringMatrix_isLossless_of_components_isLossless`: the external
  response packaged as a scattering matrix, proved lossless from component unitarity.
- `FlatNetlist.responseTransform_isPowerPreserving_withConnections_iff` and
  `ModeTransform.isPowerPreserving_rephase_iff`-based corollaries: physical predicates are
  invariant under relabelling and rephasing.

## iv. Table of contents

- A. Componentwise power decomposition
- B. Passivity and losslessness of the assembled component boundary
- C. Exact wiring power bookkeeping
- D. Passivity and losslessness closure
- E. The external scattering matrix
- F. Relabelling and rephasing invariance

-/

@[expose] public section

namespace Optics

noncomputable section

universe u v w x y

/-!

## A. Componentwise power decomposition

-/

namespace ScatteringComponentFamily

variable (family : ScatteringComponentFamily.{u, v, w})

section Finite

variable [Fintype family.Component]
  [∀ component, Fintype (family.portFamily component).Channel]
  [Fintype family.aggregatePortModeFamily.Channel]

/-- Aggregate modal power is the sum of the powers carried by each component's own channels.

No component shares a channel with another, so this is an exact decomposition rather than a
bound. -/
lemma power_eq_sum_component
    (amplitude : ModeAmplitude family.aggregatePortModeFamily.Channel) :
    amplitude.power =
      ∑ component : family.Component,
        (amplitude.restrictEmbedding
          (family.componentChannelEmbedding component)).power := by
  classical
  rw [ModeAmplitude.power_eq_sum_normSq,
    ← Fintype.sum_equiv family.channelEquiv
      (fun indexed => Complex.normSq (amplitude (family.channelEquiv indexed)))
      (fun channel => Complex.normSq (amplitude channel)) (fun _ => rfl),
    Fintype.sum_sigma]
  refine Finset.sum_congr rfl ?_
  intro component _
  rw [ModeAmplitude.power_restrictEmbedding_eq_sum]
  rfl

/-- Aggregate incident power is the sum of the component-restricted incident powers. -/
lemma power_eq_sum_component_incident
    (amplitude : ModeAmplitude (Incident family.aggregatePortModeFamily.Channel)) :
    amplitude.power =
      ∑ component : family.Component,
        (amplitude.restrictEmbedding
          (Incident.relabelEmbedding
            (family.componentChannelEmbedding component))).power := by
  classical
  have hRestrict : ∀ component : family.Component,
      (ModeAmplitude.reindex Incident.channelEquiv amplitude).restrictEmbedding
          (family.componentChannelEmbedding component) =
        ModeAmplitude.reindex Incident.channelEquiv
          (amplitude.restrictEmbedding
            (Incident.relabelEmbedding
              (family.componentChannelEmbedding component))) := by
    intro component
    apply WithLp.ofLp_injective 2
    funext channel
    rfl
  calc
    amplitude.power = (ModeAmplitude.reindex Incident.channelEquiv amplitude).power :=
      (ModeAmplitude.power_reindex _ _).symm
    _ = ∑ component : family.Component,
          ((ModeAmplitude.reindex Incident.channelEquiv amplitude).restrictEmbedding
            (family.componentChannelEmbedding component)).power :=
      family.power_eq_sum_component _
    _ = _ := by simp only [hRestrict, ModeAmplitude.power_reindex]

/-- Aggregate outgoing power is the sum of the component-restricted outgoing powers. -/
lemma power_eq_sum_component_outgoing
    (amplitude : ModeAmplitude (Outgoing family.aggregatePortModeFamily.Channel)) :
    amplitude.power =
      ∑ component : family.Component,
        (amplitude.restrictEmbedding
          (Outgoing.relabelEmbedding
            (family.componentChannelEmbedding component))).power := by
  classical
  have hRestrict : ∀ component : family.Component,
      (ModeAmplitude.reindex Outgoing.channelEquiv amplitude).restrictEmbedding
          (family.componentChannelEmbedding component) =
        ModeAmplitude.reindex Outgoing.channelEquiv
          (amplitude.restrictEmbedding
            (Outgoing.relabelEmbedding
              (family.componentChannelEmbedding component))) := by
    intro component
    apply WithLp.ofLp_injective 2
    funext channel
    rfl
  calc
    amplitude.power = (ModeAmplitude.reindex Outgoing.channelEquiv amplitude).power :=
      (ModeAmplitude.power_reindex _ _).symm
    _ = ∑ component : family.Component,
          ((ModeAmplitude.reindex Outgoing.channelEquiv amplitude).restrictEmbedding
            (family.componentChannelEmbedding component)).power :=
      family.power_eq_sum_component _
    _ = _ := by simp only [hRestrict, ModeAmplitude.power_reindex]

/-!

## B. Passivity and losslessness of the assembled component boundary

-/

section Assembled

variable [DecidableEq family.Component]
  [∀ component, DecidableEq (family.portFamily component).Channel]
  [DecidableEq family.aggregatePortModeFamily.Channel]

/-- Block-diagonal assembly of passive components is passive on the aggregate boundary. -/
lemma assembledScatteringMatrix_isPassive
    (hComponents : ∀ component : family.Component,
      (family.scattering component).toOrientedModeTransform.IsPassive) :
    family.assembledScatteringMatrix.toOrientedModeTransform.IsPassive := by
  intro incident
  rw [family.power_eq_sum_component_outgoing, family.power_eq_sum_component_incident]
  refine Finset.sum_le_sum ?_
  intro component _
  rw [family.assembledScatteringMatrix_toOrientedModeTransform_apply_component]
  exact hComponents component _

/-- Block-diagonal assembly of power-preserving components preserves aggregate power. -/
lemma assembledScatteringMatrix_isPowerPreserving
    (hComponents : ∀ component : family.Component,
      (family.scattering component).toOrientedModeTransform.IsPowerPreserving) :
    family.assembledScatteringMatrix.toOrientedModeTransform.IsPowerPreserving := by
  intro incident
  rw [family.power_eq_sum_component_outgoing, family.power_eq_sum_component_incident]
  refine Finset.sum_congr rfl ?_
  intro component _
  rw [family.assembledScatteringMatrix_toOrientedModeTransform_apply_component]
  exact hComponents component _

/-- Block-diagonal assembly of lossless components preserves aggregate power. -/
lemma assembledScatteringMatrix_isPowerPreserving_of_isLossless
    (hComponents : ∀ component : family.Component, (family.scattering component).IsLossless) :
    family.assembledScatteringMatrix.toOrientedModeTransform.IsPowerPreserving :=
  family.assembledScatteringMatrix_isPowerPreserving fun component =>
    (ScatteringMatrix.isLossless_iff_toOrientedModeTransform_isPowerPreserving
      (family.scattering component)).mp (hComponents component)

end Assembled

end Finite

end ScatteringComponentFamily

/-!

## C. Exact wiring power bookkeeping

-/

namespace PortConnectionFamily

variable {P : PortModeFamily.{u, v}} {ι : Type w} (family : PortConnectionFamily P ι)

/-- Connected and external outgoing coordinates split ambient outgoing power exactly once.

This is the power form of the projector resolution
`PortConnectionFamily.outgoingRangeProjector_add_externalRangeProjector`: no ambient outgoing
channel is counted twice and none is dropped. -/
lemma power_restrictEmbedding_connected_add_external
    [Fintype family.Channel] [Fintype family.ExternalChannel] [Fintype P.Channel]
    (amplitude : ModeAmplitude (Outgoing P.Channel)) :
    (amplitude.restrictEmbedding family.outgoingChannelEmbedding).power +
        (amplitude.restrictEmbedding family.externalOutgoingEmbedding).power =
      amplitude.power := by
  classical
  set relabelled :=
    ModeAmplitude.reindex family.outgoingPartitionEquiv.symm amplitude with hRelabelled
  have hLeft :
      relabelled.restrictInl = amplitude.restrictEmbedding family.outgoingChannelEmbedding := by
    apply WithLp.ofLp_injective 2
    funext channel
    change amplitude (family.outgoingPartitionEquiv (Sum.inl channel)) = _
    rw [family.outgoingPartitionEquiv_apply_inl]
    rfl
  have hRight :
      relabelled.restrictInr =
        amplitude.restrictEmbedding family.externalOutgoingEmbedding := by
    apply WithLp.ofLp_injective 2
    funext channel
    change amplitude (family.outgoingPartitionEquiv (Sum.inr channel)) = _
    rw [family.outgoingPartitionEquiv_apply_inr]
    rfl
  calc
    (amplitude.restrictEmbedding family.outgoingChannelEmbedding).power +
          (amplitude.restrictEmbedding family.externalOutgoingEmbedding).power =
        relabelled.restrictInl.power + relabelled.restrictInr.power := by
      rw [hLeft, hRight]
    _ = (relabelled.restrictInl.directSum relabelled.restrictInr).power :=
      (ModeAmplitude.power_directSum _ _).symm
    _ = relabelled.power := by rw [ModeAmplitude.directSum_restrict]
    _ = amplitude.power := by rw [hRelabelled, ModeAmplitude.power_reindex]

end PortConnectionFamily

namespace FlatNetlist

variable (netlist : FlatNetlist.{u, v, w, x})

section Finite

variable [Fintype netlist.Channel] [Fintype netlist.ConnectedChannel]

/-- Classical equality on aggregate channels, kept local to finite conservation statements. -/
local instance conservationChannelDecidableEq : DecidableEq netlist.Channel := Classical.decEq _

/-- Classical equality on connected channels, kept local to finite conservation statements. -/
local instance conservationConnectedChannelDecidableEq :
    DecidableEq netlist.ConnectedChannel := Classical.decEq _

/-- The external complement of the finite aggregate and connected channel families is finite. -/
local instance conservationExternalChannelFintype : Fintype netlist.ExternalChannel := by
  classical
  infer_instance

/-- The internal connection power balance of a flat netlist.

For every ambient outgoing amplitude `b` and external input `u`, the assembled incident amplitude
`a = C b + E_in u` and the external readout `y = E_outᴴ b` satisfy `‖a‖² + ‖y‖² = ‖b‖² + ‖u‖²`.

No component law, well-posedness, passivity, or losslessness hypothesis is used: this is the
statement that the wiring layer alone neither creates nor destroys modal power, because it
neither duplicates a channel nor leaves one unaccounted for. -/
lemma power_balance
    (outgoing : ModeAmplitude netlist.OutgoingIndex)
    (external : ModeAmplitude netlist.ExternalIncident) :
    (netlist.connections.incidentAssembly outgoing external).power +
        (netlist.outputReadout.toLinearMap outgoing).power =
      outgoing.power + external.power := by
  classical
  rw [netlist.connections.incidentAssembly_power,
    PortConnectionFamily.externalOutgoingReadout_apply]
  rw [add_right_comm,
    netlist.connections.power_restrictEmbedding_connected_add_external outgoing]

/-- The internal connection power balance of every complete solution state.

The incident, outgoing, external input, and external output powers of a solution are related by
`‖a‖² + ‖y‖² = ‖b‖² + ‖u‖²`. -/
lemma power_balance_of_mem_solutionBehavior
    (external : ModeAmplitude netlist.ExternalIncident)
    (incident : ModeAmplitude netlist.IncidentIndex)
    (outgoing : ModeAmplitude netlist.OutgoingIndex)
    (hSolution : (external, incident.directSum outgoing) ∈ netlist.solutionBehavior) :
    incident.power + (netlist.outputReadout.toLinearMap outgoing).power =
      outgoing.power + external.power := by
  classical
  rcases (netlist.mem_solutionBehavior_directSum_iff external incident outgoing).mp
    hSolution with ⟨_, hIncident⟩
  rw [hIncident]
  exact netlist.power_balance outgoing external

/-!

## D. Passivity and losslessness closure

-/

/-- Passivity closure: a network of passive components never returns more external power than it
receives.

The hypothesis is passivity of the assembled component law `S`. Internal routing is a
power-nonincreasing partial isometry and external exposure is disjoint from it by construction,
so no extra hypothesis on the wiring is required. -/
lemma power_le_of_isPassive
    (hScattering : netlist.scatteringTransform.IsPassive)
    (input : ModeAmplitude netlist.ExternalIncident)
    (output : ModeAmplitude netlist.ExternalOutgoing)
    (hBehavior : (input, output) ∈ netlist.behavior) :
    output.power ≤ input.power := by
  classical
  rcases (netlist.mem_behavior_iff_componentBehavior input output).mp hBehavior with
    ⟨incident, outgoing, hComponent, hIncident, hOutput⟩
  rw [netlist.mem_componentBehavior_iff] at hComponent
  have hBalance := netlist.power_balance outgoing input
  rw [← hIncident] at hBalance
  have hComponentPower : outgoing.power ≤ incident.power := by
    rw [hComponent]
    exact hScattering incident
  rw [hOutput]
  have hSum : incident.power + (netlist.outputReadout.toLinearMap outgoing).power ≤
      incident.power + input.power := by
    rw [hBalance]
    exact add_le_add hComponentPower le_rfl
  exact le_of_add_le_add_left hSum

/-- Losslessness closure: a network of power-preserving components returns exactly the external
power it receives. -/
lemma power_eq_of_isPowerPreserving
    (hScattering : netlist.scatteringTransform.IsPowerPreserving)
    (input : ModeAmplitude netlist.ExternalIncident)
    (output : ModeAmplitude netlist.ExternalOutgoing)
    (hBehavior : (input, output) ∈ netlist.behavior) :
    output.power = input.power := by
  classical
  rcases (netlist.mem_behavior_iff_componentBehavior input output).mp hBehavior with
    ⟨incident, outgoing, hComponent, hIncident, hOutput⟩
  rw [netlist.mem_componentBehavior_iff] at hComponent
  have hBalance := netlist.power_balance outgoing input
  rw [← hIncident] at hBalance
  have hComponentPower : outgoing.power = incident.power := by
    rw [hComponent]
    exact hScattering incident
  rw [hOutput]
  rw [hComponentPower] at hBalance
  exact add_left_cancel hBalance

/-- The external response of a well-posed network of passive components is passive. -/
lemma responseTransform_isPassive
    (hWellPosed : netlist.IsWellPosed)
    (hScattering : netlist.scatteringTransform.IsPassive) :
    (netlist.responseTransform hWellPosed).IsPassive := by
  intro input
  refine netlist.power_le_of_isPassive hScattering input _ ?_
  exact (netlist.mem_behavior_iff_eq_responseTransform hWellPosed input _).mpr rfl

/-- The external response of a well-posed network of power-preserving components preserves
power.

This is the theorem that makes system-level losslessness a consequence of component losslessness
and wiring validity rather than an assumption about the network. -/
lemma responseTransform_isPowerPreserving
    (hWellPosed : netlist.IsWellPosed)
    (hScattering : netlist.scatteringTransform.IsPowerPreserving) :
    (netlist.responseTransform hWellPosed).IsPowerPreserving := by
  intro input
  refine netlist.power_eq_of_isPowerPreserving hScattering input _ ?_
  exact (netlist.mem_behavior_iff_eq_responseTransform hWellPosed input _).mpr rfl

/-!

### D.1. Closure directly from component classifications

-/

section Components

variable [Fintype netlist.components.Component] [DecidableEq netlist.components.Component]
  [∀ component, Fintype (netlist.components.portFamily component).Channel]
  [∀ component, DecidableEq (netlist.components.portFamily component).Channel]

omit [Fintype netlist.ConnectedChannel] in
/-- The assembled netlist component law is passive when every individual component is passive. -/
lemma scatteringTransform_isPassive_of_components
    (hComponents : ∀ component : netlist.components.Component,
      (netlist.components.scattering component).toOrientedModeTransform.IsPassive) :
    netlist.scatteringTransform.IsPassive := by
  classical
  have hAssembled :
      netlist.scatteringMatrix = netlist.components.assembledScatteringMatrix := by
    unfold scatteringMatrix
    congr!
  change netlist.scatteringMatrix.toOrientedModeTransform.IsPassive
  rw [hAssembled]
  exact netlist.components.assembledScatteringMatrix_isPassive hComponents

omit [Fintype netlist.ConnectedChannel] in
/-- The assembled netlist component law preserves power when every component is lossless. -/
lemma scatteringTransform_isPowerPreserving_of_components_isLossless
    (hComponents : ∀ component : netlist.components.Component,
      (netlist.components.scattering component).IsLossless) :
    netlist.scatteringTransform.IsPowerPreserving := by
  classical
  have hAssembled :
      netlist.scatteringMatrix = netlist.components.assembledScatteringMatrix := by
    unfold scatteringMatrix
    congr!
  change netlist.scatteringMatrix.toOrientedModeTransform.IsPowerPreserving
  rw [hAssembled]
  exact netlist.components.assembledScatteringMatrix_isPowerPreserving_of_isLossless hComponents

/-- Passivity closure stated directly from the component classifications. -/
lemma responseTransform_isPassive_of_components
    (hWellPosed : netlist.IsWellPosed)
    (hComponents : ∀ component : netlist.components.Component,
      (netlist.components.scattering component).toOrientedModeTransform.IsPassive) :
    (netlist.responseTransform hWellPosed).IsPassive :=
  netlist.responseTransform_isPassive hWellPosed
    (netlist.scatteringTransform_isPassive_of_components hComponents)

/-- Losslessness closure stated directly from the component classifications.

Only two physical hypotheses appear: every component is lossless, and the network is well posed.
Everything else the statement needs is structural, because internal routing is a partial isometry
of the connected channels and the external channels are their exact complement. -/
lemma responseTransform_isPowerPreserving_of_components_isLossless
    (hWellPosed : netlist.IsWellPosed)
    (hComponents : ∀ component : netlist.components.Component,
      (netlist.components.scattering component).IsLossless) :
    (netlist.responseTransform hWellPosed).IsPowerPreserving :=
  netlist.responseTransform_isPowerPreserving hWellPosed
    (netlist.scatteringTransform_isPowerPreserving_of_components_isLossless hComponents)

end Components

/-!

## E. The external scattering matrix

-/

/-- The well-posed external response packaged as a scattering matrix on the external channels.

The external incident and external outgoing index types are the nominally distinct wrappers
`Incident netlist.ExternalChannel` and `Outgoing netlist.ExternalChannel` of one and the same
channel type, so this packaging uses only the canonical identity-on-channels relabellings
`Incident.channelEquiv` and `Outgoing.channelEquiv`. It asserts no time-reversed physical port
pairing, no reference-plane convention, and no reciprocity. -/
def externalScatteringMatrix (hWellPosed : netlist.IsWellPosed) :
    ScatteringMatrix netlist.ExternalChannel where
  toModeTransform :=
    (netlist.responseTransform hWellPosed).reindex Incident.channelEquiv Outgoing.channelEquiv

/-- The packaged external scattering matrix retains every response entry. -/
@[simp]
lemma externalScatteringMatrix_apply (hWellPosed : netlist.IsWellPosed)
    (output input : netlist.ExternalChannel) :
    (netlist.externalScatteringMatrix hWellPosed).toModeTransform output input =
      netlist.responseTransform hWellPosed (Outgoing.mk output) (Incident.mk input) := rfl

/-- The packaged external scattering matrix of a well-posed passive network is passive. -/
lemma externalScatteringMatrix_isPassive
    (hWellPosed : netlist.IsWellPosed)
    (hScattering : netlist.scatteringTransform.IsPassive) :
    (netlist.externalScatteringMatrix hWellPosed).toModeTransform.IsPassive :=
  (ModeTransform.isPassive_reindex_iff Incident.channelEquiv Outgoing.channelEquiv
    (netlist.responseTransform hWellPosed)).mpr
      (netlist.responseTransform_isPassive hWellPosed hScattering)

/-- The packaged external scattering matrix of a well-posed lossless network is unitary. -/
lemma externalScatteringMatrix_isLossless
    (hWellPosed : netlist.IsWellPosed)
    (hScattering : netlist.scatteringTransform.IsPowerPreserving) :
    (netlist.externalScatteringMatrix hWellPosed).IsLossless := by
  rw [ScatteringMatrix.isLossless_iff_isPowerPreserving]
  exact (ModeTransform.isPowerPreserving_reindex_iff Incident.channelEquiv
    Outgoing.channelEquiv (netlist.responseTransform hWellPosed)).mpr
      (netlist.responseTransform_isPowerPreserving hWellPosed hScattering)

/-- System-level losslessness as a theorem from component unitarity and wiring validity. -/
lemma externalScatteringMatrix_isLossless_of_components_isLossless
    [Fintype netlist.components.Component] [DecidableEq netlist.components.Component]
    [∀ component, Fintype (netlist.components.portFamily component).Channel]
    [∀ component, DecidableEq (netlist.components.portFamily component).Channel]
    (hWellPosed : netlist.IsWellPosed)
    (hComponents : ∀ component : netlist.components.Component,
      (netlist.components.scattering component).IsLossless) :
    (netlist.externalScatteringMatrix hWellPosed).IsLossless :=
  netlist.externalScatteringMatrix_isLossless hWellPosed
    (netlist.scatteringTransform_isPowerPreserving_of_components_isLossless hComponents)

/-!

## F. Relabelling and rephasing invariance

-/

section WiringInvariance

variable {ι' : Type y}
  (connections' : PortConnectionFamily netlist.PortFamily ι')
  (wiring : PortConnectionFamily.WiringEquiv netlist.connections connections')
  [Fintype connections'.Channel]

/-- External channels in a wiring-equivalent replacement presentation remain finite. -/
local instance conservationReplacementExternalChannelFintype :
    Fintype connections'.ExternalChannel := by
  classical
  infer_instance

include wiring in
/-- Passivity of the external response does not depend on the wiring presentation. -/
lemma responseTransform_isPassive_withConnections_iff
    (hReplacement : (netlist.withConnections connections').IsWellPosed)
    (hOriginal : netlist.IsWellPosed) :
    ((netlist.withConnections connections').responseTransform hReplacement).IsPassive ↔
      (netlist.responseTransform hOriginal).IsPassive := by
  rw [netlist.responseTransform_withConnections connections' wiring hReplacement hOriginal,
    ModeTransform.isPassive_reindex_iff]

include wiring in
/-- Losslessness of the external response does not depend on the wiring presentation. -/
lemma responseTransform_isPowerPreserving_withConnections_iff
    (hReplacement : (netlist.withConnections connections').IsWellPosed)
    (hOriginal : netlist.IsWellPosed) :
    ((netlist.withConnections connections').responseTransform hReplacement).IsPowerPreserving ↔
      (netlist.responseTransform hOriginal).IsPowerPreserving := by
  rw [netlist.responseTransform_withConnections connections' wiring hReplacement hOriginal,
    ModeTransform.isPowerPreserving_reindex_iff]

end WiringInvariance

/-- Passivity of the external response is invariant under any external channel-end phase gauge.

This is gauge invariance of the predicate for a fixed response transform. It is not a covariance
theorem transporting a whole netlist along a phase gauge: matched-gauge covariance of connection
routing is an open N2a item and is not assumed anywhere in this file. -/
lemma isPassive_rephase_responseTransform_iff
    (hWellPosed : netlist.IsWellPosed)
    (gaugeIn : ModePhaseGauge netlist.ExternalIncident)
    (gaugeOut : ModePhaseGauge netlist.ExternalOutgoing) :
    ((netlist.responseTransform hWellPosed).rephase gaugeIn gaugeOut).IsPassive ↔
      (netlist.responseTransform hWellPosed).IsPassive :=
  ModeTransform.isPassive_rephase_iff gaugeIn gaugeOut _

/-- Losslessness of the external response is invariant under any external channel-end phase
gauge. -/
lemma isPowerPreserving_rephase_responseTransform_iff
    (hWellPosed : netlist.IsWellPosed)
    (gaugeIn : ModePhaseGauge netlist.ExternalIncident)
    (gaugeOut : ModePhaseGauge netlist.ExternalOutgoing) :
    ((netlist.responseTransform hWellPosed).rephase gaugeIn gaugeOut).IsPowerPreserving ↔
      (netlist.responseTransform hWellPosed).IsPowerPreserving :=
  ModeTransform.isPowerPreserving_rephase_iff gaugeIn gaugeOut _

/-- Losslessness of the packaged external scattering matrix is invariant under any external
channel phase gauge. -/
lemma externalScatteringMatrix_isLossless_rephase_iff
    (hWellPosed : netlist.IsWellPosed)
    (gaugeIn gaugeOut : ModePhaseGauge netlist.ExternalChannel) :
    ((netlist.externalScatteringMatrix hWellPosed).rephase gaugeIn gaugeOut).IsLossless ↔
      (netlist.externalScatteringMatrix hWellPosed).IsLossless :=
  ScatteringMatrix.isLossless_rephase_iff gaugeIn gaugeOut _

end Finite

end FlatNetlist

end

end Optics
