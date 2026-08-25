/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.ExternalChannel
public import Physlib.Optics.Network.RectangularBehavior
public import Physlib.Optics.Network.ScatteringComponentFamily

/-!
# Singular-safe semantics of flat scattering netlists

## i. Overview

A flat scattering netlist combines a typed family of fixed-frequency components with a
proof-carrying family of one-to-one port connections on the exact aggregate component boundary.
The component scattering transform `S`, partial internal routing `C`, external incident injection
`E_in`, and external outgoing readout `E_outᴴ` are derived rather than stored independently.

The solution behavior retains every complete incident/outgoing state satisfying the component and
return relations. The projected external behavior therefore relates `(u, y)` exactly when there
are ambient incident and outgoing amplitudes `a` and `b` satisfying

```text
b = S a,
a = C b + E_in u,
y = E_outᴴ b.
```

These relations remain meaningful when the feedback equation has no solution or several
solutions. Eliminating only the explicit component output gives the equivalent implicit equation
`(1 - C * S) a = E_in u`; no matrix inverse or uniqueness hypothesis is used.

## ii. Scope

This file gives fixed-frequency relational semantics, not a solver or executable compiler. It does
not assert that either behavior is total, single-valued, passive, lossless, reciprocal, causal, or
electromagnetically normalized. In particular, `1 - C * S` is not inverted here. Well-posedness
must later concern uniqueness of the complete solution state, which is stronger than uniqueness of
the externally observed output. `componentBehavior` is the graph of the already assembled
block-diagonal transform; identifying it with a dependent parallel composition of every local
component graph is a separate family-level theorem.

## iii. Key definitions and results

- `FlatNetlist`: component and connection data for a typed flat network.
- `FlatNetlist.scatteringTransform`: the block-diagonal component law `S`.
- `FlatNetlist.routingTransform`: the ambient partial-routing law `C`.
- `FlatNetlist.inputExposure` and `FlatNetlist.outputReadout`: the derived external boundary maps.
- `FlatNetlist.incidentAssemblyBehavior`: relational composition implementing `C b + E_in u`.
- `FlatNetlist.solutionBehavior`: every full state satisfying component and return relations.
- `FlatNetlist.behavior`: the singular-safe external behavior obtained by relational projection.
- `FlatNetlist.mem_behavior_iff_equations`: the exact three network equations.
- `FlatNetlist.mem_behavior_iff_feedbackEquation`: the equivalent implicit feedback relation.

## iv. Table of contents

- A. Flat netlists and shaped transforms
- B. Component and return behaviors
- C. Complete solution states
- D. External relational behavior
- E. The implicit feedback equation

-/

@[expose] public section

namespace Optics

noncomputable section

universe u v w x

/-!

## A. Flat netlists and shaped transforms

-/

-- The universe levels independently track component labels, local ports, local modes, and
-- connection labels.
set_option linter.checkUnivs false in
/-- A typed flat network of scattering components and one-to-one physical-port connections.

The connection family is defined on the aggregate component port family, so ill-typed mode
connections, reused physical endpoints, and component/wiring coordinate disagreement cannot be
supplied as netlist data.
-/
structure FlatNetlist where
  /-- The indexed fixed-frequency components and their local scattering laws. -/
  components : ScatteringComponentFamily.{u, v, w}
  /-- The type indexing the physical connections. -/
  Connection : Type x
  /-- The proof-carrying connections on the aggregate component boundary. -/
  connections : PortConnectionFamily components.aggregatePortModeFamily Connection

namespace FlatNetlist

variable (netlist : FlatNetlist.{u, v, w, x})

/-- The aggregate physical-port family of the netlist components. -/
abbrev PortFamily := netlist.components.aggregatePortModeFamily

/-- The aggregate physical channels of the netlist components. -/
abbrev Channel := netlist.PortFamily.Channel

/-- The dependent family of channels selected by internal connections. -/
abbrev ConnectedChannel := netlist.connections.Channel

/-- The aggregate channels not selected by an internal connection. -/
abbrev ExternalChannel := netlist.connections.ExternalChannel

/-- The full incident endpoint index of the aggregate component boundary. -/
abbrev IncidentIndex := Incident netlist.Channel

/-- The full outgoing endpoint index of the aggregate component boundary. -/
abbrev OutgoingIndex := Outgoing netlist.Channel

/-- The external incident endpoint index supplied to the network. -/
abbrev ExternalIncident := Incident netlist.ExternalChannel

/-- The external outgoing endpoint index exposed by the network. -/
abbrev ExternalOutgoing := Outgoing netlist.ExternalChannel

/-- The complete boundary-state index, with incident coordinates before outgoing coordinates. -/
abbrev SolutionIndex := netlist.IncidentIndex ⊕ netlist.OutgoingIndex

/-- The assembled block-diagonal scattering matrix of all netlist components. -/
def scatteringMatrix : ScatteringMatrix netlist.Channel := by
  classical
  exact netlist.components.assembledScatteringMatrix

/-- The assembled component law `S : A_in → A_out` with nominal endpoint wrappers retained. -/
def scatteringTransform : ModeTransform netlist.IncidentIndex netlist.OutgoingIndex :=
  netlist.scatteringMatrix.toOrientedModeTransform

/-- The partial internal-routing law `C : A_out → A_in` derived from physical connections. -/
abbrev routingTransform [Fintype netlist.ConnectedChannel]
    [DecidableEq netlist.ConnectedChannel] [DecidableEq netlist.Channel] :
    ModeTransform netlist.OutgoingIndex netlist.IncidentIndex :=
  netlist.connections.partialRouting

/-- The external incident injection `E_in : U → A_in`. -/
abbrev inputExposure [DecidableEq netlist.Channel] :
    ModeTransform netlist.ExternalIncident netlist.IncidentIndex :=
  netlist.connections.externalIncidentInjection

/-- The external outgoing exposure `E_out : Y → A_out`. -/
abbrev outputExposure [DecidableEq netlist.Channel] :
    ModeTransform netlist.ExternalOutgoing netlist.OutgoingIndex :=
  netlist.connections.externalOutgoingInjection

/-- The external outgoing readout `E_outᴴ : A_out → Y`. -/
abbrev outputReadout [DecidableEq netlist.Channel] :
    ModeTransform netlist.OutgoingIndex netlist.ExternalOutgoing :=
  netlist.connections.externalOutgoingReadout

/-- Netlist output readout is the adjoint of the derived output exposure. -/
lemma outputReadout_eq_conjTranspose [DecidableEq netlist.Channel] :
    netlist.outputReadout = Matrix.conjTranspose netlist.outputExposure := by
  exact netlist.connections.externalOutgoingReadout_eq_conjTranspose

/-!

## B. Component and return behaviors

-/

section Finite

variable [Fintype netlist.Channel]

/-- Classical equality on the aggregate channel type, kept local to finite matrix semantics. -/
local instance channelDecidableEq : DecidableEq netlist.Channel := Classical.decEq _

/-- The graph behavior of the assembled block-diagonal component scattering law. -/
def componentBehavior : LinearBehavior netlist.IncidentIndex netlist.OutgoingIndex :=
  netlist.scatteringTransform.toBehavior

/-- Component-behavior membership is exactly application of the assembled scattering transform. -/
@[simp]
lemma mem_componentBehavior_iff
    (incident : ModeAmplitude netlist.IncidentIndex)
    (outgoing : ModeAmplitude netlist.OutgoingIndex) :
    (incident, outgoing) ∈ netlist.componentBehavior ↔
      outgoing = netlist.scatteringTransform.toLinearMap incident := by
  classical
  exact ModeTransform.mem_toBehavior_iff_toLinearMap _ _ _

variable [Fintype netlist.ConnectedChannel]

/-- Classical equality on connected channels, kept local to derived routing semantics. -/
local instance connectedChannelDecidableEq : DecidableEq netlist.ConnectedChannel :=
  Classical.decEq _

/-- The external complement of finite aggregate and connected channel families is finite. -/
local instance externalChannelFintype : Fintype netlist.ExternalChannel := by
  classical
  infer_instance

/-- The relational construction of incident assembly.

Internal routing and external injection act independently in parallel, after which algebraic
coherent sum adds their two incident-space outputs. This use of coherent sum is vector addition,
not a physical combiner component.
-/
def incidentAssemblyBehavior :
    LinearBehavior (netlist.OutgoingIndex ⊕ netlist.ExternalIncident)
      netlist.IncidentIndex :=
  (netlist.routingTransform.toBehavior.parallel netlist.inputExposure.toBehavior).series
    (LinearBehavior.coherentSum :
      LinearBehavior (netlist.IncidentIndex ⊕ netlist.IncidentIndex) netlist.IncidentIndex)

/-- The relational incident assembly is exactly `a = C b + E_in u`. -/
@[simp]
lemma mem_incidentAssemblyBehavior_iff
    (outgoing : ModeAmplitude netlist.OutgoingIndex)
    (external : ModeAmplitude netlist.ExternalIncident)
    (incident : ModeAmplitude netlist.IncidentIndex) :
    (outgoing.directSum external, incident) ∈ netlist.incidentAssemblyBehavior ↔
      incident = netlist.connections.incidentAssembly outgoing external := by
  constructor
  · rintro ⟨middle, hParallel, hSum⟩
    rw [LinearBehavior.mem_parallel_iff] at hParallel
    simp only [ModeAmplitude.restrictInl_directSum,
      ModeAmplitude.restrictInr_directSum] at hParallel
    rcases hParallel with ⟨hRouting, hExposure⟩
    change middle.restrictInl = netlist.routingTransform.toLinearMap outgoing at hRouting
    change middle.restrictInr = netlist.inputExposure.toLinearMap external at hExposure
    rw [LinearBehavior.mem_coherentSum_iff] at hSum
    rw [hRouting, hExposure] at hSum
    simpa only [PortConnectionFamily.incidentAssembly] using hSum
  · intro hIncident
    refine ⟨(netlist.routingTransform.toLinearMap outgoing).directSum
      (netlist.inputExposure.toLinearMap external), ?_, ?_⟩
    · rw [LinearBehavior.mem_parallel_iff]
      simp only [ModeAmplitude.restrictInl_directSum,
        ModeAmplitude.restrictInr_directSum]
      exact ⟨rfl, rfl⟩
    · rw [LinearBehavior.mem_coherentSum_iff,
        ModeAmplitude.restrictInl_directSum,
        ModeAmplitude.restrictInr_directSum]
      simpa only [PortConnectionFamily.incidentAssembly] using hIncident

/-!

## C. Complete solution states

-/

/-- Every complete boundary state satisfying the assembled component and return behaviors.

The left state summand is the incident amplitude `a`; the right summand is the outgoing amplitude
`b`. No existence or uniqueness of a state is asserted.
-/
def solutionBehavior :
    LinearBehavior netlist.ExternalIncident netlist.SolutionIndex :=
  netlist.componentBehavior.feedbackSolutions netlist.incidentAssemblyBehavior

/-- A displayed state is a solution exactly when it satisfies the component and incident-assembly
relations. -/
@[simp]
lemma mem_solutionBehavior_directSum_iff
    (external : ModeAmplitude netlist.ExternalIncident)
    (incident : ModeAmplitude netlist.IncidentIndex)
    (outgoing : ModeAmplitude netlist.OutgoingIndex) :
    (external, incident.directSum outgoing) ∈ netlist.solutionBehavior ↔
      (incident, outgoing) ∈ netlist.componentBehavior ∧
        incident = netlist.connections.incidentAssembly outgoing external := by
  rw [solutionBehavior, LinearBehavior.mem_feedbackSolutions_directSum_iff,
    netlist.mem_incidentAssemblyBehavior_iff]

/-- A displayed solution state satisfies exactly `b = S a` and `a = C b + E_in u`. -/
lemma mem_solutionBehavior_directSum_iff_equations
    (external : ModeAmplitude netlist.ExternalIncident)
    (incident : ModeAmplitude netlist.IncidentIndex)
    (outgoing : ModeAmplitude netlist.OutgoingIndex) :
    (external, incident.directSum outgoing) ∈ netlist.solutionBehavior ↔
      outgoing = netlist.scatteringTransform.toLinearMap incident ∧
        incident = netlist.routingTransform.toLinearMap outgoing +
          netlist.inputExposure.toLinearMap external := by
  rw [netlist.mem_solutionBehavior_directSum_iff,
    netlist.mem_componentBehavior_iff, PortConnectionFamily.incidentAssembly]

/-!

## D. External relational behavior

-/

/-- The singular-safe external behavior obtained by relationally projecting complete solutions.

The first series step selects the outgoing summand of a solution state. The second applies the
derived external readout. Neither composition assumes that a solution exists uniquely.
-/
def behavior : LinearBehavior netlist.ExternalIncident netlist.ExternalOutgoing :=
  (netlist.solutionBehavior.series
    (LinearBehavior.selectRight :
      LinearBehavior netlist.SolutionIndex netlist.OutgoingIndex)).series
    netlist.outputReadout.toBehavior

/-- External behavior is relational composition of the complete solution relation and derived
output readout. -/
lemma mem_behavior_iff_componentBehavior
    (input : ModeAmplitude netlist.ExternalIncident)
    (output : ModeAmplitude netlist.ExternalOutgoing) :
    (input, output) ∈ netlist.behavior ↔
      ∃ incident outgoing,
        (incident, outgoing) ∈ netlist.componentBehavior ∧
          incident = netlist.connections.incidentAssembly outgoing input ∧
          output = netlist.outputReadout.toLinearMap outgoing := by
  constructor
  · rintro ⟨outgoing, ⟨state, hSolution, hSelect⟩, hReadout⟩
    rw [LinearBehavior.mem_selectRight_iff] at hSelect
    rw [ModeTransform.mem_toBehavior_iff_toLinearMap] at hReadout
    let incident := state.restrictInl
    let stateOutgoing := state.restrictInr
    have hState : state = incident.directSum stateOutgoing :=
      (ModeAmplitude.directSum_restrict state).symm
    have hSolution' :
        (input, incident.directSum stateOutgoing) ∈ netlist.solutionBehavior := by
      rw [← hState]
      exact hSolution
    rcases (netlist.mem_solutionBehavior_directSum_iff _ _ _).mp hSolution' with
      ⟨hComponent, hIncident⟩
    refine ⟨incident, stateOutgoing, hComponent, hIncident, ?_⟩
    change outgoing = stateOutgoing at hSelect
    change output = netlist.outputReadout.toLinearMap outgoing at hReadout
    rw [hSelect] at hReadout
    exact hReadout
  · rintro ⟨incident, outgoing, hComponent, hIncident, hOutput⟩
    refine ⟨outgoing, ⟨incident.directSum outgoing, ?_, ?_⟩, ?_⟩
    · exact (netlist.mem_solutionBehavior_directSum_iff _ _ _).mpr
        ⟨hComponent, hIncident⟩
    · rw [LinearBehavior.mem_selectRight_iff,
        ModeAmplitude.restrictInr_directSum]
    · exact (ModeTransform.mem_toBehavior_iff_toLinearMap _ _ _).mpr hOutput

/-- Netlist behavior membership is exactly the three shaped equations
`b = S a`, `a = C b + E_in u`, and `y = E_outᴴ b`. -/
lemma mem_behavior_iff_equations
    (input : ModeAmplitude netlist.ExternalIncident)
    (output : ModeAmplitude netlist.ExternalOutgoing) :
    (input, output) ∈ netlist.behavior ↔
      ∃ incident outgoing,
        outgoing = netlist.scatteringTransform.toLinearMap incident ∧
          incident = netlist.routingTransform.toLinearMap outgoing +
            netlist.inputExposure.toLinearMap input ∧
          output = netlist.outputReadout.toLinearMap outgoing := by
  rw [netlist.mem_behavior_iff_componentBehavior]
  simp only [netlist.mem_componentBehavior_iff,
    PortConnectionFamily.incidentAssembly]

/-!

## E. The implicit feedback equation

-/

/-- The incident-space feedback operator `1 - C * S`, without any invertibility claim. -/
def feedbackOperator : ModeTransform netlist.IncidentIndex netlist.IncidentIndex :=
  1 - netlist.routingTransform * netlist.scatteringTransform

/-- Applying the feedback operator gives `a - C (S a)` in the incident space. -/
lemma feedbackOperator_apply (incident : ModeAmplitude netlist.IncidentIndex) :
    netlist.feedbackOperator.toLinearMap incident =
      incident - netlist.routingTransform.toLinearMap
        (netlist.scatteringTransform.toLinearMap incident) := by
  simp only [feedbackOperator, ModeTransform.toLinearMap, map_sub,
    Matrix.toLpLin_one, LinearMap.sub_apply, LinearMap.id_apply,
    Matrix.toLpLin_mul_same, LinearMap.comp_apply]

/-- A complete state is a solution exactly when its outgoing part obeys component scattering and
its incident part obeys the implicit feedback equation. -/
lemma mem_solutionBehavior_directSum_iff_scattering_feedbackEquation
    (external : ModeAmplitude netlist.ExternalIncident)
    (incident : ModeAmplitude netlist.IncidentIndex)
    (outgoing : ModeAmplitude netlist.OutgoingIndex) :
    (external, incident.directSum outgoing) ∈ netlist.solutionBehavior ↔
      outgoing = netlist.scatteringTransform.toLinearMap incident ∧
        netlist.feedbackOperator.toLinearMap incident =
          netlist.inputExposure.toLinearMap external := by
  rw [netlist.mem_solutionBehavior_directSum_iff_equations]
  constructor
  · rintro ⟨hScattering, hIncident⟩
    refine ⟨hScattering, ?_⟩
    rw [netlist.feedbackOperator_apply, ← hScattering, hIncident]
    abel
  · rintro ⟨hScattering, hFeedback⟩
    refine ⟨hScattering, ?_⟩
    rw [netlist.feedbackOperator_apply, ← hScattering] at hFeedback
    exact (sub_eq_iff_eq_add.mp hFeedback).trans (add_comm _ _)

/-- An incident amplitude extends to a complete solution exactly when it satisfies the implicit
feedback equation. The outgoing witness is then fixed by component scattering, but the incident
solution itself need not exist uniquely for a given external input. -/
lemma exists_outgoing_mem_solutionBehavior_iff_feedbackEquation
    (external : ModeAmplitude netlist.ExternalIncident)
    (incident : ModeAmplitude netlist.IncidentIndex) :
    (∃ outgoing,
        (external, incident.directSum outgoing) ∈ netlist.solutionBehavior) ↔
      netlist.feedbackOperator.toLinearMap incident =
        netlist.inputExposure.toLinearMap external := by
  constructor
  · rintro ⟨outgoing, hSolution⟩
    exact (netlist.mem_solutionBehavior_directSum_iff_scattering_feedbackEquation
      external incident outgoing).mp hSolution |>.2
  · intro hFeedback
    exact ⟨netlist.scatteringTransform.toLinearMap incident,
      (netlist.mem_solutionBehavior_directSum_iff_scattering_feedbackEquation
        external incident _).mpr ⟨rfl, hFeedback⟩⟩

/-- The external relation can equivalently eliminate `b` and retain the implicit feedback
equation. This is substitution only: it does not invert `1 - C * S` or choose a solution. -/
lemma mem_behavior_iff_feedbackEquation
    (input : ModeAmplitude netlist.ExternalIncident)
    (output : ModeAmplitude netlist.ExternalOutgoing) :
    (input, output) ∈ netlist.behavior ↔
      ∃ incident,
        netlist.feedbackOperator.toLinearMap incident =
            netlist.inputExposure.toLinearMap input ∧
          output = netlist.outputReadout.toLinearMap
            (netlist.scatteringTransform.toLinearMap incident) := by
  rw [netlist.mem_behavior_iff_equations]
  constructor
  · rintro ⟨incident, outgoing, hScattering, hIncident, hOutput⟩
    refine ⟨incident, ?_, ?_⟩
    · rw [netlist.feedbackOperator_apply, ← hScattering, hIncident]
      abel
    · simpa only [hScattering] using hOutput
  · rintro ⟨incident, hFeedback, hOutput⟩
    refine ⟨incident, netlist.scatteringTransform.toLinearMap incident, rfl, ?_, hOutput⟩
    rw [netlist.feedbackOperator_apply] at hFeedback
    exact (sub_eq_iff_eq_add.mp hFeedback).trans (add_comm _ _)

end Finite

end FlatNetlist

end

end Optics
