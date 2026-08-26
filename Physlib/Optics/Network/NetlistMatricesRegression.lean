/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.NetlistDataRegression
public import Physlib.Optics.Network.NetlistMatrices

/-!
# Regression tests for executable finite-netlist matrices

## i. Overview

The certified two-component integer fixture is compiled to exact executable `S`, `C`, `E_in`,
`E_out`, and output-readout matrices. Asymmetric entries pin matrix orientation, distinct component
indices pin block separation, and the two directed endpoint wrappers of one physical link pin the
mate routing convention. A nonzero kernel vector keeps the derived feedback matrix singular, and
the same witness produces the external output `(1, 2)` at zero input through the generic semantic
bridge, proving that executable compilation retains multivalued relational behavior. A second
member sends nonzero input `(1, -1)` to `(0, 2)`, exercising external injection, while a three-mode
cycle distinguishes the stored forward and inverse mode tables in the routing matrix.

## ii. Key results

## iii. Table of contents

- A. Raw aggregate channels
- B. Executable scattering, routing, and exposure entries
- C. Singular feedback and relational soundness
- D. Non-self-inverse mode-map routing

## iv. References

These are exact algebraic compiler sentinels. They make no passivity, losslessness, reciprocity,
causality, inverse, determinant, or unique-solvability claim.

-/

@[expose] public section

namespace Optics

/-- The raw aggregate fixture retains the compiler's constructive finite enumeration. -/
local instance netlistMatricesRegressionChannelFintype :
    Fintype netlistDataRegressionShape.Channel := by
    letI : Fintype netlistDataRegressionShape.IndexedChannel := by
      change Fintype (Σ component : netlistDataRegressionShape.Component,
        Σ port : netlistDataRegressionShape.LocalPort component,
          Fin (netlistDataRegressionShape.modeCount component port))
      infer_instance
    exact Fintype.ofEquiv netlistDataRegressionShape.IndexedChannel
      netlistDataRegressionShape.indexedChannelEquiv

/-- The raw aggregate fixture retains the compiler's constructive equality decision. -/
local instance netlistMatricesRegressionChannelDecidableEq :
    DecidableEq netlistDataRegressionShape.Channel := by
    letI : DecidableEq netlistDataRegressionShape.IndexedChannel := by
      change DecidableEq (Σ component : netlistDataRegressionShape.Component,
        Σ port : netlistDataRegressionShape.LocalPort component,
          Fin (netlistDataRegressionShape.modeCount component port))
      infer_instance
    exact netlistDataRegressionShape.indexedChannelEquiv.symm.decidableEq

/-- The data projection exposes the same aggregate-channel enumeration. -/
local instance netlistMatricesRegressionDataChannelFintype :
    Fintype netlistDataRegression.shape.Channel := by
  change Fintype netlistDataRegressionShape.Channel
  exact netlistMatricesRegressionChannelFintype

/-- The data projection exposes the same aggregate-channel equality decision. -/
local instance netlistMatricesRegressionDataChannelDecidableEq :
    DecidableEq netlistDataRegression.shape.Channel := by
  change DecidableEq netlistDataRegressionShape.Channel
  exact netlistMatricesRegressionChannelDecidableEq

/-- Stored connection-local channels retain constructive finite enumeration. -/
local instance netlistMatricesRegressionConnectedChannelFintype :
    Fintype netlistDataRegression.ConnectedChannel := by
    change Fintype (Σ index : netlistDataRegression.Connection,
      netlistDataRegressionShape.Mode
          (netlistDataRegression.connection index).first ⊕
        netlistDataRegressionShape.Mode
          (netlistDataRegression.connection index).second)
    infer_instance

/-- Stored connection-local channels retain constructive equality. -/
local instance netlistMatricesRegressionConnectedChannelDecidableEq :
    DecidableEq netlistDataRegression.ConnectedChannel := by
    change DecidableEq (Σ index : netlistDataRegression.Connection,
      netlistDataRegressionShape.Mode
          (netlistDataRegression.connection index).first ⊕
        netlistDataRegressionShape.Mode
          (netlistDataRegression.connection index).second)
    infer_instance

/-- The exact complement of the finite raw channel image is finite. -/
noncomputable local instance netlistMatricesRegressionExternalChannelFintype :
    Fintype netlistDataRegression.ExternalChannel := by
  exact Fintype.ofInjective Subtype.val Subtype.val_injective

/-- Raw incident labels inherit the raw channel enumeration. -/
local instance netlistMatricesRegressionIncidentFintype :
    Fintype (Incident netlistDataRegressionShape.Channel) :=
  Incident.fintypeOf netlistMatricesRegressionChannelFintype

/-- Raw outgoing labels inherit the raw channel enumeration. -/
local instance netlistMatricesRegressionOutgoingFintype :
    Fintype (Outgoing netlistDataRegressionShape.Channel) :=
  Outgoing.fintypeOf netlistMatricesRegressionChannelFintype

/-- The data projection exposes the same raw incident enumeration. -/
local instance netlistMatricesRegressionDataIncidentFintype :
    Fintype (Incident netlistDataRegression.shape.Channel) := by
  change Fintype (Incident netlistDataRegressionShape.Channel)
  exact netlistMatricesRegressionIncidentFintype

/-- The data projection exposes the same raw outgoing enumeration. -/
local instance netlistMatricesRegressionDataOutgoingFintype :
    Fintype (Outgoing netlistDataRegression.shape.Channel) := by
  change Fintype (Outgoing netlistDataRegressionShape.Channel)
  exact netlistMatricesRegressionOutgoingFintype

/-- Raw external incident labels inherit the exact-complement enumeration. -/
noncomputable local instance netlistMatricesRegressionExternalIncidentFintype :
    Fintype (Incident netlistDataRegression.ExternalChannel) :=
  Incident.fintypeOf netlistMatricesRegressionExternalChannelFintype

/-- Raw external outgoing labels inherit the exact-complement enumeration. -/
noncomputable local instance netlistMatricesRegressionExternalOutgoingFintype :
    Fintype (Outgoing netlistDataRegression.ExternalChannel) :=
  Outgoing.fintypeOf netlistMatricesRegressionExternalChannelFintype

/-!

## A. Raw aggregate channels

-/

/-- An aggregate fixture channel selected by component and local port. -/
def netlistMatricesRegressionChannel
    (component : netlistDataRegressionShape.Component)
    (port : netlistDataRegressionShape.LocalPort component) :
    netlistDataRegressionShape.Channel :=
  netlistDataRegressionShape.indexedChannelEquiv
    ⟨component, netlistDataRegressionLocalChannel component port⟩

/-- Component A's external aggregate channel. -/
abbrev netlistMatricesRegressionAExternal : netlistDataRegressionShape.Channel :=
  netlistMatricesRegressionChannel netlistDataRegressionComponentA
    (netlistDataRegressionExternalPort netlistDataRegressionComponentA).2

/-- Component A's connected aggregate channel. -/
abbrev netlistMatricesRegressionALink : netlistDataRegressionShape.Channel :=
  netlistMatricesRegressionChannel netlistDataRegressionComponentA
    (netlistDataRegressionLinkPort netlistDataRegressionComponentA).2

/-- Component B's external aggregate channel. -/
abbrev netlistMatricesRegressionBExternal : netlistDataRegressionShape.Channel :=
  netlistMatricesRegressionChannel netlistDataRegressionComponentB
    (netlistDataRegressionExternalPort netlistDataRegressionComponentB).2

/-- Component B's connected aggregate channel. -/
abbrev netlistMatricesRegressionBLink : netlistDataRegressionShape.Channel :=
  netlistMatricesRegressionChannel netlistDataRegressionComponentB
    (netlistDataRegressionLinkPort netlistDataRegressionComponentB).2

/-- The first stored connection-local channel. -/
abbrev netlistMatricesRegressionConnectedA : netlistDataRegression.ConnectedChannel :=
  ⟨⟨0, by decide⟩,
    Sum.inl (netlistDataRegressionMode
      (netlistDataRegressionLinkPort netlistDataRegressionComponentA))⟩

/-- The second stored connection-local channel. -/
abbrev netlistMatricesRegressionConnectedB : netlistDataRegression.ConnectedChannel :=
  ⟨⟨0, by decide⟩,
    Sum.inr (netlistDataRegressionMode
      (netlistDataRegressionLinkPort netlistDataRegressionComponentB))⟩

/-- Every fixture external port lies outside the stored link-channel image. -/
lemma netlistMatricesRegression_external_not_mem_range
    (component : netlistDataRegressionShape.Component) :
    netlistMatricesRegressionChannel component
        (netlistDataRegressionExternalPort component).2 ∉
      Set.range netlistDataRegression.connectedChannelMap := by
  fin_cases component <;>
    rintro ⟨⟨index, mode⟩, hChannel⟩ <;>
    fin_cases index <;>
    rcases mode with mode | mode <;> fin_cases mode
  all_goals
    have hPort := congrArg (fun channel => channel.1.2.val) hChannel
    change (1 : ℕ) = 0 at hPort
    omega

/-- Component A's external channel is outside the stored connection image. -/
def netlistMatricesRegressionExternalA : netlistDataRegression.ExternalChannel :=
  ⟨netlistMatricesRegressionAExternal,
    netlistMatricesRegression_external_not_mem_range netlistDataRegressionComponentA⟩

/-- Component B's external channel is outside the stored connection image. -/
def netlistMatricesRegressionExternalB : netlistDataRegression.ExternalChannel :=
  ⟨netlistMatricesRegressionBExternal,
    netlistMatricesRegression_external_not_mem_range netlistDataRegressionComponentB⟩

/-!

## B. Executable scattering, routing, and exposure entries

-/

/-- The asymmetric component-B link-to-external coefficient occupies the expected `S` entry. -/
lemma netlistMatricesRegression_scattering_BExternal_BLink :
    netlistDataRegression.scatteringMatrix
        (Outgoing.mk netlistMatricesRegressionBExternal)
        (Incident.mk netlistMatricesRegressionBLink) = 2 := by
  rfl

/-- The reverse component-B coefficient is one, so executable scattering was not transposed. -/
lemma netlistMatricesRegression_scattering_BLink_BExternal :
    netlistDataRegression.scatteringMatrix
        (Outgoing.mk netlistMatricesRegressionBLink)
        (Incident.mk netlistMatricesRegressionBExternal) = 1 := by
  rfl

/-- Executable scattering has no direct coefficient between distinct component blocks. -/
lemma netlistMatricesRegression_scattering_crossComponent :
    netlistDataRegression.scatteringMatrix
        (Outgoing.mk netlistMatricesRegressionBExternal)
        (Incident.mk netlistMatricesRegressionALink) = 0 := by
  decide

/-- Outgoing amplitude on A's link returns to the incident amplitude on B's mate channel. -/
lemma netlistMatricesRegression_routing_BLink_ALink :
    netlistDataRegression.routingMatrix
        (Incident.mk netlistMatricesRegressionBLink)
        (Outgoing.mk netlistMatricesRegressionALink) = 1 := by
  decide

/-- Outgoing amplitude on B's link returns to the incident amplitude on A's mate channel. -/
lemma netlistMatricesRegression_routing_ALink_BLink :
    netlistDataRegression.routingMatrix
        (Incident.mk netlistMatricesRegressionALink)
        (Outgoing.mk netlistMatricesRegressionBLink) = 1 := by
  decide

/-- A connected channel does not route back to itself. -/
lemma netlistMatricesRegression_routing_ALink_ALink :
    netlistDataRegression.routingMatrix
        (Incident.mk netlistMatricesRegressionALink)
        (Outgoing.mk netlistMatricesRegressionALink) = 0 := by
  decide

/-- An external outgoing channel contributes a zero column to internal mate routing. -/
lemma netlistMatricesRegression_routing_external :
    netlistDataRegression.routingMatrix
        (Incident.mk netlistMatricesRegressionALink)
        (Outgoing.mk netlistMatricesRegressionAExternal) = 0 := by
  decide

/-- External incident injection selects the exact ambient A coordinate. -/
lemma netlistMatricesRegression_inputExposure_AExternal :
    netlistDataRegression.inputExposureMatrix
        (Incident.mk netlistMatricesRegressionAExternal)
        (Incident.mk netlistMatricesRegressionExternalA) = 1 := by
  simpa only [netlistMatricesRegressionExternalA] using
    netlistDataRegression.inputExposureMatrix_entry netlistMatricesRegressionExternalA

/-- External incident injection does not leak from A's external coordinate to B's. -/
lemma netlistMatricesRegression_inputExposure_crossExternal :
    netlistDataRegression.inputExposureMatrix
        (Incident.mk netlistMatricesRegressionBExternal)
        (Incident.mk netlistMatricesRegressionExternalA) = 0 := by
  decide

/-- External output exposure selects the exact ambient B coordinate. -/
lemma netlistMatricesRegression_outputExposure_BExternal :
    netlistDataRegression.outputExposureMatrix
        (Outgoing.mk netlistMatricesRegressionBExternal)
        (Outgoing.mk netlistMatricesRegressionExternalB) = 1 := by
  simpa only [netlistMatricesRegressionExternalB] using
    netlistDataRegression.outputExposureMatrix_entry netlistMatricesRegressionExternalB

/-- The output readout selects B's external ambient coordinate. -/
lemma netlistMatricesRegression_outputReadout_BExternal :
    netlistDataRegression.outputReadoutMatrix
        (Outgoing.mk netlistMatricesRegressionExternalB)
        (Outgoing.mk netlistMatricesRegressionBExternal) = 1 := by
  simpa only [netlistMatricesRegressionExternalB] using
    netlistDataRegression.outputReadoutMatrix_entry netlistMatricesRegressionExternalB

/-- Exposure followed by readout is a boundary projector, not the ambient identity. -/
lemma netlistMatricesRegression_outputProjector_internal :
    (netlistDataRegression.outputExposureMatrix *
        netlistDataRegression.outputReadoutMatrix)
      (Outgoing.mk netlistMatricesRegressionALink)
      (Outgoing.mk netlistMatricesRegressionALink) = 0 := by
  classical
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro external _
  unfold FiniteNetlistData.outputExposureMatrix
  split
  · rename_i hEqual
    exfalso
    apply external.channel.2
    exact ⟨netlistMatricesRegressionConnectedA, hEqual⟩
  · exact zero_mul _

/-!

## C. Singular feedback and relational soundness

-/

/-- Equal incident amplitudes on the two link channels and zero external amplitudes. -/
def netlistMatricesRegressionKernelVector :
    Incident netlistDataRegressionShape.Channel → ℤ :=
  fun incident =>
    if incident.channel.1.2.val = 1 then 1 else 0

/-- The displayed link-supported vector is nonzero. -/
lemma netlistMatricesRegression_kernelVector_ne_zero :
    netlistMatricesRegressionKernelVector ≠ 0 := by
  intro hZero
  have hCoordinate := congrFun hZero (Incident.mk netlistMatricesRegressionALink)
  have hOne :
      netlistMatricesRegressionKernelVector
        (Incident.mk netlistMatricesRegressionALink) = 1 := by
    rfl
  rw [hOne] at hCoordinate
  norm_num at hCoordinate

/-- The executable `1 - C * S` remains singular on the certified fixture. -/
lemma netlistMatricesRegression_feedbackMatrix_kernel :
    Matrix.mulVec netlistDataRegression.feedbackMatrix
        netlistMatricesRegressionKernelVector = 0 := by
  decide

/-- Integer outgoing coordinates corresponding to the unit internal-link incident state. -/
def netlistMatricesRegressionOutgoingInt :
    Outgoing netlistDataRegressionShape.Channel → ℤ :=
  fun outgoing =>
    if outgoing.channel.1.1.val = 0 then 1
    else if outgoing.channel.1.2.val = 0 then 2 else 1

/-- Raw executable scattering sends the unit link state to the displayed outgoing state. -/
lemma netlistMatricesRegression_scattering_mulVec_int :
    Matrix.mulVec netlistDataRegression.scatteringMatrix
        netlistMatricesRegressionKernelVector =
      netlistMatricesRegressionOutgoingInt := by
  funext output
  rcases output with ⟨⟨⟨component, port⟩, mode⟩⟩
  fin_cases component <;> fin_cases port <;>
    change Fin 1 at mode <;> fin_cases mode <;> decide

/-- Raw executable mate routing returns the displayed outgoing state to the unit link state. -/
lemma netlistMatricesRegression_routing_mulVec_int :
    Matrix.mulVec netlistDataRegression.routingMatrix
        netlistMatricesRegressionOutgoingInt =
      netlistMatricesRegressionKernelVector := by
  funext incident
  rcases incident with ⟨⟨⟨component, port⟩, mode⟩⟩
  fin_cases component <;> fin_cases port <;>
    change Fin 1 at mode <;> fin_cases mode <;> decide

/-- The evaluated unit link-supported incident state on the compiled typed boundary. -/
def netlistMatricesRegressionIncidentOne :
    ModeAmplitude netlistDataRegressionFlatNetlist.IncidentIndex :=
  WithLp.toLp 2 fun incident =>
    netlistDataRegressionEvaluate
      (netlistMatricesRegressionKernelVector (Incident.mk incident.channel))

/-- The evaluated outgoing state generated by the unit link-supported incident state. -/
def netlistMatricesRegressionOutgoingOne :
    ModeAmplitude netlistDataRegressionFlatNetlist.OutgoingIndex :=
  WithLp.toLp 2 fun outgoing =>
    netlistDataRegressionEvaluate
      (netlistMatricesRegressionOutgoingInt (Outgoing.mk outgoing.channel))

/-- External readout of the evaluated unit-parameter outgoing state. -/
def netlistMatricesRegressionOutputOne :
    ModeAmplitude netlistDataRegressionFlatNetlist.ExternalOutgoing :=
  WithLp.toLp 2 fun external =>
    netlistDataRegressionEvaluate
      (netlistMatricesRegressionOutgoingInt (Outgoing.mk external.channel.1))

/-- Component A's raw external channel transported to the compiled external index. -/
abbrev netlistMatricesRegressionTypedExternalA :
    netlistDataRegressionFlatNetlist.ExternalChannel :=
  netlistDataRegression.externalChannelEquiv netlistDataRegressionEvaluate
    netlistDataRegression_wellFormed netlistMatricesRegressionExternalA

/-- Component B's raw external channel transported to the compiled external index. -/
abbrev netlistMatricesRegressionTypedExternalB :
    netlistDataRegressionFlatNetlist.ExternalChannel :=
  netlistDataRegression.externalChannelEquiv netlistDataRegressionEvaluate
    netlistDataRegression_wellFormed netlistMatricesRegressionExternalB

/-- The compiled unit witness exposes amplitude one at component A's external output. -/
lemma netlistMatricesRegression_outputOne_AExternal :
    netlistMatricesRegressionOutputOne
        (Outgoing.mk netlistMatricesRegressionTypedExternalA) = 1 := by
  change netlistDataRegressionEvaluate
    (netlistMatricesRegressionOutgoingInt
      (Outgoing.mk netlistMatricesRegressionAExternal)) = 1
  have hComponent : netlistMatricesRegressionAExternal.1.1.val = 0 := rfl
  simp [netlistMatricesRegressionOutgoingInt, hComponent]

/-- The compiled unit witness exposes the asymmetric gain two at component B's external output. -/
lemma netlistMatricesRegression_outputOne_BExternal :
    netlistMatricesRegressionOutputOne
        (Outgoing.mk netlistMatricesRegressionTypedExternalB) = 2 := by
  change netlistDataRegressionEvaluate
    (netlistMatricesRegressionOutgoingInt
      (Outgoing.mk netlistMatricesRegressionBExternal)) = 2
  have hComponent : netlistMatricesRegressionBExternal.1.1.val = 1 := rfl
  have hPort : netlistMatricesRegressionBExternal.1.2.val = 0 := rfl
  simp [netlistMatricesRegressionOutgoingInt, hComponent, hPort]

/-- The compiled unit witness has a nonzero external output. -/
lemma netlistMatricesRegression_outputOne_ne_zero :
    netlistMatricesRegressionOutputOne ≠ 0 := by
  intro hOutput
  have hCoordinate := congrFun (congrArg WithLp.ofLp hOutput)
    (Outgoing.mk netlistMatricesRegressionTypedExternalA)
  rw [netlistMatricesRegression_outputOne_AExternal] at hCoordinate
  norm_num at hCoordinate

/-- Integer external input values `(1, -1)` on components A and B. -/
def netlistMatricesRegressionNonzeroInputInt
    (channel : netlistDataRegressionShape.Channel) : ℤ :=
  if channel.1.1.val = 0 then 1 else -1

/-- Integer incident coordinates `(1, 0, -1, 1)` in component/port order. -/
def netlistMatricesRegressionNonzeroIncidentInt :
    Incident netlistDataRegressionShape.Channel → ℤ :=
  fun incident =>
    if incident.channel.1.1.val = 0 then
      if incident.channel.1.2.val = 0 then 1 else 0
    else if incident.channel.1.2.val = 0 then -1 else 1

/-- Integer outgoing coordinates `(0, 1, 2, 0)` in component/port order. -/
def netlistMatricesRegressionNonzeroOutgoingInt :
    Outgoing netlistDataRegressionShape.Channel → ℤ :=
  fun outgoing =>
    if outgoing.channel.1.1.val = 0 then
      if outgoing.channel.1.2.val = 0 then 0 else 1
    else if outgoing.channel.1.2.val = 0 then 2 else 0

/-- The routed part `(0, 0, 0, 1)` of the nonzero-input incident state. -/
def netlistMatricesRegressionNonzeroRoutingInt :
    Incident netlistDataRegressionShape.Channel → ℤ :=
  fun incident =>
    if incident.channel.1.1.val = 0 then 0
    else if incident.channel.1.2.val = 0 then 0 else 1

/-- The externally injected part `(1, 0, -1, 0)` of the incident state. -/
def netlistMatricesRegressionNonzeroInjectionInt :
    Incident netlistDataRegressionShape.Channel → ℤ :=
  fun incident =>
    if incident.channel.1.2.val = 0 then
      if incident.channel.1.1.val = 0 then 1 else -1
    else 0

/-- Raw external input coordinates before evaluation and external-channel relabeling. -/
def netlistMatricesRegressionNonzeroRawInput :
    Incident netlistDataRegression.ExternalChannel → ℤ :=
  fun external =>
    netlistMatricesRegressionNonzeroInputInt external.channel.1

/-- Raw scattering sends the displayed nonzero-input incident state to its outgoing state. -/
lemma netlistMatricesRegression_scattering_mulVec_nonzero :
    Matrix.mulVec netlistDataRegression.scatteringMatrix
        netlistMatricesRegressionNonzeroIncidentInt =
      netlistMatricesRegressionNonzeroOutgoingInt := by
  funext output
  rcases output with ⟨⟨⟨component, port⟩, mode⟩⟩
  fin_cases component <;> fin_cases port <;>
    change Fin 1 at mode <;> fin_cases mode <;> decide

/-- Raw mate routing extracts the displayed internal part of the nonzero-input incident state. -/
lemma netlistMatricesRegression_routing_mulVec_nonzero :
    Matrix.mulVec netlistDataRegression.routingMatrix
        netlistMatricesRegressionNonzeroOutgoingInt =
      netlistMatricesRegressionNonzeroRoutingInt := by
  funext incident
  rcases incident with ⟨⟨⟨component, port⟩, mode⟩⟩
  fin_cases component <;> fin_cases port <;>
    change Fin 1 at mode <;> fin_cases mode <;> decide

/-- The displayed incident state is the sum of its routed and externally injected parts. -/
lemma netlistMatricesRegression_nonzeroIncidentInt_eq_routing_add_injection :
    netlistMatricesRegressionNonzeroIncidentInt =
      netlistMatricesRegressionNonzeroRoutingInt +
        netlistMatricesRegressionNonzeroInjectionInt := by
  funext incident
  rcases incident with ⟨⟨⟨component, port⟩, mode⟩⟩
  fin_cases component <;> fin_cases port <;>
    change Fin 1 at mode <;> fin_cases mode <;> decide

/-- Raw executable exposure injects `(1, -1)` only at the two external coordinates. -/
lemma netlistMatricesRegression_inputExposure_mulVec_nonzero :
    Matrix.mulVec netlistDataRegression.inputExposureMatrix
        netlistMatricesRegressionNonzeroRawInput =
      netlistMatricesRegressionNonzeroInjectionInt := by
  funext incident
  rcases incident with ⟨⟨⟨component, port⟩, mode⟩⟩
  fin_cases component <;> fin_cases port <;>
    change Fin 1 at mode <;> fin_cases mode
  · change Matrix.mulVec netlistDataRegression.inputExposureMatrix _
        (Incident.mk netlistMatricesRegressionExternalA.1) = 1
    calc
      _ = netlistMatricesRegressionNonzeroInputInt
          netlistMatricesRegressionExternalA.1 :=
        netlistDataRegression.inputExposureMatrix_mulVec_external
          netlistMatricesRegressionNonzeroRawInput
          netlistMatricesRegressionExternalA
      _ = 1 := by rfl
  · change Matrix.mulVec netlistDataRegression.inputExposureMatrix _
        (Incident.mk (netlistDataRegression.connectedChannelMap
          netlistMatricesRegressionConnectedA)) = 0
    exact netlistDataRegression.inputExposureMatrix_mulVec_connected
      netlistMatricesRegressionNonzeroRawInput
      netlistMatricesRegressionConnectedA
  · change Matrix.mulVec netlistDataRegression.inputExposureMatrix _
        (Incident.mk netlistMatricesRegressionExternalB.1) = -1
    calc
      _ = netlistMatricesRegressionNonzeroInputInt
          netlistMatricesRegressionExternalB.1 :=
        netlistDataRegression.inputExposureMatrix_mulVec_external
          netlistMatricesRegressionNonzeroRawInput
          netlistMatricesRegressionExternalB
      _ = -1 := by rfl
  · change Matrix.mulVec netlistDataRegression.inputExposureMatrix _
        (Incident.mk (netlistDataRegression.connectedChannelMap
          netlistMatricesRegressionConnectedB)) = 0
    exact netlistDataRegression.inputExposureMatrix_mulVec_connected
      netlistMatricesRegressionNonzeroRawInput
      netlistMatricesRegressionConnectedB

/-- The evaluated nonzero external input on the compiled boundary. -/
def netlistMatricesRegressionNonzeroInput :
    ModeAmplitude netlistDataRegressionFlatNetlist.ExternalIncident :=
  WithLp.toLp 2 fun external =>
    netlistDataRegressionEvaluate
      (netlistMatricesRegressionNonzeroInputInt external.channel.1)

/-- The evaluated incident witness for the nonzero external input. -/
def netlistMatricesRegressionNonzeroIncident :
    ModeAmplitude netlistDataRegressionFlatNetlist.IncidentIndex :=
  WithLp.toLp 2 fun incident =>
    netlistDataRegressionEvaluate
      (netlistMatricesRegressionNonzeroIncidentInt (Incident.mk incident.channel))

/-- The evaluated routed contribution to the nonzero-input incident witness. -/
def netlistMatricesRegressionNonzeroRouting :
    ModeAmplitude netlistDataRegressionFlatNetlist.IncidentIndex :=
  WithLp.toLp 2 fun incident =>
    netlistDataRegressionEvaluate
      (netlistMatricesRegressionNonzeroRoutingInt (Incident.mk incident.channel))

/-- The evaluated injected contribution to the nonzero-input incident witness. -/
def netlistMatricesRegressionNonzeroInjection :
    ModeAmplitude netlistDataRegressionFlatNetlist.IncidentIndex :=
  WithLp.toLp 2 fun incident =>
    netlistDataRegressionEvaluate
      (netlistMatricesRegressionNonzeroInjectionInt (Incident.mk incident.channel))

/-- The evaluated outgoing witness for the nonzero external input. -/
def netlistMatricesRegressionNonzeroOutgoing :
    ModeAmplitude netlistDataRegressionFlatNetlist.OutgoingIndex :=
  WithLp.toLp 2 fun outgoing =>
    netlistDataRegressionEvaluate
      (netlistMatricesRegressionNonzeroOutgoingInt (Outgoing.mk outgoing.channel))

/-- External readout `(0, 2)` of the nonzero-input outgoing witness. -/
def netlistMatricesRegressionNonzeroOutput :
    ModeAmplitude netlistDataRegressionFlatNetlist.ExternalOutgoing :=
  WithLp.toLp 2 fun external =>
    netlistDataRegressionEvaluate
      (netlistMatricesRegressionNonzeroOutgoingInt (Outgoing.mk external.channel.1))

/-- Evaluated executable scattering maps the unit incident witness to its displayed outgoing
coordinates. -/
lemma netlistMatricesRegression_scatteringEquation_one :
    WithLp.ofLp netlistMatricesRegressionOutgoingOne =
      ModeTransform.mulVecWith
        (netlistDataRegression.compiledIncidentFintype
          netlistDataRegressionEvaluate netlistDataRegression_wellFormed)
        (netlistDataRegression.scatteringMatrixInTypedCoordinates
          netlistDataRegressionEvaluate netlistDataRegression_wellFormed)
        (WithLp.ofLp netlistMatricesRegressionIncidentOne) := by
  rw [Subsingleton.elim
    (netlistDataRegression.compiledIncidentFintype
      netlistDataRegressionEvaluate netlistDataRegression_wellFormed)
    netlistMatricesRegressionDataIncidentFintype]
  funext output
  change netlistDataRegressionEvaluate
      (netlistMatricesRegressionOutgoingInt (Outgoing.mk output.channel)) =
    Matrix.mulVec (netlistDataRegression.scatteringMatrix.map
      netlistDataRegressionEvaluate)
      (netlistDataRegressionEvaluate ∘ netlistMatricesRegressionKernelVector) output
  rw [← netlistMatricesRegression_scattering_mulVec_int]
  exact RingHom.map_mulVec netlistDataRegressionEvaluate
    netlistDataRegression.scatteringMatrix
    netlistMatricesRegressionKernelVector output

/-- Evaluated executable mate routing returns the unit outgoing witness to its incident state. -/
lemma netlistMatricesRegression_routingEquation_one :
    WithLp.ofLp netlistMatricesRegressionIncidentOne =
      ModeTransform.mulVecWith
        (netlistDataRegression.compiledOutgoingFintype
          netlistDataRegressionEvaluate netlistDataRegression_wellFormed)
        (netlistDataRegression.routingMatrixInTypedCoordinates
          netlistDataRegressionEvaluate netlistDataRegression_wellFormed)
        (WithLp.ofLp netlistMatricesRegressionOutgoingOne) := by
  rw [Subsingleton.elim
    (netlistDataRegression.compiledOutgoingFintype
      netlistDataRegressionEvaluate netlistDataRegression_wellFormed)
    netlistMatricesRegressionDataOutgoingFintype]
  funext incident
  change netlistDataRegressionEvaluate
      (netlistMatricesRegressionKernelVector (Incident.mk incident.channel)) =
    Matrix.mulVec (netlistDataRegression.routingMatrix.map
      netlistDataRegressionEvaluate)
      (netlistDataRegressionEvaluate ∘ netlistMatricesRegressionOutgoingInt) incident
  rw [← netlistMatricesRegression_routing_mulVec_int]
  exact RingHom.map_mulVec netlistDataRegressionEvaluate
    netlistDataRegression.routingMatrix
    netlistMatricesRegressionOutgoingInt incident

/-- Evaluated executable scattering maps the nonzero-input incident witness to its outgoing
coordinates. -/
lemma netlistMatricesRegression_scatteringEquation_nonzero :
    WithLp.ofLp netlistMatricesRegressionNonzeroOutgoing =
      ModeTransform.mulVecWith
        (netlistDataRegression.compiledIncidentFintype
          netlistDataRegressionEvaluate netlistDataRegression_wellFormed)
        (netlistDataRegression.scatteringMatrixInTypedCoordinates
          netlistDataRegressionEvaluate netlistDataRegression_wellFormed)
        (WithLp.ofLp netlistMatricesRegressionNonzeroIncident) := by
  rw [Subsingleton.elim
    (netlistDataRegression.compiledIncidentFintype
      netlistDataRegressionEvaluate netlistDataRegression_wellFormed)
    netlistMatricesRegressionDataIncidentFintype]
  funext output
  change netlistDataRegressionEvaluate
      (netlistMatricesRegressionNonzeroOutgoingInt (Outgoing.mk output.channel)) =
    Matrix.mulVec (netlistDataRegression.scatteringMatrix.map
      netlistDataRegressionEvaluate)
      (netlistDataRegressionEvaluate ∘ netlistMatricesRegressionNonzeroIncidentInt) output
  rw [← netlistMatricesRegression_scattering_mulVec_nonzero]
  exact RingHom.map_mulVec netlistDataRegressionEvaluate
    netlistDataRegression.scatteringMatrix
    netlistMatricesRegressionNonzeroIncidentInt output

/-- Evaluated executable mate routing produces the internal part of the nonzero-input witness. -/
lemma netlistMatricesRegression_routingEquation_nonzero :
    WithLp.ofLp netlistMatricesRegressionNonzeroRouting =
      ModeTransform.mulVecWith
        (netlistDataRegression.compiledOutgoingFintype
          netlistDataRegressionEvaluate netlistDataRegression_wellFormed)
        (netlistDataRegression.routingMatrixInTypedCoordinates
          netlistDataRegressionEvaluate netlistDataRegression_wellFormed)
        (WithLp.ofLp netlistMatricesRegressionNonzeroOutgoing) := by
  rw [Subsingleton.elim
    (netlistDataRegression.compiledOutgoingFintype
      netlistDataRegressionEvaluate netlistDataRegression_wellFormed)
    netlistMatricesRegressionDataOutgoingFintype]
  funext incident
  change netlistDataRegressionEvaluate
      (netlistMatricesRegressionNonzeroRoutingInt (Incident.mk incident.channel)) =
    Matrix.mulVec (netlistDataRegression.routingMatrix.map
      netlistDataRegressionEvaluate)
      (netlistDataRegressionEvaluate ∘ netlistMatricesRegressionNonzeroOutgoingInt) incident
  rw [← netlistMatricesRegression_routing_mulVec_nonzero]
  exact RingHom.map_mulVec netlistDataRegressionEvaluate
    netlistDataRegression.routingMatrix
    netlistMatricesRegressionNonzeroOutgoingInt incident

/-- Evaluated executable input exposure produces the injected part of the nonzero-input witness. -/
lemma netlistMatricesRegression_inputExposureEquation_nonzero :
    WithLp.ofLp netlistMatricesRegressionNonzeroInjection =
      ModeTransform.mulVecWith
        (netlistDataRegression.compiledExternalIncidentFintype
          netlistDataRegressionEvaluate netlistDataRegression_wellFormed)
        (netlistDataRegression.inputExposureMatrixInTypedCoordinates
          netlistDataRegressionEvaluate netlistDataRegression_wellFormed)
        (WithLp.ofLp netlistMatricesRegressionNonzeroInput) := by
  have hInput : WithLp.ofLp netlistMatricesRegressionNonzeroInput ∘
      Incident.relabelEquiv (netlistDataRegression.externalChannelEquiv
        netlistDataRegressionEvaluate netlistDataRegression_wellFormed) =
      netlistDataRegressionEvaluate ∘
        netlistMatricesRegressionNonzeroRawInput := by
    funext external
    rcases external with ⟨external⟩
    rfl
  rw [Subsingleton.elim
    (netlistDataRegression.compiledExternalIncidentFintype
      netlistDataRegressionEvaluate netlistDataRegression_wellFormed)
      (inferInstance : Fintype netlistDataRegressionFlatNetlist.ExternalIncident),
    ModeTransform.mulVecWith_inferInstance,
    FiniteNetlistData.inputExposureMatrixInTypedCoordinates,
    Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv, Equiv.symm_symm, hInput]
  funext incident
  change netlistDataRegressionEvaluate
      (netlistMatricesRegressionNonzeroInjectionInt (Incident.mk incident.channel)) =
    Matrix.mulVec (netlistDataRegression.inputExposureMatrix.map
      netlistDataRegressionEvaluate)
      (netlistDataRegressionEvaluate ∘ netlistMatricesRegressionNonzeroRawInput)
      (Incident.mk incident.channel)
  rw [← netlistMatricesRegression_inputExposure_mulVec_nonzero]
  exact RingHom.map_mulVec netlistDataRegressionEvaluate
    netlistDataRegression.inputExposureMatrix
    netlistMatricesRegressionNonzeroRawInput (Incident.mk incident.channel)

/-- The displayed nonzero-input incident state is the sum of its executable routing and exposure
actions. -/
lemma netlistMatricesRegression_incidentEquation_nonzero :
    WithLp.ofLp netlistMatricesRegressionNonzeroIncident =
      ModeTransform.mulVecWith
          (netlistDataRegression.compiledOutgoingFintype
            netlistDataRegressionEvaluate netlistDataRegression_wellFormed)
          (netlistDataRegression.routingMatrixInTypedCoordinates
            netlistDataRegressionEvaluate netlistDataRegression_wellFormed)
          (WithLp.ofLp netlistMatricesRegressionNonzeroOutgoing) +
        ModeTransform.mulVecWith
          (netlistDataRegression.compiledExternalIncidentFintype
            netlistDataRegressionEvaluate netlistDataRegression_wellFormed)
          (netlistDataRegression.inputExposureMatrixInTypedCoordinates
            netlistDataRegressionEvaluate netlistDataRegression_wellFormed)
          (WithLp.ofLp netlistMatricesRegressionNonzeroInput) := by
  calc
    _ = WithLp.ofLp netlistMatricesRegressionNonzeroRouting +
        WithLp.ofLp netlistMatricesRegressionNonzeroInjection := by
      funext incident
      change netlistDataRegressionEvaluate
          (netlistMatricesRegressionNonzeroIncidentInt (Incident.mk incident.channel)) =
        netlistDataRegressionEvaluate
            (netlistMatricesRegressionNonzeroRoutingInt (Incident.mk incident.channel)) +
          netlistDataRegressionEvaluate
            (netlistMatricesRegressionNonzeroInjectionInt (Incident.mk incident.channel))
      rw [congrFun
        netlistMatricesRegression_nonzeroIncidentInt_eq_routing_add_injection
        (Incident.mk incident.channel)]
      simp only [Pi.add_apply, map_add]
    _ = _ := by rw [netlistMatricesRegression_routingEquation_nonzero,
      netlistMatricesRegression_inputExposureEquation_nonzero]

/-- Evaluated executable readout produces external output `(0, 2)` for the nonzero input. -/
lemma netlistMatricesRegression_outputEquation_nonzero :
    WithLp.ofLp netlistMatricesRegressionNonzeroOutput =
      ModeTransform.mulVecWith
        (netlistDataRegression.compiledOutgoingFintype
          netlistDataRegressionEvaluate netlistDataRegression_wellFormed)
        (netlistDataRegression.outputReadoutMatrixInTypedCoordinates
          netlistDataRegressionEvaluate netlistDataRegression_wellFormed)
        (WithLp.ofLp netlistMatricesRegressionNonzeroOutgoing) := by
  rw [Subsingleton.elim
    (netlistDataRegression.compiledOutgoingFintype
      netlistDataRegressionEvaluate netlistDataRegression_wellFormed)
    netlistMatricesRegressionDataOutgoingFintype]
  funext external
  obtain ⟨external, rfl⟩ :=
    (Outgoing.relabelEquiv (netlistDataRegression.externalChannelEquiv
      netlistDataRegressionEvaluate netlistDataRegression_wellFormed)).surjective external
  rcases external with ⟨external⟩
  change netlistDataRegressionEvaluate
      (netlistMatricesRegressionNonzeroOutgoingInt (Outgoing.mk external.1)) =
    Matrix.mulVec (netlistDataRegression.outputReadoutMatrix.map
      netlistDataRegressionEvaluate)
      (netlistDataRegressionEvaluate ∘ netlistMatricesRegressionNonzeroOutgoingInt)
      (Outgoing.mk external)
  calc
    _ = netlistDataRegressionEvaluate
        (Matrix.mulVec netlistDataRegression.outputReadoutMatrix
          netlistMatricesRegressionNonzeroOutgoingInt (Outgoing.mk external)) := by
      congr 1
      exact (netlistDataRegression.outputReadoutMatrix_mulVec
        netlistMatricesRegressionNonzeroOutgoingInt external).symm
    _ = _ := RingHom.map_mulVec netlistDataRegressionEvaluate
      netlistDataRegression.outputReadoutMatrix
      netlistMatricesRegressionNonzeroOutgoingInt (Outgoing.mk external)

/-- Evaluated executable readout selects the two displayed external output coordinates. -/
lemma netlistMatricesRegression_outputEquation_one :
    WithLp.ofLp netlistMatricesRegressionOutputOne =
      ModeTransform.mulVecWith
        (netlistDataRegression.compiledOutgoingFintype
          netlistDataRegressionEvaluate netlistDataRegression_wellFormed)
        (netlistDataRegression.outputReadoutMatrixInTypedCoordinates
          netlistDataRegressionEvaluate netlistDataRegression_wellFormed)
        (WithLp.ofLp netlistMatricesRegressionOutgoingOne) := by
  rw [Subsingleton.elim
    (netlistDataRegression.compiledOutgoingFintype
      netlistDataRegressionEvaluate netlistDataRegression_wellFormed)
    netlistMatricesRegressionDataOutgoingFintype]
  funext external
  obtain ⟨external, rfl⟩ :=
    (Outgoing.relabelEquiv (netlistDataRegression.externalChannelEquiv
      netlistDataRegressionEvaluate netlistDataRegression_wellFormed)).surjective external
  rcases external with ⟨external⟩
  change netlistDataRegressionEvaluate
      (netlistMatricesRegressionOutgoingInt (Outgoing.mk external.1)) =
    Matrix.mulVec (netlistDataRegression.outputReadoutMatrix.map
      netlistDataRegressionEvaluate)
      (netlistDataRegressionEvaluate ∘ netlistMatricesRegressionOutgoingInt)
      (Outgoing.mk external)
  calc
    _ = netlistDataRegressionEvaluate
        (Matrix.mulVec netlistDataRegression.outputReadoutMatrix
          netlistMatricesRegressionOutgoingInt (Outgoing.mk external)) := by
      congr 1
      exact (netlistDataRegression.outputReadoutMatrix_mulVec
        netlistMatricesRegressionOutgoingInt external).symm
    _ = _ := RingHom.map_mulVec netlistDataRegressionEvaluate
      netlistDataRegression.outputReadoutMatrix
      netlistMatricesRegressionOutgoingInt (Outgoing.mk external)

/-- The soundness bridge sends the zero executable solution to the N4 external relation. -/
lemma netlistMatricesRegression_zero_mem_behavior :
    ((0, 0) : ModeAmplitude netlistDataRegressionFlatNetlist.ExternalIncident ×
      ModeAmplitude netlistDataRegressionFlatNetlist.ExternalOutgoing) ∈
        netlistDataRegressionFlatNetlist.behavior := by
  apply (netlistDataRegression.mem_toFlatNetlist_behavior_iff_matrixEquations
    netlistDataRegressionEvaluate netlistDataRegression_wellFormed 0 0).mpr
  refine ⟨0, 0, ?_, ?_, ?_⟩ <;>
    simp

/-- The executable unit internal-link state produces a nonzero zero-input external solution. -/
lemma netlistMatricesRegression_one_mem_behavior :
    ((0, netlistMatricesRegressionOutputOne) :
      ModeAmplitude netlistDataRegressionFlatNetlist.ExternalIncident ×
        ModeAmplitude netlistDataRegressionFlatNetlist.ExternalOutgoing) ∈
      netlistDataRegressionFlatNetlist.behavior := by
  apply (netlistDataRegression.mem_toFlatNetlist_behavior_iff_matrixEquations
    netlistDataRegressionEvaluate netlistDataRegression_wellFormed
    0 netlistMatricesRegressionOutputOne).mpr
  refine ⟨netlistMatricesRegressionIncidentOne, netlistMatricesRegressionOutgoingOne,
    netlistMatricesRegression_scatteringEquation_one, ?_,
    netlistMatricesRegression_outputEquation_one⟩
  simpa [ModeTransform.mulVecWith] using
    netlistMatricesRegression_routingEquation_one

/-- The second executable semantic witness has genuinely nonzero external input. -/
lemma netlistMatricesRegression_nonzeroInput_AExternal :
    netlistMatricesRegressionNonzeroInput
        (Incident.mk netlistMatricesRegressionTypedExternalA) = 1 := by
  change netlistDataRegressionEvaluate
    (netlistMatricesRegressionNonzeroInputInt netlistMatricesRegressionAExternal) = 1
  have hComponent : netlistMatricesRegressionAExternal.1.1.val = 0 := rfl
  simp [netlistMatricesRegressionNonzeroInputInt, hComponent]

/-- The second displayed external input coordinate is minus one. -/
lemma netlistMatricesRegression_nonzeroInput_BExternal :
    netlistMatricesRegressionNonzeroInput
        (Incident.mk netlistMatricesRegressionTypedExternalB) = -1 := by
  change netlistDataRegressionEvaluate
    (netlistMatricesRegressionNonzeroInputInt netlistMatricesRegressionBExternal) = -1
  have hComponent : netlistMatricesRegressionBExternal.1.1.val = 1 := rfl
  simp [netlistMatricesRegressionNonzeroInputInt, hComponent]

/-- The displayed external input is not the zero amplitude. -/
lemma netlistMatricesRegression_nonzeroInput_ne_zero :
    netlistMatricesRegressionNonzeroInput ≠ 0 := by
  intro hInput
  have hCoordinate := congrFun (congrArg WithLp.ofLp hInput)
    (Incident.mk netlistMatricesRegressionTypedExternalA)
  rw [netlistMatricesRegression_nonzeroInput_AExternal] at hCoordinate
  norm_num at hCoordinate

/-- The nonzero-input witness exposes amplitude two at component B's external output. -/
lemma netlistMatricesRegression_nonzeroOutput_BExternal :
    netlistMatricesRegressionNonzeroOutput
        (Outgoing.mk netlistMatricesRegressionTypedExternalB) = 2 := by
  change netlistDataRegressionEvaluate
    (netlistMatricesRegressionNonzeroOutgoingInt
      (Outgoing.mk netlistMatricesRegressionBExternal)) = 2
  have hComponent : netlistMatricesRegressionBExternal.1.1.val = 1 := rfl
  have hPort : netlistMatricesRegressionBExternal.1.2.val = 0 := rfl
  simp [netlistMatricesRegressionNonzeroOutgoingInt, hComponent, hPort]

/-- The displayed nonzero-input output vanishes at component A's external coordinate. -/
lemma netlistMatricesRegression_nonzeroOutput_AExternal :
    netlistMatricesRegressionNonzeroOutput
        (Outgoing.mk netlistMatricesRegressionTypedExternalA) = 0 := by
  change netlistDataRegressionEvaluate
    (netlistMatricesRegressionNonzeroOutgoingInt
      (Outgoing.mk netlistMatricesRegressionAExternal)) = 0
  have hComponent : netlistMatricesRegressionAExternal.1.1.val = 0 := rfl
  have hPort : netlistMatricesRegressionAExternal.1.2.val = 0 := rfl
  simp [netlistMatricesRegressionNonzeroOutgoingInt, hComponent, hPort]

/-- The generic executable equations produce the displayed nonzero-input external behavior. -/
lemma netlistMatricesRegression_nonzeroInput_mem_behavior :
    (netlistMatricesRegressionNonzeroInput, netlistMatricesRegressionNonzeroOutput) ∈
      netlistDataRegressionFlatNetlist.behavior := by
  apply (netlistDataRegression.mem_toFlatNetlist_behavior_iff_matrixEquations
    netlistDataRegressionEvaluate netlistDataRegression_wellFormed
    netlistMatricesRegressionNonzeroInput
    netlistMatricesRegressionNonzeroOutput).mpr
  exact ⟨netlistMatricesRegressionNonzeroIncident,
    netlistMatricesRegressionNonzeroOutgoing,
    netlistMatricesRegression_scatteringEquation_nonzero,
    netlistMatricesRegression_incidentEquation_nonzero,
    netlistMatricesRegression_outputEquation_nonzero⟩

/-- Executable singular-network semantics remains multivalued at zero external input. -/
lemma netlistMatricesRegression_behavior_not_singleValued :
    ¬netlistDataRegressionFlatNetlist.behavior.IsSingleValued := by
  intro hSingleValued
  apply netlistMatricesRegression_outputOne_ne_zero
  symm
  exact hSingleValued netlistMatricesRegression_zero_mem_behavior
    netlistMatricesRegression_one_mem_behavior

/-!

## D. Non-self-inverse mode-map routing

-/

/-- Two one-port components whose connected ports each carry three modes. -/
def netlistMatricesRegressionCycleShape : FiniteNetlistShape where
  componentCount := 2
  portCount := fun _ => 1
  modeCount := fun _ _ => 3

/-- A three-mode connection whose forward table is a cycle and whose inverse table is the
opposite cycle. -/
def netlistMatricesRegressionCycleConnection :
    FiniteConnectionSpec netlistMatricesRegressionCycleShape where
  first := ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩
  second := ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩
  modeMap := fun mode => finRotate 3 mode
  modeInv := fun mode => (finRotate 3).symm mode

/-- The valid three-mode cycle fixture with zero component scattering. -/
def netlistMatricesRegressionCycleData : FiniteNetlistData ℤ where
  shape := netlistMatricesRegressionCycleShape
  scattering := fun _ _ _ => 0
  connections := #[netlistMatricesRegressionCycleConnection]

/-- The forward/inverse cycle fixture passes the exact structural checker. -/
lemma netlistMatricesRegression_cycle_wellFormed :
    netlistMatricesRegressionCycleData.WellFormed := by
  decide

/-- The mode-zero channel at the first endpoint of the cycle connection. -/
def netlistMatricesRegressionCycleLeftZero :
    netlistMatricesRegressionCycleData.ConnectedChannel :=
  ⟨⟨0, by decide⟩, Sum.inl ⟨0, by decide⟩⟩

/-- The mode-zero channel at the second endpoint of the cycle connection. -/
def netlistMatricesRegressionCycleRightZero :
    netlistMatricesRegressionCycleData.ConnectedChannel :=
  ⟨⟨0, by decide⟩, Sum.inr ⟨0, by decide⟩⟩

/-- The aggregate mode-one channel at the second endpoint. -/
def netlistMatricesRegressionCycleRightOne :
    netlistMatricesRegressionCycleShape.Channel :=
  ⟨netlistMatricesRegressionCycleConnection.second, ⟨1, by decide⟩⟩

/-- The aggregate mode-two channel at the second endpoint. -/
def netlistMatricesRegressionCycleRightTwo :
    netlistMatricesRegressionCycleShape.Channel :=
  ⟨netlistMatricesRegressionCycleConnection.second, ⟨2, by decide⟩⟩

/-- The aggregate mode-one channel at the first endpoint. -/
def netlistMatricesRegressionCycleLeftOne :
    netlistMatricesRegressionCycleShape.Channel :=
  ⟨netlistMatricesRegressionCycleConnection.first, ⟨1, by decide⟩⟩

/-- The aggregate mode-two channel at the first endpoint. -/
def netlistMatricesRegressionCycleLeftTwo :
    netlistMatricesRegressionCycleShape.Channel :=
  ⟨netlistMatricesRegressionCycleConnection.first, ⟨2, by decide⟩⟩

/-- Raw routing uses the stored forward cycle from first-end mode zero to second-end mode one. -/
lemma netlistMatricesRegression_routing_modeMap_cycle :
    netlistMatricesRegressionCycleData.routingMatrix
        (Incident.mk netlistMatricesRegressionCycleRightOne)
        (Outgoing.mk (netlistMatricesRegressionCycleData.connectedChannelMap
          netlistMatricesRegressionCycleLeftZero)) = 1 := by
  decide

/-- The inverse-cycle target is absent from the forward routing column. -/
lemma netlistMatricesRegression_routing_modeMap_wrongTarget :
    netlistMatricesRegressionCycleData.routingMatrix
        (Incident.mk netlistMatricesRegressionCycleRightTwo)
        (Outgoing.mk (netlistMatricesRegressionCycleData.connectedChannelMap
          netlistMatricesRegressionCycleLeftZero)) = 0 := by
  decide

/-- Raw routing uses the distinct inverse cycle from second-end mode zero to first-end mode two. -/
lemma netlistMatricesRegression_routing_modeInv_cycle :
    netlistMatricesRegressionCycleData.routingMatrix
        (Incident.mk netlistMatricesRegressionCycleLeftTwo)
        (Outgoing.mk (netlistMatricesRegressionCycleData.connectedChannelMap
          netlistMatricesRegressionCycleRightZero)) = 1 := by
  decide

/-- The forward-cycle target is absent from the inverse routing column. -/
lemma netlistMatricesRegression_routing_modeInv_wrongTarget :
    netlistMatricesRegressionCycleData.routingMatrix
        (Incident.mk netlistMatricesRegressionCycleLeftOne)
        (Outgoing.mk (netlistMatricesRegressionCycleData.connectedChannelMap
          netlistMatricesRegressionCycleRightZero)) = 0 := by
  decide

end Optics
