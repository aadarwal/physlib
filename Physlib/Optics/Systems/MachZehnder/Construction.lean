/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Components.DirectionalCouplerPhysical
public import Physlib.Optics.Components.DirectionalCouplerPower
public import Physlib.Optics.Components.MatchedPropagationPhysical
public import Physlib.Optics.Network.FlatNetlistElimination

/-!
# Mach--Zehnder netlist construction and N5 elimination

## i. Overview

This file constructs a fixed-carrier Mach--Zehnder interferometer solely from two physical
directional couplers and two physical matched-propagation arms. The four components are joined by
four one-to-one physical-port connections and interpreted by the singular-safe `FlatNetlist`
semantics. The response is extracted only after proving complete-state well-posedness through N5.
No interferometer transfer matrix or output formula is stored in a definition.

The component parameters are exactly the N7 parameter structures declared at
`Physlib/Optics/Components/DirectionalCoupler.lean:62` and
`Physlib/Optics/Components/MatchedPropagation.lean:79`. The component family uses the physical
scattering laws at `DirectionalCouplerPhysical.lean:161` and
`MatchedPropagationPhysical.lean:167`. Their independently transported behaviors occur at
`DirectionalCouplerPhysical.lean:145` and `MatchedPropagationPhysical.lean:151`.

This system is the Physlib extension recorded at `goal.md:152-155` and `goal.md:2150-2160`; it is
not a HOL-corpus parity result. The response is algebraically defined for every `Parameters` value,
including arbitrary lossy or gaining couplers and arms. A physical interpretation is asserted only
under `Parameters.IsValid`, which uses the N7 validity domains at
`DirectionalCouplerPower.lean:67` and `MatchedPropagation.lean:90`; there the couplers are unitary
and attenuation can occur only through the two arm factors. The model has no polarization or
dispersion. The carrier phase is fixed-frequency, not a time-domain delay, as stated at
`Physlib/Optics/Components/MatchedPropagation.lean:93-103`. No reciprocity or time-reversed
external-port pairing is claimed.

## ii. Key results

- `MachZehnder.netlist`: the certified two-coupler, two-arm N4 flat netlist.
- `MachZehnder.isWellPosed`: complete-state well-posedness for all algebraic parameters.
- `MachZehnder.output_amplitudes`: the Mach--Zehnder transfer amplitudes extracted through N5.

## iii. Table of contents

- A. Parameters and component family
- B. Physical wiring and external channels
- C. Component and routing coordinate laws
- D. N5 well-posedness and extracted amplitudes

## iv. References

The reusable component laws are Physlib-original N7 interfaces. The Mach--Zehnder system row is a
Physlib extension; the exact program-ledger locations are quoted above.
-/

@[expose] public section

namespace Optics

noncomputable section

namespace MachZehnder

/-! ## A. Parameters and component family -/

/-- The two couplers and two fixed-carrier arms of a Mach--Zehnder interferometer. -/
structure Parameters where
  /-- The directional coupler at the left reference plane. -/
  inputCoupler : DirectionalCoupler.Parameters
  /-- The matched-propagation component in the upper arm. -/
  upperArm : MatchedPropagation.Parameters
  /-- The matched-propagation component in the lower arm. -/
  lowerArm : MatchedPropagation.Parameters
  /-- The directional coupler at the right reference plane. -/
  outputCoupler : DirectionalCoupler.Parameters

/-- All component parameters lie in their canonical N7 validity domains. -/
def Parameters.IsValid (p : Parameters) : Prop :=
  p.inputCoupler.IsValid ∧ p.upperArm.IsValid ∧ p.lowerArm.IsValid ∧
    p.outputCoupler.IsValid

/-- Every component preserves normalized modal power. -/
def Parameters.IsLossless (p : Parameters) : Prop :=
  p.inputCoupler.IsUnitary ∧ p.upperArm.amplitudeTransmission = 1 ∧
    p.lowerArm.amplitudeTransmission = 1 ∧ p.outputCoupler.IsUnitary

/-- The four component instances, ordered from the input coupler through the arms to the output
coupler. -/
inductive Component
  | inputCoupler
  | upperArm
  | lowerArm
  | outputCoupler

/-- Component labels have classical decidable equality for finite matrix assembly. -/
@[reducible]
noncomputable instance : DecidableEq Component := Classical.decEq _

/-- The four Mach--Zehnder component labels form a finite family. -/
instance : Fintype Component where
  elems := {.inputCoupler, .upperArm, .lowerArm, .outputCoupler}
  complete component := by cases component <;> simp

/-- Four single-mode local coordinates for a directional coupler. -/
@[reducible]
def couplerPortFamily : PortModeFamily where
  Port := Fin 4
  Mode := fun _ => Unit

/-- Two single-mode local coordinates for a matched-propagation arm. -/
@[reducible]
def armPortFamily : PortModeFamily where
  Port := Fin 2
  Mode := fun _ => Unit

/-- Local directional-coupler channels form a finite family. -/
instance : Fintype couplerPortFamily.Channel := by
  change Fintype (Sigma fun _ : Fin 4 => Unit)
  infer_instance

/-- Local directional-coupler channels have decidable equality. -/
instance : DecidableEq couplerPortFamily.Channel := by
  change DecidableEq (Sigma fun _ : Fin 4 => Unit)
  infer_instance

/-- Local matched-propagation channels form a finite family. -/
instance : Fintype armPortFamily.Channel := by
  change Fintype (Sigma fun _ : Fin 2 => Unit)
  infer_instance

/-- Local matched-propagation channels have decidable equality. -/
instance : DecidableEq armPortFamily.Channel := by
  change DecidableEq (Sigma fun _ : Fin 2 => Unit)
  infer_instance

/-- N7's physical directional-coupler port order as four local coordinates. -/
def couplerPortEquiv : DirectionalCoupler.Port ≃ Fin 4 where
  toFun
    | .leftFirst => 0
    | .leftSecond => 1
    | .rightFirst => 2
    | .rightSecond => 3
  invFun := ![.leftFirst, .leftSecond, .rightFirst, .rightSecond]
  left_inv := by intro port; cases port <;> rfl
  right_inv := by intro port; fin_cases port <;> rfl

/-- N7's physical matched-propagation port order as two local coordinates. -/
def armPortEquiv : MatchedPropagation.Port ≃ Fin 2 where
  toFun
    | .left => 0
    | .right => 1
  invFun := ![.left, .right]
  left_inv := by intro port; cases port <;> rfl
  right_inv := by intro port; fin_cases port <;> rfl

/-- N7's physical coupler channels relabeled by the system-local coordinates. -/
def couplerChannelEquiv :
    (DirectionalCoupler.portFamily Unit).Channel ≃ couplerPortFamily.Channel where
  toFun := fun channel => ⟨couplerPortEquiv channel.1, channel.2⟩
  invFun := fun channel => ⟨couplerPortEquiv.symm channel.1, channel.2⟩
  left_inv := by rintro ⟨port, mode⟩; cases port <;> cases mode <;> rfl
  right_inv := by
    rintro ⟨port, mode⟩
    change Fin 4 at port
    change Unit at mode
    fin_cases port <;> cases mode <;> rfl

/-- N7's physical propagation channels relabeled by the system-local coordinates. -/
def armChannelEquiv :
    (MatchedPropagation.portFamily Unit).Channel ≃ armPortFamily.Channel where
  toFun := fun channel => ⟨armPortEquiv channel.1, channel.2⟩
  invFun := fun channel => ⟨armPortEquiv.symm channel.1, channel.2⟩
  left_inv := by rintro ⟨port, mode⟩; cases port <;> cases mode <;> rfl
  right_inv := by
    rintro ⟨port, mode⟩
    change Fin 2 at port
    change Unit at mode
    fin_cases port <;> cases mode <;> rfl

/-- A directional-coupler channel at one of the four local coordinates. -/
def couplerChannel (port : Fin 4) : couplerPortFamily.Channel := ⟨port, ()⟩

/-- A matched-propagation channel at one of the two local coordinates. -/
def armChannel (port : Fin 2) : armPortFamily.Channel := ⟨port, ()⟩

/-- One N7 physical directional coupler in the system-local coordinates. -/
def couplerScattering (p : DirectionalCoupler.Parameters) :
    ScatteringMatrix couplerPortFamily.Channel :=
  (DirectionalCoupler.physicalScattering p Unit).reindex couplerChannelEquiv

/-- One N7 physical matched-propagation component in the system-local coordinates. -/
def armScattering (p : MatchedPropagation.Parameters) :
    ScatteringMatrix armPortFamily.Channel :=
  (MatchedPropagation.physicalScattering p Unit).reindex armChannelEquiv

/-- The local coordinate family owned by each system component. -/
@[reducible]
def componentPortFamily : Component → PortModeFamily
  | .inputCoupler => couplerPortFamily
  | .upperArm => armPortFamily
  | .lowerArm => armPortFamily
  | .outputCoupler => couplerPortFamily

/-- The N7 scattering components used by the Mach--Zehnder netlist. -/
@[reducible]
def components (p : Parameters) : ScatteringComponentFamily where
  Component := Component
  portFamily := componentPortFamily
  scattering
    | .inputCoupler => couplerScattering p.inputCoupler
    | .upperArm => armScattering p.upperArm
    | .lowerArm => armScattering p.lowerArm
    | .outputCoupler => couplerScattering p.outputCoupler

/-- Every local component channel family is finite. -/
instance componentChannelFintype (p : Parameters) (component : Component) :
    Fintype ((components p).portFamily component).Channel := by
  cases component <;> change Fintype (Sigma fun _ : Fin _ => Unit) <;> infer_instance

/-- Every local component channel family has decidable equality. -/
instance componentChannelDecidableEq (p : Parameters) (component : Component) :
    DecidableEq ((components p).portFamily component).Channel := by
  cases component <;> change DecidableEq (Sigma fun _ : Fin _ => Unit) <;> infer_instance

/-! ## B. Physical wiring and external channels -/

/-- The four arm-end connections between the two couplers and two propagation components. -/
inductive Connection
  | upperInput
  | lowerInput
  | upperOutput
  | lowerOutput
  deriving DecidableEq

/-- The four Mach--Zehnder internal connections form a finite family. -/
instance : Fintype Connection where
  elems := {.upperInput, .lowerInput, .upperOutput, .lowerOutput}
  complete index := by cases index <;> simp

/-- The physical connection selected by each arm end. -/
def connection (p : Parameters) (index : Connection) :
    PortConnection (components p).aggregatePortModeFamily :=
  match index with
  | .upperInput =>
      { left := ⟨Component.inputCoupler, (2 : Fin 4)⟩
        right := ⟨Component.upperArm, (0 : Fin 2)⟩
        left_ne_right := by intro h; cases congrArg Sigma.fst h
        modeEquiv := Equiv.refl Unit }
  | .lowerInput =>
      { left := ⟨Component.inputCoupler, (3 : Fin 4)⟩
        right := ⟨Component.lowerArm, (0 : Fin 2)⟩
        left_ne_right := by intro h; cases congrArg Sigma.fst h
        modeEquiv := Equiv.refl Unit }
  | .upperOutput =>
      { left := ⟨Component.upperArm, (1 : Fin 2)⟩
        right := ⟨Component.outputCoupler, (0 : Fin 4)⟩
        left_ne_right := by intro h; cases congrArg Sigma.fst h
        modeEquiv := Equiv.refl Unit }
  | .lowerOutput =>
      { left := ⟨Component.lowerArm, (1 : Fin 2)⟩
        right := ⟨Component.outputCoupler, (1 : Fin 4)⟩
        left_ne_right := by intro h; cases congrArg Sigma.fst h
        modeEquiv := Equiv.refl Unit }

/-- A numerical code separating every component-owned physical port. -/
def portCode (p : Parameters) :
    (components p).aggregatePortModeFamily.Port → Fin 12
  | ⟨.inputCoupler, port⟩ => ⟨port.val, by omega⟩
  | ⟨.upperArm, port⟩ => ⟨4 + port.val, by omega⟩
  | ⟨.lowerArm, port⟩ => ⟨6 + port.val, by omega⟩
  | ⟨.outputCoupler, port⟩ => ⟨8 + port.val, by omega⟩

/-- The four arm-end connections form a one-to-one physical-port connection family. -/
def connections (p : Parameters) :
    PortConnectionFamily (components p).aggregatePortModeFamily Connection where
  connection := connection p
  endpointPort_injective := by
    rintro ⟨firstIndex, firstEnd⟩ ⟨secondIndex, secondEnd⟩ hPort
    have hCode := congrArg (portCode p) hPort
    cases firstIndex <;> cases firstEnd <;>
      cases secondIndex <;> cases secondEnd
    all_goals first | rfl | (exfalso; norm_num [connection,
      PortConnection.endpointPort, portCode] at hCode)

/-- The N4 flat netlist containing exactly the two N7 couplers and two N7 propagation arms. -/
def netlist (p : Parameters) : FlatNetlist where
  components := components p
  Connection := Connection
  connections := connections p

/-- The component family retained by the compiled netlist is finite. -/
@[reducible]
instance netlistComponentFintype (p : Parameters) :
    Fintype (netlist p).components.Component := by
  change Fintype Component
  infer_instance

/-- The component labels retained by the compiled netlist have decidable equality. -/
@[reducible]
instance netlistComponentDecidableEq (p : Parameters) :
    DecidableEq (netlist p).components.Component := by
  change DecidableEq Component
  infer_instance

/-- Every component-local channel family retained by the compiled netlist is finite. -/
@[reducible]
instance netlistComponentChannelFintype (p : Parameters)
    (component : (netlist p).components.Component) :
    Fintype ((netlist p).components.portFamily component).Channel := by
  change Fintype ((components p).portFamily component).Channel
  exact componentChannelFintype p component

/-- Every component-local channel family retained by the compiled netlist has decidable
equality. -/
@[reducible]
instance netlistComponentChannelDecidableEq (p : Parameters)
    (component : (netlist p).components.Component) :
    DecidableEq ((netlist p).components.portFamily component).Channel := by
  change DecidableEq ((components p).portFamily component).Channel
  exact componentChannelDecidableEq p component

/-- Aggregate Mach--Zehnder channels are finite. -/
noncomputable instance indexedChannelFintype (p : Parameters) :
    Fintype (components p).IndexedChannel := by
  change Fintype (Sigma fun component : Component =>
    ((components p).portFamily component).Channel)
  infer_instance

/-- Aggregate component-indexed channels have decidable equality. -/
instance indexedChannelDecidableEq (p : Parameters) :
    DecidableEq (components p).IndexedChannel := by
  classical
  exact Classical.decEq _

/-- Aggregate Mach--Zehnder channels are finite. -/
noncomputable instance aggregateChannelFintype (p : Parameters) :
    Fintype (components p).aggregatePortModeFamily.Channel :=
  Fintype.ofEquiv (components p).IndexedChannel (components p).channelEquiv

/-- Aggregate Mach--Zehnder channels have decidable equality. -/
@[reducible]
instance aggregateChannelDecidableEq (p : Parameters) :
    DecidableEq (components p).aggregatePortModeFamily.Channel :=
  Classical.decEq _

/-- The compiled N4 Mach--Zehnder channel family retains the aggregate finite enumeration. -/
noncomputable instance channelFintype (p : Parameters) : Fintype (netlist p).Channel :=
  aggregateChannelFintype p

/-- The compiled N4 Mach--Zehnder channel family retains decidable equality. -/
@[reducible]
instance channelDecidableEq (p : Parameters) : DecidableEq (netlist p).Channel :=
  Classical.decEq _

/-- Connected Mach--Zehnder channels are finite. -/
instance connectionLocalChannelFintype (p : Parameters) (index : Connection) :
    Fintype (connection p index).LocalChannel := by
  cases index <;> change Fintype (Unit ⊕ Unit) <;> infer_instance

/-- Each connected local-channel block has decidable equality. -/
instance connectionLocalChannelDecidableEq (p : Parameters) (index : Connection) :
    DecidableEq (connection p index).LocalChannel := by
  cases index <;> change DecidableEq (Unit ⊕ Unit) <;> infer_instance

/-- Connected Mach--Zehnder channels are finite. -/
instance connectedChannelFintype (p : Parameters) :
    Fintype (netlist p).ConnectedChannel := by
  change Fintype (Σ index : Connection, (connection p index).LocalChannel)
  infer_instance

/-- Connected Mach--Zehnder channels have decidable equality. -/
@[reducible]
instance connectedChannelDecidableEq (p : Parameters) :
    DecidableEq (netlist p).ConnectedChannel := by
  classical
  exact Classical.decEq _

/-- External Mach--Zehnder channels are finite. -/
@[reducible]
instance externalChannelFintype (p : Parameters) : Fintype (netlist p).ExternalChannel := by
  infer_instance

/-- External Mach--Zehnder channels have decidable equality. -/
@[reducible]
instance externalChannelDecidableEq (p : Parameters) :
    DecidableEq (netlist p).ExternalChannel := by
  infer_instance

/-- The four unconnected physical channels at the two outer coupler reference planes. -/
inductive ExternalPort
  | inputFirst
  | inputSecond
  | outputFirst
  | outputSecond
  deriving DecidableEq

/-- The four outer Mach--Zehnder ports form a finite family. -/
instance : Fintype ExternalPort where
  elems := {.inputFirst, .inputSecond, .outputFirst, .outputSecond}
  complete port := by cases port <;> simp

/-- The ambient channel selected by an external-port label. -/
def externalAmbientChannel (p : Parameters) : ExternalPort → (netlist p).Channel
  | .inputFirst =>
      ⟨⟨Component.inputCoupler, (0 : Fin 4)⟩, ()⟩
  | .inputSecond =>
      ⟨⟨Component.inputCoupler, (1 : Fin 4)⟩, ()⟩
  | .outputFirst =>
      ⟨⟨Component.outputCoupler, (2 : Fin 4)⟩, ()⟩
  | .outputSecond =>
      ⟨⟨Component.outputCoupler, (3 : Fin 4)⟩, ()⟩

/-- Every displayed outer channel is outside the internal connection range. -/
lemma externalAmbientChannel_not_mem_range (p : Parameters) (port : ExternalPort) :
    externalAmbientChannel p port ∉ Set.range (netlist p).connections.channelEmbedding := by
  rintro ⟨⟨index, channel⟩, hChannel⟩
  change (connection p index).channelEmbedding channel =
    externalAmbientChannel p port at hChannel
  have hCode := congrArg (fun selected => portCode p selected.1) hChannel
  cases port <;> cases index <;> rcases channel with mode | mode <;> cases mode <;>
    norm_num [externalAmbientChannel, connection, PortConnection.channelEmbedding,
      portCode] at hCode

/-- The packaged external channel selected by an outer-port label. -/
def externalChannel (p : Parameters) (port : ExternalPort) : (netlist p).ExternalChannel :=
  ⟨externalAmbientChannel p port, externalAmbientChannel_not_mem_range p port⟩

/-- Forgetting the packaged external-channel proof returns the selected ambient channel. -/
@[simp]
lemma externalChannel_val (p : Parameters) (port : ExternalPort) :
    (externalChannel p port).1 = externalAmbientChannel p port := rfl

/-- Coercing a packaged external channel returns the selected ambient channel. -/
@[simp]
lemma externalChannel_coe (p : Parameters) (port : ExternalPort) :
    ((externalChannel p port : (netlist p).ExternalChannel) : (netlist p).Channel) =
      externalAmbientChannel p port := rfl

/-- Distinct outer-port labels give distinct external channels. -/
lemma externalChannel_injective (p : Parameters) : Function.Injective (externalChannel p) := by
  intro first second hChannel
  have hAmbient := congrArg Subtype.val hChannel
  have hCode := congrArg (fun selected => portCode p selected.1) hAmbient
  cases first <;> cases second
  all_goals first | rfl | (exfalso; norm_num [externalChannel, externalAmbientChannel,
    portCode] at hCode)

/-- Every external netlist channel is one of the four outer coupler channels. -/
lemma externalChannel_surjective (p : Parameters) : Function.Surjective (externalChannel p) := by
  rintro ⟨⟨⟨component, port⟩, mode⟩, hExternal⟩
  cases component
  · change Fin 4 at port
    change Unit at mode
    fin_cases port <;> cases mode
    · exact ⟨.inputFirst, Subtype.ext (by rfl)⟩
    · exact ⟨.inputSecond, Subtype.ext (by rfl)⟩
    · exfalso
      apply hExternal
      exact ⟨⟨Connection.upperInput, Sum.inl ()⟩, rfl⟩
    · exfalso
      apply hExternal
      exact ⟨⟨Connection.lowerInput, Sum.inl ()⟩, rfl⟩
  · change Fin 2 at port
    change Unit at mode
    fin_cases port <;> cases mode
    · exfalso
      apply hExternal
      exact ⟨⟨Connection.upperInput, Sum.inr ()⟩, rfl⟩
    · exfalso
      apply hExternal
      exact ⟨⟨Connection.upperOutput, Sum.inl ()⟩, rfl⟩
  · change Fin 2 at port
    change Unit at mode
    fin_cases port <;> cases mode
    · exfalso
      apply hExternal
      exact ⟨⟨Connection.lowerInput, Sum.inr ()⟩, rfl⟩
    · exfalso
      apply hExternal
      exact ⟨⟨Connection.lowerOutput, Sum.inl ()⟩, rfl⟩
  · change Fin 4 at port
    change Unit at mode
    fin_cases port <;> cases mode
    · exfalso
      apply hExternal
      exact ⟨⟨Connection.upperOutput, Sum.inr ()⟩, rfl⟩
    · exfalso
      apply hExternal
      exact ⟨⟨Connection.lowerOutput, Sum.inr ()⟩, rfl⟩
    · exact ⟨.outputFirst, Subtype.ext (by rfl)⟩
    · exact ⟨.outputSecond, Subtype.ext (by rfl)⟩

/-- The four named outer ports are exactly the external channel family. -/
noncomputable def externalChannelEquiv (p : Parameters) :
    ExternalPort ≃ (netlist p).ExternalChannel :=
  Equiv.ofBijective (externalChannel p)
    ⟨externalChannel_injective p, externalChannel_surjective p⟩

/-- External-port labels transported to nominal incident endpoints. -/
noncomputable def externalIncidentEquiv (p : Parameters) :
    ExternalPort ≃ (netlist p).ExternalIncident :=
  (externalChannelEquiv p).trans Incident.channelEquiv.symm

/-- External-port labels transported to nominal outgoing endpoints. -/
noncomputable def externalOutgoingEquiv (p : Parameters) :
    ExternalPort ≃ (netlist p).ExternalOutgoing :=
  (externalChannelEquiv p).trans Outgoing.channelEquiv.symm

/-- The incident endpoint equivalence packages the selected external channel. -/
@[simp]
lemma externalIncidentEquiv_apply (p : Parameters) (port : ExternalPort) :
    externalIncidentEquiv p port = Incident.mk (externalChannel p port) := rfl

/-- The outgoing endpoint equivalence packages the selected external channel. -/
@[simp]
lemma externalOutgoingEquiv_apply (p : Parameters) (port : ExternalPort) :
    externalOutgoingEquiv p port = Outgoing.mk (externalChannel p port) := rfl

/-- A coherent excitation on the two left coupler inputs, with both right inputs zero. -/
def leftInput (p : Parameters) (first second : ℂ) :
    ModeAmplitude (netlist p).ExternalIncident :=
  WithLp.toLp 2 fun endpoint =>
    match (externalIncidentEquiv p).symm endpoint with
    | .inputFirst => first
    | .inputSecond => second
    | .outputFirst => 0
    | .outputSecond => 0

/-- The left excitation has the two supplied input coordinates and zero right incidence. -/
lemma leftInput_apply (p : Parameters) (first second : ℂ) (port : ExternalPort) :
    leftInput p first second (externalIncidentEquiv p port) =
      match port with
      | .inputFirst => first
      | .inputSecond => second
      | .outputFirst => 0
      | .outputSecond => 0 := by
  change (match (externalIncidentEquiv p).symm (externalIncidentEquiv p port) with
    | .inputFirst => first
    | .inputSecond => second
    | .outputFirst => 0
    | .outputSecond => 0) = _
  rw [Equiv.symm_apply_apply]

/-! ## C. Component and routing coordinate laws -/

/-- Embed one local component channel into the aggregate Mach--Zehnder boundary. -/
@[reducible]
def ambientChannel (p : Parameters) (component : Component)
    (channel : ((components p).portFamily component).Channel) : (netlist p).Channel :=
  ⟨⟨component, channel.1⟩, channel.2⟩

/-- The canonical component-channel embedding is the explicit aggregate channel. -/
@[simp]
lemma componentChannelEmbedding_eq_ambientChannel (p : Parameters) (component : Component)
    (channel : ((components p).portFamily component).Channel) :
    (components p).componentChannelEmbedding component channel =
      ambientChannel p component channel := rfl

/-- Restrict an aggregate incident amplitude to one component's unwrapped local channels. -/
def localIncident (p : Parameters) (incident : ModeAmplitude (netlist p).IncidentIndex)
    (component : Component) :
    ModeAmplitude ((components p).portFamily component).Channel :=
  WithLp.toLp 2 fun channel => incident (Incident.mk (ambientChannel p component channel))

/-- Local incident restriction is exact coordinate selection at the aggregate boundary. -/
@[simp]
lemma localIncident_apply (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex) (component : Component)
    (channel : ((components p).portFamily component).Channel) :
    localIncident p incident component channel =
      incident (Incident.mk (ambientChannel p component channel)) := rfl

/-- The N4 assembled scattering action at one local output is exactly the corresponding N7
component action on the locally restricted incident amplitude. -/
lemma scatteringTransform_apply_component (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex) (component : Component)
    (output : ((components p).portFamily component).Channel) :
    (netlist p).scatteringTransform.toLinearMap incident
        (Outgoing.mk (ambientChannel p component output)) =
      ((components p).scattering component).toModeTransform.toLinearMap
        (localIncident p incident component) output := by
  classical
  rw [FlatNetlist.scatteringTransform, FlatNetlist.scatteringMatrix,
    ScatteringMatrix.toLinearMap_toOrientedModeTransform,
    ModeAmplitude.reindex_apply]
  simp only [Equiv.symm_symm, Outgoing.channelEquiv_apply]
  change (components p).assembledScatteringMatrix.toModeTransform.toLinearMap
      (ModeAmplitude.reindex Incident.channelEquiv incident)
        ((components p).componentChannelEmbedding component output) = _
  rw [(components p).assembledScatteringMatrix_apply_component]
  have hLocal :
      (ModeAmplitude.reindex Incident.channelEquiv incident).restrictEmbedding
          ((components p).componentChannelEmbedding component) =
        localIncident p incident component := by
    apply WithLp.ofLp_injective 2
    funext channel
    rfl
  exact congrArg
    (fun selected : ModeAmplitude ((components p).portFamily component).Channel =>
      ((components p).scattering component).toModeTransform.toLinearMap selected output)
    hLocal

/-- At an internal channel, N4 routing returns the outgoing amplitude at its connected mate. -/
lemma routingTransform_apply_connected (p : Parameters)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (channel : (netlist p).ConnectedChannel) :
    (netlist p).routingTransform.toLinearMap outgoing
        (Incident.mk ((netlist p).connections.channelEmbedding channel)) =
      outgoing (Outgoing.mk ((netlist p).connections.channelEmbedding
        ((netlist p).connections.mateEquiv channel))) := by
  simpa only [(netlist p).connections.mateEquiv_apply_apply] using
    ((netlist p).connections.partialRouting_apply_internal outgoing
      ((netlist p).connections.mateEquiv channel))

/-- N4 routing vanishes at each of the four external Mach--Zehnder channels. -/
lemma routingTransform_apply_external (p : Parameters)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex) (port : ExternalPort) :
    (netlist p).routingTransform.toLinearMap outgoing
        (Incident.mk (externalAmbientChannel p port)) = 0 := by
  exact (netlist p).connections.partialRouting_apply_of_incident_not_mem_range
    outgoing (externalAmbientChannel p port) (externalAmbientChannel_not_mem_range p port)

/-- A directional coupler's first left output uses the through and negative-quadrature cross
coefficients pinned at `Physlib/Optics/Components/DirectionalCoupler.lean:68-77`. -/
lemma couplerScattering_apply_leftFirst (p : DirectionalCoupler.Parameters)
    (amplitude : ModeAmplitude couplerPortFamily.Channel) :
    (couplerScattering p).toModeTransform.toLinearMap amplitude (couplerChannel 0) =
      (p.throughAmplitude : ℂ) * amplitude (couplerChannel 2) +
        DirectionalCoupler.crossCoefficient p * amplitude (couplerChannel 3) := by
  rw [couplerScattering, DirectionalCoupler.physicalScattering,
    ScatteringMatrix.toModeTransform_reindex,
    ModeTransform.toLinearMap_reindex_eq,
    ScatteringMatrix.toModeTransform_reindex,
    ModeTransform.toLinearMap_reindex_eq]
  set rawInput := ModeAmplitude.reindex (DirectionalCoupler.channelEquiv Unit).symm
    (ModeAmplitude.reindex couplerChannelEquiv.symm amplitude)
  conv_lhs =>
    enter [1, 2]
    rw [show rawInput = rawInput.restrictInl.directSum rawInput.restrictInr by simp]
  rw [DirectionalCoupler.scattering_toLinearMap_apply]
  change (DirectionalCoupler.mixing p Unit).toLinearMap rawInput.restrictInr
    (Sum.inl ()) = _
  rw [DirectionalCoupler.mixing_toLinearMap_apply]
  change (p.throughAmplitude : ℂ) * amplitude (couplerChannel 2) +
    DirectionalCoupler.crossCoefficient p * amplitude (couplerChannel 3) = _
  rfl

/-- A directional coupler's second left output uses the cross and through coefficients. -/
lemma couplerScattering_apply_leftSecond (p : DirectionalCoupler.Parameters)
    (amplitude : ModeAmplitude couplerPortFamily.Channel) :
    (couplerScattering p).toModeTransform.toLinearMap amplitude (couplerChannel 1) =
      DirectionalCoupler.crossCoefficient p * amplitude (couplerChannel 2) +
        (p.throughAmplitude : ℂ) * amplitude (couplerChannel 3) := by
  rw [couplerScattering, DirectionalCoupler.physicalScattering,
    ScatteringMatrix.toModeTransform_reindex,
    ModeTransform.toLinearMap_reindex_eq,
    ScatteringMatrix.toModeTransform_reindex,
    ModeTransform.toLinearMap_reindex_eq]
  set rawInput := ModeAmplitude.reindex (DirectionalCoupler.channelEquiv Unit).symm
    (ModeAmplitude.reindex couplerChannelEquiv.symm amplitude)
  conv_lhs =>
    enter [1, 2]
    rw [show rawInput = rawInput.restrictInl.directSum rawInput.restrictInr by simp]
  rw [DirectionalCoupler.scattering_toLinearMap_apply]
  change (DirectionalCoupler.mixing p Unit).toLinearMap rawInput.restrictInr
    (Sum.inr ()) = _
  rw [DirectionalCoupler.mixing_toLinearMap_apply]
  change DirectionalCoupler.crossCoefficient p * amplitude (couplerChannel 2) +
    (p.throughAmplitude : ℂ) * amplitude (couplerChannel 3) = _
  rfl

/-- A directional coupler's first right output uses the through and cross coefficients. -/
lemma couplerScattering_apply_rightFirst (p : DirectionalCoupler.Parameters)
    (amplitude : ModeAmplitude couplerPortFamily.Channel) :
    (couplerScattering p).toModeTransform.toLinearMap amplitude (couplerChannel 2) =
      (p.throughAmplitude : ℂ) * amplitude (couplerChannel 0) +
        DirectionalCoupler.crossCoefficient p * amplitude (couplerChannel 1) := by
  rw [couplerScattering, DirectionalCoupler.physicalScattering,
    ScatteringMatrix.toModeTransform_reindex,
    ModeTransform.toLinearMap_reindex_eq,
    ScatteringMatrix.toModeTransform_reindex,
    ModeTransform.toLinearMap_reindex_eq]
  set rawInput := ModeAmplitude.reindex (DirectionalCoupler.channelEquiv Unit).symm
    (ModeAmplitude.reindex couplerChannelEquiv.symm amplitude)
  conv_lhs =>
    enter [1, 2]
    rw [show rawInput = rawInput.restrictInl.directSum rawInput.restrictInr by simp]
  rw [DirectionalCoupler.scattering_toLinearMap_apply]
  change (DirectionalCoupler.mixing p Unit).toLinearMap rawInput.restrictInl
    (Sum.inl ()) = _
  rw [DirectionalCoupler.mixing_toLinearMap_apply]
  change (p.throughAmplitude : ℂ) * amplitude (couplerChannel 0) +
    DirectionalCoupler.crossCoefficient p * amplitude (couplerChannel 1) = _
  rfl

/-- A directional coupler's second right output uses the cross and through coefficients. -/
lemma couplerScattering_apply_rightSecond (p : DirectionalCoupler.Parameters)
    (amplitude : ModeAmplitude couplerPortFamily.Channel) :
    (couplerScattering p).toModeTransform.toLinearMap amplitude (couplerChannel 3) =
      DirectionalCoupler.crossCoefficient p * amplitude (couplerChannel 0) +
        (p.throughAmplitude : ℂ) * amplitude (couplerChannel 1) := by
  rw [couplerScattering, DirectionalCoupler.physicalScattering,
    ScatteringMatrix.toModeTransform_reindex,
    ModeTransform.toLinearMap_reindex_eq,
    ScatteringMatrix.toModeTransform_reindex,
    ModeTransform.toLinearMap_reindex_eq]
  set rawInput := ModeAmplitude.reindex (DirectionalCoupler.channelEquiv Unit).symm
    (ModeAmplitude.reindex couplerChannelEquiv.symm amplitude)
  conv_lhs =>
    enter [1, 2]
    rw [show rawInput = rawInput.restrictInl.directSum rawInput.restrictInr by simp]
  rw [DirectionalCoupler.scattering_toLinearMap_apply]
  change (DirectionalCoupler.mixing p Unit).toLinearMap rawInput.restrictInl
    (Sum.inr ()) = _
  rw [DirectionalCoupler.mixing_toLinearMap_apply]
  change DirectionalCoupler.crossCoefficient p * amplitude (couplerChannel 0) +
    (p.throughAmplitude : ℂ) * amplitude (couplerChannel 1) = _
  rfl

/-- A matched-propagation component sends its right incident amplitude to its left output. -/
lemma armScattering_apply_left (p : MatchedPropagation.Parameters)
    (amplitude : ModeAmplitude armPortFamily.Channel) :
    (armScattering p).toModeTransform.toLinearMap amplitude (armChannel 0) =
      MatchedPropagation.transmissionCoefficient p * amplitude (armChannel 1) := by
  rw [armScattering, MatchedPropagation.physicalScattering,
    ScatteringMatrix.toModeTransform_reindex,
    ModeTransform.toLinearMap_reindex_eq,
    ScatteringMatrix.toModeTransform_reindex,
    ModeTransform.toLinearMap_reindex_eq]
  set rawInput := ModeAmplitude.reindex (MatchedPropagation.channelEquiv Unit).symm
    (ModeAmplitude.reindex armChannelEquiv.symm amplitude)
  conv_lhs =>
    enter [1, 2]
    rw [show rawInput = rawInput.restrictInl.directSum rawInput.restrictInr by simp]
  rw [MatchedPropagation.scattering_toLinearMap_apply]
  change MatchedPropagation.transmissionCoefficient p * amplitude (armChannel 1) = _
  rfl

/-- A matched-propagation component sends its left incident amplitude to its right output. -/
lemma armScattering_apply_right (p : MatchedPropagation.Parameters)
    (amplitude : ModeAmplitude armPortFamily.Channel) :
    (armScattering p).toModeTransform.toLinearMap amplitude (armChannel 1) =
      MatchedPropagation.transmissionCoefficient p * amplitude (armChannel 0) := by
  rw [armScattering, MatchedPropagation.physicalScattering,
    ScatteringMatrix.toModeTransform_reindex,
    ModeTransform.toLinearMap_reindex_eq,
    ScatteringMatrix.toModeTransform_reindex,
    ModeTransform.toLinearMap_reindex_eq]
  set rawInput := ModeAmplitude.reindex (MatchedPropagation.channelEquiv Unit).symm
    (ModeAmplitude.reindex armChannelEquiv.symm amplitude)
  conv_lhs =>
    enter [1, 2]
    rw [show rawInput = rawInput.restrictInl.directSum rawInput.restrictInr by simp]
  rw [MatchedPropagation.scattering_toLinearMap_apply]
  change MatchedPropagation.transmissionCoefficient p * amplitude (armChannel 0) = _
  rfl

/-- The assembled input coupler's two right-going coordinates are its local N7 mixing law. -/
lemma inputCoupler_outgoing_right (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex) :
    (netlist p).scatteringTransform.toLinearMap incident
          (Outgoing.mk (ambientChannel p .inputCoupler (couplerChannel 2))) =
        (p.inputCoupler.throughAmplitude : ℂ) *
            incident (Incident.mk (ambientChannel p .inputCoupler (couplerChannel 0))) +
          DirectionalCoupler.crossCoefficient p.inputCoupler *
            incident (Incident.mk (ambientChannel p .inputCoupler (couplerChannel 1))) ∧
      (netlist p).scatteringTransform.toLinearMap incident
          (Outgoing.mk (ambientChannel p .inputCoupler (couplerChannel 3))) =
        DirectionalCoupler.crossCoefficient p.inputCoupler *
            incident (Incident.mk (ambientChannel p .inputCoupler (couplerChannel 0))) +
          (p.inputCoupler.throughAmplitude : ℂ) *
            incident (Incident.mk (ambientChannel p .inputCoupler (couplerChannel 1))) := by
  constructor
  · rw [scatteringTransform_apply_component p incident .inputCoupler (couplerChannel 2)]
    change (couplerScattering p.inputCoupler).toModeTransform.toLinearMap
      (localIncident p incident .inputCoupler) (couplerChannel 2) = _
    rw [couplerScattering_apply_rightFirst, localIncident_apply, localIncident_apply]
  · rw [scatteringTransform_apply_component p incident .inputCoupler (couplerChannel 3)]
    change (couplerScattering p.inputCoupler).toModeTransform.toLinearMap
      (localIncident p incident .inputCoupler) (couplerChannel 3) = _
    rw [couplerScattering_apply_rightSecond, localIncident_apply, localIncident_apply]

/-- The assembled input coupler's two left-going coordinates are its local N7 mixing law. -/
lemma inputCoupler_outgoing_left (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex) :
    (netlist p).scatteringTransform.toLinearMap incident
          (Outgoing.mk (ambientChannel p .inputCoupler (couplerChannel 0))) =
        (p.inputCoupler.throughAmplitude : ℂ) *
            incident (Incident.mk (ambientChannel p .inputCoupler (couplerChannel 2))) +
          DirectionalCoupler.crossCoefficient p.inputCoupler *
            incident (Incident.mk (ambientChannel p .inputCoupler (couplerChannel 3))) ∧
      (netlist p).scatteringTransform.toLinearMap incident
          (Outgoing.mk (ambientChannel p .inputCoupler (couplerChannel 1))) =
        DirectionalCoupler.crossCoefficient p.inputCoupler *
            incident (Incident.mk (ambientChannel p .inputCoupler (couplerChannel 2))) +
          (p.inputCoupler.throughAmplitude : ℂ) *
            incident (Incident.mk (ambientChannel p .inputCoupler (couplerChannel 3))) := by
  constructor
  · rw [scatteringTransform_apply_component p incident .inputCoupler (couplerChannel 0)]
    change (couplerScattering p.inputCoupler).toModeTransform.toLinearMap
      (localIncident p incident .inputCoupler) (couplerChannel 0) = _
    rw [couplerScattering_apply_leftFirst, localIncident_apply, localIncident_apply]
  · rw [scatteringTransform_apply_component p incident .inputCoupler (couplerChannel 1)]
    change (couplerScattering p.inputCoupler).toModeTransform.toLinearMap
      (localIncident p incident .inputCoupler) (couplerChannel 1) = _
    rw [couplerScattering_apply_leftSecond, localIncident_apply, localIncident_apply]

/-- The assembled output coupler's two right-going coordinates are its local N7 mixing law. -/
lemma outputCoupler_outgoing_right (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex) :
    (netlist p).scatteringTransform.toLinearMap incident
          (Outgoing.mk (ambientChannel p .outputCoupler (couplerChannel 2))) =
        (p.outputCoupler.throughAmplitude : ℂ) *
            incident (Incident.mk (ambientChannel p .outputCoupler (couplerChannel 0))) +
          DirectionalCoupler.crossCoefficient p.outputCoupler *
            incident (Incident.mk (ambientChannel p .outputCoupler (couplerChannel 1))) ∧
      (netlist p).scatteringTransform.toLinearMap incident
          (Outgoing.mk (ambientChannel p .outputCoupler (couplerChannel 3))) =
        DirectionalCoupler.crossCoefficient p.outputCoupler *
            incident (Incident.mk (ambientChannel p .outputCoupler (couplerChannel 0))) +
          (p.outputCoupler.throughAmplitude : ℂ) *
            incident (Incident.mk (ambientChannel p .outputCoupler (couplerChannel 1))) := by
  constructor
  · rw [scatteringTransform_apply_component p incident .outputCoupler (couplerChannel 2)]
    change (couplerScattering p.outputCoupler).toModeTransform.toLinearMap
      (localIncident p incident .outputCoupler) (couplerChannel 2) = _
    rw [couplerScattering_apply_rightFirst, localIncident_apply, localIncident_apply]
  · rw [scatteringTransform_apply_component p incident .outputCoupler (couplerChannel 3)]
    change (couplerScattering p.outputCoupler).toModeTransform.toLinearMap
      (localIncident p incident .outputCoupler) (couplerChannel 3) = _
    rw [couplerScattering_apply_rightSecond, localIncident_apply, localIncident_apply]

/-- The assembled output coupler's two left-going coordinates are its local N7 mixing law. -/
lemma outputCoupler_outgoing_left (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex) :
    (netlist p).scatteringTransform.toLinearMap incident
          (Outgoing.mk (ambientChannel p .outputCoupler (couplerChannel 0))) =
        (p.outputCoupler.throughAmplitude : ℂ) *
            incident (Incident.mk (ambientChannel p .outputCoupler (couplerChannel 2))) +
          DirectionalCoupler.crossCoefficient p.outputCoupler *
            incident (Incident.mk (ambientChannel p .outputCoupler (couplerChannel 3))) ∧
      (netlist p).scatteringTransform.toLinearMap incident
          (Outgoing.mk (ambientChannel p .outputCoupler (couplerChannel 1))) =
        DirectionalCoupler.crossCoefficient p.outputCoupler *
            incident (Incident.mk (ambientChannel p .outputCoupler (couplerChannel 2))) +
          (p.outputCoupler.throughAmplitude : ℂ) *
            incident (Incident.mk (ambientChannel p .outputCoupler (couplerChannel 3))) := by
  constructor
  · rw [scatteringTransform_apply_component p incident .outputCoupler (couplerChannel 0)]
    change (couplerScattering p.outputCoupler).toModeTransform.toLinearMap
      (localIncident p incident .outputCoupler) (couplerChannel 0) = _
    rw [couplerScattering_apply_leftFirst, localIncident_apply, localIncident_apply]
  · rw [scatteringTransform_apply_component p incident .outputCoupler (couplerChannel 1)]
    change (couplerScattering p.outputCoupler).toModeTransform.toLinearMap
      (localIncident p incident .outputCoupler) (couplerChannel 1) = _
    rw [couplerScattering_apply_leftSecond, localIncident_apply, localIncident_apply]

/-- The assembled upper arm sends its left incident coordinate to its right output. -/
lemma upperArm_outgoing_right (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex) :
    (netlist p).scatteringTransform.toLinearMap incident
        (Outgoing.mk (ambientChannel p .upperArm (armChannel 1))) =
      MatchedPropagation.transmissionCoefficient p.upperArm *
        incident (Incident.mk (ambientChannel p .upperArm (armChannel 0))) := by
  rw [scatteringTransform_apply_component p incident .upperArm (armChannel 1)]
  change (armScattering p.upperArm).toModeTransform.toLinearMap
    (localIncident p incident .upperArm) (armChannel 1) = _
  rw [armScattering_apply_right, localIncident_apply]

/-- The assembled lower arm sends its left incident coordinate to its right output. -/
lemma lowerArm_outgoing_right (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex) :
    (netlist p).scatteringTransform.toLinearMap incident
        (Outgoing.mk (ambientChannel p .lowerArm (armChannel 1))) =
      MatchedPropagation.transmissionCoefficient p.lowerArm *
        incident (Incident.mk (ambientChannel p .lowerArm (armChannel 0))) := by
  rw [scatteringTransform_apply_component p incident .lowerArm (armChannel 1)]
  change (armScattering p.lowerArm).toModeTransform.toLinearMap
    (localIncident p incident .lowerArm) (armChannel 1) = _
  rw [armScattering_apply_right, localIncident_apply]

/-- The assembled upper arm sends its right incident coordinate to its left output. -/
lemma upperArm_outgoing_left (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex) :
    (netlist p).scatteringTransform.toLinearMap incident
        (Outgoing.mk (ambientChannel p .upperArm (armChannel 0))) =
      MatchedPropagation.transmissionCoefficient p.upperArm *
        incident (Incident.mk (ambientChannel p .upperArm (armChannel 1))) := by
  rw [scatteringTransform_apply_component p incident .upperArm (armChannel 0)]
  change (armScattering p.upperArm).toModeTransform.toLinearMap
    (localIncident p incident .upperArm) (armChannel 0) = _
  rw [armScattering_apply_left, localIncident_apply]

/-- The assembled lower arm sends its right incident coordinate to its left output. -/
lemma lowerArm_outgoing_left (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex) :
    (netlist p).scatteringTransform.toLinearMap incident
        (Outgoing.mk (ambientChannel p .lowerArm (armChannel 0))) =
      MatchedPropagation.transmissionCoefficient p.lowerArm *
        incident (Incident.mk (ambientChannel p .lowerArm (armChannel 1))) := by
  rw [scatteringTransform_apply_component p incident .lowerArm (armChannel 0)]
  change (armScattering p.lowerArm).toModeTransform.toLinearMap
    (localIncident p incident .lowerArm) (armChannel 0) = _
  rw [armScattering_apply_left, localIncident_apply]

/-! ## D. N5 well-posedness and extracted amplitudes -/

/-- A solution of the N5 feedback equation is the N4 incident assembly of component outputs and
the supplied external input. -/
lemma incident_eq_incidentAssembly_of_feedbackEquation (p : Parameters)
    (input : ModeAmplitude (netlist p).ExternalIncident)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (hFeedback : (netlist p).feedbackOperator.toLinearMap incident =
      (netlist p).inputExposure.toLinearMap input) :
    incident = (netlist p).connections.incidentAssembly
      ((netlist p).scatteringTransform.toLinearMap incident) input := by
  rw [(netlist p).feedbackOperator_apply] at hFeedback
  change incident = (netlist p).routingTransform.toLinearMap
      ((netlist p).scatteringTransform.toLinearMap incident) +
        (netlist p).inputExposure.toLinearMap input
  exact (sub_eq_iff_eq_add.mp hFeedback).trans (add_comm _ _)

/-- N5's incident solution is the N4 assembly of its component output and the supplied input. -/
lemma incidentSolution_eq_incidentAssembly (p : Parameters) (hWellPosed : (netlist p).IsWellPosed)
    (input : ModeAmplitude (netlist p).ExternalIncident) :
    ((netlist p).incidentSolutionBlockFormula hWellPosed).toLinearMap input =
      (netlist p).connections.incidentAssembly
        ((netlist p).scatteringTransform.toLinearMap
          (((netlist p).incidentSolutionBlockFormula hWellPosed).toLinearMap input))
        input := by
  apply incident_eq_incidentAssembly_of_feedbackEquation p
  change (netlist p).feedbackOperator.toLinearMap
    (ModeTransform.toLinearMap
      ((netlist p).feedbackInverse hWellPosed * (netlist p).inputExposure) input) = _
  rw [ModeTransform.toLinearMap_mul_apply,
    (netlist p).feedbackOperator_apply_feedbackInverse hWellPosed]

/-- An external coordinate of the N5 incident solution equals the supplied external input. -/
lemma incidentSolution_apply_external (p : Parameters) (hWellPosed : (netlist p).IsWellPosed)
    (input : ModeAmplitude (netlist p).ExternalIncident) (port : ExternalPort) :
    ((netlist p).incidentSolutionBlockFormula hWellPosed).toLinearMap input
        (Incident.mk (externalAmbientChannel p port)) =
      input (externalIncidentEquiv p port) := by
  rw [incidentSolution_eq_incidentAssembly p hWellPosed]
  have h := (netlist p).connections.incidentAssembly_apply_external
    ((netlist p).scatteringTransform.toLinearMap
      (((netlist p).incidentSolutionBlockFormula hWellPosed).toLinearMap input))
    input (externalChannel p port)
  rw [externalChannel_val] at h
  rw [externalIncidentEquiv_apply]
  exact h

/-- A connected coordinate of the N5 incident solution equals its routed component output. -/
lemma incidentSolution_apply_connected (p : Parameters) (hWellPosed : (netlist p).IsWellPosed)
    (input : ModeAmplitude (netlist p).ExternalIncident)
    (channel : (netlist p).ConnectedChannel) :
    ((netlist p).incidentSolutionBlockFormula hWellPosed).toLinearMap input
        (Incident.mk ((netlist p).connections.channelEmbedding channel)) =
      (netlist p).scatteringTransform.toLinearMap
          (((netlist p).incidentSolutionBlockFormula hWellPosed).toLinearMap input)
        (Outgoing.mk ((netlist p).connections.channelEmbedding
          ((netlist p).connections.mateEquiv channel))) := by
  let incident := ((netlist p).incidentSolutionBlockFormula hWellPosed).toLinearMap input
  let outgoing := (netlist p).scatteringTransform.toLinearMap incident
  have hAssembly := incidentSolution_eq_incidentAssembly p hWellPosed input
  change incident (Incident.mk ((netlist p).connections.channelEmbedding channel)) =
    outgoing (Outgoing.mk ((netlist p).connections.channelEmbedding
      ((netlist p).connections.mateEquiv channel)))
  calc
    _ = ((netlist p).connections.incidentAssembly outgoing input)
        (Incident.mk ((netlist p).connections.channelEmbedding channel)) :=
      congrArg (fun amplitude =>
        amplitude (Incident.mk ((netlist p).connections.channelEmbedding channel))) hAssembly
    _ = _ := (netlist p).connections.incidentAssembly_apply_connected_channel
      outgoing input channel

/-- N5 response readout at a named external port is the corresponding solved component output. -/
lemma responseTransform_apply_external (p : Parameters) (hWellPosed : (netlist p).IsWellPosed)
    (input : ModeAmplitude (netlist p).ExternalIncident) (port : ExternalPort) :
    ((netlist p).responseTransform hWellPosed).toLinearMap input
        (externalOutgoingEquiv p port) =
      (netlist p).scatteringTransform.toLinearMap
          (((netlist p).incidentSolutionBlockFormula hWellPosed).toLinearMap input)
        (Outgoing.mk (externalAmbientChannel p port)) := by
  let incident :=
    ((netlist p).incidentSolutionBlockFormula hWellPosed).toLinearMap input
  let outgoing := (netlist p).scatteringTransform.toLinearMap incident
  have hResponse :
      ((netlist p).responseTransform hWellPosed).toLinearMap input =
        (netlist p).outputReadout.toLinearMap outgoing := by
    calc
      _ = ((netlist p).responseBlockFormula hWellPosed).toLinearMap input :=
        congrArg (fun transform => transform.toLinearMap input)
          ((netlist p).responseTransform_eq_blockFormula hWellPosed)
      _ = (netlist p).outputReadout.toLinearMap
          (((netlist p).outgoingSolutionBlockFormula hWellPosed).toLinearMap input) :=
        (netlist p).responseBlockFormula_apply hWellPosed input
      _ = (netlist p).outputReadout.toLinearMap outgoing := by
        apply congrArg ((netlist p).outputReadout.toLinearMap)
        exact (netlist p).outgoingSolutionBlockFormula_apply hWellPosed input
  rw [hResponse, PortConnectionFamily.externalOutgoingReadout_apply]
  rfl

/-- An external coordinate of a feedback fixed point vanishes. -/
lemma feedbackFixedPoint_apply_external (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (hFixed : incident = (netlist p).routingTransform.toLinearMap
      ((netlist p).scatteringTransform.toLinearMap incident)) (port : ExternalPort) :
    incident (Incident.mk (externalAmbientChannel p port)) = 0 := by
  rw [hFixed]
  exact routingTransform_apply_external p
    ((netlist p).scatteringTransform.toLinearMap incident) port

/-- A connected coordinate of a feedback fixed point equals its mate's component output. -/
lemma feedbackFixedPoint_apply_connected (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (hFixed : incident = (netlist p).routingTransform.toLinearMap
      ((netlist p).scatteringTransform.toLinearMap incident))
    (channel : (netlist p).ConnectedChannel) :
    incident (Incident.mk ((netlist p).connections.channelEmbedding channel)) =
      (netlist p).scatteringTransform.toLinearMap incident
        (Outgoing.mk ((netlist p).connections.channelEmbedding
          ((netlist p).connections.mateEquiv channel))) := by
  let outgoing := (netlist p).scatteringTransform.toLinearMap incident
  change incident (Incident.mk ((netlist p).connections.channelEmbedding channel)) =
    outgoing (Outgoing.mk ((netlist p).connections.channelEmbedding
      ((netlist p).connections.mateEquiv channel)))
  calc
    _ = ((netlist p).routingTransform.toLinearMap outgoing)
        (Incident.mk ((netlist p).connections.channelEmbedding channel)) :=
      congrArg (fun amplitude =>
        amplitude (Incident.mk ((netlist p).connections.channelEmbedding channel))) hFixed
    _ = _ := routingTransform_apply_connected p outgoing channel

/-- Both left incident coordinates of the input coupler vanish at a feedback fixed point. -/
lemma feedbackFixedPoint_input_left_eq_zero (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (hFixed : incident = (netlist p).routingTransform.toLinearMap
      ((netlist p).scatteringTransform.toLinearMap incident)) :
    incident (Incident.mk (ambientChannel p .inputCoupler (couplerChannel 0))) = 0 ∧
      incident (Incident.mk (ambientChannel p .inputCoupler (couplerChannel 1))) = 0 := by
  constructor
  · simpa only [externalAmbientChannel, ambientChannel, couplerChannel] using
      feedbackFixedPoint_apply_external p incident hFixed .inputFirst
  · simpa only [externalAmbientChannel, ambientChannel, couplerChannel] using
      feedbackFixedPoint_apply_external p incident hFixed .inputSecond

/-- Both left incident arm coordinates vanish after the zero input-coupler coordinates scatter. -/
lemma feedbackFixedPoint_arm_left_eq_zero (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (hFixed : incident = (netlist p).routingTransform.toLinearMap
      ((netlist p).scatteringTransform.toLinearMap incident)) :
    incident (Incident.mk (ambientChannel p .upperArm (armChannel 0))) = 0 ∧
      incident (Incident.mk (ambientChannel p .lowerArm (armChannel 0))) = 0 := by
  rcases feedbackFixedPoint_input_left_eq_zero p incident hFixed with ⟨hFirst, hSecond⟩
  have hOutgoing := inputCoupler_outgoing_right p incident
  rw [hFirst, hSecond] at hOutgoing
  simp only [mul_zero, add_zero] at hOutgoing
  constructor
  · have h := feedbackFixedPoint_apply_connected p incident hFixed
      ⟨Connection.upperInput, Sum.inr ()⟩
    change incident (Incident.mk (ambientChannel p .upperArm (armChannel 0))) =
      (netlist p).scatteringTransform.toLinearMap incident
        (Outgoing.mk (ambientChannel p .inputCoupler (couplerChannel 2))) at h
    exact h.trans hOutgoing.1
  · have h := feedbackFixedPoint_apply_connected p incident hFixed
      ⟨Connection.lowerInput, Sum.inr ()⟩
    change incident (Incident.mk (ambientChannel p .lowerArm (armChannel 0))) =
      (netlist p).scatteringTransform.toLinearMap incident
        (Outgoing.mk (ambientChannel p .inputCoupler (couplerChannel 3))) at h
    exact h.trans hOutgoing.2

/-- Both left incident coordinates of the output coupler vanish after forward arm propagation. -/
lemma feedbackFixedPoint_output_left_eq_zero (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (hFixed : incident = (netlist p).routingTransform.toLinearMap
      ((netlist p).scatteringTransform.toLinearMap incident)) :
    incident (Incident.mk (ambientChannel p .outputCoupler (couplerChannel 0))) = 0 ∧
      incident (Incident.mk (ambientChannel p .outputCoupler (couplerChannel 1))) = 0 := by
  rcases feedbackFixedPoint_arm_left_eq_zero p incident hFixed with ⟨hUpper, hLower⟩
  have hUpperOutgoing := upperArm_outgoing_right p incident
  have hLowerOutgoing := lowerArm_outgoing_right p incident
  rw [hUpper] at hUpperOutgoing
  rw [hLower] at hLowerOutgoing
  simp only [mul_zero] at hUpperOutgoing hLowerOutgoing
  constructor
  · have h := feedbackFixedPoint_apply_connected p incident hFixed
      ⟨Connection.upperOutput, Sum.inr ()⟩
    change incident (Incident.mk (ambientChannel p .outputCoupler (couplerChannel 0))) =
      (netlist p).scatteringTransform.toLinearMap incident
        (Outgoing.mk (ambientChannel p .upperArm (armChannel 1))) at h
    exact h.trans hUpperOutgoing
  · have h := feedbackFixedPoint_apply_connected p incident hFixed
      ⟨Connection.lowerOutput, Sum.inr ()⟩
    change incident (Incident.mk (ambientChannel p .outputCoupler (couplerChannel 1))) =
      (netlist p).scatteringTransform.toLinearMap incident
        (Outgoing.mk (ambientChannel p .lowerArm (armChannel 1))) at h
    exact h.trans hLowerOutgoing

/-- Both right incident coordinates of the output coupler vanish at a feedback fixed point. -/
lemma feedbackFixedPoint_output_right_eq_zero (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (hFixed : incident = (netlist p).routingTransform.toLinearMap
      ((netlist p).scatteringTransform.toLinearMap incident)) :
    incident (Incident.mk (ambientChannel p .outputCoupler (couplerChannel 2))) = 0 ∧
      incident (Incident.mk (ambientChannel p .outputCoupler (couplerChannel 3))) = 0 := by
  constructor
  · simpa only [externalAmbientChannel, ambientChannel, couplerChannel] using
      feedbackFixedPoint_apply_external p incident hFixed .outputFirst
  · simpa only [externalAmbientChannel, ambientChannel, couplerChannel] using
      feedbackFixedPoint_apply_external p incident hFixed .outputSecond

/-- Both right incident arm coordinates vanish after the zero output-coupler coordinates scatter. -/
lemma feedbackFixedPoint_arm_right_eq_zero (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (hFixed : incident = (netlist p).routingTransform.toLinearMap
      ((netlist p).scatteringTransform.toLinearMap incident)) :
    incident (Incident.mk (ambientChannel p .upperArm (armChannel 1))) = 0 ∧
      incident (Incident.mk (ambientChannel p .lowerArm (armChannel 1))) = 0 := by
  rcases feedbackFixedPoint_output_right_eq_zero p incident hFixed with ⟨hFirst, hSecond⟩
  have hOutgoing := outputCoupler_outgoing_left p incident
  rw [hFirst, hSecond] at hOutgoing
  simp only [mul_zero, add_zero] at hOutgoing
  constructor
  · have h := feedbackFixedPoint_apply_connected p incident hFixed
      ⟨Connection.upperOutput, Sum.inl ()⟩
    change incident (Incident.mk (ambientChannel p .upperArm (armChannel 1))) =
      (netlist p).scatteringTransform.toLinearMap incident
        (Outgoing.mk (ambientChannel p .outputCoupler (couplerChannel 0))) at h
    exact h.trans hOutgoing.1
  · have h := feedbackFixedPoint_apply_connected p incident hFixed
      ⟨Connection.lowerOutput, Sum.inl ()⟩
    change incident (Incident.mk (ambientChannel p .lowerArm (armChannel 1))) =
      (netlist p).scatteringTransform.toLinearMap incident
        (Outgoing.mk (ambientChannel p .outputCoupler (couplerChannel 1))) at h
    exact h.trans hOutgoing.2

/-- Both right incident coordinates of the input coupler vanish after reverse arm propagation. -/
lemma feedbackFixedPoint_input_right_eq_zero (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (hFixed : incident = (netlist p).routingTransform.toLinearMap
      ((netlist p).scatteringTransform.toLinearMap incident)) :
    incident (Incident.mk (ambientChannel p .inputCoupler (couplerChannel 2))) = 0 ∧
      incident (Incident.mk (ambientChannel p .inputCoupler (couplerChannel 3))) = 0 := by
  rcases feedbackFixedPoint_arm_right_eq_zero p incident hFixed with ⟨hUpper, hLower⟩
  have hUpperOutgoing := upperArm_outgoing_left p incident
  have hLowerOutgoing := lowerArm_outgoing_left p incident
  rw [hUpper] at hUpperOutgoing
  rw [hLower] at hLowerOutgoing
  simp only [mul_zero] at hUpperOutgoing hLowerOutgoing
  constructor
  · have h := feedbackFixedPoint_apply_connected p incident hFixed
      ⟨Connection.upperInput, Sum.inl ()⟩
    change incident (Incident.mk (ambientChannel p .inputCoupler (couplerChannel 2))) =
      (netlist p).scatteringTransform.toLinearMap incident
        (Outgoing.mk (ambientChannel p .upperArm (armChannel 0))) at h
    exact h.trans hUpperOutgoing
  · have h := feedbackFixedPoint_apply_connected p incident hFixed
      ⟨Connection.lowerInput, Sum.inl ()⟩
    change incident (Incident.mk (ambientChannel p .inputCoupler (couplerChannel 3))) =
      (netlist p).scatteringTransform.toLinearMap incident
        (Outgoing.mk (ambientChannel p .lowerArm (armChannel 0))) at h
    exact h.trans hLowerOutgoing

/-- The Mach--Zehnder feedback operator has a trivial kernel for every algebraic parameter value.
This is the N5 complete-state uniqueness gate, proved from the feed-forward component and routing
coordinate laws rather than from a stored interferometer transfer matrix. -/
lemma feedbackOperator_eq_zero_imp_eq_zero (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (hFeedback : (netlist p).feedbackOperator.toLinearMap incident = 0) :
    incident = 0 := by
  have hApplied := (netlist p).feedbackOperator_apply incident
  have hZero : incident - (netlist p).routingTransform.toLinearMap
      ((netlist p).scatteringTransform.toLinearMap incident) = 0 :=
    hApplied.symm.trans hFeedback
  have hFixed : incident = (netlist p).routingTransform.toLinearMap
      ((netlist p).scatteringTransform.toLinearMap incident) := by
    simpa only [sub_eq_zero] using hZero
  rcases feedbackFixedPoint_input_left_eq_zero p incident hFixed with
    ⟨hInputLeftFirst, hInputLeftSecond⟩
  rcases feedbackFixedPoint_input_right_eq_zero p incident hFixed with
    ⟨hInputRightFirst, hInputRightSecond⟩
  rcases feedbackFixedPoint_arm_left_eq_zero p incident hFixed with
    ⟨hUpperLeft, hLowerLeft⟩
  rcases feedbackFixedPoint_arm_right_eq_zero p incident hFixed with
    ⟨hUpperRight, hLowerRight⟩
  rcases feedbackFixedPoint_output_left_eq_zero p incident hFixed with
    ⟨hOutputLeftFirst, hOutputLeftSecond⟩
  rcases feedbackFixedPoint_output_right_eq_zero p incident hFixed with
    ⟨hOutputRightFirst, hOutputRightSecond⟩
  apply WithLp.ofLp_injective 2
  funext endpoint
  rcases endpoint with ⟨⟨⟨component, port⟩, mode⟩⟩
  cases component
  · change Fin 4 at port
    change Unit at mode
    fin_cases port <;> cases mode
    · change incident (Incident.mk
        (ambientChannel p .inputCoupler (couplerChannel 0))) = 0
      exact hInputLeftFirst
    · change incident (Incident.mk
        (ambientChannel p .inputCoupler (couplerChannel 1))) = 0
      exact hInputLeftSecond
    · change incident (Incident.mk
        (ambientChannel p .inputCoupler (couplerChannel 2))) = 0
      exact hInputRightFirst
    · change incident (Incident.mk
        (ambientChannel p .inputCoupler (couplerChannel 3))) = 0
      exact hInputRightSecond
  · change Fin 2 at port
    change Unit at mode
    fin_cases port <;> cases mode
    · change incident (Incident.mk (ambientChannel p .upperArm (armChannel 0))) = 0
      exact hUpperLeft
    · change incident (Incident.mk (ambientChannel p .upperArm (armChannel 1))) = 0
      exact hUpperRight
  · change Fin 2 at port
    change Unit at mode
    fin_cases port <;> cases mode
    · change incident (Incident.mk (ambientChannel p .lowerArm (armChannel 0))) = 0
      exact hLowerLeft
    · change incident (Incident.mk (ambientChannel p .lowerArm (armChannel 1))) = 0
      exact hLowerRight
  · change Fin 4 at port
    change Unit at mode
    fin_cases port <;> cases mode
    · change incident (Incident.mk
        (ambientChannel p .outputCoupler (couplerChannel 0))) = 0
      exact hOutputLeftFirst
    · change incident (Incident.mk
        (ambientChannel p .outputCoupler (couplerChannel 1))) = 0
      exact hOutputLeftSecond
    · change incident (Incident.mk
        (ambientChannel p .outputCoupler (couplerChannel 2))) = 0
      exact hOutputRightFirst
    · change incident (Incident.mk
        (ambientChannel p .outputCoupler (couplerChannel 3))) = 0
      exact hOutputRightSecond

/-- The N5 solver's complete-state well-posedness gate holds for the Mach--Zehnder netlist. -/
lemma isWellPosed (p : Parameters) : (netlist p).IsWellPosed := by
  rw [(netlist p).isWellPosed_iff_feedbackOperator_injective]
  intro first second hEqual
  apply sub_eq_zero.mp
  apply feedbackOperator_eq_zero_imp_eq_zero p
  rw [map_sub]
  exact sub_eq_zero.mpr hEqual

/-- The N5 feedback determinant is nonzero; in particular, the ideal lossless specialization has
no denominator side condition left to discharge. -/
lemma feedbackOperator_det_ne_zero (p : Parameters) :
    (netlist p).feedbackOperator.det ≠ 0 :=
  (netlist p).isWellPosed_iff_feedbackOperator_det_ne_zero.mp (isWellPosed p)

/-- The solved input coupler produces the two forward arm-launch amplitudes. -/
lemma incidentSolution_inputCoupler_right_amplitudes
    (p : Parameters) (first second : ℂ) :
    let input := leftInput p first second
    let incident :=
      ((netlist p).incidentSolutionBlockFormula (isWellPosed p)).toLinearMap input
    (netlist p).scatteringTransform.toLinearMap incident
          (Outgoing.mk (ambientChannel p .inputCoupler (couplerChannel 2))) =
        (p.inputCoupler.throughAmplitude : ℂ) * first +
          DirectionalCoupler.crossCoefficient p.inputCoupler * second ∧
      (netlist p).scatteringTransform.toLinearMap incident
          (Outgoing.mk (ambientChannel p .inputCoupler (couplerChannel 3))) =
        DirectionalCoupler.crossCoefficient p.inputCoupler * first +
          (p.inputCoupler.throughAmplitude : ℂ) * second := by
  let input := leftInput p first second
  let incident :=
    ((netlist p).incidentSolutionBlockFormula (isWellPosed p)).toLinearMap input
  change (netlist p).scatteringTransform.toLinearMap incident
        (Outgoing.mk (ambientChannel p .inputCoupler (couplerChannel 2))) = _ ∧
    (netlist p).scatteringTransform.toLinearMap incident
        (Outgoing.mk (ambientChannel p .inputCoupler (couplerChannel 3))) = _
  have hFirst := incidentSolution_apply_external p (isWellPosed p) input .inputFirst
  have hSecond := incidentSolution_apply_external p (isWellPosed p) input .inputSecond
  change incident (Incident.mk (ambientChannel p .inputCoupler (couplerChannel 0))) =
    input (externalIncidentEquiv p .inputFirst) at hFirst
  change incident (Incident.mk (ambientChannel p .inputCoupler (couplerChannel 1))) =
    input (externalIncidentEquiv p .inputSecond) at hSecond
  rw [leftInput_apply] at hFirst hSecond
  rcases inputCoupler_outgoing_right p incident with ⟨hOutgoingFirst, hOutgoingSecond⟩
  constructor
  · exact hOutgoingFirst.trans (by rw [hFirst, hSecond])
  · exact hOutgoingSecond.trans (by rw [hFirst, hSecond])

/-- The solved propagation arms carry the two launch amplitudes to the output coupler. -/
lemma incidentSolution_arm_right_amplitudes (p : Parameters) (first second : ℂ) :
    let input := leftInput p first second
    let incident :=
      ((netlist p).incidentSolutionBlockFormula (isWellPosed p)).toLinearMap input
    (netlist p).scatteringTransform.toLinearMap incident
          (Outgoing.mk (ambientChannel p .upperArm (armChannel 1))) =
        MatchedPropagation.transmissionCoefficient p.upperArm *
          ((p.inputCoupler.throughAmplitude : ℂ) * first +
            DirectionalCoupler.crossCoefficient p.inputCoupler * second) ∧
      (netlist p).scatteringTransform.toLinearMap incident
          (Outgoing.mk (ambientChannel p .lowerArm (armChannel 1))) =
        MatchedPropagation.transmissionCoefficient p.lowerArm *
          (DirectionalCoupler.crossCoefficient p.inputCoupler * first +
            (p.inputCoupler.throughAmplitude : ℂ) * second) := by
  let input := leftInput p first second
  let incident :=
    ((netlist p).incidentSolutionBlockFormula (isWellPosed p)).toLinearMap input
  change (netlist p).scatteringTransform.toLinearMap incident
        (Outgoing.mk (ambientChannel p .upperArm (armChannel 1))) = _ ∧
    (netlist p).scatteringTransform.toLinearMap incident
        (Outgoing.mk (ambientChannel p .lowerArm (armChannel 1))) = _
  have hLaunch := incidentSolution_inputCoupler_right_amplitudes p first second
  change (netlist p).scatteringTransform.toLinearMap incident
          (Outgoing.mk (ambientChannel p .inputCoupler (couplerChannel 2))) = _ ∧
      (netlist p).scatteringTransform.toLinearMap incident
          (Outgoing.mk (ambientChannel p .inputCoupler (couplerChannel 3))) = _ at hLaunch
  have hUpper := incidentSolution_apply_connected p (isWellPosed p) input
    ⟨Connection.upperInput, Sum.inr ()⟩
  have hLower := incidentSolution_apply_connected p (isWellPosed p) input
    ⟨Connection.lowerInput, Sum.inr ()⟩
  change incident (Incident.mk (ambientChannel p .upperArm (armChannel 0))) =
    (netlist p).scatteringTransform.toLinearMap incident
      (Outgoing.mk (ambientChannel p .inputCoupler (couplerChannel 2))) at hUpper
  change incident (Incident.mk (ambientChannel p .lowerArm (armChannel 0))) =
    (netlist p).scatteringTransform.toLinearMap incident
      (Outgoing.mk (ambientChannel p .inputCoupler (couplerChannel 3))) at hLower
  constructor
  · rw [upperArm_outgoing_right, hUpper, hLaunch.1]
  · rw [lowerArm_outgoing_right, hLower, hLaunch.2]

/-- N4 routing places the two solved arm outputs on the output coupler's left coordinates. -/
lemma incidentSolution_outputCoupler_left_amplitudes
    (p : Parameters) (first second : ℂ) :
    let input := leftInput p first second
    let incident :=
      ((netlist p).incidentSolutionBlockFormula (isWellPosed p)).toLinearMap input
    incident (Incident.mk (ambientChannel p .outputCoupler (couplerChannel 0))) =
        MatchedPropagation.transmissionCoefficient p.upperArm *
          ((p.inputCoupler.throughAmplitude : ℂ) * first +
            DirectionalCoupler.crossCoefficient p.inputCoupler * second) ∧
      incident (Incident.mk (ambientChannel p .outputCoupler (couplerChannel 1))) =
        MatchedPropagation.transmissionCoefficient p.lowerArm *
          (DirectionalCoupler.crossCoefficient p.inputCoupler * first +
            (p.inputCoupler.throughAmplitude : ℂ) * second) := by
  let input := leftInput p first second
  let incident :=
    ((netlist p).incidentSolutionBlockFormula (isWellPosed p)).toLinearMap input
  change incident (Incident.mk (ambientChannel p .outputCoupler (couplerChannel 0))) = _ ∧
    incident (Incident.mk (ambientChannel p .outputCoupler (couplerChannel 1))) = _
  have hArms := incidentSolution_arm_right_amplitudes p first second
  change (netlist p).scatteringTransform.toLinearMap incident
          (Outgoing.mk (ambientChannel p .upperArm (armChannel 1))) = _ ∧
      (netlist p).scatteringTransform.toLinearMap incident
          (Outgoing.mk (ambientChannel p .lowerArm (armChannel 1))) = _ at hArms
  have hUpper := incidentSolution_apply_connected p (isWellPosed p) input
    ⟨Connection.upperOutput, Sum.inr ()⟩
  have hLower := incidentSolution_apply_connected p (isWellPosed p) input
    ⟨Connection.lowerOutput, Sum.inr ()⟩
  change incident (Incident.mk (ambientChannel p .outputCoupler (couplerChannel 0))) =
    (netlist p).scatteringTransform.toLinearMap incident
      (Outgoing.mk (ambientChannel p .upperArm (armChannel 1))) at hUpper
  change incident (Incident.mk (ambientChannel p .outputCoupler (couplerChannel 1))) =
    (netlist p).scatteringTransform.toLinearMap incident
      (Outgoing.mk (ambientChannel p .lowerArm (armChannel 1))) at hLower
  exact ⟨hUpper.trans hArms.1, hLower.trans hArms.2⟩

/-- The Mach--Zehnder transfer amplitudes extracted by N5 elimination.

The negative-quadrature cross coefficient is exactly the N7 convention declared at
`Physlib/Optics/Components/DirectionalCoupler.lean:68-77`. A convention using the opposite cross
phase is related by an arm gauge; it is not a different power-transfer law.
-/
theorem output_amplitudes (p : Parameters) (first second : ℂ) :
    ((netlist p).responseTransform (isWellPosed p)).toLinearMap
          (leftInput p first second) (externalOutgoingEquiv p .outputFirst) =
        (p.outputCoupler.throughAmplitude : ℂ) *
            MatchedPropagation.transmissionCoefficient p.upperArm *
              ((p.inputCoupler.throughAmplitude : ℂ) * first +
                DirectionalCoupler.crossCoefficient p.inputCoupler * second) +
          DirectionalCoupler.crossCoefficient p.outputCoupler *
            MatchedPropagation.transmissionCoefficient p.lowerArm *
              (DirectionalCoupler.crossCoefficient p.inputCoupler * first +
                (p.inputCoupler.throughAmplitude : ℂ) * second) ∧
      ((netlist p).responseTransform (isWellPosed p)).toLinearMap
          (leftInput p first second) (externalOutgoingEquiv p .outputSecond) =
        DirectionalCoupler.crossCoefficient p.outputCoupler *
            MatchedPropagation.transmissionCoefficient p.upperArm *
              ((p.inputCoupler.throughAmplitude : ℂ) * first +
                DirectionalCoupler.crossCoefficient p.inputCoupler * second) +
          (p.outputCoupler.throughAmplitude : ℂ) *
            MatchedPropagation.transmissionCoefficient p.lowerArm *
              (DirectionalCoupler.crossCoefficient p.inputCoupler * first +
                (p.inputCoupler.throughAmplitude : ℂ) * second) := by
  let input := leftInput p first second
  let incident :=
    ((netlist p).incidentSolutionBlockFormula (isWellPosed p)).toLinearMap input
  have hOutputIncident := incidentSolution_outputCoupler_left_amplitudes p first second
  change incident (Incident.mk (ambientChannel p .outputCoupler (couplerChannel 0))) = _ ∧
    incident (Incident.mk (ambientChannel p .outputCoupler (couplerChannel 1))) = _
      at hOutputIncident
  have hOutput := outputCoupler_outgoing_right p incident
  rw [hOutputIncident.1, hOutputIncident.2] at hOutput
  constructor
  · change ((netlist p).responseTransform (isWellPosed p)).toLinearMap input
      (externalOutgoingEquiv p .outputFirst) = _
    rw [responseTransform_apply_external p (isWellPosed p) input .outputFirst]
    change (netlist p).scatteringTransform.toLinearMap incident
      (Outgoing.mk (ambientChannel p .outputCoupler (couplerChannel 2))) = _
    rw [hOutput.1]
    ring
  · change ((netlist p).responseTransform (isWellPosed p)).toLinearMap input
      (externalOutgoingEquiv p .outputSecond) = _
    rw [responseTransform_apply_external p (isWellPosed p) input .outputSecond]
    change (netlist p).scatteringTransform.toLinearMap incident
      (Outgoing.mk (ambientChannel p .outputCoupler (couplerChannel 3))) = _
    rw [hOutput.2]
    ring

end MachZehnder

end

end Optics
