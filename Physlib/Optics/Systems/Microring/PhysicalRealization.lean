/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Systems.Microring.PhysicalParameters

/-!
# Physical realization of microring travelling-field relations

## i. Overview

This file specifies forward travelling-field relations independently of the S2 netlists. The
one-bus relation connects the incident and through fields to the launched and returning ring
fields. The two-bus relation additionally exposes both symmetric half arcs and the add/drop bus.

The typed topologies are then defined by mapping physical parameters into the existing explicit
N7 netlists. The realization lemmas prove, from the component scattering and wiring equations,
that every netlist behavior supplies internal fields satisfying the independent relations. Under
the exact S2 nonzero-denominator gates, separate elimination lemmas prove that every such relation
solution has the S2 through and drop transfers. Thus the transfer expressions are consequences of
the component realization rather than fields stored in a formula container.

The parameter records, field relations, and singular-safe netlist behaviors are total. Their
canonical passive interpretation requires `AllPassPhysicalParameters.IsValid` or
`AddDropPhysicalParameters.IsValid`; a functional N5 response additionally requires the displayed
nonzero-denominator gate. No matrix inverse or determinant identity is asserted without that gate.

The N7 `-I * k` cross coefficient is defined at
`Physlib/Optics/Components/DirectionalCoupler.lean:68-70`. All-pass through response contains its
square and is gauge-insensitive. Add-drop response contains one cross factor from each coupler and
is gauge-dependent. Its first-arc factor also makes it reference-plane-dependent; this file uses
the symmetric half-arc convention at
`Physlib/Optics/Systems/Microring/AddDropNetwork.lean:117-181`.

No DATE'14/SysCon'15 source matrix is asserted in this source-neutral file. That final port and
parameter dictionary must compose this realization with the separately audited source bridge.
No reciprocity, dispersion, bending loss, coupling-length, thermal, nonlinear, bandwidth,
causality, group-delay, or material realization is claimed. Power means normalized modal power,
not electromagnetic power before the finite, common-frequency, Maxwell-qualified, pairwise-
integrable, mutually flux-orthogonal, unit-normalized bridge at
`Physlib/Optics/HarmonicFlux/PropagatingModePower.lean:16-22,60-93`.

## ii. Key results

- `AllPassFieldRelation`: independent one-bus external/internal field equations.
- `AddDropFieldRelation`: independent two-bus external/internal field equations.
- `allPassTopology_satisfies_fieldRelation`: the N7 one-bus realization certificate.
- `addDropTopology_satisfies_fieldRelation`: the N7 two-bus realization certificate.
- `AllPassFieldRelation.through_eq_transfer`: relation solutions induce the S2 transfer.
- `AddDropFieldRelation.through_drop_eq_transfer`: relation solutions induce both S2 transfers.
- `allPass_physicalResponse_eq_transfer`: the proof-gated N5 one-bus consequence.
- `addDrop_physicalResponse_eq_transfers`: the proof-gated N5 two-bus consequence.

## iii. Table of contents

- A. Typed physical topologies
- B. Independent travelling-field relations
- C. N7 realization certificates
- D. Relation-level elimination
- E. Proof-gated N5 consequences

## iv. References

The source contrast is DATE'14 Def. 3 and SysCon'15 Def. 3, summarized at
`HOL-CORPUS.md:194-198,232-249`: those predicates store closed-form transfer fields. Here the field
relations contain only local coupler and propagation equations, and their closed forms are proved.
-/

@[expose] public section

namespace Optics

noncomputable section

namespace Microring

/-!
## A. Typed physical topologies
-/

/-- The typed one-coupler, one-propagation-component topology selected by physical data. -/
abbrev allPassTopology (p : AllPassPhysicalParameters) : FlatNetlist :=
  AllPass.netlist p.toParameters

/-- The input channel of the physical one-bus topology. -/
abbrev allPassInputChannel (p : AllPassPhysicalParameters) :
    (allPassTopology p).ExternalChannel :=
  AllPass.inputChannel p.toParameters

/-- The through channel of the physical one-bus topology. -/
abbrev allPassThroughChannel (p : AllPassPhysicalParameters) :
    (allPassTopology p).ExternalChannel :=
  AllPass.throughChannel p.toParameters

/-- The typed two-coupler, two-half-arc topology selected by physical data. -/
abbrev addDropTopology (p : AddDropPhysicalParameters) : FlatNetlist :=
  AddDrop.netlist p.toParameters

/-- The input channel of the physical two-bus topology. -/
abbrev addDropInputChannel (p : AddDropPhysicalParameters) :
    (addDropTopology p).ExternalChannel :=
  AddDrop.inputChannel p.toParameters

/-- The through channel of the physical two-bus topology. -/
abbrev addDropThroughChannel (p : AddDropPhysicalParameters) :
    (addDropTopology p).ExternalChannel :=
  AddDrop.throughChannel p.toParameters

/-- The add channel of the physical two-bus topology. -/
abbrev addDropAddChannel (p : AddDropPhysicalParameters) :
    (addDropTopology p).ExternalChannel :=
  AddDrop.addChannel p.toParameters

/-- The drop channel of the physical two-bus topology. -/
abbrev addDropDropChannel (p : AddDropPhysicalParameters) :
    (addDropTopology p).ExternalChannel :=
  AddDrop.dropChannel p.toParameters

/-!
## B. Independent travelling-field relations
-/

/-- Internal forward-circulating fields of a one-bus ring at the coupler reference plane. -/
structure AllPassInternalFields where
  /-- Field launched from the coupler into the ring. -/
  launched : ℂ
  /-- Field returning to the coupler after one complete circulation. -/
  returning : ℂ

/-- Independent one-bus relation between external and internal travelling fields.

The relation states only the local N7 coupler equations and the full-circulation propagation
equation. It does not mention a netlist, response transform, or closed-form transfer.
-/
def AllPassFieldRelation (p : AllPassPhysicalParameters) (incident through : ℂ)
    (internal : AllPassInternalFields) : Prop :=
  through =
      (p.toParameters.throughAmplitude : ℂ) * incident +
        DirectionalCoupler.crossCoefficient p.toParameters.coupler * internal.returning ∧
    internal.launched =
      DirectionalCoupler.crossCoefficient p.toParameters.coupler * incident +
        (p.toParameters.throughAmplitude : ℂ) * internal.returning ∧
    internal.returning = p.toParameters.loopCoefficient * internal.launched

/-- Internal forward-circulating fields of a two-bus ring in the symmetric half-arc convention. -/
structure AddDropInternalFields where
  /-- Field launched by the input coupler into the first half arc. -/
  inputCouplerOutput : ℂ
  /-- Field arriving at the drop coupler after the first half arc. -/
  dropCouplerInput : ℂ
  /-- Field launched by the drop coupler into the second half arc. -/
  dropCouplerOutput : ℂ
  /-- Field returning to the input coupler after the second half arc. -/
  inputCouplerInput : ℂ

/-- Independent two-bus relation between external and internal travelling fields.

The drop amplitude uses the N7 negative-quadrature gauge and the S2 first-half-arc reference
plane. These are defined at `Physlib/Optics/Components/DirectionalCoupler.lean:68-77` and
`Physlib/Optics/Systems/Microring/AddDropNetwork.lean:116-166`; both choices are explicit in the
coefficients appearing here.
-/
def AddDropFieldRelation (p : AddDropPhysicalParameters)
    (input add through drop : ℂ) (internal : AddDropInternalFields) : Prop :=
  through =
      (p.toParameters.inputThroughAmplitude : ℂ) * input +
        DirectionalCoupler.crossCoefficient p.toParameters.inputCoupler *
          internal.inputCouplerInput ∧
    internal.inputCouplerOutput =
      DirectionalCoupler.crossCoefficient p.toParameters.inputCoupler * input +
        (p.toParameters.inputThroughAmplitude : ℂ) * internal.inputCouplerInput ∧
    internal.dropCouplerInput =
      p.toParameters.firstArcCoefficient * internal.inputCouplerOutput ∧
    drop =
      (p.toParameters.dropThroughAmplitude : ℂ) * add +
        DirectionalCoupler.crossCoefficient p.toParameters.dropCoupler *
          internal.dropCouplerInput ∧
    internal.dropCouplerOutput =
      DirectionalCoupler.crossCoefficient p.toParameters.dropCoupler * add +
        (p.toParameters.dropThroughAmplitude : ℂ) * internal.dropCouplerInput ∧
    internal.inputCouplerInput =
      p.toParameters.secondArcCoefficient * internal.dropCouplerOutput

/-!
## C. N7 realization certificates
-/

/-- Extract the two forward internal one-bus fields from a complete N7 netlist state. -/
def allPassInternalFieldsOfState (p : AllPassPhysicalParameters)
    (incident : ModeAmplitude (allPassTopology p).IncidentIndex)
    (outgoing : ModeAmplitude (allPassTopology p).OutgoingIndex) : AllPassInternalFields where
  launched := outgoing (Outgoing.mk
    (AllPass.couplerChannel p.toParameters DirectionalCoupler.Port.rightSecond))
  returning := incident (Incident.mk
    (AllPass.couplerChannel p.toParameters DirectionalCoupler.Port.leftSecond))

/-- The N7 component and wiring equations of the one-bus topology satisfy its field relation. -/
lemma allPass_realization_satisfies_fieldRelation (p : AllPassPhysicalParameters)
    (external : ModeAmplitude (allPassTopology p).ExternalIncident)
    (incident : ModeAmplitude (allPassTopology p).IncidentIndex)
    (outgoing : ModeAmplitude (allPassTopology p).OutgoingIndex)
    (hScattering : outgoing =
      (allPassTopology p).scatteringTransform.toLinearMap incident)
    (hAssembly : incident =
      (allPassTopology p).connections.incidentAssembly outgoing external) :
    AllPassFieldRelation p
      (external (Incident.mk (allPassInputChannel p)))
      (outgoing (Outgoing.mk
        (AllPass.couplerChannel p.toParameters DirectionalCoupler.Port.rightFirst)))
      (allPassInternalFieldsOfState p incident outgoing) := by
  let q := p.toParameters
  have hInput := congrArg
    (fun state => state (Incident.mk
      (AllPass.couplerChannel q DirectionalCoupler.Port.leftFirst))) hAssembly
  rw [AllPass.incidentAssembly_apply_leftFirst] at hInput
  have hPropagationInput := congrArg
    (fun state => state (Incident.mk
      (AllPass.propagationChannel q MatchedPropagation.Port.left))) hAssembly
  rw [AllPass.incidentAssembly_apply_propagation_left] at hPropagationInput
  have hReturn := congrArg
    (fun state => state (Incident.mk
      (AllPass.couplerChannel q DirectionalCoupler.Port.leftSecond))) hAssembly
  rw [AllPass.incidentAssembly_apply_coupler_leftSecond] at hReturn
  refine ⟨?_, ?_, ?_⟩
  · have hThrough :=
      AllPass.scatteringEquation_coupler_rightFirst q incident outgoing hScattering
    rw [hInput] at hThrough
    simpa [q, allPassInternalFieldsOfState] using hThrough
  · have hLaunched :=
      AllPass.scatteringEquation_coupler_rightSecond q incident outgoing hScattering
    rw [hInput] at hLaunched
    simpa [q, allPassInternalFieldsOfState] using hLaunched
  · rw [allPassInternalFieldsOfState, hReturn,
      AllPass.scatteringEquation_propagation_right q incident outgoing hScattering,
      hPropagationInput]

/-- Every behavior of the typed one-bus N7 topology has fields satisfying the independent
relation. -/
lemma allPassTopology_satisfies_fieldRelation (p : AllPassPhysicalParameters)
    (external : ModeAmplitude (allPassTopology p).ExternalIncident)
    (output : ModeAmplitude (allPassTopology p).ExternalOutgoing)
    (hBehavior : (external, output) ∈ (allPassTopology p).behavior) :
    ∃ internal, AllPassFieldRelation p
      (external (Incident.mk (allPassInputChannel p)))
      (output (Outgoing.mk (allPassThroughChannel p))) internal := by
  rcases ((allPassTopology p).mem_behavior_iff_equations external output).mp hBehavior with
    ⟨incident, outgoing, hScattering, hAssembly, hOutput⟩
  have hAssembly' : incident =
      (allPassTopology p).connections.incidentAssembly outgoing external := by
    simpa only [PortConnectionFamily.incidentAssembly] using hAssembly
  refine ⟨allPassInternalFieldsOfState p incident outgoing, ?_⟩
  have hRelation := allPass_realization_satisfies_fieldRelation
    p external incident outgoing hScattering hAssembly'
  have hReadout := congrArg
    (fun state => state (Outgoing.mk (allPassThroughChannel p))) hOutput
  rw [AllPass.outputReadout_apply_through] at hReadout
  rwa [hReadout]

/-- Extract the four forward internal two-bus fields from a complete N7 netlist state. -/
def addDropInternalFieldsOfState (p : AddDropPhysicalParameters)
    (incident : ModeAmplitude (addDropTopology p).IncidentIndex)
    (outgoing : ModeAmplitude (addDropTopology p).OutgoingIndex) : AddDropInternalFields where
  inputCouplerOutput := outgoing (Outgoing.mk
    (AddDrop.inputCouplerChannel p.toParameters DirectionalCoupler.Port.rightSecond))
  dropCouplerInput := incident (Incident.mk
    (AddDrop.dropCouplerChannel p.toParameters DirectionalCoupler.Port.leftSecond))
  dropCouplerOutput := outgoing (Outgoing.mk
    (AddDrop.dropCouplerChannel p.toParameters DirectionalCoupler.Port.rightSecond))
  inputCouplerInput := incident (Incident.mk
    (AddDrop.inputCouplerChannel p.toParameters DirectionalCoupler.Port.leftSecond))

/-- The N7 component and wiring equations of the two-bus topology satisfy its field relation. -/
lemma addDrop_realization_satisfies_fieldRelation (p : AddDropPhysicalParameters)
    (external : ModeAmplitude (addDropTopology p).ExternalIncident)
    (incident : ModeAmplitude (addDropTopology p).IncidentIndex)
    (outgoing : ModeAmplitude (addDropTopology p).OutgoingIndex)
    (hScattering : outgoing =
      (addDropTopology p).scatteringTransform.toLinearMap incident)
    (hAssembly : incident =
      (addDropTopology p).connections.incidentAssembly outgoing external) :
    AddDropFieldRelation p
      (external (Incident.mk (addDropInputChannel p)))
      (external (Incident.mk (addDropAddChannel p)))
      (outgoing (Outgoing.mk
        (AddDrop.inputCouplerChannel p.toParameters DirectionalCoupler.Port.rightFirst)))
      (outgoing (Outgoing.mk
        (AddDrop.dropCouplerChannel p.toParameters DirectionalCoupler.Port.rightFirst)))
      (addDropInternalFieldsOfState p incident outgoing) := by
  let q := p.toParameters
  have hInput := congrArg
    (fun state => state (Incident.mk
      (AddDrop.inputCouplerChannel q DirectionalCoupler.Port.leftFirst))) hAssembly
  rw [AddDrop.incidentAssembly_apply_input_leftFirst] at hInput
  have hAdd := congrArg
    (fun state => state (Incident.mk
      (AddDrop.dropCouplerChannel q DirectionalCoupler.Port.leftFirst))) hAssembly
  rw [AddDrop.incidentAssembly_apply_drop_leftFirst] at hAdd
  have hFirstInput := congrArg
    (fun state => state (Incident.mk
      (AddDrop.firstArcChannel q MatchedPropagation.Port.left))) hAssembly
  rw [AddDrop.incidentAssembly_apply_firstArc_left] at hFirstInput
  have hDropInput := congrArg
    (fun state => state (Incident.mk
      (AddDrop.dropCouplerChannel q DirectionalCoupler.Port.leftSecond))) hAssembly
  rw [AddDrop.incidentAssembly_apply_dropCoupler_leftSecond] at hDropInput
  have hSecondInput := congrArg
    (fun state => state (Incident.mk
      (AddDrop.secondArcChannel q MatchedPropagation.Port.left))) hAssembly
  rw [AddDrop.incidentAssembly_apply_secondArc_left] at hSecondInput
  have hReturn := congrArg
    (fun state => state (Incident.mk
      (AddDrop.inputCouplerChannel q DirectionalCoupler.Port.leftSecond))) hAssembly
  rw [AddDrop.incidentAssembly_apply_inputCoupler_leftSecond] at hReturn
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hThrough :=
      AddDrop.scatteringEquation_inputCoupler_rightFirst q incident outgoing hScattering
    rw [hInput] at hThrough
    simpa [q, addDropInternalFieldsOfState] using hThrough
  · have hLaunched :=
      AddDrop.scatteringEquation_inputCoupler_rightSecond q incident outgoing hScattering
    rw [hInput] at hLaunched
    simpa [q, addDropInternalFieldsOfState] using hLaunched
  · rw [addDropInternalFieldsOfState, hDropInput,
      AddDrop.scatteringEquation_firstArc_right q incident outgoing hScattering,
      hFirstInput]
  · have hDrop :=
      AddDrop.scatteringEquation_dropCoupler_rightFirst q incident outgoing hScattering
    rw [hAdd] at hDrop
    simpa [q, addDropInternalFieldsOfState] using hDrop
  · have hDropLaunched :=
      AddDrop.scatteringEquation_dropCoupler_rightSecond q incident outgoing hScattering
    rw [hAdd] at hDropLaunched
    simpa [q, addDropInternalFieldsOfState] using hDropLaunched
  · rw [addDropInternalFieldsOfState, hReturn,
      AddDrop.scatteringEquation_secondArc_right q incident outgoing hScattering,
      hSecondInput]

/-- Every behavior of the typed two-bus N7 topology has fields satisfying the independent
relation. -/
lemma addDropTopology_satisfies_fieldRelation (p : AddDropPhysicalParameters)
    (external : ModeAmplitude (addDropTopology p).ExternalIncident)
    (output : ModeAmplitude (addDropTopology p).ExternalOutgoing)
    (hBehavior : (external, output) ∈ (addDropTopology p).behavior) :
    ∃ internal, AddDropFieldRelation p
      (external (Incident.mk (addDropInputChannel p)))
      (external (Incident.mk (addDropAddChannel p)))
      (output (Outgoing.mk (addDropThroughChannel p)))
      (output (Outgoing.mk (addDropDropChannel p))) internal := by
  rcases ((addDropTopology p).mem_behavior_iff_equations external output).mp hBehavior with
    ⟨incident, outgoing, hScattering, hAssembly, hOutput⟩
  have hAssembly' : incident =
      (addDropTopology p).connections.incidentAssembly outgoing external := by
    simpa only [PortConnectionFamily.incidentAssembly] using hAssembly
  refine ⟨addDropInternalFieldsOfState p incident outgoing, ?_⟩
  have hRelation := addDrop_realization_satisfies_fieldRelation
    p external incident outgoing hScattering hAssembly'
  have hThrough := congrArg
    (fun state => state (Outgoing.mk (addDropThroughChannel p))) hOutput
  rw [AddDrop.outputReadout_apply_through] at hThrough
  have hDrop := congrArg
    (fun state => state (Outgoing.mk (addDropDropChannel p))) hOutput
  rw [AddDrop.outputReadout_apply_drop] at hDrop
  rwa [hThrough, hDrop]

/-!
## D. Relation-level elimination
-/

/-- Under the exact all-pass solve gate, every one-bus relation solution has the S2 transfer. -/
lemma AllPassFieldRelation.through_eq_transfer {p : AllPassPhysicalParameters}
    {incident through : ℂ} {internal : AllPassInternalFields}
    (hRelation : AllPassFieldRelation p incident through internal)
    (hDenominator : p.toParameters.HasNonzeroDenominator) :
    through = AllPass.throughTransfer p.toParameters * incident := by
  let q := p.toParameters
  have hReturning : q.denominator * internal.returning =
      q.loopCoefficient * DirectionalCoupler.crossCoefficient q.coupler * incident := by
    rw [AllPass.Parameters.denominator, AllPass.Parameters.loopGain]
    linear_combination hRelation.2.2 + q.loopCoefficient * hRelation.2.1
  have hReturning' : internal.returning =
      q.loopCoefficient * DirectionalCoupler.crossCoefficient q.coupler * incident /
        q.denominator := by
    apply (eq_div_iff hDenominator).2
    rw [mul_comm, hReturning]
  rw [hRelation.1, hReturning', AllPass.throughTransfer]
  ring

/-- Under the exact add-drop solve gate and zero add input, every relation solution has both S2
transfers in the gauge and reference plane cited by `AddDropFieldRelation`. -/
lemma AddDropFieldRelation.through_drop_eq_transfer {p : AddDropPhysicalParameters}
    {input add through drop : ℂ} {internal : AddDropInternalFields}
    (hRelation : AddDropFieldRelation p input add through drop internal)
    (hAdd : add = 0) (hDenominator : p.toParameters.HasNonzeroDenominator) :
    through = AddDrop.throughTransfer p.toParameters * input ∧
      drop = AddDrop.dropTransfer p.toParameters * input := by
  let q := p.toParameters
  simp only [AddDropFieldRelation, hAdd, mul_zero, zero_add] at hRelation
  have hReturning : q.denominator * internal.inputCouplerInput =
      q.secondArcCoefficient * (q.dropThroughAmplitude : ℂ) *
        q.firstArcCoefficient * DirectionalCoupler.crossCoefficient q.inputCoupler * input := by
    rw [AddDrop.Parameters.denominator, AddDrop.Parameters.loopGain,
      AddDrop.Parameters.roundTripCoefficient]
    linear_combination hRelation.2.2.2.2.2 +
      q.secondArcCoefficient * hRelation.2.2.2.2.1 +
      q.secondArcCoefficient * (q.dropThroughAmplitude : ℂ) * hRelation.2.2.1 +
      q.secondArcCoefficient * (q.dropThroughAmplitude : ℂ) *
        q.firstArcCoefficient * hRelation.2.1
  have hReturning' : internal.inputCouplerInput =
      q.secondArcCoefficient * (q.dropThroughAmplitude : ℂ) *
        q.firstArcCoefficient * DirectionalCoupler.crossCoefficient q.inputCoupler * input /
          q.denominator := by
    apply (eq_div_iff hDenominator).2
    rw [mul_comm, hReturning]
  have hDropInput : q.denominator * internal.dropCouplerInput =
      q.firstArcCoefficient * DirectionalCoupler.crossCoefficient q.inputCoupler * input := by
    rw [AddDrop.Parameters.denominator, AddDrop.Parameters.loopGain,
      AddDrop.Parameters.roundTripCoefficient]
    linear_combination hRelation.2.2.1 + q.firstArcCoefficient * hRelation.2.1 +
      q.firstArcCoefficient * (q.inputThroughAmplitude : ℂ) * hRelation.2.2.2.2.2 +
      q.firstArcCoefficient * (q.inputThroughAmplitude : ℂ) *
        q.secondArcCoefficient * hRelation.2.2.2.2.1
  have hDropInput' : internal.dropCouplerInput =
      q.firstArcCoefficient * DirectionalCoupler.crossCoefficient q.inputCoupler * input /
        q.denominator := by
    apply (eq_div_iff hDenominator).2
    rw [mul_comm, hDropInput]
  constructor
  · rw [hRelation.1, hReturning', AddDrop.throughTransfer,
      AddDrop.Parameters.roundTripCoefficient]
    ring
  · rw [hRelation.2.2.2.1, hDropInput', AddDrop.dropTransfer]
    ring

/-!
## E. Proof-gated N5 consequences
-/

/-- The proof-gated N5 response of the physical one-bus topology satisfies its field relation. -/
lemma allPass_physicalResponse_satisfies_fieldRelation (p : AllPassPhysicalParameters)
    (hDenominator : p.toParameters.HasNonzeroDenominator) (amplitude : ℂ) :
    ∃ internal, AllPassFieldRelation p amplitude
      (((allPassTopology p).responseTransform
        (AllPass.isWellPosed_of_hasNonzeroDenominator p.toParameters hDenominator)).toLinearMap
        (AllPass.inputAmplitude p.toParameters amplitude)
        (Outgoing.mk (allPassThroughChannel p))) internal := by
  let hWellPosed := AllPass.isWellPosed_of_hasNonzeroDenominator
    p.toParameters hDenominator
  let output := (allPassTopology p).responseTransform hWellPosed |>.toLinearMap
    (AllPass.inputAmplitude p.toParameters amplitude)
  have hBehavior : (AllPass.inputAmplitude p.toParameters amplitude, output) ∈
      (allPassTopology p).behavior := by
    rw [← (allPassTopology p).toBehavior_responseTransform hWellPosed,
      ModeTransform.mem_toBehavior_iff_toLinearMap]
  obtain ⟨internal, hRelation⟩ :=
    allPassTopology_satisfies_fieldRelation p _ output hBehavior
  refine ⟨internal, ?_⟩
  rw [AllPass.inputAmplitude_apply_input] at hRelation
  simpa [output, hWellPosed] using hRelation

/-- The physical one-bus N7 realization induces the S2 transfer under its exact solve gate. -/
lemma allPass_physicalResponse_eq_transfer (p : AllPassPhysicalParameters)
    (hDenominator : p.toParameters.HasNonzeroDenominator) (amplitude : ℂ) :
    ((allPassTopology p).responseTransform
      (AllPass.isWellPosed_of_hasNonzeroDenominator p.toParameters hDenominator)).toLinearMap
      (AllPass.inputAmplitude p.toParameters amplitude)
      (Outgoing.mk (allPassThroughChannel p)) =
        AllPass.throughTransfer p.toParameters * amplitude := by
  obtain ⟨internal, hRelation⟩ :=
    allPass_physicalResponse_satisfies_fieldRelation p hDenominator amplitude
  exact hRelation.through_eq_transfer hDenominator

/-- The proof-gated N5 response of the physical two-bus topology satisfies its field relation. -/
lemma addDrop_physicalResponse_satisfies_fieldRelation (p : AddDropPhysicalParameters)
    (hDenominator : p.toParameters.HasNonzeroDenominator) (amplitude : ℂ) :
    ∃ internal, AddDropFieldRelation p amplitude 0
      (((addDropTopology p).responseTransform
        (AddDrop.isWellPosed_of_hasNonzeroDenominator p.toParameters hDenominator)).toLinearMap
        (AddDrop.inputAmplitude p.toParameters amplitude)
        (Outgoing.mk (addDropThroughChannel p)))
      (((addDropTopology p).responseTransform
        (AddDrop.isWellPosed_of_hasNonzeroDenominator p.toParameters hDenominator)).toLinearMap
        (AddDrop.inputAmplitude p.toParameters amplitude)
        (Outgoing.mk (addDropDropChannel p))) internal := by
  let hWellPosed := AddDrop.isWellPosed_of_hasNonzeroDenominator
    p.toParameters hDenominator
  let output := (addDropTopology p).responseTransform hWellPosed |>.toLinearMap
    (AddDrop.inputAmplitude p.toParameters amplitude)
  have hBehavior : (AddDrop.inputAmplitude p.toParameters amplitude, output) ∈
      (addDropTopology p).behavior := by
    rw [← (addDropTopology p).toBehavior_responseTransform hWellPosed,
      ModeTransform.mem_toBehavior_iff_toLinearMap]
  obtain ⟨internal, hRelation⟩ :=
    addDropTopology_satisfies_fieldRelation p _ output hBehavior
  refine ⟨internal, ?_⟩
  rw [AddDrop.inputAmplitude_apply_input, AddDrop.inputAmplitude_apply_add] at hRelation
  simpa [output, hWellPosed] using hRelation

/-- The physical two-bus N7 realization induces both S2 transfers under its exact solve gate. -/
lemma addDrop_physicalResponse_eq_transfers (p : AddDropPhysicalParameters)
    (hDenominator : p.toParameters.HasNonzeroDenominator) (amplitude : ℂ) :
    ((addDropTopology p).responseTransform
      (AddDrop.isWellPosed_of_hasNonzeroDenominator p.toParameters hDenominator)).toLinearMap
      (AddDrop.inputAmplitude p.toParameters amplitude)
      (Outgoing.mk (addDropThroughChannel p)) =
        AddDrop.throughTransfer p.toParameters * amplitude ∧
    ((addDropTopology p).responseTransform
      (AddDrop.isWellPosed_of_hasNonzeroDenominator p.toParameters hDenominator)).toLinearMap
      (AddDrop.inputAmplitude p.toParameters amplitude)
      (Outgoing.mk (addDropDropChannel p)) =
        AddDrop.dropTransfer p.toParameters * amplitude := by
  obtain ⟨internal, hRelation⟩ :=
    addDrop_physicalResponse_satisfies_fieldRelation p hDenominator amplitude
  exact hRelation.through_drop_eq_transfer rfl hDenominator

end Microring

end

end Optics
