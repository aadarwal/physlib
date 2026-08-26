/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Mathematics.LinearAlgebra.Matrix.Analytic
public import Physlib.Optics.Network.FlatNetlistElimination

/-!
# Parameterized compilation and network response domains

## i. Overview

A fixed-frequency scattering netlist describes one operating point. A physical device is instead
described by a family of component laws indexed by a parameter, usually optical frequency. This
file separates the parameter-independent data of a network -- component labels, physical ports,
mode fibers, and wiring -- from the parameter-dependent component scattering laws, and compiles
each parameter value to the fixed-frequency `FlatNetlist` semantics of `Physlib.Optics.Network`.

Two domains are then distinguished and never conflated.

* The *algebraic solve domain* collects the parameter values at which the compiled internal
  operator `1 - C * S` is invertible, equivalently at which the compiled netlist is well posed in
  the sense of `FlatNetlist.IsWellPosed`.
* Each component additionally carries a stored *parameter-validity* predicate recording where its
  own model is claimed to hold. The *physical response domain* is the intersection of the
  algebraic solve domain with every component's validity domain.

The response function is defined only on the physical response domain, and every statement about
it carries the proof gate. Evaluation commutes with compilation and with `N5` elimination: the
value of the response at a parameter is the response transform of the netlist compiled at that
parameter, which is in turn the exact four-factor block formula
`E_outᴴ * S * (1 - C * S)⁻¹ * E_in` at that parameter.

## ii. Key results

- `ParameterizedComponentFamily`: parameter-independent component geometry with parameter-dependent
  scattering laws and a stored per-component validity predicate.
- `ParameterizedComponentFamily.evaluate`: the fixed-frequency component family at one parameter.
- `ParameterizedNetlist`: a parameterized component family wired by parameter-independent
  connections.
- `ParameterizedNetlist.compile`: compilation of one parameter value to the `N4` flat netlist.
- `ParameterizedNetlist.solveDomain`: the algebraic domain where the compiled `1 - C * S` is
  invertible.
- `ParameterizedNetlist.responseDomain`: the physical domain, the intersection of the solve domain
  with every component's validity domain.
- `ParameterizedNetlist.response`: the proof-gated external response on the physical domain.
- `ParameterizedNetlist.response_eq_blockFormula`: evaluation commutes with compilation and
  elimination.
- `ParameterizedNetlist.mem_compileBehavior_iff_unguardedResponse`: on the algebraic solve domain
  the compiled singular-safe relational semantics is the graph of the total-inverse formula.
- `ParameterizedNetlist.mem_compileBehavior_iff_response`: its physical corollary on the response
  domain.
- `ParameterizedNetlist.unguardedResponse_eq_response`: the total-inverse formula agrees with the
  proof-gated response exactly on the domain.
- `ParameterizedNetlist.response_reparameterize`: response evaluation commutes with substitution
  into the parameter.
- `ParameterizedNetlist.continuousAt_unguardedResponse`: continuity of the algebraic total-inverse
  formula on the algebraic solve domain, from continuity of the stored component entries. This is
  not a claim that a physical response is continuous.
- `ParameterizedNetlist.analyticAt_unguardedResponse_entry`: entrywise analyticity of the algebraic
  total-inverse formula on the algebraic solve domain, from analyticity of the stored component
  entries. This is not a claim that a physical response is analytic.

## iii. Table of contents

- A. Parameterized component families
- B. Parameterized netlists, pointwise compilation, and reparameterization
- C. Algebraic solve and physical response domains
- D. The response function and evaluation commutation
- E. Reparameterization of the response domains
- F. Regularity under hypotheses on component data

## iv. References

This file supplies the parameterized layer only. It does not name a physical frequency variable, a
delay variable, a Laplace variable, or a `Z`-transform variable, and it asserts no relationship
between them; `Param` is an arbitrary index type. It does not assume that the stored component
laws are causal, passive, lossless, reciprocal, dispersive, or rational in any variable, and it
does not claim that the parameter-validity predicate is nonempty, open, connected, or physically
correct: validity is data supplied with the components, not a theorem.

No resonance condition, free-spectral-range statement, or spectral observable is derived here.
Those belong to the system milestone and must be derived from this response, not from an
independently postulated formula.

`unguardedResponse` is written with Mathlib's total matrix inverse purely to obtain a function of
the parameter with no proof argument, so that regularity can be stated. Its meaning differs across
three regions of the parameter space, and the difference is deliberate.

* Outside `solveDomain` the middle factor is Mathlib's junk value for the inverse of a singular
  matrix, and the whole expression means nothing at all.
* On `solveDomain \ validityDomain` the middle factor is a genuine algebraic inverse and the
  expression is the exact `N5` block formula, but not every component model is claimed valid
  there -- at least one component lacks a validity claim, while others may well have one -- so it
  is not a physical response. The regression exhibits such a parameter.
* On `responseDomain` it agrees with the proof-gated `response`.

Accordingly the algebraic statements about it carry a `solveDomain` hypothesis and the physical
ones a `responseDomain` hypothesis; the words *physical response* are reserved for the latter.

-/

@[expose] public section

namespace Optics

noncomputable section

universe p u v w x y z

/-!

## A. Parameterized component families

-/

-- The universe levels independently track parameters, component labels, local ports, and local
-- mode fibers.
set_option linter.checkUnivs false in
/-- An indexed family of optical scattering components whose local laws depend on a parameter.

The component labels, physical ports, and mode fibers are deliberately parameter-independent: a
network whose channel types changed with frequency could not have a single response function. Only
the stored scattering law varies. `IsValidAt` records, as data, where each component's own model
is claimed to hold; it is never proved here.
-/
structure ParameterizedComponentFamily (Param : Type p) where
  /-- The type indexing the component instances. -/
  Component : Type u
  /-- The typed physical-port family owned by each component, independent of the parameter. -/
  portFamily : Component → PortModeFamily.{v, w}
  /-- The scattering law of each component at each parameter value. -/
  scattering :
    Param → (component : Component) → ScatteringMatrix (portFamily component).Channel
  /-- The parameter values at which a component's stored law is claimed to be a valid model. -/
  IsValidAt : Component → Param → Prop

namespace ParameterizedComponentFamily

variable {Param : Type p} (family : ParameterizedComponentFamily.{p, u, v, w} Param)

/-- The fixed-frequency component family obtained by evaluating every component law at one
parameter value. -/
def evaluate (value : Param) : ScatteringComponentFamily.{u, v, w} where
  Component := family.Component
  portFamily := family.portFamily
  scattering := family.scattering value

/-- Evaluation retains the component labels. -/
lemma evaluate_component (value : Param) :
    (family.evaluate value).Component = family.Component := rfl

/-- Evaluation retains the physical-port family of each component. -/
lemma evaluate_portFamily (value : Param) :
    (family.evaluate value).portFamily = family.portFamily := rfl

/-- Evaluation selects exactly the stored law at that parameter value. -/
lemma evaluate_scattering (value : Param) :
    (family.evaluate value).scattering = family.scattering value := rfl

/-- The aggregate physical-port family of the components, retaining the component tag.

This is written independently of any parameter and is proved equal to the aggregate port family of
every evaluation, so that one wiring family serves every parameter value.
-/
def aggregatePortModeFamily : PortModeFamily.{max u v, w} where
  Port := Σ component : family.Component, (family.portFamily component).Port
  Mode := fun ⟨component, port⟩ => (family.portFamily component).Mode port

/-- Evaluating at a parameter does not change the aggregate physical-port family. -/
lemma evaluate_aggregatePortModeFamily (value : Param) :
    (family.evaluate value).aggregatePortModeFamily = family.aggregatePortModeFamily := rfl

/-- The aggregate physical channels of the components, independent of the parameter. -/
abbrev Channel := family.aggregatePortModeFamily.Channel

/-- Every component's stored model is claimed valid at this parameter value. -/
def IsValid (value : Param) : Prop :=
  ∀ component : family.Component, family.IsValidAt component value

/-- The set of parameters at which every component's stored model is claimed valid. -/
def validityDomain : Set Param := {value | family.IsValid value}

/-- Membership in the validity domain is exactly componentwise stored validity. -/
lemma mem_validityDomain_iff (value : Param) :
    value ∈ family.validityDomain ↔
      ∀ component : family.Component, family.IsValidAt component value := Iff.rfl

/-- A parameter-independent component family, declared valid at every parameter value.

This exhibits the fixed-frequency `N4` layer as the constant case of the parameterized layer; it
does not claim that any physical component is frequency-independent.
-/
def const (components : ScatteringComponentFamily.{u, v, w}) (Param : Type p) :
    ParameterizedComponentFamily.{p, u, v, w} Param where
  Component := components.Component
  portFamily := components.portFamily
  scattering := fun _ => components.scattering
  IsValidAt := fun _ _ => True

/-- Evaluating a constant family returns the original fixed-frequency family. -/
lemma evaluate_const (components : ScatteringComponentFamily.{u, v, w}) (value : Param) :
    (const components Param).evaluate value = components := rfl

/-- A constant family declares every parameter value valid. -/
lemma validityDomain_const (components : ScatteringComponentFamily.{u, v, w}) :
    (const components Param).validityDomain = Set.univ :=
  Set.eq_univ_of_forall fun _ _ => trivial

end ParameterizedComponentFamily

/-!

## B. Parameterized netlists, pointwise compilation, and reparameterization

-/

-- The universe levels independently track parameters, component labels, local ports, local mode
-- fibers, and connection labels.
set_option linter.checkUnivs false in
/-- A typed network of parameterized scattering components and parameter-independent connections.

The wiring is defined on the aggregate component port family, which does not depend on the
parameter, so the same proof-carrying connection data serves every parameter value.
-/
structure ParameterizedNetlist (Param : Type p) where
  /-- The parameterized components and their local scattering laws. -/
  components : ParameterizedComponentFamily.{p, u, v, w} Param
  /-- The type indexing the physical connections. -/
  Connection : Type x
  /-- The proof-carrying connections on the aggregate component boundary. -/
  connections : PortConnectionFamily components.aggregatePortModeFamily Connection

namespace ParameterizedNetlist

variable {Param : Type p} (netlist : ParameterizedNetlist.{p, u, v, w, x} Param)

/-- The fixed-frequency flat netlist compiled from one parameter value.

Only the component scattering laws are evaluated; the wiring is transported unchanged.
-/
def compile (value : Param) : FlatNetlist.{u, v, w, x} where
  components := netlist.components.evaluate value
  Connection := netlist.Connection
  connections := netlist.connections

/-- The aggregate physical channels, independent of the parameter. -/
abbrev Channel := netlist.components.Channel

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

/-- Compilation retains the aggregate channel type. -/
lemma compile_channel (value : Param) :
    (netlist.compile value).Channel = netlist.Channel := rfl

/-- Compilation retains the connected-channel type. -/
lemma compile_connectedChannel (value : Param) :
    (netlist.compile value).ConnectedChannel = netlist.ConnectedChannel := rfl

/-- Compilation retains the external-channel type. -/
lemma compile_externalChannel (value : Param) :
    (netlist.compile value).ExternalChannel = netlist.ExternalChannel := rfl

/-- Compilation transports the wiring data unchanged. -/
lemma compile_connections (value : Param) :
    (netlist.compile value).connections = netlist.connections := rfl

/-- Compilation evaluates exactly the stored component laws. -/
lemma compile_components (value : Param) :
    (netlist.compile value).components = netlist.components.evaluate value := rfl

/-- The component scattering entries of the compiled netlist are exactly the stored local entries
at that parameter value. -/
lemma compile_scatteringTransform_entry_same (value : Param)
    (component : netlist.components.Component)
    (output input : (netlist.components.portFamily component).Channel) :
    (netlist.compile value).scatteringTransform
        (Outgoing.mk
          ((netlist.compile value).components.componentChannelEmbedding component output))
        (Incident.mk
          ((netlist.compile value).components.componentChannelEmbedding component input)) =
      ((netlist.components.scattering value component)).toModeTransform output input :=
  (netlist.compile value).scatteringTransform_entry_same component output input

/-- Distinct component blocks never scatter directly into one another at any parameter value. -/
lemma compile_scatteringTransform_entry_of_ne (value : Param)
    {first second : netlist.components.Component} (hComponent : first ≠ second)
    (output : (netlist.components.portFamily first).Channel)
    (input : (netlist.components.portFamily second).Channel) :
    (netlist.compile value).scatteringTransform
        (Outgoing.mk
          ((netlist.compile value).components.componentChannelEmbedding first output))
        (Incident.mk
          ((netlist.compile value).components.componentChannelEmbedding second input)) = 0 :=
  (netlist.compile value).scatteringTransform_entry_of_ne hComponent output input

/-- Substituting a map into the parameter of a network.

The geometry, wiring, and component laws are untouched; only the indexing of parameter values
changes.
-/
def reparameterize {Param' : Type z} (substitution : Param' → Param) :
    ParameterizedNetlist.{z, u, v, w, x} Param' where
  components :=
    { Component := netlist.components.Component
      portFamily := netlist.components.portFamily
      scattering := fun value' => netlist.components.scattering (substitution value')
      IsValidAt := fun component value' =>
        netlist.components.IsValidAt component (substitution value') }
  Connection := netlist.Connection
  connections := netlist.connections

/-- Compiling a substituted network at a parameter is compiling the original network at the
substituted value. -/
lemma compile_reparameterize {Param' : Type z} (substitution : Param' → Param)
    (value' : Param') :
    (netlist.reparameterize substitution).compile value' =
      netlist.compile (substitution value') := rfl

section Finite

variable [Fintype netlist.Channel] [Fintype netlist.ConnectedChannel]

/-- The compiled aggregate channels are finite. -/
local instance compileChannelFintype (value : Param) :
    Fintype (netlist.compile value).Channel :=
  inferInstanceAs (Fintype netlist.Channel)

/-- The compiled connected channels are finite. -/
local instance compileConnectedChannelFintype (value : Param) :
    Fintype (netlist.compile value).ConnectedChannel :=
  inferInstanceAs (Fintype netlist.ConnectedChannel)

/-- Classical equality on compiled aggregate channels, kept local to the parameterized layer. -/
local instance compileChannelDecidableEq (value : Param) :
    DecidableEq (netlist.compile value).Channel := Classical.decEq _

/-- Classical equality on compiled connected channels, kept local to the parameterized layer. -/
local instance compileConnectedChannelDecidableEq (value : Param) :
    DecidableEq (netlist.compile value).ConnectedChannel := Classical.decEq _

/-- Classical equality on aggregate channels, kept local to the parameterized layer. -/
local instance parameterizedChannelDecidableEq : DecidableEq netlist.Channel :=
  Classical.decEq _

/-- Classical equality on connected channels, kept local to the parameterized layer. -/
local instance parameterizedConnectedChannelDecidableEq :
    DecidableEq netlist.ConnectedChannel := Classical.decEq _

/-- The external channels of a finite parameterized netlist are finite. -/
local instance parameterizedExternalChannelFintype : Fintype netlist.ExternalChannel := by
  classical
  infer_instance

/-- The assembled component law `S` of the network at one parameter value, displayed in the
parameter-independent aggregate boundary coordinates. -/
def scatteringTransform (value : Param) :
    ModeTransform netlist.IncidentIndex netlist.OutgoingIndex :=
  (netlist.compile value).scatteringTransform

/-- The partial internal-routing law `C`, derived from the wiring alone. -/
def routingTransform : ModeTransform netlist.OutgoingIndex netlist.IncidentIndex :=
  netlist.connections.partialRouting

/-- The external incident injection `E_in`, derived from the wiring alone. -/
def inputExposure : ModeTransform netlist.ExternalIncident netlist.IncidentIndex :=
  netlist.connections.externalIncidentInjection

/-- The external outgoing readout `E_outᴴ`, derived from the wiring alone. -/
def outputReadout : ModeTransform netlist.OutgoingIndex netlist.ExternalOutgoing :=
  netlist.connections.externalOutgoingReadout

/-- The incident-space internal operator `1 - C * S` at one parameter value, with no
invertibility claim. -/
def feedbackOperator (value : Param) :
    ModeTransform netlist.IncidentIndex netlist.IncidentIndex :=
  (netlist.compile value).feedbackOperator

omit [Fintype netlist.Channel] [Fintype netlist.ConnectedChannel] in
/-- The parameterized component law is the compiled component law. -/
lemma compile_scatteringTransform (value : Param) :
    (netlist.compile value).scatteringTransform = netlist.scatteringTransform value := rfl

omit [Fintype netlist.Channel] in
/-- Internal routing is derived from the wiring alone and therefore does not depend on the
parameter. -/
lemma compile_routingTransform (value : Param) :
    (netlist.compile value).routingTransform = netlist.routingTransform := rfl

omit [Fintype netlist.Channel] [Fintype netlist.ConnectedChannel] in
/-- External incident injection is derived from the wiring alone and therefore does not depend on
the parameter. -/
lemma compile_inputExposure (value : Param) :
    (netlist.compile value).inputExposure = netlist.inputExposure := rfl

omit [Fintype netlist.Channel] [Fintype netlist.ConnectedChannel] in
/-- External outgoing readout is derived from the wiring alone and therefore does not depend on
the parameter. -/
lemma compile_outputReadout (value : Param) :
    (netlist.compile value).outputReadout = netlist.outputReadout := rfl

/-- The parameterized internal operator is the compiled internal operator. -/
lemma compile_feedbackOperator (value : Param) :
    (netlist.compile value).feedbackOperator = netlist.feedbackOperator value := rfl

/-- The internal operator is `1 - C * S` with only the component law evaluated. -/
lemma feedbackOperator_eq (value : Param) :
    netlist.feedbackOperator value =
      1 - netlist.routingTransform * netlist.scatteringTransform value := rfl

/-!

## C. Algebraic solve and physical response domains

-/

/-- The algebraic solve domain: the parameters at which the compiled network is well posed.

This is a statement about the internal operator `1 - C * S` alone. It records nothing about
whether the stored component models are claimed to hold there.
-/
def solveDomain : Set Param := {value | (netlist.compile value).IsWellPosed}

/-- Membership in the algebraic solve domain is exactly compiled well-posedness. -/
lemma mem_solveDomain_iff (value : Param) :
    value ∈ netlist.solveDomain ↔ (netlist.compile value).IsWellPosed := Iff.rfl

/-- The algebraic solve domain is exactly where the internal operator is bijective. -/
lemma mem_solveDomain_iff_feedbackOperator_bijective (value : Param) :
    value ∈ netlist.solveDomain ↔
      Function.Bijective (netlist.feedbackOperator value).toLinearMap :=
  (netlist.compile value).isWellPosed_iff_feedbackOperator_bijective

/-- The algebraic solve domain is exactly where the internal determinant is nonzero. -/
lemma mem_solveDomain_iff_det_ne_zero (value : Param) :
    value ∈ netlist.solveDomain ↔ (netlist.feedbackOperator value).det ≠ 0 :=
  (netlist.compile value).isWellPosed_iff_feedbackOperator_det_ne_zero

/-- The physical response domain: algebraic solvability together with stored component validity.

Intersecting is not cosmetic. A parameter at which the internal operator happens to be invertible
but at which some component's own model is not claimed to hold carries an algebraic solution and
no physical response.
-/
def responseDomain : Set Param :=
  netlist.solveDomain ∩ netlist.components.validityDomain

/-- Membership in the physical response domain unfolds to its two independent conditions. -/
lemma mem_responseDomain_iff (value : Param) :
    value ∈ netlist.responseDomain ↔
      (netlist.compile value).IsWellPosed ∧
        ∀ component : netlist.components.Component,
          netlist.components.IsValidAt component value := Iff.rfl

/-- The physical response domain is contained in the algebraic solve domain. -/
lemma responseDomain_subset_solveDomain : netlist.responseDomain ⊆ netlist.solveDomain :=
  Set.inter_subset_left

/-- The physical response domain is contained in the stored component validity domain. -/
lemma responseDomain_subset_validityDomain :
    netlist.responseDomain ⊆ netlist.components.validityDomain :=
  Set.inter_subset_right

/-- A parameter of the physical response domain compiles to a well-posed netlist. -/
lemma isWellPosed_compile_of_mem_responseDomain {value : Param}
    (hValue : value ∈ netlist.responseDomain) : (netlist.compile value).IsWellPosed := hValue.1

/-- A parameter of the physical response domain satisfies every component's stored validity
predicate. -/
lemma isValidAt_of_mem_responseDomain {value : Param}
    (hValue : value ∈ netlist.responseDomain) (component : netlist.components.Component) :
    netlist.components.IsValidAt component value := hValue.2 component

/-!

## D. The response function and evaluation commutation

-/

/-- The external response of the network at a parameter of the physical response domain.

The proof gate is the compiled well-posedness extracted from domain membership; no inverse is
formed without it.
-/
def response {value : Param} (hValue : value ∈ netlist.responseDomain) :
    ModeTransform netlist.ExternalIncident netlist.ExternalOutgoing :=
  (netlist.compile value).responseTransform hValue.1

/-- The response at a parameter is the behavior-derived response transform of the netlist compiled
at that parameter: evaluation commutes with compilation. -/
lemma response_eq_responseTransform {value : Param}
    (hValue : value ∈ netlist.responseDomain) :
    netlist.response hValue = (netlist.compile value).responseTransform hValue.1 := rfl

/-- The response at a parameter is the proof-gated `N5` block formula at that parameter:
evaluation commutes with elimination. -/
lemma response_eq_blockFormula {value : Param} (hValue : value ∈ netlist.responseDomain) :
    netlist.response hValue = (netlist.compile value).responseBlockFormula hValue.1 :=
  (netlist.compile value).responseTransform_eq_blockFormula hValue.1

/-- The graph of the response is exactly the compiled singular-safe relational semantics. -/
lemma toBehavior_response {value : Param} (hValue : value ∈ netlist.responseDomain) :
    (netlist.response hValue).toBehavior = (netlist.compile value).behavior :=
  (netlist.compile value).toBehavior_responseTransform hValue.1

/-- The response does not depend on which proof of domain membership is supplied. -/
lemma response_congr {value : Param} (first second : value ∈ netlist.responseDomain) :
    netlist.response first = netlist.response second := rfl

/-- Mathlib's total matrix inverse of the internal operator, in parameter-uniform coordinates.

Naming it fixes the index type once, and makes every use of the total inverse visible. It is an
inverse only on the algebraic solve domain; see `totalFeedbackInverse_eq_feedbackInverse`.
-/
def totalFeedbackInverse (value : Param) :
    ModeTransform netlist.IncidentIndex netlist.IncidentIndex :=
  (netlist.feedbackOperator value)⁻¹

/-- The external response formula written with Mathlib's total matrix inverse.

This is a function of the parameter with no proof argument, which is what regularity statements
need. Outside the solve domain the middle factor is the total inverse of a singular matrix and the
value is not a network response; `unguardedResponse_eq_response` is the only bridge, and it is
gated.
-/
def unguardedResponse (value : Param) :
    ModeTransform netlist.ExternalIncident netlist.ExternalOutgoing :=
  netlist.outputReadout * netlist.scatteringTransform value *
    netlist.totalFeedbackInverse value * netlist.inputExposure

/-- On the solve domain the proof-gated feedback inverse is Mathlib's total matrix inverse. -/
lemma totalFeedbackInverse_eq_feedbackInverse {value : Param}
    (hValue : (netlist.compile value).IsWellPosed) :
    netlist.totalFeedbackInverse value =
      (netlist.compile value).feedbackInverse hValue :=
  Matrix.inv_eq_left_inv ((netlist.compile value).feedbackInverse_mul_feedbackOperator hValue)

/-- On the algebraic solve domain the total-inverse formula is exactly the proof-gated `N5` block
formula. The algebraic gate alone licenses the algebraic formula; it does not license calling the
result a physical response. -/
lemma unguardedResponse_eq_blockFormula {value : Param}
    (hSolve : value ∈ netlist.solveDomain) :
    netlist.unguardedResponse value =
      (netlist.compile value).responseBlockFormula hSolve := by
  rw [unguardedResponse, netlist.totalFeedbackInverse_eq_feedbackInverse hSolve,
    (netlist.compile value).responseBlockFormula_eq hSolve]
  rfl

/-- The total-inverse formula agrees with the proof-gated response exactly on the physical
response domain. -/
lemma unguardedResponse_eq_response {value : Param}
    (hValue : value ∈ netlist.responseDomain) :
    netlist.unguardedResponse value = netlist.response hValue := by
  rw [netlist.unguardedResponse_eq_blockFormula hValue.1,
    netlist.response_eq_blockFormula hValue]

/-- On the algebraic solve domain, the compiled singular-safe relational semantics is exactly
evaluation of the algebraic total-inverse formula.

This is the commutation statement on the well-posed domain: wherever the compiled network is
uniquely solvable, evaluating the parameter, compiling, and eliminating give the same relation,
whether or not any component's stored model is claimed to hold there.
-/
lemma mem_compileBehavior_iff_unguardedResponse {value : Param}
    (hSolve : value ∈ netlist.solveDomain)
    (input : ModeAmplitude netlist.ExternalIncident)
    (output : ModeAmplitude netlist.ExternalOutgoing) :
    (input, output) ∈ (netlist.compile value).behavior ↔
      output = (netlist.unguardedResponse value).toLinearMap input := by
  rw [netlist.unguardedResponse_eq_blockFormula hSolve,
    ← (netlist.compile value).toBehavior_responseBlockFormula hSolve]
  exact ModeTransform.mem_toBehavior_iff_toLinearMap _ _ _

/-- On the physical response domain, the compiled relational semantics is evaluation of the
proof-gated response: the physical corollary of the solve-domain commutation statement. -/
lemma mem_compileBehavior_iff_response {value : Param}
    (hValue : value ∈ netlist.responseDomain)
    (input : ModeAmplitude netlist.ExternalIncident)
    (output : ModeAmplitude netlist.ExternalOutgoing) :
    (input, output) ∈ (netlist.compile value).behavior ↔
      output = (netlist.response hValue).toLinearMap input := by
  rw [← netlist.unguardedResponse_eq_response hValue]
  exact netlist.mem_compileBehavior_iff_unguardedResponse hValue.1 input output

/-- Applying the response solves the compiled network equations at that parameter. -/
lemma response_apply_mem_compileBehavior {value : Param}
    (hValue : value ∈ netlist.responseDomain)
    (input : ModeAmplitude netlist.ExternalIncident) :
    (input, (netlist.response hValue).toLinearMap input) ∈ (netlist.compile value).behavior :=
  (netlist.mem_compileBehavior_iff_response hValue input _).mpr rfl

/-- The response at a parameter of the physical domain is the exact four-factor elimination
product `E_outᴴ * S * (1 - C * S)⁻¹ * E_in`, with only the component law evaluated at that
parameter and the internal inverse taken where the solve domain licenses it. -/
lemma response_eq_fourFactor {value : Param} (hValue : value ∈ netlist.responseDomain) :
    netlist.response hValue =
      netlist.outputReadout * netlist.scatteringTransform value *
        netlist.totalFeedbackInverse value * netlist.inputExposure := by
  rw [← netlist.unguardedResponse_eq_response hValue, unguardedResponse]

/-!

## E. Reparameterization of the response domains

-/

section Reparameterize

variable {Param' : Type z} (substitution : Param' → Param)

/-- The aggregate channels of a substituted network are finite. -/
local instance reparameterizeChannelFintype :
    Fintype (netlist.reparameterize substitution).Channel :=
  inferInstanceAs (Fintype netlist.Channel)

/-- The connected channels of a substituted network are finite. -/
local instance reparameterizeConnectedChannelFintype :
    Fintype (netlist.reparameterize substitution).ConnectedChannel :=
  inferInstanceAs (Fintype netlist.ConnectedChannel)

/-- The algebraic solve domain of a substituted network is the preimage of the original one. -/
lemma solveDomain_reparameterize :
    (netlist.reparameterize substitution).solveDomain =
      substitution ⁻¹' netlist.solveDomain := rfl

/-- The physical response domain of a substituted network is the preimage of the original one. -/
lemma responseDomain_reparameterize :
    (netlist.reparameterize substitution).responseDomain =
      substitution ⁻¹' netlist.responseDomain := rfl

/-- Response evaluation commutes with substitution into the parameter. -/
lemma response_reparameterize
    {value' : Param'} (hValue' : value' ∈ (netlist.reparameterize substitution).responseDomain)
    (hValue : substitution value' ∈ netlist.responseDomain) :
    (netlist.reparameterize substitution).response hValue' = netlist.response hValue := rfl

end Reparameterize

/-!

## F. Regularity under hypotheses on component data

-/

section Regularity

/-- Each component's stored scattering entries vary continuously at a parameter value. -/
def ComponentEntriesContinuousAt [TopologicalSpace Param] (value : Param) : Prop :=
  ∀ (component : netlist.components.Component)
    (output input : (netlist.components.portFamily component).Channel),
    ContinuousAt (fun parameter =>
      (netlist.components.scattering parameter component).toModeTransform output input) value

/-- Each component's stored scattering entries are analytic at a parameter value. -/
def ComponentEntriesAnalyticAt [NormedAddCommGroup Param] [NormedSpace ℂ Param]
    (value : Param) : Prop :=
  ∀ (component : netlist.components.Component)
    (output input : (netlist.components.portFamily component).Channel),
    AnalyticAt ℂ (fun parameter =>
      (netlist.components.scattering parameter component).toModeTransform output input) value

section Continuity

variable [TopologicalSpace Param]

omit [Fintype netlist.Channel] [Fintype netlist.ConnectedChannel] in
/-- Componentwise continuity of the stored laws gives continuity of the assembled component
law. Cross-component entries are identically zero and contribute nothing. -/
lemma continuousAt_scatteringTransform {value : Param}
    (hComponents : netlist.ComponentEntriesContinuousAt value) :
    ContinuousAt netlist.scatteringTransform value := by
  classical
  refine continuousAt_pi.mpr fun output => continuousAt_pi.mpr fun input => ?_
  obtain ⟨⟨⟨outputComponent, outputPort⟩, outputMode⟩⟩ := output
  obtain ⟨⟨⟨inputComponent, inputPort⟩, inputMode⟩⟩ := input
  by_cases hComponent : outputComponent = inputComponent
  · subst hComponent
    have hEntry : (fun parameter : Param =>
        netlist.scatteringTransform parameter
          ⟨⟨⟨outputComponent, outputPort⟩, outputMode⟩⟩
          ⟨⟨⟨outputComponent, inputPort⟩, inputMode⟩⟩) =
        fun parameter : Param =>
          (netlist.components.scattering parameter outputComponent).toModeTransform
            ⟨outputPort, outputMode⟩ ⟨inputPort, inputMode⟩ := by
      funext parameter
      exact (netlist.compile parameter).scatteringTransform_entry_same outputComponent
        ⟨outputPort, outputMode⟩ ⟨inputPort, inputMode⟩
    rw [hEntry]
    exact hComponents outputComponent ⟨outputPort, outputMode⟩ ⟨inputPort, inputMode⟩
  · have hEntry : (fun parameter : Param =>
        netlist.scatteringTransform parameter
          ⟨⟨⟨outputComponent, outputPort⟩, outputMode⟩⟩
          ⟨⟨⟨inputComponent, inputPort⟩, inputMode⟩⟩) = fun _ : Param => 0 := by
      funext parameter
      exact (netlist.compile parameter).scatteringTransform_entry_of_ne hComponent
        ⟨outputPort, outputMode⟩ ⟨inputPort, inputMode⟩
    rw [hEntry]
    exact continuousAt_const

/-- Continuity of the assembled component law gives continuity of the internal operator, which
differs from it by the fixed wiring. -/
lemma continuousAt_feedbackOperator {value : Param}
    (hScattering : ContinuousAt netlist.scatteringTransform value) :
    ContinuousAt netlist.feedbackOperator value := by
  have hMap : Continuous fun matrix : ModeTransform netlist.IncidentIndex netlist.OutgoingIndex =>
      (1 : ModeTransform netlist.IncidentIndex netlist.IncidentIndex) -
        netlist.routingTransform * matrix :=
    continuous_const.sub (continuous_const.matrix_mul continuous_id)
  exact hMap.continuousAt.comp hScattering

/-- On the algebraic solve domain, continuity of the stored component data gives continuity of the
algebraic total-inverse formula.

This is a statement about `unguardedResponse` under the algebraic gate alone. It does not claim
continuity of a physical response: no component's stored validity is assumed, and on the part of
the solve domain where validity fails there is no physical response to be continuous. The physical
statement is this one restricted to `responseDomain`, where `unguardedResponse_eq_response`
applies.
-/
lemma continuousAt_unguardedResponse {value : Param}
    (hComponents : netlist.ComponentEntriesContinuousAt value)
    (hSolve : value ∈ netlist.solveDomain) :
    ContinuousAt netlist.unguardedResponse value := by
  classical
  have hScattering : ContinuousAt netlist.scatteringTransform value :=
    netlist.continuousAt_scatteringTransform hComponents
  have hFeedback : ContinuousAt netlist.feedbackOperator value :=
    netlist.continuousAt_feedbackOperator hScattering
  have hDet : (netlist.feedbackOperator value).det ≠ 0 :=
    (netlist.mem_solveDomain_iff_det_ne_zero value).mp hSolve
  have hRingInverse : ContinuousAt Ring.inverse (netlist.feedbackOperator value).det := by
    simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hDet
  have hInverse : ContinuousAt netlist.totalFeedbackInverse value :=
    (continuousAt_matrix_inv _ hRingInverse).comp hFeedback
  have hLeft : Continuous fun matrix :
      ModeTransform netlist.IncidentIndex netlist.OutgoingIndex =>
      netlist.outputReadout * matrix :=
    continuous_const.matrix_mul continuous_id
  have hRight : Continuous fun matrix :
      ModeTransform netlist.IncidentIndex netlist.ExternalOutgoing =>
      matrix * netlist.inputExposure :=
    continuous_id.matrix_mul continuous_const
  have hProduct : ContinuousAt (fun parameter =>
      netlist.outputReadout * netlist.scatteringTransform parameter *
        netlist.totalFeedbackInverse parameter) value :=
    ((continuous_fst.matrix_mul continuous_snd :
      Continuous fun pair :
        ModeTransform netlist.IncidentIndex netlist.ExternalOutgoing ×
          ModeTransform netlist.IncidentIndex netlist.IncidentIndex =>
        pair.1 * pair.2).continuousAt).comp
      ((hLeft.continuousAt.comp hScattering).prodMk hInverse)
  exact hRight.continuousAt.comp hProduct

end Continuity

section Analyticity

variable [NormedAddCommGroup Param] [NormedSpace ℂ Param]

omit [Fintype netlist.Channel] [Fintype netlist.ConnectedChannel] in
/-- Componentwise analyticity of the stored laws gives entrywise analyticity of the assembled
component law. -/
lemma analyticAt_scatteringTransform_entry {value : Param}
    (hComponents : netlist.ComponentEntriesAnalyticAt value)
    (output : netlist.OutgoingIndex) (input : netlist.IncidentIndex) :
    AnalyticAt ℂ (fun parameter => netlist.scatteringTransform parameter output input) value := by
  classical
  obtain ⟨⟨⟨outputComponent, outputPort⟩, outputMode⟩⟩ := output
  obtain ⟨⟨⟨inputComponent, inputPort⟩, inputMode⟩⟩ := input
  by_cases hComponent : outputComponent = inputComponent
  · subst hComponent
    have hEntry : (fun parameter : Param =>
        netlist.scatteringTransform parameter
          ⟨⟨⟨outputComponent, outputPort⟩, outputMode⟩⟩
          ⟨⟨⟨outputComponent, inputPort⟩, inputMode⟩⟩) =
        fun parameter : Param =>
          (netlist.components.scattering parameter outputComponent).toModeTransform
            ⟨outputPort, outputMode⟩ ⟨inputPort, inputMode⟩ := by
      funext parameter
      exact (netlist.compile parameter).scatteringTransform_entry_same outputComponent
        ⟨outputPort, outputMode⟩ ⟨inputPort, inputMode⟩
    rw [hEntry]
    exact hComponents outputComponent ⟨outputPort, outputMode⟩ ⟨inputPort, inputMode⟩
  · have hEntry : (fun parameter : Param =>
        netlist.scatteringTransform parameter
          ⟨⟨⟨outputComponent, outputPort⟩, outputMode⟩⟩
          ⟨⟨⟨inputComponent, inputPort⟩, inputMode⟩⟩) = fun _ : Param => 0 := by
      funext parameter
      exact (netlist.compile parameter).scatteringTransform_entry_of_ne hComponent
        ⟨outputPort, outputMode⟩ ⟨inputPort, inputMode⟩
    rw [hEntry]
    exact analyticAt_const

/-- Entrywise analyticity of the assembled component law gives entrywise analyticity of the
internal operator. -/
lemma analyticAt_feedbackOperator_entry {value : Param}
    (hScattering : ∀ output input,
      AnalyticAt ℂ (fun parameter => netlist.scatteringTransform parameter output input) value)
    (output input : netlist.IncidentIndex) :
    AnalyticAt ℂ (fun parameter => netlist.feedbackOperator parameter output input) value := by
  have hEntry : (fun parameter : Param => netlist.feedbackOperator parameter output input) =
      fun parameter : Param =>
        (1 : ModeTransform netlist.IncidentIndex netlist.IncidentIndex) output input -
          ∑ middle : netlist.OutgoingIndex,
            netlist.routingTransform output middle *
              netlist.scatteringTransform parameter middle input := by
    funext parameter
    rw [netlist.feedbackOperator_eq parameter, Matrix.sub_apply, Matrix.mul_apply]
  rw [hEntry]
  exact analyticAt_const.sub
    (Finset.analyticAt_fun_sum _ fun middle _ =>
      analyticAt_const.mul (hScattering middle input))

/-- On the algebraic solve domain, analyticity of the stored component data gives entrywise
analyticity of the algebraic total-inverse formula.

As with continuity, the gate here is algebraic only: this is not a claim that a physical response
is analytic, and it becomes one only on `responseDomain`. The inverse factor is handled by
Mathlib's determinant/adjugate presentation of the matrix inverse: `Matrix.inv_def` reduces it to
a reciprocal determinant, which is analytic exactly because the solve domain forbids a vanishing
determinant.
-/
lemma analyticAt_unguardedResponse_entry {value : Param}
    (hComponents : netlist.ComponentEntriesAnalyticAt value)
    (hSolve : value ∈ netlist.solveDomain)
    (output : netlist.ExternalOutgoing) (input : netlist.ExternalIncident) :
    AnalyticAt ℂ (fun parameter => netlist.unguardedResponse parameter output input) value := by
  classical
  have hScattering : ∀ first second,
      AnalyticAt ℂ (fun parameter =>
        netlist.scatteringTransform parameter first second) value :=
    fun first second => netlist.analyticAt_scatteringTransform_entry hComponents first second
  have hFeedback : ∀ first second,
      AnalyticAt ℂ (fun parameter => netlist.feedbackOperator parameter first second) value :=
    fun first second => netlist.analyticAt_feedbackOperator_entry hScattering first second
  have hDet : (netlist.feedbackOperator value).det ≠ 0 :=
    (netlist.mem_solveDomain_iff_det_ne_zero value).mp hSolve
  have hDetAnalytic : AnalyticAt ℂ
      (fun parameter => (netlist.feedbackOperator parameter).det) value :=
    analyticAt_matrix_det hFeedback
  have hInverse : ∀ first second,
      AnalyticAt ℂ (fun parameter =>
        netlist.totalFeedbackInverse parameter first second) value :=
    fun first second =>
      analyticAt_matrix_inv_entry hFeedback hDet first second
  have hFirst : ∀ first second,
      AnalyticAt ℂ (fun parameter =>
        (netlist.outputReadout * netlist.scatteringTransform parameter) first second) value :=
    fun first second =>
      analyticAt_matrix_mul_entry (left := fun _ => netlist.outputReadout)
        (fun _ _ => analyticAt_const) hScattering first second
  have hSecond : ∀ first second,
      AnalyticAt ℂ (fun parameter =>
        (netlist.outputReadout * netlist.scatteringTransform parameter *
          netlist.totalFeedbackInverse parameter) first second) value :=
    fun first second => analyticAt_matrix_mul_entry hFirst hInverse first second
  exact analyticAt_matrix_mul_entry (right := fun _ => netlist.inputExposure) hSecond
    (fun _ _ => analyticAt_const) output input

end Analyticity

end Regularity

end Finite

end ParameterizedNetlist

end

end Optics
