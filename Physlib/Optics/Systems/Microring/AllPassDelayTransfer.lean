/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Systems.DelayTransfer.Evaluation
public import Physlib.Optics.Systems.Microring.AllPass

/-!
# Rational delay netlist of the all-pass microring

## i. Overview

This file lifts the physical all-pass microring into the generic rational-delay network layer. The
coupler entries are constant rational models, while the matched propagation arc carries the formal
one-delay factor `a*q`. Pointwise evaluation is proved to recover the existing N7 component family
and the exact S2 connection family when the stored loop coefficient is `a*q`.

The proof-gated response is derived from the compiled netlist's component and wiring equations. It
is not defined by the closed-form all-pass transfer. Thus this module supplies the semantic bridge
needed to compare reciprocal-Z and causal Z-transform descriptions with the already verified N5
ring response.

## ii. Key results

- `allPassRationalComponents`, `allPassRationalNetlist`: the rational N7 component family and S2
  wiring.
- `allPassRationalNetlist_compile_eq`: pointwise evaluation recovers `AllPass.netlist`.
- `allPassRationalNetlist_mem_responseDomain`: component validity and the exact feedback gate give
  a proof-gated response point.
- `allPassRationalNetlist_responseThrough`: the compiled channel equations determine the through
  response.
- `allPassRationalNetlist_response_entry`: the selected rational/N5F response entry equals the
  physical S2 transfer.
- `allPassRationalNetlist_response_cleared`: the compiled response obeys
  `(1 - t*a*q) * H(q) = t - a*q`.

## iii. Table of contents

- A. Rational components and compilation
- B. Compiled channels and component equations
- C. Wiring-coordinate bridges
- D. Solve domain and proof-gated response

## iv. References

This is Physlib-original integration between the S2 all-pass netlist and the S4 delay-transfer
layer. The formal variable is a propagation factor, not by itself a physical frequency, causal
delay, or region of convergence. The response theorem requires the explicit validity and N5 solve
gates; no ROC equivalence, symbolic fraction-field elimination, or material model is claimed.
-/

@[expose] public section

namespace Optics.DelayTransfer

noncomputable section

/-!
## A. Rational components and compilation
-/

/-- The rational entry model for a matched propagation arc with formal factor `a*q`. -/
def allPassPropagationEntryModel (a : ℂ)
    (output input : (MatchedPropagation.portFamily Unit).Channel) : RationalModel 1 :=
  match output.1, input.1 with
  | .left, .right | .right, .left =>
      RationalModel.ofPolynomial (MvPolynomial.C a * MvPolynomial.X 0)
  | _, _ => RationalModel.constant 0

/-- Evaluating a formal propagation entry gives `a*q` across the arc and zero reflection. -/
lemma allPassPropagationEntryModel_eval (a q : ℂ)
    (output input : (MatchedPropagation.portFamily Unit).Channel) :
    (allPassPropagationEntryModel a output input).eval (fun _ => q) =
      match output.1, input.1 with
      | .left, .right | .right, .left => a * q
      | _, _ => 0 := by
  rcases output with ⟨outputPort, outputMode⟩
  rcases input with ⟨inputPort, inputMode⟩
  cases outputPort <;> cases inputPort <;> cases outputMode <;> cases inputMode <;>
    simp [allPassPropagationEntryModel]

/-- The evaluated formal propagation entries, collected in the N7 physical-channel labels. -/
def allPassEvaluatedPropagationScattering (a q : ℂ) :
    ScatteringMatrix ((MatchedPropagation.portFamily Unit).Channel) where
  toModeTransform output input :=
    (allPassPropagationEntryModel a output input).eval (fun _ => q)

/-- If `a*q` is the stored propagation coefficient, the evaluated entry matrix is the N7
matched-propagation scattering matrix. -/
lemma allPassEvaluatedPropagationScattering_eq (p : AllPass.Parameters) (q : ℂ)
    (hLoop : p.loopCoefficient = (p.fieldAttenuation : ℂ) * q) :
    allPassEvaluatedPropagationScattering (p.fieldAttenuation : ℂ) q =
      MatchedPropagation.physicalScattering p.propagation Unit := by
  change MatchedPropagation.transmissionCoefficient p.propagation =
    (p.fieldAttenuation : ℂ) * q at hLoop
  change ScatteringMatrix.mk _ = ScatteringMatrix.mk _
  congr 1
  funext output input
  rcases output with ⟨outputPort, outputMode⟩
  rcases input with ⟨inputPort, inputMode⟩
  cases outputPort <;> cases inputPort <;> cases outputMode <;> cases inputMode
  all_goals
    simp only [allPassPropagationEntryModel,
      RationalModel.eval_ofPolynomial, RationalModel.eval_constant, MvPolynomial.eval_mul,
      MvPolynomial.eval_C, MvPolynomial.eval_X]
    rw [ModeTransform.reindex_apply]
    simp [MatchedPropagation.scattering, ReflectionlessTwoPort.scattering,
      MatchedPropagation.transmission, MatchedPropagation.channelEquiv,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, hLoop]

/-- The S2 all-pass component family with constant N7 coupler entries and formal arc entries. -/
def allPassRationalComponents (p : AllPass.Parameters) : RationalComponentFamily 1 where
  Component := AllPass.Component
  portFamily := AllPass.componentPortFamily
  entryModel
    | .coupler => fun output input =>
        RationalModel.constant
          ((AllPass.componentScattering p .coupler).toModeTransform output input)
    | .propagation => allPassPropagationEntryModel (p.fieldAttenuation : ℂ)
  ModelValidAt := fun _ _ => p.IsValid

/-- The rational all-pass ring uses the exact proof-carrying S2 feedback connections. -/
def allPassRationalNetlist (p : AllPass.Parameters) : RationalNetlist 1 where
  components := allPassRationalComponents p
  Connection := AllPass.Connection
  connections := AllPass.connections p

/-- The left-bus input channel in the retained formal-delay presentation. -/
def allPassRationalFormalInputChannel (p : AllPass.Parameters) :
    (allPassRationalNetlist p).ExternalChannel :=
  ⟨⟨⟨AllPass.Component.coupler, DirectionalCoupler.Port.leftFirst⟩, ()⟩, by
    rintro ⟨⟨connection, channel⟩, hChannel⟩
    cases connection <;> rcases channel with mode | mode <;> cases mode
    all_goals cases hChannel⟩

/-- The right-bus through channel in the retained formal-delay presentation. -/
def allPassRationalFormalThroughChannel (p : AllPass.Parameters) :
    (allPassRationalNetlist p).ExternalChannel :=
  ⟨⟨⟨AllPass.Component.coupler, DirectionalCoupler.Port.rightFirst⟩, ()⟩, by
    rintro ⟨⟨connection, channel⟩, hChannel⟩
    cases connection <;> rcases channel with mode | mode <;> cases mode
    all_goals cases hChannel⟩

/-- The rational all-pass model retains the finite aggregate S2 channels. -/
noncomputable instance allPassRationalChannelFintype (p : AllPass.Parameters) :
    Fintype (allPassRationalNetlist p).Channel :=
  AllPass.channelFintype p

/-- The rational all-pass model retains the finite connected S2 channels. -/
noncomputable instance allPassRationalConnectedChannelFintype (p : AllPass.Parameters) :
    Fintype (allPassRationalNetlist p).ConnectedChannel :=
  AllPass.connectedChannelFintype p

/-- Laplace reparameterization retains the finite aggregate all-pass channels. -/
noncomputable instance allPassRationalLaplaceChannelFintype (p : AllPass.Parameters)
    (delays : Fin 1 → ℝ) :
    Fintype ((allPassRationalNetlist p).laplace delays).Channel :=
  inferInstanceAs (Fintype (allPassRationalNetlist p).Channel)

/-- Laplace reparameterization retains the finite connected all-pass channels. -/
noncomputable instance allPassRationalLaplaceConnectedChannelFintype (p : AllPass.Parameters)
    (delays : Fin 1 → ℝ) :
    Fintype ((allPassRationalNetlist p).laplace delays).ConnectedChannel :=
  inferInstanceAs (Fintype (allPassRationalNetlist p).ConnectedChannel)

/-- Reciprocal-Z reparameterization retains the finite aggregate all-pass channels. -/
noncomputable instance allPassRationalReciprocalZChannelFintype (p : AllPass.Parameters) :
    Fintype (allPassRationalNetlist p).reciprocalZ.Channel :=
  inferInstanceAs (Fintype (allPassRationalNetlist p).Channel)

/-- Reciprocal-Z reparameterization retains the finite connected all-pass channels. -/
noncomputable instance allPassRationalReciprocalZConnectedChannelFintype (p : AllPass.Parameters) :
    Fintype (allPassRationalNetlist p).reciprocalZ.ConnectedChannel :=
  inferInstanceAs (Fintype (allPassRationalNetlist p).ConnectedChannel)

/-- Pointwise compilation retains the finite aggregate all-pass channels. -/
noncomputable instance allPassRationalCompileChannelFintype (p : AllPass.Parameters)
    (value : DelayTuple 1) : Fintype ((allPassRationalNetlist p).compile value).Channel :=
  ParameterizedNetlist.compileChannelFintype
    (allPassRationalNetlist p).toParameterizedNetlist value

/-- Pointwise compilation retains the finite connected all-pass channels. -/
noncomputable instance allPassRationalCompileConnectedChannelFintype (p : AllPass.Parameters)
    (value : DelayTuple 1) :
    Fintype ((allPassRationalNetlist p).compile value).ConnectedChannel :=
  ParameterizedNetlist.compileConnectedChannelFintype
    (allPassRationalNetlist p).toParameterizedNetlist value

/-- Pointwise compiled all-pass channels have classical decidable equality. -/
noncomputable instance allPassRationalCompileChannelDecidableEq (p : AllPass.Parameters)
    (value : DelayTuple 1) : DecidableEq ((allPassRationalNetlist p).compile value).Channel :=
  Classical.decEq _

/-- Pointwise compiled connected all-pass channels have classical decidable equality. -/
noncomputable instance allPassRationalCompileConnectedChannelDecidableEq (p : AllPass.Parameters)
    (value : DelayTuple 1) :
    DecidableEq ((allPassRationalNetlist p).compile value).ConnectedChannel :=
  Classical.decEq _

/-- Evaluating the rational component family leaves the N7 coupler scattering matrix unchanged. -/
lemma allPassRationalComponents_scattering_coupler (p : AllPass.Parameters)
    (value : DelayTuple 1) :
    (allPassRationalComponents p).scattering value .coupler =
      DirectionalCoupler.physicalScattering p.coupler Unit := by
  unfold RationalComponentFamily.scattering
  dsimp [allPassRationalComponents]
  congr 1
  funext output input
  rw [RationalModel.eval_constant]
  rfl

/-- If the formal arc evaluates to the stored loop coefficient, its scattering matrix is S2's
matched-propagation matrix. -/
lemma allPassRationalComponents_scattering_propagation (p : AllPass.Parameters) (q : ℂ)
    (hLoop : p.loopCoefficient = (p.fieldAttenuation : ℂ) * q) :
    (allPassRationalComponents p).scattering (fun _ => q) .propagation =
      MatchedPropagation.physicalScattering p.propagation Unit := by
  unfold RationalComponentFamily.scattering
  dsimp [allPassRationalComponents]
  exact allPassEvaluatedPropagationScattering_eq p q hLoop

/-- Evaluating every formal component entry recovers the S2 component family when `a*q` is the
declared loop coefficient. -/
lemma allPassRationalComponents_scattering_eq (p : AllPass.Parameters) (q : ℂ)
    (hLoop : p.loopCoefficient = (p.fieldAttenuation : ℂ) * q) :
    (allPassRationalComponents p).scattering (fun _ => q) =
      AllPass.componentScattering p := by
  funext component
  cases component
  · change _ = DirectionalCoupler.physicalScattering p.coupler Unit
    exact allPassRationalComponents_scattering_coupler p (fun _ => q)
  · change _ = MatchedPropagation.physicalScattering p.propagation Unit
    exact allPassRationalComponents_scattering_propagation p q hLoop

/-- With the loop coefficient matched, pointwise rational compilation is exactly the S2 flat
netlist, including its proof-carrying wiring. -/
lemma allPassRationalNetlist_compile_eq (p : AllPass.Parameters) (q : ℂ)
    (hLoop : p.loopCoefficient = (p.fieldAttenuation : ℂ) * q) :
    (allPassRationalNetlist p).compile (fun _ => q) = AllPass.netlist p := by
  have hScattering := allPassRationalComponents_scattering_eq p q hLoop
  change FlatNetlist.mk
      { Component := AllPass.Component
        portFamily := AllPass.componentPortFamily
        scattering := (allPassRationalComponents p).scattering (fun _ => q) }
      AllPass.Connection (AllPass.connections p) = AllPass.netlist p
  rw [hScattering]
  rfl

/-- The compiled model has the same assembled scattering transform as S2 when the evaluated arc
coefficient is the stored loop coefficient. -/
lemma allPassRationalNetlist_scatteringTransform_eq (p : AllPass.Parameters) (q : ℂ)
    (hLoop : p.loopCoefficient = (p.fieldAttenuation : ℂ) * q) :
    ((allPassRationalNetlist p).compile (fun _ => q)).scatteringTransform =
      (AllPass.netlist p).scatteringTransform := by
  have hScattering := allPassRationalComponents_scattering_eq p q hLoop
  unfold FlatNetlist.scatteringTransform FlatNetlist.scatteringMatrix
  dsimp only [RationalNetlist.compile, RationalNetlist.toParameterizedNetlist,
    RationalComponentFamily.toParameterizedComponentFamily, ParameterizedNetlist.compile,
    ParameterizedComponentFamily.evaluate, allPassRationalNetlist, AllPass.netlist]
  rw [hScattering]
  rfl

/-!
## B. Compiled channels and component equations
-/

/-- The fixed-frequency netlist obtained by compiling the rational all-pass model at `q`. -/
abbrev allPassCompiledNetlist (p : AllPass.Parameters) (q : ℂ) : FlatNetlist :=
  (allPassRationalNetlist p).compile (fun _ => q)

/-- A coupler-owned aggregate channel of the compiled rational model. -/
def allPassRationalCouplerChannel (p : AllPass.Parameters) (q : ℂ)
    (port : DirectionalCoupler.Port) : (allPassCompiledNetlist p q).Channel :=
  ⟨⟨AllPass.Component.coupler, port⟩, ()⟩

/-- A propagation-owned aggregate channel of the compiled rational model. -/
def allPassRationalPropagationChannel (p : AllPass.Parameters) (q : ℂ)
    (port : MatchedPropagation.Port) : (allPassCompiledNetlist p q).Channel :=
  ⟨⟨AllPass.Component.propagation, port⟩, ()⟩

/-- The compiled model's disconnected left bus input channel. -/
def allPassRationalInputChannel (p : AllPass.Parameters) (q : ℂ) :
    (allPassCompiledNetlist p q).ExternalChannel :=
  ⟨allPassRationalCouplerChannel p q DirectionalCoupler.Port.leftFirst, by
    rintro ⟨⟨connection, channel⟩, hChannel⟩
    cases connection <;> rcases channel with mode | mode <;> cases mode
    all_goals cases hChannel⟩

/-- The compiled model's disconnected right bus through channel. -/
def allPassRationalThroughChannel (p : AllPass.Parameters) (q : ℂ) :
    (allPassCompiledNetlist p q).ExternalChannel :=
  ⟨allPassRationalCouplerChannel p q DirectionalCoupler.Port.rightFirst, by
    rintro ⟨⟨connection, channel⟩, hChannel⟩
    cases connection <;> rcases channel with mode | mode <;> cases mode
    all_goals cases hChannel⟩

/-- The compiled model's left-bus single-channel input amplitude. -/
def allPassRationalInputAmplitude (p : AllPass.Parameters) (q amplitude : ℂ) :
    ModeAmplitude (allPassCompiledNetlist p q).ExternalIncident :=
  PiLp.single 2 (Incident.mk (allPassRationalInputChannel p q)) amplitude

/-- The compiled model input amplitude has the supplied input-channel value. -/
@[simp]
lemma allPassRationalInputAmplitude_apply_input (p : AllPass.Parameters) (q amplitude : ℂ) :
    allPassRationalInputAmplitude p q amplitude
        (Incident.mk (allPassRationalInputChannel p q)) = amplitude := by
  simp [allPassRationalInputAmplitude]

/-- Compiled component labels remain finite. -/
noncomputable instance allPassCompiledComponentFintype (p : AllPass.Parameters) (q : ℂ) :
    Fintype (allPassCompiledNetlist p q).components.Component := by
  change Fintype AllPass.Component
  infer_instance

/-- Every compiled local component channel family remains finite. -/
noncomputable instance allPassCompiledLocalChannelFintype (p : AllPass.Parameters) (q : ℂ)
    (component : (allPassCompiledNetlist p q).components.Component) :
    Fintype ((allPassCompiledNetlist p q).components.portFamily component).Channel := by
  change Fintype (AllPass.componentPortFamily component).Channel
  exact AllPass.localChannelFintype component

/-- Every compiled local incident endpoint family remains finite. -/
noncomputable instance allPassCompiledLocalIncidentFintype (p : AllPass.Parameters) (q : ℂ)
    (component : (allPassCompiledNetlist p q).components.Component) :
    Fintype (Incident ((allPassCompiledNetlist p q).components.portFamily component).Channel) :=
  Incident.fintypeOf (allPassCompiledLocalChannelFintype p q component)

/-- Every retained rational local channel family is finite in this model. -/
noncomputable instance allPassRationalLocalChannelFintype (p : AllPass.Parameters)
    (component : (allPassRationalComponents p).Component) :
    Fintype ((allPassRationalComponents p).portFamily component).Channel := by
  change Fintype (AllPass.componentPortFamily component).Channel
  exact AllPass.localChannelFintype component

/-- Every retained rational local incident endpoint family is finite in this model. -/
noncomputable instance allPassRationalLocalIncidentFintype (p : AllPass.Parameters)
    (component : (allPassRationalComponents p).Component) :
    Fintype (Incident ((allPassRationalComponents p).portFamily component).Channel) :=
  Incident.fintypeOf (allPassRationalLocalChannelFintype p component)

/-- A compiled global scattering equation restricts to the N7 coupler scattering graph. -/
lemma allPassRationalCoupler_scatteringGraph_of_scatteringEquation
    (p : AllPass.Parameters) (q : ℂ)
    (incident : ModeAmplitude (allPassCompiledNetlist p q).IncidentIndex)
    (outgoing : ModeAmplitude (allPassCompiledNetlist p q).OutgoingIndex)
    (hScattering : outgoing =
      (allPassCompiledNetlist p q).scatteringTransform.toLinearMap incident) :
    (incident.restrictEmbedding
          (Incident.relabelEmbedding
            ((allPassCompiledNetlist p q).components.componentChannelEmbedding
              AllPass.Component.coupler)),
      outgoing.restrictEmbedding
          (Outgoing.relabelEmbedding
            ((allPassCompiledNetlist p q).components.componentChannelEmbedding
              AllPass.Component.coupler))) ∈
        ModeTransform.toBehavior
          (DirectionalCoupler.physicalScattering p.coupler Unit).toOrientedModeTransform := by
  have hMember : (incident, outgoing) ∈ (allPassCompiledNetlist p q).componentBehavior :=
    ((allPassCompiledNetlist p q).mem_componentBehavior_iff incident outgoing).mpr hScattering
  have hLocal :=
    ((allPassCompiledNetlist p q).mem_componentBehavior_iff_forall_component
      incident outgoing).mp hMember AllPass.Component.coupler
  have hEvaluated :
      (allPassCompiledNetlist p q).components.scattering AllPass.Component.coupler =
        DirectionalCoupler.physicalScattering p.coupler Unit :=
    allPassRationalComponents_scattering_coupler p (fun _ => q)
  rw [hEvaluated] at hLocal
  exact hLocal

/-- A compiled global scattering equation restricts to the N7 propagation scattering graph when
`a*q` is the stored loop coefficient. -/
lemma allPassRationalPropagation_scatteringGraph_of_scatteringEquation
    (p : AllPass.Parameters) (q : ℂ)
    (hLoop : p.loopCoefficient = (p.fieldAttenuation : ℂ) * q)
    (incident : ModeAmplitude (allPassCompiledNetlist p q).IncidentIndex)
    (outgoing : ModeAmplitude (allPassCompiledNetlist p q).OutgoingIndex)
    (hScattering : outgoing =
      (allPassCompiledNetlist p q).scatteringTransform.toLinearMap incident) :
    (incident.restrictEmbedding
          (Incident.relabelEmbedding
            ((allPassCompiledNetlist p q).components.componentChannelEmbedding
              AllPass.Component.propagation)),
      outgoing.restrictEmbedding
          (Outgoing.relabelEmbedding
            ((allPassCompiledNetlist p q).components.componentChannelEmbedding
              AllPass.Component.propagation))) ∈
        ModeTransform.toBehavior
          (MatchedPropagation.physicalScattering p.propagation Unit).toOrientedModeTransform := by
  have hMember : (incident, outgoing) ∈ (allPassCompiledNetlist p q).componentBehavior :=
    ((allPassCompiledNetlist p q).mem_componentBehavior_iff incident outgoing).mpr hScattering
  have hLocal :=
    ((allPassCompiledNetlist p q).mem_componentBehavior_iff_forall_component
      incident outgoing).mp hMember AllPass.Component.propagation
  have hEvaluated :
      (allPassCompiledNetlist p q).components.scattering AllPass.Component.propagation =
        MatchedPropagation.physicalScattering p.propagation Unit :=
    allPassRationalComponents_scattering_propagation p q hLoop
  rw [hEvaluated] at hLocal
  exact hLocal

/-- The compiled scattering equation gives the right-bus coupler coordinate equation. -/
lemma allPassRational_scatteringEquation_coupler_rightFirst
    (p : AllPass.Parameters) (q : ℂ)
    (incident : ModeAmplitude (allPassCompiledNetlist p q).IncidentIndex)
    (outgoing : ModeAmplitude (allPassCompiledNetlist p q).OutgoingIndex)
    (hScattering : outgoing =
      (allPassCompiledNetlist p q).scatteringTransform.toLinearMap incident) :
    outgoing (Outgoing.mk
        (allPassRationalCouplerChannel p q DirectionalCoupler.Port.rightFirst)) =
      (p.throughAmplitude : ℂ) *
          incident (Incident.mk
            (allPassRationalCouplerChannel p q DirectionalCoupler.Port.leftFirst)) +
        DirectionalCoupler.crossCoefficient p.coupler *
          incident (Incident.mk
            (allPassRationalCouplerChannel p q DirectionalCoupler.Port.leftSecond)) := by
  have hGraph :=
    allPassRationalCoupler_scatteringGraph_of_scatteringEquation p q incident outgoing
      hScattering
  let localIncident :
      ModeAmplitude (Incident (DirectionalCoupler.portFamily Unit).Channel) :=
    incident.restrictEmbedding
      (Incident.relabelEmbedding
        ((allPassCompiledNetlist p q).components.componentChannelEmbedding
          AllPass.Component.coupler))
  let localOutgoing :
      ModeAmplitude (Outgoing (DirectionalCoupler.portFamily Unit).Channel) :=
    outgoing.restrictEmbedding
      (Outgoing.relabelEmbedding
        ((allPassCompiledNetlist p q).components.componentChannelEmbedding
          AllPass.Component.coupler))
  have hGraphLocal : (localIncident, localOutgoing) ∈
      (DirectionalCoupler.physicalScattering p.coupler Unit).toOrientedModeTransform.toBehavior :=
    hGraph
  have hRaw := (ModeTransform.mem_toBehavior_iff_toLinearMap _ _ _).mp hGraphLocal
  have hCoordinate := congrArg
    (fun amplitude => amplitude
      (Outgoing.mk ⟨DirectionalCoupler.Port.rightFirst, ()⟩)) hRaw
  rw [AllPass.couplerScattering_apply_rightFirst] at hCoordinate
  change
    outgoing (Outgoing.mk
        (allPassRationalCouplerChannel p q DirectionalCoupler.Port.rightFirst)) =
      (p.throughAmplitude : ℂ) *
          incident (Incident.mk
            (allPassRationalCouplerChannel p q DirectionalCoupler.Port.leftFirst)) +
        DirectionalCoupler.crossCoefficient p.coupler *
          incident (Incident.mk
            (allPassRationalCouplerChannel p q DirectionalCoupler.Port.leftSecond))
    at hCoordinate
  exact hCoordinate

/-- The compiled scattering equation gives the right-ring coupler coordinate equation. -/
lemma allPassRational_scatteringEquation_coupler_rightSecond
    (p : AllPass.Parameters) (q : ℂ)
    (incident : ModeAmplitude (allPassCompiledNetlist p q).IncidentIndex)
    (outgoing : ModeAmplitude (allPassCompiledNetlist p q).OutgoingIndex)
    (hScattering : outgoing =
      (allPassCompiledNetlist p q).scatteringTransform.toLinearMap incident) :
    outgoing (Outgoing.mk
        (allPassRationalCouplerChannel p q DirectionalCoupler.Port.rightSecond)) =
      DirectionalCoupler.crossCoefficient p.coupler *
          incident (Incident.mk
            (allPassRationalCouplerChannel p q DirectionalCoupler.Port.leftFirst)) +
        (p.throughAmplitude : ℂ) *
          incident (Incident.mk
            (allPassRationalCouplerChannel p q DirectionalCoupler.Port.leftSecond)) := by
  have hGraph :=
    allPassRationalCoupler_scatteringGraph_of_scatteringEquation p q incident outgoing
      hScattering
  let localIncident :
      ModeAmplitude (Incident (DirectionalCoupler.portFamily Unit).Channel) :=
    incident.restrictEmbedding
      (Incident.relabelEmbedding
        ((allPassCompiledNetlist p q).components.componentChannelEmbedding
          AllPass.Component.coupler))
  let localOutgoing :
      ModeAmplitude (Outgoing (DirectionalCoupler.portFamily Unit).Channel) :=
    outgoing.restrictEmbedding
      (Outgoing.relabelEmbedding
        ((allPassCompiledNetlist p q).components.componentChannelEmbedding
          AllPass.Component.coupler))
  have hGraphLocal : (localIncident, localOutgoing) ∈
      (DirectionalCoupler.physicalScattering p.coupler Unit).toOrientedModeTransform.toBehavior :=
    hGraph
  have hRaw := (ModeTransform.mem_toBehavior_iff_toLinearMap _ _ _).mp hGraphLocal
  have hCoordinate := congrArg
    (fun amplitude => amplitude
      (Outgoing.mk ⟨DirectionalCoupler.Port.rightSecond, ()⟩)) hRaw
  rw [AllPass.couplerScattering_apply_rightSecond] at hCoordinate
  change
    outgoing (Outgoing.mk
        (allPassRationalCouplerChannel p q DirectionalCoupler.Port.rightSecond)) =
      DirectionalCoupler.crossCoefficient p.coupler *
          incident (Incident.mk
            (allPassRationalCouplerChannel p q DirectionalCoupler.Port.leftFirst)) +
        (p.throughAmplitude : ℂ) *
          incident (Incident.mk
            (allPassRationalCouplerChannel p q DirectionalCoupler.Port.leftSecond))
    at hCoordinate
  exact hCoordinate

/-- The compiled scattering equation gives forward propagation around the ring. -/
lemma allPassRational_scatteringEquation_propagation_right
    (p : AllPass.Parameters) (q : ℂ)
    (hLoop : p.loopCoefficient = (p.fieldAttenuation : ℂ) * q)
    (incident : ModeAmplitude (allPassCompiledNetlist p q).IncidentIndex)
    (outgoing : ModeAmplitude (allPassCompiledNetlist p q).OutgoingIndex)
    (hScattering : outgoing =
      (allPassCompiledNetlist p q).scatteringTransform.toLinearMap incident) :
    outgoing (Outgoing.mk
        (allPassRationalPropagationChannel p q MatchedPropagation.Port.right)) =
      p.loopCoefficient *
        incident (Incident.mk
          (allPassRationalPropagationChannel p q MatchedPropagation.Port.left)) := by
  have hGraph :=
    allPassRationalPropagation_scatteringGraph_of_scatteringEquation p q hLoop incident
      outgoing hScattering
  let localIncident :
      ModeAmplitude (Incident (MatchedPropagation.portFamily Unit).Channel) :=
    incident.restrictEmbedding
      (Incident.relabelEmbedding
        ((allPassCompiledNetlist p q).components.componentChannelEmbedding
          AllPass.Component.propagation))
  let localOutgoing :
      ModeAmplitude (Outgoing (MatchedPropagation.portFamily Unit).Channel) :=
    outgoing.restrictEmbedding
      (Outgoing.relabelEmbedding
        ((allPassCompiledNetlist p q).components.componentChannelEmbedding
          AllPass.Component.propagation))
  have hGraphLocal : (localIncident, localOutgoing) ∈
      ModeTransform.toBehavior
        (MatchedPropagation.physicalScattering p.propagation Unit).toOrientedModeTransform :=
    hGraph
  have hRaw := (ModeTransform.mem_toBehavior_iff_toLinearMap _ _ _).mp hGraphLocal
  have hCoordinate := congrArg
    (fun amplitude => amplitude
      (Outgoing.mk ⟨MatchedPropagation.Port.right, ()⟩)) hRaw
  rw [AllPass.propagationScattering_apply_right] at hCoordinate
  change
    outgoing (Outgoing.mk
        (allPassRationalPropagationChannel p q MatchedPropagation.Port.right)) =
      p.loopCoefficient *
        incident (Incident.mk
          (allPassRationalPropagationChannel p q MatchedPropagation.Port.left))
    at hCoordinate
  exact hCoordinate

/-!
## C. Wiring-coordinate bridges
-/

/-- The compiled connected coordinate at the coupler right-ring endpoint. -/
def allPassRationalConnectedCouplerRightSecond (p : AllPass.Parameters) (q : ℂ) :
    (allPassCompiledNetlist p q).ConnectedChannel :=
  ⟨AllPass.Connection.rightToPropagation, Sum.inl ()⟩

/-- The compiled connected coordinate at the propagation left endpoint. -/
def allPassRationalConnectedPropagationLeft (p : AllPass.Parameters) (q : ℂ) :
    (allPassCompiledNetlist p q).ConnectedChannel :=
  ⟨AllPass.Connection.rightToPropagation, Sum.inr ()⟩

/-- The compiled connected coordinate at the propagation right endpoint. -/
def allPassRationalConnectedPropagationRight (p : AllPass.Parameters) (q : ℂ) :
    (allPassCompiledNetlist p q).ConnectedChannel :=
  ⟨AllPass.Connection.propagationToLeft, Sum.inl ()⟩

/-- The compiled connected coordinate at the coupler left-ring endpoint. -/
def allPassRationalConnectedCouplerLeftSecond (p : AllPass.Parameters) (q : ℂ) :
    (allPassCompiledNetlist p q).ConnectedChannel :=
  ⟨AllPass.Connection.propagationToLeft, Sum.inr ()⟩

/-- The compiled right-ring coupler coordinate embeds in its aggregate channel. -/
@[simp]
lemma allPassRationalConnectedCouplerRightSecond_embedding (p : AllPass.Parameters) (q : ℂ) :
    (allPassCompiledNetlist p q).connections.channelEmbedding
        (allPassRationalConnectedCouplerRightSecond p q) =
      allPassRationalCouplerChannel p q DirectionalCoupler.Port.rightSecond := rfl

/-- The compiled propagation-left coordinate embeds in its aggregate channel. -/
@[simp]
lemma allPassRationalConnectedPropagationLeft_embedding (p : AllPass.Parameters) (q : ℂ) :
    (allPassCompiledNetlist p q).connections.channelEmbedding
        (allPassRationalConnectedPropagationLeft p q) =
      allPassRationalPropagationChannel p q MatchedPropagation.Port.left := rfl

/-- The compiled propagation-right coordinate embeds in its aggregate channel. -/
@[simp]
lemma allPassRationalConnectedPropagationRight_embedding (p : AllPass.Parameters) (q : ℂ) :
    (allPassCompiledNetlist p q).connections.channelEmbedding
        (allPassRationalConnectedPropagationRight p q) =
      allPassRationalPropagationChannel p q MatchedPropagation.Port.right := rfl

/-- The compiled left-ring coupler coordinate embeds in its aggregate channel. -/
@[simp]
lemma allPassRationalConnectedCouplerLeftSecond_embedding (p : AllPass.Parameters) (q : ℂ) :
    (allPassCompiledNetlist p q).connections.channelEmbedding
        (allPassRationalConnectedCouplerLeftSecond p q) =
      allPassRationalCouplerChannel p q DirectionalCoupler.Port.leftSecond := rfl

/-- The compiled right-ring coupler endpoint is mated to propagation left. -/
lemma allPassRationalConnectedCouplerRightSecond_mate (p : AllPass.Parameters) (q : ℂ) :
    (allPassCompiledNetlist p q).connections.mateEquiv
        (allPassRationalConnectedCouplerRightSecond p q) =
      allPassRationalConnectedPropagationLeft p q := rfl

/-- The compiled propagation-left endpoint is mated to the right-ring coupler endpoint. -/
lemma allPassRationalConnectedPropagationLeft_mate (p : AllPass.Parameters) (q : ℂ) :
    (allPassCompiledNetlist p q).connections.mateEquiv
        (allPassRationalConnectedPropagationLeft p q) =
      allPassRationalConnectedCouplerRightSecond p q := rfl

/-- The compiled propagation-right endpoint is mated to the left-ring coupler endpoint. -/
lemma allPassRationalConnectedPropagationRight_mate (p : AllPass.Parameters) (q : ℂ) :
    (allPassCompiledNetlist p q).connections.mateEquiv
        (allPassRationalConnectedPropagationRight p q) =
      allPassRationalConnectedCouplerLeftSecond p q := rfl

/-- The compiled left-ring coupler endpoint is mated to propagation right. -/
lemma allPassRationalConnectedCouplerLeftSecond_mate (p : AllPass.Parameters) (q : ℂ) :
    (allPassCompiledNetlist p q).connections.mateEquiv
        (allPassRationalConnectedCouplerLeftSecond p q) =
      allPassRationalConnectedPropagationRight p q := rfl

/-- Compiled incident assembly exposes the declared left-bus input coordinate. -/
lemma allPassRational_incidentAssembly_apply_leftFirst (p : AllPass.Parameters) (q : ℂ)
    (outgoing : ModeAmplitude (allPassCompiledNetlist p q).OutgoingIndex)
    (external : ModeAmplitude (allPassCompiledNetlist p q).ExternalIncident) :
    (allPassCompiledNetlist p q).connections.incidentAssembly outgoing external
        (Incident.mk
          (allPassRationalCouplerChannel p q DirectionalCoupler.Port.leftFirst)) =
      external (Incident.mk (allPassRationalInputChannel p q)) := by
  exact (allPassCompiledNetlist p q).connections.incidentAssembly_apply_external
    outgoing external (allPassRationalInputChannel p q)

/-- The compiled coupler left-ring input is routed from propagation right. -/
lemma allPassRational_incidentAssembly_apply_coupler_leftSecond
    (p : AllPass.Parameters) (q : ℂ)
    (outgoing : ModeAmplitude (allPassCompiledNetlist p q).OutgoingIndex)
    (external : ModeAmplitude (allPassCompiledNetlist p q).ExternalIncident) :
    (allPassCompiledNetlist p q).connections.incidentAssembly outgoing external
        (Incident.mk
          (allPassRationalCouplerChannel p q DirectionalCoupler.Port.leftSecond)) =
      outgoing (Outgoing.mk
        (allPassRationalPropagationChannel p q MatchedPropagation.Port.right)) := by
  rw [← allPassRationalConnectedCouplerLeftSecond_embedding,
    (allPassCompiledNetlist p q).connections.incidentAssembly_apply_connected_channel,
    allPassRationalConnectedCouplerLeftSecond_mate,
    allPassRationalConnectedPropagationRight_embedding]

/-- The compiled propagation-left input is routed from the coupler right-ring output. -/
lemma allPassRational_incidentAssembly_apply_propagation_left
    (p : AllPass.Parameters) (q : ℂ)
    (outgoing : ModeAmplitude (allPassCompiledNetlist p q).OutgoingIndex)
    (external : ModeAmplitude (allPassCompiledNetlist p q).ExternalIncident) :
    (allPassCompiledNetlist p q).connections.incidentAssembly outgoing external
        (Incident.mk
          (allPassRationalPropagationChannel p q MatchedPropagation.Port.left)) =
      outgoing (Outgoing.mk
        (allPassRationalCouplerChannel p q DirectionalCoupler.Port.rightSecond)) := by
  rw [← allPassRationalConnectedPropagationLeft_embedding,
    (allPassCompiledNetlist p q).connections.incidentAssembly_apply_connected_channel,
    allPassRationalConnectedPropagationLeft_mate,
    allPassRationalConnectedCouplerRightSecond_embedding]

/-- The compiled output readout exposes the declared right-bus through coordinate. -/
lemma allPassRational_outputReadout_apply_through (p : AllPass.Parameters) (q : ℂ)
    (outgoing : ModeAmplitude (allPassCompiledNetlist p q).OutgoingIndex) :
    (allPassCompiledNetlist p q).outputReadout.toLinearMap outgoing
        (Outgoing.mk (allPassRationalThroughChannel p q)) =
      outgoing (Outgoing.mk
        (allPassRationalCouplerChannel p q DirectionalCoupler.Port.rightFirst)) := by
  rw [FlatNetlist.outputReadout,
    (allPassCompiledNetlist p q).connections.externalOutgoingReadout_apply,
    ModeAmplitude.restrictEmbedding_apply]
  rfl

/-!
## D. Solve domain and proof-gated response
-/

/-- A homogeneous fixed point of the compiled rational model vanishes at a nonzero S2
feedback denominator. -/
lemma allPassRationalNetlist_feedbackFixedPoint_eq_zero (p : AllPass.Parameters) (q : ℂ)
    (hLoop : p.loopCoefficient = (p.fieldAttenuation : ℂ) * q)
    (hDenominator : p.HasNonzeroDenominator)
    (incident : ModeAmplitude ((allPassRationalNetlist p).compile (fun _ => q)).IncidentIndex)
    (outgoing : ModeAmplitude ((allPassRationalNetlist p).compile (fun _ => q)).OutgoingIndex)
    (hScattering : outgoing =
      ((allPassRationalNetlist p).compile (fun _ => q)).scatteringTransform.toLinearMap incident)
    (hAssembly : incident =
      ((allPassRationalNetlist p).compile (fun _ => q)).connections.incidentAssembly
        outgoing 0) :
    incident = 0 := by
  have hScattering' : outgoing =
      (AllPass.netlist p).scatteringTransform.toLinearMap incident := by
    rw [← allPassRationalNetlist_scatteringTransform_eq p q hLoop]
    exact hScattering
  have hAssembly' : incident =
      (AllPass.netlist p).connections.incidentAssembly outgoing 0 := hAssembly
  exact AllPass.feedback_fixedPoint_eq_zero p hDenominator incident outgoing
    hScattering' hAssembly'

/-- A nonzero S2 feedback denominator makes the independently compiled rational model well
posed. -/
lemma allPassRationalNetlist_isWellPosed (p : AllPass.Parameters) (q : ℂ)
    (hLoop : p.loopCoefficient = (p.fieldAttenuation : ℂ) * q)
    (hDenominator : p.HasNonzeroDenominator) :
    ((allPassRationalNetlist p).compile (fun _ => q)).IsWellPosed := by
  let compiled := (allPassRationalNetlist p).compile (fun _ => q)
  rw [compiled.isWellPosed_iff_feedbackOperator_injective]
  intro first second hFeedback
  let difference := first - second
  have hKernel : compiled.feedbackOperator.toLinearMap difference = 0 := by
    simp [difference, hFeedback]
  let outgoing := compiled.scatteringTransform.toLinearMap difference
  have hAssembly : difference = compiled.connections.incidentAssembly outgoing 0 := by
    rw [PortConnectionFamily.incidentAssembly, map_zero, add_zero]
    rw [compiled.feedbackOperator_apply] at hKernel
    exact sub_eq_zero.mp hKernel
  have hDifference := allPassRationalNetlist_feedbackFixedPoint_eq_zero p q hLoop
    hDenominator difference outgoing rfl hAssembly
  exact sub_eq_zero.mp hDifference

/-- Valid S2 parameters make every retained rational component entry valid at every formal delay
value; all retained entry denominators are one. -/
lemma allPassRationalComponents_isValidAt (p : AllPass.Parameters) (hp : p.IsValid)
    (value : DelayTuple 1) (component : AllPass.Component) :
    (allPassRationalComponents p).toParameterizedComponentFamily.IsValidAt component value := by
  constructor
  · exact hp
  · intro output input
    cases component
    · simp [allPassRationalComponents, RationalModel.evaluationDomain,
        RationalModel.constant, RationalModel.ofPolynomial]
    · rcases output with ⟨outputPort, outputMode⟩
      rcases input with ⟨inputPort, inputMode⟩
      cases outputPort <;> cases inputPort <;> cases outputMode <;> cases inputMode <;>
        simp [allPassRationalComponents, allPassPropagationEntryModel,
          RationalModel.evaluationDomain, RationalModel.constant, RationalModel.ofPolynomial]

/-- The matched formal-delay point belongs to the proof-gated response domain for valid S2
parameters with a nonzero feedback denominator. -/
lemma allPassRationalNetlist_mem_responseDomain (p : AllPass.Parameters) (q : ℂ)
    (hLoop : p.loopCoefficient = (p.fieldAttenuation : ℂ) * q) (hp : p.IsValid)
    (hDenominator : p.HasNonzeroDenominator) :
    (fun _ : Fin 1 => q) ∈
      (allPassRationalNetlist p).toParameterizedNetlist.responseDomain := by
  change
    (fun _ : Fin 1 => q) ∈
        (allPassRationalNetlist p).toParameterizedNetlist.solveDomain ∧
      (fun _ : Fin 1 => q) ∈
        (allPassRationalNetlist p).toParameterizedNetlist.components.validityDomain
  constructor
  · change ((allPassRationalNetlist p).compile (fun _ => q)).IsWellPosed
    exact allPassRationalNetlist_isWellPosed p q hLoop hDenominator
  · intro component
    exact allPassRationalComponents_isValidAt p hp (fun _ => q) component

/-- The compiled rational model sends the named input amplitude to the S2 through transfer.
The proof expands the compiled netlist's three channel equations and the scalar loop solve. -/
lemma allPassRationalNetlist_responseThrough (p : AllPass.Parameters) (q : ℂ)
    (hLoop : p.loopCoefficient = (p.fieldAttenuation : ℂ) * q)
    (hDomain : (fun _ : Fin 1 => q) ∈
      (allPassRationalNetlist p).toParameterizedNetlist.responseDomain)
    (hDenominator : p.HasNonzeroDenominator) (amplitude : ℂ) :
    (((allPassRationalNetlist p).compile (fun _ => q)).responseTransform hDomain.1).toLinearMap
        (allPassRationalInputAmplitude p q amplitude)
        (Outgoing.mk (allPassRationalThroughChannel p q)) =
      AllPass.throughTransfer p * amplitude := by
  let compiled := allPassCompiledNetlist p q
  let input := allPassRationalInputAmplitude p q amplitude
  let output := (compiled.responseTransform hDomain.1).toLinearMap input
  have hMember : (input, output) ∈ compiled.behavior := by
    rw [← compiled.toBehavior_responseTransform hDomain.1,
      ModeTransform.mem_toBehavior_iff_toLinearMap]
  rcases (compiled.mem_behavior_iff_equations _ _).mp hMember with
    ⟨incident, outgoing, hScattering, hAssembly, hOutput⟩
  have hAssemblyCompiled : incident =
      compiled.connections.incidentAssembly outgoing input := by
    simpa only [PortConnectionFamily.incidentAssembly] using hAssembly
  have hInput := congrArg
    (fun state => state (Incident.mk
      (allPassRationalCouplerChannel p q DirectionalCoupler.Port.leftFirst)))
      hAssemblyCompiled
  rw [allPassRational_incidentAssembly_apply_leftFirst,
    allPassRationalInputAmplitude_apply_input] at hInput
  have hCouplerLeft := congrArg
    (fun state => state (Incident.mk
      (allPassRationalCouplerChannel p q DirectionalCoupler.Port.leftSecond)))
      hAssemblyCompiled
  rw [allPassRational_incidentAssembly_apply_coupler_leftSecond,
    allPassRational_scatteringEquation_propagation_right p q hLoop incident outgoing
      hScattering] at hCouplerLeft
  have hPropagationLeft := congrArg
    (fun state => state (Incident.mk
      (allPassRationalPropagationChannel p q MatchedPropagation.Port.left)))
      hAssemblyCompiled
  rw [allPassRational_incidentAssembly_apply_propagation_left,
    allPassRational_scatteringEquation_coupler_rightSecond p q incident outgoing hScattering,
    hInput] at hPropagationLeft
  have hLoopEquation : p.denominator *
      incident (Incident.mk
        (allPassRationalCouplerChannel p q DirectionalCoupler.Port.leftSecond)) =
        p.loopCoefficient * DirectionalCoupler.crossCoefficient p.coupler * amplitude := by
    rw [AllPass.Parameters.denominator, AllPass.Parameters.loopGain]
    linear_combination hCouplerLeft + p.loopCoefficient * hPropagationLeft
  have hLoopSolution :
      incident (Incident.mk
        (allPassRationalCouplerChannel p q DirectionalCoupler.Port.leftSecond)) =
        p.loopCoefficient * DirectionalCoupler.crossCoefficient p.coupler * amplitude /
          p.denominator := by
    apply (eq_div_iff hDenominator).2
    rw [mul_comm, hLoopEquation]
  have hThrough := allPassRational_scatteringEquation_coupler_rightFirst p q
    incident outgoing hScattering
  rw [hInput] at hThrough
  have hReadout := congrArg
    (fun state => state (Outgoing.mk (allPassRationalThroughChannel p q))) hOutput
  rw [allPassRational_outputReadout_apply_through] at hReadout
  change
    (compiled.responseTransform hDomain.1).toLinearMap
        (allPassRationalInputAmplitude p q amplitude)
        (Outgoing.mk (allPassRationalThroughChannel p q)) =
      AllPass.throughTransfer p * amplitude
  change output (Outgoing.mk (allPassRationalThroughChannel p q)) =
    AllPass.throughTransfer p * amplitude
  rw [hReadout, hThrough, hLoopSolution, AllPass.throughTransfer]
  ring

/-- The proof-gated rational-netlist response entry agrees with the S2 through transfer, without
using the general compile/response commutation theorem. -/
lemma allPassRationalNetlist_response_entry (p : AllPass.Parameters) (q : ℂ)
    (hLoop : p.loopCoefficient = (p.fieldAttenuation : ℂ) * q) (hp : p.IsValid)
    (hDenominator : p.HasNonzeroDenominator) :
    (allPassRationalNetlist p).toParameterizedNetlist.response
        (allPassRationalNetlist_mem_responseDomain p q hLoop hp hDenominator)
        (Outgoing.mk (allPassRationalThroughChannel p q))
        (Incident.mk (allPassRationalInputChannel p q)) =
      AllPass.throughTransfer p := by
  unfold ParameterizedNetlist.response
  change ((allPassRationalNetlist p).compile (fun _ => q)).responseTransform _ _ _ = _
  have hResponse := allPassRationalNetlist_responseThrough p q hLoop
    (allPassRationalNetlist_mem_responseDomain p q hLoop hp hDenominator)
    hDenominator 1
  simp [allPassRationalInputAmplitude, ModeTransform.toLinearMap,
    Matrix.toLpLin_apply] at hResponse
  convert hResponse using 1
  all_goals rfl

/-- The proof-gated compiled response obeys the denominator-cleared all-pass equation.

The selected response is first obtained from the compiled component and wiring equations by
`allPassRationalNetlist_response_entry`; the unitary-coupler law then reduces its numerator to
`t - a*q`. Thus this is a semantic consequence of the rational netlist, not a definition of a
second closed-form response.
-/
lemma allPassRationalNetlist_response_cleared (p : AllPass.Parameters) (q : ℂ)
    (hLoop : p.loopCoefficient = (p.fieldAttenuation : ℂ) * q) (hp : p.IsValid)
    (hUnitary : p.coupler.IsUnitary) (hDenominator : p.HasNonzeroDenominator) :
    (1 - (p.throughAmplitude : ℂ) * (p.fieldAttenuation : ℂ) * q) *
        (allPassRationalNetlist p).toParameterizedNetlist.response
          (allPassRationalNetlist_mem_responseDomain p q hLoop hp hDenominator)
          (Outgoing.mk (allPassRationalThroughChannel p q))
          (Incident.mk (allPassRationalInputChannel p q)) =
      (p.throughAmplitude : ℂ) - (p.fieldAttenuation : ℂ) * q := by
  rw [allPassRationalNetlist_response_entry p q hLoop hp hDenominator,
    AllPass.throughTransfer_eq_standard p hUnitary hDenominator,
    AllPass.standardThroughTransfer]
  have hFactor :
      1 - (p.throughAmplitude : ℂ) * (p.fieldAttenuation : ℂ) * q =
        p.denominator := by
    rw [AllPass.Parameters.denominator, AllPass.Parameters.loopGain, hLoop]
    ring
  rw [hFactor, mul_comm, div_mul_cancel₀ _ hDenominator, hLoop]

end

end Optics.DelayTransfer
