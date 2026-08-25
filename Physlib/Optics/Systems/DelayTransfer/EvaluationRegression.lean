/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Systems.DelayTransfer.Evaluation
public import Physlib.Optics.Systems.Microring.AllPassRegression

/-!
# One-delay all-pass evaluation regressions

## i. Overview

The retained rational model `allPassDelayModel t a` is
`(t - a*q) / (1 - t*a*q)`. Its formal variable is the single propagation phase factor; the field
attenuation `a` remains a coefficient. On the denominator's nonzero domain, the generic bridge
agrees with `AllPass.throughTransfer` when the N7 coupler is unitary and its loop coefficient is
`a*q`.

The exact S2 fixtures are expanded independently at `q = 1` and `q = -1`. They give `1 / 7` and
`11 / 13`, respectively, before those values are compared with the named S2 transfer results.
The non-real point `q = -I` gives `75 / 109 + (32 / 109) I`; separate equalities obtain this
formal value from both `laplaceEvaluation` at `s = I*pi/2`, `τ = 1`, and
`zInverseEvaluation` at `z = I`.

`allPassRationalNetlist` independently lifts the constant N7 coupler entries and the formal
propagation entries `a*q`, then reuses the exact S2 connection family. Its compile equality is
proved entry by entry. The proof-gated response anchor therefore exercises rational evaluation,
pointwise compilation, S2 wiring, and N5 elimination without invoking the general commutation
theorem.

## ii. Key definitions and results

- `allPassDelayModel`: the retained one-delay rational presentation.
- `allPassDelayModel_eq_throughTransfer`: agreement with the S2 all-pass response.
- `allPassDelayModel_resonance_value`: direct evaluation at the zero-phase fixture.
- `allPassDelayModel_antiresonance_value`: direct evaluation at the half-turn fixture.
- `allPassDelayModel_resonance_agrees`: agreement with the S2 zero-phase transfer.
- `allPassDelayModel_antiresonance_agrees`: agreement with the S2 half-turn transfer.
- `allPassRationalNetlist`: the actual rational-component S2 network fixture.
- `allPassRationalNetlist_compile_eq`: entrywise evaluation and compilation recover S2.
- `allPassRationalNetlist_response_entry`: its independently anchored proof-gated response.
- `allPassRationalNetlist_resonance_response_entry`: compiled zero-phase response `1/7`.
- `allPassRationalNetlist_antiresonance_response_entry`: compiled half-turn response `11/13`.
- `allPassRationalNetlist_quadrature_response_entry`: compiled non-real response.
- `laplaceEvaluation_quadrature`, `zInverseEvaluation_quadrature`: both conventions give `-I`.

## iii. Table of contents

- A. The retained rational all-pass response
- B. Exact S2 phase-point regressions
- C. Compiled rational-netlist regression
- D. Non-real convention anchor

## iv. References and non-claims

The all-pass transfer, loop coefficient, and solve gate are defined in
`Physlib/Optics/Systems/Microring/AllPass.lean:114-188`. The two exact phase fixtures and transfer
values are defined and proved in
`Physlib/Optics/Systems/Microring/AllPassRegression.lean:62-99,219-247`.
The compiled fixture reuses `AllPass.componentPortFamily`, `AllPass.Connection`, and
`AllPass.connections` from `Physlib/Optics/Systems/Microring/AllPass.lean:211-300`.

Here `q` is a formal propagation factor. The declarations make no rational-in-frequency,
dispersion, group-delay, global-phase, stability, or physical-resonance claim. They do not perform
symbolic external-response elimination in the fraction field.
-/

@[expose] public section

namespace Optics.DelayTransfer

noncomputable section

/-!

## A. The retained rational all-pass response

-/

/-- The one-delay all-pass presentation `(t - a*q) / (1 - t*a*q)`. -/
def allPassDelayModel (t a : ℂ) : RationalModel 1 where
  numerator := MvPolynomial.C t - MvPolynomial.C a * MvPolynomial.X 0
  denominator := 1 - MvPolynomial.C (t * a) * MvPolynomial.X 0
  denominator_ne_zero := by
    intro hZero
    have hEval := congrArg (MvPolynomial.eval fun _ : Fin 1 => (0 : ℂ)) hZero
    simp at hEval

/-- Evaluation expands to `(t - a*q) / (1 - t*a*q)`. -/
lemma allPassDelayModel_eval (t a q : ℂ) :
    (allPassDelayModel t a).eval (fun _ => q) =
      (t - a * q) / (1 - t * a * q) := by
  simp [allPassDelayModel, RationalModel.eval, mul_assoc]

/-- The retained all-pass denominator is regular exactly when `1 - t*a*q` is nonzero. -/
lemma mem_allPassDelayModel_evaluationDomain_iff (t a q : ℂ) :
    (fun _ : Fin 1 => q) ∈ (allPassDelayModel t a).evaluationDomain ↔
      1 - t * a * q ≠ 0 := by
  simp [allPassDelayModel, RationalModel.evaluationDomain, mul_assoc]

/-- On the solve domain, the formal all-pass response agrees with the N7/N5F all-pass transfer. -/
lemma allPassDelayModel_eq_throughTransfer (p : AllPass.Parameters) (q : ℂ)
    (hUnitary : p.coupler.IsUnitary) (hDenominator : p.HasNonzeroDenominator)
    (hLoop : p.loopCoefficient = (p.fieldAttenuation : ℂ) * q) :
    (allPassDelayModel (p.throughAmplitude : ℂ) (p.fieldAttenuation : ℂ)).eval
        (fun _ => q) = AllPass.throughTransfer p := by
  rw [AllPass.throughTransfer_eq_standard p hUnitary hDenominator]
  simp [allPassDelayModel_eval, AllPass.standardThroughTransfer,
    AllPass.Parameters.denominator, AllPass.Parameters.loopGain, hLoop, mul_assoc]

/-!

## B. Exact S2 phase-point regressions

-/

/-- Direct rational evaluation at the S2 zero-phase point gives `1 / 7`. -/
lemma allPassDelayModel_resonance_value :
    (allPassDelayModel (3 / 5) (1 / 2)).eval (fun _ : Fin 1 => 1) = 1 / 7 := by
  norm_num [allPassDelayModel, RationalModel.eval]

/-- The formal-delay and S2 all-pass transfers agree at the zero-phase point. -/
lemma allPassDelayModel_resonance_agrees :
    (allPassDelayModel (3 / 5) (1 / 2)).eval (fun _ : Fin 1 => 1) =
      AllPass.throughTransfer AllPass.allPassRegressionResonanceParameters := by
  rw [allPassDelayModel_resonance_value,
    AllPass.allPassRegression_resonance_throughTransfer]

/-- Direct rational evaluation at the S2 half-turn point gives `11 / 13`. -/
lemma allPassDelayModel_antiresonance_value :
    (allPassDelayModel (3 / 5) (1 / 2)).eval (fun _ : Fin 1 => -1) = 11 / 13 := by
  norm_num [allPassDelayModel, RationalModel.eval]

/-- The formal-delay and S2 all-pass transfers agree at the half-turn point. -/
lemma allPassDelayModel_antiresonance_agrees :
    (allPassDelayModel (3 / 5) (1 / 2)).eval (fun _ : Fin 1 => -1) =
      AllPass.throughTransfer AllPass.allPassRegressionAntiresonanceParameters := by
  rw [allPassDelayModel_antiresonance_value,
    AllPass.allPassRegression_antiresonance_throughTransfer]

/-!

## C. Compiled rational-netlist regression

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

/-- The rational all-pass fixture retains the finite aggregate S2 channels. -/
local instance allPassRationalChannelFintype (p : AllPass.Parameters) :
    Fintype (allPassRationalNetlist p).Channel :=
  AllPass.channelFintype p

/-- The rational all-pass fixture retains the finite connected S2 channels. -/
local instance allPassRationalConnectedChannelFintype (p : AllPass.Parameters) :
    Fintype (allPassRationalNetlist p).ConnectedChannel :=
  AllPass.connectedChannelFintype p

/-- Pointwise compilation retains the finite aggregate all-pass channels. -/
local instance allPassRationalCompileChannelFintype (p : AllPass.Parameters)
    (value : DelayTuple 1) : Fintype ((allPassRationalNetlist p).compile value).Channel :=
  ParameterizedNetlist.compileChannelFintype
    (allPassRationalNetlist p).toParameterizedNetlist value

/-- Pointwise compilation retains the finite connected all-pass channels. -/
local instance allPassRationalCompileConnectedChannelFintype (p : AllPass.Parameters)
    (value : DelayTuple 1) :
    Fintype ((allPassRationalNetlist p).compile value).ConnectedChannel :=
  ParameterizedNetlist.compileConnectedChannelFintype
    (allPassRationalNetlist p).toParameterizedNetlist value

/-- Pointwise compiled all-pass channels have classical decidable equality. -/
local instance allPassRationalCompileChannelDecidableEq (p : AllPass.Parameters)
    (value : DelayTuple 1) : DecidableEq ((allPassRationalNetlist p).compile value).Channel :=
  Classical.decEq _

/-- Pointwise compiled connected all-pass channels have classical decidable equality. -/
local instance allPassRationalCompileConnectedChannelDecidableEq (p : AllPass.Parameters)
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
  change
    ({ components :=
        { Component := AllPass.Component
          portFamily := AllPass.componentPortFamily
          scattering := (allPassRationalComponents p).scattering (fun _ => q) }
      Connection := AllPass.Connection
      connections := AllPass.connections p } : FlatNetlist) = AllPass.netlist p
  rw [hScattering]
  rfl

/-- The compiled fixture has the same assembled scattering transform as S2 when the evaluated arc
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

/-- The fixed-frequency netlist obtained by compiling the rational all-pass fixture at `q`. -/
abbrev allPassCompiledNetlist (p : AllPass.Parameters) (q : ℂ) : FlatNetlist :=
  (allPassRationalNetlist p).compile (fun _ => q)

/-- A coupler-owned aggregate channel of the compiled rational fixture. -/
def allPassRationalCouplerChannel (p : AllPass.Parameters) (q : ℂ)
    (port : DirectionalCoupler.Port) : (allPassCompiledNetlist p q).Channel :=
  ⟨⟨AllPass.Component.coupler, port⟩, ()⟩

/-- A propagation-owned aggregate channel of the compiled rational fixture. -/
def allPassRationalPropagationChannel (p : AllPass.Parameters) (q : ℂ)
    (port : MatchedPropagation.Port) : (allPassCompiledNetlist p q).Channel :=
  ⟨⟨AllPass.Component.propagation, port⟩, ()⟩

/-- The compiled fixture's disconnected left bus input channel. -/
def allPassRationalInputChannel (p : AllPass.Parameters) (q : ℂ) :
    (allPassCompiledNetlist p q).ExternalChannel :=
  ⟨allPassRationalCouplerChannel p q DirectionalCoupler.Port.leftFirst, by
    rintro ⟨⟨connection, channel⟩, hChannel⟩
    cases connection <;> rcases channel with mode | mode <;> cases mode
    all_goals cases hChannel⟩

/-- The compiled fixture's disconnected right bus through channel. -/
def allPassRationalThroughChannel (p : AllPass.Parameters) (q : ℂ) :
    (allPassCompiledNetlist p q).ExternalChannel :=
  ⟨allPassRationalCouplerChannel p q DirectionalCoupler.Port.rightFirst, by
    rintro ⟨⟨connection, channel⟩, hChannel⟩
    cases connection <;> rcases channel with mode | mode <;> cases mode
    all_goals cases hChannel⟩

/-- The compiled fixture's left-bus single-channel input amplitude. -/
def allPassRationalInputAmplitude (p : AllPass.Parameters) (q amplitude : ℂ) :
    ModeAmplitude (allPassCompiledNetlist p q).ExternalIncident :=
  PiLp.single 2 (Incident.mk (allPassRationalInputChannel p q)) amplitude

/-- The compiled fixture input amplitude has the supplied input-channel value. -/
@[simp]
lemma allPassRationalInputAmplitude_apply_input (p : AllPass.Parameters) (q amplitude : ℂ) :
    allPassRationalInputAmplitude p q amplitude
        (Incident.mk (allPassRationalInputChannel p q)) = amplitude := by
  simp [allPassRationalInputAmplitude]

/-- Compiled component labels remain finite. -/
local instance allPassCompiledComponentFintype (p : AllPass.Parameters) (q : ℂ) :
    Fintype (allPassCompiledNetlist p q).components.Component := by
  change Fintype AllPass.Component
  infer_instance

/-- Every compiled local component channel family remains finite. -/
local instance allPassCompiledLocalChannelFintype (p : AllPass.Parameters) (q : ℂ)
    (component : (allPassCompiledNetlist p q).components.Component) :
    Fintype ((allPassCompiledNetlist p q).components.portFamily component).Channel := by
  change Fintype (AllPass.componentPortFamily component).Channel
  exact AllPass.localChannelFintype component

/-- Every compiled local incident endpoint family remains finite. -/
local instance allPassCompiledLocalIncidentFintype (p : AllPass.Parameters) (q : ℂ)
    (component : (allPassCompiledNetlist p q).components.Component) :
    Fintype (Incident ((allPassCompiledNetlist p q).components.portFamily component).Channel) :=
  Incident.fintypeOf (allPassCompiledLocalChannelFintype p q component)

/-- Every retained rational local channel family is finite in this fixture. -/
local instance allPassRationalLocalChannelFintype (p : AllPass.Parameters)
    (component : (allPassRationalComponents p).Component) :
    Fintype ((allPassRationalComponents p).portFamily component).Channel := by
  change Fintype (AllPass.componentPortFamily component).Channel
  exact AllPass.localChannelFintype component

/-- Every retained rational local incident endpoint family is finite in this fixture. -/
local instance allPassRationalLocalIncidentFintype (p : AllPass.Parameters)
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

/-- A homogeneous fixed point of the compiled rational fixture vanishes at a nonzero S2
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

/-- A nonzero S2 feedback denominator makes the independently compiled rational fixture well
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

/-- The compiled rational fixture sends the named input amplitude to the S2 through transfer.
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

/-!

## D. Non-real convention anchor

-/

/-- At the named zero-phase S2 point, the stored loop coefficient is `a*1`. -/
lemma allPassRational_resonance_loopCoefficient :
    AllPass.allPassRegressionResonanceParameters.loopCoefficient =
      (AllPass.allPassRegressionResonanceParameters.fieldAttenuation : ℂ) * 1 := by
  rw [AllPass.allPassRegression_resonance_loopCoefficient]
  norm_num [AllPass.allPassRegressionResonanceParameters]

/-- The named zero-phase S2 point has a nonzero feedback denominator. -/
lemma allPassRational_resonance_hasNonzeroDenominator :
    AllPass.allPassRegressionResonanceParameters.HasNonzeroDenominator := by
  rw [AllPass.Parameters.HasNonzeroDenominator,
    AllPass.allPassRegression_resonance_denominator]
  norm_num

/-- The named zero-phase S2 point belongs to the compiled rational response domain. -/
lemma allPassRationalResonanceDomain :
    (fun _ : Fin 1 => (1 : ℂ)) ∈
      (allPassRationalNetlist
        AllPass.allPassRegressionResonanceParameters).toParameterizedNetlist.responseDomain :=
  allPassRationalNetlist_mem_responseDomain
    AllPass.allPassRegressionResonanceParameters 1
    allPassRational_resonance_loopCoefficient
    AllPass.allPassRegression_resonance_isValid
    allPassRational_resonance_hasNonzeroDenominator

/-- The compiled rational fixture recovers the named S2 zero-phase response `1/7`. -/
lemma allPassRationalNetlist_resonance_response_entry :
    (allPassRationalNetlist
      AllPass.allPassRegressionResonanceParameters).toParameterizedNetlist.response
        allPassRationalResonanceDomain
        (Outgoing.mk (allPassRationalThroughChannel
          AllPass.allPassRegressionResonanceParameters 1))
        (Incident.mk (allPassRationalInputChannel
          AllPass.allPassRegressionResonanceParameters 1)) = 1 / 7 := by
  have hResponse := allPassRationalNetlist_response_entry
    AllPass.allPassRegressionResonanceParameters 1
    allPassRational_resonance_loopCoefficient
    AllPass.allPassRegression_resonance_isValid
    allPassRational_resonance_hasNonzeroDenominator
  rw [AllPass.allPassRegression_resonance_throughTransfer] at hResponse
  simpa [allPassRationalResonanceDomain] using hResponse

/-- The named half-turn S2 point satisfies the component-validity predicates. -/
lemma allPassRational_antiresonance_isValid :
    AllPass.allPassRegressionAntiresonanceParameters.IsValid := by
  constructor
  · constructor
    · norm_num [AllPass.allPassRegressionAntiresonanceParameters,
        DirectionalCoupler.Parameters.IsValid]
    · constructor
      · norm_num [AllPass.allPassRegressionAntiresonanceParameters,
          DirectionalCoupler.Parameters.IsValid]
      · norm_num [AllPass.allPassRegressionAntiresonanceParameters,
          DirectionalCoupler.Parameters.IsUnitary,
          DirectionalCoupler.Parameters.powerFactor]
  · norm_num [AllPass.allPassRegressionAntiresonanceParameters,
      MatchedPropagation.Parameters.IsValid]

/-- At the named half-turn S2 point, the stored loop coefficient is `a*(-1)`. -/
lemma allPassRational_antiresonance_loopCoefficient :
    AllPass.allPassRegressionAntiresonanceParameters.loopCoefficient =
      (AllPass.allPassRegressionAntiresonanceParameters.fieldAttenuation : ℂ) * (-1) := by
  rw [AllPass.allPassRegression_antiresonance_loopCoefficient]
  norm_num [AllPass.allPassRegressionAntiresonanceParameters]

/-- The named half-turn S2 point has a nonzero feedback denominator. -/
lemma allPassRational_antiresonance_hasNonzeroDenominator :
    AllPass.allPassRegressionAntiresonanceParameters.HasNonzeroDenominator := by
  rw [AllPass.Parameters.HasNonzeroDenominator,
    AllPass.allPassRegression_antiresonance_denominator]
  norm_num

/-- The named half-turn S2 point belongs to the compiled rational response domain. -/
lemma allPassRationalAntiresonanceDomain :
    (fun _ : Fin 1 => (-1 : ℂ)) ∈
      (allPassRationalNetlist
        AllPass.allPassRegressionAntiresonanceParameters).toParameterizedNetlist.responseDomain :=
  allPassRationalNetlist_mem_responseDomain
    AllPass.allPassRegressionAntiresonanceParameters (-1)
    allPassRational_antiresonance_loopCoefficient
    allPassRational_antiresonance_isValid
    allPassRational_antiresonance_hasNonzeroDenominator

/-- The compiled rational fixture recovers the named S2 half-turn response `11/13`. -/
lemma allPassRationalNetlist_antiresonance_response_entry :
    (allPassRationalNetlist
      AllPass.allPassRegressionAntiresonanceParameters).toParameterizedNetlist.response
        allPassRationalAntiresonanceDomain
        (Outgoing.mk (allPassRationalThroughChannel
          AllPass.allPassRegressionAntiresonanceParameters (-1)))
        (Incident.mk (allPassRationalInputChannel
          AllPass.allPassRegressionAntiresonanceParameters (-1))) = 11 / 13 := by
  have hResponse := allPassRationalNetlist_response_entry
    AllPass.allPassRegressionAntiresonanceParameters (-1)
    allPassRational_antiresonance_loopCoefficient
    allPassRational_antiresonance_isValid
    allPassRational_antiresonance_hasNonzeroDenominator
  rw [AllPass.allPassRegression_antiresonance_throughTransfer] at hResponse
  simpa [allPassRationalAntiresonanceDomain] using hResponse

/-- The `3-4-5` all-pass fixture at quarter-turn round-trip phase. -/
def allPassRationalQuadratureParameters : AllPass.Parameters where
  throughAmplitude := 3 / 5
  crossAmplitude := 4 / 5
  fieldAttenuation := 1 / 2
  roundTripPhase := (((Real.pi / 2 : ℝ)) : Real.Angle)

/-- The quarter-turn fixture satisfies the component-validity predicates. -/
lemma allPassRational_quadrature_isValid : allPassRationalQuadratureParameters.IsValid := by
  constructor
  · constructor
    · norm_num [allPassRationalQuadratureParameters,
        DirectionalCoupler.Parameters.IsValid]
    · constructor
      · norm_num [allPassRationalQuadratureParameters,
          DirectionalCoupler.Parameters.IsValid]
      · norm_num [allPassRationalQuadratureParameters,
          DirectionalCoupler.Parameters.IsUnitary,
          DirectionalCoupler.Parameters.powerFactor]
  · norm_num [allPassRationalQuadratureParameters, MatchedPropagation.Parameters.IsValid]

/-- The quarter-turn fixture has one-pass coefficient `(1/2)*(-I)`. -/
lemma allPassRational_quadrature_loopCoefficient :
    allPassRationalQuadratureParameters.loopCoefficient =
      (allPassRationalQuadratureParameters.fieldAttenuation : ℂ) * (-Complex.I) := by
  simp [allPassRationalQuadratureParameters, AllPass.Parameters.loopCoefficient,
    AllPass.Parameters.propagation, MatchedPropagation.transmissionCoefficient,
    MatchedPropagation.carrierPhaseFactor, Real.Angle.toCircle_coe, Circle.coe_exp,
    Complex.exp_mul_I]

/-- The quarter-turn fixture denominator is `1 + (3/10) I`. -/
lemma allPassRational_quadrature_denominator :
    allPassRationalQuadratureParameters.denominator = 1 + (3 / 10 : ℂ) * Complex.I := by
  rw [AllPass.Parameters.denominator, AllPass.Parameters.loopGain,
    allPassRational_quadrature_loopCoefficient]
  norm_num [allPassRationalQuadratureParameters]
  ring

/-- The quarter-turn fixture has a nonzero feedback denominator. -/
lemma allPassRational_quadrature_hasNonzeroDenominator :
    allPassRationalQuadratureParameters.HasNonzeroDenominator := by
  rw [AllPass.Parameters.HasNonzeroDenominator,
    allPassRational_quadrature_denominator]
  intro hZero
  have hImag := congrArg Complex.im hZero
  norm_num at hImag

/-- Direct scalar expansion gives the non-real through response
`75/109 + (32/109) I`. -/
lemma allPassRational_quadrature_throughTransfer :
    AllPass.throughTransfer allPassRationalQuadratureParameters =
      75 / 109 + (32 / 109) * Complex.I := by
  rw [AllPass.throughTransfer, allPassRational_quadrature_loopCoefficient,
    allPassRational_quadrature_denominator]
  have hInverse : (1 + (3 / 10 : ℂ) * Complex.I)⁻¹ =
      (100 - 30 * Complex.I) / 109 := by
    apply inv_eq_of_mul_eq_one_right
    field_simp
    ring_nf
    norm_num [Complex.I_sq]
  simp [allPassRationalQuadratureParameters, AllPass.Parameters.coupler,
    DirectionalCoupler.crossCoefficient]
  rw [mul_pow, Complex.I_sq]
  conv_lhs =>
    rhs
    rw [div_eq_mul_inv, hInverse]
  ring_nf
  norm_num [Complex.I_sq]
  ring

/-- The quarter-turn point belongs to the compiled rational response domain at `q = -I`. -/
lemma allPassRationalQuadratureDomain :
    (fun _ : Fin 1 => -Complex.I) ∈
      (allPassRationalNetlist
        allPassRationalQuadratureParameters).toParameterizedNetlist.responseDomain :=
  allPassRationalNetlist_mem_responseDomain
    allPassRationalQuadratureParameters (-Complex.I)
    allPassRational_quadrature_loopCoefficient
    allPassRational_quadrature_isValid
    allPassRational_quadrature_hasNonzeroDenominator

/-- The compiled fixture's non-real response is `75/109 + (32/109) I`. -/
lemma allPassRationalNetlist_quadrature_response_entry :
    (allPassRationalNetlist
      allPassRationalQuadratureParameters).toParameterizedNetlist.response
        allPassRationalQuadratureDomain
        (Outgoing.mk (allPassRationalThroughChannel
          allPassRationalQuadratureParameters (-Complex.I)))
        (Incident.mk (allPassRationalInputChannel
          allPassRationalQuadratureParameters (-Complex.I))) =
      75 / 109 + (32 / 109) * Complex.I := by
  have hResponse := allPassRationalNetlist_response_entry
    allPassRationalQuadratureParameters (-Complex.I)
    allPassRational_quadrature_loopCoefficient
    allPassRational_quadrature_isValid
    allPassRational_quadrature_hasNonzeroDenominator
  rw [allPassRational_quadrature_throughTransfer] at hResponse
  simpa [allPassRationalQuadratureDomain] using hResponse

/-- With unit delay and `s = I*pi/2`, the Laplace convention evaluates to `q = -I`. -/
lemma laplaceEvaluation_quadrature :
    laplaceEvaluation (fun _ : Fin 1 => 1) (Complex.I * (Real.pi / 2 : ℝ)) =
      (fun _ => -Complex.I) := by
  funext i
  rw [laplaceEvaluation_apply]
  have hExponent :
      -(Complex.I * (Real.pi / 2 : ℝ)) * ((1 : ℝ) : ℂ) =
        ((-(Real.pi / 2 : ℝ) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hExponent, Complex.exp_mul_I]
  simp

/-- At `z = I`, reciprocal-Z evaluation gives `q = z⁻¹ = -I`. -/
lemma zInverseEvaluation_quadrature :
    zInverseEvaluation Complex.I = (fun _ => -Complex.I) := by
  funext i
  rw [zInverseEvaluation_apply, Complex.inv_I]

end

end Optics.DelayTransfer
