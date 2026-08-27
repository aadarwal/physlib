/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Systems.DelayTransfer.Evaluation

/-!
# Cleared-polynomial elimination for rational-delay optical networks

## i. Overview

This file clears the retained denominators of every component scattering entry before eliminating
the internal network state. A single aggregate polynomial `D` clears the assembled component
matrix `S`, giving `B = D * 1 - C * S_clear` and an adjugate/determinant response representative.
Evaluation is compared with the existing N5F elimination only where all retained component
denominators and the evaluated determinant of `B` are nonzero. The N5F matrices and operator are
defined in `Physlib/Optics/Network/ParameterizedResponse.lean:376-428`; its total-inverse and
proof-gated response bridge is at `Physlib/Optics/Network/ParameterizedResponse.lean:545-574`.
`RationalNetlist`, its inherited domains, and its response specialization are defined in
`Physlib/Optics/Systems/DelayTransfer/Evaluation.lean:153-170,228-260`. The construction is
deliberately unreduced. Common factors can encode removable singularities, and identifying or
cancelling them belongs to the separate reduced-response layer.

## ii. Key results

- `RationalNetlist.commonDenominator`: one retained denominator for the assembled component law.
- `RationalNetlist.clearedScattering`: the polynomial matrix `S_clear`.
- `RationalNetlist.clearedFeedback`: the polynomial internal matrix `B`.
- `RationalNetlist.responseNumerator`: the adjugate-based external numerator matrix.
- `RationalNetlist.responseDenominator`: the determinant of `B`.
- `RationalNetlist.evaluatedResponseQuotient_eq_unguardedResponse`: agreement with N5F elimination.

## iii. Table of contents

- A. Aggregate rational entry models
- B. Common-denominator clearing
- C. Cleared feedback and response polynomials
- D. Evaluation and N5F agreement

## iv. References

The formula is the finite-dimensional adjugate identity applied to the already-defined N5F
operator `1 - C * S`. It proves rationality in formal delay variables only; the retained
denominator is unreduced and its roots are not called physical poles. The network-level
reachability/observability or no-cancellation criterion remains withheld. It also makes no claim
of minimality, physical-frequency rationality, causality, stability, passivity, resonance,
bandwidth, or material dispersion.

-/

@[expose] public section

namespace Optics.DelayTransfer

noncomputable section

universe u v w x

/-!

## A. Aggregate rational entry models

-/

namespace RationalComponentFamily

variable {n : ℕ} (family : RationalComponentFamily.{u, v, w} n)

/-- The component-indexed sum of the local channels of a rational component family. -/
abbrev IndexedChannel := Σ component, (family.portFamily component).Channel

/-- Reassociate a component-indexed local channel as an aggregate physical channel. -/
def indexedChannelEquiv :
    family.IndexedChannel ≃ family.toParameterizedComponentFamily.Channel where
  toFun := fun ⟨component, ⟨port, mode⟩⟩ => ⟨⟨component, port⟩, mode⟩
  invFun := fun ⟨⟨component, port⟩, mode⟩ => ⟨component, ⟨port, mode⟩⟩
  left_inv := by
    rintro ⟨component, ⟨port, mode⟩⟩
    rfl
  right_inv := by
    rintro ⟨⟨component, port⟩, mode⟩
    rfl

/-- The retained rational model of one entry of the aggregate block-diagonal component law. -/
def aggregateEntryModel (output input : family.IndexedChannel) : RationalModel n := by
  classical
  exact if hComponent : output.1 = input.1 then
      family.entryModel output.1 output.2
        (Eq.mp (congrArg (fun component => (family.portFamily component).Channel)
          hComponent.symm) input.2)
    else
      RationalModel.constant 0

/-- A diagonal aggregate entry is exactly its selected local rational model. -/
@[simp]
lemma aggregateEntryModel_same (component : family.Component)
    (output input : (family.portFamily component).Channel) :
    family.aggregateEntryModel ⟨component, output⟩ ⟨component, input⟩ =
      family.entryModel component output input := by
  simp [aggregateEntryModel]

/-- Aggregate entries between distinct components are the constant-zero rational model. -/
lemma aggregateEntryModel_of_ne {first second : family.Component}
    (hComponent : first ≠ second)
    (output : (family.portFamily first).Channel)
    (input : (family.portFamily second).Channel) :
    family.aggregateEntryModel ⟨first, output⟩ ⟨second, input⟩ =
      RationalModel.constant 0 := by
  simp [aggregateEntryModel, hComponent]

end RationalComponentFamily

namespace RationalNetlist

variable {n : ℕ} (netlist : RationalNetlist.{u, v, w, x} n)

/-- The full incident index of the aggregate rational-netlist boundary. -/
abbrev IncidentIndex := netlist.toParameterizedNetlist.IncidentIndex

/-- The full outgoing index of the aggregate rational-netlist boundary. -/
abbrev OutgoingIndex := netlist.toParameterizedNetlist.OutgoingIndex

/-- Every retained local component entry is regular at one formal-delay assignment. -/
def ComponentEntriesRegularAt (value : DelayTuple n) : Prop :=
  ∀ component, netlist.components.EntriesRegularAt component value

/-- The retained rational model of one assembled scattering entry. -/
def scatteringEntryModel (output input : netlist.Channel) : RationalModel n :=
  netlist.components.aggregateEntryModel
    (netlist.components.indexedChannelEquiv.symm output)
    (netlist.components.indexedChannelEquiv.symm input)

/-- A local diagonal block selects exactly the stored component entry model. -/
@[simp]
lemma scatteringEntryModel_same (component : netlist.components.Component)
    (output input : (netlist.components.portFamily component).Channel) :
    netlist.scatteringEntryModel
        (netlist.components.indexedChannelEquiv ⟨component, output⟩)
        (netlist.components.indexedChannelEquiv ⟨component, input⟩) =
      netlist.components.entryModel component output input := by
  simp [scatteringEntryModel]

/-- Entries between two distinct component blocks are represented by the constant-zero model. -/
lemma scatteringEntryModel_of_ne {first second : netlist.components.Component}
    (hComponent : first ≠ second)
    (output : (netlist.components.portFamily first).Channel)
    (input : (netlist.components.portFamily second).Channel) :
    netlist.scatteringEntryModel
        (netlist.components.indexedChannelEquiv ⟨first, output⟩)
        (netlist.components.indexedChannelEquiv ⟨second, input⟩) =
      RationalModel.constant 0 := by
  simp only [scatteringEntryModel, Equiv.symm_apply_apply]
  exact netlist.components.aggregateEntryModel_of_ne hComponent output input

/-- Evaluating an aggregate entry model gives the corresponding assembled scattering entry. -/
lemma scatteringEntryModel_eval (value : DelayTuple n)
    (output input : netlist.Channel) :
    (netlist.scatteringEntryModel output input).eval value =
      netlist.toParameterizedNetlist.scatteringTransform value
        (Outgoing.mk output) (Incident.mk input) := by
  obtain ⟨⟨outputComponent, outputChannel⟩, rfl⟩ :=
    netlist.components.indexedChannelEquiv.surjective output
  obtain ⟨⟨inputComponent, inputChannel⟩, rfl⟩ :=
    netlist.components.indexedChannelEquiv.surjective input
  by_cases hComponent : outputComponent = inputComponent
  · subst inputComponent
    rw [netlist.scatteringEntryModel_same]
    exact (netlist.toParameterizedNetlist.compile_scatteringTransform_entry_same
      value outputComponent outputChannel inputChannel).symm
  · rw [netlist.scatteringEntryModel_of_ne hComponent,
      RationalModel.eval_constant]
    exact (netlist.toParameterizedNetlist.compile_scatteringTransform_entry_of_ne
      value hComponent outputChannel inputChannel).symm

/-!

## B. Common-denominator clearing

-/

section Finite

variable [Fintype netlist.Channel] [Fintype netlist.ConnectedChannel]

/-- Classical equality on aggregate rational-netlist channels. -/
local instance rationalEliminationChannelDecidableEq : DecidableEq netlist.Channel :=
  Classical.decEq _

/-- Classical equality on connected channels for the inherited routing matrix. -/
local instance rationalEliminationConnectedChannelDecidableEq :
    DecidableEq netlist.ConnectedChannel := Classical.decEq _

/-- External channels of a finite rational netlist are finite. -/
local instance rationalEliminationExternalChannelFintype :
    Fintype netlist.ExternalChannel := by
  classical
  infer_instance

/-- The product of every retained aggregate scattering-entry denominator. -/
def commonDenominator : DelayPolynomial n :=
  ∏ entry : netlist.Channel × netlist.Channel,
    (netlist.scatteringEntryModel entry.1 entry.2).denominator

/-- The product of every denominator except the selected aggregate scattering entry. -/
def denominatorComplement (output input : netlist.Channel) : DelayPolynomial n :=
  ∏ entry ∈ Finset.univ.erase (output, input),
    (netlist.scatteringEntryModel entry.1 entry.2).denominator

omit [Fintype netlist.ConnectedChannel] in
/-- One entry denominator times its complementary product is the common denominator. -/
lemma denominator_mul_denominatorComplement (output input : netlist.Channel) :
    (netlist.scatteringEntryModel output input).denominator *
        netlist.denominatorComplement output input =
      netlist.commonDenominator := by
  rw [commonDenominator, denominatorComplement]
  exact Finset.mul_prod_erase Finset.univ
    (fun entry => (netlist.scatteringEntryModel entry.1 entry.2).denominator)
    (Finset.mem_univ (output, input))

omit [Fintype netlist.ConnectedChannel] in
/-- The aggregate common denominator is a nonzero formal polynomial. -/
lemma commonDenominator_ne_zero : netlist.commonDenominator ≠ 0 := by
  rw [commonDenominator]
  exact Finset.prod_ne_zero_iff.mpr fun entry _ =>
    (netlist.scatteringEntryModel entry.1 entry.2).denominator_ne_zero

omit [Fintype netlist.Channel] [Fintype netlist.ConnectedChannel] in
/-- Componentwise regularity makes every retained aggregate entry denominator nonzero. -/
lemma scatteringEntryModel_regular (value : DelayTuple n)
    (hRegular : netlist.ComponentEntriesRegularAt value)
    (output input : netlist.Channel) :
    value ∈ (netlist.scatteringEntryModel output input).evaluationDomain := by
  obtain ⟨⟨outputComponent, outputChannel⟩, rfl⟩ :=
    netlist.components.indexedChannelEquiv.surjective output
  obtain ⟨⟨inputComponent, inputChannel⟩, rfl⟩ :=
    netlist.components.indexedChannelEquiv.surjective input
  by_cases hComponent : outputComponent = inputComponent
  · subst inputComponent
    rw [netlist.scatteringEntryModel_same]
    exact hRegular outputComponent outputChannel inputChannel
  · rw [netlist.scatteringEntryModel_of_ne hComponent,
      RationalModel.constant, RationalModel.evaluationDomain_ofPolynomial]
    exact Set.mem_univ _

omit [Fintype netlist.ConnectedChannel] in
/-- The common denominator evaluates nontrivially at every component-regular point. -/
lemma eval_commonDenominator_ne_zero (value : DelayTuple n)
    (hRegular : netlist.ComponentEntriesRegularAt value) :
    MvPolynomial.eval value netlist.commonDenominator ≠ 0 := by
  rw [commonDenominator, map_prod]
  exact Finset.prod_ne_zero_iff.mpr fun entry _ =>
    netlist.scatteringEntryModel_regular value hRegular entry.1 entry.2

/-- The polynomial scattering matrix obtained after clearing the common denominator. -/
def clearedScattering :
    Matrix netlist.OutgoingIndex netlist.IncidentIndex (DelayPolynomial n) :=
  fun output input =>
    (netlist.scatteringEntryModel output.channel input.channel).numerator *
      netlist.denominatorComplement output.channel input.channel

omit [Fintype netlist.ConnectedChannel] in
/-- Evaluation of the cleared scattering matrix is the common denominator times the assembled
component law. -/
lemma eval_clearedScattering (value : DelayTuple n)
    (hRegular : netlist.ComponentEntriesRegularAt value) :
    netlist.clearedScattering.map (MvPolynomial.eval value) =
      MvPolynomial.eval value netlist.commonDenominator •
        netlist.toParameterizedNetlist.scatteringTransform value := by
  ext output input
  let model := netlist.scatteringEntryModel output.channel input.channel
  have hDenominator : MvPolynomial.eval value model.denominator ≠ 0 :=
    netlist.scatteringEntryModel_regular value hRegular output.channel input.channel
  have hProduct :
      MvPolynomial.eval value model.denominator *
          MvPolynomial.eval value
            (netlist.denominatorComplement output.channel input.channel) =
        MvPolynomial.eval value netlist.commonDenominator := by
    simpa only [model, MvPolynomial.eval_mul] using
      congrArg (MvPolynomial.eval value)
        (netlist.denominator_mul_denominatorComplement output.channel input.channel)
  change
    MvPolynomial.eval value
        (model.numerator * netlist.denominatorComplement output.channel input.channel) =
      MvPolynomial.eval value netlist.commonDenominator *
        netlist.toParameterizedNetlist.scatteringTransform value output input
  rw [← netlist.scatteringEntryModel_eval value output.channel input.channel]
  change
    MvPolynomial.eval value
        (model.numerator * netlist.denominatorComplement output.channel input.channel) =
      MvPolynomial.eval value netlist.commonDenominator * model.eval value
  simp only [MvPolynomial.eval_mul, RationalModel.eval_eq]
  rw [← hProduct]
  field_simp

/-!

## C. Cleared feedback and response polynomials

-/

/-- The parameter-independent routing matrix lifted to polynomial coefficients. -/
def polynomialRouting :
    Matrix netlist.IncidentIndex netlist.OutgoingIndex (DelayPolynomial n) :=
  netlist.toParameterizedNetlist.routingTransform.map MvPolynomial.C

/-- The external incident injection lifted to polynomial coefficients. -/
def polynomialInputExposure :
    Matrix netlist.IncidentIndex netlist.ExternalIncident (DelayPolynomial n) :=
  netlist.toParameterizedNetlist.inputExposure.map MvPolynomial.C

/-- The external outgoing readout lifted to polynomial coefficients. -/
def polynomialOutputReadout :
    Matrix netlist.ExternalOutgoing netlist.OutgoingIndex (DelayPolynomial n) :=
  netlist.toParameterizedNetlist.outputReadout.map MvPolynomial.C

/-- The denominator-cleared internal matrix `D * 1 - C * S_clear`. -/
def clearedFeedback :
    Matrix netlist.IncidentIndex netlist.IncidentIndex (DelayPolynomial n) :=
  netlist.commonDenominator • (1 :
    Matrix netlist.IncidentIndex netlist.IncidentIndex (DelayPolynomial n)) -
      netlist.polynomialRouting * netlist.clearedScattering

/-- The retained adjugate-based numerator matrix of the external response. -/
def responseNumerator :
    Matrix netlist.ExternalOutgoing netlist.ExternalIncident (DelayPolynomial n) :=
  netlist.polynomialOutputReadout * netlist.clearedScattering *
    netlist.clearedFeedback.adjugate * netlist.polynomialInputExposure

/-- The retained denominator of every external response entry. -/
def responseDenominator : DelayPolynomial n :=
  netlist.clearedFeedback.det

/-- The formal gate that the cleared internal determinant is not the zero polynomial. -/
def IsGenericallyWellPosed : Prop :=
  netlist.responseDenominator ≠ 0

/-- One retained external response entry as a rational model. -/
def responseEntryModel (hGeneric : netlist.IsGenericallyWellPosed)
    (output : netlist.ExternalOutgoing) (input : netlist.ExternalIncident) :
    RationalModel n where
  numerator := netlist.responseNumerator output input
  denominator := netlist.responseDenominator
  denominator_ne_zero := hGeneric

/-- The pointwise quotient of the retained external numerator and denominator matrices. -/
def evaluatedResponseQuotient (value : DelayTuple n) :
    ModeTransform netlist.ExternalIncident netlist.ExternalOutgoing :=
  fun output input =>
    MvPolynomial.eval value (netlist.responseNumerator output input) /
      MvPolynomial.eval value netlist.responseDenominator

/-!

## D. Evaluation and N5F agreement

-/

omit [Fintype netlist.Channel] in
/-- Evaluation removes the polynomial lift from the routing matrix. -/
lemma eval_polynomialRouting (value : DelayTuple n) :
    netlist.polynomialRouting.map (MvPolynomial.eval value) =
      netlist.toParameterizedNetlist.routingTransform := by
  ext incident outgoing
  simp [polynomialRouting]

omit [Fintype netlist.Channel] [Fintype netlist.ConnectedChannel] in
/-- Evaluation removes the polynomial lift from the external incident injection. -/
lemma eval_polynomialInputExposure (value : DelayTuple n) :
    netlist.polynomialInputExposure.map (MvPolynomial.eval value) =
      netlist.toParameterizedNetlist.inputExposure := by
  ext incident external
  simp [polynomialInputExposure]

omit [Fintype netlist.Channel] [Fintype netlist.ConnectedChannel] in
/-- Evaluation removes the polynomial lift from the external outgoing readout. -/
lemma eval_polynomialOutputReadout (value : DelayTuple n) :
    netlist.polynomialOutputReadout.map (MvPolynomial.eval value) =
      netlist.toParameterizedNetlist.outputReadout := by
  ext external outgoing
  simp [polynomialOutputReadout]

/-- Evaluation of the cleared internal matrix is the evaluated common denominator times the N5F
feedback operator. -/
lemma eval_clearedFeedback (value : DelayTuple n)
    (hRegular : netlist.ComponentEntriesRegularAt value) :
    netlist.clearedFeedback.map (MvPolynomial.eval value) =
      MvPolynomial.eval value netlist.commonDenominator •
        netlist.toParameterizedNetlist.feedbackOperator value := by
  rw [clearedFeedback,
    Matrix.map_sub (MvPolynomial.eval value)
      (fun first second => (MvPolynomial.eval value).map_sub first second),
    Matrix.map_smul' (MvPolynomial.eval value) netlist.commonDenominator
      (1 : Matrix netlist.IncidentIndex netlist.IncidentIndex (DelayPolynomial n))
      (fun first second => (MvPolynomial.eval value).map_mul first second),
    Matrix.map_one (MvPolynomial.eval value)
      (MvPolynomial.eval value).map_zero (MvPolynomial.eval value).map_one,
    Matrix.map_mul,
    netlist.eval_polynomialRouting,
    netlist.eval_clearedScattering value hRegular,
    Matrix.mul_smul, ← smul_sub,
    ParameterizedNetlist.feedbackOperator_eq]

/-- Evaluating the retained response denominator evaluates the cleared determinant. -/
lemma eval_responseDenominator (value : DelayTuple n) :
    MvPolynomial.eval value netlist.responseDenominator =
      (netlist.clearedFeedback.map (MvPolynomial.eval value)).det := by
  exact (MvPolynomial.eval value).map_det netlist.clearedFeedback

/-- Evaluation commutes with the four polynomial matrix factors defining the retained response
numerator. -/
lemma eval_responseNumerator (value : DelayTuple n)
    (hRegular : netlist.ComponentEntriesRegularAt value) :
    netlist.responseNumerator.map (MvPolynomial.eval value) =
      netlist.toParameterizedNetlist.outputReadout *
        (MvPolynomial.eval value netlist.commonDenominator •
          netlist.toParameterizedNetlist.scatteringTransform value) *
        (MvPolynomial.eval value netlist.commonDenominator •
          netlist.toParameterizedNetlist.feedbackOperator value).adjugate *
        netlist.toParameterizedNetlist.inputExposure := by
  have hAdjugate :=
    (MvPolynomial.eval value).map_adjugate netlist.clearedFeedback
  change netlist.clearedFeedback.adjugate.map (MvPolynomial.eval value) =
    (netlist.clearedFeedback.map (MvPolynomial.eval value)).adjugate at hAdjugate
  rw [responseNumerator, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul,
    hAdjugate,
    netlist.eval_polynomialOutputReadout,
    netlist.eval_clearedScattering value hRegular,
    netlist.eval_clearedFeedback value hRegular,
    netlist.eval_polynomialInputExposure]

private lemma adjugateQuotient_fourFactor
    {internal outgoing externalOutgoing externalIncident : Type*}
    [Fintype internal] [DecidableEq internal]
    [Fintype outgoing]
    (denominator : ℂ) (hDenominator : denominator ≠ 0)
    (scattering : Matrix outgoing internal ℂ)
    (feedback : Matrix internal internal ℂ)
    (hFeedback : feedback.det ≠ 0)
    (readout : Matrix externalOutgoing outgoing ℂ)
    (exposure : Matrix internal externalIncident ℂ) :
    (fun output input =>
        (readout * (denominator • scattering) *
            (denominator • feedback).adjugate * exposure) output input /
          (denominator • feedback).det) =
      readout * scattering * feedback⁻¹ * exposure := by
  let _ : Invertible denominator := invertibleOfNonzero hDenominator
  have hFeedbackUnit : IsUnit feedback.det := hFeedback.isUnit
  have hQuotient :
      (fun output input =>
        (readout * (denominator • scattering) *
            (denominator • feedback).adjugate * exposure) output input /
          (denominator • feedback).det) =
        ((denominator • feedback).det)⁻¹ •
          (readout * (denominator • scattering) *
            (denominator • feedback).adjugate * exposure) := by
    ext output input
    change
      (readout * (denominator • scattering) *
          (denominator • feedback).adjugate * exposure) output input /
          (denominator • feedback).det =
        (denominator • feedback).det⁻¹ *
          (readout * (denominator • scattering) *
            (denominator • feedback).adjugate * exposure) output input
    rw [div_eq_inv_mul]
  have hAdjugate :
      ((denominator • feedback).det)⁻¹ •
          (readout * (denominator • scattering) *
            (denominator • feedback).adjugate * exposure) =
        readout * (denominator • scattering) *
          (denominator • feedback)⁻¹ * exposure := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv]
    simp only [Matrix.mul_smul, Matrix.smul_mul]
  have hScale :
      readout * (denominator • scattering) *
          (denominator • feedback)⁻¹ * exposure =
        readout * scattering * feedback⁻¹ * exposure := by
    rw [Matrix.inv_smul feedback denominator hFeedbackUnit, invOf_eq_inv]
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul,
      inv_mul_cancel₀ hDenominator, one_smul]
  exact hQuotient.trans (hAdjugate.trans hScale)

/-- The evaluated cleared determinant is the corresponding scalar power times the N5F feedback
determinant. -/
lemma eval_responseDenominator_eq (value : DelayTuple n)
    (hRegular : netlist.ComponentEntriesRegularAt value) :
    MvPolynomial.eval value netlist.responseDenominator =
      MvPolynomial.eval value netlist.commonDenominator ^
          Fintype.card netlist.IncidentIndex *
        (netlist.toParameterizedNetlist.feedbackOperator value).det := by
  rw [netlist.eval_responseDenominator,
    netlist.eval_clearedFeedback value hRegular, Matrix.det_smul]

/-- At a component-regular point, the retained response denominator is nonzero exactly on the
N5F algebraic solve domain. -/
lemma eval_responseDenominator_ne_zero_iff_solveDomain (value : DelayTuple n)
    (hRegular : netlist.ComponentEntriesRegularAt value) :
    MvPolynomial.eval value netlist.responseDenominator ≠ 0 ↔
      value ∈ netlist.toParameterizedNetlist.solveDomain := by
  rw [netlist.eval_responseDenominator_eq value hRegular,
    netlist.toParameterizedNetlist.mem_solveDomain_iff_det_ne_zero]
  simp only [mul_ne_zero_iff]
  exact and_iff_right
    (pow_ne_zero _ (netlist.eval_commonDenominator_ne_zero value hRegular))

/-- Evaluation of the cleared adjugate quotient agrees with the existing N5F total-inverse
formula wherever every component entry and the cleared determinant are regular. -/
lemma evaluatedResponseQuotient_eq_unguardedResponse (value : DelayTuple n)
    (hRegular : netlist.ComponentEntriesRegularAt value)
    (hDeterminant : MvPolynomial.eval value netlist.responseDenominator ≠ 0) :
    netlist.evaluatedResponseQuotient value =
      netlist.toParameterizedNetlist.unguardedResponse value := by
  have hSolve : value ∈ netlist.toParameterizedNetlist.solveDomain :=
    (netlist.eval_responseDenominator_ne_zero_iff_solveDomain value hRegular).mp hDeterminant
  have hFeedback :
      (netlist.toParameterizedNetlist.feedbackOperator value).det ≠ 0 :=
    (netlist.toParameterizedNetlist.mem_solveDomain_iff_det_ne_zero value).mp hSolve
  change
    (fun output input =>
      (netlist.responseNumerator.map (MvPolynomial.eval value)) output input /
        MvPolynomial.eval value netlist.responseDenominator) =
      netlist.toParameterizedNetlist.outputReadout *
        netlist.toParameterizedNetlist.scatteringTransform value *
        (netlist.toParameterizedNetlist.feedbackOperator value)⁻¹ *
        netlist.toParameterizedNetlist.inputExposure
  rw [netlist.eval_responseNumerator value hRegular,
    netlist.eval_responseDenominator,
    netlist.eval_clearedFeedback value hRegular]
  exact adjugateQuotient_fourFactor
    (MvPolynomial.eval value netlist.commonDenominator)
    (netlist.eval_commonDenominator_ne_zero value hRegular)
    (netlist.toParameterizedNetlist.scatteringTransform value)
    (netlist.toParameterizedNetlist.feedbackOperator value)
    hFeedback
    netlist.toParameterizedNetlist.outputReadout
    netlist.toParameterizedNetlist.inputExposure

/-- Physical response-domain membership supplies regularity of every retained component entry. -/
lemma componentEntriesRegularAt_of_mem_responseDomain {value : DelayTuple n}
    (hValue : value ∈ netlist.responseDomain) : netlist.ComponentEntriesRegularAt value :=
  fun component => (hValue.2 component).2

/-- On the physical response domain, the evaluated cleared quotient is the proof-gated N5F
response. -/
lemma evaluatedResponseQuotient_eq_response {value : DelayTuple n}
    (hValue : value ∈ netlist.responseDomain) :
    netlist.evaluatedResponseQuotient value =
      netlist.toParameterizedNetlist.response hValue := by
  have hRegular := netlist.componentEntriesRegularAt_of_mem_responseDomain hValue
  have hDeterminant : MvPolynomial.eval value netlist.responseDenominator ≠ 0 :=
    (netlist.eval_responseDenominator_ne_zero_iff_solveDomain value hRegular).mpr hValue.1
  rw [netlist.evaluatedResponseQuotient_eq_unguardedResponse value hRegular hDeterminant,
    netlist.toParameterizedNetlist.unguardedResponse_eq_response hValue]

/-- Every retained response-entry model evaluates to the proof-gated N5F response on the physical
response domain. -/
lemma responseEntryModel_eval_eq_response (hGeneric : netlist.IsGenericallyWellPosed)
    {value : DelayTuple n} (hValue : value ∈ netlist.responseDomain)
    (output : netlist.ExternalOutgoing) (input : netlist.ExternalIncident) :
    (netlist.responseEntryModel hGeneric output input).eval value =
      netlist.toParameterizedNetlist.response hValue output input := by
  change netlist.evaluatedResponseQuotient value output input = _
  exact congrFun
    (congrFun (netlist.evaluatedResponseQuotient_eq_response hValue) output) input

end Finite

end RationalNetlist

end


end Optics.DelayTransfer
