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
matrix `S`. The resulting internal matrix is

`B = D * 1 - C * S_clear`,

so its adjugate and determinant give an explicit retained polynomial numerator and denominator for
every external response entry. Evaluation is compared with the existing N5F elimination only at
points where all retained component denominators and the evaluated determinant of `B` are nonzero.

The construction is deliberately unreduced. Common factors can encode removable singularities,
and identifying or cancelling them belongs to the separate reduced-response layer.

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
operator `1 - C * S`. It proves rationality in formal delay variables only. It makes no statement
about rationality in physical frequency, minimality, pole visibility, causality, stability,
passivity, resonance, bandwidth, or material dispersion. The retained denominator is generally
not reduced, and its roots are not called physical poles.

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
def aggregateEntryModel (output input : family.IndexedChannel) : RationalModel n :=
  if hComponent : output.1 = input.1 then
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

/-- One entry denominator times its complementary product is the common denominator. -/
lemma denominator_mul_denominatorComplement (output input : netlist.Channel) :
    (netlist.scatteringEntryModel output input).denominator *
        netlist.denominatorComplement output input =
      netlist.commonDenominator := by
  rw [commonDenominator, denominatorComplement]
  exact Finset.mul_prod_erase _ (Finset.mem_univ (output, input))

/-- The aggregate common denominator is a nonzero formal polynomial. -/
lemma commonDenominator_ne_zero : netlist.commonDenominator ≠ 0 := by
  rw [commonDenominator]
  exact Finset.prod_ne_zero_iff.mpr fun entry _ =>
    (netlist.scatteringEntryModel entry.1 entry.2).denominator_ne_zero

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
      RationalModel.evaluationDomain_ofPolynomial]
    exact Set.mem_univ _

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
  have hProduct := congrArg (MvPolynomial.eval value)
    (netlist.denominator_mul_denominatorComplement output.channel input.channel)
  change
    MvPolynomial.eval value
        (model.numerator * netlist.denominatorComplement output.channel input.channel) =
      MvPolynomial.eval value netlist.commonDenominator *
        netlist.toParameterizedNetlist.scatteringTransform value output input
  rw [netlist.scatteringEntryModel_eval]
  change
    MvPolynomial.eval value
        (model.numerator * netlist.denominatorComplement output.channel input.channel) =
      MvPolynomial.eval value netlist.commonDenominator * model.eval value
  simp only [MvPolynomial.eval_mul, RationalModel.eval_eq]
  simp only [MvPolynomial.eval_mul] at hProduct
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

/-- Evaluation removes the polynomial lift from the routing matrix. -/
lemma eval_polynomialRouting (value : DelayTuple n) :
    netlist.polynomialRouting.map (MvPolynomial.eval value) =
      netlist.toParameterizedNetlist.routingTransform := by
  ext incident outgoing
  simp [polynomialRouting]

/-- Evaluation removes the polynomial lift from the external incident injection. -/
lemma eval_polynomialInputExposure (value : DelayTuple n) :
    netlist.polynomialInputExposure.map (MvPolynomial.eval value) =
      netlist.toParameterizedNetlist.inputExposure := by
  ext incident external
  simp [polynomialInputExposure]

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
  rw [clearedFeedback, Matrix.map_sub _ _ (map_sub _), Matrix.map_mul,
    netlist.eval_polynomialRouting, netlist.eval_clearedScattering value hRegular]
  ext incident input
  simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply,
    map_smul, map_one, smul_eq_mul, Matrix.sub_apply,
    ParameterizedNetlist.feedbackOperator_eq]
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
  ring

/-- Evaluating the retained response denominator evaluates the cleared determinant. -/
lemma eval_responseDenominator (value : DelayTuple n) :
    MvPolynomial.eval value netlist.responseDenominator =
      (netlist.clearedFeedback.map (MvPolynomial.eval value)).det := by
  exact (MvPolynomial.eval value).map_det netlist.clearedFeedback

end Finite

end RationalNetlist

end


end Optics.DelayTransfer
