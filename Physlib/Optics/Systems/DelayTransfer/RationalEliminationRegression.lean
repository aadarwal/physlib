/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Systems.DelayTransfer.RationalElimination

/-!
# Regression tests for cleared rational-delay elimination

## i. Overview

This file tests the cleared-polynomial construction on a one-port all-pass fixture whose retained
entry is `(1 - q) / (1 - q)`. The unreduced numerator and denominator both vanish at `q = 1`, even
though the represented rational function is one away from that excluded point. At `q = -1`, the
polynomial quotient and the raw compiled network equations are expanded separately and both give
one.

## ii. Key results

- `cancellationHiding_responseNumerator`: the retained external numerator is `1 - q`.
- `cancellationHiding_responseDenominator`: the retained external denominator is `1 - q`.
- `cancellationHiding_independent_regular_anchor`: both independently expanded semantics give one
  at `q = -1`.
- `cancellationHiding_singular_anchor`: both retained polynomials vanish at `q = 1`.

## iii. Table of contents

- A. Cancellation-hiding one-port fixture
- B. Independent polynomial and network anchors

## iv. References

This is an algebraic regression for unreduced formal-delay elimination. It does not model a
physical resonator, infer a pole at the removable singularity, or state causality, stability,
passivity, resonance, bandwidth, or material-dispersion results.

-/

@[expose] public section

namespace Optics.DelayTransfer

noncomputable section

/-!

## A. Cancellation-hiding one-port fixture

-/

/-- The retained polynomial `1 - q` used on both sides of the cancellation-hiding fixture. -/
def cancellationHidingPolynomial : DelayPolynomial 1 :=
  1 - MvPolynomial.X 0

/-- The polynomial `1 - q` is not identically zero. -/
lemma cancellationHidingPolynomial_ne_zero : cancellationHidingPolynomial ≠ 0 := by
  intro hZero
  have hEval := congrArg (MvPolynomial.eval fun _ : Fin 1 => (0 : ℂ)) hZero
  norm_num [cancellationHidingPolynomial] at hEval

/-- The unreduced one-port all-pass entry `(1 - q) / (1 - q)`. -/
def cancellationHidingEntryModel : RationalModel 1 where
  numerator := cancellationHidingPolynomial
  denominator := cancellationHidingPolynomial
  denominator_ne_zero := cancellationHidingPolynomial_ne_zero

/-- The singleton physical port and singleton mode fiber of the fixture. -/
def cancellationHidingPortFamily : PortModeFamily where
  Port := Unit
  Mode := fun _ => Unit

/-- The singleton rational component carrying the unreduced all-pass entry. -/
def cancellationHidingComponents : RationalComponentFamily 1 where
  Component := Unit
  portFamily := fun _ => cancellationHidingPortFamily
  entryModel := fun _ _ _ => cancellationHidingEntryModel
  ModelValidAt := fun _ value => ‖value 0‖ ≤ 2

/-- The empty connection family leaves the unique one-port component externally exposed. -/
def cancellationHidingConnections : PortConnectionFamily
    cancellationHidingComponents.toParameterizedComponentFamily.aggregatePortModeFamily Empty where
  connection := Empty.elim
  endpointPort_injective := by
    rintro ⟨connection, _⟩
    exact connection.elim

/-- The one-port rational netlist used to expose retained cancellation. -/
def cancellationHidingNetlist : RationalNetlist 1 where
  components := cancellationHidingComponents
  Connection := Empty
  connections := cancellationHidingConnections

/-- The fixture's unique aggregate channel. -/
def cancellationHidingChannel : cancellationHidingNetlist.Channel :=
  ⟨⟨(), ()⟩, ()⟩

/-- The fixture's unique external channel. -/
def cancellationHidingExternalChannel : cancellationHidingNetlist.ExternalChannel :=
  ⟨cancellationHidingChannel, by
    rintro ⟨⟨connection, _⟩, _⟩
    exact connection.elim⟩

/-- The aggregate singleton fixture has a unique channel. -/
instance cancellationHidingChannelUnique : Unique cancellationHidingNetlist.Channel where
  default := cancellationHidingChannel
  uniq := by
    rintro ⟨⟨component, port⟩, mode⟩
    cases component
    cases port
    cases mode
    rfl

/-- The empty wiring leaves a unique external channel. -/
instance cancellationHidingExternalChannelUnique :
    Unique cancellationHidingNetlist.ExternalChannel where
  default := cancellationHidingExternalChannel
  uniq := by
    intro channel
    apply Subtype.ext
    exact Subsingleton.elim channel.1 cancellationHidingChannel

/-- Aggregate channels of the singleton fixture are finite. -/
noncomputable instance cancellationHidingChannelFintype :
    Fintype cancellationHidingNetlist.Channel := by
  change Fintype (Σ _ : (Σ _ : Unit, Unit), Unit)
  infer_instance

/-- Classical equality on the aggregate singleton channel. -/
noncomputable instance cancellationHidingChannelDecidableEq :
    DecidableEq cancellationHidingNetlist.Channel := Classical.decEq _

/-- Classical equality in the component-family spelling of the aggregate channel. -/
noncomputable instance cancellationHidingAggregateChannelDecidableEq :
    DecidableEq
      cancellationHidingComponents.toParameterizedComponentFamily.aggregatePortModeFamily.Channel :=
  Classical.decEq _

/-- The singleton incident index is unique. -/
instance cancellationHidingIncidentUnique : Unique cancellationHidingNetlist.IncidentIndex where
  default := Incident.mk cancellationHidingChannel
  uniq := by
    rintro ⟨channel⟩
    exact congrArg Incident.mk (Subsingleton.elim channel cancellationHidingChannel)

/-- The singleton outgoing index is unique. -/
instance cancellationHidingOutgoingUnique : Unique cancellationHidingNetlist.OutgoingIndex where
  default := Outgoing.mk cancellationHidingChannel
  uniq := by
    rintro ⟨channel⟩
    exact congrArg Outgoing.mk (Subsingleton.elim channel cancellationHidingChannel)

/-- The singleton external incident index is unique. -/
instance cancellationHidingExternalIncidentUnique :
    Unique cancellationHidingNetlist.ExternalIncident where
  default := Incident.mk cancellationHidingExternalChannel
  uniq := by
    rintro ⟨channel⟩
    exact congrArg Incident.mk (Subsingleton.elim channel cancellationHidingExternalChannel)

/-- The singleton external outgoing index is unique. -/
instance cancellationHidingExternalOutgoingUnique :
    Unique cancellationHidingNetlist.ExternalOutgoing where
  default := Outgoing.mk cancellationHidingExternalChannel
  uniq := by
    rintro ⟨channel⟩
    exact congrArg Outgoing.mk (Subsingleton.elim channel cancellationHidingExternalChannel)

/-- The empty family of connected channels is finite. -/
noncomputable instance cancellationHidingConnectedChannelFintype :
    Fintype cancellationHidingNetlist.ConnectedChannel := by
  let equivalence : Empty ≃ cancellationHidingNetlist.ConnectedChannel :=
    { toFun := Empty.elim
      invFun := fun channel => channel.1.elim
      left_inv := fun element => element.elim
      right_inv := fun channel => channel.1.elim }
  exact Fintype.ofEquiv Empty equivalence

/-- The connection-family spelling of the empty connected-channel type is finite. -/
noncomputable instance cancellationHidingConnectionChannelFintype :
    Fintype cancellationHidingConnections.Channel := by
  exact cancellationHidingConnectedChannelFintype

/-- Classical equality on the empty connected-channel type. -/
noncomputable instance cancellationHidingConnectedChannelDecidableEq :
    DecidableEq cancellationHidingNetlist.ConnectedChannel := Classical.decEq _

/-!

## B. Independent polynomial and network anchors

-/

/-- The unique assembled entry selects the fixture's stored rational model. -/
lemma cancellationHiding_scatteringEntryModel :
    cancellationHidingNetlist.scatteringEntryModel
        cancellationHidingChannel cancellationHidingChannel = cancellationHidingEntryModel := by
  simp [RationalNetlist.scatteringEntryModel, RationalComponentFamily.aggregateEntryModel,
    RationalComponentFamily.indexedChannelEquiv, cancellationHidingNetlist,
    cancellationHidingComponents, cancellationHidingChannel]

/-- The fixture's retained common denominator is exactly `1 - q`. -/
lemma cancellationHiding_commonDenominator :
    cancellationHidingNetlist.commonDenominator = cancellationHidingPolynomial := by
  classical
  have hUniv :
      (Finset.univ : Finset
        (cancellationHidingNetlist.Channel × cancellationHidingNetlist.Channel)) =
        {(cancellationHidingChannel, cancellationHidingChannel)} := by
    ext entry
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    exact Subsingleton.elim entry (cancellationHidingChannel, cancellationHidingChannel)
  rw [RationalNetlist.commonDenominator, hUniv, Finset.prod_singleton]
  rw [cancellationHiding_scatteringEntryModel]
  rfl

/-- The selected cleared scattering entry is the uncancelled numerator `1 - q`. -/
lemma cancellationHiding_clearedScattering_entry :
    cancellationHidingNetlist.clearedScattering
        (Outgoing.mk cancellationHidingChannel)
        (Incident.mk cancellationHidingChannel) = cancellationHidingPolynomial := by
  classical
  rw [RationalNetlist.clearedScattering]
  change (cancellationHidingNetlist.scatteringEntryModel
      cancellationHidingChannel cancellationHidingChannel).numerator *
      cancellationHidingNetlist.denominatorComplement
        cancellationHidingChannel cancellationHidingChannel = _
  rw [cancellationHiding_scatteringEntryModel]
  have hUniv :
      (Finset.univ : Finset
        (cancellationHidingNetlist.Channel × cancellationHidingNetlist.Channel)) =
        {(cancellationHidingChannel, cancellationHidingChannel)} := by
    ext entry
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    exact Subsingleton.elim entry (cancellationHidingChannel, cancellationHidingChannel)
  have hErase :
      (Finset.univ.erase (cancellationHidingChannel, cancellationHidingChannel) :
        Finset (cancellationHidingNetlist.Channel × cancellationHidingNetlist.Channel)) = ∅ := by
    rw [hUniv, Finset.erase_singleton]
  rw [RationalNetlist.denominatorComplement, hErase]
  simp [cancellationHidingEntryModel]

/-- With no internal connection, the selected lifted routing entry is zero. -/
lemma cancellationHiding_polynomialRouting_entry :
    cancellationHidingNetlist.polynomialRouting
        (Incident.mk cancellationHidingChannel)
        (Outgoing.mk cancellationHidingChannel) = 0 := by
  change MvPolynomial.C
    (cancellationHidingConnections.partialRouting
      (Incident.mk cancellationHidingChannel)
      (Outgoing.mk cancellationHidingChannel)) = 0
  rw [cancellationHidingConnections.partialRouting_entry_of_incident_not_mem_range
    cancellationHidingChannel cancellationHidingExternalChannel.2]
  simp

/-- The selected cleared feedback entry is the common denominator itself. -/
lemma cancellationHiding_clearedFeedback_entry :
    cancellationHidingNetlist.clearedFeedback
        (Incident.mk cancellationHidingChannel)
        (Incident.mk cancellationHidingChannel) = cancellationHidingPolynomial := by
  classical
  rw [RationalNetlist.clearedFeedback, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply, Matrix.mul_apply, Fintype.sum_unique]
  rw [Subsingleton.elim (default : cancellationHidingNetlist.OutgoingIndex)
    (Outgoing.mk cancellationHidingChannel)]
  simp [cancellationHiding_commonDenominator, cancellationHiding_polynomialRouting_entry]

/-- The selected polynomial external readout entry is one. -/
lemma cancellationHiding_polynomialOutputReadout_entry :
    cancellationHidingNetlist.polynomialOutputReadout
        (Outgoing.mk cancellationHidingExternalChannel)
        (Outgoing.mk cancellationHidingChannel) = 1 := by
  simp [RationalNetlist.polynomialOutputReadout, ParameterizedNetlist.outputReadout,
    PortConnectionFamily.externalOutgoingReadout, cancellationHidingExternalChannel]

/-- The selected polynomial external incident injection entry is one. -/
lemma cancellationHiding_polynomialInputExposure_entry :
    cancellationHidingNetlist.polynomialInputExposure
        (Incident.mk cancellationHidingChannel)
        (Incident.mk cancellationHidingExternalChannel) = 1 := by
  simp [RationalNetlist.polynomialInputExposure, ParameterizedNetlist.inputExposure,
    PortConnectionFamily.externalIncidentInjection, cancellationHidingExternalChannel]

/-- The selected retained external numerator is exactly `1 - q`. -/
lemma cancellationHiding_responseNumerator :
    cancellationHidingNetlist.responseNumerator
        (Outgoing.mk cancellationHidingExternalChannel)
        (Incident.mk cancellationHidingExternalChannel) =
      cancellationHidingPolynomial := by
  classical
  rw [RationalNetlist.responseNumerator, Matrix.mul_apply, Fintype.sum_unique,
    Matrix.mul_apply, Fintype.sum_unique, Matrix.mul_apply, Fintype.sum_unique,
    Matrix.adjugate_subsingleton]
  rw [Subsingleton.elim (default : cancellationHidingNetlist.OutgoingIndex)
      (Outgoing.mk cancellationHidingChannel),
    Subsingleton.elim (default : cancellationHidingNetlist.IncidentIndex)
      (Incident.mk cancellationHidingChannel)]
  simp [cancellationHiding_polynomialOutputReadout_entry,
    cancellationHiding_clearedScattering_entry,
    cancellationHiding_polynomialInputExposure_entry]

/-- The selected retained external denominator is exactly `1 - q`. -/
lemma cancellationHiding_responseDenominator :
    cancellationHidingNetlist.responseDenominator = cancellationHidingPolynomial := by
  rw [RationalNetlist.responseDenominator,
    Matrix.det_eq_elem_of_subsingleton _ (Incident.mk cancellationHidingChannel),
    cancellationHiding_clearedFeedback_entry]

/-- Direct evaluation of the retained quotient at `q = -1` gives one. -/
lemma cancellationHiding_quotient_at_neg_one :
    cancellationHidingNetlist.evaluatedResponseQuotient (fun _ => (-1 : ℂ))
        (Outgoing.mk cancellationHidingExternalChannel)
        (Incident.mk cancellationHidingExternalChannel) = 1 := by
  rw [RationalNetlist.evaluatedResponseQuotient,
    cancellationHiding_responseNumerator, cancellationHiding_responseDenominator]
  norm_num [cancellationHidingPolynomial]

/-- At `q = -1`, direct evaluation of the unique assembled scattering entry gives one. -/
lemma cancellationHiding_scattering_at_neg_one :
    cancellationHidingNetlist.toParameterizedNetlist.scatteringTransform
        (fun _ => (-1 : ℂ))
        (Outgoing.mk cancellationHidingChannel)
        (Incident.mk cancellationHidingChannel) = 1 := by
  rw [← cancellationHidingNetlist.scatteringEntryModel_eval
    (fun _ => (-1 : ℂ)) cancellationHidingChannel cancellationHidingChannel]
  rw [cancellationHiding_scatteringEntryModel]
  norm_num [cancellationHidingEntryModel, cancellationHidingPolynomial, RationalModel.eval]

/-- The unique raw routing entry is zero because the singleton port is external. -/
lemma cancellationHiding_routing_entry :
    cancellationHidingNetlist.toParameterizedNetlist.routingTransform
        (Incident.mk cancellationHidingChannel)
        (Outgoing.mk cancellationHidingChannel) = 0 := by
  change cancellationHidingConnections.partialRouting
    (Incident.mk cancellationHidingChannel)
    (Outgoing.mk cancellationHidingChannel) = 0
  exact cancellationHidingConnections.partialRouting_entry_of_incident_not_mem_range
    cancellationHidingChannel cancellationHidingExternalChannel.2 _

/-- At `q = -1`, the raw N5 feedback matrix is the identity. -/
lemma cancellationHiding_feedback_at_neg_one :
    cancellationHidingNetlist.toParameterizedNetlist.feedbackOperator
        (fun _ => (-1 : ℂ)) = 1 := by
  ext incident input
  rw [cancellationHidingNetlist.toParameterizedNetlist.feedbackOperator_eq,
    Matrix.sub_apply, Matrix.one_apply, Matrix.mul_apply, Fintype.sum_unique]
  rw [Subsingleton.elim incident (Incident.mk cancellationHidingChannel),
    Subsingleton.elim input (Incident.mk cancellationHidingChannel),
    Subsingleton.elim (default : cancellationHidingNetlist.OutgoingIndex)
      (Outgoing.mk cancellationHidingChannel)]
  simp [cancellationHiding_routing_entry, cancellationHiding_scattering_at_neg_one]

/-- The raw external readout selects the singleton outgoing channel with coefficient one. -/
lemma cancellationHiding_outputReadout_entry :
    cancellationHidingNetlist.toParameterizedNetlist.outputReadout
        (Outgoing.mk cancellationHidingExternalChannel)
        (Outgoing.mk cancellationHidingChannel) = 1 := by
  simp [ParameterizedNetlist.outputReadout, PortConnectionFamily.externalOutgoingReadout,
    cancellationHidingExternalChannel]

/-- The raw external injection selects the singleton incident channel with coefficient one. -/
lemma cancellationHiding_inputExposure_entry :
    cancellationHidingNetlist.toParameterizedNetlist.inputExposure
        (Incident.mk cancellationHidingChannel)
        (Incident.mk cancellationHidingExternalChannel) = 1 := by
  simp [ParameterizedNetlist.inputExposure, PortConnectionFamily.externalIncidentInjection,
    cancellationHidingExternalChannel]

/-- Direct expansion of the compiled singleton network at `q = -1` gives external response one.

It does not use the cleared-elimination identification theorem.
-/
lemma cancellationHiding_rawN5_at_neg_one :
    cancellationHidingNetlist.toParameterizedNetlist.unguardedResponse (fun _ => (-1 : ℂ))
        (Outgoing.mk cancellationHidingExternalChannel)
        (Incident.mk cancellationHidingExternalChannel) = 1 := by
  classical
  rw [ParameterizedNetlist.unguardedResponse, ParameterizedNetlist.totalFeedbackInverse,
    cancellationHiding_feedback_at_neg_one]
  rw [inv_one, Matrix.mul_one, Matrix.mul_apply, Fintype.sum_unique,
    Matrix.mul_apply, Fintype.sum_unique]
  rw [Subsingleton.elim (default : cancellationHidingNetlist.OutgoingIndex)
      (Outgoing.mk cancellationHidingChannel),
    Subsingleton.elim (default : cancellationHidingNetlist.IncidentIndex)
      (Incident.mk cancellationHidingChannel)]
  simp [cancellationHiding_outputReadout_entry, cancellationHiding_scattering_at_neg_one,
    cancellationHiding_inputExposure_entry]

/-- At the regular point `q = -1`, the independently expanded polynomial quotient and compiled
network response agree at the value one. -/
lemma cancellationHiding_independent_regular_anchor :
    cancellationHidingNetlist.evaluatedResponseQuotient (fun _ => (-1 : ℂ))
        (Outgoing.mk cancellationHidingExternalChannel)
        (Incident.mk cancellationHidingExternalChannel) = 1 ∧
      cancellationHidingNetlist.toParameterizedNetlist.unguardedResponse (fun _ => (-1 : ℂ))
        (Outgoing.mk cancellationHidingExternalChannel)
        (Incident.mk cancellationHidingExternalChannel) = 1 :=
  ⟨cancellationHiding_quotient_at_neg_one, cancellationHiding_rawN5_at_neg_one⟩

/-- The unreduced numerator and denominator both vanish at `q = 1`, pinning the removable
singularity that reduction must handle separately. -/
lemma cancellationHiding_singular_anchor :
    MvPolynomial.eval (fun _ : Fin 1 => (1 : ℂ))
        (cancellationHidingNetlist.responseNumerator
          (Outgoing.mk cancellationHidingExternalChannel)
          (Incident.mk cancellationHidingExternalChannel)) = 0 ∧
      MvPolynomial.eval (fun _ : Fin 1 => (1 : ℂ))
        cancellationHidingNetlist.responseDenominator = 0 := by
  rw [cancellationHiding_responseNumerator, cancellationHiding_responseDenominator]
  norm_num [cancellationHidingPolynomial]

end

end Optics.DelayTransfer
