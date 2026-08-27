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

/-!

## B. Independent polynomial and network anchors

-/

/-- The fixture's retained common denominator is exactly `1 - q`. -/
lemma cancellationHiding_commonDenominator :
    cancellationHidingNetlist.commonDenominator = cancellationHidingPolynomial := by
  classical
  simp [RationalNetlist.commonDenominator, RationalNetlist.scatteringEntryModel,
    RationalComponentFamily.aggregateEntryModel, cancellationHidingNetlist,
    cancellationHidingComponents, cancellationHidingEntryModel]

/-- The selected retained external numerator is exactly `1 - q`. -/
lemma cancellationHiding_responseNumerator :
    cancellationHidingNetlist.responseNumerator
        (Outgoing.mk cancellationHidingExternalChannel)
        (Incident.mk cancellationHidingExternalChannel) =
      cancellationHidingPolynomial := by
  classical
  simp [RationalNetlist.responseNumerator, RationalNetlist.clearedScattering,
    RationalNetlist.clearedFeedback, RationalNetlist.polynomialOutputReadout,
    RationalNetlist.polynomialInputExposure, RationalNetlist.polynomialRouting,
    RationalNetlist.denominatorComplement, cancellationHiding_commonDenominator,
    cancellationHidingExternalChannel, cancellationHidingChannel,
    cancellationHidingNetlist, cancellationHidingConnections,
    cancellationHidingComponents, cancellationHidingEntryModel,
    RationalNetlist.scatteringEntryModel, RationalComponentFamily.aggregateEntryModel]

/-- The selected retained external denominator is exactly `1 - q`. -/
lemma cancellationHiding_responseDenominator :
    cancellationHidingNetlist.responseDenominator = cancellationHidingPolynomial := by
  classical
  simp [RationalNetlist.responseDenominator, RationalNetlist.clearedFeedback,
    RationalNetlist.polynomialRouting, cancellationHiding_commonDenominator,
    cancellationHidingNetlist, cancellationHidingConnections]

/-- Direct evaluation of the retained quotient at `q = -1` gives one. -/
lemma cancellationHiding_quotient_at_neg_one :
    cancellationHidingNetlist.evaluatedResponseQuotient (fun _ => (-1 : ℂ))
        (Outgoing.mk cancellationHidingExternalChannel)
        (Incident.mk cancellationHidingExternalChannel) = 1 := by
  rw [RationalNetlist.evaluatedResponseQuotient,
    cancellationHiding_responseNumerator, cancellationHiding_responseDenominator]
  norm_num [cancellationHidingPolynomial]

/-- Direct expansion of the compiled singleton network at `q = -1` gives external response one.
It does not use the cleared-elimination identification theorem. -/
lemma cancellationHiding_rawN5_at_neg_one :
    cancellationHidingNetlist.toParameterizedNetlist.unguardedResponse (fun _ => (-1 : ℂ))
        (Outgoing.mk cancellationHidingExternalChannel)
        (Incident.mk cancellationHidingExternalChannel) = 1 := by
  classical
  simp [ParameterizedNetlist.unguardedResponse, ParameterizedNetlist.totalFeedbackInverse,
    ParameterizedNetlist.outputReadout, ParameterizedNetlist.inputExposure,
    ParameterizedNetlist.feedbackOperator, ParameterizedNetlist.routingTransform,
    ParameterizedNetlist.scatteringTransform, RationalNetlist.toParameterizedNetlist,
    ParameterizedNetlist.compile, RationalComponentFamily.toParameterizedComponentFamily,
    RationalComponentFamily.scattering, cancellationHidingNetlist,
    cancellationHidingConnections, cancellationHidingComponents,
    cancellationHidingEntryModel, cancellationHidingPolynomial, RationalModel.eval]

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
