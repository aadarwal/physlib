/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Mathematics.ZTransform.Stability
public import Physlib.Optics.Systems.DelayTransfer.Evaluation

/-!
# Candidate singularities and poles after cancellation

## i. Overview

This file keeps three objects distinct. An `InternalDeterminantPolynomial` certifies that a
one-delay polynomial evaluates to the determinant of N5F's internal feedback operator. Its roots
are `candidateSingularities`: points where the internal network equations are singular, whether
or not the selected input and output can see that singular mode.

A `ReducedRationalResponse` has coprime, nonzero numerator and denominator polynomials. Its
denominator roots are transfer-function poles after cancellation. `RationalReduction` records an
unreduced numerator and denominator together with the common factor removed from both. Therefore
every pole after cancellation is an unreduced candidate pole, unconditionally. The converse is
proved only under `NoPoleCancellation`, which says that the removed factor has no root at the
point in question. A regression module exhibits a cancelled internal candidate.

Finally, `recurrenceDenominator` makes the existing
`Physlib.ZTransform.candidatePoles` definition from
`Physlib/Mathematics/ZTransform/Stability.lean:226` the scalar one-delay special case, with the
required reciprocal-coordinate convention `q = z⁻¹`.

## ii. Key definitions and results

- `InternalDeterminantPolynomial`: a certified polynomial internal determinant.
- `InternalDeterminantPolynomial.candidateSingularities`: its root set in formal `q`.
- `ReducedRationalResponse`: a coprime numerator/denominator response.
- `RationalReduction`: explicit common-factor cancellation data.
- `RationalReduction.actualPoles_subset_candidatePoles`: the unconditional direction.
- `RationalReduction.candidatePoles_subset_actualPoles`: the no-cancellation converse.
- `recurrenceCandidatePoles_eq`: bridge to `Physlib.ZTransform.candidatePoles`.

## iii. Table of contents

- A. Polynomial internal determinants
- B. Reduced responses and explicit cancellation
- C. Candidate-to-actual pole criteria
- D. Bridge to finite difference equations

## iv. References and non-claims

The candidate/actual distinction is required by `goal.md` section H.4 S4 and S4P. A candidate
internal singularity is not called an actual pole without the cancellation criterion. Hidden
unreachable or unobservable singular modes are not ruled out automatically. No root is called a
physical resonance, and the source term “resonance condition” for all numerator zeros inside the
unit disk is deliberately not adopted.

The response is rational in formal `q`, not necessarily in physical frequency. No stability,
BIBO, causality, passivity, or frequency-response claim is made in this module.
-/

@[expose] public section

namespace Optics.DelayTransfer

noncomputable section

open Polynomial

/-!

## A. Polynomial internal determinants

-/

universe u v w x

/-- The determinant of a one-delay netlist's internal N5F feedback operator. -/
def RationalNetlist.internalDeterminant
    (netlist : RationalNetlist.{u, v, w, x} 1)
    [Fintype netlist.Channel] [Fintype netlist.ConnectedChannel] (q : ℂ) : ℂ := by
  classical
  exact (netlist.toParameterizedNetlist.feedbackOperator (fun _ => q)).det

/-- A polynomial certified to evaluate to a one-delay network's internal determinant. -/
structure InternalDeterminantPolynomial
    (netlist : RationalNetlist.{u, v, w, x} 1)
    [Fintype netlist.Channel] [Fintype netlist.ConnectedChannel] where
  /-- The formal polynomial in the single delay variable `q`. -/
  polynomial : Polynomial ℂ
  /-- Evaluation agrees with the determinant of N5F's internal operator. -/
  evaluation_eq : ∀ q : ℂ,
    polynomial.eval q = netlist.internalDeterminant q

namespace InternalDeterminantPolynomial

variable {netlist : RationalNetlist.{u, v, w, x} 1}
  [Fintype netlist.Channel] [Fintype netlist.ConnectedChannel]

/-- Formal delay values at which the certified internal determinant vanishes. -/
def candidateSingularities (determinant : InternalDeterminantPolynomial netlist) : Set ℂ :=
  {q | determinant.polynomial.eval q = 0}

/-- A polynomial candidate singularity is exactly a singular N5F feedback operator. -/
lemma mem_candidateSingularities_iff
    (determinant : InternalDeterminantPolynomial netlist) (q : ℂ) :
    q ∈ determinant.candidateSingularities ↔
      netlist.internalDeterminant q = 0 := by
  change determinant.polynomial.eval q = 0 ↔ netlist.internalDeterminant q = 0
  rw [determinant.evaluation_eq]

end InternalDeterminantPolynomial

/-!

## B. Reduced responses and explicit cancellation

-/

/-- A nonzero coprime numerator and denominator representing a reduced one-delay response. -/
structure ReducedRationalResponse where
  /-- The numerator after cancellation. -/
  numerator : Polynomial ℂ
  /-- The denominator after cancellation. -/
  denominator : Polynomial ℂ
  /-- The reduced numerator is not the zero polynomial. -/
  numerator_ne_zero : numerator ≠ 0
  /-- The reduced denominator is not the zero polynomial. -/
  denominator_ne_zero : denominator ≠ 0
  /-- The reduced numerator and denominator have no common nonunit factor. -/
  isCoprime : IsCoprime numerator denominator

namespace ReducedRationalResponse

/-- The domain on which the reduced denominator evaluates nontrivially. -/
def evaluationDomain (response : ReducedRationalResponse) : Set ℂ :=
  {q | response.denominator.eval q ≠ 0}

/-- Totalized value of a reduced response.

It has transfer-function meaning only on `evaluationDomain`.
-/
def eval (response : ReducedRationalResponse) (q : ℂ) : ℂ :=
  response.numerator.eval q / response.denominator.eval q

/-- The zeros of a reduced transfer response. -/
def zeros (response : ReducedRationalResponse) : Set ℂ :=
  {q | response.numerator.eval q = 0}

/-- The poles of a reduced transfer response, after common-factor cancellation. -/
def poles (response : ReducedRationalResponse) : Set ℂ :=
  {q | response.denominator.eval q = 0}

/-- At a reduced denominator root, the coprime numerator is nonzero. -/
lemma numerator_ne_zero_of_mem_poles (response : ReducedRationalResponse)
    {q : ℂ} (hq : q ∈ response.poles) : response.numerator.eval q ≠ 0 := by
  have hEither := Polynomial.aeval_ne_zero_of_isCoprime response.isCoprime q
  rw [Polynomial.aeval_def, Polynomial.aeval_def] at hEither
  apply hEither.resolve_right
  intro hDenominator
  exact hDenominator hq

end ReducedRationalResponse

/-- An explicit reduction of an unreduced rational response by one common factor. -/
structure RationalReduction where
  /-- The numerator before cancellation. -/
  rawNumerator : Polynomial ℂ
  /-- The denominator before cancellation. -/
  rawDenominator : Polynomial ℂ
  /-- The common factor removed from numerator and denominator. -/
  cancelledFactor : Polynomial ℂ
  /-- The coprime response remaining after cancellation. -/
  reduced : ReducedRationalResponse
  /-- The cancelled factor is a nonzero formal polynomial. -/
  cancelledFactor_ne_zero : cancelledFactor ≠ 0
  /-- The raw numerator factors through the cancelled factor. -/
  rawNumerator_eq : rawNumerator = cancelledFactor * reduced.numerator
  /-- The raw denominator factors through the cancelled factor. -/
  rawDenominator_eq : rawDenominator = cancelledFactor * reduced.denominator

namespace RationalReduction

/-- Roots of the unreduced denominator, before input/output cancellation is removed. -/
def candidatePoles (reduction : RationalReduction) : Set ℂ :=
  {q | reduction.rawDenominator.eval q = 0}

/-- Poles of the reduced transfer response, after cancellation. -/
def actualPoles (reduction : RationalReduction) : Set ℂ := reduction.reduced.poles

/-- No pole cancellation means that the removed common factor has no root. -/
def NoPoleCancellation (reduction : RationalReduction) : Prop :=
  ∀ q : ℂ, reduction.cancelledFactor.eval q ≠ 0

/-- The unreduced denominator is a nonzero formal polynomial. -/
lemma rawDenominator_ne_zero (reduction : RationalReduction) :
    reduction.rawDenominator ≠ 0 := by
  rw [reduction.rawDenominator_eq]
  exact mul_ne_zero reduction.cancelledFactor_ne_zero reduction.reduced.denominator_ne_zero

/-!

## C. Candidate-to-actual pole criteria

-/

/-- Every transfer-function pole after cancellation is an unreduced candidate pole. -/
lemma actualPoles_subset_candidatePoles (reduction : RationalReduction) :
    reduction.actualPoles ⊆ reduction.candidatePoles := by
  intro q hq
  change reduction.reduced.denominator.eval q = 0 at hq
  change reduction.rawDenominator.eval q = 0
  rw [reduction.rawDenominator_eq, eval_mul, hq, mul_zero]

/-- Under the explicit no-cancellation criterion, every candidate pole is an actual pole. -/
lemma candidatePoles_subset_actualPoles (reduction : RationalReduction)
    (hNoCancellation : reduction.NoPoleCancellation) :
    reduction.candidatePoles ⊆ reduction.actualPoles := by
  intro q hq
  change reduction.rawDenominator.eval q = 0 at hq
  change reduction.reduced.denominator.eval q = 0
  rw [reduction.rawDenominator_eq, eval_mul] at hq
  exact (mul_eq_zero.mp hq).resolve_left (hNoCancellation q)

/-- With no cancellation, candidate and actual pole sets coincide. -/
lemma candidatePoles_eq_actualPoles (reduction : RationalReduction)
    (hNoCancellation : reduction.NoPoleCancellation) :
    reduction.candidatePoles = reduction.actualPoles :=
  Set.Subset.antisymm
    (reduction.candidatePoles_subset_actualPoles hNoCancellation)
    reduction.actualPoles_subset_candidatePoles

/-- If the unreduced denominator is the certified internal determinant polynomial, every actual
transfer pole is an internal candidate singularity. -/
lemma actualPoles_subset_candidateSingularities
    {netlist : RationalNetlist.{u, v, w, x} 1}
    [Fintype netlist.Channel] [Fintype netlist.ConnectedChannel]
    (determinant : InternalDeterminantPolynomial netlist)
    (reduction : RationalReduction)
    (hDenominator : reduction.rawDenominator = determinant.polynomial) :
    reduction.actualPoles ⊆ determinant.candidateSingularities := by
  intro q hq
  have hCandidate := reduction.actualPoles_subset_candidatePoles hq
  simpa [candidatePoles, InternalDeterminantPolynomial.candidateSingularities,
    hDenominator] using hCandidate

/-- If the internal determinant is the unreduced denominator and no factor was cancelled, every
internal candidate singularity is an actual transfer pole. -/
lemma candidateSingularities_subset_actualPoles
    {netlist : RationalNetlist.{u, v, w, x} 1}
    [Fintype netlist.Channel] [Fintype netlist.ConnectedChannel]
    (determinant : InternalDeterminantPolynomial netlist)
    (reduction : RationalReduction)
    (hDenominator : reduction.rawDenominator = determinant.polynomial)
    (hNoCancellation : reduction.NoPoleCancellation) :
    determinant.candidateSingularities ⊆ reduction.actualPoles := by
  intro q hq
  apply reduction.candidatePoles_subset_actualPoles hNoCancellation
  simpa [candidatePoles, InternalDeterminantPolynomial.candidateSingularities,
    hDenominator] using hq

end RationalReduction

/-!

## D. Bridge to finite difference equations

-/

/-- The polynomial `1 - ∑ k ∈ s, α k * q ^ k` of a finite feedback recurrence. -/
def recurrenceDenominator (s : Finset ℕ) (α : ℕ → ℂ) : Polynomial ℂ :=
  1 - ∑ k ∈ s, Polynomial.C (α k) * Polynomial.X ^ k

/-- Evaluating the recurrence denominator polynomial gives the existing delay symbol. -/
lemma eval_recurrenceDenominator (s : Finset ℕ) (α : ℕ → ℂ) (q : ℂ) :
    (recurrenceDenominator s α).eval q =
      1 - Physlib.ZTransform.delaySymbol s α q := by
  change (Polynomial.evalRingHom q) (recurrenceDenominator s α) = _
  simp only [recurrenceDenominator, Physlib.ZTransform.delaySymbol, map_sub, map_one,
    map_sum, map_mul, map_pow, Polynomial.coe_evalRingHom, eval_C, eval_X]

/-- Nonzero `z` values whose reciprocal is a root of a delay polynomial. -/
def reciprocalCandidatePoles (denominator : Polynomial ℂ) : Set ℂ :=
  {z | z ≠ 0 ∧ denominator.eval z⁻¹ = 0}

/-- Existing Z-transform candidate poles are exactly the reciprocal-coordinate roots of the
one-delay recurrence denominator polynomial. -/
lemma recurrenceCandidatePoles_eq (s : Finset ℕ) (α : ℕ → ℂ) :
    Physlib.ZTransform.candidatePoles s α =
      reciprocalCandidatePoles (recurrenceDenominator s α) := by
  ext z
  simp [Physlib.ZTransform.candidatePoles, reciprocalCandidatePoles,
    eval_recurrenceDenominator]

end

end Optics.DelayTransfer
