/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Mathematics.ZTransform.Stability
public import Physlib.Optics.Systems.DelayTransfer.Evaluation

/-!
# Candidate singularities and abstract polynomial cancellation

## i. Overview

This file keeps two independent schemas distinct. An `InternalDeterminantPolynomial` certifies
that a one-delay polynomial evaluates to the determinant of N5F's internal feedback operator. Its
roots are `candidateSingularities`: points where the internal network equations are singular,
whether or not a selected input and output can see that singular mode.

Separately, `ReducedRationalResponse` is an abstract coprime polynomial quotient, and
`RationalReduction` records a purely polynomial common-factor cancellation. The numerator is not
certified to be a selected N5F response numerator. The subset and equality lemmas therefore state
only relationships between the raw denominator roots and reduced denominator roots of this
abstract schema.

Finally, `recurrenceDenominator` makes the existing
`Physlib.ZTransform.candidatePoles` definition from
`Physlib/Mathematics/ZTransform/Stability.lean:226` the scalar one-delay special case, with the
required reciprocal-coordinate convention `q = z⁻¹`.

## ii. Key results

- `InternalDeterminantPolynomial`: a certified polynomial internal determinant.
- `InternalDeterminantPolynomial.candidateSingularities`: its root set in formal `q`.
- `ReducedRationalResponse`: an abstract coprime polynomial quotient.
- `RationalReduction`: explicit common-factor cancellation data.
- `RationalReduction.reducedPoles_subset_rawDenominatorRoots`: the unconditional direction.
- `RationalReduction.NoPoleCancellation`: the pointwise cancellation criterion.
- `RationalReduction.rawDenominatorRoots_subset_reducedPoles`: the gated converse.
- `recurrenceCandidatePoles_eq`: bridge to `Physlib.ZTransform.candidatePoles`.

## iii. Table of contents

- A. Polynomial internal determinants
- B. Abstract reduced quotients and explicit cancellation
- C. Abstract denominator-root criteria
- D. Bridge to finite difference equations

## iv. References

No theorem here relates a `ReducedRationalResponse` quotient to a selected network response entry.
Consequently, no reduced denominator root is identified as an actual pole of an N5F network.
That bridge requires the withheld symbolic response elimination, a response-indexed quotient
certificate, and a genuine singular-but-cancelled netlist fixture; those remain future work.

Hidden unreachable or unobservable singular modes are not ruled out. No root is called a physical
resonance, and the source term “resonance condition” for all numerator zeros inside the unit disk
is deliberately not adopted. The quotient is rational only in formal `q`, not necessarily in
physical frequency. No degree or finiteness bound, stability, BIBO, causality, passivity, or
frequency-response claim is made in this module.

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

## B. Abstract reduced quotients and explicit cancellation

-/

/-- A nonzero coprime numerator and denominator representing an abstract reduced quotient. -/
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

/-- The domain on which the abstract reduced denominator evaluates nontrivially. -/
def evaluationDomain (response : ReducedRationalResponse) : Set ℂ :=
  {q | response.denominator.eval q ≠ 0}

/-- Totalized value of a reduced response.

It has quotient-evaluation meaning only on `evaluationDomain`. No network response is certified.
-/
def eval (response : ReducedRationalResponse) (q : ℂ) : ℂ :=
  response.numerator.eval q / response.denominator.eval q

/-- Numerator roots of the abstract reduced quotient. -/
def zeros (response : ReducedRationalResponse) : Set ℂ :=
  {q | response.numerator.eval q = 0}

/-- Denominator roots of the abstract reduced quotient, after common-factor cancellation. -/
def poles (response : ReducedRationalResponse) : Set ℂ :=
  {q | response.denominator.eval q = 0}

/-- At an abstract reduced denominator root, the coprime numerator is nonzero. -/
lemma numerator_ne_zero_of_mem_poles (response : ReducedRationalResponse)
    {q : ℂ} (hq : q ∈ response.poles) : response.numerator.eval q ≠ 0 := by
  have hEither := Polynomial.aeval_ne_zero_of_isCoprime response.isCoprime q
  rw [Polynomial.aeval_def, Polynomial.aeval_def] at hEither
  apply hEither.resolve_right
  intro hDenominator
  exact hDenominator hq

end ReducedRationalResponse

/-- An explicit reduction of an abstract polynomial quotient by one common factor. -/
structure RationalReduction where
  /-- The numerator before cancellation. -/
  rawNumerator : Polynomial ℂ
  /-- The denominator before cancellation. -/
  rawDenominator : Polynomial ℂ
  /-- The common factor removed from numerator and denominator. -/
  cancelledFactor : Polynomial ℂ
  /-- The coprime quotient remaining after cancellation. -/
  reduced : ReducedRationalResponse
  /-- The cancelled factor is a nonzero formal polynomial. -/
  cancelledFactor_ne_zero : cancelledFactor ≠ 0
  /-- The raw numerator factors through the cancelled factor. -/
  rawNumerator_eq : rawNumerator = cancelledFactor * reduced.numerator
  /-- The raw denominator factors through the cancelled factor. -/
  rawDenominator_eq : rawDenominator = cancelledFactor * reduced.denominator

namespace RationalReduction

/-- Roots of the raw denominator before the abstract common factor is removed. -/
def rawDenominatorRoots (reduction : RationalReduction) : Set ℂ :=
  {q | reduction.rawDenominator.eval q = 0}

/-- Denominator roots of the abstract reduced quotient. -/
def reducedPoles (reduction : RationalReduction) : Set ℂ := reduction.reduced.poles

/-- No cancellation at `q` means that the removed common factor does not vanish at `q`. -/
def NoPoleCancellation (reduction : RationalReduction) (q : ℂ) : Prop :=
  reduction.cancelledFactor.eval q ≠ 0

/-- The unreduced denominator is a nonzero formal polynomial. -/
lemma rawDenominator_ne_zero (reduction : RationalReduction) :
    reduction.rawDenominator ≠ 0 := by
  rw [reduction.rawDenominator_eq]
  exact mul_ne_zero reduction.cancelledFactor_ne_zero reduction.reduced.denominator_ne_zero

/-!

## C. Abstract denominator-root criteria

-/

/-- Every reduced denominator root is a raw denominator root. -/
lemma reducedPoles_subset_rawDenominatorRoots (reduction : RationalReduction) :
    reduction.reducedPoles ⊆ reduction.rawDenominatorRoots := by
  intro q hq
  change reduction.reduced.denominator.eval q = 0 at hq
  change reduction.rawDenominator.eval q = 0
  rw [reduction.rawDenominator_eq, eval_mul, hq, mul_zero]

/-- Under the explicit no-cancellation criterion, every raw root remains a reduced root. -/
lemma rawDenominatorRoots_subset_reducedPoles (reduction : RationalReduction)
    (hNoCancellation : ∀ q ∈ reduction.rawDenominatorRoots,
      reduction.NoPoleCancellation q) :
    reduction.rawDenominatorRoots ⊆ reduction.reducedPoles := by
  intro q hq
  have hFactor := hNoCancellation q hq
  change reduction.rawDenominator.eval q = 0 at hq
  change reduction.reduced.denominator.eval q = 0
  rw [reduction.rawDenominator_eq, eval_mul] at hq
  exact (mul_eq_zero.mp hq).resolve_left hFactor

/-- With no cancellation, the raw and reduced denominator-root sets coincide. -/
lemma rawDenominatorRoots_eq_reducedPoles (reduction : RationalReduction)
    (hNoCancellation : ∀ q ∈ reduction.rawDenominatorRoots,
      reduction.NoPoleCancellation q) :
    reduction.rawDenominatorRoots = reduction.reducedPoles :=
  Set.Subset.antisymm
    (reduction.rawDenominatorRoots_subset_reducedPoles hNoCancellation)
    reduction.reducedPoles_subset_rawDenominatorRoots

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
