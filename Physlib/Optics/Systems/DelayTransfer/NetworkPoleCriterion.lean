/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Systems.DelayTransfer.Poles
public import Physlib.Optics.Systems.DelayTransfer.RationalElimination

/-!
# Network-level pole visibility for one formal delay

## i. Overview

This file connects the abstract polynomial-reduction schema to one selected entry of the
cleared response of a finite one-delay rational netlist. A certificate identifies the raw
numerator and denominator of a `RationalReduction` with the selected adjugate numerator and
cleared internal determinant. Its reduced denominator roots are consequently actual poles of that
selected formal response.

At a delay value where every retained component entry is regular, a root of the cleared internal
determinant is exactly failure of the N5F solve gate. If the certificate's removed factor does not
vanish there, candidate-root and actual-pole membership agree. This is an explicit sufficient
pointwise no-cancellation condition, not a necessary condition or a reachability/observability test.

## ii. Key results

- `OneDelayNetworkResponseReduction`: a selected network response and its polynomial reduction.
- `OneDelayNetworkResponseReduction.actualPoles_subset_candidateSingularities`: every actual pole
  comes from the cleared determinant.
- `OneDelayNetworkResponseReduction.candidateSingularities_eq_actualPoles`: equality under global
  no cancellation.
- `OneDelayNetworkResponseReduction.mem_actualPoles_iff_not_mem_solveDomain`: the pointwise
  network criterion at component-regular delay values.
- `OneDelayNetworkResponseReduction.reduced_eval_eq_response`: the reduced quotient agrees with
  the proof-gated N5F response.

## iii. Table of contents

- A. One-delay polynomial coordinates
- B. Network response-reduction certificates
- C. Candidate singularities and actual poles
- D. Reduced-response semantics

## iv. References

This is a Physlib-original bridge between the cleared finite-network eliminator and the abstract
reduction layer. It concerns formal `q`, not physical frequency. It assumes an explicit reduction
certificate and does not construct a greatest-common-divisor reduction, prove minimality, or
replace the no-cancellation gate by controllability, reachability, or observability. Component
denominator singularities are excluded from the N5 solve-gate equivalence. No causality, ROC,
stability, BIBO, passivity, resonance, bandwidth, or material claim is made.

-/

@[expose] public section

namespace Optics.DelayTransfer

noncomputable section

open Polynomial

universe u v w x

/-!

## A. One-delay polynomial coordinates

-/

/-- The canonical algebra equivalence from the unique formal delay variable to a polynomial
variable. -/
def oneDelayPolynomialEquiv : DelayPolynomial 1 ≃ₐ[ℂ] Polynomial ℂ :=
  MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)

/-- Evaluation is unchanged by the one-delay polynomial coordinate equivalence. -/
lemma oneDelayPolynomialEquiv_eval (polynomial : DelayPolynomial 1) (q : ℂ) :
    (oneDelayPolynomialEquiv polynomial).eval q =
      MvPolynomial.eval (fun _ : Fin 1 => q) polynomial := by
  exact MvPolynomial.eval₂_const_uniqueAlgEquiv
    (R := ℂ) (S := ℂ) (f := polynomial) (φ := RingHom.id ℂ) (a := q)

/-!

## B. Network response-reduction certificates

-/

/-- A polynomial reduction certified to be one selected entry of a finite one-delay netlist's
cleared external response. -/
structure OneDelayNetworkResponseReduction
    (netlist : RationalNetlist.{u, v, w, x} 1)
    [Fintype netlist.Channel] [Fintype netlist.ConnectedChannel]
    (output : netlist.ExternalOutgoing) (input : netlist.ExternalIncident) where
  /-- The explicit common-factor reduction of the selected response entry. -/
  reduction : RationalReduction
  /-- The raw reduction numerator is the selected cleared adjugate numerator. -/
  rawNumerator_eq : reduction.rawNumerator =
    oneDelayPolynomialEquiv (netlist.responseNumerator output input)
  /-- The raw reduction denominator is the cleared internal determinant. -/
  rawDenominator_eq : reduction.rawDenominator =
    oneDelayPolynomialEquiv netlist.responseDenominator

namespace OneDelayNetworkResponseReduction

variable {netlist : RationalNetlist.{u, v, w, x} 1}
  [Fintype netlist.Channel] [Fintype netlist.ConnectedChannel]
  {output : netlist.ExternalOutgoing} {input : netlist.ExternalIncident}

/-- A response-reduction certificate proves that the selected cleared denominator is not the zero
polynomial. -/
lemma isGenericallyWellPosed
    (certificate : OneDelayNetworkResponseReduction netlist output input) :
    netlist.IsGenericallyWellPosed := by
  intro hZero
  apply certificate.reduction.rawDenominator_ne_zero
  rw [certificate.rawDenominator_eq, hZero]
  exact map_zero oneDelayPolynomialEquiv

/-!

## C. Candidate singularities and actual poles

-/

/-- Roots of the selected response's cleared internal determinant. -/
def candidateSingularities
    (_certificate : OneDelayNetworkResponseReduction netlist output input) : Set ℂ :=
  {q | MvPolynomial.eval (fun _ : Fin 1 => q) netlist.responseDenominator = 0}

/-- Reduced denominator roots of the selected certified network response. -/
def actualPoles
    (certificate : OneDelayNetworkResponseReduction netlist output input) : Set ℂ :=
  certificate.reduction.reducedPoles

/-- The raw denominator-root set of the certificate is the selected network candidate set. -/
lemma rawDenominatorRoots_eq_candidateSingularities
    (certificate : OneDelayNetworkResponseReduction netlist output input) :
    certificate.reduction.rawDenominatorRoots = certificate.candidateSingularities := by
  ext q
  change certificate.reduction.rawDenominator.eval q = 0 ↔
    MvPolynomial.eval (fun _ : Fin 1 => q) netlist.responseDenominator = 0
  rw [certificate.rawDenominator_eq, oneDelayPolynomialEquiv_eval]

/-- Every actual pole is a candidate root of the selected cleared internal determinant. -/
lemma actualPoles_subset_candidateSingularities
    (certificate : OneDelayNetworkResponseReduction netlist output input) :
    certificate.actualPoles ⊆ certificate.candidateSingularities := by
  rw [← certificate.rawDenominatorRoots_eq_candidateSingularities]
  exact certificate.reduction.reducedPoles_subset_rawDenominatorRoots

/-- Under pointwise no cancellation, one selected candidate singularity is an actual pole. -/
lemma mem_actualPoles_of_mem_candidateSingularities
    (certificate : OneDelayNetworkResponseReduction netlist output input) {q : ℂ}
    (hCandidate : q ∈ certificate.candidateSingularities)
    (hNoCancellation : certificate.reduction.NoPoleCancellation q) :
    q ∈ certificate.actualPoles := by
  have hRaw : certificate.reduction.rawDenominator.eval q = 0 := by
    change q ∈ certificate.reduction.rawDenominatorRoots
    rwa [certificate.rawDenominatorRoots_eq_candidateSingularities]
  change certificate.reduction.reduced.denominator.eval q = 0
  rw [certificate.reduction.rawDenominator_eq, Polynomial.eval_mul] at hRaw
  exact (mul_eq_zero.mp hRaw).resolve_left hNoCancellation

/-- If no candidate root is cancelled, every candidate singularity is an actual pole. -/
lemma candidateSingularities_subset_actualPoles
    (certificate : OneDelayNetworkResponseReduction netlist output input)
    (hNoCancellation : ∀ q ∈ certificate.candidateSingularities,
      certificate.reduction.NoPoleCancellation q) :
    certificate.candidateSingularities ⊆ certificate.actualPoles := by
  rw [← certificate.rawDenominatorRoots_eq_candidateSingularities] at hNoCancellation ⊢
  exact certificate.reduction.rawDenominatorRoots_subset_reducedPoles hNoCancellation

/-- With no cancellation at any candidate root, selected candidate singularities and actual poles
coincide. -/
lemma candidateSingularities_eq_actualPoles
    (certificate : OneDelayNetworkResponseReduction netlist output input)
    (hNoCancellation : ∀ q ∈ certificate.candidateSingularities,
      certificate.reduction.NoPoleCancellation q) :
    certificate.candidateSingularities = certificate.actualPoles :=
  Set.Subset.antisymm
    (certificate.candidateSingularities_subset_actualPoles hNoCancellation)
    certificate.actualPoles_subset_candidateSingularities

/-- At a component-regular delay value, a cleared determinant root is exactly failure of the N5F
solve gate. -/
lemma mem_candidateSingularities_iff_not_mem_solveDomain
    (certificate : OneDelayNetworkResponseReduction netlist output input) (q : ℂ)
    (hRegular : netlist.ComponentEntriesRegularAt (fun _ : Fin 1 => q)) :
    q ∈ certificate.candidateSingularities ↔
      (fun _ : Fin 1 => q) ∉ netlist.toParameterizedNetlist.solveDomain := by
  change MvPolynomial.eval (fun _ : Fin 1 => q) netlist.responseDenominator = 0 ↔ _
  constructor
  · intro hZero hSolve
    exact ((netlist.eval_responseDenominator_ne_zero_iff_solveDomain
      (fun _ : Fin 1 => q) hRegular).mpr hSolve) hZero
  · intro hNotSolve
    by_contra hNonzero
    exact hNotSolve ((netlist.eval_responseDenominator_ne_zero_iff_solveDomain
      (fun _ : Fin 1 => q) hRegular).mp hNonzero)

/-- At a component-regular point with no cancellation, actual-pole membership is exactly failure
of the N5F solve gate. -/
lemma mem_actualPoles_iff_not_mem_solveDomain
    (certificate : OneDelayNetworkResponseReduction netlist output input) (q : ℂ)
    (hRegular : netlist.ComponentEntriesRegularAt (fun _ : Fin 1 => q))
    (hNoCancellation : certificate.reduction.NoPoleCancellation q) :
    q ∈ certificate.actualPoles ↔
      (fun _ : Fin 1 => q) ∉ netlist.toParameterizedNetlist.solveDomain := by
  constructor
  · intro hPole
    exact (certificate.mem_candidateSingularities_iff_not_mem_solveDomain q hRegular).mp
      (certificate.actualPoles_subset_candidateSingularities hPole)
  · intro hNotSolve
    exact certificate.mem_actualPoles_of_mem_candidateSingularities
      ((certificate.mem_candidateSingularities_iff_not_mem_solveDomain q hRegular).mpr hNotSolve)
      hNoCancellation

/-!

## D. Reduced-response semantics

-/

/-- Away from the explicitly cancelled factor, the reduced quotient equals the evaluated cleared
network quotient. -/
lemma reduced_eval_eq_evaluatedResponseQuotient
    (certificate : OneDelayNetworkResponseReduction netlist output input) (q : ℂ)
    (hNoCancellation : certificate.reduction.NoPoleCancellation q) :
    certificate.reduction.reduced.eval q =
      netlist.evaluatedResponseQuotient (fun _ : Fin 1 => q) output input := by
  rw [ReducedRationalResponse.eval, RationalNetlist.evaluatedResponseQuotient,
    ← oneDelayPolynomialEquiv_eval, ← oneDelayPolynomialEquiv_eval,
    ← certificate.rawNumerator_eq, ← certificate.rawDenominator_eq,
    certificate.reduction.rawNumerator_eq, certificate.reduction.rawDenominator_eq,
    Polynomial.eval_mul, Polynomial.eval_mul]
  exact (mul_div_mul_left _ _ hNoCancellation).symm

/-- Membership in the N5F response domain rules out cancellation of the selected response's
certified common factor. -/
lemma noPoleCancellation_of_mem_responseDomain
    (certificate : OneDelayNetworkResponseReduction netlist output input) {q : ℂ}
    (hValue : (fun _ : Fin 1 => q) ∈ netlist.responseDomain) :
    certificate.reduction.NoPoleCancellation q := by
  have hRegular := netlist.componentEntriesRegularAt_of_mem_responseDomain hValue
  have hRawDenominator : certificate.reduction.rawDenominator.eval q ≠ 0 := by
    rw [certificate.rawDenominator_eq, oneDelayPolynomialEquiv_eval]
    exact (netlist.eval_responseDenominator_ne_zero_iff_solveDomain
      (fun _ : Fin 1 => q) hRegular).mpr hValue.1
  intro hFactor
  apply hRawDenominator
  rw [certificate.reduction.rawDenominator_eq, Polynomial.eval_mul, hFactor, zero_mul]

/-- On the N5F response domain, the certified reduced quotient equals the selected proof-gated
network response entry. -/
lemma reduced_eval_eq_response
    (certificate : OneDelayNetworkResponseReduction netlist output input) {q : ℂ}
    (hValue : (fun _ : Fin 1 => q) ∈ netlist.responseDomain) :
    certificate.reduction.reduced.eval q =
      netlist.toParameterizedNetlist.response hValue output input := by
  rw [certificate.reduced_eval_eq_evaluatedResponseQuotient q
    (certificate.noPoleCancellation_of_mem_responseDomain hValue),
    netlist.evaluatedResponseQuotient_eq_response hValue]

end OneDelayNetworkResponseReduction

end

end Optics.DelayTransfer
