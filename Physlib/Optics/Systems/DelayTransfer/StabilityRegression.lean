/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Systems.DelayTransfer.Stability

/-!
# Regression tests for reduced-quotient roots and one-pole stability

## i. Overview

Two instances of the stated proper causal one-pole class pin both sides of the strict Schur/BIBO
criterion. The coefficient `1/2` has formal denominator root `q = 2`, reciprocal-coordinate root
`z = 1/2`, and is stable. The coefficient `2` has reciprocal-coordinate root `z = 2` and is not
stable. The pair therefore detects a reversed `q = z⁻¹` convention and a weakened non-strict
unit-disk test.

The stable fixture also computes its numerator and denominator root sets and exact degrees. These
are abstract quotient checks: no N5F response-entry certificate is inferred.

## ii. Key definitions and results

- `stableOnePole`: the coefficient-`1/2` proper causal class member.
- `unstableOnePole`: the audited coefficient-`2` class member.
- `stableOnePole_formalPoles`: the exact formal root `{2}`.
- `stableOnePole_zPoles`: the exact reciprocal-coordinate root `{1/2}`.
- `stableOnePole_transform_one`: the exact response/impulse transform anchor.
- `stableOnePole_isBIBOStable`: the positive stability anchor.
- `unstableOnePole_not_isBIBOStable`: the strict unstable anchor.

## iii. Table of contents

- A. Stable root and degree anchors
- B. Stable and unstable criterion anchors

## iv. References and non-claims

The one-pole Z-transform candidate and Schur characterizations are in
`Physlib/Mathematics/ZTransform/StabilityRegression.lean:89-106`. The generic candidate-pole
definition and BIBO sufficiency result are in
`Physlib/Mathematics/ZTransform/Stability.lean:202-236`. Regression row S-07 requests an audited
unstable parameter case at `goal.md:2556`; the DCDR instance remains the responsibility of the
S7D lane.

No physical resonance, network transfer-pole, DCDR topology, or general proper-rational BIBO
equivalence is asserted.
-/

@[expose] public section

namespace Optics.DelayTransfer

noncomputable section

open Polynomial
open Physlib.ZTransform

/-!

## A. Stable root and degree anchors

-/

/-- The stable one-pole fixture with coefficient `1/2`. -/
def stableOnePole : ProperCausalOnePole where
  coefficient := 1 / 2
  coefficient_ne_zero := by norm_num

/-- The stable fixture's abstract numerator has no roots. -/
lemma stableOnePole_zeros : stableOnePole.response.zeros = ∅ := by
  ext q
  simp [stableOnePole, ProperCausalOnePole.response,
    ReducedRationalResponse.onePoleReducedResponse, ReducedRationalResponse.zeros]

/-- The stable fixture's formal denominator-root set is exactly `{2}`. -/
lemma stableOnePole_formalPoles : stableOnePole.response.poles = {(2 : ℂ)} := by
  ext q
  simp only [ProperCausalOnePole.response, stableOnePole,
    ReducedRationalResponse.onePoleReducedResponse, ReducedRationalResponse.poles,
    Set.mem_ofPred_eq, Set.mem_singleton_iff, eval_sub, eval_one, eval_mul, eval_C, eval_X]
  constructor
  · intro h
    linear_combination -2 * h
  · rintro rfl
    norm_num

/-- The stable fixture's reciprocal-coordinate denominator root is exactly `{1/2}`. -/
lemma stableOnePole_zPoles : stableOnePole.response.zPoles = {(1 / 2 : ℂ)} := by
  rw [stableOnePole.response_zPoles_eq_candidatePoles,
    candidatePoles_onePole stableOnePole.coefficient_ne_zero]
  rfl

/-- The stable fixture has numerator degree zero. -/
lemma stableOnePole_numerator_natDegree :
    stableOnePole.response.numerator.natDegree = 0 := by
  simp [stableOnePole, ProperCausalOnePole.response,
    ReducedRationalResponse.onePoleReducedResponse]

/-- The stable fixture has reduced denominator degree one. -/
lemma stableOnePole_denominator_natDegree :
    stableOnePole.response.denominator.natDegree = 1 := by
  change (1 - C (1 / 2 : ℂ) * X).natDegree = 1
  have hPolynomial :
      (1 - C (1 / 2 : ℂ) * X : Polynomial ℂ) =
        C (-(1 / 2 : ℂ)) * X + C 1 := by
    simp only [map_neg, map_one]
    ring
  rw [hPolynomial, natDegree_linear (by norm_num)]

/-- The literal all-numerator-roots disk condition holds for the constant numerator.

No physical resonance interpretation is attached to this vacuous root condition.
-/
lemma stableOnePole_allZerosInsideUnitDisk :
    stableOnePole.response.AllZerosInsideUnitDisk := by
  intro z hz
  rw [ReducedRationalResponse.zZeros] at hz
  exact absurd hz.2 (by simp [stableOnePole_zeros])

/-- At `z = 1`, the stable impulse transform and rational response both equal `2`. -/
lemma stableOnePole_transform_one :
    transform stableOnePole.impulseResponse 1 = 2 := by
  rw [stableOnePole.transform_impulseResponse_eq_response_eval (by
    norm_num [stableOnePole])]
  norm_num [stableOnePole, ProperCausalOnePole.response,
    ReducedRationalResponse.onePoleReducedResponse_eval]

/-!

## B. Stable and unstable criterion anchors

-/

/-- The stable fixture satisfies the reduced-quotient Schur predicate. -/
lemma stableOnePole_isSchurStable : stableOnePole.response.IsSchurStable := by
  rw [stableOnePole.response_isSchurStable_iff_zTransform,
    isSchurStable_onePole_iff stableOnePole.coefficient_ne_zero]
  norm_num [stableOnePole]

/-- The stable fixture's causal impulse response is BIBO stable. -/
lemma stableOnePole_isBIBOStable : IsBIBOStable stableOnePole.impulseResponse :=
  stableOnePole.isBIBOStable_of_isSchurStable stableOnePole_isSchurStable

/-- The audited unstable one-pole fixture with coefficient `2`. -/
def unstableOnePole : ProperCausalOnePole where
  coefficient := 2
  coefficient_ne_zero := by norm_num

/-- The unstable fixture's reciprocal-coordinate denominator root is exactly `{2}`. -/
lemma unstableOnePole_zPoles : unstableOnePole.response.zPoles = {(2 : ℂ)} := by
  rw [unstableOnePole.response_zPoles_eq_candidatePoles,
    candidatePoles_onePole unstableOnePole.coefficient_ne_zero]
  rfl

/-- The audited coefficient-`2` fixture is not Schur stable. -/
lemma unstableOnePole_not_isSchurStable : ¬ unstableOnePole.response.IsSchurStable := by
  rw [unstableOnePole.response_isSchurStable_iff_zTransform,
    isSchurStable_onePole_iff unstableOnePole.coefficient_ne_zero]
  norm_num [unstableOnePole]

/-- The audited coefficient-`2` impulse response is not BIBO stable. -/
lemma unstableOnePole_not_isBIBOStable :
    ¬ IsBIBOStable unstableOnePole.impulseResponse := by
  rw [unstableOnePole.isBIBOStable_iff_isSchurStable]
  exact unstableOnePole_not_isSchurStable

end

end Optics.DelayTransfer
