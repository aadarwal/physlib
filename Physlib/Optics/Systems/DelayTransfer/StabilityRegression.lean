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

Three instances pin the strict Schur/BIBO criterion. Coefficient `1/2` has roots `q = 2` and
`z = 1/2` and is stable; the boundary coefficient `1` and exterior coefficient `2` have roots
`z = 1` and `z = 2` and are unstable. Together they detect a reversed `q = z⁻¹` convention and a
weakened non-strict unit-disk test.

The stable fixture also computes its numerator and denominator root sets and exact degrees. These
are abstract quotient checks: no N5F response-entry certificate is inferred.

## ii. Key results

- `stableOnePole_formalPoles`: the exact formal root `{2}`.
- `stableOnePole_zPoles`: the exact reciprocal-coordinate root `{1/2}`.
- `stableOnePole_transform_one`: the exact response/impulse transform anchor.
- `stableOnePole_isBIBOStable`: the positive stability anchor.
- `boundaryOnePole_not_isSchurStable`: the strict-boundary anchor.
- `boundaryOnePole_not_isBIBOStable`: the boundary BIBO witness.
- `unstableOnePole_not_isBIBOStable`: the strict unstable anchor.

## iii. Table of contents

- A. Stable root and degree anchors
- B. Stable and unstable criterion anchors

## iv. References

The production one-pole candidate characterization and unit-circle ROC bridge are in
`Physlib/Mathematics/ZTransform/OnePole.lean:73-116`. The generic candidate-pole definition and
BIBO sufficiency result are in `Physlib/Mathematics/ZTransform/Stability.lean:202-236`.
Regression row S-07 requests an audited unstable parameter case at `goal.md:2571`; the DCDR
instance remains the responsibility of the S7D lane.

The BIBO anchors below do not call this delay-transfer module's Schur/BIBO equivalence. The
stable anchor uses the production unit-circle ROC route directly; the unstable anchor supplies
the bounded unit impulse and exhibits unbounded powers of two in the output. The boundary anchor
specializes the neutral explicit self-convolution growth witness from `OnePoleBIBO`.

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
  rw [ReducedRationalResponse.IsSchurStable]
  intro z hz
  rw [stableOnePole_zPoles] at hz
  rw [Set.mem_singleton_iff.mp hz]
  norm_num

/-- The stable fixture's causal impulse response is BIBO stable. -/
lemma stableOnePole_isBIBOStable : IsBIBOStable stableOnePole.impulseResponse := by
  apply isBIBOStable_of_sphere_subset_ROC
  change Metric.sphere (0 : ℂ) 1 ⊆ ROC (geometricSeq (1 / 2))
  exact sphere_subset_ROC_geometricSeq (by norm_num) (by norm_num)

/-- The unit-circle boundary fixture with coefficient `1`. -/
def boundaryOnePole : ProperCausalOnePole where
  coefficient := 1
  coefficient_ne_zero := one_ne_zero

/-- The boundary fixture's reciprocal-coordinate denominator root is exactly `{1}`. -/
lemma boundaryOnePole_zPoles : boundaryOnePole.response.zPoles = {(1 : ℂ)} := by
  rw [boundaryOnePole.response_zPoles_eq_candidatePoles,
    candidatePoles_onePole boundaryOnePole.coefficient_ne_zero]
  rfl

/-- The unit-circle boundary is excluded by the strict Schur predicate. -/
lemma boundaryOnePole_not_isSchurStable : ¬ boundaryOnePole.response.IsSchurStable := by
  intro hSchur
  rw [ReducedRationalResponse.IsSchurStable] at hSchur
  have hAtOne := hSchur 1 (by rw [boundaryOnePole_zPoles]; rfl)
  norm_num at hAtOne

/-- The unit-circle boundary impulse response is not BIBO stable. -/
lemma boundaryOnePole_not_isBIBOStable :
    ¬ IsBIBOStable boundaryOnePole.impulseResponse := by
  exact not_isBIBOStable_geometricSeq_of_norm_eq_one (by norm_num [boundaryOnePole])

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
  intro hSchur
  rw [ReducedRationalResponse.IsSchurStable] at hSchur
  have hAtTwo := hSchur 2 (by rw [unstableOnePole_zPoles]; rfl)
  norm_num at hAtTwo

/-- The audited coefficient-`2` impulse response is not BIBO stable. -/
lemma unstableOnePole_not_isBIBOStable :
    ¬ IsBIBOStable unstableOnePole.impulseResponse := by
  intro hStable
  obtain ⟨bound, hBound⟩ := hStable unitImpulse isBoundedSeq_unitImpulse
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt bound (by norm_num : 1 < ‖(2 : ℂ)‖)
  have hAtN := hBound (n : ℤ)
  change ‖convolution (geometricSeq 2) unitImpulse (n : ℤ)‖ ≤ bound at hAtN
  rw [convolution_unitImpulse_right, geometricSeq_natCast, norm_pow] at hAtN
  exact (not_le_of_gt hn) hAtN

end

end Optics.DelayTransfer
