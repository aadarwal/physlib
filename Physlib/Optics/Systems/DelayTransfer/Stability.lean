/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Mathematics.ZTransform.OnePoleBIBO
public import Physlib.Optics.Systems.DelayTransfer.Poles

/-!
# Roots, degree bounds, and one-pole stability

## i. Overview

The numerator and denominator roots of an abstract `ReducedRationalResponse` are finite because
both complex polynomials are nonzero. Their distinct-root counts are bounded by the corresponding
polynomial degrees. Under `q = z⁻¹`, `zPoles` removes the formal root `q = 0` and inverts the
remaining denominator roots; `q = 0` has no finite reciprocal coordinate. This
complex-coordinate API supplies no projective interpretation. The reciprocal root set has the
same degree bound. `IsSchurStable` says literally that every
such reciprocal-coordinate denominator root lies inside the unit disk.

The BIBO equivalence is deliberately restricted to the named nonzero proper causal one-pole
class `1 / (1 - a*q)`, whose impulse response is `geometricSeq a`. Its denominator bridge proves
that reduced-response Schur stability is exactly `Physlib.ZTransform.IsSchurStable`. The
sufficiency direction passes the unit-circle region-of-convergence result to
`Physlib.ZTransform.isBIBOStable_of_sphere_subset_ROC`; it does not rederive the general BIBO
theorem. Necessity is proved for this class with explicit bounded inputs.

## ii. Key results

- `ReducedRationalResponse.zeroFinset`, `poleFinset`: finite distinct polynomial roots.
- `ReducedRationalResponse.card_zeroFinset_le_natDegree`: the zero degree bound.
- `ReducedRationalResponse.card_poleFinset_le_natDegree`: the pole degree bound.
- `ReducedRationalResponse.ncard_poles_le_natDegree`: the formal-`q` set-cardinality bound.
- `ReducedRationalResponse.zZeroFinset`, `zPoleFinset`: reciprocal-coordinate roots.
- `ReducedRationalResponse.ncard_zPoles_le_natDegree`: the reciprocal-`z` set-cardinality bound.
- `ReducedRationalResponse.IsSchurStable`: every reciprocal-coordinate pole is inside the disk.
- `ReducedRationalResponse.AllZerosInsideUnitDisk`: literal numerator-root condition.
- `ProperCausalOnePole`: the stated nonzero proper causal rational class.
- `ProperCausalOnePole.transform_impulseResponse_eq_response_eval`: its transform bridge.
- `ProperCausalOnePole.response_isSchurStable_iff_zTransform`: the Schur bridge.
- `ProperCausalOnePole.isBIBOStable_iff_isSchurStable`: BIBO/Schur equivalence for the class.

## iii. Table of contents

- A. Finite zeros and poles
- B. Reciprocal-coordinate poles and literal disk conditions
- C. The nonzero proper causal one-pole class
- D. The stated-class Schur and BIBO equivalence

## iv. References

`Physlib.ZTransform.IsBIBOStable`,
`Physlib.ZTransform.isBIBOStable_of_sphere_subset_ROC`, and
`Physlib.ZTransform.IsSchurStable` are defined or proved in
`Physlib/Mathematics/ZTransform/Stability.lean:202-236`; they are reused, not redefined. The exact
one-pole candidate set, Schur characterization, and unit-circle ROC theorem are reused from
the neutral production modules `Physlib/Mathematics/ZTransform/OnePole.lean:73-116` and
`Physlib/Mathematics/ZTransform/OnePoleBIBO.lean`.

FMICS'15 Definition 7 calls the condition that every nonzero numerator root lies inside the unit
disk a “resonance condition”, according to the audited statement in `goal.md:2284-2289`. Here
`zZeros` are exactly the finite `z`-coordinate images of nonzero formal-`q` numerator roots. This
module names only the literal predicate `AllZerosInsideUnitDisk`; it proves no physical resonance
theorem. As stated in `Poles.lean`, no generic `ReducedRationalResponse` is certified to equal a
selected N5F network response entry. Thus the generic root results below are abstract polynomial
quotient results, not network transfer-zero or transfer-pole theorems. This module also proves no
Schur/BIBO equivalence for arbitrary proper causal rational responses, no reachability or
observability theorem, and no physical-frequency, passivity, group-delay, or dispersion result.

This module implements the requested “degree and finiteness bounds” at `goal.md:2274` and the
stated-class Schur/BIBO requirement at `goal.md:2277-2278`.

-/

@[expose] public section

namespace Optics.DelayTransfer

noncomputable section

open Polynomial
open Physlib.ZTransform

namespace ReducedRationalResponse

/-!

## A. Finite zeros and poles

-/

/-- The finite set of distinct numerator roots. -/
def zeroFinset (response : ReducedRationalResponse) : Finset ℂ :=
  response.numerator.roots.toFinset

/-- The finite set of distinct reduced denominator roots. -/
def poleFinset (response : ReducedRationalResponse) : Finset ℂ :=
  response.denominator.roots.toFinset

/-- The zero set is represented exactly by the numerator root finset. -/
lemma zeros_eq_coe_zeroFinset (response : ReducedRationalResponse) :
    response.zeros = ↑response.zeroFinset := by
  ext q
  simp [zeros, zeroFinset, Polynomial.mem_roots response.numerator_ne_zero,
    Polynomial.IsRoot]

/-- The reduced denominator-root set is represented exactly by its root finset. -/
lemma poles_eq_coe_poleFinset (response : ReducedRationalResponse) :
    response.poles = ↑response.poleFinset := by
  ext q
  simp [poles, poleFinset, Polynomial.mem_roots response.denominator_ne_zero,
    Polynomial.IsRoot]

/-- The abstract numerator-root set is finite. -/
lemma finite_zeros (response : ReducedRationalResponse) : response.zeros.Finite := by
  rw [response.zeros_eq_coe_zeroFinset]
  exact response.zeroFinset.finite_toSet

/-- The abstract reduced denominator-root set is finite. -/
lemma finite_poles (response : ReducedRationalResponse) : response.poles.Finite := by
  rw [response.poles_eq_coe_poleFinset]
  exact response.poleFinset.finite_toSet

/-- The number of distinct zeros is at most the numerator degree. -/
lemma card_zeroFinset_le_natDegree (response : ReducedRationalResponse) :
    response.zeroFinset.card ≤ response.numerator.natDegree :=
  (Multiset.toFinset_card_le response.numerator.roots).trans
    (Polynomial.card_roots' response.numerator)

/-- The number of distinct poles is at most the reduced denominator degree. -/
lemma card_poleFinset_le_natDegree (response : ReducedRationalResponse) :
    response.poleFinset.card ≤ response.denominator.natDegree :=
  (Multiset.toFinset_card_le response.denominator.roots).trans
    (Polynomial.card_roots' response.denominator)

/-- The cardinality of the formal-`q` pole set is at most the reduced denominator degree. -/
lemma ncard_poles_le_natDegree (response : ReducedRationalResponse) :
    response.poles.ncard ≤ response.denominator.natDegree := by
  rw [response.poles_eq_coe_poleFinset, Set.ncard_coe_finset]
  exact response.card_poleFinset_le_natDegree

/-!

## B. Reciprocal-coordinate poles and literal disk conditions

-/

/-- Nonzero numerator roots in the `z` coordinate selected by `q = z⁻¹`.

The omitted formal root `q = 0` has no finite reciprocal `z`; this complex-coordinate API supplies
no projective interpretation.
-/
def zZeros (response : ReducedRationalResponse) : Set ℂ :=
  {z | z ≠ 0 ∧ z⁻¹ ∈ response.zeros}

/-- A finite presentation of the reciprocal-coordinate numerator roots. -/
def zZeroFinset (response : ReducedRationalResponse) : Finset ℂ :=
  (response.zeroFinset.filter fun q => q ≠ 0).image fun q => q⁻¹

/-- The reciprocal-coordinate zero set is represented exactly by `zZeroFinset`. -/
lemma zZeros_eq_coe_zZeroFinset (response : ReducedRationalResponse) :
    response.zZeros = ↑response.zZeroFinset := by
  ext z
  constructor
  · rintro ⟨hz, hZero⟩
    rw [response.zeros_eq_coe_zeroFinset] at hZero
    simp only [zZeroFinset, Finset.coe_image, Finset.coe_filter, Set.mem_image,
      Set.mem_ofPred_eq]
    exact ⟨z⁻¹, ⟨hZero, inv_ne_zero hz⟩, inv_inv z⟩
  · intro hz
    change z ∈ response.zZeroFinset at hz
    rcases Finset.mem_image.mp hz with ⟨q, hq, rfl⟩
    have hqData := Finset.mem_filter.mp hq
    constructor
    · exact inv_ne_zero hqData.2
    · rw [inv_inv, response.zeros_eq_coe_zeroFinset]
      exact hqData.1

/-- The reciprocal-coordinate numerator-root set is finite. -/
lemma finite_zZeros (response : ReducedRationalResponse) : response.zZeros.Finite := by
  rw [response.zZeros_eq_coe_zZeroFinset]
  exact response.zZeroFinset.finite_toSet

/-- The number of reciprocal-coordinate zeros is at most the numerator degree. -/
lemma card_zZeroFinset_le_natDegree (response : ReducedRationalResponse) :
    response.zZeroFinset.card ≤ response.numerator.natDegree := by
  calc
    response.zZeroFinset.card ≤
        (response.zeroFinset.filter fun q => q ≠ 0).card := Finset.card_image_le
    _ ≤ response.zeroFinset.card := Finset.card_filter_le _ _
    _ ≤ response.numerator.natDegree := response.card_zeroFinset_le_natDegree

/-- Nonzero denominator roots in the `z` coordinate selected by `q = z⁻¹`.

The omitted formal root `q = 0` has no finite reciprocal `z`; this complex-coordinate API supplies
no projective interpretation.
-/
def zPoles (response : ReducedRationalResponse) : Set ℂ :=
  {z | z ≠ 0 ∧ z⁻¹ ∈ response.poles}

/-- A finite presentation of the reciprocal-coordinate denominator roots. -/
def zPoleFinset (response : ReducedRationalResponse) : Finset ℂ :=
  (response.poleFinset.filter fun q => q ≠ 0).image fun q => q⁻¹

/-- The reciprocal-coordinate pole set is represented exactly by `zPoleFinset`. -/
lemma zPoles_eq_coe_zPoleFinset (response : ReducedRationalResponse) :
    response.zPoles = ↑response.zPoleFinset := by
  ext z
  constructor
  · rintro ⟨hz, hPole⟩
    rw [response.poles_eq_coe_poleFinset] at hPole
    simp only [zPoleFinset, Finset.coe_image, Finset.coe_filter, Set.mem_image,
      Set.mem_ofPred_eq]
    exact ⟨z⁻¹, ⟨hPole, inv_ne_zero hz⟩, inv_inv z⟩
  · intro hz
    change z ∈ response.zPoleFinset at hz
    rcases Finset.mem_image.mp hz with ⟨q, hq, rfl⟩
    have hqData := Finset.mem_filter.mp hq
    constructor
    · exact inv_ne_zero hqData.2
    · rw [inv_inv, response.poles_eq_coe_poleFinset]
      exact hqData.1

/-- The reciprocal-coordinate denominator-root set is finite. -/
lemma finite_zPoles (response : ReducedRationalResponse) : response.zPoles.Finite := by
  rw [response.zPoles_eq_coe_zPoleFinset]
  exact response.zPoleFinset.finite_toSet

/-- The number of reciprocal-coordinate poles is at most the denominator degree. -/
lemma card_zPoleFinset_le_natDegree (response : ReducedRationalResponse) :
    response.zPoleFinset.card ≤ response.denominator.natDegree := by
  calc
    response.zPoleFinset.card ≤
        (response.poleFinset.filter fun q => q ≠ 0).card := Finset.card_image_le
    _ ≤ response.poleFinset.card := Finset.card_filter_le _ _
    _ ≤ response.denominator.natDegree := response.card_poleFinset_le_natDegree

/-- The cardinality of the finite reciprocal-`z` pole set is at most the reduced denominator
degree. The omitted formal root `q = 0` cannot increase this cardinality. -/
lemma ncard_zPoles_le_natDegree (response : ReducedRationalResponse) :
    response.zPoles.ncard ≤ response.denominator.natDegree := by
  rw [response.zPoles_eq_coe_zPoleFinset, Set.ncard_coe_finset]
  exact response.card_zPoleFinset_le_natDegree

/-- FMICS'15 Theorem 2's coefficient-list premise, adapted to a reduced formal-`q` denominator.

`Finset.range (n + 1)` is the printed index set `{0, ..., n}`. The nonzero-coefficient premise is
retained literally even though `ReducedRationalResponse.denominator_ne_zero` already guarantees
that the denominator is nonzero.
-/
lemma finite_poles_and_ncard_le_of_denominator_eq_coefficients
    (response : ReducedRationalResponse) (n : ℕ) (c : ℕ → ℂ)
    (_hCoefficient : ∃ i ∈ Finset.range (n + 1), c i ≠ 0)
    (hDenominator : response.denominator =
      ∑ i ∈ Finset.range (n + 1), C (c i) * X ^ i) :
    response.poles.Finite ∧ response.poles.ncard ≤ n := by
  refine ⟨response.finite_poles, response.ncard_poles_le_natDegree.trans ?_⟩
  rw [hDenominator]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  exact (Polynomial.natDegree_C_mul_X_pow_le (c i) i).trans
    (Nat.le_of_lt_succ (Finset.mem_range.mp hi))

/-- FMICS'15 Theorem 2's finite-pole conclusion in the reciprocal coordinate `q = z⁻¹`.

`zPoles` explicitly requires `z ≠ 0`, matching the source's Definition 6. Its finite presentation
also removes the formal root `q = 0` before inversion because that root has no finite reciprocal.
These restrictions and inversion cannot create more distinct poles than the denominator degree.
-/
lemma finite_zPoles_and_ncard_le_of_denominator_eq_coefficients
    (response : ReducedRationalResponse) (n : ℕ) (c : ℕ → ℂ)
    (_hCoefficient : ∃ i ∈ Finset.range (n + 1), c i ≠ 0)
    (hDenominator : response.denominator =
      ∑ i ∈ Finset.range (n + 1), C (c i) * X ^ i) :
    response.zPoles.Finite ∧ response.zPoles.ncard ≤ n := by
  refine ⟨response.finite_zPoles, response.ncard_zPoles_le_natDegree.trans ?_⟩
  rw [hDenominator]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  exact (Polynomial.natDegree_C_mul_X_pow_le (c i) i).trans
    (Nat.le_of_lt_succ (Finset.mem_range.mp hi))

/-- An abstract reduced quotient is Schur stable when each `z`-denominator root is inside the
unit disk. -/
def IsSchurStable (response : ReducedRationalResponse) : Prop :=
  ∀ z ∈ response.zPoles, ‖z‖ < 1

/-- Literal condition that every reciprocal-coordinate numerator root lies inside the unit disk.

No physical resonance meaning is attached to this name.
-/
def AllZerosInsideUnitDisk (response : ReducedRationalResponse) : Prop :=
  ∀ z ∈ response.zZeros, ‖z‖ < 1

/-!

## C. The nonzero proper causal one-pole class

-/

/-- An abstract reduced quotient is degree-proper in formal `q` when numerator degree does not
exceed denominator degree. This condition alone is not a causality criterion under `q = z⁻¹`. -/
def IsProper (response : ReducedRationalResponse) : Prop :=
  response.numerator.natDegree ≤ response.denominator.natDegree

/-- The reduced one-pole response `1 / (1 - a*q)`. -/
def onePoleReducedResponse (a : ℂ) : ReducedRationalResponse where
  numerator := 1
  denominator := 1 - Polynomial.C a * Polynomial.X
  numerator_ne_zero := one_ne_zero
  denominator_ne_zero := by
    intro hZero
    have hEval :
        Polynomial.eval 0 (1 - Polynomial.C a * Polynomial.X) =
          Polynomial.eval 0 (0 : Polynomial ℂ) :=
      congrArg (Polynomial.eval 0) hZero
    have hOne : (1 : ℂ) = 0 := by
      simpa only [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X, mul_zero, sub_zero,
        Polynomial.eval_zero] using hEval
    exact one_ne_zero hOne
  isCoprime := isCoprime_one_left

/-- The one-pole response is proper. -/
lemma onePoleReducedResponse_isProper (a : ℂ) :
    (onePoleReducedResponse a).IsProper := by
  simp [IsProper, onePoleReducedResponse]

/-- Evaluation of the reduced one-pole response gives `(1 - a*q)⁻¹`. -/
lemma onePoleReducedResponse_eval (a q : ℂ) :
    (onePoleReducedResponse a).eval q = (1 - a * q)⁻¹ := by
  simp [onePoleReducedResponse, eval, div_eq_mul_inv]

/-- A recurrence denominator identifies the reduced response's reciprocal-coordinate poles with
the existing Z-transform candidate poles. -/
lemma zPoles_eq_candidatePoles_of_denominator_eq_recurrence
    (response : ReducedRationalResponse) (s : Finset ℕ) (α : ℕ → ℂ)
    (hDenominator : response.denominator = recurrenceDenominator s α) :
    response.zPoles = Physlib.ZTransform.candidatePoles s α := by
  rw [recurrenceCandidatePoles_eq]
  ext z
  simp [zPoles, poles, reciprocalCandidatePoles, hDenominator]

/-- Under a recurrence-denominator identification, reduced-response Schur stability is exactly
the existing Z-transform Schur predicate. -/
lemma isSchurStable_iff_zTransform_of_denominator_eq_recurrence
    (response : ReducedRationalResponse) (s : Finset ℕ) (α : ℕ → ℂ)
    (hDenominator : response.denominator = recurrenceDenominator s α) :
    response.IsSchurStable ↔ Physlib.ZTransform.IsSchurStable s α := by
  rw [IsSchurStable, Physlib.ZTransform.IsSchurStable,
    response.zPoles_eq_candidatePoles_of_denominator_eq_recurrence s α hDenominator]

end ReducedRationalResponse

/-- The stated nonzero proper causal rational class `1 / (1 - a*q)`.

The nonzero coefficient makes the existing one-pole candidate-pole characterization directly
applicable. The associated impulse response is supplied separately below and proved causal.
-/
structure ProperCausalOnePole where
  /-- The one-pole feedback and impulse-response coefficient. -/
  coefficient : ℂ
  /-- The class excludes the degenerate constant response. -/
  coefficient_ne_zero : coefficient ≠ 0

namespace ProperCausalOnePole

/-- The reduced rational response associated with the stated one-pole class. -/
def response (system : ProperCausalOnePole) : ReducedRationalResponse :=
  ReducedRationalResponse.onePoleReducedResponse system.coefficient

/-- The causal impulse response associated with the stated one-pole class. -/
def impulseResponse (system : ProperCausalOnePole) : ℤ → ℂ :=
  geometricSeq system.coefficient

/-- Every response in the stated one-pole class is proper. -/
lemma response_isProper (system : ProperCausalOnePole) : system.response.IsProper :=
  ReducedRationalResponse.onePoleReducedResponse_isProper system.coefficient

/-- Every impulse response in the stated one-pole class is causal. -/
lemma impulseResponse_isCausal (system : ProperCausalOnePole) :
    IsCausal system.impulseResponse :=
  geometricSeq_isCausal system.coefficient

/-- On its open region of convergence, the impulse response transforms to the stated rational
response evaluated with `q = z⁻¹`. -/
lemma transform_impulseResponse_eq_response_eval (system : ProperCausalOnePole)
    {z : ℂ} (hz : ‖system.coefficient‖ < ‖z‖) :
    transform system.impulseResponse z = system.response.eval z⁻¹ := by
  rw [impulseResponse, transform_geometricSeq system.coefficient_ne_zero hz,
    response, ReducedRationalResponse.onePoleReducedResponse_eval]

/-- The one-pole reduced denominator is the existing lag-one recurrence denominator. -/
lemma response_denominator_eq_recurrenceDenominator (system : ProperCausalOnePole) :
    system.response.denominator =
      recurrenceDenominator {1} (onePoleFeedback system.coefficient) := by
  simp [response, ReducedRationalResponse.onePoleReducedResponse,
    recurrenceDenominator, onePoleFeedback_one]

/-- The stated class's reciprocal-coordinate denominator roots are the Z-transform candidate
poles. -/
lemma response_zPoles_eq_candidatePoles (system : ProperCausalOnePole) :
    system.response.zPoles =
      Physlib.ZTransform.candidatePoles
        {1} (onePoleFeedback system.coefficient) :=
  system.response.zPoles_eq_candidatePoles_of_denominator_eq_recurrence
    {1} (onePoleFeedback system.coefficient)
    system.response_denominator_eq_recurrenceDenominator

/-- The stated class's reduced-response Schur predicate is exactly the existing Z-transform
Schur predicate. -/
lemma response_isSchurStable_iff_zTransform (system : ProperCausalOnePole) :
    system.response.IsSchurStable ↔
      Physlib.ZTransform.IsSchurStable
        {1} (onePoleFeedback system.coefficient) :=
  system.response.isSchurStable_iff_zTransform_of_denominator_eq_recurrence
    {1} (onePoleFeedback system.coefficient)
    system.response_denominator_eq_recurrenceDenominator

end ProperCausalOnePole

/-!

## D. The stated-class Schur and BIBO equivalence

-/

namespace ProperCausalOnePole

/-- Schur stability implies BIBO stability for the stated proper causal one-pole class.

The proof uses the existing unit-circle ROC theorem and
`Physlib.ZTransform.isBIBOStable_of_sphere_subset_ROC`.
-/
lemma isBIBOStable_of_isSchurStable (system : ProperCausalOnePole)
    (hSchur : system.response.IsSchurStable) :
    IsBIBOStable system.impulseResponse := by
  have hZTransform := system.response_isSchurStable_iff_zTransform.mp hSchur
  have hNorm :=
    (isSchurStable_onePole_iff
      system.coefficient_ne_zero).mp hZTransform
  exact isBIBOStable_of_sphere_subset_ROC system.impulseResponse
    (sphere_subset_ROC_geometricSeq system.coefficient_ne_zero hNorm)

/-- BIBO stability implies Schur stability for the stated proper causal one-pole class. -/
lemma isSchurStable_of_isBIBOStable (system : ProperCausalOnePole)
    (hBIBO : IsBIBOStable system.impulseResponse) :
    system.response.IsSchurStable := by
  have hNorm := norm_lt_one_of_isBIBOStable_geometricSeq hBIBO
  apply system.response_isSchurStable_iff_zTransform.mpr
  exact (isSchurStable_onePole_iff
    system.coefficient_ne_zero).mpr hNorm

/-- BIBO and Schur stability are equivalent for the stated proper causal one-pole class. -/
lemma isBIBOStable_iff_isSchurStable (system : ProperCausalOnePole) :
    IsBIBOStable system.impulseResponse ↔ system.response.IsSchurStable :=
  ⟨system.isSchurStable_of_isBIBOStable, system.isBIBOStable_of_isSchurStable⟩

end ProperCausalOnePole

end

end Optics.DelayTransfer
