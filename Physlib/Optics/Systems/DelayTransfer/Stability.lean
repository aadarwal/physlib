/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Mathematics.ZTransform.Convolution
public import Physlib.Mathematics.ZTransform.OnePole
public import Physlib.Optics.Systems.DelayTransfer.Poles

/-!
# Roots, degree bounds, and one-pole stability

## i. Overview

The numerator and denominator roots of an abstract `ReducedRationalResponse` are finite because
both complex polynomials are nonzero. Their distinct-root counts are bounded by the corresponding
polynomial degrees. Under `q = z⁻¹`, `zPoles` removes the formal root `q = 0` and inverts the
remaining denominator roots; `q = 0` has no finite reciprocal coordinate and formally represents
`z = ∞`. Its cardinality has the same degree bound. `IsSchurStable` says literally that every
such reciprocal-coordinate denominator root lies inside the unit disk.

The BIBO equivalence is deliberately restricted to the named nonzero proper causal one-pole
class `1 / (1 - a*q)`, whose impulse response is `geometricSeq a`. Its denominator bridge proves
that reduced-response Schur stability is exactly `Physlib.ZTransform.IsSchurStable`. The
sufficiency direction passes the unit-circle region-of-convergence result to
`Physlib.ZTransform.isBIBOStable_of_sphere_subset_ROC`; it does not rederive the general BIBO
theorem. Necessity is proved for this class with explicit bounded inputs.

## ii. Key definitions and results

- `ReducedRationalResponse.zeroFinset`, `poleFinset`: finite distinct polynomial roots.
- `ReducedRationalResponse.card_zeroFinset_le_natDegree`: the zero degree bound.
- `ReducedRationalResponse.card_poleFinset_le_natDegree`: the pole degree bound.
- `ReducedRationalResponse.zZeroFinset`, `zPoleFinset`: reciprocal-coordinate roots.
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
- D. Necessity of the one-pole BIBO criterion
- E. The stated-class Schur and BIBO equivalence

## iv. References and non-claims

`Physlib.ZTransform.IsBIBOStable`,
`Physlib.ZTransform.isBIBOStable_of_sphere_subset_ROC`, and
`Physlib.ZTransform.IsSchurStable` are defined or proved in
`Physlib/Mathematics/ZTransform/Stability.lean:202-236`; they are reused, not redefined. The exact
one-pole candidate set, Schur characterization, and unit-circle ROC theorem are reused from
the neutral production module `Physlib/Mathematics/ZTransform/OnePole.lean:72-108`.

FMICS'15 Definition 7 calls the condition that every nonzero numerator root lies inside the unit
disk a “resonance condition”, according to the audited statement in `goal.md:2273-2278`. Here
`zZeros` are exactly the finite `z`-coordinate images of nonzero formal-`q` numerator roots. This
module names only the literal predicate `AllZerosInsideUnitDisk`; it proves no physical resonance
theorem. As stated in `Poles.lean`, no generic `ReducedRationalResponse` is certified to equal a
selected N5F network response entry. Thus the generic root results below are abstract polynomial
quotient results, not network transfer-zero or transfer-pole theorems. This module also proves no
Schur/BIBO equivalence for arbitrary proper causal rational responses, no reachability or
observability theorem, and no physical-frequency, passivity, group-delay, or dispersion result.

This module implements the requested “degree and finiteness bounds” and “discrete-time Schur
stability and BIBO equivalence only for a stated proper causal rational class” from
`goal.md:2263-2267`.
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

/-!

## B. Reciprocal-coordinate poles and literal disk conditions

-/

/-- Nonzero numerator roots in the `z` coordinate selected by `q = z⁻¹`.

The omitted formal root `q = 0` has no finite reciprocal `z`; it formally represents `z = ∞`.
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

The omitted formal root `q = 0` has no finite reciprocal `z`; it formally represents `z = ∞`.
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

/-- An abstract reduced quotient is proper when numerator degree does not exceed denominator
degree. -/
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
      recurrenceDenominator {1} (onePoleFeedbackCoefficients system.coefficient) := by
  simp [response, ReducedRationalResponse.onePoleReducedResponse,
    recurrenceDenominator, onePoleFeedbackCoefficients_one]

/-- The stated class's reciprocal-coordinate denominator roots are the Z-transform candidate
poles. -/
lemma response_zPoles_eq_candidatePoles (system : ProperCausalOnePole) :
    system.response.zPoles =
      Physlib.ZTransform.candidatePoles
        {1} (onePoleFeedbackCoefficients system.coefficient) :=
  system.response.zPoles_eq_candidatePoles_of_denominator_eq_recurrence
    {1} (onePoleFeedbackCoefficients system.coefficient)
    system.response_denominator_eq_recurrenceDenominator

/-- The stated class's reduced-response Schur predicate is exactly the existing Z-transform
Schur predicate. -/
lemma response_isSchurStable_iff_zTransform (system : ProperCausalOnePole) :
    system.response.IsSchurStable ↔
      Physlib.ZTransform.IsSchurStable
        {1} (onePoleFeedbackCoefficients system.coefficient) :=
  system.response.isSchurStable_iff_zTransform_of_denominator_eq_recurrence
    {1} (onePoleFeedbackCoefficients system.coefficient)
    system.response_denominator_eq_recurrenceDenominator

end ProperCausalOnePole

/-!

## D. Necessity of the one-pole BIBO criterion

-/

/-- The unit impulse is a bounded input sequence. -/
lemma isBoundedSeq_unitImpulse : IsBoundedSeq unitImpulse := by
  refine ⟨1, fun n => ?_⟩
  by_cases hn : n = 0
  · simp [unitImpulse, hn]
  · simp [unitImpulse, hn]

/-- A causal geometric sequence is bounded when its ratio has modulus at most one. -/
lemma isBoundedSeq_geometricSeq_of_norm_le_one {a : ℂ} (ha : ‖a‖ ≤ 1) :
    IsBoundedSeq (geometricSeq a) := by
  refine ⟨1, fun n => ?_⟩
  by_cases hn : n < 0
  · rw [geometricSeq_isCausal a n hn, norm_zero]
    exact zero_le_one
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_not_gt hn)
    rw [geometricSeq_natCast, norm_pow]
    exact pow_le_one₀ (norm_nonneg a) ha

/-- Outside the unit circle, the geometric impulse response is not BIBO stable. -/
lemma not_isBIBOStable_geometricSeq_of_one_lt_norm {a : ℂ} (ha : 1 < ‖a‖) :
    ¬ IsBIBOStable (geometricSeq a) := by
  intro hStable
  obtain ⟨bound, hBound⟩ := hStable unitImpulse isBoundedSeq_unitImpulse
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt bound ha
  have hAtN := hBound (n : ℤ)
  rw [convolution_unitImpulse_right, geometricSeq_natCast, norm_pow] at hAtN
  exact (not_le_of_gt hn) hAtN

/-- On the unit-circle boundary, self-convolution grows linearly in sample number. -/
lemma norm_convolution_geometricSeq_self {a : ℂ} (ha : ‖a‖ = 1) (n : ℕ) :
    ‖convolution (geometricSeq a) (geometricSeq a) (n : ℤ)‖ = n + 1 := by
  rw [convolution_natCast (geometricSeq_isCausal a)]
  have hSummand :
      (∑ k ∈ Finset.range (n + 1),
          geometricSeq a (k : ℤ) * geometricSeq a ((n - k : ℕ) : ℤ)) =
        ∑ _k ∈ Finset.range (n + 1), a ^ n := by
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [geometricSeq_natCast]
    rw [← pow_add, Nat.add_sub_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))]
  rw [hSummand]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, norm_mul, norm_pow,
    ha, one_pow, mul_one]
  simpa only [Nat.cast_add, Nat.cast_one] using Complex.norm_natCast (n + 1)

/-- A geometric impulse response on the unit-circle boundary is not BIBO stable. -/
lemma not_isBIBOStable_geometricSeq_of_norm_eq_one {a : ℂ} (ha : ‖a‖ = 1) :
    ¬ IsBIBOStable (geometricSeq a) := by
  intro hStable
  have hInput : IsBoundedSeq (geometricSeq a) :=
    isBoundedSeq_geometricSeq_of_norm_le_one ha.le
  obtain ⟨bound, hBound⟩ := hStable (geometricSeq a) hInput
  obtain ⟨n, hn⟩ := exists_nat_gt bound
  have hAtN := hBound (n : ℤ)
  rw [norm_convolution_geometricSeq_self ha] at hAtN
  linarith

/-- BIBO stability of a causal one-pole geometric response forces its pole inside the unit disk. -/
lemma norm_lt_one_of_isBIBOStable_geometricSeq {a : ℂ}
    (hStable : IsBIBOStable (geometricSeq a)) : ‖a‖ < 1 := by
  by_contra hNot
  have hAtLeast : 1 ≤ ‖a‖ := le_of_not_gt hNot
  rcases hAtLeast.eq_or_lt with hBoundary | hOutside
  · exact not_isBIBOStable_geometricSeq_of_norm_eq_one hBoundary.symm hStable
  · exact not_isBIBOStable_geometricSeq_of_one_lt_norm hOutside hStable

/-!

## E. The stated-class Schur and BIBO equivalence

-/

/-- For a nonzero one-pole proper causal response, BIBO stability is exactly the strict pole
modulus condition. -/
lemma isBIBOStable_geometricSeq_iff {a : ℂ} (ha : a ≠ 0) :
    IsBIBOStable (geometricSeq a) ↔ ‖a‖ < 1 :=
  ⟨norm_lt_one_of_isBIBOStable_geometricSeq,
    fun h => isBIBOStable_of_sphere_subset_ROC _
      (sphere_subset_ROC_geometricSeq_of_norm_lt_one ha h)⟩

/-- For the nonzero proper causal one-pole class, BIBO and Schur stability are equivalent. -/
lemma isBIBOStable_geometricSeq_iff_isSchurStable_onePole {a : ℂ} (ha : a ≠ 0) :
    IsBIBOStable (geometricSeq a) ↔
      Physlib.ZTransform.IsSchurStable
        {1} (Physlib.ZTransform.onePoleFeedbackCoefficients a) := by
  rw [isBIBOStable_geometricSeq_iff ha,
    Physlib.ZTransform.isSchurStable_onePoleFeedbackCoefficients_iff ha]

/-- For the nonzero proper causal one-pole class, absolute summability and BIBO stability are
equivalent. -/
lemma isAbsSummable_geometricSeq_iff_isBIBOStable {a : ℂ} (ha : a ≠ 0) :
    IsAbsSummable (geometricSeq a) ↔ IsBIBOStable (geometricSeq a) := by
  rw [Physlib.ZTransform.isAbsSummable_geometricSeq_iff_norm_lt_one ha,
    isBIBOStable_geometricSeq_iff ha]

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
    (isSchurStable_onePoleFeedbackCoefficients_iff
      system.coefficient_ne_zero).mp hZTransform
  exact isBIBOStable_of_sphere_subset_ROC system.impulseResponse
    (sphere_subset_ROC_geometricSeq_of_norm_lt_one system.coefficient_ne_zero hNorm)

/-- BIBO stability implies Schur stability for the stated proper causal one-pole class. -/
lemma isSchurStable_of_isBIBOStable (system : ProperCausalOnePole)
    (hBIBO : IsBIBOStable system.impulseResponse) :
    system.response.IsSchurStable := by
  have hNorm := norm_lt_one_of_isBIBOStable_geometricSeq hBIBO
  apply system.response_isSchurStable_iff_zTransform.mpr
  exact (isSchurStable_onePoleFeedbackCoefficients_iff
    system.coefficient_ne_zero).mpr hNorm

/-- BIBO and Schur stability are equivalent for the stated proper causal one-pole class. -/
lemma isBIBOStable_iff_isSchurStable (system : ProperCausalOnePole) :
    IsBIBOStable system.impulseResponse ↔ system.response.IsSchurStable :=
  ⟨system.isSchurStable_of_isBIBOStable, system.isBIBOStable_of_isSchurStable⟩

end ProperCausalOnePole

end

end Optics.DelayTransfer
