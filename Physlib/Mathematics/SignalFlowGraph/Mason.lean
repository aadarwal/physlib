/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Mathematics.SignalFlowGraph.Combinatorics

/-!
# The graph determinant is the system determinant

## i. Overview

The alternating sum over families of pairwise non-touching loops is exactly the determinant of
`1 - G`. This is the identity that turns the combinatorics of the previous file into linear
algebra, and it is proved in full generality here.

The proof is the Leibniz expansion, read the right way. Each factor of `∏ i, (1 - G) (σ i) i`
splits as an identity part and a gain part, and expanding the product over subsets of the node
type turns one permutation into a sum over vertex sets. The identity part contributes `1` exactly
when the permutation is supported inside the chosen vertex set and `0` otherwise, so the surviving
terms are precisely the loop families of that set. What remains is a sign count: the Leibniz sign
of a permutation is `(-1)` to the size of its support plus its number of cycles, and multiplying
by `(-1)` to the size of the vertex set converts that into `(-1)` to the number of loops, because
the two exponents differ by twice the support size.

## ii. Key results

- `Physlib.SignalFlowGraph.prod_one_compl`: the identity part of the expansion selects the
  families supported in the vertex set.
- `Physlib.SignalFlowGraph.neg_one_pow_card_mul_sign`: the sign count, converting the Leibniz sign
  into `(-1)` to the number of loops.
- `Physlib.SignalFlowGraph.graphDet_eq_det`: the graph determinant is `det (1 - G)`.
- `Physlib.SignalFlowGraph.graphDet_ne_zero_iff`: a nonvanishing graph determinant is exactly
  unique solvability of the node equations.
- `Physlib.SignalFlowGraph.gain_eq_adjugate_div_graphDet`: the gain between two nodes is a
  cofactor of the system matrix divided by the graph determinant.
- `Physlib.SignalFlowGraph.gain_eq_masonGain_iff`: Mason's quotient computes the gain exactly
  when the forward-path sum computes that cofactor.

## iii. Table of contents

- A. Expanding the Leibniz product
- B. The graph determinant is the system determinant
- C. The gain as a cofactor quotient

## iv. References

No fetched source in the Concordia HVG corpus relates Mason's graph determinant to a matrix
determinant. U. Siddique, S. M. Beillahi, and S. Tahar, "On the Formal Analysis of Photonic
Signal Processing Systems", FMICS 2015, LNCS 9128, Definition 4 (p. 168) defines the determinant
only through the executable enumeration of elementary circuits, and the same is true of
S. M. Beillahi, U. Siddique, and S. Tahar, "On the Formalization of Signal-Flow-Graphs in HOL",
Technical Report, Concordia University, November 2014, and its journal successor in NSV 2016,
LNCS 10152, Definition 6 (p. 37). This file is therefore Physlib-original, and it is what
`goal.md` section H.4 S6 asks for in the bullets "graph determinant and cofactors" and "equality
with the corresponding entry of `(1 - A)⁻¹`".

The identity itself is the classical expansion of `det (1 - G)` over principal minors, read
through the cycle decomposition of permutations; it is standard mathematics, formalized here
rather than cited.

Deliberately not claimed, and stated precisely rather than left vague. The denominator half of
Mason's formula is proved here in full: the graph determinant **is** `det (1 - G)`. The numerator
half is not. `gain_eq_masonGain_iff` reduces the remaining obligation to a single identity,
`masonNumerator G s t = (systemMatrix G).adjugate t s`, and that identity is **not proved in
general**.

The route for it is known and is recorded here so it can be picked up rather than rediscovered.
Expanding `Matrix.adjugate_apply` and the Leibniz sum for the updated row leaves the permutations
`σ` with `σ t = s`; expanding each remaining factor as in section A leaves a vertex set `T` not
containing `t` with `σ` supported in `T ∪ {t}`. For such a `σ` the orbit of `t` is a cycle
through `s`, and deleting its edge from `t` back to `s` is exactly a forward path from `s` to `t`,
while the cycles off that orbit are a loop family on the untouched vertices. The correspondence in
the other direction is `σ = List.formPerm p * σ'`, using Mathlib's `List.formPerm` for the cycle
of a repetition-free list and `Equiv.Perm.toList` for its inverse. What then remains is a sign
count of the same kind as `neg_one_pow_card_mul_sign`, together with the factorisation of the
family gain along the orbit. The cost is the cycle bookkeeping, not the idea.

Until that lands, the companion regression file specializes the forward-path computation and the
proved determinant bridge on small graphs. It does not independently evaluate the loop-family
definition, so `goal.md` section I.3 rows G-01 and G-03 remain only partially exercised.

The representational limitation of the previous file also carries over: loops are node-level, so
parallel edges are not distinguished.

This file is neutral mathematics and imports no physics.

-/

@[expose] public section

namespace Physlib.SignalFlowGraph

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-!

## A. Expanding the Leibniz product

-/

/-- Summing over the loop families of a vertex set is summing over all permutations with the
others zeroed out. -/
lemma sum_loopFamilies (T : Finset ι) (f : Equiv.Perm ι → ℂ) :
    ∑ σ ∈ loopFamilies T, f σ
      = ∑ σ : Equiv.Perm ι, if σ.support ⊆ T then f σ else 0 :=
  Finset.sum_filter _ _

/-- The identity part of the Leibniz expansion contributes one exactly when the permutation is
supported inside the chosen vertex set. -/
lemma prod_one_compl (T : Finset ι) (σ : Equiv.Perm ι) :
    ∏ i ∈ Tᶜ, (1 : Matrix ι ι ℂ) (σ i) i = if σ.support ⊆ T then 1 else 0 := by
  by_cases h : σ.support ⊆ T
  · rw [if_pos h]
    refine Finset.prod_eq_one fun i hi => ?_
    have hfix : σ i = i := by
      by_contra hne
      exact (Finset.mem_compl.mp hi) (h (Equiv.Perm.mem_support.mpr hne))
    rw [Matrix.one_apply, if_pos hfix]
  · rw [if_neg h]
    obtain ⟨i, hi, hiT⟩ := Finset.not_subset.mp h
    refine Finset.prod_eq_zero (Finset.mem_compl.mpr hiT) ?_
    rw [Matrix.one_apply, if_neg (Equiv.Perm.mem_support.mp hi)]

omit [Fintype ι] [DecidableEq ι] in
/-- The gain part of the Leibniz expansion is the family gain up to the sign of the vertex
count. -/
lemma prod_neg_gain (G : Matrix ι ι ℂ) (T : Finset ι) (σ : Equiv.Perm ι) :
    ∏ i ∈ T, -(G (σ i) i) = (-1 : ℂ) ^ T.card * familyGain G T σ := by
  rw [familyGain, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => (neg_one_mul _).symm

/-- The sign count: for a family supported in the vertex set, the Leibniz sign times `(-1)` to the
vertex count is `(-1)` to the number of loops. The two exponents differ by twice the support
size. -/
lemma neg_one_pow_card_mul_sign {T : Finset ι} {σ : Equiv.Perm ι} (h : σ.support ⊆ T) :
    ((Equiv.Perm.sign σ : ℤ) : ℂ) * (-1 : ℂ) ^ T.card = (-1 : ℂ) ^ loopCount T σ := by
  have hle : σ.support.card ≤ T.card := Finset.card_le_card h
  have hsign : ((Equiv.Perm.sign σ : ℤ) : ℂ)
      = (-1 : ℂ) ^ (σ.support.card + Multiset.card σ.cycleType) := by
    rw [Equiv.Perm.sign_of_cycleType, Equiv.Perm.sum_cycleType]
    push_cast
    ring
  have hexp : σ.support.card + Multiset.card σ.cycleType + T.card
      = loopCount T σ + 2 * σ.support.card := by
    rw [loopCount]
    omega
  rw [hsign, ← pow_add, hexp, pow_add, pow_mul]
  norm_num

/-!

## B. The graph determinant is the system determinant

-/

/-- The graph determinant, the alternating sum over families of pairwise non-touching loops, is
the determinant of the system matrix `1 - G`. -/
theorem graphDet_eq_det (G : Matrix ι ι ℂ) : graphDet G = (systemMatrix G).det := by
  rw [systemMatrix, Matrix.det_apply']
  have hsplit : ∀ (σ : Equiv.Perm ι) (i : ι),
      ((1 : Matrix ι ι ℂ) - G) (σ i) i = -(G (σ i) i) + (1 : Matrix ι ι ℂ) (σ i) i := by
    intro σ i
    rw [Matrix.sub_apply]
    ring
  have hprod : ∀ σ : Equiv.Perm ι,
      ∏ i, ((1 : Matrix ι ι ℂ) - G) (σ i) i
        = ∑ T : Finset ι,
            (-1 : ℂ) ^ T.card * familyGain G T σ * (if σ.support ⊆ T then 1 else 0) := by
    intro σ
    simp_rw [hsplit σ]
    rw [Fintype.prod_add]
    exact Finset.sum_congr rfl fun T _ => by rw [prod_neg_gain, prod_one_compl]
  simp_rw [hprod, Finset.mul_sum]
  rw [Finset.sum_comm, graphDet, graphDetOn, Finset.powerset_univ]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [sum_loopFamilies]
  refine Finset.sum_congr rfl fun σ _ => ?_
  by_cases h : σ.support ⊆ T
  · rw [if_pos h, if_pos h, mul_one, ← neg_one_pow_card_mul_sign h]
    ring
  · rw [if_neg h, if_neg h, mul_zero, mul_zero]

/-- A nonvanishing graph determinant is exactly unique solvability of the node equations. -/
lemma graphDet_ne_zero_iff (G : Matrix ι ι ℂ) :
    graphDet G ≠ 0 ↔ ∀ b : ι → ℂ, ∃! x, IsNodeSolution G b x := by
  rw [graphDet_eq_det, existsUnique_isNodeSolution_iff, isUnit_iff_ne_zero]

/-!

## C. The gain as a cofactor quotient

-/

/-- The totalized inverse entry between two nodes is a cofactor divided by the graph determinant.
At a zero determinant both inverse and division are Mathlib's totalized algebraic expressions;
interpreting either side as a solved response requires `graphDet G ≠ 0`. Expressing the numerator
as a sum over forward paths is a separate identity. -/
lemma gain_eq_adjugate_div_graphDet (G : Matrix ι ι ℂ) (s t : ι) :
    gain G s t = (systemMatrix G).adjugate t s / graphDet G := by
  rw [gain, Matrix.inv_def, graphDet_eq_det, Matrix.smul_apply, Ring.inverse_eq_inv,
    div_eq_inv_mul, smul_eq_mul]

/-- Mason's quotient computes the gain exactly when the forward-path sum computes the cofactor.
This isolates the one identity that the forward-path half of Mason's formula still needs. -/
lemma gain_eq_masonGain_iff (G : Matrix ι ι ℂ) (s t : ι) (h : graphDet G ≠ 0) :
    gain G s t = masonGain G s t ↔ masonNumerator G s t = (systemMatrix G).adjugate t s := by
  rw [gain_eq_adjugate_div_graphDet, masonGain, div_eq_div_iff h h]
  exact ⟨fun hx => by field_simp at hx; linear_combination -hx,
    fun hx => by rw [hx]⟩

/-- Where the forward-path sum computes the cofactor, Mason's quotient is the gain. -/
lemma gain_eq_masonGain (G : Matrix ι ι ℂ) (s t : ι) (h : graphDet G ≠ 0)
    (hnum : masonNumerator G s t = (systemMatrix G).adjugate t s) :
    gain G s t = masonGain G s t :=
  (gain_eq_masonGain_iff G s t h).mpr hnum

end Physlib.SignalFlowGraph
