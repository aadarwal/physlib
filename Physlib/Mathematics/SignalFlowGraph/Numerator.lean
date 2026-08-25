/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Mathematics.SignalFlowGraph.Mason

/-!
# The numerator of Mason's formula in loop-family form

## i. Overview

The gain between two nodes is a ratio of two alternating sums over families of pairwise
non-touching loops. The denominator is the graph determinant of the previous file. The numerator
is the same kind of sum restricted to the families whose loop through the sink sends it to the
source, with the gain of that closing edge divided out.

The proof reuses the expansion of the previous file without change. Replacing one row of the
system matrix by a unit vector, as the adjugate does, kills every permutation that does not route
the sink to the source; the surviving ones expand exactly as before, except over the columns other
than the sink, and adjoining the sink to each vertex set turns those terms into loop families that
close through it. The extra minus sign is the one lost vertex in the exponent.

This completes Mason's gain formula as a calculation about a linear system: both the numerator and
the denominator are explicit finite sums over loop families, and their ratio is the entry of the
inverse system matrix.

What is not proved here is the repackaging of the numerator's families as forward paths. That is a
change of presentation, not of content, and it is what
`Physlib.SignalFlowGraph.masonNumerator` still needs.

## ii. Key results

- `Physlib.SignalFlowGraph.cyclicNumerator`: the numerator as a sum over the loop families that
  close through the sink.
- `Physlib.SignalFlowGraph.prod_updateRow`: the Leibniz product for the replaced row vanishes off
  the routing permutations.
- `Physlib.SignalFlowGraph.cyclicNumerator_eq_adjugate`: the numerator is the cofactor.
- `Physlib.SignalFlowGraph.gain_eq_cyclicNumerator_div_graphDet`: Mason's formula in loop-family
  form.

## iii. Table of contents

- A. Families that close through the sink
- B. The replaced row
- C. The numerator is the cofactor

## iv. References

As with the determinant identity, no fetched source in the Concordia HVG corpus relates Mason's
numerator to a cofactor; the sources define it through the executable enumeration of forward
circuits. See U. Siddique, S. M. Beillahi, and S. Tahar, "On the Formal Analysis of Photonic
Signal Processing Systems", FMICS 2015, LNCS 9128, Definitions 3-4 (p. 168), and
S. M. Beillahi, U. Siddique, and S. Tahar, NSV 2016, LNCS 10152, Definition 6 (p. 37). This file
is Physlib-original.

Deliberately not claimed. `Physlib.SignalFlowGraph.masonNumerator`, the sum over forward paths, is
still **not** proved equal to this numerator. The two differ only in how the closing family is
presented: here as a permutation that routes the sink to the source, there as the forward path
obtained by deleting the closing edge from the orbit of the sink. The remaining obligation is
therefore `masonNumerator G s t = cyclicNumerator G s t`, which is a repackaging along
`List.formPerm` and `Equiv.Perm.toList`, and it is not proved. Nothing here asserts it.

This file is neutral mathematics and imports no physics.

-/

@[expose] public section

namespace Physlib.SignalFlowGraph

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-!

## A. Families that close through the sink

-/

/-- The vertex sets containing a given node. -/
def vertexSetsContaining (t : ι) : Finset (Finset ι) := {T : Finset ι | t ∈ T}

/-- Membership in the vertex sets containing a node. -/
@[simp]
lemma mem_vertexSetsContaining {t : ι} {T : Finset ι} :
    T ∈ vertexSetsContaining t ↔ t ∈ T := by
  simp [vertexSetsContaining]

/-- The loop families of a vertex set whose loop through one node sends it to another. -/
def loopFamiliesRouting (T : Finset ι) (t s : ι) : Finset (Equiv.Perm ι) :=
  {σ ∈ loopFamilies T | σ t = s}

/-- Membership in the routed loop families. -/
@[simp]
lemma mem_loopFamiliesRouting {T : Finset ι} {t s : ι} {σ : Equiv.Perm ι} :
    σ ∈ loopFamiliesRouting T t s ↔ σ.support ⊆ T ∧ σ t = s := by
  simp [loopFamiliesRouting]

/-- Summing over the routed families is summing over the routing permutations with the others
zeroed out. -/
lemma sum_loopFamiliesRouting (T : Finset ι) (t s : ι) (f : Equiv.Perm ι → ℂ) :
    ∑ σ ∈ loopFamiliesRouting T t s, f σ
      = ∑ σ : Equiv.Perm ι, if σ t = s then (if σ.support ⊆ T then f σ else 0) else 0 := by
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext σ
  simp [loopFamiliesRouting, loopFamilies, and_comm]

/-- The numerator of Mason's formula in loop-family form: the alternating sum over the families of
pairwise non-touching loops that close through the sink, with the gain of the closing edge divided
out. -/
noncomputable def cyclicNumerator (G : Matrix ι ι ℂ) (s t : ι) : ℂ :=
  -∑ T ∈ vertexSetsContaining t, ∑ σ ∈ loopFamiliesRouting T t s,
      (-1 : ℂ) ^ loopCount T σ * familyGain G (T.erase t) σ

/-!

## B. The replaced row

-/

/-- The Leibniz product for the replaced row vanishes unless the permutation routes the sink to
the source, and is otherwise the product over the remaining columns. -/
lemma prod_updateRow (G : Matrix ι ι ℂ) (s t : ι) (σ : Equiv.Perm ι) :
    ∏ i, ((systemMatrix G).updateRow s (Pi.single t 1)) (σ i) i
      = if σ t = s then ∏ i ∈ Finset.univ.erase t, (systemMatrix G) (σ i) i else 0 := by
  by_cases h : σ t = s
  · rw [if_pos h, ← Finset.prod_erase_mul _ _ (Finset.mem_univ t), h, Matrix.updateRow_self,
      Pi.single_eq_same, mul_one]
    refine Finset.prod_congr rfl fun i hi => ?_
    have hne : σ i ≠ s := fun hcon => (Finset.mem_erase.mp hi).1 (σ.injective (hcon.trans h.symm))
    exact congrFun (Matrix.updateRow_ne hne) i
  · rw [if_neg h]
    refine Finset.prod_eq_zero (Finset.mem_univ (σ.symm s)) ?_
    rw [Equiv.apply_symm_apply, Matrix.updateRow_self]
    exact Pi.single_eq_of_ne (fun hcon => h (by rw [← hcon, Equiv.apply_symm_apply])) 1

/-- Removing the sink from the complement of a vertex set adjoins it to that set. -/
lemma sdiff_erase_eq_compl_insert (T : Finset ι) (t : ι) :
    Finset.univ.erase t \ T = (insert t T)ᶜ := by
  ext i
  simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, Finset.mem_compl,
    Finset.mem_insert, not_or]
  tauto

/-!

## C. The numerator is the cofactor

-/

/-- The numerator of Mason's formula in loop-family form is the cofactor of the system matrix. -/
theorem cyclicNumerator_eq_adjugate (G : Matrix ι ι ℂ) (s t : ι) :
    cyclicNumerator G s t = (systemMatrix G).adjugate t s := by
  have hsplit : ∀ (σ : Equiv.Perm ι) (i : ι),
      (systemMatrix G) (σ i) i = -(G (σ i) i) + (1 : Matrix ι ι ℂ) (σ i) i := by
    intro σ i
    rw [systemMatrix, Matrix.sub_apply]
    ring
  have hprod : ∀ σ : Equiv.Perm ι,
      ∏ i ∈ Finset.univ.erase t, (systemMatrix G) (σ i) i
        = ∑ T ∈ (Finset.univ.erase t).powerset,
            (-1 : ℂ) ^ T.card * familyGain G T σ *
              (if σ.support ⊆ insert t T then 1 else 0) := by
    intro σ
    simp_rw [hsplit σ]
    rw [Finset.prod_add]
    exact Finset.sum_congr rfl fun T _ => by
      rw [prod_neg_gain, sdiff_erase_eq_compl_insert T t, prod_one_compl]
  have hpull : ∀ (P : Prop) (_ : Decidable P) (u : Finset (Finset ι)) (F : Finset ι → ℂ),
      (if P then ∑ T ∈ u, F T else 0) = ∑ T ∈ u, if P then F T else 0 := by
    intro P hP u F
    by_cases h : P
    · simp only [if_pos h]
    · simp only [if_neg h, Finset.sum_const_zero]
  rw [Matrix.adjugate_apply, Matrix.det_apply']
  simp_rw [prod_updateRow, hprod, mul_ite, mul_zero, Finset.mul_sum]
  rw [Finset.sum_congr rfl fun σ _ => hpull _ _ _ _, Finset.sum_comm, cyclicNumerator,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_nbij' (i := fun T => T.erase t) (j := fun T => insert t T) ?_ ?_ ?_ ?_ ?_
  · intro T hT
    rw [Finset.mem_powerset]
    intro i hi
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hi).1, Finset.mem_univ i⟩
  · intro T hT
    exact mem_vertexSetsContaining.mpr (Finset.mem_insert_self t T)
  · intro T hT
    exact Finset.insert_erase (mem_vertexSetsContaining.mp hT)
  · intro T hT
    exact Finset.erase_insert
      (fun hcon => (Finset.mem_erase.mp (Finset.mem_powerset.mp hT hcon)).1 rfl)
  · intro T hT
    have htT : t ∈ T := mem_vertexSetsContaining.mp hT
    have hins : insert t (T.erase t) = T := Finset.insert_erase htT
    rw [sum_loopFamiliesRouting, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    by_cases hrt : σ t = s
    · rw [if_pos hrt, if_pos hrt, hins]
      by_cases hsupp : σ.support ⊆ T
      · rw [if_pos hsupp, if_pos hsupp, mul_one, Finset.card_erase_of_mem htT]
        have hpos : 0 < T.card := Finset.card_pos.mpr ⟨t, htT⟩
        have hpow : (-1 : ℂ) ^ T.card = -((-1 : ℂ) ^ (T.card - 1)) := by
          obtain ⟨n, hn⟩ : ∃ n, T.card = n + 1 := ⟨T.card - 1, by omega⟩
          rw [hn, Nat.add_sub_cancel, pow_succ]
          ring
        have hsign : ((Equiv.Perm.sign σ : ℤ) : ℂ) * (-1 : ℂ) ^ T.card
            = (-1 : ℂ) ^ loopCount T σ := neg_one_pow_card_mul_sign hsupp
        rw [hpow] at hsign
        linear_combination (familyGain G (T.erase t) σ) * hsign
      · rw [if_neg hsupp, if_neg hsupp, mul_zero, neg_zero]
    · rw [if_neg hrt, if_neg hrt, neg_zero]

/-- Mason's formula in loop-family form: the gain between two nodes is the numerator over the
graph determinant, both explicit alternating sums over families of pairwise non-touching loops. -/
theorem gain_eq_cyclicNumerator_div_graphDet (G : Matrix ι ι ℂ) (s t : ι) :
    gain G s t = cyclicNumerator G s t / graphDet G := by
  rw [gain_eq_adjugate_div_graphDet, cyclicNumerator_eq_adjugate]

end Physlib.SignalFlowGraph
