/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Mathlib.GroupTheory.Perm.Cycle.Concrete
public import Physlib.Mathematics.SignalFlowGraph.Numerator

/-!
# Paths as closing cycles

## i. Overview

The numerator of Mason's formula has two presentations. In
`Physlib.Mathematics.SignalFlowGraph.Numerator` it is a sum over the families of pairwise
non-touching loops that close through the sink; classically it is a sum over forward paths from
the source to the sink. The two are the same objects seen differently: a closing family is a
permutation routing the sink to the source, and deleting the closing edge from the orbit of the
sink leaves exactly a forward path.

This file proves the content of that correspondence. The gain along a repetition-free path is the
family gain of the cyclic permutation of its nodes, restricted to the nodes other than its last;
a path cycle and a loop family supported off the path are disjoint permutations; their product
follows the path on the path and the family off it; the family gain of the product splits as the
path gain times the family gain; and the product has exactly one loop more than the family.

What is **not** proved here is the index bijection that turns those facts into the identity
`masonNumerator = cyclicNumerator`. See the references section for exactly what remains.

## ii. Key results

- `Physlib.SignalFlowGraph.pathGain_eq_familyGain`: the gain along a path is the family gain of
  the cycle that closes it.
- `Physlib.SignalFlowGraph.disjoint_formPerm`: a path cycle is disjoint from a family supported
  off the path.
- `Physlib.SignalFlowGraph.mul_apply_of_mem`, `Physlib.SignalFlowGraph.mul_apply_of_notMem`: the
  product follows the path on the path and the family off it.
- `Physlib.SignalFlowGraph.familyGain_union`: the family gain of a disjoint union splits.
- `Physlib.SignalFlowGraph.loopCount_mul`: a path cycle contributes exactly one loop.

## iii. Table of contents

- A. Reading the last node of a path
- B. The gain along a path is a family gain
- C. A path cycle and a disjoint family
- D. Splitting the gain and counting the loops

## iv. References

The correspondence being formalized is the classical reading of Mason's rule, in which each
forward path from source to sink, together with a family of loops touching none of it, contributes
one term. See U. Siddique, S. M. Beillahi, and S. Tahar, "On the Formal Analysis of Photonic
Signal Processing Systems", FMICS 2015, LNCS 9128, Definitions 3-4 (p. 168). The sources
enumerate forward circuits directly and never form the closing permutation, so nothing here has a
source counterpart; this file is Physlib-original.

Deliberately not claimed, and stated exactly. The identity
`masonNumerator G s t = cyclicNumerator G s t` is **not proved**. What remains is only the index
bijection between

* triples of a forward path `p`, a vertex set `T'` disjoint from it, and a family `σ'` supported
  in `T'`; and
* pairs of a vertex set `T` containing the sink and a family `σ` supported in `T` with
  `σ t = s`,

given in one direction by `T = p.toFinset ∪ T'` and `σ = p.formPerm * σ'`. Every summand identity
that bijection has to respect is proved in this file. The inverse direction sends `σ` to the
rotation of `Equiv.Perm.toList σ t`; note that `Equiv.Perm.formPerm_toList` together with
`List.formPerm_rotate_one` recovers `p.formPerm = σ.cycleOf t` immediately, so no round trip
through `Equiv.Perm.toList` is needed, and the support condition on the residual family follows
from `σ` agreeing with `σ.cycleOf t` on that orbit. The degenerate case where the source equals
the sink, in which the path is the single node and the cycle is the identity, has to be taken
separately.

This file is neutral mathematics and imports no physics.

-/

@[expose] public section

namespace Physlib.SignalFlowGraph

open Matrix

variable {ι : Type*} [DecidableEq ι]

/-!

## A. Reading the last node of a path

-/
omit [DecidableEq ι] in
/-- Reading the last node off a nonempty list. -/
lemma eq_getLast_of_getLast? {x : ι} {l : List ι} {z : ι} (hz : (x :: l).getLast? = some z) :
    z = (x :: l).getLast (List.cons_ne_nil x l) :=
  Option.some_injective _
    (hz.symm.trans (List.getLast?_eq_some_getLast (List.cons_ne_nil x l)))

omit [DecidableEq ι] in
/-- The last node of a nonempty list belongs to it. -/
lemma mem_of_getLast? {x : ι} {l : List ι} {z : ι} (hz : (x :: l).getLast? = some z) :
    z ∈ x :: l := by
  rw [eq_getLast_of_getLast? hz]
  exact List.getLast_mem _

/-!

## B. The gain along a path is a family gain

-/

/-- The successor of the last node of a repetition-free list is its head. -/
lemma formPerm_apply_last {x : ι} {l : List ι} {z : ι} (hz : (x :: l).getLast? = some z) :
    (x :: l).formPerm z = x := by
  rw [eq_getLast_of_getLast? hz]
  exact List.formPerm_apply_getLast x l

/-- Away from the last node, adding a node at the front does not change the successor. -/
lemma formPerm_cons_apply {x y : ι} {l : List ι} (h : (x :: y :: l).Nodup) {z : ι}
    (hz : (y :: l).getLast? = some z) {i : ι} (hi : i ∈ y :: l) (hiz : i ≠ z) :
    (x :: y :: l).formPerm i = (y :: l).formPerm i := by
  rw [List.formPerm_cons_cons, Equiv.Perm.mul_apply]
  have hmem : (y :: l).formPerm i ∈ y :: l := List.formPerm_apply_mem_of_mem hi
  have hxnot : x ∉ y :: l := by simpa using (List.nodup_cons.mp h).1
  have hne_x : (y :: l).formPerm i ≠ x := fun hcon => hxnot (hcon ▸ hmem)
  have hne_y : (y :: l).formPerm i ≠ y := fun hcon =>
    hiz ((List.formPerm (y :: l)).injective (hcon.trans (formPerm_apply_last hz).symm))
  rw [Equiv.swap_apply_of_ne_of_ne hne_x hne_y]

/-- The gain along a repetition-free path is the family gain of the cycle that closes it: the
cyclic permutation of the path's nodes, restricted to the nodes other than its last. -/
lemma pathGain_eq_familyGain (G : Matrix ι ι ℂ) :
    ∀ (p : List ι) (z : ι), p.Nodup → p.getLast? = some z →
      pathGain G p = familyGain G (p.toFinset.erase z) p.formPerm := by
  intro p
  induction p with
  | nil => intro z _ hz; exact absurd hz (by simp)
  | cons x l ih =>
    match l with
    | [] =>
      intro z _ hz
      have : z = x := Option.some_injective _ hz.symm
      subst this
      simp [pathGain, familyGain]
    | (y :: l') =>
      intro z hp hz
      have hz' : (y :: l').getLast? = some z := by rwa [List.getLast?_cons_cons] at hz
      have hxnot : x ∉ y :: l' := by simpa using (List.nodup_cons.mp hp).1
      have hzmem : z ∈ y :: l' := mem_of_getLast? hz'
      have hxz : x ≠ z := fun hcon => hxnot (hcon ▸ hzmem)
      have hxnotS : x ∉ (y :: l').toFinset.erase z := fun hcon =>
        hxnot (List.mem_toFinset.mp (Finset.mem_of_mem_erase hcon))
      simp only [List.toFinset_cons] at hxnotS
      rw [pathGain_cons_cons, ih z (List.nodup_cons.mp hp).2 hz']
      simp only [familyGain, List.toFinset_cons]
      rw [Finset.erase_insert_of_ne hxz, Finset.prod_insert hxnotS,
        List.formPerm_apply_head x y l' hp]
      congr 1
      refine Finset.prod_congr rfl fun i hi => ?_
      have himem : i ∈ y :: l' := by
        rw [← List.mem_toFinset, List.toFinset_cons]
        exact Finset.mem_of_mem_erase hi
      rw [formPerm_cons_apply hp hz' himem (Finset.ne_of_mem_erase hi)]

/-!

## C. A path cycle and a disjoint family

-/

variable [Fintype ι]

/-- A cycle along a repetition-free list is disjoint from any permutation supported off it. -/
lemma disjoint_formPerm {p : List ι} {τ : Equiv.Perm ι}
    (h : Disjoint τ.support p.toFinset) : Equiv.Perm.Disjoint p.formPerm τ := by
  intro x
  by_cases hx : x ∈ p.toFinset
  · right
    by_contra hcon
    exact (Finset.disjoint_left.mp h (Equiv.Perm.mem_support.mpr hcon)) hx
  · left
    exact List.formPerm_apply_of_notMem (fun hcon => hx (List.mem_toFinset.mpr hcon))

/-- On the path, the product permutation follows the path. -/
lemma mul_apply_of_mem {p : List ι} {τ : Equiv.Perm ι}
    (h : Disjoint τ.support p.toFinset) {x : ι} (hx : x ∈ p.toFinset) :
    (p.formPerm * τ) x = p.formPerm x := by
  have : τ x = x := by
    by_contra hcon
    exact (Finset.disjoint_left.mp h (Equiv.Perm.mem_support.mpr hcon)) hx
  rw [Equiv.Perm.mul_apply, this]

/-- Off the path, the product permutation follows the loop family. -/
lemma mul_apply_of_notMem {p : List ι} {τ : Equiv.Perm ι}
    (h : Disjoint τ.support p.toFinset) {x : ι} (hx : x ∉ p.toFinset) :
    (p.formPerm * τ) x = τ x := by
  have hnot : τ x ∉ p.toFinset := by
    by_cases hxs : x ∈ τ.support
    · exact Finset.disjoint_left.mp h (Equiv.Perm.apply_mem_support.mpr hxs)
    · rw [Equiv.Perm.notMem_support.mp hxs]
      exact hx
  rw [Equiv.Perm.mul_apply,
    List.formPerm_apply_of_notMem (fun hcon => hnot (List.mem_toFinset.mpr hcon))]

/-!

## D. Splitting the gain and counting the loops

-/

omit [Fintype ι] in
/-- The family gain of a disjoint union splits along the two parts. -/
lemma familyGain_union {G : Matrix ι ι ℂ} {A B : Finset ι} (hAB : Disjoint A B)
    {ρ σ τ : Equiv.Perm ι} (hσ : ∀ i ∈ A, ρ i = σ i) (hτ : ∀ i ∈ B, ρ i = τ i) :
    familyGain G (A ∪ B) ρ = familyGain G A σ * familyGain G B τ := by
  rw [familyGain, familyGain, familyGain, Finset.prod_union hAB]
  congr 1
  · exact Finset.prod_congr rfl fun i hi => by rw [hσ i hi]
  · exact Finset.prod_congr rfl fun i hi => by rw [hτ i hi]

/-- The support of a path cycle of length at least two is the path's node set. -/
lemma support_formPerm_toFinset {p : List ι} (hp : p.Nodup) (hl : 2 ≤ p.length) :
    p.formPerm.support = p.toFinset :=
  List.support_formPerm_of_nodup p hp (fun x hcon => by simp [hcon] at hl)

/-- The number of loops of a path cycle together with a disjoint family is one more than the
family's. -/
lemma loopCount_mul {p : List ι} {T : Finset ι} {τ : Equiv.Perm ι} (hp : p.Nodup)
    (hd : Disjoint p.toFinset T) (hsupp : τ.support ⊆ T) (hne : p ≠ []) :
    loopCount (p.toFinset ∪ T) (p.formPerm * τ) = 1 + loopCount T τ := by
  have hdis : Equiv.Perm.Disjoint p.formPerm τ :=
    disjoint_formPerm (Finset.disjoint_left.mpr fun a ha hb =>
      Finset.disjoint_left.mp hd hb (hsupp ha))
  have hsuppmul : (p.formPerm * τ).support = p.formPerm.support ∪ τ.support :=
    hdis.support_mul
  have hcyc : (p.formPerm * τ).cycleType = p.formPerm.cycleType + τ.cycleType :=
    hdis.cycleType_mul
  have hcardT : τ.support.card ≤ T.card := Finset.card_le_card hsupp
  have hunion : (p.toFinset ∪ T).card = p.toFinset.card + T.card :=
    Finset.card_union_of_disjoint hd
  rcases Nat.lt_or_ge p.length 2 with hlt | hge
  · have hone : p.formPerm = 1 := (List.formPerm_eq_one_iff p hp).mpr (by omega)
    have hcardp : p.toFinset.card = 1 := by
      match p with
      | [] => exact absurd rfl hne
      | [x] => simp
      | (x :: y :: l) => simp at hlt
    rw [loopCount, loopCount, hsuppmul, hcyc, hone, hunion, hcardp]
    simp only [Equiv.Perm.support_one, Equiv.Perm.cycleType_one, Finset.empty_union, zero_add]
    omega
  · have hsp : p.formPerm.support = p.toFinset := support_formPerm_toFinset hp hge
    have hcycp : p.formPerm.cycleType = {p.length} := by
      rw [(List.isCycle_formPerm hp hge).cycleType, hsp, List.toFinset_card_of_nodup hp]
    have hcardp : p.toFinset.card = p.length := List.toFinset_card_of_nodup hp
    rw [loopCount, loopCount, hsuppmul, hcyc, hsp, hcycp, hunion, hcardp,
      Finset.card_union_of_disjoint (Finset.disjoint_left.mpr fun a ha hb =>
        Finset.disjoint_left.mp hd ha (hsupp hb))]
    simp only [Multiset.card_add, Multiset.card_singleton]
    omega

end Physlib.SignalFlowGraph
