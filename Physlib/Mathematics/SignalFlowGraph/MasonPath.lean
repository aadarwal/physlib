/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Mathematics.SignalFlowGraph.PathCycle

/-!
# Mason's gain formula over forward paths

## i. Overview

This file closes Mason's rule in its classical form: the gain between two nodes is the sum, over
the forward paths from the source to the sink, of the path gain times the graph determinant of the
nodes the path does not touch, divided by the graph determinant of the whole graph.

The two presentations of the numerator are reindexed against each other. A forward path `p`
together with a loop family `σ'` supported off it gives the closing family `p.formPerm * σ'` on
the vertex set `p.toFinset ∪ T'`; conversely a family that routes the sink to the source is
recovered by taking the orbit of the source, which begins at the source and ends at the sink
because the sink is the source's predecessor. That the two constructions invert each other is
`orbitPath_mul`, and it is what makes the correspondence a bijection rather than a surjection.

The summand identities were proved in `Physlib.Mathematics.SignalFlowGraph.PathCycle`: the path
gain is the family gain of the closing cycle, the family gain of the union splits, and the closing
cycle contributes exactly one extra loop, which supplies the sign.

## ii. Key results

- `Physlib.SignalFlowGraph.orbitPath`: the forward path of a family that routes the sink back to
  the source.
- `Physlib.SignalFlowGraph.orbitPath_mul`: the orbit path recovers the forward path it came from.
- `Physlib.SignalFlowGraph.masonNumerator_eq_cyclicNumerator`: the forward-path numerator and the
  loop-family numerator agree.
- `Physlib.SignalFlowGraph.masonNumerator_eq_adjugate`: the forward-path numerator is the
  cofactor of the system matrix.
- `Physlib.SignalFlowGraph.masonGain_eq_gain`: Mason's gain formula.

## iii. Table of contents

- A. The orbit path of a routing family
- B. Recovering a forward path
- C. Reindexing the two numerators
- D. Mason's gain formula

## iv. References

Mason's rule in this form is Definition 4 (p. 168) of U. Siddique, S. M. Beillahi, and S. Tahar,
"On the Formal Analysis of Photonic Signal Processing Systems", FMICS 2015, LNCS 9128, and
Definition 6 (p. 37) of S. M. Beillahi, U. Siddique, and S. Tahar, "Formal Analysis of Engineering
Systems Based on Signal-Flow-Graph Theory", NSV 2016, LNCS 10152. Those sources define the gain by
that formula; here it is a theorem about the node equations of the graph, proved equal to the
entry of the inverse system matrix. No fetched source states that equality, so this file is
Physlib-original.

The `Equiv.Perm.toList` and `List.formPerm` machinery is Mathlib's and is used rather than
reproved; `Equiv.Perm.formPerm_toList` and `Equiv.Perm.toList_formPerm_nontrivial` are what make
the recovery direction short.

Deliberately not claimed. The enumeration is still node-level, so parallel edges are not
distinguished and regression row G-02 of `goal.md` section I.3 remains unmet; that is the subject
of a separate slice. Nothing here asserts agreement with any network or netlist semantics.

This file is neutral mathematics and imports no physics.

-/

@[expose] public section

namespace Physlib.SignalFlowGraph

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-!

## A. The orbit path of a routing family

-/
/-- The forward path of a permutation that routes the sink back to the source. -/
def orbitPath (σ : Equiv.Perm ι) (t : ι) : List ι :=
  if σ t = t then [t] else σ.toList (σ t)

/-- The source lies in the support when the sink is not fixed. -/
lemma apply_mem_support_of_ne {σ : Equiv.Perm ι} {t : ι} (h : σ t ≠ t) : σ t ∈ σ.support := by
  rw [Equiv.Perm.mem_support]
  exact fun hcon => h (σ.injective hcon)

/-- The orbit path is repetition-free. -/
lemma nodup_orbitPath (σ : Equiv.Perm ι) (t : ι) : (orbitPath σ t).Nodup := by
  by_cases h : σ t = t
  · rw [orbitPath, if_pos h]
    exact List.nodup_singleton t
  · rw [orbitPath, if_neg h]
    exact Equiv.Perm.nodup_toList _ _

/-- The orbit path is nonempty. -/
lemma orbitPath_ne_nil (σ : Equiv.Perm ι) (t : ι) : orbitPath σ t ≠ [] := by
  by_cases h : σ t = t
  · rw [orbitPath, if_pos h]
    exact List.cons_ne_nil t []
  · rw [orbitPath, if_neg h, Ne, Equiv.Perm.toList_eq_nil_iff]
    exact not_not_intro (apply_mem_support_of_ne h)

/-- The orbit path begins at the source. -/
lemma head?_orbitPath (σ : Equiv.Perm ι) (t : ι) : (orbitPath σ t).head? = some (σ t) := by
  by_cases h : σ t = t
  · rw [orbitPath, if_pos h, h]
    rfl
  · have h2 : 2 ≤ (σ.toList (σ t)).length :=
      Equiv.Perm.two_le_length_toList_iff_mem_support.mpr (apply_mem_support_of_ne h)
    have hlen : 0 < (σ.toList (σ t)).length := by omega
    rw [orbitPath, if_neg h, List.head?_eq_getElem?, List.getElem?_eq_getElem hlen]
    congr 1
    rw [Equiv.Perm.getElem_toList]
    simp

/-- Every node of the orbit path lies on the same cycle as the source. -/
lemma sameCycle_of_mem_orbitPath {σ : Equiv.Perm ι} {t : ι} (h : σ t ≠ t) {y : ι}
    (hy : y ∈ orbitPath σ t) : σ.SameCycle (σ t) y := by
  rw [orbitPath, if_neg h] at hy
  exact (Equiv.Perm.mem_toList_iff.mp hy).1

/-- The cycle of the orbit path is the cycle of the source. -/
lemma formPerm_orbitPath {σ : Equiv.Perm ι} {t : ι} (h : σ t ≠ t) :
    (orbitPath σ t).formPerm = σ.cycleOf (σ t) := by
  rw [orbitPath, if_neg h, Equiv.Perm.formPerm_toList]

omit [Fintype ι] in
/-- A cycle sends the last node of a nonempty list to its first. -/
lemma formPerm_apply_getLast_head {l : List ι} (h : l ≠ []) :
    l.formPerm (l.getLast h) = l.head h := by
  obtain ⟨u, l', rfl⟩ := List.exists_cons_of_ne_nil h
  exact List.formPerm_apply_getLast u l'

/-- The orbit path ends at the sink. -/
lemma getLast_orbitPath {σ : Equiv.Perm ι} {t : ι} (h : σ t ≠ t) :
    (orbitPath σ t).getLast (orbitPath_ne_nil σ t) = t := by
  have hmem : (orbitPath σ t).getLast (orbitPath_ne_nil σ t) ∈ orbitPath σ t := List.getLast_mem _
  have hform : (orbitPath σ t).formPerm ((orbitPath σ t).getLast (orbitPath_ne_nil σ t)) = σ t := by
    rw [formPerm_apply_getLast_head (orbitPath_ne_nil σ t)]
    have hh := head?_orbitPath σ t
    rw [List.head?_eq_some_head (orbitPath_ne_nil σ t)] at hh
    exact Option.some_injective _ hh
  rw [formPerm_orbitPath h, (sameCycle_of_mem_orbitPath h hmem).cycleOf_apply] at hform
  exact σ.injective hform

/-- The orbit path ends at the sink. -/
lemma getLast?_orbitPath (σ : Equiv.Perm ι) (t : ι) : (orbitPath σ t).getLast? = some t := by
  by_cases h : σ t = t
  · rw [orbitPath, if_pos h]
    rfl
  · rw [List.getLast?_eq_some_getLast (orbitPath_ne_nil σ t), getLast_orbitPath h]

/-!

## B. Recovering a forward path

-/

omit [Fintype ι] in
/-- Powers of a path cycle keep a node of the path on the path. -/
lemma formPerm_pow_apply_mem {p : List ι} {x : ι} (hx : x ∈ p.toFinset) (k : ℕ) :
    (p.formPerm ^ k) x ∈ p.toFinset := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    exact List.mem_toFinset.mpr (List.formPerm_apply_mem_of_mem (List.mem_toFinset.mp ih))

/-- On the path, the product permutation and the path cycle have the same powers. -/
lemma pow_mul_apply_eq {p : List ι} {τ : Equiv.Perm ι} (hd : Disjoint τ.support p.toFinset)
    {x : ι} (hx : x ∈ p.toFinset) (k : ℕ) :
    ((p.formPerm * τ) ^ k) x = (p.formPerm ^ k) x := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc ((p.formPerm * τ) ^ (k + 1)) x
        = (p.formPerm * τ) (((p.formPerm * τ) ^ k) x) := by rw [pow_succ']; rfl
      _ = (p.formPerm * τ) ((p.formPerm ^ k) x) := by rw [ih]
      _ = p.formPerm ((p.formPerm ^ k) x) := mul_apply_of_mem hd (formPerm_pow_apply_mem hx k)
      _ = ((p.formPerm : Equiv.Perm ι) ^ (k + 1)) x := by rw [pow_succ']; rfl

/-- The orbit path recovers the forward path it came from. -/
lemma orbitPath_mul {p : List ι} {τ : Equiv.Perm ι} {s t : ι} (hnd : p.Nodup)
    (hhead : p.head? = some s) (hlast : p.getLast? = some t)
    (hd : Disjoint τ.support p.toFinset) : orbitPath (p.formPerm * τ) t = p := by
  have htmem : t ∈ p.toFinset := by
    rw [List.mem_toFinset]
    exact List.mem_of_getLast? hlast
  have hsmem : s ∈ p.toFinset := by
    rw [List.mem_toFinset]
    exact List.mem_of_head? hhead
  have hne : p ≠ [] := fun hcon => by simp [hcon] at hhead
  have hgl : p.getLast hne = t := Option.some_injective _
    ((List.getLast?_eq_some_getLast hne).symm.trans hlast)
  have hhd : p.head hne = s := Option.some_injective _
    ((List.head?_eq_some_head hne).symm.trans hhead)
  have happ : (p.formPerm * τ) t = s := by
    rw [mul_apply_of_mem hd htmem, ← hgl, formPerm_apply_getLast_head hne, hhd]
  rcases Nat.lt_or_ge p.length 2 with hlt | hge
  · have h1 : p.length = 1 := by
      rcases p with _ | ⟨x, l⟩
      · exact absurd rfl hne
      · simp only [List.length_cons] at hlt ⊢
        omega
    obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp h1
    subst hx
    have htx : t = x := by simpa using htmem
    subst htx
    have hfix : τ t = t :=
      Equiv.Perm.notMem_support.mp (fun hcon => Finset.disjoint_left.mp hd hcon htmem)
    have hcollapse : ([t] : List ι).formPerm * τ = τ := by
      rw [List.formPerm_singleton, one_mul]
    rw [hcollapse, orbitPath, if_pos hfix]
  · have hsnet : s ≠ t := by
      clear happ hgl hhd hne htmem hsmem
      rcases p with _ | ⟨x, _ | ⟨y, l⟩⟩
      · simp at hge
      · simp at hge
      · intro hcon
        have hxs : x = s := by simpa using hhead
        have hgl2 : (y :: l).getLast (List.cons_ne_nil y l) = t := by
          have hcons : (x :: y :: l).getLast (List.cons_ne_nil x (y :: l))
              = (y :: l).getLast (List.cons_ne_nil y l) := List.getLast_cons _
          rw [← hcons]
          exact Option.some_injective _
            ((List.getLast?_eq_some_getLast (List.cons_ne_nil x (y :: l))).symm.trans hlast)
        have hmemt : t ∈ y :: l := hgl2 ▸ List.getLast_mem _
        have hnm : x ∉ y :: l := by simpa using (List.nodup_cons.mp hnd).1
        exact hnm (by rw [hxs, hcon]; exact hmemt)
    have happne : (p.formPerm * τ) t ≠ t := by rw [happ]; exact hsnet
    have hcyc : (p.formPerm * τ).cycleOf s = p.formPerm.cycleOf s := by
      have hdisj : Equiv.Perm.Disjoint p.formPerm τ := disjoint_formPerm hd
      rw [hdisj.cycleOf_mul_distrib s,
        (Equiv.Perm.cycleOf_eq_one_iff τ).mpr
          (Equiv.Perm.notMem_support.mp (fun hcon => Finset.disjoint_left.mp hd hcon hsmem)),
        mul_one]
    have hlist : (p.formPerm * τ).toList s = p.formPerm.toList s := by
      refine List.ext_getElem (by simp [Equiv.Perm.length_toList, hcyc]) fun n hn hn' => ?_
      rw [Equiv.Perm.getElem_toList, Equiv.Perm.getElem_toList, pow_mul_apply_eq hd hsmem]
    have hget : p.head hne = p.get ⟨0, by omega⟩ := by
      simpa using List.head_eq_getElem_zero hne
    rw [orbitPath, if_neg happne, happ, hlist, ← hhd, hget]
    exact Equiv.Perm.toList_formPerm_nontrivial p hge hnd

/-- The product routes the sink to the source. -/
lemma mul_apply_getLast {p : List ι} {τ : Equiv.Perm ι} {s t : ι}
    (hhead : p.head? = some s) (hlast : p.getLast? = some t)
    (hd : Disjoint τ.support p.toFinset) : (p.formPerm * τ) t = s := by
  have hne : p ≠ [] := fun hcon => by simp [hcon] at hhead
  have htmem : t ∈ p.toFinset := by
    rw [List.mem_toFinset]
    exact List.mem_of_getLast? hlast
  have hgl : p.getLast hne = t := Option.some_injective _
    ((List.getLast?_eq_some_getLast hne).symm.trans hlast)
  have hhd : p.head hne = s := Option.some_injective _
    ((List.head?_eq_some_head hne).symm.trans hhead)
  rw [mul_apply_of_mem hd htmem, ← hgl, formPerm_apply_getLast_head hne, hhd]

/-- On its own nodes, the orbit path cycle agrees with the permutation. -/
lemma formPerm_orbitPath_apply {σ : Equiv.Perm ι} {t x : ι} (hx : x ∈ (orbitPath σ t).toFinset) :
    (orbitPath σ t).formPerm x = σ x := by
  by_cases h : σ t = t
  · rw [orbitPath, if_pos h] at hx ⊢
    have : x = t := by simpa using hx
    rw [this, List.formPerm_singleton, Equiv.Perm.one_apply, h]
  · rw [formPerm_orbitPath h,
      (sameCycle_of_mem_orbitPath h (List.mem_toFinset.mp hx)).cycleOf_apply]

/-- The nodes of the orbit path lie in any vertex set carrying the family. -/
lemma toFinset_orbitPath_subset {σ : Equiv.Perm ι} {t : ι} {T : Finset ι} (ht : t ∈ T)
    (hsupp : σ.support ⊆ T) : (orbitPath σ t).toFinset ⊆ T := by
  intro x hx
  by_cases h : σ t = t
  · rw [orbitPath, if_pos h] at hx
    have : x = t := by simpa using hx
    rw [this]
    exact ht
  · rw [orbitPath, if_neg h, List.mem_toFinset] at hx
    obtain ⟨hsame, hmem⟩ := Equiv.Perm.mem_toList_iff.mp hx
    exact hsupp (hsame.mem_support_iff.mp hmem)

/-!

## C. Reindexing the two numerators

-/

/-- The index set of the forward-path numerator. -/
def pathIndex (s t : ι) : Finset ((_ : List ι) × ((_ : Finset ι) × Equiv.Perm ι)) :=
  (forwardPaths s t).sigma fun p => ((Finset.univ \ p.toFinset).powerset).sigma loopFamilies

/-- The index set of the loop-family numerator. -/
def familyIndex (s t : ι) : Finset ((_ : Finset ι) × Equiv.Perm ι) :=
  (vertexSetsContaining t).sigma fun T => loopFamiliesRouting T t s

/-- Membership in the forward-path index set. -/
lemma mem_pathIndex {y : (_ : List ι) × ((_ : Finset ι) × Equiv.Perm ι)} :
    y ∈ pathIndex s t ↔ y.1 ∈ forwardPaths s t ∧ y.2.1 ⊆ Finset.univ \ y.1.toFinset ∧
      y.2.2.support ⊆ y.2.1 := by
  simp [pathIndex, Finset.mem_sigma, Finset.mem_powerset]

/-- Membership in the loop-family index set. -/
lemma mem_familyIndex {z : (_ : Finset ι) × Equiv.Perm ι} :
    z ∈ familyIndex s t ↔ t ∈ z.1 ∧ z.2.support ⊆ z.1 ∧ z.2 t = s := by
  simp [familyIndex, Finset.mem_sigma]

/-- The forward-path numerator, flattened. -/
lemma masonNumerator_eq_sum (G : Matrix ι ι ℂ) (s t : ι) :
    masonNumerator G s t
      = ∑ y ∈ pathIndex s t, pathGain G y.1 *
          ((-1 : ℂ) ^ loopCount y.2.1 y.2.2 * familyGain G y.2.1 y.2.2) := by
  have h1 : ∀ p ∈ forwardPaths s t, pathGain G p * pathCofactor G p
      = ∑ x ∈ ((Finset.univ \ p.toFinset).powerset).sigma loopFamilies,
          pathGain G p * ((-1 : ℂ) ^ loopCount x.1 x.2 * familyGain G x.1 x.2) := by
    intro p _
    rw [pathCofactor, graphDetOn]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_sigma']
  rw [masonNumerator, Finset.sum_congr rfl h1, pathIndex, Finset.sum_sigma']

/-- The loop-family numerator, flattened. -/
lemma cyclicNumerator_eq_sum (G : Matrix ι ι ℂ) (s t : ι) :
    cyclicNumerator G s t
      = ∑ z ∈ familyIndex s t,
          -((-1 : ℂ) ^ loopCount z.1 z.2 * familyGain G (z.1.erase t) z.2) := by
  rw [Finset.sum_neg_distrib, cyclicNumerator, familyIndex, Finset.sum_sigma']

/-!

## D. Mason's gain formula

-/

/-- The forward-path numerator and the loop-family numerator agree. -/
lemma masonNumerator_eq_cyclicNumerator (G : Matrix ι ι ℂ) (s t : ι) :
    masonNumerator G s t = cyclicNumerator G s t := by
  rw [masonNumerator_eq_sum, cyclicNumerator_eq_sum]
  refine Finset.sum_nbij'
    (i := fun y => (⟨y.1.toFinset ∪ y.2.1, y.1.formPerm * y.2.2⟩ :
      (_ : Finset ι) × Equiv.Perm ι))
    (j := fun z => (⟨orbitPath z.2 t,
      ⟨z.1 \ (orbitPath z.2 t).toFinset, ((orbitPath z.2 t).formPerm)⁻¹ * z.2⟩⟩ :
      (_ : List ι) × ((_ : Finset ι) × Equiv.Perm ι))) ?_ ?_ ?_ ?_ ?_
  · intro y hy
    obtain ⟨hp, hT, hs⟩ := mem_pathIndex.mp hy
    obtain ⟨hnd, hhead, hlast⟩ := mem_forwardPaths_iff.mp hp
    have hdis : Disjoint y.2.2.support y.1.toFinset :=
      Finset.disjoint_left.mpr fun a ha hb => (Finset.mem_sdiff.mp (hT (hs ha))).2 hb
    refine mem_familyIndex.mpr ⟨?_, ?_, ?_⟩
    · exact Finset.mem_union_left _ (List.mem_toFinset.mpr (List.mem_of_getLast? hlast))
    · exact (Equiv.Perm.support_mul_le _ _).trans
        (Finset.union_subset_union (List.support_formPerm_le y.1) hs)
    · exact mul_apply_getLast hhead hlast hdis
  · intro z hz
    obtain ⟨ht, hsupp, hrt⟩ := mem_familyIndex.mp hz
    have hsub : (orbitPath z.2 t).toFinset ⊆ z.1 := toFinset_orbitPath_subset ht hsupp
    refine mem_pathIndex.mpr ⟨?_, ?_, ?_⟩
    · refine mem_forwardPaths_iff.mpr ⟨nodup_orbitPath _ _, ?_, getLast?_orbitPath _ _⟩
      rw [head?_orbitPath, hrt]
    · exact Finset.sdiff_subset_sdiff (Finset.subset_univ _) le_rfl
    · intro x hx
      have hxp : x ∉ (orbitPath z.2 t).toFinset := by
        intro hmem
        refine (Equiv.Perm.mem_support.mp hx) ?_
        show ((orbitPath z.2 t).formPerm⁻¹ * z.2) x = x
        rw [Equiv.Perm.mul_apply, ← formPerm_orbitPath_apply hmem]
        simp
      refine Finset.mem_sdiff.mpr ⟨?_, hxp⟩
      rcases Finset.mem_union.mp (Equiv.Perm.support_mul_le _ _ hx) with h | h
      · rw [Equiv.Perm.support_inv] at h
        exact absurd (List.support_formPerm_le _ h) hxp
      · exact hsupp h
  · intro y hy
    obtain ⟨hp, hT, hs⟩ := mem_pathIndex.mp hy
    obtain ⟨hnd, hhead, hlast⟩ := mem_forwardPaths_iff.mp hp
    have hdis : Disjoint y.2.2.support y.1.toFinset :=
      Finset.disjoint_left.mpr fun a ha hb => (Finset.mem_sdiff.mp (hT (hs ha))).2 hb
    have hrec : orbitPath (y.1.formPerm * y.2.2) t = y.1 :=
      orbitPath_mul hnd hhead hlast hdis
    have hTd : Disjoint y.1.toFinset y.2.1 :=
      Finset.disjoint_left.mpr fun a ha hb => (Finset.mem_sdiff.mp (hT hb)).2 ha
    have h1 : (y.1.toFinset ∪ y.2.1) \ y.1.toFinset = y.2.1 :=
      Finset.union_sdiff_cancel_left hTd
    have h2 : (y.1.formPerm)⁻¹ * (y.1.formPerm * y.2.2) = y.2.2 := by
      rw [← mul_assoc, inv_mul_cancel, one_mul]
    simp only [hrec, h1, h2]
  · intro z hz
    obtain ⟨ht, hsupp, hrt⟩ := mem_familyIndex.mp hz
    have hsub : (orbitPath z.2 t).toFinset ⊆ z.1 := toFinset_orbitPath_subset ht hsupp
    have h1 : (orbitPath z.2 t).toFinset ∪ (z.1 \ (orbitPath z.2 t).toFinset) = z.1 :=
      Finset.union_sdiff_of_subset hsub
    have h2 : (orbitPath z.2 t).formPerm * ((orbitPath z.2 t).formPerm⁻¹ * z.2) = z.2 := by
      rw [← mul_assoc, mul_inv_cancel, one_mul]
    simp only [h1, h2]
  · intro y hy
    obtain ⟨hp, hT, hs⟩ := mem_pathIndex.mp hy
    obtain ⟨hnd, hhead, hlast⟩ := mem_forwardPaths_iff.mp hp
    have hne : y.1 ≠ [] := fun hcon => by simp [hcon] at hhead
    have htmem : t ∈ y.1.toFinset :=
      List.mem_toFinset.mpr (List.mem_of_getLast? hlast)
    have hdis : Disjoint y.2.2.support y.1.toFinset :=
      Finset.disjoint_left.mpr fun a ha hb => (Finset.mem_sdiff.mp (hT (hs ha))).2 hb
    have hTd : Disjoint y.1.toFinset y.2.1 :=
      Finset.disjoint_left.mpr fun a ha hb => (Finset.mem_sdiff.mp (hT hb)).2 ha
    have hcount : loopCount (y.1.toFinset ∪ y.2.1) (y.1.formPerm * y.2.2)
        = 1 + loopCount y.2.1 y.2.2 := loopCount_mul hnd hTd hs hne
    have htnot : t ∉ y.2.1 := fun hcon => Finset.disjoint_left.mp hTd htmem hcon
    have herase : (y.1.toFinset ∪ y.2.1).erase t = y.1.toFinset.erase t ∪ y.2.1 := by
      rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem htnot]
    have hgain : familyGain G ((y.1.toFinset ∪ y.2.1).erase t) (y.1.formPerm * y.2.2)
        = pathGain G y.1 * familyGain G y.2.1 y.2.2 := by
      rw [herase, familyGain_union
        (Finset.disjoint_left.mpr fun a ha hb =>
          Finset.disjoint_left.mp hTd (Finset.mem_of_mem_erase ha) hb)
        (fun i hi => mul_apply_of_mem hdis (Finset.mem_of_mem_erase hi))
        (fun i hi => mul_apply_of_notMem hdis
          (fun hcon => Finset.disjoint_left.mp hTd hcon hi)),
        pathGain_eq_familyGain G y.1 t hnd hlast]
    rw [hcount, hgain, pow_add, pow_one]
    ring

/-- The forward-path numerator is the cofactor of the system matrix. -/
lemma masonNumerator_eq_adjugate (G : Matrix ι ι ℂ) (s t : ι) :
    masonNumerator G s t = (systemMatrix G).adjugate t s := by
  rw [masonNumerator_eq_cyclicNumerator, cyclicNumerator_eq_adjugate]

/-- **Mason's gain formula.** Where the graph determinant does not vanish, the gain between two
nodes is the sum over forward paths of the path gain times the graph determinant of the nodes the
path does not touch, divided by the graph determinant of the whole graph. -/
lemma masonGain_eq_gain (G : Matrix ι ι ℂ) (s t : ι) (h : graphDet G ≠ 0) :
    masonGain G s t = gain G s t :=
  (gain_eq_masonGain G s t h (masonNumerator_eq_adjugate G s t)).symm

end Physlib.SignalFlowGraph
