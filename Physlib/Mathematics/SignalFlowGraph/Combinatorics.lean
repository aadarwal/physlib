/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Mathematics.SignalFlowGraph.Basic

/-!
# Loops, forward paths, and the graph determinant

## i. Overview

A family of pairwise non-touching loops on a vertex set `T` is carried here by a permutation of
the node type whose support is contained in `T`. That encoding is exact rather than convenient.
The cycles of a permutation are automatically vertex-disjoint, so "pairwise non-touching" is not a
side condition to be checked but a property of the representation; the vertices of `T` that the
permutation fixes are the self-loops of the family; and the loop gains are read off as the
products along the cycles. The number of loops is therefore the number of fixed points inside `T`
plus the number of nontrivial cycles.

The graph determinant is the alternating sum `1 - Σ L₁ + Σ L₂ - Σ L₃ + ⋯` over all such families,
written as one sum over vertex sets and permutations weighted by `(-1)` to the number of loops.
Unwinding it on a two-element vertex set gives the product of two self-loop gains minus the gain
of the two-cycle, which is the expected second-order term.

A forward path from a source to a sink is a repetition-free list of nodes beginning at the source
and ending at the sink, and its gain is the product of the edge gains along it. Paths are
enumerated as a `Finset` by recursion on a length bound and then filtering, and the bound loses
nothing because a repetition-free list over a finite node type is no longer than the node count.
The enumeration is genuinely executable: it uses no choice, so small examples are settled by
`decide` rather than by an argument. The cofactor of a path is the graph determinant of the
vertex set the path does not touch.

Nothing here is proved equal to a determinant or to a gain; this file only builds the
combinatorial objects and their elementary properties. The identification with `det (1 - G)` and
Mason's formula are separate.

## ii. Key results

- `Physlib.SignalFlowGraph.loopFamilies`: the non-touching loop families on a vertex set.
- `Physlib.SignalFlowGraph.loopCount`: the number of loops in a family.
- `Physlib.SignalFlowGraph.familyGain`: the product of the loop gains of a family.
- `Physlib.SignalFlowGraph.graphDetOn`, `Physlib.SignalFlowGraph.graphDet`: the graph determinant.
- `Physlib.SignalFlowGraph.graphDetOn_empty`: on the empty vertex set the determinant is one,
  because only the empty family contributes.
- `Physlib.SignalFlowGraph.listsLen`, `Physlib.SignalFlowGraph.nodupLists`: executable
  enumerations of bounded-length and of repetition-free node lists.
- `Physlib.SignalFlowGraph.forwardPaths`: the executable enumeration of forward paths.
- `Physlib.SignalFlowGraph.mem_forwardPaths_iff`: its characterization.
- `Physlib.SignalFlowGraph.pathGain`, `Physlib.SignalFlowGraph.pathCofactor`: a path's gain and
  the determinant of the loops it does not touch.
- `Physlib.SignalFlowGraph.masonNumerator`, `Physlib.SignalFlowGraph.masonGain`: the numerator
  and quotient of Mason's formula, as definitions only.

## iii. Table of contents

- A. Non-touching loop families
- B. The graph determinant
- C. Forward paths
- D. Path gains, cofactors, and Mason's quotient

## iv. References

The objects follow U. Siddique, S. M. Beillahi, and S. Tahar, "On the Formal Analysis of Photonic
Signal Processing Systems", FMICS 2015, LNCS 9128, Definitions 1-4 (pp. 167-168), and
S. M. Beillahi, U. Siddique, and S. Tahar, "On the Formalization of Signal-Flow-Graphs in HOL",
Technical Report, Concordia University, November 2014, together with its journal successor,
"Formal Analysis of Engineering Systems Based on Signal-Flow-Graph Theory", NSV 2016, LNCS 10152,
Definition 6 (p. 37). Those sources enumerate elementary circuits and forward circuits from a
branch list and define Mason's gain as a quotient; they do not relate either to a determinant.

Two representational differences are recorded. First, the sources carry a graph as a list of
branches `ℕ × ℂ × ℕ`, so a loop is a list of branches; here a family of non-touching loops is a
permutation, which makes vertex-disjointness structural instead of a checked side condition, at
the cost of not distinguishing parallel edges. That cost is the subject of the non-claim below.
Second, the sources define the determinant only through their enumeration; here it is defined
directly as the alternating sum over families, which is what `goal.md` section H.4 S6 asks for.

Deliberately not claimed. A permutation records only which node follows which, so two parallel
edges between the same ordered pair of nodes give the same loop and are not distinguished, and a
forward path is a list of nodes rather than of edges. `goal.md` section H.4 S6 requires a
multigraph representation with explicit edge identity, and its regression row G-02 requires
distinct parallel branches to stay distinct through the enumeration; neither is met by this file.
An edge-indexed layer and an edge-based enumeration are scheduled separately. Nothing here
asserts a determinant identity, a gain, or any topological interpretation of `masonGain`.

This file is neutral mathematics and imports no physics.

-/

@[expose] public section

namespace Physlib.SignalFlowGraph

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-!

## A. Non-touching loop families

-/

/-- The families of pairwise non-touching loops covering a vertex set `T`, each carried by a
permutation of the node type supported inside `T`. Vertices of `T` fixed by the permutation are
the self-loops of the family, and the nontrivial cycles are its longer loops. -/
def loopFamilies (T : Finset ι) : Finset (Equiv.Perm ι) :=
  {σ : Equiv.Perm ι | σ.support ⊆ T}

/-- Membership in the loop families of a vertex set. -/
@[simp]
lemma mem_loopFamilies {T : Finset ι} {σ : Equiv.Perm ι} :
    σ ∈ loopFamilies T ↔ σ.support ⊆ T := by
  simp [loopFamilies]

/-- The identity permutation is the empty family on any vertex set. -/
lemma one_mem_loopFamilies (T : Finset ι) : (1 : Equiv.Perm ι) ∈ loopFamilies T := by
  simp

/-- The only family on the empty vertex set is the empty one. -/
lemma loopFamilies_empty : loopFamilies (∅ : Finset ι) = {1} := by
  ext σ
  simp [Equiv.Perm.support_eq_empty_iff]

/-- The number of loops in a family: the self-loops, which are the vertices of `T` fixed by the
permutation, together with the nontrivial cycles. -/
def loopCount (T : Finset ι) (σ : Equiv.Perm ι) : ℕ :=
  (T.card - σ.support.card) + Multiset.card σ.cycleType

/-- The empty family on a vertex set has one self-loop per vertex. -/
@[simp]
lemma loopCount_one (T : Finset ι) : loopCount T 1 = T.card := by
  simp [loopCount]

/-- The product of the loop gains of a family. -/
noncomputable def familyGain (G : Matrix ι ι ℂ) (T : Finset ι) (σ : Equiv.Perm ι) : ℂ :=
  ∏ i ∈ T, G (σ i) i

omit [Fintype ι] [DecidableEq ι] in
/-- The empty family has unit gain. -/
@[simp]
lemma familyGain_empty (G : Matrix ι ι ℂ) (σ : Equiv.Perm ι) :
    familyGain G ∅ σ = 1 := by
  simp [familyGain]

/-!

## B. The graph determinant

-/

/-- The graph determinant of the subgraph on a vertex set: the alternating sum
`1 - Σ L₁ + Σ L₂ - ⋯` over the families of pairwise non-touching loops inside that set. -/
noncomputable def graphDetOn (G : Matrix ι ι ℂ) (S : Finset ι) : ℂ :=
  ∑ T ∈ S.powerset, ∑ σ ∈ loopFamilies T, (-1 : ℂ) ^ loopCount T σ * familyGain G T σ

/-- The graph determinant of the whole graph. -/
noncomputable def graphDet (G : Matrix ι ι ℂ) : ℂ := graphDetOn G Finset.univ

/-- On the empty vertex set the graph determinant is one: only the empty family contributes. -/
@[simp]
lemma graphDetOn_empty (G : Matrix ι ι ℂ) : graphDetOn G ∅ = 1 := by
  rw [graphDetOn, Finset.powerset_empty, Finset.sum_singleton, loopFamilies_empty,
    Finset.sum_singleton, loopCount_one, Finset.card_empty, familyGain_empty, pow_zero, mul_one]

/-!

## C. Forward paths

-/

/-- The node lists of length at most `n`, enumerated by recursion on the length bound. -/
def listsLen (ι : Type*) [Fintype ι] [DecidableEq ι] : ℕ → Finset (List ι)
  | 0 => {[]}
  | n + 1 => insert [] ((Finset.univ : Finset ι).biUnion fun a =>
      (listsLen ι n).image (a :: ·))

/-- The enumeration by length bound is exactly the lists of that length. -/
lemma mem_listsLen_iff {n : ℕ} {p : List ι} : p ∈ listsLen ι n ↔ p.length ≤ n := by
  induction n generalizing p with
  | zero => simp [listsLen, List.length_eq_zero_iff]
  | succ n ih =>
    rw [listsLen, Finset.mem_insert, Finset.mem_biUnion]
    constructor
    · rintro (rfl | ⟨a, -, ha⟩)
      · simp
      · rw [Finset.mem_image] at ha
        obtain ⟨q, hq, rfl⟩ := ha
        simpa using Nat.succ_le_succ (ih.mp hq)
    · intro hlen
      match p with
      | [] => exact Or.inl rfl
      | a :: q =>
        refine Or.inr ⟨a, Finset.mem_univ a, Finset.mem_image.mpr ⟨q, ih.mpr ?_, rfl⟩⟩
        simpa using hlen

/-- Every repetition-free list of nodes. A repetition-free list over a finite node type is no
longer than the node count, so bounding the length loses nothing. -/
def nodupLists (ι : Type*) [Fintype ι] [DecidableEq ι] : Finset (List ι) :=
  (listsLen ι (Fintype.card ι)).filter fun p => p.Nodup

/-- The enumeration of repetition-free lists is exactly the repetition-free lists. -/
lemma mem_nodupLists_iff {p : List ι} : p ∈ nodupLists ι ↔ p.Nodup := by
  rw [nodupLists, Finset.mem_filter, mem_listsLen_iff]
  exact ⟨fun h => h.2, fun h => ⟨h.length_le_card, h⟩⟩

/-- The forward paths from a source node to a sink node: the repetition-free node lists that begin
at the source and end at the sink. -/
def forwardPaths (s t : ι) : Finset (List ι) :=
  (nodupLists ι).filter fun p => p.head? = some s ∧ p.getLast? = some t

/-- Membership in the forward paths, unfolded. -/
lemma mem_forwardPaths_iff {s t : ι} {p : List ι} :
    p ∈ forwardPaths s t ↔ p.Nodup ∧ p.head? = some s ∧ p.getLast? = some t := by
  rw [forwardPaths, Finset.mem_filter, mem_nodupLists_iff]

/-- The one-node list is the trivial forward path from a node to itself. -/
lemma singleton_mem_forwardPaths (s : ι) : [s] ∈ forwardPaths s s := by
  rw [mem_forwardPaths_iff]
  exact ⟨List.nodup_singleton s, rfl, rfl⟩

/-- No forward path is empty. -/
lemma nil_notMem_forwardPaths (s t : ι) : [] ∉ forwardPaths s t := by
  rw [mem_forwardPaths_iff]
  rintro ⟨-, h, -⟩
  simp at h

/-!

## D. Path gains, cofactors, and Mason's quotient

-/

/-- The gain along a node list: the product of the edge gains of its consecutive pairs. A list of
fewer than two nodes has unit gain. -/
noncomputable def pathGain (G : Matrix ι ι ℂ) : List ι → ℂ
  | [] => 1
  | [_] => 1
  | u :: v :: rest => G v u * pathGain G (v :: rest)

omit [Fintype ι] [DecidableEq ι] in
/-- The gain of the empty node list. -/
@[simp]
lemma pathGain_nil (G : Matrix ι ι ℂ) : pathGain G [] = 1 := rfl

omit [Fintype ι] [DecidableEq ι] in
/-- The gain of a one-node list. -/
@[simp]
lemma pathGain_singleton (G : Matrix ι ι ℂ) (u : ι) : pathGain G [u] = 1 := rfl

omit [Fintype ι] [DecidableEq ι] in
/-- The gain of a list peels off its first edge. -/
@[simp]
lemma pathGain_cons_cons (G : Matrix ι ι ℂ) (u v : ι) (rest : List ι) :
    pathGain G (u :: v :: rest) = G v u * pathGain G (v :: rest) := rfl

/-- The cofactor of a node list: the graph determinant of the loops that do not touch it. -/
noncomputable def pathCofactor (G : Matrix ι ι ℂ) (p : List ι) : ℂ :=
  graphDetOn G (Finset.univ \ p.toFinset)

/-- The numerator of Mason's formula: the sum over forward paths of the path gain times its
cofactor. -/
noncomputable def masonNumerator (G : Matrix ι ι ℂ) (s t : ι) : ℂ :=
  ∑ p ∈ forwardPaths s t, pathGain G p * pathCofactor G p

/-- Mason's quotient. No theorem in this file relates it to
`Physlib.SignalFlowGraph.gain`; that identification is proved separately. -/
noncomputable def masonGain (G : Matrix ι ι ℂ) (s t : ι) : ℂ := masonNumerator G s t / graphDet G

end Physlib.SignalFlowGraph
