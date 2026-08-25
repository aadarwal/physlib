/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Mathematics.SignalFlowGraph.Extraction
public import Physlib.Mathematics.SignalFlowGraph.MasonPath

/-!
# Edge-level enumeration over a multigraph

## i. Overview

The loops and forward paths of the preceding files are node-level: a loop family is a permutation
of nodes and a path is a list of nodes, so two parallel edges between the same ordered pair of
nodes are the same step. This file refines both enumerations to the edge level and proves that
refining changes nothing about the values.

The mechanism is one distributive law. An entry of the gain matrix is the sum of the gains of the
edges joining an ordered pair of nodes, so a product of entries is a sum over choices of one edge
per factor. A node-level loop family therefore expands into the family of its **edge-level
refinements**, one for each way of picking an edge per node of the vertex set, and a node-level
path expands into the edge lists that refine it, one for each way of picking an edge per step.
Summing the refinements returns the node-level value.

Parallel edges are distinct at the edge level even though they are indistinguishable in the gain
matrix, so the refinements of a step through two parallel edges are two refinements rather than
one. The companion regression proves that on the pair of multigraphs whose gain matrices were
shown equal in the extraction regressions, closing the gap those left open.

Everything above the enumeration is inherited: the edge-level determinant is `det (1 - toMatrix)`,
and the edge-level Mason quotient is the gain, both as corollaries of the node-level theorems
rather than as new arguments.

## ii. Key results

- `Physlib.SignalFlowGraph.edgeChoices`, `Physlib.SignalFlowGraph.edgeFamilyGain`: the edge-level
  refinements of a loop family and their gains.
- `Physlib.SignalFlowGraph.familyGain_toMatrix`: a family gain is the sum over its refinements.
- `Physlib.SignalFlowGraph.edgeGraphDet_eq_det`: the edge-level determinant is
  `det (1 - toMatrix)`.
- `Physlib.SignalFlowGraph.refiningEdgeLists`, `Physlib.SignalFlowGraph.edgeListGain`: the edge
  lists refining a node path and their gains.
- `Physlib.SignalFlowGraph.pathGain_toMatrix`: a path gain is the sum over its refinements.
- `Physlib.SignalFlowGraph.edgeMasonGain_eq_gain`: Mason's gain formula, edge-level.

## iii. Table of contents

- A. Edge refinements of a loop family
- B. The edge-level graph determinant
- C. Edge lists refining a node path
- D. Mason's formula at the edge level

## iv. References

The requirement met here is regression row G-02 of `goal.md` section I.3, "distinct parallel
branches remain distinct in compilation and Mason enumeration", together with the sentence in
section H.4 S6 that "A simple digraph that collapses parallel edges does not meet this milestone".
The source development carries branches as list entries and so distinguishes parallel branches by
construction; see U. Siddique, S. M. Beillahi, and S. Tahar, "On the Formal Analysis of Photonic
Signal Processing Systems", FMICS 2015, LNCS 9128, Definitions 1-3 (pp. 167-168). No fetched
source relates a branch-level enumeration to a node-level one, so the reduction proved here is
Physlib-original.

Deliberately not claimed. The refinement is exact on values, so no edge-level statement here is
stronger than its node-level counterpart; the gain is in what the enumeration distinguishes, not
in what it computes. Nothing here asserts agreement with any network or netlist semantics.

This file is neutral mathematics and imports no physics.

-/

@[expose] public section

namespace Physlib.SignalFlowGraph

open Matrix

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]

/-!

## A. Edge refinements of a loop family

-/

/-- The edge-level refinements of a loop family: a choice of one edge for each node of the vertex
set, running from that node to its image. -/
def edgeChoices (Γ : Multigraph ι E) (T : Finset ι) (σ : Equiv.Perm ι) :
    Finset (∀ i ∈ T, E) :=
  T.pi fun i => Γ.edgesBetween i (σ i)

/-- The gain of an edge-level loop family: the product of the chosen edges' gains. -/
noncomputable def edgeFamilyGain (Γ : Multigraph ι E) (T : Finset ι)
    (c : ∀ i ∈ T, E) : ℂ :=
  ∏ x ∈ T.attach, Γ.gain (c x.1 x.2)

omit [Fintype ι] [DecidableEq E] in
/-- A family gain of the gain matrix is the sum of the gains of its edge-level refinements. Two
parallel edges give two refinements, so nothing is collapsed at this level. -/
lemma familyGain_toMatrix (Γ : Multigraph ι E) (T : Finset ι) (σ : Equiv.Perm ι) :
    familyGain Γ.toMatrix T σ = ∑ c ∈ edgeChoices Γ T σ, edgeFamilyGain Γ T c := by
  rw [familyGain, edgeChoices]
  simp only [Multigraph.toMatrix_apply]
  exact Finset.prod_sum T _ _

/-!

## B. The edge-level graph determinant

-/

/-- The edge-level graph determinant on a vertex set: the alternating sum over node-level loop
families of the gains of all their edge-level refinements. -/
noncomputable def edgeGraphDetOn (Γ : Multigraph ι E) (S : Finset ι) : ℂ :=
  ∑ T ∈ S.powerset, ∑ σ ∈ loopFamilies T, ∑ c ∈ edgeChoices Γ T σ,
    (-1 : ℂ) ^ loopCount T σ * edgeFamilyGain Γ T c

/-- The edge-level graph determinant of the whole multigraph. -/
noncomputable def edgeGraphDet (Γ : Multigraph ι E) : ℂ := edgeGraphDetOn Γ Finset.univ

omit [DecidableEq E] in
/-- Refining to the edge level does not change the graph determinant on a vertex set. -/
lemma edgeGraphDetOn_eq_graphDetOn (Γ : Multigraph ι E) (S : Finset ι) :
    edgeGraphDetOn Γ S = graphDetOn Γ.toMatrix S := by
  rw [edgeGraphDetOn, graphDetOn]
  refine Finset.sum_congr rfl fun T _ => Finset.sum_congr rfl fun σ _ => ?_
  rw [familyGain_toMatrix, Finset.mul_sum]

omit [DecidableEq E] in
/-- The edge-level graph determinant is the determinant of the system matrix of the gain
matrix. -/
lemma edgeGraphDet_eq_det (Γ : Multigraph ι E) :
    edgeGraphDet Γ = (systemMatrix Γ.toMatrix).det := by
  rw [edgeGraphDet, edgeGraphDetOn_eq_graphDetOn, ← graphDet, graphDet_eq_det]

/-!

## C. Edge lists refining a node path

-/

/-- The edge lists refining a node path: one edge per step, each running between the consecutive
nodes it refines. -/
def refiningEdgeLists (Γ : Multigraph ι E) : List ι → Finset (List E)
  | [] => {[]}
  | [_] => {[]}
  | u :: v :: rest => (Γ.edgesBetween u v).biUnion fun e =>
      (refiningEdgeLists Γ (v :: rest)).image (e :: ·)

omit [Fintype ι] in
/-- The refinements of a single-node path are the empty edge list alone. -/
lemma refiningEdgeLists_singleton (Γ : Multigraph ι E) (u : ι) :
    refiningEdgeLists Γ [u] = {[]} := rfl

omit [Fintype ι] in
/-- The refinements of a two-node step are the one-edge lists over the edges joining them. -/
lemma refiningEdgeLists_pair (Γ : Multigraph ι E) (u v : ι) :
    refiningEdgeLists Γ [u, v] = (Γ.edgesBetween u v).image fun e => [e] := by
  ext l
  simp only [refiningEdgeLists, Finset.mem_biUnion, Finset.mem_image,
    Multigraph.mem_edgesBetween]
  constructor
  · rintro ⟨e, he, m, hm, rfl⟩
    exact ⟨e, he, by simpa using hm⟩
  · rintro ⟨e, he, rfl⟩
    exact ⟨e, he, [], Finset.mem_singleton_self _, rfl⟩

/-- The gain of an edge list: the product of its edges' gains. -/
noncomputable def edgeListGain (Γ : Multigraph ι E) (l : List E) : ℂ := (l.map Γ.gain).prod

omit [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E] in
/-- The gain of an edge list peels off its first edge. -/
@[simp]
lemma edgeListGain_cons (Γ : Multigraph ι E) (e : E) (l : List E) :
    edgeListGain Γ (e :: l) = Γ.gain e * edgeListGain Γ l := by
  rw [edgeListGain, edgeListGain, List.map_cons, List.prod_cons]

omit [Fintype ι] in
/-- A path gain of the gain matrix is the sum of the gains of the edge lists refining it. Parallel
edges refine the same step differently, so nothing is collapsed at this level. -/
lemma pathGain_toMatrix (Γ : Multigraph ι E) (q : List ι) :
    pathGain Γ.toMatrix q = ∑ l ∈ refiningEdgeLists Γ q, edgeListGain Γ l := by
  induction q with
  | nil => simp [refiningEdgeLists, edgeListGain]
  | cons u rest ih =>
    match rest with
    | [] => simp [refiningEdgeLists, edgeListGain]
    | (v :: rest') =>
      have hdisj : ∀ e ∈ Γ.edgesBetween u v, ∀ e' ∈ Γ.edgesBetween u v, e ≠ e' →
          Disjoint ((refiningEdgeLists Γ (v :: rest')).image (e :: ·))
            ((refiningEdgeLists Γ (v :: rest')).image (e' :: ·)) := by
        intro e _ e' _ hne
        refine Finset.disjoint_left.mpr fun l hl hl' => ?_
        obtain ⟨m, -, hm⟩ := Finset.mem_image.mp hl
        obtain ⟨m', -, hm'⟩ := Finset.mem_image.mp hl'
        exact hne (List.head_eq_of_cons_eq (hm.trans hm'.symm))
      rw [pathGain_cons_cons, ih, Multigraph.toMatrix_apply, refiningEdgeLists,
        Finset.sum_biUnion hdisj, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [Finset.sum_image (fun _ _ _ _ h => List.tail_eq_of_cons_eq h)]
      exact Finset.sum_congr rfl fun l _ => (edgeListGain_cons Γ e l).symm

/-!

## D. Mason's formula at the edge level

-/

/-- The edge-level numerator of Mason's formula. -/
noncomputable def edgeMasonNumerator (Γ : Multigraph ι E) (s t : ι) : ℂ :=
  ∑ q ∈ forwardPaths s t, ∑ l ∈ refiningEdgeLists Γ q,
    edgeListGain Γ l * edgeGraphDetOn Γ (Finset.univ \ q.toFinset)

/-- Refining to the edge level does not change the numerator of Mason's formula. -/
lemma edgeMasonNumerator_eq (Γ : Multigraph ι E) (s t : ι) :
    edgeMasonNumerator Γ s t = masonNumerator Γ.toMatrix s t := by
  rw [edgeMasonNumerator, masonNumerator]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [pathCofactor, ← edgeGraphDetOn_eq_graphDetOn, pathGain_toMatrix, Finset.sum_mul]

/-- **Mason's gain formula at the edge level.** Where the graph determinant does not vanish, the
gain between two nodes is the edge-level numerator over the edge-level determinant, both summed
over enumerations in which parallel edges stay distinct. -/
theorem edgeMasonGain_eq_gain (Γ : Multigraph ι E) (s t : ι) (h : graphDet Γ.toMatrix ≠ 0) :
    edgeMasonNumerator Γ s t / edgeGraphDet Γ = gain Γ.toMatrix s t := by
  rw [edgeMasonNumerator_eq, edgeGraphDet, edgeGraphDetOn_eq_graphDetOn, ← graphDet]
  exact masonGain_eq_gain Γ.toMatrix s t h

end Physlib.SignalFlowGraph
