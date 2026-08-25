/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Mathematics.SignalFlowGraph.MasonRegression
public import Physlib.Mathematics.SignalFlowGraph.Terminated

/-!
# Definition-level checks of the determinant and gain

## i. Overview

The regressions elsewhere in this development compute a graph determinant through
`graphDet_eq_det` and a gain through the adjugate, so they exercise the theorems but not the
definitions those theorems are about. This file checks the definitions directly on two nodes and
meets the theorems from outside.

The graph determinant is expanded by enumerating what its definition sums over: the four vertex
subsets of a two-element node type, and for each the permutations supported inside it. That
enumeration is decidable and is settled by evaluation. The resulting closed form is then shown to
agree with the determinant of the system matrix, which is a second and independent proof of the
general identity restricted to two nodes.

The gain is checked the other way round, in two layers that should not be confused. The first
is inverse-free: an explicit signal vector is exhibited and verified to satisfy the node equations
under a unit injection at the input, and separately the output component of *any* solution of
those equations is shown to be `a / (1 - a * b)`, by eliminating the input component between the
two scalar equations. That argument uses no inverse, no adjugate and no uniqueness lemma, so it
confirms the value obtained elsewhere from a two-by-two adjugate by a genuinely different route.

The second layer transfers this to `gain`, and it is not inverse-free, because it cannot be:
`gain` is *defined* as an entry of the totalized inverse system matrix, and the bridge from a
solution to that entry runs through `gain_eq_nodeSolution` and `eq_nodeSolution`, both proved by
multiplying by the inverse. What the corollary avoids is expanding the two-by-two inverse in
closed form, not the inverse itself.

## ii. Key results

- `Physlib.SignalFlowGraph.loopFamilies_fin_two_univ`: the loop families on two nodes, evaluated.
- `Physlib.SignalFlowGraph.graphDet_fin_two`: the graph determinant on two nodes, expanded
  directly from its definition.
- `Physlib.SignalFlowGraph.graphDet_fin_two_eq_det`: that expansion agrees with the determinant
  of the system matrix, independently of the general identity.
- `Physlib.SignalFlowGraph.graphDet_fullTwoNode_direct`: the audited touching case, from the
  definition.
- `Physlib.SignalFlowGraph.isNodeSolution_twoNodeLoop_explicit`: an explicit solution of the node
  equations.
- `Physlib.SignalFlowGraph.output_of_isNodeSolution_twoNodeLoop`: the output component of every
  solution of the node equations, forced without any use of an inverse.
- `Physlib.SignalFlowGraph.gain_twoNodeLoop_via_nodeSolution`: the same value for `gain`, through
  the inverse bridge that the definition of `gain` makes unavoidable.

## iii. Table of contents

- A. The loop families on two nodes
- B. The graph determinant from its definition
- C. The gain from the node equations

## iv. References

These are the definition-level counterparts of regression rows G-01 and G-03 of `goal.md`
section I.3. The rows are already discharged elsewhere, but through the same theorems that relate
the definitions to matrix quantities; the point of this file is to reach the same values by routes
that do not pass through those theorems, so that an error inside one of them would be caught here.

These are decidable evaluations and algebraic identities on complex matrices. No physical,
optical, or signal-processing interpretation is asserted.

-/

@[expose] public section

namespace Physlib.SignalFlowGraph

open Matrix

/-!

## A. The loop families on two nodes

-/

/-- The four vertex subsets of a two-element node type. -/
lemma univ_finset_fin_two :
    (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide

/-- The only loop family on the empty vertex set is the empty one. -/
lemma loopFamilies_fin_two_empty : loopFamilies (∅ : Finset (Fin 2)) = {1} := by decide

/-- The only loop family on a single node is its self-loop. -/
lemma loopFamilies_fin_two_zero : loopFamilies ({0} : Finset (Fin 2)) = {1} := by decide

/-- The only loop family on the other single node is its self-loop. -/
lemma loopFamilies_fin_two_one : loopFamilies ({1} : Finset (Fin 2)) = {1} := by decide

/-- On both nodes there are two families: the pair of self-loops, and the two-cycle. -/
lemma loopFamilies_fin_two_univ :
    loopFamilies ({0, 1} : Finset (Fin 2)) = {1, Equiv.swap 0 1} := by decide

/-- The pair of self-loops counts as two loops. -/
lemma loopCount_fin_two_univ_one : loopCount ({0, 1} : Finset (Fin 2)) 1 = 2 := by decide

/-- The two-cycle counts as one loop. -/
lemma loopCount_fin_two_univ_swap :
    loopCount ({0, 1} : Finset (Fin 2)) (Equiv.swap 0 1) = 1 := by decide

/-!

## B. The graph determinant from its definition

-/

/-- The graph determinant on two nodes, expanded directly from the alternating sum over loop
families. Nothing here passes through the identification with a matrix determinant. -/
lemma graphDet_fin_two (G : Matrix (Fin 2) (Fin 2) ℂ) :
    graphDet G = 1 - G 0 0 - G 1 1 + G 0 0 * G 1 1 - G 1 0 * G 0 1 := by
  rw [graphDet, graphDetOn, Finset.powerset_univ, univ_finset_fin_two]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [loopFamilies_fin_two_empty, loopFamilies_fin_two_zero, loopFamilies_fin_two_one,
    loopFamilies_fin_two_univ]
  rw [Finset.sum_singleton, Finset.sum_singleton, Finset.sum_singleton,
    Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [loopCount_fin_two_univ_one, loopCount_fin_two_univ_swap]
  simp only [loopCount, familyGain, Finset.card_empty, Finset.card_singleton,
    Equiv.Perm.support_one, Equiv.Perm.cycleType_one, Finset.card_empty, Multiset.card_zero,
    Finset.prod_empty, Finset.prod_singleton, Equiv.Perm.one_apply, Nat.sub_self, Nat.sub_zero,
    add_zero, pow_zero, pow_one]
  rw [Finset.prod_insert (by decide), Finset.prod_singleton, Finset.prod_insert (by decide),
    Finset.prod_singleton, Equiv.swap_apply_left, Equiv.swap_apply_right]
  ring

/-- The direct expansion agrees with the determinant of the system matrix. This is a second,
independent proof of the general identity restricted to two nodes. -/
lemma graphDet_fin_two_eq_det (G : Matrix (Fin 2) (Fin 2) ℂ) :
    graphDet G = (systemMatrix G).det := by
  rw [graphDet_fin_two, systemMatrix]
  have hmat : ((1 : Matrix (Fin 2) (Fin 2) ℂ) - G)
      = !![1 - G 0 0, -G 0 1; -G 1 0, 1 - G 1 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [hmat, det_fin_two_of]
  ring

/-- The single feedback loop, from the definition. -/
lemma graphDet_twoNodeLoop_direct (a b : ℂ) :
    graphDet (twoNodeLoop a b) = 1 - a * b := by
  rw [graphDet_fin_two]
  simp [twoNodeLoop]

/-- The audited touching case, from the definition: two self-loops and a two-cycle give three
first-order terms but only one second-order term. -/
lemma graphDet_fullTwoNode_direct (c d f g : ℂ) :
    graphDet (fullTwoNode c d f g) = 1 - c - d - f * g + c * d := by
  rw [graphDet_fin_two]
  simp only [fullTwoNode]
  norm_num
  ring

/-!

## C. The gain from the node equations

-/

/-- An explicit solution of the node equations of the two-node feedback graph under a unit
injection at the input. -/
lemma isNodeSolution_twoNodeLoop_explicit {a b : ℂ} (h : 1 - a * b ≠ 0) :
    IsNodeSolution (twoNodeLoop a b) (Pi.single 0 1)
      ![(1 - a * b)⁻¹, a * (1 - a * b)⁻¹] := by
  rw [isNodeSolution_iff, systemMatrix_twoNodeLoop]
  funext i
  fin_cases i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    field_simp
    ring
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The output signal of the two-node feedback graph is forced by the node equations alone: every
signal vector satisfying them under a unit injection at the input has the same output component.
The derivation eliminates the input component between the two scalar equations, so it appeals to
no matrix inverse, no adjugate, and no uniqueness lemma. -/
lemma output_of_isNodeSolution_twoNodeLoop {a b : ℂ} (h : 1 - a * b ≠ 0) (x : Fin 2 → ℂ)
    (hx : IsNodeSolution (twoNodeLoop a b) (Pi.single 0 1) x) :
    x 1 = a / (1 - a * b) := by
  rw [isNodeSolution_iff, systemMatrix_twoNodeLoop] at hx
  have h0 := congrFun hx 0
  have h1 := congrFun hx 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
  rw [eq_div_iff h]
  linear_combination h1 + a * h0

/-- The gain of the two-node feedback graph. This follows from the explicit solution, but unlike
`output_of_isNodeSolution_twoNodeLoop` it is **not** inverse-free, and the difference is worth
stating. `gain` is by definition an entry of the totalized inverse system matrix, and the step
from a solution to that entry goes through `gain_eq_nodeSolution` and `eq_nodeSolution`, each
proved by multiplying by the inverse. What is avoided here is expanding the two-by-two inverse in
closed form. -/
lemma gain_twoNodeLoop_via_nodeSolution {a b : ℂ} (h : 1 - a * b ≠ 0) :
    gain (twoNodeLoop a b) 0 1 = a / (1 - a * b) := by
  have hunit : IsUnit (systemMatrix (twoNodeLoop a b)).det := by
    rw [det_systemMatrix_twoNodeLoop, isUnit_iff_ne_zero]
    exact h
  have hsol := eq_nodeSolution hunit (isNodeSolution_twoNodeLoop_explicit h)
  rw [gain_eq_nodeSolution, ← hsol]
  simp [div_eq_mul_inv]

/-- The transfer function of the terminated two-node feedback graph. Like
`gain_twoNodeLoop_via_nodeSolution`, this reads an entry of the totalized inverse and so carries
the inverse bridge with it. -/
lemma transfer_terminate_twoNodeLoop {a b : ℂ} (h : 1 - a * b ≠ 0) :
    (TerminatedGraph.mk (twoNodeLoop a b) 0 1).transfer = a / (1 - a * b) :=
  gain_twoNodeLoop_via_nodeSolution h

end Physlib.SignalFlowGraph
