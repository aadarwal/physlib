/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.Analysis.Complex.Basic

/-!
# Node equations of a finite signal-flow graph

## i. Overview

A finite signal-flow graph on a node type `ι` is carried here by its gain matrix `G`, where
`G i j` is the total gain of the edges from node `j` into node `i`. The node signals `x` and the
injected input `b` satisfy the node equation `x = G *ᵥ x + b`, which says that the signal at each
node is the sum of the injected input there and the gains along the incoming edges.

The whole file is linear algebra. The node equation is equivalent to `(1 - G) *ᵥ x = b`, so it has
exactly one solution for every input exactly when `1 - G` is invertible, and that solution is
`(1 - G)⁻¹ *ᵥ b`. Under this gate, the response from a source node to a sink node is the
corresponding entry of `(1 - G)⁻¹`, and an arbitrary response is their superposition.

Both directions of the solvability criterion are proved. If `1 - G` is singular then some nonzero
vector is annihilated by it, so the zero input already has two solutions; uniqueness therefore
fails, and the criterion is not merely sufficient.

## ii. Key results

- `Physlib.SignalFlowGraph.IsNodeSolution`: the node equation `x = G *ᵥ x + b`.
- `Physlib.SignalFlowGraph.systemMatrix`: the matrix `1 - G`.
- `Physlib.SignalFlowGraph.isNodeSolution_iff`: the node equation as `(1 - G) *ᵥ x = b`.
- `Physlib.SignalFlowGraph.nodeSolution`: the algebraic inverse expression `(1 - G)⁻¹ *ᵥ b`.
- `Physlib.SignalFlowGraph.existsUnique_isNodeSolution_iff`: unique solvability for every input is
  exactly invertibility of `1 - G`.
- `Physlib.SignalFlowGraph.gain`: the totalized inverse-system entry from source to sink.
- `Physlib.SignalFlowGraph.nodeSolution_eq_sum_gain`: superposition of the gains.

## iii. Table of contents

- A. The node equation
- B. Unique solvability
- C. Gain between two nodes

## iv. References

This file supplies the "node-equation semantics and adjacency matrix" and the "equality with the
corresponding entry of `(1 - A)⁻¹`" requirements of `goal.md` section H.4 S6. The topological
requirements of that section are only partly developed in later files: they provide node-level
paths and loop families, the graph determinant, and a routed-loop-family/cofactor quotient, while
edge-level enumeration and the general forward-path Mason identity remain open.

The source development is S. M. Beillahi, U. Siddique, and S. Tahar, "On the Formalization of
Signal-Flow-Graphs in HOL", Technical Report, Concordia University, November 2014, and
S. M. Beillahi, U. Siddique, and S. Tahar, "Formal Analysis of Engineering Systems Based on
Signal-Flow-Graph Theory", NSV 2016, LNCS 10152, pp. 31-46, together with U. Siddique,
S. M. Beillahi, and S. Tahar, "On the Formal Analysis of Photonic Signal Processing Systems",
FMICS 2015, LNCS 9128, pp. 162-177, Definition 1 (p. 167). Those sources carry a graph as a list
of branches and define Mason's gain by executable enumeration; they do not state a node-equation
semantics or relate the gain to a matrix inverse. This file is therefore not a parity claim: it
is the linear-algebra layer that the later routed-loop-family/cofactor theorem agrees with.

Two things are deliberately not claimed. First, a gain matrix records only the **total** gain
between an ordered pair of nodes, so it does not by itself distinguish parallel edges, and its
support changes if an edge gain happens to be zero. `goal.md` section H.4 S6 requires a
multigraph representation with explicit edge identity for exactly that reason; a separate
edge-indexed layer above this one is needed to meet it, and is not provided here. Second, no
claim is made about matrix-valued edge gains: the development is scalar throughout, as
`goal.md` section H.4 S6 requires.

This file is neutral mathematics and imports no physics.

-/

@[expose] public section

namespace Physlib.SignalFlowGraph

noncomputable section

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {G : Matrix ι ι ℂ} {b x : ι → ℂ}

/-!

## A. The node equation

-/

/-- The node signals `x` solve the signal-flow graph with gain matrix `G` and injected input `b`
when each node signal is the injected input there plus the gains along the incoming edges. -/
def IsNodeSolution (G : Matrix ι ι ℂ) (b x : ι → ℂ) : Prop := x = G *ᵥ x + b

/-- The system matrix of a signal-flow graph. -/
def systemMatrix (G : Matrix ι ι ℂ) : Matrix ι ι ℂ := 1 - G

/-- The node equation written as a linear system for the system matrix. -/
lemma isNodeSolution_iff : IsNodeSolution G b x ↔ systemMatrix G *ᵥ x = b := by
  rw [IsNodeSolution, systemMatrix, sub_mulVec, one_mulVec, sub_eq_iff_eq_add,
    add_comm b (G *ᵥ x)]

/-- The zero input has the zero solution. -/
lemma isNodeSolution_zero (G : Matrix ι ι ℂ) : IsNodeSolution G 0 0 := by
  rw [isNodeSolution_iff, mulVec_zero]

/-!

## B. Unique solvability

-/

/-- The algebraic inverse expression for the node equation. When the system matrix is invertible,
`isNodeSolution_nodeSolution` proves that this is the unique solution. At a singular matrix,
Mathlib's inverse is totalized and this expression has no solution semantics by itself. -/
def nodeSolution (G : Matrix ι ι ℂ) (b : ι → ℂ) : ι → ℂ :=
  (systemMatrix G)⁻¹ *ᵥ b

/-- Where the system matrix is invertible, the constructed vector solves the node equation. -/
lemma isNodeSolution_nodeSolution (h : IsUnit (systemMatrix G).det) (b : ι → ℂ) :
    IsNodeSolution G b (nodeSolution G b) := by
  rw [isNodeSolution_iff, nodeSolution, mulVec_mulVec, mul_nonsing_inv _ h, one_mulVec]

/-- Where the system matrix is invertible, every solution of the node equation is the constructed
one. -/
lemma eq_nodeSolution (h : IsUnit (systemMatrix G).det) (hx : IsNodeSolution G b x) :
    x = nodeSolution G b := by
  rw [isNodeSolution_iff] at hx
  rw [nodeSolution, ← hx, mulVec_mulVec, nonsing_inv_mul _ h, one_mulVec]

/-- Where the system matrix is invertible, the node equation has exactly one solution for every
input. -/
lemma existsUnique_isNodeSolution (h : IsUnit (systemMatrix G).det) (b : ι → ℂ) :
    ∃! x, IsNodeSolution G b x :=
  ⟨nodeSolution G b, isNodeSolution_nodeSolution h b, fun _ hx => eq_nodeSolution h hx⟩

/-- Unique solvability for every input is exactly invertibility of the system matrix. The reverse
direction shows the hypothesis is not merely sufficient: a singular system matrix annihilates some
nonzero vector, so the zero input already has two solutions. -/
theorem existsUnique_isNodeSolution_iff (G : Matrix ι ι ℂ) :
    (∀ b : ι → ℂ, ∃! x, IsNodeSolution G b x) ↔ IsUnit (systemMatrix G).det := by
  refine ⟨fun hall => ?_, fun h b => existsUnique_isNodeSolution h b⟩
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv, hvz⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  obtain ⟨y, -, huniq⟩ := hall 0
  have h0 : (0 : ι → ℂ) = y := huniq 0 (isNodeSolution_zero G)
  have hvsol : IsNodeSolution G 0 v := by rw [isNodeSolution_iff, hvz]
  exact hv ((huniq v hvsol).trans h0.symm)

/-!

## C. Gain between two nodes

-/

/-- The inverse-system entry from a source node to a sink node. When the system matrix is
invertible this maps a unit source injection to the solved sink signal. At a singular matrix it
is only Mathlib's totalized inverse entry, not a solved network response. -/
def gain (G : Matrix ι ι ℂ) (s t : ι) : ℂ := (systemMatrix G)⁻¹ t s

/-- The gain is the sink component of the algebraic inverse expression driven by a unit injection
at the source. Its solution interpretation requires an invertible system matrix. -/
lemma gain_eq_nodeSolution (G : Matrix ι ι ℂ) (s t : ι) :
    gain G s t = nodeSolution G (Pi.single s 1) t := by
  rw [gain, nodeSolution, mulVec_single_one]
  rfl

/-- The algebraic inverse expression for an arbitrary input is the input-weighted sum of the
inverse entries. Under invertibility this is superposition of the unique solved response. -/
lemma nodeSolution_eq_sum_gain (G : Matrix ι ι ℂ) (b : ι → ℂ) (t : ι) :
    nodeSolution G b t = ∑ s, gain G s t * b s := by
  rw [nodeSolution]
  rfl

end

end Physlib.SignalFlowGraph
