/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Mathematics.SignalFlowGraph.Mason

/-!
# Extracting a signal-flow graph

## i. Overview

Two ways of handing a linear system to the signal-flow machinery are named here. A coefficient
matrix already in the form `x = A x + b` is a gain matrix as it stands. A system already in the
form `M x = b`, which is the shape a solved netlist produces, becomes a gain matrix by taking the
complement `1 - M`; its system matrix is then `M` again, so its graph determinant is `det M` and
its gains are the entries of `M⁻¹`. Neither construction is deep. They exist so that a caller
never has to guess which side of `1 - G` a matrix belongs on.

The second half of the file adds edge identity. A gain matrix records only the total gain between
an ordered pair of nodes, so it cannot distinguish two parallel edges from one edge carrying their
sum, and it cannot tell an edge of gain zero from an absent edge. A multigraph carries a separate
edge type with source, target, and gain maps, so both distinctions survive: the topology is the
edge type and is fixed independently of what the gains happen to be. Its gain matrix is obtained
by summing the parallel edges.

That summing representation is genuinely lossy: the companion regression file exhibits two
distinguishable edge-indexed presentations, two parallel edges of gains `a` and `b` and one edge
of gain `a + b`, with the same gain matrix. So the multigraph layer is not decoration; it carries
information the matrix layer does not.

## ii. Key results

- `Physlib.SignalFlowGraph.ofCoefficientMatrix`: a coefficient matrix as a gain matrix.
- `Physlib.SignalFlowGraph.ofSystemMatrix`: a linear system `M x = b` as a gain matrix.
- `Physlib.SignalFlowGraph.systemMatrix_ofSystemMatrix`: the round trip.
- `Physlib.SignalFlowGraph.graphDet_ofSystemMatrix`: the graph determinant is `det M`.
- `Physlib.SignalFlowGraph.gain_ofSystemMatrix`: the gains are the entries of `M⁻¹`.
- `Physlib.SignalFlowGraph.Multigraph`: a directed weighted multigraph with explicit edge
  identity; finiteness is requested only by finite enumeration operations.
- `Physlib.SignalFlowGraph.Multigraph.toMatrix`: its gain matrix, summing parallel edges.
- `Physlib.SignalFlowGraph.Multigraph.toMatrix_apply`: the entry is the sum of the gains of the
  edges joining that ordered pair of nodes.

## iii. Table of contents

- A. Graphs from a linear system
- B. Multigraphs with explicit edge identity
- C. The gain matrix of a multigraph

## iv. References

Section A is the hook `goal.md` section H.4 S6 calls "extraction from suitable scalar network
models". It deliberately stops at the linear algebra: the theorem that this agrees with the
network semantics of the typed netlist layer belongs to that layer and is not attempted here.

Section B supplies explicit edge identity and topology independent of whether a symbolic or
evaluated edge weight happens to be zero. It does **not** store distinguished input/output nodes,
and its current path and loop enumeration is not edge-indexed, so it is only a foundation for the
larger S6 multigraph requirement. The source development carries a graph as a list of branches
`ℕ × ℂ × ℕ`; see U. Siddique, S. M. Beillahi, and S. Tahar, "On the Formal Analysis of Photonic
Signal Processing Systems",
FMICS 2015, LNCS 9128, Definition 1 (p. 167). A separate edge type is the same idea with the
branch index made a first-class parameter rather than a list position.

Deliberately not claimed. The path and loop enumeration of this development is still node-level,
so it does not distinguish parallel edges even though the representation here does. Regression
row G-02 of `goal.md` section I.3 asks for distinct parallel branches to remain distinct **through
the enumeration**, and that is not delivered by this file; an edge-based enumeration proved equal
to the matrix-level sums is scheduled separately. Nothing here asserts agreement with any network
or netlist semantics.

This file is neutral mathematics and imports no physics.

-/

@[expose] public section

namespace Physlib.SignalFlowGraph

open Matrix

section LinearSystem

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-!

## A. Graphs from a linear system

-/

/-- A coefficient matrix of a system already written as `x = A x + b` is a gain matrix as it
stands. -/
def ofCoefficientMatrix (A : Matrix ι ι ℂ) : Matrix ι ι ℂ := A

/-- A linear system `M x = b` becomes a gain matrix by taking the complement of `M`. -/
def ofSystemMatrix (M : Matrix ι ι ℂ) : Matrix ι ι ℂ := 1 - M

omit [Fintype ι] in
/-- The system matrix of the graph of a linear system is that system's matrix. -/
@[simp]
lemma systemMatrix_ofSystemMatrix (M : Matrix ι ι ℂ) :
    systemMatrix (ofSystemMatrix M) = M := by
  rw [systemMatrix, ofSystemMatrix, sub_sub_cancel]

/-- The node equations of the graph of a linear system are that linear system. -/
lemma isNodeSolution_ofSystemMatrix (M : Matrix ι ι ℂ) (b x : ι → ℂ) :
    IsNodeSolution (ofSystemMatrix M) b x ↔ M *ᵥ x = b := by
  rw [isNodeSolution_iff, systemMatrix_ofSystemMatrix]

/-- The graph determinant of the graph of a linear system is that system's determinant, so the
loop sum of the extracted graph is computed by an ordinary determinant. -/
lemma graphDet_ofSystemMatrix (M : Matrix ι ι ℂ) : graphDet (ofSystemMatrix M) = M.det := by
  rw [graphDet_eq_det, systemMatrix_ofSystemMatrix]

/-- The gains of the graph of a linear system are the entries of that system's inverse. -/
lemma gain_ofSystemMatrix (M : Matrix ι ι ℂ) (s t : ι) :
    gain (ofSystemMatrix M) s t = M⁻¹ t s := by
  rw [gain, systemMatrix_ofSystemMatrix]

end LinearSystem

section Multigraphs

variable {ι E : Type*}

/-!

## B. Multigraphs with explicit edge identity

-/

/-- A directed weighted multigraph on a node type: a separate edge type carrying a source, a
target, and a gain. Parallel edges are distinct because they are distinct elements of the edge
type, and the topology is fixed by the source and target maps independently of the gains, so an
edge of gain zero is still an edge. Operations that enumerate edges separately request a finite
edge type. -/
structure Multigraph (ι : Type*) (E : Type*) where
  /-- The tail of each edge. -/
  source : E → ι
  /-- The head of each edge. -/
  target : E → ι
  /-- The gain carried by each edge. -/
  gain : E → ℂ

/-- The edges of a multigraph joining one ordered pair of nodes. -/
def Multigraph.edgesBetween [DecidableEq ι] [Fintype E] (Γ : Multigraph ι E) (j i : ι) :
    Finset E := {e : E | Γ.source e = j ∧ Γ.target e = i}

/-- Membership in the edges joining an ordered pair of nodes. -/
@[simp]
lemma Multigraph.mem_edgesBetween [DecidableEq ι] [Fintype E] {Γ : Multigraph ι E} {j i : ι}
    {e : E} : e ∈ Γ.edgesBetween j i ↔ Γ.source e = j ∧ Γ.target e = i := by
  simp [Multigraph.edgesBetween]

/-- Replacing the gains of a multigraph leaves its topology untouched. -/
def Multigraph.setGain (Γ : Multigraph ι E) (g : E → ℂ) : Multigraph ι E :=
  { Γ with gain := g }

/-- Replacing the gains keeps the edges joining each ordered pair of nodes, so the topology does
not depend on which gains happen to vanish. -/
@[simp]
lemma Multigraph.setGain_edgesBetween [DecidableEq ι] [Fintype E] (Γ : Multigraph ι E)
    (g : E → ℂ) (j i : ι) : (Γ.setGain g).edgesBetween j i = Γ.edgesBetween j i := rfl

/-!

## C. The gain matrix of a multigraph

-/

/-- The gain matrix of a multigraph: the entry for an ordered pair of nodes is the sum of the
gains of the edges joining them, so parallel edges add. -/
noncomputable def Multigraph.toMatrix [DecidableEq ι] [Fintype E] (Γ : Multigraph ι E) :
    Matrix ι ι ℂ := fun i j => ∑ e ∈ Γ.edgesBetween j i, Γ.gain e

/-- The entry of the gain matrix is the sum of the gains of the edges joining that ordered pair of
nodes. -/
lemma Multigraph.toMatrix_apply [DecidableEq ι] [Fintype E] (Γ : Multigraph ι E) (i j : ι) :
    Γ.toMatrix i j = ∑ e ∈ Γ.edgesBetween j i, Γ.gain e := rfl

/-- A multigraph with no edges has the zero gain matrix. -/
@[simp]
lemma Multigraph.toMatrix_of_isEmpty [DecidableEq ι] [Fintype E] [IsEmpty E]
    (Γ : Multigraph ι E) : Γ.toMatrix = 0 := by
  funext i j
  simp [Multigraph.toMatrix, Multigraph.edgesBetween]

end Multigraphs

end Physlib.SignalFlowGraph
