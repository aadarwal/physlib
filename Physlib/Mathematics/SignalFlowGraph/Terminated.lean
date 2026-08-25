/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Mathematics.SignalFlowGraph.EdgeEnumeration

/-!
# Signal-flow graphs with distinguished terminals

## i. Overview

Until now the source and the sink have been arguments of the gain, so a graph carried no notion of
which nodes it is driven at and read from. A terminated graph packages a gain matrix with a
distinguished input node and a distinguished output node, and its transfer function is the gain
between them.

The packaging is thin on purpose: every theorem here is an instance of one already proved. The
transfer function is the entry of the inverse system matrix, it is the algebraic expression driven
by a unit injection at the input, it is Mason's quotient over forward paths, and it is the
edge-level Mason quotient over a multigraph refining it. Those four descriptions of the same
number are what the terminals make it possible to state without naming the two nodes again.

Three of those four identities are unconditional, and it matters why. `transfer` is defined from
Mathlib's inverse, which is totalized: it returns a value at a singular matrix rather than
failing. So the unconditional identities are statements about that totalized expression, not
about a network response. The transfer function acquires its solved-response meaning only where
the system matrix is invertible, and `transfer_eq_of_isNodeSolution` is the statement that carries
it: under invertibility the transfer function is the output component of the unique signal vector
solving the node equations. Away from invertibility no such reading is claimed here.

A multigraph is terminated by choosing the two nodes, and the resulting transfer function is
computed by its own edge-level enumeration, in which parallel edges stay distinct. Two ways of
doing this are offered, and they differ in what they retain: `Multigraph.terminate` produces a
`TerminatedGraph` and therefore forgets edge identity, while `TerminatedMultigraph` bundles the
multigraph itself with the terminals and keeps it.

## ii. Key results

- `Physlib.SignalFlowGraph.TerminatedGraph`: a gain matrix with distinguished terminals.
- `Physlib.SignalFlowGraph.TerminatedGraph.transfer`: its transfer function.
- `Physlib.SignalFlowGraph.TerminatedGraph.transfer_eq_nodeSolution`: the transfer function is the
  output component of the algebraic inverse expression under a unit injection at the input.
- `Physlib.SignalFlowGraph.TerminatedGraph.transfer_eq_of_isNodeSolution`: where the system matrix
  is invertible, it is the output component of a solution of the node equations. This is the
  identity that gives the transfer function a response meaning.
- `Physlib.SignalFlowGraph.TerminatedGraph.transfer_eq_masonGain`: it is Mason's quotient.
- `Physlib.SignalFlowGraph.Multigraph.terminate`: terminating a multigraph, forgetting edges.
- `Physlib.SignalFlowGraph.Multigraph.transfer_terminate_eq_edgeMason`: the transfer function of a
  terminated multigraph is its edge-level Mason quotient.
- `Physlib.SignalFlowGraph.TerminatedMultigraph`: a multigraph bundled with its terminals, edge
  identity retained.

## iii. Table of contents

- A. Terminated graphs
- B. The transfer function and its solution meaning
- C. Terminating a multigraph

## iv. References

The requirement met here is the phrase "with distinguished input/output nodes" in `goal.md`
section H.4 S6. The source development carries the input and output node numbers in its graph
record; see U. Siddique, S. M. Beillahi, and S. Tahar, "On the Formal Analysis of Photonic Signal
Processing Systems", FMICS 2015, LNCS 9128, Definition 1 (p. 167), where an `sfg` is a path
together with a node count, an input node and an output node, and a `path` is a list of branches
`ℕ × ℂ × ℕ`.

The parity claim has to be split between the two structures here, because they do not stand in
the same relation to that record.

`TerminatedMultigraph` matches its shape: the branch list corresponds to the edge-indexed
`Multigraph`, in which parallel edges are distinct objects exactly as distinct branches are; the
node count is carried by the `Fintype` instance; and the two terminal fields are the source's
input and output node numbers. This is parity of representation.

`TerminatedGraph` is **not**. It carries the terminal fields, but its gain matrix has already
summed parallel edges, so the branch list has no counterpart in it. That is the representation
divergence recorded as ledger row IP-21, and `Multigraph.terminate` inherits it, since `toMatrix`
performs exactly that summation. For `TerminatedGraph` the claim is therefore narrower: parity of
the distinguished-terminal fields only, and only when composed with a separate `Multigraph` to
supply the edge layer.

The theorems relating the transfer function to the node equations, to the inverse matrix, and to
the two Mason quotients have no source counterpart.

Deliberately not claimed. Terminating a graph adds no mathematical content: every result here is
an instance of one already proved, and none is stronger. No claim is made that the input and
output nodes are distinct, or that either lies on any loop. `transfer` **is** defined at every
gain matrix, including one whose graph determinant vanishes, because Mathlib's inverse is
totalized; what is not claimed there is that the value it returns is a network response. Only
`transfer_eq_of_isNodeSolution`, which is gated on invertibility, asserts a response reading.

This file is neutral mathematics and imports no physics.

-/

@[expose] public section

namespace Physlib.SignalFlowGraph

open Matrix

/-!

## A. Terminated graphs

-/

/-- A signal-flow graph with distinguished terminals: a gain matrix together with the node it is
driven at and the node it is read from. -/
structure TerminatedGraph (ι : Type*) where
  /-- The gain matrix, whose entry `i j` is the total gain of the edges from `j` into `i`. -/
  gainMatrix : Matrix ι ι ℂ
  /-- The distinguished input node. -/
  input : ι
  /-- The distinguished output node. -/
  output : ι

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The transfer function of a terminated graph: the gain from its input node to its output
node. -/
noncomputable def TerminatedGraph.transfer (S : TerminatedGraph ι) : ℂ :=
  gain S.gainMatrix S.input S.output

/-- The transfer function unfolded. -/
lemma TerminatedGraph.transfer_def (S : TerminatedGraph ι) :
    S.transfer = gain S.gainMatrix S.input S.output := rfl

/-!

## B. The transfer function and its solution meaning

-/

/-- The transfer function is the output component of the algebraic inverse expression driven by a
unit injection at the input node. This is an identity between totalized expressions and holds at
every gain matrix; for the reading of it as a solved response see
`TerminatedGraph.transfer_eq_of_isNodeSolution`. -/
lemma TerminatedGraph.transfer_eq_nodeSolution (S : TerminatedGraph ι) :
    S.transfer = nodeSolution S.gainMatrix (Pi.single S.input 1) S.output :=
  gain_eq_nodeSolution _ _ _

/-- Where the system matrix is invertible, the transfer function is the output component of a
signal vector solving the node equations under a unit injection at the input. Since such a
solution is unique there, this is the statement that gives the transfer function its meaning as a
network response, and it is the only identity in this file that asserts one. -/
lemma TerminatedGraph.transfer_eq_of_isNodeSolution (S : TerminatedGraph ι)
    (h : IsUnit (systemMatrix S.gainMatrix).det) {x : ι → ℂ}
    (hx : IsNodeSolution S.gainMatrix (Pi.single S.input 1) x) :
    S.transfer = x S.output := by
  rw [S.transfer_eq_nodeSolution, eq_nodeSolution h hx]

/-- The transfer function is the corresponding entry of the inverse system matrix. -/
lemma TerminatedGraph.transfer_eq_inv (S : TerminatedGraph ι) :
    S.transfer = (systemMatrix S.gainMatrix)⁻¹ S.output S.input := rfl

/-- The transfer function is Mason's quotient over the forward paths from input to output. -/
lemma TerminatedGraph.transfer_eq_masonGain (S : TerminatedGraph ι)
    (h : graphDet S.gainMatrix ≠ 0) :
    S.transfer = masonGain S.gainMatrix S.input S.output :=
  (masonGain_eq_gain _ _ _ h).symm

/-- The transfer function is the loop-family quotient. Both sides are totalized, so this holds
with no hypothesis on the graph determinant; at a vanishing determinant it equates two totalized
values rather than describing a response. -/
lemma TerminatedGraph.transfer_eq_cyclicNumerator_div (S : TerminatedGraph ι) :
    S.transfer = cyclicNumerator S.gainMatrix S.input S.output / graphDet S.gainMatrix :=
  gain_eq_cyclicNumerator_div_graphDet _ _ _

/-!

## C. Terminating a multigraph

-/

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- Terminating a multigraph by choosing an input node and an output node. This passes through
`toMatrix` and so forgets edge identity; `TerminatedMultigraph` is the variant that keeps it. -/
noncomputable def Multigraph.terminate (Γ : Multigraph ι E) (input output : ι) :
    TerminatedGraph ι :=
  ⟨Γ.toMatrix, input, output⟩

omit [Fintype ι] [DecidableEq E] in
/-- The gain matrix of a terminated multigraph is the multigraph's. -/
@[simp]
lemma Multigraph.gainMatrix_terminate (Γ : Multigraph ι E) (input output : ι) :
    (Γ.terminate input output).gainMatrix = Γ.toMatrix := rfl

omit [Fintype ι] [DecidableEq E] in
/-- The input node of a terminated multigraph. -/
@[simp]
lemma Multigraph.input_terminate (Γ : Multigraph ι E) (input output : ι) :
    (Γ.terminate input output).input = input := rfl

omit [Fintype ι] [DecidableEq E] in
/-- The output node of a terminated multigraph. -/
@[simp]
lemma Multigraph.output_terminate (Γ : Multigraph ι E) (input output : ι) :
    (Γ.terminate input output).output = output := rfl

/-- The transfer function of a terminated multigraph is its edge-level Mason quotient, computed
by an enumeration in which parallel edges stay distinct. -/
lemma Multigraph.transfer_terminate_eq_edgeMason (Γ : Multigraph ι E) (input output : ι)
    (h : graphDet Γ.toMatrix ≠ 0) :
    (Γ.terminate input output).transfer
      = edgeMasonNumerator Γ input output / edgeGraphDet Γ :=
  (edgeMasonGain_eq_gain Γ input output h).symm

/-- A multigraph with distinguished terminals: the edge-indexed graph itself, together with the
node it is driven at and the node it is read from. Unlike `TerminatedGraph` this retains edge
identity, so parallel edges remain distinct objects, and it is this structure rather than
`TerminatedGraph` that has the shape of the source's graph record. -/
structure TerminatedMultigraph (ι : Type*) (E : Type*) where
  /-- The underlying multigraph, in which parallel edges are distinct. -/
  graph : Multigraph ι E
  /-- The distinguished input node. -/
  input : ι
  /-- The distinguished output node. -/
  output : ι

/-- The transfer function of a terminated multigraph. -/
noncomputable def TerminatedMultigraph.transfer (S : TerminatedMultigraph ι E) : ℂ :=
  gain S.graph.toMatrix S.input S.output

/-- Forgetting edge identity: the terminated graph underlying a terminated multigraph. -/
noncomputable def TerminatedMultigraph.toTerminatedGraph (S : TerminatedMultigraph ι E) :
    TerminatedGraph ι :=
  S.graph.terminate S.input S.output

omit [DecidableEq E] in
/-- Forgetting edge identity does not change the transfer function. The content of retaining
edges is in the enumeration, not in the value. -/
lemma TerminatedMultigraph.transfer_toTerminatedGraph (S : TerminatedMultigraph ι E) :
    S.toTerminatedGraph.transfer = S.transfer := rfl

/-- The transfer function of a terminated multigraph is its edge-level Mason quotient, computed
by an enumeration in which parallel edges stay distinct. -/
lemma TerminatedMultigraph.transfer_eq_edgeMason (S : TerminatedMultigraph ι E)
    (h : graphDet S.graph.toMatrix ≠ 0) :
    S.transfer = edgeMasonNumerator S.graph S.input S.output / edgeGraphDet S.graph :=
  (edgeMasonGain_eq_gain S.graph S.input S.output h).symm

omit [DecidableEq E] in
/-- Where the system matrix is invertible, the transfer function of a terminated multigraph is the
output component of a solution of the node equations of the summed gain matrix. -/
lemma TerminatedMultigraph.transfer_eq_of_isNodeSolution (S : TerminatedMultigraph ι E)
    (h : IsUnit (systemMatrix S.graph.toMatrix).det) {x : ι → ℂ}
    (hx : IsNodeSolution S.graph.toMatrix (Pi.single S.input 1) x) :
    S.transfer = x S.output :=
  S.toTerminatedGraph.transfer_eq_of_isNodeSolution h hx

end Physlib.SignalFlowGraph
