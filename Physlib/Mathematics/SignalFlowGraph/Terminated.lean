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
transfer function is the output signal produced by a unit injection at the input, it is the entry
of the inverse system matrix, it is Mason's quotient over forward paths, and it is the edge-level
Mason quotient over a multigraph refining it. Those four descriptions of the same number are what
the terminals make it possible to state without naming the two nodes again each time.

A multigraph is terminated by choosing the two nodes, and the resulting transfer function is
computed by its own edge-level enumeration, in which parallel edges stay distinct.

## ii. Key results

- `Physlib.SignalFlowGraph.TerminatedGraph`: a gain matrix with distinguished terminals.
- `Physlib.SignalFlowGraph.TerminatedGraph.transfer`: its transfer function.
- `Physlib.SignalFlowGraph.TerminatedGraph.transfer_eq_nodeSolution`: the transfer function is the
  output signal under a unit injection at the input.
- `Physlib.SignalFlowGraph.TerminatedGraph.transfer_eq_masonGain`: it is Mason's quotient.
- `Physlib.SignalFlowGraph.Multigraph.terminate`: terminating a multigraph.
- `Physlib.SignalFlowGraph.Multigraph.transfer_terminate_eq_edgeMason`: the transfer function of a
  terminated multigraph is its edge-level Mason quotient.

## iii. Table of contents

- A. Terminated graphs
- B. The four descriptions of the transfer function
- C. Terminating a multigraph

## iv. References

The requirement met here is the phrase "with distinguished input/output nodes" in `goal.md`
section H.4 S6. The source development carries the input and output node numbers in its graph
record; see U. Siddique, S. M. Beillahi, and S. Tahar, "On the Formal Analysis of Photonic Signal
Processing Systems", FMICS 2015, LNCS 9128, Definition 1 (p. 167), where an `sfg` is a path
together with a node count, an input node and an output node. This file is therefore parity of
representation with that source; the theorems relating the transfer function to the node
equations, to the inverse matrix, and to the two Mason quotients have no source counterpart.

Deliberately not claimed. Terminating a graph adds no mathematical content: every result here is
an instance of one already proved, and none is stronger. No claim is made that the input and
output nodes are distinct, that either lies on any loop, or that the transfer function is defined
when the graph determinant vanishes.

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

## B. The four descriptions of the transfer function

-/

/-- The transfer function is the signal at the output node when a unit input is injected at the
input node. -/
lemma TerminatedGraph.transfer_eq_nodeSolution (S : TerminatedGraph ι) :
    S.transfer = nodeSolution S.gainMatrix (Pi.single S.input 1) S.output :=
  gain_eq_nodeSolution _ _ _

/-- The transfer function is the corresponding entry of the inverse system matrix. -/
lemma TerminatedGraph.transfer_eq_inv (S : TerminatedGraph ι) :
    S.transfer = (systemMatrix S.gainMatrix)⁻¹ S.output S.input := rfl

/-- The transfer function is Mason's quotient over the forward paths from input to output. -/
lemma TerminatedGraph.transfer_eq_masonGain (S : TerminatedGraph ι)
    (h : graphDet S.gainMatrix ≠ 0) :
    S.transfer = masonGain S.gainMatrix S.input S.output :=
  (masonGain_eq_gain _ _ _ h).symm

/-- The transfer function is the loop-family quotient. -/
lemma TerminatedGraph.transfer_eq_cyclicNumerator_div (S : TerminatedGraph ι) :
    S.transfer = cyclicNumerator S.gainMatrix S.input S.output / graphDet S.gainMatrix :=
  gain_eq_cyclicNumerator_div_graphDet _ _ _

/-!

## C. Terminating a multigraph

-/

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- Terminating a multigraph by choosing an input node and an output node. -/
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

end Physlib.SignalFlowGraph
