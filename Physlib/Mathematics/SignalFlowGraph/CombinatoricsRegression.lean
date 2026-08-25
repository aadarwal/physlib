/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Mathematics.SignalFlowGraph.BasicRegression
public import Physlib.Mathematics.SignalFlowGraph.Combinatorics

/-!
# Regression tests for the signal-flow combinatorics

## i. Overview

The enumeration of forward paths is decidable, and these examples evaluate it. On three nodes the
forward paths from the first node to the last are exactly the direct hop and the one that goes
through the middle node, and that is checked by evaluation rather than by an argument. On two
nodes there is exactly one forward path, so the numerator of Mason's formula for the two-node
feedback graph is its single path gain; the graph determinant that will divide it is the subject
of a later file.

The path gain and the path cofactor are also evaluated. A path that visits every node leaves no
vertices for loops, so its cofactor is one; this fixes the orientation of the cofactor definition,
which would otherwise be easy to state as the determinant of the vertices the path *does* touch.

## ii. Key results

- `Physlib.SignalFlowGraph.forwardPaths_fin_three`: the forward paths on three nodes, evaluated.
- `Physlib.SignalFlowGraph.pathGain_fin_three`: the gain along the two-hop path.
- `Physlib.SignalFlowGraph.pathCofactor_spanning`: a spanning path has unit cofactor.
- `Physlib.SignalFlowGraph.masonNumerator_twoNodeLoop`: the numerator of Mason's formula for the
  two-node feedback graph is the forward gain.

## iii. Table of contents

- A. Evaluating the forward-path enumeration
- B. Path gains and cofactors
- C. The numerator for the two-node feedback graph

## iv. References

The enumeration mirrors the executable forward-circuit enumeration of U. Siddique,
S. M. Beillahi, and S. Tahar, "On the Formal Analysis of Photonic Signal Processing Systems",
FMICS 2015, LNCS 9128, Definition 3 (p. 168), but over node lists rather than branch lists, so it
does not distinguish parallel edges. That limitation is recorded in
`Physlib.Mathematics.SignalFlowGraph.Combinatorics` and is not repaired here.

These are decidable evaluations and algebraic identities on complex matrices. No physical,
optical, or signal-processing interpretation is asserted.

-/

@[expose] public section

namespace Physlib.SignalFlowGraph

noncomputable section

/-!

## A. Evaluating the forward-path enumeration

-/

/-- On three nodes the forward paths from the first to the last are the direct hop and the one
through the middle node. -/
theorem forwardPaths_fin_three :
    forwardPaths (0 : Fin 3) 2 = {[0, 2], [0, 1, 2]} := by decide

/-- On two nodes there is exactly one forward path from the first to the second. -/
theorem forwardPaths_fin_two : forwardPaths (0 : Fin 2) 1 = {[0, 1]} := by decide

/-- A node is joined to itself by the trivial path alone. -/
theorem forwardPaths_self_fin_two : forwardPaths (0 : Fin 2) 0 = {[0]} := by decide

/-!

## B. Path gains and cofactors

-/

/-- The gain along the two-hop path is the product of its two edge gains, in the order that reads
each edge from its tail to its head. -/
theorem pathGain_fin_three (G : Matrix (Fin 3) (Fin 3) ℂ) :
    pathGain G [0, 1, 2] = G 1 0 * G 2 1 := by
  rw [pathGain_cons_cons, pathGain_cons_cons, pathGain_singleton, mul_one, mul_comm]

/-- A path that visits every node leaves no vertices for loops, so its cofactor is one. This fixes
the orientation of the cofactor: it is the determinant of the vertices the path does **not**
touch. -/
theorem pathCofactor_spanning (G : Matrix (Fin 3) (Fin 3) ℂ) :
    pathCofactor G [0, 1, 2] = 1 := by
  have hcompl : (Finset.univ : Finset (Fin 3)) \ ([0, 1, 2] : List (Fin 3)).toFinset = ∅ := by
    decide
  rw [pathCofactor, hcompl, graphDetOn_empty]

/-- The direct hop on three nodes leaves the middle node free, so its cofactor is the graph
determinant of that single vertex. -/
theorem pathCofactor_direct (G : Matrix (Fin 3) (Fin 3) ℂ) :
    pathCofactor G [0, 2] = graphDetOn G {1} := by
  have hcompl : (Finset.univ : Finset (Fin 3)) \ ([0, 2] : List (Fin 3)).toFinset = {1} := by
    decide
  rw [pathCofactor, hcompl]

/-!

## C. The numerator for the two-node feedback graph

-/

/-- The numerator of Mason's formula for the two-node feedback graph is its single forward path
gain. The determinant that divides it is identified in a later file. -/
theorem masonNumerator_twoNodeLoop (a b : ℂ) :
    masonNumerator (twoNodeLoop a b) 0 1 = a := by
  have hcompl : (Finset.univ : Finset (Fin 2)) \ ([0, 1] : List (Fin 2)).toFinset = ∅ := by
    decide
  rw [masonNumerator, forwardPaths_fin_two, Finset.sum_singleton, pathCofactor, hcompl,
    graphDetOn_empty, mul_one, pathGain_cons_cons, pathGain_singleton, mul_one]
  rfl

end

end Physlib.SignalFlowGraph
