/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Mathematics.SignalFlowGraph.Extraction
public import Physlib.Mathematics.SignalFlowGraph.MasonPath
public import Physlib.Optics.Network.FlatNetlistElimination

/-!
# Mason gain for a well-posed flat scattering netlist

## i. Overview

A finite `FlatNetlist` has the implicit incident-amplitude equation

```text
(1 - C * S) a = E_in u.
```

This file extracts the scalar signal-flow graph with gain matrix `C * S`. Its system matrix is
therefore exactly the N5 feedback operator `1 - C * S`, so the graph-determinant gate is equivalent
to relational well-posedness. Mason's gain formula then reconstructs the proof-gated feedback
inverse entry by entry. Substitution into the external readout proves that the Mason response and
the behavior-derived N5 response are the same transform.

## ii. Key results

- `FlatNetlist.feedbackSignalFlowGraph`: the scalar graph with gain matrix `C * S`.
- `FlatNetlist.isWellPosed_iff_feedbackSignalFlowGraph_graphDet_ne_zero`: the exact common gate.
- `FlatNetlist.feedbackMasonTransform`: the matrix of internal Mason gains.
- `FlatNetlist.feedbackMasonTransform_eq_feedbackInverse`: agreement with N5 feedback elimination.
- `FlatNetlist.masonResponseTransform`: the external response assembled from Mason gains.
- `FlatNetlist.responseTransform_eq_masonResponseTransform`: equality with the N5 response.

## iii. Table of contents

- A. Extracting the feedback graph
- B. Internal Mason gains
- C. External response agreement

## iv. References

The construction expands the finite modal coordinates into scalar graph nodes. It is exact on the
same domain as N5 elimination and assumes no contraction or infinite-series convergence. The gain
matrix records the sum of parallel edge gains, so this bridge does not preserve edge identity or
replace the edge-indexed signal-flow layer. It does not instantiate a ring or DCDR topology and
does not by itself prove the broader cross-semantics regressions of `goal.md` section I.3.

The external response is assembled from the internal Mason gains by the existing exposure,
component-scattering, and readout matrices. It is not presented as one distinguished-terminal
Mason graph. No causality, frequency dependence, passivity, losslessness, reciprocity, or physical
realization is asserted.

-/

@[expose] public section

namespace Optics

noncomputable section

universe u v w x

namespace FlatNetlist

variable (netlist : FlatNetlist.{u, v, w, x})
variable [Fintype netlist.Channel] [Fintype netlist.ConnectedChannel]

/-- Classical equality on aggregate channels, kept local to the finite graph extraction. -/
local instance masonChannelDecidableEq : DecidableEq netlist.Channel := Classical.decEq _

/-- Classical equality on connected channels, kept local to the finite graph extraction. -/
local instance masonConnectedChannelDecidableEq : DecidableEq netlist.ConnectedChannel :=
  Classical.decEq _

/-- The external complement remains finite for the assembled response transform. -/
local instance masonExternalChannelFintype : Fintype netlist.ExternalChannel := by
  classical
  infer_instance

/-!

## A. Extracting the feedback graph

-/

/-- The scalar signal-flow graph extracted from the netlist feedback equation. -/
def feedbackSignalFlowGraph : Matrix netlist.IncidentIndex netlist.IncidentIndex ℂ :=
  Physlib.SignalFlowGraph.ofSystemMatrix netlist.feedbackOperator

/-- The extracted graph has exactly the N5 feedback operator as its system matrix. -/
@[simp]
lemma systemMatrix_feedbackSignalFlowGraph :
    Physlib.SignalFlowGraph.systemMatrix netlist.feedbackSignalFlowGraph =
      netlist.feedbackOperator :=
  Physlib.SignalFlowGraph.systemMatrix_ofSystemMatrix netlist.feedbackOperator

/-- The extracted graph gain matrix is literally the routed component transform `C * S`. -/
lemma feedbackSignalFlowGraph_eq_routing_mul_scattering :
    netlist.feedbackSignalFlowGraph =
      netlist.routingTransform * netlist.scatteringTransform := by
  simp [feedbackSignalFlowGraph, Physlib.SignalFlowGraph.ofSystemMatrix,
    feedbackOperator]

/-- The signal-flow graph determinant is the determinant of the N5 feedback operator. -/
lemma graphDet_feedbackSignalFlowGraph :
    Physlib.SignalFlowGraph.graphDet netlist.feedbackSignalFlowGraph =
      netlist.feedbackOperator.det :=
  Physlib.SignalFlowGraph.graphDet_ofSystemMatrix netlist.feedbackOperator

/-- Relational netlist well-posedness is exactly the nonvanishing graph-determinant gate for
Mason's formula. -/
lemma isWellPosed_iff_feedbackSignalFlowGraph_graphDet_ne_zero :
    netlist.IsWellPosed ↔
      Physlib.SignalFlowGraph.graphDet netlist.feedbackSignalFlowGraph ≠ 0 := by
  rw [netlist.graphDet_feedbackSignalFlowGraph,
    netlist.isWellPosed_iff_feedbackOperator_det_ne_zero]

/-!

## B. Internal Mason gains

-/

/-- The proof-gated feedback inverse agrees with Mathlib's total matrix inverse on the well-posed
domain. This lemma is only a comparison; network solving continues to use `feedbackInverse`. -/
lemma feedbackInverse_eq_matrix_inv (hWellPosed : netlist.IsWellPosed) :
    netlist.feedbackInverse hWellPosed = netlist.feedbackOperator⁻¹ := by
  exact (Matrix.inv_eq_left_inv
    (netlist.feedbackInverse_mul_feedbackOperator hWellPosed)).symm

/-- The internal transfer matrix whose `(output, input)` entry is Mason's gain from the input node
to the output node. -/
noncomputable def feedbackMasonTransform :
    ModeTransform netlist.IncidentIndex netlist.IncidentIndex :=
  fun output input ↦
    Physlib.SignalFlowGraph.masonGain netlist.feedbackSignalFlowGraph input output

/-- An entry of the internal Mason transform has the declared source-to-sink order. -/
lemma feedbackMasonTransform_apply
    (output input : netlist.IncidentIndex) :
    netlist.feedbackMasonTransform output input =
      Physlib.SignalFlowGraph.masonGain
        netlist.feedbackSignalFlowGraph input output := rfl

/-- Under the exact N5 well-posedness gate, internal Mason gains reconstruct the proof-gated
feedback inverse entry by entry. -/
lemma feedbackMasonTransform_eq_feedbackInverse
    (hWellPosed : netlist.IsWellPosed) :
    netlist.feedbackMasonTransform = netlist.feedbackInverse hWellPosed := by
  ext output input
  rw [feedbackMasonTransform_apply,
    Physlib.SignalFlowGraph.masonGain_eq_gain _ _ _
      (netlist.isWellPosed_iff_feedbackSignalFlowGraph_graphDet_ne_zero.mp hWellPosed),
    feedbackSignalFlowGraph,
    Physlib.SignalFlowGraph.gain_ofSystemMatrix,
    netlist.feedbackInverse_eq_matrix_inv hWellPosed]

/-!

## C. External response agreement

-/

/-- The external transform obtained by exposure, internal Mason gain, component scattering, and
external readout. -/
noncomputable def masonResponseTransform :
    ModeTransform netlist.ExternalIncident netlist.ExternalOutgoing :=
  netlist.outputReadout * netlist.scatteringTransform *
    netlist.feedbackMasonTransform * netlist.inputExposure

/-- On the common well-posed domain, the behavior-derived N5 response and the response assembled
from Mason gains are exactly the same typed transform. -/
lemma responseTransform_eq_masonResponseTransform
    (hWellPosed : netlist.IsWellPosed) :
    netlist.responseTransform hWellPosed = netlist.masonResponseTransform := by
  rw [netlist.responseTransform_eq_blockFormula,
    netlist.responseBlockFormula_eq, masonResponseTransform,
    netlist.feedbackMasonTransform_eq_feedbackInverse hWellPosed]

end FlatNetlist

end

end Optics
