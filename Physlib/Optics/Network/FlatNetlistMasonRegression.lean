/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Mathematics.SignalFlowGraph.DefinitionRegression
public import Physlib.Optics.Network.FlatNetlistEliminationRegression
public import Physlib.Optics.Network.FlatNetlistMason

/-!
# Regression tests for flat-netlist Mason agreement

## i. Overview

The well-posed shared-link fixture has an internal two-node loop with gains `I` in both directions.
The principal graph is extracted from the independently displayed N5 feedback matrix. Its forward
path numerator is `I`, its loop-family determinant is `2`, and its Mason gain is therefore
`I / 2`. Separately, raw N5 elimination gives the external self-response `1 + 4 * I`; expanding
the direct path, input/output coupling, and the independently computed Mason gain gives the same
value without using either general agreement theorem.

## ii. Scope

These are hostile algebraic fixtures, not passive or physically normalized optical systems. The
loop calculation uses the S6 forward-path and loop-family enumeration lemmas, while the N5 value
uses the separately established exact elimination matrix. It does not provide a ring, DCDR,
edge-identity, frequency-domain, or Z-transform cross-semantics result.

## iii. Table of contents

- A. An extracted nonreal feedback loop

-/

@[expose] public section

namespace Optics

noncomputable section

/-!

## A. An extracted nonreal feedback loop

-/

/-- Aggregate channels in the well-posed fixture are finite. -/
local instance flatNetlistMasonRegressionChannelFintype :
    Fintype flatNetlistEliminationRegression.Channel := by
  change Fintype (Σ _ : (Σ _ : Bool, Bool), Unit)
  infer_instance

/-- Aggregate channels in the well-posed fixture have decidable equality. -/
local instance flatNetlistMasonRegressionChannelDecidableEq :
    DecidableEq flatNetlistEliminationRegression.Channel := Classical.decEq _

/-- Connected channels in the well-posed fixture are finite. -/
local instance flatNetlistMasonRegressionConnectedChannelFintype :
    Fintype flatNetlistEliminationRegression.ConnectedChannel := by
  change Fintype (Σ _ : Unit, Unit ⊕ Unit)
  infer_instance

/-- Connected channels in the well-posed fixture have decidable equality. -/
local instance flatNetlistMasonRegressionConnectedChannelDecidableEq :
    DecidableEq flatNetlistEliminationRegression.ConnectedChannel := Classical.decEq _

/-- The extracted graph system matrix is the independently displayed feedback matrix. -/
lemma flatNetlistMasonRegression_systemMatrix_eq :
    Physlib.SignalFlowGraph.systemMatrix
        flatNetlistEliminationRegression.feedbackSignalFlowGraph =
      flatNetlistEliminationRegressionFeedback := by
  rw [flatNetlistEliminationRegression.systemMatrix_feedbackSignalFlowGraph,
    flatNetlistEliminationRegression_feedbackOperator_eq]

/-- The internal node order is `(B.link, A.link)`, chosen so the A-to-B driven path runs from node
zero to node one. -/
def flatNetlistMasonRegressionInternalNode :
    Fin 2 → flatNetlistEliminationRegression.IncidentIndex :=
  ![Incident.mk flatNetlistEliminationRegressionBLink,
    Incident.mk flatNetlistEliminationRegressionALink]

/-- The principal graph on the two internally wired incident coordinates. -/
def flatNetlistMasonRegressionInternalGraph : Matrix (Fin 2) (Fin 2) ℂ :=
  fun output input ↦
    flatNetlistEliminationRegression.feedbackSignalFlowGraph
      (flatNetlistMasonRegressionInternalNode output)
      (flatNetlistMasonRegressionInternalNode input)

/-- The internal principal graph is the genuine nonreal loop `B.link → A.link → B.link`,
with gain `I` on each directed edge. -/
lemma flatNetlistMasonRegression_internalGraph_eq :
    flatNetlistMasonRegressionInternalGraph =
      Physlib.SignalFlowGraph.twoNodeLoop Complex.I Complex.I := by
  have hBA :
      Incident.mk flatNetlistEliminationRegressionBLink ≠
        Incident.mk flatNetlistEliminationRegressionALink := by
    intro hEqual
    have hComponent := congrArg (fun endpoint ↦ endpoint.channel.1.1) hEqual
    exact Bool.noConfusion hComponent
  have hAB :
      Incident.mk flatNetlistEliminationRegressionALink ≠
        Incident.mk flatNetlistEliminationRegressionBLink := by
    intro hEqual
    have hComponent := congrArg (fun endpoint ↦ endpoint.channel.1.1) hEqual
    exact Bool.noConfusion hComponent
  ext output input
  fin_cases output <;> fin_cases input <;>
    simp [flatNetlistMasonRegressionInternalGraph,
      flatNetlistMasonRegressionInternalNode, FlatNetlist.feedbackSignalFlowGraph,
      Physlib.SignalFlowGraph.ofSystemMatrix,
      flatNetlistEliminationRegression_feedbackOperator_eq,
      flatNetlistEliminationRegressionFeedback, Physlib.SignalFlowGraph.twoNodeLoop,
      hBA, hAB]

/-- Direct loop-family enumeration gives `Δ = 1 - I * I = 2`; this does not use the generic
Mason/N5 bridge or the determinant of the N5 feedback operator. -/
lemma flatNetlistMasonRegression_internalGraph_graphDet :
    Physlib.SignalFlowGraph.graphDet flatNetlistMasonRegressionInternalGraph = 2 := by
  rw [flatNetlistMasonRegression_internalGraph_eq,
    Physlib.SignalFlowGraph.graphDet_twoNodeLoop_direct, Complex.I_mul_I]
  norm_num

/-- Direct forward-path enumeration gives numerator `I` for the path from `B.link` to `A.link`. -/
lemma flatNetlistMasonRegression_internalGraph_numerator :
    Physlib.SignalFlowGraph.masonNumerator flatNetlistMasonRegressionInternalGraph 0 1 =
      Complex.I := by
  rw [flatNetlistMasonRegression_internalGraph_eq,
    Physlib.SignalFlowGraph.masonNumerator_twoNodeLoop]

/-- The independently enumerated path and loop families give the internal Mason gain `I / 2`. -/
lemma flatNetlistMasonRegression_internalGraph_masonGain :
    Physlib.SignalFlowGraph.masonGain flatNetlistMasonRegressionInternalGraph 0 1 =
      Complex.I / 2 := by
  rw [Physlib.SignalFlowGraph.masonGain,
    flatNetlistMasonRegression_internalGraph_numerator,
    flatNetlistMasonRegression_internalGraph_graphDet]

/-- Independent N5 elimination gives the first exposed self-response `1 + 4 * I`. -/
lemma flatNetlistMasonRegression_n5_response_a_to_a :
    flatNetlistEliminationRegression.responseTransform
        flatNetlistEliminationRegression_isWellPosed
        (Outgoing.mk flatNetlistEliminationRegressionExternalA)
        (Incident.mk flatNetlistEliminationRegressionExternalA) = 1 + 4 * Complex.I := by
  rw [flatNetlistEliminationRegression_responseTransform_eq]
  rfl

/-- Raw N5 elimination and the independently enumerated Mason loop give the same response: the
direct gain is `1`, the input couples with gain `2`, and readout couples with gain `4`. Neither
general agreement theorem is used. -/
lemma flatNetlistMasonRegression_n5_response_eq_direct_mason :
    flatNetlistEliminationRegression.responseTransform
        flatNetlistEliminationRegression_isWellPosed
        (Outgoing.mk flatNetlistEliminationRegressionExternalA)
        (Incident.mk flatNetlistEliminationRegressionExternalA) =
      1 + 4 *
        (Physlib.SignalFlowGraph.masonGain
          flatNetlistMasonRegressionInternalGraph 0 1 * 2) := by
  rw [flatNetlistMasonRegression_n5_response_a_to_a,
    flatNetlistMasonRegression_internalGraph_masonGain]
  ring

end

end Optics
