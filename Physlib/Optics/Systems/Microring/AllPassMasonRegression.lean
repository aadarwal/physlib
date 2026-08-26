/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Mathematics.SignalFlowGraph.DefinitionRegression
public import Physlib.Optics.Systems.Microring.AllPassMason
public import Physlib.Optics.Systems.Microring.AllPassRegression

/-!
# Regression tests for all-pass Mason semantics

## i. Overview

The zero-phase `3-4-5` ring has circulation edges `gamma = 1 / 2` and `t = 3 / 5`. Direct
forward-path and loop-family expansion therefore gives determinant `7 / 10`, internal Mason gain
`5 / 7`, and assembled through response `1 / 7`. The already independent raw N5 channel solution
reaches the same value without either Mason/N5 bridge theorem.

The unequal edge gains make an edge-role swap visible: the exact forward anchor `5 / 7` differs
from the incorrect swapped-role value `6 / 7`.

The fixture tests the independently defined reduced circulation model, not a graph reduction from
the complete bidirectional `C * S` graph. The selected parameters satisfy the exact nonzero-
denominator gate used by the response comparison. It asserts no chain, Z-transform, passivity,
reciprocity, resonance extremum, bandwidth, or material interpretation.

## ii. Key results

- `allPassMasonRegression_loopGraphDet`: direct loop-family expansion gives `7 / 10`.
- `allPassMasonRegression_loopNumerator`: direct path expansion gives `1 / 2`.
- `allPassMasonRegression_loopMasonThroughTransfer`: the reduced model gives `1 / 7`.
- `allPassMasonRegression_n5_eq_reducedMason`: raw N5 elimination gives the same value.

## iii. Table of contents

- A. Direct path-and-loop expansion
- B. Independent N5 agreement

## iv. References

This is a Physlib-original adversarial regression for the N5/Mason bridge. It makes no external
source-parity claim.

-/

@[expose] public section

namespace Optics

noncomputable section

namespace AllPass

/-!
## A. Direct path-and-loop expansion
-/

/-- The fixture's reduced circulation model has unequal edge gains `1 / 2` and `3 / 5`. -/
lemma allPassMasonRegression_loopSignalFlowGraph :
    loopSignalFlowGraph allPassRegressionResonanceParameters =
      Physlib.SignalFlowGraph.twoNodeLoop (1 / 2) (3 / 5) := by
  rw [loopSignalFlowGraph,
    allPassRegression_resonance_loopCoefficient]
  ext output input
  fin_cases output <;> fin_cases input <;>
    simp [allPassRegressionResonanceParameters,
      Physlib.SignalFlowGraph.twoNodeLoop]

/-- Direct loop-family expansion gives the reduced circulation determinant `7 / 10`. -/
lemma allPassMasonRegression_loopGraphDet :
    Physlib.SignalFlowGraph.graphDet
        (loopSignalFlowGraph allPassRegressionResonanceParameters) = 7 / 10 := by
  rw [allPassMasonRegression_loopSignalFlowGraph,
    Physlib.SignalFlowGraph.graphDet_twoNodeLoop_direct]
  norm_num

/-- Direct forward-path expansion gives numerator `1 / 2` in the declared source-to-sink order. -/
lemma allPassMasonRegression_loopNumerator :
    Physlib.SignalFlowGraph.masonNumerator
        (loopSignalFlowGraph allPassRegressionResonanceParameters) 0 1 = 1 / 2 := by
  rw [allPassMasonRegression_loopSignalFlowGraph,
    Physlib.SignalFlowGraph.masonNumerator_twoNodeLoop]

/-- Independent path and loop expansion gives the internal Mason gain `5 / 7`. -/
lemma allPassMasonRegression_loopMasonGain :
    loopMasonGain allPassRegressionResonanceParameters = 5 / 7 := by
  rw [loopMasonGain, Physlib.SignalFlowGraph.masonGain,
    allPassMasonRegression_loopNumerator,
    allPassMasonRegression_loopGraphDet]
  norm_num

/-- The required forward Mason gain is not the incorrect swapped-edge value `6 / 7`. -/
lemma allPassMasonRegression_loopMasonGain_ne_swappedEdgeValue :
    loopMasonGain allPassRegressionResonanceParameters ≠ 6 / 7 := by
  rw [allPassMasonRegression_loopMasonGain]
  norm_num

/-- Direct expansion of the bus path, cross-coupler quadrature square, and enumerated loop gives
through gain `1 / 7`. -/
lemma allPassMasonRegression_loopMasonThroughTransfer :
    loopMasonThroughTransfer allPassRegressionResonanceParameters = 1 / 7 := by
  rw [loopMasonThroughTransfer, allPassMasonRegression_loopMasonGain]
  simp [allPassRegressionResonanceParameters, Parameters.coupler,
    DirectionalCoupler.crossCoefficient]
  rw [mul_pow, Complex.I_sq]
  norm_num

/-!
## B. Independent N5 agreement
-/

/-- The raw N5 channel solution and the independently enumerated reduced circulation model agree.
Neither general Mason/N5 bridge theorem is used. -/
lemma allPassMasonRegression_n5_eq_reducedMason :
    (netlist allPassRegressionResonanceParameters).responseTransform
        allPassRegression_resonance_isWellPosed
        (Outgoing.mk (throughChannel allPassRegressionResonanceParameters))
        (Incident.mk (inputChannel allPassRegressionResonanceParameters)) =
      loopMasonThroughTransfer allPassRegressionResonanceParameters := by
  rw [allPassRegression_resonance_responseTransform_entry,
    allPassMasonRegression_loopMasonThroughTransfer]

end AllPass

end

end Optics
