/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Systems.DCDR.Topology

/-!
# Regression tests for the DCDR topology

## i. Overview

An asymmetric fixed-carrier fixture assigns distinct values to both coupler directions and all
three propagation paths. Direct edge-level summation pins the published eight-node orientation:
the lower input of the second coupler reaches the external output with its cross coefficient,
whereas the upper input reaches it with the unequal through coefficient. A transpose or an arm
swap therefore fails the sentinel.

The connection fixture separately expands all twelve endpoints of the six physical wires. The
matrix anchors do not use `coefficientMatrix_eq_displayed`; they enumerate the concrete retained
edges through `Multigraph.toMatrix`.

These are hostile algebraic topology fixtures. The coupler values are not unitary or passive, and
the tests assert no response, power, stability, pole, zero, resonance, causality, reciprocity, or
material interpretation. Power would mean normalized modal power, not electromagnetic power
before the separately gated Poynting-normalization bridge.

## ii. Key results

- `topologyRegression_connectionEndpoints`: all six netlist wires in endpoint order.
- `topologyRegression_output_fromLower`: direct edge enumeration gives the lower cross entry.
- `topologyRegression_output_fromUpper`: direct edge enumeration gives the upper through entry.
- `topologyRegression_output_orientation`: the unequal entries detect an arm swap.

## iii. Table of contents

- A. Asymmetric parameters and physical wiring
- B. Direct edge-level matrix anchors

## iv. References

The branch order is FMICS 2015, Definition 8 (p. 173). This regression checks Physlib's audited
transcription and makes no additional source claim.
-/

@[expose] public section

namespace Optics

noncomputable section

namespace DCDR

/-! ## A. Asymmetric parameters and physical wiring -/

/-- Distinct algebraic gains used to expose every directed role in the topology. -/
def topologyRegressionParameters : Parameters where
  firstCoupler :=
    { throughAmplitude := 2
      crossAmplitude := 3 }
  secondCoupler :=
    { throughAmplitude := 5
      crossAmplitude := 7 }
  upperPath :=
    { amplitudeTransmission := 11
      carrierPathPhase := 0 }
  lowerPath :=
    { amplitudeTransmission := 13
      carrierPathPhase := 0 }
  feedbackPath :=
    { amplitudeTransmission := 17
      carrierPathPhase := 0 }

/-- The zero-phase paths retain the three distinct real gains. -/
lemma topologyRegression_pathCoefficients :
    topologyRegressionParameters.upperCoefficient = 11 ∧
      topologyRegressionParameters.lowerCoefficient = 13 ∧
      topologyRegressionParameters.feedbackCoefficient = 17 := by
  simp [topologyRegressionParameters, Parameters.upperCoefficient,
    Parameters.lowerCoefficient, Parameters.feedbackCoefficient,
    MatchedPropagation.transmissionCoefficient,
    MatchedPropagation.carrierPhaseFactor]

/-- Direct expansion pins both endpoints of each of the six physical connections. -/
lemma topologyRegression_connectionEndpoints :
    ((connections topologyRegressionParameters).connection
        Connection.firstToUpper).left =
        ⟨Component.firstCoupler, DirectionalCoupler.Port.rightFirst⟩ ∧
      ((connections topologyRegressionParameters).connection
        Connection.firstToUpper).right =
        ⟨Component.upperPath, MatchedPropagation.Port.left⟩ ∧
      ((connections topologyRegressionParameters).connection
        Connection.upperToSecond).left =
        ⟨Component.upperPath, MatchedPropagation.Port.right⟩ ∧
      ((connections topologyRegressionParameters).connection
        Connection.upperToSecond).right =
        ⟨Component.secondCoupler, DirectionalCoupler.Port.leftFirst⟩ ∧
      ((connections topologyRegressionParameters).connection
        Connection.firstToLower).left =
        ⟨Component.firstCoupler, DirectionalCoupler.Port.rightSecond⟩ ∧
      ((connections topologyRegressionParameters).connection
        Connection.firstToLower).right =
        ⟨Component.lowerPath, MatchedPropagation.Port.left⟩ ∧
      ((connections topologyRegressionParameters).connection
        Connection.lowerToSecond).left =
        ⟨Component.lowerPath, MatchedPropagation.Port.right⟩ ∧
      ((connections topologyRegressionParameters).connection
        Connection.lowerToSecond).right =
        ⟨Component.secondCoupler, DirectionalCoupler.Port.leftSecond⟩ ∧
      ((connections topologyRegressionParameters).connection
        Connection.secondToFeedback).left =
        ⟨Component.secondCoupler, DirectionalCoupler.Port.rightSecond⟩ ∧
      ((connections topologyRegressionParameters).connection
        Connection.secondToFeedback).right =
        ⟨Component.feedbackPath, MatchedPropagation.Port.left⟩ ∧
      ((connections topologyRegressionParameters).connection
        Connection.feedbackToFirst).left =
        ⟨Component.feedbackPath, MatchedPropagation.Port.right⟩ ∧
      ((connections topologyRegressionParameters).connection
        Connection.feedbackToFirst).right =
        ⟨Component.firstCoupler, DirectionalCoupler.Port.leftSecond⟩ := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The eleven source-node indices are retained in the audited published order. -/
lemma topologyRegression_edgeSources :
    edgeSource = ![0, 2, 5, 0, 3, 4, 5, 6, 1, 1, 4] := rfl

/-- The eleven target-node indices are retained in the audited published order. -/
lemma topologyRegression_edgeTargets :
    edgeTarget = ![2, 5, 7, 3, 4, 7, 6, 1, 2, 3, 6] := rfl

/-! ## B. Direct edge-level matrix anchors -/

/-- Direct edge enumeration gives the first coupler's upper through entry. -/
lemma topologyRegression_firstUpper :
    coefficientMatrix topologyRegressionParameters 2 0 = 2 := by
  rw [coefficientMatrix, Physlib.SignalFlowGraph.Multigraph.toMatrix_apply]
  change
    (∑ e with
      (signalMultigraph topologyRegressionParameters).source e = 0 ∧
        (signalMultigraph topologyRegressionParameters).target e = 2,
      (signalMultigraph topologyRegressionParameters).gain e) = 2
  rw [Finset.sum_filter]
  simp [signalMultigraph, edgeSource, edgeTarget, edgeGain,
    topologyRegressionParameters, Fin.sum_univ_succ]

/-- Direct edge enumeration gives the feedback propagation entry. -/
lemma topologyRegression_feedback :
    coefficientMatrix topologyRegressionParameters 1 6 = 17 := by
  rw [coefficientMatrix, Physlib.SignalFlowGraph.Multigraph.toMatrix_apply]
  change
    (∑ e with
      (signalMultigraph topologyRegressionParameters).source e = 6 ∧
        (signalMultigraph topologyRegressionParameters).target e = 1,
      (signalMultigraph topologyRegressionParameters).gain e) = 17
  rw [Finset.sum_filter]
  simp [signalMultigraph, edgeSource, edgeTarget, edgeGain,
    topologyRegressionParameters, Parameters.feedbackCoefficient,
    MatchedPropagation.transmissionCoefficient,
    MatchedPropagation.carrierPhaseFactor, Fin.sum_univ_succ]

/-- Direct edge enumeration gives the lower-to-output cross entry `-7 * I`. -/
lemma topologyRegression_output_fromLower :
    coefficientMatrix topologyRegressionParameters 7 4 = -7 * Complex.I := by
  rw [coefficientMatrix, Physlib.SignalFlowGraph.Multigraph.toMatrix_apply]
  change
    (∑ e with
      (signalMultigraph topologyRegressionParameters).source e = 4 ∧
        (signalMultigraph topologyRegressionParameters).target e = 7,
      (signalMultigraph topologyRegressionParameters).gain e) = -7 * Complex.I
  rw [Finset.sum_filter]
  simp [signalMultigraph, edgeSource, edgeTarget, edgeGain,
    topologyRegressionParameters, DirectionalCoupler.crossCoefficient,
    Fin.sum_univ_succ]
  ring

/-- Direct edge enumeration gives the upper-to-output through entry `5`. -/
lemma topologyRegression_output_fromUpper :
    coefficientMatrix topologyRegressionParameters 7 5 = 5 := by
  rw [coefficientMatrix, Physlib.SignalFlowGraph.Multigraph.toMatrix_apply]
  change
    (∑ e with
      (signalMultigraph topologyRegressionParameters).source e = 5 ∧
        (signalMultigraph topologyRegressionParameters).target e = 7,
      (signalMultigraph topologyRegressionParameters).gain e) = 5
  rw [Finset.sum_filter]
  simp [signalMultigraph, edgeSource, edgeTarget, edgeGain,
    topologyRegressionParameters, Fin.sum_univ_succ]

/-- The unequal second-coupler entries detect a lower/upper arm swap or graph transpose. -/
lemma topologyRegression_output_orientation :
    coefficientMatrix topologyRegressionParameters 7 4 ≠
      coefficientMatrix topologyRegressionParameters 7 5 := by
  rw [topologyRegression_output_fromLower, topologyRegression_output_fromUpper]
  intro hEqual
  have hImaginary := congrArg Complex.im hEqual
  norm_num at hImaginary

end DCDR

end

end Optics
