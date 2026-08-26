/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Systems.Cascade.PandaTopologyRegression

/-!
# Numeric and singular regressions for the PANDA response

## i. Overview

The positive fixture uses normalized `3-4-5` and `5-12-13` bus couplers, identity main-ring
quarters, identity-through side couplers, and zero side-ring propagation. The raw 24-edge matrix
is expanded coordinate by coordinate. It gives through response `7/25` and drop response `-24/25`.
The proof does not use either NSV'16 comparison theorem or a Mason/N5 agreement theorem.

The negative fixture changes both bus couplers to identity through-coupling. Its printed source
denominator is zero. A displayed nonzero homogeneous vector satisfies the raw matrix equation,
which forces the graph determinant to vanish. Thus the solve gate is executable and able to fail;
the totalized source quotients are not assigned response meaning at that point.

## ii. Key results

- `Panda.responseRegression_rawNodeEquation`: hand-expanded positive 24-edge matrix anchor.
- `Panda.responseRegression_through`: direct numeric through coordinate `7/25`.
- `Panda.responseRegression_drop`: direct numeric drop coordinate `-24/25`.
- `Panda.responseRegression_singularGraphDet`: explicit determinant-zero point.

## iii. Table of contents

- A. Positive normalized fixture
- B. Hand-expanded matrix anchor
- C. Singular determinant fixture

## iv. Scope

These fixtures audit coherent complex amplitudes. They assert no passivity, reciprocity,
losslessness, causality, convergence, stability, resonance, bandwidth, dispersion, power
normalization, or material realization.
-/

@[expose] public section

namespace Optics

noncomputable section

namespace Panda

open Physlib.SignalFlowGraph

/-! ## A. Positive normalized fixture -/

/-- A zero-phase propagation section with the selected real amplitude. -/
def responseRegressionPropagation (amplitude : ℝ) : MatchedPropagation.Parameters where
  amplitudeTransmission := amplitude
  carrierPathPhase := 0

/-- The positive PANDA fixture with nontrivial normalized input/output couplers. -/
def responseRegressionParameters : Parameters where
  inputCoupler := ⟨3 / 5, 4 / 5⟩
  outputCoupler := ⟨5 / 13, 12 / 13⟩
  rightCoupler := ⟨1, 0⟩
  leftCoupler := ⟨1, 0⟩
  mainQuarterOne := responseRegressionPropagation 1
  mainQuarterTwo := responseRegressionPropagation 1
  mainQuarterThree := responseRegressionPropagation 1
  mainQuarterFour := responseRegressionPropagation 1
  rightHalfOne := responseRegressionPropagation 0
  rightHalfTwo := responseRegressionPropagation 0
  leftHalfOne := responseRegressionPropagation 0
  leftHalfTwo := responseRegressionPropagation 0

/-- The printed symbols corresponding to the positive fixture. -/
def responseRegressionSource : SourceParameters where
  mainRoundTrip := 1
  rightRoundTrip := 0
  leftRoundTrip := 0
  c1 := 3 / 5
  s1 := 4 / 5
  c2 := 5 / 13
  s2 := 12 / 13
  cr := 1
  sr := 0
  cl := 1
  sl := 0

/-- The positive fixture discharges the complete coupler-symbol dictionary. -/
lemma responseRegression_sourceDictionary :
    HasSourceCouplerDictionary responseRegressionParameters responseRegressionSource := by
  constructor <;> norm_num [responseRegressionParameters, responseRegressionSource]

/-- The positive fixture satisfies all four source normalization hypotheses. -/
lemma responseRegression_sourceNormalization :
    HasSourceCouplerNormalization responseRegressionSource := by
  constructor <;> norm_num [responseRegressionSource]

/-- The positive fixture discharges the inherited principal-root gate. -/
lemma responseRegression_principalRootSelection :
    HasPrincipalRootSelection responseRegressionParameters responseRegressionSource := by
  constructor <;>
    simp [responseRegressionParameters, responseRegressionSource,
      responseRegressionPropagation, Parameters.mainQuarterOneCoefficient,
      Parameters.mainQuarterTwoCoefficient, Parameters.mainQuarterThreeCoefficient,
      Parameters.mainQuarterFourCoefficient, Parameters.rightHalfOneCoefficient,
      Parameters.rightHalfTwoCoefficient, Parameters.leftHalfOneCoefficient,
      Parameters.leftHalfTwoCoefficient, Parameters.mainRoundTripCoefficient,
      Parameters.rightRoundTripCoefficient, Parameters.leftRoundTripCoefficient,
      MatchedPropagation.transmissionCoefficient, MatchedPropagation.carrierPhaseFactor]

/-- Direct expansion of the printed denominator gives `10/13`. -/
lemma responseRegression_sourceDenominator :
    sourceDenominator responseRegressionSource = 10 / 13 := by
  norm_num [sourceDenominator, responseRegressionSource]

/-- The positive source denominator is nonzero. -/
lemma responseRegression_hasNonzeroSourceDenominator :
    HasNonzeroSourceDenominator responseRegressionSource := by
  rw [HasNonzeroSourceDenominator, responseRegression_sourceDenominator]
  norm_num

/-! ## B. Hand-expanded matrix anchor -/

/-- The eighteen hand-expanded node values for the positive fixture. -/
def responseRegressionState : Node → ℂ :=
  ![1, -(2 / 5) * Complex.I, 7 / 25, -(26 / 25) * Complex.I,
    -(26 / 25) * Complex.I, 0, -(2 / 5) * Complex.I, -(24 / 25),
    -(26 / 25) * Complex.I, -(26 / 25) * Complex.I, 0, 0, 0,
    -(2 / 5) * Complex.I, -(2 / 5) * Complex.I, 0, 0, 0]

/-- Hand expansion of all 24 retained edges gives the positive node equation.

This proof unfolds the multigraph matrix directly; it does not use `nsv16_throughTransfer`,
`nsv16_dropTransfer`, or a Mason/N5 bridge theorem.
-/
lemma responseRegression_rawNodeEquation :
    responseRegressionState =
      (coefficientMatrix responseRegressionParameters).mulVec responseRegressionState +
        signalInput 1 := by
  funext node
  fin_cases node <;>
    simp [Matrix.mulVec, dotProduct, coefficientMatrix,
      Physlib.SignalFlowGraph.Multigraph.toMatrix_apply,
      Physlib.SignalFlowGraph.Multigraph.edgesBetween, Finset.sum_filter,
      signalMultigraph, edgeSource, edgeTarget, edgeGain, responseRegressionState,
      responseRegressionParameters, responseRegressionPropagation,
      signalInput, Parameters.mainQuarterOneCoefficient,
      Parameters.mainQuarterTwoCoefficient, Parameters.mainQuarterThreeCoefficient,
      Parameters.mainQuarterFourCoefficient, Parameters.rightHalfOneCoefficient,
      Parameters.rightHalfTwoCoefficient, Parameters.leftHalfOneCoefficient,
      Parameters.leftHalfTwoCoefficient, DirectionalCoupler.crossCoefficient,
      MatchedPropagation.transmissionCoefficient, MatchedPropagation.carrierPhaseFactor,
      Fin.sum_univ_succ, Complex.I_sq] <;>
    ring

/-- The positive vector solves the retained graph directly from the raw matrix equation. -/
lemma responseRegression_isNodeSolution :
    IsNodeSolution (signalFlowGraph responseRegressionParameters) (signalInput 1)
      responseRegressionState := by
  rw [IsNodeSolution, signalFlowGraph_eq_coefficientMatrix]
  exact responseRegression_rawNodeEquation

/-- The hand-expanded through coordinate is `7/25`. -/
lemma responseRegression_through : responseRegressionState 2 = 7 / 25 := by
  norm_num [responseRegressionState]

/-- The hand-expanded drop coordinate is `-24/25`. -/
lemma responseRegression_drop : responseRegressionState 7 = -(24 / 25) := by
  norm_num [responseRegressionState]

/-- Independent expansion of the printed through quotient gives the same `7/25`. -/
lemma responseRegression_sourceThrough :
    sourceThroughTransfer responseRegressionSource = 7 / 25 := by
  norm_num [sourceThroughTransfer, sourceThroughNumerator, sourceDenominator,
    responseRegressionSource]

/-- Independent expansion of the printed drop quotient gives the same `-24/25`. -/
lemma responseRegression_sourceDrop :
    sourceDropTransfer responseRegressionSource = -(24 / 25) := by
  norm_num [sourceDropTransfer, sourceDropNumerator, sourceDenominator,
    responseRegressionSource]

/-! ## C. Singular determinant fixture -/

/-- The determinant-zero fixture, with identity through-coupling on all four couplers. -/
def responseRegressionSingularParameters : Parameters where
  inputCoupler := ⟨1, 0⟩
  outputCoupler := ⟨1, 0⟩
  rightCoupler := ⟨1, 0⟩
  leftCoupler := ⟨1, 0⟩
  mainQuarterOne := responseRegressionPropagation 1
  mainQuarterTwo := responseRegressionPropagation 1
  mainQuarterThree := responseRegressionPropagation 1
  mainQuarterFour := responseRegressionPropagation 1
  rightHalfOne := responseRegressionPropagation 0
  rightHalfTwo := responseRegressionPropagation 0
  leftHalfOne := responseRegressionPropagation 0
  leftHalfTwo := responseRegressionPropagation 0

/-- The printed symbols corresponding to the determinant-zero fixture. -/
def responseRegressionSingularSource : SourceParameters where
  mainRoundTrip := 1
  rightRoundTrip := 0
  leftRoundTrip := 0
  c1 := 1
  s1 := 0
  c2 := 1
  s2 := 0
  cr := 1
  sr := 0
  cl := 1
  sl := 0

/-- The singular fixture's printed source denominator is zero. -/
lemma responseRegression_singularSourceDenominator :
    sourceDenominator responseRegressionSingularSource = 0 := by
  norm_num [sourceDenominator, responseRegressionSingularSource]

/-- A nonzero homogeneous circulating state at the singular fixture. -/
def responseRegressionSingularState : Node → ℂ :=
  ![0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0]

/-- The displayed homogeneous state is nonzero. -/
lemma responseRegression_singularState_ne_zero :
    responseRegressionSingularState ≠ 0 := by
  intro hState
  have hOne := congrFun hState (1 : Node)
  norm_num [responseRegressionSingularState] at hOne

/-- Direct expansion of the 24-edge matrix gives the singular homogeneous node equation. -/
lemma responseRegression_singularRawNodeEquation :
    responseRegressionSingularState =
      (coefficientMatrix responseRegressionSingularParameters).mulVec
          responseRegressionSingularState + signalInput 0 := by
  funext node
  fin_cases node <;>
    simp [Matrix.mulVec, dotProduct, coefficientMatrix,
      Physlib.SignalFlowGraph.Multigraph.toMatrix_apply,
      Physlib.SignalFlowGraph.Multigraph.edgesBetween, Finset.sum_filter,
      signalMultigraph, edgeSource, edgeTarget, edgeGain,
      responseRegressionSingularState, responseRegressionSingularParameters,
      responseRegressionPropagation, signalInput,
      Parameters.mainQuarterOneCoefficient, Parameters.mainQuarterTwoCoefficient,
      Parameters.mainQuarterThreeCoefficient, Parameters.mainQuarterFourCoefficient,
      Parameters.rightHalfOneCoefficient, Parameters.rightHalfTwoCoefficient,
      Parameters.leftHalfOneCoefficient, Parameters.leftHalfTwoCoefficient,
      DirectionalCoupler.crossCoefficient, MatchedPropagation.transmissionCoefficient,
      MatchedPropagation.carrierPhaseFactor, Fin.sum_univ_succ]

/-- The displayed nonzero state solves the zero-input singular graph. -/
lemma responseRegression_singularIsNodeSolution :
    IsNodeSolution (signalFlowGraph responseRegressionSingularParameters) 0
      responseRegressionSingularState := by
  have hInput : signalInput 0 = 0 := by
    funext node
    fin_cases node <;> simp [signalInput]
  rw [IsNodeSolution, signalFlowGraph_eq_coefficientMatrix]
  simpa [hInput] using responseRegression_singularRawNodeEquation

/-- The explicit nonzero homogeneous state forces the retained graph determinant to vanish. -/
lemma responseRegression_singularGraphDet :
    graphDet (signalFlowGraph responseRegressionSingularParameters) = 0 := by
  by_contra hGraph
  have hUnit :
      IsUnit (systemMatrix (signalFlowGraph responseRegressionSingularParameters)).det := by
    rw [← graphDet_eq_det]
    exact isUnit_iff_ne_zero.mpr hGraph
  have hSingular := eq_nodeSolution hUnit responseRegression_singularIsNodeSolution
  have hZero := eq_nodeSolution hUnit
    (isNodeSolution_zero (signalFlowGraph responseRegressionSingularParameters))
  exact responseRegression_singularState_ne_zero (hSingular.trans hZero.symm)

end Panda

end

end Optics
