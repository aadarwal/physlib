/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.FlatNetlistMason
public import Physlib.Optics.Systems.DCDR.Response

/-!
# Mason response of the double-coupler double-ring

## i. Overview

The DCDR has two related Mason presentations. `auditedMasonResponse` is the edge-level quotient of
the certified eight-node, eleven-branch graph, so its enumeration retains every branch identity.
`masonResponse` is the selected entry of the complete response assembled from the N5 netlist's
automatically extracted feedback graph.

The generic extraction defines `FlatNetlist.masonResponseTransform` at
`Physlib/Optics/Network/FlatNetlistMason.lean:168-173`. Its generic N5 agreement theorem is
`FlatNetlist.responseTransform_eq_masonResponseTransform`, at lines 175-182. The G-04 result
`masonResponse_eq_eliminationResponse` below is only an instantiation of that theorem; it does not
re-prove the generic Mason/N5 bridge.

The separately certified eight-node graph has the same exact scalar solve gate. Its edge-level
Mason quotient reaches the independently derived transfer through the graph equations. Combining
that result with the generic instantiation relates both Mason presentations to N5 elimination.
The regression module expands the eight equations and the eleven-branch path/loop enumeration
independently, without using either agreement theorem.

All Mason quotients are totalized algebraic definitions. Their response meaning is asserted only
under `Parameters.HasNonzeroDenominator`. No contraction, infinite series, causality, delay,
region of convergence, pole, zero, stability, passivity, reciprocity, resonance, bandwidth, or
material realization is asserted.

## ii. Key results

- `DCDR.auditedSignalFlowGraph_graphDet_ne_zero_iff`: the audited graph has the N5 solve gate.
- `DCDR.auditedMasonResponse_eq_transfer`: the eleven-branch quotient gives the closed response.
- `DCDR.masonResponse_eq_eliminationResponse`: G-04 by the merged generic Mason/N5 theorem.
- `DCDR.auditedMasonResponse_eq_masonResponse`: both graph presentations agree.

## iii. Table of contents

- A. The two Mason response presentations
- B. The audited graph gate and response
- C. Generic N5/Mason instantiation

## iv. References

U. Siddique, S. M. Beillahi, and S. Tahar, "On the Formal Analysis of Photonic Signal Processing
Systems", FMICS 2015, LNCS 9128, Definitions 1-4 and 8 and Theorem 3 (pp. 167-173).
-/

@[expose] public section

namespace Optics

noncomputable section

namespace DCDR

/-! ## A. The two Mason response presentations -/

/-- The edge-level Mason quotient of the audited eight-node, eleven-branch graph. -/
noncomputable def auditedMasonResponse (p : Parameters) : ℂ :=
  Physlib.SignalFlowGraph.edgeMasonNumerator (signalMultigraph p) 0 7 /
    Physlib.SignalFlowGraph.edgeGraphDet (signalMultigraph p)

/-- The selected external entry of the complete netlist-extracted Mason response. -/
noncomputable def masonResponse (p : Parameters) : ℂ :=
  (netlist p).masonResponseTransform
    (Outgoing.mk (outputChannel p)) (Incident.mk (inputChannel p))

/-! ## B. The audited graph gate and response -/

/-- The unit source injection used by the terminated audited graph is `signalInput 1`. -/
lemma signalInput_one_eq_single :
    signalInput 1 = Pi.single (0 : Node) 1 := by
  funext node
  fin_cases node <;> simp [signalInput, Pi.single]

/-- A nonzero scalar denominator makes the audited graph determinant nonzero. -/
lemma auditedSignalFlowGraph_graphDet_ne_zero_of_hasNonzeroDenominator (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) :
    Physlib.SignalFlowGraph.graphDet (signalFlowGraph p) ≠ 0 := by
  rw [Physlib.SignalFlowGraph.graphDet_eq_det]
  rw [← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det]
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro first second hEqual
  let difference := first - second
  have hKernel :
      (Physlib.SignalFlowGraph.systemMatrix (signalFlowGraph p)).mulVec difference = 0 := by
    simp [difference, Matrix.mulVec_sub, hEqual]
  have hNode : Physlib.SignalFlowGraph.IsNodeSolution
      (signalFlowGraph p) (signalInput 0) difference := by
    rw [Physlib.SignalFlowGraph.isNodeSolution_iff]
    have hInput : signalInput 0 = 0 := by
      funext node
      fin_cases node <;> simp [signalInput]
    rw [hInput]
    exact hKernel
  have hEquations := (isNodeSolution_iff_forwardEquations p 0 difference).mp hNode
  exact sub_eq_zero.mp (hEquations.eq_zero hDenominator)

/-- A zero scalar denominator makes the audited graph determinant vanish. -/
lemma auditedSignalFlowGraph_graphDet_eq_zero_of_denominator_eq_zero (p : Parameters)
    (hDenominator : p.denominator = 0) :
    Physlib.SignalFlowGraph.graphDet (signalFlowGraph p) = 0 := by
  by_contra hGraph
  have hUnit : IsUnit (Physlib.SignalFlowGraph.systemMatrix (signalFlowGraph p)).det := by
    rw [← Physlib.SignalFlowGraph.graphDet_eq_det]
    exact isUnit_iff_ne_zero.mpr hGraph
  have hUnique := Physlib.SignalFlowGraph.eq_nodeSolution hUnit
    (singularForwardState_isNodeSolution p hDenominator)
  have hZero := Physlib.SignalFlowGraph.eq_nodeSolution hUnit
    (Physlib.SignalFlowGraph.isNodeSolution_zero (signalFlowGraph p))
  exact singularForwardState_ne_zero p (hUnique.trans hZero.symm)

/-- The audited eight-node graph and N5 elimination have exactly the same scalar solve gate. -/
lemma auditedSignalFlowGraph_graphDet_ne_zero_iff (p : Parameters) :
    Physlib.SignalFlowGraph.graphDet (signalFlowGraph p) ≠ 0 ↔
      p.HasNonzeroDenominator := by
  constructor
  · intro hGraph hDenominator
    exact hGraph (auditedSignalFlowGraph_graphDet_eq_zero_of_denominator_eq_zero
      p hDenominator)
  · exact auditedSignalFlowGraph_graphDet_ne_zero_of_hasNonzeroDenominator p

/-- The edge-level Mason quotient of the audited graph is the coherent DCDR transfer. -/
lemma auditedMasonResponse_eq_transfer (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) :
    auditedMasonResponse p = transfer p := by
  have hGraph :=
    auditedSignalFlowGraph_graphDet_ne_zero_of_hasNonzeroDenominator p hDenominator
  have hUnit : IsUnit (Physlib.SignalFlowGraph.systemMatrix (signalFlowGraph p)).det := by
    rw [← Physlib.SignalFlowGraph.graphDet_eq_det]
    exact isUnit_iff_ne_zero.mpr hGraph
  let state := Physlib.SignalFlowGraph.nodeSolution (signalFlowGraph p) (signalInput 1)
  have hState : Physlib.SignalFlowGraph.IsNodeSolution
      (signalFlowGraph p) (signalInput 1) state :=
    Physlib.SignalFlowGraph.isNodeSolution_nodeSolution hUnit (signalInput 1)
  have hOutput := ((isNodeSolution_iff_forwardEquations p 1 state).mp hState).output_eq_transfer
    hDenominator
  have hMultigraph :
      Physlib.SignalFlowGraph.graphDet (signalMultigraph p).toMatrix ≠ 0 := by
    simpa only [signalFlowGraph, coefficientMatrix,
      Physlib.SignalFlowGraph.ofCoefficientMatrix] using hGraph
  calc
    auditedMasonResponse p = (terminatedMultigraph p).transfer :=
      (Physlib.SignalFlowGraph.TerminatedMultigraph.transfer_eq_edgeMason
        (terminatedMultigraph p) hMultigraph).symm
    _ = state 7 := by
      apply Physlib.SignalFlowGraph.TerminatedMultigraph.transfer_eq_of_isNodeSolution
      · simpa only [terminatedMultigraph, signalFlowGraph, coefficientMatrix,
          Physlib.SignalFlowGraph.ofCoefficientMatrix] using hUnit
      · simpa only [terminatedMultigraph, signalFlowGraph, coefficientMatrix,
          Physlib.SignalFlowGraph.ofCoefficientMatrix, signalInput_one_eq_single] using hState
    _ = transfer p := by simpa using hOutput

/-! ## C. Generic N5/Mason instantiation -/

/-- The complete extracted feedback graph has exactly the N5 well-posedness gate. -/
lemma feedbackSignalFlowGraph_graphDet_ne_zero_iff (p : Parameters) :
    Physlib.SignalFlowGraph.graphDet (netlist p).feedbackSignalFlowGraph ≠ 0 ↔
      p.HasNonzeroDenominator := by
  rw [← (netlist p).isWellPosed_iff_feedbackSignalFlowGraph_graphDet_ne_zero,
    isWellPosed_iff]

/-- G-04: the DCDR Mason response equals the independently compiled N5 elimination response on
the common scalar solve domain.

This is the DCDR specialization of
`FlatNetlist.responseTransform_eq_masonResponseTransform`; no generic bridge is reproved here.
-/
lemma masonResponse_eq_eliminationResponse (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) :
    masonResponse p =
      eliminationResponse p (isWellPosed_of_hasNonzeroDenominator p hDenominator) := by
  let hWellPosed := isWellPosed_of_hasNonzeroDenominator p hDenominator
  have hAgreement := (netlist p).responseTransform_eq_masonResponseTransform hWellPosed
  exact (congrFun (congrFun hAgreement (Outgoing.mk (outputChannel p)))
    (Incident.mk (inputChannel p))).symm

/-- The edge-indexed audited Mason response and N5 elimination agree on their exact common
domain. -/
lemma auditedMasonResponse_eq_eliminationResponse (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) :
    auditedMasonResponse p =
      eliminationResponse p (isWellPosed_of_hasNonzeroDenominator p hDenominator) := by
  rw [auditedMasonResponse_eq_transfer p hDenominator,
    eliminationResponse_eq_transfer p hDenominator]

/-- The audited eleven-branch quotient and complete extracted Mason response agree on the solve
domain. -/
lemma auditedMasonResponse_eq_masonResponse (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) :
    auditedMasonResponse p = masonResponse p := by
  rw [auditedMasonResponse_eq_eliminationResponse p hDenominator,
    masonResponse_eq_eliminationResponse p hDenominator]

end DCDR

end

end Optics
