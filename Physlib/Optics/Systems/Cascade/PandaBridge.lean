/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Systems.Cascade.PandaGraph

/-!
# Relational N7 bridge for the PANDA forward graph

## i. Overview

This file certifies that the 18-node PANDA graph is a forward projection of the explicit N7
netlist. The certificate has two independent parts. First, `connectionForwardPorts_eq_connection`
checks all fourteen boundary identifications against the actual `PortConnectionFamily`. Second,
`coefficientMatrix_eq_netlistProjection` proves that every coefficient of the graph is the sum of
the corresponding assembled N7 scattering entries.

The resulting relation `NetlistForwardRelation` is phrased only through that N7-entry matrix. Its
equivalence with the graph node equation is the matrix-level bridge requested by the construction;
no separately hand-parameterized graph is admitted.

This is a zero-reverse forward projection. The complete netlist is bidirectional, whereas NSV'16
calls its source SFG undirected. The bridge neither deletes the N7 reverse coordinates nor claims
that the directed 18-node matrix equals an undirected-edge closure.

## ii. Key results

- `Panda.connectionForwardPorts_eq_connection`: all fourteen wires match the graph boundaries.
- `Panda.coefficientMatrix_eq_netlistProjection`: matrix equality derived from N7 entries.
- `Panda.isNodeSolution_iff_netlistForwardRelation`: relational graph/netlist certificate.
- `Panda.isNodeSolution_iff_forwardEquations`: the 18 explicit forward equations.

## iii. Table of contents

- A. Routing certificate
- B. N7-entry coefficient projection
- C. Explicit forward equations

## iv. References and non-claims

S. M. Beillahi, U. Siddique, and S. Tahar, "Formal Analysis of Engineering Systems Based on
Signal-Flow-Graph Theory", NSV 2016, LNCS 10152, Definition 11, pp. 42-43.

This module asserts no undirected-graph equality, transfer-function formula, passivity,
losslessness, reciprocity, causality, bandwidth, dispersion, stability, resonance, or material
realization.
-/

@[expose] public section

namespace Optics

noncomputable section

namespace Panda

/-! ## A. Routing certificate -/

/-- The graph node identified by each physical wire in the printed forward orientation. -/
def connectionNode : Connection → Node
  | .inputToQuarterOne => 3
  | .quarterOneToRight => 8
  | .rightToQuarterTwo => 9
  | .quarterTwoToOutput => 4
  | .outputToQuarterThree => 6
  | .quarterThreeToLeft => 13
  | .leftToQuarterFour => 14
  | .quarterFourToInput => 1
  | .rightToHalfOne => 11
  | .rightHalfJoin => 12
  | .rightHalfTwoToCoupler => 10
  | .leftToHalfOne => 16
  | .leftHalfJoin => 17
  | .leftHalfTwoToCoupler => 15

/-- The two concrete component ports identified by each PANDA wire. -/
def connectionForwardPorts (p : Parameters) :
    Connection → (components p).aggregatePortModeFamily.Port ×
      (components p).aggregatePortModeFamily.Port
  | .inputToQuarterOne =>
      (⟨Component.inputCoupler, DirectionalCoupler.Port.rightSecond⟩,
        ⟨Component.mainQuarterOne, MatchedPropagation.Port.left⟩)
  | .quarterOneToRight =>
      (⟨Component.mainQuarterOne, MatchedPropagation.Port.right⟩,
        ⟨Component.rightCoupler, DirectionalCoupler.Port.leftFirst⟩)
  | .rightToQuarterTwo =>
      (⟨Component.rightCoupler, DirectionalCoupler.Port.rightFirst⟩,
        ⟨Component.mainQuarterTwo, MatchedPropagation.Port.left⟩)
  | .quarterTwoToOutput =>
      (⟨Component.mainQuarterTwo, MatchedPropagation.Port.right⟩,
        ⟨Component.outputCoupler, DirectionalCoupler.Port.leftFirst⟩)
  | .outputToQuarterThree =>
      (⟨Component.outputCoupler, DirectionalCoupler.Port.rightFirst⟩,
        ⟨Component.mainQuarterThree, MatchedPropagation.Port.left⟩)
  | .quarterThreeToLeft =>
      (⟨Component.mainQuarterThree, MatchedPropagation.Port.right⟩,
        ⟨Component.leftCoupler, DirectionalCoupler.Port.leftFirst⟩)
  | .leftToQuarterFour =>
      (⟨Component.leftCoupler, DirectionalCoupler.Port.rightFirst⟩,
        ⟨Component.mainQuarterFour, MatchedPropagation.Port.left⟩)
  | .quarterFourToInput =>
      (⟨Component.mainQuarterFour, MatchedPropagation.Port.right⟩,
        ⟨Component.inputCoupler, DirectionalCoupler.Port.leftSecond⟩)
  | .rightToHalfOne =>
      (⟨Component.rightCoupler, DirectionalCoupler.Port.rightSecond⟩,
        ⟨Component.rightHalfOne, MatchedPropagation.Port.left⟩)
  | .rightHalfJoin =>
      (⟨Component.rightHalfOne, MatchedPropagation.Port.right⟩,
        ⟨Component.rightHalfTwo, MatchedPropagation.Port.left⟩)
  | .rightHalfTwoToCoupler =>
      (⟨Component.rightHalfTwo, MatchedPropagation.Port.right⟩,
        ⟨Component.rightCoupler, DirectionalCoupler.Port.leftSecond⟩)
  | .leftToHalfOne =>
      (⟨Component.leftCoupler, DirectionalCoupler.Port.rightSecond⟩,
        ⟨Component.leftHalfOne, MatchedPropagation.Port.left⟩)
  | .leftHalfJoin =>
      (⟨Component.leftHalfOne, MatchedPropagation.Port.right⟩,
        ⟨Component.leftHalfTwo, MatchedPropagation.Port.left⟩)
  | .leftHalfTwoToCoupler =>
      (⟨Component.leftHalfTwo, MatchedPropagation.Port.right⟩,
        ⟨Component.leftCoupler, DirectionalCoupler.Port.leftSecond⟩)

/-- Every displayed port pair is exactly the endpoint pair of its declared physical wire. -/
lemma connectionForwardPorts_eq_connection (p : Parameters) (connection : Connection) :
    (connectionForwardPorts p connection).1 =
        ((connections p).connection connection).left ∧
      (connectionForwardPorts p connection).2 =
        ((connections p).connection connection).right := by
  cases connection <;> exact ⟨rfl, rfl⟩

/-! ## B. N7-entry coefficient projection -/

/-- The forward coefficient matrix formed directly from assembled N7 component entries. -/
noncomputable def netlistProjectionMatrix (p : Parameters) : Matrix Node Node ℂ :=
  fun output input ↦
    ∑ edge with edgeSource edge = input ∧ edgeTarget edge = output,
      (netlist p).scatteringTransform
        (Outgoing.mk (edgeN7OutputChannel p edge))
        (Incident.mk (edgeN7InputChannel p edge))

/-- The 24-edge coefficient matrix is exactly its assembled-N7-entry projection. -/
lemma coefficientMatrix_eq_netlistProjection (p : Parameters) :
    coefficientMatrix p = netlistProjectionMatrix p := by
  ext output input
  rw [coefficientMatrix, Physlib.SignalFlowGraph.Multigraph.toMatrix_apply]
  apply Finset.sum_congr rfl
  intro edge hEdge
  exact edgeGain_eq_n7ScatteringEntry p edge

/-- The sparse action of the retained edges in printed node order. -/
def displayedAction (p : Parameters) (state : Node → ℂ) : Node → ℂ :=
  ![0,
    p.mainQuarterFourCoefficient * state 14,
    (p.inputCoupler.throughAmplitude : ℂ) * state 0 +
      DirectionalCoupler.crossCoefficient p.inputCoupler * state 1,
    DirectionalCoupler.crossCoefficient p.inputCoupler * state 0 +
      (p.inputCoupler.throughAmplitude : ℂ) * state 1,
    p.mainQuarterTwoCoefficient * state 9,
    0,
    (p.outputCoupler.throughAmplitude : ℂ) * state 4 +
      DirectionalCoupler.crossCoefficient p.outputCoupler * state 5,
    DirectionalCoupler.crossCoefficient p.outputCoupler * state 4 +
      (p.outputCoupler.throughAmplitude : ℂ) * state 5,
    p.mainQuarterOneCoefficient * state 3,
    (p.rightCoupler.throughAmplitude : ℂ) * state 8 +
      DirectionalCoupler.crossCoefficient p.rightCoupler * state 10,
    p.rightHalfTwoCoefficient * state 12,
    DirectionalCoupler.crossCoefficient p.rightCoupler * state 8 +
      (p.rightCoupler.throughAmplitude : ℂ) * state 10,
    p.rightHalfOneCoefficient * state 11,
    p.mainQuarterThreeCoefficient * state 6,
    (p.leftCoupler.throughAmplitude : ℂ) * state 13 +
      DirectionalCoupler.crossCoefficient p.leftCoupler * state 15,
    p.leftHalfTwoCoefficient * state 17,
    DirectionalCoupler.crossCoefficient p.leftCoupler * state 13 +
      (p.leftCoupler.throughAmplitude : ℂ) * state 15,
    p.leftHalfOneCoefficient * state 16]

/-- Summing the 24 retained edges gives the sparse displayed action. -/
lemma coefficientMatrix_mulVec_eq_displayedAction (p : Parameters) (state : Node → ℂ) :
    (coefficientMatrix p).mulVec state = displayedAction p state := by
  set_option maxHeartbeats 1000000 in
    funext output
    fin_cases output <;>
      simp [Matrix.mulVec, dotProduct, coefficientMatrix,
        Physlib.SignalFlowGraph.Multigraph.toMatrix_apply,
        Physlib.SignalFlowGraph.Multigraph.edgesBetween, Finset.sum_filter,
        signalMultigraph, edgeSource, edgeTarget, edgeGain, displayedAction,
        Fin.sum_univ_succ, add_comm]

/-- The forward N7 relation is the node equation of the netlist-entry projection matrix. -/
def NetlistForwardRelation (p : Parameters) (input : ℂ) (state : Node → ℂ) : Prop :=
  Physlib.SignalFlowGraph.IsNodeSolution
    (netlistProjectionMatrix p) (fun node ↦ if node = 0 then input else 0) state

/-- The graph node equation and the assembled-N7-entry forward relation are equivalent. -/
lemma isNodeSolution_iff_netlistForwardRelation (p : Parameters) (input : ℂ)
    (state : Node → ℂ) :
    Physlib.SignalFlowGraph.IsNodeSolution (signalFlowGraph p)
        (fun node ↦ if node = 0 then input else 0) state ↔
      NetlistForwardRelation p input state := by
  rw [NetlistForwardRelation, signalFlowGraph_eq_coefficientMatrix,
    coefficientMatrix_eq_netlistProjection]

/-! ## C. Explicit forward equations -/

/-- Source-only injection at printed node one. -/
def signalInput (amplitude : ℂ) : Node → ℂ :=
  ![amplitude, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The eighteen forward equations in the node order of NSV'16 Definition 11. -/
structure ForwardEquations (p : Parameters) (input : ℂ) (state : Node → ℂ) : Prop where
  /-- Node one is the supplied source. -/
  nodeOne : state 0 = input
  /-- Node two is the fourth-quarter return to the input coupler. -/
  nodeTwo : state 1 = p.mainQuarterFourCoefficient * state 14
  /-- Node three is the through output. -/
  nodeThree : state 2 =
    (p.inputCoupler.throughAmplitude : ℂ) * state 0 +
      DirectionalCoupler.crossCoefficient p.inputCoupler * state 1
  /-- Node four launches the main ring. -/
  nodeFour : state 3 =
    DirectionalCoupler.crossCoefficient p.inputCoupler * state 0 +
      (p.inputCoupler.throughAmplitude : ℂ) * state 1
  /-- Node five is the second-quarter output. -/
  nodeFive : state 4 = p.mainQuarterTwoCoefficient * state 9
  /-- Node six is the unexcited add input. -/
  nodeSix : state 5 = 0
  /-- Node seven continues around the main ring. -/
  nodeSeven : state 6 =
    (p.outputCoupler.throughAmplitude : ℂ) * state 4 +
      DirectionalCoupler.crossCoefficient p.outputCoupler * state 5
  /-- Node eight is the drop output. -/
  nodeEight : state 7 =
    DirectionalCoupler.crossCoefficient p.outputCoupler * state 4 +
      (p.outputCoupler.throughAmplitude : ℂ) * state 5
  /-- Node nine is the first-quarter output. -/
  nodeNine : state 8 = p.mainQuarterOneCoefficient * state 3
  /-- Node ten is the right coupler's main-ring output. -/
  nodeTen : state 9 =
    (p.rightCoupler.throughAmplitude : ℂ) * state 8 +
      DirectionalCoupler.crossCoefficient p.rightCoupler * state 10
  /-- Node eleven is the second right-half output. -/
  nodeEleven : state 10 = p.rightHalfTwoCoefficient * state 12
  /-- Node twelve launches the right side ring. -/
  nodeTwelve : state 11 =
    DirectionalCoupler.crossCoefficient p.rightCoupler * state 8 +
      (p.rightCoupler.throughAmplitude : ℂ) * state 10
  /-- Node thirteen is the first right-half output. -/
  nodeThirteen : state 12 = p.rightHalfOneCoefficient * state 11
  /-- Node fourteen is the third-quarter output. -/
  nodeFourteen : state 13 = p.mainQuarterThreeCoefficient * state 6
  /-- Node fifteen is the left coupler's main-ring output. -/
  nodeFifteen : state 14 =
    (p.leftCoupler.throughAmplitude : ℂ) * state 13 +
      DirectionalCoupler.crossCoefficient p.leftCoupler * state 15
  /-- Node sixteen is the second left-half output. -/
  nodeSixteen : state 15 = p.leftHalfTwoCoefficient * state 17
  /-- Node seventeen launches the left side ring. -/
  nodeSeventeen : state 16 =
    DirectionalCoupler.crossCoefficient p.leftCoupler * state 13 +
      (p.leftCoupler.throughAmplitude : ℂ) * state 15
  /-- Node eighteen is the first left-half output. -/
  nodeEighteen : state 17 = p.leftHalfOneCoefficient * state 16

/-- The source vector is the single-coordinate injection used by the relational bridge. -/
lemma signalInput_eq_piecewise (input : ℂ) :
    signalInput input = fun node ↦ if node = 0 then input else 0 := by
  funext node
  fin_cases node <;> simp [signalInput]

/-- The retained graph node equation is exactly the eighteen displayed forward equations. -/
lemma isNodeSolution_iff_forwardEquations (p : Parameters) (input : ℂ)
    (state : Node → ℂ) :
    Physlib.SignalFlowGraph.IsNodeSolution (signalFlowGraph p) (signalInput input) state ↔
      ForwardEquations p input state := by
  rw [Physlib.SignalFlowGraph.IsNodeSolution, signalFlowGraph_eq_coefficientMatrix,
    coefficientMatrix_mulVec_eq_displayedAction]
  constructor
  · intro hState
    have h0 := congrFun hState (0 : Node)
    have h1 := congrFun hState (1 : Node)
    have h2 := congrFun hState (2 : Node)
    have h3 := congrFun hState (3 : Node)
    have h4 := congrFun hState (4 : Node)
    have h5 := congrFun hState (5 : Node)
    have h6 := congrFun hState (6 : Node)
    have h7 := congrFun hState (7 : Node)
    have h8 := congrFun hState (8 : Node)
    have h9 := congrFun hState (9 : Node)
    have h10 := congrFun hState (10 : Node)
    have h11 := congrFun hState (11 : Node)
    have h12 := congrFun hState (12 : Node)
    have h13 := congrFun hState (13 : Node)
    have h14 := congrFun hState (14 : Node)
    have h15 := congrFun hState (15 : Node)
    have h16 := congrFun hState (16 : Node)
    have h17 := congrFun hState (17 : Node)
    exact ⟨by simpa [displayedAction, signalInput] using h0,
      by simpa [displayedAction, signalInput] using h1,
      by simpa [displayedAction, signalInput] using h2,
      by simpa [displayedAction, signalInput] using h3,
      by simpa [displayedAction, signalInput] using h4,
      by simpa [displayedAction, signalInput] using h5,
      by simpa [displayedAction, signalInput] using h6,
      by simpa [displayedAction, signalInput] using h7,
      by simpa [displayedAction, signalInput] using h8,
      by simpa [displayedAction, signalInput] using h9,
      by simpa [displayedAction, signalInput] using h10,
      by simpa [displayedAction, signalInput] using h11,
      by simpa [displayedAction, signalInput] using h12,
      by simpa [displayedAction, signalInput] using h13,
      by simpa [displayedAction, signalInput] using h14,
      by simpa [displayedAction, signalInput] using h15,
      by simpa [displayedAction, signalInput] using h16,
      by simpa [displayedAction, signalInput] using h17⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
      h13, h14, h15, h16, h17⟩
    funext node
    fin_cases node
    all_goals simp [displayedAction, signalInput, add_comm] at *
    all_goals assumption

end Panda

end

end Optics
