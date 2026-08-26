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
the corresponding assembled N7 scattering entries. The intervening `edgeInput_routedBoundary`
and `edgeOutput_routedBoundary` results certify each edge endpoint against those physical wires.

The resulting relation `NetlistForwardRelation` is phrased only through that N7-entry matrix. Its
equivalence with the graph node equation is the matrix-level bridge requested by the construction;
no separately hand-parameterized graph is admitted.

This is a zero-reverse forward projection. The complete netlist is bidirectional, whereas NSV'16
calls its source SFG undirected. The bridge neither deletes the N7 reverse coordinates nor claims
that the directed 18-node matrix equals an undirected-edge closure.

## ii. Key results

- `Panda.connectionForwardPorts_eq_connection`: all fourteen wires match the graph boundaries.
- `Panda.edgeInput_routedBoundary`: every edge source reaches its local scattering input.
- `Panda.edgeOutput_routedBoundary`: every local scattering output reaches its edge target.
- `Panda.edge_routedN7Certificate`: bundled topology-and-gain ownership of every branch.
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

/-- One representative physical channel for each printed graph node. -/
def nodeN7Channel (p : Parameters) : Node → (netlist p).Channel :=
  ![componentChannel p .inputCoupler ⟨DirectionalCoupler.Port.leftFirst, ()⟩,
    componentChannel p .inputCoupler ⟨DirectionalCoupler.Port.leftSecond, ()⟩,
    componentChannel p .inputCoupler ⟨DirectionalCoupler.Port.rightFirst, ()⟩,
    componentChannel p .inputCoupler ⟨DirectionalCoupler.Port.rightSecond, ()⟩,
    componentChannel p .outputCoupler ⟨DirectionalCoupler.Port.leftFirst, ()⟩,
    componentChannel p .outputCoupler ⟨DirectionalCoupler.Port.leftSecond, ()⟩,
    componentChannel p .outputCoupler ⟨DirectionalCoupler.Port.rightFirst, ()⟩,
    componentChannel p .outputCoupler ⟨DirectionalCoupler.Port.rightSecond, ()⟩,
    componentChannel p .rightCoupler ⟨DirectionalCoupler.Port.leftFirst, ()⟩,
    componentChannel p .rightCoupler ⟨DirectionalCoupler.Port.rightFirst, ()⟩,
    componentChannel p .rightCoupler ⟨DirectionalCoupler.Port.leftSecond, ()⟩,
    componentChannel p .rightCoupler ⟨DirectionalCoupler.Port.rightSecond, ()⟩,
    componentChannel p .rightHalfTwo ⟨MatchedPropagation.Port.left, ()⟩,
    componentChannel p .leftCoupler ⟨DirectionalCoupler.Port.leftFirst, ()⟩,
    componentChannel p .leftCoupler ⟨DirectionalCoupler.Port.rightFirst, ()⟩,
    componentChannel p .leftCoupler ⟨DirectionalCoupler.Port.leftSecond, ()⟩,
    componentChannel p .leftCoupler ⟨DirectionalCoupler.Port.rightSecond, ()⟩,
    componentChannel p .leftHalfTwo ⟨MatchedPropagation.Port.left, ()⟩]

/-- The unique mode at the left endpoint of a PANDA connection. -/
def connectionLeftMode (p : Parameters) (connection : Connection) :
    (netlist p).components.aggregatePortModeFamily.Mode
      ((netlist p).connections.connection connection).left := by
  cases connection <;> exact ()

/-- The unique mode at the right endpoint of a PANDA connection. -/
def connectionRightMode (p : Parameters) (connection : Connection) :
    (netlist p).components.aggregatePortModeFamily.Mode
      ((netlist p).connections.connection connection).right := by
  cases connection <;> exact ()

/-- The aggregate channel at the left endpoint of a PANDA connection. -/
def connectionLeftChannel (p : Parameters) (connection : Connection) : (netlist p).Channel :=
  (netlist p).connections.channelEmbedding
    ⟨connection, Sum.inl (connectionLeftMode p connection)⟩

/-- The aggregate channel at the right endpoint of a PANDA connection. -/
def connectionRightChannel (p : Parameters) (connection : Connection) : (netlist p).Channel :=
  (netlist p).connections.channelEmbedding
    ⟨connection, Sum.inr (connectionRightMode p connection)⟩

/-- Two N7 channels represent the same directed graph boundary when they are identical or are the
two physical endpoints of one declared PANDA connection. -/
def RoutedBoundary (p : Parameters) (first second : (netlist p).Channel) : Prop :=
  first = second ∨
    ∃ connection : Connection,
      (first = connectionLeftChannel p connection ∧
        second = connectionRightChannel p connection) ∨
      (first = connectionRightChannel p connection ∧
        second = connectionLeftChannel p connection)

/-- Equality gives a routed-boundary identification. -/
lemma routedBoundary_refl (p : Parameters) (channel : (netlist p).Channel) :
    RoutedBoundary p channel channel := Or.inl rfl

/-- The left and right channels of a physical connection form one routed boundary. -/
lemma routedBoundary_connection_forward (p : Parameters) (connection : Connection) :
    RoutedBoundary p
      (connectionLeftChannel p connection) (connectionRightChannel p connection) := by
  exact Or.inr ⟨connection, Or.inl ⟨rfl, rfl⟩⟩

/-- The routed-boundary identification is available in the reverse endpoint order. -/
lemma routedBoundary_connection_reverse (p : Parameters) (connection : Connection) :
    RoutedBoundary p
      (connectionRightChannel p connection) (connectionLeftChannel p connection) := by
  exact Or.inr ⟨connection, Or.inr ⟨rfl, rfl⟩⟩

/-- The node assigned to each physical wire is routed to both of that wire's endpoint channels. -/
lemma connectionNode_routedBoundaries (p : Parameters) (connection : Connection) :
    RoutedBoundary p (nodeN7Channel p (connectionNode connection))
        (connectionLeftChannel p connection) ∧
      RoutedBoundary p (nodeN7Channel p (connectionNode connection))
        (connectionRightChannel p connection) := by
  cases connection
  · exact ⟨routedBoundary_refl p _,
      routedBoundary_connection_forward p .inputToQuarterOne⟩
  · exact ⟨routedBoundary_connection_reverse p .quarterOneToRight,
      routedBoundary_refl p _⟩
  · exact ⟨routedBoundary_refl p _,
      routedBoundary_connection_forward p .rightToQuarterTwo⟩
  · exact ⟨routedBoundary_connection_reverse p .quarterTwoToOutput,
      routedBoundary_refl p _⟩
  · exact ⟨routedBoundary_refl p _,
      routedBoundary_connection_forward p .outputToQuarterThree⟩
  · exact ⟨routedBoundary_connection_reverse p .quarterThreeToLeft,
      routedBoundary_refl p _⟩
  · exact ⟨routedBoundary_refl p _,
      routedBoundary_connection_forward p .leftToQuarterFour⟩
  · exact ⟨routedBoundary_connection_reverse p .quarterFourToInput,
      routedBoundary_refl p _⟩
  · exact ⟨routedBoundary_refl p _,
      routedBoundary_connection_forward p .rightToHalfOne⟩
  · exact ⟨routedBoundary_connection_reverse p .rightHalfJoin,
      routedBoundary_refl p _⟩
  · exact ⟨routedBoundary_connection_reverse p .rightHalfTwoToCoupler,
      routedBoundary_refl p _⟩
  · exact ⟨routedBoundary_refl p _,
      routedBoundary_connection_forward p .leftToHalfOne⟩
  · exact ⟨routedBoundary_connection_reverse p .leftHalfJoin,
      routedBoundary_refl p _⟩
  · exact ⟨routedBoundary_connection_reverse p .leftHalfTwoToCoupler,
      routedBoundary_refl p _⟩

/-- Every printed edge source is routed to the incident channel of its owned N7 scattering entry. -/
lemma edgeInput_routedBoundary (p : Parameters) (edge : Edge) :
    RoutedBoundary p (nodeN7Channel p (edgeSource edge)) (edgeN7InputChannel p edge) := by
  fin_cases edge
  all_goals first
    | exact routedBoundary_refl p _
    | exact routedBoundary_connection_forward p .inputToQuarterOne
    | exact routedBoundary_connection_forward p .rightToQuarterTwo
    | exact routedBoundary_connection_forward p .outputToQuarterThree
    | exact routedBoundary_connection_forward p .rightToHalfOne
    | exact routedBoundary_connection_forward p .leftToHalfOne
    | exact routedBoundary_connection_forward p .leftToQuarterFour

/-- Every owned N7 scattering output is routed to the target of its printed graph edge. -/
lemma edgeOutput_routedBoundary (p : Parameters) (edge : Edge) :
    RoutedBoundary p (nodeN7Channel p (edgeTarget edge)) (edgeN7OutputChannel p edge) := by
  fin_cases edge
  all_goals first
    | exact routedBoundary_refl p _
    | exact routedBoundary_connection_reverse p .quarterOneToRight
    | exact routedBoundary_connection_reverse p .rightHalfJoin
    | exact routedBoundary_connection_reverse p .rightHalfTwoToCoupler
    | exact routedBoundary_connection_reverse p .quarterTwoToOutput
    | exact routedBoundary_connection_reverse p .quarterThreeToLeft
    | exact routedBoundary_connection_reverse p .leftHalfJoin
    | exact routedBoundary_connection_reverse p .leftHalfTwoToCoupler
    | exact routedBoundary_connection_reverse p .quarterFourToInput

/-- Each printed branch is one concrete N7 scattering entry between physically routed source and
target boundaries. -/
lemma edge_routedN7Certificate (p : Parameters) (edge : Edge) :
    RoutedBoundary p (nodeN7Channel p (edgeSource edge)) (edgeN7InputChannel p edge) ∧
      edgeGain p edge =
        (netlist p).scatteringTransform
          (Outgoing.mk (edgeN7OutputChannel p edge))
          (Incident.mk (edgeN7InputChannel p edge)) ∧
      RoutedBoundary p (nodeN7Channel p (edgeTarget edge))
        (edgeN7OutputChannel p edge) := by
  exact ⟨edgeInput_routedBoundary p edge, edgeGain_eq_n7ScatteringEntry p edge,
    edgeOutput_routedBoundary p edge⟩

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

private lemma coefficientMatrix_mulVec_apply_zero (p : Parameters) (state : Node → ℂ) :
    (coefficientMatrix p).mulVec state 0 = displayedAction p state 0 := by
  simp [Matrix.mulVec, dotProduct, coefficientMatrix,
    Physlib.SignalFlowGraph.Multigraph.toMatrix_apply,
    Physlib.SignalFlowGraph.Multigraph.edgesBetween, Finset.sum_filter,
    signalMultigraph, edgeSource, edgeTarget, edgeGain, displayedAction,
    Fin.sum_univ_succ, add_comm]

private lemma coefficientMatrix_mulVec_apply_one (p : Parameters) (state : Node → ℂ) :
    (coefficientMatrix p).mulVec state 1 = displayedAction p state 1 := by
  simp [Matrix.mulVec, dotProduct, coefficientMatrix,
    Physlib.SignalFlowGraph.Multigraph.toMatrix_apply,
    Physlib.SignalFlowGraph.Multigraph.edgesBetween, Finset.sum_filter,
    signalMultigraph, edgeSource, edgeTarget, edgeGain, displayedAction,
    Fin.sum_univ_succ, add_comm]

private lemma coefficientMatrix_mulVec_apply_two (p : Parameters) (state : Node → ℂ) :
    (coefficientMatrix p).mulVec state 2 = displayedAction p state 2 := by
  simp [Matrix.mulVec, dotProduct, coefficientMatrix,
    Physlib.SignalFlowGraph.Multigraph.toMatrix_apply,
    Physlib.SignalFlowGraph.Multigraph.edgesBetween, Finset.sum_filter,
    signalMultigraph, edgeSource, edgeTarget, edgeGain, displayedAction,
    Fin.sum_univ_succ, add_comm]

private lemma coefficientMatrix_mulVec_apply_three (p : Parameters) (state : Node → ℂ) :
    (coefficientMatrix p).mulVec state 3 = displayedAction p state 3 := by
  simp [Matrix.mulVec, dotProduct, coefficientMatrix,
    Physlib.SignalFlowGraph.Multigraph.toMatrix_apply,
    Physlib.SignalFlowGraph.Multigraph.edgesBetween, Finset.sum_filter,
    signalMultigraph, edgeSource, edgeTarget, edgeGain, displayedAction,
    Fin.sum_univ_succ, add_comm]

private lemma coefficientMatrix_mulVec_apply_four (p : Parameters) (state : Node → ℂ) :
    (coefficientMatrix p).mulVec state 4 = displayedAction p state 4 := by
  simp [Matrix.mulVec, dotProduct, coefficientMatrix,
    Physlib.SignalFlowGraph.Multigraph.toMatrix_apply,
    Physlib.SignalFlowGraph.Multigraph.edgesBetween, Finset.sum_filter,
    signalMultigraph, edgeSource, edgeTarget, edgeGain, displayedAction,
    Fin.sum_univ_succ, add_comm]

private lemma coefficientMatrix_mulVec_apply_five (p : Parameters) (state : Node → ℂ) :
    (coefficientMatrix p).mulVec state 5 = displayedAction p state 5 := by
  simp [Matrix.mulVec, dotProduct, coefficientMatrix,
    Physlib.SignalFlowGraph.Multigraph.toMatrix_apply,
    Physlib.SignalFlowGraph.Multigraph.edgesBetween, Finset.sum_filter,
    signalMultigraph, edgeSource, edgeTarget, edgeGain, displayedAction,
    Fin.sum_univ_succ, add_comm]

private lemma coefficientMatrix_mulVec_apply_six (p : Parameters) (state : Node → ℂ) :
    (coefficientMatrix p).mulVec state 6 = displayedAction p state 6 := by
  simp [Matrix.mulVec, dotProduct, coefficientMatrix,
    Physlib.SignalFlowGraph.Multigraph.toMatrix_apply,
    Physlib.SignalFlowGraph.Multigraph.edgesBetween, Finset.sum_filter,
    signalMultigraph, edgeSource, edgeTarget, edgeGain, displayedAction,
    Fin.sum_univ_succ, add_comm]

private lemma coefficientMatrix_mulVec_apply_seven (p : Parameters) (state : Node → ℂ) :
    (coefficientMatrix p).mulVec state 7 = displayedAction p state 7 := by
  simp [Matrix.mulVec, dotProduct, coefficientMatrix,
    Physlib.SignalFlowGraph.Multigraph.toMatrix_apply,
    Physlib.SignalFlowGraph.Multigraph.edgesBetween, Finset.sum_filter,
    signalMultigraph, edgeSource, edgeTarget, edgeGain, displayedAction,
    Fin.sum_univ_succ, add_comm]

private lemma coefficientMatrix_mulVec_apply_eight (p : Parameters) (state : Node → ℂ) :
    (coefficientMatrix p).mulVec state 8 = displayedAction p state 8 := by
  simp [Matrix.mulVec, dotProduct, coefficientMatrix,
    Physlib.SignalFlowGraph.Multigraph.toMatrix_apply,
    Physlib.SignalFlowGraph.Multigraph.edgesBetween, Finset.sum_filter,
    signalMultigraph, edgeSource, edgeTarget, edgeGain, displayedAction,
    Fin.sum_univ_succ, add_comm]

private lemma coefficientMatrix_mulVec_apply_nine (p : Parameters) (state : Node → ℂ) :
    (coefficientMatrix p).mulVec state 9 = displayedAction p state 9 := by
  simp [Matrix.mulVec, dotProduct, coefficientMatrix,
    Physlib.SignalFlowGraph.Multigraph.toMatrix_apply,
    Physlib.SignalFlowGraph.Multigraph.edgesBetween, Finset.sum_filter,
    signalMultigraph, edgeSource, edgeTarget, edgeGain, displayedAction,
    Fin.sum_univ_succ, add_comm]

private lemma coefficientMatrix_mulVec_apply_ten (p : Parameters) (state : Node → ℂ) :
    (coefficientMatrix p).mulVec state 10 = displayedAction p state 10 := by
  simp [Matrix.mulVec, dotProduct, coefficientMatrix,
    Physlib.SignalFlowGraph.Multigraph.toMatrix_apply,
    Physlib.SignalFlowGraph.Multigraph.edgesBetween, Finset.sum_filter,
    signalMultigraph, edgeSource, edgeTarget, edgeGain, displayedAction,
    Fin.sum_univ_succ, add_comm]

private lemma coefficientMatrix_mulVec_apply_eleven (p : Parameters) (state : Node → ℂ) :
    (coefficientMatrix p).mulVec state 11 = displayedAction p state 11 := by
  simp [Matrix.mulVec, dotProduct, coefficientMatrix,
    Physlib.SignalFlowGraph.Multigraph.toMatrix_apply,
    Physlib.SignalFlowGraph.Multigraph.edgesBetween, Finset.sum_filter,
    signalMultigraph, edgeSource, edgeTarget, edgeGain, displayedAction,
    Fin.sum_univ_succ, add_comm]

private lemma coefficientMatrix_mulVec_apply_twelve (p : Parameters) (state : Node → ℂ) :
    (coefficientMatrix p).mulVec state 12 = displayedAction p state 12 := by
  simp [Matrix.mulVec, dotProduct, coefficientMatrix,
    Physlib.SignalFlowGraph.Multigraph.toMatrix_apply,
    Physlib.SignalFlowGraph.Multigraph.edgesBetween, Finset.sum_filter,
    signalMultigraph, edgeSource, edgeTarget, edgeGain, displayedAction,
    Fin.sum_univ_succ, add_comm]

private lemma coefficientMatrix_mulVec_apply_thirteen (p : Parameters) (state : Node → ℂ) :
    (coefficientMatrix p).mulVec state 13 = displayedAction p state 13 := by
  simp [Matrix.mulVec, dotProduct, coefficientMatrix,
    Physlib.SignalFlowGraph.Multigraph.toMatrix_apply,
    Physlib.SignalFlowGraph.Multigraph.edgesBetween, Finset.sum_filter,
    signalMultigraph, edgeSource, edgeTarget, edgeGain, displayedAction,
    Fin.sum_univ_succ, add_comm]

private lemma coefficientMatrix_mulVec_apply_fourteen (p : Parameters) (state : Node → ℂ) :
    (coefficientMatrix p).mulVec state 14 = displayedAction p state 14 := by
  simp [Matrix.mulVec, dotProduct, coefficientMatrix,
    Physlib.SignalFlowGraph.Multigraph.toMatrix_apply,
    Physlib.SignalFlowGraph.Multigraph.edgesBetween, Finset.sum_filter,
    signalMultigraph, edgeSource, edgeTarget, edgeGain, displayedAction,
    Fin.sum_univ_succ, add_comm]

private lemma coefficientMatrix_mulVec_apply_fifteen (p : Parameters) (state : Node → ℂ) :
    (coefficientMatrix p).mulVec state 15 = displayedAction p state 15 := by
  simp [Matrix.mulVec, dotProduct, coefficientMatrix,
    Physlib.SignalFlowGraph.Multigraph.toMatrix_apply,
    Physlib.SignalFlowGraph.Multigraph.edgesBetween, Finset.sum_filter,
    signalMultigraph, edgeSource, edgeTarget, edgeGain, displayedAction,
    Fin.sum_univ_succ, add_comm]

private lemma coefficientMatrix_mulVec_apply_sixteen (p : Parameters) (state : Node → ℂ) :
    (coefficientMatrix p).mulVec state 16 = displayedAction p state 16 := by
  simp [Matrix.mulVec, dotProduct, coefficientMatrix,
    Physlib.SignalFlowGraph.Multigraph.toMatrix_apply,
    Physlib.SignalFlowGraph.Multigraph.edgesBetween, Finset.sum_filter,
    signalMultigraph, edgeSource, edgeTarget, edgeGain, displayedAction,
    Fin.sum_univ_succ, add_comm]

private lemma coefficientMatrix_mulVec_apply_seventeen (p : Parameters) (state : Node → ℂ) :
    (coefficientMatrix p).mulVec state 17 = displayedAction p state 17 := by
  simp [Matrix.mulVec, dotProduct, coefficientMatrix,
    Physlib.SignalFlowGraph.Multigraph.toMatrix_apply,
    Physlib.SignalFlowGraph.Multigraph.edgesBetween, Finset.sum_filter,
    signalMultigraph, edgeSource, edgeTarget, edgeGain, displayedAction,
    Fin.sum_univ_succ, add_comm]

/-- Summing the 24 retained edges gives the sparse displayed action. -/
lemma coefficientMatrix_mulVec_eq_displayedAction (p : Parameters) (state : Node → ℂ) :
    (coefficientMatrix p).mulVec state = displayedAction p state := by
  funext output
  fin_cases output
  · exact coefficientMatrix_mulVec_apply_zero p state
  · exact coefficientMatrix_mulVec_apply_one p state
  · exact coefficientMatrix_mulVec_apply_two p state
  · exact coefficientMatrix_mulVec_apply_three p state
  · exact coefficientMatrix_mulVec_apply_four p state
  · exact coefficientMatrix_mulVec_apply_five p state
  · exact coefficientMatrix_mulVec_apply_six p state
  · exact coefficientMatrix_mulVec_apply_seven p state
  · exact coefficientMatrix_mulVec_apply_eight p state
  · exact coefficientMatrix_mulVec_apply_nine p state
  · exact coefficientMatrix_mulVec_apply_ten p state
  · exact coefficientMatrix_mulVec_apply_eleven p state
  · exact coefficientMatrix_mulVec_apply_twelve p state
  · exact coefficientMatrix_mulVec_apply_thirteen p state
  · exact coefficientMatrix_mulVec_apply_fourteen p state
  · exact coefficientMatrix_mulVec_apply_fifteen p state
  · exact coefficientMatrix_mulVec_apply_sixteen p state
  · exact coefficientMatrix_mulVec_apply_seventeen p state

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
