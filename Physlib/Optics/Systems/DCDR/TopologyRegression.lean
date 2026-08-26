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

A second numeric fixture hand-computes all eleven graph gains and an eight-coordinate unit-input
solution, then crosses the relational bridge to complete netlist equations.
`topologyProjection_n7Entries` is a numeric specialization of
`edgeGain_eq_n7ScatteringEntry`, not an independent raw-transform expansion. Its negative control
swaps the first coupler's two launch ports in an actual `FlatNetlist`; the production lift then
fails the rewired incident-assembly equation at the upper path.

These are hostile algebraic topology fixtures. The coupler values are not unitary or passive, and
the tests assert no response, power, stability, pole, zero, resonance, causality, reciprocity, or
material interpretation. Power would mean normalized modal power, not electromagnetic power
before the separately gated Poynting-normalization bridge.

## ii. Key results

- `topologyRegression_connectionEndpoints`: all six netlist wires in endpoint order.
- `topologyRegression_output_fromLower`: direct edge enumeration gives the lower cross entry.
- `topologyRegression_output_fromUpper`: direct edge enumeration gives the upper through entry.
- `topologyRegression_output_orientation`: the unequal entries detect an arm swap.
- `topologyProjection_exists_netlistRealization`: a numeric graph solution lifts to raw netlist
  equations through the relational bridge.
- `topologyProjection_swappedNetlist_rejects_productionLift`: an actual port swap rejects that
  production extraction.

## iii. Table of contents

- A. Asymmetric parameters and physical wiring
- B. Direct edge-level matrix anchors
- C. Numeric graph-to-netlist projection
- D. Rewired-netlist negative control

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

/-! ## C. Numeric graph-to-netlist projection -/

/-- A numeric fixture with zero feedback gain, retaining unequal coupler and arm coefficients. -/
def topologyProjectionParameters : Parameters where
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
    { amplitudeTransmission := 0
      carrierPathPhase := 0 }

/-- The hand-computed eight forward coordinates for unit input at the projection fixture. -/
def topologyProjectionState : Node → ℂ :=
  ![1, 0, 2, -3 * Complex.I, -39 * Complex.I, 22, -349 * Complex.I, -163]

/-- The eight entries of the hand-computed projection state in node order. -/
lemma topologyProjectionState_coordinates :
    topologyProjectionState 0 = 1 ∧
      topologyProjectionState 1 = 0 ∧
      topologyProjectionState 2 = 2 ∧
      topologyProjectionState 3 = -3 * Complex.I ∧
      topologyProjectionState 4 = -39 * Complex.I ∧
      topologyProjectionState 5 = 22 ∧
      topologyProjectionState 6 = -349 * Complex.I ∧
      topologyProjectionState 7 = -163 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The eleven graph gains are the hand-computed numeric N7 component entries. -/
lemma topologyProjection_edgeGains :
    edgeGain topologyProjectionParameters =
      ![2, 11, 5, -3 * Complex.I, 13, -7 * Complex.I,
        -7 * Complex.I, 0, -3 * Complex.I, 2, 5] := by
  funext edge
  fin_cases edge <;>
    simp [edgeGain, topologyProjectionParameters,
      Parameters.upperCoefficient, Parameters.lowerCoefficient,
      Parameters.feedbackCoefficient, DirectionalCoupler.crossCoefficient,
      MatchedPropagation.transmissionCoefficient,
      MatchedPropagation.carrierPhaseFactor]
  all_goals ring

/-- The numeric edge gains are entries of the assembled physical N7 scattering transform. -/
lemma topologyProjection_n7Entries :
    (fun edge =>
      (netlist topologyProjectionParameters).scatteringTransform
        (Outgoing.mk (edgeN7OutputChannel topologyProjectionParameters edge))
        (Incident.mk (edgeN7InputChannel topologyProjectionParameters edge))) =
      ![2, 11, 5, -3 * Complex.I, 13, -7 * Complex.I,
        -7 * Complex.I, 0, -3 * Complex.I, 2, 5] := by
  funext edge
  rw [← edgeGain_eq_n7ScatteringEntry]
  exact congrFun topologyProjection_edgeGains edge

/-- The hand-computed coordinates satisfy all eight numeric forward equations. -/
lemma topologyProjection_forwardEquations :
    ForwardEquations topologyProjectionParameters 1 topologyProjectionState := by
  rcases topologyProjectionState_coordinates with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  constructor <;>
    simp only [h0, h1, h2, h3, h4, h5, h6, h7] <;>
    norm_num [topologyProjectionParameters,
      Parameters.upperCoefficient, Parameters.lowerCoefficient,
      Parameters.feedbackCoefficient, DirectionalCoupler.crossCoefficient,
      MatchedPropagation.transmissionCoefficient,
      MatchedPropagation.carrierPhaseFactor, Complex.I_mul_I, Complex.I_sq] <;>
    ring_nf
  norm_num [Complex.I_sq]

/-- The hand-computed numeric state solves the extracted graph equation. -/
lemma topologyProjection_isNodeSolution :
    Physlib.SignalFlowGraph.IsNodeSolution
      (signalFlowGraph topologyProjectionParameters) (signalInput 1)
      topologyProjectionState := by
  rw [isNodeSolution_iff_forwardEquations]
  exact topologyProjection_forwardEquations

/-- The numeric graph solution lifts through the relational bridge to complete netlist equations. -/
lemma topologyProjection_exists_netlistRealization :
    ∃ incident : ModeAmplitude (netlist topologyProjectionParameters).IncidentIndex,
      ∃ outgoing : ModeAmplitude (netlist topologyProjectionParameters).OutgoingIndex,
        outgoing = (netlist topologyProjectionParameters).scatteringTransform.toLinearMap
            incident ∧
          incident = (netlist topologyProjectionParameters).connections.incidentAssembly
            outgoing (inputAmplitude topologyProjectionParameters 1) ∧
          forwardState topologyProjectionParameters incident outgoing =
            topologyProjectionState := by
  exact (isNodeSolution_iff_exists_netlistRealization
    topologyProjectionParameters 1 topologyProjectionState).mp
      topologyProjection_isNodeSolution

/-! ## D. Rewired-netlist negative control -/

/-- The DCDR wiring with the first coupler's upper and lower launch ports deliberately swapped. -/
def topologySwappedConnections (p : Parameters) :
    PortConnectionFamily (components p).aggregatePortModeFamily Connection where
  connection
    | .firstToUpper =>
        { left := ⟨Component.firstCoupler, DirectionalCoupler.Port.rightSecond⟩
          right := ⟨Component.upperPath, MatchedPropagation.Port.left⟩
          left_ne_right := by intro h; cases h
          modeEquiv := Equiv.refl Unit }
    | .upperToSecond =>
        { left := ⟨Component.upperPath, MatchedPropagation.Port.right⟩
          right := ⟨Component.secondCoupler, DirectionalCoupler.Port.leftFirst⟩
          left_ne_right := by intro h; cases h
          modeEquiv := Equiv.refl Unit }
    | .firstToLower =>
        { left := ⟨Component.firstCoupler, DirectionalCoupler.Port.rightFirst⟩
          right := ⟨Component.lowerPath, MatchedPropagation.Port.left⟩
          left_ne_right := by intro h; cases h
          modeEquiv := Equiv.refl Unit }
    | .lowerToSecond =>
        { left := ⟨Component.lowerPath, MatchedPropagation.Port.right⟩
          right := ⟨Component.secondCoupler, DirectionalCoupler.Port.leftSecond⟩
          left_ne_right := by intro h; cases h
          modeEquiv := Equiv.refl Unit }
    | .secondToFeedback =>
        { left := ⟨Component.secondCoupler, DirectionalCoupler.Port.rightSecond⟩
          right := ⟨Component.feedbackPath, MatchedPropagation.Port.left⟩
          left_ne_right := by intro h; cases h
          modeEquiv := Equiv.refl Unit }
    | .feedbackToFirst =>
        { left := ⟨Component.feedbackPath, MatchedPropagation.Port.right⟩
          right := ⟨Component.firstCoupler, DirectionalCoupler.Port.leftSecond⟩
          left_ne_right := by intro h; cases h
          modeEquiv := Equiv.refl Unit }
  endpointPort_injective := by
    rintro ⟨firstConnection, firstEnd⟩ ⟨secondConnection, secondEnd⟩ hPort
    cases firstConnection <;> cases firstEnd <;>
      cases secondConnection <;> cases secondEnd
    all_goals first | rfl | cases hPort

/-- The deliberately arm-swapped flat netlist used only as a negative-control fixture. -/
def topologySwappedNetlist (p : Parameters) : FlatNetlist where
  components := components p
  Connection := Connection
  connections := topologySwappedConnections p

/-- Every local channel of a swapped fixture connection is finite. -/
noncomputable instance topologySwappedConnectionLocalChannelFintype (p : Parameters)
    (connection : Connection) :
    Fintype ((topologySwappedConnections p).connection connection).LocalChannel := by
  cases connection <;> change Fintype (Unit ⊕ Unit) <;> infer_instance

/-- The swapped fixture has the same finite ambient channel family as the production netlist. -/
noncomputable instance topologySwappedChannelFintype (p : Parameters) :
    Fintype (topologySwappedNetlist p).Channel := by
  change Fintype (components p).aggregatePortModeFamily.Channel
  exact componentsChannelFintype p

/-- The swapped fixture's ambient channels have decidable equality. -/
noncomputable instance topologySwappedChannelDecidableEq (p : Parameters) :
    DecidableEq (topologySwappedNetlist p).Channel := Classical.decEq _

/-- The swapped fixture's connected channels are finite. -/
noncomputable instance topologySwappedConnectedChannelFintype (p : Parameters) :
    Fintype (topologySwappedNetlist p).ConnectedChannel := by
  change Fintype (topologySwappedConnections p).Channel
  infer_instance

/-- The swapped fixture's connected channels have decidable equality. -/
noncomputable instance topologySwappedConnectedChannelDecidableEq (p : Parameters) :
    DecidableEq (topologySwappedNetlist p).ConnectedChannel := Classical.decEq _

/-- Unit input on the swapped fixture's first-coupler left-first external channel. -/
def topologySwappedInputAmplitude (p : Parameters) (input : ℂ) :
    ModeAmplitude (topologySwappedNetlist p).ExternalIncident :=
  WithLp.toLp 2 fun endpoint =>
    match endpoint.channel.1.1.1, endpoint.channel.1.1.2 with
    | .firstCoupler, .leftFirst => input
    | _, _ => 0

/-- In the swapped netlist, the upper path receives the first coupler's lower launch output. -/
lemma topologySwapped_incidentAssembly_apply_upperPath_left (p : Parameters)
    (outgoing : ModeAmplitude (topologySwappedNetlist p).OutgoingIndex)
    (external : ModeAmplitude (topologySwappedNetlist p).ExternalIncident) :
    (topologySwappedNetlist p).connections.incidentAssembly outgoing external
        (Incident.mk (upperPathChannel p MatchedPropagation.Port.left)) =
      outgoing (Outgoing.mk
        (firstCouplerChannel p DirectionalCoupler.Port.rightSecond)) := by
  change
    (topologySwappedNetlist p).connections.incidentAssembly outgoing external
        (Incident.mk ((topologySwappedNetlist p).connections.channelEmbedding
          ⟨Connection.firstToUpper, Sum.inr ()⟩)) = _
  rw [(topologySwappedNetlist p).connections.incidentAssembly_apply_connected_channel]
  rfl

/-- The production graph lift fails the rewired netlist equation: its upper value is `2`, while
the swapped routing supplies the unequal lower launch value `-3 * I`. -/
lemma topologyProjection_swappedNetlist_rejects_productionLift :
    liftedIncident topologyProjectionParameters topologyProjectionState ≠
      (topologySwappedNetlist topologyProjectionParameters).connections.incidentAssembly
        (liftedOutgoing topologyProjectionParameters topologyProjectionState)
        (topologySwappedInputAmplitude topologyProjectionParameters 1) := by
  intro hAssembly
  have hCoordinate := congrArg
    (fun amplitude => amplitude (Incident.mk
      (upperPathChannel topologyProjectionParameters MatchedPropagation.Port.left)))
    hAssembly
  change
    liftedIncident topologyProjectionParameters topologyProjectionState
        (Incident.mk
          (upperPathChannel topologyProjectionParameters MatchedPropagation.Port.left)) =
      (topologySwappedNetlist topologyProjectionParameters).connections.incidentAssembly
        (liftedOutgoing topologyProjectionParameters topologyProjectionState)
        (topologySwappedInputAmplitude topologyProjectionParameters 1)
        (Incident.mk
          (upperPathChannel topologyProjectionParameters MatchedPropagation.Port.left))
      at hCoordinate
  have hRoute := topologySwapped_incidentAssembly_apply_upperPath_left
    topologyProjectionParameters
    (show ModeAmplitude
        (topologySwappedNetlist topologyProjectionParameters).OutgoingIndex from
      liftedOutgoing topologyProjectionParameters topologyProjectionState)
    (topologySwappedInputAmplitude topologyProjectionParameters 1)
  rw [hRoute] at hCoordinate
  have hMismatch : topologyProjectionState 2 = topologyProjectionState 3 := by
    simpa [liftedIncident, liftedOutgoing, upperPathChannel,
      firstCouplerChannel] using hCoordinate
  rw [topologyProjectionState_coordinates.2.2.1,
    topologyProjectionState_coordinates.2.2.2.1] at hMismatch
  have hReal := congrArg Complex.re hMismatch
  norm_num at hReal

end DCDR

end

end Optics
