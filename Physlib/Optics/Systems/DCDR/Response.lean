/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.FlatNetlistElimination
public import Physlib.Optics.Systems.DCDR.Topology

/-!
# Elimination response of the double-coupler double-ring

## i. Overview

This file derives the coherent fixed-carrier DCDR response from the complete N7 netlist. The
scalar solve gate is the nonvanishing of the common forward/reverse loop denominator. Under that
gate, both directional feedback systems have only the zero homogeneous solution, so the N5
relation is well posed. Raw component-scattering and routing equations then give the selected
input-to-output response.

`FlatNetlist.responseTransform` is the behavior-derived N5 transform defined at
`Physlib/Optics/Network/FlatNetlistElimination.lean:442-445`, and its agreement with the explicit
four-factor elimination formula is proved there at lines 466-470. Here `eliminationResponse`
selects one entry of that existing transform; it does not define network semantics by a stored
formula.

## ii. Key results

- `DCDR.isWellPosed_iff`: the scalar denominator gate is exactly N5 well-posedness.
- `DCDR.eliminationResponse`: the selected proof-gated N5 response entry.
- `DCDR.eliminationResponse_eq_transfer`: raw N7 elimination gives the closed transfer.

## iii. Table of contents

- A. Scalar response data
- B. Forward and reverse homogeneous equations
- C. Exact N5 solve gate
- D. Selected elimination response

## iv. References

The algebraic `transfer` quotient is totalized by Mathlib. Its netlist-response meaning is asserted
only under `Parameters.HasNonzeroDenominator`. No contraction, infinite-series convergence,
causality, delay, region of convergence, pole, zero, stability, passivity, losslessness,
reciprocity, resonance, bandwidth, or material realization is asserted.

U. Siddique, S. M. Beillahi, and S. Tahar, "On the Formal Analysis of Photonic Signal Processing
Systems", FMICS 2015, LNCS 9128, Definition 8 and Theorem 3 (p. 173). The printed theorem is the
source's incoherent case. Its coherent branch is stated but deferred to unavailable reference [3]
on p. 172; this file derives that coherent N7 branch rather than identifying the two cases.
-/

@[expose] public section

namespace Optics

noncomputable section

namespace DCDR

/-- The response layer uses the same finite external-channel instance as N5 elimination. -/
local instance responseExternalChannelFintype (p : Parameters) :
    Fintype (netlist p).ExternalChannel :=
  (netlist p).eliminationExternalChannelFintype

/-!

## A. Scalar response data

-/

/-- The coherent gain around the DCDR feedback loop. -/
def Parameters.loopGain (p : Parameters) : ℂ :=
  p.feedbackCoefficient *
    ((p.secondCoupler.throughAmplitude : ℂ) * p.lowerCoefficient *
        p.firstCoupler.throughAmplitude +
      DirectionalCoupler.crossCoefficient p.secondCoupler * p.upperCoefficient *
        DirectionalCoupler.crossCoefficient p.firstCoupler)

/-- The scalar denominator of the coherent DCDR feedback solve. -/
def Parameters.denominator (p : Parameters) : ℂ := 1 - p.loopGain

/-- The exact scalar domain on which the coherent DCDR feedback solve is meaningful. -/
def Parameters.HasNonzeroDenominator (p : Parameters) : Prop := p.denominator ≠ 0

/-- The unit-input drive returning through the feedback path. -/
def Parameters.feedbackDrive (p : Parameters) : ℂ :=
  p.feedbackCoefficient *
    ((p.secondCoupler.throughAmplitude : ℂ) * p.lowerCoefficient *
        DirectionalCoupler.crossCoefficient p.firstCoupler +
      DirectionalCoupler.crossCoefficient p.secondCoupler * p.upperCoefficient *
        p.firstCoupler.throughAmplitude)

/-- The direct gain from the source input to the selected output. -/
def Parameters.directGain (p : Parameters) : ℂ :=
  DirectionalCoupler.crossCoefficient p.secondCoupler * p.lowerCoefficient *
      DirectionalCoupler.crossCoefficient p.firstCoupler +
    (p.secondCoupler.throughAmplitude : ℂ) * p.upperCoefficient *
      p.firstCoupler.throughAmplitude

/-- The gain from the feedback input of the first coupler to the selected output. -/
def Parameters.feedbackReadoutGain (p : Parameters) : ℂ :=
  DirectionalCoupler.crossCoefficient p.secondCoupler * p.lowerCoefficient *
      p.firstCoupler.throughAmplitude +
    (p.secondCoupler.throughAmplitude : ℂ) * p.upperCoefficient *
      DirectionalCoupler.crossCoefficient p.firstCoupler

/-- The coherent DCDR response numerator after eliminating the feedback coordinate. -/
def Parameters.responseNumerator (p : Parameters) : ℂ :=
  p.directGain * p.denominator + p.feedbackReadoutGain * p.feedbackDrive

/-- The totalized coherent DCDR transfer quotient.

Its response meaning is proved only under `Parameters.HasNonzeroDenominator`.
-/
def transfer (p : Parameters) : ℂ := p.responseNumerator / p.denominator

/-- Reversing the propagation direction swaps the two coupler roles. -/
def Parameters.reverse (p : Parameters) : Parameters where
  firstCoupler := p.secondCoupler
  secondCoupler := p.firstCoupler
  upperPath := p.upperPath
  lowerPath := p.lowerPath
  feedbackPath := p.feedbackPath

/-- Swapping the couplers leaves the scalar feedback denominator unchanged. -/
lemma Parameters.denominator_reverse (p : Parameters) :
    p.reverse.denominator = p.denominator := by
  change 1 - p.feedbackCoefficient *
      ((p.firstCoupler.throughAmplitude : ℂ) * p.lowerCoefficient *
          p.secondCoupler.throughAmplitude +
        DirectionalCoupler.crossCoefficient p.firstCoupler * p.upperCoefficient *
          DirectionalCoupler.crossCoefficient p.secondCoupler) =
    1 - p.feedbackCoefficient *
      ((p.secondCoupler.throughAmplitude : ℂ) * p.lowerCoefficient *
          p.firstCoupler.throughAmplitude +
        DirectionalCoupler.crossCoefficient p.secondCoupler * p.upperCoefficient *
          DirectionalCoupler.crossCoefficient p.firstCoupler)
  ring

/-!

## B. Forward and reverse homogeneous equations

-/

/-- A forward state satisfying the homogeneous equations vanishes on the solve gate. -/
lemma ForwardEquations.eq_zero {p : Parameters} {state : Node → ℂ}
    (hEquations : ForwardEquations p 0 state) (hDenominator : p.HasNonzeroDenominator) :
    state = 0 := by
  have hLoop : state 1 = p.loopGain * state 1 := by
    calc
      state 1 = p.feedbackCoefficient * state 6 := hEquations.nodeTwo
      _ = p.feedbackCoefficient *
          ((p.secondCoupler.throughAmplitude : ℂ) * state 4 +
            DirectionalCoupler.crossCoefficient p.secondCoupler * state 5) := by
          rw [hEquations.nodeSeven]
      _ = p.loopGain * state 1 := by
          rw [hEquations.nodeFive, hEquations.nodeSix, hEquations.nodeThree,
            hEquations.nodeFour, hEquations.nodeOne]
          simp [Parameters.loopGain]
          ring
  have hFeedback : state 1 = 0 := by
    have hProduct : p.denominator * state 1 = 0 := by
      rw [Parameters.denominator]
      calc
        (1 - p.loopGain) * state 1 = state 1 - p.loopGain * state 1 := by ring
        _ = 0 := sub_eq_zero.mpr hLoop
    exact (mul_eq_zero.mp hProduct).resolve_left hDenominator
  have hInput : state 0 = 0 := hEquations.nodeOne
  have hUpper : state 2 = 0 := by rw [hEquations.nodeThree, hInput, hFeedback]; simp
  have hLower : state 3 = 0 := by rw [hEquations.nodeFour, hInput, hFeedback]; simp
  have hLowerPath : state 4 = 0 := by rw [hEquations.nodeFive, hLower]; simp
  have hUpperPath : state 5 = 0 := by rw [hEquations.nodeSix, hUpper]; simp
  have hReturn : state 6 = 0 := by
    rw [hEquations.nodeSeven, hLowerPath, hUpperPath]
    simp
  have hOutput : state 7 = 0 := by
    rw [hEquations.nodeEight, hLowerPath, hUpperPath]
    simp
  funext node
  fin_cases node <;> assumption

/-- The eight reverse-going boundary coordinates, ordered as the forward graph of `p.reverse`. -/
def reverseState (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex) : Node → ℂ :=
  ![incident (Incident.mk
      (secondCouplerChannel p DirectionalCoupler.Port.rightFirst)),
    incident (Incident.mk
      (secondCouplerChannel p DirectionalCoupler.Port.rightSecond)),
    outgoing (Outgoing.mk
      (secondCouplerChannel p DirectionalCoupler.Port.leftFirst)),
    outgoing (Outgoing.mk
      (secondCouplerChannel p DirectionalCoupler.Port.leftSecond)),
    incident (Incident.mk
      (firstCouplerChannel p DirectionalCoupler.Port.rightSecond)),
    incident (Incident.mk
      (firstCouplerChannel p DirectionalCoupler.Port.rightFirst)),
    outgoing (Outgoing.mk
      (firstCouplerChannel p DirectionalCoupler.Port.leftSecond)),
    outgoing (Outgoing.mk
      (firstCouplerChannel p DirectionalCoupler.Port.leftFirst))]

/-- Reverse propagation through the upper arm gives the corresponding reversed graph coordinate. -/
lemma reverseUpperCoordinate_of_netlistEquations (p : Parameters)
    (external : ModeAmplitude (netlist p).ExternalIncident)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident)
    (hAssembly : incident = (netlist p).connections.incidentAssembly outgoing external) :
    incident (Incident.mk
        (firstCouplerChannel p DirectionalCoupler.Port.rightFirst)) =
      p.upperCoefficient * outgoing (Outgoing.mk
        (secondCouplerChannel p DirectionalCoupler.Port.leftFirst)) := by
  have hFirst := congrArg (fun state => state (Incident.mk
    (firstCouplerChannel p DirectionalCoupler.Port.rightFirst))) hAssembly
  have hPath := scatteringEquation_upperPath_left p incident outgoing hScattering
  have hSecond := congrArg (fun state => state (Incident.mk
    (upperPathChannel p MatchedPropagation.Port.right))) hAssembly
  rw [incidentAssembly_apply_firstCoupler_rightFirst] at hFirst
  rw [incidentAssembly_apply_upperPath_right] at hSecond
  calc
    _ = outgoing (Outgoing.mk (upperPathChannel p MatchedPropagation.Port.left)) := hFirst
    _ = p.upperCoefficient *
        incident (Incident.mk (upperPathChannel p MatchedPropagation.Port.right)) := hPath
    _ = _ := by rw [hSecond]

/-- Reverse propagation through the lower arm gives the corresponding reversed graph coordinate. -/
lemma reverseLowerCoordinate_of_netlistEquations (p : Parameters)
    (external : ModeAmplitude (netlist p).ExternalIncident)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident)
    (hAssembly : incident = (netlist p).connections.incidentAssembly outgoing external) :
    incident (Incident.mk
        (firstCouplerChannel p DirectionalCoupler.Port.rightSecond)) =
      p.lowerCoefficient * outgoing (Outgoing.mk
        (secondCouplerChannel p DirectionalCoupler.Port.leftSecond)) := by
  have hFirst := congrArg (fun state => state (Incident.mk
    (firstCouplerChannel p DirectionalCoupler.Port.rightSecond))) hAssembly
  have hPath := scatteringEquation_lowerPath_left p incident outgoing hScattering
  have hSecond := congrArg (fun state => state (Incident.mk
    (lowerPathChannel p MatchedPropagation.Port.right))) hAssembly
  rw [incidentAssembly_apply_firstCoupler_rightSecond] at hFirst
  rw [incidentAssembly_apply_lowerPath_right] at hSecond
  calc
    _ = outgoing (Outgoing.mk (lowerPathChannel p MatchedPropagation.Port.left)) := hFirst
    _ = p.lowerCoefficient *
        incident (Incident.mk (lowerPathChannel p MatchedPropagation.Port.right)) := hPath
    _ = _ := by rw [hSecond]

/-- Reverse propagation through the feedback arm gives the reversed feedback coordinate. -/
lemma reverseFeedbackCoordinate_of_netlistEquations (p : Parameters)
    (external : ModeAmplitude (netlist p).ExternalIncident)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident)
    (hAssembly : incident = (netlist p).connections.incidentAssembly outgoing external) :
    incident (Incident.mk
        (secondCouplerChannel p DirectionalCoupler.Port.rightSecond)) =
      p.feedbackCoefficient * outgoing (Outgoing.mk
        (firstCouplerChannel p DirectionalCoupler.Port.leftSecond)) := by
  have hSecond := congrArg (fun state => state (Incident.mk
    (secondCouplerChannel p DirectionalCoupler.Port.rightSecond))) hAssembly
  have hPath := scatteringEquation_feedbackPath_left p incident outgoing hScattering
  have hFirst := congrArg (fun state => state (Incident.mk
    (feedbackPathChannel p MatchedPropagation.Port.right))) hAssembly
  rw [incidentAssembly_apply_secondCoupler_rightSecond] at hSecond
  rw [incidentAssembly_apply_feedbackPath_right] at hFirst
  calc
    _ = outgoing (Outgoing.mk (feedbackPathChannel p MatchedPropagation.Port.left)) := hSecond
    _ = p.feedbackCoefficient *
        incident (Incident.mk (feedbackPathChannel p MatchedPropagation.Port.right)) := hPath
    _ = _ := by rw [hFirst]

/-- Raw N7 equations imply the eight reverse equations in the swapped-coupler ordering. -/
lemma reverseEquations_of_netlistEquations (p : Parameters)
    (external : ModeAmplitude (netlist p).ExternalIncident)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident)
    (hAssembly : incident = (netlist p).connections.incidentAssembly outgoing external) :
    ForwardEquations p.reverse (external (Incident.mk (outputChannel p)))
      (reverseState p incident outgoing) := by
  have hInput := congrArg (fun state => state (Incident.mk
    (secondCouplerChannel p DirectionalCoupler.Port.rightFirst))) hAssembly
  rw [incidentAssembly_apply_output] at hInput
  exact ⟨by simpa [reverseState] using hInput,
    by simpa [reverseState, Parameters.reverse, Parameters.feedbackCoefficient] using
      reverseFeedbackCoordinate_of_netlistEquations p external incident outgoing
        hScattering hAssembly,
    by simpa [reverseState, Parameters.reverse] using
      scatteringEquation_secondCoupler_leftFirst p incident outgoing hScattering,
    by simpa [reverseState, Parameters.reverse] using
      scatteringEquation_secondCoupler_leftSecond p incident outgoing hScattering,
    by simpa [reverseState, Parameters.reverse, Parameters.lowerCoefficient] using
      reverseLowerCoordinate_of_netlistEquations p external incident outgoing
        hScattering hAssembly,
    by simpa [reverseState, Parameters.reverse, Parameters.upperCoefficient] using
      reverseUpperCoordinate_of_netlistEquations p external incident outgoing
        hScattering hAssembly,
    by simpa [reverseState, Parameters.reverse, add_comm] using
      scatteringEquation_firstCoupler_leftSecond p incident outgoing hScattering,
    by simpa [reverseState, Parameters.reverse, add_comm] using
      scatteringEquation_firstCoupler_leftFirst p incident outgoing hScattering⟩

/-!

## C. Exact N5 solve gate

-/

/-- A homogeneous complete N7 state vanishes when the scalar denominator is nonzero. -/
lemma feedbackFixedPoint_eq_zero (p : Parameters) (hDenominator : p.HasNonzeroDenominator)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident)
    (hAssembly : incident = (netlist p).connections.incidentAssembly outgoing 0) :
    incident = 0 := by
  have hForward := forwardEquations_of_netlistEquations p 0 incident outgoing hScattering
    hAssembly
  have hForwardZero : forwardState p incident outgoing = 0 :=
    hForward.eq_zero hDenominator
  have hReverse := reverseEquations_of_netlistEquations p 0 incident outgoing hScattering
    hAssembly
  have hReverseDenominator : p.reverse.HasNonzeroDenominator := by
    simpa [Parameters.HasNonzeroDenominator, Parameters.denominator_reverse] using hDenominator
  have hReverseZero : reverseState p incident outgoing = 0 :=
    hReverse.eq_zero hReverseDenominator
  have hUpperLeft := congrArg (fun state => state (Incident.mk
    (upperPathChannel p MatchedPropagation.Port.left))) hAssembly
  have hUpperRight := congrArg (fun state => state (Incident.mk
    (upperPathChannel p MatchedPropagation.Port.right))) hAssembly
  have hLowerLeft := congrArg (fun state => state (Incident.mk
    (lowerPathChannel p MatchedPropagation.Port.left))) hAssembly
  have hLowerRight := congrArg (fun state => state (Incident.mk
    (lowerPathChannel p MatchedPropagation.Port.right))) hAssembly
  have hFeedbackLeft := congrArg (fun state => state (Incident.mk
    (feedbackPathChannel p MatchedPropagation.Port.left))) hAssembly
  have hFeedbackRight := congrArg (fun state => state (Incident.mk
    (feedbackPathChannel p MatchedPropagation.Port.right))) hAssembly
  rw [incidentAssembly_apply_upperPath_left] at hUpperLeft
  rw [incidentAssembly_apply_upperPath_right] at hUpperRight
  rw [incidentAssembly_apply_lowerPath_left] at hLowerLeft
  rw [incidentAssembly_apply_lowerPath_right] at hLowerRight
  rw [incidentAssembly_apply_feedbackPath_left] at hFeedbackLeft
  rw [incidentAssembly_apply_feedbackPath_right] at hFeedbackRight
  apply WithLp.ofLp_injective 2
  funext endpoint
  rcases endpoint with ⟨⟨⟨component, port⟩, mode⟩⟩
  cases component <;> cases port <;> cases mode
  all_goals first
    | simpa [forwardState, firstCouplerChannel] using congrFun hForwardZero (0 : Node)
    | simpa [forwardState, firstCouplerChannel] using congrFun hForwardZero (1 : Node)
    | simpa [reverseState, firstCouplerChannel] using congrFun hReverseZero (5 : Node)
    | simpa [reverseState, firstCouplerChannel] using congrFun hReverseZero (4 : Node)
    | simpa [forwardState, secondCouplerChannel] using congrFun hForwardZero (5 : Node)
    | simpa [forwardState, secondCouplerChannel] using congrFun hForwardZero (4 : Node)
    | simpa [reverseState, secondCouplerChannel] using congrFun hReverseZero (0 : Node)
    | simpa [reverseState, secondCouplerChannel] using congrFun hReverseZero (1 : Node)
    | exact hUpperLeft.trans (by
        simpa [forwardState] using congrFun hForwardZero (2 : Node))
    | exact hUpperRight.trans (by
        simpa [reverseState] using congrFun hReverseZero (2 : Node))
    | exact hLowerLeft.trans (by
        simpa [forwardState] using congrFun hForwardZero (3 : Node))
    | exact hLowerRight.trans (by
        simpa [reverseState] using congrFun hReverseZero (3 : Node))
    | exact hFeedbackLeft.trans (by
        simpa [forwardState] using congrFun hForwardZero (6 : Node))
    | exact hFeedbackRight.trans (by
        simpa [reverseState] using congrFun hReverseZero (6 : Node))

/-- A nonzero scalar denominator makes the complete DCDR netlist well posed. -/
lemma isWellPosed_of_hasNonzeroDenominator (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) : (netlist p).IsWellPosed := by
  rw [(netlist p).isWellPosed_iff_feedbackOperator_injective]
  intro first second hFeedback
  let difference := first - second
  have hKernel : (netlist p).feedbackOperator.toLinearMap difference = 0 := by
    simp [difference, hFeedback]
  let outgoing := (netlist p).scatteringTransform.toLinearMap difference
  have hAssembly : difference = (netlist p).connections.incidentAssembly outgoing 0 := by
    rw [PortConnectionFamily.incidentAssembly, map_zero, add_zero]
    rw [(netlist p).feedbackOperator_apply] at hKernel
    exact sub_eq_zero.mp hKernel
  have hDifference := feedbackFixedPoint_eq_zero p hDenominator difference outgoing rfl hAssembly
  exact sub_eq_zero.mp hDifference

/-- The nonzero forward state displayed when the scalar denominator vanishes. -/
def singularForwardState (p : Parameters) : Node → ℂ :=
  ![0, 1,
    DirectionalCoupler.crossCoefficient p.firstCoupler,
    p.firstCoupler.throughAmplitude,
    p.lowerCoefficient * p.firstCoupler.throughAmplitude,
    p.upperCoefficient * DirectionalCoupler.crossCoefficient p.firstCoupler,
    (p.secondCoupler.throughAmplitude : ℂ) * p.lowerCoefficient *
        p.firstCoupler.throughAmplitude +
      DirectionalCoupler.crossCoefficient p.secondCoupler * p.upperCoefficient *
        DirectionalCoupler.crossCoefficient p.firstCoupler,
    DirectionalCoupler.crossCoefficient p.secondCoupler * p.lowerCoefficient *
        p.firstCoupler.throughAmplitude +
      (p.secondCoupler.throughAmplitude : ℂ) * p.upperCoefficient *
        DirectionalCoupler.crossCoefficient p.firstCoupler]

/-- A zero denominator closes the displayed nonzero homogeneous forward graph state. -/
lemma singularForwardState_isNodeSolution (p : Parameters) (hDenominator : p.denominator = 0) :
    Physlib.SignalFlowGraph.IsNodeSolution
      (signalFlowGraph p) (signalInput 0) (singularForwardState p) := by
  rw [isNodeSolution_iff_forwardEquations]
  have hLoop : p.loopGain = 1 := by
    exact (sub_eq_zero.mp (by simpa [Parameters.denominator] using hDenominator)).symm
  refine ⟨by simp [singularForwardState], ?_, by simp [singularForwardState],
    by simp [singularForwardState], by simp [singularForwardState],
    by simp [singularForwardState], by simp [singularForwardState]; ring,
    by simp [singularForwardState]; ring⟩
  simpa [singularForwardState, Parameters.loopGain] using hLoop.symm

/-- The displayed singular forward state is nonzero. -/
lemma singularForwardState_ne_zero (p : Parameters) : singularForwardState p ≠ 0 := by
  intro hZero
  have hCoordinate := congrFun hZero (1 : Node)
  norm_num [singularForwardState] at hCoordinate

/-- A zero scalar denominator prevents well-posedness of the complete DCDR netlist. -/
lemma not_isWellPosed_of_denominator_eq_zero (p : Parameters)
    (hDenominator : p.denominator = 0) : ¬(netlist p).IsWellPosed := by
  rw [(netlist p).isWellPosed_iff_feedbackOperator_injective]
  intro hInjective
  obtain ⟨incident, outgoing, hScattering, hAssembly, hProjection⟩ :=
    (isNodeSolution_iff_exists_netlistRealization p 0 (singularForwardState p)).mp
      (singularForwardState_isNodeSolution p hDenominator)
  have hInputZero : inputAmplitude p 0 = 0 := by
    ext endpoint
    simp [inputAmplitude]
  rw [hInputZero, PortConnectionFamily.incidentAssembly, map_zero, add_zero] at hAssembly
  have hKernel : (netlist p).feedbackOperator.toLinearMap incident = 0 := by
    rw [(netlist p).feedbackOperator_apply, ← hScattering]
    exact sub_eq_zero.mpr hAssembly
  have hIncident : incident = 0 := hInjective (by simpa using hKernel)
  have hCoordinate := congrFun hProjection (1 : Node)
  rw [hIncident] at hCoordinate
  norm_num [forwardState, singularForwardState] at hCoordinate

/-- N5 well-posedness is exactly the coherent scalar denominator gate. -/
lemma isWellPosed_iff (p : Parameters) :
    (netlist p).IsWellPosed ↔ p.HasNonzeroDenominator := by
  constructor
  · intro hWellPosed hZero
    exact not_isWellPosed_of_denominator_eq_zero p hZero hWellPosed
  · exact isWellPosed_of_hasNonzeroDenominator p

/-!

## D. Selected elimination response

-/

/-- The selected input-to-output entry of the proof-gated N5 response transform. -/
noncomputable def eliminationResponse (p : Parameters) (hWellPosed : (netlist p).IsWellPosed) :
    ℂ :=
  (netlist p).responseTransform hWellPosed
    (Outgoing.mk (outputChannel p)) (Incident.mk (inputChannel p))

/-- External readout returns the second coupler's declared output coordinate. -/
lemma outputReadout_apply_output (p : Parameters)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex) :
    (netlist p).outputReadout.toLinearMap outgoing (Outgoing.mk (outputChannel p)) =
      outgoing (Outgoing.mk
        (secondCouplerChannel p DirectionalCoupler.Port.rightFirst)) := by
  rw [FlatNetlist.outputReadout,
    (netlist p).connections.externalOutgoingReadout_apply,
    ModeAmplitude.restrictEmbedding_apply]
  rfl

/-- The selected N5 response scales a source-only scalar input by `eliminationResponse`. -/
lemma responseTransform_apply_inputAmplitude (p : Parameters)
    (hWellPosed : (netlist p).IsWellPosed) (amplitude : ℂ) :
    ((netlist p).responseTransform hWellPosed).toLinearMap (inputAmplitude p amplitude)
        (Outgoing.mk (outputChannel p)) =
      eliminationResponse p hWellPosed * amplitude := by
  simp [eliminationResponse, inputAmplitude, Matrix.toLpLin_apply]
  ring

/-- Eliminating the feedback coordinate in the eight forward equations gives `transfer`. -/
lemma ForwardEquations.output_eq_transfer {p : Parameters} {input : ℂ} {state : Node → ℂ}
    (hEquations : ForwardEquations p input state)
    (hDenominator : p.HasNonzeroDenominator) :
    state 7 = transfer p * input := by
  change p.denominator ≠ 0 at hDenominator
  have hLoop : state 1 = p.loopGain * state 1 + p.feedbackDrive * input := by
    calc
      state 1 = p.feedbackCoefficient * state 6 := hEquations.nodeTwo
      _ = p.feedbackCoefficient *
          ((p.secondCoupler.throughAmplitude : ℂ) * state 4 +
            DirectionalCoupler.crossCoefficient p.secondCoupler * state 5) := by
          rw [hEquations.nodeSeven]
      _ = p.loopGain * state 1 + p.feedbackDrive * input := by
          rw [hEquations.nodeFive, hEquations.nodeSix, hEquations.nodeThree,
            hEquations.nodeFour, hEquations.nodeOne]
          simp [Parameters.loopGain, Parameters.feedbackDrive]
          ring
  have hFeedback : state 1 = p.feedbackDrive * input / p.denominator := by
    apply (eq_div_iff hDenominator).2
    rw [Parameters.denominator]
    linear_combination hLoop
  have hOutput : state 7 =
      p.directGain * input + p.feedbackReadoutGain * state 1 := by
    rw [hEquations.nodeEight, hEquations.nodeFive, hEquations.nodeSix,
      hEquations.nodeThree, hEquations.nodeFour, hEquations.nodeOne]
    simp [Parameters.directGain, Parameters.feedbackReadoutGain]
    ring
  rw [hOutput, hFeedback, transfer, Parameters.responseNumerator,
    div_eq_mul_inv]
  have hInverse : p.denominator * p.denominator⁻¹ = 1 :=
    mul_inv_cancel₀ hDenominator
  calc
    p.directGain * input +
          p.feedbackReadoutGain * (p.feedbackDrive * input * p.denominator⁻¹) =
        p.directGain * input +
          p.feedbackReadoutGain * p.feedbackDrive * input * p.denominator⁻¹ := by ring
    _ = p.directGain * input * (p.denominator * p.denominator⁻¹) +
          p.feedbackReadoutGain * p.feedbackDrive * input * p.denominator⁻¹ := by
        simp [hInverse]
    _ = (p.directGain * p.denominator + p.feedbackReadoutGain * p.feedbackDrive) *
          p.denominator⁻¹ * input := by ring

/-- Raw N7 equations give the closed DCDR transfer as the selected N5 response entry. -/
lemma eliminationResponse_eq_transfer (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) :
    eliminationResponse p (isWellPosed_of_hasNonzeroDenominator p hDenominator) = transfer p := by
  let hWellPosed := isWellPosed_of_hasNonzeroDenominator p hDenominator
  let output := ((netlist p).responseTransform hWellPosed).toLinearMap (inputAmplitude p 1)
  have hMember : (inputAmplitude p 1, output) ∈ (netlist p).behavior := by
    rw [← (netlist p).toBehavior_responseTransform hWellPosed,
      ModeTransform.mem_toBehavior_iff_toLinearMap]
  rcases ((netlist p).mem_behavior_iff_equations (inputAmplitude p 1) output).mp hMember with
    ⟨incident, outgoing, hScattering, hAssembly, hOutput⟩
  have hAssembly' :
      incident = (netlist p).connections.incidentAssembly outgoing (inputAmplitude p 1) := by
    simpa only [PortConnectionFamily.incidentAssembly] using hAssembly
  have hForward := forwardEquations_of_netlistEquations p (inputAmplitude p 1) incident outgoing
    hScattering hAssembly'
  have hValue := hForward.output_eq_transfer hDenominator
  have hReadout := congrArg (fun state => state (Outgoing.mk (outputChannel p))) hOutput
  rw [outputReadout_apply_output] at hReadout
  have hOutputValue : output (Outgoing.mk (outputChannel p)) = transfer p := by
    simpa [forwardState] using hReadout.trans hValue
  have hResponse := responseTransform_apply_inputAmplitude p hWellPosed 1
  calc
    eliminationResponse p hWellPosed = output (Outgoing.mk (outputChannel p)) := by
      simpa [output] using hResponse.symm
    _ = transfer p := hOutputValue

end DCDR

end

end Optics
