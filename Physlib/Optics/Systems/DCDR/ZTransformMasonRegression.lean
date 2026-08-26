/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Systems.DCDR.PolesRegression
public import Physlib.Optics.Systems.DCDR.ResponseRegression

/-!
# Raw N5 and Mason regression for the DCDR Z bridge

## i. Overview

At the stable nonzero-loop point and formal coordinate q = -I, this module independently expands
all eight raw N5 channel equations and the complete eleven-branch Mason enumeration. The Mason
audit classifies the two touching cycles, enumerates the four supported paths and their edge
refinements, and computes every path cofactor without using a DCDR response-agreement theorem.

These are algebraic discrete-time fixtures, not physical resonance claims. No coherent--incoherent
equivalence, BIBO conclusion, modal or electromagnetic power statement, Maxwell time-domain
interpretation, reciprocity, physical-frequency interpretation, or HOL-script claim is made.

## ii. Key results

- `DCDR.zRegression_stable_eliminationResponse_neg_I`: raw N5 equations give `-(7/8) I`.
- `DCDR.zRegression_stable_edgeGraphDetOn`: the two cycles give every induced determinant.
- `DCDR.zRegression_stable_edgeMasonNumerator`: all eleven branches give the numerator.
- `DCDR.zRegression_stable_auditedMasonResponse_neg_I`: direct Mason enumeration gives the value.

## iii. Table of contents

- A. Stable raw N5 and Mason audit

## iv. References

This adversarial regression is Physlib-original. It exercises the source's coherent unprinted
branch without identifying it with FMICS'15's printed incoherent formula.
-/

@[expose] public section

namespace Optics.DCDR

noncomputable section

open Physlib.SignalFlowGraph

/-- The regression uses the same finite external-channel instance as N5 elimination. -/
local instance zMasonRegressionExternalChannelFintype (p : Parameters) :
    Fintype (netlist p).ExternalChannel :=
  (netlist p).eliminationExternalChannelFintype

/-!

## A. Stable raw N5 and Mason audit

-/

/-- The fixed `q = -I` N5 solve gate, expanded from the stable denominator data. -/
lemma zRegression_stable_fixed_hasNonzeroDenominator_I :
    (stableUnitDelayParameters.at (-Complex.I)).HasNonzeroDenominator := by
  rw [Parameters.HasNonzeroDenominator,
    ← stableUnitDelayParameters.eval_denominatorPolynomial,
    stable_denominatorPolynomial_expansion]
  norm_num [stableDenominator, Complex.I_mul_I]

/-- The hand-expanded eight-node state at the nonzero-loop point `q = -I`. -/
def zRegressionStableFixedState : Node → ℂ :=
  ![1, (5 / 4) * Complex.I, 8 / 5, -(1 / 20) * Complex.I,
    -1 / 20, -(61 / 40) * Complex.I, -5 / 4, -(7 / 8) * Complex.I]

/-- All eight raw N5 channel equations hold for the displayed nonzero-loop state. -/
lemma zRegression_stable_fixed_forwardEquations_I :
    ForwardEquations (stableUnitDelayParameters.at (-Complex.I)) 1
      zRegressionStableFixedState := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [zRegressionStableFixedState, UnitDelayParameters.at,
      stableUnitDelayParameters, poleRegressionCoupler,
      Parameters.upperCoefficient, Parameters.lowerCoefficient,
      Parameters.feedbackCoefficient, DirectionalCoupler.crossCoefficient]
  all_goals ring_nf
  all_goals norm_num [pow_two, Complex.I_mul_I]

/-- The complete raw N5 relation independently reads `-(7/8) I` at `q = -I`.

The proof lifts the displayed eight-equation state to all component channels and uses behavior
functionality only to identify that realization with the compiled response. It does not invoke
an elimination, rational-response, or Mason equality.
-/
lemma zRegression_stable_eliminationResponse_neg_I :
    eliminationResponse (stableUnitDelayParameters.at (-Complex.I))
        (isWellPosed_of_hasNonzeroDenominator
          (stableUnitDelayParameters.at (-Complex.I))
          zRegression_stable_fixed_hasNonzeroDenominator_I) =
      -(7 / 8) * Complex.I := by
  let p := stableUnitDelayParameters.at (-Complex.I)
  let hWellPosed := isWellPosed_of_hasNonzeroDenominator p
    zRegression_stable_fixed_hasNonzeroDenominator_I
  have hNode : Physlib.SignalFlowGraph.IsNodeSolution (signalFlowGraph p)
      (signalInput 1) zRegressionStableFixedState :=
    (isNodeSolution_iff_forwardEquations p 1 zRegressionStableFixedState).mpr
      zRegression_stable_fixed_forwardEquations_I
  rcases (isNodeSolution_iff_exists_netlistRealization p 1
      zRegressionStableFixedState).mp hNode with
    ⟨incident, outgoing, hScattering, hAssembly, hProjection⟩
  let output := (netlist p).outputReadout.toLinearMap outgoing
  have hMember : (inputAmplitude p 1, output) ∈ (netlist p).behavior := by
    apply ((netlist p).mem_behavior_iff_equations (inputAmplitude p 1) output).mpr
    exact ⟨incident, outgoing, hScattering, hAssembly, rfl⟩
  have hResponseMember : (inputAmplitude p 1, output) ∈
      ((netlist p).responseTransform hWellPosed).toBehavior := by
    rw [(netlist p).toBehavior_responseTransform hWellPosed]
    exact hMember
  have hOutput :=
    (ModeTransform.mem_toBehavior_iff_toLinearMap _ _ _).mp hResponseMember
  have hState := congrArg (fun value ↦ value (7 : Node)) hProjection
  have hOutputValue : output (Outgoing.mk (outputChannel p)) =
      -(7 / 8) * Complex.I := by
    rw [outputReadout_apply_output]
    simpa [zRegressionStableFixedState, forwardState] using hState
  have hResponse := responseTransform_apply_inputAmplitude p hWellPosed 1
  calc
    eliminationResponse p hWellPosed =
        output (Outgoing.mk (outputChannel p)) := by
      rw [hOutput]
      simpa using hResponse.symm
    _ = -(7 / 8) * Complex.I := hOutputValue

/-- Nodes of the upper nonzero feedback cycle in the stable eleven-branch graph. -/
def zRegressionStableUpperLoopNodes : Finset Node := {1, 2, 5, 6}

/-- Nodes of the lower nonzero feedback cycle in the stable eleven-branch graph. -/
def zRegressionStableLowerLoopNodes : Finset Node := {1, 3, 4, 6}

/-- The upper cycle permutation `1 -> 2 -> 5 -> 6 -> 1`. -/
def zRegressionStableUpperLoopPermutation : Equiv.Perm Node :=
  [1, 2, 5, 6].formPerm

/-- The lower cycle permutation `1 -> 3 -> 4 -> 6 -> 1`. -/
def zRegressionStableLowerLoopPermutation : Equiv.Perm Node :=
  [1, 3, 4, 6].formPerm

/-- Edge labels selected by the stable upper feedback cycle. -/
def zRegressionStableUpperLoopEdge : Node → Edge := ![0, 8, 1, 0, 0, 6, 7, 0]

/-- Edge labels selected by the stable lower feedback cycle. -/
def zRegressionStableLowerLoopEdge : Node → Edge := ![0, 9, 0, 4, 10, 0, 7, 0]

/-- The dependent upper-cycle edge selection. -/
def zRegressionStableUpperLoopChoice :
    ∀ node ∈ zRegressionStableUpperLoopNodes, Edge :=
  fun node _ ↦ zRegressionStableUpperLoopEdge node

/-- The dependent lower-cycle edge selection. -/
def zRegressionStableLowerLoopChoice :
    ∀ node ∈ zRegressionStableLowerLoopNodes, Edge :=
  fun node _ ↦ zRegressionStableLowerLoopEdge node

/-- A selected loop edge records its source and permutation target. -/
private lemma zRegression_stable_selectedEndpoints
    {nodes : Finset Node} {permutation : Equiv.Perm Node}
    {choice : ∀ node ∈ nodes, Edge}
    (hChoice : choice ∈ edgeChoices
      (signalMultigraph (stableUnitDelayParameters.at (-Complex.I))) nodes permutation)
    (node : Node) (hNode : node ∈ nodes) :
    edgeSource (choice node hNode) = node ∧
      edgeTarget (choice node hNode) = permutation node := by
  have hSelected := Finset.mem_pi.mp hChoice node hNode
  simpa [signalMultigraph] using hSelected

/-- A loop-family permutation preserves its declared node set. -/
private lemma zRegression_stable_permutation_mem
    {nodes : Finset Node} {permutation : Equiv.Perm Node}
    (hPermutation : permutation ∈ loopFamilies nodes)
    (node : Node) (hNode : node ∈ nodes) : permutation node ∈ nodes := by
  by_cases hSupport : node ∈ permutation.support
  · exact (mem_loopFamilies.mp hPermutation)
      (Equiv.Perm.apply_mem_support.mpr hSupport)
  · rw [Equiv.Perm.notMem_support.mp hSupport]
    exact hNode

/-- The two retained branches leaving feedback-input node one. -/
private lemma zRegression_stable_edge_from_one (edge : Edge)
    (hSource : edgeSource edge = 1) : edge = 8 ∨ edge = 9 := by
  fin_cases edge <;> simp [edgeSource] at hSource ⊢

/-- The unique retained branch leaving upper launch node two. -/
private lemma zRegression_stable_edge_from_two (edge : Edge)
    (hSource : edgeSource edge = 2) : edge = 1 := by
  fin_cases edge <;> simp [edgeSource] at hSource ⊢

/-- The unique retained branch leaving lower launch node three. -/
private lemma zRegression_stable_edge_from_three (edge : Edge)
    (hSource : edgeSource edge = 3) : edge = 4 := by
  fin_cases edge <;> simp [edgeSource] at hSource ⊢

/-- The two retained branches leaving lower propagation node four. -/
private lemma zRegression_stable_edge_from_four (edge : Edge)
    (hSource : edgeSource edge = 4) : edge = 5 ∨ edge = 10 := by
  fin_cases edge <;> simp [edgeSource] at hSource ⊢

/-- The two retained branches leaving upper propagation node five. -/
private lemma zRegression_stable_edge_from_five (edge : Edge)
    (hSource : edgeSource edge = 5) : edge = 2 ∨ edge = 6 := by
  fin_cases edge <;> simp [edgeSource] at hSource ⊢

/-- The unique retained feedback branch leaves node six. -/
private lemma zRegression_stable_edge_from_six (edge : Edge)
    (hSource : edgeSource edge = 6) : edge = 7 := by
  fin_cases edge <;> simp [edgeSource] at hSource ⊢

/-- No retained branch leaves external output node seven. -/
private lemma zRegression_stable_noEdgeSource_seven (edge : Edge) :
    edgeSource edge ≠ 7 := by
  fin_cases edge <;> simp [edgeSource]

/-- Every nonempty loop refinement contains the sole rank-return edge seven. -/
private lemma zRegression_stable_edgeChoice_contains_feedbackEdge
    {nodes : Finset Node} {permutation : Equiv.Perm Node}
    {choice : ∀ node ∈ nodes, Edge} (hNodes : nodes.Nonempty)
    (hPermutation : permutation ∈ loopFamilies nodes)
    (hChoice : choice ∈ edgeChoices
      (signalMultigraph (stableUnitDelayParameters.at (-Complex.I))) nodes permutation) :
    ∃ node, ∃ hNode : node ∈ nodes, choice node hNode = 7 := by
  by_contra hMissing
  push Not at hMissing
  obtain ⟨node, hNode, hMax⟩ :=
    Finset.exists_max_image nodes responseRegressionNodeRank hNodes
  have hPermutationNode : permutation node ∈ nodes :=
    zRegression_stable_permutation_mem hPermutation node hNode
  have hEndpoints := zRegression_stable_selectedEndpoints hChoice node hNode
  have hRank := responseRegressionNodeRank_lt (choice node hNode)
    (hMissing node hNode)
  rw [hEndpoints.1, hEndpoints.2] at hRank
  exact (Nat.not_lt_of_ge (hMax (permutation node) hPermutationNode)) hRank

/-- Every nonempty loop-family refinement is one of the two displayed touching cycles. -/
private lemma zRegression_stable_loopFamily_cases
    {nodes : Finset Node} {permutation : Equiv.Perm Node}
    {choice : ∀ node ∈ nodes, Edge} (hNodes : nodes.Nonempty)
    (hPermutation : permutation ∈ loopFamilies nodes)
    (hChoice : choice ∈ edgeChoices
      (signalMultigraph (stableUnitDelayParameters.at (-Complex.I))) nodes permutation) :
    (nodes = zRegressionStableUpperLoopNodes ∧
        permutation = zRegressionStableUpperLoopPermutation) ∨
      (nodes = zRegressionStableLowerLoopNodes ∧
        permutation = zRegressionStableLowerLoopPermutation) := by
  obtain ⟨feedbackNode, hFeedbackNode, hFeedbackEdge⟩ :=
    zRegression_stable_edgeChoice_contains_feedbackEdge hNodes hPermutation hChoice
  have hFeedbackEndpoints :=
    zRegression_stable_selectedEndpoints hChoice feedbackNode hFeedbackNode
  have hFeedbackNodeEq : feedbackNode = 6 := by
    simpa [hFeedbackEdge, edgeSource] using hFeedbackEndpoints.1.symm
  subst feedbackNode
  have h6 : (6 : Node) ∈ nodes := hFeedbackNode
  have hPermutation6 : permutation 6 = 1 := by
    simpa [hFeedbackEdge, edgeTarget] using hFeedbackEndpoints.2.symm
  have h1 : (1 : Node) ∈ nodes := by
    rw [← hPermutation6]
    exact zRegression_stable_permutation_mem hPermutation 6 h6
  have hEndpoints1 := zRegression_stable_selectedEndpoints hChoice 1 h1
  rcases zRegression_stable_edge_from_one _ hEndpoints1.1 with hUpper | hLower
  · have hPermutation1 : permutation 1 = 2 := by
      simpa [hUpper, edgeTarget] using hEndpoints1.2.symm
    have h2 : (2 : Node) ∈ nodes := by
      rw [← hPermutation1]
      exact zRegression_stable_permutation_mem hPermutation 1 h1
    have hEndpoints2 := zRegression_stable_selectedEndpoints hChoice 2 h2
    have hEdge2 := zRegression_stable_edge_from_two _ hEndpoints2.1
    have hPermutation2 : permutation 2 = 5 := by
      simpa [hEdge2, edgeTarget] using hEndpoints2.2.symm
    have h5 : (5 : Node) ∈ nodes := by
      rw [← hPermutation2]
      exact zRegression_stable_permutation_mem hPermutation 2 h2
    have hEndpoints5 := zRegression_stable_selectedEndpoints hChoice 5 h5
    have hEdge5 : choice 5 h5 = 6 := by
      rcases zRegression_stable_edge_from_five _ hEndpoints5.1 with hOutput | hReturn
      · have hPermutation5 : permutation 5 = 7 := by
          simpa [hOutput, edgeTarget] using hEndpoints5.2.symm
        have h7 : (7 : Node) ∈ nodes := by
          rw [← hPermutation5]
          exact zRegression_stable_permutation_mem hPermutation 5 h5
        exact absurd (zRegression_stable_selectedEndpoints hChoice 7 h7).1
          (zRegression_stable_noEdgeSource_seven _)
      · exact hReturn
    have hPermutation5 : permutation 5 = 6 := by
      simpa [hEdge5, edgeTarget] using hEndpoints5.2.symm
    have hMainSubset : zRegressionStableUpperLoopNodes ⊆ nodes := by
      intro node hNode
      simp only [zRegressionStableUpperLoopNodes, Finset.mem_insert,
        Finset.mem_singleton] at hNode
      rcases hNode with rfl | rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact h5
      · exact h6
    have hNoExtra : nodes \ zRegressionStableUpperLoopNodes = ∅ := by
      by_contra hExtra
      have hExtraNonempty : (nodes \ zRegressionStableUpperLoopNodes).Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr hExtra
      obtain ⟨node, hNode, hMax⟩ := Finset.exists_max_image
        (nodes \ zRegressionStableUpperLoopNodes) responseRegressionNodeRank hExtraNonempty
      have hNodeParts := Finset.mem_sdiff.mp hNode
      have hPermutationNodeNodes :=
        zRegression_stable_permutation_mem hPermutation node hNodeParts.1
      have hPermutationNodeNotMain :
          permutation node ∉ zRegressionStableUpperLoopNodes := by
        intro hTarget
        simp only [zRegressionStableUpperLoopNodes, Finset.mem_insert,
          Finset.mem_singleton] at hTarget
        rcases hTarget with hTarget | hTarget | hTarget | hTarget
        · exact hNodeParts.2 (by
            have := permutation.injective (hTarget.trans hPermutation6.symm)
            simp [this, zRegressionStableUpperLoopNodes])
        · exact hNodeParts.2 (by
            have := permutation.injective (hTarget.trans hPermutation1.symm)
            simp [this, zRegressionStableUpperLoopNodes])
        · exact hNodeParts.2 (by
            have := permutation.injective (hTarget.trans hPermutation2.symm)
            simp [this, zRegressionStableUpperLoopNodes])
        · exact hNodeParts.2 (by
            have := permutation.injective (hTarget.trans hPermutation5.symm)
            simp [this, zRegressionStableUpperLoopNodes])
      have hPermutationNode : permutation node ∈
          nodes \ zRegressionStableUpperLoopNodes :=
        Finset.mem_sdiff.mpr ⟨hPermutationNodeNodes, hPermutationNodeNotMain⟩
      have hEndpoints := zRegression_stable_selectedEndpoints hChoice node hNodeParts.1
      have hNotFeedback : choice node hNodeParts.1 ≠ 7 := by
        intro hEdge
        have hNodeEq : node = 6 := by
          simpa [hEdge, edgeSource] using hEndpoints.1.symm
        exact hNodeParts.2 (by simp [hNodeEq, zRegressionStableUpperLoopNodes])
      have hRank := responseRegressionNodeRank_lt (choice node hNodeParts.1) hNotFeedback
      rw [hEndpoints.1, hEndpoints.2] at hRank
      exact (Nat.not_lt_of_ge (hMax (permutation node) hPermutationNode)) hRank
    have hNodesEqual : nodes = zRegressionStableUpperLoopNodes := by
      exact Finset.Subset.antisymm
        (Finset.sdiff_eq_empty_iff_subset.mp hNoExtra) hMainSubset
    have hFixedOutside (node : Node) (hNode : node ∉ zRegressionStableUpperLoopNodes) :
        permutation node = node := by
      apply Equiv.Perm.notMem_support.mp
      intro hSupport
      apply hNode
      rw [← hNodesEqual]
      exact (mem_loopFamilies.mp hPermutation) hSupport
    refine Or.inl ⟨hNodesEqual, Equiv.ext ?_⟩
    intro node
    fin_cases node
    · simpa [zRegressionStableUpperLoopPermutation, Equiv.swap_apply_def] using
        hFixedOutside 0 (by decide)
    · simpa [zRegressionStableUpperLoopPermutation, Equiv.swap_apply_def] using
        hPermutation1
    · simpa [zRegressionStableUpperLoopPermutation, Equiv.swap_apply_def] using
        hPermutation2
    · simpa [zRegressionStableUpperLoopPermutation, Equiv.swap_apply_def] using
        hFixedOutside 3 (by decide)
    · simpa [zRegressionStableUpperLoopPermutation, Equiv.swap_apply_def] using
        hFixedOutside 4 (by decide)
    · simpa [zRegressionStableUpperLoopPermutation, Equiv.swap_apply_def] using
        hPermutation5
    · simpa [zRegressionStableUpperLoopPermutation, Equiv.swap_apply_def] using
        hPermutation6
    · simpa [zRegressionStableUpperLoopPermutation, Equiv.swap_apply_def] using
        hFixedOutside 7 (by decide)
  · have hPermutation1 : permutation 1 = 3 := by
      simpa [hLower, edgeTarget] using hEndpoints1.2.symm
    have h3 : (3 : Node) ∈ nodes := by
      rw [← hPermutation1]
      exact zRegression_stable_permutation_mem hPermutation 1 h1
    have hEndpoints3 := zRegression_stable_selectedEndpoints hChoice 3 h3
    have hEdge3 := zRegression_stable_edge_from_three _ hEndpoints3.1
    have hPermutation3 : permutation 3 = 4 := by
      simpa [hEdge3, edgeTarget] using hEndpoints3.2.symm
    have h4 : (4 : Node) ∈ nodes := by
      rw [← hPermutation3]
      exact zRegression_stable_permutation_mem hPermutation 3 h3
    have hEndpoints4 := zRegression_stable_selectedEndpoints hChoice 4 h4
    have hEdge4 : choice 4 h4 = 10 := by
      rcases zRegression_stable_edge_from_four _ hEndpoints4.1 with hOutput | hReturn
      · have hPermutation4 : permutation 4 = 7 := by
          simpa [hOutput, edgeTarget] using hEndpoints4.2.symm
        have h7 : (7 : Node) ∈ nodes := by
          rw [← hPermutation4]
          exact zRegression_stable_permutation_mem hPermutation 4 h4
        exact absurd (zRegression_stable_selectedEndpoints hChoice 7 h7).1
          (zRegression_stable_noEdgeSource_seven _)
      · exact hReturn
    have hPermutation4 : permutation 4 = 6 := by
      simpa [hEdge4, edgeTarget] using hEndpoints4.2.symm
    have hMainSubset : zRegressionStableLowerLoopNodes ⊆ nodes := by
      intro node hNode
      simp only [zRegressionStableLowerLoopNodes, Finset.mem_insert,
        Finset.mem_singleton] at hNode
      rcases hNode with rfl | rfl | rfl | rfl
      · exact h1
      · exact h3
      · exact h4
      · exact h6
    have hNoExtra : nodes \ zRegressionStableLowerLoopNodes = ∅ := by
      by_contra hExtra
      have hExtraNonempty : (nodes \ zRegressionStableLowerLoopNodes).Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr hExtra
      obtain ⟨node, hNode, hMax⟩ := Finset.exists_max_image
        (nodes \ zRegressionStableLowerLoopNodes) responseRegressionNodeRank hExtraNonempty
      have hNodeParts := Finset.mem_sdiff.mp hNode
      have hPermutationNodeNodes :=
        zRegression_stable_permutation_mem hPermutation node hNodeParts.1
      have hPermutationNodeNotMain :
          permutation node ∉ zRegressionStableLowerLoopNodes := by
        intro hTarget
        simp only [zRegressionStableLowerLoopNodes, Finset.mem_insert,
          Finset.mem_singleton] at hTarget
        rcases hTarget with hTarget | hTarget | hTarget | hTarget
        · exact hNodeParts.2 (by
            have := permutation.injective (hTarget.trans hPermutation6.symm)
            simp [this, zRegressionStableLowerLoopNodes])
        · exact hNodeParts.2 (by
            have := permutation.injective (hTarget.trans hPermutation1.symm)
            simp [this, zRegressionStableLowerLoopNodes])
        · exact hNodeParts.2 (by
            have := permutation.injective (hTarget.trans hPermutation3.symm)
            simp [this, zRegressionStableLowerLoopNodes])
        · exact hNodeParts.2 (by
            have := permutation.injective (hTarget.trans hPermutation4.symm)
            simp [this, zRegressionStableLowerLoopNodes])
      have hPermutationNode : permutation node ∈
          nodes \ zRegressionStableLowerLoopNodes :=
        Finset.mem_sdiff.mpr ⟨hPermutationNodeNodes, hPermutationNodeNotMain⟩
      have hEndpoints := zRegression_stable_selectedEndpoints hChoice node hNodeParts.1
      have hNotFeedback : choice node hNodeParts.1 ≠ 7 := by
        intro hEdge
        have hNodeEq : node = 6 := by
          simpa [hEdge, edgeSource] using hEndpoints.1.symm
        exact hNodeParts.2 (by simp [hNodeEq, zRegressionStableLowerLoopNodes])
      have hRank := responseRegressionNodeRank_lt (choice node hNodeParts.1) hNotFeedback
      rw [hEndpoints.1, hEndpoints.2] at hRank
      exact (Nat.not_lt_of_ge (hMax (permutation node) hPermutationNode)) hRank
    have hNodesEqual : nodes = zRegressionStableLowerLoopNodes := by
      exact Finset.Subset.antisymm
        (Finset.sdiff_eq_empty_iff_subset.mp hNoExtra) hMainSubset
    have hFixedOutside (node : Node) (hNode : node ∉ zRegressionStableLowerLoopNodes) :
        permutation node = node := by
      apply Equiv.Perm.notMem_support.mp
      intro hSupport
      apply hNode
      rw [← hNodesEqual]
      exact (mem_loopFamilies.mp hPermutation) hSupport
    refine Or.inr ⟨hNodesEqual, Equiv.ext ?_⟩
    intro node
    fin_cases node
    · simpa [zRegressionStableLowerLoopPermutation, Equiv.swap_apply_def] using
        hFixedOutside 0 (by decide)
    · simpa [zRegressionStableLowerLoopPermutation, Equiv.swap_apply_def] using
        hPermutation1
    · simpa [zRegressionStableLowerLoopPermutation, Equiv.swap_apply_def] using
        hFixedOutside 2 (by decide)
    · simpa [zRegressionStableLowerLoopPermutation, Equiv.swap_apply_def] using
        hPermutation3
    · simpa [zRegressionStableLowerLoopPermutation, Equiv.swap_apply_def] using
        hPermutation4
    · simpa [zRegressionStableLowerLoopPermutation, Equiv.swap_apply_def] using
        hFixedOutside 5 (by decide)
    · simpa [zRegressionStableLowerLoopPermutation, Equiv.swap_apply_def] using
        hPermutation6
    · simpa [zRegressionStableLowerLoopPermutation, Equiv.swap_apply_def] using
        hFixedOutside 7 (by decide)

/-- The displayed upper permutation is a loop family on its four nodes. -/
lemma zRegression_stable_upperLoopPermutation_mem :
    zRegressionStableUpperLoopPermutation ∈
      loopFamilies zRegressionStableUpperLoopNodes := by
  apply mem_loopFamilies.mpr
  simpa [zRegressionStableUpperLoopPermutation, zRegressionStableUpperLoopNodes] using
    List.support_formPerm_le ([1, 2, 5, 6] : List Node)

/-- The displayed lower permutation is a loop family on its four nodes. -/
lemma zRegression_stable_lowerLoopPermutation_mem :
    zRegressionStableLowerLoopPermutation ∈
      loopFamilies zRegressionStableLowerLoopNodes := by
  apply mem_loopFamilies.mpr
  simpa [zRegressionStableLowerLoopPermutation, zRegressionStableLowerLoopNodes] using
    List.support_formPerm_le ([1, 3, 4, 6] : List Node)

/-- The upper loop has exactly the edge choice `8, 1, 6, 7`. -/
private lemma zRegression_stable_upperLoopChoice_mem :
    zRegressionStableUpperLoopChoice ∈
      edgeChoices (signalMultigraph (stableUnitDelayParameters.at (-Complex.I)))
        zRegressionStableUpperLoopNodes zRegressionStableUpperLoopPermutation := by
  have hFiber (node : Node) (hNode : node ∈ zRegressionStableUpperLoopNodes) :
      (signalMultigraph (stableUnitDelayParameters.at (-Complex.I))).edgesBetween
          node (zRegressionStableUpperLoopPermutation node) =
        {zRegressionStableUpperLoopEdge node} := by
    simp only [zRegressionStableUpperLoopNodes, Finset.mem_insert,
      Finset.mem_singleton] at hNode
    rcases hNode with rfl | rfl | rfl | rfl <;> decide
  apply Finset.mem_pi.mpr
  intro node hNode
  rw [hFiber node hNode]
  simp [zRegressionStableUpperLoopChoice]

/-- Every upper-cycle refinement is the displayed dependent edge choice. -/
private lemma zRegression_stable_upperLoopChoice_unique
    {choice : ∀ node ∈ zRegressionStableUpperLoopNodes, Edge}
    (hChoice : choice ∈
      edgeChoices (signalMultigraph (stableUnitDelayParameters.at (-Complex.I)))
        zRegressionStableUpperLoopNodes zRegressionStableUpperLoopPermutation) :
    choice = zRegressionStableUpperLoopChoice := by
  have hFiber (node : Node) (hNode : node ∈ zRegressionStableUpperLoopNodes) :
      (signalMultigraph (stableUnitDelayParameters.at (-Complex.I))).edgesBetween
          node (zRegressionStableUpperLoopPermutation node) =
        {zRegressionStableUpperLoopEdge node} := by
    simp only [zRegressionStableUpperLoopNodes, Finset.mem_insert,
      Finset.mem_singleton] at hNode
    rcases hNode with rfl | rfl | rfl | rfl <;> decide
  funext node hNode
  have hSelected := Finset.mem_pi.mp hChoice node hNode
  rw [hFiber node hNode] at hSelected
  simpa [zRegressionStableUpperLoopChoice] using hSelected

lemma zRegression_stable_upperLoopChoices :
    edgeChoices (signalMultigraph (stableUnitDelayParameters.at (-Complex.I)))
        zRegressionStableUpperLoopNodes zRegressionStableUpperLoopPermutation =
      {zRegressionStableUpperLoopChoice} := by
  ext choice
  simp only [Finset.mem_singleton]
  constructor
  · exact zRegression_stable_upperLoopChoice_unique
  · rintro rfl
    exact zRegression_stable_upperLoopChoice_mem

/-- The lower loop has exactly the edge choice `9, 4, 10, 7`. -/
private lemma zRegression_stable_lowerLoopChoice_mem :
    zRegressionStableLowerLoopChoice ∈
      edgeChoices (signalMultigraph (stableUnitDelayParameters.at (-Complex.I)))
        zRegressionStableLowerLoopNodes zRegressionStableLowerLoopPermutation := by
  have hFiber (node : Node) (hNode : node ∈ zRegressionStableLowerLoopNodes) :
      (signalMultigraph (stableUnitDelayParameters.at (-Complex.I))).edgesBetween
          node (zRegressionStableLowerLoopPermutation node) =
        {zRegressionStableLowerLoopEdge node} := by
    simp only [zRegressionStableLowerLoopNodes, Finset.mem_insert,
      Finset.mem_singleton] at hNode
    rcases hNode with rfl | rfl | rfl | rfl <;> decide
  apply Finset.mem_pi.mpr
  intro node hNode
  rw [hFiber node hNode]
  simp [zRegressionStableLowerLoopChoice]

/-- Every lower-cycle refinement is the displayed dependent edge choice. -/
private lemma zRegression_stable_lowerLoopChoice_unique
    {choice : ∀ node ∈ zRegressionStableLowerLoopNodes, Edge}
    (hChoice : choice ∈
      edgeChoices (signalMultigraph (stableUnitDelayParameters.at (-Complex.I)))
        zRegressionStableLowerLoopNodes zRegressionStableLowerLoopPermutation) :
    choice = zRegressionStableLowerLoopChoice := by
  have hFiber (node : Node) (hNode : node ∈ zRegressionStableLowerLoopNodes) :
      (signalMultigraph (stableUnitDelayParameters.at (-Complex.I))).edgesBetween
          node (zRegressionStableLowerLoopPermutation node) =
        {zRegressionStableLowerLoopEdge node} := by
    simp only [zRegressionStableLowerLoopNodes, Finset.mem_insert,
      Finset.mem_singleton] at hNode
    rcases hNode with rfl | rfl | rfl | rfl <;> decide
  funext node hNode
  have hSelected := Finset.mem_pi.mp hChoice node hNode
  rw [hFiber node hNode] at hSelected
  simpa [zRegressionStableLowerLoopChoice] using hSelected

lemma zRegression_stable_lowerLoopChoices :
    edgeChoices (signalMultigraph (stableUnitDelayParameters.at (-Complex.I)))
        zRegressionStableLowerLoopNodes zRegressionStableLowerLoopPermutation =
      {zRegressionStableLowerLoopChoice} := by
  ext choice
  simp only [Finset.mem_singleton]
  constructor
  · exact zRegression_stable_lowerLoopChoice_unique
  · rintro rfl
    exact zRegression_stable_lowerLoopChoice_mem

/-- The upper family contains one cycle. -/
lemma zRegression_stable_upperLoopCount :
    loopCount zRegressionStableUpperLoopNodes
      zRegressionStableUpperLoopPermutation = 1 := by
  decide

/-- The lower family contains one cycle. -/
lemma zRegression_stable_lowerLoopCount :
    loopCount zRegressionStableLowerLoopNodes
      zRegressionStableLowerLoopPermutation = 1 := by
  decide

/-- Direct multiplication gives upper feedback-loop gain `61/100`. -/
lemma zRegression_stable_upperLoopFamilyGain :
    edgeFamilyGain (signalMultigraph (stableUnitDelayParameters.at (-Complex.I)))
        zRegressionStableUpperLoopNodes zRegressionStableUpperLoopChoice = 61 / 100 := by
  rw [edgeFamilyGain]
  simp only [zRegressionStableUpperLoopChoice]
  calc
    (∏ x ∈ zRegressionStableUpperLoopNodes.attach,
        (signalMultigraph (stableUnitDelayParameters.at (-Complex.I))).gain
          (zRegressionStableUpperLoopEdge x)) =
        ∏ node ∈ zRegressionStableUpperLoopNodes,
          (signalMultigraph (stableUnitDelayParameters.at (-Complex.I))).gain
            (zRegressionStableUpperLoopEdge node) :=
      Finset.prod_attach zRegressionStableUpperLoopNodes
        (fun node ↦
          (signalMultigraph (stableUnitDelayParameters.at (-Complex.I))).gain
            (zRegressionStableUpperLoopEdge node))
    _ = 61 / 100 := by
      simp [zRegressionStableUpperLoopNodes, Finset.prod_insert,
        zRegressionStableUpperLoopEdge, signalMultigraph, edgeGain,
        UnitDelayParameters.at, stableUnitDelayParameters, poleRegressionCoupler,
        Parameters.upperCoefficient, Parameters.feedbackCoefficient,
        DirectionalCoupler.crossCoefficient]
      ring_nf
      norm_num [pow_succ, Complex.I_mul_I]

/-- Direct multiplication gives lower feedback-loop gain `-9/25`. -/
lemma zRegression_stable_lowerLoopFamilyGain :
    edgeFamilyGain (signalMultigraph (stableUnitDelayParameters.at (-Complex.I)))
        zRegressionStableLowerLoopNodes zRegressionStableLowerLoopChoice = -9 / 25 := by
  rw [edgeFamilyGain]
  simp only [zRegressionStableLowerLoopChoice]
  calc
    (∏ x ∈ zRegressionStableLowerLoopNodes.attach,
        (signalMultigraph (stableUnitDelayParameters.at (-Complex.I))).gain
          (zRegressionStableLowerLoopEdge x)) =
        ∏ node ∈ zRegressionStableLowerLoopNodes,
          (signalMultigraph (stableUnitDelayParameters.at (-Complex.I))).gain
            (zRegressionStableLowerLoopEdge node) :=
      Finset.prod_attach zRegressionStableLowerLoopNodes
        (fun node ↦
          (signalMultigraph (stableUnitDelayParameters.at (-Complex.I))).gain
            (zRegressionStableLowerLoopEdge node))
    _ = -9 / 25 := by
      simp [zRegressionStableLowerLoopNodes, Finset.prod_insert,
        zRegressionStableLowerLoopEdge, signalMultigraph, edgeGain,
        UnitDelayParameters.at, stableUnitDelayParameters, poleRegressionCoupler,
        Parameters.lowerCoefficient, Parameters.feedbackCoefficient,
        DirectionalCoupler.crossCoefficient]
      ring_nf
      norm_num [pow_succ, Complex.I_mul_I]

/-- Every other nonempty node set has zero total loop-family contribution. -/
private lemma zRegression_stable_nonLoopFamilySum_eq_zero
    {nodes : Finset Node} (hNodes : nodes.Nonempty)
    (hNotUpper : nodes ≠ zRegressionStableUpperLoopNodes)
    (hNotLower : nodes ≠ zRegressionStableLowerLoopNodes) :
    (∑ permutation ∈ loopFamilies nodes,
      ∑ choice ∈ edgeChoices
          (signalMultigraph (stableUnitDelayParameters.at (-Complex.I))) nodes permutation,
        (-1 : ℂ) ^ loopCount nodes permutation *
          edgeFamilyGain
            (signalMultigraph (stableUnitDelayParameters.at (-Complex.I))) nodes choice) = 0 := by
  apply Finset.sum_eq_zero
  intro permutation hPermutation
  apply Finset.sum_eq_zero
  intro choice hChoice
  rcases zRegression_stable_loopFamily_cases hNodes hPermutation hChoice with
    hUpper | hLower
  · exact (hNotUpper hUpper.1).elim
  · exact (hNotLower hLower.1).elim

/-- The upper node set contributes the signed gain `-61/100`. -/
lemma zRegression_stable_upperFamilySum :
    (∑ permutation ∈ loopFamilies zRegressionStableUpperLoopNodes,
      ∑ choice ∈ edgeChoices
          (signalMultigraph (stableUnitDelayParameters.at (-Complex.I)))
            zRegressionStableUpperLoopNodes permutation,
        (-1 : ℂ) ^ loopCount zRegressionStableUpperLoopNodes permutation *
          edgeFamilyGain
            (signalMultigraph (stableUnitDelayParameters.at (-Complex.I)))
              zRegressionStableUpperLoopNodes choice) = -61 / 100 := by
  calc
    _ = ∑ choice ∈ edgeChoices
          (signalMultigraph (stableUnitDelayParameters.at (-Complex.I)))
            zRegressionStableUpperLoopNodes zRegressionStableUpperLoopPermutation,
        (-1 : ℂ) ^ loopCount zRegressionStableUpperLoopNodes
            zRegressionStableUpperLoopPermutation *
          edgeFamilyGain
            (signalMultigraph (stableUnitDelayParameters.at (-Complex.I)))
              zRegressionStableUpperLoopNodes choice := by
      apply Finset.sum_eq_single zRegressionStableUpperLoopPermutation
      · intro permutation hPermutation hNotPermutation
        apply Finset.sum_eq_zero
        intro choice hChoice
        rcases zRegression_stable_loopFamily_cases (by decide) hPermutation hChoice with
          hUpper | hLower
        · exact (hNotPermutation hUpper.2).elim
        · exact (by
            have : zRegressionStableUpperLoopNodes ≠
                zRegressionStableLowerLoopNodes := by decide
            exact (this hLower.1).elim)
      · intro hMissing
        exact (hMissing zRegression_stable_upperLoopPermutation_mem).elim
    _ = -61 / 100 := by
      rw [zRegression_stable_upperLoopChoices]
      simp [zRegression_stable_upperLoopCount,
        zRegression_stable_upperLoopFamilyGain]
      ring

/-- The lower node set contributes the signed gain `9/25`. -/
lemma zRegression_stable_lowerFamilySum :
    (∑ permutation ∈ loopFamilies zRegressionStableLowerLoopNodes,
      ∑ choice ∈ edgeChoices
          (signalMultigraph (stableUnitDelayParameters.at (-Complex.I)))
            zRegressionStableLowerLoopNodes permutation,
        (-1 : ℂ) ^ loopCount zRegressionStableLowerLoopNodes permutation *
          edgeFamilyGain
            (signalMultigraph (stableUnitDelayParameters.at (-Complex.I)))
              zRegressionStableLowerLoopNodes choice) = 9 / 25 := by
  calc
    _ = ∑ choice ∈ edgeChoices
          (signalMultigraph (stableUnitDelayParameters.at (-Complex.I)))
            zRegressionStableLowerLoopNodes zRegressionStableLowerLoopPermutation,
        (-1 : ℂ) ^ loopCount zRegressionStableLowerLoopNodes
            zRegressionStableLowerLoopPermutation *
          edgeFamilyGain
            (signalMultigraph (stableUnitDelayParameters.at (-Complex.I)))
              zRegressionStableLowerLoopNodes choice := by
      apply Finset.sum_eq_single zRegressionStableLowerLoopPermutation
      · intro permutation hPermutation hNotPermutation
        apply Finset.sum_eq_zero
        intro choice hChoice
        rcases zRegression_stable_loopFamily_cases (by decide) hPermutation hChoice with
          hUpper | hLower
        · exact (by
            have : zRegressionStableLowerLoopNodes ≠
                zRegressionStableUpperLoopNodes := by decide
            exact (this hUpper.1).elim)
        · exact (hNotPermutation hLower.2).elim
      · intro hMissing
        exact (hMissing zRegression_stable_lowerLoopPermutation_mem).elim
    _ = 9 / 25 := by
      rw [zRegression_stable_lowerLoopChoices]
      simp [zRegression_stable_lowerLoopCount,
        zRegression_stable_lowerLoopFamilyGain]
      ring

/-- Direct two-cycle enumeration gives every induced edge determinant. -/
lemma zRegression_stable_edgeGraphDetOn (nodes : Finset Node) :
    edgeGraphDetOn
        (signalMultigraph (stableUnitDelayParameters.at (-Complex.I))) nodes =
      1 - (if zRegressionStableUpperLoopNodes ⊆ nodes then 61 / 100 else 0) +
        (if zRegressionStableLowerLoopNodes ⊆ nodes then 9 / 25 else 0) := by
  let contribution : Finset Node → ℂ := fun selected ↦
    ∑ permutation ∈ loopFamilies selected,
      ∑ choice ∈ edgeChoices
          (signalMultigraph (stableUnitDelayParameters.at (-Complex.I)))
            selected permutation,
        (-1 : ℂ) ^ loopCount selected permutation *
          edgeFamilyGain
            (signalMultigraph (stableUnitDelayParameters.at (-Complex.I))) selected choice
  rw [edgeGraphDetOn]
  change (∑ selected ∈ nodes.powerset, contribution selected) = _
  calc
    (∑ selected ∈ nodes.powerset, contribution selected) =
        ∑ selected ∈ nodes.powerset,
          if selected = ∅ then 1
          else if selected = zRegressionStableUpperLoopNodes then -61 / 100
          else if selected = zRegressionStableLowerLoopNodes then 9 / 25
          else 0 := by
      apply Finset.sum_congr rfl
      intro selected hSelected
      by_cases hEmpty : selected = ∅
      · subst selected
        simp [contribution, loopFamilies_empty, edgeChoices,
          edgeFamilyGain, loopCount]
      · rw [if_neg hEmpty]
        by_cases hUpper : selected = zRegressionStableUpperLoopNodes
        · subst selected
          rw [if_pos rfl]
          exact zRegression_stable_upperFamilySum
        · rw [if_neg hUpper]
          by_cases hLower : selected = zRegressionStableLowerLoopNodes
          · subst selected
            rw [if_pos rfl]
            exact zRegression_stable_lowerFamilySum
          · rw [if_neg hLower]
            exact zRegression_stable_nonLoopFamilySum_eq_zero
              (Finset.nonempty_iff_ne_empty.mpr hEmpty) hUpper hLower
    _ = 1 - (if zRegressionStableUpperLoopNodes ⊆ nodes then 61 / 100 else 0) +
          (if zRegressionStableLowerLoopNodes ⊆ nodes then 9 / 25 else 0) := by
      have hSplit (selected : Finset Node) :
          (if selected = ∅ then (1 : ℂ)
            else if selected = zRegressionStableUpperLoopNodes then -61 / 100
            else if selected = zRegressionStableLowerLoopNodes then 9 / 25
            else 0) =
          (if selected = ∅ then 1 else 0) +
            (if selected = zRegressionStableUpperLoopNodes then -61 / 100 else 0) +
              (if selected = zRegressionStableLowerLoopNodes then 9 / 25 else 0) := by
        by_cases hEmpty : selected = ∅
        · subst selected
          simp [show (∅ : Finset Node) ≠ zRegressionStableUpperLoopNodes by decide,
            show (∅ : Finset Node) ≠ zRegressionStableLowerLoopNodes by decide]
        · by_cases hUpper : selected = zRegressionStableUpperLoopNodes
          · subst selected
            simp [hEmpty, show zRegressionStableUpperLoopNodes ≠
              zRegressionStableLowerLoopNodes by decide]
          · by_cases hLower : selected = zRegressionStableLowerLoopNodes
            · subst selected
              simp [hEmpty, hUpper]
            · simp [hEmpty, hUpper, hLower]
      simp_rw [hSplit, Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq', Finset.mem_powerset, Finset.empty_subset,
        if_pos]
      by_cases hUpper : zRegressionStableUpperLoopNodes ⊆ nodes <;>
        by_cases hLower : zRegressionStableLowerLoopNodes ⊆ nodes <;>
        simp [hUpper, hLower] <;> ring

/-- Refinement nonemptiness is the retained topology's consecutive-node adjacency. -/
private lemma zRegression_stable_refiningEdgeLists_nonempty_iff_isChain
    (path : List Node) :
    (refiningEdgeLists
      (signalMultigraph (stableUnitDelayParameters.at (-Complex.I))) path).Nonempty ↔
      path.IsChain responseRegressionAdjacent := by
  induction path with
  | nil => simp [refiningEdgeLists]
  | cons first rest ih =>
      cases rest with
      | nil => simp [refiningEdgeLists]
      | cons second tail =>
          constructor
          · rintro ⟨edgeList, hEdgeList⟩
            rw [refiningEdgeLists] at hEdgeList
            rcases Finset.mem_biUnion.mp hEdgeList with ⟨edge, hEdge, hImage⟩
            rcases Finset.mem_image.mp hImage with ⟨tailList, hTailList, rfl⟩
            have hAdjacent : responseRegressionAdjacent first second := by
              simpa [responseRegressionAdjacent, Multigraph.edgesBetween,
                signalMultigraph] using ⟨edge, hEdge⟩
            exact List.IsChain.cons_cons hAdjacent
              (ih.mp ⟨tailList, hTailList⟩)
          · intro hChain
            obtain ⟨edge, hEdge⟩ := hChain.rel
            have hStableEdge : edge ∈
                (signalMultigraph
                  (stableUnitDelayParameters.at (-Complex.I))).edgesBetween first second := by
              apply Multigraph.mem_edgesBetween.mpr
              simpa [responseRegressionAdjacent, signalMultigraph] using
                (Multigraph.mem_edgesBetween.mp hEdge)
            obtain ⟨tailList, hTailList⟩ := ih.mpr hChain.tail
            refine ⟨edge :: tailList, ?_⟩
            rw [refiningEdgeLists]
            exact Finset.mem_biUnion.mpr ⟨edge, hStableEdge,
              Finset.mem_image.mpr ⟨tailList, hTailList, rfl⟩⟩

/-- Supported stable paths use the same four node lists as the topology audit. -/
def zRegressionStableSupportedForwardPaths : Finset (List Node) :=
  (forwardPaths 0 7).filter fun path ↦
    (refiningEdgeLists
      (signalMultigraph (stableUnitDelayParameters.at (-Complex.I))) path).Nonempty

/-- Exactly four source-to-output paths have eleven-branch refinements. -/
lemma zRegression_stable_supportedForwardPaths :
    zRegressionStableSupportedForwardPaths =
      { [0, 2, 5, 7], [0, 3, 4, 7],
        [0, 2, 5, 6, 1, 3, 4, 7], [0, 3, 4, 6, 1, 2, 5, 7] } := by
  ext path
  simp only [zRegressionStableSupportedForwardPaths, Finset.mem_filter]
  constructor
  · rintro ⟨hPath, hRefinement⟩
    have hTopologyRefinement :
        (refiningEdgeLists (signalMultigraph topologyProjectionParameters) path).Nonempty :=
      (responseRegression_refiningEdgeLists_nonempty_iff_isChain path).mpr
        ((zRegression_stable_refiningEdgeLists_nonempty_iff_isChain path).mp hRefinement)
    rcases responseRegression_supportedForwardPath_cases hPath hTopologyRefinement with
      rfl | rfl | rfl | rfl <;> simp
  · intro hPath
    simp only [Finset.mem_insert, Finset.mem_singleton] at hPath
    rcases hPath with rfl | rfl | rfl | rfl
    all_goals
      constructor
      · apply mem_forwardPaths_iff.mpr
        decide
      · decide

/-- The upper direct path refines to edges zero, one, and two. -/
lemma zRegression_stable_refiningEdges_upper :
    refiningEdgeLists
        (signalMultigraph (stableUnitDelayParameters.at (-Complex.I))) [0, 2, 5, 7] =
      {[0, 1, 2]} := by
  decide

/-- The lower direct path refines to edges three, four, and five. -/
lemma zRegression_stable_refiningEdges_lower :
    refiningEdgeLists
        (signalMultigraph (stableUnitDelayParameters.at (-Complex.I))) [0, 3, 4, 7] =
      {[3, 4, 5]} := by
  decide

/-- The upper-launch feedback-return path has one seven-edge refinement. -/
lemma zRegression_stable_refiningEdges_upperReturn :
    refiningEdgeLists (signalMultigraph (stableUnitDelayParameters.at (-Complex.I)))
        [0, 2, 5, 6, 1, 3, 4, 7] = {[0, 1, 6, 7, 9, 4, 5]} := by
  decide

/-- The lower-launch feedback-return path has one seven-edge refinement. -/
lemma zRegression_stable_refiningEdges_lowerReturn :
    refiningEdgeLists (signalMultigraph (stableUnitDelayParameters.at (-Complex.I)))
        [0, 3, 4, 6, 1, 2, 5, 7] = {[3, 4, 10, 7, 8, 1, 2]} := by
  decide

/-- Direct multiplication gives upper direct-path gain `-(549/1600) I`. -/
lemma zRegression_stable_edgeListGain_upper :
    edgeListGain (signalMultigraph (stableUnitDelayParameters.at (-Complex.I)))
        [0, 1, 2] = -(549 / 1600) * Complex.I := by
  simp [edgeListGain, signalMultigraph, edgeGain, UnitDelayParameters.at,
    stableUnitDelayParameters, poleRegressionCoupler, Parameters.upperCoefficient,
    DirectionalCoupler.crossCoefficient]
  ring

/-- Direct multiplication gives lower direct-path gain `(16/25) I`. -/
lemma zRegression_stable_edgeListGain_lower :
    edgeListGain (signalMultigraph (stableUnitDelayParameters.at (-Complex.I)))
        [3, 4, 5] = (16 / 25) * Complex.I := by
  simp [edgeListGain, signalMultigraph, edgeGain, UnitDelayParameters.at,
    stableUnitDelayParameters, poleRegressionCoupler, Parameters.lowerCoefficient,
    DirectionalCoupler.crossCoefficient]
  ring_nf
  rw [show Complex.I ^ 3 = -Complex.I by
    norm_num [pow_succ, Complex.I_mul_I]]
  ring

/-- The first feedback-return path has gain `-(549/2500) I`. -/
lemma zRegression_stable_edgeListGain_upperReturn :
    edgeListGain (signalMultigraph (stableUnitDelayParameters.at (-Complex.I)))
        [0, 1, 6, 7, 9, 4, 5] = -(549 / 2500) * Complex.I := by
  simp [edgeListGain, signalMultigraph, edgeGain, UnitDelayParameters.at,
    stableUnitDelayParameters, poleRegressionCoupler, Parameters.upperCoefficient,
    Parameters.lowerCoefficient, Parameters.feedbackCoefficient,
    DirectionalCoupler.crossCoefficient]
  ring_nf
  rw [show Complex.I ^ 5 = Complex.I by
    norm_num [pow_succ, Complex.I_mul_I]]

/-- The second feedback-return path also has gain `-(549/2500) I`. -/
lemma zRegression_stable_edgeListGain_lowerReturn :
    edgeListGain (signalMultigraph (stableUnitDelayParameters.at (-Complex.I)))
        [3, 4, 10, 7, 8, 1, 2] = -(549 / 2500) * Complex.I := by
  simp [edgeListGain, signalMultigraph, edgeGain, UnitDelayParameters.at,
    stableUnitDelayParameters, poleRegressionCoupler, Parameters.upperCoefficient,
    Parameters.lowerCoefficient, Parameters.feedbackCoefficient,
    DirectionalCoupler.crossCoefficient]
  ring_nf
  rw [show Complex.I ^ 5 = Complex.I by
    norm_num [pow_succ, Complex.I_mul_I]]

/-- Removing the upper direct path leaves only the lower-loop cofactor `34/25`. -/
lemma zRegression_stable_upperPathCofactor :
    edgeGraphDetOn (signalMultigraph (stableUnitDelayParameters.at (-Complex.I)))
        (Finset.univ \ [0, 2, 5, 7].toFinset) = 34 / 25 := by
  rw [zRegression_stable_edgeGraphDetOn, if_neg (by decide), if_pos (by decide)]
  norm_num

/-- Removing the lower direct path leaves only the upper-loop cofactor `39/100`. -/
lemma zRegression_stable_lowerPathCofactor :
    edgeGraphDetOn (signalMultigraph (stableUnitDelayParameters.at (-Complex.I)))
        (Finset.univ \ [0, 3, 4, 7].toFinset) = 39 / 100 := by
  rw [zRegression_stable_edgeGraphDetOn, if_pos (by decide), if_neg (by decide)]
  norm_num

/-- Each feedback-return path visits every node, so its cofactor is one. -/
lemma zRegression_stable_upperReturnPathCofactor :
    edgeGraphDetOn (signalMultigraph (stableUnitDelayParameters.at (-Complex.I)))
        (Finset.univ \ [0, 2, 5, 6, 1, 3, 4, 7].toFinset) = 1 := by
  rw [zRegression_stable_edgeGraphDetOn, if_neg (by decide), if_neg (by decide)]
  norm_num

/-- The other feedback-return path also visits every node and has unit cofactor. -/
lemma zRegression_stable_lowerReturnPathCofactor :
    edgeGraphDetOn (signalMultigraph (stableUnitDelayParameters.at (-Complex.I)))
        (Finset.univ \ [0, 3, 4, 6, 1, 2, 5, 7].toFinset) = 1 := by
  rw [zRegression_stable_edgeGraphDetOn, if_neg (by decide), if_neg (by decide)]
  norm_num

/-- Unsupported paths contribute an empty edge-refinement sum at the stable fixture. -/
lemma zRegression_stable_edgeMasonNumerator_eq_supportedSum :
    edgeMasonNumerator
        (signalMultigraph (stableUnitDelayParameters.at (-Complex.I))) 0 7 =
      ∑ path ∈ zRegressionStableSupportedForwardPaths,
        ∑ edgeList ∈ refiningEdgeLists
            (signalMultigraph (stableUnitDelayParameters.at (-Complex.I))) path,
          edgeListGain
              (signalMultigraph (stableUnitDelayParameters.at (-Complex.I))) edgeList *
            edgeGraphDetOn
              (signalMultigraph (stableUnitDelayParameters.at (-Complex.I)))
                (Finset.univ \ path.toFinset) := by
  rw [edgeMasonNumerator]
  symm
  unfold zRegressionStableSupportedForwardPaths
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro path hPath hUnsupported
  have hEmpty : refiningEdgeLists
      (signalMultigraph (stableUnitDelayParameters.at (-Complex.I))) path = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro hNonempty
    exact hUnsupported (Finset.mem_filter.mpr ⟨hPath, hNonempty⟩)
  simp [hEmpty]

/-- The complete eleven-branch numerator is `-(21/32) I`. -/
lemma zRegression_stable_edgeMasonNumerator :
    edgeMasonNumerator
        (signalMultigraph (stableUnitDelayParameters.at (-Complex.I))) 0 7 =
      -(21 / 32) * Complex.I := by
  rw [zRegression_stable_edgeMasonNumerator_eq_supportedSum,
    zRegression_stable_supportedForwardPaths]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [zRegression_stable_refiningEdges_upper, zRegression_stable_refiningEdges_lower,
    zRegression_stable_refiningEdges_upperReturn,
    zRegression_stable_refiningEdges_lowerReturn]
  simp only [Finset.sum_singleton]
  rw [zRegression_stable_edgeListGain_upper, zRegression_stable_edgeListGain_lower,
    zRegression_stable_edgeListGain_upperReturn,
    zRegression_stable_edgeListGain_lowerReturn,
    zRegression_stable_upperPathCofactor, zRegression_stable_lowerPathCofactor,
    zRegression_stable_upperReturnPathCofactor,
    zRegression_stable_lowerReturnPathCofactor]
  ring

/-- The two touching loops give the complete eleven-branch determinant `3/4`. -/
lemma zRegression_stable_edgeGraphDet :
    edgeGraphDet
        (signalMultigraph (stableUnitDelayParameters.at (-Complex.I))) = 3 / 4 := by
  rw [edgeGraphDet, zRegression_stable_edgeGraphDetOn,
    if_pos (by decide), if_pos (by decide)]
  norm_num

/-- Independent eleven-branch Mason enumeration gives `-(7/8) I` at `q = -I`. -/
lemma zRegression_stable_auditedMasonResponse_neg_I :
    auditedMasonResponse (stableUnitDelayParameters.at (-Complex.I)) =
      -(7 / 8) * Complex.I := by
  rw [auditedMasonResponse, zRegression_stable_edgeMasonNumerator,
    zRegression_stable_edgeGraphDet]
  ring

end

end Optics.DCDR
