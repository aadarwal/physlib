/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Systems.DCDR.Mason
public import Physlib.Optics.Systems.DCDR.TopologyRegression

/-!
# Regression tests for the DCDR response

## i. Overview

An asymmetric zero-feedback fixture obtains the N5 response from the complete netlist relation.
It opens `toBehavior_responseTransform`, extracts the raw scattering and routing witnesses, and
solves the eight projected equations in order. It never uses `eliminationResponse_eq_transfer`.

The Mason side retains all eleven edge identities. Its denominator audit works directly on
`edgeChoices`: every nonempty loop refinement contains the feedback edge, whose fixture gain is
zero. Its numerator audit filters the executable forward-path enumeration to the four paths
supported by those eleven edges and multiplies their edge lists directly. Neither audit uses
`masonGain_eq_gain`, `edgeMasonGain_eq_gain`, or an elimination-response theorem.

A negative-control multigraph swaps the two first-coupler launch edges, matching the rewiring in
`topologySwappedNetlist`. Its independently enumerated Mason response is unequal to the N5
response, so the S-06 fixture is capable of detecting that wiring error.

These are hostile algebraic topology fixtures. Their couplers are not unitary or passive. No
contraction, convergence, causality, delay, pole, zero, stability, resonance, bandwidth,
reciprocity, losslessness, power, or material realization is asserted. Power would mean
normalized modal power, not electromagnetic power before the separately gated
Poynting-normalization bridge.

## ii. Key results

- `DCDR.responseRegression_eliminationResponse`: raw N5 equations give the numeric response.
- `DCDR.responseRegression_edgeMasonNumerator`: eleven-edge enumeration gives its numerator.
- `DCDR.responseRegression_s06`: the two independently computed responses agree.
- `DCDR.responseRegression_swappedEdge_fails_s06`: a launch-edge swap breaks that agreement.

## iii. Table of contents

- A. Independent N5 elimination anchor
- B. Direct loop-refinement audit
- C. Direct forward-path audit
- D. Miswired-edge negative control

## iv. References

U. Siddique, S. M. Beillahi, and S. Tahar, "On the Formal Analysis of Photonic Signal Processing
Systems", FMICS 2015, LNCS 9128, Definitions 1-4 and 8 and Theorem 3 (pp. 167-173).
-/

@[expose] public section

namespace Optics

noncomputable section

namespace DCDR

open Physlib.SignalFlowGraph

/-- The regression uses the same finite external-channel instance as N5 elimination. -/
local instance responseRegressionExternalChannelFintype (p : Parameters) :
    Fintype (netlist p).ExternalChannel :=
  (netlist p).eliminationExternalChannelFintype

/-! ## A. Independent N5 elimination anchor -/

/-- The projection fixture's feedback coefficient makes its scalar denominator one. -/
lemma topologyProjection_hasNonzeroDenominator :
    topologyProjectionParameters.HasNonzeroDenominator := by
  norm_num [Parameters.HasNonzeroDenominator, Parameters.denominator, Parameters.loopGain,
    topologyProjectionParameters, Parameters.feedbackCoefficient,
    MatchedPropagation.transmissionCoefficient, MatchedPropagation.carrierPhaseFactor]

/-- Expanding the complete N5 relation and its eight retained equations gives response `-163`.

This proof does not use `eliminationResponse_eq_transfer` or any Mason agreement theorem.
-/
lemma responseRegression_eliminationResponse :
    eliminationResponse topologyProjectionParameters
      (isWellPosed_of_hasNonzeroDenominator topologyProjectionParameters
        topologyProjection_hasNonzeroDenominator) = -163 := by
  let hWellPosed := isWellPosed_of_hasNonzeroDenominator topologyProjectionParameters
    topologyProjection_hasNonzeroDenominator
  let output := ((netlist topologyProjectionParameters).responseTransform hWellPosed).toLinearMap
    (inputAmplitude topologyProjectionParameters 1)
  have hMember : (inputAmplitude topologyProjectionParameters 1, output) ∈
      (netlist topologyProjectionParameters).behavior := by
    rw [← (netlist topologyProjectionParameters).toBehavior_responseTransform hWellPosed,
      ModeTransform.mem_toBehavior_iff_toLinearMap]
  rcases ((netlist topologyProjectionParameters).mem_behavior_iff_equations
      (inputAmplitude topologyProjectionParameters 1) output).mp hMember with
    ⟨incident, outgoing, hScattering, hAssembly, hOutput⟩
  have hAssembly' : incident =
      (netlist topologyProjectionParameters).connections.incidentAssembly outgoing
        (inputAmplitude topologyProjectionParameters 1) := by
    simpa only [PortConnectionFamily.incidentAssembly] using hAssembly
  let state := forwardState topologyProjectionParameters incident outgoing
  have hForward : ForwardEquations topologyProjectionParameters 1 state := by
    simpa [state] using forwardEquations_of_netlistEquations topologyProjectionParameters
      (inputAmplitude topologyProjectionParameters 1) incident outgoing hScattering hAssembly'
  have h0 : state 0 = 1 := by simpa [state] using hForward.nodeOne
  have h1 : state 1 = 0 := by
    rw [hForward.nodeTwo]
    simp [state, topologyProjectionParameters, Parameters.feedbackCoefficient,
      MatchedPropagation.transmissionCoefficient, MatchedPropagation.carrierPhaseFactor]
  have h2 : state 2 = 2 := by
    rw [hForward.nodeThree, h0, h1]
    norm_num [topologyProjectionParameters, DirectionalCoupler.crossCoefficient]
  have h3 : state 3 = -3 * Complex.I := by
    rw [hForward.nodeFour, h0, h1]
    norm_num [topologyProjectionParameters, DirectionalCoupler.crossCoefficient]
    ring
  have h4 : state 4 = -39 * Complex.I := by
    rw [hForward.nodeFive, h3]
    norm_num [topologyProjectionParameters, Parameters.lowerCoefficient,
      MatchedPropagation.transmissionCoefficient, MatchedPropagation.carrierPhaseFactor]
    ring
  have h5 : state 5 = 22 := by
    rw [hForward.nodeSix, h2]
    norm_num [topologyProjectionParameters, Parameters.upperCoefficient,
      MatchedPropagation.transmissionCoefficient, MatchedPropagation.carrierPhaseFactor]
  have h7 : state 7 = -163 := by
    rw [hForward.nodeEight, h4, h5]
    norm_num [topologyProjectionParameters, DirectionalCoupler.crossCoefficient,
      Complex.I_sq]
    ring_nf
    norm_num [Complex.I_sq]
  have hReadout := congrArg
    (fun value => value (Outgoing.mk (outputChannel topologyProjectionParameters))) hOutput
  rw [outputReadout_apply_output] at hReadout
  have hOutputValue :
      output (Outgoing.mk (outputChannel topologyProjectionParameters)) = -163 := by
    simpa [state, forwardState] using hReadout.trans h7
  have hResponse := responseTransform_apply_inputAmplitude topologyProjectionParameters
    hWellPosed 1
  calc
    eliminationResponse topologyProjectionParameters hWellPosed =
        output (Outgoing.mk (outputChannel topologyProjectionParameters)) := by
      simpa [output] using hResponse.symm
    _ = -163 := hOutputValue

/-! ## B. Direct loop-refinement audit -/

/-- A topological rank that increases along every retained edge except the feedback edge. -/
def responseRegressionNodeRank : Node → ℕ := ![0, 1, 2, 2, 3, 3, 4, 5]

/-- Every branch other than edge seven increases the topological rank. -/
lemma responseRegressionNodeRank_lt (edge : Edge) (hEdge : edge ≠ 7) :
    responseRegressionNodeRank (edgeSource edge) <
      responseRegressionNodeRank (edgeTarget edge) := by
  fin_cases edge <;>
    simp [responseRegressionNodeRank, edgeSource, edgeTarget] at hEdge ⊢

/-- Every nonempty edge refinement of a loop family contains the feedback edge. -/
lemma responseRegression_edgeChoice_contains_feedbackEdge
    {T : Finset Node} {permutation : Equiv.Perm Node}
    {choice : ∀ node ∈ T, Edge} (hT : T.Nonempty)
    (hPermutation : permutation ∈ loopFamilies T)
    (hChoice : choice ∈ edgeChoices (signalMultigraph topologyProjectionParameters)
      T permutation) :
    ∃ node, ∃ hNode : node ∈ T, choice node hNode = 7 := by
  by_contra hMissing
  push Not at hMissing
  obtain ⟨node, hNode, hMax⟩ := Finset.exists_max_image T responseRegressionNodeRank hT
  have hPermutationNode : permutation node ∈ T := by
    by_cases hSupport : node ∈ permutation.support
    · exact (mem_loopFamilies.mp hPermutation)
        (Equiv.Perm.apply_mem_support.mpr hSupport)
    · rw [Equiv.Perm.notMem_support.mp hSupport]
      exact hNode
  have hSelected := Finset.mem_pi.mp hChoice node hNode
  have hEndpoints : edgeSource (choice node hNode) = node ∧
      edgeTarget (choice node hNode) = permutation node := by
    simpa [signalMultigraph] using hSelected
  have hRank := responseRegressionNodeRank_lt (choice node hNode)
    (hMissing node hNode)
  rw [hEndpoints.1, hEndpoints.2] at hRank
  exact (Nat.not_lt_of_ge (hMax (permutation node) hPermutationNode)) hRank

/-- Edge seven has zero gain at the projection fixture. -/
lemma topologyProjection_feedbackEdgeGain :
    (signalMultigraph topologyProjectionParameters).gain 7 = 0 := by
  simpa [signalMultigraph] using congrFun topologyProjection_edgeGains 7

/-- Every nonempty loop refinement has zero gain at the projection fixture. -/
lemma responseRegression_edgeFamilyGain_eq_zero
    {T : Finset Node} {permutation : Equiv.Perm Node}
    {choice : ∀ node ∈ T, Edge} (hT : T.Nonempty)
    (hPermutation : permutation ∈ loopFamilies T)
    (hChoice : choice ∈ edgeChoices (signalMultigraph topologyProjectionParameters)
      T permutation) :
    edgeFamilyGain (signalMultigraph topologyProjectionParameters) T choice = 0 := by
  obtain ⟨node, hNode, hFeedback⟩ :=
    responseRegression_edgeChoice_contains_feedbackEdge hT hPermutation hChoice
  rw [edgeFamilyGain]
  apply Finset.prod_eq_zero (i := ⟨node, hNode⟩)
  · simp
  · simpa [hFeedback] using topologyProjection_feedbackEdgeGain

/-- Direct edge-choice expansion gives unit determinant on every induced node set. -/
lemma responseRegression_edgeGraphDetOn (nodes : Finset Node) :
    edgeGraphDetOn (signalMultigraph topologyProjectionParameters) nodes = 1 := by
  rw [edgeGraphDetOn]
  calc
    (∑ T ∈ nodes.powerset, ∑ permutation ∈ loopFamilies T,
        ∑ choice ∈ edgeChoices (signalMultigraph topologyProjectionParameters)
          T permutation,
          (-1 : ℂ) ^ loopCount T permutation *
            edgeFamilyGain (signalMultigraph topologyProjectionParameters) T choice) =
        ∑ permutation ∈ loopFamilies ∅,
          ∑ choice ∈ edgeChoices (signalMultigraph topologyProjectionParameters)
            ∅ permutation,
            (-1 : ℂ) ^ loopCount ∅ permutation *
              edgeFamilyGain (signalMultigraph topologyProjectionParameters) ∅ choice := by
      apply Finset.sum_eq_single ∅
      · intro T hT hNonempty
        apply Finset.sum_eq_zero
        intro permutation hPermutation
        apply Finset.sum_eq_zero
        intro choice hChoice
        rw [responseRegression_edgeFamilyGain_eq_zero
          (Finset.nonempty_iff_ne_empty.mpr hNonempty) hPermutation hChoice]
        simp
      · simp
    _ = 1 := by
      simp [loopFamilies_empty, edgeChoices, edgeFamilyGain, loopCount]

/-- Direct loop-family expansion gives unit denominator for the eleven-edge projection graph. -/
lemma responseRegression_edgeGraphDet :
    edgeGraphDet (signalMultigraph topologyProjectionParameters) = 1 := by
  exact responseRegression_edgeGraphDetOn Finset.univ

/-! ## C. Direct forward-path audit -/

/-- Forward node paths that have at least one refinement by the retained eleven edges. -/
def responseRegressionSupportedForwardPaths : Finset (List Node) :=
  (forwardPaths 0 7).filter fun path =>
    (refiningEdgeLists (signalMultigraph topologyProjectionParameters) path).Nonempty

/-- Adjacency in the retained eleven-edge topology, independent of the edge gains. -/
def responseRegressionAdjacent (first second : Node) : Prop :=
  ((signalMultigraph topologyProjectionParameters).edgesBetween first second).Nonempty

/-- Refinement nonemptiness is exactly consecutive retained-edge adjacency. -/
lemma responseRegression_refiningEdgeLists_nonempty_iff_isChain (path : List Node) :
    (refiningEdgeLists (signalMultigraph topologyProjectionParameters) path).Nonempty ↔
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
            exact List.IsChain.cons_cons ⟨edge, hEdge⟩
              (ih.mp ⟨tailList, hTailList⟩)
          · intro hChain
            obtain ⟨edge, hEdge⟩ := hChain.rel
            obtain ⟨tailList, hTailList⟩ := ih.mpr hChain.tail
            refine ⟨edge :: tailList, ?_⟩
            rw [refiningEdgeLists]
            exact Finset.mem_biUnion.mpr ⟨edge, hEdge,
              Finset.mem_image.mpr ⟨tailList, hTailList, rfl⟩⟩

/-- The two retained successors of source node zero are nodes two and three. -/
lemma responseRegression_adjacent_zero (next : Node) :
    responseRegressionAdjacent 0 next ↔ next = 2 ∨ next = 3 := by
  fin_cases next <;> unfold responseRegressionAdjacent <;> decide

/-- Node two has only the retained successor node five. -/
lemma responseRegression_adjacent_two (next : Node) :
    responseRegressionAdjacent 2 next ↔ next = 5 := by
  fin_cases next <;> unfold responseRegressionAdjacent <;> decide

/-- Node three has only the retained successor node four. -/
lemma responseRegression_adjacent_three (next : Node) :
    responseRegressionAdjacent 3 next ↔ next = 4 := by
  fin_cases next <;> unfold responseRegressionAdjacent <;> decide

/-- Node four has the retained successors six and seven. -/
lemma responseRegression_adjacent_four (next : Node) :
    responseRegressionAdjacent 4 next ↔ next = 6 ∨ next = 7 := by
  fin_cases next <;> unfold responseRegressionAdjacent <;> decide

/-- Node five has the retained successors six and seven. -/
lemma responseRegression_adjacent_five (next : Node) :
    responseRegressionAdjacent 5 next ↔ next = 6 ∨ next = 7 := by
  fin_cases next <;> unfold responseRegressionAdjacent <;> decide

/-- Node six has only the feedback successor node one. -/
lemma responseRegression_adjacent_six (next : Node) :
    responseRegressionAdjacent 6 next ↔ next = 1 := by
  fin_cases next <;> unfold responseRegressionAdjacent <;> decide

/-- Node one has the retained successors nodes two and three. -/
lemma responseRegression_adjacent_one (next : Node) :
    responseRegressionAdjacent 1 next ↔ next = 2 ∨ next = 3 := by
  fin_cases next <;> unfold responseRegressionAdjacent <;> decide

/-- Output node seven has no retained successor. -/
lemma responseRegression_not_adjacent_seven (next : Node) :
    ¬responseRegressionAdjacent 7 next := by
  fin_cases next <;> unfold responseRegressionAdjacent <;> decide

/-- A retained path that reaches output node seven ends there. -/
lemma responseRegression_chain_from_seven_eq_singleton {rest : List Node}
    (hChain : (7 :: rest).IsChain responseRegressionAdjacent) : rest = [] := by
  cases rest with
  | nil => rfl
  | cons next tail =>
      exact absurd hChain.rel (responseRegression_not_adjacent_seven next)

/-- A simple retained path beginning with the upper launch has one of two tails. -/
lemma responseRegression_upperPath_cases {rest : List Node}
    (hNodup : (0 :: 2 :: rest).Nodup)
    (hLast : (0 :: 2 :: rest).getLast? = some 7)
    (hChain : (0 :: 2 :: rest).IsChain responseRegressionAdjacent) :
    rest = [5, 7] ∨ rest = [5, 6, 1, 3, 4, 7] := by
  rcases rest with _ | ⟨third, rest⟩
  · simp at hLast
  have hThird := (responseRegression_adjacent_two third).mp hChain.tail.rel
  subst third
  rcases rest with _ | ⟨fourth, rest⟩
  · simp at hLast
  rcases (responseRegression_adjacent_five fourth).mp hChain.tail.tail.rel with rfl | rfl
  · rcases rest with _ | ⟨fifth, rest⟩
    · simp at hLast
    have hFifth := (responseRegression_adjacent_six fifth).mp hChain.tail.tail.tail.rel
    subst fifth
    rcases rest with _ | ⟨sixth, rest⟩
    · simp at hLast
    rcases (responseRegression_adjacent_one sixth).mp
        hChain.tail.tail.tail.tail.rel with hSixth | hSixth
    · subst sixth
      simp at hNodup
    · subst sixth
      rcases rest with _ | ⟨seventh, rest⟩
      · simp at hLast
      have hSeventh := (responseRegression_adjacent_three seventh).mp
        hChain.tail.tail.tail.tail.tail.rel
      subst seventh
      rcases rest with _ | ⟨eighth, rest⟩
      · simp at hLast
      rcases (responseRegression_adjacent_four eighth).mp
          hChain.tail.tail.tail.tail.tail.tail.rel with hEighth | hEighth
      · subst eighth
        simp at hNodup
      · subst eighth
        rw [responseRegression_chain_from_seven_eq_singleton
          hChain.tail.tail.tail.tail.tail.tail.tail]
        exact Or.inr rfl
  · rw [responseRegression_chain_from_seven_eq_singleton hChain.tail.tail.tail]
    exact Or.inl rfl

/-- A simple retained path beginning with the lower launch has one of two tails. -/
lemma responseRegression_lowerPath_cases {rest : List Node}
    (hNodup : (0 :: 3 :: rest).Nodup)
    (hLast : (0 :: 3 :: rest).getLast? = some 7)
    (hChain : (0 :: 3 :: rest).IsChain responseRegressionAdjacent) :
    rest = [4, 7] ∨ rest = [4, 6, 1, 2, 5, 7] := by
  rcases rest with _ | ⟨third, rest⟩
  · simp at hLast
  have hThird := (responseRegression_adjacent_three third).mp hChain.tail.rel
  subst third
  rcases rest with _ | ⟨fourth, rest⟩
  · simp at hLast
  rcases (responseRegression_adjacent_four fourth).mp hChain.tail.tail.rel with rfl | rfl
  · rcases rest with _ | ⟨fifth, rest⟩
    · simp at hLast
    have hFifth := (responseRegression_adjacent_six fifth).mp hChain.tail.tail.tail.rel
    subst fifth
    rcases rest with _ | ⟨sixth, rest⟩
    · simp at hLast
    rcases (responseRegression_adjacent_one sixth).mp
        hChain.tail.tail.tail.tail.rel with hSixth | hSixth
    · subst sixth
      rcases rest with _ | ⟨seventh, rest⟩
      · simp at hLast
      have hSeventh := (responseRegression_adjacent_two seventh).mp
        hChain.tail.tail.tail.tail.tail.rel
      subst seventh
      rcases rest with _ | ⟨eighth, rest⟩
      · simp at hLast
      rcases (responseRegression_adjacent_five eighth).mp
          hChain.tail.tail.tail.tail.tail.tail.rel with hEighth | hEighth
      · subst eighth
        simp at hNodup
      · subst eighth
        rw [responseRegression_chain_from_seven_eq_singleton
          hChain.tail.tail.tail.tail.tail.tail.tail]
        exact Or.inr rfl
    · subst sixth
      simp at hNodup
  · rw [responseRegression_chain_from_seven_eq_singleton hChain.tail.tail.tail]
    exact Or.inl rfl

/-- Every supported simple source-to-output node path is one of the four displayed paths. -/
lemma responseRegression_supportedForwardPath_cases {path : List Node}
    (hPath : path ∈ forwardPaths (0 : Node) 7)
    (hRefinement :
      (refiningEdgeLists (signalMultigraph topologyProjectionParameters) path).Nonempty) :
    path = [0, 2, 5, 7] ∨ path = [0, 3, 4, 7] ∨
      path = [0, 2, 5, 6, 1, 3, 4, 7] ∨
      path = [0, 3, 4, 6, 1, 2, 5, 7] := by
  obtain ⟨hNodup, hHead, hLast⟩ := mem_forwardPaths_iff.mp hPath
  have hChain :=
    (responseRegression_refiningEdgeLists_nonempty_iff_isChain path).mp hRefinement
  rcases path with _ | ⟨first, rest⟩
  · simp at hHead
  have hFirst : first = 0 := by simpa using hHead
  subst first
  rcases rest with _ | ⟨second, rest⟩
  · simp at hLast
  rcases (responseRegression_adjacent_zero second).mp hChain.rel with rfl | rfl
  · rcases responseRegression_upperPath_cases hNodup hLast hChain with hRest | hRest
    · subst rest
      exact Or.inl rfl
    · subst rest
      exact Or.inr (Or.inr (Or.inl rfl))
  · rcases responseRegression_lowerPath_cases hNodup hLast hChain with hRest | hRest
    · subst rest
      exact Or.inr (Or.inl rfl)
    · subst rest
      exact Or.inr (Or.inr (Or.inr rfl))

/-- Exactly four simple source-to-output paths are supported by the retained edges. -/
lemma responseRegression_supportedForwardPaths :
    responseRegressionSupportedForwardPaths =
      { [0, 2, 5, 7], [0, 3, 4, 7],
        [0, 2, 5, 6, 1, 3, 4, 7], [0, 3, 4, 6, 1, 2, 5, 7] } := by
  ext path
  simp only [responseRegressionSupportedForwardPaths, Finset.mem_filter]
  constructor
  · rintro ⟨hPath, hRefinement⟩
    rcases responseRegression_supportedForwardPath_cases hPath hRefinement with
      rfl | rfl | rfl | rfl <;> simp
  · intro hPath
    simp only [Finset.mem_insert, Finset.mem_singleton] at hPath
    rcases hPath with rfl | rfl | rfl | rfl
    all_goals
      constructor
      · apply mem_forwardPaths_iff.mpr
        decide
      · decide

/-- The direct upper path refines to edges zero, one, and two. -/
lemma responseRegression_refiningEdges_upper :
    refiningEdgeLists (signalMultigraph topologyProjectionParameters) [0, 2, 5, 7] =
      { [0, 1, 2] } := by
  decide

/-- The direct lower path refines to edges three, four, and five. -/
lemma responseRegression_refiningEdges_lower :
    refiningEdgeLists (signalMultigraph topologyProjectionParameters) [0, 3, 4, 7] =
      { [3, 4, 5] } := by
  decide

/-- The upper launch followed by the lower return has one retained edge refinement. -/
lemma responseRegression_refiningEdges_upperReturn :
    refiningEdgeLists (signalMultigraph topologyProjectionParameters)
      [0, 2, 5, 6, 1, 3, 4, 7] = { [0, 1, 6, 7, 9, 4, 5] } := by
  decide

/-- The lower launch followed by the upper return has one retained edge refinement. -/
lemma responseRegression_refiningEdges_lowerReturn :
    refiningEdgeLists (signalMultigraph topologyProjectionParameters)
      [0, 3, 4, 6, 1, 2, 5, 7] = { [3, 4, 10, 7, 8, 1, 2] } := by
  decide

/-- Unsupported node paths contribute an empty edge-refinement sum. -/
lemma responseRegression_edgeMasonNumerator_eq_supportedSum :
    edgeMasonNumerator (signalMultigraph topologyProjectionParameters) 0 7 =
      ∑ path ∈ responseRegressionSupportedForwardPaths,
        ∑ edgeList ∈
            refiningEdgeLists (signalMultigraph topologyProjectionParameters) path,
          edgeListGain (signalMultigraph topologyProjectionParameters) edgeList *
            edgeGraphDetOn (signalMultigraph topologyProjectionParameters)
              (Finset.univ \ path.toFinset) := by
  rw [edgeMasonNumerator]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro path hPath hUnsupported
  have hEmpty :
      refiningEdgeLists (signalMultigraph topologyProjectionParameters) path = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro hNonempty
    exact hUnsupported (Finset.mem_filter.mpr ⟨hPath, hNonempty⟩)
  simp [hEmpty]

/-- The direct upper edge list has gain `110`. -/
lemma responseRegression_edgeListGain_upper :
    edgeListGain (signalMultigraph topologyProjectionParameters) [0, 1, 2] = 110 := by
  simp [edgeListGain, signalMultigraph, edgeGain, topologyProjectionParameters,
    Parameters.upperCoefficient, MatchedPropagation.transmissionCoefficient,
    MatchedPropagation.carrierPhaseFactor]
  norm_num

/-- The direct lower edge list has gain `-273`. -/
lemma responseRegression_edgeListGain_lower :
    edgeListGain (signalMultigraph topologyProjectionParameters) [3, 4, 5] = -273 := by
  simp [edgeListGain, signalMultigraph, edgeGain, topologyProjectionParameters,
    Parameters.lowerCoefficient, DirectionalCoupler.crossCoefficient,
    MatchedPropagation.transmissionCoefficient, MatchedPropagation.carrierPhaseFactor]
  ring_nf
  norm_num [Complex.I_sq]

/-- The upper-launch feedback-return edge list vanishes at edge seven. -/
lemma responseRegression_edgeListGain_upperReturn :
    edgeListGain (signalMultigraph topologyProjectionParameters) [0, 1, 6, 7, 9, 4, 5] =
      0 := by
  simp [edgeListGain, topologyProjection_feedbackEdgeGain]

/-- The lower-launch feedback-return edge list vanishes at edge seven. -/
lemma responseRegression_edgeListGain_lowerReturn :
    edgeListGain (signalMultigraph topologyProjectionParameters) [3, 4, 10, 7, 8, 1, 2] =
      0 := by
  simp [edgeListGain, topologyProjection_feedbackEdgeGain]

/-- Direct eleven-edge path and cofactor enumeration gives Mason numerator `-163`. -/
lemma responseRegression_edgeMasonNumerator :
    edgeMasonNumerator (signalMultigraph topologyProjectionParameters) 0 7 = -163 := by
  rw [responseRegression_edgeMasonNumerator_eq_supportedSum,
    responseRegression_supportedForwardPaths]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [responseRegression_refiningEdges_upper, responseRegression_refiningEdges_lower,
    responseRegression_refiningEdges_upperReturn,
    responseRegression_refiningEdges_lowerReturn]
  simp only [Finset.sum_singleton]
  rw [responseRegression_edgeListGain_upper, responseRegression_edgeListGain_lower,
    responseRegression_edgeListGain_upperReturn,
    responseRegression_edgeListGain_lowerReturn]
  simp [responseRegression_edgeGraphDetOn]
  norm_num

/-- The directly enumerated edge-level Mason quotient is `-163`. -/
lemma responseRegression_auditedMasonResponse :
    auditedMasonResponse topologyProjectionParameters = -163 := by
  rw [auditedMasonResponse, responseRegression_edgeMasonNumerator,
    responseRegression_edgeGraphDet]
  norm_num

/-- S-06: independently expanded N5 elimination and eleven-edge Mason enumeration agree. -/
lemma responseRegression_s06 :
    auditedMasonResponse topologyProjectionParameters =
      eliminationResponse topologyProjectionParameters
        (isWellPosed_of_hasNonzeroDenominator topologyProjectionParameters
          topologyProjection_hasNonzeroDenominator) := by
  rw [responseRegression_auditedMasonResponse,
    responseRegression_eliminationResponse]

/-! ## D. Miswired-edge negative control -/

/-- Edge sources after swapping the first coupler's two launch wires. -/
def responseRegressionSwappedEdgeSource : Edge → Node :=
  ![0, 3, 5, 0, 2, 4, 5, 6, 1, 1, 4]

/-- The edge graph induced by the same launch swap as `topologySwappedNetlist`. -/
def responseRegressionSwappedMultigraph : Multigraph Node Edge where
  source := responseRegressionSwappedEdgeSource
  target := edgeTarget
  gain := edgeGain topologyProjectionParameters

/-- The swapped source vector differs from the production graph at a launch edge. -/
lemma responseRegression_swappedEdgeSource_ne :
    responseRegressionSwappedEdgeSource ≠ edgeSource := by
  intro hSource
  have hEdge := congrFun hSource 1
  norm_num [responseRegressionSwappedEdgeSource, edgeSource] at hEdge
  exact (by decide : (3 : Node) ≠ 2) hEdge

/-- Every swapped branch other than edge seven increases the same topological rank. -/
lemma responseRegression_swappedNodeRank_lt (edge : Edge) (hEdge : edge ≠ 7) :
    responseRegressionNodeRank (responseRegressionSwappedEdgeSource edge) <
      responseRegressionNodeRank (edgeTarget edge) := by
  fin_cases edge <;>
    simp [responseRegressionNodeRank, responseRegressionSwappedEdgeSource,
      edgeTarget] at hEdge ⊢

/-- Every nonempty swapped loop refinement still contains the feedback edge. -/
lemma responseRegression_swappedEdgeChoice_contains_feedbackEdge
    {T : Finset Node} {permutation : Equiv.Perm Node}
    {choice : ∀ node ∈ T, Edge} (hT : T.Nonempty)
    (hPermutation : permutation ∈ loopFamilies T)
    (hChoice : choice ∈ edgeChoices responseRegressionSwappedMultigraph T permutation) :
    ∃ node, ∃ hNode : node ∈ T, choice node hNode = 7 := by
  by_contra hMissing
  push Not at hMissing
  obtain ⟨node, hNode, hMax⟩ := Finset.exists_max_image T responseRegressionNodeRank hT
  have hPermutationNode : permutation node ∈ T := by
    by_cases hSupport : node ∈ permutation.support
    · exact (mem_loopFamilies.mp hPermutation)
        (Equiv.Perm.apply_mem_support.mpr hSupport)
    · rw [Equiv.Perm.notMem_support.mp hSupport]
      exact hNode
  have hSelected := Finset.mem_pi.mp hChoice node hNode
  have hEndpoints :
      responseRegressionSwappedEdgeSource (choice node hNode) = node ∧
        edgeTarget (choice node hNode) = permutation node := by
    simpa [responseRegressionSwappedMultigraph] using hSelected
  have hRank := responseRegression_swappedNodeRank_lt (choice node hNode)
    (hMissing node hNode)
  rw [hEndpoints.1, hEndpoints.2] at hRank
  exact (Nat.not_lt_of_ge (hMax (permutation node) hPermutationNode)) hRank

/-- Every nonempty swapped loop refinement has zero gain. -/
lemma responseRegression_swappedEdgeFamilyGain_eq_zero
    {T : Finset Node} {permutation : Equiv.Perm Node}
    {choice : ∀ node ∈ T, Edge} (hT : T.Nonempty)
    (hPermutation : permutation ∈ loopFamilies T)
    (hChoice : choice ∈ edgeChoices responseRegressionSwappedMultigraph T permutation) :
    edgeFamilyGain responseRegressionSwappedMultigraph T choice = 0 := by
  obtain ⟨node, hNode, hFeedback⟩ :=
    responseRegression_swappedEdgeChoice_contains_feedbackEdge hT hPermutation hChoice
  rw [edgeFamilyGain]
  apply Finset.prod_eq_zero (i := ⟨node, hNode⟩)
  · simp
  · simpa [responseRegressionSwappedMultigraph, signalMultigraph, hFeedback] using
      topologyProjection_feedbackEdgeGain

/-- Direct edge-choice expansion gives unit determinant on every swapped induced node set. -/
lemma responseRegression_swappedEdgeGraphDetOn (nodes : Finset Node) :
    edgeGraphDetOn responseRegressionSwappedMultigraph nodes = 1 := by
  rw [edgeGraphDetOn]
  calc
    (∑ T ∈ nodes.powerset, ∑ permutation ∈ loopFamilies T,
        ∑ choice ∈ edgeChoices responseRegressionSwappedMultigraph T permutation,
          (-1 : ℂ) ^ loopCount T permutation *
            edgeFamilyGain responseRegressionSwappedMultigraph T choice) =
        ∑ permutation ∈ loopFamilies ∅,
          ∑ choice ∈ edgeChoices responseRegressionSwappedMultigraph ∅ permutation,
            (-1 : ℂ) ^ loopCount ∅ permutation *
              edgeFamilyGain responseRegressionSwappedMultigraph ∅ choice := by
      apply Finset.sum_eq_single ∅
      · intro T hT hNonempty
        apply Finset.sum_eq_zero
        intro permutation hPermutation
        apply Finset.sum_eq_zero
        intro choice hChoice
        rw [responseRegression_swappedEdgeFamilyGain_eq_zero
          (Finset.nonempty_iff_ne_empty.mpr hNonempty) hPermutation hChoice]
        simp
      · simp
    _ = 1 := by
      simp [loopFamilies_empty, edgeChoices, edgeFamilyGain, loopCount]

/-- Direct swapped loop-family expansion gives unit graph determinant. -/
lemma responseRegression_swappedEdgeGraphDet :
    edgeGraphDet responseRegressionSwappedMultigraph = 1 := by
  exact responseRegression_swappedEdgeGraphDetOn Finset.univ

/-- Swapped adjacency in the retained eleven-edge topology. -/
def responseRegressionSwappedAdjacent (first second : Node) : Prop :=
  (responseRegressionSwappedMultigraph.edgesBetween first second).Nonempty

/-- Swapped refinement nonemptiness is exactly consecutive swapped adjacency. -/
lemma responseRegression_swappedRefiningEdgeLists_nonempty_iff_isChain (path : List Node) :
    (refiningEdgeLists responseRegressionSwappedMultigraph path).Nonempty ↔
      path.IsChain responseRegressionSwappedAdjacent := by
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
            exact List.IsChain.cons_cons ⟨edge, hEdge⟩
              (ih.mp ⟨tailList, hTailList⟩)
          · intro hChain
            obtain ⟨edge, hEdge⟩ := hChain.rel
            obtain ⟨tailList, hTailList⟩ := ih.mpr hChain.tail
            refine ⟨edge :: tailList, ?_⟩
            rw [refiningEdgeLists]
            exact Finset.mem_biUnion.mpr ⟨edge, hEdge,
              Finset.mem_image.mpr ⟨tailList, hTailList, rfl⟩⟩

/-- Swapped source node zero still has successors two and three. -/
lemma responseRegression_swappedAdjacent_zero (next : Node) :
    responseRegressionSwappedAdjacent 0 next ↔ next = 2 ∨ next = 3 := by
  fin_cases next <;> unfold responseRegressionSwappedAdjacent <;> decide

/-- Swapped node two has only successor node four. -/
lemma responseRegression_swappedAdjacent_two (next : Node) :
    responseRegressionSwappedAdjacent 2 next ↔ next = 4 := by
  fin_cases next <;> unfold responseRegressionSwappedAdjacent <;> decide

/-- Swapped node three has only successor node five. -/
lemma responseRegression_swappedAdjacent_three (next : Node) :
    responseRegressionSwappedAdjacent 3 next ↔ next = 5 := by
  fin_cases next <;> unfold responseRegressionSwappedAdjacent <;> decide

/-- Swapped node four has successors six and seven. -/
lemma responseRegression_swappedAdjacent_four (next : Node) :
    responseRegressionSwappedAdjacent 4 next ↔ next = 6 ∨ next = 7 := by
  fin_cases next <;> unfold responseRegressionSwappedAdjacent <;> decide

/-- Swapped node five has successors six and seven. -/
lemma responseRegression_swappedAdjacent_five (next : Node) :
    responseRegressionSwappedAdjacent 5 next ↔ next = 6 ∨ next = 7 := by
  fin_cases next <;> unfold responseRegressionSwappedAdjacent <;> decide

/-- Swapped node six has only feedback successor node one. -/
lemma responseRegression_swappedAdjacent_six (next : Node) :
    responseRegressionSwappedAdjacent 6 next ↔ next = 1 := by
  fin_cases next <;> unfold responseRegressionSwappedAdjacent <;> decide

/-- Swapped node one has successors two and three. -/
lemma responseRegression_swappedAdjacent_one (next : Node) :
    responseRegressionSwappedAdjacent 1 next ↔ next = 2 ∨ next = 3 := by
  fin_cases next <;> unfold responseRegressionSwappedAdjacent <;> decide

/-- Swapped output node seven has no successor. -/
lemma responseRegression_swappedNotAdjacent_seven (next : Node) :
    ¬responseRegressionSwappedAdjacent 7 next := by
  fin_cases next <;> unfold responseRegressionSwappedAdjacent <;> decide

/-- A swapped retained path that reaches node seven ends there. -/
lemma responseRegression_swappedChain_from_seven_eq_singleton {rest : List Node}
    (hChain : (7 :: rest).IsChain responseRegressionSwappedAdjacent) : rest = [] := by
  cases rest with
  | nil => rfl
  | cons next tail =>
      exact absurd hChain.rel (responseRegression_swappedNotAdjacent_seven next)

/-- A simple swapped path beginning at node two has one of two tails. -/
lemma responseRegression_swappedUpperPath_cases {rest : List Node}
    (hNodup : (0 :: 2 :: rest).Nodup)
    (hLast : (0 :: 2 :: rest).getLast? = some 7)
    (hChain : (0 :: 2 :: rest).IsChain responseRegressionSwappedAdjacent) :
    rest = [4, 7] ∨ rest = [4, 6, 1, 3, 5, 7] := by
  rcases rest with _ | ⟨third, rest⟩
  · simp at hLast
  have hThird := (responseRegression_swappedAdjacent_two third).mp hChain.tail.rel
  subst third
  rcases rest with _ | ⟨fourth, rest⟩
  · simp at hLast
  rcases (responseRegression_swappedAdjacent_four fourth).mp hChain.tail.tail.rel with rfl | rfl
  · rcases rest with _ | ⟨fifth, rest⟩
    · simp at hLast
    have hFifth := (responseRegression_swappedAdjacent_six fifth).mp
      hChain.tail.tail.tail.rel
    subst fifth
    rcases rest with _ | ⟨sixth, rest⟩
    · simp at hLast
    rcases (responseRegression_swappedAdjacent_one sixth).mp
        hChain.tail.tail.tail.tail.rel with hSixth | hSixth
    · subst sixth
      simp at hNodup
    · subst sixth
      rcases rest with _ | ⟨seventh, rest⟩
      · simp at hLast
      have hSeventh := (responseRegression_swappedAdjacent_three seventh).mp
        hChain.tail.tail.tail.tail.tail.rel
      subst seventh
      rcases rest with _ | ⟨eighth, rest⟩
      · simp at hLast
      rcases (responseRegression_swappedAdjacent_five eighth).mp
          hChain.tail.tail.tail.tail.tail.tail.rel with hEighth | hEighth
      · subst eighth
        simp at hNodup
      · subst eighth
        rw [responseRegression_swappedChain_from_seven_eq_singleton
          hChain.tail.tail.tail.tail.tail.tail.tail]
        exact Or.inr rfl
  · rw [responseRegression_swappedChain_from_seven_eq_singleton
      hChain.tail.tail.tail]
    exact Or.inl rfl

/-- A simple swapped path beginning at node three has one of two tails. -/
lemma responseRegression_swappedLowerPath_cases {rest : List Node}
    (hNodup : (0 :: 3 :: rest).Nodup)
    (hLast : (0 :: 3 :: rest).getLast? = some 7)
    (hChain : (0 :: 3 :: rest).IsChain responseRegressionSwappedAdjacent) :
    rest = [5, 7] ∨ rest = [5, 6, 1, 2, 4, 7] := by
  rcases rest with _ | ⟨third, rest⟩
  · simp at hLast
  have hThird := (responseRegression_swappedAdjacent_three third).mp hChain.tail.rel
  subst third
  rcases rest with _ | ⟨fourth, rest⟩
  · simp at hLast
  rcases (responseRegression_swappedAdjacent_five fourth).mp hChain.tail.tail.rel with rfl | rfl
  · rcases rest with _ | ⟨fifth, rest⟩
    · simp at hLast
    have hFifth := (responseRegression_swappedAdjacent_six fifth).mp
      hChain.tail.tail.tail.rel
    subst fifth
    rcases rest with _ | ⟨sixth, rest⟩
    · simp at hLast
    rcases (responseRegression_swappedAdjacent_one sixth).mp
        hChain.tail.tail.tail.tail.rel with hSixth | hSixth
    · subst sixth
      rcases rest with _ | ⟨seventh, rest⟩
      · simp at hLast
      have hSeventh := (responseRegression_swappedAdjacent_two seventh).mp
        hChain.tail.tail.tail.tail.tail.rel
      subst seventh
      rcases rest with _ | ⟨eighth, rest⟩
      · simp at hLast
      rcases (responseRegression_swappedAdjacent_four eighth).mp
          hChain.tail.tail.tail.tail.tail.tail.rel with hEighth | hEighth
      · subst eighth
        simp at hNodup
      · subst eighth
        rw [responseRegression_swappedChain_from_seven_eq_singleton
          hChain.tail.tail.tail.tail.tail.tail.tail]
        exact Or.inr rfl
    · subst sixth
      simp at hNodup
  · rw [responseRegression_swappedChain_from_seven_eq_singleton
      hChain.tail.tail.tail]
    exact Or.inl rfl

/-- Every supported simple swapped path is one of the four displayed paths. -/
lemma responseRegression_swappedSupportedForwardPath_cases {path : List Node}
    (hPath : path ∈ forwardPaths (0 : Node) 7)
    (hRefinement : (refiningEdgeLists responseRegressionSwappedMultigraph path).Nonempty) :
    path = [0, 2, 4, 7] ∨ path = [0, 3, 5, 7] ∨
      path = [0, 2, 4, 6, 1, 3, 5, 7] ∨
      path = [0, 3, 5, 6, 1, 2, 4, 7] := by
  obtain ⟨hNodup, hHead, hLast⟩ := mem_forwardPaths_iff.mp hPath
  have hChain :=
    (responseRegression_swappedRefiningEdgeLists_nonempty_iff_isChain path).mp hRefinement
  rcases path with _ | ⟨first, rest⟩
  · simp at hHead
  have hFirst : first = 0 := by simpa using hHead
  subst first
  rcases rest with _ | ⟨second, rest⟩
  · simp at hLast
  rcases (responseRegression_swappedAdjacent_zero second).mp hChain.rel with rfl | rfl
  · rcases responseRegression_swappedUpperPath_cases hNodup hLast hChain with hRest | hRest
    · subst rest
      exact Or.inl rfl
    · subst rest
      exact Or.inr (Or.inr (Or.inl rfl))
  · rcases responseRegression_swappedLowerPath_cases hNodup hLast hChain with hRest | hRest
    · subst rest
      exact Or.inr (Or.inl rfl)
    · subst rest
      exact Or.inr (Or.inr (Or.inr rfl))

/-- Forward node paths supported by the swapped retained edges. -/
def responseRegressionSwappedSupportedForwardPaths : Finset (List Node) :=
  (forwardPaths 0 7).filter fun path =>
    (refiningEdgeLists responseRegressionSwappedMultigraph path).Nonempty

/-- Exactly four simple source-to-output paths are supported after the launch swap. -/
lemma responseRegression_swappedSupportedForwardPaths :
    responseRegressionSwappedSupportedForwardPaths =
      { [0, 2, 4, 7], [0, 3, 5, 7],
        [0, 2, 4, 6, 1, 3, 5, 7], [0, 3, 5, 6, 1, 2, 4, 7] } := by
  ext path
  simp only [responseRegressionSwappedSupportedForwardPaths, Finset.mem_filter]
  constructor
  · rintro ⟨hPath, hRefinement⟩
    rcases responseRegression_swappedSupportedForwardPath_cases hPath hRefinement with
      rfl | rfl | rfl | rfl <;> simp
  · intro hPath
    simp only [Finset.mem_insert, Finset.mem_singleton] at hPath
    rcases hPath with rfl | rfl | rfl | rfl
    all_goals
      constructor
      · apply mem_forwardPaths_iff.mpr
        decide
      · decide

/-- The swapped direct upper-node path refines to edges zero, four, and five. -/
lemma responseRegression_swappedRefiningEdges_upper :
    refiningEdgeLists responseRegressionSwappedMultigraph [0, 2, 4, 7] =
      { [0, 4, 5] } := by
  decide

/-- The swapped direct lower-node path refines to edges three, one, and two. -/
lemma responseRegression_swappedRefiningEdges_lower :
    refiningEdgeLists responseRegressionSwappedMultigraph [0, 3, 5, 7] =
      { [3, 1, 2] } := by
  decide

/-- The first swapped feedback-return node path has one retained edge refinement. -/
lemma responseRegression_swappedRefiningEdges_upperReturn :
    refiningEdgeLists responseRegressionSwappedMultigraph [0, 2, 4, 6, 1, 3, 5, 7] =
      { [0, 4, 10, 7, 9, 1, 2] } := by
  decide

/-- The second swapped feedback-return node path has one retained edge refinement. -/
lemma responseRegression_swappedRefiningEdges_lowerReturn :
    refiningEdgeLists responseRegressionSwappedMultigraph [0, 3, 5, 6, 1, 2, 4, 7] =
      { [3, 1, 6, 7, 8, 4, 5] } := by
  decide

/-- Unsupported swapped node paths contribute an empty edge-refinement sum. -/
lemma responseRegression_swappedEdgeMasonNumerator_eq_supportedSum :
    edgeMasonNumerator responseRegressionSwappedMultigraph 0 7 =
      ∑ path ∈ responseRegressionSwappedSupportedForwardPaths,
        ∑ edgeList ∈ refiningEdgeLists responseRegressionSwappedMultigraph path,
          edgeListGain responseRegressionSwappedMultigraph edgeList *
            edgeGraphDetOn responseRegressionSwappedMultigraph
              (Finset.univ \ path.toFinset) := by
  rw [edgeMasonNumerator]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro path hPath hUnsupported
  have hEmpty : refiningEdgeLists responseRegressionSwappedMultigraph path = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro hNonempty
    exact hUnsupported (Finset.mem_filter.mpr ⟨hPath, hNonempty⟩)
  simp [hEmpty]

/-- The first swapped direct edge list has gain `-182 * I`. -/
lemma responseRegression_swappedEdgeListGain_upper :
    edgeListGain responseRegressionSwappedMultigraph [0, 4, 5] = -182 * Complex.I := by
  simp [edgeListGain, responseRegressionSwappedMultigraph, edgeGain,
    topologyProjectionParameters, Parameters.lowerCoefficient,
    DirectionalCoupler.crossCoefficient, MatchedPropagation.transmissionCoefficient,
    MatchedPropagation.carrierPhaseFactor]
  ring

/-- The second swapped direct edge list has gain `-165 * I`. -/
lemma responseRegression_swappedEdgeListGain_lower :
    edgeListGain responseRegressionSwappedMultigraph [3, 1, 2] = -165 * Complex.I := by
  simp [edgeListGain, responseRegressionSwappedMultigraph, edgeGain,
    topologyProjectionParameters, Parameters.upperCoefficient,
    DirectionalCoupler.crossCoefficient, MatchedPropagation.transmissionCoefficient,
    MatchedPropagation.carrierPhaseFactor]
  ring

/-- The first swapped feedback-return edge list vanishes at edge seven. -/
lemma responseRegression_swappedEdgeListGain_upperReturn :
    edgeListGain responseRegressionSwappedMultigraph [0, 4, 10, 7, 9, 1, 2] = 0 := by
  have hFeedback : responseRegressionSwappedMultigraph.gain 7 = 0 := by
    simpa [responseRegressionSwappedMultigraph, signalMultigraph] using
      topologyProjection_feedbackEdgeGain
  simp [edgeListGain, hFeedback]

/-- The second swapped feedback-return edge list vanishes at edge seven. -/
lemma responseRegression_swappedEdgeListGain_lowerReturn :
    edgeListGain responseRegressionSwappedMultigraph [3, 1, 6, 7, 8, 4, 5] = 0 := by
  have hFeedback : responseRegressionSwappedMultigraph.gain 7 = 0 := by
    simpa [responseRegressionSwappedMultigraph, signalMultigraph] using
      topologyProjection_feedbackEdgeGain
  simp [edgeListGain, hFeedback]

/-- Direct swapped eleven-edge enumeration gives numerator `-347 * I`. -/
lemma responseRegression_swappedEdgeMasonNumerator :
    edgeMasonNumerator responseRegressionSwappedMultigraph 0 7 = -347 * Complex.I := by
  rw [responseRegression_swappedEdgeMasonNumerator_eq_supportedSum,
    responseRegression_swappedSupportedForwardPaths]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [responseRegression_swappedRefiningEdges_upper,
    responseRegression_swappedRefiningEdges_lower,
    responseRegression_swappedRefiningEdges_upperReturn,
    responseRegression_swappedRefiningEdges_lowerReturn]
  simp only [Finset.sum_singleton]
  rw [responseRegression_swappedEdgeListGain_upper,
    responseRegression_swappedEdgeListGain_lower,
    responseRegression_swappedEdgeListGain_upperReturn,
    responseRegression_swappedEdgeListGain_lowerReturn]
  simp [responseRegression_swappedEdgeGraphDetOn]
  ring

/-- The edge-level Mason quotient of the deliberately swapped launch graph. -/
noncomputable def responseRegressionSwappedMasonResponse : ℂ :=
  edgeMasonNumerator responseRegressionSwappedMultigraph 0 7 /
    edgeGraphDet responseRegressionSwappedMultigraph

/-- The swapped edge-level Mason quotient is `-347 * I`. -/
lemma responseRegression_swappedMasonResponse :
    responseRegressionSwappedMasonResponse = -347 * Complex.I := by
  rw [responseRegressionSwappedMasonResponse,
    responseRegression_swappedEdgeMasonNumerator,
    responseRegression_swappedEdgeGraphDet]
  norm_num

/-- The miswired launch-edge fixture fails S-06 against the unchanged N5 elimination response. -/
lemma responseRegression_swappedEdge_fails_s06 :
    responseRegressionSwappedMasonResponse ≠
      eliminationResponse topologyProjectionParameters
        (isWellPosed_of_hasNonzeroDenominator topologyProjectionParameters
          topologyProjection_hasNonzeroDenominator) := by
  rw [responseRegression_swappedMasonResponse,
    responseRegression_eliminationResponse]
  intro hEqual
  have hReal := congrArg Complex.re hEqual
  norm_num at hReal

end DCDR

end

end Optics
