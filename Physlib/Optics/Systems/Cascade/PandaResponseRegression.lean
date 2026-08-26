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
Independent loop-family and supported-path expansions give determinant `10/13` and the two Mason
numerators. The terminated values come from the raw node equation and this determinant, without
either NSV'16 comparison theorem. The relational bridge then supplies an actual raw N5 behavior
witness and response-transform values under its explicit solve gate.

The negative fixture changes both bus couplers to identity through-coupling. Its printed source
denominator is zero. A displayed nonzero homogeneous vector satisfies the raw matrix equation,
which forces the graph determinant to vanish. Thus the solve gate is executable and able to fail;
the totalized source quotients are not assigned response meaning at that point.

## ii. Key results

- `Panda.responseRegression_rawNodeEquation`: hand-expanded positive 24-edge matrix anchor.
- `Panda.responseRegression_edgeGraphDet`: exhaustive loop-family determinant expansion.
- `Panda.responseRegression_edgeMasonNumerator_through`: exhaustive through numerator.
- `Panda.responseRegression_edgeMasonNumerator_drop`: exhaustive drop numerator.
- `Panda.responseRegression_throughTerminated`: unique through transfer `7/25`.
- `Panda.responseRegression_dropTerminated`: unique drop transfer `-24/25`.
- `Panda.responseRegression_rawNetlistBehavior`: actual N7/N5 behavior anchor.
- `Panda.responseRegression_singularGraphDet`: explicit determinant-zero point.

## iii. Table of contents

- A. Positive normalized fixture
- B. Direct loop-family determinant expansion
- C. Direct supported-path numerator expansion
- D. Hand-expanded matrix and N5 anchors
- E. Singular determinant fixture

## iv. References

These fixtures audit coherent complex amplitudes. They assert no passivity, reciprocity,
losslessness, causality, convergence, stability, resonance, bandwidth, dispersion, power
normalization, or material realization.
-/

@[expose] public section

namespace Optics

noncomputable section

namespace Panda

open Physlib.SignalFlowGraph
/-!
## A. Positive normalized fixture
-/
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
/-!
## B. Direct loop-family determinant expansion
-/
/-- A topological rank that increases on every retained edge except the two zero-gain side-ring
returns and the main-ring feedback edge. -/
def responseRegressionNodeRank : Node → ℕ :=
  ![0, 0, 14, 1, 7, 0, 8, 14, 2, 6, 3, 4, 5, 9, 13, 10, 11, 12]

/-- Every retained branch except edges eight, twenty, and twenty-three increases the rank. -/
lemma responseRegressionNodeRank_lt (edge : Edge)
    (hEdge : edge ≠ 8 ∧ edge ≠ 20 ∧ edge ≠ 23) :
    responseRegressionNodeRank (edgeSource edge) <
      responseRegressionNodeRank (edgeTarget edge) := by
  fin_cases edge <;>
    simp [responseRegressionNodeRank, edgeSource, edgeTarget] at hEdge ⊢

/-- Every nonempty loop-family refinement uses a rank-decreasing retained edge. -/
private lemma responseRegression_edgeChoice_contains_rankReturn
    {T : Finset Node} {permutation : Equiv.Perm Node}
    {choice : ∀ node ∈ T, Edge} (hT : T.Nonempty)
    (hPermutation : permutation ∈ loopFamilies T)
    (hChoice : choice ∈
      edgeChoices (signalMultigraph responseRegressionParameters) T permutation) :
    ∃ node, ∃ hNode : node ∈ T,
      choice node hNode = 8 ∨ choice node hNode = 20 ∨ choice node hNode = 23 := by
  by_contra hMissing
  push Not at hMissing
  obtain ⟨node, hNode, hMax⟩ :=
    Finset.exists_max_image T responseRegressionNodeRank hT
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
    ⟨hMissing node hNode |>.1,
      hMissing node hNode |>.2.1,
      hMissing node hNode |>.2.2⟩
  rw [hEndpoints.1, hEndpoints.2] at hRank
  exact (Nat.not_lt_of_ge (hMax (permutation node) hPermutationNode)) hRank

/-- A nonzero family product makes every selected branch gain nonzero. -/
private lemma responseRegression_selectedGain_ne_zero
    {T : Finset Node} {choice : ∀ node ∈ T, Edge}
    (hFamily : edgeFamilyGain (signalMultigraph responseRegressionParameters) T choice ≠ 0)
    (node : Node) (hNode : node ∈ T) :
    (signalMultigraph responseRegressionParameters).gain (choice node hNode) ≠ 0 := by
  intro hGain
  apply hFamily
  rw [edgeFamilyGain]
  apply Finset.prod_eq_zero (i := ⟨node, hNode⟩)
  · simp
  · simpa using hGain

/-- A selected edge records its source and its permutation target. -/
private lemma responseRegression_selectedEndpoints
    {T : Finset Node} {permutation : Equiv.Perm Node}
    {choice : ∀ node ∈ T, Edge}
    (hChoice : choice ∈
      edgeChoices (signalMultigraph responseRegressionParameters) T permutation)
    (node : Node) (hNode : node ∈ T) :
    edgeSource (choice node hNode) = node ∧
      edgeTarget (choice node hNode) = permutation node := by
  have hSelected := Finset.mem_pi.mp hChoice node hNode
  simpa [signalMultigraph] using hSelected

/-- A loop-family permutation preserves its declared node set. -/
private lemma responseRegression_permutation_mem
    {T : Finset Node} {permutation : Equiv.Perm Node}
    (hPermutation : permutation ∈ loopFamilies T)
    (node : Node) (hNode : node ∈ T) : permutation node ∈ T := by
  by_cases hSupport : node ∈ permutation.support
  · exact (mem_loopFamilies.mp hPermutation)
      (Equiv.Perm.apply_mem_support.mpr hSupport)
  · rw [Equiv.Perm.notMem_support.mp hSupport]
    exact hNode

/-- No retained edge leaves the through-output node. -/
private lemma responseRegression_noEdgeSource_two (edge : Edge) : edgeSource edge ≠ 2 := by
  fin_cases edge <;> simp [edgeSource]

/-- No retained edge leaves the drop-output node. -/
private lemma responseRegression_noEdgeSource_seven (edge : Edge) : edgeSource edge ≠ 7 := by
  fin_cases edge <;> simp [edgeSource]

/-- The nonzero retained edges leaving node two in the paper's numbering are the two input-coupler
branches. -/
private lemma responseRegression_nonzeroEdge_from_one (edge : Edge)
    (hSource : edgeSource edge = 1) : edge = 2 ∨ edge = 3 := by
  fin_cases edge <;> simp [edgeSource] at hSource ⊢

/-- The only retained edge leaving node four in the paper's numbering is edge four. -/
private lemma responseRegression_edge_from_three (edge : Edge)
    (hSource : edgeSource edge = 3) : edge = 4 := by
  fin_cases edge <;> simp [edgeSource] at hSource ⊢

/-- The only nonzero fixture edge leaving the first right-coupler node is its direct branch. -/
private lemma responseRegression_nonzeroEdge_from_eight (edge : Edge)
    (hSource : edgeSource edge = 8)
    (hGain : (signalMultigraph responseRegressionParameters).gain edge ≠ 0) : edge = 5 := by
  fin_cases edge <;> simp [edgeSource] at hSource
  all_goals
    simp_all [signalMultigraph, edgeGain, responseRegressionParameters,
      DirectionalCoupler.crossCoefficient]

/-- The only retained edge leaving node ten is the second main-quarter branch. -/
private lemma responseRegression_edge_from_nine (edge : Edge)
    (hSource : edgeSource edge = 9) : edge = 11 := by
  fin_cases edge <;> simp [edgeSource] at hSource ⊢

/-- The two retained output-coupler branches leave node five. -/
private lemma responseRegression_edge_from_four (edge : Edge)
    (hSource : edgeSource edge = 4) : edge = 12 ∨ edge = 13 := by
  fin_cases edge <;> simp [edgeSource] at hSource ⊢

/-- The only retained edge leaving node seven is the third main quarter. -/
private lemma responseRegression_edge_from_six (edge : Edge)
    (hSource : edgeSource edge = 6) : edge = 16 := by
  fin_cases edge <;> simp [edgeSource] at hSource ⊢

/-- The only nonzero fixture edge leaving the first left-coupler node is its direct branch. -/
private lemma responseRegression_nonzeroEdge_from_thirteen (edge : Edge)
    (hSource : edgeSource edge = 13)
    (hGain : (signalMultigraph responseRegressionParameters).gain edge ≠ 0) : edge = 17 := by
  fin_cases edge <;> simp [edgeSource] at hSource
  all_goals
    simp_all [signalMultigraph, edgeGain, responseRegressionParameters,
      DirectionalCoupler.crossCoefficient]

/-- The only retained edge leaving node fifteen is the fourth main quarter. -/
private lemma responseRegression_edge_from_fourteen (edge : Edge)
    (hSource : edgeSource edge = 14) : edge = 23 := by
  fin_cases edge <;> simp [edgeSource] at hSource ⊢

/-- Nodes of the unique nonzero loop-family refinement at the positive fixture. -/
def responseRegressionMainLoopNodes : Finset Node :=
  {1, 3, 8, 9, 4, 6, 13, 14}

/-- Permutation carried by the unique nonzero main-ring loop. -/
def responseRegressionMainLoopPermutation : Equiv.Perm Node :=
  [1, 3, 8, 9, 4, 6, 13, 14].formPerm

/-- The unique edge selected at each node of the nonzero main-ring loop. -/
def responseRegressionMainLoopEdge : Node → Edge :=
  ![0, 2, 0, 4, 12, 0, 16, 0, 5, 11, 0, 0, 0, 17, 23, 0, 0, 0]

/-- The dependent edge choice carried by the nonzero main-ring loop. -/
def responseRegressionMainLoopChoice :
    ∀ node ∈ responseRegressionMainLoopNodes, Edge :=
  fun node _ ↦ responseRegressionMainLoopEdge node

/-- The displayed main permutation is a loop family on exactly the displayed nodes. -/
lemma responseRegression_mainLoopPermutation_mem :
    responseRegressionMainLoopPermutation ∈
      loopFamilies responseRegressionMainLoopNodes := by
  apply mem_loopFamilies.mpr
  simpa [responseRegressionMainLoopPermutation, responseRegressionMainLoopNodes] using
    List.support_formPerm_le ([1, 3, 8, 9, 4, 6, 13, 14] : List Node)

/-- The displayed main edge selection refines the displayed permutation. -/
lemma responseRegression_mainLoopChoice_mem :
    responseRegressionMainLoopChoice ∈
      edgeChoices (signalMultigraph responseRegressionParameters)
        responseRegressionMainLoopNodes responseRegressionMainLoopPermutation := by
  decide

/-- The displayed main family consists of one loop. -/
lemma responseRegression_mainLoopCount :
    loopCount responseRegressionMainLoopNodes responseRegressionMainLoopPermutation = 1 := by
  decide

/-- The unique nonzero loop-family refinement has gain `3/13`. -/
lemma responseRegression_mainLoopFamilyGain :
    edgeFamilyGain (signalMultigraph responseRegressionParameters)
        responseRegressionMainLoopNodes responseRegressionMainLoopChoice = 3 / 13 := by
  rw [edgeFamilyGain]
  simp only [responseRegressionMainLoopChoice]
  calc
    (∏ x ∈ responseRegressionMainLoopNodes.attach,
        (signalMultigraph responseRegressionParameters).gain
          (responseRegressionMainLoopEdge x)) =
        ∏ node ∈ responseRegressionMainLoopNodes,
          (signalMultigraph responseRegressionParameters).gain
            (responseRegressionMainLoopEdge node) :=
      Finset.prod_attach responseRegressionMainLoopNodes
        (fun node ↦ (signalMultigraph responseRegressionParameters).gain
          (responseRegressionMainLoopEdge node))
    _ = 3 / 13 := by
      simp [responseRegressionMainLoopNodes, Finset.prod_insert,
        responseRegressionMainLoopEdge,
        signalMultigraph, edgeGain, responseRegressionParameters,
        responseRegressionPropagation, Parameters.mainQuarterOneCoefficient,
        Parameters.mainQuarterTwoCoefficient, Parameters.mainQuarterThreeCoefficient,
        Parameters.mainQuarterFourCoefficient, MatchedPropagation.transmissionCoefficient,
        MatchedPropagation.carrierPhaseFactor]
      norm_num

/-- The right-side rank-return edge has zero gain at the positive fixture. -/
private lemma responseRegression_edgeEightGain :
    (signalMultigraph responseRegressionParameters).gain 8 = 0 := by
  simp [signalMultigraph, edgeGain, responseRegressionParameters,
    responseRegressionPropagation, Parameters.rightHalfTwoCoefficient,
    MatchedPropagation.transmissionCoefficient, MatchedPropagation.carrierPhaseFactor]

/-- The left-side rank-return edge has zero gain at the positive fixture. -/
private lemma responseRegression_edgeTwentyGain :
    (signalMultigraph responseRegressionParameters).gain 20 = 0 := by
  simp [signalMultigraph, edgeGain, responseRegressionParameters,
    responseRegressionPropagation, Parameters.leftHalfTwoCoefficient,
    MatchedPropagation.transmissionCoefficient, MatchedPropagation.carrierPhaseFactor]

/-- Every nonzero nonempty loop-family refinement is exactly the displayed main-ring family at
the level of its node set and permutation. -/
private lemma responseRegression_nonzeroFamily_eq_main
    {T : Finset Node} {permutation : Equiv.Perm Node}
    {choice : ∀ node ∈ T, Edge} (hT : T.Nonempty)
    (hPermutation : permutation ∈ loopFamilies T)
    (hChoice : choice ∈
      edgeChoices (signalMultigraph responseRegressionParameters) T permutation)
    (hFamily :
      edgeFamilyGain (signalMultigraph responseRegressionParameters) T choice ≠ 0) :
    T = responseRegressionMainLoopNodes ∧
      permutation = responseRegressionMainLoopPermutation := by
  obtain ⟨feedbackNode, hFeedbackNode, hFeedbackEdge⟩ :=
    responseRegression_edgeChoice_contains_rankReturn hT hPermutation hChoice
  have hFeedbackGain := responseRegression_selectedGain_ne_zero
    hFamily feedbackNode hFeedbackNode
  have hFeedbackEndpoints :=
    responseRegression_selectedEndpoints hChoice feedbackNode hFeedbackNode
  have hFeedbackIsTwentyThree : choice feedbackNode hFeedbackNode = 23 := by
    rcases hFeedbackEdge with hEight | hTwenty | hTwentyThree
    · exfalso
      apply hFeedbackGain
      rw [hEight, responseRegression_edgeEightGain]
    · exfalso
      apply hFeedbackGain
      rw [hTwenty, responseRegression_edgeTwentyGain]
    · exact hTwentyThree
  have hFeedbackNodeEq : feedbackNode = 14 := by
    simpa [hFeedbackIsTwentyThree, edgeSource] using hFeedbackEndpoints.1.symm
  subst feedbackNode
  have h14 : (14 : Node) ∈ T := hFeedbackNode
  have hChoice14 : choice 14 h14 = 23 := hFeedbackIsTwentyThree
  have hPermutation14 : permutation 14 = 1 := by
    simpa [hChoice14, edgeTarget] using hFeedbackEndpoints.2.symm
  have h1 : (1 : Node) ∈ T := by
    rw [← hPermutation14]
    exact responseRegression_permutation_mem hPermutation 14 h14
  have hEndpoints1 := responseRegression_selectedEndpoints hChoice 1 h1
  have hChoice1 : choice 1 h1 = 2 := by
    rcases responseRegression_nonzeroEdge_from_one _ hEndpoints1.1 with hTwo | hThree
    · exact hTwo
    · have hPermutation1 : permutation 1 = 2 := by
        simpa [hThree, edgeTarget] using hEndpoints1.2.symm
      have h2 : (2 : Node) ∈ T := by
        rw [← hPermutation1]
        exact responseRegression_permutation_mem hPermutation 1 h1
      exact absurd (responseRegression_selectedEndpoints hChoice 2 h2).1
        (responseRegression_noEdgeSource_two _)
  have hPermutation1 : permutation 1 = 3 := by
    simpa [hChoice1, edgeTarget] using hEndpoints1.2.symm
  have h3 : (3 : Node) ∈ T := by
    rw [← hPermutation1]
    exact responseRegression_permutation_mem hPermutation 1 h1
  have hEndpoints3 := responseRegression_selectedEndpoints hChoice 3 h3
  have hChoice3 : choice 3 h3 = 4 :=
    responseRegression_edge_from_three _ hEndpoints3.1
  have hPermutation3 : permutation 3 = 8 := by
    simpa [hChoice3, edgeTarget] using hEndpoints3.2.symm
  have h8 : (8 : Node) ∈ T := by
    rw [← hPermutation3]
    exact responseRegression_permutation_mem hPermutation 3 h3
  have hEndpoints8 := responseRegression_selectedEndpoints hChoice 8 h8
  have hGain8 := responseRegression_selectedGain_ne_zero hFamily 8 h8
  have hChoice8 : choice 8 h8 = 5 :=
    responseRegression_nonzeroEdge_from_eight _ hEndpoints8.1 hGain8
  have hPermutation8 : permutation 8 = 9 := by
    simpa [hChoice8, edgeTarget] using hEndpoints8.2.symm
  have h9 : (9 : Node) ∈ T := by
    rw [← hPermutation8]
    exact responseRegression_permutation_mem hPermutation 8 h8
  have hEndpoints9 := responseRegression_selectedEndpoints hChoice 9 h9
  have hChoice9 : choice 9 h9 = 11 :=
    responseRegression_edge_from_nine _ hEndpoints9.1
  have hPermutation9 : permutation 9 = 4 := by
    simpa [hChoice9, edgeTarget] using hEndpoints9.2.symm
  have h4 : (4 : Node) ∈ T := by
    rw [← hPermutation9]
    exact responseRegression_permutation_mem hPermutation 9 h9
  have hEndpoints4 := responseRegression_selectedEndpoints hChoice 4 h4
  have hChoice4 : choice 4 h4 = 12 := by
    rcases responseRegression_edge_from_four _ hEndpoints4.1 with hTwelve | hThirteen
    · exact hTwelve
    · have hPermutation4 : permutation 4 = 7 := by
        simpa [hThirteen, edgeTarget] using hEndpoints4.2.symm
      have h7 : (7 : Node) ∈ T := by
        rw [← hPermutation4]
        exact responseRegression_permutation_mem hPermutation 4 h4
      exact absurd (responseRegression_selectedEndpoints hChoice 7 h7).1
        (responseRegression_noEdgeSource_seven _)
  have hPermutation4 : permutation 4 = 6 := by
    simpa [hChoice4, edgeTarget] using hEndpoints4.2.symm
  have h6 : (6 : Node) ∈ T := by
    rw [← hPermutation4]
    exact responseRegression_permutation_mem hPermutation 4 h4
  have hEndpoints6 := responseRegression_selectedEndpoints hChoice 6 h6
  have hChoice6 : choice 6 h6 = 16 :=
    responseRegression_edge_from_six _ hEndpoints6.1
  have hPermutation6 : permutation 6 = 13 := by
    simpa [hChoice6, edgeTarget] using hEndpoints6.2.symm
  have h13 : (13 : Node) ∈ T := by
    rw [← hPermutation6]
    exact responseRegression_permutation_mem hPermutation 6 h6
  have hEndpoints13 := responseRegression_selectedEndpoints hChoice 13 h13
  have hGain13 := responseRegression_selectedGain_ne_zero hFamily 13 h13
  have hChoice13 : choice 13 h13 = 17 :=
    responseRegression_nonzeroEdge_from_thirteen _ hEndpoints13.1 hGain13
  have hPermutation13 : permutation 13 = 14 := by
    simpa [hChoice13, edgeTarget] using hEndpoints13.2.symm
  have hMainSubset : responseRegressionMainLoopNodes ⊆ T := by
    intro node hNode
    simp only [responseRegressionMainLoopNodes, Finset.mem_insert,
      Finset.mem_singleton] at hNode
    rcases hNode with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h1
    · exact h3
    · exact h8
    · exact h9
    · exact h4
    · exact h6
    · exact h13
    · exact h14
  have hNoExtra : T \ responseRegressionMainLoopNodes = ∅ := by
    by_contra hExtra
    have hExtraNonempty : (T \ responseRegressionMainLoopNodes).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hExtra
    obtain ⟨node, hNode, hMax⟩ := Finset.exists_max_image
      (T \ responseRegressionMainLoopNodes) responseRegressionNodeRank hExtraNonempty
    have hNodeNotMain := (Finset.mem_sdiff.mp hNode).2
    have hPermutationNodeT := responseRegression_permutation_mem hPermutation node
      (Finset.mem_sdiff.mp hNode).1
    have hPermutationNodeNotMain : permutation node ∉ responseRegressionMainLoopNodes := by
      intro hTarget
      simp only [responseRegressionMainLoopNodes, Finset.mem_insert,
        Finset.mem_singleton] at hTarget
      rcases hTarget with hTarget | hTarget | hTarget | hTarget |
        hTarget | hTarget | hTarget | hTarget
      · apply hNodeNotMain
        have hNodeEq := permutation.injective (hTarget.trans hPermutation14.symm)
        simp [hNodeEq, responseRegressionMainLoopNodes]
      · apply hNodeNotMain
        have hNodeEq := permutation.injective (hTarget.trans hPermutation1.symm)
        simp [hNodeEq, responseRegressionMainLoopNodes]
      · apply hNodeNotMain
        have hNodeEq := permutation.injective (hTarget.trans hPermutation3.symm)
        simp [hNodeEq, responseRegressionMainLoopNodes]
      · apply hNodeNotMain
        have hNodeEq := permutation.injective (hTarget.trans hPermutation8.symm)
        simp [hNodeEq, responseRegressionMainLoopNodes]
      · apply hNodeNotMain
        have hNodeEq := permutation.injective (hTarget.trans hPermutation9.symm)
        simp [hNodeEq, responseRegressionMainLoopNodes]
      · apply hNodeNotMain
        have hNodeEq := permutation.injective (hTarget.trans hPermutation4.symm)
        simp [hNodeEq, responseRegressionMainLoopNodes]
      · apply hNodeNotMain
        have hNodeEq := permutation.injective (hTarget.trans hPermutation6.symm)
        simp [hNodeEq, responseRegressionMainLoopNodes]
      · apply hNodeNotMain
        have hNodeEq := permutation.injective (hTarget.trans hPermutation13.symm)
        simp [hNodeEq, responseRegressionMainLoopNodes]
    have hPermutationNode : permutation node ∈
        T \ responseRegressionMainLoopNodes :=
      Finset.mem_sdiff.mpr ⟨hPermutationNodeT, hPermutationNodeNotMain⟩
    have hEndpoints := responseRegression_selectedEndpoints hChoice node
      (Finset.mem_sdiff.mp hNode).1
    have hGain := responseRegression_selectedGain_ne_zero hFamily node
      (Finset.mem_sdiff.mp hNode).1
    have hNotEight : choice node (Finset.mem_sdiff.mp hNode).1 ≠ 8 := by
      intro hEdge
      apply hGain
      rw [hEdge, responseRegression_edgeEightGain]
    have hNotTwenty : choice node (Finset.mem_sdiff.mp hNode).1 ≠ 20 := by
      intro hEdge
      apply hGain
      rw [hEdge, responseRegression_edgeTwentyGain]
    have hNotTwentyThree : choice node (Finset.mem_sdiff.mp hNode).1 ≠ 23 := by
      intro hEdge
      have hNodeEq : node = 14 := by
        simpa [hEdge, edgeSource] using hEndpoints.1.symm
      exact hNodeNotMain (by simp [hNodeEq, responseRegressionMainLoopNodes])
    have hRank := responseRegressionNodeRank_lt
      (choice node (Finset.mem_sdiff.mp hNode).1)
      ⟨hNotEight, hNotTwenty, hNotTwentyThree⟩
    rw [hEndpoints.1, hEndpoints.2] at hRank
    exact (Nat.not_lt_of_ge (hMax (permutation node) hPermutationNode)) hRank
  have hTEqual : T = responseRegressionMainLoopNodes := by
    apply Finset.Subset.antisymm
    · exact Finset.sdiff_eq_empty_iff_subset.mp hNoExtra
    · exact hMainSubset
  have hFixedOutside (node : Node) (hNode : node ∉ responseRegressionMainLoopNodes) :
      permutation node = node := by
    apply Equiv.Perm.notMem_support.mp
    intro hSupport
    apply hNode
    rw [← hTEqual]
    exact (mem_loopFamilies.mp hPermutation) hSupport
  refine ⟨hTEqual, Equiv.ext ?_⟩
  intro node
  fin_cases node
  · simpa [responseRegressionMainLoopPermutation, Equiv.swap_apply_def] using
      hFixedOutside 0 (by decide)
  · simpa [responseRegressionMainLoopPermutation, Equiv.swap_apply_def] using hPermutation1
  · simpa [responseRegressionMainLoopPermutation, Equiv.swap_apply_def] using
      hFixedOutside 2 (by decide)
  · simpa [responseRegressionMainLoopPermutation, Equiv.swap_apply_def] using hPermutation3
  · simpa [responseRegressionMainLoopPermutation, Equiv.swap_apply_def] using hPermutation4
  · simpa [responseRegressionMainLoopPermutation, Equiv.swap_apply_def] using
      hFixedOutside 5 (by decide)
  · simpa [responseRegressionMainLoopPermutation, Equiv.swap_apply_def] using hPermutation6
  · simpa [responseRegressionMainLoopPermutation, Equiv.swap_apply_def] using
      hFixedOutside 7 (by decide)
  · simpa [responseRegressionMainLoopPermutation, Equiv.swap_apply_def] using hPermutation8
  · simpa [responseRegressionMainLoopPermutation, Equiv.swap_apply_def] using hPermutation9
  · simpa [responseRegressionMainLoopPermutation, Equiv.swap_apply_def] using
      hFixedOutside 10 (by decide)
  · simpa [responseRegressionMainLoopPermutation, Equiv.swap_apply_def] using
      hFixedOutside 11 (by decide)
  · simpa [responseRegressionMainLoopPermutation, Equiv.swap_apply_def] using
      hFixedOutside 12 (by decide)
  · simpa [responseRegressionMainLoopPermutation, Equiv.swap_apply_def] using hPermutation13
  · simpa [responseRegressionMainLoopPermutation, Equiv.swap_apply_def] using hPermutation14
  · simpa [responseRegressionMainLoopPermutation, Equiv.swap_apply_def] using
      hFixedOutside 15 (by decide)
  · simpa [responseRegressionMainLoopPermutation, Equiv.swap_apply_def] using
      hFixedOutside 16 (by decide)
  · simpa [responseRegressionMainLoopPermutation, Equiv.swap_apply_def] using
      hFixedOutside 17 (by decide)

/-- The displayed main permutation has exactly one edge-level refinement. -/
lemma responseRegression_mainLoopChoices :
    edgeChoices (signalMultigraph responseRegressionParameters)
        responseRegressionMainLoopNodes responseRegressionMainLoopPermutation =
      {responseRegressionMainLoopChoice} := by
  decide

/-- Every nonempty node set other than the displayed main loop has zero total loop-family
contribution at the positive fixture. -/
private lemma responseRegression_nonMainFamilySum_eq_zero
    {T : Finset Node} (hT : T.Nonempty)
    (hNotMain : T ≠ responseRegressionMainLoopNodes) :
    (∑ permutation ∈ loopFamilies T,
      ∑ choice ∈ edgeChoices (signalMultigraph responseRegressionParameters) T permutation,
        (-1 : ℂ) ^ loopCount T permutation *
          edgeFamilyGain (signalMultigraph responseRegressionParameters) T choice) = 0 := by
  apply Finset.sum_eq_zero
  intro permutation hPermutation
  apply Finset.sum_eq_zero
  intro choice hChoice
  by_cases hFamily :
      edgeFamilyGain (signalMultigraph responseRegressionParameters) T choice = 0
  · simp [hFamily]
  · exact absurd
      (responseRegression_nonzeroFamily_eq_main hT hPermutation hChoice hFamily).1
      hNotMain

/-- The displayed main node set contributes exactly the negative main-loop gain. -/
lemma responseRegression_mainFamilySum :
    (∑ permutation ∈ loopFamilies responseRegressionMainLoopNodes,
      ∑ choice ∈
          edgeChoices (signalMultigraph responseRegressionParameters)
            responseRegressionMainLoopNodes permutation,
        (-1 : ℂ) ^ loopCount responseRegressionMainLoopNodes permutation *
          edgeFamilyGain (signalMultigraph responseRegressionParameters)
            responseRegressionMainLoopNodes choice) = -(3 / 13) := by
  calc
    (∑ permutation ∈ loopFamilies responseRegressionMainLoopNodes,
        ∑ choice ∈
            edgeChoices (signalMultigraph responseRegressionParameters)
              responseRegressionMainLoopNodes permutation,
          (-1 : ℂ) ^ loopCount responseRegressionMainLoopNodes permutation *
            edgeFamilyGain (signalMultigraph responseRegressionParameters)
              responseRegressionMainLoopNodes choice) =
        ∑ choice ∈
            edgeChoices (signalMultigraph responseRegressionParameters)
              responseRegressionMainLoopNodes responseRegressionMainLoopPermutation,
          (-1 : ℂ) ^ loopCount responseRegressionMainLoopNodes
              responseRegressionMainLoopPermutation *
            edgeFamilyGain (signalMultigraph responseRegressionParameters)
              responseRegressionMainLoopNodes choice := by
      apply Finset.sum_eq_single responseRegressionMainLoopPermutation
      · intro permutation hPermutation hNotMain
        apply Finset.sum_eq_zero
        intro choice hChoice
        by_cases hFamily : edgeFamilyGain (signalMultigraph responseRegressionParameters)
            responseRegressionMainLoopNodes choice = 0
        · simp [hFamily]
        · exact absurd
            (responseRegression_nonzeroFamily_eq_main
              (by decide) hPermutation hChoice hFamily).2 hNotMain
      · intro hMissing
        exact (hMissing responseRegression_mainLoopPermutation_mem).elim
    _ = -(3 / 13) := by
      rw [responseRegression_mainLoopChoices]
      simp [responseRegression_mainLoopCount, responseRegression_mainLoopFamilyGain]

/-- Direct edge-choice expansion gives the positive fixture's determinant on every induced node
set. The sole nonzero loop contributes exactly when all of its nodes remain. -/
lemma responseRegression_edgeGraphDetOn (nodes : Finset Node) :
    edgeGraphDetOn (signalMultigraph responseRegressionParameters) nodes =
      if responseRegressionMainLoopNodes ⊆ nodes then 10 / 13 else 1 := by
  let contribution : Finset Node → ℂ := fun T ↦
    ∑ permutation ∈ loopFamilies T,
      ∑ choice ∈ edgeChoices (signalMultigraph responseRegressionParameters) T permutation,
        (-1 : ℂ) ^ loopCount T permutation *
          edgeFamilyGain (signalMultigraph responseRegressionParameters) T choice
  rw [edgeGraphDetOn]
  change (∑ T ∈ nodes.powerset, contribution T) = _
  have hEmptyMem : (∅ : Finset Node) ∈ nodes.powerset := by simp
  have hEmpty : contribution ∅ = 1 := by
    simp [contribution, loopFamilies_empty, edgeChoices, edgeFamilyGain, loopCount]
  rw [← Finset.add_sum_erase nodes.powerset contribution hEmptyMem, hEmpty]
  by_cases hMainSubset : responseRegressionMainLoopNodes ⊆ nodes
  · have hMainMem : responseRegressionMainLoopNodes ∈ nodes.powerset := by
      simpa using hMainSubset
    have hMainNonempty : responseRegressionMainLoopNodes.Nonempty := by decide
    have hMainErase : responseRegressionMainLoopNodes ∈ nodes.powerset.erase ∅ := by
      exact Finset.mem_erase.mpr
        ⟨Finset.nonempty_iff_ne_empty.mp hMainNonempty, hMainMem⟩
    rw [← Finset.add_sum_erase (nodes.powerset.erase ∅) contribution hMainErase]
    have hMain : contribution responseRegressionMainLoopNodes = -(3 / 13) := by
      simpa [contribution] using responseRegression_mainFamilySum
    rw [hMain]
    have hOther :
        ∑ T ∈ (nodes.powerset.erase ∅).erase responseRegressionMainLoopNodes,
          contribution T = 0 := by
      apply Finset.sum_eq_zero
      intro T hT
      have hNotEmpty : T ≠ ∅ := by
        exact (Finset.mem_erase.mp (Finset.mem_erase.mp hT).2).1
      have hNotMain : T ≠ responseRegressionMainLoopNodes :=
        (Finset.mem_erase.mp hT).1
      simpa [contribution] using responseRegression_nonMainFamilySum_eq_zero
        (Finset.nonempty_iff_ne_empty.mpr hNotEmpty) hNotMain
    rw [hOther]
    simp [hMainSubset]
    norm_num
  · have hOther : ∑ T ∈ nodes.powerset.erase ∅, contribution T = 0 := by
      apply Finset.sum_eq_zero
      intro T hT
      have hNotEmpty : T ≠ ∅ := (Finset.mem_erase.mp hT).1
      have hNotMain : T ≠ responseRegressionMainLoopNodes := by
        intro hEqual
        apply hMainSubset
        have hPowerset : T ∈ nodes.powerset := (Finset.mem_erase.mp hT).2
        simpa [hEqual] using hPowerset
      simpa [contribution] using responseRegression_nonMainFamilySum_eq_zero
        (Finset.nonempty_iff_ne_empty.mpr hNotEmpty) hNotMain
    rw [hOther]
    simp [hMainSubset]

/-- Direct loop-family expansion gives edge determinant `10/13` at the positive fixture. -/
lemma responseRegression_edgeGraphDet :
    edgeGraphDet (signalMultigraph responseRegressionParameters) = 10 / 13 := by
  rw [edgeGraphDet]
  rw [responseRegression_edgeGraphDetOn]
  simp
/-!
## C. Direct supported-path numerator expansion
-/
/-- The sixteen retained edges whose gains are nonzero at the positive fixture. -/
def responseRegressionSupportedEdges : Finset Edge :=
  {0, 1, 2, 3, 4, 5, 10, 11, 12, 13, 14, 15, 16, 17, 21, 23}

/-- Fixture edge gain is nonzero exactly on the displayed sixteen labels. -/
lemma responseRegression_edgeGain_ne_zero_iff (edge : Edge) :
    (signalMultigraph responseRegressionParameters).gain edge ≠ 0 ↔
      edge ∈ responseRegressionSupportedEdges := by
  fin_cases edge <;>
    simp [responseRegressionSupportedEdges, signalMultigraph, edgeGain,
      responseRegressionParameters, responseRegressionPropagation,
      Parameters.mainQuarterOneCoefficient, Parameters.mainQuarterTwoCoefficient,
      Parameters.mainQuarterThreeCoefficient, Parameters.mainQuarterFourCoefficient,
      Parameters.rightHalfOneCoefficient, Parameters.rightHalfTwoCoefficient,
      Parameters.leftHalfOneCoefficient, Parameters.leftHalfTwoCoefficient,
      DirectionalCoupler.crossCoefficient, MatchedPropagation.transmissionCoefficient,
      MatchedPropagation.carrierPhaseFactor]

/-- Two nodes are adjacent at the positive fixture when a retained edge between them has nonzero
gain. -/
def ResponseRegressionNonzeroAdjacent (first second : Node) : Prop :=
  ∃ edge ∈ responseRegressionSupportedEdges,
    edgeSource edge = first ∧ edgeTarget edge = second

/-- A node path is supported when it has an edge refinement with nonzero product. -/
def ResponseRegressionPathSupported (path : List Node) : Prop :=
  ∃ edgeList ∈
      refiningEdgeLists (signalMultigraph responseRegressionParameters) path,
    edgeListGain (signalMultigraph responseRegressionParameters) edgeList ≠ 0

/-- A path has a nonzero refinement exactly when each consecutive node pair has a nonzero retained
edge. -/
lemma responseRegression_pathSupported_iff_isChain (path : List Node) :
    ResponseRegressionPathSupported path ↔
      path.IsChain ResponseRegressionNonzeroAdjacent := by
  induction path with
  | nil => simp [ResponseRegressionPathSupported, refiningEdgeLists, edgeListGain]
  | cons first rest ih =>
      cases rest with
      | nil => simp [ResponseRegressionPathSupported, refiningEdgeLists, edgeListGain]
      | cons second tail =>
          constructor
          · rintro ⟨edgeList, hEdgeList, hGain⟩
            rw [refiningEdgeLists] at hEdgeList
            rcases Finset.mem_biUnion.mp hEdgeList with ⟨edge, hEdge, hImage⟩
            rcases Finset.mem_image.mp hImage with ⟨tailList, hTailList, rfl⟩
            have hProduct :
                (signalMultigraph responseRegressionParameters).gain edge ≠ 0 ∧
                  edgeListGain (signalMultigraph responseRegressionParameters) tailList ≠ 0 :=
              mul_ne_zero_iff.mp (by simpa using hGain)
            have hEndpoints :=
              Physlib.SignalFlowGraph.Multigraph.mem_edgesBetween.mp hEdge
            exact List.IsChain.cons_cons
              ⟨edge, (responseRegression_edgeGain_ne_zero_iff edge).mp hProduct.1,
                hEndpoints⟩
              (ih.mp ⟨tailList, hTailList, hProduct.2⟩)
          · intro hChain
            obtain ⟨edge, hSupported, hEndpoints⟩ := hChain.rel
            have hEdge : edge ∈
                (signalMultigraph responseRegressionParameters).edgesBetween first second :=
              Physlib.SignalFlowGraph.Multigraph.mem_edgesBetween.mpr hEndpoints
            have hEdgeGain :
                (signalMultigraph responseRegressionParameters).gain edge ≠ 0 :=
              (responseRegression_edgeGain_ne_zero_iff edge).mpr hSupported
            obtain ⟨tailList, hTailList, hTailGain⟩ := ih.mpr hChain.tail
            refine ⟨edge :: tailList, ?_, ?_⟩
            · rw [refiningEdgeLists]
              exact Finset.mem_biUnion.mpr ⟨edge, hEdge,
                Finset.mem_image.mpr ⟨tailList, hTailList, rfl⟩⟩
            · simpa using mul_ne_zero hEdgeGain hTailGain

/-- The supported successors of source node zero are the two input-coupler outputs. -/
lemma responseRegression_nonzeroAdjacent_zero (next : Node) :
    ResponseRegressionNonzeroAdjacent 0 next ↔ next = 2 ∨ next = 3 := by
  fin_cases next <;> unfold ResponseRegressionNonzeroAdjacent <;> decide

/-- The supported successors of main-feedback node one are nodes two and three. -/
lemma responseRegression_nonzeroAdjacent_one (next : Node) :
    ResponseRegressionNonzeroAdjacent 1 next ↔ next = 2 ∨ next = 3 := by
  fin_cases next <;> unfold ResponseRegressionNonzeroAdjacent <;> decide

/-- Main node three has only supported successor eight. -/
lemma responseRegression_nonzeroAdjacent_three (next : Node) :
    ResponseRegressionNonzeroAdjacent 3 next ↔ next = 8 := by
  fin_cases next <;> unfold ResponseRegressionNonzeroAdjacent <;> decide

/-- The right coupler's supported forward branch goes directly from node eight to node nine. -/
lemma responseRegression_nonzeroAdjacent_eight (next : Node) :
    ResponseRegressionNonzeroAdjacent 8 next ↔ next = 9 := by
  fin_cases next <;> unfold ResponseRegressionNonzeroAdjacent <;> decide

/-- Main node nine has only supported successor four. -/
lemma responseRegression_nonzeroAdjacent_nine (next : Node) :
    ResponseRegressionNonzeroAdjacent 9 next ↔ next = 4 := by
  fin_cases next <;> unfold ResponseRegressionNonzeroAdjacent <;> decide

/-- Output-coupler node four has supported successors six and seven. -/
lemma responseRegression_nonzeroAdjacent_four (next : Node) :
    ResponseRegressionNonzeroAdjacent 4 next ↔ next = 6 ∨ next = 7 := by
  fin_cases next <;> unfold ResponseRegressionNonzeroAdjacent <;> decide

/-- Main node six has only supported successor thirteen. -/
lemma responseRegression_nonzeroAdjacent_six (next : Node) :
    ResponseRegressionNonzeroAdjacent 6 next ↔ next = 13 := by
  fin_cases next <;> unfold ResponseRegressionNonzeroAdjacent <;> decide

/-- The left coupler's supported forward branch goes directly from node thirteen to fourteen. -/
lemma responseRegression_nonzeroAdjacent_thirteen (next : Node) :
    ResponseRegressionNonzeroAdjacent 13 next ↔ next = 14 := by
  fin_cases next <;> unfold ResponseRegressionNonzeroAdjacent <;> decide

/-- Main node fourteen has only the supported feedback successor one. -/
lemma responseRegression_nonzeroAdjacent_fourteen (next : Node) :
    ResponseRegressionNonzeroAdjacent 14 next ↔ next = 1 := by
  fin_cases next <;> unfold ResponseRegressionNonzeroAdjacent <;> decide

/-- No supported edge leaves the through-output node. -/
lemma responseRegression_not_nonzeroAdjacent_two (next : Node) :
    ¬ResponseRegressionNonzeroAdjacent 2 next := by
  fin_cases next <;> unfold ResponseRegressionNonzeroAdjacent <;> decide

/-- No supported edge leaves the drop-output node. -/
lemma responseRegression_not_nonzeroAdjacent_seven (next : Node) :
    ¬ResponseRegressionNonzeroAdjacent 7 next := by
  fin_cases next <;> unfold ResponseRegressionNonzeroAdjacent <;> decide

/-- A supported path that reaches the through node ends there. -/
private lemma responseRegression_chain_from_two_eq_singleton {rest : List Node}
    (hChain : (2 :: rest).IsChain ResponseRegressionNonzeroAdjacent) : rest = [] := by
  cases rest with
  | nil => rfl
  | cons next tail =>
      exact absurd hChain.rel (responseRegression_not_nonzeroAdjacent_two next)

/-- A supported path that reaches the drop node ends there. -/
private lemma responseRegression_chain_from_seven_eq_singleton {rest : List Node}
    (hChain : (7 :: rest).IsChain ResponseRegressionNonzeroAdjacent) : rest = [] := by
  cases rest with
  | nil => rfl
  | cons next tail =>
      exact absurd hChain.rel (responseRegression_not_nonzeroAdjacent_seven next)

/-- A simple supported path launched into the ring reaches exactly one of the two bus outputs. -/
private lemma responseRegression_ringPath_cases {rest : List Node} {output : Node}
    (hOutput : output = 2 ∨ output = 7)
    (hNodup : (0 :: 3 :: rest).Nodup)
    (hLast : (0 :: 3 :: rest).getLast? = some output)
    (hChain : (0 :: 3 :: rest).IsChain ResponseRegressionNonzeroAdjacent) :
    rest = [8, 9, 4, 7] ∨ rest = [8, 9, 4, 6, 13, 14, 1, 2] := by
  rcases rest with _ | ⟨third, rest⟩
  · rcases hOutput with rfl | rfl <;> simp at hLast
  have hThird := (responseRegression_nonzeroAdjacent_three third).mp hChain.tail.rel
  subst third
  rcases rest with _ | ⟨fourth, rest⟩
  · rcases hOutput with rfl | rfl <;> simp at hLast
  have hFourth := (responseRegression_nonzeroAdjacent_eight fourth).mp
    hChain.tail.tail.rel
  subst fourth
  rcases rest with _ | ⟨fifth, rest⟩
  · rcases hOutput with rfl | rfl <;> simp at hLast
  have hFifth := (responseRegression_nonzeroAdjacent_nine fifth).mp
    hChain.tail.tail.tail.rel
  subst fifth
  rcases rest with _ | ⟨sixth, rest⟩
  · rcases hOutput with rfl | rfl <;> simp at hLast
  rcases (responseRegression_nonzeroAdjacent_four sixth).mp
      hChain.tail.tail.tail.tail.rel with rfl | rfl
  · rcases rest with _ | ⟨seventh, rest⟩
    · rcases hOutput with rfl | rfl <;> simp at hLast
    have hSeventh := (responseRegression_nonzeroAdjacent_six seventh).mp
      hChain.tail.tail.tail.tail.tail.rel
    subst seventh
    rcases rest with _ | ⟨eighth, rest⟩
    · rcases hOutput with rfl | rfl <;> simp at hLast
    have hEighth := (responseRegression_nonzeroAdjacent_thirteen eighth).mp
      hChain.tail.tail.tail.tail.tail.tail.rel
    subst eighth
    rcases rest with _ | ⟨ninth, rest⟩
    · rcases hOutput with rfl | rfl <;> simp at hLast
    have hNinth := (responseRegression_nonzeroAdjacent_fourteen ninth).mp
      hChain.tail.tail.tail.tail.tail.tail.tail.rel
    subst ninth
    rcases rest with _ | ⟨tenth, rest⟩
    · rcases hOutput with rfl | rfl <;> simp at hLast
    rcases (responseRegression_nonzeroAdjacent_one tenth).mp
        hChain.tail.tail.tail.tail.tail.tail.tail.tail.rel with rfl | rfl
    · rw [responseRegression_chain_from_two_eq_singleton
          hChain.tail.tail.tail.tail.tail.tail.tail.tail.tail]
      exact Or.inr rfl
    · simp at hNodup
  · rw [responseRegression_chain_from_seven_eq_singleton
        hChain.tail.tail.tail.tail.tail]
    exact Or.inl rfl

set_option maxRecDepth 2000 in
/-- A supported simple source-to-through path is direct or makes one main-ring turn. -/
lemma responseRegression_supportedThroughPath_cases {path : List Node}
    (hPath : path ∈ forwardPaths (0 : Node) 2)
    (hSupported : ResponseRegressionPathSupported path) :
    path = topologyThroughDirect ∨ path = topologyThroughMainDirect := by
  obtain ⟨hNodup, hHead, hLast⟩ := mem_forwardPaths_iff.mp hPath
  have hChain := (responseRegression_pathSupported_iff_isChain path).mp hSupported
  rcases path with _ | ⟨first, rest⟩
  · simp at hHead
  have hFirst : first = 0 := by simpa using hHead
  subst first
  rcases rest with _ | ⟨second, rest⟩
  · simp at hLast
  rcases (responseRegression_nonzeroAdjacent_zero second).mp hChain.rel with rfl | rfl
  · rw [responseRegression_chain_from_two_eq_singleton hChain.tail]
    exact Or.inl rfl
  · rcases responseRegression_ringPath_cases (Or.inl rfl) hNodup hLast hChain with
      hDrop | hMain
    · subst rest
      simp at hLast
    · subst rest
      exact Or.inr rfl

set_option maxRecDepth 2000 in
/-- The direct-drop path is the only supported simple source-to-drop path. -/
lemma responseRegression_supportedDropPath_eq {path : List Node}
    (hPath : path ∈ forwardPaths (0 : Node) 7)
    (hSupported : ResponseRegressionPathSupported path) :
    path = topologyDropDirect := by
  obtain ⟨hNodup, hHead, hLast⟩ := mem_forwardPaths_iff.mp hPath
  have hChain := (responseRegression_pathSupported_iff_isChain path).mp hSupported
  rcases path with _ | ⟨first, rest⟩
  · simp at hHead
  have hFirst : first = 0 := by simpa using hHead
  subst first
  rcases rest with _ | ⟨second, rest⟩
  · simp at hLast
  rcases (responseRegression_nonzeroAdjacent_zero second).mp hChain.rel with rfl | rfl
  · rw [responseRegression_chain_from_two_eq_singleton hChain.tail] at hLast
    simp at hLast
  · rcases responseRegression_ringPath_cases (Or.inr rfl) hNodup hLast hChain with
      hDrop | hMain
    · subst rest
      rfl
    · subst rest
      simp at hLast

/-- Supported simple source-to-through paths at the positive fixture. -/
noncomputable def responseRegressionSupportedThroughPaths : Finset (List Node) := by
  classical
  exact (forwardPaths 0 2).filter ResponseRegressionPathSupported

/-- Supported simple source-to-drop paths at the positive fixture. -/
noncomputable def responseRegressionSupportedDropPaths : Finset (List Node) := by
  classical
  exact (forwardPaths 0 7).filter ResponseRegressionPathSupported

set_option maxRecDepth 2000 in
/-- Exactly two source-to-through paths have a nonzero edge refinement. -/
lemma responseRegression_supportedThroughPaths :
    responseRegressionSupportedThroughPaths =
      {topologyThroughDirect, topologyThroughMainDirect} := by
  classical
  ext path
  simp only [responseRegressionSupportedThroughPaths, Finset.mem_filter]
  constructor
  · rintro ⟨hPath, hSupported⟩
    rcases responseRegression_supportedThroughPath_cases hPath hSupported with rfl | rfl <;>
      simp
  · intro hPath
    simp only [Finset.mem_insert, Finset.mem_singleton] at hPath
    rcases hPath with rfl | rfl
    all_goals
      constructor
      · apply mem_forwardPaths_iff.mpr
        decide
      · rw [responseRegression_pathSupported_iff_isChain]
        unfold ResponseRegressionNonzeroAdjacent
        decide

set_option maxRecDepth 2000 in
/-- Exactly one source-to-drop path has a nonzero edge refinement. -/
lemma responseRegression_supportedDropPaths :
    responseRegressionSupportedDropPaths = {topologyDropDirect} := by
  classical
  ext path
  simp only [responseRegressionSupportedDropPaths, Finset.mem_filter]
  constructor
  · rintro ⟨hPath, hSupported⟩
    rw [responseRegression_supportedDropPath_eq hPath hSupported]
    simp
  · intro hPath
    simp only [Finset.mem_singleton] at hPath
    subst path
    constructor
    · apply mem_forwardPaths_iff.mpr
      decide
    · rw [responseRegression_pathSupported_iff_isChain]
      unfold ResponseRegressionNonzeroAdjacent
      decide

set_option maxRecDepth 2000 in
/-- Unsupported through-node paths contribute zero to the edge-level Mason numerator. -/
lemma responseRegression_throughNumerator_eq_supportedSum :
    edgeMasonNumerator (signalMultigraph responseRegressionParameters) 0 2 =
      ∑ path ∈ responseRegressionSupportedThroughPaths,
        ∑ edgeList ∈ refiningEdgeLists
            (signalMultigraph responseRegressionParameters) path,
          edgeListGain (signalMultigraph responseRegressionParameters) edgeList *
            edgeGraphDetOn (signalMultigraph responseRegressionParameters)
              (Finset.univ \ path.toFinset) := by
  classical
  rw [edgeMasonNumerator]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro path hPath hUnsupported
  apply Finset.sum_eq_zero
  intro edgeList hRefinement
  have hGain :
      edgeListGain (signalMultigraph responseRegressionParameters) edgeList = 0 := by
    by_contra hNonzero
    exact hUnsupported (Finset.mem_filter.mpr
      ⟨hPath, edgeList, hRefinement, hNonzero⟩)
  simp [hGain]

set_option maxRecDepth 2000 in
/-- Unsupported drop-node paths contribute zero to the edge-level Mason numerator. -/
lemma responseRegression_dropNumerator_eq_supportedSum :
    edgeMasonNumerator (signalMultigraph responseRegressionParameters) 0 7 =
      ∑ path ∈ responseRegressionSupportedDropPaths,
        ∑ edgeList ∈ refiningEdgeLists
            (signalMultigraph responseRegressionParameters) path,
          edgeListGain (signalMultigraph responseRegressionParameters) edgeList *
            edgeGraphDetOn (signalMultigraph responseRegressionParameters)
              (Finset.univ \ path.toFinset) := by
  classical
  rw [edgeMasonNumerator]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro path hPath hUnsupported
  apply Finset.sum_eq_zero
  intro edgeList hRefinement
  have hGain :
      edgeListGain (signalMultigraph responseRegressionParameters) edgeList = 0 := by
    by_contra hNonzero
    exact hUnsupported (Finset.mem_filter.mpr
      ⟨hPath, edgeList, hRefinement, hNonzero⟩)
  simp [hGain]

/-- The direct through-node path refines only to edge zero. -/
lemma responseRegression_refiningEdges_throughDirect :
    refiningEdgeLists (signalMultigraph responseRegressionParameters)
      topologyThroughDirect = {[0]} :=
  (topology_path_refinements responseRegressionParameters).1

/-- The one-turn through-node path has the displayed nine-edge refinement. -/
lemma responseRegression_refiningEdges_throughMain :
    refiningEdgeLists (signalMultigraph responseRegressionParameters)
      topologyThroughMainDirect = {[1, 4, 5, 11, 12, 16, 17, 23, 3]} :=
  (topology_path_refinements responseRegressionParameters).2.1

/-- The direct drop-node path has the displayed five-edge refinement. -/
lemma responseRegression_refiningEdges_dropDirect :
    refiningEdgeLists (signalMultigraph responseRegressionParameters)
      topologyDropDirect = {[1, 4, 5, 11, 13]} :=
  (topology_drop_path_refinements responseRegressionParameters).1

/-- The direct through-edge refinement has gain `3/5`. -/
lemma responseRegression_edgeListGain_throughDirect :
    edgeListGain (signalMultigraph responseRegressionParameters) [0] = 3 / 5 := by
  norm_num [edgeListGain, signalMultigraph, edgeGain, responseRegressionParameters]

/-- The one-turn through-edge refinement has gain `-16/65`. -/
lemma responseRegression_edgeListGain_throughMain :
    edgeListGain (signalMultigraph responseRegressionParameters)
      [1, 4, 5, 11, 12, 16, 17, 23, 3] = -(16 / 65) := by
  simp [edgeListGain, signalMultigraph, edgeGain, responseRegressionParameters,
    responseRegressionPropagation, Parameters.mainQuarterOneCoefficient,
    Parameters.mainQuarterTwoCoefficient, Parameters.mainQuarterThreeCoefficient,
    Parameters.mainQuarterFourCoefficient, DirectionalCoupler.crossCoefficient,
    MatchedPropagation.transmissionCoefficient, MatchedPropagation.carrierPhaseFactor]
  ring_nf
  rw [pow_two, Complex.I_mul_I]
  norm_num

/-- The direct drop-edge refinement has gain `-48/65`. -/
lemma responseRegression_edgeListGain_dropDirect :
    edgeListGain (signalMultigraph responseRegressionParameters) [1, 4, 5, 11, 13] =
      -(48 / 65) := by
  simp [edgeListGain, signalMultigraph, edgeGain, responseRegressionParameters,
    responseRegressionPropagation, Parameters.mainQuarterOneCoefficient,
    Parameters.mainQuarterTwoCoefficient, DirectionalCoupler.crossCoefficient,
    MatchedPropagation.transmissionCoefficient, MatchedPropagation.carrierPhaseFactor]
  ring_nf
  rw [pow_two, Complex.I_mul_I]
  norm_num

/-- Removing the direct through path leaves the full main-loop cofactor. -/
lemma responseRegression_throughDirectCofactor :
    edgeGraphDetOn (signalMultigraph responseRegressionParameters)
      (Finset.univ \ topologyThroughDirect.toFinset) = 10 / 13 := by
  rw [responseRegression_edgeGraphDetOn]
  rw [if_pos (by decide)]

/-- Removing the one-turn path breaks the sole nonzero loop. -/
lemma responseRegression_throughMainCofactor :
    edgeGraphDetOn (signalMultigraph responseRegressionParameters)
      (Finset.univ \ topologyThroughMainDirect.toFinset) = 1 := by
  rw [responseRegression_edgeGraphDetOn]
  rw [if_neg (by decide)]

/-- Removing the direct drop path breaks the sole nonzero loop. -/
lemma responseRegression_dropDirectCofactor :
    edgeGraphDetOn (signalMultigraph responseRegressionParameters)
      (Finset.univ \ topologyDropDirect.toFinset) = 1 := by
  rw [responseRegression_edgeGraphDetOn]
  rw [if_neg (by decide)]

/-- Direct path/refinement/cofactor expansion gives through numerator `14/65`. -/
lemma responseRegression_edgeMasonNumerator_through :
    edgeMasonNumerator (signalMultigraph responseRegressionParameters) 0 2 = 14 / 65 := by
  rw [responseRegression_throughNumerator_eq_supportedSum,
    responseRegression_supportedThroughPaths]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton,
    responseRegression_refiningEdges_throughDirect,
    responseRegression_refiningEdges_throughMain]
  simp only [Finset.sum_singleton]
  rw [responseRegression_edgeListGain_throughDirect,
    responseRegression_edgeListGain_throughMain,
    responseRegression_throughDirectCofactor,
    responseRegression_throughMainCofactor]
  norm_num

/-- Direct path/refinement/cofactor expansion gives drop numerator `-48/65`. -/
lemma responseRegression_edgeMasonNumerator_drop :
    edgeMasonNumerator (signalMultigraph responseRegressionParameters) 0 7 =
      -(48 / 65) := by
  rw [responseRegression_dropNumerator_eq_supportedSum,
    responseRegression_supportedDropPaths, Finset.sum_singleton,
    responseRegression_refiningEdges_dropDirect, Finset.sum_singleton,
    responseRegression_edgeListGain_dropDirect,
    responseRegression_dropDirectCofactor]
  norm_num
/-!
## D. Hand-expanded matrix and N5 anchors
-/
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
      Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals
    rw [show Complex.I ^ 2 = (-1 : ℂ) by
      rw [pow_two, Complex.I_mul_I]]
  all_goals ring

/-- The positive vector solves the retained graph directly from the raw matrix equation. -/
lemma responseRegression_isNodeSolution :
    IsNodeSolution (signalFlowGraph responseRegressionParameters) (signalInput 1)
      responseRegressionState := by
  rw [IsNodeSolution, signalFlowGraph_eq_coefficientMatrix]
  exact responseRegression_rawNodeEquation

/-- The hand-expanded through coordinate is `7/25`. -/
lemma responseRegression_through : responseRegressionState 2 = 7 / 25 := by
  simp [responseRegressionState]

/-- The hand-expanded drop coordinate is `-24/25`. -/
lemma responseRegression_drop : responseRegressionState 7 = -(24 / 25) := by
  simp [responseRegressionState]

/-- Independent edge-family expansion gives graph determinant `10/13`. -/
lemma responseRegression_graphDet :
    graphDet (coefficientMatrix responseRegressionParameters) = 10 / 13 := by
  rw [graphDet_eq_det, coefficientMatrix, ← edgeGraphDet_eq_det]
  exact responseRegression_edgeGraphDet

/-- The positive fixture's directed graph is invertible. -/
lemma responseRegression_graphDet_ne_zero :
    graphDet (coefficientMatrix responseRegressionParameters) ≠ 0 := by
  rw [responseRegression_graphDet]
  norm_num

/-- The displayed positive state is the unique solution of the unit-input node equation. -/
lemma responseRegression_nodeSolution_unique (state : Node → ℂ)
    (hState : IsNodeSolution (coefficientMatrix responseRegressionParameters)
      (Pi.single (0 : Node) 1) state) :
    state = responseRegressionState := by
  have hUnit : IsUnit
      (systemMatrix (coefficientMatrix responseRegressionParameters)).det := by
    rw [← graphDet_eq_det]
    exact isUnit_iff_ne_zero.mpr responseRegression_graphDet_ne_zero
  have hAnchor : IsNodeSolution (coefficientMatrix responseRegressionParameters)
      (Pi.single (0 : Node) 1) responseRegressionState := by
    simpa only [signalFlowGraph_eq_coefficientMatrix, signalInput_one_eq_single] using
      responseRegression_isNodeSolution
  exact (eq_nodeSolution hUnit hState).trans (eq_nodeSolution hUnit hAnchor).symm

/-- The hand-expanded unique solution gives terminated through transfer `7/25`. -/
lemma responseRegression_throughTerminated :
    (throughTerminatedMultigraph responseRegressionParameters).transfer = 7 / 25 := by
  have hUnit : IsUnit
      (systemMatrix (coefficientMatrix responseRegressionParameters)).det := by
    rw [← graphDet_eq_det]
    exact isUnit_iff_ne_zero.mpr responseRegression_graphDet_ne_zero
  have hState : IsNodeSolution (coefficientMatrix responseRegressionParameters)
      (Pi.single (0 : Node) 1) responseRegressionState := by
    simpa only [signalFlowGraph_eq_coefficientMatrix, signalInput_one_eq_single] using
      responseRegression_isNodeSolution
  exact (TerminatedMultigraph.transfer_eq_of_isNodeSolution
    (throughTerminatedMultigraph responseRegressionParameters) hUnit hState).trans
      responseRegression_through

/-- The hand-expanded unique solution gives terminated drop transfer `-24/25`. -/
lemma responseRegression_dropTerminated :
    (dropTerminatedMultigraph responseRegressionParameters).transfer = -(24 / 25) := by
  have hUnit : IsUnit
      (systemMatrix (coefficientMatrix responseRegressionParameters)).det := by
    rw [← graphDet_eq_det]
    exact isUnit_iff_ne_zero.mpr responseRegression_graphDet_ne_zero
  have hState : IsNodeSolution (coefficientMatrix responseRegressionParameters)
      (Pi.single (0 : Node) 1) responseRegressionState := by
    simpa only [signalFlowGraph_eq_coefficientMatrix, signalInput_one_eq_single] using
      responseRegression_isNodeSolution
  exact (TerminatedMultigraph.transfer_eq_of_isNodeSolution
    (dropTerminatedMultigraph responseRegressionParameters) hUnit hState).trans
      responseRegression_drop

/-- The actual N7 equations have a raw N5 behavior output with the two anchored values. -/
lemma responseRegression_rawNetlistBehavior :
    ∃ output : ModeAmplitude (netlist responseRegressionParameters).ExternalOutgoing,
      (inputAmplitude responseRegressionParameters 1, output) ∈
          (netlist responseRegressionParameters).behavior ∧
        output (Outgoing.mk (throughChannel responseRegressionParameters)) = 7 / 25 ∧
        output (Outgoing.mk (dropChannel responseRegressionParameters)) = -(24 / 25) := by
  rcases (isNodeSolution_iff_exists_netlistRealization responseRegressionParameters 1
    responseRegressionState).mp responseRegression_isNodeSolution with
    ⟨incident, outgoing, hScattering, hAssembly, hProjection⟩
  let output := (netlist responseRegressionParameters).outputReadout.toLinearMap outgoing
  refine ⟨output, ?_, ?_, ?_⟩
  · rw [(netlist responseRegressionParameters).mem_behavior_iff_equations]
    refine ⟨incident, outgoing, hScattering, ?_, rfl⟩
    simpa only [PortConnectionFamily.incidentAssembly] using hAssembly
  · change ((netlist responseRegressionParameters).outputReadout.toLinearMap outgoing)
      (Outgoing.mk (throughChannel responseRegressionParameters)) = 7 / 25
    rw [outputReadout_apply_through, ← responseRegression_through, ← hProjection]
    rfl
  · change ((netlist responseRegressionParameters).outputReadout.toLinearMap outgoing)
      (Outgoing.mk (dropChannel responseRegressionParameters)) = -(24 / 25)
    rw [outputReadout_apply_drop, ← responseRegression_drop, ← hProjection]
    rfl

/-- The fixture's actual N5 through entry is `7/25` whenever its explicit solve gate holds. -/
lemma responseRegression_n5Through (hWellPosed :
    (netlist responseRegressionParameters).IsWellPosed) :
    (netlist responseRegressionParameters).responseTransform hWellPosed
        (Outgoing.mk (throughChannel responseRegressionParameters))
        (Incident.mk (inputChannel responseRegressionParameters)) = 7 / 25 := by
  rw [← throughTransfer_eq_responseTransform responseRegressionParameters hWellPosed
    responseRegression_graphDet_ne_zero]
  exact responseRegression_throughTerminated

/-- The fixture's actual N5 drop entry is `-24/25` whenever its explicit solve gate holds. -/
lemma responseRegression_n5Drop (hWellPosed :
    (netlist responseRegressionParameters).IsWellPosed) :
    (netlist responseRegressionParameters).responseTransform hWellPosed
        (Outgoing.mk (dropChannel responseRegressionParameters))
        (Incident.mk (inputChannel responseRegressionParameters)) = -(24 / 25) := by
  rw [← dropTransfer_eq_responseTransform responseRegressionParameters hWellPosed
    responseRegression_graphDet_ne_zero]
  exact responseRegression_dropTerminated

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
/-!
## E. Singular determinant fixture
-/
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
