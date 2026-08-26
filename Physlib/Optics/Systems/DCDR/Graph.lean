/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Mathematics.SignalFlowGraph.Terminated
public import Physlib.Optics.Systems.DCDR.Netlist

/-!
# Double-coupler double-ring signal-flow graph

## i. Overview

This file records the published FMICS'15 DCDR graph as an edge-indexed
`TerminatedMultigraph` with eight nodes and eleven branches. Its terminal and transfer
conventions are defined in `Physlib/Mathematics/SignalFlowGraph/Terminated.lean:227-241`.
The scalar coefficient matrix is the parallel-edge sum from
`Physlib/Mathematics/SignalFlowGraph/Extraction.lean:175-183`, named through
`ofCoefficientMatrix` from the same file's lines 95-97.

## ii. Key results

- `DCDR.signalMultigraph`: the edge-indexed eight-node, eleven-branch forward graph.
- `DCDR.signalFlowGraph`: its coefficient-matrix signal-flow graph.
- `DCDR.edgeGain_eq_n7ScatteringEntry`: every gain is an assembled N7 entry.
- `DCDR.coefficientMatrix_eq_displayed`: the branch sum gives the displayed matrix.

## iii. Table of contents

- A. The edge-indexed eight-node signal-flow graph

## iv. References

The complete N7 netlist is bidirectional, while this graph records only the forward boundary
coordinates. No claim identifies this matrix with the complete `C * S` feedback graph.

U. Siddique, S. M. Beillahi, and S. Tahar, "On the Formal Analysis of Photonic Signal
Processing Systems", FMICS 2015, LNCS 9128, Definition 8 and Theorem 3 (p. 173).
-/

@[expose] public section

namespace Optics

noncomputable section

namespace DCDR

/-!

## A. The edge-indexed eight-node signal-flow graph

-/

/-- The eight forward DCDR boundary signals, indexed as source nodes one through eight. -/
abbrev Node := Fin 8

/-- The forward graph has exactly eight named boundary coordinates. -/
lemma node_card : Fintype.card Node = 8 := by decide

/-- The eleven source branches, indexed in the order of FMICS'15 Definition 8. -/
abbrev Edge := Fin 11

/-- The source node of each branch in the published eleven-branch order. -/
def edgeSource : Edge → Node := ![0, 2, 5, 0, 3, 4, 5, 6, 1, 1, 4]

/-- The target node of each branch in the published eleven-branch order. -/
def edgeTarget : Edge → Node := ![2, 5, 7, 3, 4, 7, 6, 1, 2, 3, 6]

/-- The coherent N7 field gains in the published eleven-branch order. -/
def edgeGain (p : Parameters) : Edge → ℂ :=
  ![p.firstCoupler.throughAmplitude,
    p.upperCoefficient,
    p.secondCoupler.throughAmplitude,
    DirectionalCoupler.crossCoefficient p.firstCoupler,
    p.lowerCoefficient,
    DirectionalCoupler.crossCoefficient p.secondCoupler,
    DirectionalCoupler.crossCoefficient p.secondCoupler,
    p.feedbackCoefficient,
    DirectionalCoupler.crossCoefficient p.firstCoupler,
    p.firstCoupler.throughAmplitude,
    p.secondCoupler.throughAmplitude]

/-- The physical N7 incident channel supplying each retained graph edge. -/
def edgeN7InputChannel (p : Parameters) : Edge → (netlist p).Channel :=
  ![(netlist p).components.componentChannelEmbedding Component.firstCoupler
      ⟨DirectionalCoupler.Port.leftFirst, ()⟩,
    (netlist p).components.componentChannelEmbedding Component.upperPath
      ⟨MatchedPropagation.Port.left, ()⟩,
    (netlist p).components.componentChannelEmbedding Component.secondCoupler
      ⟨DirectionalCoupler.Port.leftFirst, ()⟩,
    (netlist p).components.componentChannelEmbedding Component.firstCoupler
      ⟨DirectionalCoupler.Port.leftFirst, ()⟩,
    (netlist p).components.componentChannelEmbedding Component.lowerPath
      ⟨MatchedPropagation.Port.left, ()⟩,
    (netlist p).components.componentChannelEmbedding Component.secondCoupler
      ⟨DirectionalCoupler.Port.leftSecond, ()⟩,
    (netlist p).components.componentChannelEmbedding Component.secondCoupler
      ⟨DirectionalCoupler.Port.leftFirst, ()⟩,
    (netlist p).components.componentChannelEmbedding Component.feedbackPath
      ⟨MatchedPropagation.Port.left, ()⟩,
    (netlist p).components.componentChannelEmbedding Component.firstCoupler
      ⟨DirectionalCoupler.Port.leftSecond, ()⟩,
    (netlist p).components.componentChannelEmbedding Component.firstCoupler
      ⟨DirectionalCoupler.Port.leftSecond, ()⟩,
    (netlist p).components.componentChannelEmbedding Component.secondCoupler
      ⟨DirectionalCoupler.Port.leftSecond, ()⟩]

/-- The physical N7 outgoing channel receiving each retained graph edge. -/
def edgeN7OutputChannel (p : Parameters) : Edge → (netlist p).Channel :=
  ![(netlist p).components.componentChannelEmbedding Component.firstCoupler
      ⟨DirectionalCoupler.Port.rightFirst, ()⟩,
    (netlist p).components.componentChannelEmbedding Component.upperPath
      ⟨MatchedPropagation.Port.right, ()⟩,
    (netlist p).components.componentChannelEmbedding Component.secondCoupler
      ⟨DirectionalCoupler.Port.rightFirst, ()⟩,
    (netlist p).components.componentChannelEmbedding Component.firstCoupler
      ⟨DirectionalCoupler.Port.rightSecond, ()⟩,
    (netlist p).components.componentChannelEmbedding Component.lowerPath
      ⟨MatchedPropagation.Port.right, ()⟩,
    (netlist p).components.componentChannelEmbedding Component.secondCoupler
      ⟨DirectionalCoupler.Port.rightFirst, ()⟩,
    (netlist p).components.componentChannelEmbedding Component.secondCoupler
      ⟨DirectionalCoupler.Port.rightSecond, ()⟩,
    (netlist p).components.componentChannelEmbedding Component.feedbackPath
      ⟨MatchedPropagation.Port.right, ()⟩,
    (netlist p).components.componentChannelEmbedding Component.firstCoupler
      ⟨DirectionalCoupler.Port.rightFirst, ()⟩,
    (netlist p).components.componentChannelEmbedding Component.firstCoupler
      ⟨DirectionalCoupler.Port.rightSecond, ()⟩,
    (netlist p).components.componentChannelEmbedding Component.secondCoupler
      ⟨DirectionalCoupler.Port.rightSecond, ()⟩]

/-- The four forward entries of an owned N7 directional-coupler scattering matrix. -/
private lemma directionalCoupler_forwardScatteringEntries
    (q : DirectionalCoupler.Parameters) :
    (DirectionalCoupler.physicalScattering q Unit).toModeTransform
          ⟨DirectionalCoupler.Port.rightFirst, ()⟩
          ⟨DirectionalCoupler.Port.leftFirst, ()⟩ = q.throughAmplitude ∧
      (DirectionalCoupler.physicalScattering q Unit).toModeTransform
          ⟨DirectionalCoupler.Port.rightSecond, ()⟩
          ⟨DirectionalCoupler.Port.leftFirst, ()⟩ =
        DirectionalCoupler.crossCoefficient q ∧
      (DirectionalCoupler.physicalScattering q Unit).toModeTransform
          ⟨DirectionalCoupler.Port.rightFirst, ()⟩
          ⟨DirectionalCoupler.Port.leftSecond, ()⟩ =
        DirectionalCoupler.crossCoefficient q ∧
      (DirectionalCoupler.physicalScattering q Unit).toModeTransform
          ⟨DirectionalCoupler.Port.rightSecond, ()⟩
          ⟨DirectionalCoupler.Port.leftSecond, ()⟩ = q.throughAmplitude := by
  simp [DirectionalCoupler.physicalScattering,
    ScatteringMatrix.toModeTransform_reindex, ModeTransform.reindex_apply,
    DirectionalCoupler.scattering, ReflectionlessTwoPort.scattering,
    DirectionalCoupler.mixing, DirectionalCoupler.portFamily,
    DirectionalCoupler.channelEquiv]

/-- The forward entry of an owned N7 matched-propagation scattering matrix. -/
private lemma matchedPropagation_forwardScatteringEntry
    (q : MatchedPropagation.Parameters) :
    (MatchedPropagation.physicalScattering q Unit).toModeTransform
        ⟨MatchedPropagation.Port.right, ()⟩
        ⟨MatchedPropagation.Port.left, ()⟩ =
      MatchedPropagation.transmissionCoefficient q := by
  simp [MatchedPropagation.physicalScattering,
    ScatteringMatrix.toModeTransform_reindex, ModeTransform.reindex_apply,
    MatchedPropagation.scattering, ReflectionlessTwoPort.scattering,
    MatchedPropagation.transmission, MatchedPropagation.portFamily,
    MatchedPropagation.channelEquiv]

/-- Every retained edge gain is the corresponding entry of the assembled N7 component law. -/
lemma edgeGain_eq_n7ScatteringEntry (p : Parameters) (edge : Edge) :
    edgeGain p edge =
      (netlist p).scatteringTransform
        (Outgoing.mk (edgeN7OutputChannel p edge))
        (Incident.mk (edgeN7InputChannel p edge)) := by
  -- The dependent local-channel types require one short check for each audited edge label.
  fin_cases edge
  · simp [edgeGain, edgeN7InputChannel, edgeN7OutputChannel]
    symm
    exact ((netlist p).scatteringTransform_entry_same Component.firstCoupler
      ⟨DirectionalCoupler.Port.rightFirst, ()⟩
      ⟨DirectionalCoupler.Port.leftFirst, ()⟩).trans (by
        change (DirectionalCoupler.physicalScattering p.firstCoupler Unit).toModeTransform
          ⟨DirectionalCoupler.Port.rightFirst, ()⟩
          ⟨DirectionalCoupler.Port.leftFirst, ()⟩ = p.firstCoupler.throughAmplitude
        exact (directionalCoupler_forwardScatteringEntries p.firstCoupler).1)
  · simp [edgeGain, edgeN7InputChannel, edgeN7OutputChannel]
    symm
    exact ((netlist p).scatteringTransform_entry_same Component.upperPath
      ⟨MatchedPropagation.Port.right, ()⟩ ⟨MatchedPropagation.Port.left, ()⟩).trans (by
        change (MatchedPropagation.physicalScattering p.upperPath Unit).toModeTransform
          ⟨MatchedPropagation.Port.right, ()⟩ ⟨MatchedPropagation.Port.left, ()⟩ =
            MatchedPropagation.transmissionCoefficient p.upperPath
        exact matchedPropagation_forwardScatteringEntry p.upperPath)
  · simp [edgeGain, edgeN7InputChannel, edgeN7OutputChannel]
    symm
    exact ((netlist p).scatteringTransform_entry_same Component.secondCoupler
      ⟨DirectionalCoupler.Port.rightFirst, ()⟩
      ⟨DirectionalCoupler.Port.leftFirst, ()⟩).trans (by
        change (DirectionalCoupler.physicalScattering p.secondCoupler Unit).toModeTransform
          ⟨DirectionalCoupler.Port.rightFirst, ()⟩
          ⟨DirectionalCoupler.Port.leftFirst, ()⟩ = p.secondCoupler.throughAmplitude
        exact (directionalCoupler_forwardScatteringEntries p.secondCoupler).1)
  · simp [edgeGain, edgeN7InputChannel, edgeN7OutputChannel]
    symm
    exact ((netlist p).scatteringTransform_entry_same Component.firstCoupler
      ⟨DirectionalCoupler.Port.rightSecond, ()⟩
      ⟨DirectionalCoupler.Port.leftFirst, ()⟩).trans (by
        change (DirectionalCoupler.physicalScattering p.firstCoupler Unit).toModeTransform
          ⟨DirectionalCoupler.Port.rightSecond, ()⟩
          ⟨DirectionalCoupler.Port.leftFirst, ()⟩ =
            DirectionalCoupler.crossCoefficient p.firstCoupler
        exact (directionalCoupler_forwardScatteringEntries p.firstCoupler).2.1)
  · simp [edgeGain, edgeN7InputChannel, edgeN7OutputChannel]
    symm
    exact ((netlist p).scatteringTransform_entry_same Component.lowerPath
      ⟨MatchedPropagation.Port.right, ()⟩ ⟨MatchedPropagation.Port.left, ()⟩).trans (by
        change (MatchedPropagation.physicalScattering p.lowerPath Unit).toModeTransform
          ⟨MatchedPropagation.Port.right, ()⟩ ⟨MatchedPropagation.Port.left, ()⟩ =
            MatchedPropagation.transmissionCoefficient p.lowerPath
        exact matchedPropagation_forwardScatteringEntry p.lowerPath)
  · simp [edgeGain, edgeN7InputChannel, edgeN7OutputChannel]
    symm
    exact ((netlist p).scatteringTransform_entry_same Component.secondCoupler
      ⟨DirectionalCoupler.Port.rightFirst, ()⟩
      ⟨DirectionalCoupler.Port.leftSecond, ()⟩).trans (by
        change (DirectionalCoupler.physicalScattering p.secondCoupler Unit).toModeTransform
          ⟨DirectionalCoupler.Port.rightFirst, ()⟩
          ⟨DirectionalCoupler.Port.leftSecond, ()⟩ =
            DirectionalCoupler.crossCoefficient p.secondCoupler
        exact (directionalCoupler_forwardScatteringEntries p.secondCoupler).2.2.1)
  · simp [edgeGain, edgeN7InputChannel, edgeN7OutputChannel]
    symm
    exact ((netlist p).scatteringTransform_entry_same Component.secondCoupler
      ⟨DirectionalCoupler.Port.rightSecond, ()⟩
      ⟨DirectionalCoupler.Port.leftFirst, ()⟩).trans (by
        change (DirectionalCoupler.physicalScattering p.secondCoupler Unit).toModeTransform
          ⟨DirectionalCoupler.Port.rightSecond, ()⟩
          ⟨DirectionalCoupler.Port.leftFirst, ()⟩ =
            DirectionalCoupler.crossCoefficient p.secondCoupler
        exact (directionalCoupler_forwardScatteringEntries p.secondCoupler).2.1)
  · simp [edgeGain, edgeN7InputChannel, edgeN7OutputChannel]
    symm
    exact ((netlist p).scatteringTransform_entry_same Component.feedbackPath
      ⟨MatchedPropagation.Port.right, ()⟩ ⟨MatchedPropagation.Port.left, ()⟩).trans (by
        change (MatchedPropagation.physicalScattering p.feedbackPath Unit).toModeTransform
          ⟨MatchedPropagation.Port.right, ()⟩ ⟨MatchedPropagation.Port.left, ()⟩ =
            MatchedPropagation.transmissionCoefficient p.feedbackPath
        exact matchedPropagation_forwardScatteringEntry p.feedbackPath)
  · simp [edgeGain, edgeN7InputChannel, edgeN7OutputChannel]
    symm
    exact ((netlist p).scatteringTransform_entry_same Component.firstCoupler
      ⟨DirectionalCoupler.Port.rightFirst, ()⟩
      ⟨DirectionalCoupler.Port.leftSecond, ()⟩).trans (by
        change (DirectionalCoupler.physicalScattering p.firstCoupler Unit).toModeTransform
          ⟨DirectionalCoupler.Port.rightFirst, ()⟩
          ⟨DirectionalCoupler.Port.leftSecond, ()⟩ =
            DirectionalCoupler.crossCoefficient p.firstCoupler
        exact (directionalCoupler_forwardScatteringEntries p.firstCoupler).2.2.1)
  · simp [edgeGain, edgeN7InputChannel, edgeN7OutputChannel]
    symm
    exact ((netlist p).scatteringTransform_entry_same Component.firstCoupler
      ⟨DirectionalCoupler.Port.rightSecond, ()⟩
      ⟨DirectionalCoupler.Port.leftSecond, ()⟩).trans (by
        change (DirectionalCoupler.physicalScattering p.firstCoupler Unit).toModeTransform
          ⟨DirectionalCoupler.Port.rightSecond, ()⟩
          ⟨DirectionalCoupler.Port.leftSecond, ()⟩ = p.firstCoupler.throughAmplitude
        exact (directionalCoupler_forwardScatteringEntries p.firstCoupler).2.2.2)
  · simp [edgeGain, edgeN7InputChannel, edgeN7OutputChannel]
    symm
    exact ((netlist p).scatteringTransform_entry_same Component.secondCoupler
      ⟨DirectionalCoupler.Port.rightSecond, ()⟩
      ⟨DirectionalCoupler.Port.leftSecond, ()⟩).trans (by
        change (DirectionalCoupler.physicalScattering p.secondCoupler Unit).toModeTransform
          ⟨DirectionalCoupler.Port.rightSecond, ()⟩
          ⟨DirectionalCoupler.Port.leftSecond, ()⟩ = p.secondCoupler.throughAmplitude
        exact (directionalCoupler_forwardScatteringEntries p.secondCoupler).2.2.2)

/-- The edge-indexed eight-node, eleven-branch forward DCDR graph. -/
def signalMultigraph (p : Parameters) :
    Physlib.SignalFlowGraph.Multigraph Node Edge where
  source := edgeSource
  target := edgeTarget
  gain := edgeGain p

/-- The forward DCDR gain matrix obtained from the edge-indexed graph. -/
noncomputable def coefficientMatrix (p : Parameters) : Matrix Node Node ℂ :=
  (signalMultigraph p).toMatrix

/-- The forward DCDR graph explicitly regarded as a coefficient-matrix extraction. -/
noncomputable def signalFlowGraph (p : Parameters) : Matrix Node Node ℂ :=
  Physlib.SignalFlowGraph.ofCoefficientMatrix (coefficientMatrix p)

/-- The edge-indexed DCDR graph with source node one and output node eight. -/
def terminatedMultigraph (p : Parameters) :
    Physlib.SignalFlowGraph.TerminatedMultigraph Node Edge where
  graph := signalMultigraph p
  input := 0
  output := 7

/-- The edge-indexed graph contains exactly eleven branches. -/
lemma edge_card : Fintype.card Edge = 11 := by decide

/-- The terminated graph pins source node one and output node eight. -/
lemma terminatedMultigraph_terminals (p : Parameters) :
    (terminatedMultigraph p).input = 0 ∧ (terminatedMultigraph p).output = 7 :=
  ⟨rfl, rfl⟩

/-- The named coefficient extraction leaves the multigraph gain matrix unchanged. -/
lemma signalFlowGraph_eq_coefficientMatrix (p : Parameters) :
    signalFlowGraph p = coefficientMatrix p := rfl

/-- The displayed coefficient matrix in the published node order one through eight. -/
def displayedCoefficientMatrix (p : Parameters) : Matrix Node Node ℂ :=
  ![![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, p.feedbackCoefficient, 0],
    ![p.firstCoupler.throughAmplitude,
      DirectionalCoupler.crossCoefficient p.firstCoupler, 0, 0, 0, 0, 0, 0],
    ![DirectionalCoupler.crossCoefficient p.firstCoupler,
      p.firstCoupler.throughAmplitude, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, p.lowerCoefficient, 0, 0, 0, 0],
    ![0, 0, p.upperCoefficient, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, p.secondCoupler.throughAmplitude,
      DirectionalCoupler.crossCoefficient p.secondCoupler, 0, 0],
    ![0, 0, 0, 0, DirectionalCoupler.crossCoefficient p.secondCoupler,
      p.secondCoupler.throughAmplitude, 0, 0]]

/-- Summing the eleven retained branches gives the displayed forward coefficient matrix. -/
lemma coefficientMatrix_eq_displayed (p : Parameters) :
    coefficientMatrix p = displayedCoefficientMatrix p := by
  ext output input
  rw [coefficientMatrix, Physlib.SignalFlowGraph.Multigraph.toMatrix_apply]
  change
    (∑ e with
      (signalMultigraph p).source e = input ∧
        (signalMultigraph p).target e = output,
      (signalMultigraph p).gain e) = displayedCoefficientMatrix p output input
  rw [Finset.sum_filter]
  fin_cases output <;> fin_cases input <;>
    simp [signalMultigraph, edgeSource, edgeTarget, edgeGain,
      displayedCoefficientMatrix, Fin.sum_univ_succ]


end DCDR

end

end Optics
