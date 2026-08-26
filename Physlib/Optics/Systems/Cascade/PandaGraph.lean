/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Mathematics.SignalFlowGraph.Terminated
public import Physlib.Optics.Systems.Cascade.PandaNetlist

/-!
# Netlist-owned PANDA forward signal-flow graph

## i. Overview

This file indexes the 24 forward component entries displayed in NSV'16 Definition 11. Every edge
gain is proved to be an entry of the assembled N7 component scattering law; the graph is therefore
not an independently parameterized edge table. `PandaBridge` supplies the corresponding routing
and zero-reverse relational certificate.

The source calls the PANDA graph undirected and singles out the branch between nodes 10 and 5
(NSV'16, text preceding Section 5). Physlib does not silently identify that object with the matrix.
This `Multigraph` retains the arrow orientation printed in Definition 11 and Figure 6.
It contains `10 → 5` but not a second `5 → 10` edge; the complete N7 netlist retains
bidirectionality through separate reverse-going amplitudes. Later comparisons are consequently
forward, zero-reverse formula comparisons, not equality with an undirected-edge closure.

## ii. Key results

- `Panda.signalMultigraph`: the 18-node, 24-edge forward projection.
- `Panda.edgeGain_eq_n7ScatteringEntry`: N7 ownership of every edge gain.
- `Panda.node_card` and `Panda.edge_card`: proved source counts.

## iii. Table of contents

- A. Fixed-carrier coefficients
- B. Source node and edge indices
- C. N7 edge ownership
- D. Coefficient-matrix graph

## iv. References

No claim equates this directed projection with the paper's undirected graph object. No source
transfer formula, passivity, losslessness, reciprocity, causality, stability, resonance, bandwidth,
dispersion, or material realization is asserted here.

S. M. Beillahi, U. Siddique, and S. Tahar, "Formal Analysis of Engineering Systems Based on
Signal-Flow-Graph Theory", NSV 2016, LNCS 10152, Definition 11 and Figure 6, pp. 42-43.
-/

@[expose] public section

namespace Optics

noncomputable section

namespace Panda

/-! ## A. Fixed-carrier coefficients -/

/-- The selected coefficient of the first main-ring quarter section. -/
def Parameters.mainQuarterOneCoefficient (p : Parameters) : ℂ :=
  MatchedPropagation.transmissionCoefficient p.mainQuarterOne

/-- The selected coefficient of the second main-ring quarter section. -/
def Parameters.mainQuarterTwoCoefficient (p : Parameters) : ℂ :=
  MatchedPropagation.transmissionCoefficient p.mainQuarterTwo

/-- The selected coefficient of the third main-ring quarter section. -/
def Parameters.mainQuarterThreeCoefficient (p : Parameters) : ℂ :=
  MatchedPropagation.transmissionCoefficient p.mainQuarterThree

/-- The selected coefficient of the fourth main-ring quarter section. -/
def Parameters.mainQuarterFourCoefficient (p : Parameters) : ℂ :=
  MatchedPropagation.transmissionCoefficient p.mainQuarterFour

/-- The selected coefficient of the first right-ring half section. -/
def Parameters.rightHalfOneCoefficient (p : Parameters) : ℂ :=
  MatchedPropagation.transmissionCoefficient p.rightHalfOne

/-- The selected coefficient of the second right-ring half section. -/
def Parameters.rightHalfTwoCoefficient (p : Parameters) : ℂ :=
  MatchedPropagation.transmissionCoefficient p.rightHalfTwo

/-- The selected coefficient of the first left-ring half section. -/
def Parameters.leftHalfOneCoefficient (p : Parameters) : ℂ :=
  MatchedPropagation.transmissionCoefficient p.leftHalfOne

/-- The selected coefficient of the second left-ring half section. -/
def Parameters.leftHalfTwoCoefficient (p : Parameters) : ℂ :=
  MatchedPropagation.transmissionCoefficient p.leftHalfTwo

/-- The product of the four selected main-ring quarter coefficients. -/
def Parameters.mainRoundTripCoefficient (p : Parameters) : ℂ :=
  p.mainQuarterOneCoefficient * p.mainQuarterTwoCoefficient *
    p.mainQuarterThreeCoefficient * p.mainQuarterFourCoefficient

/-- The product of the two selected right-ring half coefficients. -/
def Parameters.rightRoundTripCoefficient (p : Parameters) : ℂ :=
  p.rightHalfOneCoefficient * p.rightHalfTwoCoefficient

/-- The product of the two selected left-ring half coefficients. -/
def Parameters.leftRoundTripCoefficient (p : Parameters) : ℂ :=
  p.leftHalfOneCoefficient * p.leftHalfTwoCoefficient

/-! ## B. Source node and edge indices -/

/-- The 18 source-numbered PANDA coordinates, represented with zero-based `Fin` indices. -/
abbrev Node := Fin 18

/-- The forward projection has exactly 18 nodes. -/
lemma node_card : Fintype.card Node = 18 := by decide

/-- The 24 branches in the order printed in NSV'16 Definition 11. -/
abbrev Edge := Fin 24

/-- The forward projection has exactly 24 indexed branches. -/
lemma edge_card : Fintype.card Edge = 24 := by decide

/-- Source nodes of the 24 printed branches, translated from one-based to zero-based indices. -/
def edgeSource : Edge → Node :=
  ![0, 0, 1, 1, 3, 8, 8, 11, 12, 10, 10, 9,
    4, 4, 5, 5, 6, 13, 13, 16, 17, 15, 15, 14]

/-- Target nodes of the 24 printed branches, translated from one-based to zero-based indices. -/
def edgeTarget : Edge → Node :=
  ![2, 3, 3, 2, 8, 9, 11, 12, 10, 9, 11, 4,
    6, 7, 7, 6, 13, 14, 16, 17, 15, 16, 14, 1]

/-- Coherent forward edge gains selected from the twelve N7 component laws. -/
def edgeGain (p : Parameters) : Edge → ℂ :=
  ![(p.inputCoupler.throughAmplitude : ℂ),
    DirectionalCoupler.crossCoefficient p.inputCoupler,
    (p.inputCoupler.throughAmplitude : ℂ),
    DirectionalCoupler.crossCoefficient p.inputCoupler,
    p.mainQuarterOneCoefficient,
    (p.rightCoupler.throughAmplitude : ℂ),
    DirectionalCoupler.crossCoefficient p.rightCoupler,
    p.rightHalfOneCoefficient,
    p.rightHalfTwoCoefficient,
    DirectionalCoupler.crossCoefficient p.rightCoupler,
    (p.rightCoupler.throughAmplitude : ℂ),
    p.mainQuarterTwoCoefficient,
    (p.outputCoupler.throughAmplitude : ℂ),
    DirectionalCoupler.crossCoefficient p.outputCoupler,
    (p.outputCoupler.throughAmplitude : ℂ),
    DirectionalCoupler.crossCoefficient p.outputCoupler,
    p.mainQuarterThreeCoefficient,
    (p.leftCoupler.throughAmplitude : ℂ),
    DirectionalCoupler.crossCoefficient p.leftCoupler,
    p.leftHalfOneCoefficient,
    p.leftHalfTwoCoefficient,
    (p.leftCoupler.throughAmplitude : ℂ),
    DirectionalCoupler.crossCoefficient p.leftCoupler,
    p.mainQuarterFourCoefficient]

/-! ## C. N7 edge ownership -/

/-- The physical N7 incident channel supplying each retained forward edge. -/
def edgeN7InputChannel (p : Parameters) : Edge → (netlist p).Channel :=
  ![componentChannel p .inputCoupler ⟨DirectionalCoupler.Port.leftFirst, ()⟩,
    componentChannel p .inputCoupler ⟨DirectionalCoupler.Port.leftFirst, ()⟩,
    componentChannel p .inputCoupler ⟨DirectionalCoupler.Port.leftSecond, ()⟩,
    componentChannel p .inputCoupler ⟨DirectionalCoupler.Port.leftSecond, ()⟩,
    componentChannel p .mainQuarterOne ⟨MatchedPropagation.Port.left, ()⟩,
    componentChannel p .rightCoupler ⟨DirectionalCoupler.Port.leftFirst, ()⟩,
    componentChannel p .rightCoupler ⟨DirectionalCoupler.Port.leftFirst, ()⟩,
    componentChannel p .rightHalfOne ⟨MatchedPropagation.Port.left, ()⟩,
    componentChannel p .rightHalfTwo ⟨MatchedPropagation.Port.left, ()⟩,
    componentChannel p .rightCoupler ⟨DirectionalCoupler.Port.leftSecond, ()⟩,
    componentChannel p .rightCoupler ⟨DirectionalCoupler.Port.leftSecond, ()⟩,
    componentChannel p .mainQuarterTwo ⟨MatchedPropagation.Port.left, ()⟩,
    componentChannel p .outputCoupler ⟨DirectionalCoupler.Port.leftFirst, ()⟩,
    componentChannel p .outputCoupler ⟨DirectionalCoupler.Port.leftFirst, ()⟩,
    componentChannel p .outputCoupler ⟨DirectionalCoupler.Port.leftSecond, ()⟩,
    componentChannel p .outputCoupler ⟨DirectionalCoupler.Port.leftSecond, ()⟩,
    componentChannel p .mainQuarterThree ⟨MatchedPropagation.Port.left, ()⟩,
    componentChannel p .leftCoupler ⟨DirectionalCoupler.Port.leftFirst, ()⟩,
    componentChannel p .leftCoupler ⟨DirectionalCoupler.Port.leftFirst, ()⟩,
    componentChannel p .leftHalfOne ⟨MatchedPropagation.Port.left, ()⟩,
    componentChannel p .leftHalfTwo ⟨MatchedPropagation.Port.left, ()⟩,
    componentChannel p .leftCoupler ⟨DirectionalCoupler.Port.leftSecond, ()⟩,
    componentChannel p .leftCoupler ⟨DirectionalCoupler.Port.leftSecond, ()⟩,
    componentChannel p .mainQuarterFour ⟨MatchedPropagation.Port.left, ()⟩]

/-- The physical N7 outgoing channel receiving each retained forward edge. -/
def edgeN7OutputChannel (p : Parameters) : Edge → (netlist p).Channel :=
  ![componentChannel p .inputCoupler ⟨DirectionalCoupler.Port.rightFirst, ()⟩,
    componentChannel p .inputCoupler ⟨DirectionalCoupler.Port.rightSecond, ()⟩,
    componentChannel p .inputCoupler ⟨DirectionalCoupler.Port.rightSecond, ()⟩,
    componentChannel p .inputCoupler ⟨DirectionalCoupler.Port.rightFirst, ()⟩,
    componentChannel p .mainQuarterOne ⟨MatchedPropagation.Port.right, ()⟩,
    componentChannel p .rightCoupler ⟨DirectionalCoupler.Port.rightFirst, ()⟩,
    componentChannel p .rightCoupler ⟨DirectionalCoupler.Port.rightSecond, ()⟩,
    componentChannel p .rightHalfOne ⟨MatchedPropagation.Port.right, ()⟩,
    componentChannel p .rightHalfTwo ⟨MatchedPropagation.Port.right, ()⟩,
    componentChannel p .rightCoupler ⟨DirectionalCoupler.Port.rightFirst, ()⟩,
    componentChannel p .rightCoupler ⟨DirectionalCoupler.Port.rightSecond, ()⟩,
    componentChannel p .mainQuarterTwo ⟨MatchedPropagation.Port.right, ()⟩,
    componentChannel p .outputCoupler ⟨DirectionalCoupler.Port.rightFirst, ()⟩,
    componentChannel p .outputCoupler ⟨DirectionalCoupler.Port.rightSecond, ()⟩,
    componentChannel p .outputCoupler ⟨DirectionalCoupler.Port.rightSecond, ()⟩,
    componentChannel p .outputCoupler ⟨DirectionalCoupler.Port.rightFirst, ()⟩,
    componentChannel p .mainQuarterThree ⟨MatchedPropagation.Port.right, ()⟩,
    componentChannel p .leftCoupler ⟨DirectionalCoupler.Port.rightFirst, ()⟩,
    componentChannel p .leftCoupler ⟨DirectionalCoupler.Port.rightSecond, ()⟩,
    componentChannel p .leftHalfOne ⟨MatchedPropagation.Port.right, ()⟩,
    componentChannel p .leftHalfTwo ⟨MatchedPropagation.Port.right, ()⟩,
    componentChannel p .leftCoupler ⟨DirectionalCoupler.Port.rightSecond, ()⟩,
    componentChannel p .leftCoupler ⟨DirectionalCoupler.Port.rightFirst, ()⟩,
    componentChannel p .mainQuarterFour ⟨MatchedPropagation.Port.right, ()⟩]

/-- A component-local matrix entry is unchanged by its canonical embedding in the netlist. -/
lemma scatteringTransform_entry_component (p : Parameters) (component : Component)
    (output input : (componentPortFamily component).Channel) :
    (netlist p).scatteringTransform
        (Outgoing.mk (componentChannel p component output))
        (Incident.mk (componentChannel p component input)) =
      (componentScattering p component).toModeTransform output input := by
  simpa [netlist, components, componentChannel] using
    (netlist p).scatteringTransform_entry_same component output input

/-- The four forward entries of one owned N7 directional-coupler matrix. -/
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

/-- The forward entry of one owned N7 matched-propagation matrix. -/
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

/-- Every retained gain is the corresponding assembled N7 component-scattering entry. -/
lemma edgeGain_eq_n7ScatteringEntry (p : Parameters) (edge : Edge) :
    edgeGain p edge =
      (netlist p).scatteringTransform
        (Outgoing.mk (edgeN7OutputChannel p edge))
        (Incident.mk (edgeN7InputChannel p edge)) := by
  fin_cases edge <;>
    simp [edgeGain, edgeN7InputChannel, edgeN7OutputChannel,
      Parameters.mainQuarterOneCoefficient, Parameters.mainQuarterTwoCoefficient,
      Parameters.mainQuarterThreeCoefficient, Parameters.mainQuarterFourCoefficient,
      Parameters.rightHalfOneCoefficient, Parameters.rightHalfTwoCoefficient,
      Parameters.leftHalfOneCoefficient, Parameters.leftHalfTwoCoefficient] <;>
    rw [scatteringTransform_entry_component]
  · exact (directionalCoupler_forwardScatteringEntries p.inputCoupler).1.symm
  · exact (directionalCoupler_forwardScatteringEntries p.inputCoupler).2.1.symm
  · exact (directionalCoupler_forwardScatteringEntries p.inputCoupler).2.2.2.symm
  · exact (directionalCoupler_forwardScatteringEntries p.inputCoupler).2.2.1.symm
  · exact (matchedPropagation_forwardScatteringEntry p.mainQuarterOne).symm
  · exact (directionalCoupler_forwardScatteringEntries p.rightCoupler).1.symm
  · exact (directionalCoupler_forwardScatteringEntries p.rightCoupler).2.1.symm
  · exact (matchedPropagation_forwardScatteringEntry p.rightHalfOne).symm
  · exact (matchedPropagation_forwardScatteringEntry p.rightHalfTwo).symm
  · exact (directionalCoupler_forwardScatteringEntries p.rightCoupler).2.2.1.symm
  · exact (directionalCoupler_forwardScatteringEntries p.rightCoupler).2.2.2.symm
  · exact (matchedPropagation_forwardScatteringEntry p.mainQuarterTwo).symm
  · exact (directionalCoupler_forwardScatteringEntries p.outputCoupler).1.symm
  · exact (directionalCoupler_forwardScatteringEntries p.outputCoupler).2.1.symm
  · exact (directionalCoupler_forwardScatteringEntries p.outputCoupler).2.2.2.symm
  · exact (directionalCoupler_forwardScatteringEntries p.outputCoupler).2.2.1.symm
  · exact (matchedPropagation_forwardScatteringEntry p.mainQuarterThree).symm
  · exact (directionalCoupler_forwardScatteringEntries p.leftCoupler).1.symm
  · exact (directionalCoupler_forwardScatteringEntries p.leftCoupler).2.1.symm
  · exact (matchedPropagation_forwardScatteringEntry p.leftHalfOne).symm
  · exact (matchedPropagation_forwardScatteringEntry p.leftHalfTwo).symm
  · exact (directionalCoupler_forwardScatteringEntries p.leftCoupler).2.2.2.symm
  · exact (directionalCoupler_forwardScatteringEntries p.leftCoupler).2.2.1.symm
  · exact (matchedPropagation_forwardScatteringEntry p.mainQuarterFour).symm

/-! ## D. Coefficient-matrix graph -/

/-- The 18-node, 24-edge forward projection owned by the PANDA N7 netlist. -/
def signalMultigraph (p : Parameters) :
    Physlib.SignalFlowGraph.Multigraph Node Edge where
  source := edgeSource
  target := edgeTarget
  gain := edgeGain p

/-- The coefficient matrix obtained by summing retained parallel edge gains. -/
noncomputable def coefficientMatrix (p : Parameters) : Matrix Node Node ℂ :=
  (signalMultigraph p).toMatrix

/-- The retained forward graph as a coefficient-matrix signal-flow graph. -/
noncomputable def signalFlowGraph (p : Parameters) : Matrix Node Node ℂ :=
  Physlib.SignalFlowGraph.ofCoefficientMatrix (coefficientMatrix p)

/-- The source-input to through-output terminated forward graph. -/
def throughTerminatedMultigraph (p : Parameters) :
    Physlib.SignalFlowGraph.TerminatedMultigraph Node Edge where
  graph := signalMultigraph p
  input := 0
  output := 2

/-- The source-input to drop-output terminated forward graph. -/
def dropTerminatedMultigraph (p : Parameters) :
    Physlib.SignalFlowGraph.TerminatedMultigraph Node Edge where
  graph := signalMultigraph p
  input := 0
  output := 7

/-- The two terminated projections use source node one and printed outputs three and eight. -/
lemma terminatedMultigraph_terminals (p : Parameters) :
    (throughTerminatedMultigraph p).input = 0 ∧
      (throughTerminatedMultigraph p).output = 2 ∧
      (dropTerminatedMultigraph p).input = 0 ∧
      (dropTerminatedMultigraph p).output = 7 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Naming the coefficient extraction leaves the retained gain matrix unchanged. -/
lemma signalFlowGraph_eq_coefficientMatrix (p : Parameters) :
    signalFlowGraph p = coefficientMatrix p := rfl

end Panda

end

end Optics
