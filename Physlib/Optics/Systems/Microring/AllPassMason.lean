/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.FlatNetlistMason
public import Physlib.Optics.Systems.Microring.AllPass

/-!
# Mason semantics of the all-pass microring

## i. Overview

The all-pass ring has two complementary signal-flow presentations. The generic N5 extraction uses
the complete matrix `C * S`. Separately, this file defines a reduced two-signal circulation model
whose nodes are the coupler-to-propagation signal and the propagated return. It does not derive a
graph reduction, graph isomorphism, or edge-level extraction from the complete graph. Instead, on
`Parameters.HasNonzeroDenominator`, it proves that the reduced model's assembled through transfer
equals the existing N5-derived transfer through their common closed form.

The reduced graph is independently defined as

```text
y = t * x + c * input
x = gamma * y,
```

so its loop determinant is `1 - t * gamma`. The through output is `t * input + c * x`. Mason's
gain from `y` to `x` therefore reconstructs the feedback term in `AllPass.throughTransfer`.
`loopMasonGain` and `loopMasonThroughTransfer` are totalized algebraic definitions; their response
meaning is established only on the nonzero-denominator gate. These fixed-carrier statements make
no delay, causality, region-of-convergence, passivity, reciprocity, or time-reversed pairing claim.
Chain and Z-transform semantics remain separate layers.

## ii. Key results

- `AllPass.loopSignalFlowGraph`: the independently defined two-signal circulation model.
- `AllPass.loopSignalFlowGraph_graphDet`: its determinant is the ring denominator.
- `AllPass.loopMasonThroughTransfer_eq_throughTransfer`: reduced Mason gain equals feedback
  algebra.
- `AllPass.mem_behavior_iff_eq_masonResponseTransform`: relational and generic Mason semantics.
- `AllPass.masonResponseTransform_entry_through_input_eq_loopMason`: the generic extracted
  response, reduced circulation model, and N5 response agree on the solve gate.

## iii. Table of contents

- A. The reduced circulation model
- B. Agreement with the complete N5 graph

## iv. References

This Physlib-original bridge joins the existing all-pass N5 semantics with the generic
signal-flow/Mason API. It reproduces no external source theorem.

-/

@[expose] public section

namespace Optics

noncomputable section

namespace AllPass

/-! ## A. The reduced circulation model -/

/-- The independently defined two-node signal-flow graph of one circulation direction.

Node zero is the coupler-to-propagation signal `y`; node one is the propagated return `x`.
Consequently the edge `0 → 1` has gain `gamma` and the edge `1 → 0` has gain `t`.
-/
def loopSignalFlowGraph (p : Parameters) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, (p.throughAmplitude : ℂ); p.loopCoefficient, 0]

/-- The system matrix of the reduced circulation model. -/
lemma systemMatrix_loopSignalFlowGraph (p : Parameters) :
    Physlib.SignalFlowGraph.systemMatrix (loopSignalFlowGraph p) =
      !![1, -(p.throughAmplitude : ℂ); -p.loopCoefficient, 1] := by
  rw [Physlib.SignalFlowGraph.systemMatrix, loopSignalFlowGraph]
  ext output input
  fin_cases output <;> fin_cases input <;> simp

/-- The reduced circulation model has determinant `1 - t * gamma`, exactly the all-pass
feedback denominator. -/
lemma loopSignalFlowGraph_graphDet (p : Parameters) :
    Physlib.SignalFlowGraph.graphDet (loopSignalFlowGraph p) = p.denominator := by
  rw [Physlib.SignalFlowGraph.graphDet_eq_det,
    systemMatrix_loopSignalFlowGraph, Matrix.det_fin_two_of]
  simp [Parameters.denominator, Parameters.loopGain]

/-- The nonzero ring denominator is exactly the reduced model's Mason determinant gate. -/
lemma loopSignalFlowGraph_graphDet_ne_zero_iff (p : Parameters) :
    Physlib.SignalFlowGraph.graphDet (loopSignalFlowGraph p) ≠ 0 ↔
      p.HasNonzeroDenominator := by
  rw [loopSignalFlowGraph_graphDet]
  rfl

/-- Mason's internal gain from the coupler drive to the propagated return. -/
def loopMasonGain (p : Parameters) : ℂ :=
  Physlib.SignalFlowGraph.masonGain (loopSignalFlowGraph p) 0 1

/-- On the exact solve domain, the internal Mason gain is `gamma / (1 - t * gamma)`. -/
lemma loopMasonGain_eq (p : Parameters) (hDenominator : p.HasNonzeroDenominator) :
    loopMasonGain p = p.loopCoefficient / p.denominator := by
  rw [loopMasonGain,
    Physlib.SignalFlowGraph.masonGain_eq_gain _ _ _
      ((loopSignalFlowGraph_graphDet_ne_zero_iff p).2 hDenominator),
    Physlib.SignalFlowGraph.gain, systemMatrix_loopSignalFlowGraph,
    Matrix.inv_def, Matrix.adjugate_fin_two_of]
  have hDet :
      (!![(1 : ℂ), -(p.throughAmplitude : ℂ); -p.loopCoefficient, 1]).det =
        p.denominator := by
    rw [Matrix.det_fin_two_of]
    simp [Parameters.denominator, Parameters.loopGain]
  rw [hDet]
  simp [Ring.inverse_eq_inv, div_eq_inv_mul]

/-- The totalized through expression assembled from the direct bus path and reduced Mason loop. -/
def loopMasonThroughTransfer (p : Parameters) : ℂ :=
  (p.throughAmplitude : ℂ) +
    DirectionalCoupler.crossCoefficient p.coupler ^ 2 * loopMasonGain p

/-- On the solve gate, the reduced Mason model reconstructs the all-pass feedback transfer. -/
lemma loopMasonThroughTransfer_eq_throughTransfer (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) :
    loopMasonThroughTransfer p = throughTransfer p := by
  rw [loopMasonThroughTransfer, loopMasonGain_eq p hDenominator, throughTransfer]
  simp [div_eq_mul_inv, mul_assoc]

/-! ## B. Agreement with the complete N5 graph -/

/-- The complete extracted feedback graph and the scalar ring denominator have the same exact
nonvanishing gate. -/
lemma feedbackSignalFlowGraph_graphDet_ne_zero_iff_hasNonzeroDenominator (p : Parameters) :
    Physlib.SignalFlowGraph.graphDet (netlist p).feedbackSignalFlowGraph ≠ 0 ↔
      p.HasNonzeroDenominator := by
  rw [← (netlist p).isWellPosed_iff_feedbackSignalFlowGraph_graphDet_ne_zero,
    isWellPosed_iff]

/-- External relational behavior is exactly action by the response assembled from the complete
N5 feedback graph's Mason gains. -/
lemma mem_behavior_iff_eq_masonResponseTransform (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator)
    (input : ModeAmplitude (netlist p).ExternalIncident)
    (output : ModeAmplitude (netlist p).ExternalOutgoing) :
    (input, output) ∈ (netlist p).behavior ↔
      output = (netlist p).masonResponseTransform.toLinearMap input := by
  rw [(netlist p).mem_behavior_iff_eq_responseTransform
      (isWellPosed_of_hasNonzeroDenominator p hDenominator),
    (netlist p).responseTransform_eq_masonResponseTransform]

/-- On the solve gate, the input-to-through entry of the complete extracted Mason response is the
all-pass transfer. -/
lemma masonResponseTransform_entry_through_input (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) :
    (netlist p).masonResponseTransform
        (Outgoing.mk (throughChannel p)) (Incident.mk (inputChannel p)) =
      throughTransfer p := by
  rw [← (netlist p).responseTransform_eq_masonResponseTransform
      (isWellPosed_of_hasNonzeroDenominator p hDenominator),
    responseTransform_entry_through_input p hDenominator]

/-- On the solve gate, the complete extracted response and reduced circulation model agree at the
input-to-through entry. -/
lemma masonResponseTransform_entry_through_input_eq_loopMason (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) :
    (netlist p).masonResponseTransform
        (Outgoing.mk (throughChannel p)) (Incident.mk (inputChannel p)) =
      loopMasonThroughTransfer p := by
  rw [masonResponseTransform_entry_through_input p hDenominator,
    loopMasonThroughTransfer_eq_throughTransfer p hDenominator]

end AllPass

end

end Optics
