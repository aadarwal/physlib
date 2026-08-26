/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Systems.Cascade.PandaResponse

/-!
# PANDA forward-graph response bridge

## i. Overview

This file carries the relational equivalence in `PandaRealization` through the external N5
readout. Under both independently visible solve gates, the through and drop transfers of the
directed eighteen-node projection equal the corresponding entries of the actual twelve-component
`FlatNetlist.responseTransform`.

The proof opens `FlatNetlist.behavior`, extracts the actual component-scattering, routing, and
external-readout equations, and projects their complete incident/outgoing witness. It does not
identify the directed projection with the complete N5 feedback graph or with the source's
undirected SFG.

## ii. Key results

- `Panda.throughTransfer_eq_responseTransform`: actual N5 through readout.
- `Panda.dropTransfer_eq_responseTransform`: actual N5 drop readout.

## iii. Table of contents

- A. External N5 readouts
- B. Directed transfer comparison

## iv. References

The equalities are response statements only under N5 well-posedness and invertibility of the
directed graph. No equivalence between those two gates is claimed. No passivity, losslessness,
reciprocity, causality, convergence, stability, resonance, bandwidth, dispersion, pole/zero
location, insertion-loss model, material realization, or power normalization is asserted.
-/

@[expose] public section

namespace Optics

noncomputable section

namespace Panda

open Physlib.SignalFlowGraph

/-- The bridge uses the same finite external-channel enumeration as N5 elimination. -/
local instance responseBridgeExternalChannelFintype (p : Parameters) :
    Fintype (netlist p).ExternalChannel :=
  (netlist p).eliminationExternalChannelFintype
/-!
## A. External N5 readouts
-/
/-- External readout returns the input coupler's declared through coordinate. -/
lemma outputReadout_apply_through (p : Parameters)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex) :
    (netlist p).outputReadout.toLinearMap outgoing
        (Outgoing.mk (throughChannel p)) =
      outgoing (Outgoing.mk (couplerChannel p .input .rightFirst)) := by
  rw [FlatNetlist.outputReadout,
    (netlist p).connections.externalOutgoingReadout_apply,
    ModeAmplitude.restrictEmbedding_apply]
  rfl

/-- External readout returns the output coupler's declared drop coordinate. -/
lemma outputReadout_apply_drop (p : Parameters)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex) :
    (netlist p).outputReadout.toLinearMap outgoing
        (Outgoing.mk (dropChannel p)) =
      outgoing (Outgoing.mk (couplerChannel p .output .rightSecond)) := by
  rw [FlatNetlist.outputReadout,
    (netlist p).connections.externalOutgoingReadout_apply,
    ModeAmplitude.restrictEmbedding_apply]
  rfl

/-- The N5 through coordinate on source-only excitation is its input-column entry. -/
lemma responseTransform_apply_inputAmplitude_through (p : Parameters)
    (hWellPosed : (netlist p).IsWellPosed) (amplitude : ℂ) :
    ((netlist p).responseTransform hWellPosed).toLinearMap (inputAmplitude p amplitude)
        (Outgoing.mk (throughChannel p)) =
      (netlist p).responseTransform hWellPosed
          (Outgoing.mk (throughChannel p)) (Incident.mk (inputChannel p)) * amplitude := by
  simp [inputAmplitude, Matrix.toLpLin_apply]
  ring

/-- The N5 drop coordinate on source-only excitation is its input-column entry. -/
lemma responseTransform_apply_inputAmplitude_drop (p : Parameters)
    (hWellPosed : (netlist p).IsWellPosed) (amplitude : ℂ) :
    ((netlist p).responseTransform hWellPosed).toLinearMap (inputAmplitude p amplitude)
        (Outgoing.mk (dropChannel p)) =
      (netlist p).responseTransform hWellPosed
          (Outgoing.mk (dropChannel p)) (Incident.mk (inputChannel p)) * amplitude := by
  simp [inputAmplitude, Matrix.toLpLin_apply]
  ring
/-!
## B. Directed transfer comparison
-/
/-- The directed through transfer equals the actual N5 input-to-through entry under both solve
gates. -/
lemma throughTransfer_eq_responseTransform (p : Parameters)
    (hWellPosed : (netlist p).IsWellPosed)
    (hGraph : graphDet (coefficientMatrix p) ≠ 0) :
    (throughTerminatedMultigraph p).transfer =
      (netlist p).responseTransform hWellPosed
        (Outgoing.mk (throughChannel p)) (Incident.mk (inputChannel p)) := by
  let output := ((netlist p).responseTransform hWellPosed).toLinearMap (inputAmplitude p 1)
  have hMember : (inputAmplitude p 1, output) ∈ (netlist p).behavior := by
    rw [← (netlist p).toBehavior_responseTransform hWellPosed,
      ModeTransform.mem_toBehavior_iff_toLinearMap]
  rcases ((netlist p).mem_behavior_iff_equations (inputAmplitude p 1) output).mp hMember with
    ⟨incident, outgoing, hScattering, hAssembly, hOutput⟩
  have hAssembly' : incident =
      (netlist p).connections.incidentAssembly outgoing (inputAmplitude p 1) := by
    simpa only [PortConnectionFamily.incidentAssembly] using hAssembly
  let state := forwardState p incident outgoing
  have hState : IsNodeSolution (coefficientMatrix p) (Pi.single (0 : Node) 1) state := by
    have hProjection := forwardState_isNodeSolution_of_netlistEquations p 1 incident outgoing
      hScattering hAssembly'
    simpa only [signalFlowGraph_eq_coefficientMatrix, signalInput_one_eq_single, state] using
      hProjection
  have hUnit : IsUnit (systemMatrix (coefficientMatrix p)).det := by
    rw [← graphDet_eq_det]
    exact isUnit_iff_ne_zero.mpr hGraph
  have hTransfer : (throughTerminatedMultigraph p).transfer = state 2 :=
    TerminatedMultigraph.transfer_eq_of_isNodeSolution
      (throughTerminatedMultigraph p) hUnit hState
  have hReadout := congrArg
    (fun value => value (Outgoing.mk (throughChannel p))) hOutput
  rw [outputReadout_apply_through] at hReadout
  have hOutputValue : output (Outgoing.mk (throughChannel p)) = state 2 := by
    simpa [state, forwardState] using hReadout
  have hResponse := responseTransform_apply_inputAmplitude_through p hWellPosed 1
  calc
    (throughTerminatedMultigraph p).transfer = state 2 := hTransfer
    _ = output (Outgoing.mk (throughChannel p)) := hOutputValue.symm
    _ = (netlist p).responseTransform hWellPosed
        (Outgoing.mk (throughChannel p)) (Incident.mk (inputChannel p)) := by
      simpa [output] using hResponse

/-- The directed drop transfer equals the actual N5 input-to-drop entry under both solve gates. -/
lemma dropTransfer_eq_responseTransform (p : Parameters)
    (hWellPosed : (netlist p).IsWellPosed)
    (hGraph : graphDet (coefficientMatrix p) ≠ 0) :
    (dropTerminatedMultigraph p).transfer =
      (netlist p).responseTransform hWellPosed
        (Outgoing.mk (dropChannel p)) (Incident.mk (inputChannel p)) := by
  let output := ((netlist p).responseTransform hWellPosed).toLinearMap (inputAmplitude p 1)
  have hMember : (inputAmplitude p 1, output) ∈ (netlist p).behavior := by
    rw [← (netlist p).toBehavior_responseTransform hWellPosed,
      ModeTransform.mem_toBehavior_iff_toLinearMap]
  rcases ((netlist p).mem_behavior_iff_equations (inputAmplitude p 1) output).mp hMember with
    ⟨incident, outgoing, hScattering, hAssembly, hOutput⟩
  have hAssembly' : incident =
      (netlist p).connections.incidentAssembly outgoing (inputAmplitude p 1) := by
    simpa only [PortConnectionFamily.incidentAssembly] using hAssembly
  let state := forwardState p incident outgoing
  have hState : IsNodeSolution (coefficientMatrix p) (Pi.single (0 : Node) 1) state := by
    have hProjection := forwardState_isNodeSolution_of_netlistEquations p 1 incident outgoing
      hScattering hAssembly'
    simpa only [signalFlowGraph_eq_coefficientMatrix, signalInput_one_eq_single, state] using
      hProjection
  have hUnit : IsUnit (systemMatrix (coefficientMatrix p)).det := by
    rw [← graphDet_eq_det]
    exact isUnit_iff_ne_zero.mpr hGraph
  have hTransfer : (dropTerminatedMultigraph p).transfer = state 7 :=
    TerminatedMultigraph.transfer_eq_of_isNodeSolution
      (dropTerminatedMultigraph p) hUnit hState
  have hReadout := congrArg
    (fun value => value (Outgoing.mk (dropChannel p))) hOutput
  rw [outputReadout_apply_drop] at hReadout
  have hOutputValue : output (Outgoing.mk (dropChannel p)) = state 7 := by
    simpa [state, forwardState] using hReadout
  have hResponse := responseTransform_apply_inputAmplitude_drop p hWellPosed 1
  calc
    (dropTerminatedMultigraph p).transfer = state 7 := hTransfer
    _ = output (Outgoing.mk (dropChannel p)) := hOutputValue.symm
    _ = (netlist p).responseTransform hWellPosed
        (Outgoing.mk (dropChannel p)) (Incident.mk (inputChannel p)) := by
      simpa [output] using hResponse

end Panda

end

end Optics
