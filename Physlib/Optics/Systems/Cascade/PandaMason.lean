/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.FlatNetlistMason
public import Physlib.Optics.Systems.Cascade.PandaResponseBridge

/-!
# Mason semantics of the PANDA N7 netlist

## i. Overview

This file instantiates `FlatNetlistMason` for the explicit twelve-component PANDA netlist. The
automatically extracted feedback graph is the complete N5 coordinate graph, including both
propagation directions. Its determinant is nonzero exactly when the relational netlist is well
posed. Under that common gate, the through- and drop-port entries of the extracted Mason transform
equal the corresponding entries of the behavior-derived N5 response.

This complete extracted graph is distinct from the oriented 18-node Definition-11 projection in
`PandaGraph`. In particular, no result here silently identifies it with the source's undirected
SFG. The source-formula comparisons in `PandaResponse` are instead proved from all eighteen
oriented equations under the explicit principal-root and source-normalization gates.

## ii. Key results

- `Panda.feedbackSignalFlowGraph_graphDet_ne_zero_iff`: the exact common-domain gate.
- `Panda.responseTransform_entry_through_eq_mason`: generic N5/Mason instantiation at through.
- `Panda.responseTransform_entry_drop_eq_mason`: generic N5/Mason instantiation at drop.

## iii. Table of contents

- A. Selected Mason entries
- B. Exact common-domain gate
- C. Generic N5/Mason instantiations

## iv. References and non-claims

The extraction and agreement theorem are Physlib-original generic network results. The PANDA
topology and source formulas are compared with NSV'16 Definition 11 and Theorems 5-6 in the
adjacent modules.

The Mason quotients are totalized definitions. Their response interpretation below is proof-gated
by `FlatNetlist.IsWellPosed`. No convergence, causality, passivity, losslessness, reciprocity,
stability, resonance, bandwidth, dispersion, pole/zero location, insertion-loss model, or material
realization is asserted.
-/

@[expose] public section

namespace Optics

noncomputable section

namespace Panda

/-! ## A. Selected Mason entries -/

/-- The input-to-through entry of the complete N5-extracted Mason response. -/
noncomputable def masonThroughResponse (p : Parameters) : ℂ :=
  (netlist p).masonResponseTransform
    (Outgoing.mk (throughChannel p)) (Incident.mk (inputChannel p))

/-- The input-to-drop entry of the complete N5-extracted Mason response. -/
noncomputable def masonDropResponse (p : Parameters) : ℂ :=
  (netlist p).masonResponseTransform
    (Outgoing.mk (dropChannel p)) (Incident.mk (inputChannel p))

/-! ## B. Exact common-domain gate -/

/-- The complete extracted feedback graph determinant is nonzero exactly when the PANDA N7
relation is well posed. -/
lemma feedbackSignalFlowGraph_graphDet_ne_zero_iff (p : Parameters) :
    Physlib.SignalFlowGraph.graphDet (netlist p).feedbackSignalFlowGraph ≠ 0 ↔
      (netlist p).IsWellPosed := by
  exact (netlist p).isWellPosed_iff_feedbackSignalFlowGraph_graphDet_ne_zero.symm

/-! ## C. Generic N5/Mason instantiations -/

/-- The behavior-derived N5 through entry equals the extracted Mason through entry on their exact
common domain. This is only an instantiation of
`FlatNetlist.responseTransform_eq_masonResponseTransform`. -/
lemma responseTransform_entry_through_eq_mason (p : Parameters)
    (hWellPosed : (netlist p).IsWellPosed) :
    (netlist p).responseTransform hWellPosed
        (Outgoing.mk (throughChannel p)) (Incident.mk (inputChannel p)) =
      masonThroughResponse p := by
  have hAgreement := (netlist p).responseTransform_eq_masonResponseTransform hWellPosed
  exact congrFun (congrFun hAgreement (Outgoing.mk (throughChannel p)))
    (Incident.mk (inputChannel p))

/-- The behavior-derived N5 drop entry equals the extracted Mason drop entry on their exact common
domain. This is only an instantiation of
`FlatNetlist.responseTransform_eq_masonResponseTransform`. -/
lemma responseTransform_entry_drop_eq_mason (p : Parameters)
    (hWellPosed : (netlist p).IsWellPosed) :
    (netlist p).responseTransform hWellPosed
        (Outgoing.mk (dropChannel p)) (Incident.mk (inputChannel p)) =
      masonDropResponse p := by
  have hAgreement := (netlist p).responseTransform_eq_masonResponseTransform hWellPosed
  exact congrFun (congrFun hAgreement (Outgoing.mk (dropChannel p)))
    (Incident.mk (inputChannel p))

end Panda

end

end Optics
