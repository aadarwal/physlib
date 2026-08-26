/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Systems.DCDR.Bridge

/-!
# Double-coupler double-ring topology

## i. Overview

This compatibility module re-exports the DCDR construction split across `Netlist`, `Graph`,
and `Bridge`. The split preserves every declaration in the `Optics.DCDR` namespace.

FMICS'15 p. 172 states that its coherent treatment was not printed. Coherent N7
`t`/`-I * k` is the source's own unprinted coherent branch; the printed incoherent
`1 - k`/`k` model is a different case, compared only if reference [3] surfaces.

The complete N7 netlist is bidirectional, while the source graph records only its forward
boundary coordinates. No claim identifies the eight-node matrix with the complete `C * S`
feedback graph. This is a fixed-carrier, single-mode topology; no passivity, losslessness,
reciprocity, causality, time-domain behavior, stability, pole, zero, resonance, bandwidth, or
material realization is asserted.

## ii. Key results

- `DCDR.netlist`: the explicit two-coupler, three-path N7 flat netlist.
- `DCDR.signalMultigraph`: the edge-indexed eight-node, eleven-branch forward graph.
- `DCDR.edgeGain_eq_n7ScatteringEntry`: every retained gain is an assembled N7 entry.
- `DCDR.isNodeSolution_iff_exists_netlistRealization`: graph solutions are exactly the
  projected complete zero-reverse N7 realizations.

## iii. Table of contents

- `DCDR.Netlist`: components, wiring, external channels, and forward coordinates
- `DCDR.Graph`: multigraph, coefficient matrix, graph, and edge provenance
- `DCDR.Bridge`: lifts and the relational extraction equivalence

## iv. References

U. Siddique, S. M. Beillahi, and S. Tahar, "On the Formal Analysis of Photonic Signal
Processing Systems", FMICS 2015, LNCS 9128, Definition 8 and Theorem 3 (p. 173).
-/
