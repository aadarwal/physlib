# S7C slice 4b: NSV'16 PANDA Vernier

## Cutoff and synchronization

This cutoff adds the PANDA Vernier slice for parity rows IP-13 and IP-14. The exact required
battery-green sync target was
`3662b475ef6bdfab628bb354801e09c8177e3551`. It was merged before the exact gate in
`f99831fe8e4c832e3897c8a85a1ecd3cf386854d`, and is an ancestor of the gated source. The target
deleted the prior lane-local handoff; no Lean conflict occurred.

The implementation consists of seven new, unregistered modules:

- `Physlib/Optics/Systems/Cascade/PandaNetlist.lean` (401 lines);
- `Physlib/Optics/Systems/Cascade/PandaGraph.lean` (344 lines);
- `Physlib/Optics/Systems/Cascade/PandaBridge.lean` (637 lines);
- `Physlib/Optics/Systems/Cascade/PandaResponse.lean` (706 lines);
- `Physlib/Optics/Systems/Cascade/PandaMason.lean` (110 lines);
- `Physlib/Optics/Systems/Cascade/PandaTopologyRegression.lean` (405 lines); and
- `Physlib/Optics/Systems/Cascade/PandaResponseRegression.lean` (284 lines).

All are below the 1500-line module cap. `Physlib.lean` is intentionally unchanged in the cutoff.

## Source transcription and scope

The source text is the layout-preserving extraction at `scratchpad/papers/NSV16.txt`.

- Lines 541-554 print Definition 11 as an 18-node list of 24 directed triples.
- Lines 558-573 print Theorem 5, the input-to-through quotient.
- Lines 578-591 print Theorem 6, the input-to-drop quotient.
- Lines 568 and 580 give exactly four complex hypotheses:
  `c1^2 + s1^2 = 1`, `c2^2 + s2^2 = 1`, `cr^2 + sr^2 = 1`, and
  `cl^2 + sl^2 = 1`.
- Lines 353-356 and 539 call the source PANDA SFG undirected and cite the branch between source
  nodes 10 and 5.
- Lines 609-612 say that the authors found missing parts in three transfer functions in reference
  [10] and a sign mismatch in reference [1]. They do not identify an error in their own Theorem 5
  or 6.

Accordingly, `HasSourceCouplerNormalization` is exactly the four printed complex square-sum
hypotheses. Physlib reproduces the two printed numerators and their common denominator without a
forced correction. The extra hypotheses on the comparison theorems are explicitly cross-model or
response-semantic gates: the N7/source coupler dictionary, the IP-12 principal-root selection,
nonzero printed denominator, and invertibility of the oriented graph.

The paper's undirected graph is not silently identified with the Physlib graph. `signalMultigraph`
is the 18-node, 24-edge orientation printed in Definition 11; in one-based source numbering it
contains the `10 -> 5` branch but not a separately inserted `5 -> 10` edge. The complete N7
`FlatNetlist` remains bidirectional. The matrix bridge therefore certifies a zero-reverse forward
projection, not equality with an undirected-edge closure.

## Construction and bridge

`PandaNetlist` defines an explicit N7 `FlatNetlist` with four directional couplers, four main-ring
quarter delays, four side-ring half delays, fourteen proof-carrying connections, and the four
external channels input, through, add, and drop.

`PandaGraph` defines `Node = Fin 18` and `Edge = Fin 24`; `node_card` and `edge_card` prove the
source counts. Every `edgeGain` is certified by `edgeGain_eq_n7ScatteringEntry` to be an entry of
the assembled N7 component scattering transform.

`PandaBridge` strengthens component ownership to physical routing. In particular:

- `connectionForwardPorts_eq_connection` checks all fourteen netlist wires;
- `edgeInput_routedBoundary` and `edgeOutput_routedBoundary` certify every indexed endpoint;
- `edge_routedN7Certificate` bundles endpoint routing with N7 gain ownership;
- `coefficientMatrix_eq_netlistProjection` proves the whole graph coefficient matrix equal to the
  matrix assembled from those N7 entries; and
- `isNodeSolution_iff_netlistForwardRelation` gives the requested relational graph/netlist bridge.

Thus the 18-node matrix is derived from the netlist by a proved matrix equality and routing
relation. It is not a separately accepted hand-drawn edge table.

## Mason instantiations and source theorems

There are two deliberately distinct Mason layers.

`PandaMason` instantiates the generic `FlatNetlistMason` construction on the full N7 netlist. Its
automatically extracted feedback graph contains the complete N5 coordinates. The exact common
domain is the iff

```text
feedbackSignalFlowGraph_graphDet_ne_zero_iff:
  graphDet (netlist p).feedbackSignalFlowGraph != 0 <-> (netlist p).IsWellPosed.
```

On that domain, `responseTransform_entry_through_eq_mason` and
`responseTransform_entry_drop_eq_mason` identify the behavior-derived N5 entries with the generic
Mason entries. These are instantiations, not new literature theorems.

Separately, `PandaResponse` solves all eighteen oriented equations and proves the only two theorem
declarations in the slice:

```text
nsv16_throughTransfer:
  (throughTerminatedMultigraph p).transfer = sourceThroughTransfer s

nsv16_dropTransfer:
  (dropTerminatedMultigraph p).transfer = sourceDropTransfer s
```

Both carry the exact source normalization plus the dictionary, principal-root, denominator, and
oriented-graph gates described above. `auditedThroughMasonResponse_eq_source` and
`auditedDropMasonResponse_eq_source` are lemmas connecting the oriented edge-Mason quotients to
the printed expressions on that same domain.

The source denominator is solved without dividing by either side-ring factor. The only scalar
division gate is `HasNonzeroSourceDenominator`; the sparse factorization is proved separately by
`sourceDenominator_eq_factorized`.

## Path, loop, and wiring audit

`PandaTopologyRegression` enumerates five simple through paths, two simple drop paths, and six
canonically based simple loops. This inventory has the following independent teeth:

- the three cardinality lemmas are kernel `decide` proofs;
- the soundness lemmas prove terminals, repetition freedom, closure where applicable, and actual
  adjacency in the retained 24-edge topology;
- `topology_path_refinements`, `topology_drop_path_refinements`, and
  `topology_loop_refinements` give the exact indexed edge list for every path and loop;
- the gain lemmas expand every retained coupler and propagation choice; and
- `topology_loop_touch_audit` proves both touching and non-touching cases needed by Mason
  cofactors.

The asymmetric negative control cross-wires the two side-ring half joins while preserving both
finite counts and all scalar gains. `topologyMiswiredMultigraph_ne` proves the graph changed, and
`topology_miswired_rightDetour_not_refined` proves that the expected right-circulation refinement
then disappears. The sentinel is gain-independent and can genuinely fail under mis-wiring.

## Independent numeric anchors

`PandaResponseRegression` uses a concrete positive parameter record and directly unfolds the raw
24-edge coefficient matrix. The hand-expanded 18-coordinate state satisfies the node equation and
has

```text
through coordinate = 7/25
drop coordinate = -24/25
printed denominator = 10/13.
```

The source quotients are expanded independently to the same two values. These proofs do not invoke
either NSV comparison theorem or either Mason/N5 bridge lemma.

The determinant-zero fixture uses identity through-coupling, zero cross-coupling, unit main-ring
propagation, and zero side-ring propagation. Direct expansion gives a zero printed denominator and
a nonzero homogeneous 18-coordinate solution. `responseRegression_singularGraphDet` derives that
the oriented graph determinant is zero from this raw witness, rather than assuming or invoking a
response comparison.

## Public declaration inventory

All declarations below are in namespaces `Optics.Panda` or `Optics.Panda.Parameters`.

### `PandaNetlist`

```text
Parameters
Component
componentPortFamily
componentScattering
components
Connection
connections
netlist
componentChannel
input_not_connected
through_not_connected
add_not_connected
drop_not_connected
inputChannel
throughChannel
addChannel
dropChannel
inputChannel_ne_addChannel
inputAmplitude
inputAmplitude_apply_input
inputAmplitude_apply_add
```

### `PandaGraph`

```text
mainQuarterOneCoefficient
mainQuarterTwoCoefficient
mainQuarterThreeCoefficient
mainQuarterFourCoefficient
rightHalfOneCoefficient
rightHalfTwoCoefficient
leftHalfOneCoefficient
leftHalfTwoCoefficient
mainRoundTripCoefficient
rightRoundTripCoefficient
leftRoundTripCoefficient
Node
node_card
Edge
edge_card
edgeSource
edgeTarget
edgeGain
edgeN7InputChannel
edgeN7OutputChannel
scatteringTransform_entry_component
edgeGain_eq_n7ScatteringEntry
signalMultigraph
coefficientMatrix
signalFlowGraph
throughTerminatedMultigraph
dropTerminatedMultigraph
terminatedMultigraph_terminals
signalFlowGraph_eq_coefficientMatrix
```

### `PandaBridge`

```text
connectionNode
connectionForwardPorts
connectionForwardPorts_eq_connection
nodeN7Channel
connectionLeftMode
connectionRightMode
connectionLeftChannel
connectionRightChannel
RoutedBoundary
routedBoundary_refl
routedBoundary_connection_forward
routedBoundary_connection_reverse
connectionNode_routedBoundaries
edgeInput_routedBoundary
edgeOutput_routedBoundary
edge_routedN7Certificate
netlistProjectionMatrix
coefficientMatrix_eq_netlistProjection
displayedAction
coefficientMatrix_mulVec_eq_displayedAction
NetlistForwardRelation
isNodeSolution_iff_netlistForwardRelation
signalInput
ForwardEquations
signalInput_eq_piecewise
isNodeSolution_iff_forwardEquations
```

### `PandaResponse`

```text
SourceParameters
HasSourceCouplerDictionary
HasPrincipalRootSelection
HasSourceCouplerNormalization
sourceDenominator
HasNonzeroSourceDenominator
sourceThroughNumerator
sourceDropNumerator
sourceThroughTransfer
sourceDropTransfer
auditedThroughMasonResponse
auditedDropMasonResponse
sourceDenominator_eq_factorized
sourceThroughNumerator_eq_factorized
sourceDropNumerator_eq_factorized
sourceCrossCoefficient
closedState
sourceCrossCoefficient_sq
closedState_forwardEquations
signalInput_one_eq_single
nsv16_throughTransfer
nsv16_dropTransfer
auditedThroughMasonResponse_eq_source
auditedDropMasonResponse_eq_source
```

### `PandaMason`

```text
masonThroughResponse
masonDropResponse
feedbackSignalFlowGraph_graphDet_ne_zero_iff
responseTransform_entry_through_eq_mason
responseTransform_entry_drop_eq_mason
```

### `PandaTopologyRegression`

```text
TopologyAdjacent
topologyAdjacentDecidable
topologyAdjacent_iff
topologyThroughDirect
topologyThroughMainDirect
topologyThroughRightCirculation
topologyThroughLeftCirculation
topologyThroughBothCirculations
topologyThroughPaths
topologyThroughPaths_card
topologyDropDirect
topologyDropRightCirculation
topologyDropPaths
topologyDropPaths_card
topologyThroughPaths_sound
topologyDropPaths_sound
topologyRightLoop
topologyLeftLoop
topologyMainDirectLoop
topologyMainRightLoop
topologyMainLeftLoop
topologyMainBothLoop
topologyCanonicalLoops
topologyCanonicalLoops_card
topologyCanonicalLoops_sound
topology_path_refinements
topology_drop_path_refinements
topology_loop_refinements
topology_rightLoop_gain
topology_leftLoop_gain
topology_throughPath_gains
topology_dropPath_gains
topology_mainLoop_gains
topology_loop_touch_audit
topologyMiswiredEdgeTarget
topologyMiswiredMultigraph
topologyMiswiredSkeleton
topology_miswired_join_sentinel
topologyMiswiredMultigraph_ne
topology_miswired_rightDetour_not_refined
```

### `PandaResponseRegression`

```text
responseRegressionPropagation
responseRegressionParameters
responseRegressionSource
responseRegression_sourceDictionary
responseRegression_sourceNormalization
responseRegression_principalRootSelection
responseRegression_sourceDenominator
responseRegression_hasNonzeroSourceDenominator
responseRegressionState
responseRegression_rawNodeEquation
responseRegression_isNodeSolution
responseRegression_through
responseRegression_drop
responseRegression_sourceThrough
responseRegression_sourceDrop
responseRegressionSingularParameters
responseRegressionSingularSource
responseRegression_singularSourceDenominator
responseRegressionSingularState
responseRegression_singularState_ne_zero
responseRegression_singularRawNodeEquation
responseRegression_singularIsNodeSolution
responseRegression_singularGraphDet
```

## Reviewer and validation bindings

Suggested review order:

1. `PandaNetlist.netlist`, then `PandaBridge.coefficientMatrix_eq_netlistProjection` and
   `PandaBridge.isNodeSolution_iff_netlistForwardRelation`;
2. `PandaGraph.node_card`, `edge_card`, and `edgeGain_eq_n7ScatteringEntry`;
3. `PandaTopologyRegression.topology_*_refinements`, gain lemmas, touch audit, and mis-wire
   sentinel;
4. `PandaResponse.HasSourceCouplerNormalization`, `HasPrincipalRootSelection`, and the two NSV
   theorems;
5. `PandaMason.feedbackSignalFlowGraph_graphDet_ne_zero_iff` and the two generic instantiations;
   and
6. both raw fixtures in `PandaResponseRegression`.

The validation lane should bind at least these names:

- graph counts: `node_card`, `edge_card`;
- N7 derivation: `connectionForwardPorts_eq_connection`, `edge_routedN7Certificate`,
  `coefficientMatrix_eq_netlistProjection`, `isNodeSolution_iff_netlistForwardRelation`;
- common Mason domain: `feedbackSignalFlowGraph_graphDet_ne_zero_iff`;
- printed comparisons: `nsv16_throughTransfer`, `nsv16_dropTransfer`;
- oriented Mason comparisons: `auditedThroughMasonResponse_eq_source`,
  `auditedDropMasonResponse_eq_source`;
- topology teeth: all three refinement lemmas, the three grouped gain lemmas, and
  `topology_loop_touch_audit`;
- mis-wire control: `topologyMiswiredMultigraph_ne`,
  `topology_miswired_rightDetour_not_refined`;
- positive raw anchor: `responseRegression_rawNodeEquation`, `responseRegression_through`,
  `responseRegression_drop`, `responseRegression_sourceThrough`,
  `responseRegression_sourceDrop`; and
- singular anchor: `responseRegression_singularRawNodeEquation`,
  `responseRegression_singularState_ne_zero`, `responseRegression_singularGraphDet`, and
  `responseRegression_singularSourceDenominator`.

## Non-claims

- No equality between the directed projection and the paper's undirected SFG is claimed.
- No claim equates the full N5-extracted Mason graph with the 18-node projection.
- No additional or corrected version of NSV'16 Theorem 5 or 6 is claimed.
- The totalized quotients have response meaning only on their stated nonzero/well-posed domains.
- The singular fixture is not asserted to satisfy N7 component validity.
- No DATE lattice, quadruple-ring lattice, coupled-lattice, or full `M x N` lattice result is
  claimed.
- No passivity, losslessness, reciprocity, impedance match, causality, convergence, stability,
  resonance, bandwidth, dispersion, pole/zero location, insertion-loss model, material
  realization, or measurement-validation claim is made.
- No electromagnetic power claim is made. A later power interpretation remains normalized modal
  power until the common-frequency Maxwell and aperture-flux hypotheses in
  `Physlib/Optics/HarmonicFlux/PropagatingModePower.lean:60-90` are supplied.
- Human verification of the bibliography and source transcription remains required by
  `AI-POLICY.md`.

## Exact validation record

The exact implementation source head was
`f99831fe8e4c832e3897c8a85a1ecd3cf386854d`. Before the gate, the development build cache was
refreshed with `rsync --ignore-existing`. One `lake-lock env bash` hold temporarily registered
only the seven PANDA modules and ran:

```text
lake exe cache get
lake --wfail build <the seven PANDA modules>
lake exe runPhyslibLinters
lake exe lint_all
./scripts/lint-style.sh
git diff --check
the banned-token, theorem-count, 100-codepoint, and 1500-line audits
```

Results:

- cache: no files to download; 8690 files already decompressed;
- targeted warning-as-error build: passed, 2760 jobs;
- `runPhyslibLinters`: Physlib and QuantumInfo passed;
- `lint_all`: exited 0; the full build and declaration linters passed, and its advisory
  repository-wide style/import inventories named no PANDA file;
- standalone committed-state `lint-style.sh`: passed;
- `git diff --check`: passed;
- no PANDA file contains `maxHeartbeats`, `native_decide`, `sorry`, `axiom`, or
  `Lean.ofReduceBool`;
- every PANDA line is at most 100 Unicode codepoints and every module is below 1500 lines; and
- `PandaResponse.lean` contains exactly two theorem declarations, the printed NSV'16 Theorems 5
  and 6; both audited Mason comparisons are lemmas.

The temporary registry was restored byte-identically. `Physlib.lean` had SHA-256
`d21d939c6ba90ce5f2391008df6208425e7110029c0b6929261be3a261ab0f37` before and after the gate.
The implementation difference from the named sync target is exactly the seven PANDA Lean files;
this final cutoff commit changes only `HANDOFF.md`.
