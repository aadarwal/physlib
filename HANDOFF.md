# S7C slice 4b: NSV'16 PANDA Vernier

## Cutoff and synchronization

This AA2 cutoff repairs all three reviewer blockers for the PANDA Vernier slice and parity rows
IP-13 and IP-14. The exact required sync target was
`6f474de29aeec37d454a69e6398540470d4e56df`. It was merged in
`f8afe43b88ea560f2ec8129c8c31605d50967e6c` before the implementation and is an ancestor of the
gated source head `aaaa25edb2493105c97941d09410e388b2c85384`.

The implementation consists of nine new, unregistered modules:

- `Physlib/Optics/Systems/Cascade/PandaNetlist.lean` (468 lines);
- `Physlib/Optics/Systems/Cascade/PandaGraph.lean` (344 lines);
- `Physlib/Optics/Systems/Cascade/PandaBridge.lean` (602 lines);
- `Physlib/Optics/Systems/Cascade/PandaRealization.lean` (1383 lines);
- `Physlib/Optics/Systems/Cascade/PandaResponse.lean` (706 lines);
- `Physlib/Optics/Systems/Cascade/PandaResponseBridge.lean` (191 lines);
- `Physlib/Optics/Systems/Cascade/PandaMason.lean` (110 lines);
- `Physlib/Optics/Systems/Cascade/PandaTopologyRegression.lean` (400 lines); and
- `Physlib/Optics/Systems/Cascade/PandaResponseRegression.lean` (1407 lines).

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
`FlatNetlist` remains bidirectional. The relational bridge therefore certifies a zero-reverse
forward sector, not equality with an undirected-edge closure.

## Construction and bridge

`PandaNetlist` defines an explicit N7 `FlatNetlist` with four directional couplers, four main-ring
quarter delays, four side-ring half delays, fourteen proof-carrying connections, and the four
external channels input, through, add, and drop.

`PandaGraph` defines `Node = Fin 18` and `Edge = Fin 24`; `node_card` and `edge_card` prove the
source counts. Every `edgeGain` is certified by `edgeGain_eq_n7ScatteringEntry` to be an entry of
the assembled N7 component scattering transform.

`PandaBridge` supplies physical routing and the eighteen scalar equations. In particular:

- `connectionForwardPorts_eq_connection` checks all fourteen netlist wires;
- `edgeInput_routedBoundary` and `edgeOutput_routedBoundary` certify every indexed endpoint;
- `edge_routedN7Certificate` bundles endpoint routing with N7 gain ownership; and
- `isNodeSolution_iff_forwardEquations` identifies the raw graph equation with all eighteen
  displayed scalar equations.

`PandaRealization` then proves the complete DCDR-shaped relational bridge. Its
`liftedOutgoing_eq_scatteringTransform` checks all 32 actual component outputs, and
`liftedIncident_eq_incidentAssembly` checks both endpoints of all fourteen wires plus all four
external channels. The resulting statement at
`Physlib/Optics/Systems/Cascade/PandaRealization.lean:1364-1383` is:

```text
isNodeSolution_iff_exists_netlistRealization:
  IsNodeSolution (signalFlowGraph p) (signalInput input) state <->
    exists incident outgoing,
      outgoing = (netlist p).scatteringTransform.toLinearMap incident /\
      incident = (netlist p).connections.incidentAssembly
        outgoing (inputAmplitude p input) /\
      forwardState p incident outgoing = state
```

This theorem reaches the actual `FlatNetlist` scattering and wiring semantics; neither side is a
matrix defined by resumming the retained edge table. The construction is the zero-reverse sector
of the complete bidirectional N7 netlist.

Finally, `throughTransfer_eq_responseTransform` and `dropTransfer_eq_responseTransform` at
`Physlib/Optics/Systems/Cascade/PandaResponseBridge.lean:106-189` open
`FlatNetlist.behavior` through `FlatNetlist.mem_behavior_iff_equations`
(`Physlib/Optics/Network/FlatNetlist.lean:487-500`). Under both the actual N5 well-posedness gate
and the independently exposed directed-graph determinant gate, they identify the two terminated
directed responses with the corresponding entries of the actual `netlist.responseTransform`.

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
canonically based simple loops as topology sentinels. Its inventory has the following teeth:

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

Completeness is discharged independently in `PandaResponseRegression`, not inferred from the
hand-listed inventory. At the positive fixture:

- `responseRegression_nonzeroFamily_eq_main` classifies every nonzero nonempty edge-level loop
  family as the displayed main-ring family;
- `responseRegression_edgeGraphDetOn` at
  `Physlib/Optics/Systems/Cascade/PandaResponseRegression.lean:646-697` sums every node subset,
  loop-family permutation, and parallel-edge choice and proves the only nonzero loop correction;
- `responseRegression_supportedThroughPath_cases` and
  `responseRegression_supportedDropPath_eq` prove converses for all simple forward paths having a
  nonzero edge refinement;
- `responseRegression_supportedThroughPaths` and `responseRegression_supportedDropPaths` at
  `Physlib/Optics/Systems/Cascade/PandaResponseRegression.lean:962-1000` identify the complete
  supported path finsets; and
- `responseRegression_edgeMasonNumerator_through` and
  `responseRegression_edgeMasonNumerator_drop` at
  `Physlib/Optics/Systems/Cascade/PandaResponseRegression.lean:1122-1146` expand the complete
  edge-level numerator sums, including refinements and cofactors, to `14/65` and `-48/65`.

The determinant proof uses the generic edge-family identity at
`Physlib/Mathematics/SignalFlowGraph/EdgeEnumeration.lean:135-138`; the numerator expansion starts
from the actual `edgeMasonNumerator` definition at
`Physlib/Mathematics/SignalFlowGraph/EdgeEnumeration.lean:213-216`.

## Independent numeric anchors

`PandaResponseRegression` uses a concrete positive parameter record and directly unfolds the raw
24-edge coefficient matrix. The hand-expanded 18-coordinate state satisfies the node equation and
has the two displayed coordinates. Separately, exhaustive edge enumeration gives

```text
edge graph determinant = 10/13
through Mason numerator = 14/65
drop Mason numerator = -48/65
```

`responseRegression_graphDet_ne_zero` and `responseRegression_nodeSolution_unique` at
`Physlib/Optics/Systems/Cascade/PandaResponseRegression.lean:1201-1225` connect that independent
determinant to the raw node solution. The generic terminated-solution rule cited at
`Physlib/Mathematics/SignalFlowGraph/Terminated.lean:264-268` then gives, without either printed
NSV theorem:

```text
responseRegression_throughTerminated = 7/25
responseRegression_dropTerminated = -24/25
```

These are proved at
`Physlib/Optics/Systems/Cascade/PandaResponseRegression.lean:1228-1256` from the hand-expanded
state and the independent determinant. `responseRegression_rawNetlistBehavior` at
`Physlib/Optics/Systems/Cascade/PandaResponseRegression.lean:1258-1280` pushes the same state
through the actual relational bridge and constructs an actual N5 behavior output with through
value `7/25` and drop value `-24/25`. Under the separately visible N5 solve gate,
`responseRegression_n5Through` and `responseRegression_n5Drop` at
`Physlib/Optics/Systems/Cascade/PandaResponseRegression.lean:1282-1300` pin the actual
response-transform entries to those values. The source quotients are also expanded independently
to the same values.

The determinant-zero fixture uses identity through-coupling, zero cross-coupling, unit main-ring
propagation, and zero side-ring propagation. Direct expansion gives a zero printed denominator and
a nonzero homogeneous 18-coordinate solution. `responseRegression_singularGraphDet` derives that
the oriented graph determinant is zero from this raw witness, rather than assuming or invoking a
response comparison.

## Parity discharge map

- IP-13 (NSV'16 through): `nsv16_throughTransfer` at
  `Physlib/Optics/Systems/Cascade/PandaResponse.lean:612-637` reproduces printed Theorem 5 under
  `HasSourceCouplerDictionary`, the inherited `HasPrincipalRootSelection` branch gate, the four
  printed `HasSourceCouplerNormalization` hypotheses, `HasNonzeroSourceDenominator`, and nonzero
  directed graph determinant. Composing it with `throughTransfer_eq_responseTransform` at
  `Physlib/Optics/Systems/Cascade/PandaResponseBridge.lean:106-145` adds the actual N5
  `FlatNetlist.IsWellPosed` gate and yields the actual input-to-through response entry.
- IP-14 (NSV'16 drop): `nsv16_dropTransfer` at
  `Physlib/Optics/Systems/Cascade/PandaResponse.lean:639-668` reproduces printed Theorem 6 under
  the identical dictionary, principal-root, four normalization, denominator, and directed-graph
  gates. Composing it with `dropTransfer_eq_responseTransform` at
  `Physlib/Optics/Systems/Cascade/PandaResponseBridge.lean:147-189` adds the actual N5 solve gate
  and yields the actual input-to-drop response entry.

The principal-root premise is not silently discharged: it is the PANDA form of the branch map
already exposed for IP-12 at
`Physlib/Optics/Systems/Microring/SourceBridgeSfg.lean:98-110`. The two N5 bridge lemmas do not
claim that directed-graph invertibility and N5 well-posedness are equivalent.

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
localChannelFintype
localChannelDecidableEq
componentsLocalChannelFintype
componentsLocalChannelDecidableEq
netlistComponentFintype
netlistComponentDecidableEq
netlistLocalChannelFintype
netlistLocalChannelDecidableEq
channelFintype
channelDecidableEq
connectionLocalChannelFintype
connectedChannelFintype
connectedChannelDecidableEq
externalChannelFintype
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
inputChannel_ne_throughChannel
inputChannel_ne_dropChannel
inputAmplitude
inputAmplitude_apply_input
inputAmplitude_apply_add
inputAmplitude_apply_through
inputAmplitude_apply_drop
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
displayedAction
coefficientMatrix_mulVec_eq_displayedAction
signalInput
ForwardEquations
signalInput_eq_piecewise
isNodeSolution_iff_forwardEquations
```

### `PandaRealization`

```text
CouplerLabel
CouplerLabel.component
CouplerLabel.parameters
couplerChannel
PropagationLabel
PropagationLabel.component
PropagationLabel.parameters
propagationChannel
forwardState
liftedIncident
liftedOutgoing
liftedOutgoing_eq_scatteringTransform
incidentAssembly_apply_connectionLeft
incidentAssembly_apply_connectionRight
incidentAssembly_apply_input
incidentAssembly_apply_through
incidentAssembly_apply_add
incidentAssembly_apply_drop
liftedIncident_eq_incidentAssembly
PropagationLabel.inputConnection
PropagationLabel.outputConnection
PropagationLabel.upstreamChannel
PropagationLabel.downstreamChannel
propagationCoordinate_of_netlistEquations
forwardState_lifted
forwardEquations_of_netlistEquations
forwardState_isNodeSolution_of_netlistEquations
isNodeSolution_iff_exists_netlistRealization
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

### `PandaResponseBridge`

```text
outputReadout_apply_through
outputReadout_apply_drop
responseTransform_apply_inputAmplitude_through
responseTransform_apply_inputAmplitude_drop
throughTransfer_eq_responseTransform
dropTransfer_eq_responseTransform
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
responseRegressionNodeRank
responseRegressionNodeRank_lt
responseRegressionMainLoopNodes
responseRegressionMainLoopPermutation
responseRegressionMainLoopEdge
responseRegressionMainLoopChoice
responseRegression_mainLoopPermutation_mem
responseRegression_mainLoopChoice_mem
responseRegression_mainLoopCount
responseRegression_mainLoopFamilyGain
responseRegression_mainLoopChoices
responseRegression_mainFamilySum
responseRegression_edgeGraphDetOn
responseRegression_edgeGraphDet
responseRegressionSupportedEdges
responseRegression_edgeGain_ne_zero_iff
ResponseRegressionNonzeroAdjacent
ResponseRegressionPathSupported
responseRegression_pathSupported_iff_isChain
responseRegression_nonzeroAdjacent_zero
responseRegression_nonzeroAdjacent_one
responseRegression_nonzeroAdjacent_three
responseRegression_nonzeroAdjacent_eight
responseRegression_nonzeroAdjacent_nine
responseRegression_nonzeroAdjacent_four
responseRegression_nonzeroAdjacent_six
responseRegression_nonzeroAdjacent_thirteen
responseRegression_nonzeroAdjacent_fourteen
responseRegression_not_nonzeroAdjacent_two
responseRegression_not_nonzeroAdjacent_seven
responseRegression_supportedThroughPath_cases
responseRegression_supportedDropPath_eq
responseRegressionSupportedThroughPaths
responseRegressionSupportedDropPaths
responseRegression_supportedThroughPaths
responseRegression_supportedDropPaths
responseRegression_throughNumerator_eq_supportedSum
responseRegression_dropNumerator_eq_supportedSum
responseRegression_refiningEdges_throughDirect
responseRegression_refiningEdges_throughMain
responseRegression_refiningEdges_dropDirect
responseRegression_edgeListGain_throughDirect
responseRegression_edgeListGain_throughMain
responseRegression_edgeListGain_dropDirect
responseRegression_throughDirectCofactor
responseRegression_throughMainCofactor
responseRegression_dropDirectCofactor
responseRegression_edgeMasonNumerator_through
responseRegression_edgeMasonNumerator_drop
responseRegressionState
responseRegression_rawNodeEquation
responseRegression_isNodeSolution
responseRegression_through
responseRegression_drop
responseRegression_graphDet
responseRegression_graphDet_ne_zero
responseRegression_nodeSolution_unique
responseRegression_throughTerminated
responseRegression_dropTerminated
responseRegression_rawNetlistBehavior
responseRegression_n5Through
responseRegression_n5Drop
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

1. `PandaNetlist.netlist`, `PandaGraph.edgeGain_eq_n7ScatteringEntry`, and the routing certificates
   in `PandaBridge`;
2. `PandaRealization.liftedOutgoing_eq_scatteringTransform`,
   `liftedIncident_eq_incidentAssembly`, and
   `isNodeSolution_iff_exists_netlistRealization`;
3. the two actual response readouts in `PandaResponseBridge`;
4. `PandaResponseRegression.responseRegression_edgeGraphDetOn`, supported-path classification,
   and the two complete numerator expansions;
5. the positive unique/terminated/N5 anchors and singular fixture in `PandaResponseRegression`;
6. `PandaResponse.HasSourceCouplerNormalization`, `HasPrincipalRootSelection`, and the two NSV
   theorems; and
7. the full-N5 Mason instantiations and retained topology/mis-wire sentinels.

The validation lane should bind at least these names:

- graph counts: `node_card`, `edge_card`;
- N7 derivation: `connectionForwardPorts_eq_connection`, `edge_routedN7Certificate`,
  `liftedOutgoing_eq_scatteringTransform`, `liftedIncident_eq_incidentAssembly`, and
  `isNodeSolution_iff_exists_netlistRealization`;
- actual N5 response: `throughTransfer_eq_responseTransform`,
  `dropTransfer_eq_responseTransform`;
- common Mason domain: `feedbackSignalFlowGraph_graphDet_ne_zero_iff`;
- printed comparisons: `nsv16_throughTransfer`, `nsv16_dropTransfer`;
- oriented Mason comparisons: `auditedThroughMasonResponse_eq_source`,
  `auditedDropMasonResponse_eq_source`;
- exhaustive edge audit: `responseRegression_edgeGraphDetOn`,
  `responseRegression_supportedThroughPaths`, `responseRegression_supportedDropPaths`,
  `responseRegression_edgeMasonNumerator_through`, and
  `responseRegression_edgeMasonNumerator_drop`;
- topology sentinels: all three refinement lemmas, the three grouped gain lemmas, and
  `topology_loop_touch_audit`;
- mis-wire control: `topologyMiswiredMultigraph_ne`,
  `topology_miswired_rightDetour_not_refined`;
- positive anchor: `responseRegression_rawNodeEquation`, `responseRegression_graphDet_ne_zero`,
  `responseRegression_nodeSolution_unique`, `responseRegression_throughTerminated`,
  `responseRegression_dropTerminated`, `responseRegression_rawNetlistBehavior`,
  `responseRegression_n5Through`, and `responseRegression_n5Drop`; and
- singular anchor: `responseRegression_singularRawNodeEquation`,
  `responseRegression_singularState_ne_zero`, `responseRegression_singularGraphDet`, and
  `responseRegression_singularSourceDenominator`.

## Non-claims

- No equality between the directed projection and the paper's undirected SFG is claimed.
- No claim equates the full N5-extracted Mason graph with the 18-node projection.
- No equivalence between the N5 well-posedness gate and directed-graph invertibility is claimed;
  both are retained by every response-transform comparison.
- The raw N5 behavior witness proves existence only; uniqueness is asserted only after supplying
  the actual N5 well-posedness gate.
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
`aaaa25edb2493105c97941d09410e388b2c85384`. One successful `lake-lock env bash` hold temporarily
registered only the nine PANDA modules and ran:

```text
lake exe cache get
lake --wfail build <the nine PANDA modules>
lake exe runPhyslibLinters
lake exe lint_all
./scripts/lint-style.sh
git diff --check
the banned-token, theorem-count, 100-codepoint, and 1500-line audits
```

Results:

- cache: no files to download; 8690 files already decompressed;
- targeted warning-as-error build: passed, 2762 jobs;
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
`c6fcae741d8c29643e5ca027773ee5b1e30968c1a3731a26fef32764a4af7f48` before and after the gate.
The implementation difference from the named sync target is confined to the PANDA modules; this
final cutoff commit changes only `HANDOFF.md`.
