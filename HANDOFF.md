# S7D DCDR slice 2b handoff

## Branch and cutoff scope

- Branch: `optics/s7d-dcdr`
- Worktree: `/Users/aadarwal/src/aadarwal/physlib-wt/optics-s7d-dcdr`
- Exact controller sync target: `329d5a59`
- Sync merge head before the slice-2b cutoff edits: `fcfd057b`
- Slice 2 adds the N5 elimination response, the certified-graph Mason response, the generic
  N5/Mason specialization, independent S-06 anchors, and a miswired-edge negative control.
- Slice 2b adds exhaustive nonzero-feedback loop topology and a concrete singular N5 anchor.
- The topology implementation is mechanically split without moving any declaration out of
  `Optics.DCDR`. `Topology.lean` remains a compatibility re-export.
- `Physlib.lean` is never committed by this lane. The final gate temporarily registers every
  module below and restores the registry byte-identically.

## Files and registrations requested

Register these modules in sorted order in `Physlib.lean`:

- `Physlib.Optics.Systems.DCDR.Bridge`
- `Physlib.Optics.Systems.DCDR.Graph`
- `Physlib.Optics.Systems.DCDR.Mason`
- `Physlib.Optics.Systems.DCDR.Netlist`
- `Physlib.Optics.Systems.DCDR.Response`
- `Physlib.Optics.Systems.DCDR.ResponseRegression`
- `Physlib.Optics.Systems.DCDR.Topology`
- `Physlib.Optics.Systems.DCDR.TopologyRegression`

Files in the cutoff:

- `Physlib/Optics/Systems/DCDR/Netlist.lean` (418 lines)
- `Physlib/Optics/Systems/DCDR/Graph.lean` (347 lines)
- `Physlib/Optics/Systems/DCDR/Bridge.lean` (1362 lines)
- `Physlib/Optics/Systems/DCDR/Topology.lean` (46-line compatibility façade)
- `Physlib/Optics/Systems/DCDR/TopologyRegression.lean` (451 lines)
- `Physlib/Optics/Systems/DCDR/Response.lean` (545 lines)
- `Physlib/Optics/Systems/DCDR/Mason.lean` (208 lines)
- `Physlib/Optics/Systems/DCDR/ResponseRegression.lean` (1396 lines)

Every DCDR Lean file is below the 1500-line `ERR_NUM_LIN` cap.

## Goal text and row status

This slice supplies the DCDR instance of the quoted S7 suite requirement:

> at least one signal-flow/Mason derivation proved equal to network elimination

It satisfies the literal S-06 row:

> the audited eight-node DCDR response agrees between elimination and Mason gain

It satisfies the literal G-04 row:

> DCDR Mason response equals the independently compiled elimination response

The positive S-06 fixture computes N5 elimination and edge-level Mason enumeration independently.
The negative control swaps two launch-edge sources and proves that its Mason response does not
equal the unchanged N5 response.

Slice 2b takes reviewer option 1(b). Its nonzero-feedback point has loop gains `-1` and `2`.
It proves that every nonempty loop refinement contains edge seven, enumerates exactly two return
stems, identifies the two closed edge lists, and proves that their node sets intersect at
`{1, 6}`. Their signed determinant expansion is `1 - (-1) - 2 = 0`, matching the raw N5
denominator. A raw nonzero homogeneous complete N5 state directly disproves functional
well-posedness without either production gate iff.

This slice does not satisfy S-07:

> DCDR pole/zero/stability theorems include the audited unstable parameter case

It also does not satisfy X-01:

> one ring and one DCDR satisfy the full relational/compiled/chain/feedback/Mason/Z
> cross-semantics equality on the common domain

Only relational/N5 and Mason response layers are present here; delay-variable, recurrence/Z,
pole, zero, stability, and observable layers remain for later slices.

## Semantic summary

### N5 elimination

`eliminationResponse` selects the external output/input entry of the behavior-derived
`FlatNetlist.responseTransform`. `isWellPosed_iff` proves that N5 well-posedness is exactly
`Parameters.HasNonzeroDenominator`. A zero denominator constructs a nonzero homogeneous graph
state and therefore cannot use the response transform.

`eliminationResponse_eq_transfer` derives the selected response by opening the complete netlist
behavior, projecting its raw scattering/routing equations, and solving the eight forward
coordinates. The algebraic quotient `transfer` remains totalized; its response meaning is gated.

### Mason response and G-04

`auditedMasonResponse` is the edge-level quotient of the certified eight-node, eleven-edge
multigraph. `auditedSignalFlowGraph_graphDet_ne_zero_iff` proves that its graph determinant has
the same exact scalar gate. `auditedMasonResponse_eq_transfer` applies the existing edge-level
Mason theorem and reads the output of the audited node solution.

`masonResponse` selects the same external entry from the complete netlist-extracted
`FlatNetlist.masonResponseTransform`. `masonResponse_eq_eliminationResponse` is only an
entrywise instantiation of the merged generic
`FlatNetlist.responseTransform_eq_masonResponseTransform`; no generic bridge is reproved.

### Independent regression anchors

At `ResponseRegression.lean:87-149`, the N5 anchor opens
`toBehavior_responseTransform`, obtains raw scattering and assembly witnesses, and solves all
eight projected equations to `-163`. It never uses `eliminationResponse_eq_transfer`.

At `ResponseRegression.lean:154-554`, the Mason anchor proves every nonempty loop refinement
contains zero-gain feedback edge seven, classifies all supported forward paths, identifies their
edge refinements, and multiplies their gains. It obtains numerator and quotient `-163` without
`masonGain_eq_gain`, `edgeMasonGain_eq_gain`, or an elimination theorem.

At `ResponseRegression.lean:568-1001`, the negative control swaps the first-coupler launch-edge
sources. Direct enumeration gives `-347 * I`, and
`responseRegression_swappedEdge_fails_s06` proves inequality with the unchanged N5 value.

At `ResponseRegression.lean:1006-1390`, the nonzero-feedback fixture enumerates the only two
simple loop stems, closes them through edge seven, computes gains `-1` and `2`, proves the
cycles touch, and records the signed edge-determinant expansion. The state
`[0, 1, -I, 1, 2, -I, 1, -3I]` satisfies all eight homogeneous equations, lifts to a raw
nonzero complete N5 realization, and directly contradicts single-valuedness.

## Complete declaration inventory

All public names below remain in namespace `Optics.DCDR`; private and local declarations are
marked. Line numbers are for this cutoff tree. The topology split changes module ownership only;
declaration names and namespaces are unchanged.

### Netlist.lean

- `Parameters` (line 59)
- `Parameters.upperCoefficient` (line 72)
- `Parameters.lowerCoefficient` (line 76)
- `Parameters.feedbackCoefficient` (line 80)
- `Component` (line 84)
- anonymous instance (line 93)
- `componentPortFamily` (line 99)
- `componentScattering` (line 107)
- `components` (line 116)
- `Connection` (line 122)
- anonymous instance (line 132)
- `connections` (line 139)
- `netlist` (line 179)
- `localChannelFintype` (line 185)
- `localChannelDecidableEq` (line 195)
- `componentsLocalChannelFintype` (line 205)
- `componentsLocalChannelDecidableEq` (line 212)
- `componentsChannelFintype` (line 219)
- `componentsChannelDecidableEq` (line 227)
- `netlistComponentFintype` (line 231)
- `netlistComponentDecidableEq` (line 237)
- `netlistLocalChannelFintype` (line 243)
- `netlistLocalChannelDecidableEq` (line 250)
- `channelFintype` (line 257)
- `channelDecidableEq` (line 264)
- `connectionLocalChannelFintype` (line 268)
- `connectedChannelFintype` (line 274)
- `connectedChannelDecidableEq` (line 280)
- `firstCouplerChannel` (line 286)
- `secondCouplerChannel` (line 291)
- `upperPathChannel` (line 296)
- `lowerPathChannel` (line 301)
- `feedbackPathChannel` (line 306)
- `firstCoupler_leftFirst_not_connected` (line 311)
- `secondCoupler_rightFirst_not_connected` (line 319)
- `inputChannel` (line 327)
- `outputChannel` (line 332)
- `inputChannel_ne_outputChannel` (line 337)
- `externalChannel_eq_input_or_output` (line 344)
- `externalChannelOfFin` (line 365)
- `externalChannelEquiv` (line 369)
- `externalChannelFintype` (line 384)
- `externalChannel_card` (line 389)
- `inputAmplitude` (line 395)
- `inputAmplitude_apply_input` (line 401)
- `inputAmplitude_apply_output` (line 407)

### Graph.lean

- `Node` (line 54)
- `node_card` (line 57)
- `Edge` (line 60)
- `edgeSource` (line 63)
- `edgeTarget` (line 66)
- `edgeGain` (line 69)
- `edgeN7InputChannel` (line 83)
- `edgeN7OutputChannel` (line 108)
- `directionalCoupler_forwardScatteringEntries` (private) (line 133)
- `matchedPropagation_forwardScatteringEntry` (private) (line 156)
- `edgeGain_eq_n7ScatteringEntry` (line 169)
- `signalMultigraph` (line 278)
- `coefficientMatrix` (line 285)
- `signalFlowGraph` (line 289)
- `terminatedMultigraph` (line 293)
- `edge_card` (line 300)
- `terminatedMultigraph_terminals` (line 303)
- `signalFlowGraph_eq_coefficientMatrix` (line 308)
- `displayedCoefficientMatrix` (line 312)
- `coefficientMatrix_eq_displayed` (line 327)

### Bridge.lean

- `firstCoupler_physicalBehavior_of_scatteringEquation` (line 53)
- `secondCoupler_physicalBehavior_of_scatteringEquation` (line 83)
- `upperPath_physicalBehavior_of_scatteringEquation` (line 113)
- `lowerPath_physicalBehavior_of_scatteringEquation` (line 143)
- `feedbackPath_physicalBehavior_of_scatteringEquation` (line 173)
- `scatteringEquation_firstCoupler_leftFirst` (line 203)
- `scatteringEquation_firstCoupler_leftSecond` (line 236)
- `scatteringEquation_secondCoupler_leftFirst` (line 269)
- `scatteringEquation_secondCoupler_leftSecond` (line 302)
- `scatteringEquation_upperPath_left` (line 335)
- `scatteringEquation_lowerPath_left` (line 357)
- `scatteringEquation_feedbackPath_left` (line 379)
- `scatteringEquation_firstCoupler_rightFirst` (line 401)
- `scatteringEquation_firstCoupler_rightSecond` (line 434)
- `scatteringEquation_secondCoupler_rightFirst` (line 467)
- `scatteringEquation_secondCoupler_rightSecond` (line 500)
- `scatteringEquation_upperPath_right` (line 533)
- `scatteringEquation_lowerPath_right` (line 555)
- `scatteringEquation_feedbackPath_right` (line 577)
- `incidentAssembly_apply_input` (line 599)
- `incidentAssembly_apply_output` (line 610)
- `incidentAssembly_apply_firstCoupler_rightFirst` (line 621)
- `incidentAssembly_apply_firstCoupler_rightSecond` (line 636)
- `incidentAssembly_apply_secondCoupler_rightSecond` (line 651)
- `incidentAssembly_apply_upperPath_right` (line 666)
- `incidentAssembly_apply_lowerPath_right` (line 681)
- `incidentAssembly_apply_feedbackPath_right` (line 696)
- `incidentAssembly_apply_upperPath_left` (line 711)
- `incidentAssembly_apply_secondCoupler_leftFirst` (line 726)
- `incidentAssembly_apply_lowerPath_left` (line 741)
- `incidentAssembly_apply_secondCoupler_leftSecond` (line 756)
- `incidentAssembly_apply_feedbackPath_left` (line 771)
- `incidentAssembly_apply_firstCoupler_leftSecond` (line 786)
- `forwardState` (line 806)
- `signalInput` (line 827)
- `liftedIncident` (line 835)
- `liftedOutgoing` (line 859)
- `liftedIncident_apply_edgeN7Input` (line 879)
- `liftedOutgoing_apply_edgeN7Output` (line 887)
- `ForwardEquations` (line 895)
- `liftedOutgoing_eq_scatteringTransform` (line 922)
- `liftedIncident_eq_incidentAssembly` (line 1019)
- `forwardState_lifted` (line 1129)
- `isNodeSolution_iff_forwardEquations` (line 1136)
- `upperCoordinate_of_netlistEquations` (line 1189)
- `lowerCoordinate_of_netlistEquations` (line 1218)
- `feedbackCoordinate_of_netlistEquations` (line 1247)
- `forwardEquations_of_netlistEquations` (line 1277)
- `forwardState_isNodeSolution_of_netlistEquations` (line 1314)
- `isNodeSolution_iff_exists_netlistRealization` (line 1333)

### Topology.lean

- No declarations; compatibility re-export only.

### TopologyRegression.lean

- `topologyRegressionParameters` (line 72)
- `topologyRegression_pathCoefficients` (line 90)
- `topologyRegression_connectionEndpoints` (line 100)
- `topologyRegression_edgeSources` (line 140)
- `topologyRegression_edgeTargets` (line 144)
- `topologyRegression_firstUpper` (line 150)
- `topologyRegression_feedback` (line 163)
- `topologyRegression_output_fromLower` (line 178)
- `topologyRegression_output_fromUpper` (line 193)
- `topologyRegression_output_orientation` (line 206)
- `topologyProjectionParameters` (line 217)
- `topologyProjectionState` (line 235)
- `topologyProjectionState_coordinates` (line 239)
- `topologyProjection_edgeGains` (line 251)
- `topologyProjection_n7Entries` (line 265)
- `topologyProjection_forwardEquations` (line 277)
- `topologyProjection_isNodeSolution` (line 292)
- `topologyProjection_exists_netlistRealization` (line 300)
- `topologySwappedConnections` (line 316)
- `topologySwappedNetlist` (line 356)
- `topologySwappedConnectionLocalChannelFintype` (line 362)
- `topologySwappedChannelFintype` (line 368)
- `topologySwappedChannelDecidableEq` (line 374)
- `topologySwappedConnectedChannelFintype` (line 378)
- `topologySwappedConnectedChannelDecidableEq` (line 384)
- `topologySwappedInputAmplitude` (line 388)
- `topologySwapped_incidentAssembly_apply_upperPath_left` (line 396)
- `topologyProjection_swappedNetlist_rejects_productionLift` (line 412)

### Response.lean

- `responseExternalChannelFintype` (local) (line 63)
- `Parameters.loopGain` (line 70)
- `Parameters.denominator` (line 78)
- `Parameters.HasNonzeroDenominator` (line 81)
- `Parameters.feedbackDrive` (line 84)
- `Parameters.directGain` (line 92)
- `Parameters.feedbackReadoutGain` (line 99)
- `Parameters.responseNumerator` (line 106)
- `transfer` (line 113)
- `Parameters.reverse` (line 116)
- `Parameters.denominator_reverse` (line 124)
- `ForwardEquations.eq_zero` (line 141)
- `reverseState` (line 178)
- `reverseUpperCoordinate_of_netlistEquations` (line 199)
- `reverseLowerCoordinate_of_netlistEquations` (line 223)
- `reverseFeedbackCoordinate_of_netlistEquations` (line 247)
- `reverseEquations_of_netlistEquations` (line 271)
- `feedbackFixedPoint_eq_zero` (line 304)
- `isWellPosed_of_hasNonzeroDenominator` (line 365)
- `singularForwardState` (line 381)
- `singularForwardState_isNodeSolution` (line 397)
- `singularForwardState_ne_zero` (line 410)
- `not_isWellPosed_of_denominator_eq_zero` (line 416)
- `isWellPosed_iff` (line 436)
- `eliminationResponse` (line 446)
- `outputReadout_apply_output` (line 452)
- `responseTransform_apply_inputAmplitude` (line 463)
- `ForwardEquations.output_eq_transfer` (line 472)
- `eliminationResponse_eq_transfer` (line 515)

### Mason.lean

- `auditedMasonResponse` (line 68)
- `masonResponse` (line 73)
- `signalInput_one_eq_single` (line 80)
- `auditedSignalFlowGraph_graphDet_ne_zero_of_hasNonzeroDenominator` (line 86)
- `auditedSignalFlowGraph_graphDet_eq_zero_of_denominator_eq_zero` (line 109)
- `auditedSignalFlowGraph_graphDet_ne_zero_iff` (line 123)
- `auditedMasonResponse_eq_transfer` (line 133)
- `feedbackSignalFlowGraph_graphDet_ne_zero_iff` (line 166)
- `masonResponse_eq_eliminationResponse` (line 178)
- `auditedMasonResponse_eq_eliminationResponse` (line 189)
- `auditedMasonResponse_eq_masonResponse` (line 198)

### ResponseRegression.lean

- `responseRegressionExternalChannelFintype` (local) (line 70)
- `topologyProjection_hasNonzeroDenominator` (line 77)
- `responseRegression_eliminationResponse` (line 87)
- `responseRegressionNodeRank` (line 154)
- `responseRegressionNodeRank_lt` (line 157)
- `responseRegression_edgeChoice_contains_feedbackEdge` (line 164)
- `topologyProjection_feedbackEdgeGain` (line 190)
- `responseRegression_edgeFamilyGain_eq_zero` (line 195)
- `responseRegression_edgeGraphDetOn` (line 210)
- `responseRegression_edgeGraphDet` (line 238)
- `responseRegressionSupportedForwardPaths` (line 245)
- `responseRegressionAdjacent` (line 250)
- `responseRegression_refiningEdgeLists_nonempty_iff_isChain` (line 254)
- `responseRegression_adjacent_zero` (line 279)
- `responseRegression_adjacent_two` (line 284)
- `responseRegression_adjacent_three` (line 289)
- `responseRegression_adjacent_four` (line 294)
- `responseRegression_adjacent_five` (line 299)
- `responseRegression_adjacent_six` (line 304)
- `responseRegression_adjacent_one` (line 309)
- `responseRegression_not_adjacent_seven` (line 314)
- `responseRegression_chain_from_seven_eq_singleton` (line 319)
- `responseRegression_upperPath_cases` (line 327)
- `responseRegression_lowerPath_cases` (line 369)
- `responseRegression_supportedForwardPath_cases` (line 411)
- `responseRegression_supportedForwardPaths` (line 440)
- `responseRegression_refiningEdges_upper` (line 460)
- `responseRegression_refiningEdges_lower` (line 466)
- `responseRegression_refiningEdges_upperReturn` (line 472)
- `responseRegression_refiningEdges_lowerReturn` (line 478)
- `responseRegression_edgeMasonNumerator_eq_supportedSum` (line 484)
- `responseRegression_edgeListGain_upper` (line 504)
- `responseRegression_edgeListGain_lower` (line 512)
- `responseRegression_edgeListGain_upperReturn` (line 521)
- `responseRegression_edgeListGain_lowerReturn` (line 527)
- `responseRegression_edgeMasonNumerator` (line 533)
- `responseRegression_auditedMasonResponse` (line 550)
- `responseRegression_s06` (line 557)
- `responseRegressionSwappedEdgeSource` (line 568)
- `responseRegressionSwappedMultigraph` (line 572)
- `responseRegression_swappedEdgeSource_ne` (line 578)
- `responseRegression_swappedNodeRank_lt` (line 586)
- `responseRegression_swappedEdgeChoice_contains_feedbackEdge` (line 594)
- `responseRegression_swappedEdgeFamilyGain_eq_zero` (line 620)
- `responseRegression_swappedEdgeGraphDetOn` (line 635)
- `responseRegression_swappedEdgeGraphDet` (line 661)
- `responseRegressionSwappedAdjacent` (line 666)
- `responseRegression_swappedRefiningEdgeLists_nonempty_iff_isChain` (line 670)
- `responseRegression_swappedAdjacent_zero` (line 695)
- `responseRegression_swappedAdjacent_two` (line 700)
- `responseRegression_swappedAdjacent_three` (line 705)
- `responseRegression_swappedAdjacent_four` (line 710)
- `responseRegression_swappedAdjacent_five` (line 715)
- `responseRegression_swappedAdjacent_six` (line 720)
- `responseRegression_swappedAdjacent_one` (line 725)
- `responseRegression_swappedNotAdjacent_seven` (line 730)
- `responseRegression_swappedChain_from_seven_eq_singleton` (line 735)
- `responseRegression_swappedUpperPath_cases` (line 743)
- `responseRegression_swappedLowerPath_cases` (line 787)
- `responseRegression_swappedSupportedForwardPath_cases` (line 831)
- `responseRegressionSwappedSupportedForwardPaths` (line 859)
- `responseRegression_swappedSupportedForwardPaths` (line 864)
- `responseRegression_swappedRefiningEdges_upper` (line 884)
- `responseRegression_swappedRefiningEdges_lower` (line 890)
- `responseRegression_swappedRefiningEdges_upperReturn` (line 896)
- `responseRegression_swappedRefiningEdges_lowerReturn` (line 902)
- `responseRegression_swappedEdgeMasonNumerator_eq_supportedSum` (line 908)
- `responseRegression_swappedEdgeListGain_upper` (line 926)
- `responseRegression_swappedEdgeListGain_lower` (line 935)
- `responseRegression_swappedEdgeListGain_upperReturn` (line 944)
- `responseRegression_swappedEdgeListGain_lowerReturn` (line 952)
- `responseRegression_swappedEdgeMasonNumerator` (line 960)
- `responseRegressionSwappedMasonResponse` (line 979)
- `responseRegression_swappedMasonResponse` (line 984)
- `responseRegression_swappedEdge_fails_s06` (line 992)
- `responseRegressionSingularParameters` (line 1006)
- `responseRegression_singularEdgeGains` (line 1024)
- `responseRegressionUpperLoop` (line 1036)
- `responseRegressionLowerLoop` (line 1039)
- `responseRegressionSingularLoopStems` (line 1042)
- `responseRegressionSingularAdjacent` (line 1047)
- `responseRegression_singularRefiningEdgeLists_nonempty_iff_isChain` (line 1051)
- `responseRegression_singularAdjacent_one` (line 1076)
- `responseRegression_singularAdjacent_two` (line 1081)
- `responseRegression_singularAdjacent_three` (line 1086)
- `responseRegression_singularAdjacent_four` (line 1091)
- `responseRegression_singularAdjacent_five` (line 1096)
- `responseRegression_singularAdjacent_six` (line 1101)
- `responseRegression_singularNotAdjacent_seven` (line 1106)
- `responseRegression_singularChain_from_seven_eq_singleton` (line 1111)
- `responseRegression_singularLoopStem_cases` (line 1119)
- `responseRegression_singularLoopStems` (line 1173)
- `responseRegression_singularEdgeChoice_contains_feedbackEdge` (line 1191)
- `responseRegression_singularUpperLoopEdges` (line 1218)
- `responseRegression_singularLowerLoopEdges` (line 1225)
- `responseRegression_singularLoops_touch` (line 1232)
- `responseRegression_singularUpperLoopGain` (line 1237)
- `responseRegression_singularLowerLoopGain` (line 1243)
- `responseRegression_singularLoopSum_eq_loopGain` (line 1249)
- `responseRegression_singularDenominator` (line 1262)
- `responseRegressionSingularState` (line 1271)
- `responseRegression_singularForwardEquations` (line 1275)
- `responseRegression_singularState_ne_zero` (line 1287)
- `responseRegression_singularIsNodeSolution` (line 1293)
- `responseRegression_singularEdgeGraphDet` (line 1305)
- `responseRegression_singularEdgeGraphDet_expansion` (line 1330)
- `responseRegression_singular_exists_raw_n5_state` (line 1342)
- `responseRegression_singular_not_isWellPosed` (line 1367)

## Exact validation bindings

The validation lane should bind at least these public names:

- `Optics.DCDR.netlist`
- `Optics.DCDR.signalMultigraph`
- `Optics.DCDR.edgeGain_eq_n7ScatteringEntry`
- `Optics.DCDR.isNodeSolution_iff_exists_netlistRealization`
- `Optics.DCDR.Parameters.denominator`
- `Optics.DCDR.Parameters.HasNonzeroDenominator`
- `Optics.DCDR.transfer`
- `Optics.DCDR.isWellPosed_iff`
- `Optics.DCDR.eliminationResponse`
- `Optics.DCDR.eliminationResponse_eq_transfer`
- `Optics.DCDR.auditedMasonResponse`
- `Optics.DCDR.masonResponse`
- `Optics.DCDR.auditedSignalFlowGraph_graphDet_ne_zero_iff`
- `Optics.DCDR.feedbackSignalFlowGraph_graphDet_ne_zero_iff`
- `Optics.DCDR.auditedMasonResponse_eq_transfer`
- `Optics.DCDR.masonResponse_eq_eliminationResponse`
- `Optics.DCDR.auditedMasonResponse_eq_eliminationResponse`
- `Optics.DCDR.auditedMasonResponse_eq_masonResponse`
- `Optics.DCDR.responseRegression_eliminationResponse`
- `Optics.DCDR.responseRegression_edgeMasonNumerator`
- `Optics.DCDR.responseRegression_s06`
- `Optics.DCDR.responseRegression_swappedMasonResponse`
- `Optics.DCDR.responseRegression_swappedEdge_fails_s06`
- `Optics.DCDR.responseRegression_singularLoopStems`
- `Optics.DCDR.responseRegression_singularEdgeChoice_contains_feedbackEdge`
- `Optics.DCDR.responseRegression_singularLoops_touch`
- `Optics.DCDR.responseRegression_singularLoopSum_eq_loopGain`
- `Optics.DCDR.responseRegression_singularEdgeGraphDet_expansion`
- `Optics.DCDR.responseRegression_singular_exists_raw_n5_state`
- `Optics.DCDR.responseRegression_singular_not_isWellPosed`

## Cross-module conventions and reused results

- `FlatNetlist.responseTransform` is the behavior-derived N5 transform at
  `Physlib/Optics/Network/FlatNetlistElimination.lean:442-445`. Its equality with the explicit
  four-factor block formula is at lines 466-470.
- `FlatNetlist.masonResponseTransform` is defined at
  `Physlib/Optics/Network/FlatNetlistMason.lean:168-173`. The generic typed transform equality
  `responseTransform_eq_masonResponseTransform` is at lines 175-182.
- The all-pass ring instance follows this same specialization pattern at
  `Physlib/Optics/Systems/Microring/AllPassMason.lean:144-172`.
- The edge-retaining transfer/Mason theorem is
  `TerminatedMultigraph.transfer_eq_edgeMason` at
  `Physlib/Mathematics/SignalFlowGraph/Terminated.lean:254-259`.
- `edgeGraphDetOn` and `edgeGraphDet` are the signed edge-family sums at
  `Physlib/Mathematics/SignalFlowGraph/EdgeEnumeration.lean:116-122`. Their identity with the
  system determinant is at lines 132-137. `edgeMasonNumerator` is defined at lines 213-215,
  and `edgeMasonGain_eq_gain` is the existing theorem at lines 227-230.
- The N7 cross coefficient is exactly `-Complex.I * crossAmplitude` at
  `Physlib/Optics/Components/DirectionalCoupler.lean:68-70`; the mixer order is at lines 72-76.
- Fixed-carrier path phase and transmission coefficients are defined at
  `Physlib/Optics/Components/MatchedPropagation.lean:93-103`.
- The certified edge provenance theorem is now at
  `Physlib/Optics/Systems/DCDR/Graph.lean:169-275`; the relational extraction equivalence is at
  `Physlib/Optics/Systems/DCDR/Bridge.lean:1333-1354`.
- `topologyProjection_n7Entries` is a numeric specialization of
  `edgeGain_eq_n7ScatteringEntry`, not an independent raw-transform expansion. This is stated
  at `Physlib/Optics/Systems/DCDR/TopologyRegression.lean:27-29`.
- The modal-power/flux bridge requires `IsApertureFluxOrthonormal`, defined with integrability,
  normalization, and orthogonality at
  `Physlib/Optics/HarmonicFlux/ModePower.lean:91-101`. Common frequency, Maxwell qualification,
  and aperture interpretation remain external requirements at lines 93-95; the outgoing bridge
  is at lines 161-170.

## Source-coherence correction

FMICS'15 says that its coherent DCDR treatment existed but was not printed. Coherent N7
`t`/`-I * k` is therefore the source's own unprinted coherent branch; the printed incoherent
`1 - k`/`k` model is a different case, compared only if reference [3] surfaces. The module
docs do not describe the coherent construction as a departure from the source.

## Totality and non-claims

- `transfer`, `auditedMasonResponse`, and `masonResponse` are totalized algebraic
  definitions. Their response equalities require `Parameters.HasNonzeroDenominator`.
- No infinite-series, contraction, summability, causality, time-domain, delay-variable,
  Z-transform, or region-of-convergence result is proved.
- No pole, zero, Schur/BIBO stability, source-named resonance, bandwidth, or audited unstable
  parameter result is proved.
- No passivity, losslessness, reciprocity, material realization, or electromagnetic-power claim
  is proved.
- Power means normalized modal power, not electromagnetic power before the separately gated
  aperture-flux bridge.
- The asymmetric numeric fixtures are hostile algebraic sentinels, not physical devices.
- No full X-01 DCDR cross-semantics theorem is claimed.
- No parity-ledger status is edited by this lane.
- The singular fixture proves failure of well-posedness only; it does not define a pole,
  instability, or time-domain response.

## Gate record

The exact controller sync target was `782ba5c7`, merged at `7d5b0aea`. The gated Lean source head
was `c6a2377f`. A final HANDOFF-only child records this result; no Lean source changed afterward.

After committing every DCDR source file, `./scripts/lint-style.sh` exited zero. It covered all
tracked Lean files, including `Netlist`, `Graph`, `Bridge`, `Topology`, `TopologyRegression`,
`Response`, `Mason`, and `ResponseRegression`. No DCDR file exceeds 1500 lines.

With the eight requested imports inserted temporarily in sorted order, this single locked command
exited zero:

```text
lake-lock env bash -c 'lake exe cache get &&
  lake --wfail build Physlib.Optics.Systems.DCDR.Netlist
    Physlib.Optics.Systems.DCDR.Graph
    Physlib.Optics.Systems.DCDR.Bridge
    Physlib.Optics.Systems.DCDR.Topology
    Physlib.Optics.Systems.DCDR.TopologyRegression
    Physlib.Optics.Systems.DCDR.Response
    Physlib.Optics.Systems.DCDR.Mason
    Physlib.Optics.Systems.DCDR.ResponseRegression &&
  lake exe runPhyslibLinters && lake exe lint_all'
```

The cache was current. The warnings-as-errors build passed. `runPhyslibLinters` passed for Physlib
and QuantumInfo. `lint_all` passed its build, file-registration, illegal-import, PhyslibAlpha
registration, duplicate-tag, sorry/pseudo-attribution, declaration-linter, and transitive-import
checks. Its advisory style and transitive-import inventories named only pre-existing non-DCDR
files.

`Physlib.lean` was restored byte-identically to SHA-256
`d6279000556c059e0a352aac530487e353adc7e5fa1f7c05b2bce229ec34f510` and has no diff.

## Slice 2b gate record

The exact controller sync target was `329d5a59`, merged at `fcfd057b`. The Lean repair is
`393be55e`; the committed head gated after its pre-gate handoff update was `706a99e1`. A final
HANDOFF-only child records this result; no Lean source changed after the gate.

Reviewer option 1(b) was used. At the concrete point where both couplers have through and cross
amplitudes `1`, the upper and lower transmissions are `1` and `2`, the feedback transmission is
`1`, and every phase is zero, the two loop gains are `-1` and `2`. Their signed edge determinant
and the raw N5 denominator are both `1 - (-1) - 2 = 0`. The explicit nonzero homogeneous state
is `[0, 1, -I, 1, 2, -I, 1, -3I]`.

After committing all source and pre-gate handoff changes, `./scripts/lint-style.sh` exited zero.
Every DCDR Lean file is below 1500 lines; `ResponseRegression.lean` is 1396 lines. The advisory
style inventory inside `lint_all` still printed repository formatting notices, including the
pre-existing split-file blank-line notices, but it is non-gating and the committed-state style
script above passed.

With the six split modules inserted temporarily beside the two registered compatibility imports,
this single locked command exited zero:

```text
lake-lock env bash -c 'lake exe cache get &&
  lake --wfail build Physlib.Optics.Systems.DCDR.Netlist
    Physlib.Optics.Systems.DCDR.Graph
    Physlib.Optics.Systems.DCDR.Bridge
    Physlib.Optics.Systems.DCDR.Topology
    Physlib.Optics.Systems.DCDR.TopologyRegression
    Physlib.Optics.Systems.DCDR.Response
    Physlib.Optics.Systems.DCDR.Mason
    Physlib.Optics.Systems.DCDR.ResponseRegression &&
  lake exe runPhyslibLinters && lake exe lint_all'
```

The cache was current. The warnings-as-errors build completed successfully with 2761 jobs.
`runPhyslibLinters` passed for Physlib and QuantumInfo. `lint_all` exited zero: its build,
illegal-import, PhyslibAlpha-registration, duplicate-tag, sorry/pseudo-attribution, declaration,
and transitive-import checks passed. Its file-registration advisory named only four unrelated
Microring modules, and its transitive-import advisory named no DCDR file.

`Physlib.lean` was restored byte-identically to SHA-256
`d6279000556c059e0a352aac530487e353adc7e5fa1f7c05b2bce229ec34f510` and has no diff.
