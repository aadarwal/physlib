# S7D DCDR slice 1 handoff

## Branch and cutoff scope

- Branch: `optics/s7d-dcdr`
- Worktree: `/Users/aadarwal/src/aadarwal/physlib-wt/optics-s7d-dcdr`
- This slice adds the explicit N7 DCDR netlist, the edge-indexed eight-node graph, the derivation of
  its forward equations from raw component and routing equations, and hostile topology regressions.
- The final synchronized development head and post-sync gate source head are recorded in the gate
  section below.
- `Physlib.lean` is not committed by this lane. The two modules were registered temporarily for
  the shipped registry linters and the file was restored byte-identically.

## Files and registrations requested

Register these modules in sorted order in `Physlib.lean`:

- `Physlib.Optics.Systems.DCDR.Topology`
- `Physlib.Optics.Systems.DCDR.TopologyRegression`

Files:

- `Physlib/Optics/Systems/DCDR/Topology.lean`
- `Physlib/Optics/Systems/DCDR/TopologyRegression.lean`

## Goal text and row status

This slice implements the literal first S7D bullet at `goal.md:2399-2402`:

> the human-audited eight-node, eleven-edge topology with parallel edges retained;

The graph retains edge identity with `Edge := Fin 11` even when gains coincide or vanish. The
source audit summarized at
`/Users/aadarwal/src/aadarwal/physlib-parity/HOL-CORPUS.md:304-324` identifies FMICS'15
Definition 8 as an explicitly listed eight-node, eleven-branch SFG. The corresponding ledger row
is IP-08 at
`/Users/aadarwal/src/aadarwal/physlib-parity/PARITY-LEDGER.md:115`.

This topology foundation contributes to, but does not satisfy, S-06 or G-04. Those rows require
independently compiled elimination and Mason responses (`goal.md:2591` and `:2602`). It does not
satisfy S-07, which requires pole/zero/stability results including the unstable case
(`goal.md:2592`), or X-01, which requires all six semantics on a common domain (`goal.md:2603`).
No parity-ledger status is changed by this slice.

## Production declaration inventory

All declarations below are in namespace `Optics.DCDR`.

### Parameters and physical construction

- `Parameters`
- `Parameters.upperCoefficient`
- `Parameters.lowerCoefficient`
- `Parameters.feedbackCoefficient`
- `Component`
- the `Fintype Component` instance
- `componentPortFamily`
- `componentScattering`
- `components`
- `Connection`
- the `Fintype Connection` instance
- `connections`
- `netlist`

The public instance declarations are:

- `localChannelFintype`
- `localChannelDecidableEq`
- `componentsLocalChannelFintype`
- `componentsLocalChannelDecidableEq`
- `componentsChannelFintype`
- `componentsChannelDecidableEq`
- `netlistComponentFintype`
- `netlistComponentDecidableEq`
- `netlistLocalChannelFintype`
- `netlistLocalChannelDecidableEq`
- `channelFintype`
- `channelDecidableEq`
- `connectionLocalChannelFintype`
- `connectedChannelFintype`
- `connectedChannelDecidableEq`
- `externalChannelFintype`

### External channels and graph

- `firstCouplerChannel`
- `secondCouplerChannel`
- `upperPathChannel`
- `lowerPathChannel`
- `feedbackPathChannel`
- `firstCoupler_leftFirst_not_connected`
- `secondCoupler_rightFirst_not_connected`
- `inputChannel`
- `outputChannel`
- `inputChannel_ne_outputChannel`
- `inputAmplitude`
- `inputAmplitude_apply_input`
- `inputAmplitude_apply_output`
- `Node`
- `Edge`
- `edgeSource`
- `edgeTarget`
- `edgeGain`
- `signalMultigraph`
- `coefficientMatrix`
- `signalFlowGraph`
- `terminatedMultigraph`
- `edge_card`
- `terminatedMultigraph_terminals`
- `signalFlowGraph_eq_coefficientMatrix`
- `displayedCoefficientMatrix`
- `coefficientMatrix_eq_displayed`

### Netlist-to-graph derivation

- `firstCoupler_physicalBehavior_of_scatteringEquation`
- `secondCoupler_physicalBehavior_of_scatteringEquation`
- `upperPath_physicalBehavior_of_scatteringEquation`
- `lowerPath_physicalBehavior_of_scatteringEquation`
- `feedbackPath_physicalBehavior_of_scatteringEquation`
- `scatteringEquation_firstCoupler_rightFirst`
- `scatteringEquation_firstCoupler_rightSecond`
- `scatteringEquation_secondCoupler_rightFirst`
- `scatteringEquation_secondCoupler_rightSecond`
- `scatteringEquation_upperPath_right`
- `scatteringEquation_lowerPath_right`
- `scatteringEquation_feedbackPath_right`
- `incidentAssembly_apply_input`
- `incidentAssembly_apply_upperPath_left`
- `incidentAssembly_apply_secondCoupler_leftFirst`
- `incidentAssembly_apply_lowerPath_left`
- `incidentAssembly_apply_secondCoupler_leftSecond`
- `incidentAssembly_apply_feedbackPath_left`
- `incidentAssembly_apply_firstCoupler_leftSecond`
- `forwardState`
- `signalInput`
- `ForwardEquations`
- `isNodeSolution_iff_forwardEquations`
- `upperCoordinate_of_netlistEquations`
- `lowerCoordinate_of_netlistEquations`
- `feedbackCoordinate_of_netlistEquations`
- `forwardEquations_of_netlistEquations`
- `forwardState_isNodeSolution_of_netlistEquations`

## Regression declaration inventory

All declarations below are in namespace `Optics.DCDR`.

- `topologyRegressionParameters`
- `topologyRegression_pathCoefficients`
- `topologyRegression_connectionEndpoints`
- `topologyRegression_edgeSources`
- `topologyRegression_edgeTargets`
- `topologyRegression_firstUpper`
- `topologyRegression_feedback`
- `topologyRegression_output_fromLower`
- `topologyRegression_output_fromUpper`
- `topologyRegression_output_orientation`

The fixture uses unequal through amplitudes `2` and `5`, cross amplitudes `3` and `7`, and path
coefficients `11`, `13`, and `17`. Its matrix anchors enumerate `Multigraph.toMatrix` directly and
do not use `coefficientMatrix_eq_displayed`. The endpoint anchor separately expands all twelve
ends of the six physical wires. The values are deliberately outside any passive or unitary gate.

## Exact validation bindings

The validation lane should bind at least these public names:

- `Optics.DCDR.netlist`
- `Optics.DCDR.connections`
- `Optics.DCDR.inputChannel`
- `Optics.DCDR.outputChannel`
- `Optics.DCDR.edgeSource`
- `Optics.DCDR.edgeTarget`
- `Optics.DCDR.edgeGain`
- `Optics.DCDR.signalMultigraph`
- `Optics.DCDR.terminatedMultigraph`
- `Optics.DCDR.edge_card`
- `Optics.DCDR.terminatedMultigraph_terminals`
- `Optics.DCDR.coefficientMatrix_eq_displayed`
- `Optics.DCDR.isNodeSolution_iff_forwardEquations`
- `Optics.DCDR.forwardState_isNodeSolution_of_netlistEquations`
- `Optics.DCDR.topologyRegression_connectionEndpoints`
- `Optics.DCDR.topologyRegression_edgeSources`
- `Optics.DCDR.topologyRegression_edgeTargets`
- `Optics.DCDR.topologyRegression_firstUpper`
- `Optics.DCDR.topologyRegression_feedback`
- `Optics.DCDR.topologyRegression_output_fromLower`
- `Optics.DCDR.topologyRegression_output_fromUpper`
- `Optics.DCDR.topologyRegression_output_orientation`

## Cross-module conventions and reused results

- `DirectionalCoupler.Parameters` stores real through and cross modal-amplitude parameters at
  `Physlib/Optics/Components/DirectionalCoupler.lean:61-66`. Its cross coefficient is exactly
  `-Complex.I * crossAmplitude` at lines 68-70, and the displayed mixer order is pinned at lines
  72-76.
- `MatchedPropagation.Parameters` stores a normalized modal-amplitude factor and fixed-carrier
  path phase at `Physlib/Optics/Components/MatchedPropagation.lean:71-83`. The phase and common
  transmission coefficients are defined at lines 93-103.
- The component-owned physical endpoint adapters and their exact realization lemmas are at
  `Physlib/Optics/Components/DirectionalCouplerPhysical.lean:144-182` and
  `Physlib/Optics/Components/MatchedPropagationPhysical.lean:150-189`.
- `FlatNetlist.scatteringTransform` is the block-diagonal component law, with same-component and
  different-component entries at `Physlib/Optics/Network/FlatNetlist.lean:140-165`.
- Connected and external incident-assembly coordinates are stated at
  `Physlib/Optics/Network/ExternalChannel.lean:663-712`. These are the routing equations used to
  derive the forward coordinates.
- A coefficient matrix already in `x = A x + b` form is accepted unchanged by
  `ofCoefficientMatrix` at `Physlib/Mathematics/SignalFlowGraph/Extraction.lean:95-97`.
- `Multigraph` retains source, target, and gain per edge at
  `Physlib/Mathematics/SignalFlowGraph/Extraction.lean:136-147`; its matrix sums all edges between
  an ordered node pair at lines 175-183.
- `TerminatedMultigraph` retains edge identity and distinguished terminals, while its transfer is
  the scalar matrix gain, at `Physlib/Mathematics/SignalFlowGraph/Terminated.lean:227-241`.
- The formal aperture-flux bridge requires a finite mode family satisfying
  `IsApertureFluxOrthonormal`, defined at `Physlib/Optics/HarmonicFlux/ModePower.lean:91-101`.
  Its contract states that common carrier frequency, Maxwell qualification, and aperture
  interpretation are external requirements at lines 93-95; the outgoing modal-power conclusion
  is at lines 161-170.

## Convention split and totality

- This slice is coherent and fixed-carrier. Its N7 field coefficients are `t` and `-I*k`; it does
  not identify them with FMICS'15's incoherent branch coefficients `1-k` and `k`.
- The complete N7 `FlatNetlist` is bidirectional. The eight-node graph records only selected
  forward boundary coordinates. It is not claimed equal to the complete `C * S` feedback graph,
  which also contains reverse-direction and propagation-component boundary coordinates.
- `Parameters`, the netlist, and all graph objects are total. No determinant, inverse, response,
  or well-posedness claim is made in this slice.
- `forwardState_isNodeSolution_of_netlistEquations` is conditional on the raw component scattering
  equation and incident-assembly equation. It does not infer network behavior membership or
  functional solvability by itself.

## Non-claims

- No elimination response, Mason response, or equality between those responses is proved.
- No source transfer formula or incoherent source-parameter bridge is proved.
- No active/passive, lossless, reciprocal, unit-delay, or multiple-delay specialization is proved.
- No power, coherency transport, or electromagnetic-flux interpretation is proved.
- No pole, zero, stability, source-named "resonance", bandwidth, or unstable-parameter result is
  proved.
- No causal, time-domain, Z-transform, chain, or full X-01 semantics result is proved.
- The hostile regression values are algebraic sentinels, not a physical device realization.

## Gate record

The slice is synchronized through development head `e52d83b7` by merge head `75bd0989`. At that
post-sync source head, this single locked command exited successfully with temporary sorted
registrations:

```text
lake-lock env bash -c 'lake exe cache get &&
  lake --wfail build Physlib.Optics.Systems.DCDR.Topology
    Physlib.Optics.Systems.DCDR.TopologyRegression &&
  lake exe runPhyslibLinters && lake exe lint_all'
```

Both DCDR modules built with warnings as errors. `runPhyslibLinters` passed for Physlib and
QuantumInfo. `lint_all` exited zero after its build, registry, legal-import, duplicate-tag,
sorry/pseudo-attribution, declaration-linter, and transitive-import checks. Its advisory style and
transitive-import inventories named only pre-existing files, with neither DCDR module present.
The file-import inventory named four unregistered development-side thin-cell modules and neither
DCDR module. `Physlib.lean` was then restored byte-identically to SHA-256
`9b7092d5e30e9c9c618e07892d20d2f45535c4d259f5280946bad68234aba787`.

After the Lean changes were committed, `./scripts/lint-style.sh` named only synchronized
development-side findings in
`Physlib/Electromagnetism/ThreeDimension/BoundaryConditions/OneSidedTraceRegression.lean:176`
and `:189`; neither DCDR module was named.
