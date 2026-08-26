# S7C slice 7: matched-gauge connection-routing covariance

## Cutoff and synchronization

This slice is based exactly on controller-authorized registered head
`5772103ba77a01e23bc72a367b53260ce3dd8a14`; no mid-slice synchronization was performed. The
exact II fix-up gated source is `8d32bfc4a5f916bbe8f816b065bf57aff61ce81a`. The cutoff is its
HANDOFF-only child. The repair changes only the regression module; every production file and
`Physlib.lean` remain byte-identical to source `019bcedceea51da519ea2f3278029d2fb620144f`.

## Scope and classification

The controlling text at `goal.md:1937-1938` on the cutoff says:

> matched-gauge covariance of connection routing under channel-end rephasing; arbitrary
> independent endpoint rephasings do not leave a unit-gain wire unchanged;

This neutral Network slice discharges that item and targets ledger row N-07 (`goal.md:2612`),
whose failure mode is index- or convention-dependent behavior. The registered N-08 three-stage
hierarchy is the downstream canary. Every result introduced here is a `lemma`; no declaration is
presented as a printed physics theorem.

## Authorized files

The exact changes are the three authorized new files:

- `Physlib/Optics/Network/ConnectionRoutingRephase.lean` (387 lines);
- `Physlib/Optics/Network/FlatNetlistRephase.lean` (498 lines); and
- `Physlib/Optics/Network/FlatNetlistRephaseRegression.lean` (617 lines).

No pre-existing Network or Mode file changed. Production imports no regression module.

## Channel-end routing covariance

`ChannelEndGauge` at `ConnectionRoutingRephase.lean:66` assigns independent unit-complex phases
to incident and outgoing presentations of every ambient channel.
`PortConnectionFamily.connectedGauge`, `externalGauge`, and `IsMatchedGauge` are at lines 104,
109, and 115. Matching is the exact directed mate condition: the incident phase at every routed
target equals the outgoing phase at its stored source.

`idealRouting_rephase_eq_iff` at line 127 proves the exact iff: conjugating connected unit-gain
routing by the two endpoint gauges leaves it unchanged exactly under mate matching.
`idealRouting_rephase_eq` is at line 183. Ambient partial-routing covariance and its converse
criterion are at lines 196 and 220; coordinate action is at line 261.

The external-boundary covariance API consists of `externalIncidentInjection_rephase_eq` at line
280, `externalOutgoingReadout_rephase_eq` at line 301, and the readout action at line 322.
`incidentAssembly_rephase` at line 342 joins connected routing and external injection without a
solver or physical hypothesis.

## Singular-safe, flat, response, and hierarchy lifts

`LinearBehavior.rephase`, its equality congruence, membership characterization, inverse
cancellation, and functionality transport are at `FlatNetlistRephase.lean:82`, `:92`, `:100`,
`:133`, and `:141`. `ModeTransform.toBehavior_rephase` is at line 162.

`PortConnectionFamily.closeBehavior_rephase` at line 209 proves singular-safe closure covariance.
Its hypotheses are only finite channel structure and the explicit `IsMatchedGauge`; no existence,
uniqueness, determinant, functionality, or well-posedness hypothesis is present.

The component and external rephased relations are defined at lines 282 and 288.
`FlatNetlist.rephasedBehavior_eq` at line 294 identifies the complete external relation with the
covariantly rephased original behavior. `toBehavior_rephase_responseTransform` at line 343 proves
the corresponding graph identity. `rephasedResponseTransform` and
`rephasedResponseTransform_eq` are at lines 359 and 370; both name the original netlist's existing
`hWellPosed` gate, and no response transform is claimed outside that domain.

For the N-08 downstream canary, `boundaryGauge` is at line 402 and
`isMatchedGauge_append_iff` at line 411 proves that flattened matching is exactly inner matching
plus matching of the induced outer-boundary gauge. `closeBehavior_append_rephase_eq_staged` at
line 477 composes singular-safe covariance with the registered hierarchical flattening identity;
it adds no well-posedness assumption.

## Dynamic N-07 / N-08 regression

The positive gauge uses the two distinct non-real phases `I` and `-I`
(`FlatNetlistRephaseRegression.lean:86-95`). The independently declared component operator has
forward gains `2I`, `-3`, `-5`, and `-7` at line 152.
`routingRephaseRegression_componentOperator_eq_rephase` at line 170 proves by all finite matrix
entries that it is exactly the primitive rephase of `reuseRegressionComponentOperator` by the
declared incident and outgoing gauges; no routing or netlist covariance result is used.

The hand-expanded incident west coordinates are `1`, `2I`, `-6I`, and `30I`; the outgoing east
coordinates are `2I`, `-6I`, `30I`, and `-210I` at lines 188-209. The coordinatewise primitive
provenance equalities are `routingRephaseRegression_incident_eq_rephase` at line 212 and
`routingRephaseRegression_outgoing_eq_rephase` at line 226. Component scattering is expanded from
`Matrix.mulVec`, finite sums, and those primitives at line 256. The three routed cross amplitudes
are proved nonzero at line 275.

The right-associated raw assembly/readout/closure are proved independently at lines 290, 347,
and 360. The left-associated versions are at lines 378, 435, and 448.
`routingRephaseRegression_mem_both_parenthesizations` at line 466 joins the two raw solutions and
pins their common external response to `-210I`. None of these proofs invokes a routing/closure
covariance or hierarchical associativity lemma under test; the declaration-name grep is empty.

The hostile gauge at line 496 changes only the second-west incident endpoint from `I` to `1`; the
connected first-east outgoing source remains at `I`. It is proved not mate-matched at line 510.
`routingRephaseRegression_hostile_incident_eq_rephase` at line 533 proves directly that the hostile
state is the primitive rephasing of `reuseRegressionIncident`. At the mismatched routed direction,
`routingRephaseRegression_hostile_idealRouting_mate_entry` at line 548 expands the rephased ideal
routing coefficient to exactly `-I`.
`routingRephaseRegression_hostile_idealRouting_mate_entry_ne_one` at line 567 proves that this
coefficient is not one. The hostile proposed incident coordinate is exactly `2` at line 583, while
stored unit routing forces `2I` at line 589.
`routingRephaseRegression_hostile_incidentAssembly_ne` at line 603 proves the resulting inequality,
so inverse/conjugation, mate-direction, subsystem-boundary, port-lift, Sum-associator, and
cascade-index errors can change or reject this fixture.

## Non-claims

- No time-reversal, reciprocity, reference-plane, propagation, passivity, losslessness, stability,
  causality, frequency dependence, physical realization, or electromagnetic-power claim is made.
- A gauge is a passive coordinate change, not a propagation component or a claim that
  independently rephasing one end preserves a physical wire.
- Response-transform covariance is asserted only under the named existing
  `FlatNetlist.IsWellPosed` hypothesis; singular-safe relation covariance does not assume it.
- The three other open Network bullets quoted in the Slice 7 proposal remain open. No
  source-parity claim is made.
- Regression coefficients are algebraic sentinels, not normalized physical couplers. Human
  verification remains required by `AI-POLICY.md`.

## Reviewer map

1. Read `ConnectionRoutingRephase.lean:66-188` for the gauge and exact ideal-routing iff.
2. Read `ConnectionRoutingRephase.lean:192-387` for ambient and boundary covariance.
3. Read `FlatNetlistRephase.lean:71-267` for relation and singular-safe closure covariance.
4. Read `FlatNetlistRephase.lean:270-388` for behavior and gated response.
5. Read `FlatNetlistRephase.lean:391-498` for hierarchical matching and flattening.
6. Read `FlatNetlistRephaseRegression.lean:140-489` for primitive positive provenance and both
   independently expanded positive raw solutions.
7. Read `FlatNetlistRephaseRegression.lean:490-617` for hostile-state provenance, the exact `-I`
   mate entry, and the raw one-end negative control.

## Exact validation record

The original source head `019bcedceea51da519ea2f3278029d2fb620144f` passed the complete Slice 7
battery recorded in cutoff `7d2421fb9f9943bc979e2088ab2f1c86a2df9115`. The exact II fix-up
source `8d32bfc4a5f916bbe8f816b065bf57aff61ce81a` was then tested under `lake-lock`, with temporary
registration of the same three Slice 7 modules for declaration linters.

Results:

- direct elaboration of `FlatNetlistRephaseRegression.lean`: passed without warnings after removal
  of one redundant trailing tactic;
- targeted build of `Physlib.Optics.Network.FlatNetlistRephaseRegression`: passed, 2734 jobs;
- `runPhyslibLinters`: Physlib and QuantumInfo passed, including `simpNF`;
- committed-state `lint-style.sh`: passed;
- `git diff --check`: passed;
- file line counts are 387, 498, and 617, all below 1500;
- no current Lean file exceeds 100 Unicode codepoints per line;
- no current Lean file contains a `theorem` declaration, `sorry`, `axiom`, `native_decide`,
  `maxHeartbeats`, or `Lean.ofReduceBool`;
- production imports no regression module; and
- the regression contains no invocation of `idealRouting_rephase_eq_iff`,
  `incidentAssembly_rephase`, a routing/closure covariance lemma, or an associativity lemma under
  test.

Temporary registration was restored byte-identically. `Physlib.lean` had SHA-256
`4b7b024391d123ee25eb527930b8bf69d93c9f0e7346a2b96089625bc555e004` before and after the gate.
This final cutoff child changes only `HANDOFF.md`.
