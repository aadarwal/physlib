# S9 slice 1 cutoff: CROW demonstrator

## Cutoff identity

- Branch: `optics/s9-demo`
- Initial assigned base: `e24b21cb`
- Named battery-green sync target: `b8ef3236`
- Sync merge: `d7526554`
- Gated source ref: `9cd8083708cd2431a1e06c23c3d75eadf030fea0`
- Worktree: `/Users/aadarwal/src/aadarwal/physlib-wt/optics-s9-demo`

The source ref above contains all Lean and convention-map content. This handoff is a documentation-
only child. The controller still owns hostile review, merge, permanent registration, the full
battery, and any ledger change.

## Files and requested registration

- `Physlib/Optics/Examples/CROW.lean` — 534 lines; production construction and generic spine.
- `Physlib/Optics/Examples/CROWRegression.lean` — 1523 lines; exact two-ring regression.
- `Physlib/Optics/Examples/CROWTable1ConventionMap.md` — 130 lines; slice-1B comparison contract.

Please add these sorted imports to `Physlib.lean` after hostile review:

```lean
public import Physlib.Optics.Examples.CROW
public import Physlib.Optics.Examples.CROWRegression
```

Production does not import regression. The mapping document is not a Lean module.

## Claim and evidence boundary

For every natural `ringCount`, `CROW.netlist` assembles `ringCount + 1` existing physical-port
directional couplers and two existing matched-propagation half-arcs per ring. Adjacent rings share
a coupler, and only the unused arms of the end couplers provide bus access. The topology is a
directly resonator-coupled CROW, not rings coupled independently to one common bus.

`CROW.generic_spine_agrees` is explicitly gated by `FlatNetlist.IsWellPosed`. It instantiates the
unchanged generic declarations for relational component closure, compiled elimination, and Mason
extraction. `CROW.netlist_eq_hierarchy_flatten` identifies the public flat netlist with the generic
hierarchy flattening, and `CROW.connections_assoc_transport` applies generic three-stage transport.
No CROW-specific eliminator, stored closed response, or topology-specific semantic bridge is added.

This is a generality/reuse claim. Heebner et al. already publish topology-specific CROW unit-cell
matrix entries. This slice shows that the same general typed-network solve also accepts this CROW
without adding a per-device elimination rule. It makes no stronger claim about published matrix
methods or about every possible product representation.

The corrected scope separates the generic theorem spine from system-specific transform-domain and
recurrence bridges. This slice proves only the former for CROW.

## Exact regression and independent anchors

The two-ring fixture uses end couplers `(3/5, 4/5)`, middle coupler `(5/13, 12/13)`, and zero-phase
half-arcs of amplitude `1/2`. The two Pythagorean identities are exact. The anchor is the explicit
primitive incident/outgoing table, expanded through component equations and routing before it is
shown to belong to the flat relation.

- The independently assembled selected output is `(768 / 4717) * I`.
- Compiled elimination returns that selected output on `crowRegression_isWellPosed`.
- Generic Mason extraction returns the same selected output through `generic_spine_agrees`.
- The deliberately wrong internal coordinate is `-1920 / 4717`, so it is unequal to the selected
  response. The sentinel pins coordinate selection only.
- The two displayed isolated-ring primitive factors reduce to `7/17` and `7/47`; their product is
  `49/799`. `crowResponse_ne_isolatedRingTransferProduct` compares the raw CROW witness with that
  expanded product and rejects equality by imaginary part. It does not invoke the response-value
  lemma under test.
- `crowRegression_firstIsolatedRingTransfer_eq_standard` and
  `crowRegression_secondIsolatedRingTransfer_eq_standard` identify those literals with
  `AllPass.standardThroughTransfer`; the corresponding `*_eq_allPass` lemmas certify the standard
  transfer through `AllPass.throughTransfer_eq_standard` using unitary couplers and nonzero
  denominators. The first factor is assigned the end coupler and the second the shared middle
  coupler as an explicit modelling choice.

The non-product result is qualified: it differs from this product of individual isolated-ring
factors. It does not rule out products of coupled unit-cell transfer matrices, which occur in the
published CROW literature.

## Heebner Table 1 status

**convention mapping written; numeric Table-1 parity deferred to slice 1B; NO verdict**

`Physlib/Optics/Examples/CROWTable1ConventionMap.md` was written after checking the primary PDF. It
pins the source `(A_j, B_j)` order, full- versus half-ring phase structure, the `+i` versus Physlib
`-i` coupler gauge, uniform bulk parameters, and finite end access. It also records that both exact
coupler pairs satisfy the source Pythagorean condition, while half-amplitude propagation does not
make the fixture globally lossless.

No comparison may run until slice 1B proves all four preconditions in the map:

1. a uniform Pythagorean coupler fixture with unit-amplitude propagation;
2. explicit finite left/right access matrices and end readout;
3. the full-phase and scattering-to-transfer coordinate conversion; and
4. consistent transport of the coupler gauge and internal-field extraction.

After those obligations, slice 1B must record which protocol outcome fired: agreement, ours-wrong,
or table-wrong. Every outcome is publishable evidence; disagreement is a finding to investigate.
No outcome has fired in slice 1.

## Measured API friction

### Counting scope

At gated source ref `9cd80837`, the count covers `CROW.lean` lines 77 through 528. It counts
nonblank, noncomment Lean source lines, including attributes, declaration headers, fields, and
proofs. It excludes imports, namespaces, the module doc, section headings, and closing `end` lines.

- Total general-API-to-CROW wiring/result code in that scope: **325 LOC**.
- Generic-in-need structural lifting: **172 LOC**. This includes the projected-instance bands
  120–174 and 437–502 (**85 LOC**), plus normalized aggregate-port and non-consumption bands
  195–231, 268–310, and 339–363 (**87 LOC**).
- Topology-specific construction, routing proofs, and theorem-spine application: **153 LOC**.

The parse was a line-state scan that removes `/- ... -/` blocks before testing for nonwhitespace.
The equality `325 = 172 + 153` was reproduced at the gated source ref.

### What was awkward

Dependent projections through `ScatteringComponentFamily`, successive external boundaries, and
appended connection families do not retain the required `Fintype` and `DecidableEq` instances
automatically. The repeated lifting is structural. Endpoint disjointness was most robust when
compared through the explicit normalized `PortLabel` equivalence, rather than by the construction
history of nested subtype witnesses. The reviewer classifies that normalization and its six
non-consumption obligations as generic-in-need structural lifting too. Once those facts were
present, hierarchy flattening, associativity transport, relational closure, elimination, and Mason
extraction applied unchanged.

Declarations that would move into a neutral finite-family/flattening combinator are:

- `componentsComponentFintype` — `Physlib/Optics/Examples/CROW.lean:120`
- `componentsComponentDecidableEq` — `Physlib/Optics/Examples/CROW.lean:126`
- `localChannelFintype` — `Physlib/Optics/Examples/CROW.lean:132`
- `localChannelDecidableEq` — `Physlib/Optics/Examples/CROW.lean:140`
- `componentsLocalChannelFintype` — `Physlib/Optics/Examples/CROW.lean:149`
- `componentsLocalChannelDecidableEq` — `Physlib/Optics/Examples/CROW.lean:156`
- `componentsChannelFintype` — `Physlib/Optics/Examples/CROW.lean:163`
- `componentsChannelDecidableEq` — `Physlib/Optics/Examples/CROW.lean:172`
- `rightLocalChannelFintype` — `Physlib/Optics/Examples/CROW.lean:437`
- `rightChannelFintype` — `Physlib/Optics/Examples/CROW.lean:444`
- `forwardLocalChannelFintype` — `Physlib/Optics/Examples/CROW.lean:449`
- `forwardChannelFintype` — `Physlib/Optics/Examples/CROW.lean:456`
- `returnLocalChannelFintype` — `Physlib/Optics/Examples/CROW.lean:461`
- `returnChannelFintype` — `Physlib/Optics/Examples/CROW.lean:468`
- `outerChannelFintype` — `Physlib/Optics/Examples/CROW.lean:473`
- `connectedChannelFintype` — `Physlib/Optics/Examples/CROW.lean:480`
- `channelFintype` — `Physlib/Optics/Examples/CROW.lean:487`
- `channelDecidableEq` — `Physlib/Optics/Examples/CROW.lean:491`
- `connectedChannelDecidableEq` — `Physlib/Optics/Examples/CROW.lean:495`
- `externalChannelFintype` — `Physlib/Optics/Examples/CROW.lean:499`
- `PortLabel` — `Physlib/Optics/Examples/CROW.lean:195`
- `portLabelEquiv` — `Physlib/Optics/Examples/CROW.lean:202`
- `portLabelEquiv_couplerPort` — `Physlib/Optics/Examples/CROW.lean:216`
- `portLabelEquiv_forwardArcPort` — `Physlib/Optics/Examples/CROW.lean:221`
- `portLabelEquiv_returnArcPort` — `Physlib/Optics/Examples/CROW.lean:226`
- `coupler_rightSecond_not_rightConnected` — `Physlib/Optics/Examples/CROW.lean:268`
- `forwardArc_left_not_rightConnected` — `Physlib/Optics/Examples/CROW.lean:279`
- `returnArc_right_not_rightConnected` — `Physlib/Optics/Examples/CROW.lean:290`
- `coupler_leftSecond_not_rightConnected` — `Physlib/Optics/Examples/CROW.lean:301`
- `returnArc_right_not_forwardConnected` — `Physlib/Optics/Examples/CROW.lean:339`
- `coupler_leftSecond_not_forwardConnected` — `Physlib/Optics/Examples/CROW.lean:352`

### Semantic-glue audit and slice-2 decidable test

Topology-specific semantic glue: **zero LOC**. `componentScattering` selects existing primitive
semantics, and `generic_spine_agrees` is the required semantic result, but its proof consists only
of direct applications of existing generic theorems. Neither declares nor re-proves a CROW channel
equation. All glue that makes those applications typecheck arranges labels, finite instances,
ports, endpoints, and transports.

The regression's former prose claim of coupler-order sensitivity was weakened: no order-permutation
sentinel is present in slice 1, so the shipped text now claims only certification for the selected
mutually coupled fixture.

Would the 172-LOC lift/replication glue have to be rewritten essentially unchanged for slice 2's
heterogeneous ring-assisted MZI? **YES.** The component cases and wiring are different, but the
projected dependent-family and appended-boundary instance obligations recur. This is a genuine
missing structural combinator. It is not a missing semantic theorem. Per the sequencing ruling,
slice 1 lands with this friction recorded; slice 1B precedes any neutral combinator slice.

## P3 validation-gap audit

### Pre-existing modules exercised

The following declaration-bearing modules were present at `f5bb935c` and are exercised by the
production or raw regression proof:

- `Physlib/Optics/Components/DirectionalCouplerPhysical.lean`
- `Physlib/Optics/Components/MatchedPropagationPhysical.lean`
- `Physlib/Optics/Network/Port.lean`
- `Physlib/Optics/Network/ScatteringComponentFamily.lean`
- `Physlib/Optics/Network/ConnectionFamily.lean`
- `Physlib/Optics/Network/ExternalChannel.lean`
- `Physlib/Optics/Network/FlatNetlist.lean`
- `Physlib/Optics/Network/FlatNetlistElimination.lean`
- `Physlib/Optics/Network/FlatNetlistMason.lean`
- `Physlib/Optics/Network/Hierarchical.lean`
- `Physlib/Optics/Network/ConnectionFamilyTransport.lean`
- `Physlib/Optics/Network/HierarchicalReuse.lean`

`CROWRegression.lean` also directly imports
`Physlib/Optics/Systems/Microring/AllPass.lean` so the isolated-ring source API is in scope, but the
anchor deliberately expands the primitive isolated factors and invokes no AllPass response lemma.
It is therefore not counted as an exercised semantic bridge.

Source implementation and lane gates are complete at the gated source ref. Hostile review, merge,
permanent registration, integration battery, and ledger changes are not complete.

The Heebner Table 1 numeric cross-check has not run. Its outcome is: no verdict. Only the primary-
source convention mapping and slice-1B preconditions have been completed.

Major semantics not touched include the DCDR and microring system bridges, parameterized response,
recurrence or transform-domain semantics, conservation/coherency/rephasing closures, simulator
references, physical loss, dispersion, fabrication tolerance, thermal response, material models,
measurement, reciprocity, time reversal, reference planes, and electromagnetic power.

## Goal text exercised, not newly flipped

No `goal.md` row names CROW at the gated source ref. The demonstrator adds evidence for already
completed infrastructure and for the API-test layer; it does not claim a new completion flip.
The exact text exercised at `9cd80837` is:

> - [x] transport of a `PortConnectionFamily` along an equivalence of port families, with
> covariance of incident assembly, external readout, and relational closure. This supports
> replacement of an inner family by another with the same boundary relation and literal
> three-stage append associativity after the canonical port-family transport. The
> fixed-inner-wiring congruence is also complete. All N-08 reuse hypotheses are structural
> `Fintype` assumptions on channel indices, not physical assumptions.

and:

> - **API/elaboration tests:** canonical examples use only public declarations, ensuring that the
> abstraction is usable and does not depend on private proof details.

The controller owns any additive validation binding and must quote its final ledger text at the
integration ref.

## Declaration inventory at `9cd80837`

Every line below points at the line containing the declaration keyword, not its docstring.

### `Physlib/Optics/Examples/CROW.lean`

- `Parameters`
  — `Physlib/Optics/Examples/CROW.lean:78`
- `Component`
  — `Physlib/Optics/Examples/CROW.lean:87`
- `componentPortFamily`
  — `Physlib/Optics/Examples/CROW.lean:95`
- `componentScattering`
  — `Physlib/Optics/Examples/CROW.lean:102`
- `components`
  — `Physlib/Optics/Examples/CROW.lean:114`
- `componentsComponentFintype`
  — `Physlib/Optics/Examples/CROW.lean:120`
- `componentsComponentDecidableEq`
  — `Physlib/Optics/Examples/CROW.lean:126`
- `localChannelFintype`
  — `Physlib/Optics/Examples/CROW.lean:132`
- `localChannelDecidableEq`
  — `Physlib/Optics/Examples/CROW.lean:140`
- `componentsLocalChannelFintype`
  — `Physlib/Optics/Examples/CROW.lean:149`
- `componentsLocalChannelDecidableEq`
  — `Physlib/Optics/Examples/CROW.lean:156`
- `componentsChannelFintype`
  — `Physlib/Optics/Examples/CROW.lean:163`
- `componentsChannelDecidableEq`
  — `Physlib/Optics/Examples/CROW.lean:172`
- `couplerPort`
  — `Physlib/Optics/Examples/CROW.lean:177`
- `forwardArcPort`
  — `Physlib/Optics/Examples/CROW.lean:183`
- `returnArcPort`
  — `Physlib/Optics/Examples/CROW.lean:189`
- `PortLabel`
  — `Physlib/Optics/Examples/CROW.lean:195`
- `portLabelEquiv`
  — `Physlib/Optics/Examples/CROW.lean:202`
- `portLabelEquiv_couplerPort`
  — `Physlib/Optics/Examples/CROW.lean:216`
- `portLabelEquiv_forwardArcPort`
  — `Physlib/Optics/Examples/CROW.lean:221`
- `portLabelEquiv_returnArcPort`
  — `Physlib/Optics/Examples/CROW.lean:226`
- `RightConnection`
  — `Physlib/Optics/Examples/CROW.lean:235`
- `rightConnection`
  — `Physlib/Optics/Examples/CROW.lean:238`
- `rightConnections`
  — `Physlib/Optics/Examples/CROW.lean:253`
- `coupler_rightSecond_not_rightConnected`
  — `Physlib/Optics/Examples/CROW.lean:268`
- `forwardArc_left_not_rightConnected`
  — `Physlib/Optics/Examples/CROW.lean:279`
- `returnArc_right_not_rightConnected`
  — `Physlib/Optics/Examples/CROW.lean:290`
- `coupler_leftSecond_not_rightConnected`
  — `Physlib/Optics/Examples/CROW.lean:301`
- `ForwardConnection`
  — `Physlib/Optics/Examples/CROW.lean:312`
- `forwardConnection`
  — `Physlib/Optics/Examples/CROW.lean:315`
- `forwardConnections`
  — `Physlib/Optics/Examples/CROW.lean:326`
- `returnArc_right_not_forwardConnected`
  — `Physlib/Optics/Examples/CROW.lean:339`
- `coupler_leftSecond_not_forwardConnected`
  — `Physlib/Optics/Examples/CROW.lean:352`
- `ReturnConnection`
  — `Physlib/Optics/Examples/CROW.lean:365`
- `returnConnection`
  — `Physlib/Optics/Examples/CROW.lean:368`
- `returnConnections`
  — `Physlib/Optics/Examples/CROW.lean:383`
- `connections`
  — `Physlib/Optics/Examples/CROW.lean:396`
- `leftAssociatedConnections`
  — `Physlib/Optics/Examples/CROW.lean:403`
- `connections_assoc_transport`
  — `Physlib/Optics/Examples/CROW.lean:410`
- `hierarchy`
  — `Physlib/Optics/Examples/CROW.lean:420`
- `netlist`
  — `Physlib/Optics/Examples/CROW.lean:433`
- `rightLocalChannelFintype`
  — `Physlib/Optics/Examples/CROW.lean:437`
- `rightChannelFintype`
  — `Physlib/Optics/Examples/CROW.lean:444`
- `forwardLocalChannelFintype`
  — `Physlib/Optics/Examples/CROW.lean:449`
- `forwardChannelFintype`
  — `Physlib/Optics/Examples/CROW.lean:456`
- `returnLocalChannelFintype`
  — `Physlib/Optics/Examples/CROW.lean:461`
- `returnChannelFintype`
  — `Physlib/Optics/Examples/CROW.lean:468`
- `outerChannelFintype`
  — `Physlib/Optics/Examples/CROW.lean:473`
- `connectedChannelFintype`
  — `Physlib/Optics/Examples/CROW.lean:480`
- `channelFintype`
  — `Physlib/Optics/Examples/CROW.lean:487`
- `channelDecidableEq`
  — `Physlib/Optics/Examples/CROW.lean:491`
- `connectedChannelDecidableEq`
  — `Physlib/Optics/Examples/CROW.lean:495`
- `externalChannelFintype`
  — `Physlib/Optics/Examples/CROW.lean:499`
- `netlist_eq_hierarchy_flatten`
  — `Physlib/Optics/Examples/CROW.lean:509`
- `generic_spine_agrees`
  — `Physlib/Optics/Examples/CROW.lean:520`

### `Physlib/Optics/Examples/CROWRegression.lean`

- `crowRegressionEndCoupler`
  — `Physlib/Optics/Examples/CROWRegression.lean:72`
- `crowRegressionMiddleCoupler`
  — `Physlib/Optics/Examples/CROWRegression.lean:77`
- `crowRegressionHalfArc`
  — `Physlib/Optics/Examples/CROWRegression.lean:82`
- `crowRegressionParameters`
  — `Physlib/Optics/Examples/CROWRegression.lean:87`
- `crowRegressionFirstIsolatedRing`
  — `Physlib/Optics/Examples/CROWRegression.lean:94`
- `crowRegressionSecondIsolatedRing`
  — `Physlib/Optics/Examples/CROWRegression.lean:101`
- `crowRegression_endCoupler_pythagorean`
  — `Physlib/Optics/Examples/CROWRegression.lean:108`
- `crowRegression_middleCoupler_pythagorean`
  — `Physlib/Optics/Examples/CROWRegression.lean:114`
- `crowRegressionIncidentValue`
  — `Physlib/Optics/Examples/CROWRegression.lean:120`
- `crowRegressionOutgoingValue`
  — `Physlib/Optics/Examples/CROWRegression.lean:140`
- `CrowRegressionChannel`
  — `Physlib/Optics/Examples/CROWRegression.lean:160`
- `crowRegressionIncident`
  — `Physlib/Optics/Examples/CROWRegression.lean:164`
- `crowRegressionOutgoing`
  — `Physlib/Optics/Examples/CROWRegression.lean:170`
- `crowRegressionChannel`
  — `Physlib/Optics/Examples/CROWRegression.lean:176`
- `crowRegressionCouplerChannel`
  — `Physlib/Optics/Examples/CROWRegression.lean:181`
- `crowRegressionForwardArcChannel`
  — `Physlib/Optics/Examples/CROWRegression.lean:186`
- `crowRegressionReturnArcChannel`
  — `Physlib/Optics/Examples/CROWRegression.lean:191`
- `portLabelEquiv_crowRegressionCouplerChannel`
  — `Physlib/Optics/Examples/CROWRegression.lean:197`
- `portLabelEquiv_crowRegressionForwardArcChannel`
  — `Physlib/Optics/Examples/CROWRegression.lean:206`
- `portLabelEquiv_crowRegressionReturnArcChannel`
  — `Physlib/Optics/Examples/CROWRegression.lean:215`
- `crowRegressionConnections`
  — `Physlib/Optics/Examples/CROWRegression.lean:223`
- `crowRegressionRightConnectedChannel`
  — `Physlib/Optics/Examples/CROWRegression.lean:226`
- `crowRegressionForwardConnectedChannel`
  — `Physlib/Optics/Examples/CROWRegression.lean:235`
- `crowRegressionReturnConnectedChannel`
  — `Physlib/Optics/Examples/CROWRegression.lean:242`
- `crowRegressionRightForward_left_embedding`
  — `Physlib/Optics/Examples/CROWRegression.lean:250`
- `crowRegressionRightForward_right_embedding`
  — `Physlib/Optics/Examples/CROWRegression.lean:258`
- `crowRegressionRightReturn_left_embedding`
  — `Physlib/Optics/Examples/CROWRegression.lean:266`
- `crowRegressionRightReturn_right_embedding`
  — `Physlib/Optics/Examples/CROWRegression.lean:274`
- `crowRegressionForward_left_embedding`
  — `Physlib/Optics/Examples/CROWRegression.lean:282`
- `crowRegressionForward_right_embedding`
  — `Physlib/Optics/Examples/CROWRegression.lean:290`
- `crowRegressionReturn_left_embedding`
  — `Physlib/Optics/Examples/CROWRegression.lean:298`
- `crowRegressionReturn_right_embedding`
  — `Physlib/Optics/Examples/CROWRegression.lean:306`
- `crowRegressionRightConnectedChannel_mate_left`
  — `Physlib/Optics/Examples/CROWRegression.lean:314`
- `crowRegressionRightConnectedChannel_mate_right`
  — `Physlib/Optics/Examples/CROWRegression.lean:322`
- `crowRegressionForwardConnectedChannel_mate_left`
  — `Physlib/Optics/Examples/CROWRegression.lean:330`
- `crowRegressionForwardConnectedChannel_mate_right`
  — `Physlib/Optics/Examples/CROWRegression.lean:338`
- `crowRegressionReturnConnectedChannel_mate_left`
  — `Physlib/Optics/Examples/CROWRegression.lean:346`
- `crowRegressionReturnConnectedChannel_mate_right`
  — `Physlib/Optics/Examples/CROWRegression.lean:354`
- `CrowRegressionExternalPort`
  — `Physlib/Optics/Examples/CROWRegression.lean:361`
- `crowRegressionExternalAmbientChannel`
  — `Physlib/Optics/Examples/CROWRegression.lean:369`
- `crowRegressionExternalAmbientChannel_not_connected`
  — `Physlib/Optics/Examples/CROWRegression.lean:377`
- `crowRegressionExternalChannel`
  — `Physlib/Optics/Examples/CROWRegression.lean:437`
- `crowRegressionIncident_component`
  — `Physlib/Optics/Examples/CROWRegression.lean:444`
- `crowRegressionOutgoing_component`
  — `Physlib/Optics/Examples/CROWRegression.lean:453`
- `crowRegressionIncident_coupler`
  — `Physlib/Optics/Examples/CROWRegression.lean:462`
- `crowRegressionOutgoing_coupler`
  — `Physlib/Optics/Examples/CROWRegression.lean:470`
- `crowRegressionIncident_forwardArc`
  — `Physlib/Optics/Examples/CROWRegression.lean:478`
- `crowRegressionOutgoing_forwardArc`
  — `Physlib/Optics/Examples/CROWRegression.lean:486`
- `crowRegressionIncident_returnArc`
  — `Physlib/Optics/Examples/CROWRegression.lean:494`
- `crowRegressionOutgoing_returnArc`
  — `Physlib/Optics/Examples/CROWRegression.lean:502`
- `crowRegressionInput`
  — `Physlib/Optics/Examples/CROWRegression.lean:509`
- `crowRegressionOutput`
  — `Physlib/Optics/Examples/CROWRegression.lean:513`
- `crowRegressionLocalIncident`
  — `Physlib/Optics/Examples/CROWRegression.lean:521`
- `crowRegressionLocalOutgoing`
  — `Physlib/Optics/Examples/CROWRegression.lean:526`
- `crowRegressionIncident_restrict`
  — `Physlib/Optics/Examples/CROWRegression.lean:531`
- `crowRegressionOutgoing_restrict`
  — `Physlib/Optics/Examples/CROWRegression.lean:541`
- `crowRegression_mem_componentBehavior`
  — `Physlib/Optics/Examples/CROWRegression.lean:551`
- `crowRegression_coupler_equations`
  — `Physlib/Optics/Examples/CROWRegression.lean:672`
- `crowRegression_forwardArc_equations`
  — `Physlib/Optics/Examples/CROWRegression.lean:754`
- `crowRegression_returnArc_equations`
  — `Physlib/Optics/Examples/CROWRegression.lean:814`
- `crowRegression_feedbackCoordinates_eq_zero`
  — `Physlib/Optics/Examples/CROWRegression.lean:874`
- `crowRegression_feedbackFixedPoint_eq_zero`
  — `Physlib/Optics/Examples/CROWRegression.lean:926`
- `crowRegression_isWellPosed`
  — `Physlib/Optics/Examples/CROWRegression.lean:1248`
- `crowRegression_incidentAssembly`
  — `Physlib/Optics/Examples/CROWRegression.lean:1272`
- `crowRegression_mem_behavior`
  — `Physlib/Optics/Examples/CROWRegression.lean:1371`
- `crowRegression_rawSelectedOutput`
  — `Physlib/Optics/Examples/CROWRegression.lean:1385`
- `crowRegression_responseTransform_selectedOutput`
  — `Physlib/Optics/Examples/CROWRegression.lean:1402`
- `crowRegression_masonResponseTransform_selectedOutput`
  — `Physlib/Optics/Examples/CROWRegression.lean:1416`
- `crowRegression_wrongRingIndex_ne_response`
  — `Physlib/Optics/Examples/CROWRegression.lean:1426`
- `crowRegression_firstIsolatedRingTransfer`
  — `Physlib/Optics/Examples/CROWRegression.lean:1435`
- `crowRegression_firstIsolatedRingTransfer_eq_standard`
  — `Physlib/Optics/Examples/CROWRegression.lean:1441`
- `crowRegression_firstIsolatedRingTransfer_eq_allPass`
  — `Physlib/Optics/Examples/CROWRegression.lean:1453`
- `crowRegression_secondIsolatedRingTransfer`
  — `Physlib/Optics/Examples/CROWRegression.lean:1465`
- `crowRegression_secondIsolatedRingTransfer_eq_standard`
  — `Physlib/Optics/Examples/CROWRegression.lean:1471`
- `crowRegression_secondIsolatedRingTransfer_eq_allPass`
  — `Physlib/Optics/Examples/CROWRegression.lean:1483`
- `crowResponse_ne_isolatedRingTransferProduct`
  — `Physlib/Optics/Examples/CROWRegression.lean:1500`

## Gate record

All Lean calls used `lake-lock`. The build cache was refreshed after the named sync merge.

- Targeted warnings-as-errors build of both CROW modules: passed, 2760 jobs.
- Temporary sorted registration followed by root warnings-as-errors `Physlib` build: passed,
  5023 jobs.
- `runPhyslibLinters`: passed for Physlib and QuantumInfo after the root build.
- `check_file_imports`: passed with both temporary imports present.
- `sorry_lint`: passed.
- `module_doc_lint`: known repository baseline 147; zero CROW error lines.
- Registered `lint_all`: exit 0; build, imports, illegal imports, duplicate tags, sorry/pseudo,
  Physlib/QuantumInfo Lean linters, and transitive-import stage completed. Printed style/import
  backlog did not name either CROW module.
- Focused `lint-style.py` on both Lean files: passed.
- Full committed-state `lint-style.sh`: completed with zero CROW findings.
- `git diff --check`: passed. Both Lean files have no line over 100 codepoints and stay below
  1500 lines.
- Temporary `Physlib.lean` imports were removed. Restored SHA-256:
  `c54d6030b0fe32d41cd7088aec51224141d6f35cb5997bd4b0f4668f9a1cf0bf`; restored git blob:
  `695167f454ecd4d72f6232d261f95b23d197e68b`.

## Explicit non-claims

Both module docs fence physical loss, dispersion, fabrication tolerance, thermal effects,
stability, causality, measurement, material realization, reciprocity, time reversal, reference
planes, modal completeness, omitted channels, and electromagnetic power. The fixture is a
fixed-carrier normalized-modal-amplitude calculation. No simulator parity or Table-1 numeric parity
is claimed.

## Required sequence after cutoff

1. Hostile review and ordinary merge/registration/battery/ledger pipeline for slice 1.
2. Slice 1B exact Table-1 comparison, beginning with the four written preconditions.
3. Only after slice 1B, a separate neutral structural-combinator slice if authorized.

The pre-authorized slice-2 action immediately after this cutoff is a read-only proposal for a
heterogeneous ring-assisted MZI. It is not implemented by this slice.
