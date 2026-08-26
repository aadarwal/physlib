# S7D slice 9 handoff: joint ring and DCDR X-01 boundary/chain regression

## Cutoff identity

- Exact sync target: `cb89d1d2d5ff3459c2cb50f21274713cd00ad62f`.
- Sync merge: `001977bafa8fcf2c9ee5e47fb0e792cfbd734693`.
- Gated source: `a99091fcd4a0315f00f85d32b8ff5eb534bc46f6`.
- `Physlib.lean` is unchanged. Its restored SHA-256 is
  `85727e4debf1f8ad8c50abe04763611f45131275542b2b6ee18f1e28d5f538d0`.
- The source merge delta is exactly the three Lean modules listed below. This
  handoff is the cutoff-only child.

The later development head `110eb5cd` was announced while the gate was running.
Per controller direction, this cutoff remains based on `cb89d1d2`; no mid-gate
resync was performed.

## Goal resolution

At this cutoff ref, `goal.md:2430-2432` says verbatim:

> - for an eligible ring and the DCDR case, a cross-semantics theorem equating
> relational behavior, compiled elimination, chain response, feedback algebra,
> Mason gain, and recurrence/Z response on the intersection of their domains.

The X-01 row at `goal.md:2646` says verbatim:

> | X-01 | one ring and one DCDR satisfy the full
> relational/compiled/chain/feedback/Mason/Z cross-semantics equality on the
> common domain | abstraction layers disagree despite local proofs |

The preceding status at `goal.md:2408-2411` says verbatim:

> On their explicit intersection, one theorem identifies the causal transform,
> rational response, circulation series, fixed N5 response, complete Mason
> response, typed scattering, backward-first chain, and original relational
> behavior. This completes the ring instance of X-01; the DCDR half remains
> separate, so X-01 as a two-system regression is still open.

This slice supplies the missing DCDR nominal-chain leg and a joint two-system
predicate/regression. The joint predicate is the conjunction of the already
accepted ring agreement and the new DCDR agreement on their respective common
domains. It never states that the two systems have the same response value.
Thus the two-system X-01 row is closed in exactly that systemwise sense.

## Files and registration request

- `Physlib/Optics/Systems/DCDR/NominalChain.lean`: nominal two-channel boundary,
  complete N5 response, scalar pivot, N3T chain, and extended DCDR agreement.
- `Physlib/Optics/Systems/DCDR/NominalChainRegression.lean`: independent exact
  N7, scattering, pivot, chain, common-domain, and hostile-plane fixtures.
- `Physlib/Optics/Systems/Microring/AllPassDCDRX01Regression.lean`: joint
  ring-and-DCDR predicate, unequal anchors, and joint negative sentinel.

Please register these imports in repository-sorted order:

```lean
public import Physlib.Optics.Systems.DCDR.NominalChain
public import Physlib.Optics.Systems.DCDR.NominalChainRegression
public import Physlib.Optics.Systems.Microring.AllPassDCDRX01Regression
```

`ZTransformBridge.lean` received no additive edit. No existing source file was
changed by this slice.

## Production claims

`NominalChain.lean` labels the two existing DCDR external N7 channels in an
explicit order:

- nominal left is the first coupler's exposed `leftFirst` endpoint;
- nominal right is the second coupler's exposed `rightFirst` endpoint.

These are nominal algebraic coordinates only. The endpoint map is proved
bijective and is used to reindex the complete external relation and N5 response.

`response_nominal_reference_coordinates` at `NominalChain.lean:180` starts from
the complete forward and reverse N7 equations. It proves the full two-coordinate
response for arbitrary external incidence. The resulting four N5 blocks are

```text
             incident left       incident right
outgoing left       0             transfer(p.reverse)
outgoing right  transfer(p)               0
```

The reflectionless `nominalTwoPortScattering` is independently stated from these
two scalar transmissions. On the existing solve gate, the packaged N5 transform,
the reindexed original relation, and that independently stated scattering law are
identified.

The scalar pivot is the nominal right-to-left transmission
`transfer p.reverse`. The lemma
`packagedNominalTwoPortScattering_hasBijectiveRightToLeftTransmission_iff` at
`NominalChain.lean:455` proves that the full block is bijective exactly when this
scalar is nonzero. This pivot is not inferred from well-posedness, ROC membership,
contraction, Schur certification, no cancellation, or reduced evaluation.

On the solve and pivot gates, `nominalBackwardFirstChainTransform_eq_matrix` at
`NominalChain.lean:546` identifies the behavior-derived backward-first chain with

```text
diag((transfer p.reverse)^-1, transfer p).
```

`nominalBackwardFirstChainTransform_roundTrip` at `NominalChain.lean:582` uses
the generic N3T round trip to recover the complete packaged N5 scattering law.
The underlying generic block formula is in
`Physlib/Optics/Network/TwoPortScatteringChain.lean:431-553`; the scattering
round trip is in
`Physlib/Optics/Network/TwoPortChainScattering.lean:781-795`.

`IsZChainCrossSemanticsDomain` extends the accepted DCDR Z common domain with one
separate pivot field. `zChainCrossSemantics_agree` at `NominalChain.lean:664`
collects:

- causal impulse-response Z transform and named ROC;
- reduced rational and reciprocal-Z compiled response;
- feedback/circulation response on its contraction gate;
- fixed N5 elimination and complete Mason response;
- packaged typed scattering and full-vector relational behavior;
- nominal backward-first chain and its N3T scattering round trip.

The base DCDR common-domain and agreement records reused here are at
`DCDR/ZTransformBridge.lean:242-357`.

## Joint two-system closure

`RingDCDRX01Agreement` at `AllPassDCDRX01Regression.lean:64` is deliberately a
conjunction:

```text
ring ZCrossSemanticsAgreement AND DCDR ZChainCrossSemanticsAgreement.
```

There is no field comparing ring and DCDR values. The accepted ring witness is
reused from `AllPassZTransformBridge.lean:327-424` and its regression witness at
`AllPassZTransformBridgeRegression.lean:68`.

`ringDCDRX01Regression_hasAgreement` supplies both production agreements.
`ringDCDRX01Regression_independentAnchors` then pins each system independently:

- ring response `1/7` and chain diagonal `(7, 1/7)`;
- DCDR response `-(7/8) I` and chain diagonal
  `((8/7) I, -(7/8) I)`.

It also proves `(1/7 : ℂ) ≠ -(7/8) I`, making the absence of a cross-system
value equality load-bearing rather than merely documentary.

## Independent regression audit

The DCDR fixture is `stableUnitDelayParameters` at `z = I`, hence formal
`q = z^-1 = -I`. Its nonzero loop polynomial is `-(1/4) q^2`. Direct parameter
expansion gives both forward and reverse transmission `-(7/8) I`; the inverse
pivot is `(8/7) I`.

The independently audited packaged N5 matrix is

```text
[       0       -(7/8) I ]
[ -(7/8) I          0    ].
```

The independently audited backward-first chain is

```text
[ (8/7) I        0       ]
[    0       -(7/8) I    ].
```

The anchor dependency audit is:

- `zChainRegression_forwardEquations_output` expands the raw N7 equations and
  does not use `ForwardEquations.output_eq_transfer`.
- `zChainRegression_independent_packaged_blocks` at
  `NominalChainRegression.lean:356` derives all four blocks through those raw
  equations and direct readout unfolding. It does not use the production response
  entry or packaged-entry lemmas.
- `zChainRegression_hasBijectiveRightToLeftTransmission` at line 458 constructs
  the pivot inverse from the exact scalar product. It does not use the production
  pivot iff, pivot action, or entry lemmas.
- The four `zChainRegression_chain_*` values unfold the generic N3T block
  construction. They do not use
  `nominalBackwardFirstChainTransform_eq_matrix` or any production reflection or
  transmission value lemma.
- `zChainRegression_productionChain_with_independent_entries` at line 579 keeps
  the production equality and all independently computed entries in separate
  conjuncts.
- `zChainRegression_independent_common_point` at line 618 reuses the accepted
  primitive causal, reciprocal-Z, raw-N5, and eleven-branch Mason audit at
  `ZTransformRegression.lean:563`, then joins it to the independently unfolded
  chain. It does not use `zChainCrossSemantics_agree`.
- `zChainRegression_productionAgreement_with_independent_anchor` at line 641
  pairs the production agreement with the independent values only after those
  values have been established.
- The joint anchors use the accepted independent ring recurrence, raw N5, Mason,
  and chain fixtures plus the independent DCDR conjunction. They do not derive a
  value through `RingDCDRX01Agreement`.

A feedback sign, reverse reindex, pivot, or N3T block-order error changes one of
these exact values.

## Fail-capable sentinel

`zChainRegressionWrongReferencePlaneMatrix` swaps the two correct DCDR diagonal
entries. At the same fixture, the correct leading entry is `(8/7) I`, while the
wrong leading entry is `-(7/8) I`.

`zChainRegression_chain_ne_wrongReferencePlaneMatrix` at
`NominalChainRegression.lean:672` rejects this matrix by an independently pinned
entry inequality. The joint
`ringDCDRX01Regression_wrongReferencePlane_rejected` at
`AllPassDCDRX01Regression.lean:145` retains the ring leading value `7` and DCDR
leading value `(8/7) I` while rejecting the same wrong nominal order.

## Gate record

All Lean jobs ran through the machine-wide `lake-lock`.

- Targeted builds of `NominalChainRegression` and
  `AllPassDCDRX01Regression` passed: 2,818 jobs.
- With the three modules temporarily registered, cache retrieval and
  `lake --wfail build Physlib` passed: 5,002 jobs.
- `check_file_imports`, `sorry_lint`, `runPhyslibLinters`, and `api_map_index`
  passed.
- `lint_all` exited successfully. Its displayed style and redundant-import
  findings are pre-existing files outside this three-file slice; it reported no
  new module and its build/import/declaration stages passed.
- `scripts/lint-style.sh` passed repository-wide. Direct `lint-style.py` checks
  also passed on all three new files.
- The repository-wide `module_doc_lint` still exits on legacy modules outside
  this lane. A captured scoped audit contains no `NominalChain` or
  `AllPassDCDRX01Regression` finding. Each new module has the four literal
  headings and a TOC exactly matching its numbered sections.
- There are zero banned declarations, zero `theorem` declarations, and no line
  over 100 codepoints. The files have 681, 685, and 158 lines respectively.
- `Physlib.lean` was restored byte-for-byte after temporary registration.

## Non-claims and human audit

The DCDR chain is a nominal algebraic two-port. This slice makes no claim of a
physical reference plane, reciprocity, physical time reversal, physical
resonance, coherent-incoherent equivalence, BIBO stability beyond S4P's gate,
normalized-modal or electromagnetic power, Maxwell time-domain meaning,
physical-frequency meaning, HOL-script semantics, or a shared ring/DCDR response
value.

Per `AI-POLICY.md`, a human author must independently certify the boundary labels,
the reverse-transmission pivot, the chain convention, the exact regression
values, and the stated X-01 closure before merge.
