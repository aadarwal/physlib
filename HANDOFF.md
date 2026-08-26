# S7C slice 6: connection-family transport and hierarchical reuse

## Cutoff and synchronization

This slice remains on the controller-authorized base
`195c3a22366b1f5b0a0efed54f41cb893b5779fd`; no mid-slice synchronization was performed. The
exact gated source is `bdb6eb59859735c2b8003417d05d9e317526ee1b`. The cutoff is its
HANDOFF-only child. `Physlib.lean` is intentionally unchanged.

## Scope and classification

The controlling text at `goal.md:2098-2102` on the authorized base says:

> the remaining reuse machinery: transport of a `PortConnectionFamily` along an equivalence of
> port families. This single construction is needed both to replace an inner family by another
> with the same boundary relation and to state literal three-stage append associativity. The
> fixed-inner-wiring congruence is already complete. All current N-08 hypotheses are structural
> `Fintype` assumptions on channel indices, not physical assumptions.

This slice supplies that neutral Network machinery for ledger target N-08. S-08 remains the
downstream lattice canary. Every result introduced here is a `lemma`; no declaration is presented
as a printed physics theorem.

## Authorized out-of-home additions

The exact out-of-home changes are:

- additive-only `LinearBehavior.reindex_trans` in
  `Physlib/Optics/Network/LinearBehaviorReindex.lean`;
- new `Physlib/Optics/Network/ConnectionFamilyTransport.lean`;
- new `Physlib/Optics/Network/HierarchicalReuse.lean`; and
- new `Physlib/Optics/Network/HierarchicalReuseRegression.lean`.

No existing declaration, statement, proof, or attribute in `Hierarchical.lean`,
`WiringInvariance.lean`, `ConnectionFamily.lean`, or another existing Network module changed.
Production imports no regression module.

## Transport API

`PortModeFamily.Equiv` at `ConnectionFamilyTransport.lean:69` stores a port equivalence and a
dependent equivalence of every mode fiber. Identity, composition, reversal, and the induced sigma
channel equivalence are at lines 81, 86, 92, and 100.

Connection transport is defined at `ConnectionFamilyTransport.lean:124`; its local-channel
equivalence, ambient embedding covariance, and mate covariance are at lines 133, 138, and 146.
Connection-family transport is defined at line 180; its connected-channel equivalence, embedding
covariance, and mate covariance are at lines 190, 196, and 204.

The transported unconnected-port, external-channel, and dependent external-boundary equivalences
are at `ConnectionFamilyTransport.lean:225`, `:253`, and `:281`. The boundary/channel compatibility
lemma is at line 290.

The equation-level covariance API is:

- `incidentAssembly_transport`, `ConnectionFamilyTransport.lean:332`;
- `externalOutgoingReadout_transport`, line 426;
- `mem_closeBehavior_transport_iff`, line 446; and
- `closeBehavior_transport`, line 511.

These are complete singular-safe relational statements. Their hypotheses are only finite index
structure needed by `ModeAmplitude` and matrix-backed assembly; no solvability, uniqueness,
well-posedness, or physical hypothesis appears.

Successive behavior relabellings are composed by `LinearBehavior.reindex_trans` at
`LinearBehaviorReindex.lean:72`. This is the sole additive change to that pre-existing module.

## Hierarchical reuse and associativity

`appendExternalPortModeFamilyEquiv` and its reverse presentation are at
`HierarchicalReuse.lean:66` and `:74`. After transporting stage three through that boundary,
`append_assoc_transport` at line 125 proves literal equality of the two three-stage connection
families after `Equiv.sumAssoc` reindexes the connection labels.

For replacement, the supplied inner-boundary and final external-channel equivalences are at
`HierarchicalReuse.lean:150` and `:156`. The proof proceeds through:

- `innerBoundaryBehavior_eq_of_boundaryRelation`, line 187;
- `replacementExternal_reindex`, line 283; and
- `replaceInnerFamily`, line 350.

Thus, if two inner families have equal complete closed boundary relations after the explicitly
supplied dependent boundary transport, appending the correspondingly transported outer family
preserves the complete relation up to the induced final external relabelling. The statement does
not assume either relation is functional or well posed.

## Dynamic N-08 regression

The regression uses four supplied two-port operators with forward gains `2`, `3`, `5`, and `7`.
The hand-expanded ambient incident west-port values are `1`, `2`, `6`, and `30`; outgoing east-port
values are `2`, `6`, `30`, and `210`.

The component graph is expanded from the matrix primitives in
`reuseRegression_mem_componentBehavior` at `HierarchicalReuseRegression.lean:386`. The three
nonzero cross-stage amplitudes and exact routed equalities are pinned independently at lines 408
and 419.

The two parenthesizations are checked separately:

- right-associated incident assembly and readout are expanded at lines 484 and 542, with raw
  closure membership at line 554;
- left-associated incident assembly and readout are expanded at lines 615 and 673, with raw
  closure membership at line 685; and
- `reuseRegression_mem_both_parenthesizations` at line 698 joins the two independently established
  memberships and their common exact response `210`.

None of these proofs invokes the transport-covariance, replacement, or append-associativity lemmas
under test. A declaration-name grep for those results in the regression is empty.

The hostile dependent boundary equivalence at `HierarchicalReuseRegression.lean:768` swaps the
correctly lifted third-east source with the external first-west drive while preserving the
singleton mode fibers. Its two embedded endpoints are calculated at lines 794 and 807, and its
wrong mate at line 823. Consequently, the fourth-west incident coordinate reads the zero
first-west outgoing amplitude instead of the nonzero third-east amplitude (line 831).
`reuseRegression_hostile_incidentAssembly_ne` at line 843 rejects every hostile external input by
the concrete contradiction `30 = 0`. Together with the distinct raw expansions under both
parenthesizations, this detects subsystem-boundary, port-lift, associator-branch, and cascade-index
errors.

## Non-claims

- No connection stage or closed relation is claimed well posed, functional, total, or uniquely
  solvable.
- No passivity, losslessness, reciprocity, stability, causality, resonance, bandwidth, dispersion,
  measurement, physical-realization, or electromagnetic-power claim is made.
- The regression coefficients are algebraic sentinels, not normalized physical couplers.
- No source-parity claim is made; this is neutral N-08 reuse machinery.
- Human verification of the intended API remains required by `AI-POLICY.md`.

## Reviewer map

1. Read `ConnectionFamilyTransport.lean:69-209` for the dependent equivalence and connection/family
   transport.
2. Read `ConnectionFamilyTransport.lean:216-526` for external boundaries and equation/closure
   covariance.
3. Read `HierarchicalReuse.lean:56-135` for boundary presentation and literal associativity.
4. Read `HierarchicalReuse.lean:139-391` for equivalent-boundary replacement.
5. Read `HierarchicalReuseRegression.lean:386-716` for the independent positive raw equations.
6. Read `HierarchicalReuseRegression.lean:768-853` for the hostile boundary and `30 = 0` rejection.

## Exact validation record

The exact source head `bdb6eb59859735c2b8003417d05d9e317526ee1b` was tested with temporary
registration of the four current Network modules, both lattice modules, and the nine unregistered
PANDA dependencies. One `lake-lock` hold ran the exact-source umbrella build, declaration linters,
and aggregate lint.

Results:

- `lake exe cache get`: no downloads; 8690 files were already decompressed;
- targeted warning-as-error build of all four current modules: passed, 2727 jobs;
- warning-as-error `Physlib` umbrella build under temporary registration: passed, 4956 jobs;
- `runPhyslibLinters`: Physlib and QuantumInfo passed;
- `lint_all`: build, illegal-import, duplicate-tag, sorry/pseudo, and declaration-linter stages
  passed; its listed missing registrations and transitive-import/style diagnostics are the frozen
  base's out-of-lane backlog;
- committed-state `lint-style.sh`: no current Network file was reported;
- filename-filtered `module_doc_lint`: no current Network file was reported;
- every current module has the literal four required module-document headings and an exact TOC;
- `git diff --check`: passed;
- no current Lean file exceeds 100 Unicode codepoints per line;
- line counts are 102, 532, 395, and 856, all below 1500;
- no current Lean file contains a `theorem` declaration, `sorry`, `axiom`, `native_decide`,
  `maxHeartbeats`, or `Lean.ofReduceBool`;
- production imports no regression module; and
- the regression contains no invocation of a transport-covariance, replacement, or associativity
  lemma under test.

Temporary registration was restored byte-identically. `Physlib.lean` had SHA-256
`88d1329fba21fc443261608300b3c922c4612d3cb4454a7f82e57e760aeaadb7` before and after the gate.
This final cutoff child changes only `HANDOFF.md`.
