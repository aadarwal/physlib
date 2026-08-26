# S7C phase 9a: beam-splitter and mirror physical ports

## Cutoff and synchronization

This phase remains based on the controller-authorized registered head
`110eb5cde9fcaf9990f77aec7ad7276032c6c01a`. The exact synchronization merge is
`3e64308943d3e0dc43dca86f0ca554189a8015b7`; no re-sync occurred during repair.

The original KK-2 source was `b9dc4cbb9a8a47e4d995e1be56ddf40d697615b1`. The exact KK-3
repair source is `daadda47412242c6aae6ec549e83ac8da07d8773`. This cutoff is its
HANDOFF-only child.

Relative to the sync target, the production delta remains exactly the five authorized Phase 9a
files. No pre-existing source module changed. `Physlib.lean` remains byte-identical to the sync
target.

## Goal and phase boundary

The controlling N7 text at `goal.md:2184-2185` on the cutoff says:

> component-owned physical-port packaging for the remaining beam-splitter, mirror,
> polarization, and interface primitives consumed by `ScatteringComponentFamily`;

The repaired independence discipline at `goal.md:2193-2194` says:

> an independent behavioral specification for every component, followed by a realization lemma
> proving that its matrix or relation satisfies that specification; and

Phase 9a supplies only the beam-splitter and mirror members. Polarization and interface
packaging remain open for Phase 9b, which has not started. The frequency-parameterized
propagation item at `goal.md:2186-2187` also remains open.

The component laws and packaging are Physlib-original. Every result is a `lemma`; this phase
asserts no literal printed physics theorem.

## Authorized files

- `Physlib/Optics/Components/BeamSplitter.lean` (276 lines);
- `Physlib/Optics/Components/BeamSplitterPhysical.lean` (224 lines);
- `Physlib/Optics/Components/Mirror.lean` (168 lines);
- `Physlib/Optics/Components/MirrorPhysical.lean` (206 lines); and
- `Physlib/Optics/Components/PhysicalPortSuiteRegression.lean` (794 lines).

Production imports no regression module. No additive edit to an existing Components, Network,
or Mode module was needed.

## Independent beam-splitter equations

`BeamSplitter.Parameters` records independent real through and cross amplitudes at
`Physlib/Optics/Components/BeamSplitter.lean:68`. The separately declared matrix
`BeamSplitter.mixing` is at line 95 and is not an alias of `DirectionalCoupler`.

The repaired independent output law is defined at line 133. It constructs two linear maps from
incident endpoint amplitudes directly:

- first output: `t * firstInput + (-I * k) * secondInput`;
- second output: `(-I * k) * firstInput + t * secondInput`.

Neither `BeamSplitter.outputMap` nor `BeamSplitter.behavior` calls `mixing`, `scattering`, or a
matrix action. `BeamSplitter.outputMap_apply` exposes both equations at line 158, and
`BeamSplitter.mem_behavior_iff` makes them the behavior-membership equation at line 179.

The scattering adapter stores `mixing` separately at line 200. Its action is derived from matrix
blocks at line 204. `BeamSplitter.scattering_realizes_behavior` at line 214 now rewrites the
matrix action to the two independent endpoint equations and expands the cross coefficient. It is
not a wrapper-level definitional equality.

Exact normalized-modal-power scaling remains at line 231, power preservation under
`Parameters.IsUnitary` at line 261, and algebraic losslessness at line 267.

## Independent mirror equation

`Mirror.Parameters` stores one complex reflection coefficient at
`Physlib/Optics/Components/Mirror.lean:63`. The separately declared scalar matrix
`Mirror.reflection` is at line 72.

The repaired `Mirror.outputMap` at line 98 constructs coefficient-times-corresponding-mode
directly from endpoint reindexing and scalar multiplication. It calls neither `reflection` nor
`scattering`. Its explicit equation is at line 108, and `Mirror.mem_behavior_iff` makes that
equation behavior membership at line 123.

The scattering adapter is constructed separately at line 137. Its matrix action is proved at
line 141. `Mirror.scattering_realizes_behavior` at line 148 derives the endpoint equation from
that matrix action. Modal losslessness under the explicit unit-phase hypothesis is at line 156.

## Component-owned physical ports

The beam splitter owns distinct `first` and `second` ports at
`Physlib/Optics/Components/BeamSplitterPhysical.lean:67`. Its `PortModeFamily` and pinned
raw-channel equivalence are at lines 79 and 84. Independent behavior and scattering are
transported separately at lines 156 and 172. Exact graph realization is at line 187, and the
direct singleton `ScatteringComponentFamily` witness is at line 205.

The mirror owns one `surface` port at
`Physlib/Optics/Components/MirrorPhysical.lean:66`. Its `PortModeFamily` and pinned equivalence
are at lines 78 and 83. Independent behavior and scattering are at lines 136 and 152. Exact graph
realization is at line 169, and the direct component-family witness is at line 187.

These adapters now transport independently stated endpoint equations rather than matrices that
were postulated to be unrelated. Ownership remains present by construction.

## Fail-capable mixed-family regression

The positive fixture uses beam parameters `t = 3/5`, `k = 4/5`, beam input `(1, 2)`, mirror
phase `I`, and mirror input `3`. Primitive matrix multiplication gives
`((3 - 8I)/5, (6 - 4I)/5)` and `3I` at
`Physlib/Optics/Components/PhysicalPortSuiteRegression.lean:102` and `:125`.

The mixed family is built at lines 188-214. An explicit three-channel matrix is at line 349 and
is proved entrywise equal to the family matrix at line 368. Its action is expanded as three
finite sums at line 412. Aggregate input/output coordinates are proved at lines 482 and 496,
then joined by the raw aggregate action at line 512.

The hostile fixture swaps only the beam output endpoint order at line 527. Its independently
written indexed matrix is at line 614, and its finite-sum action is at line 656. On the same input
the hostile values are `((6 - 4I)/5, (3 - 8I)/5)` and `3I`, proved at line 730. The first output
inequality is at line 747, and the full outputs differ at line 757. The valid graph member remains
anchored at line 783.

The KK-2 repair changed no regression proof or coefficient. Only its module-doc non-claim fence
changed, so the accepted primitive and hostile derivations remain intact.

### Path-qualified anchor-independence map

- `Physlib/Optics/Components/PhysicalPortSuiteRegression.lean`:
  `physicalPortSuite9a_beam_raw_action` unfolds the primitive beam matrix. It is independent of
  both physical-port modules, all realization lemmas, and assembled-family action lemmas.
- `Physlib/Optics/Components/PhysicalPortSuiteRegression.lean`:
  `physicalPortSuite9a_mirror_raw_action` unfolds the primitive scalar matrix. It is independent
  of mirror physical-port packaging, its realization lemma, and assembled-family action lemmas.
- `Physlib/Optics/Components/PhysicalPortSuiteRegression.lean`:
  `physicalPortSuite9a_indexedScatteringMatrix_eq_explicit` is an entrywise finite-case proof. It
  is independent of component-family projection lemmas and assembled-matrix entry helpers.
- `Physlib/Optics/Components/PhysicalPortSuiteRegression.lean`:
  `physicalPortSuite9a_indexed_action` expands `Matrix.mulVec` and all three sums. It is
  independent of assembled-matrix action helpers and both component realization lemmas.
- `Physlib/Optics/Components/PhysicalPortSuiteRegression.lean`:
  `physicalPortSuite9a_aggregate_action` uses the raw indexed action and explicit reindexing. It
  is independent of every packaged assembled-action lemma.
- `Physlib/Optics/Components/PhysicalPortSuiteRegression.lean`:
  `physicalPortSuite9a_hostile_indexedScatteringMatrix_eq_explicit`,
  `physicalPortSuite9a_hostile_indexed_action`,
  `physicalPortSuite9a_hostile_aggregate_action`, and
  `physicalPortSuite9a_hostile_action_ne` repeat the finite expansion for the swapped endpoint.
  They are independent of positive packaging and assembled-action lemmas under test.

A declaration-name grep over
`Physlib/Optics/Components/PhysicalPortSuiteRegression.lean` remains empty for both
`assembledScatteringMatrix_*` helpers, both `componentFamily_*` projections, both physical
realization/adapter lemmas, and both raw scattering-realization lemmas.

## Per-module non-claim boundary

All five module docs now state the full applicable boundary explicitly:

- modal losslessness is squared-amplitude bookkeeping, not electromagnetic power;
- no reciprocity or time-reversal law is asserted;
- no reverse-incidence Maxwell law or modal completeness is asserted;
- no propagation, causality, or dispersion is asserted; and
- exact graph realization is not a physical-realization claim.

The matrices are fixed-carrier reduced laws. No geometry, coating, material interface,
reference-plane, bandwidth, stability, measurement, or fabrication claim is made. Human
verification remains required by `AI-POLICY.md`.

## Reviewer map

1. Read `Physlib/Optics/Components/BeamSplitter.lean:123-197` for the matrix-free endpoint law.
2. Read `Physlib/Optics/Components/BeamSplitter.lean:200-220` for substantive realization.
3. Read `Physlib/Optics/Components/Mirror.lean:88-133` for its matrix-free endpoint law.
4. Read `Physlib/Optics/Components/Mirror.lean:137-154` for substantive realization.
5. Read both Physical modules from their A sections through their direct family witnesses.
6. Read `Physlib/Optics/Components/PhysicalPortSuiteRegression.lean:62-180` for raw actions.
7. Read lines 184-519 for the positive explicit matrix and aggregate action.
8. Read lines 523-760 for the hostile endpoint-swap matrix, action, and inequality.

## Exact validation record

The exact repair source `daadda47412242c6aae6ec549e83ac8da07d8773` was checked under
`lake-lock`. Temporary sorted registration of all five modules was used for declaration and
module-document linters, then removed.

- targeted builds of `Physlib.Optics.Components.BeamSplitter` and
  `Physlib.Optics.Components.Mirror`: passed;
- targeted build of `Physlib.Optics.Components.PhysicalPortSuiteRegression`: passed,
  2719 jobs;
- `runPhyslibLinters`: Physlib and QuantumInfo passed, including `simpNF`;
- `module_doc_lint`: no diagnostic names any Phase 9a module; the command remains globally red on
  the pre-existing repository-wide documentation backlog;
- committed-state `lint-style.sh`: passed;
- `git diff --check`: passed;
- file lengths are 276, 224, 168, 206, and 794, all below 1500 lines;
- per-file maxima are 97, 99, 99, 99, and 100 Unicode codepoints;
- no file contains `theorem`, `sorry`, `axiom`, `native_decide`, `maxHeartbeats`, or
  `Lean.ofReduceBool`;
- production imports no regression module; and
- the repaired behavior sections contain no call to `mixing`, `reflection`, or `scattering`.

Temporary registration was restored byte-identically. `Physlib.lean` had SHA-256
`a76a905b6d702efe94fa12ef5bd68cf6dfee745428ae35ac155dc148b6de574d` before and after the gate.
This final cutoff child changes only `HANDOFF.md`.
