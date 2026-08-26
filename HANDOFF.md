# S7C phase 9a: beam-splitter and mirror physical ports

## Cutoff and synchronization

This phase synchronized exactly onto the controller-authorized registered head
`110eb5cde9fcaf9990f77aec7ad7276032c6c01a`. The synchronization merge is
`3e64308943d3e0dc43dca86f0ca554189a8015b7`. The gated source is
`b9dc4cbb9a8a47e4d995e1be56ddf40d697615b1`. This cutoff is its HANDOFF-only
child.

Relative to the sync target, the source adds exactly the five authorized Phase 9a files.
No pre-existing file changed. `Physlib.lean` remains byte-identical to the sync target.

## Goal and phase boundary

The controlling N7 text at `goal.md:2184-2185` on the cutoff says:

> component-owned physical-port packaging for the remaining beam-splitter, mirror,
> polarization, and interface primitives consumed by `ScatteringComponentFamily`;

Phase 9a supplies only the beam-splitter and mirror members. Polarization and interface
packaging remain open for the separately authorized Phase 9b, which has not started. The
fixed-carrier propagation bullet at `goal.md:2186-2187` also remains open.

The component laws and packaging are Physlib-original. Every result is a `lemma`; the phase
asserts no literal printed physics theorem.

## Authorized files

- `Physlib/Optics/Components/BeamSplitter.lean` (240 lines);
- `Physlib/Optics/Components/BeamSplitterPhysical.lean` (221 lines);
- `Physlib/Optics/Components/Mirror.lean` (161 lines);
- `Physlib/Optics/Components/MirrorPhysical.lean` (203 lines); and
- `Physlib/Optics/Components/PhysicalPortSuiteRegression.lean` (793 lines).

No additive edit to an existing Components, Network, or Mode module was needed. Production
imports no regression module.

## Independent beam-splitter law

`BeamSplitter.Parameters` records independent real through and cross amplitudes at
`BeamSplitter.lean:66`. The declared transform at line 93 is
`[[t, -I*k], [-I*k, t]]`; it is not an alias of `DirectionalCoupler`. The independent
incident-to-outgoing behavior is defined before the scattering adapter at line 147. Exact graph
realization is proved at line 178.

The normalized-modal-power factor `t² + k²` is defined at line 73. Exact scaling is proved at
line 195, power preservation under `IsUnitary` at line 225, and algebraic losslessness at line
231. The negative-quadrature cross phase is declared model data, not a reciprocity or
reverse-incidence Maxwell derivation.

## Independent mirror law

`Mirror.Parameters` stores one complex reflection coefficient at `Mirror.lean:61`.
`Mirror.reflection` is the same-mode scalar transform at line 70. The independent one-port
behavior is defined at line 113, and the scattering graph realizes it exactly at line 141.
Unit squared modulus is the explicit algebraic hypothesis at line 66; modal losslessness under
that hypothesis is proved at line 149.

## Component-owned physical ports

The beam splitter owns distinct `first` and `second` ports at
`BeamSplitterPhysical.lean:64`. Its `PortModeFamily` and pinned raw-channel equivalence are at
lines 76 and 81. Independent behavior and scattering are transported separately at lines 153
and 169, with exact graph realization at line 184. The direct singleton
`ScatteringComponentFamily` witness is at line 202.

The mirror owns one `surface` port at `MirrorPhysical.lean:63`. Its `PortModeFamily` and pinned
equivalence are at lines 75 and 80. Independent behavior and scattering are at lines 133 and
149, exact graph realization is at line 166, and the direct component-family witness is at line
184. In both components, ownership is present in the construction rather than recovered by a
post-hoc channel identification.

## Fail-capable mixed-family regression

The positive fixture uses beam parameters `t = 3/5`, `k = 4/5`, beam input `(1, 2)`, mirror
phase `I`, and mirror input `3`. Primitive matrix multiplication gives the exact outputs
`((3 - 8I)/5, (6 - 4I)/5)` and `3I` at
`PhysicalPortSuiteRegression.lean:101` and `:124`.

The mixed component family is built at lines 187-213. An explicit three-channel indexed matrix
is defined at line 348 and proved entrywise equal to the family matrix at line 367. Its action is
expanded as three concrete finite sums at line 411. The aggregate input and output coordinates
are proved at lines 481 and 495, then joined by the raw aggregate action at line 511.

The hostile fixture swaps only the beam output endpoint order at line 526. Its independently
written indexed matrix is at line 613, its direct finite-sum action is at line 655, and its
aggregate output is proved at line 716. On the same input the hostile values are
`((6 - 4I)/5, (3 - 8I)/5)` and `3I`, as recorded at line 729. The first output inequality is at
line 746, and the full output functions differ at line 756. The valid graph member is anchored
at line 782.

This negative case can fail if the endpoint lift, local channel order, component index, or
aggregate reindex is wrong. It is not a mere type-level or zero-amplitude sentinel.

### Anchor-independence map

- `physicalPortSuite9a_beam_raw_action` unfolds the primitive beam matrix. It is independent of
  both physical-port modules, both realization lemmas, and every assembled-family action lemma.
- `physicalPortSuite9a_mirror_raw_action` unfolds the primitive scalar matrix. It is independent
  of mirror physical-port packaging, its realization lemma, and assembled-family action lemmas.
- `physicalPortSuite9a_indexedScatteringMatrix_eq_explicit` is an entrywise finite-case proof. It
  is independent of the component-family projection lemmas and assembled-matrix entry helpers.
- `physicalPortSuite9a_indexed_action` expands `Matrix.mulVec` and all three sums. It is
  independent of assembled-matrix action helpers and both component realization lemmas.
- `physicalPortSuite9a_aggregate_action` uses the raw indexed action and explicit reindexing. It
  is independent of every packaged assembled-action lemma.
- The hostile explicit-matrix equality, action, coordinates, and inequality repeat the finite
  expansion for the swapped endpoint. They are independent of the positive packaging and action
  lemmas under test.

A declaration-name grep over the regression is empty for
`assembledScatteringMatrix_apply_component`, `assembledScatteringMatrix_entry`, both
`componentFamily_*` projection lemmas, both physical-scattering realization/adapter lemmas, and
both raw scattering-realization lemmas.

## Non-claims

- The matrices describe fixed-carrier algebraic modal amplitudes. Their power statements are
  squared-amplitude bookkeeping, not electromagnetic energy or power theorems.
- The symmetric beam matrix and one-port mirror coefficient are declared reduced laws. No
  reciprocity, time reversal, reverse-incidence Maxwell, or modal-completeness claim is made.
- No geometry, coating, material interface, propagation, reference-plane, bandwidth, stability,
  causality, dispersion, measurement, or physical-realization claim is made.
- Exact “realization” means equality of the independent algebraic behavior and scattering graph;
  it does not certify fabrication or a Maxwell boundary-value model.
- The regression coefficients are fail-capable algebraic sentinels, not measured component data.
  Human verification remains required by `AI-POLICY.md`.

## Reviewer map

1. Read `BeamSplitter.lean:62-181` for the independent mixer, behavior, and realization.
2. Read `BeamSplitter.lean:186-235` for exact modal-power scaling and unitary classification.
3. Read `Mirror.lean:57-153` for the one-port law, independent behavior, and realization.
4. Read both Physical modules from their A sections through their direct family witnesses.
5. Read `PhysicalPortSuiteRegression.lean:62-179` for primitive nonzero component actions.
6. Read lines 183-518 for the explicit indexed matrix and positive aggregate action.
7. Read lines 522-759 for the hostile endpoint-swap matrix, action, and inequality.

## Exact validation record

The exact gated source `b9dc4cbb9a8a47e4d995e1be56ddf40d697615b1` was checked under
`lake-lock`. Temporary sorted registration of all five modules was used for declaration linters
and then removed.

- targeted build of `Physlib.Optics.Components.PhysicalPortSuiteRegression`: passed,
  2719 jobs;
- `runPhyslibLinters`: Physlib and QuantumInfo passed, including `simpNF`;
- committed-state `lint-style.sh`: passed;
- `git diff --check`: passed;
- file lengths are 240, 221, 161, 203, and 793, all below 1500 lines;
- the per-file maximum line lengths are 97, 99, 99, 99, and 100 Unicode codepoints;
- no file contains `theorem`, `sorry`, `axiom`, `native_decide`, `maxHeartbeats`, or
  `Lean.ofReduceBool`;
- all module docs use the four literal required headings and matching section TOCs;
- production imports no regression module; and
- relative to `110eb5cd`, the source diff contains exactly the five authorized new files.

Temporary registration was restored byte-identically. `Physlib.lean` had SHA-256
`a76a905b6d702efe94fa12ef5bd68cf6dfee745428ae35ac155dc148b6de574d` before and after the gate.
This final cutoff child changes only `HANDOFF.md`.
