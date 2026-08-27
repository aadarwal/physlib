# S7D slice 10 handoff: DCDR second-order coherency observables

## Cutoff identity

- Branch: `optics/s7d-dcdr`.
- Exact sync target: `9c1f4929d20a17fcc7ada2c37c1e5f2f82b3df38`.
- Sync merge: `e32d42d6fe4c7d7c1777793832f0c5c67db7756d`.
- Gated source: `e32d42d6fe4c7d7c1777793832f0c5c67db7756d`.
- This file is the HANDOFF-only cutoff child.
- `Physlib.lean` is unchanged. Its restored SHA-256 is
  `f7486c686c1d5087c1cb8a87f33b3af2dd11cb761b14fa0ebbc0a0e9489d0a20`.

The build cache was refreshed from the `optics-development` worktree immediately after the exact
sync merge. The semantic source delta from the named sync target is exactly the two Lean modules
listed below. The retained lane `HANDOFF.md` is not part of the requested source merge.

## Goal resolution

At this cutoff ref, `goal.md:2453` says verbatim:

> - coherent and incoherent interpretations through N6c;

The generic status row at `goal.md:2842` says verbatim:

> | N6c coherent/incoherent observables | done | P2a, N5, N6a | PSD amplitude/channel-power
> coherencies, congruence response, trace power bounds/equalities, incoherent sums, channel
> powers, and explicit cross-term identity |

This slice closes the DCDR-specific word `coherent` with rank-one amplitude coherencies and closes
the DCDR-specific word `incoherent` only in N6c's precise second-order sense: diagonal coherency
data or mutually decorrelated coherency contributions. It does not identify the coherent N7 DCDR
with FMICS'15's separately printed incoherent coefficient model.

The existing status at `goal.md:2412-2416` still says that the ring and DCDR X-01 agreements are
packaged on their respective domains and concludes:

> Thus X-01 is complete only in this systemwise sense.

This slice does not alter that result. X-01 remains closed only in the systemwise sense, never as
an equality between the ring and DCDR response values.

## Files and registration request

- `Physlib/Optics/Systems/DCDR/Coherency.lean`: proof-gated specialization of generic N6c
  transport to the complete two-channel DCDR response.
- `Physlib/Optics/Systems/DCDR/CoherencyRegression.lean`: independent exact second-order anchors,
  hostile negatives, and a separate production-agreement fixture.

Please register these imports in repository-sorted order:

```lean
public import Physlib.Optics.Systems.DCDR.Coherency
public import Physlib.Optics.Systems.DCDR.CoherencyRegression
```

No existing production or regression module was edited. Production does not import the new
regression module.

## Validation names

- `sum_externalIncident` —
  `Physlib/Optics/Systems/DCDR/Coherency.lean`.
- `sum_externalOutgoing` —
  `Physlib/Optics/Systems/DCDR/Coherency.lean`.
- `responseCoherency_rankOne_channelPowers` —
  `Physlib/Optics/Systems/DCDR/Coherency.lean`.
- `responseCoherency_source_channelPower` —
  `Physlib/Optics/Systems/DCDR/Coherency.lean`.
- `responseCoherency_diagonal_channelPowers` —
  `Physlib/Optics/Systems/DCDR/Coherency.lean`.
- `responseCoherency_entry` —
  `Physlib/Optics/Systems/DCDR/Coherency.lean`.
- `responseCoherency_trace_twoChannels` —
  `Physlib/Optics/Systems/DCDR/Coherency.lean`.
- `responseCoherency_source_trace` —
  `Physlib/Optics/Systems/DCDR/Coherency.lean`.
- `responseCoherency_decorrelated_channelPower` —
  `Physlib/Optics/Systems/DCDR/Coherency.lean`.
- `responseCoherency_source_crossTerm` —
  `Physlib/Optics/Systems/DCDR/Coherency.lean`.
- `coherencyRegressionTransform` —
  `Physlib/Optics/Systems/DCDR/CoherencyRegression.lean`.
- `coherencyRegressionTransform_matches_response` —
  `Physlib/Optics/Systems/DCDR/CoherencyRegression.lean`.
- `coherencyRegressionFirst` —
  `Physlib/Optics/Systems/DCDR/CoherencyRegression.lean`.
- `coherencyRegressionSecond` —
  `Physlib/Optics/Systems/DCDR/CoherencyRegression.lean`.
- `coherencyRegression_amplitudes_add` —
  `Physlib/Optics/Systems/DCDR/CoherencyRegression.lean`.
- `coherencyRegression_coherent_channelPower` —
  `Physlib/Optics/Systems/DCDR/CoherencyRegression.lean`.
- `coherencyRegression_decorrelated_channelPower` —
  `Physlib/Optics/Systems/DCDR/CoherencyRegression.lean`.
- `coherencyRegression_crossTerm` —
  `Physlib/Optics/Systems/DCDR/CoherencyRegression.lean`.
- `coherencyRegression_coherent_sub_decorrelated` —
  `Physlib/Optics/Systems/DCDR/CoherencyRegression.lean`.
- `coherencyRegression_models_differ` —
  `Physlib/Optics/Systems/DCDR/CoherencyRegression.lean`.
- `coherencyRegressionNonrealAmplitude` —
  `Physlib/Optics/Systems/DCDR/CoherencyRegression.lean`.
- `coherencyRegression_nonreal_offDiagonal` —
  `Physlib/Optics/Systems/DCDR/CoherencyRegression.lean`.
- `coherencyRegression_unstarred_offDiagonal` —
  `Physlib/Optics/Systems/DCDR/CoherencyRegression.lean`.
- `coherencyRegression_conjugation_is_loadBearing` —
  `Physlib/Optics/Systems/DCDR/CoherencyRegression.lean`.
- `coherencyRegression_production_agreement` —
  `Physlib/Optics/Systems/DCDR/CoherencyRegression.lean`.

## Generic N6c route and DCDR specialization

The reused generic engine is `FlatNetlist.responseCoherency` at
`Physlib/Optics/Network/Coherency.lean:452`. It transports a supplied input coherency by
`H * Gamma * H^H`, where `H` is the proof-gated complete response transform. The generic
rank-one, diagonal, decorrelated, and cross-term adapters are at lines 189, 297, 326, 342, and
359 of that file.

The DCDR response is not restated as free matrix data. The two output coordinates are derived from
the complete forward and reverse N7 equations by `response_nominal_reference_coordinates` at
`Physlib/Optics/Systems/DCDR/NominalChain.lean:180`. Its four proof-gated response entries are at
lines 220-253.

On `Parameters.HasNonzeroDenominator`, the new specialization proves:

- rank-one coherent power at both nominal output channels;
- source-only coherent channel power `normSq (transfer p * amplitude)`;
- both channel powers for nonnegative diagonal second-order input data;
- every output coherency entry as the explicit two-channel N6c double sum;
- the complete trace as the sum of the two named output-channel powers;
- the source-only trace formula;
- channel-power additivity for supplied mutually decorrelated coherencies; and
- the exact phase-sensitive coherent-minus-decorrelated cross term.

The diagonal and decorrelated results do not delete a cross term from a coherent input. They apply
to different supplied second-order data: a diagonal coherency or `incoherentSum`. The coherent
formula retains the explicit term

```text
2 Re((transfer p * first) * star (transfer p * second)).
```

## Independent regression audit

The fixture reuses the accepted stable DCDR point at `z = I`, hence formal delay `q = z^-1 = -I`.
The response value is `-(7/8) I`, and the independently stated raw response matrix is

```text
[       0       -(7/8) I ]
[ -(7/8) I          0    ].
```

`coherencyRegressionTransform_matches_response` connects that raw `Fin 2` matrix to the four
existing response entries proved from N7. It is an agreement lemma only; none of the numeric
second-order anchors below uses it.

Two input amplitudes contribute `1` and `-1` on the same incident channel. Direct expansion of
`CoherencyMatrix.map`, the outer products, both matrix products, and both `Fin 2` sums gives:

- coherent amplitude sum: `0`;
- coherent output channel power: `0`;
- decorrelated second-order output channel power: `49/32`;
- explicit coherent-minus-decorrelated cross term: `-49/32`; and
- coherent power minus decorrelated power: `-49/32`.

The dependency audit is:

- `coherencyRegression_coherent_channelPower` unfolds primitive matrices and does not use a
  production DCDR coherency lemma.
- `coherencyRegression_decorrelated_channelPower` unfolds both rank-one matrices and their sum; it
  does not use `responseCoherency_decorrelated_channelPower` or the generic derived adapter.
- `coherencyRegression_crossTerm` unfolds the raw linear action and does not use
  `responseCoherency_source_crossTerm`.
- `coherencyRegression_models_differ` compares the independently pinned values `0` and `49/32`,
  so conflating coherent cancellation with decorrelated addition fails on the same fixture.
- `coherencyRegression_production_agreement` invokes production only after the independent
  decorrelated value has been pinned in its first conjunct.

For the separate nonreal orientation check, input amplitude `[1, I]` gives

```text
(H * Gamma * H^H) 0 1 = (49/64) I.
```

Replacing `H^H` with the ordinary transpose gives `-(49/64) I`.
`coherencyRegression_conjugation_is_loadBearing` proves those entries unequal. Both values are
expanded from matrix primitives and do not route through a coherency lemma under test. Thus a
conjugation-sign error is fail-capable.

## Gate record

All Lean jobs ran through the machine-wide `lake-lock`.

- After exact sync, the cache was refreshed with the required `rsync --ignore-existing` command.
- Targeted warnings-as-errors builds of both new modules passed: 2,805 jobs.
- With both modules temporarily registered in repository-sorted order, the root
  warnings-as-errors `Physlib` build passed: 5,013 jobs.
- Only after that fresh root build, `runPhyslibLinters` passed for both Physlib and QuantumInfo.
- `scripts/lint-style.sh` passed on both committed new files.
- The repository-wide `module_doc_lint` continues to exit on legacy modules outside this slice.
  Its emitted findings did not name either new module. Both new modules have the four literal
  headings, and their tables of contents exactly match their numbered section headings.
- There are zero banned declarations, zero `theorem` declarations, and no line over 100
  codepoints. The files have 300 and 292 lines; their maxima are 98 codepoints.
- `git diff --check` passes, and `Physlib.lean` was restored byte-for-byte after temporary
  registration.

## Claims, non-claims, and human audit

The results are normalized-modal, second-order channel observables for the proof-gated coherent
DCDR response. The word `power` in the API means `CoherencyMatrix.channelPower`; it does not claim
physical power flux or electromagnetic energy.

This slice makes no claim of physical resonance, power flux, electromagnetic energy, reciprocity,
physical time reversal, physical reference planes, coherent-incoherent equivalence, causality or
Maxwell time-domain meaning, physical-frequency meaning, or HOL-script semantics. It makes no
BIBO claim beyond the separate S4P gate. N6b reciprocity remains blocked on its convention data.

Per `AI-POLICY.md`, a human author must independently certify the N6c interpretation, the nominal
channel ordering, the exact values `0`, `49/32`, `-49/32`, and `(49/64) I`, and the stated boundary
between second-order decorrelation and FMICS'15's printed coefficient model before merge.
