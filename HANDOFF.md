# S7D slice 4b handoff: DCDR observable claim boundaries

## Cutoff identity

- Branch: `optics/s7d-dcdr`.
- Required sync target: `9e82661209fb4984e846936bf90abb1ef0bdf243`.
- Exact sync merge: `85e7f88a62839b20e294f248397de6add638067e`.
- Gated Lean source head: `4a5f95fb1e4ebde7d9b8f79beb40c6807b392732`.
- Source commit after the sync merge:
  - `4a5f95fb` — demote the strict adaptation and complete the observable non-claims.
- The final cutoff commit is a HANDOFF-only child of the gated source head.

The sync merge had one expected modify/delete conflict: development deletes lane HANDOFF files.
The merge took development's deletion, and this slice-4b HANDOFF was recreated only after the
source fix and gate.

## Files and registration request

Changed modules:

- `Physlib/Optics/Systems/DCDR/Observables.lean` — 222 lines.
- `Physlib/Optics/Systems/DCDR/ObservablesRegression.lean` — 396 lines.

The registration request remains:

```lean
public import Physlib.Optics.Systems.DCDR.Observables
public import Physlib.Optics.Systems.DCDR.ObservablesRegression
```

Add them in sorted order between `DCDR.Netlist` and the already registered `DCDR.Poles` imports.
The cutoff gate used those two temporary registrations. They were removed afterward;
`Physlib.lean` is byte-identical to the exact sync state, with SHA-256
`dc20f2cc3700122c99335a56dc1184c4073d97db1e4f48d59e3d1fbd5cfb1360`.

Every DCDR file remains below 1500 lines. The unchanged largest files are
`ResponseRegression.lean` at 1397 lines and `Bridge.lean` at 1362 lines.

## BB disposition

### 1. Strict adaptation is a lemma

`printedIncoherent_allZerosInsideUnitDisk_of_strict` is now a `lemma`
(`Observables.lean:180-188`). It is a strict Physlib adaptation, not the literal published
implication.

That classification is forced by the formal boundary already accepted by BB:

- FMICS'15 Theorem 5 prints `norm (Complex.sqrt (C/L)) <= 1`;
- FMICS'15 Definition 7 concludes the strict condition `norm z < 1`;
- at `G1 = G2 = G3 = 1`, `k1 = k2 = 0`, all three printed hypotheses hold while the finite zero
  `z = 1` violates the strict conclusion (`ObservablesRegression.lean:365-392`).

The literal printed Theorem 5 implication is therefore false at the norm-one boundary. The strict
Physlib lemma assumes a strengthened `< 1` predicate and cannot inherit the source theorem's
keyword merely because its algebra follows the source calculation.

The production overview now says explicitly that this is the same defect class as FMICS'15
Theorem 4: a non-strict hypothesis cannot establish Definition 7's strict conclusion
(`Observables.lean:28-32`). The exact printed audit predicate remains separate, and only the valid
strict-to-printed implication is retained (`:146-172`).

### 2. Claim boundary completed in both modules

The production non-claims now state all of the requested boundaries
(`Observables.lean:52-60`):

- neither normalized-modal power nor electromagnetic power is introduced;
- no E3b power bridge is used;
- no causality or time-domain interpretation is supplied; and
- the existing physical-resonance, frequency-response, passivity, BIBO, coordinate, and
  coherent/incoherent non-claims remain.

The regression module states the same normalized-modal/EM-power and causality/time-domain
boundaries (`ObservablesRegression.lean:50-58`). Its independence prose now calls the production
declaration a result/lemma rather than an observable theorem (`:22-25`, `:325-330`).

## Accepted substance retained unchanged

BB passed the slice-4 substance; this cutoff does not alter any definition, statement, proof, or
fixture body.

- `ResponseReduction.allZerosInsideUnitDisk` remains the certified reduced response's finite
  reciprocal-`z` predicate (`Observables.lean:81-88`).
- The printed incoherent numerator remains exactly `L*q - C*q^3`, with
  `L = (1-k1)(1-k2)G1 + k1*k2*G2` and
  `C = (1-2*k1)(1-2*k2)G1*G2*G3` (`:98-120`).
- `PrintedIncoherentTheoremFiveConditions` retains the printed non-strict square-root bound and
  both nonzero hypotheses (`:140-152`). The two nonzero hypotheses remain credited to FMICS'15
  itself as discoveries absent from Binh [5], not to Physlib (`:22-26`, `:140-144`).
- `PrintedIncoherentStrictAllZerosConditions` remains a separate strict predicate (`:154-165`).
- No declaration identifies the source's printed incoherent `1-k`/`k` model with its unprinted
  coherent N7 `t`/`-I*k` branch (`:34-36`).
- The coherent positive fixture still has a finite zero at `z = 1/2` and proves the universal
  all-zeros predicate by direct rational-data expansion
  (`ObservablesRegression.lean:317-342`).
- The coherent boundary fixture still has the finite zero `z = 1` and directly rejects the strict
  predicate (`:344-357`).
- The separate printed boundary still proves all three source assumptions while rejecting both
  Physlib's strict condition and the strict zero conclusion (`:365-392`).

The regression anchors still do not invoke
`printedIncoherent_allZerosInsideUnitDisk_of_strict` or another observable result.

## Reused APIs and source pins

- `ReducedRationalResponse.zZeros` removes formal `q = 0` and transports nonzero roots by
  `q = z^-1` at `Physlib/Optics/Systems/DelayTransfer/Stability.lean:141-146`.
- `ReducedRationalResponse.AllZerosInsideUnitDisk` is the reused literal predicate at
  `Physlib/Optics/Systems/DelayTransfer/Stability.lean:234-239`.
- The response-indexed DCDR reduction certificate is `ResponseReduction` at
  `Physlib/Optics/Systems/DCDR/Poles.lean:647-654`.
- The N7 directional-coupler cross coefficient is `-I*k` at
  `Physlib/Optics/Components/DirectionalCoupler.lean:62-70`.
- FMICS'15 Definition 7 and Theorem 5 are indexed at
  `/Users/aadarwal/src/aadarwal/physlib-parity/HOL-CORPUS.md:316-323`.
- The primary printed hypotheses and the paper's credit for the two nonzero discoveries are at
  `/private/tmp/claude-501/-Users-aadarwal-src-aadarwal-physlib/25cc2ec7-865f-4379-ab2d-a78ab2bf365b/scratchpad/papers/FMICS15_1.txt:622-638`.

## Public declarations

All names and types are unchanged from BB. All are in `Optics.DCDR`, except the first definition
is nested in `Optics.DCDR.ResponseReduction`.

Production declarations in `Observables.lean`:

- `ResponseReduction.allZerosInsideUnitDisk` (`:87`).
- `printedIncoherentZeroLinearCoefficient` (`:99`).
- `printedIncoherentZeroCubicCoefficient` (`:104`).
- `printedIncoherentZeroPolynomial` (`:109`).
- `eval_printedIncoherentZeroPolynomial` (`:115`).
- `PrintedIncoherentAllZerosInsideUnitDisk` (`:128`).
- `PrintedIncoherentTheoremFiveConditions` (`:146`).
- `PrintedIncoherentStrictAllZerosConditions` (`:159`).
- `PrintedIncoherentStrictAllZerosConditions.toTheoremFiveConditions` (`:168`).
- `printedIncoherent_allZerosInsideUnitDisk_of_strict` (`:185`, now a lemma).

Regression declarations in `ObservablesRegression.lean`:

- `insideZerosParameters` (`:76`), `boundaryZerosParameters` (`:84`), and their admissibility
  lemmas (`:92`, `:97`).
- `insideZerosNumerator`, `insideZerosDenominator`, `boundaryZerosNumerator`, and
  `boundaryZerosDenominator` (`:108-122`).
- The six direct loop/denominator/numerator expansions (`:124-203`).
- The six nonzero and explicit-Bezout coprimality lemmas (`:212-253`).
- `insideZerosReducedResponse` and `boundaryZerosReducedResponse` (`:256`, `:264`).
- `insideZerosRationalReduction` and `boundaryZerosRationalReduction` (`:272`, `:286`).
- `insideZerosResponseReduction` and `boundaryZerosResponseReduction` (`:300`, `:306`).
- `insideZerosResponseReduction_half_mem_zZeros` (`:318`).
- `insideZerosResponseReduction_allZerosInsideUnitDisk` (`:330`).
- `boundaryZerosResponseReduction_one_mem_zZeros` (`:345`).
- `boundaryZerosResponseReduction_not_allZerosInsideUnitDisk` (`:353`).
- `printedIncoherentTheoremFiveConditions_boundary` (`:366`).
- `printedIncoherentStrictAllZerosConditions_boundary_fails` (`:373`).
- `printedIncoherentZeroPolynomial_boundary_one` (`:380`).
- `printedIncoherentAllZerosInsideUnitDisk_boundary_fails` (`:387`).

## Validation binding map

The slice-4 bindings remain unchanged:

- `Optics.DCDR.ResponseReduction.allZerosInsideUnitDisk`.
- `Optics.DCDR.insideZerosResponseReduction_half_mem_zZeros`.
- `Optics.DCDR.insideZerosResponseReduction_allZerosInsideUnitDisk`.
- `Optics.DCDR.boundaryZerosResponseReduction_one_mem_zZeros`.
- `Optics.DCDR.boundaryZerosResponseReduction_not_allZerosInsideUnitDisk`.
- `Optics.DCDR.PrintedIncoherentTheoremFiveConditions`.
- `Optics.DCDR.PrintedIncoherentStrictAllZerosConditions`.
- `Optics.DCDR.printedIncoherent_allZerosInsideUnitDisk_of_strict` (lemma).
- `Optics.DCDR.printedIncoherentTheoremFiveConditions_boundary`.
- `Optics.DCDR.printedIncoherentStrictAllZerosConditions_boundary_fails`.
- `Optics.DCDR.printedIncoherentAllZerosInsideUnitDisk_boundary_fails`.

The printed declarations remain an audit, not a coherent/incoherent parity bridge. IP-10 remains
non-comparable under the IP-08 discipline.

## Goal scope and non-claims

This cutoff preserves the accepted S7D observable evidence for the quoted bullet

> "poles, zeros, and stability results"

and the §S4P rule declining FMICS'15's word "resonance" for a mere all-zeros-inside predicate.

No physical resonance, physical-frequency, normalized-modal power, electromagnetic power, E3b
power bridge, passivity, losslessness, BIBO, stability, material, causality, or time-domain result
is claimed. Formal `q` and reciprocal `z` remain algebraic coordinates. No coherent/incoherent
equivalence or FMICS'15 parity discharge is claimed.

## Gate record

At committed source head `4a5f95fb`, the focused warnings-as-errors build of `Observables` and
`ObservablesRegression` completed successfully. The shipped `./scripts/lint-style.sh` exited zero
on committed state; every DCDR file remains below the 1500-line cap.

With only `Observables` and `ObservablesRegression` inserted temporarily in sorted order in
`Physlib.lean`, this single locked command exited zero:

```text
lake-lock env bash -c 'lake exe cache get &&
  lake --wfail build <all twelve DCDR production/regression targets> &&
  lake exe runPhyslibLinters && lake exe lint_all'
```

The warnings-as-errors target build completed successfully with 2787 jobs.
`runPhyslibLinters` passed for Physlib and QuantumInfo. `lint_all` exited zero: its full build,
illegal-import, PhyslibAlpha-registration, duplicate-tag, sorry/pseudo-attribution, declaration,
and transitive-import phases completed. Its registration advisory named only unrelated modules
already present at the sync target, including `AllPassZTransform*`, `AffineBoxLocalDivergence`,
`PlanarRectangleLocalStokes`, and `PlanarSplitRectangleStokes`. The style/transitive advisories
were repository baseline and named neither edited module. `Physlib.lean` was restored
byte-identically before this HANDOFF was written.
