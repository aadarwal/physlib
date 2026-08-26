# S7D slice 6 handoff: exact audit of FMICS'15's passive DCDR case

## Cutoff identity

- Branch: `optics/s7d-dcdr`.
- Exact required sync target: `6df351b47fc836b37b8f7ff539b3b226a6e9b9b5`.
- Sync operation: clean fast-forward to that exact hash; no later development head was merged.
- Gated Lean source head: `d222e86db6c314c516c65aadad30a97b67b762f7`.
- The final cutoff is this HANDOFF-only child of the gated source head.
- The controller later announced `5fc99609` as a new sync target with no forced mid-slice
  re-sync; this cutoff intentionally remains based on the required `6df351b4` target.

## Scope and source text

This cutoff targets parity row IP-11 at
`/Users/aadarwal/src/aadarwal/physlib-parity@3e7ee24:PARITY-LEDGER.md:118` and the
following goal at `goal.md:2425-2426`:

> "an exact or interval-certified, human-audited version of the source's reported unstable
> passive parameter case."

IP-11 records that the source pole list is supplied as data and asks Physlib for the stronger
exact audit.

FMICS'15 p. 175 states (`scratchpad/papers/FMICS15_1.txt:640-650`):

> "In an effort to validate the stability results provided in [5], we discovered that both given
> values of poles cannot satisfy the stability conditions. We formally proved the instability of
> the DCDR in case of passive operation (i.e., G1 = G2 = G3 = 1) with k1 = k2 = 0.9 as follows:
> unstable psp (lambda z. DCDR (1/z) (1/z) (1/z) 0.9 0.9
> [0.905539; -0.905539]), where unstable psp sys = not (is stable psp sys) as described in
> Definition 7."

The ASCII rendering changes typography only. The human-audit sheet below pins each number and
sign to an exact Lean term.

## Files and registration request

Substantive slice-6 files:

- `Physlib/Optics/Systems/DCDR/SourceBridge.lean` — 407 lines; the passive source value and its
  coherent unit-delay dictionary image.
- `Physlib/Optics/Systems/DCDR/PassiveCaseRegression.lean` — 868 lines; exact printed and coherent
  quotients, both coordinate root sets, decimal rejection, interval bound, independent Schur
  anchors, and the printed-claim audit.

Registration request, in sorted DCDR order:

```lean
public import Physlib.Optics.Systems.DCDR.PassiveCaseRegression
```

The slice-5 `SourceBridge` and `SourceBridgeRegression` registrations are landing separately, as
the controller specified. `Physlib.lean` was not touched, including temporarily. Production
imports no regression module.

Every DCDR file remains below 1500 lines. The largest is the unchanged-code
`ResponseRegression.lean` at 1417 lines after documentation normalization; the new regression is
868 lines.

## Module-doc normalization (doc-only)

Commit `d222e86d` changes documentation only. It installs the four literal headings required by
the new house rule, makes each TOC exactly match its section headings, expands formerly inline
section headings into linter-visible module-doc blocks, and places non-claims first under
`## iv. References`. No declaration or proof text changed.

Touched files:

- `DCDR/Bridge.lean`.
- `DCDR/Graph.lean`.
- `DCDR/Mason.lean`.
- `DCDR/Netlist.lean`.
- `DCDR/Observables.lean`.
- `DCDR/ObservablesRegression.lean`.
- `DCDR/PassiveCaseRegression.lean`.
- `DCDR/Poles.lean`.
- `DCDR/PolesRegression.lean`.
- `DCDR/Response.lean`.
- `DCDR/ResponseRegression.lean`.
- `DCDR/SourceBridge.lean`.
- `DCDR/SourceBridgeRegression.lean`.
- `DCDR/Topology.lean`.
- `DCDR/TopologyRegression.lean`.

All 15 modules build together. An exact file-by-file check using the shipped linter's heading and
TOC transformation reports all 15 clean, including the three not yet reachable from
`Physlib.lean`.

## Controller-brief coordinate correction

The initial slice-6 routing brief assigned `sqrt (41/50)` to the formal-`q` roots of
`D(q) = 1 - (41/50) q^2`. S7D stopped and reported that this coordinate was inverted. The
controller confirmed this correction before implementation:

| Coordinate | Exact set | Squared modulus | Meaning |
|---|---|---:|---|
| formal `q` | `{sqrt (50/41), -sqrt (50/41)}` | `50/41 > 1` | roots of `D(q)` |
| reciprocal `z` | `{sqrt (41/50), -sqrt (41/50)}` | `41/50 < 1` | poles for `q=z^-1` |

Every statement in this cutoff uses the corrected ZT-10/IP-76 legend explicitly. The source
decimals are candidate reciprocal-`z` poles; their reciprocals are the corresponding candidate
formal-`q` roots.

## Exact printed and coherent quotients

Primitive substitution into FMICS'15 Theorem 3 gives the two printed loop terms separately:

- `k1*k2*G1*G3 = 81/100`;
- `(1-k1)*(1-k2)*G2*G3 = 1/100`.

Thus the printed denominator is exactly
`1 - (81/100 + 1/100) q^2 = 1 - (41/50) q^2`. The numerator is
`(41/50) q - (16/25) q^3`. An explicit Bezout identity proves that the quotient is coprime, so
the exact denominator roots survive reduction.

The formal-`q` and reciprocal-`z` root sets are enumerated by direct polynomial evaluation, not
by the abstract S4P pole or Schur lemmas. Their squared-modulus anchors are likewise expanded
from the exact roots. They conclude `passivePrintedReducedResponse.IsSchurStable`, whose meaning
is the strict reciprocal-`z` unit-disk predicate at
`Physlib/Optics/Systems/DelayTransfer/Stability.lean:282-285`.

The coherent dictionary image is audited separately. Its loop coefficient is `-4/5`, so its
denominator is `1 + (4/5) q^2`; its formal roots are
`{sqrt (5/4)*I, -sqrt (5/4)*I}` and its reciprocal poles are
`{sqrt (4/5)*I, -sqrt (4/5)*I}`. Those reciprocal poles also satisfy the strict Schur gate. The
printed and coherent denominators are proved unequal. This is a divergence result, not an
equivalence.

## Exact decimal audit

The displayed magnitude is stored as the rational `905539/1000000`. Multiplying
`D(z^-1)` by `z^2` gives the finite reciprocal-`z` polynomial `z^2 - 41/50`. Direct integer
arithmetic proves

```text
905539^2 = 820000880521 != 820000000000 = 820000 * 10^6.
```

Both signed `z` evaluations are exactly `880521/10^12`, not zero. Equivalently, evaluating the
formal denominator at each reciprocal gives `880521/820000880521`, not zero. Therefore neither
signed decimal belongs to the exact reciprocal-`z` pole set, and neither reciprocal belongs to
the formal-`q` root set.

The human-checkable rational squeeze is

```text
9055385/10000000 < sqrt (41/50) < 9055386/10000000.
```

Each signed displayed decimal therefore has absolute error strictly between `4/10000000` and
`5/10000000` from the corresponding exact reciprocal-`z` pole. No `Float`, decimal oracle,
`native_decide`, or imported pole/stability theorem is used.

## Printed-claim audit

| Printed item | Lean-checked fact | Disposition |
|---|---|---|
| Thm. 3 passive denominator | exact `z` poles have modulus squared `41/50` | stable by Def. 7 |
| Thm. 4 hypotheses | expression `41/50`; sqrt norm `<= 1`; expression nonzero | both hold |
| p. 175 pole list | both decimals are nonroots in `z`, and reciprocally in `q` | rounded data |
| p. 175 prose | prints `unstable psp ...` | conflicts under the exact-pole reading |

At this passive point `G1 = G2 = G3`, so Theorem 3's printed `G1*G3` term and Theorem 4's printed
`G1*G2` term have the same exact value. The generic indexing mismatch recorded in slice 5 does
not explain this particular case.

This is a candidate eighth source finding, restricted to the printed text. A possible alternative
reading is that the HOL `psp` predicate consumes the displayed pole list as supplied data, so
"unstable" may reject the rounded numbers as invalid poles rather than locate an actual pole
outside the unit disk. The script delegated to reference [3] is unavailable (the recorded URL
returns 404), so this cutoff does not choose between those readings or claim what the script
implements. It makes no claim about Binh [5].

## Human audit sheet

Lean certifies the right two columns; a human must certify that each source row was transcribed
and interpreted correctly. Human sign-off remains **OPEN** at this cutoff.

The `SourceParameters` prefix below is
`Optics.DCDRSourceBridge.passiveCaseSourceParameters`; all other short names are in
`Optics.DCDR`.

| Printed source | Lean term | Exact checked value |
|---|---|---|
| p. 175 `G1 = 1` (`:645-646`) | `SourceParameters.G1` | `1` |
| p. 175 `G2 = 1` (`:645-646`) | `SourceParameters.G2` | `1` |
| p. 175 `G3 = 1` (`:645-646`) | `SourceParameters.G3` | `1` |
| p. 175 `k1 = 0.9` (`:646`) | `SourceParameters.k1` | `9/10` |
| p. 175 `k2 = 0.9` (`:646`) | `SourceParameters.k2` | `9/10` |
| p. 175 first pole (`:648`) | `passiveReportedPoleMagnitude` | `905539/1000000` |
| p. 175 second pole (`:648`) | `-passiveReportedPoleMagnitude` | `-905539/1000000` |
| Thm. 3 first loop term (`:572-576`) | `passiveCase_printedLoopTerms.1` | `81/100` |
| Thm. 3 second loop term (`:572-576`) | `passiveCase_printedLoopTerms.2` | `1/100` |
| Thm. 3 denominator (`:572-576`) | `passivePrintedDenominator` | `1-(41/50)q^2` |
| corrected formal coordinate | `passivePrintedReducedResponse.poles` | `+/-sqrt(50/41)` |
| reciprocal coordinate | `passivePrintedReducedResponse.zPoles` | `+/-sqrt(41/50)` |
| Thm. 4 expression (`:610-618`) | `passiveCase_printedTheoremFourExpression` | `41/50` |
| first coherent through field | first coupler `throughAmplitude` | `sqrt(1/10)` |
| first coherent cross field | first coupler `crossAmplitude` | `sqrt(9/10)` |
| second coherent through field | second coupler `throughAmplitude` | `sqrt(1/10)` |
| second coherent cross field | second coupler `crossAmplitude` | `sqrt(9/10)` |
| coherent N7 loop coefficient | `passiveCaseUnitDelayParameters.loopCoefficient` | `-4/5` |
| coherent N7 denominator | `passiveCoherentDenominator` | `1+(4/5)q^2` |

Human certification requested:

- [ ] The five passive parameters match FMICS'15 p. 175.
- [ ] The two displayed pole decimals and their signs match p. 175.
- [ ] Theorem 3 was transcribed with the printed `G1*G3` and `G2*G3` indexing.
- [ ] Theorem 4 was transcribed with its printed `G1*G2` first term and both hypotheses.
- [ ] The `q=z^-1` coordinate correction and printed/coherent separation are accepted.

## Proof independence and failure sensitivity

- Parameter and coefficient anchors unfold the source dictionary and use exact rational
  arithmetic.
- Root sets are derived by factoring the hand-expanded quadratic evaluations.
- Schur anchors consume those enumerated sets and squared norms, not S4P's general theorem.
- Decimal nonroot anchors evaluate both coordinate polynomials directly.
- The rational squeeze compares exact rational squares to `41/50`.
- The coherent denominator is independently expanded and proved unequal to the printed one.

Changing a sign, source index, `41/50`, displayed decimal, or the `q=z^-1` convention breaks one
or more fixtures.

## Public declarations and validation map

Production declarations in `Optics.DCDRSourceBridge`:

- `passiveCaseSourceParameters` (`SourceBridge.lean:389`).
- `passiveCaseUnitDelayParameters` (`SourceBridge.lean:400`).

Validation should bind at least:

- `Optics.DCDR.passiveCaseSourceParameters_data` (`PassiveCaseRegression.lean:108`).
- `Optics.DCDR.passiveCase_printedLoopTerms` (`:142`).
- `Optics.DCDR.passiveCase_printedDenominatorPolynomial_expansion` (`:169`).
- `Optics.DCDR.passivePrintedReducedResponse_poles` (`:398`).
- `Optics.DCDR.passivePrintedReducedResponse_zPoles` (`:444`).
- `Optics.DCDR.passivePrintedFormalRoot_norm_sq` (`:505`).
- `Optics.DCDR.passivePrintedReciprocalPole_norm_sq` (`:519`).
- `Optics.DCDR.passivePrintedReducedResponse_isSchurStable` (`:534`).
- `Optics.DCDR.passiveCase_coherentDenominatorPolynomial_expansion` (`:196`).
- `Optics.DCDR.passiveCase_denominatorPolynomials_ne` (`:263`).
- `Optics.DCDR.passiveCoherentReducedResponse_poles` (`:558`).
- `Optics.DCDR.passiveCoherentReducedResponse_zPoles` (`:606`).
- `Optics.DCDR.passiveCoherentReducedResponse_isSchurStable` (`:704`).
- `Optics.DCDR.passiveReportedPole_integer_square_ne` (`:725`).
- `Optics.DCDR.passiveReportedPoles_zForm_evaluation` (`:730`).
- `Optics.DCDR.passiveReportedPoles_qForm_evaluation` (`:747`).
- `Optics.DCDR.passiveReportedPoles_not_mem_zPoles` (`:764`).
- `Optics.DCDR.passiveReportedReciprocals_not_mem_poles` (`:774`).
- `Optics.DCDR.passiveReportedPole_rational_squeeze` (`:781`).
- `Optics.DCDR.passiveReportedPole_absoluteError` (`:800`).
- `Optics.DCDR.passivePrintedTheoremFourConditions` (`:841`).

## Non-claims

This cutoff makes no physical-resonance claim, no coherent-incoherent equivalence claim, no BIBO
claim beyond S4P's existing gate, no normalized-modal or electromagnetic-power claim, no
causality or time-domain claim, no physical-frequency claim, no claim about the unavailable HOL
script's semantics, and no claim about Binh [5]. The Schur result is only the exact algebraic
reciprocal-`z` pole-location predicate.

## Gate record

At committed source head `d222e86d`:

- `lake exe cache get`: green.
- Full `lake --wfail build` of `Physlib` plus all 15 DCDR targets: green, 4942 jobs.
- `lake exe sorry_lint`: green.
- `lake exe runPhyslibLinters`: green for Physlib and QuantumInfo.
- `lake exe api_map_index`: green.
- `lake exe lint_all`: green.
- `./scripts/lint-style.sh`: green on committed state.
- `lake exe module_doc_lint`: every DCDR module green; the repository command remains nonzero
  only on out-of-lane modules at the pinned `6df351b4` sync. The controller's later
  `5fc99609` battery contains the conductor's outside-lane sweep and did not require a mid-slice
  re-sync.
- The exact heading/TOC check passes all 15 DCDR files, including unregistered modules.

`lake exe check_file_imports` reports the expected pending registrations. The DCDR entries are
`PassiveCaseRegression`, `SourceBridge`, and `SourceBridgeRegression`; the latter two are the
already dispatched slice-5 registration. The same report contains unrelated Electromagnetism,
Microring, and SpaceAndTime modules. This cutoff obeys the explicit instruction not to touch
`Physlib.lean`, which is byte-identical to the sync target.
