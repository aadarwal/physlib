# S7D slice 3b handoff: DCDR reciprocal coordinates and cancellation teeth

## Cutoff identity

- Branch: `optics/s7d-dcdr`.
- Required sync target: `f849f67439210200ed8e8cfbfec32840a40759da`.
- Exact sync merge: `248320f84571890660d661385fa64736a5f0b805`.
- Gated Lean source head: `dda88bc7c2e370e6b90ecfb53429ff480cd4c5ed`.
- Source commits after the sync merge:
  - `37bbaaf1` — rename the formal zero set and state the coordinate limitation.
  - `dda88bc7` — add the printed-boundary, cancellation, and asymmetric-Z fixtures.
- The final cutoff commit is a HANDOFF-only child of the gated source head.

## Files and registration request

Changed modules:

- `Physlib/Optics/Systems/DCDR/Poles.lean` — 731 lines.
- `Physlib/Optics/Systems/DCDR/PolesRegression.lean` — 758 lines.

Both modules remain below the 1500-line cap, as do all other DCDR modules. The registration
request is unchanged: add these sorted imports to `Physlib.lean` between `Netlist` and `Response`:

```lean
public import Physlib.Optics.Systems.DCDR.Poles
public import Physlib.Optics.Systems.DCDR.PolesRegression
```

The cutoff gate used those temporary registrations. They were removed after the gate;
`Physlib.lean` was never committed.

## Reviewer Z disposition

### 1. Printed Theorem 4 predicate and strictness separation

`PrintedIncoherentStabilityConditions` now applies the printed complex square root before taking
the norm and retains the nonzero-expression hypothesis
(`PolesRegression.lean:88-101`). The source predicate deliberately uses `<= 1`; it is not S4's
strict Schur predicate. The boundary fixture at all unit arguments proves the printed predicate
while its square-root norm is not `< 1` (`:104-113`). Thus replacing the printed non-strict bound
with a strict bound would be invalid. The module doc explicitly states that no implication between
the printed incoherent predicate and coherent strict Schur stability is proved (`:27-34`, `:60-70`).

The audited source text is FMICS'15 Theorem 4 at
`/private/tmp/claude-501/-Users-aadarwal-src-aadarwal-physlib/25cc2ec7-865f-4379-ab2d-a78ab2bf365b/scratchpad/papers/FMICS15_1.txt:610-627`:
the bound is the norm of the complex square root, and the expression is required to be nonzero.

### 2. Formal zero coordinate: option 2

This cutoff takes reviewer option 2. `ResponseReduction.actualZeros` was renamed to
`ResponseReduction.formalZeros` (`Poles.lean:657-665`). Its docstring says it is a formal-`q` set,
not `zZeros`, and that `q = 0` represents `z = infinity`. The active fixture is correspondingly
renamed `unstableResponseReduction_zero_mem_formalZeros` and explicitly says it is not evidence of
a finite reciprocal-Z zero (`PolesRegression.lean:681-687`).

The old `q = 0` statement is withdrawn as S-07 reciprocal-zero evidence. S4 makes the distinction
at `Physlib/Optics/Systems/DelayTransfer/Stability.lean:141-146`: `zZeros` contains only nonzero
formal roots transported by `q = z^-1` and omits `q = 0`.

### 3. Response-indexed cancellation sentinel

The new exact fixture has both coherent couplers `t = 1`, `k = 0` and all three gains equal to one
(`PolesRegression.lean:142-152`). Direct expansion, without a candidate/pole theorem, gives:

- loop polynomial `q^2` (`:283-290`);
- raw denominator `1 - q^2` (`:292-297`);
- selected raw numerator `q * (1 - q^2)` (`:299-310`);
- reduced quotient `q / 1` (`:370-375`, `:696-699`).

`cancellationSentinelRationalReduction` ties that common-factor reduction to the selected DCDR raw
numerator and denominator (`:406-421`), and `cancellationSentinelResponseReduction` ties it to the
compiled-response certificate (`:436-441`). This is a network response fixture, not S4's abstract
polynomial-only cancellation regression.

At `q = 1`, direct denominator substitution gives a raw root (`:702-706`). The operator-first proof
unfolds `candidateSingularities`, transfers bijectivity through the compiled/fixed feedback-operator
equality, and contradicts the displayed zero-denominator N5 state (`:714-733`). It never uses
`mem_candidateSingularities_iff` or a response-reduction pole-set theorem. Consequently:

- `q = 1` is an internal operator candidate singularity (`:714-733`);
- `z = 1` is an internal candidate pole (`:736-740`);
- `NoPoleCancellation 1` fails because the removed factor evaluates to zero (`:743-747`);
- `z = 1` is not an actual reduced response pole because the reduced denominator is one
  (`:749-755`).

These proofs are sensitive to the netlist-derived loop sign and selected-response wiring: changing
either raw polynomial breaks the direct expansions or the response-indexed reduction certificate.

### 4. Asymmetric reciprocal-Z anchor

The non-real stable anchor pins S4's convention at `z = I`:

- `zInverseEvaluation I = -I` (`PolesRegression.lean:537-541`);
- `q = -I` lies in the compiled response domain (`:544-551`);
- `z = I` lies in the reciprocal-Z response domain (`:553-562`);
- direct formal-delay response expansion gives `-(7/8) * I` (`:565-578`);
- S4's generic reciprocal-response transport gives the proof-gated Z response
  `-(7/8) * I` (`:583-593`);
- reversing the map to `q = I` gives `+(7/8) * I` (`:596-604`), and the explicit inequality
  proves the anchor distinguishes the two maps (`:607-614`).

The Z anchor does not invoke the DCDR theorem
`rationalZEliminationResponse_eq_responseModel`. It instantiates the generic S4 transport at
`Physlib/Optics/Systems/DelayTransfer/Evaluation.lean:483-495`, selects the network entry, and then
uses the already certified formal-delay N5 response before hand-expanding the rational data.

### 5. Production non-claim

The production module now explicitly withholds any time-domain impulse-response or causality
interpretation (`Poles.lean:61-66`).

## Reused APIs and pinned conventions

- The coherent directional-coupler cross coefficient is exactly `-I * k` at
  `Physlib/Optics/Components/DirectionalCoupler.lean:62-70`.
- The reciprocal convention is exactly `zInverseEvaluation z = fun _ => z^-1` at
  `Physlib/Optics/Systems/DelayTransfer/Basic.lean:233-239`.
- S4's proof-gated reciprocal response transport is
  `RationalNetlist.response_reciprocalZ_reindex_of_evaluation_eq` at
  `Physlib/Optics/Systems/DelayTransfer/Evaluation.lean:483-495`.
- S4 defines `RationalReduction.NoPoleCancellation` by nonvanishing of the removed factor and uses
  it for the raw-to-reduced root direction at
  `Physlib/Optics/Systems/DelayTransfer/Poles.lean:194-236`.
- S4's finite reciprocal zero/pole coordinate and strict Schur predicate are at
  `Physlib/Optics/Systems/DelayTransfer/Stability.lean:141-232`.
- Generic N5 well-posedness is feedback-operator bijectivity at
  `Physlib/Optics/Network/FlatNetlistElimination.lean:192-196`.
- The DCDR's displayed nonzero homogeneous state proves that a zero scalar denominator prevents
  fixed-netlist well-posedness at `Physlib/Optics/Systems/DCDR/Response.lean:383-434`.
- The pointwise rational/fixed DCDR feedback-operator equality used by the cancellation fixture is
  `rationalNetlist_feedbackOperator_eq` at `Poles.lean:430-448`.
- S4's BIBO equivalence remains restricted to `ProperCausalOnePole` at
  `Physlib/Optics/Systems/DelayTransfer/Stability.lean:306-405`; it is not applied here.
- The FMICS'15 Table 1 amplifier configuration and Theorem 4 audit are indexed at
  `/Users/aadarwal/src/aadarwal/physlib-parity/HOL-CORPUS.md:307-308`.

## Public declaration changes in slice 3b

All names are in namespace `Optics.DCDR` unless a nested namespace is shown.

Changed production declaration:

- `ResponseReduction.formalZeros` (`Poles.lean:664`) — renamed from `actualZeros`; formal-`q`
  numerator roots only.

Printed-predicate declarations:

- `PrintedIncoherentStabilityConditions` (`PolesRegression.lean:97`) — now uses `Complex.sqrt`.
- `printedIncoherentStabilityConditions_boundary` (`:104`).
- `printedIncoherentStabilityConditions_boundary_not_strict` (`:110`).

Cancellation fixture declarations:

- `cancellationSentinelCoupler` (`:142`).
- `cancellationSentinelParameters` (`:147`).
- `cancellationSentinelParameters_isAdmissible` (`:165`).
- `cancellationSentinelFactor` (`:279`).
- `cancellationSentinel_loopPolynomial_expansion` (`:283`).
- `cancellationSentinel_denominatorPolynomial_expansion` (`:292`).
- `cancellationSentinel_responseNumeratorPolynomial_expansion` (`:299`).
- `cancellationSentinelReducedResponse` (`:370`).
- `cancellationSentinelRationalReduction` (`:406`).
- `cancellationSentinelResponseReduction` (`:436`).
- `cancellationSentinelReducedResponse_eval` (`:696`).
- `cancellationSentinel_one_mem_rawDenominatorRoots` (`:702`).
- `cancellationSentinel_one_mem_candidateSingularities` (`:714`).
- `cancellationSentinel_one_mem_candidatePoles` (`:736`).
- `cancellationSentinel_not_noPoleCancellation` (`:743`).
- `cancellationSentinel_one_not_mem_actualPoles` (`:749`).

Asymmetric reciprocal-Z declarations:

- `zInverseEvaluation_I` (`:537`).
- `stable_neg_I_mem_responseDomain` (`:544`).
- `stable_I_mem_reciprocalZResponseDomain` (`:553`).
- `stable_rationalEliminationResponse_neg_I` (`:565`).
- `stable_rationalZEliminationResponse_I` (`:583`).
- `stable_responseModel_I_expansion` (`:596`).
- `stable_rationalZEliminationResponse_I_ne_reversed` (`:607`).

Renamed regression declaration:

- `unstableResponseReduction_zero_mem_formalZeros` (`:684`) — renamed from
  `unstableResponseReduction_zero_mem_actualZeros` and withdrawn as reciprocal-zero evidence.

All prior slice-3 rational-family, N5-response, candidate/actual-pole, stable Schur, and active
outside-pole declarations remain public and unchanged apart from line movement.

## Validation binding map

Validation should bind these exact new or changed names for Z2:

- Printed source audit:
  `Optics.DCDR.PrintedIncoherentStabilityConditions`,
  `Optics.DCDR.printedIncoherentStabilityConditions_boundary`, and
  `Optics.DCDR.printedIncoherentStabilityConditions_boundary_not_strict`.
- Coordinate correction:
  `Optics.DCDR.ResponseReduction.formalZeros` and
  `Optics.DCDR.unstableResponseReduction_zero_mem_formalZeros`.
  The latter is formal-`q` only and must not be bound as S-07 reciprocal-zero evidence.
- Reciprocal orientation:
  `Optics.DCDR.stable_rationalZEliminationResponse_I`,
  `Optics.DCDR.stable_responseModel_I_expansion`, and
  `Optics.DCDR.stable_rationalZEliminationResponse_I_ne_reversed`.
- Response-indexed cancellation:
  `Optics.DCDR.cancellationSentinelResponseReduction`,
  `Optics.DCDR.cancellationSentinel_one_mem_candidateSingularities`,
  `Optics.DCDR.cancellationSentinel_not_noPoleCancellation`, and
  `Optics.DCDR.cancellationSentinel_one_not_mem_actualPoles`.

The previously accepted S-07 positive and hostile anchors remain:

- `Optics.DCDR.stableReducedResponse_isSchurStable`;
- `Optics.DCDR.unstableAmplifierParameters_all_gains_gt_one`;
- `Optics.DCDR.unstableResponseReduction_two_mul_I_mem_actualPoles`;
- `Optics.DCDR.unstableReducedResponse_not_isSchurStable`.

## Goal text and scope

This rework preserves the delivered validation row:

> “DCDR pole/zero/stability theorems include the audited unstable parameter case”

The S-07 evidence is the exact `G_i > 1` active fixture, its response-indexed no-cancellation
certificate, and the actual reciprocal pole `2 * I` of norm two. The old formal root `q = 0` is no
longer presented as reciprocal-zero evidence.

The asymmetric anchor also exercises:

> “the selected `q = z^-1` translation commutes with evaluation”

It does so with a sign-sensitive non-real value rather than the self-inverse point `z = 1`.

## Gate record

After committing the Lean source, `./scripts/lint-style.sh` exited zero. It checked committed state;
all DCDR files are below 1500 lines, and neither changed file has a line over 100 codepoints.

With `Poles` and `PolesRegression` inserted temporarily in sorted order in `Physlib.lean`, this
single locked command exited zero at source head `dda88bc7`:

```text
lake-lock env bash -c 'lake exe cache get &&
  lake --wfail build Physlib.Optics.Systems.DCDR.Netlist
    Physlib.Optics.Systems.DCDR.Graph
    Physlib.Optics.Systems.DCDR.Bridge
    Physlib.Optics.Systems.DCDR.Topology
    Physlib.Optics.Systems.DCDR.TopologyRegression
    Physlib.Optics.Systems.DCDR.Response
    Physlib.Optics.Systems.DCDR.Mason
    Physlib.Optics.Systems.DCDR.ResponseRegression
    Physlib.Optics.Systems.DCDR.Poles
    Physlib.Optics.Systems.DCDR.PolesRegression &&
  lake exe runPhyslibLinters && lake exe lint_all'
```

The warnings-as-errors targeted build completed successfully with 2785 jobs.
`runPhyslibLinters` passed for Physlib and QuantumInfo. `lint_all` exited zero: its full build,
illegal-import, PhyslibAlpha-registration, duplicate-tag, sorry/pseudo-attribution, declaration,
and transitive-import checks completed. Its file-registration advisory named only unrelated
Microring and SpaceAndTime modules. Its style and transitive-import advisories named neither
`Poles.lean` nor `PolesRegression.lean` and no other changed file.

`Physlib.lean` was restored byte-identically after the gate. Its SHA-256 is
`d21d939c6ba90ce5f2391008df6208425e7110029c0b6929261be3a261ab0f37`, and its git blob hash is
`43c75f5a64a8375d68826ba11bef311b589f94f1`.

## Non-claims

- The printed incoherent Theorem 4 predicate is not identified with the coherent N7 response, and
  no implication to or from strict Schur stability is proved.
- The coherent `t`/`-I * k` model is the source's own unprinted coherent branch; the printed
  incoherent `1-k`/`k` expression is a different case.
- `formalZeros` is not a reciprocal-coordinate zero set. In particular, `q = 0` is not a finite
  Z-plane zero.
- No all-zeros-inside condition is called resonance, and no physical resonance theorem is stated.
- No physical-frequency, time-domain impulse-response, or causality interpretation is supplied.
- No power, coherence, group-delay, dispersion, or other observable is introduced in this slice.
- No DCDR BIBO theorem is claimed; S4's BIBO theorem is one-pole only, while both stable and active
  DCDR denominators here have nonzero quadratic coefficients.
- The active fixture is an exact algebraic Table 1 `G_i > 1` audit, not a material amplifier model,
  passivity theorem, or reconstruction of the source's passive decimal pole list.
- Actual-pole equality is not unconditional: candidate-to-actual promotion still requires the
  explicit pointwise `NoPoleCancellation` hypothesis.
