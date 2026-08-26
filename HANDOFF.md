# S7D slice 3 handoff: rational delay, reciprocal-Z poles, and stability fixtures

## Cutoff identity

- Branch: `optics/s7d-dcdr`.
- Required sync target: `cd8168880f1a420d0c720ea27b0e3aa8e91bdc44`.
- Sync merge: `d5eaee9a4e92711bc6ea1035a72aa37370164cc0`.
- Gated Lean source head: `fe299119fa5f9888eac4f3699dfcb411b762e143`.
- The final cutoff commit is a HANDOFF-only child of that source head.
- The exact W2 determinant docstring from dev commit `b126ebb6` is retained at
  `Physlib/Optics/Systems/DCDR/ResponseRegression.lean:1329-1330`:
  “The zero determinant has the numeric expansion `1 - (-1) - 2 = 0`, consistently with the
  two separately enumerated touching loops.” There is no lane diff to that dev wording.

## Files and registration request

New modules:

- `Physlib/Optics/Systems/DCDR/Poles.lean` — 727 lines.
- `Physlib/Optics/Systems/DCDR/PolesRegression.lean` — 503 lines.

Please add these two sorted imports to `Physlib.lean`, between the existing DCDR `Netlist` and
`Response` imports:

```lean
public import Physlib.Optics.Systems.DCDR.Poles
public import Physlib.Optics.Systems.DCDR.PolesRegression
```

The other eight DCDR modules are already registered. Every DCDR file remains below the 1500-line
cap; `ResponseRegression.lean` is 1397 lines.

## Goal text and delivered scope

This slice advances the exact S7D bullet “poles, zeros, and stability results”
(`goal.md:2424`) by tying the reduced numerator and denominator to a selected compiled network
response and by adding exact stable and unstable reduced-response fixtures. It also supplies the
unit-delay active specialization requested by “active/passive, unit-delay, and multiple-delay
specializations” (`goal.md:2422`); this cutoff does not claim the entire passive or multiple-delay
part of that bullet.

The validation row addressed is quoted verbatim:

> “DCDR pole/zero/stability theorems include the audited unstable parameter case”

This is row S-07 at `goal.md:2611`. The active fixture has all three gains strictly greater than
one, an exact response-indexed no-cancellation certificate, and the actual reduced pole `2 * I`
of norm two. Its reduced numerator also has the directly expanded zero `q = 0`. The pole therefore
fails the Schur premise directly, while the zero anchor exercises the active response numerator.

The proof-gated reciprocal substitution also exercises the row:

> “the selected `q = z⁻¹` translation commutes with evaluation”

This is row T-05 at `goal.md:2617`. Both concrete `z = 1` response anchors pass through S4's
`response_reciprocalZ_reindex_of_evaluation_eq` before their values are expanded from the retained
rational data.

This slice adds the reciprocal-Z leg needed later by X-01, but does not claim the full row
“one ring and one DCDR satisfy the full relational/compiled/chain/feedback/Mason/Z cross-semantics
equality on the common domain” (`goal.md:2622`).

## Reused APIs and pinned conventions

### N7 and the already certified DCDR netlist

- The coherent coupler parameters and the pinned cross coefficient `-I * k` are declared at
  `Physlib/Optics/Components/DirectionalCoupler.lean:62-70`; its reflectionless scattering law is
  at lines 124-135.
- Fixed-carrier propagation stores an amplitude factor and angle at
  `Physlib/Optics/Components/MatchedPropagation.lean:79-103`; its reflectionless scattering law is
  at lines 151-163. `pathAt` realizes the coefficient `gain * q` through this interface.
- The complete DCDR parameter record and its three path coefficients are at
  `Physlib/Optics/Systems/DCDR/Netlist.lean:59-81`. The five-component family is at lines 98-119,
  the complete wired flat netlist at line 179, and the selected external input/output channels at
  lines 327-334.
- The existing coherent scalar loop, denominator, drive, direct term, readout, numerator, and
  totalized transfer are at `Physlib/Optics/Systems/DCDR/Response.lean:70-113`.
- Existing well-posedness is exactly the nonzero scalar gate at
  `Physlib/Optics/Systems/DCDR/Response.lean:436-440`; the selected N5 entry and its derivation from
  raw N7 equations are at lines 446-449 and 515-539.
- The only generic matrix-inverse comparison used by the compiled response bridge is
  `FlatNetlist.feedbackInverse_eq_matrix_inv` at
  `Physlib/Optics/Network/FlatNetlistMason.lean:128-133`.

### S4 rational delay, reduction, and stability

- `RationalModel`, its retained domain, and totalized evaluation are at
  `Physlib/Optics/Systems/DelayTransfer/Basic.lean:104-140`. The reciprocal convention
  `zInverseEvaluation z = fun _ => z⁻¹` is at lines 233-239.
- `RationalNetlist`, pointwise compilation, and its inherited proof-gated response domain are at
  `Physlib/Optics/Systems/DelayTransfer/Evaluation.lean:152-260`.
- The reciprocal-Z response-domain preimage and proof-gated response transport are at
  `Physlib/Optics/Systems/DelayTransfer/Evaluation.lean:448-495`. The concrete network fixtures use
  `response_reciprocalZ_reindex_of_evaluation_eq` from lines 483-495.
- `ReducedRationalResponse` and `RationalReduction` are at
  `Physlib/Optics/Systems/DelayTransfer/Poles.lean:123-191`. The explicit pointwise
  `RationalReduction.NoPoleCancellation` gate and the gated raw-to-reduced root direction are at
  lines 194-236.
- Reciprocal-coordinate `zPoles` and the reduced `IsSchurStable` predicate are at
  `Physlib/Optics/Systems/DelayTransfer/Stability.lean:189-232`.
- S4's Schur/BIBO bridge is deliberately restricted to `ProperCausalOnePole`, declared at
  `Physlib/Optics/Systems/DelayTransfer/Stability.lean:306-405`. Both DCDR fixtures prove their
  quadratic denominators are not any one-pole denominator, so that bridge is not applied here.

### Source audit

FMICS'15 Table 1's active optical-amplifier configuration `G_i > 1` and Theorem 4's printed
incoherent stability audit are recorded at
`/Users/aadarwal/src/aadarwal/physlib-parity/HOL-CORPUS.md:307-308`.
The coherent N7 `t`/`-I * k` construction is the source's own unprinted coherent branch. The
printed incoherent `1-k`/`k` expression is a different case and is retained only as an audit
predicate unless reference [3] surfaces.

## Proof architecture and hostile anchors

- `candidateSingularities` is defined first by failure of bijectivity of the compiled internal
  feedback operator. The denominator-root characterization is proved afterward; it is not the
  definition.
- `ResponseReduction` certifies both the raw numerator and raw denominator of the selected DCDR
  response. It is not an unattached polynomial container.
- Actual reduced poles are always candidate internal singularities. The converse theorem requires
  S4's pointwise `NoPoleCancellation` hypothesis.
- The stable fixture expands the loop to `-(1/4) * q^2`, denominator to
  `1 + (1/4) * q^2`, and numerator to `-(19/64) * q - (61/64) * q^3`. Its reciprocal poles are
  proved directly to have norm `1/2`, hence lie inside the open unit disk.
- The active fixture uses gains `(17/4, 2, 2)`, all strictly greater than one. It expands the loop
  to `-4 * q^2`, denominator to `1 + 4 * q^2`, and numerator to
  `(1/4) * q - 17 * q^3`. Direct substitution proves `2 * I` is an actual reduced pole; its norm
  is two, so `IsSchurStable` fails. Separate direct numerator substitution proves `q = 0` is an
  actual reduced zero of the response-indexed active reduction.
- Both reductions cancel only the unit polynomial and prove `NoPoleCancellation` by unfolding that
  factor. The coprimality witnesses are explicit Bezout identities.
- At the regular network point `z = 1`, the stable proof-gated reciprocal-Z response is `-1` and
  the active response is `-67/20`. Each proof first uses S4's proof-gated reciprocal-Z response
  transport and then evaluates the hand-expanded numerator and denominator. Neither proof uses a
  pole, cancellation, Schur, or BIBO theorem as an oracle.
- The stable/unstable polynomial, pole, and norm fixtures unfold the rational data directly. They
  do not use `mem_candidateSingularities_iff`, either `ResponseReduction` pole-set theorem, or any
  Schur/BIBO implication.

## Public declaration inventory

All names below are in namespace `Optics.DCDR` unless a nested namespace is shown.

### `Poles.lean`: formal-delay data

- `UnitDelayParameters` (`:82`): two couplers and the three real delay gains.
- `UnitDelayParameters.IsAdmissible` (`:98`): nonnegative gains, intentionally without an upper
  bound.
- `pathAt` (`:102`): fixed-carrier realization of a formal path value.
- `transmissionCoefficient_pathAt` (`:108`): the realized coefficient is `gain * q`.
- `UnitDelayParameters.at` (`:117`): fixed-carrier specialization.
- `UnitDelayParameters.upperCoefficient_at` (`:126`).
- `UnitDelayParameters.lowerCoefficient_at` (`:132`).
- `UnitDelayParameters.feedbackCoefficient_at` (`:138`).
- `UnitDelayParameters.upperPolynomial` (`:143`).
- `UnitDelayParameters.lowerPolynomial` (`:147`).
- `UnitDelayParameters.feedbackPolynomial` (`:151`).
- `UnitDelayParameters.loopPolynomial` (`:155`).
- `UnitDelayParameters.denominatorPolynomial` (`:163`).
- `UnitDelayParameters.feedbackDrivePolynomial` (`:167`).
- `UnitDelayParameters.directPolynomial` (`:175`).
- `UnitDelayParameters.feedbackReadoutPolynomial` (`:182`).
- `UnitDelayParameters.responseNumeratorPolynomial` (`:190`).
- `UnitDelayParameters.eval_loopPolynomial` (`:196`).
- `UnitDelayParameters.eval_denominatorPolynomial` (`:204`).
- `UnitDelayParameters.eval_feedbackDrivePolynomial` (`:210`).
- `UnitDelayParameters.eval_directPolynomial` (`:218`).
- `UnitDelayParameters.eval_feedbackReadoutPolynomial` (`:225`).
- `UnitDelayParameters.eval_responseNumeratorPolynomial` (`:234`).
- `UnitDelayParameters.denominatorPolynomial_ne_zero` (`:242`).
- `responseModel` (`:251`): retained one-delay selected-response quotient.
- `responseModel_eval` (`:260`): quotient evaluation equals the scalar coherent transfer.

### `Poles.lean`: rational component family and compiled response

- `rationalPathEntryModel` (`:274`).
- `rationalPathEntryModel_eval` (`:284`).
- `evaluatedPathScattering` (`:296`).
- `evaluatedPathScattering_eq` (`:302`).
- `rationalComponents` (`:322`): five rational local component laws.
- `rationalNetlist` (`:341`): complete one-delay DCDR `RationalNetlist`.
- `rationalChannelFintype` (`:347`).
- `rationalConnectedChannelFintype` (`:352`).
- `rationalCompileChannelFintype` (`:357`).
- `rationalCompileConnectedChannelFintype` (`:364`).
- `rationalCompileChannelDecidableEq` (`:371`).
- `rationalCompileConnectedChannelDecidableEq` (`:376`).
- `rationalReciprocalZChannelFintype` (`:381`).
- `rationalReciprocalZConnectedChannelFintype` (`:386`).
- `rationalComponents_scattering_eq` (`:392`).
- `rationalNetlist_compile_eq` (`:416`): pointwise compilation equals the fixed-carrier DCDR
  netlist.
- `rationalNetlist_scatteringTransform_eq` (`:429`).
- `rationalNetlist_feedbackOperator_eq` (`:443`).
- `rationalNetlist_isWellPosed_iff` (`:451`): compiled well-posedness iff the polynomial
  denominator is nonzero.
- `rationalComponents_isValidAt` (`:469`).
- `rationalNetlist_mem_responseDomain` (`:489`).
- `rationalInputChannel` (`:498`).
- `rationalOutputChannel` (`:503`).
- `rationalNetlist_feedbackInverse_eq` (`:508`).
- `rationalNetlist_responseTransform_eq` (`:519`).
- `rationalEliminationResponse` (`:539`): selected proof-gated N5 response entry.
- `rationalEliminationResponse_eq_responseModel` (`:545`): compiled entry equals the retained
  quotient.
- `rationalZEliminationResponse` (`:571`): selected, reindexed proof-gated reciprocal-Z entry.
- `rationalZEliminationResponse_eq_responseModel` (`:579`): the Z entry is the retained quotient
  at `q = z⁻¹` via S4's response transport.

### `Poles.lean`: singularities and response-indexed reduction

- `candidateSingularities` (`:620`): failure of bijectivity of the compiled internal operator.
- `mem_candidateSingularities_iff_not_isWellPosed` (`:625`).
- `mem_candidateSingularities_iff` (`:636`): operator singularity iff denominator root.
- `candidatePoles` (`:643`): nonzero reciprocal values of internal singularities.
- `ResponseReduction` (`:647`): S4 reduction plus raw numerator and denominator certificates.
- `ResponseReduction.actualZeros` (`:660`): zeros of the certified reduced response.
- `ResponseReduction.actualPoles` (`:664`).
- `ResponseReduction.actualPoles_subset_candidatePoles` (`:668`): unconditional direction.
- `ResponseReduction.candidatePoles_subset_actualPoles` (`:676`): no-cancellation direction.
- `ResponseReduction.candidatePoles_eq_actualPoles` (`:688`): equality under no cancellation.
- `ResponseReduction.reduced_eval_eq_responseModel` (`:698`).
- `ResponseReduction.reduced_eval_eq_rationalEliminationResponse` (`:714`).

### `PolesRegression.lean`: audit predicate and exact fixtures

- `printedIncoherentStabilityExpression` (`:80`).
- `PrintedIncoherentStabilityConditions` (`:86`): the norm bound and the ledger-recorded nonzero
  hypothesis, with no coherent-response bridge.
- `poleRegressionCoupler` (`:98`): exact coherent `t = 3/5`, `k = 4/5` coupler.
- `stableUnitDelayParameters` (`:103`): gains `(61/64, 1, 1)`.
- `unstableAmplifierParameters` (`:111`): active gains `(17/4, 2, 2)`.
- `stableUnitDelayParameters_isAdmissible` (`:119`).
- `unstableAmplifierParameters_isAdmissible` (`:124`).
- `unstableAmplifierParameters_all_gains_gt_one` (`:129`).
- `stableNumerator` (`:142`).
- `stableDenominator` (`:146`).
- `unstableNumerator` (`:150`).
- `unstableDenominator` (`:154`).
- `stable_loopPolynomial_expansion` (`:158`).
- `stable_denominatorPolynomial_expansion` (`:172`).
- `stable_responseNumeratorPolynomial_expansion` (`:178`).
- `unstable_loopPolynomial_expansion` (`:198`).
- `unstable_denominatorPolynomial_expansion` (`:212`).
- `unstable_responseNumeratorPolynomial_expansion` (`:218`).
- `stableNumerator_ne_zero` (`:238`).
- `stableDenominator_ne_zero` (`:244`).
- `stableNumerator_isCoprime` (`:250`): explicit Bezout witness.
- `unstableNumerator_ne_zero` (`:259`).
- `unstableDenominator_ne_zero` (`:265`).
- `unstableNumerator_isCoprime` (`:271`): explicit Bezout witness.
- `stableReducedResponse` (`:280`).
- `unstableReducedResponse` (`:288`).
- `stableRationalReduction` (`:296`): cancellation factor `1`.
- `unstableRationalReduction` (`:310`): cancellation factor `1`.
- `stableResponseReduction` (`:324`): response-indexed stable certificate.
- `unstableResponseReduction` (`:330`): response-indexed active certificate.
- `stableResponseReduction_noPoleCancellation` (`:336`).
- `unstableResponseReduction_noPoleCancellation` (`:344`).

### `PolesRegression.lean`: proof-gated Z responses and stability teeth

- `stable_one_mem_responseDomain` (`:358`).
- `unstable_one_mem_responseDomain` (`:367`).
- `stable_one_mem_reciprocalZResponseDomain` (`:376`).
- `unstable_one_mem_reciprocalZResponseDomain` (`:392`).
- `stable_rationalZEliminationResponse_one` (`:408`): proof-gated value `-1`.
- `unstable_rationalZEliminationResponse_one` (`:419`): proof-gated value `-67/20`.
- `stableDenominator_ne_onePoleDenominator` (`:431`).
- `unstableDenominator_ne_onePoleDenominator` (`:441`).
- `stableReducedResponse_isSchurStable` (`:450`): direct root/norm proof.
- `unstableReducedResponse_two_mul_I_mem_zPoles` (`:466`): direct denominator substitution.
- `norm_two_mul_I` (`:477`): the hostile pole has norm two.
- `unstableReducedResponse_not_isSchurStable` (`:481`).
- `unstableResponseReduction_two_mul_I_mem_actualPoles` (`:490`).
- `unstableResponseReduction_zero_mem_actualZeros` (`:496`): direct numerator substitution.

## Validation binding map

The validation lane should bind at least these exact public names:

- Network model and fixed-carrier bridge:
  `Optics.DCDR.rationalNetlist`, `Optics.DCDR.rationalNetlist_compile_eq`.
- Proof-gated formal-delay response:
  `Optics.DCDR.rationalEliminationResponse_eq_responseModel`.
- Proof-gated reciprocal-Z response:
  `Optics.DCDR.rationalZEliminationResponse_eq_responseModel`,
  `Optics.DCDR.stable_rationalZEliminationResponse_one`, and
  `Optics.DCDR.unstable_rationalZEliminationResponse_one`.
- Candidate/actual schema:
  `Optics.DCDR.candidateSingularities`,
  `Optics.DCDR.mem_candidateSingularities_iff`,
  `Optics.DCDR.ResponseReduction.actualPoles_subset_candidatePoles`, and
  `Optics.DCDR.ResponseReduction.candidatePoles_eq_actualPoles`.
- No-cancellation fixtures:
  `Optics.DCDR.stableResponseReduction_noPoleCancellation` and
  `Optics.DCDR.unstableResponseReduction_noPoleCancellation`.
- S-07 positive and hostile anchors:
  `Optics.DCDR.stableReducedResponse_isSchurStable`,
  `Optics.DCDR.unstableAmplifierParameters_all_gains_gt_one`,
  `Optics.DCDR.unstableResponseReduction_zero_mem_actualZeros`,
  `Optics.DCDR.unstableResponseReduction_two_mul_I_mem_actualPoles`, and
  `Optics.DCDR.unstableReducedResponse_not_isSchurStable`.
- Printed-incoherent audit only:
  `Optics.DCDR.PrintedIncoherentStabilityConditions`.

## Gate record

After the exact sync merge, the build cache was refreshed with the required
`rsync -a --ignore-existing` command. After committing all Lean source, `./scripts/lint-style.sh`
exited zero. No DCDR file exceeds 1500 lines, and no DCDR line exceeds 100 codepoints.

With `Poles` and `PolesRegression` inserted temporarily in sorted order in `Physlib.lean`, this
single locked command exited zero at source head `fe299119`:

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

The cache was current. The warnings-as-errors build completed successfully with 2785 jobs.
`runPhyslibLinters` passed for Physlib and QuantumInfo. `lint_all` exited zero: its full build,
illegal-import, PhyslibAlpha-registration, duplicate-tag, sorry/pseudo-attribution, declaration,
and transitive-import checks passed. The file-registration advisory named only four unrelated
Microring Z-transform modules. The style advisory named no slice-3 module, and the transitive-
import advisory named no DCDR module. Existing style notices in `Bridge`, `Graph`, and `Netlist`
are the already reviewed split-file end spacing and are not findings in either new module.

`Physlib.lean` was restored byte-identically after the gate. Its SHA-256 is
`d21d939c6ba90ce5f2391008df6208425e7110029c0b6929261be3a261ab0f37`, and its git blob hash is
`43c75f5a64a8375d68826ba11bef311b589f94f1`. The post-gate worktree contained only this HANDOFF.

## Non-claims

- Formal `q` and reciprocal `z` are not assigned a physical-frequency interpretation.
- No all-zeros-inside condition is called a resonance; no physical resonance theorem is stated.
- No power, coherence, group-delay, dispersion, or other observable is introduced in this slice.
- No DCDR BIBO theorem is claimed. S4's BIBO equivalence is scoped to
  `ProperCausalOnePole`, while both exact DCDR denominators have a nonzero quadratic coefficient.
- The active fixture is an exact algebraic Table 1 `G_i > 1` audit, not a material amplifier model,
  passivity theorem, or reconstruction of the source's passive decimal pole list.
- The stable fixture is an algebraic positive anchor, not a passivity or physical-device theorem.
- Actual-pole equality is not unconditional: the candidate-to-actual direction always carries
  the explicit `NoPoleCancellation` hypothesis.
- The printed incoherent Theorem 4 conditions are not identified with the coherent N7 response.
  The coherent `t`/`-I * k` branch is the source's own unprinted coherent branch; comparison with
  the printed `1-k`/`k` case remains deferred unless reference [3] surfaces.
- The slice does not claim the full X-01 relational/compiled/chain/feedback/Mason/Z equality.
- No parity-ledger, API-map, `goal.md`, or `tbd.md` status is edited by this lane.
