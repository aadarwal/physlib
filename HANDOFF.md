# S7D slice 7b handoff: admissibility-gated unit-delay bridge

## Cutoff identity

- Branch: `optics/s7d-dcdr`.
- Exact required sync target:
  `4386499b74e7b78d7ff3a897516d0433e080f374`.
- Exact sync merge commit:
  `4a3b03fa46af638049eea1c951a2b4c244b8fc72`.
- Gated Lean source head:
  `79bebe56b9fe17694b20502865ed65598306aeac`.
- The final cutoff is this HANDOFF-only child of the gated source head.
- No development head later than the named target was merged.

## Goal text and discharge

This slice addresses the literal S7D goal at `goal.md:2425-2433`, in
particular:

> "active/passive, unit-delay, and multiple-delay specializations;"

The earlier DCDR spine supplied active/passive fixtures and
`UnitDelayParameters`. Slice 7 supplied the missing formal `q^{m_i}` family
and exact multiple-delay fixtures. This 7b cutoff establishes precisely how
the old unit-delay rational family is connected to the new family: setting
`(m1,m2,m3)=(1,1,1)` gives the same polynomial data and pointwise compiled
N7 netlist, while response-domain membership and the selected N5 response
agree only under the old `UnitDelayParameters.IsAdmissible` gate. The
negative-gain regression shows why that gate cannot be dropped.

## Printed source text

FMICS'15 Equation 3 states
(`scratchpad/papers/FMICS15_1.txt:363-375`):

> “The general expression for the photonic transmittance is given as
> follows: `T_i = t_{a_i} G_i z^{m_i}`.”

FMICS'15 Table 1 prints these four rows
(`scratchpad/papers/FMICS15_1.txt:594-600`):

> “Active DCDR Circuit with Unit Delay” — `m1 = m2 = m3 = 1`
>
> “Optical Amplifier in the Fiber Path” —
> `(m1 = m2 = m3 = 1) ∧ (G_i > 1)`
>
> “Passive DCDR Circuit” — `G1 = G2 = G3 = 1`
>
> “DCDR with Multiple Delay” — `m_i` can have different combinations

Theorem 3 prints
(`scratchpad/papers/FMICS15_1.txt:572-578`) the quotient

```text
((1-k1)(1-k2)T1 + k1 k2 T2
  - (1-2k1)(1-2k2)T1 T2 T3)
/
(1 - k1 k2 T1 T3 - (1-k1)(1-k2)T2 T3).
```

The source uses a positive exponent of its symbol `z`. The source
dictionary selects `t_{a_i}=1`, names Physlib's retained polynomial
indeterminate `q`, and then applies the independently declared reciprocal
reparameterization `q=z⁻¹` at
`Physlib/Optics/Systems/DelayTransfer/Evaluation.lean:397-455`.
Consequently its retained path is stated explicitly as
`G_i*q^m_i = G_i/z^m_i`; no silent coordinate identification or
physical-frequency interpretation is made.

## Files, split, and registration request

The controller requested an early split when the coherent-only WIP reached
1208 lines. The final dependency order is:

1. `MultipleDelay.lean` — 879 lines; parameters, polynomial data,
   rational component family, selected N5 response, and the
   admissibility-gated unit-delay rational bridge.
2. `MultipleDelayPolynomial.lean` — 318 lines; expansions, degree bounds,
   cancellation-aware reduction, and generalized pole bound.
3. `MultipleDelaySource.lean` — 300 lines; the eight-symbol FMICS'15
   source dictionary and printed Theorem-3 polynomials.
4. `MultipleDelayRegression.lean` — 626 lines; four Table-1 fixtures, the
   tight degree-four pole fixture, a nontrivial shared-response anchor, and
   the negative-gain validity sentinel.

Requested sorted registrations:

```lean
public import Physlib.Optics.Systems.DCDR.MultipleDelay
public import Physlib.Optics.Systems.DCDR.MultipleDelayPolynomial
public import Physlib.Optics.Systems.DCDR.MultipleDelayRegression
public import Physlib.Optics.Systems.DCDR.MultipleDelaySource
```

Production modules do not import `MultipleDelayRegression`.
`Physlib.lean` has no committed change. The gate temporarily inserted the
four registrations and then restored the file byte-for-byte to SHA-256
`01969994b8598317a61650e9a88f5c32b21c369b9958c5c18c7a4822d0f1d56b`.

## Reused conventions and dependency evidence

- The unit-delay data and fixed-carrier path realization are
  `UnitDelayParameters` and `pathAt` at
  `Physlib/Optics/Systems/DCDR/Poles.lean:82-110`.
- The existing unit-delay polynomials are at
  `Physlib/Optics/Systems/DCDR/Poles.lean:143-194`.
- The retained five component labels and six proof-carrying connections are
  at `Physlib/Optics/Systems/DCDR/Netlist.lean:87-175`.
- The coherent cross-arm gauge is
  `crossCoefficient = -I*crossAmplitude` at
  `Physlib/Optics/Components/DirectionalCoupler.lean:63-79`.
- S4's `RationalNetlist` carrier is declared at
  `Physlib/Optics/Systems/DelayTransfer/Evaluation.lean:151-170`.
- S4's explicit common-factor `RationalReduction` certificate is at
  `Physlib/Optics/Systems/DelayTransfer/Poles.lean:168-183`.
- The finite reciprocal-`z` set and its cardinality bound are at
  `Physlib/Optics/Systems/DelayTransfer/Stability.lean:225-243`.
- The earlier DCDR reduction pattern is `ResponseReduction` at
  `Physlib/Optics/Systems/DCDR/Poles.lean:643-705`.
- The slice-5 real printed dictionary and coherent map are at
  `Physlib/Optics/Systems/DCDR/SourceBridge.lean:197-248`.
- The unit-delay at-most-two result is at
  `Physlib/Optics/Systems/DCDR/SourceBridge.lean:133-162`.
- S4P restricts its Schur/BIBO result to the named proper causal one-pole
  class at
  `Physlib/Optics/Systems/DelayTransfer/Stability.lean:424-457`.

## Coherent multiple-delay family

`MultipleDelayParameters` stores two coherent couplers, complex
`G1/G2/G3`, and natural `m1/m2/m3`. Its path laws are exactly
`G_i*q^m_i`. `IsAdmissible` requires positive retained delays but places
no passivity or reality restriction on the complex gains; the polynomial and
fixed-carrier laws remain total outside that proof-gated response domain.

`multipleDelayRationalNetlist` reuses the existing five component labels and
six wires. Pointwise compilation is proved equal to the fixed-carrier N7
netlist, its internal operator has the hand-expanded scalar denominator, and
the selected N5 elimination response equals
`responseNumeratorPolynomial / denominatorPolynomial` on the common
response domain.

`UnitDelayParameters.toMultipleDelayParameters` stores
`(m1,m2,m3)=(1,1,1)` literally. Separate lemmas prove equality of all three
path polynomials, the coherent denominator, and the selected coherent
numerator with the earlier unit-delay family.

## Unit-delay rational bridge and validity gate

The unit-exponent embedding has pointwise scattering equality component by
component and therefore compiles to the same coherent N7 flat netlist as the
old rational family at every formal `q`. This algebraic compilation equality
does not identify stored model validity.

Under `hp : p.IsAdmissible`, denominator equality and the two families'
well-posedness characterizations give an iff between response-domain
membership. On that common domain, both independently certified N5 entries
evaluate the same numerator and denominator, so the selected responses are
equal. This is the exact sense in which the embedding is a rational-family
specialization.

The gate is load-bearing. At `upperGain=-1`, `lowerGain=1`, and
`feedbackGain=0`, the old response domain is empty because the old component
validity predicate rejects the negative real gain. The embedded family has
positive exponents and denominator one, so formal `q=0` lies in its response
domain. Thus no unconditional response-domain equivalence is claimed.

## Polynomial, reduction, and pole layer

The coherent expansions give the source's degree shape without identifying
its coefficients with the printed incoherent coefficients:

```text
degree denominator <= max (m1 + m3) (m2 + m3)
degree numerator   <= max (max m1 m2) (m1 + m2 + m3)
```

`MultipleDelayResponseReduction` reuses
`DelayTransfer.RationalReduction` by name. Its proof chain is:

```text
ncard actual reciprocal-z poles
  <= degree reduced denominator
  <= degree raw coherent denominator
  <= max (m1 + m3) (m2 + m3).
```

“Actual” here always means the reduced reciprocal-`z` pole set under
`q=z⁻¹`. The raw denominator is formal-`q` data, and cancellation may
lower the reduced degree. The evaluation lemmas retain both the
no-cancellation-factor gate and the reduced-denominator domain.

## Source dictionary and coherent/printed separation

`DCDRSourceBridge.MultipleDelaySourceParameters` extends the slice-5 real
source dictionary with `m1/m2/m3`. It maps the printed symbols to the
coherent family as follows:

| Printed symbol | Coherent Lean field |
|---|---|
| `k1` | first through `sqrt(1-k1)`, first cross `sqrt(k1)` |
| `k2` | second through `sqrt(1-k2)`, second cross `sqrt(k2)` |
| `G1,G2,G3` | complex casts of the three real source gains |
| `m1,m2,m3` | the three natural delay exponents unchanged |

The core `MultipleDelayParameters` permits complex gains; the source bridge
deliberately remains the real subfamily inherited from the slice-5 dictionary.
The printed Theorem-3 polynomials retain `1-k` and `k` intensities,
whereas the coherent family uses square-root amplitudes and the pinned
`-I` gauge. The dictionary proves symbol/coefficient and unit-delay
specialization identities only. It proves no coherent–incoherent response,
pole, or stability equality.

## Exact Table-1 and tight-pole fixtures

Each Table-1 row has a concrete source value and a hand-expanded printed
numerator/denominator:

| Row | Exact selected data | Direct polynomial anchor |
|---|---|---|
| active unit delay | `G=(2,1,1), k=(0,0), m=(1,1,1)` | `N=2q-2q³, D=1-q²` |
| optical amplifier | `G=(2,3,4), k=(1,1), m=(1,1,1)` | `N=3q-24q³, D=1-8q²` |
| passive | `G=(1,1,1), k=(0,0), m=(1,1,1)` | `N=q-q³, D=1-q²` |
| multiple delay | `G=(1,1,1), k=(0,0), m=(2,1,3)` | `N=q²-q⁶, D=1-q⁴` |

The anchors unfold the dictionary and primitive polynomial operations. A
wrong gain, coupling, or delay exponent changes an exponent or coefficient and
breaks the corresponding regression.

The separate tight coherent fixture has `m=(2,1,3)`, raw response
`-q/(1-q⁴)`, and an explicit Bézout identity proving no cancellation.
Primitive fourth-degree factorization gives the reciprocal-`z` pole set
`{1,-1,I,-I}`, hence exactly four poles. The raw denominator degree is
also exactly four, so the generalized cardinality bound is attained and the
slice-5 bound of two is visibly unit-delay-specific. The coupler
`through=cross=1` is intentionally an algebraic tightness fixture, not a
normalized physical-coupler claim.

## Proof independence and failure sensitivity

- Table fixtures expand the source structures and polynomial primitives; they
  do not invoke the production coefficient or degree lemmas.
- The tight coherent denominator and numerator unfold the core construction
  rather than the polynomial expansion lemmas.
- Coprimality is an explicit Bézout identity.
- The four reciprocal poles are enumerated by direct complex factorization and
  evaluation, not by the generalized pole-cardinality lemma.
- The final `ncard=4=natDegree` anchor combines the independently expanded
  degree and pole set.
- At gains `(2,3/2,1/2)` and formal `q=1/2`, the old and embedded numerator
  and denominator values are expanded independently to `13/16`; each selected
  response is therefore pinned to `1` without using the bridge lemma.
- The negative-gain sentinel extracts the old stored validity predicate
  directly from response-domain membership and separately constructs an
  embedded domain point from the primitive denominator expansion.

Changing a Table exponent, a Theorem-3 source index, the coherent cross gauge,
the reciprocal-coordinate convention, or the tight fixture's path data breaks
one or more anchors.

## Public declarations

All declarations are lemmas/definitions/structures/instances; this cutoff
introduces no `theorem` declaration.

### `Optics.DCDR` in `MultipleDelay.lean`

- Data and scalar layer:
  `MultipleDelayParameters`,
  `MultipleDelayParameters.IsAdmissible`,
  `multipleDelayPathAt`,
  `transmissionCoefficient_multipleDelayPathAt`,
  `MultipleDelayParameters.at`,
  `MultipleDelayParameters.upperCoefficient_at`,
  `MultipleDelayParameters.lowerCoefficient_at`,
  `MultipleDelayParameters.feedbackCoefficient_at`.
- Polynomial data:
  `MultipleDelayParameters.upperPolynomial`,
  `MultipleDelayParameters.lowerPolynomial`,
  `MultipleDelayParameters.feedbackPolynomial`,
  `MultipleDelayParameters.loopPolynomial`,
  `MultipleDelayParameters.denominatorPolynomial`,
  `MultipleDelayParameters.feedbackDrivePolynomial`,
  `MultipleDelayParameters.directPolynomial`,
  `MultipleDelayParameters.feedbackReadoutPolynomial`,
  `MultipleDelayParameters.responseNumeratorPolynomial`,
  `MultipleDelayParameters.eval_upperPolynomial`,
  `MultipleDelayParameters.eval_lowerPolynomial`,
  `MultipleDelayParameters.eval_feedbackPolynomial`,
  `MultipleDelayParameters.eval_loopPolynomial`,
  `MultipleDelayParameters.eval_denominatorPolynomial`,
  `MultipleDelayParameters.eval_feedbackDrivePolynomial`,
  `MultipleDelayParameters.eval_directPolynomial`,
  `MultipleDelayParameters.eval_feedbackReadoutPolynomial`,
  `MultipleDelayParameters.eval_responseNumeratorPolynomial`,
  `MultipleDelayParameters.denominatorPolynomial_eval_zero`,
  `MultipleDelayParameters.denominatorPolynomial_ne_zero`,
  `MultipleDelayParameters.responseModel`,
  `MultipleDelayParameters.responseModel_eval`.
- Unit-delay specialization:
  `UnitDelayParameters.toMultipleDelayParameters`,
  `UnitDelayParameters.toMultipleDelayParameters_data`,
  `UnitDelayParameters.toMultipleDelayParameters_isAdmissible`,
  `UnitDelayParameters.toMultipleDelayParameters_upperPolynomial`,
  `UnitDelayParameters.toMultipleDelayParameters_lowerPolynomial`,
  `UnitDelayParameters.toMultipleDelayParameters_feedbackPolynomial`,
  `UnitDelayParameters.toMultipleDelayParameters_denominatorPolynomial`,
  `UnitDelayParameters.toMultipleDelayParameters_responseNumeratorPolynomial`.
- Rational N7/N5 layer:
  `multipleDelayRationalPathEntryModel`,
  `multipleDelayRationalPathEntryModel_eval`,
  `multipleDelayEvaluatedPathScattering`,
  `multipleDelayEvaluatedPathScattering_eq`,
  `multipleDelayRationalComponents`,
  `multipleDelayRationalNetlist`,
  `multipleDelayRationalChannelFintype`,
  `multipleDelayRationalConnectedChannelFintype`,
  `multipleDelayRationalCompileChannelFintype`,
  `multipleDelayRationalCompileConnectedChannelFintype`,
  `multipleDelayRationalCompileChannelDecidableEq`,
  `multipleDelayRationalCompileConnectedChannelDecidableEq`,
  `multipleDelayRationalComponents_scattering_eq`,
  `multipleDelayRationalNetlist_compile_eq`,
  `multipleDelayRationalNetlist_scatteringTransform_eq`,
  `multipleDelayRationalNetlist_feedbackOperator_eq`,
  `multipleDelayRationalNetlist_isWellPosed_iff`,
  `multipleDelayRationalComponents_isValidAt`,
  `multipleDelayRationalNetlist_mem_responseDomain`,
  `multipleDelayRationalInputChannel`,
  `multipleDelayRationalOutputChannel`,
  `multipleDelayRationalNetlist_feedbackInverse_eq`,
  `multipleDelayRationalNetlist_responseTransform_eq`,
  `multipleDelayRationalEliminationResponse`,
  `multipleDelayRationalEliminationResponse_eq_responseModel`.
- Admissibility-gated unit-delay rational bridge:
  `multipleDelayEvaluatedPathScattering_one_eq_evaluatedPathScattering`,
  `UnitDelayParameters.toMultipleDelayParameters_rationalComponents_scattering_eq`,
  `UnitDelayParameters.toMultipleDelayParameters_rationalNetlist_compile_eq`,
  `UnitDelayParameters.toMultipleDelayParameters_responseModel_eval_eq`,
  `UnitDelayParameters.mem_rationalNetlist_responseDomain_iff_toMultipleDelayParameters`,
  `UnitDelayParameters.rationalEliminationResponse_eq_toMultipleDelayParameters`.

### `Optics.DCDR` in `MultipleDelayPolynomial.lean`

- `MultipleDelayParameters.lowerLoopCoefficient`,
  `MultipleDelayParameters.upperLoopCoefficient`,
  `MultipleDelayParameters.loopPolynomial_expansion`,
  `MultipleDelayParameters.directUpperCoefficient`,
  `MultipleDelayParameters.directLowerCoefficient`,
  `MultipleDelayParameters.cubicCouplerCoefficient`,
  `MultipleDelayParameters.responseNumeratorPolynomial_expansion`,
  `MultipleDelayParameters.upperPolynomial_natDegree_le`,
  `MultipleDelayParameters.lowerPolynomial_natDegree_le`,
  `MultipleDelayParameters.feedbackPolynomial_natDegree_le`,
  `MultipleDelayParameters.denominatorPolynomial_natDegree_le`,
  `MultipleDelayParameters.responseNumeratorPolynomial_natDegree_le`.
- `MultipleDelayResponseReduction`,
  `MultipleDelayResponseReduction.actualPoles`,
  `MultipleDelayResponseReduction.finite_actualPoles`,
  `MultipleDelayResponseReduction.ncard_actualPoles_le_reducedDenominatorDegree`,
  `MultipleDelayResponseReduction.reducedDenominator_natDegree_le_rawDenominatorDegree`,
  `MultipleDelayResponseReduction.ncard_actualPoles_le_rawDenominatorDegree`,
  `MultipleDelayResponseReduction.ncard_actualPoles_le_delayShape`,
  `MultipleDelayResponseReduction.reduced_eval_eq_responseModel`,
  `MultipleDelayResponseReduction.reduced_eval_eq_rationalEliminationResponse`.

### `Optics.DCDRSourceBridge` in `MultipleDelaySource.lean`

- `MultipleDelaySourceParameters`,
  `MultipleDelaySourceParameters.toSourceParameters`,
  `SourceParameters.toMultipleDelaySourceParameters`,
  `MultipleDelaySourceParameters.toMultipleDelayParameters`,
  `MultipleDelaySourceParameters.toMultipleDelayParameters_data`,
  `SourceParameters.toMultipleDelaySourceParameters_coherent`.
- `MultipleDelaySourceParameters.printedUpperCoefficient`,
  `MultipleDelaySourceParameters.printedLowerCoefficient`,
  `MultipleDelaySourceParameters.printedCubicCoefficient`,
  `MultipleDelaySourceParameters.printedUpperLoopCoefficient`,
  `MultipleDelaySourceParameters.printedLowerLoopCoefficient`,
  `MultipleDelaySourceParameters.printedNumeratorPolynomial`,
  `MultipleDelaySourceParameters.printedDenominatorPolynomial`,
  `MultipleDelaySourceParameters.printedNumeratorPolynomial_natDegree_le`,
  `MultipleDelaySourceParameters.printedDenominatorPolynomial_natDegree_le`,
  `MultipleDelaySourceParameters.finite_zPoles_and_ncard_le_delayShape`,
  `SourceParameters.toMultipleDelaySourceParameters_printedNumeratorPolynomial`,
  `SourceParameters.toMultipleDelaySourceParameters_printedDenominatorPolynomial`.

### Regression declarations

In `Optics.DCDRSourceBridge`:

- `tableActiveUnitDelayParameters`,
  `tableActiveUnitDelayParameters_data`,
  `tableActiveUnitDelay_printedPolynomials`,
  `tableOpticalAmplifierParameters`,
  `tableOpticalAmplifierParameters_data`,
  `tableOpticalAmplifier_printedPolynomials`,
  `tablePassiveParameters`,
  `tablePassiveParameters_data`,
  `tablePassive_printedPolynomials`,
  `tableMultipleDelayParameters`,
  `tableMultipleDelayParameters_data`,
  `tableMultipleDelay_printedPolynomials`.

In `Optics.DCDR`:

- `tightMultipleDelayCoupler`,
  `tightMultipleDelayParameters`,
  `tightMultipleDelayParameters_data`,
  `tightMultipleDelay_denominatorPolynomial_expansion`,
  `tightMultipleDelay_responseNumeratorPolynomial_expansion`,
  `tightMultipleDelay_denominatorPolynomial_natDegree_eq_four`,
  `tightMultipleDelayNumerator_ne_zero`,
  `tightMultipleDelayDenominator_ne_zero`,
  `tightMultipleDelayNumerator_isCoprime`,
  `tightMultipleDelayReducedResponse`,
  `tightMultipleDelayRationalReduction`,
  `tightMultipleDelayResponseReduction`,
  `tightMultipleDelay_zPoles_eq_four`,
  `tightMultipleDelay_ncard_actualPoles_eq_four`,
  `tightMultipleDelay_ncard_actualPoles_eq_natDegree`,
  `unitDelayBridgeCoupler`,
  `unitDelayBridgeParameters`,
  `unitDelayBridgeQ`,
  `unitDelayBridgeParameters_isAdmissible`,
  `unitDelayBridge_old_polynomial_evaluations`,
  `unitDelayBridge_embedded_polynomial_evaluations`,
  `unitDelayBridgeOldDomainProof`,
  `unitDelayBridgeEmbeddedDomainProof`,
  `unitDelayBridge_old_response_eq_one`,
  `unitDelayBridge_embedded_response_eq_one`,
  `unitDelayBridge_both_responses_eq_one`,
  `unitDelayValidityCounterexample`,
  `unitDelayValidityCounterexample_predicates`,
  `unitDelayValidityCounterexample_old_responseDomain_eq_empty`,
  `unitDelayValidityCounterexample_embedded_denominator_at_zero`,
  `unitDelayValidityCounterexample_embedded_responseDomain_nonempty`,
  `unitDelayValidityGate_is_loadBearing`.

## Validation map

Validation should bind at least:

- `Optics.DCDR.UnitDelayParameters.toMultipleDelayParameters_data`
  (`MultipleDelay.lean:353`).
- `Optics.DCDR.UnitDelayParameters.toMultipleDelayParameters_denominatorPolynomial`
  (`MultipleDelay.lean:394`).
- `Optics.DCDR.UnitDelayParameters.toMultipleDelayParameters_responseNumeratorPolynomial`
  (`MultipleDelay.lean:411`).
- `Optics.DCDR.multipleDelayRationalNetlist_compile_eq`
  (`MultipleDelay.lean:584`).
- `Optics.DCDR.multipleDelayRationalEliminationResponse_eq_responseModel`
  (`MultipleDelay.lean:732`).
- `Optics.DCDR.UnitDelayParameters.toMultipleDelayParameters_rationalNetlist_compile_eq`
  (`MultipleDelay.lean:808`).
- `Optics.DCDR.UnitDelayParameters.mem_rationalNetlist_responseDomain_iff_toMultipleDelayParameters`
  (`MultipleDelay.lean:845`).
- `Optics.DCDR.UnitDelayParameters.rationalEliminationResponse_eq_toMultipleDelayParameters`
  (`MultipleDelay.lean:865`).
- `Optics.DCDR.MultipleDelayParameters.denominatorPolynomial_natDegree_le`
  (`MultipleDelayPolynomial.lean:142`).
- `Optics.DCDR.MultipleDelayParameters.responseNumeratorPolynomial_natDegree_le`
  (`MultipleDelayPolynomial.lean:181`).
- `Optics.DCDR.MultipleDelayResponseReduction.ncard_actualPoles_le_delayShape`
  (`MultipleDelayPolynomial.lean:278`).
- `Optics.DCDRSourceBridge.MultipleDelaySourceParameters.toMultipleDelayParameters_data`
  (`MultipleDelaySource.lean:148`).
- `Optics.DCDRSourceBridge.SourceParameters.toMultipleDelaySourceParameters_coherent`
  (`MultipleDelaySource.lean:165`).
- `Optics.DCDRSourceBridge.MultipleDelaySourceParameters.printedDenominatorPolynomial_natDegree_le`
  (`MultipleDelaySource.lean:230`).
- All four `table*_*printedPolynomials` anchors
  (`MultipleDelayRegression.lean:116,152,185,220`).
- `Optics.DCDR.tightMultipleDelay_denominatorPolynomial_natDegree_eq_four`
  (`MultipleDelayRegression.lean:298`).
- `Optics.DCDR.tightMultipleDelay_zPoles_eq_four`
  (`MultipleDelayRegression.lean:360`).
- `Optics.DCDR.tightMultipleDelay_ncard_actualPoles_eq_natDegree`
  (`MultipleDelayRegression.lean:436`).
- `Optics.DCDR.unitDelayBridge_both_responses_eq_one`
  (`MultipleDelayRegression.lean:553`).
- `Optics.DCDR.unitDelayValidityGate_is_loadBearing`
  (`MultipleDelayRegression.lean:615`).

## Non-claims

This cutoff makes no physical-resonance claim, no coherent–incoherent
equivalence claim, no BIBO claim beyond S4P's existing stated-class gate, no
normalized-modal or electromagnetic-power claim, no causality or time-domain
claim, no physical-frequency claim, and no claim about the unavailable HOL
script. The degree-four tight fixture is algebraic and is not asserted to be a
normalized passive physical coupler.

## Gate record

At committed source head `79bebe56`:

- `lake-lock exe cache get`: green; no files to download.
- Targeted `lake-lock build` of `MultipleDelay` and
  `MultipleDelayRegression`: green, 2786 jobs, with no warning.
- Temporary-registration `lake-lock --wfail build Physlib`: green, 4975 jobs,
  including all four modules in the requested repository-sorted order.
- `lake-lock exe sorry_lint`: green.
- `lake-lock exe runPhyslibLinters Physlib`: green for both Physlib and
  QuantumInfo declarations.
- `lake-lock exe api_map_index`: completed successfully; 34 maps and 649
  requirements indexed.
- `lake-lock exe lint_all`: this slice's build, declaration lints, sorry audit,
  and illegal-import check are green. The command prints the pinned
  repository's pre-existing aggregate style/transitive-import backlog. Its
  import check, with this slice temporarily registered, names only the
  unrelated pending `FluxDirection`, `FluxDirectionRegression`, and
  `PassiveCaseRegression` registrations.
- `./scripts/lint-style.sh`: green globally on committed state. Direct shipped
  style checks are also green on every DCDR module. Maximum line length among
  the four slice-7 files is 98 codepoints; every DCDR file is below 1500 lines.
- `lake-lock exe module_doc_lint`: the repository command remains nonzero on
  its broad pre-existing documentation backlog. With all four modules
  temporarily registered, filtered output names none of them; their literal
  headings and exact TOCs match the shipped algorithm.
- Static house audit: zero `sorry`, `axiom`, `native_decide`,
  `maxHeartbeats`, or `theorem`; production imports no regression module.
  `Physlib.lean` was restored byte-for-byte to SHA-256
  `01969994b8598317a61650e9a88f5c32b21c369b9958c5c18c7a4822d0f1d56b`.
