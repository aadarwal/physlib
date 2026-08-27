# S7D slice 12 SS-2 handoff: L9 nonzero reciprocal-Z coordinates

## Cutoff identity

- Branch: `optics/s7d-dcdr`.
- Exact sync target: `b8ef32367b30e1880c396b838c7f1ae43d5eafde`.
- Exact sync merge: `28978c56e8e3c5df7bf30188096aab209401797d`.
- Gated source: `c72a60e8afd9765b6c77af94be807011b532773a`.
- This file is the HANDOFF-only cutoff child.
- `Physlib.lean` is byte-identical to the exact sync target. Its SHA-256 is
  `c54d6030b0fe32d41cd7088aec51224141d6f35cb5997bd4b0f4668f9a1cf0bf`.
- The fenced
  `Physlib/Mathematics/ZTransform/DifferenceEquationRegression.lean` is untouched.
  Its base and cutoff SHA-256 is
  `3d35e7134bd6336e4328dc8d6156f37b8e18789b732edcb434bec4ae198ee9df`.

The source cache was refreshed from the `optics-development` worktree after the exact sync
merge. The Lean source delta against that target is exactly the 18 existing files itemized
below. No file was added or removed, no module registration changed, and the S8 ZT-07
coordination-fence file was not touched.

Relative to the rejected source `28978c56e8e3c5df7bf30188096aab209401797d`, the SS-2 source
delta changes only module documentation in six existing files. No declaration, statement, proof,
import, or executable definition changed.

## Goal and decision resolution

At this cutoff ref, `goal.md:2753-2754` says verbatim:

> - [ ] Confirm the exact `z` versus `q = z⁻¹` convention, the sign in `exp (-s * τ)`, and every
>   startup term before S4/S5 identities are named.

This slice implements option 1 of
`scratchpad/lanes/decisions/decision-L9.md`, “L9 – Formal delay, Z coordinate, exponential sign,
and startup terms.” The generic semantic reciprocal-Z netlist is now indexed by a nonzero
coordinate subtype. The ambient carrier domains state the nonzero gate explicitly, the ring and
DCDR bridges construct that subtype only from existing ROC proofs, and the unilateral advance
startup contribution has a public name. This closes the implementation side of the quoted L9
gate; any checkbox update belongs to the conductor.

The decision's registry sentence is adopted verbatim:

> Formal delay is `q`; `Z{x}(z)=sum_{n>=0}x[n]z^{-n}`; on `ReciprocalZCoordinate`, `q=z⁻¹`.
> Formal `q=0` has no finite reciprocal preimage. It may be described as `z=∞` only inside a
> separately named projective/extended-complex interpretation, which the current `ℂ` API does
> not provide. `q_i(s)=exp(-s*tau_i)`, so `s=I*omega` gives
> `q_i=exp(-I*omega*tau_i)` and one-delay `z=exp(+I*omega*tau)`.

The implementation uses no projective or extended-complex API and therefore makes no `z = ∞`
claim. The existing Laplace substitution remains `q_i = exp (-s * τ_i)` at
`Physlib/Optics/Systems/DelayTransfer/Basic.lean:231`; the unilateral transform remains
`sum n, f n * (z⁻¹)^n` at `Physlib/Mathematics/ZTransform/Basic.lean:149-157`.

## SS-2 documentation repair

The nonzero-state boundary now ships in the module doc at
`Physlib/Mathematics/ZTransform/Basic.lean:24-26`: the finite advance startup sum is not an
initial-state model, this file proves no nonzero-state recurrence theorem, and any extension must
expose a separately named `initialStateContribution`. This is the correct home because
`advanceStartup` and `transform_advance` are declared in that module; the HANDOFF is no longer the
only place carrying the boundary.

The bounded citation sweep checked 35 pre-existing cited targets or prose ranges across all 18
touched files. Twenty-four were correct at the source ref and remain unchanged. Eleven stale
targets were fixed:

- `Basic.lean:225-227` became the `laplaceEvaluation` declaration at line 231.
- `Evaluation.lean:396-495` became the reciprocal map at line 401 and response transports at
  lines 510-550.
- nonexistent `EvaluationRegression.lean:845-912` became the citing module's direct solve at
  `FrequencyResponseRegression.lean:156`.
- the DCDR reciprocal-substitution citation `Evaluation.lean:396-399` became line 401.
- the reduced Schur citation `Stability.lean:185-232` became line 288.
- the one-pole BIBO citation `Stability.lean:374-403` became line 458.
- `HOL-CORPUS.md:307-308` became the FMICS'15 inventory at lines 316-326.
- the frequency-response goal citation moved from `goal.md:2279` to line 2334.
- the resonance-wording goal citation moved from `goal.md:2284-2289` to lines 2340-2344.
- the degree-bound goal citation moved from `goal.md:2274` to line 2329.
- the stated-class Schur/BIBO goal citation moved from `goal.md:2277-2278` to lines 2332-2333.

The declaration-line verification was run against the gated source with
`git show c72a60e8:<path> | sed -n '<line>p'`. The checked first lines are declarations:

- `DelayTransfer/Basic.lean:231`: `def laplaceEvaluation`.
- `DelayTransfer/Evaluation.lean:401`: `def reciprocalZ`.
- `DelayTransfer/Evaluation.lean:510`: `lemma response_reciprocalZ`.
- `DelayTransfer/FrequencyResponseRegression.lean:156`:
  `lemma allPassRationalNetlist_quadrature_compiled_entry_via_equations`.
- `DelayTransfer/Stability.lean:288`: `def IsSchurStable`.
- `DelayTransfer/Stability.lean:458`: `lemma isBIBOStable_iff_isSchurStable`.

The four repaired `goal.md` ranges and `HOL-CORPUS.md:316-326` were also printed and read in full.

## Exact source file set

### Z-transform startup API

- `Physlib/Mathematics/ZTransform/Basic.lean`: adds `advanceStartup` at line 322 and states
  `transform_advance` through that named finite sum at line 381; its module doc carries the
  nonzero-state boundary at lines 24-26.
- `Physlib/Mathematics/ZTransform/BasicRegression.lean`: independently pins startup `1`, the
  corrected value `2 * (1 - 1) = 0`, and the wrong-parentheses value
  `2 * 1 - 1 = 1` at lines 150, 154, and 161.
- `Physlib/Mathematics/ZTransform/Inverse.lean`: migrates
  `tendsto_inversion_cobounded` and `eq_natCast_of_transform_eqOn` at lines 193 and 217 to the
  named startup term.
- `Physlib/Mathematics/ZTransform/InverseRegression.lean`: migrates
  `tendsto_inversion_geometricSeq_one` at line 161.

### Generic reciprocal-Z API

- `Physlib/Optics/Systems/DelayTransfer/Basic.lean`: adds
  `ReciprocalZCoordinate`, `zInverseEvaluationOnReciprocalZ`, the raw-zero negative control,
  and semantic nonzero result at lines 247, 253, 264, and 269.
- `Physlib/Optics/Systems/DelayTransfer/Evaluation.lean`: changes
  `RationalNetlist.reciprocalZ` at line 401 to the subtype; adds the ambient solve and response
  carrier domains at lines 406 and 411; proves subtype/carrier equivalences and zero exclusion
  at lines 456-503; and migrates the three response transports at lines 510-539.
- `Physlib/Optics/Systems/DelayTransfer/EvaluationRegression.lean`: packages `z = I`, pins
  semantic `q = -I`, expands raw `z = 0`, rejects semantic `q = 0`, and migrates the compiled
  quadrature response at lines 377-456.
- `Physlib/Optics/Systems/DelayTransfer/FrequencyResponse.lean`: packages every unit-circle
  coordinate at line 114, proves its semantic evaluation at line 130, and migrates the domain
  and response equivalences at lines 260-287.
- `Physlib/Optics/Systems/DelayTransfer/FrequencyResponseRegression.lean`: migrates the exact
  quadrature frequency/reciprocal-Z anchor at line 217.
- `Physlib/Optics/Systems/DelayTransfer/Stability.lean`: retains `zZeros` and `zPoles` at lines
  156 and 201 while correcting their docs to say that formal `q = 0` has no finite coordinate
  and that this API supplies no projective interpretation.

### DCDR migration

- `Physlib/Optics/Systems/DCDR/Poles.lean`: changes
  `rationalZEliminationResponse` and its model equality to the subtype at lines 573 and 582;
  `formalZeros` at line 671 gets the explicit finite-coordinate legend.
- `Physlib/Optics/Systems/DCDR/PolesRegression.lean`: packages `z = 1` and `z = I` at lines
  450 and 454; migrates the stable and active exact response anchors at lines 458-608; and
  proves the formal-`q = 0` no-finite-coordinate sentinel at line 694.
- `Physlib/Optics/Systems/DCDR/ZTransformBridge.lean`: migrates the proof-gated rational domain
  and response bridge at lines 92 and 117; packages the semantic coordinate from ROC membership
  at line 264; and migrates common-domain membership and agreement at lines 285 and 345.
- `Physlib/Optics/Systems/DCDR/ZTransformRegression.lean`: migrates the exact real and nonreal
  response anchors at lines 343 and 548-584.
- `Physlib/Optics/Systems/DCDR/NominalChainRegression.lean`: mechanically migrates the existing
  independent chain/common-domain anchor at line 632.

### Microring and joint-witness migration

- `Physlib/Optics/Systems/Microring/AllPassZTransformBridge.lean`: migrates the rational domain,
  selected response, cleared law, and recurrence equality at lines 126-187; packages the
  semantic coordinate from ROC membership at line 348; and migrates common-domain membership
  and agreement at lines 358 and 421.
- `Physlib/Optics/Systems/Microring/AllPassZTransformBridgeRegression.lean`: migrates the exact
  common-domain and quarter-turn response anchors at lines 85 and 192-214.
- `Physlib/Optics/Systems/Microring/AllPassDCDRX01Regression.lean`: mechanically migrates the
  DCDR half of `ringDCDRX01Regression_independentAnchors` at line 96.

## Semantic domain audit

`RationalNetlist.reciprocalZ` has no all-complex compatibility alias. Its parameter type is
`ReciprocalZCoordinate`, and the two canonical ambient views are exactly

```text
{z : ℂ | z ≠ 0 ∧ zInverseEvaluation z ∈ netlist.solveDomain}
{z : ℂ | z ≠ 0 ∧ zInverseEvaluation z ∈ netlist.responseDomain}.
```

`mk_mem_reciprocalZ_solveDomain_iff` and
`mk_mem_reciprocalZ_responseDomain_iff` relate those views to the subtype netlist. The generic
zero-exclusion lemmas show that no rational netlist admits the complex origin in either carrier
domain. `zInverseEvaluation 0 = fun _ => 0` remains only as an explicitly nonsemantic negative
control, while `zInverseEvaluationOnReciprocalZ_ne_zero` proves that no semantic coordinate maps
to the zero delay tuple.

Both DCDR and ring common-domain structures continue to store ROC membership over the ambient
complex coordinate. Their new `reciprocalZCoordinate` projections derive nonzeroness from that
existing analytic proof. No result derives ROC, Schur, contraction, or a solve gate from the
subtype itself.

The exact quadrature anchor remains

```text
tau = 1, z = I, q = z⁻¹ = -I.
```

The DCDR active response still has formal `q = 0` as a formal zero, but the new sentinel proves
that no finite `ReciprocalZCoordinate` evaluates to it. This is not a statement about infinity.

## Startup-term audit

`advanceStartup f z m` is definitionally

```text
sum n in range m, seriesTerm f z n.
```

The public advance law is now

```text
transform (advance m f) z =
  z^m * (transform f z - advanceStartup f z m).
```

The fail-capable fixture expands the unit impulse at `m = 1`, `z = 2` from the primitive finite
sum. It proves startup `1` and corrected result `0`, while the false conference placement gives
`1`; therefore dropping the parentheses cannot pass the fixture. Inversion and uniqueness reuse
the same named startup term. No nonzero-state recurrence theorem is added: any future such result
must expose a separately named `initialStateContribution`.

## Validation names with declaration lines

### Mandatory production names

- `ReciprocalZCoordinate` —
  `Physlib/Optics/Systems/DelayTransfer/Basic.lean:247`.
- `zInverseEvaluationOnReciprocalZ` —
  `Physlib/Optics/Systems/DelayTransfer/Basic.lean:253`.
- `zInverseEvaluationOnReciprocalZ_apply` —
  `Physlib/Optics/Systems/DelayTransfer/Basic.lean:257`.
- `zInverseEvaluation_zero` —
  `Physlib/Optics/Systems/DelayTransfer/Basic.lean:264`.
- `zInverseEvaluationOnReciprocalZ_ne_zero` —
  `Physlib/Optics/Systems/DelayTransfer/Basic.lean:269`.
- `RationalNetlist.reciprocalZ` —
  `Physlib/Optics/Systems/DelayTransfer/Evaluation.lean:401`.
- `RationalNetlist.reciprocalZSolveDomain` —
  `Physlib/Optics/Systems/DelayTransfer/Evaluation.lean:406`.
- `RationalNetlist.reciprocalZResponseDomain` —
  `Physlib/Optics/Systems/DelayTransfer/Evaluation.lean:411`.
- `RationalNetlist.solveDomain_reciprocalZ` —
  `Physlib/Optics/Systems/DelayTransfer/Evaluation.lean:456`.
- `RationalNetlist.responseDomain_reciprocalZ` —
  `Physlib/Optics/Systems/DelayTransfer/Evaluation.lean:464`.
- `RationalNetlist.mk_mem_reciprocalZ_solveDomain_iff` —
  `Physlib/Optics/Systems/DelayTransfer/Evaluation.lean:472`.
- `RationalNetlist.mk_mem_reciprocalZ_responseDomain_iff` —
  `Physlib/Optics/Systems/DelayTransfer/Evaluation.lean:484`.
- `RationalNetlist.zero_not_mem_reciprocalZSolveDomain` —
  `Physlib/Optics/Systems/DelayTransfer/Evaluation.lean:496`.
- `RationalNetlist.zero_not_mem_reciprocalZResponseDomain` —
  `Physlib/Optics/Systems/DelayTransfer/Evaluation.lean:503`.
- `RationalNetlist.response_reciprocalZ` —
  `Physlib/Optics/Systems/DelayTransfer/Evaluation.lean:510`.
- `RationalNetlist.response_reciprocalZ_reindex` —
  `Physlib/Optics/Systems/DelayTransfer/Evaluation.lean:523`.
- `RationalNetlist.response_reciprocalZ_reindex_of_evaluation_eq` —
  `Physlib/Optics/Systems/DelayTransfer/Evaluation.lean:539`.
- `advanceStartup` — `Physlib/Mathematics/ZTransform/Basic.lean:322`.
- `transform_advance` — `Physlib/Mathematics/ZTransform/Basic.lean:381`.

### Generic exact anchors

- `advanceStartup_unitImpulse_two` —
  `Physlib/Mathematics/ZTransform/BasicRegression.lean:150`.
- `transform_advance_unitImpulse_two_correct` —
  `Physlib/Mathematics/ZTransform/BasicRegression.lean:154`.
- `transform_advance_unitImpulse_two_ne_wrong_parentheses` —
  `Physlib/Mathematics/ZTransform/BasicRegression.lean:161`.
- `quadratureReciprocalZCoordinate` —
  `Physlib/Optics/Systems/DelayTransfer/EvaluationRegression.lean:377`.
- `zInverseEvaluationOnReciprocalZ_quadrature` —
  `Physlib/Optics/Systems/DelayTransfer/EvaluationRegression.lean:381`.
- `zInverseEvaluation_zero_expansion` —
  `Physlib/Optics/Systems/DelayTransfer/EvaluationRegression.lean:389`.
- `zInverseEvaluationOnReciprocalZ_quadrature_ne_zero` —
  `Physlib/Optics/Systems/DelayTransfer/EvaluationRegression.lean:395`.
- `unitCircleReciprocalZCoordinate` —
  `Physlib/Optics/Systems/DelayTransfer/FrequencyResponse.lean:114`.
- `zInverseEvaluationOnReciprocalZ_unitCirclePoint` —
  `Physlib/Optics/Systems/DelayTransfer/FrequencyResponse.lean:130`.
- `RationalNetlist.unitCirclePoint_mem_reciprocalZ_responseDomain_iff` —
  `Physlib/Optics/Systems/DelayTransfer/FrequencyResponse.lean:260`.
- `RationalNetlist.frequencyResponse_eq_reciprocalZ` —
  `Physlib/Optics/Systems/DelayTransfer/FrequencyResponse.lean:287`.

### DCDR and ring adapters

- `DCDR.rationalZEliminationResponse` —
  `Physlib/Optics/Systems/DCDR/Poles.lean:573`.
- `DCDR.rationalZEliminationResponse_eq_responseModel` —
  `Physlib/Optics/Systems/DCDR/Poles.lean:582`.
- `DCDR.oneReciprocalZCoordinate` —
  `Physlib/Optics/Systems/DCDR/PolesRegression.lean:450`.
- `DCDR.imaginaryUnitReciprocalZCoordinate` —
  `Physlib/Optics/Systems/DCDR/PolesRegression.lean:454`.
- `DCDR.zInverseEvaluationOnReciprocalZ_I` —
  `Physlib/Optics/Systems/DCDR/PolesRegression.lean:534`.
- `DCDR.stable_I_mem_reciprocalZResponseDomain` —
  `Physlib/Optics/Systems/DCDR/PolesRegression.lean:552`.
- `DCDR.stable_rationalZEliminationResponse_I` —
  `Physlib/Optics/Systems/DCDR/PolesRegression.lean:584`.
- `DCDR.stable_rationalZEliminationResponse_I_ne_reversed` —
  `Physlib/Optics/Systems/DCDR/PolesRegression.lean:608`.
- `DCDR.unstableResponseReduction_zero_formal_only` —
  `Physlib/Optics/Systems/DCDR/PolesRegression.lean:694`.
- `DCDR.rationalNetlist_mem_reciprocalZ_responseDomain` —
  `Physlib/Optics/Systems/DCDR/ZTransformBridge.lean:92`.
- `DCDR.zTransfer_eq_rationalZEliminationResponse` —
  `Physlib/Optics/Systems/DCDR/ZTransformBridge.lean:117`.
- `DCDR.IsZCrossSemanticsDomain.reciprocalZCoordinate` —
  `Physlib/Optics/Systems/DCDR/ZTransformBridge.lean:264`.
- `DCDR.IsZCrossSemanticsDomain.mem_reciprocalZResponseDomain` —
  `Physlib/Optics/Systems/DCDR/ZTransformBridge.lean:285`.
- `DCDR.zCrossSemantics_agree` —
  `Physlib/Optics/Systems/DCDR/ZTransformBridge.lean:345`.
- `AllPass.allPassRationalNetlist_mem_reciprocalZ_responseDomain` —
  `Physlib/Optics/Systems/Microring/AllPassZTransformBridge.lean:126`.
- `AllPass.reciprocalZThroughResponse` —
  `Physlib/Optics/Systems/Microring/AllPassZTransformBridge.lean:138`.
- `AllPass.zTransfer_eq_reciprocalZThroughResponse` —
  `Physlib/Optics/Systems/Microring/AllPassZTransformBridge.lean:187`.
- `AllPass.IsZCrossSemanticsDomain.reciprocalZCoordinate` —
  `Physlib/Optics/Systems/Microring/AllPassZTransformBridge.lean:348`.
- `AllPass.IsZCrossSemanticsDomain.mem_reciprocalZResponseDomain` —
  `Physlib/Optics/Systems/Microring/AllPassZTransformBridge.lean:358`.
- `AllPass.zCrossSemantics_agree` —
  `Physlib/Optics/Systems/Microring/AllPassZTransformBridge.lean:421`.

### Migrated fail-capable regressions

- `DCDR.zRegression_stable_rawCompiled_I` —
  `Physlib/Optics/Systems/DCDR/ZTransformRegression.lean:548`.
- `DCDR.zRegression_stable_independent_nonzeroLoop_I` —
  `Physlib/Optics/Systems/DCDR/ZTransformRegression.lean:565`.
- `DCDR.zRegression_stable_I_commonDomain_independent_anchor` —
  `Physlib/Optics/Systems/DCDR/ZTransformRegression.lean:584`.
- `DCDR.zChainRegression_independent_common_point` —
  `Physlib/Optics/Systems/DCDR/NominalChainRegression.lean:632`.
- `AllPass.allPassZRegression_quarterTurn_reciprocalZDomain` —
  `Physlib/Optics/Systems/Microring/AllPassZTransformBridgeRegression.lean:192`.
- `AllPass.allPassZRegression_quarterTurn_reciprocalZThroughResponse` —
  `Physlib/Optics/Systems/Microring/AllPassZTransformBridgeRegression.lean:203`.
- `AllPass.allPassZRegression_quarterTurn_rawN5F_agreement` —
  `Physlib/Optics/Systems/Microring/AllPassZTransformBridgeRegression.lean:214`.
- `AllPass.ringDCDRX01Regression_independentAnchors` —
  `Physlib/Optics/Systems/Microring/AllPassDCDRX01Regression.lean:96`.

## Gate record

- Post-sync targeted build: green, 2,827 jobs.
- Root `lake-lock build Physlib -KwarningAsError=true`: green, 5,021 jobs.
- `lake-lock exe check_file_imports`: green.
- `lake-lock exe sorry_lint`: green.
- `lake-lock exe runPhyslibLinters`: green for Physlib and QuantumInfo.
- `lake-lock exe api_map_index`: green.
- `lake-lock exe lint_all`: exit 0; its advisory output contains only repository baseline
  findings. The cited double-empty-line finding in
  `DelayTransfer/EvaluationRegression.lean:148` is byte-identical to the sync target.
- `lake-lock exe module_doc_lint`: the full repository retains its known baseline failures;
  filtering error headers against all 18 touched files is empty.
- SS-2 targeted documentation build: green, 2,791 jobs.
- SS-2 module-doc error-header filter: empty for all six docs-only files.
- `./scripts/lint-style.sh`: green on committed state.
- `git diff --check`: green.
- Lean source delta: 18 existing files, 402 insertions, 164 deletions.
- Maximum touched-file length: 773 lines.
- Maximum touched-file line length: 100 Unicode codepoints.
- Added banned declarations/options: 0. Added `theorem` declarations: 0.

## Non-claims and human review

This slice does not identify a fixed-carrier phase with a time delay, does not add a nonzero-state
recurrence result, and does not claim physical frequency, causality beyond the unilateral
zero-state API, BIBO behavior, resonance, reciprocity, modal or electromagnetic power, or a
projective value at infinity. It changes no finite `zZeros` or `zPoles` set.

Per `decision-L9.md`, Human-only is **no** for the fork convention and nonzero-domain repair.
A human must certify source attribution if this material is upstreamed; that source-certification
step is separate from the implemented coordinate-domain gate.
