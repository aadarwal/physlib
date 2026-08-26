# S7C slice 3 handoff

## Cutoff

- Branch: `optics/s7c-cascade`
- Required sync target: `6028d2a6858e5c2af4866c944ec13d1c3a255799`
- Target merge: `ee7f2505b5db997049bfb1eab97b4d79a0297a09`
- V2-ready slice-2 cutoff: `32f0a2fce921667ccbbc6d79b844de3276c25efa`
- Exact source-gated head: `9538674a748149da56333898a7a45a2257ed6ff3`
- Final cutoff: this HANDOFF-only commit

The required target is an ancestor of the cutoff. The merge retained the approved lane commits
and accepted the target's code and registry state unchanged.

## Files and registrations

Slice 3 adds:

- `Physlib.Optics.Systems.Cascade.Termination`
- `Physlib.Optics.Systems.Cascade.TerminationRegression`

The target registers the four slice-1 modules. The exact gate temporarily registered the four
unregistered slice-2 and slice-3 modules, yielding this cumulative S7C battery:

- `Physlib.Optics.Network.TwoPortChainFold`
- `Physlib.Optics.Network.TwoPortChainFoldRegression`
- `Physlib.Optics.Systems.Cascade.Heterogeneous`
- `Physlib.Optics.Systems.Cascade.HeterogeneousRegression`
- `Physlib.Optics.Systems.Cascade.Identical`
- `Physlib.Optics.Systems.Cascade.IdenticalRegression`
- `Physlib.Optics.Systems.Cascade.Termination`
- `Physlib.Optics.Systems.Cascade.TerminationRegression`

No `Physlib.lean` edit is committed. When the approved slices are integrated in order, only the
two slice-3 imports above are new at this cutoff.

## Production declaration inventory

The names below are in `Optics.MicroringCascade`.

### Determinants and pivot

- `DateCascadeStage.continuityChainMatrix_det`
- `dateFourPortBackwardFirstChainMatrix_det`
- `DateCascadeStage.compositionMatrix_det`
- `dateCascadeComposition_det`
- `dateChain_det_eq_entry11_mul_entry22_sub_entry12_mul_entry21`
- `dateChain_leadingBlock_action`
- `dateChain_hasBijectiveLeadingBlock_iff_entry11_ne_zero`
- `dateChain_hasWellPosedZeroReturn_iff_entry11_ne_zero`
- `dateChain_leadingBlockInverse_entry`
- `dateChain_rightTerminatedReflection_entry_zero`
- `dateChain_rightTerminatedTransmission_entry_zero`

### Behavior-derived DATE'14 Thm. 5 response

- `DateCascadeTerminationHypotheses`
- `DateCascadeTerminationHypotheses.hasBijectiveLeadingBlock`
- `DateCascadeTerminationHypotheses.hasBijectiveZeroReturnPivot`
- `DateCascadeTerminationHypotheses.hasWellPosedZeroReturn`
- `dateTerminatedCascadeReflectionTransform`
- `dateTerminatedCascadeTransmissionTransform`
- `dateTerminatedCascadeReflectivity`
- `dateTerminatedCascadeTransmissivity`
- `dateTerminatedCascadeReflectionTransform_eq_chain`
- `dateTerminatedCascadeTransmissionTransform_eq_chain`
- `dateTerminatedCascade_reflectivity_eq_neg_entry12_div_entry11`
- `dateTerminatedCascade_transmissivity_eq_one_div_entry11`

### Identical-cascade DATE'14 Thm. 6 response

- `DateIdenticalTerminationHypotheses`
- `DateIdenticalTerminationHypotheses.toCascade`
- `dateIdenticalTerminatedCascadeReflectivity`
- `dateIdenticalTerminatedCascadeTransmissivity`
- `dateSylvesterClosedForm_entry11`
- `dateSylvesterClosedForm_entry12`
- `DateCascadeStage.compositionMatrix_entry11`
- `DateCascadeStage.compositionMatrix_entry12`
- `dateIdenticalTerminationDenominator`
- `dateIdenticalCascadeComposition_entry11_eq_denominator_div_forwardTransfer`
- `DateIdenticalTerminationHypotheses.denominator_ne_zero`
- `dateIdenticalTerminatedCascade_reflectivity_eq_closedForm`
- `dateIdenticalTerminatedCascade_transmissivity_eq_closedForm`

Only the four results corresponding directly to DATE'14 Thms. 5--6 are declared as `theorem`.
All supporting results are `lemma`. The prior U2 Markdown nit is gone; the relevant source gate
is a single code span here:
`DateCascadeStage.hasBijectiveRingTransmission_iff_forwardTransfer_ne_zero`.

## Pivot and relational derivation

DATE Def. 8's `c_N = 0` is represented by `RightLoadBehavior.zeroReflection`. Its definition and
membership result at `Physlib/Optics/Network/TwoPortTermination.lean:100-121` say exactly that
the returning right wave is zero. They make no impedance or absorption claim.

The generic criterion at
`Physlib/Optics/Network/TwoPortChainTermination.lean:349-389` characterizes well-posed right
termination by pivot injectivity plus solvability. The zero-return specialization at
`Physlib/Optics/Network/TwoPortChainTermination.lean:686-710` identifies that pivot with the
leading chain block. For the singleton DATE channel, production proves the exact equivalence

```text
HasWellPosedRightTermination 0 <-> M11 != 0.
```

`DateCascadeTerminationHypotheses` retains both independent gates:

- every ring has the transmission pivot required to construct its chain graph; and
- the complete selected cascade has `M11 != 0`.

The relational cascade is identified with the composition graph through
`Heterogeneous.lean:227-235`. The reflection and transmission transforms are then extracted from
the terminated behavior. Their scalar coefficients are not defined as quotients. The two Thm. 5
results subsequently prove

```text
reflect = -M12 / M11
transm = 1 / M11.
```

The transmission proof first obtains the Schur response from the terminated behavior, then uses
the cascade determinant-one lemma. That determinant is derived from every ring transmission gate
and the determinant-one continuity matrices.

## Identical-cascade closed form

`DateIdenticalTerminationHypotheses` retains:

- the repeated ring-to-chain transmission pivot;
- every field of `DateSylvesterHypotheses`; and
- the selected count's distinct `M11 != 0` termination pivot.

The production result at `Identical.lean:336-343` supplies the proved source Sylvester matrix.
With `S_N = sin(N theta) / sin(theta)`, the common denominator is represented exactly as

```text
D_N = E * S_N - R * S_(N-1),
```

where `E` is the backward continuity factor and `R` is `dateForwardTransfer`. Production proves
`M11 = D_N / R` and derives `D_N != 0` from the selected pivot. DATE'14 Thm. 6 follows as

```text
reflect_N = T * E * S_N / D_N
transm_N = R / D_N.
```

These remain field-amplitude ratios. No power normalization is inferred.

## Regression declaration inventory

The positive construction and raw folds are:

- `dateTerminationRegressionRing`
- `dateTerminationRegressionStage`
- `dateTerminationRegressionRing_roundTripPhase`
- `dateTerminationRegressionRing_fieldAttenuation`
- `dateTerminationRegressionRing_phaseFactors`
- `dateTerminationRegressionRing_denominator`
- `dateTerminationRegressionRing_transfers`
- `dateTerminationRegressionStage_hasBijectiveRingTransmission`
- `dateTerminationRegressionStage_busPhase`
- `dateTerminationRegressionStage_signedContinuity`
- `dateTerminationRegressionMatrix`
- `dateTerminationRegressionStage_compositionMatrix`
- `dateTerminationRegressionStage_sylvester`
- `dateTerminationRegression_rawFold_two`
- `dateTerminationRegression_rawFold_three`
- `dateTerminationRegression_rawFold_two_entry11`
- `dateTerminationRegression_rawFold_three_entry11`
- `dateTerminationRegressionHypotheses_two`
- `dateTerminationRegressionHypotheses_three`

The direct behavior anchors and their local action facts are:

- `dateTerminationRegression_negativeOne_pivot_action`
- `dateTerminationRegression_negativeOne_incident_action`
- `dateTerminationRegression_negativeOne_lowerLeft_action`
- `dateTerminationRegression_negativeOne_lowerRight_action`
- `dateTerminationRegression_negativeMatrix_pivot_action`
- `dateTerminationRegression_negativeMatrix_incident_action`
- `dateTerminationRegression_negativeMatrix_lowerLeft_action`
- `dateTerminationRegression_negativeMatrix_lowerRight_action`
- `dateTerminationRegression_two_reflectivity_by_hand`
- `dateTerminationRegression_two_transmissivity_by_hand`
- `dateTerminationRegression_two_responses_by_hand`
- `dateTerminationRegression_three_reflectivity_by_hand`
- `dateTerminationRegression_three_transmissivity_by_hand`
- `dateTerminationRegression_three_responses_by_hand`

The singular construction and failure facts are:

- `dateTerminationRegressionSingularRing`
- `dateTerminationRegressionSingularStage`
- `dateTerminationRegressionSingularRing_phaseData`
- `dateTerminationRegressionSingularRing_transfers`
- `dateTerminationRegressionSingularStage_hasBijectiveRingTransmission`
- `dateTerminationRegressionSingularStage_signedContinuity`
- `dateTerminationRegressionSingularMatrix`
- `dateTerminationRegressionSingularStage_compositionMatrix`
- `dateTerminationRegressionSingular_rawFold_entry11`
- `dateTerminationRegressionSingular_chain_not_wellPosed`
- `dateTerminationRegressionSingular_not_wellPosed`
- `dateTerminationRegressionSingular_not_hypotheses`

## Independent positive anchors

The joined DATE fixture uses

```text
r = 3/5, t = 4/5, L_c = 1, alpha = 0,
lambda = 2, n_eff = 1, L_b = 1/2.
```

It has `R = -15/17`, `T = 8 I/17`, and displayed backward-first stage matrix

```text
[[-17 I/15, -8/15],
 [    -8/15, 17 I/15]].
```

The regressions unfold the matrices and neutral fold directly, proving by hand

```text
N = 2: raw fold = -1,     reflect = 0,      transm = -1
N = 3: raw fold = -stage, reflect = 8 I/17, transm = -15 I/17.
```

The response anchors use the graph of each behavior-derived transform, the raw termination
equations, and locally expanded pivot and block actions. They do not invoke either Thm. 5 quotient
theorem or either Thm. 6 closed-form theorem. Thus sign, coordinate order, load orientation, and
the transmission denominator can fail independently of the production formulas.

## Load-bearing negative control

The concrete control uses

```text
r = 3/4, t = 5/4, L_c = 1, alpha = 0,
lambda = 2, n_eff = 1, L_b = 1/2.
```

`DateParameters` does not impose unitarity. This point has `R = -24/25 != 0` and `T = I`, so its
own ring-to-chain pivot is valid and its relational cascade agrees with the chain graph. Its
displayed stage matrix is

```text
[[-25 I/24,       -25/24],
 [   -25/24, 1201 I/600]].
```

Direct multiplication proves the two-stage `M11 = 0`. The regression then proves all three
failure levels:

- the chain zero-return termination is not well posed;
- the concrete relational cascade with `RightLoadBehavior.zeroReflection` is not well posed; and
- `DateCascadeTerminationHypotheses` is uninhabited at that parameter point.

This fixture retains the ring pivot and fails at the complete-cascade pivot, so the missing DATE
source condition is mechanically load-bearing.

## Milestone and parity disposition

This slice discharges the S7C bullet "terminated reflection and transmission" at `goal.md:2423`.
It satisfies H-06, quoted as "terminated-cascade reflection and transmission agree with
relational termination" at `goal.md:2591`.

The IP-18 row is DATE'14 Def. 8 plus Thms. 5--6, page 5. It is discharged by the four headline
theorems listed above, under the corrected `M11 != 0` hypothesis. The source row is recorded at
`/Users/aadarwal/src/aadarwal/physlib-parity/PARITY-LEDGER.md:125`; changing ledger status remains
conductor-owned.

## Scope and non-claims

- The modeled load is only zero return at the declared right termination plane.
- Reflectivity and transmissivity are complex field amplitudes, not power fractions.
- No impedance match, absorption, radiation, passivity, reciprocity, losslessness, causality,
  bandwidth, or material-realization result is claimed.
- No lattice/source-parity, quadruple, dispersion, SFG, or NSV comparison is claimed.
- The closed identical form is restricted to the exact Sylvester and selected-pivot domain.

## Exact validation record

All Lean work and the full battery ran under one held `lake-lock env bash` acquisition. The
temporary registry was restored byte-identically after the chain. Its SHA-256 before and after
was `1741548061db23303ec95ebe539feaa278fe777a8a70eb47e151e9171f29f263`.

At exact source head `9538674a748149da56333898a7a45a2257ed6ff3`, the chain was:

```text
lake exe cache get &&
lake --wfail build <the eight cumulative S7C modules listed above> &&
lake exe runPhyslibLinters &&
lake exe lint_all
```

Results:

- cache: no files to download; 8690 already decompressed;
- targeted `--wfail` build: passed, 2765 jobs;
- `runPhyslibLinters`: Physlib and QuantumInfo passed;
- `lint_all`: passed all stages and exited zero;
- import, alpha-import, TODO-duplicate, and sorry/pseudo checks passed;
- direct elaboration of both slice-3 modules passed without warnings;
- `git diff --check`, the 100-codepoint check, and banned-token checks passed;
- committed-state `./scripts/lint-style.sh` exited zero.

The style output contained only the pre-existing S7D-owned
`Physlib/Optics/Systems/DCDR/Topology.lean` 2200-line inventory entry. No S7C path appeared in any
baseline inventory. The temporary `Physlib.lean` diff is empty.

The source commit contains only the two slice-3 Lean files. This final cutoff commit changes only
`HANDOFF.md`.
