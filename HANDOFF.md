# S7C N2b reciprocity metadata handoff

## Cutoff identity

- Branch: `optics/s7c-cascade`.
- Exact sync target: `b8ef32367b30e1880c396b838c7f1ae43d5eafde`.
- Sync merge: `fbfd0212569a4a8e8bde0fe81ca96dae53d86b24`.
- Gated source: `0a388cbdb3dbd077560f4c8d5275af9d7ea6e5cc`.
- This document is the HANDOFF-only cutoff child of that gated source.
- Authorized files: `Physlib/Optics/Network/Reciprocity.lean` and
  `Physlib/Optics/Network/ReciprocityRegression.lean`, both new.
- Registration order: production, then regression.

## Goal and decision scope

At the cutoff reference, `goal.md:1966-1974` says verbatim:

> #### N2b. Reciprocity convention metadata
>
> - time-reversed channel pairing;
> - reference-plane and port-phase conventions;
> - their transformation under relabeling and rephasing; and
> - the precise reciprocity predicate induced by those choices.
>
> Exit: reciprocity has a physical convention rather than an unexplained matrix-symmetry label. This
> package remains blocked on the decision in section L; it does not block N2a--N6a.

The decision gate is already checked at `goal.md:2744-2745`. The source cutoff does not edit
`goal.md`. The live status row at `goal.md:2848` is verbatim:

```text
| N2b reciprocity metadata | blocked | human convention decision | time-reversal/reference-plane API |
```

The integration child must replace that row exactly with:

```text
| N2b reciprocity metadata | done | human convention decision | time-reversal/reference-plane API |
```

The integration child must not edit the declaration bullets at `goal.md:1966-1974` or the
decision-gate rows at `goal.md:2744-2745`, as required by
`scratchpad/lanes/msg-15-n2b-confirm.txt`.

This implementation follows Revision 4 of
`scratchpad/lanes/decisions/decision-L6.md` and Revision 4 of
`scratchpad/lanes/decisions/registry-draft-A1.md`. It does not add the separately queued
reciprocity instances or closure results from N6b.

## Claims

`ChannelPairing` is supplied label-level data from incident ends to outgoing ends. The nominal
pairing preserves labels, and pairings transport along an equivalence. A scattering matrix is
reciprocal for a supplied pairing exactly when its outgoing rows, transported through that
pairing, form a transpose-symmetric matrix. This predicate and its paired matrix are covariant
under relabeling.

`ReferencePlaneShift` records two unit-phase gauges and the designated tau-inverse-paired law.
The paired matrix transforms by `D * A * D`; nominal pairing gives the ordinary `D * S * D`
formula. Tau-inverse-paired rephasing preserves reciprocity. More generally, rephasing preserves
every paired-symmetric matrix if and only if the paired output phase times the corresponding
incident phase is constant across labels.

`TimeReversalRealization` is a proof-bearing structure over four predicates supplied by a
component. It creates neither a pairing nor a physical instance. The regression enforces C-07 at
this abstract structure level, C-08 at the reference-plane algebra level, and C-09 at the
paired-transpose predicate level with primitive finite counterexamples.

## Non-claims

A `ChannelPairing` alone is not physical time reversal. A `ReferencePlaneShift` is not
`PortConnectionFamily.IsMatchedGauge`. No result asserts losslessness, passivity, raw Jones or
Fresnel reciprocity, reverse-incidence Maxwell physics, component realization, modal
completeness, propagation distance, delay, electromagnetic power, measurement, or physical
realization. Transpose symmetry is asserted only in paired, power-normalized scattering
coordinates; Hermitian symmetry is explicitly rejected as a substitute. Independent endpoint
gauges remain legal coordinate changes but are not called reference-plane shifts.

C-02 is unchanged: no right/left circular aliases are introduced. The abstention from R/L naming
remains deliberate under the controller's convention addendum.

## Production declarations

All declarations below are in `Physlib/Optics/Network/Reciprocity.lean`.

- `Physlib/Optics/Network/Reciprocity.lean:91` `Optics.ChannelPairing`: endpoint equivalence.
- `Physlib/Optics/Network/Reciprocity.lean:94` `Optics.nominalPairing`: nominal pairing.
- `Physlib/Optics/Network/Reciprocity.lean:99` `Optics.nominalPairing_apply`: endpoint action.
- `Physlib/Optics/Network/Reciprocity.lean:105` `Optics.ChannelPairing.reindex`: transport.
- `Physlib/Optics/Network/Reciprocity.lean:112` `Optics.ChannelPairing.reindex_apply`:
  transported endpoint action.
- `Physlib/Optics/Network/Reciprocity.lean:122` `Optics.ChannelPairing.reindex_nominalPairing`:
  nominal naturality.
- `Physlib/Optics/Network/Reciprocity.lean:139` `Optics.ScatteringMatrix.pairedMatrix`:
  pairing-transported row matrix.
- `Physlib/Optics/Network/Reciprocity.lean:146` `Optics.ScatteringMatrix.pairedMatrix_apply`:
  entry formula.
- `Physlib/Optics/Network/Reciprocity.lean:153` `Optics.ScatteringMatrix.IsReciprocal`:
  paired transpose symmetry.
- `Physlib/Optics/Network/Reciprocity.lean:158` `Optics.ScatteringMatrix.isReciprocal_iff`:
  entrywise characterization.
- `Physlib/Optics/Network/Reciprocity.lean:171`
  `Optics.ScatteringMatrix.pairedMatrix_nominalPairing`: nominal reduction.
- `Physlib/Optics/Network/Reciprocity.lean:176`
  `Optics.ScatteringMatrix.isReciprocal_nominalPairing_iff`: nominal symmetry iff.
- `Physlib/Optics/Network/Reciprocity.lean:186`
  `Optics.ScatteringMatrix.pairedMatrix_reindex`: matrix relabeling covariance.
- `Physlib/Optics/Network/Reciprocity.lean:198`
  `Optics.ScatteringMatrix.isReciprocal_reindex_iff`: reciprocity relabeling iff.
- `Physlib/Optics/Network/Reciprocity.lean:216` `Optics.ReferencePlaneShift`: two gauges and law.
- `Physlib/Optics/Network/Reciprocity.lean:218`, `:220`, `:222`
  `Optics.ReferencePlaneShift.incidentGauge`,
  `.outgoingGauge`, `.inverse_paired`: the two legs and their designated relation.
- `Physlib/Optics/Network/Reciprocity.lean:229`
  `Optics.ScatteringMatrix.pairedMatrix_rephase_apply`: entrywise gauge formula.
- `Physlib/Optics/Network/Reciprocity.lean:239`
  `Optics.ScatteringMatrix.pairedMatrix_rephase_referencePlaneShift_eq_D_mul_D`:
  pairing-aware diagonal congruence.
- `Physlib/Optics/Network/Reciprocity.lean:253`
  `Optics.ScatteringMatrix.rephase_referencePlaneShift_eq_D_S_D`: nominal corollary.
- `Physlib/Optics/Network/Reciprocity.lean:265`
  `Optics.ScatteringMatrix.isReciprocal_rephase_tauInversePaired`: designated
  reference-plane sufficiency.
- `Physlib/Optics/Network/Reciprocity.lean:281`
  `Optics.ScatteringMatrix.rephase_preserves_pairedIsSymm_iff_constant`: exact
  constant-factor characterization.
- `Physlib/Optics/Network/Reciprocity.lean:370` `Optics.TimeReversalRealization`:
  proof-bearing four-predicate realization structure.
- `Physlib/Optics/Network/Reciprocity.lean:374`, `:376`, `:378`, `:381`
  `Optics.TimeReversalRealization.same_transverse_mode`,
  `.same_reference_plane`, `.equal_power_normalization`, `.exact_frame_transport`: its four
  component-supplied proof obligations.

No existing declaration was changed. Production imports no regression module.

## Primitive regression fixtures and validation names

All declarations below are in `Physlib/Optics/Network/ReciprocityRegression.lean`.

### Primitive phases, pairing, and gauges

- `Physlib/Optics/Network/ReciprocityRegression.lean:90`
  `Optics.reciprocityRegressionI` = `I`.
- `Physlib/Optics/Network/ReciprocityRegression.lean:94`
  `Optics.reciprocityRegressionNegI` = `-I`.
- `Physlib/Optics/Network/ReciprocityRegression.lean:98`
  `Optics.reciprocityRegressionNegOne` = `-1`.
- `Physlib/Optics/Network/ReciprocityRegression.lean:102`
  `Optics.reciprocityRegressionSwapPairing`: nonidentity `Fin 2` swap.
- `Physlib/Optics/Network/ReciprocityRegression.lean:108`
  `Optics.reciprocityRegressionSwapPairing_zero`: `0` pairs with `1`.
- `Physlib/Optics/Network/ReciprocityRegression.lean:114`
  `Optics.reciprocityRegressionSwapPairing_one`: `1` pairs with `0`.
- `Physlib/Optics/Network/ReciprocityRegression.lean:119`
  `Optics.reciprocityRegressionS15Incident` = `(1, I)`.
- `Physlib/Optics/Network/ReciprocityRegression.lean:123`
  `Optics.reciprocityRegressionS15SameLabelOutgoing` = `(1, -I)`.
- `Physlib/Optics/Network/ReciprocityRegression.lean:127`
  `Optics.reciprocityRegressionS15RestoringOutgoing` = `(-I, 1)`.
- `Physlib/Optics/Network/ReciprocityRegression.lean:131`
  `Optics.reciprocityRegressionS15WrongSignOutgoing` = `(I, 1)`.
- `Physlib/Optics/Network/ReciprocityRegression.lean:135`
  `Optics.reciprocityRegressionS16Gauge` = `(1, -1)`.
- `Physlib/Optics/Network/ReciprocityRegression.lean:140`
  `Optics.reciprocityRegressionS15Incident_zero`.
- `Physlib/Optics/Network/ReciprocityRegression.lean:145`
  `Optics.reciprocityRegressionS15Incident_one`.
- `Physlib/Optics/Network/ReciprocityRegression.lean:150`
  `Optics.reciprocityRegressionS15SameLabelOutgoing_zero`.
- `Physlib/Optics/Network/ReciprocityRegression.lean:155`
  `Optics.reciprocityRegressionS15SameLabelOutgoing_one`.
- `Physlib/Optics/Network/ReciprocityRegression.lean:160`
  `Optics.reciprocityRegressionS15RestoringOutgoing_zero`.
- `Physlib/Optics/Network/ReciprocityRegression.lean:165`
  `Optics.reciprocityRegressionS15RestoringOutgoing_one`.
- `Physlib/Optics/Network/ReciprocityRegression.lean:170`
  `Optics.reciprocityRegressionS15WrongSignOutgoing_zero`.
- `Physlib/Optics/Network/ReciprocityRegression.lean:175`
  `Optics.reciprocityRegressionS15WrongSignOutgoing_one`.
- `Physlib/Optics/Network/ReciprocityRegression.lean:180`
  `Optics.reciprocityRegressionS16Gauge_zero`.
- `Physlib/Optics/Network/ReciprocityRegression.lean:185`
  `Optics.reciprocityRegressionS16Gauge_one`.

### S-15 and S-16

- `Physlib/Optics/Network/ReciprocityRegression.lean:193`
  `Optics.reciprocityRegressionAllOnes`: primitive all-ones scattering transform.
- `Physlib/Optics/Network/ReciprocityRegression.lean:197`
  `Optics.reciprocityRegressionAllOnes_pairedMatrix`: direct all-ones expansion.
- `Physlib/Optics/Network/ReciprocityRegression.lean:204`
  `Optics.reciprocityRegressionAllOnes_isReciprocal`: initial symmetry.
- `Physlib/Optics/Network/ReciprocityRegression.lean:217`
  `Optics.reciprocityRegression_s15_sameLabel_matrix`:
  `!![-I, -1; 1, -I]`.
- `Physlib/Optics/Network/ReciprocityRegression.lean:230`
  `Optics.reciprocityRegression_s15_sameLabel_offDiagonal_ne`: `-1 != 1`.
- `Physlib/Optics/Network/ReciprocityRegression.lean:241`
  `Optics.reciprocityRegression_s15_sameLabel_not_reciprocal`: S-15 must fail.
- `Physlib/Optics/Network/ReciprocityRegression.lean:250`
  `Optics.reciprocityRegression_s15_restoring_inversePaired`: designated law.
- `Physlib/Optics/Network/ReciprocityRegression.lean:260`
  `Optics.reciprocityRegression_s15_restoring_matrix`:
  `!![1, -I; -I, -1]`.
- `Physlib/Optics/Network/ReciprocityRegression.lean:273`
  `Optics.reciprocityRegression_s15_restoring_isReciprocal`: restored symmetry.
- `Physlib/Optics/Network/ReciprocityRegression.lean:290`
  `Optics.reciprocityRegression_s16_pairingFactor`: factor constantly `-1`.
- `Physlib/Optics/Network/ReciprocityRegression.lean:298`
  `Optics.reciprocityRegression_s16_not_inversePaired`: not designated inverse pairing.
- `Physlib/Optics/Network/ReciprocityRegression.lean:310`
  `Optics.reciprocityRegression_s16_matrix`: `!![-1, 1; 1, -1]`.
- `Physlib/Optics/Network/ReciprocityRegression.lean:321`
  `Optics.reciprocityRegression_s16_isReciprocal`: S-16 must pass.

These expansions unfold `ScatteringMatrix.pairedMatrix`, `ScatteringMatrix.rephase`,
`ModeTransform.rephase`, the all-ones transform, the swap, and primitive complex arithmetic. They
do not use `pairedMatrix_reindex`, `isReciprocal_reindex_iff`,
`pairedMatrix_rephase_apply`,
`pairedMatrix_rephase_referencePlaneShift_eq_D_mul_D`,
`isReciprocal_rephase_tauInversePaired`, or
`rephase_preserves_pairedIsSymm_iff_constant`.

### C-07 structure-level enforcement

- `Physlib/Optics/Network/ReciprocityRegression.lean:339`
  `Optics.reciprocityRegressionToySameTransverseMode`.
- `Physlib/Optics/Network/ReciprocityRegression.lean:347`
  `Optics.reciprocityRegressionToySameReferencePlane`.
- `Physlib/Optics/Network/ReciprocityRegression.lean:355`
  `Optics.reciprocityRegressionToyEqualPowerNormalization`.
- `Physlib/Optics/Network/ReciprocityRegression.lean:363`
  `Optics.reciprocityRegressionToyExactFrameTransport`.
- `Physlib/Optics/Network/ReciprocityRegression.lean:368`
  `Optics.reciprocityRegressionSwap_timeReversalRealization`: the swap satisfies all four.
- `Physlib/Optics/Network/ReciprocityRegression.lean:386`
  `Optics.reciprocityRegression_nominal_not_timeReversalRealization`: the nominal identity
  pairing is rejected at incident label `0`, where the toy direction-reversal predicate requires
  outgoing label `1`.

These predicates are explicitly toy structure fixtures, not physical component predicates. C-07
moves STATED to ENFORCED only at the abstract structure level here. Physical instance-level
enforcement remains N6b's obligation.

### C-08 reference-plane enforcement

- The wrong-port S-15 sentinel at
  `Physlib/Optics/Network/ReciprocityRegression.lean:217` uses same-label inversion instead of the
  tau-partner output channel, producing off-diagonal entries `-1` and `1` and refusing reciprocity.
- `Physlib/Optics/Network/ReciprocityRegression.lean:401`
  `Optics.reciprocityRegression_s15_wrongSign_matrix` directly expands the wrong-sign
  output gauge to `!![1, -I; I, 1]`.
- `Physlib/Optics/Network/ReciprocityRegression.lean:413`
  `Optics.reciprocityRegression_s15_wrongSign_changes_pinned_entry` proves that the
  lower-left entry changes from the restoring value `-I` to the wrong-sign value `I`.
- `Physlib/Optics/Network/ReciprocityRegression.lean:425`
  `Optics.reciprocityRegression_s15_wrongSign_not_reciprocal` refuses that gauge.

Thus the wrong-port and wrong-sign variants are separate fail-capable fixtures; neither is merely
subsumed by prose. C-08 moves STATED to ENFORCED for the algebraic reference-plane convention.

### C-09 reciprocity-predicate enforcement

- `Physlib/Optics/Network/ReciprocityRegression.lean:439`
  `Optics.reciprocityRegressionRawSymmetric` = `diag(1, 2)`.
- `Physlib/Optics/Network/ReciprocityRegression.lean:443`
  `Optics.reciprocityRegressionRawSymmetric_isSymm`: raw coordinates are symmetric.
- `Physlib/Optics/Network/ReciprocityRegression.lean:450`
  `Optics.reciprocityRegressionRawSymmetric_pairedMatrix`:
  the swap pairing gives `!![0, 2; 1, 0]`.
- `Physlib/Optics/Network/ReciprocityRegression.lean:458`
  `Optics.reciprocityRegression_rawSymmetric_not_reciprocal`: raw symmetry is refused.
- `Physlib/Optics/Network/ReciprocityRegression.lean:467`
  `Optics.reciprocityRegressionHermitian` = `!![0, I; -I, 0]`.
- `Physlib/Optics/Network/ReciprocityRegression.lean:471`
  `Optics.reciprocityRegressionHermitian_isHermitian`: direct conjugate-transpose proof.
- `Physlib/Optics/Network/ReciprocityRegression.lean:479`
  `Optics.reciprocityRegressionHermitian_offDiagonal_ne`: `I != -I`.
- `Physlib/Optics/Network/ReciprocityRegression.lean:485`
  `Optics.reciprocityRegression_hermitian_not_reciprocal`: Hermitian symmetry is refused
  under nominal paired-transpose reciprocity.

C-09 moves STATED to ENFORCED for both pairing-aware rather than raw symmetry and transpose rather
than conjugate-transpose symmetry. No component-level physical reciprocity is claimed.

## Registry transition discipline

- C-07: STATED -> ENFORCED at the `TimeReversalRealization` structure level by the swap-accepting
  and nominal-refusing toy predicate pair at
  `Physlib/Optics/Network/ReciprocityRegression.lean:368` and `:386`; N6b still owes physical
  instances.
- C-08: STATED -> ENFORCED at the reference-plane algebra level by S-15 wrong-port `-1 != 1` and
  the explicit wrong-sign `-I != I` sentinel at
  `Physlib/Optics/Network/ReciprocityRegression.lean:413`.
- C-09: STATED -> ENFORCED at the paired-transpose predicate level by `diag(1,2)` becoming
  `!![0,2;1,0]` under the swap and by the Hermitian-but-not-symmetric `!![0,I;-I,0]` fixture.
- No other convention is claimed to move. In particular, C-02 is unchanged.

## Reviewer map

1. Read `Reciprocity.lean:91-127` for supplied pairings and transport.
2. Read `Reciprocity.lean:139-204` for paired symmetry and relabeling covariance.
3. Read `Reciprocity.lean:216-364` for reference-plane covariance and the exact iff.
4. Read `Reciprocity.lean:370-382` for the proof-bearing realization structure.
5. Re-derive S-15/S-16 from `ReciprocityRegression.lean:90-327`.
6. Check C-07 refusal at `ReciprocityRegression.lean:339-394`.
7. Check C-08 wrong sign at `ReciprocityRegression.lean:401-433`.
8. Check both C-09 confusions at `ReciprocityRegression.lean:439-491`.

## Exact validation record

The root-first chain ran with temporary sorted registration and `Physlib.lean` was then restored
byte-identically.

- Targeted regression build: PASS, 2717 jobs, no warnings.
- `lake exe cache get`: PASS.
- `lake --wfail build Physlib`: PASS, 5023 jobs.
- `check_file_imports`: PASS.
- `sorry_lint`: PASS.
- `runPhyslibLinters`: PASS for Physlib and QuantumInfo.
- `api_map_index`: PASS, 34 maps, 653 requirements, 505 done.
- `lint_all`: PASS; only pre-existing repository-wide style and transitive-import advisories,
  with no Reciprocity hit.
- committed-state `scripts/lint-style.sh`: PASS.
- `module_doc_lint`: the repository-wide backlog remains nonzero; a filtered rerun found zero
  Reciprocity hits.
- `git diff --check`: PASS.
- File lengths: production 385, regression 494; both below 1500.
- Maximum line length: 99 codepoints in each file.
- Both modules are lemma-only and contain no `sorry`, `axiom`, `native_decide`,
  `maxHeartbeats`, or `Lean.ofReduceBool`.
- Both module docs use the four literal headings and matching tables of contents.
- Production imports no regression module.
- Relative to the exact base, excluding the pre-existing branch HANDOFF, the source adds exactly
  the two authorized modules.
- `Physlib.lean` SHA-256 before and after:
  `c54d6030b0fe32d41cd7088aec51224141d6f35cb5997bd4b0f4668f9a1cf0bf`.

This final cutoff child changes only `HANDOFF.md`. Human verification remains required by
`AI-POLICY.md`.
