# S7C slice 3b handoff

## Cutoff

- Branch: `optics/s7c-cascade`
- X-not-ready cutoff: `9036f8393ccaa0e68e2bd292ded19b47d41ecda8`
- Required sync target: `329d5a59`
- Required target commit: `329d5a5915696967bd031fdb113786012e88c7a7`
- Target merge: `0cb73b748b998c46bbf85c4a0ad4dc810460ee21`
- Exact source-gated head: `85e0c89d47788fa851255d562cdd724d7c313d2e`
- Final cutoff: this HANDOFF-only commit
- X option: (b), withdraw literal printed Thm. 6 parity

The required target is an ancestor of this cutoff. Its deletion of the lane-local handoff was the
only merge conflict; the lane handoff was retained and all target code and registry changes were
accepted unchanged.

## Files and registrations

Slice 3 remains confined to:

- `Physlib.Optics.Systems.Cascade.Termination`
- `Physlib.Optics.Systems.Cascade.TerminationRegression`

The sync target registers all six approved slice-1 and slice-2 modules. The exact gate temporarily
added the two slice-3 imports, giving this cumulative S7C battery:

- `Physlib.Optics.Network.TwoPortChainFold`
- `Physlib.Optics.Network.TwoPortChainFoldRegression`
- `Physlib.Optics.Systems.Cascade.Heterogeneous`
- `Physlib.Optics.Systems.Cascade.HeterogeneousRegression`
- `Physlib.Optics.Systems.Cascade.Identical`
- `Physlib.Optics.Systems.Cascade.IdenticalRegression`
- `Physlib.Optics.Systems.Cascade.Termination`
- `Physlib.Optics.Systems.Cascade.TerminationRegression`

No `Physlib.lean` change is committed. Only the final two imports remain for conductor
registration.

## X disposition

### X-1: printed Thm. 6 parity withdrawn

Option (b) is implemented. The two identical-cascade headlines were renamed and demoted:

- removed `dateIdenticalTerminatedCascade_reflectivity_eq_closedForm`;
- removed `dateIdenticalTerminatedCascade_transmissivity_eq_closedForm`;
- added `dateIdenticalTerminatedCascade_reflectivity_eq_relationalSylvesterForm` as a lemma; and
- added `dateIdenticalTerminatedCascade_transmissivity_eq_relationalSylvesterForm` as a lemma.

The supporting denominator API was also renamed so it does not imply a printed-source identity:

- `dateIdenticalSylvesterTerminationDenominator`;
- `dateIdenticalCascadeComposition_entry11_eq_sylvesterDenominator_div_forwardTransfer`; and
- `DateIdenticalTerminationHypotheses.sylvesterDenominator_ne_zero`.

There are now exactly two `theorem` declarations in `Termination.lean`, both passed DATE Thm. 5
results. `TerminationRegression.lean` has no theorem declaration.

### X-2: singular control made independent

The false claim `R = M11 = 0` is removed. The concrete ring has `R = -24/25 != 0`; only the
two-stage complete-cascade entry `M11` vanishes.

The new independent witness API is:

- `dateTerminationRegressionSingularKernel`;
- `dateTerminationRegressionSingularKernel_ne_zero`;
- `dateTerminationRegressionSingular_pivot_kernel`; and
- `dateTerminationRegressionSingular_pivot_not_injective`.

The raw fold entry is expanded by matrix multiplication at
`TerminationRegression.lean:820-835`. The named singleton vector is proved nonzero, and its raw
zero-return pivot image is proved zero at `:837-874`. The chain failure at `:876-886` uses only
`BackwardFirstChainTransform.hasWellPosedRightTermination_iff_pivot_injective_and_solvable`, the
generic N3T criterion. It never invokes `dateChain_hasWellPosedZeroReturn_iff_entry11_ne_zero`.

The relational failure then transports the concrete DATE behavior to its independently rejected
chain graph. The production hypothesis failure remains a separate direct contradiction with the
raw `M11 = 0` calculation.

### X-3: boundary claims completed

The production module now explicitly withholds:

- quadruple-ring, coupled-lattice, and full `M x N` lattice results;
- SFG-TR'14 and NSV'16 comparisons;
- any comparison that drops IP-12's principal-root/selected-half-arc equality;
- dispersion beyond a constant effective index at the selected carrier; and
- bundled IP-18 discharge, because that row contains printed DATE Thm. 6.

The earlier impedance, absorption, radiation, passivity, reciprocity, losslessness, causality,
bandwidth, material-realization, termination-plane, and field-versus-power boundaries remain.

## Printed Thm. 6 mismatch

The primary extraction is `scratchpad/papers/DATE14.txt:349-364`. Printed Thm. 6 uses
`exp (-j*(L_b/L_c)*delta)`. In this model that is the forward factor
`DateCascadeStage.forwardContinuityFactor`, defined at `Heterogeneous.lean:110-116`.

The proved chain entries instead contain
`DateCascadeStage.backwardContinuityFactor = exp (+I*phi)`, as exposed at
`Termination.lean:509-525`. The corrected denominator therefore has the form

```text
D_N = E_backward * S_N - R * S_(N-1).
```

Printed Thm. 6 also defines a distinct angle using `Re(cos⁻¹(...))`. Physlib's prior IP-17 result
uses the real angle

```text
dateSylvesterAngle M = Real.arccos (Re(M11)).
```

No equality between the two propagation factors or between the two angles is assumed or proved.
No bridge is forced, and this lane does not classify which Thm. 6 expression was intended.

The retained corrected relational/Sylvester lemmas are

```text
reflect_N = T * E_backward * S_N / D_N
transm_N = R / D_N.
```

They follow honestly from the passed relational response and the proved IP-17 Sylvester matrix.
They are not identified with printed DATE Thm. 6.

## Passed relational core retained

Reviewer X closed the DATE Def. 8 and Thm. 5 core. It was not altered in 3b.

- `RightLoadBehavior.zeroReflection` literally imposes `aR = 0`.
- The generic right-termination pivot criterion remains at
  `TwoPortChainTermination.lean:349-389`.
- Zero return identifies the pivot with the leading block at
  `TwoPortChainTermination.lean:688-710`.
- DATE singleton well-posedness is equivalent to `M11 != 0`.
- Both response transforms are extracted from `dateCascadeBehavior`.
- The behavior transforms are bridged to the chain before scalar formulas are derived.
- Determinant one is derived from the exact per-ring chain gates.

The two literature theorems remain:

- `dateTerminatedCascade_reflectivity_eq_neg_entry12_div_entry11`; and
- `dateTerminatedCascade_transmissivity_eq_one_div_entry11`.

They prove, from the terminated relational behavior,

```text
reflect = -M12 / M11
transm = 1 / M11.
```

The quotient formulas are not definitions.

## Production declaration inventory

All names are in `Optics.MicroringCascade`.

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

### Relational zero-return response

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

### Corrected identical-cascade specialization

- `DateIdenticalTerminationHypotheses`
- `DateIdenticalTerminationHypotheses.toCascade`
- `dateIdenticalTerminatedCascadeReflectivity`
- `dateIdenticalTerminatedCascadeTransmissivity`
- `dateSylvesterClosedForm_entry11`
- `dateSylvesterClosedForm_entry12`
- `DateCascadeStage.compositionMatrix_entry11`
- `DateCascadeStage.compositionMatrix_entry12`
- `dateIdenticalSylvesterTerminationDenominator`
- `dateIdenticalCascadeComposition_entry11_eq_sylvesterDenominator_div_forwardTransfer`
- `DateIdenticalTerminationHypotheses.sylvesterDenominator_ne_zero`
- `dateIdenticalTerminatedCascade_reflectivity_eq_relationalSylvesterForm`
- `dateIdenticalTerminatedCascade_transmissivity_eq_relationalSylvesterForm`

## Regression inventory and anchors

The positive construction and raw folds remain:

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

The raw action and behavior anchors remain:

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

The singular construction and failure chain are:

- `dateTerminationRegressionSingularRing`
- `dateTerminationRegressionSingularStage`
- `dateTerminationRegressionSingularRing_phaseData`
- `dateTerminationRegressionSingularRing_transfers`
- `dateTerminationRegressionSingularStage_hasBijectiveRingTransmission`
- `dateTerminationRegressionSingularStage_signedContinuity`
- `dateTerminationRegressionSingularMatrix`
- `dateTerminationRegressionSingularStage_compositionMatrix`
- `dateTerminationRegressionSingular_rawFold_entry11`
- `dateTerminationRegressionSingularKernel`
- `dateTerminationRegressionSingularKernel_ne_zero`
- `dateTerminationRegressionSingular_pivot_kernel`
- `dateTerminationRegressionSingular_pivot_not_injective`
- `dateTerminationRegressionSingular_chain_not_wellPosed`
- `dateTerminationRegressionSingular_not_wellPosed`
- `dateTerminationRegressionSingular_not_hypotheses`

The positive joined fixture is unchanged:

```text
r=3/5, t=4/5, Lc=1, alpha=0, lambda=2, neff=1, Lb=1/2
R=-15/17, T=8I/17
stage=[[-17I/15,-8/15],[-8/15,17I/15]]
N=2: raw=-1, reflect=0, transm=-1
N=3: raw=-stage, reflect=8I/17, transm=-15I/17.
```

The anchors call neither Thm. 5 quotient theorem nor either corrected identical-cascade lemma.

The negative joined fixture is unchanged apart from its independent kernel proof:

```text
r=3/4, t=5/4, Lc=1, alpha=0, lambda=2, neff=1, Lb=1/2
R=-24/25 != 0, T=I
stage=[[-25I/24,-25/24],[-25/24,1201I/600]]
two-stage M11=0.
```

`DateParameters` imposes no unitarity restriction. The ring-to-chain pivot therefore remains
valid at this point, while the complete-cascade termination pivot fails.

## Milestone and parity disposition

H-06, "terminated-cascade reflection and transmission agree with relational termination", is
established by the passed Thm. 5 core and independent positive anchors.

The broad S7C terminated-reflection/transmission construction exists, including the corrected
relational/Sylvester specialization. However, IP-18 bundles DATE Def. 8 and Thms. 5--6. Because
printed Thm. 6 is not bridged, this lane does not discharge IP-18 and does not request a ledger
status flip. The Thm. 5 portion is proved; the bundled parity row remains withheld.

## Scope and non-claims

- The modeled load is only zero return at the declared right termination plane.
- Reflectivity and transmissivity are complex field amplitudes, not power fractions.
- No impedance match, absorption, radiation, passivity, reciprocity, losslessness, causality,
  bandwidth, or material realization is inferred.
- No quadruple-ring, coupled-lattice, or full `M x N` lattice theorem is claimed.
- No SFG-TR'14 or NSV'16 comparison is claimed.
- IP-12's principal-root/selected-half-arc equality is not supplied or bypassed.
- Effective index is fixed at the selected carrier; no dispersion model is claimed.
- Printed DATE Thm. 6 and bundled IP-18 parity are explicitly withheld.

## Exact validation record

All Lean work and the complete battery ran under one `lake-lock env bash` acquisition. The
temporary registry added only the two slice-3 imports and was restored byte-identically.
`Physlib.lean` had SHA-256
`d6279000556c059e0a352aac530487e353adc7e5fa1f7c05b2bce229ec34f510` before and after.

At exact source head `85e0c89d47788fa851255d562cdd724d7c313d2e`, the single chain was:

```text
lake exe cache get &&
lake --wfail build <the eight cumulative S7C modules listed above> &&
lake exe runPhyslibLinters &&
lake exe lint_all &&
./scripts/lint-style.sh
```

Results:

- cache: no files to download; 8690 already decompressed;
- targeted `--wfail` build: passed, 2765 jobs;
- `runPhyslibLinters`: Physlib and QuantumInfo passed;
- `lint_all`: all seven stages completed and the command exited zero;
- its full build was successful;
- import, illegal-import, alpha-import, TODO, and sorry/pseudo stages completed;
- its declaration linters passed for Physlib and QuantumInfo;
- direct elaboration of both slice-3 modules passed without warnings;
- committed-state `lint-style.sh` exited zero;
- `git diff --check`, the 100-codepoint check, and banned-token checks passed.

The repository-wide inventories contained no S7C path. The file-import inventory named the four
sync-target AllPass-Z modules, and the committed-style inventory named only the known S7D-owned
`Physlib/Optics/Systems/DCDR/Topology.lean` line-count entry. No finding belongs to this slice.

The source commit changes only the two slice-3 Lean files. This final cutoff commit changes only
`HANDOFF.md`.

# S7C slice 4a: stagewise SFG-TR add-drop mapping

## Cutoff scope and synchronization

This cutoff implements slice 4a only. It covers the SFG-TR'14 half of the goal text
"the source-mapped SFG-TR'14 add-drop case and NSV'16 PANDA Vernier case." The NSV'16 PANDA
half is intentionally deferred to slice 4b, as authorized by the controller; IP-13 and IP-14
remain TBD and no goal.md milestone row is claimed closed by 4a alone.

The required sync target was `0ea95dd99639300ec686534810467fe5cd4c2550`. It was merged before
implementation in merge commit `05d016a7b279a225ccfe8e876597d6780048092f`, and ancestry was
rechecked at the gate.

The U2 split-code-span Markdown nit is absent after the intervening handoff replacement; this
edit does not reintroduce the split declaration span.

## Construction and source disposition

The existing IP-12 dictionary is reused, not replicated:

- `SfgParameters.ofAddDrop` maps Physlib data to the five source coefficients at
  `Physlib/Optics/Systems/Microring/SourceBridgeSfg.lean:64-74`;
- `sfgAddDropTransfer` stores the printed quotient at that file's lines 85-91; and
- `sfgAddDropTransfer_eq_dropTransfer` requires the explicit principal-root equality at
  that file's lines 98-105.

`sfgAddDropStageTransfer` is literally the function composition

```text
sfgAddDropTransfer composed with SfgParameters.ofAddDrop.
```

The list construction applies that dictionary independently to each stage record. It does not
claim that the listed drop ports are physically interconnected and does not introduce a scalar
cascade formula. Thus this is a cascade-context instantiation of already discharged IP-12, not a
new source theorem or a second parity discharge.

## Production declaration inventory

All names are in `Optics.MicroringCascade` and are defined in
`Physlib/Optics/Systems/Cascade/SourceMappedSfg.lean`.

- `sfgAddDropStageTransfer`
- `sfgAddDropStageTransfer_eq_dropTransfer`
- `sfgAddDropStageTransfers`
- `sfgAddDropStageTransfers_eq_dropTransfers`

Both comparison lemmas retain, for each compared stage, the exact gate

```text
Complex.sqrt p.roundTripCoefficient = p.firstArcCoefficient.
```

## Regression inventory and independent anchors

All names are in `Optics.MicroringCascade` and are defined in
`Physlib/Optics/Systems/Cascade/SourceMappedSfgRegression.lean`.

- `sourceMappedSfgRegression_sqrt_quarter`
- `sourceMappedSfgRegression_sqrt_neg_quarter`
- `sourceMappedSfgRegression_zeroPhase_transfer`
- `sourceMappedSfgRegression_halfTurn_transfer`
- `sourceMappedSfgRegression_twoStage_list`
- `sourceMappedSfgRegression_zeroPhase_rootGate`
- `sourceMappedSfgRegression_halfTurn_not_rootGate`
- `sourceMappedSfgRegression_halfTurn_transfer_ne_dropTransfer`

The two fixtures are the exact `3-4-5` add-drop records at
`Physlib/Optics/Systems/Microring/AddDropRegression.lean:62-69,402-409`. The regression unfolds
the composed source dictionary and quotient directly; it invokes neither production comparison
lemma. Its concrete values are

```text
zero phase: source composition = -32/91, and the root gate holds;
half turn: source composition = -32*I/109;
           N7/N5 drop transfer = 32*I/109;
           the root gate fails.
```

The half-turn fixture therefore makes both the gate and the claimed comparison genuinely able to
fail. It is not a regression oracle routed through the bridge theorem.

## Validation bindings

The validation lane should bind these public names:

- list-level positive statement: `sfgAddDropStageTransfers_eq_dropTransfers`;
- direct ordered-list anchor: `sourceMappedSfgRegression_twoStage_list`;
- inhabited gate: `sourceMappedSfgRegression_zeroPhase_rootGate`;
- failing gate: `sourceMappedSfgRegression_halfTurn_not_rootGate`; and
- false ungated comparison: `sourceMappedSfgRegression_halfTurn_transfer_ne_dropTransfer`.

## Scope and non-claims

- This cutoff makes no new SFG-TR'14 source claim and does not change IP-12's status.
- IP-13 and IP-14, NSV'16 Def. 11 and Thms. 5-6, the 18-node PANDA graph, and its Mason/N7
  derivation remain for slice 4b.
- The stage list is not a physical interconnection of add-drop ports and is not a scalar cascade
  transfer law.
- No DATE lattice, quadruple-ring, coupled-lattice, or full `M x N` lattice result is claimed.
- No dispersion, bending loss, bandwidth, causality, resonance, or measurement validation is
  claimed.
- No power statement is made. Any later power interpretation is normalized modal power until the
  finite common-frequency Maxwell and aperture-flux hypotheses at
  `Physlib/Optics/HarmonicFlux/PropagatingModePower.lean:60-90` are supplied.
- Human verification of the bibliographic statement and source transcription remains required by
  `AI-POLICY.md`.

## Exact validation record

The exact implementation source head was
`43b8153b714eef51a11efc775d14566be68fe491`. The single Lean lock hold temporarily registered the
four unmerged cascade modules, including both slice-4a modules, and ran

```text
lake exe cache get &&
lake --wfail build <the eight cumulative S7C cascade modules> &&
lake exe runPhyslibLinters &&
lake exe lint_all &&
./scripts/lint-style.sh &&
the diff, banned-token, and 100-codepoint audits.
```

Results:

- cache: no files to download; 8690 already decompressed;
- targeted warning-free build: passed, 2766 jobs;
- `runPhyslibLinters`: Physlib and QuantumInfo passed;
- `lint_all`: full build successful; file/illegal/alpha/TODO/sorry stages completed; declaration
  linters passed for Physlib and QuantumInfo;
- the repository inventories named no S7C file;
- direct scoped style, `git diff --check`, banned-token, and Unicode-codepoint audits passed for
  both new files; and
- the final repository-wide style command returned nonzero only for the synced S7D-owned
  `Physlib/Optics/Systems/DCDR/Topology.lean` 2035-line inventory entry. This cutoff does not edit
  or exempt that file.

The temporary registry was restored byte-identically: `Physlib.lean` had SHA-256
`d6279000556c059e0a352aac530487e353adc7e5fa1f7c05b2bce229ec34f510` before and after. The source
commits change only the two slice-4a Lean files; this final cutoff commit changes only
`HANDOFF.md`.
