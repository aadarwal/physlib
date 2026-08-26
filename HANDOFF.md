# S7C slice 1b handoff

## Cutoff

- Branch: `optics/s7c-cascade`
- Required sync target used: `aff2484ecc7fd14f456b0c85a71d282c6b4f4052`
- Sync merge: `cf0061a59fdfe47db06e1b6628ea3ba8b4bad867`
- Slice: heterogeneous DATE cascade (IP-15 / H-03), neutral N3T fold, and U2 sign sentinel

## Files and registrations

Register these four new modules in sorted order in `Physlib.lean`:

- `Physlib.Optics.Network.TwoPortChainFold`
- `Physlib.Optics.Network.TwoPortChainFoldRegression`
- `Physlib.Optics.Systems.Cascade.Heterogeneous`
- `Physlib.Optics.Systems.Cascade.HeterogeneousRegression`

The shipped registry linters were run with those imports added temporarily. The temporary
`Physlib.lean` edit was removed byte-identically before the cutoff gate record.

## Declarations

### `Physlib/Optics/Network/TwoPortChainFold.lean`

- `BackwardFirstTwoPortBehavior.seriesFold`
- `BackwardFirstTwoPortBehavior.seriesFold_hasLeftToRightChainView`
- `BackwardFirstChainTransform.fold`
- `BackwardFirstChainTransform.fold_append`
- `BackwardFirstChainTransform.fold_replicate`
- `BackwardFirstChainTransform.seriesFold_map_toBehavior_hasLeftToRightChainView`
- `BackwardFirstChainTransform.leftToRightChainTransform_seriesFold`
- `BackwardFirstChainTransform.seriesFold_map_toBehavior_eq_fold_toBehavior`
- `ChainableTwoPortScattering`, including fields `scattering` and
  `hasBijectiveRightToLeftTransmission`
- `ChainableTwoPortScattering.behavior`
- `ChainableTwoPortScattering.chainTransform`
- `ChainableTwoPortScattering.toBehavior_chainTransform`
- `ChainableTwoPortScattering.behaviorFold`
- `ChainableTwoPortScattering.chainFold`
- `ChainableTwoPortScattering.behaviorFold_eq_chainFold_toBehavior`
- `ChainableTwoPortScattering.behaviorFold_hasLeftToRightChainView`
- `ChainableTwoPortScattering.leftToRightChainTransform_behaviorFold`

### `Physlib/Optics/Network/TwoPortChainFoldRegression.lean`

- `twoPortChainFoldRegressionList`
- `twoPortChainFoldRegression_fold_entry`
- `twoPortChainFoldRegression_reverse_entry`
- `twoPortChainFoldRegression_ne_reverse`

### `Physlib/Optics/Systems/Cascade/Heterogeneous.lean`

- `MicroringCascade.DateCascadeStage`, including fields `ring` and `busLength`
- `MicroringCascade.DateCascadeStage.busPhase`
- `MicroringCascade.DateCascadeStage.backwardContinuityFactor`
- `MicroringCascade.DateCascadeStage.forwardContinuityFactor`
- `MicroringCascade.DateCascadeStage.continuityChainMatrix`
- `MicroringCascade.DateCascadeStage.behavior`
- `MicroringCascade.DateCascadeStage.compositionMatrix`
- `MicroringCascade.DateCascadeStage.HasBijectiveRingTransmission`
- `MicroringCascade.DateCascadeStage.hasBijectiveRingTransmission_iff_forwardTransfer_ne_zero`
- `MicroringCascade.DateCascadeStage.behavior_eq_compositionMatrix_toBehavior`
- `MicroringCascade.dateCascadeBehavior`
- `MicroringCascade.dateCascadeComposition`
- `MicroringCascade.dateCascadeBehavior_eq_composition_toBehavior`
- `MicroringCascade.dateCascadeBehavior_hasLeftToRightChainView`
- `MicroringCascade.dateCascade_leftToRightChainTransform_eq_composition`

### `Physlib/Optics/Systems/Cascade/HeterogeneousRegression.lean`

- `MicroringCascade.dateCascadeRegressionHandProduct`
- `MicroringCascade.dateCascadeRegression_twoRing_inl_inl`
- `MicroringCascade.dateCascadeRegression_twoRing_inl_inr`
- `MicroringCascade.dateCascadeRegression_twoRing_inr_inl`
- `MicroringCascade.dateCascadeRegression_twoRing_inr_inr`
- `MicroringCascade.dateCascadeRegressionQuarterTurnRing`
- `MicroringCascade.dateCascadeRegressionQuarterTurnStage`
- `MicroringCascade.dateCascadeRegressionZeroBusStage`
- `MicroringCascade.dateCascadeRegression_quarterTurn_busPhase`
- `MicroringCascade.dateCascadeRegression_quarterTurn_signedContinuity`
- `MicroringCascade.dateCascadeRegression_quarterTurnRing_fieldAttenuation`
- `MicroringCascade.dateCascadeRegression_quarterTurnRing_phaseFactor`
- `MicroringCascade.dateCascadeRegression_quarterTurnRing_denominator`
- `MicroringCascade.dateCascadeRegression_quarterTurnRing_forwardTransfer`
- `MicroringCascade.dateCascadeRegression_quarterTurnRing_backwardTransfer`
- `MicroringCascade.dateCascadeRegression_zeroBus_backwardContinuity`
- `MicroringCascade.dateCascadeRegression_quarterTurn_then_zero_inl_inl`

## Scope and milestone disposition

This slice discharges the quoted S7C bullet "arbitrary heterogeneous microring cascades"
(`goal.md:2411`). It satisfies H-03, quoted as "arbitrary cascade behavior equals the folded chain
matrix" (`goal.md:2579`), through
`MicroringCascade.dateCascadeBehavior_eq_composition_toBehavior`. Its exact domain is

```text
∀ stage ∈ stages, stage.HasBijectiveRingTransmission
```

and `DateCascadeStage.hasBijectiveRingTransmission_iff_forwardTransfer_ne_zero` identifies that
gate exactly with `dateForwardTransfer stage.ring ≠ 0`.

This also discharges IP-15 under that gate: DATE Def. 6's opposite-sign continuity matrix and
Thm. 3's heterogeneous product are represented by `DateCascadeStage.continuityChainMatrix` and
`dateCascadeBehavior_eq_composition_toBehavior`. The independent H-03 fixture is the four-entry
hand product in `HeterogeneousRegression.lean`; it does not use the headline theorem or the
generic fold agreement theorem. The quarter-turn sentinel independently expands the carrier
exponential and pins the DATE continuity signs to `I` backward and `-I` forward. The consuming
two-stage entry is `I`, so swapping the factors or dropping the backward negation breaks it.
Both hostile mutations were checked mechanically. Dropping the negation left `-I = I`; swapping
the factors additionally left `I = -I`. The production file was restored before the clean build.

The neutral `BackwardFirstChainTransform.fold_replicate` supplies the generic matrix-power half
needed later for H-04, quoted as "an identical-`N` cascade equals the corresponding matrix power"
(`goal.md:2580`). It does not by itself discharge H-04/IP-16. This slice does not claim H-05,
H-06, or S-08. Their quoted rows are:

- "the Sylvester/Chebyshev cascade form holds with its determinant and trace-domain assumptions"
  (`goal.md:2581`);
- "terminated-cascade reflection and transmission agree with relational termination"
  (`goal.md:2582`); and
- "Physlib extension: the `M × N` lattice flattening agrees with its row/column decomposition"
  (`goal.md:2593`).

The remaining S7C bullets are likewise withheld: "a Sylvester/Chebyshev closed form with its
actual determinant and trace-domain assumptions", "terminated reflection and transmission",
"the source-backed uncoupled row-sublattice result", "coupled row/column decompositions and the
full `M × N` lattice theorem, explicitly classified as Physlib-original rather than DATE'14
parity", and the source-mapped SFG/PANDA cases (`goal.md:2413-2418`).

## Validation bindings

The validation lane should bind these exact public names:

- `Optics.BackwardFirstChainTransform.fold`
- `Optics.BackwardFirstChainTransform.fold_replicate`
- `Optics.BackwardFirstChainTransform.leftToRightChainTransform_seriesFold`
- `Optics.BackwardFirstChainTransform.seriesFold_map_toBehavior_eq_fold_toBehavior`
- `Optics.ChainableTwoPortScattering.behaviorFold_eq_chainFold_toBehavior`
- `Optics.twoPortChainFoldRegression_fold_entry`
- `Optics.twoPortChainFoldRegression_reverse_entry`
- `Optics.twoPortChainFoldRegression_ne_reverse`
- `Optics.MicroringCascade.DateCascadeStage.continuityChainMatrix`
- `Optics.MicroringCascade.DateCascadeStage.`
  `hasBijectiveRingTransmission_iff_forwardTransfer_ne_zero`
- `Optics.MicroringCascade.dateCascadeComposition`
- `Optics.MicroringCascade.dateCascadeBehavior_eq_composition_toBehavior`
- `Optics.MicroringCascade.dateCascade_leftToRightChainTransform_eq_composition`
- `Optics.MicroringCascade.dateCascadeRegression_twoRing_inl_inl`
- `Optics.MicroringCascade.dateCascadeRegression_twoRing_inl_inr`
- `Optics.MicroringCascade.dateCascadeRegression_twoRing_inr_inl`
- `Optics.MicroringCascade.dateCascadeRegression_twoRing_inr_inr`
- `Optics.MicroringCascade.dateCascadeRegression_quarterTurn_busPhase`
- `Optics.MicroringCascade.dateCascadeRegression_quarterTurn_signedContinuity`
- `Optics.MicroringCascade.dateCascadeRegression_quarterTurn_then_zero_inl_inl`

The asymmetric neutral fixture has exact leading entries `1` and `7`, so reversal is detectable.

## Reused anchors and conventions

- DATE Defs. 4-7 and Thm. 3 are recorded at
  `/Users/aadarwal/src/aadarwal/physlib-parity/HOL-CORPUS.md:199-203`; the source has
  `a_(n+1) = b_n exp(-j phi)` and `c_(n+1) = d_n exp(+j phi)`.
- The source-backed scope limit is at `HOL-CORPUS.md:210-216`: only the uncoupled row sublattice
  is verified; no DATE `M × N` theorem exists.
- `BackwardFirstTwoPortBehavior.leftToRightChainTransform_series` fixes later-on-the-left order at
  `Physlib/Optics/Network/TwoPortChain.lean:149-157`.
- The scattering pivot and graph extraction APIs are at
  `Physlib/Optics/Network/TwoPortScatteringChain.lean:149-175,523-539`.
- DATE's source four-port scattering and exact nonzero pivot gate are at
  `Physlib/Optics/Systems/Microring/SourceBridgeDate.lean:861-866,909-926`.
- The typed DATE backward-first matrix and chain bridge are at
  `Physlib/Optics/Systems/Microring/SourceBridgeDate.lean:1024-1051`.
- `MatchedPropagation.carrierPhaseFactor` is `exp (-I * phase)` at
  `Physlib/Optics/Components/MatchedPropagation.lean:93-99`. Consequently DATE's backward
  coordinate uses argument `-phi`, while its forward coordinate uses `phi`.
- The modal-to-electromagnetic power bridge and all its qualifications are at
  `Physlib/Optics/HarmonicFlux/PropagatingModePower.lean:15-23,60-90`.

## Non-claims

- The neutral fold makes no ring, propagation, source-parity, termination, passivity,
  reciprocity, causality, or electromagnetic claim.
- No quadruple-ring parity row is claimed.
- No coupled lattice, full `M × N` lattice, termination, Sylvester/Chebyshev, resonance, or
  SFG-TR'14/NSV'16 comparison is claimed in this slice.
- Effective index is fixed at the selected carrier. There is no dispersion, bending-loss,
  bandwidth, causality, or material-realization claim.
- Power remains normalized modal power. Electromagnetic power requires the finite,
  common-frequency, Maxwell-qualified, pairwise-integrable, mutually flux-orthogonal,
  unit-normalized measured-profile hypotheses of the cited bridge.
- DATE matrices and quotients are totalized algebraic expressions. Relational chain meaning is
  asserted only under every stage's exact bijective-transmission gate. No denominator nonzero,
  passivity, reciprocity, losslessness, or N5 well-posedness condition is silently inferred.
- Any later SFG-TR'14/NSV'16 comparison must retain IP-12's explicit principal-root versus
  selected-half-arc branch equality; this slice makes no such comparison.

## Gate record

The exact post-sync source head gated for slice 1b is
`9ec827ae903c57c845e2d93c4837595502e03b56`. It contains the merge of the required
`aff2484e` target and every Lean change in this cutoff. With the four modules temporarily
registered in sorted order, this single locked command exited successfully:

```text
lake-lock env bash -c 'set -euo pipefail && lake exe cache get &&
  lake --wfail build Physlib.Optics.Network.TwoPortChainFold
    Physlib.Optics.Network.TwoPortChainFoldRegression
    Physlib.Optics.Systems.Cascade.Heterogeneous
    Physlib.Optics.Systems.Cascade.HeterogeneousRegression &&
  lake exe runPhyslibLinters && lake exe lint_all'
```

- Cache retrieval downloaded no files.
- All four modules built with warnings as errors; Lake completed 2756 jobs successfully.
- `runPhyslibLinters` passed for `Physlib` and `QuantumInfo`.
- `lint_all` exited zero. Its build, illegal-import, PhyslibAlpha-import, duplicate-tag,
  sorry/pseudo, and second declaration-linter stages passed.
- The file-import inventory named only five unregistered files already present in sync target
  `aff2484e`: `IntegralMacroscopicMaxwell`, `PlanarThinCell` in Electromagnetism,
  `PlanarThinCell`, `PlanarThinCellConvergence`, and `ThinCellLimit` in SpaceAndTime. It named no
  S7C file because all four S7C modules were registered for the gate.
- Advisory style and transitive-import inventories named only pre-existing repository files and
  no S7C file.
- The committed-state `./scripts/lint-style.sh` check passed at the exact source head.
- The temporary registry edit was restored byte-identically. Pre-edit and post-edit SHA-256 were
  both `9b7092d5e30e9c9c618e07892d20d2f45535c4d259f5280946bad68234aba787`.

The final cutoff-record commit changes only this handoff; no Lean source differs from the exact
gated source head above.
