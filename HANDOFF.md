# S7C slice 1 handoff

## Cutoff

- Branch: `optics/s7c-cascade`
- Required sync target used: `12b4200d72b181f215e9d6d889a5feab5cb65a82`
- Slice: heterogeneous DATE cascade (IP-15 / H-03) plus the authorized neutral N3T fold

## Files and registrations

Register these four new modules in sorted order in `Physlib.lean`:

- `Physlib.Optics.Network.TwoPortChainFold`
- `Physlib.Optics.Network.TwoPortChainFoldRegression`
- `Physlib.Optics.Systems.Cascade.Heterogeneous`
- `Physlib.Optics.Systems.Cascade.HeterogeneousRegression`

The shipped registry linters were run with those imports added temporarily. The temporary
`Physlib.lean` edit was removed byte-identically before commit.

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
generic fold agreement theorem.

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
- `Optics.MicroringCascade.DateCascadeStage.hasBijectiveRingTransmission_iff_forwardTransfer_ne_zero`
- `Optics.MicroringCascade.dateCascadeComposition`
- `Optics.MicroringCascade.dateCascadeBehavior_eq_composition_toBehavior`
- `Optics.MicroringCascade.dateCascade_leftToRightChainTransform_eq_composition`
- `Optics.MicroringCascade.dateCascadeRegression_twoRing_inl_inl`
- `Optics.MicroringCascade.dateCascadeRegression_twoRing_inl_inr`
- `Optics.MicroringCascade.dateCascadeRegression_twoRing_inr_inl`
- `Optics.MicroringCascade.dateCascadeRegression_twoRing_inr_inr`

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

## Gate

With the four modules temporarily registered, one `lake-lock` hold ran cache retrieval, both
regression builds, `runPhyslibLinters`, and full `lint_all` on sync head `12b4200d`.

- Cache retrieval downloaded nothing.
- Both regression targets built successfully.
- `runPhyslibLinters` passed for `Physlib` and `QuantumInfo` twice.
- Full build, import registration, illegal-import, PhyslibAlpha-import, duplicate-tag, and
  sorry/pseudo checks passed.
- `lint_all` reproduced only the existing whole-repository style and transitive-import backlog;
  no finding named a file in this slice.
- Direct `scripts/lint-style.py` checking of all four new files passed before and after commit.
- The required committed-state `scripts/lint-style.sh` check reproduced two unrelated baseline
  `ERR_IND` findings at
  `Physlib/Electromagnetism/ThreeDimension/BoundaryConditions/OneSidedTraceRegression.lean:176`
  and `:189`. This slice does not modify that file; no finding named a file in this slice.
