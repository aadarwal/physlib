# S7D slice 11 handoff: L8 field/intensity source boundaries

## Cutoff identity

- Branch: `optics/s7d-dcdr`.
- Exact sync target: `66df1929ccc0bb40098c1fd733675899e99c5052`.
- Exact sync merge: `53024e8f90979835d8fdc5d27c1370df76aef8b5`.
- Gated source: `9bfb7efa3096f38513a3edb6bbff7e0cce2f932e`.
- This file is the HANDOFF-only cutoff child.
- `Physlib.lean` is unchanged from the exact sync target. Its SHA-256 is
  `856a58e9bcc9d4d7a832cdb50cb05b867d75a0a16600a0f6f35280a1f8fc263c`.

The cache was refreshed from the `optics-development` worktree immediately after the exact sync
merge. The complete cutoff delta is the twelve existing Lean files below plus this HANDOFF-only
child. No module was added, removed, or newly registered.

## Goal and decision resolution

At this cutoff ref, `goal.md:2747-2748` says verbatim:

> - [ ] Confirm that every ring model distinguishes field from power attenuation and amplitude from
>   power coupling coefficients.

This slice implements option 1 of
`scratchpad/lanes/decisions/decision-L8.md`, “L8 – Ring attenuation and coupling roles.” It closes
the implementation side of L8 by making the two source-to-coherent DCDR maps use named square-root
field gains and by renaming DATE's stored `alpha` as a coefficient rather than a retention factor.
The goal checkbox remains for the conductor and the required human certification.

The four mandatory decision names are present exactly:

- `intensityGainToFieldAmplitudeGain` —
  `Physlib/Optics/Systems/DCDR/SourceBridge.lean:202`.
- `fieldAmplitudeGainToIntensityGain` —
  `Physlib/Optics/Systems/DCDR/SourceBridge.lean:206`.
- `SourceParameters.toCoherentUnitDelayParameters` —
  `Physlib/Optics/Systems/DCDR/SourceBridge.lean:253`.
- `MultipleDelaySourceParameters.toCoherentMultipleDelayParameters` —
  `Physlib/Optics/Systems/DCDR/MultipleDelaySource.lean:141`.

The old source-map names `SourceParameters.toUnitDelayParameters` and
`MultipleDelaySourceParameters.toMultipleDelayParameters` were removed without compatibility
aliases. `DateParameters.powerAttenuation` was renamed to
`DateParameters.powerAttenuationCoefficient` at
`Physlib/Optics/Systems/Microring/SourceBridgeDate.lean:75`. Searches for all three old qualified
names are clean. The similarly spelled `DCDR.UnitDelayParameters.toMultipleDelayParameters` is a
different coherent unit-exponent embedding and intentionally remains.

## Exact source file set

### Semantic DCDR changes

- `Physlib/Optics/Systems/DCDR/SourceBridge.lean`: declares the two role-bearing conversions,
  converts every coherent `G_i` field with `sqrt`, adds the three square-recovery results, and
  updates the named coherent loop coefficient. The entry declarations begin at lines 202, 253,
  311, and 329.
- `Physlib/Optics/Systems/DCDR/SourceBridgeRegression.lean`: adds the exact unit-delay gain-role
  fixture and the independent printed-polynomial noninterference anchor at lines 220-280; it also
  migrates the all-one divergence fixture to the corrected coherent map at lines 282-308.
- `Physlib/Optics/Systems/DCDR/MultipleDelaySource.lean`: transports the nonnegative-gain
  predicate, corrects the multiple-delay coherent map, adds all three square-recovery results,
  and preserves the unit-delay embedding bridge at lines 131-205.
- `Physlib/Optics/Systems/DCDR/MultipleDelayRegression.lean`: adds the distinct-delay gain-role
  and printed-polynomial anchors at lines 240-290.
- `Physlib/Optics/Systems/DCDR/PassiveCaseRegression.lean`: mechanically unfolds the corrected
  map in the already accepted passive exact-data anchors declared at lines 125, 178, and 206.

### DATE production changes

- `Physlib/Optics/Systems/Microring/SourceBridgeDate.lean`: renames the DATE source field at line
  75 and makes `DateParameters.fieldAttenuation` at line 89 consume that coefficient.
- `Physlib/Optics/Systems/Microring/PhysicalSourceBridge.lean`: propagates the coefficient into
  physical data through `DateParameters.toPhysicalPropagation` at line 109 and its validity bridge
  at line 145.

### Five mechanical constructor-propagation files

- `Physlib/Optics/Systems/Microring/SourceBridgeRegression.lean`:
  `sourceBridgeRegressionDateParameters` at line 66.
- `Physlib/Optics/Systems/Microring/PhysicalRegression.lean`:
  `physicalRegressionDateParameters` at line 477.
- `Physlib/Optics/Systems/Cascade/HeterogeneousRegression.lean`:
  `dateCascadeRegressionQuarterTurnRing` at line 169.
- `Physlib/Optics/Systems/Cascade/IdenticalRegression.lean`:
  `dateJoinedSylvesterRegressionRing` at line 229.
- `Physlib/Optics/Systems/Cascade/TerminationRegression.lean`:
  `dateTerminationRegressionRing` at line 63 and
  `dateTerminationRegressionSingularRing` at line 716.

These five files contain only the constructor field-name propagation. In particular,
`PhysicalRegression.lean` changes only the initializer at line 482; its pre-existing style-linter
indentation findings occur on other lines and are byte-identical to the sync target.

## Validation names with declaration lines

### Production conversion and unit-delay dictionary

- `intensityGainToFieldAmplitudeGain` —
  `Physlib/Optics/Systems/DCDR/SourceBridge.lean:202`.
- `fieldAmplitudeGainToIntensityGain` —
  `Physlib/Optics/Systems/DCDR/SourceBridge.lean:206`.
- `fieldAmplitudeGainToIntensityGain_intensityGainToFieldAmplitudeGain` —
  `Physlib/Optics/Systems/DCDR/SourceBridge.lean:210`.
- `intensityGainToFieldAmplitudeGain_fieldAmplitudeGainToIntensityGain` —
  `Physlib/Optics/Systems/DCDR/SourceBridge.lean:216`.
- `SourceParameters.HasNonnegativeGains` —
  `Physlib/Optics/Systems/DCDR/SourceBridge.lean:244`.
- `SourceParameters.toCoherentUnitDelayParameters` —
  `Physlib/Optics/Systems/DCDR/SourceBridge.lean:253`.
- `SourceParameters.toCoherentUnitDelayParameters_data` —
  `Physlib/Optics/Systems/DCDR/SourceBridge.lean:266`.
- `SourceParameters.toCoherentUnitDelayParameters_isAdmissible` —
  `Physlib/Optics/Systems/DCDR/SourceBridge.lean:282`.
- `SourceParameters.firstThroughAmplitude_sq` —
  `Physlib/Optics/Systems/DCDR/SourceBridge.lean:287`.
- `SourceParameters.firstCrossAmplitude_sq` —
  `Physlib/Optics/Systems/DCDR/SourceBridge.lean:293`.
- `SourceParameters.secondThroughAmplitude_sq` —
  `Physlib/Optics/Systems/DCDR/SourceBridge.lean:299`.
- `SourceParameters.secondCrossAmplitude_sq` —
  `Physlib/Optics/Systems/DCDR/SourceBridge.lean:305`.
- `SourceParameters.toCoherentUnitDelayParameters_upperGain_intensity` —
  `Physlib/Optics/Systems/DCDR/SourceBridge.lean:311`.
- `SourceParameters.toCoherentUnitDelayParameters_lowerGain_intensity` —
  `Physlib/Optics/Systems/DCDR/SourceBridge.lean:317`.
- `SourceParameters.toCoherentUnitDelayParameters_feedbackGain_intensity` —
  `Physlib/Optics/Systems/DCDR/SourceBridge.lean:323`.
- `SourceParameters.coherentLoopCoefficient` —
  `Physlib/Optics/Systems/DCDR/SourceBridge.lean:329`.
- `SourceParameters.toCoherentUnitDelayParameters_loopCoefficient` —
  `Physlib/Optics/Systems/DCDR/SourceBridge.lean:342`.
- `SourceParameters.toCoherentUnitDelayParameters_denominatorPolynomial` —
  `Physlib/Optics/Systems/DCDR/SourceBridge.lean:348`.
- `passiveCaseUnitDelayParameters` —
  `Physlib/Optics/Systems/DCDR/SourceBridge.lean:451`.

### Production multiple-delay dictionary

- `MultipleDelaySourceParameters.HasNonnegativeGains` —
  `Physlib/Optics/Systems/DCDR/MultipleDelaySource.lean:131`.
- `MultipleDelaySourceParameters.toCoherentMultipleDelayParameters` —
  `Physlib/Optics/Systems/DCDR/MultipleDelaySource.lean:141`.
- `MultipleDelaySourceParameters.toCoherentMultipleDelayParameters_data` —
  `Physlib/Optics/Systems/DCDR/MultipleDelaySource.lean:157`.
- `MultipleDelaySourceParameters.toCoherentMultipleDelayParameters_upperGain_sq` —
  `Physlib/Optics/Systems/DCDR/MultipleDelaySource.lean:178`.
- `MultipleDelaySourceParameters.toCoherentMultipleDelayParameters_lowerGain_sq` —
  `Physlib/Optics/Systems/DCDR/MultipleDelaySource.lean:186`.
- `MultipleDelaySourceParameters.toCoherentMultipleDelayParameters_feedbackGain_sq` —
  `Physlib/Optics/Systems/DCDR/MultipleDelaySource.lean:194`.
- `SourceParameters.toMultipleDelaySourceParameters_coherent` —
  `Physlib/Optics/Systems/DCDR/MultipleDelaySource.lean:202`.

### Exact independent DCDR regressions

- `sourceGainConversionParameters` —
  `Physlib/Optics/Systems/DCDR/SourceBridgeRegression.lean:220`.
- `sourceGainConversion_hasNonnegativeGains` —
  `Physlib/Optics/Systems/DCDR/SourceBridgeRegression.lean:228`.
- `sourceGainConversion_coherentGains` —
  `Physlib/Optics/Systems/DCDR/SourceBridgeRegression.lean:234`.
- `sourceGainConversion_squaredGains` —
  `Physlib/Optics/Systems/DCDR/SourceBridgeRegression.lean:249`.
- `sourceGainConversion_printedPolynomials` —
  `Physlib/Optics/Systems/DCDR/SourceBridgeRegression.lean:268`.
- `sourceDictionaryDivergenceParameters` —
  `Physlib/Optics/Systems/DCDR/SourceBridgeRegression.lean:282`.
- `sourceDictionaryDivergence_printedLoopCoefficient` —
  `Physlib/Optics/Systems/DCDR/SourceBridgeRegression.lean:290`.
- `sourceDictionaryDivergence_coherentLoopCoefficient` —
  `Physlib/Optics/Systems/DCDR/SourceBridgeRegression.lean:296`.
- `sourceDictionaryDivergence_loopCoefficients_ne` —
  `Physlib/Optics/Systems/DCDR/SourceBridgeRegression.lean:304`.
- `multipleDelayGainConversionParameters` —
  `Physlib/Optics/Systems/DCDR/MultipleDelayRegression.lean:240`.
- `multipleDelayGainConversion_hasNonnegativeGains` —
  `Physlib/Optics/Systems/DCDR/MultipleDelayRegression.lean:251`.
- `multipleDelayGainConversion_coherentGains` —
  `Physlib/Optics/Systems/DCDR/MultipleDelayRegression.lean:258`.
- `multipleDelayGainConversion_printedPolynomials` —
  `Physlib/Optics/Systems/DCDR/MultipleDelayRegression.lean:278`.
- `passiveCaseUnitDelayParameters_data` —
  `Physlib/Optics/Systems/DCDR/PassiveCaseRegression.lean:125`.
- `passiveCase_coherentLoopCoefficient` —
  `Physlib/Optics/Systems/DCDR/PassiveCaseRegression.lean:178`.
- `passiveCase_coherentNumeratorPolynomial_expansion` —
  `Physlib/Optics/Systems/DCDR/PassiveCaseRegression.lean:206`.

### DATE production and constructor sentinels

- `DateParameters.powerAttenuationCoefficient` —
  `Physlib/Optics/Systems/Microring/SourceBridgeDate.lean:75`.
- `DateParameters.fieldAttenuation` —
  `Physlib/Optics/Systems/Microring/SourceBridgeDate.lean:89`.
- `DateParameters.toPhysicalPropagation` —
  `Physlib/Optics/Systems/Microring/PhysicalSourceBridge.lean:109`.
- `DateParameters.toPhysicalPropagation_fieldAttenuation` —
  `Physlib/Optics/Systems/Microring/PhysicalSourceBridge.lean:124`.
- `DateParameters.toPhysicalAddDrop_isValid` —
  `Physlib/Optics/Systems/Microring/PhysicalSourceBridge.lean:145`.
- `sourceBridgeRegressionDateParameters` —
  `Physlib/Optics/Systems/Microring/SourceBridgeRegression.lean:66`.
- `sourceBridgeRegression_date_fieldAttenuation` —
  `Physlib/Optics/Systems/Microring/SourceBridgeRegression.lean:86`.
- `physicalRegressionDateParameters` —
  `Physlib/Optics/Systems/Microring/PhysicalRegression.lean:477`.
- `physicalRegression_date_toPhysicalAddDrop` —
  `Physlib/Optics/Systems/Microring/PhysicalRegression.lean:486`.
- `physicalRegression_date_fieldAttenuation` —
  `Physlib/Optics/Systems/Microring/PhysicalRegression.lean:490`.
- `dateCascadeRegressionQuarterTurnRing` —
  `Physlib/Optics/Systems/Cascade/HeterogeneousRegression.lean:169`.
- `dateCascadeRegression_quarterTurnRing_fieldAttenuation` —
  `Physlib/Optics/Systems/Cascade/HeterogeneousRegression.lean:211`.
- `dateJoinedSylvesterRegressionRing` —
  `Physlib/Optics/Systems/Cascade/IdenticalRegression.lean:229`.
- `dateJoinedSylvesterRegressionRing_fieldAttenuation` —
  `Physlib/Optics/Systems/Cascade/IdenticalRegression.lean:250`.
- `dateTerminationRegressionRing` —
  `Physlib/Optics/Systems/Cascade/TerminationRegression.lean:63`.
- `dateTerminationRegressionRing_fieldAttenuation` —
  `Physlib/Optics/Systems/Cascade/TerminationRegression.lean:83`.
- `dateTerminationRegressionSingularRing` —
  `Physlib/Optics/Systems/Cascade/TerminationRegression.lean:716`.

## Exact conversion and noninterference audit

For both source dictionaries, the printed `G1`, `G2`, and `G3` fields remain real intensity gains.
The corrected coherent maps store

```text
(sqrt G1, sqrt G2, sqrt G3)
```

as field-amplitude gains. The inverse results are deliberately gated by nonnegativity. The unit
map's target is algebraically admissible because every real square root is nonnegative; the
source-intensity interpretation and square recovery still require
`SourceParameters.HasNonnegativeGains`. The multiple-delay predicate transports that same source
domain while preserving all three exponents.

The independent exact source fixture is

```text
(G1, G2, G3, k1, k2) = (1/4, 1/9, 4/25, 1, 1).
```

Primitive square-root expansion gives coherent field gains `(1/2, 1/3, 2/5)`, and primitive
squaring recovers `(1/4, 1/9, 4/25)`. The unit-delay printed polynomials independently expand to

```text
numerator   = C (1/9) * X - C (1/225) * X^3
denominator = 1 - C (1/25) * X^2.
```

The multiple-delay fixture uses `(m1, m2, m3) = (2, 3, 4)`. It has the same coherent field gains,
while its independently expanded printed polynomials are

```text
numerator   = C (1/9) * X^3 - C (1/225) * X^9
denominator = 1 - C (1/25) * X^6.
```

These anchors unfold conversion and polynomial primitives; they do not route through the recovery
lemmas under test. A direct-`G_i` coherent map, a `sqrt G_i` substitution into the printed formulas,
or a wrong delay breaks an exact value.

The literal production definitions were not changed:

- `SourceParameters.printedNumeratorPolynomial` —
  `Physlib/Optics/Systems/DCDR/SourceBridge.lean:375`.
- `SourceParameters.printedDenominatorPolynomial` —
  `Physlib/Optics/Systems/DCDR/SourceBridge.lean:381`.
- `MultipleDelaySourceParameters.printedNumeratorPolynomial` —
  `Physlib/Optics/Systems/DCDR/MultipleDelaySource.lean:234`.
- `MultipleDelaySourceParameters.printedDenominatorPolynomial` —
  `Physlib/Optics/Systems/DCDR/MultipleDelaySource.lean:241`.

The existing all-one divergence tooth remains fail-capable: the literal printed loop coefficient
is `1`, while direct coherent N7 amplitude expansion gives `-1`. This is a model-separation
sentinel, not a coherent/incoherent equivalence.

DATE's stored `alpha` is now named `powerAttenuationCoefficient`; the field factor remains exactly
`exp (-alpha * couplingLength / 2)`. Existing 3-4-5, physical, cascade, and termination fixtures
retain their old exact values after the mechanical constructor migration.

## Registration and registry request

All twelve Lean files were already registered at the exact sync target. No import is requested,
and `Physlib.lean` must remain untouched.

Per `decision-L8.md`, the controller/conductor should extend registry entry Z-01 and the mandatory
name list, if that bookkeeping is maintained outside this lane, with:

```text
intensityGainToFieldAmplitudeGain
fieldAmplitudeGainToIntensityGain
SourceParameters.toCoherentUnitDelayParameters
MultipleDelaySourceParameters.toCoherentMultipleDelayParameters
```

This lane intentionally did not edit an API map, registry, parity ledger, validation ledger, or
`goal.md`.

## Gate record

All Lean invocations ran through the machine-wide `lake-lock`, and the source was committed before
long waits.

- The exact sync target `66df1929` was merged, not rebased or substituted.
- The cache was refreshed from the battery-green `optics-development` worktree.
- The final targeted warnings-as-errors build passed: 2,832 jobs.
- The root warnings-as-errors `Physlib` build then passed: 5,016 jobs.
- In hardened post-root order, `check_file_imports`, `sorry_lint`, and
  `runPhyslibLinters` passed; the latter passed for both Physlib and QuantumInfo.
- `api_map_index` and `lint_all` exited zero. `lint_all` continues to print repository-baseline
  advisory style and transitive-import findings. Its only touched-file style output is the
  pre-existing indentation backlog in `Microring/PhysicalRegression.lean`, outside its one-line
  initializer rename.
- The repository-wide `module_doc_lint` still exits one on its known global documentation backlog.
  Filtering its exact-source output for all twelve touched modules returns no findings.
- `scripts/lint-style.sh` passes on the exact gated source.
- `git diff --check` passes. Added Lean lines contain zero `sorry`, `axiom`, `native_decide`, or
  `maxHeartbeats`, and add zero `theorem` declarations.
- Every touched Lean file is below 1,500 lines. Maxima are 98-100 Unicode codepoints; the largest
  file is `Microring/SourceBridgeDate.lean` at 1,125 lines.
- `Physlib.lean` was never temporarily edited and remains byte-identical to the sync target.

## Claims, non-claims, and human certification

This slice proves a role-safe source-boundary interpretation: nonnegative printed intensity gains
map canonically to coherent field-amplitude square roots, and squaring recovers the source data.
It also removes the DATE coefficient/factor name collision while preserving the existing field
attenuation formula.

It does not claim that FMICS'15's printed incoherent coefficient model equals the coherent N7 DCDR,
and it does not alter the literal source polynomials. It makes no claim of physical resonance,
power flux, electromagnetic energy, reciprocity, physical time reversal, physical reference
planes, causality or Maxwell time-domain meaning, physical-frequency meaning, BIBO stability, or
HOL-script semantics.

Per `AI-POLICY.md`, a human author must independently certify the source-role readings, the
square-root boundary, the exact fixture values, and the DATE coefficient interpretation before
upstreaming. A green build proves formal consistency, not that the code matches the human author's
intended physics.
