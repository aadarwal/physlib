# S2/S3 microring source-bridge handoff

## Branch and cutoff scope

- Branch: `optics/s2-microring`
- Integration base at this draft: `optics/development` at `33ee2ab7`
- New umbrella production module:
  `Physlib/Optics/Systems/Microring/SourceBridge.lean`
- New per-source production modules:
  `Physlib/Optics/Systems/Microring/SourceBridgeDate.lean`,
  `Physlib/Optics/Systems/Microring/SourceBridgeSysCon.lean`, and
  `Physlib/Optics/Systems/Microring/SourceBridgeSfg.lean`.
- New regression module:
  `Physlib/Optics/Systems/Microring/SourceBridgeRegression.lean`
- No existing Microring module was edited in this slice.
- The per-source split preserves every declaration name and statement from cutoff `64646116`.
  It addresses the 1500-line style-lint limit and is not a review finding.
- `Physlib.lean`, `Physlib/Optics/API-map.yaml`, `goal.md`, and `tbd.md` were not edited by this
  branch. Changes to those files visible in the worktree came from the required development merge.

## Registrations requested from the conductor

Add these sorted public imports to `Physlib.lean`:

```lean
public import Physlib.Optics.Systems.Microring.SourceBridge
public import Physlib.Optics.Systems.Microring.SourceBridgeRegression
```

The umbrella publicly re-exports the three per-source modules. Register it and the regression as
the DATE'14, SysCon'15, and SFG-TR'14 source-parameter, port-order, algebraic channel-sign,
amplitude, power, rejection-ratio, and regression bridge for the proved add-drop microring
realization.

## N7 and network declarations used

The bridge uses the following registered N7 contract, directly or through the S2 add-drop
realization. These line references were re-grepped after the development sync:

- `Optics.DirectionalCoupler.Parameters`:
  `Physlib/Optics/Components/DirectionalCoupler.lean:62`.
- `Optics.DirectionalCoupler.crossCoefficient` and its pinned `-I*k` convention:
  `Physlib/Optics/Components/DirectionalCoupler.lean:68-70`.
- `Optics.DirectionalCoupler.Parameters.IsPowerBounded`, `.IsUnitary`, and `.IsValid`:
  `Physlib/Optics/Components/DirectionalCouplerPower.lean:59`, `:63`, and `:67`.
- `Optics.DirectionalCoupler.physicalBehavior` and `.physicalScattering`:
  `Physlib/Optics/Components/DirectionalCouplerPhysical.lean:145` and `:161`.
- `Optics.DirectionalCoupler.physicalBehavior_output_power`,
  `.physicalScattering_isPassive`, and `.physicalScattering_isLossless`:
  `Physlib/Optics/Components/DirectionalCouplerPhysicalPower.lean:51`, `:63`, and `:72`.
- `Optics.MatchedPropagation.Parameters` and `.Parameters.IsValid`:
  `Physlib/Optics/Components/MatchedPropagation.lean:79` and `:90`.
- `Optics.MatchedPropagation.physicalBehavior` and `.physicalScattering`:
  `Physlib/Optics/Components/MatchedPropagationPhysical.lean:151` and `:167`.
- `Optics.MatchedPropagation.physicalBehavior_output_power`,
  `.physicalScattering_isPassive`, and `.physicalScattering_isLossless`:
  `Physlib/Optics/Components/MatchedPropagationPhysicalPower.lean:59`, `:76`, and `:86`.

The proof-gated network response is N5's `Optics.FlatNetlist.responseTransform`
(`Physlib/Optics/Network/FlatNetlistElimination.lean:443`), with its exact block agreement at
`:467`. The source bridges bind the already derived S2 response entries
`Optics.AddDrop.responseTransform_entry_through_input` and
`Optics.AddDrop.responseTransform_entry_drop_input`
(`Physlib/Optics/Systems/Microring/AddDrop.lean:711` and `:720`). The four-port add excitation is
also solved directly from `FlatNetlist.mem_behavior_iff_equations`, whose definition is at
`Physlib/Optics/Network/FlatNetlist.lean:487`.

This slice proves no new conservation statement. The existing S3 lossless balance remains routed
only through
`Optics.FlatNetlist.externalScatteringMatrix_isLossless_of_components_isLossless`
(`Physlib/Optics/Network/Conservation.lean:544`), as required; no response matrix is checked for
unitarity by hand here.

## Public declaration inventory

### DATE'14 parameter, coupler-chain, and field dictionary

- `Optics.MicroringSourceBridge.DateParameters`
- `DateParameters.roundTripPhase`, `.fieldAttenuation`, `.phaseFactor`, `.halfPhaseFactor`
- `DateParameters.coupler`, `.IsUnitary`, `.couplerScatteringMatrix`, `.couplerScattering`
- `DateParameters.couplerScattering_leftReflection`
- `DateParameters.couplerScattering_rightToLeftTransmission`
- `DateParameters.couplerScattering_leftToRightTransmission`
- `DateParameters.couplerScattering_rightReflection`
- `sourceScalarAmplitude`
- `DateParameters.couplerScattering_rightToLeftTransmission_action`
- `DateParameters.couplerScattering_hasBijectiveRightToLeftTransmission`
- `DateParameters.couplerTransmissionInverse`
- `DateParameters.couplerTransmission_mul_explicitInverse`
- `DateParameters.couplerTransmissionInverse_eq`
- `dateN7CouplerChainMatrix`, `dateN7CouplerChainTransform_eq`
- `dateChainGauge`, `dateTwoPortChainMatrix`
- `DateTwoPortFields`, `dateTwoPortBehavior`
- `dateTwoPortInputVector`, `dateTwoPortOutputVector`, `dateTwoPortBehavior_iff_matrix`
- `dateTwoPortChainMatrix_eq_gauged_explicitN7`
- `dateTwoPortChainMatrix_eq_gauged_n7Chain`
- `DateParameters.toAddDrop`
- `DateParameters.toAddDrop_dropCoupler_eq_inputCoupler`
- `DateParameters.toAddDrop_secondArcCoefficient_eq_firstArcCoefficient`
- `DateParameters.toAddDrop_data`, `.fieldAttenuation_pos`
- `DateParameters.inputCoupler_isUnitary`, `.dropCoupler_isUnitary`
- `dateThroughGauge`, `dateAddGauge`, `dateIdentityGauge`
- `DateParameters.denominator`, `.HasNonzeroDenominator`
- `dateForwardTransfer`, `dateBackwardTransfer`
- `DateParameters.toAddDrop_roundTripCoefficient`
- `DateParameters.toAddDrop_firstArcCoefficient`
- `DateParameters.toAddDrop_denominator`
- `DateParameters.hasNonzeroDenominator_iff`
- `dateForwardTransfer_eq_gauged_throughTransfer`
- `dateBackwardTransfer_eq_dropTransfer`
- `dateForwardTransfer_eq_n5Response`, `dateBackwardTransfer_eq_n5Response`

### DATE'14 four-port behavior and genuine N5 port-order bridge

- `DateFourPortFields`, `dateFourPortBehavior`
- `dateFourPortChainMatrix`, `dateFourPortInputVector`, `dateFourPortOutputVector`
- `dateFourPortBehavior_iff_matrix`
- `dateAddAmplitude`, `dateAddAmplitude_apply_input`, `dateAddAmplitude_apply_add`
- `dateAdd_inputCoupler_leftSecond_solution`
- `dateResponse_through_add`, `dateAdd_dropCoupler_rightFirst_solution`
- `dateResponse_drop_add`
- `dateResponseTransform_entry_through_add`, `dateResponseTransform_entry_drop_add`
- `dateN5FourPortScattering`, `dateSourceFourPortScattering`
- `dateN5FourPortScattering_eq_source`
- `dateSourceFourPortScattering_rightToLeftTransmission_action`
- `dateSourceFourPortScattering_hasBijectiveRightToLeftTransmission`
- `dateN5FourPortScattering_hasBijectiveRightToLeftTransmission`
- `dateFourPortTransmissionInverse`
- `dateFourPortTransmission_mul_explicitInverse`
- `dateFourPortTransmissionInverse_eq`
- `dateBackwardFirstFinEquiv`, `dateBackwardFirstFinEquiv_data`
- `dateFourPortBackwardFirstChainMatrix`
- `dateFourPortBackwardFirstChainMatrix_reindex`
- `dateSourceFourPortChainTransform_eq`
- `dateFourPortChainMatrix_eq_n5Response`
- `dateFourPortChainMatrix_eq_reindexed_n5Response`
- `dateFourPortBehavior_iff_n5Response`

### SysCon'15 amplitude, series, derived power, and rejection ratio

- `SysConParameters`, `SysConParameters.toAddDrop`, `.toAddDrop_data`
- `SysConParameters.halfArcCoefficient`, `.realLoopGain`, `.loopGain`
- `SysConParameters.IsContractive`, `.IsContractive.norm_loopGain_lt_one`
- `SysConParameters.denominator`, `.HasNonzeroDenominator`
- `sysConDropTransfer`, `sysConDropResponseSeries`
- `sysConDropResponseSeries_summable`, `sysConDropResponseSeries_eq_transfer`
- `SysConParameters.toAddDrop_firstArcCoefficient`
- `SysConParameters.toAddDrop_roundTripCoefficient`
- `SysConParameters.toAddDrop_denominator`, `.toAddDrop_loopGain`
- `SysConParameters.IsContractive.toAddDrop`
- `SysConParameters.hasNonzeroDenominator_iff`
- `sysConDropTransfer_eq_dropTransfer`, `sysConDropTransfer_eq_n5Response`
- `sysConDropResponseSeries_eq_n5Response`
- `sysConDropPower`, `sysConDropPower_eq_n5ResponsePower`
- `sysConDropPower_eq_dropPower`, `sysConAnalyticDropPower`
- `sysConAmplitudePowerDenominator`
- `sysConDisputedPowerDenominator`, `sysConDisputedDropPower`
- `sysConAmplitudePowerDenominator_eq_cosineForm`
- `sysConDropPower_eq_analytic`
- `sysConDropPower_eq_amplitudePowerDenominator`
- `powerRatioInBase`, `powerRatioInBase_ten`, `powerRatioInBase_exp_one`
- `sysConRejectionClosedForm`
- `SysConParameters.atResonance`, `.atAntiresonance`
- `sysConRejectionRatioInBase`
- `sysConDropPower_atResonance`, `sysConDropPower_atAntiresonance`
- `sysConDropPower_atResonance_pos`, `sysConDropPower_atAntiresonance_pos`
- `sysCon_namedDropPower_ratio`
- `sysConRejectionRatioInBase_eq_closedForm`
- `sysConRejectionClosedForm_base_ten`
- `sysConRejectionRatioInBase_ten_eq_dropRejectionRatioDB`
- `sysConRejectionClosedForm_exp_one`
- `sysConRejectionRatioInBase_exp_one_eq_naturalLog`

### SFG-TR'14 dictionary

- `SfgParameters`, `SfgParameters.ofAddDrop`, `SfgParameters.ofAddDrop_data`
- `sfgAddDropTransfer`, `sfgCrossCoefficient`
- `sfgAddDropTransfer_eq_dropTransfer`, `sfgAddDropTransfer_eq_n5Response`

### Regression declarations

- `sourceBridgeRegressionDateParameters`, `sourceBridgeRegression_date_isUnitary`
- `sourceBridgeRegression_date_roundTripPhase`
- `sourceBridgeRegression_date_fieldAttenuation`
- `sourceBridgeRegression_dateTwoPortChain_entries`
- `sourceBridgeRegressionDateTwoPortFields`
- `sourceBridgeRegression_dateTwoPortBehavior`
- `sourceBridgeRegression_date_phaseFactor`
- `sourceBridgeRegression_date_halfPhaseFactor`
- `sourceBridgeRegression_date_denominator`
- `sourceBridgeRegression_dateFourPort_transfers`
- `sourceBridgeRegression_dateFourPortChain_entries`
- `sourceBridgeRegressionSysConParameters`
- `sourceBridgeRegression_sysCon_halfArcCoefficient`
- `sourceBridgeRegression_sysCon_loopGain`, `sourceBridgeRegression_sysCon_denominator`
- `sourceBridgeRegression_sysCon_resonance_transfer`
- `sourceBridgeRegression_sysCon_resonance_series`
- `sourceBridgeRegression_sysCon_resonance_power`
- `sourceBridgeRegressionSysConAntiresonance`
- `sourceBridgeRegression_sysCon_antiresonance_transfer`
- `sourceBridgeRegression_sysCon_antiresonance_power`
- `sourceBridgeRegression_sysCon_def11_resonance_power`
- `sourceBridgeRegression_sysCon_rejection_ratio`
- `sourceBridgeRegression_sysCon_rejection_closedForm`
- `sourceBridgeRegressionDisputedPowerParameters`
- `sourceBridgeRegression_amplitudePowerDenominator`
- `sourceBridgeRegression_disputedPowerDenominator`
- `sourceBridgeRegression_disputedDenominator_ne_amplitudeDenominator`
- `sourceBridgeRegressionSfgParameters`, `sourceBridgeRegression_sfg_transfer`

## Validation bindings by parity row

- IP-03: `dateTwoPortBehavior`, `dateTwoPortBehavior_iff_matrix`,
  `dateTwoPortChainMatrix`, `dateChainGauge`,
  `dateTwoPortChainMatrix_eq_gauged_n7Chain`,
  `sourceBridgeRegression_dateTwoPortChain_entries`,
  `sourceBridgeRegression_dateTwoPortBehavior`.
- IP-04: `dateFourPortBehavior`, `dateFourPortChainMatrix`,
  `dateN5FourPortScattering`, `dateN5FourPortScattering_eq_source`,
  `dateBackwardFirstFinEquiv`, `dateFourPortBackwardFirstChainMatrix_reindex`,
  `dateFourPortChainMatrix_eq_reindexed_n5Response`,
  `dateFourPortBehavior_iff_n5Response`,
  `sourceBridgeRegression_dateFourPort_transfers`,
  `sourceBridgeRegression_dateFourPortChain_entries`.
- IP-05: `SysConParameters.toAddDrop`, `sysConDropTransfer`,
  `sysConDropResponseSeries`, `sysConDropResponseSeries_eq_transfer`,
  `sysConDropTransfer_eq_dropTransfer`, `sysConDropTransfer_eq_n5Response`,
  `sysConDropResponseSeries_eq_n5Response`,
  `sourceBridgeRegression_sysCon_resonance_transfer`, and
  `sourceBridgeRegression_sysCon_resonance_series`.
- IP-06, amplitude-derived result only: `sysConDropPower`,
  `sysConDropPower_eq_n5ResponsePower`, `sysConAmplitudePowerDenominator`,
  `sysConDropPower_eq_amplitudePowerDenominator`,
  `sysConDisputedPowerDenominator`,
  `sourceBridgeRegression_disputedDenominator_ne_amplitudeDenominator`.
  Exact printed-Thm.-6 parity remains withheld.
- IP-07: `powerRatioInBase`, `sysConRejectionRatioInBase`,
  `sysConRejectionClosedForm`, `sysCon_namedDropPower_ratio`,
  `sysConRejectionRatioInBase_eq_closedForm`,
  `sysConRejectionRatioInBase_ten_eq_dropRejectionRatioDB`,
  `sysConRejectionRatioInBase_exp_one_eq_naturalLog`, and
  `sourceBridgeRegression_sysCon_rejection_ratio`.
- IP-12: `SfgParameters.ofAddDrop`, `sfgCrossCoefficient`, `sfgAddDropTransfer`,
  `sfgAddDropTransfer_eq_dropTransfer`, `sfgAddDropTransfer_eq_n5Response`, and
  `sourceBridgeRegression_sfg_transfer`.

All names above are in namespace `Optics.MicroringSourceBridge` unless qualified as a structure
method.

## Goal and parity rows

- `goal.md` H-01: independently represented DATE two- and four-port source behaviors/matrices.
- `goal.md` H-02: proof-gated scattering-to-chain conversions with exact pivot hypotheses.
- `goal.md` B-01: SysCon's geometric feedback series equals algebraic elimination only under the
  source contraction condition.
- `goal.md` S-02/S-03/S-04/S-05: source dictionaries and independent exact fixtures connect the
  already-met microring response, power, named-phase, and rejection obligations to the source
  formulas without changing their N5/N6 proof direction.
- Parity candidates closed by a source map: IP-03, IP-04, IP-05, and IP-12.
- IP-07 has a complete base-parameterized bridge plus both base-ten and natural-log readings; the
  source's intended base remains an external unverified fact.
- IP-06 exact printed-form parity is deliberately withheld; the amplitude-derived Def. 10 power is
  bridged and the provenance-uncertain alternative is refuted at an exact rational point.

## Source finding and non-claims

- `HOL-CORPUS.md:248` records SysCon Thm. 6 only as a closed form and transcribes no expression.
  The disputed `4*k1*k2*exp(-phi)*sin(phi/2)^2` term came from a previously recorded transcription
  of uncertain provenance. It is not attributed to the corpus survey, paper, or script here.
- At `u1=u2=4/5`, `k1=k2=3/5`, `x_r=9/16`, and `phi=pi`, the amplitude-derived denominator is
  exactly `1156/625`; the disputed candidate is
  `256/625 + (36/25)*exp(-pi)`, and the regression proves they differ.
- Thm. 5 norm-squaring gives the amplitude-derived denominator, and Def. 11 evaluation gives the
  Thm. 7 ratio. Their agreement is evidence, not a classification of the unverified Thm. 6 text.
- The source's bare `10 log` base is not assumed. `powerRatioInBase` carries the base explicitly;
  base ten maps to Physlib's power-ratio dB convention, and base `exp 1` maps to natural log.
- SysCon Def. 9 supplies two `sqrt(x_r)` half arcs (`HOL-CORPUS.md:244-247`). Mapping `x_r` to
  Physlib's round-trip field attenuation is the bridge dictionary's inference, not a source
  classification of `x_r` as a field or power quantity.
- DATE and SysCon quotient definitions are totalized. N5 response meaning is asserted only under
  the exact solve/contraction gates. The SysCon `tsum` is totalized and has geometric feedback
  meaning only under `SysConParameters.IsContractive`.
- DATE cascade, lattice, termination, and Sylvester claims are not bridged.
- No reciprocity, time-reversed port pairing, omitted-loss completeness, time-domain causality,
  bandwidth, dispersion, or measurement-validation claim is made.
- Source citations follow the supplied local parity corpus. Per `AI-POLICY.md`, the human author
  must independently certify the bibliography, page references, and source transcriptions.

## Gates

After the `33ee2ab7` development sync, this chained mutex-protected gate passed with temporary
registrations for the three per-source production modules and the regression module:

```text
lake --wfail build Physlib.Optics.Systems.Microring.SourceBridgeRegression
lake exe runPhyslibLinters
```

`Physlib.lean` was restored byte-for-byte after the gate. The Unicode-codepoint line audit and
`git diff --check` pass. Run `./scripts/lint-style.sh` on committed state before reporting the
cutoff.
