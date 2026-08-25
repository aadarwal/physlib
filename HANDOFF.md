# S2-S3 microring lane handoff

## Branch and cutoff scope

- Branch: `optics/s2-microring`.
- Slice: S3 add-drop observables and proof-gated nondispersive frequency response.
- Integration base: `optics/development` at `af062790` or later at cutoff.
- S2 all-pass and add-drop amplitude/series slices are already registered on development.

## Files and requested registrations

Register these new modules in dependency order:

1. `Physlib/Optics/Systems/Microring/ObservablesPower.lean`
2. `Physlib/Optics/Systems/Microring/ObservablesFrequency.lean`
3. `Physlib/Optics/Systems/Microring/Observables.lean`
4. `Physlib/Optics/Systems/Microring/ObservablesRegression.lean`

The lane did not edit `Physlib.lean`, either API map, `goal.md`, or `tbd.md` relative to the synced
development head.

## Quoted N7 component contract

The implementation was checked against the following merged N7 declarations:

- `Optics.DirectionalCoupler.Parameters` —
  `Physlib/Optics/Components/DirectionalCoupler.lean:62`.
- `Optics.DirectionalCoupler.crossCoefficient` —
  `Physlib/Optics/Components/DirectionalCoupler.lean:68-70`; its cross term is exactly
  `-Complex.I * crossAmplitude`.
- `Optics.DirectionalCoupler.Parameters.IsPowerBounded`, `.IsUnitary`, and `.IsValid` —
  `Physlib/Optics/Components/DirectionalCouplerPower.lean:59-68`.
- `Optics.DirectionalCoupler.physicalBehavior` and `.physicalScattering` —
  `Physlib/Optics/Components/DirectionalCouplerPhysical.lean:145-148,161-163`.
- `Optics.DirectionalCoupler.physicalBehavior_output_power` —
  `Physlib/Optics/Components/DirectionalCouplerPhysicalPower.lean:51-58`.
- `Optics.DirectionalCoupler.physicalScattering_isPassive` and
  `.physicalScattering_isLossless` —
  `Physlib/Optics/Components/DirectionalCouplerPhysicalPower.lean:63-75`.
- `Optics.MatchedPropagation.Parameters` and `.Parameters.IsValid` —
  `Physlib/Optics/Components/MatchedPropagation.lean:79-90`.
- `Optics.MatchedPropagation.physicalBehavior` and `.physicalScattering` —
  `Physlib/Optics/Components/MatchedPropagationPhysical.lean:151-154,167-169`.
- `Optics.MatchedPropagation.physicalBehavior_output_power` —
  `Physlib/Optics/Components/MatchedPropagationPhysicalPower.lean:59-66`.
- `Optics.MatchedPropagation.physicalScattering_isPassive` and
  `.physicalScattering_isLossless` —
  `Physlib/Optics/Components/MatchedPropagationPhysicalPower.lean:76-90`.

The system-level proof directly consumes both N7 `physicalScattering_isLossless` results. The
behavior-power and passivity declarations above are the audited companion normalization API; this
slice does not route lossless balance through either companion result.

## N5, N5F, and mandatory N6 bindings

- The fixed-parameter N5 response is `Optics.AddDrop.response_through`, `.response_drop`, and the
  two response-entry lemmas at
  `Physlib/Optics/Systems/Microring/AddDrop.lean:635-725`.
- N5F `responseDomain`, `mem_responseDomain_iff`, and proof-gated `response` are at
  `Physlib/Optics/Network/ParameterizedResponse.lean:464-472,499-518`.
  `ObservablesFrequency` uses only `ParameterizedNetlist.response` on `responseDomain`; it never
  uses `unguardedResponse`.
- System losslessness comes only through
  `Optics.FlatNetlist.externalScatteringMatrix_isLossless_of_components_isLossless` at
  `Physlib/Optics/Network/Conservation.lean:543-553`, with the exact well-posedness and
  componentwise-losslessness hypotheses.
- Coherent and incoherent second-order outputs use `Optics.FlatNetlist.responseCoherency` at
  `Physlib/Optics/Network/Coherency.lean:450-478`.

No response matrix is re-derived and checked for unitarity by hand.

## Public declaration inventory

### Fixed-frequency powers and named phase conditions

- `Optics.AddDrop.Parameters.phaseFactor`
- `Optics.AddDrop.Parameters.phaseFactor_eq_cos_sub_sin_mul_I`
- `Optics.AddDrop.Parameters.powerDenominator`
- `Optics.AddDrop.Parameters.throughPowerNumerator`
- `Optics.AddDrop.Parameters.dropPowerNumerator`
- `Optics.AddDrop.throughPower`
- `Optics.AddDrop.dropPower`
- `Optics.AddDrop.throughPower_nonneg`
- `Optics.AddDrop.dropPower_nonneg`
- `Optics.AddDrop.throughPower_pos_iff`
- `Optics.AddDrop.dropPower_pos_iff`
- `Optics.AddDrop.Parameters.powerDenominator_pos`
- `Optics.AddDrop.Parameters.dropPowerNumerator_pos`
- `Optics.AddDrop.throughPower_eq_closedForm`
- `Optics.AddDrop.dropPower_eq_closedForm`
- `Optics.AddDrop.Parameters.IsResonant`
- `Optics.AddDrop.Parameters.IsAntiresonant`
- `Optics.AddDrop.Parameters.isResonant_of_roundTripPhase_eq_zero`
- `Optics.AddDrop.Parameters.isAntiresonant_of_roundTripPhase_eq_pi`
- `Optics.AddDrop.throughPower_of_isResonant`
- `Optics.AddDrop.throughPower_of_isAntiresonant`
- `Optics.AddDrop.dropPower_of_isResonant`
- `Optics.AddDrop.dropPower_of_isAntiresonant`

Supporting exact modulus and named-phase declarations are
`Parameters.roundTripCoefficient_eq_field_mul_phaseFactor`, `Parameters.normSq_denominator`,
`Parameters.normSq_throughNumerator`, `Parameters.normSq_dropNumerator`,
`Parameters.cos_eq_one_of_isResonant`, `Parameters.cos_eq_neg_one_of_isAntiresonant`, and the
four `Parameters.*Power*of_is{Resonant,Antiresonant}` numerator/denominator lemmas.

### Critical coupling, rejection ratios, and recovery

- `Optics.AddDrop.Parameters.IsCriticallyCoupled`
- `Optics.AddDrop.criticalCoupling_extinction`
- `Optics.AddDrop.criticalCoupling_throughPower_eq_zero`
- `Optics.AddDrop.criticalCoupling_of_extinction`
- `Optics.AddDrop.powerRatioDB`
- `Optics.AddDrop.powerRatioDB_eq_logb_sub`
- `Optics.AddDrop.Parameters.atResonance`
- `Optics.AddDrop.Parameters.atAntiresonance`
- `Optics.AddDrop.throughRejectionRatioDB`
- `Optics.AddDrop.throughRejectionRatioDB_eq_closedForm`
- `Optics.AddDrop.throughRejectionRatioDB_eq_logb_sub`
- `Optics.AddDrop.dropRejectionRatioDB`
- `Optics.AddDrop.dropRejectionRatioDB_eq_closedForm`
- `Optics.AddDrop.dropRejectionRatioDB_eq_denominatorRatio`
- `Optics.AddDrop.dropRejectionRatioDB_eq_logb_sub`
- `Optics.AddDrop.fieldAttenuation_eq_of_criticalCoupling`
- `Optics.AddDrop.inputCrossAmplitude_sq_eq_of_criticalCoupling`
- `Optics.AddDrop.inputCrossAmplitude_eq_sqrt_of_criticalCoupling`
- `Optics.AddDrop.fieldAttenuation_eq_of_resonant_extinction`
- `Optics.AddDrop.attenuation_eq_of_antiresonant_field`
- `Optics.AddDrop.inputCrossAmplitude_eq_sqrt_of_resonant_extinction`

The four `Parameters.at{Resonance,Antiresonance}_*` specialization lemmas are also public.

### N6 losslessness and coherency

- `Optics.AddDrop.Parameters.IsLossless`
- `Optics.AddDrop.components_isLossless`
- `Optics.AddDrop.externalScatteringMatrix_isLossless`
- `Optics.AddDrop.responseTransform_isPowerPreserving`
- `Optics.AddDrop.ExternalPort`
- `Optics.AddDrop.externalChannel`
- `Optics.AddDrop.externalChannelEquiv`
- `Optics.AddDrop.externalIncidentEquiv`
- `Optics.AddDrop.externalOutgoingEquiv`
- `Optics.AddDrop.inputAmplitude_power`
- `Optics.AddDrop.coherent_output_channelPower`
- `Optics.AddDrop.incoherent_output_channelPower_add`
- `Optics.AddDrop.reflected_amplitudes_eq_zero`
- `Optics.AddDrop.lossless_response_through_drop_power_balance`
- `Optics.AddDrop.lossless_through_drop_power_balance`

The external-channel bijection, four-port sum, reverse-loop, reflected-coordinate, and readout
support lemmas are public and remain in `ObservablesPower` beside these results.

### N5F pointwise response and free spectral range

- `Optics.AddDrop.parameterizedComponents`
- `Optics.AddDrop.parameterizedNetlist`
- `Optics.AddDrop.parameterizedNetlist_compile`
- `Optics.AddDrop.mem_parameterizedNetlist_responseDomain_iff`
- `Optics.AddDrop.parameterizedNetlist_response_through`
- `Optics.AddDrop.parameterizedNetlist_response_drop`
- `Optics.AddDrop.parameterizedNetlist_response_through_power`
- `Optics.AddDrop.parameterizedNetlist_response_drop_power`
- `Optics.AddDrop.parameterizedNetlist_response_through_power_eq_closedForm`
- `Optics.AddDrop.parameterizedNetlist_response_drop_power_eq_closedForm`
- `Optics.AddDrop.NondispersiveGroupIndexModel`
- `Optics.AddDrop.NondispersiveGroupIndexModel.groupDelay`
- `Optics.AddDrop.NondispersiveGroupIndexModel.angularFSR`
- `Optics.AddDrop.NondispersiveGroupIndexModel.angularFSR_eq`
- `Optics.AddDrop.NondispersiveGroupIndexModel.frequencyFSR`
- `Optics.AddDrop.NondispersiveGroupIndexModel.frequencyFSR_eq`
- `Optics.AddDrop.NondispersiveGroupIndexModel.parametersAt`
- `Optics.AddDrop.NondispersiveGroupIndexModel.network`
- `Optics.AddDrop.NondispersiveGroupIndexModel.add_angularFSR_mem_responseDomain`
- `Optics.AddDrop.NondispersiveGroupIndexModel.throughPower_add_angularFSR`
- `Optics.AddDrop.NondispersiveGroupIndexModel.dropPower_add_angularFSR`
- `Optics.AddDrop.NondispersiveGroupIndexModel.nondispersive_throughPower_periodic`
- `Optics.AddDrop.NondispersiveGroupIndexModel.nondispersive_dropPower_periodic`
- `Optics.AddDrop.NondispersiveGroupIndexModel.nondispersive_throughPower_periodic_of_mem`
- `Optics.AddDrop.NondispersiveGroupIndexModel.nondispersive_dropPower_periodic_of_mem`

Positivity, phase-shift, validity-periodicity, round-trip-coefficient, denominator-periodicity, and
finite-channel support lemmas in the same namespace are public.

## Exact validation-facing fixture names

Named `t = 3 / 5`, `kappa = 4 / 5`, `a = 1 / 4` phase points:

- `Optics.AddDrop.observablesRegression_resonance_throughPower` = `2025 / 8281`
- `Optics.AddDrop.observablesRegression_resonance_dropPower` = `1024 / 8281`
- `Optics.AddDrop.observablesRegression_antiresonance_throughPower` = `5625 / 11881`
- `Optics.AddDrop.observablesRegression_antiresonance_dropPower` = `1024 / 11881`
- `Optics.AddDrop.observablesRegression_resonance_powerDenominator` = `8281 / 10000`
- `Optics.AddDrop.observablesRegression_antiresonance_powerDenominator` = `11881 / 10000`
- `Optics.AddDrop.observablesRegression_rejectionRatioDB`
- `Optics.AddDrop.observablesRegression_rejectionRatioDB_eq_logb_sub`
- `Optics.AddDrop.observablesRegression_dropRejectionRatioDB`
- `Optics.AddDrop.observablesRegression_dropRejectionRatioDB_eq_logb_sub`
- `Optics.AddDrop.observablesRegression_resonance_throughPower_eq_closedForm`
- `Optics.AddDrop.observablesRegression_resonance_dropPower_eq_closedForm`
- `Optics.AddDrop.observablesRegression_antiresonance_throughPower_eq_closedForm`
- `Optics.AddDrop.observablesRegression_antiresonance_dropPower_eq_closedForm`

Critical-coupling and recovery fixture names:

- `Optics.AddDrop.observablesRegressionCriticalParameters`
- `Optics.AddDrop.observablesRegression_critical_isLossless`
- `Optics.AddDrop.observablesRegression_critical_isValid`
- `Optics.AddDrop.observablesRegression_critical_hasNonzeroDenominator`
- `Optics.AddDrop.observablesRegression_critical_isCriticallyCoupled`
- `Optics.AddDrop.observablesRegression_critical_extinction`
- `Optics.AddDrop.observablesRegression_critical_lossless_powerBalance`
- `Optics.AddDrop.observablesRegression_critical_recovers_inputCrossAmplitude`
- `Optics.AddDrop.observablesRegression_antiresonance_recovers_attenuation`

N5F/FSR fixture names:

- `Optics.AddDrop.observablesRegressionNondispersiveModel`
- `Optics.AddDrop.observablesRegression_groupDelay` = `6 / 5`
- `Optics.AddDrop.observablesRegression_angularFSR` = `5 * Real.pi / 3`
- `Optics.AddDrop.observablesRegression_frequencyFSR` = `5 / 6`
- `Optics.AddDrop.observablesRegression_zero_mem_responseDomain`
- `Optics.AddDrop.observablesRegression_zero_mem_networkResponseDomain`
- `Optics.AddDrop.observablesRegression_oneFSR_mem_networkResponseDomain`
- `Optics.AddDrop.observablesRegression_n5f_resonance_throughPower` = `2025 / 8281`

The numerator fixtures and strict-positive named through/drop-power fixtures are public as well.

## Milestones and parity status

- `goal.md` H.4 S3: pointwise N5F powers, N6 lossless balance, named phase conditions, critical
  coupling/extinction, positive-power rejection ratios, explicit recovery hypotheses, and
  nondispersive group-index FSR.
- `goal.md` I.3 row S-03: exact transfer-derived power, named-phase, critical-coupling, rejection,
  and N5F specializations.
- `goal.md` I.3 row S-05: general power nonnegativity; exact strictly positive rejection fixtures;
  and log-difference theorems carrying their positive power or denominator hypotheses.
- S-02 and S-04 were closed by the already merged S2 slices and are not re-claimed here.
- No IP-04 through IP-07 or IP-12 parity row is claimed. The DATE'14/SysCon'15/SFG source port and
  parameter bridge remains absent; these results are derived Physlib observables, not a proof that
  the source behavior predicates coincide with this explicit N7/N5 network.

## Exact semantic split and non-claims

- `throughPower` and `dropPower` are squared moduli of totalized algebraic transfer definitions.
  The ungated drop closed-form theorem is an identity of totalized objects, not a physical response
  at a zero denominator or outside component validity. N5F physical power results are only on
  `responseDomain`.
- `IsResonant` and `IsAntiresonant` are named phase-factor conditions. The slice proves phase-point
  formulas, not minima, maxima, linewidths, or a global extremum characterization.
- `powerRatioDB` is totalized. A decibel interpretation is asserted only under strictly positive
  numerator and denominator hypotheses. The drop rejection theorem additionally states nonzero
  cross amplitudes, positive attenuation, and both solve gates before cancelling its numerator.
- Recovery theorems require phase-resolved real field data or the explicit critical-coupling and
  resonant-extinction hypotheses. They do not claim that an unrestricted single intensity spectrum
  identifies coupling, attenuation, amplitude sign, or phase.
- FSR uses positive constant group index, geometric round-trip length, and propagation speed, with
  affine phase in angular frequency. It makes no dispersive, frequency-dependent-group-index,
  linewidth, quality-factor, or inferred-group-delay claim.
- Powers are normalized modal powers, not electromagnetic powers without a separate Poynting
  normalization. No reciprocity or time-reversed external-port pairing is asserted.
- No bandwidth, causality, nonlinear, thermal, fabrication, material-realization, or
  omitted-loss-channel claim is made.

## Gates

- Synced to `optics/development` at `af062790` before the gate.
- One locked chain built `Physlib.Optics.Systems.Microring.ObservablesRegression`, checked all four
  new modules with `-DwarningAsError=true`, and ran `runPhyslibLinters`; all passed.
- Banned-token scan, Unicode-codepoint line-length scan, and `git diff --check` passed.
- The cutoff hash is recorded in the controller message after the post-gate commit.
