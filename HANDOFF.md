# S2-S3 microring lane handoff

## Branch and current cutoff

- Branch: `optics/s2-microring`
- Slice: S2 all-pass explicit feedback network
- Integration base at cutoff: `optics/development` at `b9ac5c65`

## Files

- `Physlib/Optics/Systems/Microring/AllPass.lean`
- `Physlib/Optics/Systems/Microring/AllPassRegression.lean`

The conductor should register both modules in `Physlib.lean`, in sorted order. This lane did not edit
the registry.

## N7 declarations used

The all-pass construction binds the following merged N7 declarations:

- `Optics.DirectionalCoupler.Parameters` —
  `Physlib/Optics/Components/DirectionalCoupler.lean:62`.
- `Optics.DirectionalCoupler.crossCoefficient` —
  `Physlib/Optics/Components/DirectionalCoupler.lean:68-70`; this is the pinned `-I * k`
  cross-arm convention.
- `Optics.DirectionalCoupler.Parameters.IsPowerBounded`, `.IsUnitary`, and `.IsValid` —
  `Physlib/Optics/Components/DirectionalCouplerPower.lean:59,63,67`.
- `Optics.DirectionalCoupler.physicalBehavior` and `.physicalScattering` —
  `Physlib/Optics/Components/DirectionalCouplerPhysical.lean:145,161`.
- `Optics.DirectionalCoupler.physicalBehavior_output_power`,
  `.physicalScattering_isPassive`, and `.physicalScattering_isLossless` —
  `Physlib/Optics/Components/DirectionalCouplerPhysicalPower.lean:51,63,72`.
- `Optics.MatchedPropagation.Parameters` —
  `Physlib/Optics/Components/MatchedPropagation.lean:79`.
- `Optics.MatchedPropagation.physicalBehavior` and `.physicalScattering` —
  `Physlib/Optics/Components/MatchedPropagationPhysical.lean:151,167`.
- `Optics.MatchedPropagation.physicalBehavior_output_power`,
  `.physicalScattering_isPassive`, and `.physicalScattering_isLossless` —
  `Physlib/Optics/Components/MatchedPropagationPhysicalPower.lean:59,76,86`.

The response is eliminated through `Optics.FlatNetlist.responseTransform` and
`.toBehavior_responseTransform` at
`Physlib/Optics/Network/FlatNetlistElimination.lean:443,455`. Exact well-posedness uses
`.isWellPosed_iff_feedbackOperator_injective` at line 169 and the feedback definition/equation at
`Physlib/Optics/Network/FlatNetlist.lean:574,578`.

## Public declarations

Validation-facing all-pass names:

- `Optics.AllPass.Parameters`
- `Optics.AllPass.Parameters.coupler`
- `Optics.AllPass.Parameters.propagation`
- `Optics.AllPass.Parameters.loopCoefficient`
- `Optics.AllPass.Parameters.loopGain`
- `Optics.AllPass.Parameters.denominator`
- `Optics.AllPass.Parameters.HasNonzeroDenominator`
- `Optics.AllPass.Parameters.IsContractive`
- `Optics.AllPass.Parameters.IsValid`
- `Optics.AllPass.throughTransfer`
- `Optics.AllPass.standardThroughTransfer`
- `Optics.AllPass.throughTransfer_eq_standard`
- `Optics.AllPass.netlist`
- `Optics.AllPass.isWellPosed_of_hasNonzeroDenominator`
- `Optics.AllPass.not_isWellPosed_of_denominator_eq_zero`
- `Optics.AllPass.isWellPosed_iff`
- `Optics.AllPass.inputChannel`
- `Optics.AllPass.throughChannel`
- `Optics.AllPass.inputAmplitude`
- `Optics.AllPass.response_through`
- `Optics.AllPass.responseTransform_entry_through_input`
- `Optics.AllPass.roundTripSeries`
- `Optics.AllPass.summable_roundTripSeries`
- `Optics.AllPass.Parameters.IsContractive.hasNonzeroDenominator`
- `Optics.AllPass.roundTripSeries_eq_inverse`
- `Optics.AllPass.throughTransferSeries`
- `Optics.AllPass.throughTransfer_eq_roundTripSeries`
- `Optics.AllPass.response_through_eq_roundTripSeries`

Exact validation fixtures:

- `Optics.AllPass.allPassRegressionResonanceParameters`
- `Optics.AllPass.allPassRegression_resonance_isValid`
- `Optics.AllPass.allPassRegression_resonance_loopCoefficient`
- `Optics.AllPass.allPassRegression_resonance_denominator`
- `Optics.AllPass.allPassRegression_resonance_throughTransfer`
- `Optics.AllPass.allPassRegressionAntiresonanceParameters`
- `Optics.AllPass.allPassRegression_antiresonance_loopCoefficient`
- `Optics.AllPass.allPassRegression_antiresonance_denominator`
- `Optics.AllPass.allPassRegression_antiresonance_throughTransfer`

Supporting structural API:

- Parameter projection/equation lemmas: `Parameters.coupler_amplitudes`,
  `Parameters.propagation_data`, `Parameters.loopCoefficient_eq`, `Parameters.loopGain_eq`,
  `Parameters.denominator_eq`, `Parameters.hasNonzeroDenominator_iff`,
  `Parameters.isContractive_iff`, `Parameters.isValid_iff`, and
  `throughTransfer_mul_denominator`.
- Netlist data: `Component`, `componentPortFamily`, `componentPortFamily_eq`,
  `componentScattering`, `componentScattering_eq`, `components`, `components_data`, `Connection`,
  `connections`, `connections_pairs`, and `netlist_data`.
- Channel data: `couplerChannel`, `couplerChannel_injective`, `couplerChannel_eq_iff`,
  `propagationChannel`, `propagationChannel_injective`, `propagationChannel_eq_iff`,
  `couplerChannel_ne_propagationChannel`, `propagationChannel_ne_couplerChannel`,
  `couplerChannel_leftFirst_not_connected`, `couplerChannel_rightFirst_not_connected`,
  `inputChannel_val`, `throughChannel_val`, `inputChannel_ne_throughChannel`,
  `inputAmplitude_apply_input`, and `inputAmplitude_apply_through`.
- Explicit N7/local equations: `couplerScattering_apply_rightFirst`,
  `couplerScattering_apply_rightSecond`, `couplerScattering_apply_leftSecond`,
  `propagationScattering_apply_right`, `propagationScattering_apply_left`,
  `coupler_physicalBehavior_of_scatteringEquation`,
  `propagation_physicalBehavior_of_scatteringEquation`, and the five
  `scatteringEquation_*` coordinate lemmas.
- Explicit feedback routing: the four `connected*` definitions and their embedding/mate lemmas,
  plus the six `incidentAssembly_apply_*` equations.
- Exact converse gate witness: `feedback_fixedPoint_eq_zero`, `singularIncident`,
  `singularIncident_apply`, `singularIncident_ne_zero`, `singularIncident_fixedPoint`,
  `singularIncident_feedbackOperator_eq_zero`, and `outputReadout_apply_through`.
- Projected finite/decidable instances: `componentsComponentFintype`,
  `componentsComponentDecidableEq`, `localChannelFintype`, `localChannelDecidableEq`,
  `componentsLocalChannelFintype`, `componentsLocalChannelDecidableEq`,
  `componentsChannelFintype`, `componentsChannelDecidableEq`,
  `componentsLocalIncidentFintype`, `componentsLocalIncidentDecidableEq`,
  `netlistComponentFintype`, `netlistComponentDecidableEq`, `netlistLocalChannelFintype`,
  `netlistLocalChannelDecidableEq`, `channelFintype`, `channelDecidableEq`,
  `connectionLocalChannelFintype`, `connectedChannelFintype`, `connectedChannelDecidableEq`, and
  `externalChannelFintype`.

## Milestones and parity

- `goal.md` H.4 S2, all-pass portion: explicit N7 coupler/propagation feedback network, response
  derived through N5, exact denominator gate in both directions, and contraction-gated geometric
  series equal to the elimination result.
- `goal.md` I.3 row S-02, all-pass portion: elimination and convergent round-trip series agree.
- Parity row IP-03, all-pass transfer portion: the transfer is a derived N5 consequence rather
  than a formula stored in a behavior predicate.

## Exact semantic split and non-claims

- `throughTransfer` and `standardThroughTransfer` are totalized scalar expressions. Their equality
  is gated by a unitary coupler and a nonzero denominator.
- N5 response statements are gated by `HasNonzeroDenominator`, proved equivalent to netlist
  well-posedness. The zero-denominator converse is witnessed by an explicit nonzero feedback
  kernel state; no determinant or totalized inverse is used for that converse.
- The round-trip series is stated only under `IsContractive`; contraction is sufficient, not
  necessary, for N5 well-posedness.
- The module is fixed-carrier and single-mode. It makes no bandwidth, causality, dispersion,
  group-delay, material-realization, or omitted-loss-channel claim.
- Power/conservation and sweep observables are intentionally deferred to the S3 slice, where they
  will bind the merged N6 and N5F APIs.
