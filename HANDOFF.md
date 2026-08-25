# S2-S3 microring lane handoff

## Branch and cutoff scope

- Branch: `optics/s2-microring`.
- Slice: S2 add-drop explicit feedback network.
- Integration base: `optics/development` at `66339fd4`.
- The earlier all-pass slice was merged into `optics/development` at `6343fa62`.

## Files and registrations

- `Physlib/Optics/Systems/Microring/AddDropNetwork.lean`
- `Physlib/Optics/Systems/Microring/AddDrop.lean`
- `Physlib/Optics/Systems/Microring/AddDropRegression.lean`

Register the modules in that dependency order. `AddDropNetwork.lean` is a support split required by
the repository file-length gate; `AddDrop.lean` remains the public elimination/series entry point.
This lane did not edit `Physlib.lean` or either API map.

## N7 and N5 declarations used

The add-drop construction binds these merged N7 declarations:

- `Optics.DirectionalCoupler.Parameters` —
  `Physlib/Optics/Components/DirectionalCoupler.lean:62`.
- `Optics.DirectionalCoupler.crossCoefficient` —
  `Physlib/Optics/Components/DirectionalCoupler.lean:68-70`; this is the pinned `-I * k`
  cross-arm coefficient.
- `Optics.DirectionalCoupler.Parameters.IsPowerBounded`, `.IsUnitary`, and `.IsValid` —
  `Physlib/Optics/Components/DirectionalCouplerPower.lean:59,63,67`.
- `Optics.DirectionalCoupler.physicalBehavior` and `.physicalScattering` —
  `Physlib/Optics/Components/DirectionalCouplerPhysical.lean:145,161`.
- `Optics.MatchedPropagation.Parameters` —
  `Physlib/Optics/Components/MatchedPropagation.lean:79`.
- `Optics.MatchedPropagation.physicalBehavior` and `.physicalScattering` —
  `Physlib/Optics/Components/MatchedPropagationPhysical.lean:151,167`.

The response is eliminated through `Optics.FlatNetlist.responseTransform` and
`.toBehavior_responseTransform` at
`Physlib/Optics/Network/FlatNetlistElimination.lean:443,455`. Exact well-posedness uses
`.isWellPosed_iff_feedbackOperator_injective` at line 169 and the feedback definition/equation at
`Physlib/Optics/Network/FlatNetlist.lean:574,578`.

No N6 power-conservation declaration is used in this amplitude-only slice. Power observables and
balance remain for S3 and must bind the mandated N6 theorem there.

## Validation-facing public names

Parameters and scalar amplitudes:

- `Optics.AddDrop.Parameters`
- `Optics.AddDrop.Parameters.inputCoupler`
- `Optics.AddDrop.Parameters.dropCoupler`
- `Optics.AddDrop.Parameters.halfArcAttenuation`
- `Optics.AddDrop.Parameters.halfArcPhase`
- `Optics.AddDrop.Parameters.firstPropagation`
- `Optics.AddDrop.Parameters.secondPropagation`
- `Optics.AddDrop.Parameters.firstArcCoefficient`
- `Optics.AddDrop.Parameters.secondArcCoefficient`
- `Optics.AddDrop.Parameters.roundTripCoefficient`
- `Optics.AddDrop.Parameters.roundTripCoefficient_eq_fieldAttenuation`
- `Optics.AddDrop.Parameters.loopGain`
- `Optics.AddDrop.Parameters.denominator`
- `Optics.AddDrop.Parameters.HasNonzeroDenominator`
- `Optics.AddDrop.Parameters.IsContractive`
- `Optics.AddDrop.Parameters.IsValid`
- `Optics.AddDrop.Parameters.IsValid.fieldAttenuation_nonneg`
- `Optics.AddDrop.Parameters.IsValid.fieldAttenuation_le_one`
- `Optics.AddDrop.Parameters.IsValid.roundTripCoefficient_eq_fieldAttenuation`
- `Optics.AddDrop.throughTransfer`
- `Optics.AddDrop.dropTransfer`
- `Optics.AddDrop.standardThroughTransfer`
- `Optics.AddDrop.standardDropTransfer`
- `Optics.AddDrop.throughTransfer_eq_standard`
- `Optics.AddDrop.dropTransfer_eq_standard`

Explicit network and N5 response:

- `Optics.AddDrop.Component`
- `Optics.AddDrop.Connection`
- `Optics.AddDrop.components`
- `Optics.AddDrop.connections`
- `Optics.AddDrop.netlist`
- `Optics.AddDrop.inputChannel`
- `Optics.AddDrop.throughChannel`
- `Optics.AddDrop.addChannel`
- `Optics.AddDrop.dropChannel`
- `Optics.AddDrop.inputAmplitude`
- `Optics.AddDrop.isWellPosed_of_hasNonzeroDenominator`
- `Optics.AddDrop.not_isWellPosed_of_denominator_eq_zero`
- `Optics.AddDrop.isWellPosed_iff`
- `Optics.AddDrop.response_through`
- `Optics.AddDrop.response_drop`
- `Optics.AddDrop.responseTransform_entry_through_input`
- `Optics.AddDrop.responseTransform_entry_drop_input`

Convergent-series API:

- `Optics.AddDrop.roundTripSeries`
- `Optics.AddDrop.summable_roundTripSeries`
- `Optics.AddDrop.Parameters.IsContractive.hasNonzeroDenominator`
- `Optics.AddDrop.roundTripSeries_eq_inverse`
- `Optics.AddDrop.throughTransferSeries`
- `Optics.AddDrop.dropTransferSeries`
- `Optics.AddDrop.throughTransfer_eq_roundTripSeries`
- `Optics.AddDrop.dropTransfer_eq_roundTripSeries`
- `Optics.AddDrop.response_through_eq_roundTripSeries`
- `Optics.AddDrop.response_drop_eq_roundTripSeries`

Exact named-point fixtures:

- `Optics.AddDrop.addDropRegressionResonanceParameters`
- `Optics.AddDrop.addDropRegression_resonance_isValid`
- `Optics.AddDrop.addDropRegression_connections_pairs`
- `Optics.AddDrop.addDropRegression_resonance_firstArcCoefficient`
- `Optics.AddDrop.addDropRegression_resonance_secondArcCoefficient`
- `Optics.AddDrop.addDropRegression_resonance_roundTripCoefficient`
- `Optics.AddDrop.addDropRegression_resonance_loopGain`
- `Optics.AddDrop.addDropRegression_resonance_denominator`
- `Optics.AddDrop.addDropRegression_resonance_throughTransfer`
- `Optics.AddDrop.addDropRegression_resonance_dropTransfer`
- `Optics.AddDrop.addDropRegression_resonance_isWellPosed`
- `Optics.AddDrop.addDropRegression_resonance_responseTransform_entry_through`
- `Optics.AddDrop.addDropRegression_resonance_responseTransform_entry_drop`
- `Optics.AddDrop.addDropRegression_resonance_isContractive`
- `Optics.AddDrop.addDropRegression_resonance_roundTripSeries`
- `Optics.AddDrop.addDropRegression_resonance_throughTransferSeries`
- `Optics.AddDrop.addDropRegression_resonance_dropTransferSeries`
- `Optics.AddDrop.addDropRegression_resonance_response_through_eq_series`
- `Optics.AddDrop.addDropRegression_resonance_response_drop_eq_series`
- `Optics.AddDrop.addDropRegressionAntiresonanceParameters`
- `Optics.AddDrop.addDropRegression_antiresonance_isValid`
- `Optics.AddDrop.addDropRegression_antiresonance_firstArcCoefficient`
- `Optics.AddDrop.addDropRegression_antiresonance_secondArcCoefficient`
- `Optics.AddDrop.addDropRegression_antiresonance_roundTripCoefficient`
- `Optics.AddDrop.addDropRegression_antiresonance_loopGain`
- `Optics.AddDrop.addDropRegression_antiresonance_denominator`
- `Optics.AddDrop.addDropRegression_antiresonance_throughTransfer`
- `Optics.AddDrop.addDropRegression_antiresonance_dropTransfer`

## Supporting declaration groups

- Parameter equations: `Parameters.inputCoupler_amplitudes`,
  `Parameters.dropCoupler_amplitudes`, `Parameters.halfArcAttenuation_sq`,
  `Parameters.halfArcPhase_factor_sq`, `Parameters.propagation_data`,
  `Parameters.roundTripCoefficient_eq`, `Parameters.loopGain_eq`,
  `Parameters.denominator_eq`, `Parameters.hasNonzeroDenominator_iff`,
  `Parameters.isContractive_iff`, and `Parameters.isValid_iff`.
- Network data: `componentPortFamily`, `componentPortFamily_eq`, `componentScattering`,
  `componentScattering_eq`, `components_data`, `connections_pairs`, and `netlist_data`.
- The public `connections_pairs` law and `addDropRegression_connections_pairs` fixture pin both
  endpoints of all four connections; no claim rests on symmetric numeric values detecting every
  possible arc-port permutation.
- Aggregate channels: `inputCouplerChannel`, `dropCouplerChannel`, `firstArcChannel`,
  `secondArcChannel`, their injection/disjointness lemmas, and the four external-channel
  nonconnection lemmas.
- N7 coordinate laws: the four `*_physicalBehavior_of_scatteringEquation` lemmas and the ten
  `scatteringEquation_*` lemmas.
- N5 routing laws: the twelve `incidentAssembly_apply_*` lemmas and the two
  `outputReadout_apply_*` lemmas.
- Exact gate machinery: `forwardLoop_inputCoupler_leftSecond_eq_zero`,
  `reverseLoop_inputCoupler_rightSecond_eq_zero`, `feedback_fixedPoint_eq_zero`,
  `singularIncident`, `singularIncident_apply`, `singularIncident_ne_zero`,
  `singularIncident_fixedPoint`, and `singularIncident_feedbackOperator_eq_zero`.
- Solved channel coordinates: `inputCoupler_leftSecond_solution` and
  `dropCoupler_leftSecond_solution`.

## Milestones, parity, and regressions

- `goal.md` H.4 S2 add-drop portion: explicit two-bus feedback network, both N5 transfer
  amplitudes, exact solve gate in both directions, and contraction-gated series bridges.
- `goal.md` I.3 row S-02 add-drop portion: both response entries agree with independently
  evaluated convergent-series expressions at the exact zero-phase fixture.
- `goal.md` I.3 row S-04: the physical N7 add-drop realization yields both exact N5 transfer
  responses.
- The response is Physlib-original. No DATE 2014 or SysCon 2015 port-order/chain-matrix bridge is
  claimed, so no IP parity row is closed by this slice.

## Exact semantic split and non-claims

- `throughTransfer`, `dropTransfer`, and both `standard*Transfer` definitions are totalized scalar
  expressions. Their standard-form identifications use the stated unitary/nonzero-denominator
  gates where required.
- N5 response statements are gated by `HasNonzeroDenominator`, proved equivalent to netlist
  well-posedness. The zero-denominator converse uses an explicit nonzero feedback-kernel state;
  no determinant or totalized inverse establishes that converse.
- `roundTripSeries`, `throughTransferSeries`, and `dropTransferSeries` are totalized Mathlib
  `tsum` expressions. They have no convergent-circulation or response meaning without
  `Summable`/`IsContractive`; only the interpretation and response lemmas are gated. Contraction
  is sufficient, not necessary, for N5 well-posedness.
- The symmetric `sqrt a` arc split fixes a drop-port reference plane. The theorem relating its
  product to the declared round-trip field attenuation follows directly from `Parameters.IsValid`,
  which includes the physical bounds `0 ≤ a ≤ 1`.
- “Resonance” and “antiresonance” in regression names denote zero- and half-turn phase points.
  No extremum, minimum, maximum, or global resonance characterization is claimed.
- The modules are fixed-carrier and single-mode. They do not establish power observables,
  lossless balance, critical coupling, extinction, rejection ratio, parameter recovery, free
  spectral range, bandwidth, causality, dispersion, group delay, nonlinear response, thermal
  response, material realization, or omitted-loss-channel behavior.
- The modules assert neither reciprocity nor a time-reversed pairing of external ports.
