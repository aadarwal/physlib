# S1 Mach--Zehnder handoff

## Branch and files

- Branch: `optics/s1-mzi`
- `Physlib/Optics/Systems/MachZehnder/Construction.lean`
- `Physlib/Optics/Systems/MachZehnder/Basic.lean`
- `Physlib/Optics/Systems/MachZehnder/Regression.lean`

The conductor should add these sorted registrations and make no other registry change for this
lane:

```lean
public import Physlib.Optics.Systems.MachZehnder.Basic
public import Physlib.Optics.Systems.MachZehnder.Construction
public import Physlib.Optics.Systems.MachZehnder.Regression
```

## Milestones and slices

- `goal.md:2150-2160`, S1: complete. The implementation is a Physlib extension, not a HOL parity
  row.
- `goal.md:2482`, S-01: complete. The balanced phase-zero and phase-`π` outputs, dark ports,
  every-phase lossless power balance, and phase-factor identifiability shape are symbolic.

Slice 1 constructs exactly two N7 directional couplers and two N7 matched-propagation arms as an
N4 flat netlist. It proves `Optics.MachZehnder.isWellPosed` and
`Optics.MachZehnder.feedbackOperator_det_ne_zero` for every algebraic parameter value, then derives
`Optics.MachZehnder.output_amplitudes` through the N5 incident and response block formulas.

Slice 2 proves `Optics.MachZehnder.output_powers`,
`Optics.MachZehnder.balanced_output_amplitudes`,
`Optics.MachZehnder.balanced_output_powers`, the named phase-zero and phase-`π` points, both dark
ports, and `Optics.MachZehnder.balanced_phase_factor_ratio_eq_output_ratio`.

Slice 3 proves `Optics.MachZehnder.components_isLossless`, obtains
`Optics.MachZehnder.externalScatteringMatrix_isLossless` only through N6, and derives
`Optics.MachZehnder.lossless_output_power_balance` and
`Optics.MachZehnder.balanced_output_power_balance`. Coherent and decorrelated output observables
bind N6 as `Optics.MachZehnder.coherent_output_channelPower` and
`Optics.MachZehnder.incoherent_output_channelPower_add`.

## Exact validation bindings

Topology and general response:

- `Optics.MachZehnder.Parameters`
- `Optics.MachZehnder.Parameters.IsValid`
- `Optics.MachZehnder.Parameters.IsLossless`
- `Optics.MachZehnder.netlist`
- `Optics.MachZehnder.isWellPosed`
- `Optics.MachZehnder.feedbackOperator_det_ne_zero`
- `Optics.MachZehnder.output_amplitudes`
- `Optics.MachZehnder.output_powers`

Balanced and named phase points:

- `Optics.MachZehnder.balancedCoupler`
- `Optics.MachZehnder.losslessArm`
- `Optics.MachZehnder.balancedParameters`
- `Optics.MachZehnder.balancedParameters_isValid`
- `Optics.MachZehnder.balancedParameters_isLossless`
- `Optics.MachZehnder.balanced_output_amplitudes`
- `Optics.MachZehnder.balanced_output_powers`
- `Optics.MachZehnder.balancedPhaseZero`
- `Optics.MachZehnder.balanced_phase_zero_output_amplitudes`
- `Optics.MachZehnder.balanced_phase_zero_dark_port`
- `Optics.MachZehnder.balancedPhasePi`
- `Optics.MachZehnder.balanced_phase_pi_output_amplitudes`
- `Optics.MachZehnder.balanced_phase_pi_dark_port`
- `Optics.MachZehnder.balanced_output_power_balance`
- `Optics.MachZehnder.balanced_phase_factor_ratio_eq_output_ratio`

Conservation and coherency:

- `Optics.MachZehnder.components_isLossless`
- `Optics.MachZehnder.externalScatteringMatrix_isLossless`
- `Optics.MachZehnder.responseTransform_isPowerPreserving`
- `Optics.MachZehnder.reflected_amplitudes_eq_zero`
- `Optics.MachZehnder.lossless_output_power_balance`
- `Optics.MachZehnder.lossless_single_input_output_power_balance`
- `Optics.MachZehnder.coherent_output_channelPower`
- `Optics.MachZehnder.incoherent_output_channelPower_add`

S-01 regressions:

- `Optics.MachZehnder.machZehnderRegression_balanced_through_mul_cross`
- `Optics.MachZehnder.machZehnderRegression_carrierPhaseFactor_points`
- `Optics.MachZehnder.machZehnderRegression_phase_zero_output_amplitudes`
- `Optics.MachZehnder.machZehnderRegression_phase_zero_dark_port`
- `Optics.MachZehnder.machZehnderRegression_phase_pi_output_amplitudes`
- `Optics.MachZehnder.machZehnderRegression_phase_pi_dark_port`
- `Optics.MachZehnder.machZehnderRegression_power_balance`
- `Optics.MachZehnder.machZehnderRegression_phase_factor_ratio`

Only `Optics.MachZehnder.output_amplitudes`, the headline literature-known Mach--Zehnder transfer
result, uses `theorem`. Power corollaries, specializations, and regression fixtures use `lemma`,
following `AGENTS.md:11` and the controller amendment.

## N7 declarations consumed

Directional coupler:

- `Optics.DirectionalCoupler.Parameters` —
  `Physlib/Optics/Components/DirectionalCoupler.lean:62`
- `Optics.DirectionalCoupler.Parameters.IsPowerBounded`, `.IsUnitary`, `.IsValid` —
  `Physlib/Optics/Components/DirectionalCouplerPower.lean:59`, `:63`, `:67`
- `Optics.DirectionalCoupler.physicalBehavior` and `.physicalScattering` —
  `Physlib/Optics/Components/DirectionalCouplerPhysical.lean:145`, `:161`
- `Optics.DirectionalCoupler.physicalBehavior_output_power`,
  `.physicalScattering_isPassive`, `.physicalScattering_isLossless` —
  `Physlib/Optics/Components/DirectionalCouplerPhysicalPower.lean:51`, `:63`, `:72`
- The cross convention is quoted from `Optics.DirectionalCoupler.crossCoefficient` and `mixing` at
  `Physlib/Optics/Components/DirectionalCoupler.lean:68-77`: the cross coefficient is `-I * k`.

Matched propagation:

- `Optics.MatchedPropagation.Parameters` and `.Parameters.IsValid` —
  `Physlib/Optics/Components/MatchedPropagation.lean:79`, `:90`
- `Optics.MatchedPropagation.physicalBehavior` and `.physicalScattering` —
  `Physlib/Optics/Components/MatchedPropagationPhysical.lean:151`, `:167`
- `Optics.MatchedPropagation.physicalBehavior_output_power`,
  `.physicalScattering_isPassive`, `.physicalScattering_isLossless` —
  `Physlib/Optics/Components/MatchedPropagationPhysicalPower.lean:59`, `:76`, `:86`

## N5/N6 bindings

- N5 well-posedness uses
  `Optics.FlatNetlist.isWellPosed_iff_feedbackOperator_injective`
  (`Physlib/Optics/Network/FlatNetlistElimination.lean:169`) and the determinant equivalence at
  `FlatNetlistElimination.lean:221`. Amplitudes use the N5 feedback inverse identity at `:239` and
  response block equality at `:467`.
- System losslessness comes only from
  `Optics.FlatNetlist.externalScatteringMatrix_isLossless_of_components_isLossless`
  (`Physlib/Optics/Network/Conservation.lean:544`).
- Coherent and decorrelated outputs use `Optics.FlatNetlist.responseCoherency`
  (`Physlib/Optics/Network/Coherency.lean:451`) and
  `Optics.CoherencyMatrix.channelPower_map_incoherentSum` (`Coherency.lean:325`).

## Non-claims

- No polarization.
- No dispersion or time-domain delay; arm phases are fixed-frequency path phases.
- No loss except through the explicitly parameterized per-arm field-amplitude factors.
- `ModeAmplitude.power` is normalized modal power, not electromagnetic power without a separate
  Poynting normalization.
- No reciprocity or time-reversed external-port pairing is claimed by the N6 packaging.
- This is a Physlib extension row, not a HOL-corpus parity result.
