# S4 delay-transfer slice 3 handoff

## Branch and synchronization

- Branch: `optics/s4-delay-transfer`
- Worktree: `/Users/aadarwal/src/aadarwal/physlib-wt/optics-s4-delay-transfer`
- Synced by fast-forward merge onto `optics/development` at `64246c8e` before cutoff.
- This slice changes only the four new Lean files below plus this handoff note.

## Files and registrations requested

Register these modules in sorted order in `Physlib.lean`:

- `Physlib.Optics.Systems.DelayTransfer.FrequencyResponse`
- `Physlib.Optics.Systems.DelayTransfer.FrequencyResponseRegression`
- `Physlib.Optics.Systems.DelayTransfer.Stability`
- `Physlib.Optics.Systems.DelayTransfer.StabilityRegression`

Files:

- `Physlib/Optics/Systems/DelayTransfer/FrequencyResponse.lean`
- `Physlib/Optics/Systems/DelayTransfer/FrequencyResponseRegression.lean`
- `Physlib/Optics/Systems/DelayTransfer/Stability.lean`
- `Physlib/Optics/Systems/DelayTransfer/StabilityRegression.lean`

## Goal text implemented

This slice implements these literal S4P bullets from `goal.md:2258-2271`:

- “degree and finiteness bounds”;
- “discrete-time Schur stability and BIBO equivalence only for a stated proper causal rational
  class”; and
- “frequency response under the chosen `q = exp (-s * τ) = z⁻¹` convention”.

It also supplies a generic stable/unstable one-pole strictness fixture relevant to regression row
S-07 at `goal.md:2552`. The DCDR topology-specific instance remains assigned to S7D.

## Production declarations

### `Stability.lean`

In namespace `Optics.DelayTransfer.ReducedRationalResponse`:

- `zeroFinset`
- `poleFinset`
- `zeros_eq_coe_zeroFinset`
- `poles_eq_coe_poleFinset`
- `finite_zeros`
- `finite_poles`
- `card_zeroFinset_le_natDegree`
- `card_poleFinset_le_natDegree`
- `zZeros`
- `zZeroFinset`
- `zZeros_eq_coe_zZeroFinset`
- `finite_zZeros`
- `card_zZeroFinset_le_natDegree`
- `zPoles`
- `zPoleFinset`
- `zPoles_eq_coe_zPoleFinset`
- `finite_zPoles`
- `card_zPoleFinset_le_natDegree`
- `IsSchurStable`
- `AllZerosInsideUnitDisk`
- `IsProper`
- `onePoleReducedResponse`
- `onePoleReducedResponse_isProper`
- `onePoleReducedResponse_eval`
- `zPoles_eq_candidatePoles_of_denominator_eq_recurrence`
- `isSchurStable_iff_zTransform_of_denominator_eq_recurrence`

In namespace `Optics.DelayTransfer`:

- `ProperCausalOnePole`
- `isBoundedSeq_unitImpulse`
- `isBoundedSeq_geometricSeq_of_norm_le_one`
- `not_isBIBOStable_geometricSeq_of_one_lt_norm`
- `norm_convolution_geometricSeq_self`
- `not_isBIBOStable_geometricSeq_of_norm_eq_one`
- `norm_lt_one_of_isBIBOStable_geometricSeq`
- `isBIBOStable_geometricSeq_iff`
- `isBIBOStable_geometricSeq_iff_isSchurStable_onePole`
- `isAbsSummable_geometricSeq_iff_isBIBOStable`

In namespace `Optics.DelayTransfer.ProperCausalOnePole`:

- `response`
- `impulseResponse`
- `response_isProper`
- `impulseResponse_isCausal`
- `transform_impulseResponse_eq_response_eval`
- `response_denominator_eq_recurrenceDenominator`
- `response_zPoles_eq_candidatePoles`
- `response_isSchurStable_iff_zTransform`
- `isBIBOStable_of_isSchurStable`
- `isSchurStable_of_isBIBOStable`
- `isBIBOStable_iff_isSchurStable`

### `FrequencyResponse.lean`

In namespace `Optics.DelayTransfer`:

- `imaginaryFrequency`
- `frequencyDelayEvaluation`
- `frequencyDelayEvaluation_apply`
- `unitCirclePoint`
- `norm_unitCirclePoint`
- `unitCirclePoint_ne_zero`
- `zInverseEvaluation_unitCirclePoint`

In namespace `Optics.DelayTransfer.RationalNetlist`:

- `frequencyResponseDomain`
- `mem_frequencyResponseDomain_iff`
- `frequencyResponse`
- `frequencyResponse_eq_formalDelay`
- `unitCirclePoint_mem_reciprocalZ_responseDomain_iff`
- `unitCirclePoint_mem_reciprocalZ_responseDomain`
- `frequencyResponse_eq_reciprocalZ`

## Regression declarations

### `StabilityRegression.lean`

- `stableOnePole`
- `stableOnePole_zeros`
- `stableOnePole_formalPoles`
- `stableOnePole_zPoles`
- `stableOnePole_numerator_natDegree`
- `stableOnePole_denominator_natDegree`
- `stableOnePole_allZerosInsideUnitDisk`
- `stableOnePole_transform_one`
- `stableOnePole_isSchurStable`
- `stableOnePole_isBIBOStable`
- `unstableOnePole`
- `unstableOnePole_zPoles`
- `unstableOnePole_not_isSchurStable`
- `unstableOnePole_not_isBIBOStable`

### `FrequencyResponseRegression.lean`

- `frequencyDelayEvaluation_quadrature`
- `unitCirclePoint_quadrature`
- `allPassRationalNetlistFrequencyQuadratureDomain`
- `allPassRationalNetlist_frequency_quadrature_response_entry`
- `allPassRationalNetlist_frequency_eq_reciprocalZ_quadrature_entry`

## Exact validation bindings

The validation lane should bind at least these public names:

- `Optics.DelayTransfer.ReducedRationalResponse.card_zeroFinset_le_natDegree`
- `Optics.DelayTransfer.ReducedRationalResponse.card_poleFinset_le_natDegree`
- `Optics.DelayTransfer.ReducedRationalResponse.card_zZeroFinset_le_natDegree`
- `Optics.DelayTransfer.ReducedRationalResponse.card_zPoleFinset_le_natDegree`
- `Optics.DelayTransfer.ReducedRationalResponse.AllZerosInsideUnitDisk`
- `Optics.DelayTransfer.ProperCausalOnePole.transform_impulseResponse_eq_response_eval`
- `Optics.DelayTransfer.ProperCausalOnePole.response_isSchurStable_iff_zTransform`
- `Optics.DelayTransfer.ProperCausalOnePole.isBIBOStable_iff_isSchurStable`
- `Optics.DelayTransfer.RationalNetlist.mem_frequencyResponseDomain_iff`
- `Optics.DelayTransfer.RationalNetlist.frequencyResponse_eq_formalDelay`
- `Optics.DelayTransfer.RationalNetlist.frequencyResponse_eq_reciprocalZ`
- `Optics.DelayTransfer.frequencyDelayEvaluation_quadrature`
- `Optics.DelayTransfer.unitCirclePoint_quadrature`
- `Optics.DelayTransfer.allPassRationalNetlist_frequency_quadrature_response_entry`
- `Optics.DelayTransfer.unstableOnePole_not_isBIBOStable`

## Cross-module conventions and reused results

- `ReducedRationalResponse` is only an abstract coprime quotient, and its evaluation, numerator
  roots, and denominator roots are defined in
  `Physlib/Optics/Systems/DelayTransfer/Poles.lean:122-154`. No network response certificate is
  present there; this slice preserves that narrowing.
- Formal Laplace evaluation is literally `q_i = exp (-s * τ_i)`, while reciprocal-Z evaluation is
  literally `q = z⁻¹`, in
  `Physlib/Optics/Systems/DelayTransfer/Basic.lean:225-239`.
- Laplace response-domain preimage and proof-gated response transport are reused from
  `Physlib/Optics/Systems/DelayTransfer/Evaluation.lean:320-394`.
- Reciprocal-Z response-domain preimage and proof-gated response transport are reused from
  `Physlib/Optics/Systems/DelayTransfer/Evaluation.lean:441-495`.
- N5F defines `responseDomain` as solve-domain membership intersected with stored component
  validity in `Physlib/Optics/Network/ParameterizedResponse.lean:436-472`. The two conditions are
  not collapsed in this slice.
- `IsAbsSummable`, `IsBoundedSeq`, `convolution`, `IsBIBOStable`, the unit-circle ROC sufficiency
  lemma, `candidatePoles`, and `IsSchurStable` are reused from
  `Physlib/Mathematics/ZTransform/Stability.lean:111-232`.
- The general result actually used for BIBO sufficiency is
  `isBIBOStable_of_sphere_subset_ROC` at
  `Physlib/Mathematics/ZTransform/Stability.lean:211-215`; no general converse is added.
- The causal geometric impulse response and its transform on `‖a‖ < ‖z‖` are reused from
  `Physlib/Mathematics/ZTransform/Convergence.lean:237-268`.
- The lag-one recurrence coefficient family is `onePoleFeedback` from
  `Physlib/Mathematics/ZTransform/DifferenceEquationRegression.lean:88-98`.
- The exact one-pole candidate set, Schur characterization, absolute-summability result, and
  unit-circle ROC theorem are reused from
  `Physlib/Mathematics/ZTransform/StabilityRegression.lean:82-130`. This is why production
  `Stability.lean` imports that existing S5 specialization instead of rederiving it.
- The necessity proof probes BIBO stability with the unit impulse and uses the independently
  proved right-identity formula from
  `Physlib/Mathematics/ZTransform/Convolution.lean:189-199`.
- The non-real all-pass frequency fixture reuses the already hand-solved compiled N5F anchor and
  mapped Laplace/reciprocal-Z anchors from
  `Physlib/Optics/Systems/DelayTransfer/EvaluationRegression.lean:1110-1237`.
- The audited source wording for all nonzero numerator roots inside the unit disk is quoted in
  `goal.md:2273-2278`. The API deliberately uses `AllZerosInsideUnitDisk`, not “resonance”.

## Non-claims

- Generic `ReducedRationalResponse` values remain abstract polynomial quotients. No declaration
  identifies their roots with zeros or actual poles of a selected N5F network response entry.
- No reachability, observability, hidden-mode, or network no-cancellation theorem is added.
- No Schur/BIBO equivalence is claimed for arbitrary proper causal rational responses. The exact
  equivalence is only for the named nonzero one-pole class `1 / (1 - a*q)`.
- No rational dependence on physical frequency is claimed, and no dispersion model is supplied.
- The choice `s = I*ω` is not presented as a bridge to the phasor layer's time convention.
- No passivity, physical resonance, DCDR topology, group-delay, or dispersion theorem is claimed.
- The local logarithmic-derivative extension remains slice 4 work.

## Gate record

The final post-sync chained build/lint gate and byte-identical `Physlib.lean` restoration are
recorded in the cutoff commit message/report after this note is committed.
