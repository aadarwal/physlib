# S4 delay-transfer slice 4 handoff

## Branch and synchronization

- Branch: `optics/s4-delay-transfer`
- Worktree: `/Users/aadarwal/src/aadarwal/physlib-wt/optics-s4-delay-transfer`
- Slice 4b is synchronized through `optics/development` head `f8e035ae` by merge commit
  `ae5c29e7`; the exact final post-sync gate head is recorded below.
- Slice 4 adds only the two new group-delay modules and refreshes this handoff note.

## Files and registrations requested

Register these modules in sorted order in `Physlib.lean`:

- `Physlib.Optics.Systems.DelayTransfer.GroupDelay`
- `Physlib.Optics.Systems.DelayTransfer.GroupDelayRegression`

Files:

- `Physlib/Optics/Systems/DelayTransfer/GroupDelay.lean`
- `Physlib/Optics/Systems/DelayTransfer/GroupDelayRegression.lean`

## Goal text implemented

This slice implements the literal S4P extension from `goal.md:2269-2271`:

> **Physlib extension (source claim unverified):** group delay and dispersion through a local
> logarithmic derivative or another branch-audited construction, not an unqualified global
> complex argument.

There is no additional named regression-row claim. The exact sign and nonzero-dispersion fixtures
audit this extension locally.

## Production declarations

### Scalar API in `Optics.DelayTransfer`

- `localLogDerivativeDomain`
- `localLogDerivative`
- `localGroupDelay`
- `localGroupDelayDispersionDomain`
- `localGroupDelayDispersion`
- `mem_localLogDerivativeDomain_iff`
- `eventually_ne_zero_of_mem_localLogDerivativeDomain`
- `mem_localLogDerivativeDomain_of_hasDerivAt`
- `localLogDerivative_eq_of_hasDerivAt`
- `localGroupDelay_eq_of_hasDerivAt`
- `localLogDerivative_eventuallyEq`
- `localLogDerivative_eq_of_eventuallyEq`
- `localGroupDelay_eventuallyEq`
- `localGroupDelay_eq_of_eventuallyEq`
- `mem_localGroupDelayDispersionDomain_iff`
- `localGroupDelayDispersion_eq_of_hasDerivAt`
- `localGroupDelayDispersion_eq_of_eventuallyEq`

### Network API in `Optics.DelayTransfer.RationalNetlist`

- `frequencyResponseEntry`
- `frequencyResponseEntry_eq`
- `frequencyResponseEntry_eq_zero`
- `frequencyGroupDelayDomain`
- `frequencyGroupDelay`
- `frequencyGroupDelayDispersionDomain`
- `frequencyGroupDelayDispersion`
- `mem_frequencyGroupDelayDomain_iff`
- `mem_frequencyGroupDelayDispersionDomain_iff`
- `frequencyResponseEntry_eventuallyEq_of_extension`
- `mem_frequencyGroupDelayDomain_of_extension`
- `frequencyGroupDelay_eq_of_extension_hasDerivAt`
- `mem_frequencyGroupDelayDispersionDomain_of_extension`
- `frequencyGroupDelayDispersion_eq_of_extension_hasDerivAt`

## Regression declarations

In `Optics.DelayTransfer`:

- `chirpedDelayResponse`
- `chirpedDelayResponse_ne_zero`
- `hasDerivAt_chirpedDelayResponse`
- `chirpedDelayResponse_localLogDerivativeDomain`
- `chirpedDelayResponse_localGroupDelay`
- `chirpedDelayResponse_localGroupDelayDispersionDomain`
- `chirpedDelayResponse_localGroupDelayDispersion`
- `pureDelay_groupDelay_three`
- `chirpedDelay_groupDelay_at_five`
- `chirpedDelay_dispersion_two_fifths`
- `zeroCrossingResponse`
- `zeroCrossing_not_mem_localLogDerivativeDomain`
- `groupDelayAllPassFrequencyParameters`
- `groupDelayAllPassFrequencyDelay`
- `groupDelayAllPassExtension`
- `groupDelayAllPassFrequencyDelay_norm`
- `groupDelayAllPassFrequencyParameters_isValid`
- `groupDelayAllPass_compiled_eq`
- `groupDelayAllPass_loopCoefficient`
- `groupDelayAllPass_denominator`
- `groupDelayAllPass_hasNonzeroDenominator`
- `groupDelayAllPass_throughTransfer_eq_extension`
- `groupDelayAllPass_frequencyDelayEvaluation`
- `groupDelayAllPassFormalDomain`
- `groupDelayAllPassFrequencyDomain`
- `groupDelayAllPassFrequencyInterior`
- `groupDelayAllPass_compiledResponse_eq_extension`
- `groupDelayAllPass_frequencyResponse_eq_extension`
- `hasDerivAt_groupDelayAllPassFrequencyDelay`
- `groupDelayAllPassFrequencyDelay_quadrature`
- `groupDelayAllPassExtension_quadrature`
- `groupDelayAllPassExtensionDerivative`
- `hasDerivAt_groupDelayAllPassExtension`
- `hasDerivAt_groupDelayAllPassExtension_quadrature`
- `groupDelayAllPassExtension_quadrature_ne_zero`
- `allPassRationalNetlist_frequencyGroupDelay_quadrature`

## Exact validation bindings

The validation lane should bind at least these public names:

- `Optics.DelayTransfer.localLogDerivativeDomain`
- `Optics.DelayTransfer.eventually_ne_zero_of_mem_localLogDerivativeDomain`
- `Optics.DelayTransfer.localGroupDelay`
- `Optics.DelayTransfer.mem_localGroupDelayDispersionDomain_iff`
- `Optics.DelayTransfer.RationalNetlist.mem_frequencyGroupDelayDomain_iff`
- `Optics.DelayTransfer.RationalNetlist.mem_frequencyGroupDelayDispersionDomain_iff`
- `Optics.DelayTransfer.RationalNetlist.frequencyGroupDelay_eq_of_extension_hasDerivAt`
- `Optics.DelayTransfer.RationalNetlist.frequencyGroupDelayDispersion_eq_of_extension_hasDerivAt`
- `Optics.DelayTransfer.chirpedDelayResponse_localGroupDelay`
- `Optics.DelayTransfer.chirpedDelayResponse_localGroupDelayDispersion`
- `Optics.DelayTransfer.pureDelay_groupDelay_three`
- `Optics.DelayTransfer.chirpedDelay_dispersion_two_fifths`
- `Optics.DelayTransfer.zeroCrossing_not_mem_localLogDerivativeDomain`
- `Optics.DelayTransfer.groupDelayAllPassFrequencyInterior`
- `Optics.DelayTransfer.groupDelayAllPass_compiledResponse_eq_extension`
- `Optics.DelayTransfer.groupDelayAllPass_frequencyResponse_eq_extension`
- `Optics.DelayTransfer.hasDerivAt_groupDelayAllPassExtension_quadrature`
- `Optics.DelayTransfer.allPassRationalNetlist_frequencyGroupDelay_quadrature`

The compiled anchor fixes `t = 3/5`, `κ = 4/5`, `a = 1/2`, unit delay, and
`ω₀ = π/2`. Its independently derived response and derivative are
`75/109 + (32/109) I` and `2912/11881 - (1920/11881) I`; its exact network group delay is
`2176/6649`.

## Cross-module conventions and reused results

- The selected frequency substitution is literally `q_i = exp (-I * omega * tau_i)`, and the
  reciprocal-Z unit-circle point uses the opposite exponential before inversion, in
  `Physlib/Optics/Systems/DelayTransfer/FrequencyResponse.lean:77-120`.
- `frequencyResponseDomain` is the exact preimage of the Laplace response domain, and
  `frequencyResponse` is proof-gated by membership in that set, in
  `Physlib/Optics/Systems/DelayTransfer/FrequencyResponse.lean:174-203`.
- Retained-entry regularity and network solvability are independent gates, as documented in
  `Physlib/Optics/Systems/DelayTransfer/Evaluation.lean:16-24`. This slice preserves both by using
  the existing `frequencyResponseDomain` and then requiring an interior point.
- Mathlib defines `deriv` to be the derivative when it exists and zero otherwise in
  `.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean:148-154`. Every physical
  interpretation here therefore has a separate named differentiability domain.
- Differentiability plus a nonzero value supplies an eventually nonzero germ through
  `ContinuousAt.eventually_ne`, defined in
  `.lake/packages/mathlib/Mathlib/Topology/Separation/Basic.lean:706-712`.
- The regression differentiates the displayed complex exponential with `HasDerivAt.cexp` from
  `.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ExpDeriv.lean:127-136`.
- The compiled regression fixture is defined in
  `Physlib/Optics/Systems/DelayTransfer/EvaluationRegression.lean:220-280`. Its solve helper at
  lines 845-912 expands `FlatNetlist.mem_behavior_iff_equations`, whose exact three equations are
  stated in `Physlib/Optics/Network/FlatNetlist.lean:487-503`.

## Totalized-versus-gated split

- `localLogDerivative`, `localGroupDelay`, and `localGroupDelayDispersion` are total functions.
  Their claimed meanings require `localLogDerivativeDomain` or
  `localGroupDelayDispersionDomain`, respectively.
- `frequencyResponseEntry` is zero outside the N5F proof-gated frequency-response domain. Its
  value is used for derivatives only at an interior domain point, so this arbitrary outside value
  is locally irrelevant.
- Network group delay additionally requires differentiability and a nonzero selected response
  entry. Network dispersion additionally requires differentiability of local group delay.
- General N5F interior differentiability is withheld. Both network formulas are conditional on
  user-supplied local regularity: an agreeing extension with `HasDerivAt` for the displayed
  derivative or derivatives. The all-pass regression supplies that regularity independently for
  its fixture.

## Non-claims

- No global `Complex.arg`, global phase branch, phase unwrap, or continuity-across-zeros result is
  supplied.
- No group-delay or dispersion interpretation is made outside the named domains.
- No rational dependence on physical frequency follows from the formal-delay model.
- No material-dispersion, time-domain causality, passivity, units, or source-parity theorem is
  claimed.
- The quantity named dispersion is literally the angular-frequency derivative of local group
  delay, not a constitutive material dispersion law.
- The network regression covers only the displayed compiled all-pass fixture; it is not a general
  regularity theorem for rational N5F networks.

## Gate record

At source head `ae5c29e7`, after synchronization onto development head `f8e035ae`, this single
locked command exited successfully with temporary sorted registrations:

```text
lake-lock env bash -c 'lake --wfail build <both group-delay modules> &&
  lake exe runPhyslibLinters && lake exe lint_all'
```

Both modules built with warnings as errors; `runPhyslibLinters` passed for Physlib and
QuantumInfo; and `lint_all` exited zero after registry coverage, legal-import, duplicate-tag,
sorry/pseudo-attribution, declaration-linter, and transitive-import checks. Its advisory style
and transitive-import inventories named only pre-existing repository files, with neither
group-delay module present. `Physlib.lean` was then restored byte-identically to SHA-256
`b481bad924b3229155e2d36fbb22303c5bd19b3bf1cc1d6b8423db83b3b1c010`.
