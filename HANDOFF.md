# S4 delay-transfer handoff

Branch: `optics/s4-delay-transfer`

## Registrations requested

Keep these imports sorted in `Physlib.lean`:

1. `Physlib.Optics.Systems.DelayTransfer.Basic`
2. `Physlib.Optics.Systems.DelayTransfer.Evaluation`
3. `Physlib.Optics.Systems.DelayTransfer.EvaluationRegression`
4. `Physlib.Optics.Systems.DelayTransfer.Poles`
5. `Physlib.Optics.Systems.DelayTransfer.PolesRegression`

## Slice 1: formal delays and evaluation

Files:

- `Physlib/Optics/Systems/DelayTransfer/Basic.lean`
- `Physlib/Optics/Systems/DelayTransfer/Evaluation.lean`
- `Physlib/Optics/Systems/DelayTransfer/EvaluationRegression.lean`

### Public declarations

`Optics.DelayTransfer.Basic`:

- `DelayTuple`, `DelayPolynomial`, `DelayRational`, `formalDelay`
- `RationalModel`
- `RationalModel.toRational`, `RationalModel.evaluationDomain`, `RationalModel.eval`
- `RationalModel.mem_evaluationDomain_iff`, `RationalModel.eval_eq`
- `RationalModel.eval_eq_of_toRational_eq`
- `RationalModel.ofPolynomial`, `RationalModel.constant`, `RationalModel.indeterminate`
- `RationalModel.evaluationDomain_ofPolynomial`, `RationalModel.eval_ofPolynomial`
- `RationalModel.eval_constant`, `RationalModel.eval_indeterminate`
- `RationalModel.toRational_indeterminate`
- `laplaceEvaluation`, `laplaceEvaluation_apply`
- `zInverseEvaluation`, `zInverseEvaluation_apply`

`Optics.DelayTransfer.Evaluation`:

- `RationalComponentFamily`
- `RationalComponentFamily.EntriesRegularAt`, `RationalComponentFamily.IsValidAt`
- `RationalComponentFamily.scattering`
- `RationalComponentFamily.toParameterizedComponentFamily`
- `RationalComponentFamily.toParameterizedComponentFamily_scattering_apply`
- `RationalComponentFamily.toParameterizedComponentFamily_isValidAt_iff`
- `RationalNetlist`
- `RationalNetlist.toParameterizedNetlist`
- `RationalNetlist.Channel`, `RationalNetlist.ConnectedChannel`
- `RationalNetlist.ExternalChannel`, `RationalNetlist.ExternalIncident`
- `RationalNetlist.ExternalOutgoing`, `RationalNetlist.compile`
- `RationalNetlist.solveDomain`, `RationalNetlist.responseDomain`
- `RationalNetlist.mem_compileBehavior_iff_unguardedResponse`
- `RationalNetlist.mem_compileBehavior_iff_response`
- `RationalNetlist.laplace`, `RationalNetlist.solveDomain_laplace`
- `RationalNetlist.responseDomain_laplace`, `RationalNetlist.unguardedResponse_laplace`
- `RationalNetlist.mem_compileBehavior_laplace_iff_unguardedResponse`
- `RationalNetlist.response_laplace`
- `RationalNetlist.reciprocalZ`, `RationalNetlist.solveDomain_reciprocalZ`
- `RationalNetlist.response_reciprocalZ`

`Optics.DelayTransfer.EvaluationRegression`:

- `allPassDelayModel`, `allPassDelayModel_eval`
- `mem_allPassDelayModel_evaluationDomain_iff`
- `allPassDelayModel_eq_throughTransfer`
- `allPassDelayModel_resonance_value`, `allPassDelayModel_resonance_agrees`
- `allPassDelayModel_antiresonance_value`, `allPassDelayModel_antiresonance_agrees`
- `allPassPropagationEntryModel`, `allPassPropagationEntryModel_eval`
- `allPassEvaluatedPropagationScattering`, `allPassEvaluatedPropagationScattering_eq`
- `allPassRationalComponents`, `allPassRationalNetlist`
- `allPassRationalComponents_scattering_coupler`
- `allPassRationalComponents_scattering_propagation`
- `allPassRationalComponents_scattering_eq`
- `allPassRationalNetlist_compile_eq`, `allPassRationalNetlist_scatteringTransform_eq`
- `allPassCompiledNetlist`
- `allPassRationalCouplerChannel`, `allPassRationalPropagationChannel`
- `allPassRationalInputChannel`, `allPassRationalThroughChannel`
- `allPassRationalInputAmplitude`, `allPassRationalInputAmplitude_apply_input`
- `allPassRationalCoupler_scatteringGraph_of_scatteringEquation`
- `allPassRationalPropagation_scatteringGraph_of_scatteringEquation`
- `allPassRational_scatteringEquation_coupler_rightFirst`
- `allPassRational_scatteringEquation_coupler_rightSecond`
- `allPassRational_scatteringEquation_propagation_right`
- `allPassRationalConnectedCouplerRightSecond`
- `allPassRationalConnectedPropagationLeft`, `allPassRationalConnectedPropagationRight`
- `allPassRationalConnectedCouplerLeftSecond`
- `allPassRationalConnectedCouplerRightSecond_embedding`
- `allPassRationalConnectedPropagationLeft_embedding`
- `allPassRationalConnectedPropagationRight_embedding`
- `allPassRationalConnectedCouplerLeftSecond_embedding`
- `allPassRationalConnectedCouplerRightSecond_mate`
- `allPassRationalConnectedPropagationLeft_mate`
- `allPassRationalConnectedPropagationRight_mate`
- `allPassRationalConnectedCouplerLeftSecond_mate`
- `allPassRational_incidentAssembly_apply_leftFirst`
- `allPassRational_incidentAssembly_apply_coupler_leftSecond`
- `allPassRational_incidentAssembly_apply_propagation_left`
- `allPassRational_outputReadout_apply_through`
- `allPassRationalNetlist_feedbackFixedPoint_eq_zero`
- `allPassRationalNetlist_isWellPosed`, `allPassRationalComponents_isValidAt`
- `allPassRationalNetlist_mem_responseDomain`
- `allPassRationalNetlist_responseThrough`, `allPassRationalNetlist_response_entry`
- `allPassRational_resonance_loopCoefficient`
- `allPassRational_resonance_hasNonzeroDenominator`, `allPassRationalResonanceDomain`
- `allPassRationalNetlist_resonance_response_entry`
- `allPassRational_antiresonance_isValid`
- `allPassRational_antiresonance_loopCoefficient`
- `allPassRational_antiresonance_hasNonzeroDenominator`
- `allPassRationalAntiresonanceDomain`
- `allPassRationalNetlist_antiresonance_response_entry`
- `allPassRationalQuadratureParameters`, `allPassRational_quadrature_isValid`
- `allPassRational_quadrature_loopCoefficient`
- `allPassRational_quadrature_denominator`
- `allPassRational_quadrature_hasNonzeroDenominator`
- `allPassRational_quadrature_throughTransfer`, `allPassRationalQuadratureDomain`
- `allPassRationalNetlist_quadrature_response_entry`
- `laplaceEvaluation_quadrature`, `zInverseEvaluation_quadrature`

### Goal rows and contract clauses

- S4: finite formal delay family, rational component entries, retained denominator domains,
  presentation-independent evaluation on common regular domains, Laplace substitution, and
  direct N5F compile/eliminate commutation.
- N-10: `RationalNetlist.mem_compileBehavior_laplace_iff_unguardedResponse` is the direct
  specialization; no elimination proof is duplicated.
- T-05: `RationalNetlist.response_reciprocalZ` records the selected `q = z⁻¹` convention.
- S-02 cross-regression: an actual `RationalNetlist` with constant N7 coupler entries, formal
  propagation entries, and the exact S2 wiring compiles to the S2 network. Its response is solved
  from the compiled channel equations at both named S2 points.
- Convention regression: the compiled network has response `75/109 + (32/109) I` at `q = -I`;
  both `q = exp (-s*τ)` at `s = I*pi/2`, `τ = 1` and `q = z⁻¹` at `z = I` produce that point.

### Exact public validation anchors

- `Optics.DelayTransfer.RationalModel.eval_eq_of_toRational_eq`
- `Optics.DelayTransfer.allPassRationalNetlist`
- `Optics.DelayTransfer.allPassRationalNetlist_compile_eq`
- `Optics.DelayTransfer.allPassRationalNetlist_response_entry`
- `Optics.DelayTransfer.allPassRationalNetlist_resonance_response_entry`
- `Optics.DelayTransfer.allPassRationalNetlist_antiresonance_response_entry`
- `Optics.DelayTransfer.allPassRationalNetlist_quadrature_response_entry`
- `Optics.DelayTransfer.laplaceEvaluation_quadrature`
- `Optics.DelayTransfer.zInverseEvaluation_quadrature`

### Quoted cross-module conventions

- `Physlib/Optics/Network/ParameterizedResponse.lean:436-441` calls `solveDomain` the parameters
  where the compiled network is well posed and states that it records no component-validity claim.
- `Physlib/Optics/Network/ParameterizedResponse.lean:458-465` defines `responseDomain` as the
  intersection of `solveDomain` and the component validity domain.
- `Physlib/Optics/Network/ParameterizedResponse.lean:576-590` states and proves compile/eliminate
  commutation on `solveDomain`; the Slice 1 bridge invokes that lemma directly.
- `Physlib/Optics/Network/ParameterizedResponse.lean:640-654` defines reparameterized solve and
  response domains as preimages and makes proof-gated response commutation definitional.
- `Physlib/Optics/Systems/Microring/AllPass.lean:114-146` defines the loop coefficient, loop gain,
  denominator, and exact nonzero-denominator solve gate used by the regression bridge.
- `Physlib/Optics/Systems/Microring/AllPass.lean:164-188` defines the totalized transfer and proves
  its standard `(t - gamma) / (1 - t*gamma)` form only under unitary and solve hypotheses.
- `Physlib/Optics/Systems/Microring/AllPass.lean:200-239` defines the coupler/propagation component
  labels, their N7 port families, and their two physical scattering matrices.
- `Physlib/Optics/Systems/Microring/AllPass.lean:258-300` defines the two connection labels, the
  exact coupler-to-propagation feedback pairs, and the resulting flat netlist.
- `Physlib/Optics/Systems/Microring/AllPass.lean:539-625` gives the N7 coupler and propagation
  coordinate laws reused to hand-expand the compiled fixture's local scattering equations.
- `Physlib/Optics/Systems/Microring/AllPass.lean:1034-1049` gives the fixed-point injectivity
  argument reused only after the rational fixture establishes its own compiled channel equations.
- `Physlib/Optics/Systems/Microring/AllPassRegression.lean:62-99` supplies the zero-phase S2
  parameters and exact value `1 / 7`.
- `Physlib/Optics/Systems/Microring/AllPassRegression.lean:219-248` supplies the half-turn S2
  parameters and exact value `11 / 13`.

### Non-claims

- Delay variables are formal; no rational dependence on physical frequency is asserted.
- Symbolic rational elimination of the external response is future work. Slice 1 evaluates
  retained component presentations pointwise into N5F; it does not construct the eliminated
  response as a `DelayRational` or `RationalModel`.
- Totalized division outside a retained denominator domain has no transfer interpretation.
- At `z = 0`, totalized `zInverseEvaluation` has no reciprocal-Z interpretation.
- Retained-entry regularity and `solveDomain` are independent. Regular entries need not make the
  feedback operator invertible, and a removable retained denominator can exclude an otherwise
  well-posed evaluated network.
- `solveDomain` and `responseDomain` remain distinct.
- No candidate-pole/actual-pole identification, stability, causality, physical resonance,
  group-delay, dispersion, or global-phase result is claimed in Slice 1.

### Required later slice

Construct symbolic external-response entries over the delay fraction field via determinant and
adjugate, following the entrywise matrix pattern in
`Physlib/Mathematics/LinearAlgebra/Matrix/Analytic.lean:17-27,74-117`, and include an independent
hand-expanded network fixture. Until that slice lands, the S4 bullet “rational transfer functions
for finite-delay linear networks” is explicitly withheld.

### Gates

- Synced onto `optics/development` commit `af062790` in merge commit `afbd7baa` before cutoff.
- All five registered delay-transfer modules, direct Lean checks with
  `-DwarningAsError=true`, the temporary-registry `Physlib` target, and
  `lake exe runPhyslibLinters` passed in one locked chain.
- The same chain found no `DelayTransfer` style or redundant-import finding, and
  `check_file_imports` reported that all registered files were imported correctly.
- `Physlib.lean` was restored byte-identically to SHA-256
  `ad2036c829a114b2a4e18d1035ecb1a30452724b474bd8c6fe038df8fbf5d5cd`.

## Slice 2: candidate singularities and reduced poles

Files:

- `Physlib/Optics/Systems/DelayTransfer/Poles.lean`
- `Physlib/Optics/Systems/DelayTransfer/PolesRegression.lean`

### Public declarations

`Optics.DelayTransfer.Poles`:

- `RationalNetlist.internalDeterminant`
- `InternalDeterminantPolynomial`
- `InternalDeterminantPolynomial.candidateSingularities`
- `InternalDeterminantPolynomial.mem_candidateSingularities_iff`
- `ReducedRationalResponse`
- `ReducedRationalResponse.evaluationDomain`, `ReducedRationalResponse.eval`
- `ReducedRationalResponse.zeros`, `ReducedRationalResponse.poles`
- `ReducedRationalResponse.numerator_ne_zero_of_mem_poles`
- `RationalReduction`
- `RationalReduction.candidatePoles`, `RationalReduction.actualPoles`
- `RationalReduction.NoPoleCancellation`, `RationalReduction.rawDenominator_ne_zero`
- `RationalReduction.actualPoles_subset_candidatePoles`
- `RationalReduction.candidatePoles_subset_actualPoles`
- `RationalReduction.candidatePoles_eq_actualPoles`
- `RationalReduction.actualPoles_subset_candidateSingularities`
- `RationalReduction.candidateSingularities_subset_actualPoles`
- `recurrenceDenominator`, `eval_recurrenceDenominator`
- `reciprocalCandidatePoles`, `recurrenceCandidatePoles_eq`

`Optics.DelayTransfer.PolesRegression`:

- `cancellationRegressionReduced`, `cancellationRegression`
- `cancellationRegression_candidate_not_actual`
- `cancellationRegression_not_noPoleCancellation`
- `cancellationRegression_not_candidatePoles_subset_actualPoles`

### Goal rows and contract clauses

- S4/S4P: internal determinant roots are candidate singularities; reduced denominator roots are
  actual transfer poles after explicit cancellation.
- S4P: actual poles are unconditionally candidates, while the converse requires the explicit
  `NoPoleCancellation` hypothesis.
- S4P negative control: the fully cancelled `(q - 1) / (q - 1)` fixture invalidates an ungated
  candidate-to-actual converse.
- T-02 support: `recurrenceCandidatePoles_eq` identifies the existing finite-recurrence
  candidate set with reciprocal roots of the one-delay polynomial denominator.

### Quoted cross-module conventions

- `Physlib/Optics/Network/ParameterizedResponse.lean:453-456` identifies N5F algebraic
  well-posedness with nonvanishing of the internal feedback-operator determinant.
- `Physlib/Mathematics/ZTransform/Stability.lean:223-227` defines recurrence candidate poles as
  nonzero `z` values where `1 - delaySymbol s α z⁻¹` vanishes and explicitly withholds the
  actual-pole claim when the numerator may also vanish.

### Non-claims

- A candidate internal singularity is not automatically an actual transfer pole.
- No reachability or observability theorem is inferred; `NoPoleCancellation` is an explicit
  sufficient algebraic hypothesis.
- No candidate or numerator root is called a physical resonance.
- No rational-in-frequency, stability, BIBO, causality, passivity, frequency-response,
  group-delay, or dispersion claim is made in Slice 2.

### Gates

Pending the post-sync chained Slice 2 gate; the registry will be restored byte-for-byte afterward.
