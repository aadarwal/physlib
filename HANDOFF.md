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
- `RationalNetlist.laplace`, `RationalNetlist.laplaceExternalChannelEquiv`
- `RationalNetlist.solveDomain_laplace`
- `RationalNetlist.responseDomain_laplace`, `RationalNetlist.unguardedResponse_laplace`
- `RationalNetlist.mem_compileBehavior_laplace_iff_unguardedResponse`
- `RationalNetlist.response_laplace`, `RationalNetlist.response_laplace_reindex`
- `RationalNetlist.response_laplace_reindex_of_evaluation_eq`
- `RationalNetlist.reciprocalZ`, `RationalNetlist.reciprocalZExternalChannelEquiv`
- `RationalNetlist.solveDomain_reciprocalZ`, `RationalNetlist.responseDomain_reciprocalZ`
- `RationalNetlist.response_reciprocalZ`, `RationalNetlist.response_reciprocalZ_reindex`
- `RationalNetlist.response_reciprocalZ_reindex_of_evaluation_eq`

`Optics.DelayTransfer.EvaluationRegression`:

- `allPassDelayModel`, `allPassDelayModel_eval`
- `mem_allPassDelayModel_evaluationDomain_iff`
- `allPassDelayModel_eq_throughTransfer`
- `allPassDelayModel_resonance_value`, `allPassDelayModel_resonance_agrees`
- `allPassDelayModel_antiresonance_value`, `allPassDelayModel_antiresonance_agrees`
- `allPassPropagationEntryModel`, `allPassPropagationEntryModel_eval`
- `allPassEvaluatedPropagationScattering`, `allPassEvaluatedPropagationScattering_eq`
- `allPassRationalComponents`, `allPassRationalNetlist`
- `allPassRationalFormalInputChannel`, `allPassRationalFormalThroughChannel`
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
- `allPassRationalNetlistLaplaceQuadratureDomain`
- `allPassRationalNetlist_laplace_quadrature_response_entry`
- `allPassRationalNetlistReciprocalZQuadratureDomain`
- `allPassRationalNetlist_reciprocalZ_quadrature_response_entry`

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
- Convention regression: the compiled network has response `75/109 + (32/109) I` at `q = -I`.
  The proof-gated `.laplace` response at `s = I*pi/2`, `τ = 1` and proof-gated
  `.reciprocalZ` response at `z = I` both transport through the actual reparameterized netlists
  to that compiled anchor.

### Exact public validation anchors

- `Optics.DelayTransfer.RationalModel.eval_eq_of_toRational_eq`
- `Optics.DelayTransfer.RationalNetlist.response_laplace_reindex_of_evaluation_eq`
- `Optics.DelayTransfer.RationalNetlist.response_reciprocalZ_reindex_of_evaluation_eq`
- `Optics.DelayTransfer.allPassRationalNetlist`
- `Optics.DelayTransfer.allPassRationalNetlist_compile_eq`
- `Optics.DelayTransfer.allPassRationalNetlist_response_entry`
- `Optics.DelayTransfer.allPassRationalNetlist_resonance_response_entry`
- `Optics.DelayTransfer.allPassRationalNetlist_antiresonance_response_entry`
- `Optics.DelayTransfer.allPassRationalNetlist_quadrature_response_entry`
- `Optics.DelayTransfer.laplaceEvaluation_quadrature`
- `Optics.DelayTransfer.zInverseEvaluation_quadrature`
- `Optics.DelayTransfer.allPassRationalNetlist_laplace_quadrature_response_entry`
- `Optics.DelayTransfer.allPassRationalNetlist_reciprocalZ_quadrature_response_entry`

### Quoted cross-module conventions

- `Physlib/Optics/Network/ParameterizedResponse.lean:436-441` calls `solveDomain` the parameters
  where the compiled network is well posed and states that it records no component-validity claim.
- `Physlib/Optics/Network/ParameterizedResponse.lean:458-465` defines `responseDomain` as the
  intersection of `solveDomain` and the component validity domain.
- `Physlib/Optics/Network/ParameterizedResponse.lean:576-590` states and proves compile/eliminate
  commutation on `solveDomain`; the Slice 1 bridge invokes that lemma directly.
- `Physlib/Optics/Network/ParameterizedResponse.lean:640-654` defines reparameterized solve and
  response domains as preimages and makes proof-gated response commutation definitional.
- `Physlib/Optics/Network/ParameterizedResponse.lean:525-527` proves that a response is
  independent of the supplied proof of membership in its fixed response domain.
- `Physlib/Optics/Network/Port.lean:144-151,236-243` lifts unchanged external-channel labels to
  incident and outgoing coordinate equivalences.
- `Physlib/Optics/Mode/Reindex.lean:85-94` defines response-matrix reindexing and its entry law;
  the mapped anchors use it to expose the unchanged external coordinates explicitly.
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
- No degree or finiteness bound for an eliminated response is proved in Slice 1.
- No candidate-pole/actual-pole identification, stability, causality, physical resonance,
  group-delay, dispersion, or global-phase result is claimed in Slice 1.

### Required later slice

Construct symbolic external-response entries over the delay fraction field via determinant and
adjugate, following the entrywise matrix pattern in
`Physlib/Mathematics/LinearAlgebra/Matrix/Analytic.lean:17-27,74-117`, and include an independent
hand-expanded network fixture. Until that slice lands, the S4 bullet “rational transfer functions
for finite-delay linear networks” is explicitly withheld.

### Gates

- Synced onto `optics/development` commit `8db20f71` in merge commit `d1f5e200` before cutoff.
- All five registered delay-transfer modules, direct Lean checks with
  `-DwarningAsError=true`, the temporary-registry `Physlib` target, and
  `lake exe runPhyslibLinters` passed in one locked chain.
- The same chain found no `DelayTransfer` style or redundant-import finding, and
  `check_file_imports` reported that all registered files were imported correctly.
- `Physlib.lean` was restored byte-identically to SHA-256
  `33525d318799c01166c4127080c99ddccae55cb1a3f204a6c183650e7c931d2e`.

## Slice 2: candidate singularities and abstract polynomial cancellation

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
- `RationalReduction.rawDenominatorRoots`, `RationalReduction.reducedPoles`
- `RationalReduction.NoPoleCancellation`, `RationalReduction.rawDenominator_ne_zero`
- `RationalReduction.reducedPoles_subset_rawDenominatorRoots`
- `RationalReduction.rawDenominatorRoots_subset_reducedPoles`
- `RationalReduction.rawDenominatorRoots_eq_reducedPoles`
- `recurrenceDenominator`, `eval_recurrenceDenominator`
- `reciprocalCandidatePoles`, `recurrenceCandidatePoles_eq`

`Optics.DelayTransfer.PolesRegression`:

- `cancellationRegressionReduced`, `cancellationRegression`
- `cancellationRegression_raw_root_not_reduced`
- `cancellationRegression_not_noPoleCancellation`
- `cancellationRegression_not_rawRoots_subset_reducedPoles`

### Goal rows and contract clauses

- “singular internal operators as candidate poles”: `InternalDeterminantPolynomial` certifies an
  actual N5F feedback-operator determinant, whose roots are candidate singularities only.
- “reduced rational responses and their evaluation domains; zeros and transfer-function poles
  after cancellation, distinct from candidate singularities”: only the abstract polynomial
  reduction schema is supplied here. Its numerator is not certified to a network response, so
  the transfer-function-pole part remains withheld with symbolic response elimination.
- Abstract-schema negative control: the fully cancelled `(q - 1) / (q - 1)` fixture has a raw
  denominator root that is absent after reduction. The pointwise `NoPoleCancellation q` gate is
  exactly what preserves a raw root at that `q`.
- T-02 support: `recurrenceCandidatePoles_eq` identifies the existing finite-recurrence
  candidate set with reciprocal roots of the one-delay polynomial denominator.

### Exact public validation anchors

- `Optics.DelayTransfer.InternalDeterminantPolynomial.candidateSingularities`
- `Optics.DelayTransfer.RationalReduction.reducedPoles_subset_rawDenominatorRoots`
- `Optics.DelayTransfer.RationalReduction.rawDenominatorRoots_subset_reducedPoles`
- `Optics.DelayTransfer.cancellationRegression_raw_root_not_reduced`
- `Optics.DelayTransfer.cancellationRegression_not_noPoleCancellation`
- `Optics.DelayTransfer.cancellationRegression_not_rawRoots_subset_reducedPoles`
- `Optics.DelayTransfer.recurrenceCandidatePoles_eq`

### Quoted cross-module conventions

- `Physlib/Optics/Network/ParameterizedResponse.lean:453-456` identifies N5F algebraic
  well-posedness with nonvanishing of the internal feedback-operator determinant.
- `Physlib/Mathematics/ZTransform/Stability.lean:223-227` defines recurrence candidate poles as
  nonzero `z` values where `1 - delaySymbol s α z⁻¹` vanishes and explicitly withholds the
  actual-pole claim when the numerator may also vanish.

### Non-claims

- A candidate internal singularity is not automatically an actual transfer pole.
- No theorem relates `ReducedRationalResponse` or `RationalReduction` to a selected N5F response
  entry. Their numerator, quotient, and reduced denominator roots are abstract polynomial data.
- A response-indexed quotient certificate and a genuine singular-but-cancelled netlist fixture
  remain future work after symbolic external-response elimination.
- No reachability or observability theorem is inferred. `NoPoleCancellation q` is only the
  pointwise sufficient criterion for the abstract raw denominator root at `q` to survive.
- No candidate or numerator root is called a physical resonance.
- No degree or finiteness bound is proved in Slice 2.
- No rational-in-frequency, stability, BIBO, causality, passivity, frequency-response,
  group-delay, or dispersion claim is made in Slice 2.

### Gates

- The post-sync Slice 1c chain built both pole modules with warnings as errors, built the
  temporary-registry `Physlib` target, and passed `runPhyslibLinters` and `check_file_imports`.
- The same chain found no `DelayTransfer` style, shell-style, or redundant-import finding.
- `Physlib.lean` was restored byte-identically to SHA-256
  `33525d318799c01166c4127080c99ddccae55cb1a3f204a6c183650e7c931d2e`.
