# S4 delay-transfer handoff

Branch: `optics/s4-delay-transfer`

## Registrations requested

Keep these imports sorted in `Physlib.lean`:

1. `Physlib.Optics.Systems.DelayTransfer.Basic`
2. `Physlib.Optics.Systems.DelayTransfer.Evaluation`
3. `Physlib.Optics.Systems.DelayTransfer.EvaluationRegression`

Later slices append further modules to this list.

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

### Goal rows and contract clauses

- S4: finite formal delay family, rational component entries, retained denominator domains,
  Laplace substitution, and direct N5F compile/eliminate commutation.
- N-10: `RationalNetlist.mem_compileBehavior_laplace_iff_unguardedResponse` is the direct
  specialization; no elimination proof is duplicated.
- T-05: `RationalNetlist.response_reciprocalZ` records the selected `q = z⁻¹` convention.
- S-02 cross-regression: the rational one-delay all-pass response agrees at both named S2 points.

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
- `Physlib/Optics/Systems/Microring/AllPassRegression.lean:62-99` supplies the zero-phase S2
  parameters and exact value `1 / 7`.
- `Physlib/Optics/Systems/Microring/AllPassRegression.lean:219-248` supplies the half-turn S2
  parameters and exact value `11 / 13`.

### Non-claims

- Delay variables are formal; no rational dependence on physical frequency is asserted.
- Totalized division outside a retained denominator domain has no transfer interpretation.
- `solveDomain` and `responseDomain` remain distinct.
- No candidate-pole/actual-pole identification, stability, causality, physical resonance,
  group-delay, dispersion, or global-phase result is claimed in Slice 1.

### Gates

Pending the post-sync chained Slice 1 gate; the registry will be restored byte-for-byte afterward.
