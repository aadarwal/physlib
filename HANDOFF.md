# HANDOFF

- Branch: `optics/s8-tbd`
- Gated source: `d18001a2c0817ac0826e8ded57cb00be3c6666e7`
- Source parent: `718aa5486c98bde98735493178bf08f2d909a4b7` (cleared slice-2 HANDOFF child)
- Production file: `Physlib/Mathematics/ZTransform/FrequencyResponse.lean`
- Regression file: `Physlib/Mathematics/ZTransform/FrequencyResponseRegression.lean`
- Parity input: ledger row `ZT-06` read at live parity head
  `054b294fbaf2d7769aa570fae9c6aa5c0b2b8da7`.

## Registration requested

Add these sorted imports to `Physlib.lean` after
`Physlib.Mathematics.ZTransform.ExistenceRegression` and before
`Physlib.Mathematics.ZTransform.Inverse`:

```lean
public import Physlib.Mathematics.ZTransform.FrequencyResponse
public import Physlib.Mathematics.ZTransform.FrequencyResponseRegression
```

Production imports only `Physlib.Mathematics.ZTransform.DifferenceEquation`; it does not import
the regression. The regression is a leaf importing the production module.

## Production declarations

- `Physlib.ZTransform.unitCirclePoint` —
  `Physlib/Mathematics/ZTransform/FrequencyResponse.lean:80` @ `d18001a2c0817ac0826e8ded57cb00be3c6666e7`
- `Physlib.ZTransform.norm_unitCirclePoint` —
  `Physlib/Mathematics/ZTransform/FrequencyResponse.lean:85` @ `d18001a2c0817ac0826e8ded57cb00be3c6666e7`
- `Physlib.ZTransform.unitCirclePoint_ne_zero` —
  `Physlib/Mathematics/ZTransform/FrequencyResponse.lean:90` @ `d18001a2c0817ac0826e8ded57cb00be3c6666e7`
- `Physlib.ZTransform.unitCirclePoint_inv` —
  `Physlib/Mathematics/ZTransform/FrequencyResponse.lean:94` @ `d18001a2c0817ac0826e8ded57cb00be3c6666e7`
- `Physlib.ZTransform.unitCirclePoint_inv_pow` —
  `Physlib/Mathematics/ZTransform/FrequencyResponse.lean:99` @ `d18001a2c0817ac0826e8ded57cb00be3c6666e7`
- `Physlib.ZTransform.delayCosineSum` —
  `Physlib/Mathematics/ZTransform/FrequencyResponse.lean:120` @ `d18001a2c0817ac0826e8ded57cb00be3c6666e7`
- `Physlib.ZTransform.delaySineSum` —
  `Physlib/Mathematics/ZTransform/FrequencyResponse.lean:124` @ `d18001a2c0817ac0826e8ded57cb00be3c6666e7`
- `Physlib.ZTransform.frequencyNumerator` —
  `Physlib/Mathematics/ZTransform/FrequencyResponse.lean:128` @ `d18001a2c0817ac0826e8ded57cb00be3c6666e7`
- `Physlib.ZTransform.frequencyDenominator` —
  `Physlib/Mathematics/ZTransform/FrequencyResponse.lean:132` @ `d18001a2c0817ac0826e8ded57cb00be3c6666e7`
- `Physlib.ZTransform.delaySymbol_unitCircle` —
  `Physlib/Mathematics/ZTransform/FrequencyResponse.lean:137` @ `d18001a2c0817ac0826e8ded57cb00be3c6666e7`
- `Physlib.ZTransform.one_sub_delaySymbol_unitCircle` —
  `Physlib/Mathematics/ZTransform/FrequencyResponse.lean:154` @ `d18001a2c0817ac0826e8ded57cb00be3c6666e7`
- `Physlib.ZTransform.transferFunction_unitCircle` —
  `Physlib/Mathematics/ZTransform/FrequencyResponse.lean:168` @ `d18001a2c0817ac0826e8ded57cb00be3c6666e7`
- `Physlib.ZTransform.transferFunction_unitCircle_norm` —
  `Physlib/Mathematics/ZTransform/FrequencyResponse.lean:176` @ `d18001a2c0817ac0826e8ded57cb00be3c6666e7`
- `Physlib.ZTransform.transferFunction_unitCircle_polar` —
  `Physlib/Mathematics/ZTransform/FrequencyResponse.lean:183` @ `d18001a2c0817ac0826e8ded57cb00be3c6666e7`
- `Physlib.ZTransform.frequencyDenominator_ne_zero_of_mem_iirROC` —
  `Physlib/Mathematics/ZTransform/FrequencyResponse.lean:199` @ `d18001a2c0817ac0826e8ded57cb00be3c6666e7`
- `Physlib.ZTransform.transform_div_unitCircle_polar` —
  `Physlib/Mathematics/ZTransform/FrequencyResponse.lean:207` @ `d18001a2c0817ac0826e8ded57cb00be3c6666e7`

## Regression declarations

- `Physlib.ZTransform.quadratureFeedforward` —
  `Physlib/Mathematics/ZTransform/FrequencyResponseRegression.lean:56` @ `d18001a2c0817ac0826e8ded57cb00be3c6666e7`
- `Physlib.ZTransform.quadratureFeedback` —
  `Physlib/Mathematics/ZTransform/FrequencyResponseRegression.lean:60` @ `d18001a2c0817ac0826e8ded57cb00be3c6666e7`
- `Physlib.ZTransform.delaySymbol_quadratureFeedforward` —
  `Physlib/Mathematics/ZTransform/FrequencyResponseRegression.lean:64` @ `d18001a2c0817ac0826e8ded57cb00be3c6666e7`
- `Physlib.ZTransform.delaySymbol_quadratureFeedback` —
  `Physlib/Mathematics/ZTransform/FrequencyResponseRegression.lean:69` @ `d18001a2c0817ac0826e8ded57cb00be3c6666e7`
- `Physlib.ZTransform.quadratureUnitCirclePoint` —
  `Physlib/Mathematics/ZTransform/FrequencyResponseRegression.lean:81` @ `d18001a2c0817ac0826e8ded57cb00be3c6666e7`
- Private proof helper `one_add_I_half_ne_zero` —
  `Physlib/Mathematics/ZTransform/FrequencyResponseRegression.lean:85` @ `d18001a2c0817ac0826e8ded57cb00be3c6666e7`
- Private proof helper `one_sub_I_half_ne_zero` —
  `Physlib/Mathematics/ZTransform/FrequencyResponseRegression.lean:90` @ `d18001a2c0817ac0826e8ded57cb00be3c6666e7`
- Private proof helper `two_add_I_ne_zero` —
  `Physlib/Mathematics/ZTransform/FrequencyResponseRegression.lean:95` @ `d18001a2c0817ac0826e8ded57cb00be3c6666e7`
- Private proof helper `two_sub_I_ne_zero` —
  `Physlib/Mathematics/ZTransform/FrequencyResponseRegression.lean:100` @ `d18001a2c0817ac0826e8ded57cb00be3c6666e7`
- `Physlib.ZTransform.transferFunction_quadrature` —
  `Physlib/Mathematics/ZTransform/FrequencyResponseRegression.lean:107` @ `d18001a2c0817ac0826e8ded57cb00be3c6666e7`
- `Physlib.ZTransform.transferFunction_wrongUnitCircleSign_ne` —
  `Physlib/Mathematics/ZTransform/FrequencyResponseRegression.lean:119` @ `d18001a2c0817ac0826e8ded57cb00be3c6666e7`

## Source correspondence and anchor

- `unitCirclePoint` uses a real angular frequency and is proved to have norm one.
- `delaySymbol_unitCircle` derives the `cos - I sin` expansion from the exponential and finite
  delay-symbol primitives.
- `transform_div_unitCircle_polar` uses the source lag ranges `Finset.Icc 0 N` and
  `Finset.Icc 1 M`; the latter encodes the stipulated zero leading feedback coefficient.
- Its hypotheses retain causal input and output, IIR-ROC membership, a nonzero input transform,
  and the recurrence model. Its first proof step is
  `transform_eq_transferFunction_mul_of_mem_iirROC`; the transform quotient is not introduced by
  definition.
- `frequencyDenominator_ne_zero_of_mem_iirROC` extracts the denominator gate from IIR-ROC
  membership before the polar transfer lemma is applied.
- The magnitude is the norm quotient and the phase is `Complex.arg` of the expanded quotient,
  matching the formal source statement for complex coefficients.

## Hostile regression

At `ω = π / 2`, the primitive fixture has feedforward symbol `1 + 2u`, feedback symbol `u / 2`,
and transfer value `-2I` because the delay variable is the reciprocal point `-I`.
`transferFunction_wrongUnitCircleSign_ne` substitutes `I` instead and proves the two values differ.
It unfolds `transferFunction`, `delaySymbol`, `unitCirclePoint`, and both coefficient definitions;
it does not call any production unit-circle or polar theorem.

## Pre-existing-line and registration accounting

The source delta `718aa5486c98bde98735493178bf08f2d909a4b7` →
`d18001a2c0817ac0826e8ded57cb00be3c6666e7` adds exactly the two new modules. It changes zero
pre-existing production, regression, import, or documentation lines.

The two requested imports were added to `Physlib.lean` only temporarily for the root gate and then
removed. Byte-identical restoration was checked:

- SHA-256: `f7486c686c1d5087c1cb8a87f33b3af2dd11cb761b14fa0ebbc0a0e9489d0a20`
- Git blob: `8d3318db883c44b5d1c55fe28ef599fb1fc10ad5`

The only change in the child after the gated source is this replacement `HANDOFF.md`.

## Gates

- `lake-lock build Physlib.Mathematics.ZTransform.FrequencyResponse
  Physlib.Mathematics.ZTransform.FrequencyResponseRegression`: pass at the exact cutoff.
- Temporary sorted registration followed by `lake-lock build Physlib`: pass,
  `Build completed successfully (5013 jobs)`.
- `lake-lock exe check_file_imports`: pass.
- `lake-lock exe sorry_lint`: pass.
- `lake-lock exe runPhyslibLinters`: pass for Physlib and QuantumInfo.
- `lake-lock exe lint_all`: exit 0; no finding names either new module.
- `lake-lock exe module_doc_lint`: repository baseline 147 error headings; zero findings for either
  new module.
- `./scripts/lint-style.sh`: pass.
- `git diff --check`: pass.

## Milestone

ITP'14 Thm. 13 IIR frequency-response identity added; ZT-06 moves PARTIAL -> discharged on merge.
