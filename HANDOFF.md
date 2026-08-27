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

## Verbatim ledger row

`PARITY-LEDGER.md` @ `054b294fbaf2d7769aa570fae9c6aa5c0b2b8da7`:

```text
| ZT-06 | ITP'14 Defs. 11–13 + Thms. 12–13 p. 494–496: IIR model, causality condition, `IIR_ROC` (ROC minus poles), transfer function, frequency response | **PARTIAL — and the split matters.** Covered: `transferFunction` (`Physlib/Mathematics/ZTransform/DifferenceEquation.lean:273` @ `110eb5cd`), `iirROC` (`:278`, the ROC intersection minus denominator zeros), and the IIR transfer law `transform_eq_transferFunction_mul` (`:283`) with its ROC-membership form `…_of_mem_iirROC` (`:292`). **NOT covered: Thm. 13, the IIR frequency response at `z = e^{jω}` with its magnitude/argument decomposition — there is no such declaration in the generic `ZTransform` layer.** A `frequencyResponse` DOES exist at `Physlib/Optics/Systems/DelayTransfer/FrequencyResponse.lean`, but that is the optics delay-transfer object of **IP-64** (`q = e^{−sτ} = z⁻¹`), a different construction at a different layer; **matching it to ITP'14 Thm. 13 on the strength of the name would be exactly the cross-layer confusion this ledger exists to prevent** — **on `optics/development` @ `110eb5cd`** | `HD α_lst = 0` structural constraint; `z = e^{jω}` for frequency response | Retained all four hypotheses of Thm. 12 | **PARTIALLY proved and GATED on `optics/development` @ `110eb5cd`** — Defs. 11–13 and Thm. 12 discharged; **Thm. 13 (frequency response) still WITHHELD**. Regression **T-04**. **INTEGRITY NOTE — this row was STALE and is corrected 2026-08-27.** It read *"TBD — not yet formalized"* while its target already existed. Found by A7's regression index, verified here against the tree, and cited at `110eb5cd`. **It went stale invisibly:** `tools/sweep.py` exempts any row whose lean cell contains `TBD` from the location-ref check, so no check was ever looking at it — the exemption is now reported rather than silent. **S8 TRIAGE 2026-08-27 — OPEN**, smallest named slice: named in the triage. Implementation proceeds on the S8 lane in the triage's §8 order. | parity |
```
