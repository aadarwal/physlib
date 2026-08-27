# HANDOFF

- Branch: `optics/s8-tbd`
- Gated source: `8e72d04953eed17baa7f6a08f35b8cfee218b31a`
- Source parent: `5ac9c10473b2de1ca8059c9ab5a13d13ada6bf9d` (cleared slice-3 HANDOFF child)
- Production file: `Physlib/Mathematics/ZTransform/Differentiation.lean`
- Regression file: `Physlib/Mathematics/ZTransform/DifferentiationRegression.lean`
- Parity input: ledger row `ZT-04` read at live parity head `16022cfcfe12c8c93f5b1a15e356d92cfde26f20`.

## Registration requested

Add these sorted imports to `Physlib.lean` after
`Physlib.Mathematics.ZTransform.DifferenceEquationRegression` and before
`Physlib.Mathematics.ZTransform.Existence`:

```lean
public import Physlib.Mathematics.ZTransform.Differentiation
public import Physlib.Mathematics.ZTransform.DifferentiationRegression
```

Register production first and regression second. Production imports the Mathlib calculus support
and `Physlib.Mathematics.ZTransform.Convergence`; regression is a leaf importing production.

## Production declarations

- `Physlib.ZTransform.hasDerivAt_seriesTerm` —
  `Physlib/Mathematics/ZTransform/Differentiation.lean:96` @ `8e72d04953eed17baa7f6a08f35b8cfee218b31a`
- `Physlib.ZTransform.summable_derivativeSeries` —
  `Physlib/Mathematics/ZTransform/Differentiation.lean:120` @ `8e72d04953eed17baa7f6a08f35b8cfee218b31a`
- Private proof helper `norm_derivativeSeriesTerm_le` —
  `Physlib/Mathematics/ZTransform/Differentiation.lean:151` @ `8e72d04953eed17baa7f6a08f35b8cfee218b31a`
- `Physlib.ZTransform.hasDerivAt_transform` —
  `Physlib/Mathematics/ZTransform/Differentiation.lean:174` @ `8e72d04953eed17baa7f6a08f35b8cfee218b31a`
- `Physlib.ZTransform.transform_indexMul_eq_neg_z_mul_deriv` —
  `Physlib/Mathematics/ZTransform/Differentiation.lean:233` @ `8e72d04953eed17baa7f6a08f35b8cfee218b31a`

## Regression declarations

- `Physlib.ZTransform.differentiationFixture` —
  `Physlib/Mathematics/ZTransform/DifferentiationRegression.lean:58` @ `8e72d04953eed17baa7f6a08f35b8cfee218b31a`
- `Physlib.ZTransform.seriesTerm_differentiationFixture` —
  `Physlib/Mathematics/ZTransform/DifferentiationRegression.lean:62` @ `8e72d04953eed17baa7f6a08f35b8cfee218b31a`
- `Physlib.ZTransform.summable_seriesTerm_differentiationFixture` —
  `Physlib/Mathematics/ZTransform/DifferentiationRegression.lean:72` @ `8e72d04953eed17baa7f6a08f35b8cfee218b31a`
- `Physlib.ZTransform.transform_differentiationFixture` —
  `Physlib/Mathematics/ZTransform/DifferentiationRegression.lean:85` @ `8e72d04953eed17baa7f6a08f35b8cfee218b31a`
- `Physlib.ZTransform.transform_indexMul_differentiationFixture` —
  `Physlib/Mathematics/ZTransform/DifferentiationRegression.lean:94` @ `8e72d04953eed17baa7f6a08f35b8cfee218b31a`
- `Physlib.ZTransform.deriv_transform_differentiationFixture_at_two` —
  `Physlib/Mathematics/ZTransform/DifferentiationRegression.lean:104` @ `8e72d04953eed17baa7f6a08f35b8cfee218b31a`
- `Physlib.ZTransform.transform_indexMul_wrongSign_or_missingFactor_ne` —
  `Physlib/Mathematics/ZTransform/DifferentiationRegression.lean:121` @ `8e72d04953eed17baa7f6a08f35b8cfee218b31a`

## Source correspondence and analytic anchor

- The public domain is `w ∈ ROC f` together with `‖w‖ < ‖z‖`. It is the explicit radial
  margin used to justify termwise complex differentiation; it also forces both witnesses
  nonzero.
- `summable_derivativeSeries` factors each derivative term into the absolutely summable
  transform term at `w` and a geometric factor tending to zero.
- `hasDerivAt_transform` chooses the midpoint radius between `‖w‖` and `‖z‖`, builds an open
  ball about `z` outside that radius, supplies one summable derivative majorant on the ball,
  and applies Mathlib's `hasDerivAt_tsum_of_isPreconnected`.
- `transform_indexMul_eq_neg_z_mul_deriv` is downstream of that recurrence-free analytic
  theorem. It distributes `-z` through the proved-summable derivative series and cancels one
  inverse power; it does not introduce the target identity as a definition or rewrite with it.
- The conclusion is exactly `Z{n f[n]}(z) = -z * deriv (Z{f[n]}) z`. The source's positive
  real-part restriction is unnecessary under the stated strict radial convergence margin.
- No boundary differentiability, converse, inverse-transform, stability, physics, or optics
  claim is made.

## Hostile regression

The primitive fixture is supported only at index two with coefficient `3`. Its transform and
index-multiplied transform are computed directly from finite `tsum`s, while the derivative at
`z = 2` is computed from Mathlib's derivative of inversion. Thus the regression does not use
the production differentiation identity as an oracle.

At `z = 2`, the index-multiplied transform is `3 / 2` and the derivative is `-3 / 4`; the
correct factor `-z` yields `3 / 2`. The hostile sentinel proves both `2 * deriv = -3 / 2`
(wrong sign) and `-deriv = 3 / 4` (missing factor `z`) differ from the independently computed
index-multiplied transform.

## Pre-existing-line and registration accounting

The source delta `5ac9c10473b2de1ca8059c9ab5a13d13ada6bf9d` → `8e72d04953eed17baa7f6a08f35b8cfee218b31a` adds exactly
the two new modules: 251 production lines and 132 regression lines. It changes zero
pre-existing production, regression, import, or documentation lines. In particular, the
reviewed pre-existing first-difference, z-scaling, ROC, transform, and series-term declarations
are byte-stable.

For branch-wide root and import gates, the two slice-4 imports and the already stacked slice-3
production/regression imports were added to `Physlib.lean` temporarily and then all four were
removed. Byte-identical restoration was checked:

- SHA-256: `f7486c686c1d5087c1cb8a87f33b3af2dd11cb761b14fa0ebbc0a0e9489d0a20`
- Git blob: `8d3318db883c44b5d1c55fe28ef599fb1fc10ad5`

The only change in the child after the gated source is this replacement `HANDOFF.md`.

## Gates

- `lake-lock build Physlib.Mathematics.ZTransform.Differentiation
  Physlib.Mathematics.ZTransform.DifferentiationRegression`: pass at the exact cutoff,
  `Build completed successfully (2393 jobs)`.
- Temporary sorted registration followed by `lake-lock build Physlib`: pass at the exact
  cutoff, `Build completed successfully (5015 jobs)`.
- `lake-lock exe check_file_imports`: pass at the exact cutoff; all files imported correctly
  under temporary registration.
- `lake-lock exe sorry_lint`: pass at the exact cutoff.
- `lake-lock exe runPhyslibLinters`: pass for Physlib and QuantumInfo after the final source
  edit and root build.
- `lake-lock exe lint_all`: exit 0 on the preceding cutoff; its only slice-local finding was a
  redundant production import, removed in `8e72d049`. Exact-cutoff
  `lake-lock exe redundant_imports` exits 0 and names neither new module.
- `lake-lock exe module_doc_lint`: repository baseline remains nonzero; an exact-cutoff filter
  for both new paths exits 0 with no output.
- `./scripts/lint-style.sh`: pass after committing the exact source cutoff.
- `git diff --check`: pass; production is 251 lines, regression is 132 lines, and neither file
  has a line over 100 codepoints.

## Milestone

ITP'14 Thm. 10 complex-differentiation identity added; ZT-04 moves PARTIAL -> discharged on merge.

## Verbatim ledger row

`PARITY-LEDGER.md` @ `16022cfcfe12c8c93f5b1a15e356d92cfde26f20`:

```text
| ZT-04 | ITP'14 Thm. 7 p. 490 (first difference), Thms. 8–9 p. 491 (z-domain scaling), Thm. 10 p. 491 (complex differentiation) | **PARTIAL.** Covered: Thm. 7 first difference `transform_firstDifference` (`Physlib/Mathematics/ZTransform/Basic.lean:406` @ `110eb5cd`, under `IsCausal`), and Thms. 8–9 z-domain scaling `transform_zScale` (`:439`) with `ROC_zScale` (`:444`). **NOT covered: Thm. 10, complex differentiation — no declaration for it exists anywhere in `Physlib/Mathematics/ZTransform/` (checked repo-wide).** Same treatment as ZT-06: discharge what exists, withhold the rest, and name the missing theorem rather than flipping the row whole — **on `optics/development` @ `110eb5cd`** | — | Retained | **PARTIALLY proved and GATED on `optics/development` @ `110eb5cd`** — Thms. 7–9 discharged; **Thm. 10 (complex differentiation) WITHHELD**. **INTEGRITY NOTE — STALE, corrected 2026-08-27 in the 15-row TBD sweep.** It read *"TBD — not yet formalized"* while its target already existed; found by the sweep the TBD-listing check now makes possible. **S8 TRIAGE 2026-08-27 — OPEN**, smallest named slice: named in the triage. Implementation proceeds on the S8 lane in the triage's §8 order. **Lines below are DECLARATION lines resolved by this lane at `9c1f4929`; the triage cited docstring-start lines.** Nearest existing work: `transform_firstDifference` (`Physlib/Mathematics/ZTransform/Basic.lean:406`). | parity |
```
