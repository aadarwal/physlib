# S5 lane handoff — Z-transform / difference equations

Branch: `optics/s5-ztransform` (branched off `optics/development` at `5041048a`).
Home: `Physlib/Mathematics/ZTransform/` — neutral mathematics, **no** `Physlib/Optics` import.
Worktree: `/Users/aadarwal/src/aadarwal/physlib-wt/optics-s5-ztransform`.

The conductor owns `optics/development`, `Physlib.lean`, `Physlib/Optics/API-map.yaml`,
`goal.md`, and `tbd.md`. This lane edits none of them. The registrations this lane needs are
listed below for the conductor to apply at merge.

---

## Slice status

| Slice | Content | Status |
|---|---|---|
| 1 | Causal sequences, unilateral transform, ROC (absolute vs conditional), linearity, shift laws, first difference, z-scaling, unit impulse | **done** |
| 2 | ROC exterior-of-circle shape, geometric sequence, conditional-but-not-absolute counterexample | pending |
| 3 | Linear constant-coefficient difference equations to rational transfer functions | pending |
| 4 | Stability: poles, unit circle, BIBO (directions proved stated explicitly) | pending |
| 5 | Regressions: first-order all-pass and a two-pole example | pending |

---

## Slice 1 — files

- `Physlib/Mathematics/ZTransform/Basic.lean` (471 lines)
- `Physlib/Mathematics/ZTransform/BasicRegression.lean` (211 lines)

### Registrations needed in `Physlib.lean`

Insert in alphabetical position among the `Physlib.Mathematics.*` block:

```
public import Physlib.Mathematics.ZTransform.Basic
public import Physlib.Mathematics.ZTransform.BasicRegression
```

No other registry, API-map, or `goal.md` edit is requested by this lane yet. The `API-map.yaml`
S5 row should stay `done: false` until at least slices 3 and 4 land, since the row's contract
includes difference equations and stability.

### Gates run (slice 1)

- `lake-lock build Physlib.Mathematics.ZTransform.Basic
  Physlib.Mathematics.ZTransform.BasicRegression` — clean.
- `lake-lock env lean -Dwarn.sorry=false -Dweak.says.verify=true <each file>` — zero warnings,
  zero errors (this is the warnings-as-errors check; the lakefile's `moreLeanArgs` are passed
  explicitly).
- Batteries declaration linters (the `runPhyslibLinters` linter set, including
  `Physlib.withDefsWithUnderscoreExemptions`) run against these two modules only — **passed**.
  The shipped `runPhyslibLinters` executable hard-codes `#[`Physlib`, `QuantumInfo`]` and so
  needs the whole registry built and this lane's modules registered; that full-registry run is a
  **merge-time gate for the conductor**, not something this lane can perform.
- `module_doc_lint` and `style_lint` rules re-implemented locally and run on both files (heading
  template, table-of-contents match, 100-character lines, forbidden substrings, even initial
  indentation, no double blank lines) — clean. Those two executables also read the built
  `Physlib` olean's import list, so they likewise cannot see unregistered modules.
- `grep` for `sorry`, `axiom`, `native_decide`, `set_option maxHeartbeats` — none present.
- Import minimality checked by removing each import in turn;
  `Mathlib.Analysis.SpecificLimits.Normed` was redundant and has been dropped (it returns in
  slice 2).

### Build-cache note

This worktree has no `.lake/build` of its own for `Physlib`; `.lake/packages` is a symlink to
`/Users/aadarwal/src/aadarwal/physlib/.lake/packages` (identical `lake-manifest.json`,
`lakefile.toml`, and `lean-toolchain` md5s were verified first). The ZTransform modules import
only Mathlib, so no Physlib module needs building to compile them. Disk stayed above 45 GB free
throughout.

---

## Slice 1 — declarations

`Physlib/Mathematics/ZTransform/Basic.lean`, namespace `Physlib.ZTransform`:

**A. Causal two-sided sequences** — `IsCausal`, `IsCausal.apply_of_neg`, `isCausal_zero`,
`IsCausal.add`, `IsCausal.const_mul`, `zeroExtend`, `zeroExtend_isCausal`, `zeroExtend_natCast`.

**B. The unilateral Z-transform series** — `seriesTerm`, `seriesTerm_eq_zpow`, `transform`,
`transform_eq_tsum`, `transform_zero`.

**C. Absolute and conditional regions of convergence** — `ROC`, `condROC`, `mem_ROC_iff`,
`mem_condROC_iff`, `zero_notMem_ROC`, `summable_norm_seriesTerm_iff`, `ROC_subset_condROC`,
`tendsto_sum_range_transform`.

**D. Linearity** — `seriesTerm_add`, `seriesTerm_const_mul`, `seriesTerm_neg`, `seriesTerm_sub`,
`summable_seriesTerm_add`, `summable_seriesTerm_const_mul`, `summable_seriesTerm_sub`,
`transform_add`, `transform_const_mul`, `transform_neg`, `transform_sub`,
`inter_ROC_subset_ROC_add`, `ROC_const_mul`.

**E. Delay and advance** — `delay`, `advance`, `IsCausal.delay`, `seriesTerm_delay_add`,
`seriesTerm_delay_of_lt`, `summable_seriesTerm_delay`, `transform_delay`,
`seriesTerm_advance_eq`, `summable_seriesTerm_advance`, `transform_advance`.

**F. The first difference** — `firstDifference`, `firstDifference_apply`,
`transform_firstDifference`.

**G. Scaling in the z-domain** — `zScale`, `IsCausal.zScale`, `seriesTerm_zScale`,
`transform_zScale`, `ROC_zScale`.

**H. The unit impulse** — `unitImpulse`, `unitImpulse_isCausal`, `seriesTerm_unitImpulse`,
`summable_seriesTerm_unitImpulse`, `transform_unitImpulse`, `ROC_unitImpulse`,
`transform_delay_unitImpulse`.

`Physlib/Mathematics/ZTransform/BasicRegression.lean`, same namespace:
`regressionAtNegOne`, `regressionAtNegOne_not_isCausal`, `seriesTerm_regressionAtNegOne`,
`transform_regressionAtNegOne`, `seriesTerm_delay_regressionAtNegOne`,
`transform_delay_regressionAtNegOne`, `transform_delay_ne_of_not_isCausal`,
`seriesTerm_advance_unitImpulse`, `transform_advance_unitImpulse`,
`transform_advance_unitImpulse_eq`, `transform_advance_ne_without_startup`, `twoTap`,
`twoTap_isCausal`, `seriesTerm_twoTap`, `summable_seriesTerm_twoTap`, `transform_twoTap`,
`transform_zScale_delay_unitImpulse`, `transform_zScale_delay_unitImpulse_ne_inv`.

---

## Milestone and ledger rows touched by slice 1

`goal.md` §H.4 S5 bullets satisfied so far:

- "causal complex sequences with zero extension" — `IsCausal`, `zeroExtend`.
- "analytic unilateral Z-transform with conditional and absolute convergence regions kept
  distinct" — `transform`, `ROC`, `condROC`, `ROC_subset_condROC`,
  `summable_norm_seriesTerm_iff`. The separation *witness* (a point of `condROC \ ROC`) is
  slice 2; until it lands, only the inclusion is proved, and the two sets are defined but not yet
  proved unequal.
- "linearity, causal right-delay, and left-shift laws with their startup terms" —
  `transform_add`, `transform_const_mul`, `transform_delay`, `transform_advance`.
- "first differences, `z`-domain scaling" — `transform_firstDifference`, `transform_zScale`.

Still open in §H.4 S5 after slice 1: complex-differentiation law, recurrence-to-transfer,
general IIR and frequency response, the audited second-order low-pass, BIBO/stability, and the
formal power-series connection.

`goal.md` §I.3 regressions:

- **T-01** ("Z-transform delay law records ROC and initial conditions") — addressed by
  `transform_delay_ne_of_not_isCausal` (causality is load-bearing) and
  `transform_advance_ne_without_startup` (the startup sum is load-bearing). ROC is recorded in
  the statements as the explicit `Summable (seriesTerm f z)` hypothesis.
- **T-03** ("conditional and absolute convergence regions are not identified") — *partially*
  addressed: both regions exist as separate definitions and only the true inclusion is proved.
  The counterexample that makes the non-identification a theorem is slice 2.
- T-02, T-04, T-05 — not yet started.

Parity ledger rows (`~/src/aadarwal/physlib-parity/PARITY-LEDGER.md`):

- **ZT-01** (ITP'14 Def. 8 + Def. 9, p. 488) — definition parity reached:
  `Physlib.ZTransform.transform`, `Physlib.ZTransform.ROC`. Physlib-stronger part (naming a
  conditional region) is defined; the strict-inequality proof is slice 2.
- **ZT-02** (ITP'14 Thm. 4 p. 489; Thms. 2-3 p. 488) — reached: `transform_add`,
  `transform_const_mul`, `inter_ROC_subset_ROC_add`, `ROC_const_mul`.
- **ZT-03** (ITP'14 Thm. 5 p. 489 left shift; Thm. 6 p. 490 right shift) — reached:
  `transform_advance`, `transform_delay`.
- **ZT-04** (ITP'14 Thm. 7 p. 490 first difference; Thms. 8-9 p. 491 z-scaling) — reached
  except Thm. 10 (complex differentiation), which is deferred.
- JAL'18 Def. 14 / Thm. 12 p. 888 (Dirac delta) — reached: `unitImpulse`,
  `transform_unitImpulse`.

### One correction for the parity ledger

`HOL-CORPUS.md` §7.1 renders ITP'14 Theorem 5 (left shift) as
`z^m F(z) − Σ_{n=0}^{m−1} f n z^{−n}`. That expression is not the left-shift law: taking
`f = δ` and `m = 1` it gives `z − 1`, whereas `Z{δ[n+1]}` is `0` because the advanced impulse
has no nonnegative-index sample. The correct statement, and the one proved here as
`transform_advance`, is

```
transform (advance m f) z = z ^ m * (transform f z - ∑ n ∈ Finset.range m, seriesTerm f z n)
```

that is, the `z^m` factor multiplies the startup sum too. This agrees with Oppenheim and
Schafer, *Discrete-Time Signal Processing*, 3rd ed., ch. 3. The regression
`transform_advance_unitImpulse_eq` instantiates the proved law at `f = δ`, `m = 1` and gets `0`.
Whether `HOL-CORPUS.md` §7.1 is an abbreviation in the corpus note or a genuine transcription of
the paper is **not** something this lane verified against the ITP'14 PDF; the ledger row ZT-03
should be re-checked against the source before the claim "parity" is published.

### Deliberate departures from the sources, recorded in the module docs

1. Both ITP'14 and JAL'18 define the region of convergence by summability, that is absolutely,
   and neither names a conditional region. This file names both and proves only the inclusion
   that holds.
2. The sources index sequences so that causality is a side condition on a one-sided index set.
   This file uses a two-sided index `ℤ → ℂ` and states causality as `IsCausal`, so that the
   advance law can be stated without silently discarding the negative-index samples.

### Open scope question for the human (unchanged from `HOL-CORPUS.md` §7.2)

`goal.md` §S5 says "Inverse-transform uniqueness is not required for source parity unless a
later mandatory ledger row needs it." That sentence was written against ITP'14. The journal
version of record, JAL'18, has the inverse transform (Thm. 15) and uniqueness (Thm. 16) via
`exterior_circle`. Ledger rows ZT-08 and ZT-09 are marked "scope decision required". This lane
is proceeding on the current `goal.md` scope, that is **without** inverse or uniqueness, and
will not start them without an explicit decision. Slice 2 does build the `exterior_circle` ROC
shape lemmas, which are the prerequisite for either.
