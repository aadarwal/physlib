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
| 1 | Causal sequences, unilateral transform, ROC (absolute vs conditional), linearity, shift laws, first difference, z-scaling, unit impulse | **done** (`340de28a`) |
| 2 | Modulus-only absolute convergence, exterior-of-circle ROC shape, reciprocal power series, unit step, geometric sequence, and the conditional-but-not-absolute witness | **done** |
| 3 | Linear constant-coefficient difference equations to rational transfer functions; general IIR; the audited second-order low-pass; first-order all-pass regression | pending |
| 4 | Stability: poles, the unit circle, BIBO, with the proved directions stated explicitly; two-pole regression | pending |
| 5 | Inverse transform and uniqueness (JAL'18 Thms. 15-17), built on the `IsExteriorOfCircle` lemmas | pending — **now in scope**, see the scope note below |

The slice-5 change follows the controller's decision of 2026-08-25: the corrected `goal.md`
(merged `bf0a4063`) names ITP'14 **and** JAL'18, including the inverse transform and uniqueness,
as the parity targets. The earlier "inverse and uniqueness out of scope" reading of `goal.md`
§S5 is superseded. The original slice-5 regressions (first-order all-pass, two-pole) move into
slices 3 and 4, where their supporting theory lives.

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

---

## Slice 2 — files

- `Physlib/Mathematics/ZTransform/Convergence.lean` (264 lines)
- `Physlib/Mathematics/ZTransform/ConvergenceRegression.lean` (211 lines)

### Registrations needed in `Physlib.lean` (cumulative, all four)

```
public import Physlib.Mathematics.ZTransform.Basic
public import Physlib.Mathematics.ZTransform.BasicRegression
public import Physlib.Mathematics.ZTransform.Convergence
public import Physlib.Mathematics.ZTransform.ConvergenceRegression
```

Import order matters only in that `Convergence` needs `Basic` and `ConvergenceRegression` needs
`Convergence`; alphabetical order already satisfies both.

### Slice 2 — declarations

`Physlib/Mathematics/ZTransform/Convergence.lean`, namespace `Physlib.ZTransform`:

**A. Absolute convergence depends only on the modulus** — `norm_seriesTerm`,
`summable_seriesTerm_of_norm_le`, `ne_zero_of_norm_le`.

**B. The region of convergence as an exterior of a circle** — `ROC_mem_of_mem_of_norm_le`,
`ROC_mem_of_mem_of_norm_eq`, `IsExteriorOfCircle`, `IsExteriorOfCircle.nonempty`,
`isExteriorOfCircle_ROC`, `isExteriorOfCircle_ROC_iff`.

**C. The transform as a power series in the reciprocal variable** — `transform_inv`,
`summable_pow_iff_inv_mem_ROC`.

**D. The unit step** — `unitStep`, `unitStep_isCausal`, `seriesTerm_unitStep`,
`summable_seriesTerm_unitStep_iff`, `ROC_unitStep`, `transform_unitStep`.

**E. The geometric sequence** — `geometricSeq`, `geometricSeq_natCast`, `geometricSeq_isCausal`,
`ROC_geometricSeq`, `transform_geometricSeq`.

`Physlib/Mathematics/ZTransform/ConvergenceRegression.lean`, same namespace: `harmonicSeq`,
`harmonicSeq_isCausal`, `seriesTerm_harmonicSeq_neg_one`, `norm_seriesTerm_harmonicSeq_neg_one`,
`not_summable_seriesTerm_harmonicSeq`, `neg_one_notMem_ROC_harmonicSeq`,
`neg_one_mem_condROC_harmonicSeq`, `ROC_ssubset_condROC_harmonicSeq`,
`exists_ROC_ssubset_condROC`, `self_notMem_ROC_geometricSeq`, `two_mul_mem_ROC_geometricSeq`,
`transform_geometricSeq_half`, `one_notMem_ROC_unitStep`, `I_notMem_ROC_unitStep`,
`two_mul_I_mem_ROC_unitStep`.

### What slice 2 proves that the sources do not

1. **Absolute convergence depends on `z` only through `‖z‖`.** `summable_seriesTerm_of_norm_le`
   propagates absolute convergence outward under the **non-strict** inequality `‖w‖ ≤ ‖z‖`, by
   direct comparison of term norms. No boundedness or Abel argument is used. Consequently the
   region of convergence is proved invariant under rotation (`ROC_mem_of_mem_of_norm_eq`), which
   the usual strict-inequality statement does not give.
2. **The regions of convergence of the unit step and of the geometric sequence are computed
   exactly**, as set equalities `ROC unitStep = {z | 1 < ‖z‖}` and
   `ROC (geometricSeq a) = {z | ‖a‖ < ‖z‖}` for `a ≠ 0`, not merely shown to contain an
   exterior. `self_notMem_ROC_geometricSeq` pins the boundary as excluded.
3. **The absolute and conditional regions are proved different sets**, not merely defined
   differently — see the T-03 row below.

### Slice 2 gates

Same gate set as slice 1, all clean: build; `lean -Dwarn.sorry=false -Dweak.says.verify=true`
on each of the four files gives zero output; the Batteries declaration linter set run
module-scoped over all four modules passes; the `module_doc_lint` and `style_lint` rules re-run
locally pass; no `sorry`, `axiom`, `native_decide`, or `set_option maxHeartbeats`; no
`Physlib.Optics` import anywhere; imports minimal
(`Mathlib.Analysis.SpecificLimits.Normed` turned out to be transitively available through
`Basic` and was dropped from `Convergence.lean`).

### Slice 2 — milestone and ledger rows

`goal.md` §H.4 S5:

- "absolute-summability/BIBO stability results and their relation to poles and the region of
  convergence" — the **region-of-convergence half** is done: `isExteriorOfCircle_ROC_iff`,
  `ROC_mem_of_mem_of_norm_le`, and the exact regions for the step and geometric sequences. Poles,
  BIBO, and the causal rational class are slice 4.
- The conditional/absolute distinction bullet is now fully discharged, not partially: see T-03.

`goal.md` §I.3 regressions:

- **T-03** ("conditional and absolute convergence regions are not identified") — **discharged**.
  `ROC_ssubset_condROC_harmonicSeq` proves `ROC harmonicSeq ⊂ condROC harmonicSeq`, with
  `exists_ROC_ssubset_condROC` as the existential form. The witness is `1 / (n + 1)` at `z = -1`:
  the alternating harmonic series converges, and the harmonic series does not. A development that
  defined one region and called it the other fails this file.

Parity ledger:

- **ZT-08 (partial)** — JAL'18 Def. 19 (`exterior_circle`, p. 893) is reached as
  `IsExteriorOfCircle` (the source's `0 < R` form is kept) together with
  `isExteriorOfCircle_ROC_iff`, which is the "three ROC-shape lemmas" content. The inverse
  transform itself (Thm. 15) is slice 5; `transform_inv` and `summable_pow_iff_inv_mem_ROC` are
  the substitution `u = z⁻¹` that Thm. 15 differentiates, so slice 5 starts from them.
- JAL'18 Table 1 (p. 888), unit step and geometric entries — reached exactly, as set equalities.


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

### Literature defect found by this lane, and resolved (ZT-03)

`transform_advance` did not match the left-shift law as printed in ITP'14. The parity lane
checked the PDFs at character level and confirmed: **ITP'14 p. 489 prints the advance law
incorrectly, in both equation (5) and Theorem 5**, with the startup sum outside the `z ^ m`
factor. That printed form is not provable. At `f` the unit impulse and `m = 1` it evaluates to
`z - 1`, whereas the advanced unit impulse has no nonnegative-index sample and so has unilateral
transform `0`. **JAL'18 p. 885 Theorem 5 states it correctly** and matches
`Physlib.ZTransform.transform_advance` exactly:

```
transform (advance m f) z = z ^ m * (transform f z - ∑ n ∈ Finset.range m, seriesTerm f z n)
```

Resolution applied here: the statement is unchanged; the module doc of
`Physlib/Mathematics/ZTransform/Basic.lean` now cites **JAL'18 Thm. 5 (p. 885)** as the parity
target for the advance law and records ITP'14's printed form as unprovable, with the impulse
evaluation as the reason. `transform_advance_unitImpulse_eq` in the regression file instantiates
the proved law at that point and obtains `0`. Ledger row ZT-03 should cite JAL'18 for the left
shift and keep ITP'14 only for the right shift (Thm. 6 p. 490, which is correct as printed).

### Deliberate departures from the sources, recorded in the module docs

1. Both ITP'14 and JAL'18 define the region of convergence by summability, that is absolutely,
   and neither names a conditional region. This file names both and proves only the inclusion
   that holds.
2. The sources index sequences so that causality is a side condition on a one-sided index set.
   This file uses a two-sided index `ℤ → ℂ` and states causality as `IsCausal`, so that the
   advance law can be stated without silently discarding the negative-index samples.

### Scope note: inverse and uniqueness are in scope (resolved 2026-08-25)

`goal.md` §S5 previously read "Inverse-transform uniqueness is not required for source parity
unless a later mandatory ledger row needs it", written against ITP'14. The controller has since
confirmed that the corrected `goal.md` (merged `bf0a4063`) names ITP'14 **and** JAL'18, including
the inverse transform (Thm. 15) and uniqueness (Thm. 16), as parity targets. Ledger rows ZT-08
and ZT-09 are therefore live work, scheduled as slice 5 and to be built on the
`IsExteriorOfCircle` lemmas and `transform_inv` delivered in slice 2. Nothing about slices 3 and
4 changes.
