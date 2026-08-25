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
| 3 | Linear constant-coefficient difference equations to rational transfer functions; general IIR; the audited second-order low-pass; first-order all-pass regression | **done** |
| 4 | Stability: poles, the unit circle, BIBO, with the proved directions stated explicitly; two-pole regression | **done** |
| 5 | Inverse transform and uniqueness (JAL'18 Thms. 15-17), built on the `IsExteriorOfCircle` lemmas | **done**, by the approved fallback route — see below |
| 6 | The finite-convolution theorem, and existence of causal solutions of a strictly causal recurrence | pending — scheduled by the controller on 2026-08-25 |

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


---

## Slice 3 — files

- `Physlib/Mathematics/ZTransform/DifferenceEquation.lean` (338 lines)
- `Physlib/Mathematics/ZTransform/DifferenceEquationRegression.lean` (265 lines)

### Registrations needed in `Physlib.lean` (cumulative, all six)

```
public import Physlib.Mathematics.ZTransform.Basic
public import Physlib.Mathematics.ZTransform.BasicRegression
public import Physlib.Mathematics.ZTransform.Convergence
public import Physlib.Mathematics.ZTransform.ConvergenceRegression
public import Physlib.Mathematics.ZTransform.DifferenceEquation
public import Physlib.Mathematics.ZTransform.DifferenceEquationRegression
```

Alphabetical order satisfies the dependency order.

### Slice 3 — declarations

`Physlib/Mathematics/ZTransform/DifferenceEquation.lean`, namespace `Physlib.ZTransform`:

**A. Transforms of finite sums of sequences** — `seriesTerm_zero_fun`,
`summable_seriesTerm_finsetSum`, `transform_finsetSum`.

**B. Finite delay combinations and their symbols** — `delayCombination`, `delaySymbol`,
`delayCombination_eq_sum`, `IsCausal.delayCombination`,
`summable_seriesTerm_delayCombination`, `transform_delayCombination`.

**C. Linear constant-coefficient difference equations** — `IsRecurrenceSolution`,
`IsRecurrenceSolution.apply`, `transform_isRecurrenceSolution`.

**D. Uniqueness of the causal solution** — `eq_of_isRecurrenceSolution`.

**E. The transfer function and its region of convergence** — `transferFunction`, `iirROC`,
`transform_eq_transferFunction_mul`, `transform_eq_transferFunction_mul_of_mem_iirROC`,
`transferFunction_eq_div`.

**F. The frequency-response substitution** — `inv_exp`, `transform_exp`,
`transferFunction_exp`, `transferFunction_eq_norm_mul_exp_arg`.

`Physlib/Mathematics/ZTransform/DifferenceEquationRegression.lean`, same namespace:
`onePoleFeedback`, `onePoleFeedback_one`, `onePoleFeedforward`, `onePoleFeedforward_zero`,
`unitImpulse_zero`, `geometricSeq_zero`, `isRecurrenceSolution_geometricSeq`,
`transferFunction_onePole`, `transform_geometricSeq_eq_transferFunction_mul`,
`allPassFeedback`, `allPassFeedback_one`, `allPassFeedforward`, `allPassFeedforward_zero`,
`allPassFeedforward_one`, `transferFunction_allPass`, `norm_ofReal_add_eq_norm_one_add_mul`,
`norm_transferFunction_allPass`, `lowPassFeedback`, `lowPassFeedback_one`,
`lowPassFeedback_two`, `lowPassFeedforward`, `lowPassFeedforward_zero`,
`lowPassFeedforward_one`, `lowPassFeedforward_two`, `zero_notMem_lowPass_lags`,
`delaySymbol_lowPassFeedforward`, `delaySymbol_lowPassFeedback`,
`transferFunction_lowPass_one`, `transferFunction_lowPass_neg_one`.

### Design decisions in slice 3, and the hypotheses made explicit

1. **The cleared identity is proved before the quotient.**
   `transform_isRecurrenceSolution` states
   `(1 - delaySymbol s α z⁻¹) * transform y z = delaySymbol t β z⁻¹ * transform x z`
   and needs **no** nondegeneracy hypothesis at all. Dividing is a separate theorem,
   `transform_eq_transferFunction_mul`, whose hypothesis `1 - delaySymbol s α z⁻¹ ≠ 0` is
   explicit. The sources state the quotient directly. This ordering is what keeps the
   nondegeneracy visible rather than buried in a definition.
2. **Lags are an arbitrary `Finset ℕ`, not a list.** The sources index coefficients by lists and
   impose "the head of the feedback list is zero" as a structural constraint. Here that is
   `0 ∉ s`, and it is used **only** where it is actually needed, namely in
   `eq_of_isRecurrenceSolution`. It is not needed to transform the equation.
3. **Uniqueness of the causal solution is proved and has no counterpart in the sources.**
   `eq_of_isRecurrenceSolution`: if `0 ∉ s`, two causal solutions driven by the same input are
   equal. The zero initial conditions come from causality, so this is the "linear recurrences
   with initial conditions" content of `goal.md` §H.4 S5, in its causal special case.
4. **Rationality is rationality in `z⁻¹`, never in a physical frequency.** `transferFunction` is
   a ratio of two polynomials in `z⁻¹`. The only bridge offered towards a delay variable is
   `transform_exp` and `transferFunction_exp`, the substitution `z = exp w`, which are
   identities about evaluation and assert nothing about a physical model.

### Two explicit non-claims in slice 3

- **No existence theorem for a causal solution.** Every transfer-function statement is
  conditional on being handed a solution. To show the theory is not vacuous, the regression file
  exhibits a solved case: `isRecurrenceSolution_geometricSeq` proves the causal geometric
  sequence solves `y n = a * y (n - 1) + x n` driven by the unit impulse, and
  `transform_geometricSeq_eq_transferFunction_mul` shows its transform, computed independently
  in slice 2 by summing a geometric series, equals the transfer function times the input
  transform. Two independent routes meet. Constructing solutions in general is deferred and is
  flagged below.
- **A denominator zero is only a candidate pole.** No theorem here says the transfer function
  has a pole at a zero of `1 - delaySymbol s α z⁻¹`, because a numerator zero at the same point
  can cancel it. This matches `goal.md` §S4's insistence on the same distinction; the
  cancellation analysis is slice 4 work.

### Slice 3 gates

Same set, all clean: build; `lean -Dwarn.sorry=false -Dweak.says.verify=true` on each of the six
files gives zero output; the Batteries declaration linter set run module-scoped over all six
modules passes; `module_doc_lint` and `style_lint` rules re-run locally pass; no `sorry`,
`axiom`, `native_decide`, or `set_option maxHeartbeats`; no `Physlib.Optics` import; imports
minimal (both new files needed every import they declare).

### Slice 3 — milestone and ledger rows

`goal.md` §H.4 S5:

- "finite convolution and linear recurrences with initial conditions" — the recurrence half is
  done (`IsRecurrenceSolution`, `eq_of_isRecurrenceSolution`); a general finite-convolution
  theorem `transform (x ⋆ h) = transform x * transform h` is **not** yet proved and is listed
  below as remaining work.
- "recurrence-to-transfer theorem under summability and initial-condition hypotheses" — done:
  `transform_isRecurrenceSolution`, `transform_eq_transferFunction_mul`.
- "general IIR and frequency-response theorems, including the audited second-order low-pass
  regression" — done: `transferFunction`, `iirROC`, `transferFunction_exp`,
  `transferFunction_eq_norm_mul_exp_arg`, and the low-pass regressions.
- "connection between coefficient recurrences and the formal power-series view" — partially:
  `transform_inv` (slice 2) records the transform as the power series `∑ f n u ^ n` in
  `u = z⁻¹`. A `PowerSeries ℂ` valued map is **not** built; see remaining work.

`goal.md` §I.3 regressions:

- **T-02** ("recurrence, rational transfer function, and network response agree") — the first two
  agree, proved on a solved case by `transform_geometricSeq_eq_transferFunction_mul`. The
  network-response leg belongs to the S-track and is not this lane's to close.
- **T-04** ("general IIR and audited second-order low-pass responses follow from recurrence
  semantics") — done. The low-pass uses the source's exact rationals, feedback
  `[0, 1.194, -0.436]` and feedforward `[0.0605, 0.121, 0.0605]`, as exact rationals and not
  floating point. Two exact values are proved: gain exactly `1` at `z = 1`, and gain exactly `0`
  at `z = -1`. The first detects a sign error in the feedback symbol; the second is the Nyquist
  null that makes it a low-pass.
- **T-05** ("the selected `q = z⁻¹` translation commutes with evaluation") — the mathematical
  half is done, `transform_exp` and `transferFunction_exp`. Tying `q` to `exp (-s * τ)` for a
  physical `τ` is S-track work.

Parity ledger:

- **ZT-05** (ITP'14 Def. 10 + Thm. 11 + Lemma 4, p. 492) — reached, and strengthened by the
  division-free form plus `eq_of_isRecurrenceSolution`.
- **ZT-06** (ITP'14 Defs. 11-13 + Thms. 12-13, pp. 494-496) — reached: `transferFunction`,
  `iirROC`, `transferFunction_eq_div`, `transferFunction_exp`,
  `transferFunction_eq_norm_mul_exp_arg`.
- **ZT-07** (ITP'14 Def. 14 + Thm. 14, pp. 496-497) — reached as an audited regression with the
  source's exact rational coefficients.

### Remaining work in this lane after slice 3

- Slice 4: poles and zeros after cancellation, Schur stability, and BIBO. Note ledger row ZT-10:
  **no fetched source has a Schur-stability or BIBO theorem**, so that slice is Physlib-original
  and its statements should be reviewed on their own merits, not against a source.
- Slice 5: inverse transform and uniqueness (JAL'18 Thms. 15-17), on the `IsExteriorOfCircle`
  lemmas and `transform_inv`.
- Not yet scheduled, and worth a decision: a general finite-convolution theorem, an existence
  theorem for causal solutions of a strictly causal recurrence, and a `PowerSeries ℂ` valued
  formal-power-series map. All three are named in `goal.md` §H.4 S5. None is needed by slices 4
  or 5, so they can be a slice 6 or dropped by explicit decision.

---

## Slice 4 — files

- `Physlib/Mathematics/ZTransform/Stability.lean` (289 lines)
- `Physlib/Mathematics/ZTransform/StabilityRegression.lean` (208 lines)

### Registrations needed in `Physlib.lean` (cumulative, all eight)

```
public import Physlib.Mathematics.ZTransform.Basic
public import Physlib.Mathematics.ZTransform.BasicRegression
public import Physlib.Mathematics.ZTransform.Convergence
public import Physlib.Mathematics.ZTransform.ConvergenceRegression
public import Physlib.Mathematics.ZTransform.DifferenceEquation
public import Physlib.Mathematics.ZTransform.DifferenceEquationRegression
public import Physlib.Mathematics.ZTransform.Stability
public import Physlib.Mathematics.ZTransform.StabilityRegression
```

Alphabetical order satisfies the dependency order.

### Slice 4 is Physlib-original

Parity ledger row ZT-10 records that **no fetched source in the Concordia HVG corpus contains a
Schur-stability theorem, a bounded-input bounded-output equivalence, or a group-delay or
dispersion theorem**; FMICS'15 p. 171 claims group delay and dispersion in prose only, marked
UNVERIFIED. Slice 4 is therefore not a parity claim and must be reviewed on its own merits. The
module docs say so.

### Exactly what slice 4 proves, and what it withholds

Proved, both directions:

- `isAbsSummable_iff_one_mem_ROC`, `isAbsSummable_iff_sphere_subset_ROC`,
  `isAbsSummable_iff_closedExterior_subset_ROC`. Absolute summability of a sequence, membership
  of `1` in its absolute region of convergence, containment of the unit circle in that region,
  and containment of the whole closed exterior of the unit circle are all **equivalent**. The
  strong closed-exterior form follows from slice 2's modulus-only result and is not available
  from the usual strict-inequality Abel argument.

Proved, one direction only:

- `isBIBOStable_of_isAbsSummable` and `isBIBOStable_of_sphere_subset_ROC`. Absolute summability
  implies bounded-input bounded-output stability of the causal convolution operator, with the
  explicit bound `norm_convolution_le`: `‖convolution h x n‖ ≤ (∑' k, ‖h k‖) * C`.
- **Withheld:** the converse, that bounded-input bounded-output stability implies absolute
  summability. It is true for this class, but the standard proof needs a sign-selecting input
  that is not formalized here. No theorem in the file states an equivalence, and the module doc
  says the converse is not proved.

Proved for Schur stability:

- `denominator_ne_zero_of_isSchurStable`: Schur stability makes the denominator symbol
  nonvanishing on the whole closed exterior of the unit circle.
- `closedExterior_subset_iirROC_of_isSchurStable` and
  `transform_eq_transferFunction_mul_of_isSchurStable`: with absolutely summable causal input and
  output, the transfer relation therefore holds at every point with `1 ≤ ‖z‖`, in particular on
  the unit circle itself.
- **Withheld:** that Schur stability implies a solution of the difference equation is absolutely
  summable. That is the substantive direction of the classical theorem and needs a partial
  fraction or companion-matrix argument that is not present.
- **Withheld:** that a candidate pole is an actual pole. `candidatePoles` is named a *candidate*
  set precisely because a numerator zero at the same point can cancel it, matching `goal.md`
  §S4's distinction.

Sufficient criterion:

- `isSchurStable_of_sum_norm_lt_one`: total feedback modulus below one implies Schur stability.
  It is sufficient and **not** necessary, and that is proved, not merely asserted — see the
  two-pole regression below.

### The convolution operator, and its relation to slice 6

`convolution` is **defined** in slice 4 because bounded-input bounded-output stability cannot be
stated without it, and the boundedness bound is proved here. The transform of a convolution, the
convolution theorem `transform (convolution h x) z = transform h z * transform x z`, is **not**
proved here; it is slice 6 work per the controller's decision of 2026-08-25, and will be built on
this definition rather than on a second one.

### Slice 4 — declarations

`Physlib/Mathematics/ZTransform/Stability.lean`, namespace `Physlib.ZTransform`:
`IsAbsSummable`, `seriesTerm_one`, `isAbsSummable_iff_one_mem_ROC`,
`isAbsSummable_iff_closedExterior_subset_ROC`, `isAbsSummable_iff_sphere_subset_ROC`,
`IsBoundedSeq`, `convolution`, `IsBoundedSeq.nonneg_of_bound`,
`summable_norm_convolution_term`, `norm_convolution_le`, `IsBIBOStable`,
`isBIBOStable_of_isAbsSummable`, `isBIBOStable_of_sphere_subset_ROC`, `candidatePoles`,
`IsSchurStable`, `denominator_ne_zero_of_isSchurStable`,
`closedExterior_subset_iirROC_of_isSchurStable`,
`transform_eq_transferFunction_mul_of_isSchurStable`, `isSchurStable_of_sum_norm_lt_one`.

`Physlib/Mathematics/ZTransform/StabilityRegression.lean`, same namespace:
`delaySymbol_onePoleFeedback`, `candidatePoles_onePole`, `isSchurStable_onePole_iff`,
`isAbsSummable_geometricSeq`, `sphere_subset_ROC_geometricSeq`, `isBIBOStable_geometricSeq`,
`isSchurStable_onePole_of_norm_lt_one`, `not_isAbsSummable_geometricSeq_two`,
`one_notMem_ROC_geometricSeq_two`, `not_isSchurStable_onePole_two`,
`candidatePoles_onePole_two`, `twoPoleFeedback`, `twoPoleFeedback_one`, `twoPoleFeedback_two`,
`delaySymbol_twoPoleFeedback`, `isSchurStable_twoPole`, `not_sum_norm_lt_one_twoPole`.

### Slice 4 — regressions and what each detects

- **The audited unstable parameter case** (`goal.md` §I.3 row S-07 asks for one):
  `not_isAbsSummable_geometricSeq_two`, `one_notMem_ROC_geometricSeq_two`, and
  `not_isSchurStable_onePole_two`. The `a = 2` one-pole system is proved *not* stable in all
  three senses, so the stable conclusions in section B depend on the parameter and are not
  proved by accident.
- **Reciprocal-convention check:** `candidatePoles_onePole` computes the candidate pole set
  exactly, as a singleton, and `candidatePoles_onePole_two` pins it at `2` rather than at `2⁻¹`.
  A reversed `z` versus `z⁻¹` convention fails here.
- **The criterion is strictly sufficient:** `twoPoleFeedback` has denominator symbol
  `(u - 2) ^ 2 / 4`, so its only candidate pole is `2⁻¹` and `isSchurStable_twoPole` holds; but
  its feedback coefficients have total modulus `5 / 4`, so `not_sum_norm_lt_one_twoPole` shows
  `isSchurStable_of_sum_norm_lt_one` does not apply to it. Necessity of the coefficient
  criterion is thereby refuted, not merely left unclaimed.

### Slice 4 gates

Same set, all clean over all eight files: build; `lean -Dwarn.sorry=false
-Dweak.says.verify=true` gives zero output on each; the Batteries declaration linter set run
module-scoped over all eight modules passes; `module_doc_lint` and `style_lint` rules re-run
locally pass; no `sorry`, `axiom`, `native_decide`, or `set_option maxHeartbeats`; no
`Physlib.Optics` import; imports minimal.

### Slice 4 — milestone and ledger rows

`goal.md` §H.4 S5, "absolute-summability/BIBO stability results and their relation to poles and
the region of convergence for the selected causal rational class" — done to the extent stated
above, with the two withheld directions named in the module doc rather than silently skipped.

`goal.md` §H.4 S4P, "discrete-time Schur stability and BIBO equivalence only for a stated proper
causal rational class" — the class is stated (`IsRecurrenceSolution` with feedback lags `s` and
`0 ∉ s` where needed), and the equivalence is deliberately **not** asserted; only the proved
implications are.

`goal.md` §I.3 row S-07, "pole/zero/stability theorems include the audited unstable parameter
case" — the unstable case is present and proved for this lane's one-pole system. The DCDR
instance of S-07 is S-track work.

---

## Slice 5 — files

- `Physlib/Mathematics/ZTransform/Inverse.lean` (240 lines)
- `Physlib/Mathematics/ZTransform/InverseRegression.lean` (168 lines)

### Registrations needed in `Physlib.lean` (cumulative, all ten)

```
public import Physlib.Mathematics.ZTransform.Basic
public import Physlib.Mathematics.ZTransform.BasicRegression
public import Physlib.Mathematics.ZTransform.Convergence
public import Physlib.Mathematics.ZTransform.ConvergenceRegression
public import Physlib.Mathematics.ZTransform.DifferenceEquation
public import Physlib.Mathematics.ZTransform.DifferenceEquationRegression
public import Physlib.Mathematics.ZTransform.Inverse
public import Physlib.Mathematics.ZTransform.InverseRegression
public import Physlib.Mathematics.ZTransform.Stability
public import Physlib.Mathematics.ZTransform.StabilityRegression
```

Alphabetical order satisfies the dependency order (`Inverse` needs only `Convergence`;
`InverseRegression` needs `BasicRegression` and `Inverse`).

### The route taken, and the one gap

The controller pre-approved the fallback route, and it is the route taken. JAL'18 Theorem 15
recovers the samples as Taylor coefficients,
`f n = D^n (fun z => transform f z⁻¹) 0 / n !`. That form needs the power series in the
reciprocal variable exhibited as an analytic function with its radius of convergence, and then
Mathlib's `HasFPowerSeriesAt` to iterated-derivative machinery. **That form is not proved.**

Instead the samples are recovered by limits at infinity, which is the same content by a
different route and needs no complex differentiation:

- `tendsto_transform_cobounded` (JAL'18 Thm. 17, initial value): `transform f z → f 0` as `z`
  leaves every bounded set.
- `tendsto_inversion_cobounded` (the inversion formula, JAL'18 Thm. 15 in a different form):
  `z ^ m * (transform f z - ∑ n < m, f n * z⁻¹ ^ n) → f m`.
- `eq_natCast_of_transform_eqOn` and `eq_of_isCausal_of_transform_eqOn` (JAL'18 Thm. 16,
  uniqueness).

Everything rests on one elementary quantitative estimate,
`norm_transform_sub_apply_zero_le`: if `w ∈ ROC f` and `‖w‖ ≤ ‖z‖` then
`‖transform f z - f 0‖ ≤ seriesMass f w * (‖w‖ / ‖z‖)`. That estimate uses slice 2's
modulus-only comparison; no analyticity, no contour integral, no partial fractions.

**Gap, stated rather than papered over:** the Taylor-coefficient form of Theorem 15 is not
proved. The module doc of `Inverse.lean` says so and says what it would cost. Ledger row ZT-08
should therefore be marked as reached *in content* but not in the source's literal formula, or
kept open, at the reviewer's discretion.

### A correction to the source's uniqueness statement

JAL'18 Theorem 16 states uniqueness with no causality hypothesis, because the source works with
one-sided sequences where the question cannot arise. This lane's sequences are two-sided, and the
unilateral transform never sees a negative index. So uniqueness of the *sequence* genuinely needs
causality, and without it only the nonnegative-index samples are determined.

This is proved, not assumed. `Physlib.ZTransform.shiftedImpulse` is the unit impulse with one
extra sample at index `-1`. `transform_shiftedImpulse_eq` proves its transform equals the unit
impulse's at **every** point, and `shiftedImpulse_ne_unitImpulse` proves the two sequences are
different. So `eq_of_isCausal_of_transform_eqOn` cannot have its causality hypothesis dropped,
and `eq_natCast_of_transform_eqOn` is exactly as strong as it can be.

### Slice 5 — declarations

`Physlib/Mathematics/ZTransform/Inverse.lean`, namespace `Physlib.ZTransform`:
`seriesMass`, `seriesMass_nonneg`, `norm_seriesTerm_succ_le`,
`norm_transform_sub_apply_zero_le`, `tendsto_norm_ratio_cobounded`,
`tendsto_transform_cobounded`, `tendsto_inversion_cobounded`, `eq_natCast_of_transform_eqOn`,
`eq_of_isCausal_of_transform_eqOn`.

`Physlib/Mathematics/ZTransform/InverseRegression.lean`, same namespace: `shiftedImpulse`,
`summable_seriesTerm_regressionAtNegOne`, `transform_shiftedImpulse_eq`,
`shiftedImpulse_ne_unitImpulse`, `shiftedImpulse_not_isCausal`, `two_mul_mem_ROC_geometric`,
`tendsto_transform_geometricSeq`, `tendsto_inversion_geometricSeq_one`,
`eq_geometricSeq_of_transform_eq`.

### Slice 5 — regressions and what each detects

- **Uniqueness without causality is false**: the `shiftedImpulse` pair above. This is the only
  regression in the lane that refutes a source statement's applicability in this setting rather
  than confirming one.
- **The inversion formula is instantiated, not just stated**: `tendsto_transform_geometricSeq`
  recovers the geometric sequence's sample at index zero, and
  `tendsto_inversion_geometricSeq_one` recovers its sample at index one as the ratio `a`.
- **Uniqueness used in the direction that matters**: `eq_geometricSeq_of_transform_eq` proves
  that any *causal* sequence whose transform is the one-pole rational function on a suitable
  exterior *is* the geometric sequence. That is a characterization rather than a computation,
  and it is the shape the system-level track needs when it identifies a network response with a
  recurrence.

### Slice 5 gates

Same set, all clean over all ten files: build; `lean -Dwarn.sorry=false -Dweak.says.verify=true`
gives zero output on each; the Batteries declaration linter set run module-scoped over all ten
modules passes; `module_doc_lint` and `style_lint` rules re-run locally pass; no `sorry`,
`axiom`, `native_decide`, or `set_option maxHeartbeats`; no `Physlib.Optics` import; imports
minimal.

### Slice 5 — ledger rows

- **ZT-08** (JAL'18 Def. 19 + Thm. 15, pp. 893-894) — `IsExteriorOfCircle` and the region-shape
  lemmas were reached in slice 2. The inverse transform is reached **in content**, as
  `tendsto_inversion_cobounded`, but **not** in the source's Taylor-coefficient formula. See the
  gap above.
- **ZT-09** (JAL'18 Thm. 16 uniqueness and Thm. 17 initial value, p. 894) — reached, with
  Thm. 16 corrected by an explicit causality hypothesis that the source's one-sided setting
  hides, and with that hypothesis proved necessary.

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
