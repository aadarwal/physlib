# S7C slice 2 handoff

## Cutoff

- Branch: `optics/s7c-cascade`
- Required sync target: `aff2484ecc7fd14f456b0c85a71d282c6b4f4052`
- Target merge already present: `cf0061a59fdfe47db06e1b6628ea3ba8b4bad867`
- Prior slice-1 U2-ready cutoff: `74ceb587ae085fe891b0f093390202e43d3ed592`
- Slice: identical DATE cascades and Sylvester/Chebyshev form (IP-16/IP-17, H-04/H-05)

`aff2484e` is an ancestor of this cutoff. No later development head was selected.

## Files and registrations

Slice 2 adds these modules, in sorted registry order:

- `Physlib.Optics.Systems.Cascade.Identical`
- `Physlib.Optics.Systems.Cascade.IdenticalRegression`

This branch still contains the four U2-ready slice-1 modules. Because the required sync target's
registry predates their conductor merge, the exact cutoff gate temporarily registered all six:

- `Physlib.Optics.Network.TwoPortChainFold`
- `Physlib.Optics.Network.TwoPortChainFoldRegression`
- `Physlib.Optics.Systems.Cascade.Heterogeneous`
- `Physlib.Optics.Systems.Cascade.HeterogeneousRegression`
- `Physlib.Optics.Systems.Cascade.Identical`
- `Physlib.Optics.Systems.Cascade.IdenticalRegression`

If slice 1 has already been registered when this cutoff is merged, only the two slice-2 imports
remain to add. No `Physlib.lean` edit is committed on this branch.

## Declarations

### `Physlib/Optics/Systems/Cascade/Identical.lean`

- `MicroringCascade.dateIdenticalCascadeBehavior`
- `MicroringCascade.dateIdenticalCascadeComposition`
- `MicroringCascade.dateIdenticalCascadeComposition_eq_pow`
- `MicroringCascade.dateIdenticalCascadeBehavior_eq_pow_toBehavior`
- `MicroringCascade.dateChainEntry`
- `MicroringCascade.dateChainHalfTrace`
- `MicroringCascade.dateChebyshevCoefficient`
- `MicroringCascade.dateChebyshevClosedForm`
- `MicroringCascade.dateChain_trace_eq_entry11_add_entry22`
- `MicroringCascade.dateChebyshevCoefficient_recurrence`
- `MicroringCascade.dateChain_sq_eq_trace_smul_sub_one`
- `MicroringCascade.dateChain_pow_eq_chebyshevClosedForm_of_det_eq_one`
- `MicroringCascade.DateSylvesterHypotheses`, with fields:
  - `det_eq_one`
  - `entry11_re_gt_neg_one`
  - `entry11_re_lt_one`
  - `entry22_eq_conj_entry11`
  - `entry12_eq_conj_entry21`
- `MicroringCascade.dateSylvesterAngle`
- `MicroringCascade.dateSylvesterSineCoefficient`
- `MicroringCascade.dateSylvesterClosedForm`
- `MicroringCascade.DateSylvesterHypotheses.halfTrace_eq_entry11_re`
- `MicroringCascade.DateSylvesterHypotheses.sin_angle_ne_zero`
- `MicroringCascade.DateSylvesterHypotheses.halfTrace_eq_cos_angle`
- `MicroringCascade.DateSylvesterHypotheses.chebyshevCoefficient_eq_sineCoefficient`
- `MicroringCascade.dateChain_pow_eq_sylvesterClosedForm`
- `MicroringCascade.dateIdenticalCascadeComposition_eq_sylvesterClosedForm`

### `Physlib/Optics/Systems/Cascade/IdenticalRegression.lean`

- `MicroringCascade.dateIdenticalCascadeRegression_two_by_hand`
- `MicroringCascade.dateIdenticalCascadeRegression_three_by_hand`
- `MicroringCascade.dateSylvesterRegressionMatrix`
- `MicroringCascade.dateSylvesterRegressionMatrix_det`
- `MicroringCascade.dateSylvesterRegressionMatrix_hypotheses`
- `MicroringCascade.dateSylvesterRegressionMatrix_pow_two`
- `MicroringCascade.dateSylvesterRegressionMatrix_pow_three`
- `MicroringCascade.dateSylvesterRegressionMatrix_closedForm_two`
- `MicroringCascade.dateSylvesterRegressionMatrix_closedForm_three`
- `MicroringCascade.dateSylvesterRegression_identity_exact_failure`
- `MicroringCascade.dateSylvesterRegression_identity_not_hypotheses`
- `MicroringCascade.dateSylvesterRegression_identity_closedForm_false`

## Exact source domain

The source hypothesis `|m| = 1` is represented as the actual matrix determinant equation

```text
Matrix.det matrix = 1
```

and not as a matrix norm. `DateSylvesterHypotheses` retains all four source conditions:

```text
Matrix.det matrix = 1
-1 < Re(m11)
Re(m11) < 1
m22 = conj(m11)
m12 = conj(m21)
```

`dateChainEntry` uses the source reindex in which `0` is backward and `1` is forward. Diagonal
conjugacy proves `trace(matrix)/2 = Re(m11)`. The strict interval puts
`dateSylvesterAngle matrix = arccos(Re(m11))` in `(0, pi)`, hence its sine is nonzero.

The source sine display is represented exactly as

```text
sin(N * theta) / sin(theta) * matrix
  - sin((N - 1) * theta) / sin(theta) * 1
```

The definition is totalized, while `dateChain_pow_eq_sylvesterClosedForm` and the identical
cascade corollary require the complete source structure. The weaker polynomial identity
`dateChain_pow_eq_chebyshevClosedForm_of_det_eq_one` needs only determinant one; no source sine
claim is inferred from that weaker fact.

## Milestone and parity disposition

This slice discharges the quoted S7C bullets:

- "an identical-`N` cascade as a chain-matrix power" (`goal.md:2421`); and
- "a Sylvester/Chebyshev closed form with its actual determinant and trace-domain assumptions"
  (`goal.md:2422`).

It satisfies H-04, quoted as "an identical-`N` cascade equals the corresponding matrix power"
(`goal.md:2589`), through `dateIdenticalCascadeComposition_eq_pow`. This equality is totalized and
needs no ring pivot. Its relational graph corollary separately requires
`stage.HasBijectiveRingTransmission`.

It satisfies H-05, quoted as "the Sylvester/Chebyshev cascade form holds with its determinant and
trace-domain assumptions" (`goal.md:2590`), through
`dateIdenticalCascadeComposition_eq_sylvesterClosedForm` under the complete structure above.

Thus the declarations identify discharges for:

- IP-16, DATE'14 Thm. 4, through `dateIdenticalCascadeComposition_eq_pow`; and
- IP-17, DATE'14's unnumbered Sylvester result, through
  `dateIdenticalCascadeComposition_eq_sylvesterClosedForm`.

The source rows are recorded at
`/Users/aadarwal/src/aadarwal/physlib-parity/PARITY-LEDGER.md:123-124`. A ledger status flip still
belongs to the conductor/reviewer gate, not this lane.

## Independent regressions

The H-04 regressions unfold `List.replicate`, `dateCascadeComposition`, and the neutral fold
directly at `N = 2` and `N = 3`. They do not call
`dateIdenticalCascadeComposition_eq_pow` or `fold_replicate`.

The H-05 positive fixture is `diag(I, -I)`. Its determinant and source structure are computed
directly. Its powers are independently expanded entry by entry through `Matrix.mul_apply`:

```text
matrix ^ 2 = -1
matrix ^ 3 = -matrix
```

The two source sine candidates are evaluated independently to those same values. Neither proof
calls Cayley--Hamilton, the Chebyshev power lemma, or either Sylvester headline theorem.

The negative control is the identity matrix. It satisfies determinant one, the lower bound, and
both conjugacy equations, but fails only `Re(m11) < 1`. At this excluded boundary,
`theta = 0`, totalized `sin(theta) / sin(theta) = 0`, and the following is proved:

```text
(1 : BackwardFirstChainTransform Unit Unit) ^ 1 != dateSylvesterClosedForm 1 1
```

The failed source condition is therefore load-bearing, and the fixture can fail mechanically.

## Validation bindings

The validation lane should bind these exact public names:

- `Optics.MicroringCascade.dateIdenticalCascadeComposition_eq_pow`
- `Optics.MicroringCascade.dateIdenticalCascadeBehavior_eq_pow_toBehavior`
- `Optics.MicroringCascade.DateSylvesterHypotheses`
- `Optics.MicroringCascade.dateChebyshevClosedForm`
- `Optics.MicroringCascade.dateChain_pow_eq_chebyshevClosedForm_of_det_eq_one`
- `Optics.MicroringCascade.dateSylvesterClosedForm`
- `Optics.MicroringCascade.dateChain_pow_eq_sylvesterClosedForm`
- `Optics.MicroringCascade.dateIdenticalCascadeComposition_eq_sylvesterClosedForm`
- `Optics.MicroringCascade.dateIdenticalCascadeRegression_two_by_hand`
- `Optics.MicroringCascade.dateIdenticalCascadeRegression_three_by_hand`
- `Optics.MicroringCascade.dateSylvesterRegressionMatrix_pow_two`
- `Optics.MicroringCascade.dateSylvesterRegressionMatrix_pow_three`
- `Optics.MicroringCascade.dateSylvesterRegressionMatrix_closedForm_two`
- `Optics.MicroringCascade.dateSylvesterRegressionMatrix_closedForm_three`
- `Optics.MicroringCascade.dateSylvesterRegression_identity_exact_failure`
- `Optics.MicroringCascade.dateSylvesterRegression_identity_closedForm_false`

The prior U2 Markdown nit is fixed here: the full name
`Optics.MicroringCascade.DateCascadeStage.hasBijectiveRingTransmission_iff_forwardTransfer_ne_zero`
is now one code span.

## Reused anchors and conventions

- DATE Thm. 4 and the unnumbered Sylvester result are recorded at
  `/Users/aadarwal/src/aadarwal/physlib-parity/HOL-CORPUS.md:204-207`.
- The ledger records IP-16/IP-17 and the complete source assumptions at
  `/Users/aadarwal/src/aadarwal/physlib-parity/PARITY-LEDGER.md:123-124`.
- The neutral fold and its replicate-to-power result are at
  `Physlib/Optics/Network/TwoPortChainFold.lean:90-114`.
- DATE coordinate `0` backward and coordinate `1` forward are fixed at
  `Physlib/Optics/Systems/Microring/SourceBridgeDate.lean:990-1022`.
- The one-stage DATE product `continuity ** ring` is at
  `Physlib/Optics/Systems/Cascade/Heterogeneous.lean:145-148`.
- Mathlib's second-kind recurrence and base values are in
  `Mathlib/RingTheory/Polynomial/Chebyshev.lean:265-304`.
- Mathlib's real trigonometric characterization is in
  `Mathlib/Analysis/SpecialFunctions/Trigonometric/Chebyshev/Basic.lean:147-156`.
- The modal-to-electromagnetic power bridge and its qualifications are at
  `Physlib/Optics/HarmonicFlux/PropagatingModePower.lean:16-22,60-93`.

## Non-claims

- The source sine form is claimed only under all fields of `DateSylvesterHypotheses`.
- The determinant-one Chebyshev core does not weaken the source sine theorem's trace domain.
- The totalized sine quotient is not asserted at a zero denominator or outside the strict bound.
- "Resonance" terminology is withheld.
- No quadruple-ring parity row is claimed.
- No termination, coupled lattice, full `M x N` lattice, or Physlib-original lattice result is
  claimed in this slice.
- Effective index is fixed at the selected carrier. There is no dispersion, bending loss,
  bandwidth, causality, passivity, reciprocity, or material-realization claim.
- Power remains normalized modal power. Electromagnetic power requires the finite,
  common-frequency, Maxwell-qualified, pairwise-integrable, mutually flux-orthogonal,
  unit-normalized measured-profile hypotheses of the cited bridge.
- Any later SFG-TR'14/NSV'16 comparison must retain IP-12's explicit principal-root versus
  selected-half-arc equality; this slice makes no such comparison.

## Gate record

The exact post-sync source head gated for slice 2 is
`7c6a7bd2d2fc34415bef6dca3d58f4a74ebd4b8f`. It contains every Lean and substantive handoff
change in this cutoff and has `aff2484e` as an ancestor. With all six cumulative S7C modules
temporarily registered in sorted order, this single locked command exited successfully:

```text
lake-lock env bash -c 'set -euo pipefail && lake exe cache get &&
  lake --wfail build Physlib.Optics.Network.TwoPortChainFold
    Physlib.Optics.Network.TwoPortChainFoldRegression
    Physlib.Optics.Systems.Cascade.Heterogeneous
    Physlib.Optics.Systems.Cascade.HeterogeneousRegression
    Physlib.Optics.Systems.Cascade.Identical
    Physlib.Optics.Systems.Cascade.IdenticalRegression &&
  lake exe runPhyslibLinters && lake exe lint_all'
```

- Cache retrieval downloaded no files.
- All six modules built with warnings as errors; Lake completed 2,761 jobs successfully.
- `runPhyslibLinters` passed for Physlib and QuantumInfo.
- `lint_all` completed all seven stages and exited zero.
- Its build, illegal-import, PhyslibAlpha-import, duplicate-tag, sorry/pseudo, and declaration
  linter stages passed.
- The file-import inventory named only five pre-existing unregistered files: two under
  `Physlib/Electromagnetism/**` and three under `Physlib/SpaceAndTime/**`. It named no S7C file.
- The advisory style and transitive-import inventories contain only repository-baseline files and
  no S7C file. The initially detected redundant direct Charpoly import was removed before this
  recorded rerun.
- The committed-state `./scripts/lint-style.sh` check passed at the exact source head.
- The temporary registry edit was restored byte-identically. Pre-edit and post-edit SHA-256 were
  both `9b7092d5e30e9c9c618e07892d20d2f45535c4d259f5280946bad68234aba787`.

The final cutoff-record commit changes only this gate record; no Lean source differs from the
exact gated source head above.
