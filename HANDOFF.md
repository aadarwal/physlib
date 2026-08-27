# S7D slice 13 handoff: L11 printed/script stability-name split

## Cutoff identity

- Branch: `optics/s7d-dcdr`.
- Exact battery-green sync target:
  `c5bcc6c677f593025e1f87e0d9ce9109fc7564bd`.
- Exact sync merge: `4e390aaeefe4e08334cb8ae43cae607841de0f78`.
- Gated source: `4e390aaeefe4e08334cb8ae43cae607841de0f78`.
- This file is the HANDOFF-only cutoff child; its hash is reported externally.
- `Physlib.lean` is byte-identical to the exact sync target; SHA-256:
  `a976cd77f35af6365f00cf0849d356235210342c6143ef1a2dd43dd590555fa2`.
- Generic `Physlib/Optics/Systems/DelayTransfer/Stability.lean` is byte-identical to the sync
  target; SHA-256:
  `d0157c4f20fd93fcb709557545f825d18815a20b8fdd7d8c06e42feda9e22844`.
- `goal.md` is byte-identical to the sync target; SHA-256:
  `d1b720418e1dcd197054f42fbce76db6cb393397269a3274560459a48f547317`.

The Lean source delta against the sync target is exactly six existing files, all under
`Physlib/Optics/Systems/DCDR/`. No module is added or removed, no registration changes, and every
non-DCDR source file is byte-identical to the sync target. The preliminary implementation was
committed before the sealed-head merge; the merge retained this lane-local HANDOFF as intended.

This is part of the human-authorized final research window in
`scratchpad/lanes/RESEARCH-FREEZE-PLAN.md`. No later S7D slice or proposal is implied.

## Goal and decision resolution

At this cutoff, `goal.md:2767-2768` says verbatim:

> - [ ] Confirm whether each stability condition is strict or non-strict and whether it concerns
>   poles, zeros, an internal operator, BIBO behavior, or a source-specific named condition.

This slice implements option 1 and the mandatory names in
`scratchpad/lanes/decisions/decision-L11.md`, with compatibility restricted exactly as specified
in `scratchpad/lanes/decisions/registry-draft-A2.md:33-36`. Generic Schur stability and generic
reduced-zero predicates remain strict and unchanged. Printed FMICS'15 predicates now carry
explicit open-disk names; recovered-script predicates carry explicit closed-disk names. Printed
Theorem 4 retains `G1 * G2`, while the script-specific sibling writes `G1 * G3` directly. No API
joins those source conventions.

The deprecated `PrintedIncoherentAllZerosInsideUnitDisk` spelling targets only
`PrintedIncoherentAllZerosInsideOpenUnitDisk`. No compatibility result preserves the ambiguous
old result name.

## Exact declaration contract

The declaration list below is exactly the confirmed six-file contract. Every citation points to
the line containing the declaration keyword.

### Production source split

- `PrintedIncoherentAllPolesInsideOpenUnitDisk` —
  `Physlib/Optics/Systems/DCDR/SourceBridge.lean:213`.
- `FMICSScriptInClosedUnitDisk` —
  `Physlib/Optics/Systems/DCDR/SourceBridge.lean:217`.
- `FMICSScriptAllPolesInClosedUnitDisk` —
  `Physlib/Optics/Systems/DCDR/SourceBridge.lean:226`.
- `FMICSScriptIncoherentStabilityConditions` —
  `Physlib/Optics/Systems/DCDR/SourceBridge.lean:235`.
- `printedIncoherentZeroSet` —
  `Physlib/Optics/Systems/DCDR/Observables.lean:136`.
- `PrintedIncoherentAllZerosInsideOpenUnitDisk` —
  `Physlib/Optics/Systems/DCDR/Observables.lean:147`.
- `PrintedIncoherentAllZerosInsideUnitDisk` (deprecated spelling) —
  `Physlib/Optics/Systems/DCDR/Observables.lean:153`.
- `FMICSScriptAllZerosInClosedUnitDisk` —
  `Physlib/Optics/Systems/DCDR/Observables.lean:159`.
- `printedIncoherent_allZerosInsideOpenUnitDisk_of_strict` —
  `Physlib/Optics/Systems/DCDR/Observables.lean:213`.

The contracted result rename removes
`printedIncoherent_allZerosInsideUnitDisk_of_strict`
(`Physlib/Optics/Systems/DCDR/Observables.lean:185 @ c5bcc6c6`) in favor of the explicit Open
name above. No compatibility alias preserves that ambiguous result spelling.

`Observables.lean` changes its production import from `DCDR.Poles` to `DCDR.SourceBridge` so its
source-provenance predicates reuse the explicit paper/script dictionary. `SourceBridge` already
imports `Poles`, so the change introduces no cycle. Production imports no regression module.

### Pole-boundary regression

- `sourcePoleBoundarySet` —
  `Physlib/Optics/Systems/DCDR/PolesRegression.lean:111`.
- `printedIncoherentAllPolesInsideOpenUnitDisk_boundary_fails` —
  `Physlib/Optics/Systems/DCDR/PolesRegression.lean:115`.
- `fmicsscriptAllPolesInClosedUnitDisk_boundary` —
  `Physlib/Optics/Systems/DCDR/PolesRegression.lean:122`.
- `printedOpen_scriptClosed_poleBoundary_disagree` —
  `Physlib/Optics/Systems/DCDR/PolesRegression.lean:134`.

### Theorem-4 index regression

- `sourceThmFourMismatch_printedExpression` —
  `Physlib/Optics/Systems/DCDR/SourceBridgeRegression.lean:331`.
- `sourceThmFourMismatch_scriptExpression` —
  `Physlib/Optics/Systems/DCDR/SourceBridgeRegression.lean:339`.
- `sourceThmFourMismatch_printedConditions` —
  `Physlib/Optics/Systems/DCDR/SourceBridgeRegression.lean:370`.
- `sourceThmFourMismatch_scriptConditions_fail` —
  `Physlib/Optics/Systems/DCDR/SourceBridgeRegression.lean:380`.
- `sourceThmFourMismatch_conditions_disagree` —
  `Physlib/Optics/Systems/DCDR/SourceBridgeRegression.lean:399`.

### Zero-boundary regression

- `printedIncoherentZeroSet_boundary_eq_pair` —
  `Physlib/Optics/Systems/DCDR/ObservablesRegression.lean:398`.
- `printedIncoherentAllZerosInsideOpenUnitDisk_boundary_fails` —
  `Physlib/Optics/Systems/DCDR/ObservablesRegression.lean:432`.
- `fmicsscriptAllZerosInClosedUnitDisk_boundary` —
  `Physlib/Optics/Systems/DCDR/ObservablesRegression.lean:440`.
- `printedOpen_scriptClosed_zeroBoundary_disagree` —
  `Physlib/Optics/Systems/DCDR/ObservablesRegression.lean:454`.

The contracted regression rename removes
`printedIncoherentAllZerosInsideUnitDisk_boundary_fails`
(`Physlib/Optics/Systems/DCDR/ObservablesRegression.lean:387 @ c5bcc6c6`) in favor of the
explicit Open name above.

### Passive supplied-list audit

- `passiveReportedPoleSet` —
  `Physlib/Optics/Systems/DCDR/PassiveCaseRegression.lean:736`.
- `passiveReportedPoleSet_fmicsscriptClosed` —
  `Physlib/Optics/Systems/DCDR/PassiveCaseRegression.lean:793`.
- `passiveReportedPoleSet_not_subset_zPoles` —
  `Physlib/Optics/Systems/DCDR/PassiveCaseRegression.lean:802`.
- `passiveReportedPoleSet_failedSuppliedValidity` —
  `Physlib/Optics/Systems/DCDR/PassiveCaseRegression.lean:813`.

No declaration beyond this list and the two stated predecessor removals is added, removed, or
renamed.

## Independent disagreement teeth

The three source-convention regressions expand from Mathlib primitives rather than through a
paper/script conversion result:

1. Pole boundary: `sourcePoleBoundarySet = {1}`. The primitive complex norm is exactly one, so
   printed `< 1` is false and script `<= 1` is true.
2. Zero boundary: at `(G1,G2,G3,k1,k2) = (1,1,1,0,0)`, direct factorization of `q - q^3`
   gives the finite reciprocal-zero set `{1,-1}`. Both norms are exactly one, so printed open
   fails and script closed holds on the same set.
3. Theorem-4 index: at `(1,1/4,4,1,1)`, literal products give the printed `G1*G2`
   expression `1/4` and the script `G1*G3` expression `4`. The printed conditions hold, while
   the script bound fails because `norm (sqrt 4) = 2`.

Swapping strictness, collapsing `G2` with `G3`, dropping either boundary element, or using one
source predicate to establish its sibling breaks a regression.

## No-join audit

The required declaration-aware audit over the six touched files reports:

1. Zero production declaration types contain both `Printed...` and `FMICSScript...`.
2. Zero equality, `iff`, implication, alias, coercion, or conversion declaration relates the two
   families in either direction. The mathematically true open-implies-closed result is
   deliberately not shipped.
3. The only regression declaration types containing both prefixes are the three `_disagree`
   negative conjunctions listed above.
4. Each disagreement conjunct is proved independently from primitive expansion; neither is
   derived through the other source predicate.
5. The deprecated old zero-predicate spelling aliases only the new Printed-open spelling.

## IP-11 / D08 correction

`Physlib/Optics/Systems/DCDR/PassiveCaseRegression.lean` now cites the recovered script and the
two-axis ledger restatement directly. The pinned source classification is
`physlib-parity/PARITY-LEDGER.md:169 @ ccf4104`: D08 is SUBSTANTIVE x PRINT-ONLY. The printed
actual-system instability prose is wrong, while the authors' recovered script is right.

The script distinguishes `unstable_psp` from `unstable_psp_given_poles` at
`hol-optics-scripts/extracted/sfg/sfg/Stability_Resonance.ml:79-104`; its passive result is
`fausse_example2` at `hol-optics-scripts/extracted/sfg/sfg/Application.ml:1364-1374` and proves
only the supplied-list predicate. Exact arithmetic supplies the other half of the audit:

- actual reciprocal-`z` poles are `+/-sqrt(41/50)`;
- their squared modulus is `41/50 < 1`, and the exact reduced response is Schur-stable;
- the supplied decimals `+/-905539/1000000` are rounded nonroots;
- the supplied set passes the script's closed-disk test but is not a subset of exact poles.

Accordingly, the shipped characterization is **failed supplied-decimal validity**, never actual
DCDR instability. No code from the recovered script is adapted.

## Registration and milestone discharge

All six files are already registered modules. No `Physlib.lean` edit or conductor registration is
requested. Subject to review, this implements the source-specific open/closed registry entries
required to close the quoted L11 decision gate; the conductor owns any `goal.md` or registry flip.

## Gate record

- Post-sync six-module targeted build with warnings as errors: green, 2787 jobs.
- Root `lake-lock build Physlib -KwarningAsError=true`: green, 5035 jobs.
- `lake-lock exe check_file_imports`: green; every file is registered.
- `lake-lock exe sorry_lint`: green.
- `lake-lock exe runPhyslibLinters`: green for Physlib and QuantumInfo.
- `lake-lock exe api_map_index`: green; 34 maps, 653 requirements, 506 done.
- `lake-lock exe lint_all`: exit 0. Build, import, sorry, and semantic stages are green;
  output contains only the sealed head's established advisory style/transitive-import baseline.
- `lake-lock exe module_doc_lint`: repository baseline exit 1 with 147 error headers;
  touched-file error-header filter is empty (0/6 touched modules).
- `./scripts/lint-style.sh`: green on committed synced source.
- `git diff --check`: green.
- Lean source delta: six existing DCDR files, 338 insertions, 42 deletions.
- File cap: all touched Lean files are under 1500 lines; maximum is 914 lines.
- Maximum touched Lean line length: 99 Unicode codepoints.
- Added banned declarations/options: 0. Added `theorem` declarations: 0.
- No-join declaration audit: green as itemized above.
- Declaration-line citations: all 26 verified against the gated source in one extraction pass.

The first post-sync Lean attempt did not start: `lake-lock` found 27 GB free against its 30 GB
safety floor. The controller removed only retired build caches, restoring 37 GiB of headroom;
every gate above then completed. Source and preliminary HANDOFF commits were pushed before each
long lock hold, so no work remained crash-exposed.

## Non-claims and human review

This slice makes no physical-resonance claim, no coherent-incoherent equivalence, no BIBO
generalization beyond existing stated gates, no normalized-modal or electromagnetic-power claim,
no causality or time-domain claim, no physical-frequency claim, no reciprocity claim, and no
claim about Binh [5]. It does not identify solve gates, admissibility, contraction, ROC membership,
internal singularities, candidate poles, actual poles, cancellation, Schur stability, zero
location, or BIBO behavior.

Per `decision-L11.md`, Human-only is **no** for this fork naming and strictness decision. If this
material were ever upstreamed, a human would separately certify source licensing and attribution.
