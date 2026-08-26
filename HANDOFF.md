# S7D slice 4 handoff: DCDR zero-location observables

## Cutoff identity

- Branch: `optics/s7d-dcdr`.
- Required sync target: `6f474de29aeec37d454a69e6398540470d4e56df`.
- Exact sync merge: `fa3fac439f67f8f93860e058e318764cf41ad2ec`.
- Gated Lean source head: `612290159600d952b77cde52b57434f9dbd861d5`.
- Source commits after the sync merge:
  - `3faca6fd` — define the coherent observable and audited printed-incoherent conditions.
  - `61229015` — add direct positive, negative, and printed-boundary sentinels.
- The final cutoff commit is a HANDOFF-only child of the gated source head.

## Files and registration request

New modules:

- `Physlib/Optics/Systems/DCDR/Observables.lean` — 220 lines.
- `Physlib/Optics/Systems/DCDR/ObservablesRegression.lean` — 394 lines.

Register these sorted imports in `Physlib.lean` between `Netlist` and `Poles`:

```lean
public import Physlib.Optics.Systems.DCDR.Observables
public import Physlib.Optics.Systems.DCDR.ObservablesRegression
```

The named sync target predates the conductor's slice-3 registration. Therefore the cutoff gate
temporarily registered `Poles`, `PolesRegression`, `Observables`, and `ObservablesRegression`.
The temporary edit was removed after the gate; `Physlib.lean` is byte-identical to the sync state
(SHA-256 `c6fcae741d8c29643e5ca027773ee5b1e30968c1a3731a26fef32764a4af7f48`).

Every DCDR module remains below the 1500-line cap. The largest are unchanged:
`ResponseRegression.lean` has 1397 lines and `Bridge.lean` has 1362 lines. The maximum line in the
two new modules is 99 codepoints.

## Slice result

### 1. Coherent response-level observable

`ResponseReduction.allZerosInsideUnitDisk` (`Observables.lean:79-86`) is a predicate on the
response-indexed reduction certificate introduced in slice 3. It is exactly S4's
`ReducedRationalResponse.AllZerosInsideUnitDisk`, hence quantifies over finite reciprocal-`z`
zeros after response cancellation. It is not a predicate on formal-`q` roots and is not a formula
container detached from the selected DCDR response.

The name states only the literal mathematics. FMICS'15 Definition 7 calls this condition
"resonance", but the source defines only
`forall z in zeros, norm z < 1` for nonzero numerator roots and proves no separate physical
resonance statement (`goal.md:2313-2318`). Physlib declines that terminology.

### 2. Printed incoherent Theorem 5 audit and source credit

The printed unit-delay numerator is transcribed as

```text
L*q - C*q^3
L = (1-k1)(1-k2)G1 + k1*k2*G2
C = (1-2*k1)(1-2*k2)G1*G2*G3.
```

The coefficient and polynomial declarations are at `Observables.lean:96-118`.
`PrintedIncoherentTheoremFiveConditions` (`:138-150`) retains all three hypotheses printed in
FMICS'15 Theorem 5:

1. `norm (Complex.sqrt (C / L)) <= 1`;
2. `C != 0`;
3. `L != 0`.

Credit is explicit in the production module (`:21-27`, `:138-142`): FMICS'15 itself says the last
two hypotheses are missing from Binh [5]'s paper-and-pencil derivation and that its Theorems 4 and
5 cannot be verified without the additional conditions. They are FMICS'15's discoveries, not
Physlib corrections. The primary-source text is
`scratchpad/papers/FMICS15_1.txt:622-638`; the corrected ledger wording is
`PARITY-LEDGER.md:116-117`.

The printed predicate is deliberately not forced into the coherent N7 response API.
`PrintedIncoherentAllZerosInsideUnitDisk` (`Observables.lean:120-130`) states the source's raw
numerator-root content for the separately printed `1-k`/`k` model. Coherent N7 `t`/`-I*k` is the
source's own unprinted coherent branch; no theorem identifies the two models.

### 3. Strictness finding and corrected sufficient statement

FMICS'15 Theorem 5 prints a non-strict `<= 1` square-root bound, while its own Definition 7
conclusion is strict `< 1`. Physlib retains the printed audit object and separately defines
`PrintedIncoherentStrictAllZerosConditions` (`Observables.lean:152-163`), which changes only that
first inequality and keeps the paper's two nonzero hypotheses.

The literature-headline adaptation
`printedIncoherent_allZerosInsideUnitDisk_of_strict` (`Observables.lean:178-216`) proves the strict
zero-location conclusion directly. For each finite root it derives
`z^2 = C/L`, uses `Complex.norm_cpow_inv_nat` to identify the norm of the principal complex square
root, and applies the strict hypothesis. It does not use the coherent response or a
coherent/incoherent bridge.

`PrintedIncoherentStrictAllZerosConditions.toTheoremFiveConditions` (`:165-170`) records only the
valid direction from strict Physlib conditions to the non-strict printed audit conditions. No
reverse implication is asserted.

The exact boundary at `G1 = G2 = G3 = 1`, `k1 = k2 = 0` gives `C = L = 1`:

- all three printed conditions hold (`ObservablesRegression.lean:363-368`);
- the strict Physlib condition fails (`:370-375`);
- direct numerator substitution gives the finite zero `z = 1` (`:377-382`); and
- the strict all-zeros predicate fails (`:384-390`).

This is the Physlib finding: the paper's non-strict first bound does not establish its own strict
Definition 7 conclusion. It does not re-credit the paper's two nonzero discoveries to Physlib.

### 4. Nonvacuous coherent positive anchor

`insideZerosParameters` (`ObservablesRegression.lean:73-79`) uses the coherent `3/5` through,
`4/5` cross-amplitude N7 coupler and gains `(20, 5, 1/100)`. Direct expansion from the coherent
rational data gives

```text
numerator   = 4*q - q^3
denominator = 1 + (11/100)*q^2.
```

The loop, denominator, and numerator expansions are at `:121-160`; none uses an observable or
response-bridge theorem. An explicit Bezout identity proves the displayed polynomials coprime
(`:209-229`), and the unit-factor rational reduction is tied to both selected DCDR raw response
polynomials (`:253-301`).

Direct substitution proves `z = 1/2` is a finite reduced zero (`:315-321`). The universal positive
anchor (`:323-340`) starts again from the expanded numerator, derives `z^2 = 1/4`, and proves
`norm z < 1`; it never invokes the production Theorem 5 adaptation. Thus the positive result is
nonvacuous and independently sensitive to the response numerator.

### 5. Coherent failing check

`boundaryZerosParameters` (`ObservablesRegression.lean:81-87`) uses the same coherent coupler and
gains `(41/9, 1, 9/41)`. Direct expansion gives

```text
numerator   = q - q^3
denominator = 1 + (23/41)*q^2.
```

The expansions are at `:162-201`, the explicit coprime reduction and response certificate are at
`:231-307`, and direct substitution proves `z = 1` is a finite reduced zero (`:342-348`).
`boundaryZerosResponseReduction_not_allZerosInsideUnitDisk` (`:350-355`) then rejects the strict
predicate from `norm 1 = 1`. This is the required check that can fail if the numerator wiring or
strictness changes.

## Reused APIs and pinned conventions

- The S4 reciprocal zero set `ReducedRationalResponse.zZeros` removes formal `q = 0` and applies
  `q = z^-1` at `Physlib/Optics/Systems/DelayTransfer/Stability.lean:141-146`.
- The reused literal predicate `ReducedRationalResponse.AllZerosInsideUnitDisk` is at
  `Physlib/Optics/Systems/DelayTransfer/Stability.lean:234-239`.
- `ReducedRationalResponse` requires nonzero coprime numerator and denominator at
  `Physlib/Optics/Systems/DelayTransfer/Poles.lean:123-136`.
- The response-indexed DCDR reduction certificate is `ResponseReduction` at
  `Physlib/Optics/Systems/DCDR/Poles.lean:647-654`.
- The coherent polynomial numerator and denominator are
  `UnitDelayParameters.responseNumeratorPolynomial` and `.denominatorPolynomial` at
  `Physlib/Optics/Systems/DCDR/Poles.lean:160-196`.
- The N7 directional-coupler cross coefficient is exactly `-I*k` at
  `Physlib/Optics/Components/DirectionalCoupler.lean:62-70`.
- FMICS'15 Definition 7 and Theorem 5 are indexed at
  `/Users/aadarwal/src/aadarwal/physlib-parity/HOL-CORPUS.md:316-323`.
- The primary printed Theorem 5 hypotheses and source-credit paragraph are at
  `/private/tmp/claude-501/-Users-aadarwal-src-aadarwal-physlib/25cc2ec7-865f-4379-ab2d-a78ab2bf365b/scratchpad/papers/FMICS15_1.txt:622-638`.

## Public declarations

All declarations are in namespace `Optics.DCDR`, except the first definition is nested under
`Optics.DCDR.ResponseReduction`.

Production declarations in `Observables.lean`:

- `ResponseReduction.allZerosInsideUnitDisk` (`:85`).
- `printedIncoherentZeroLinearCoefficient` (`:97`).
- `printedIncoherentZeroCubicCoefficient` (`:102`).
- `printedIncoherentZeroPolynomial` (`:107`).
- `eval_printedIncoherentZeroPolynomial` (`:113`).
- `PrintedIncoherentAllZerosInsideUnitDisk` (`:126`).
- `PrintedIncoherentTheoremFiveConditions` (`:144`).
- `PrintedIncoherentStrictAllZerosConditions` (`:157`).
- `PrintedIncoherentStrictAllZerosConditions.toTheoremFiveConditions` (`:166`).
- `printedIncoherent_allZerosInsideUnitDisk_of_strict` (`:183`).

Regression declarations in `ObservablesRegression.lean`:

- `insideZerosParameters` (`:74`) and `boundaryZerosParameters` (`:82`).
- `insideZerosParameters_isAdmissible` (`:90`) and
  `boundaryZerosParameters_isAdmissible` (`:95`).
- `insideZerosNumerator` (`:106`), `insideZerosDenominator` (`:110`),
  `boundaryZerosNumerator` (`:114`), and `boundaryZerosDenominator` (`:118`).
- `insideZeros_loopPolynomial_expansion` (`:122`),
  `insideZeros_denominatorPolynomial_expansion` (`:136`), and
  `insideZeros_responseNumeratorPolynomial_expansion` (`:143`).
- `boundaryZeros_loopPolynomial_expansion` (`:163`),
  `boundaryZeros_denominatorPolynomial_expansion` (`:177`), and
  `boundaryZeros_responseNumeratorPolynomial_expansion` (`:184`).
- `insideZerosNumerator_ne_zero` (`:210`), `insideZerosDenominator_ne_zero` (`:216`), and
  `insideZerosNumerator_isCoprime` (`:222`).
- `boundaryZerosNumerator_ne_zero` (`:232`), `boundaryZerosDenominator_ne_zero` (`:238`), and
  `boundaryZerosNumerator_isCoprime` (`:244`).
- `insideZerosReducedResponse` (`:254`) and `boundaryZerosReducedResponse` (`:262`).
- `insideZerosRationalReduction` (`:270`) and `boundaryZerosRationalReduction` (`:284`).
- `insideZerosResponseReduction` (`:298`) and `boundaryZerosResponseReduction` (`:304`).
- `insideZerosResponseReduction_half_mem_zZeros` (`:316`).
- `insideZerosResponseReduction_allZerosInsideUnitDisk` (`:328`).
- `boundaryZerosResponseReduction_one_mem_zZeros` (`:343`).
- `boundaryZerosResponseReduction_not_allZerosInsideUnitDisk` (`:351`).
- `printedIncoherentTheoremFiveConditions_boundary` (`:364`).
- `printedIncoherentStrictAllZerosConditions_boundary_fails` (`:371`).
- `printedIncoherentZeroPolynomial_boundary_one` (`:378`).
- `printedIncoherentAllZerosInsideUnitDisk_boundary_fails` (`:385`).

## Validation binding map

Bind the following exact names for slice 4:

- Coherent observable:
  `Optics.DCDR.ResponseReduction.allZerosInsideUnitDisk`.
- Nonvacuous coherent positive anchor:
  `Optics.DCDR.insideZerosResponseReduction_half_mem_zZeros` and
  `Optics.DCDR.insideZerosResponseReduction_allZerosInsideUnitDisk`.
- Required coherent negative check:
  `Optics.DCDR.boundaryZerosResponseReduction_one_mem_zZeros` and
  `Optics.DCDR.boundaryZerosResponseReduction_not_allZerosInsideUnitDisk`.
- Exact printed audit:
  `Optics.DCDR.PrintedIncoherentTheoremFiveConditions` and
  `Optics.DCDR.printedIncoherentTheoremFiveConditions_boundary`.
- Strict corrected result:
  `Optics.DCDR.PrintedIncoherentStrictAllZerosConditions` and
  `Optics.DCDR.printedIncoherent_allZerosInsideUnitDisk_of_strict`.
- Printed strictness failure:
  `Optics.DCDR.printedIncoherentStrictAllZerosConditions_boundary_fails` and
  `Optics.DCDR.printedIncoherentAllZerosInsideUnitDisk_boundary_fails`.

The printed incoherent declarations must not be bound as a parity bridge to the coherent N7
response. IP-10 remains non-comparable under the IP-08 coherent/incoherent discipline.

## Goal text and scope

This slice supplies the observable part of the S7D milestone and the quoted S7D bullet

> "poles, zeros, and stability results"

on top of the already reviewed response-indexed pole layer. It implements the §S4P naming rule

> "Names must state literal mathematical content. In particular, source terminology that calls
> all zeros inside the unit disk a 'resonance condition' is not adopted without a separate physical
> resonance theorem."

No FMICS'15 parity row is discharged: its Theorem 5 is the printed incoherent model, whereas these
network fixtures use the source's unprinted coherent N7 branch. The source audit is retained as a
separate object and its strictness failure is formalized.

Non-claims:

- no physical resonance theorem or use of "resonance" as the predicate name;
- no identification of coherent N7 `t`/`-I*k` with printed incoherent `1-k`/`k`;
- no spectral-power, physical-frequency, group-delay, or dispersion observable;
- no passivity, losslessness, material, causality, time-domain, Schur/BIBO, or stability inference;
- no claim that formal `q = 0` is a finite reciprocal-coordinate zero.

## Gate record

At committed source head `61229015`, the shipped `./scripts/lint-style.sh` exited zero. It checked
committed state; both new modules are under 1500 lines and have no line over 100 codepoints.

With `Poles`, `PolesRegression`, `Observables`, and `ObservablesRegression` inserted temporarily
in sorted order in `Physlib.lean`, this single locked command exited zero:

```text
lake-lock env bash -c 'lake exe cache get &&
  lake --wfail build <all twelve DCDR production/regression targets> &&
  lake exe runPhyslibLinters && lake exe lint_all'
```

The warnings-as-errors DCDR build completed successfully with 2787 jobs. `runPhyslibLinters`
passed for Physlib and QuantumInfo. `lint_all` exited zero: its full build, illegal-import,
PhyslibAlpha-registration, duplicate-tag, sorry/pseudo-attribution, declaration, and transitive-
import phases completed. Its registration advisory named only the existing unrelated
`AllPassZTransform*`, `PlanarRectangleLocalStokes`, and `PlanarSplitRectangleStokes` modules.
Its style and transitive-import advisories were the repository baseline and named neither new
module. `Physlib.lean` was then restored byte-identically and the worktree was clean.
