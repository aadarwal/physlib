# S7D slice 5 handoff: IP-22 pole cardinality and FMICS'15 dictionary

## Cutoff identity

- Branch: `optics/s7d-dcdr`.
- Exact required sync target: `d40969a6fca5016be5b2f569a9b656dad06897bb`.
- Sync operation: clean fast-forward to that exact hash; the gated source commit has it as its
  direct parent, so no synthetic merge commit was created.
- Gated Lean source head: `d4115de39117bc8bcaf0ad73e55dc79562573954`.
- Source commit: `d4115de3` — add the DCDR source pole-cardinality bridge.
- The final cutoff is a HANDOFF-only child of the gated source head.

## Files and registration request

Changed files:

- `Physlib/Optics/Systems/DelayTransfer/Stability.lean` — 462 lines; generic set-cardinality and
  printed-coefficient adapters.
- `Physlib/Optics/Systems/DCDR/SourceBridge.lean` — 377 lines; new production DCDR source
  dictionary, coherent degree bound, and cancellation-aware pole bound.
- `Physlib/Optics/Systems/DCDR/SourceBridgeRegression.lean` — 318 lines; new tight, degree-drop,
  model-divergence, and printed-form-mismatch fixtures.
- `Physlib/Optics/Systems/DCDR/PolesRegression.lean` — 743 lines; imports the production source
  bridge, where the two existing printed Theorem 4 audit definitions now live under their
  unchanged public names.

Registration request, in sorted order after `DCDR.ResponseRegression`:

```lean
public import Physlib.Optics.Systems.DCDR.SourceBridge
public import Physlib.Optics.Systems.DCDR.SourceBridgeRegression
```

Both registrations were inserted temporarily for the full gate and then removed.
`Physlib.lean` is byte-identical to the exact sync state, SHA-256
`42968d1b27ba0e3edc3fcbcca42c56db1c80c8cd4b620c80ed1220f20991beaf`.

Every DCDR file remains below 1500 lines. The unchanged largest DCDR file is
`ResponseRegression.lean` at 1397 lines; the new files are 377 and 318 lines.

## IP-13..IP-26 discharge list

The citations in this list are pinned to
`/Users/aadarwal/src/aadarwal/physlib-parity@3e7ee24:PARITY-LEDGER.md`.

- **IP-13** — PANDA through-port is S7C's assignment, outside S7D scope (`:120`).
- **IP-14** — PANDA drop-port is S7C's assignment, outside S7D scope (`:121`).
- **IP-15** — DATE heterogeneous cascade is S7C's assignment, outside S7D scope (`:122`).
- **IP-16** — DATE identical cascade is S7C's assignment, outside S7D scope (`:123`).
- **IP-17** — DATE Sylvester/Chebyshev form is S7C's assignment, outside S7D scope (`:124`).
- **IP-18** — DATE terminated-cascade formulas are S7C's assignment, outside S7D scope (`:125`).
- **IP-19** — DATE lattice/source-incomplete row is S7C's assignment, outside S7D scope (`:126`).
- **IP-20** — SysCon block diagrams belong to the N5/B-03 common-behavior task, not DCDR
  (`:127`; `goal.md:2604`).
- **IP-21** — closed by representation parity for graph extraction and enumeration; no S7D work
  remains (`:128`).
- **IP-22** — the only open DCDR-relevant row in this range; this cutoff supplies its Theorem 1
  definitional citation, generic Theorem 2 adapters, degree-two DCDR specialization, and source
  dictionary (`:129`).
- **IP-23** — NSV'16 transpose is N2b reciprocity, not DCDR (`:130`).
- **IP-24** — no source counterpart (`:131`).
- **IP-25** — closed by the forward-path form of Mason gain (`:132`).
- **IP-26** — no source counterpart for the netlist-extraction hook (`:133`).

## IP-22 disposition

### FMICS'15 Theorem 1

No duplicate result was added. The retained quotient is definitionally numerator over denominator:

- `RationalModel.eval` and its reflexive expansion `RationalModel.eval_eq` are at
  `Physlib/Optics/Systems/DelayTransfer/Basic.lean:130-143`.
- `ReducedRationalResponse.eval` is the same reduced polynomial quotient at
  `Physlib/Optics/Systems/DelayTransfer/Poles.lean:141-146`.

This discharges the printed transfer-equals-numerator-over-denominator statement at
`FMICS15_1.txt:400-402` without adding a theorem that merely repeats a definition.

### FMICS'15 Theorem 2 and the coordinate legend

`ReducedRationalResponse.poles` is the formal-`q` denominator-root set
(`DelayTransfer/Poles.lean:152-154`). `ReducedRationalResponse.zPoles` is the finite reciprocal
coordinate selected by `q = z^-1`; it explicitly requires `z != 0`, and its finset presentation
also removes `q = 0` before inversion because that root has no finite reciprocal
(`DelayTransfer/Stability.lean:193-205`). Thus:

- `ncard_poles_le_natDegree` bounds the formal-`q` set (`Stability.lean:137-141`).
- `ncard_zPoles_le_natDegree` bounds the source-facing reciprocal-`z` set (`:237-242`).
- `finite_poles_and_ncard_le_of_denominator_eq_coefficients` retains the printed
  nonzero-coefficient premise over `Finset.range (n + 1) = {0,...,n}` and concludes formal-`q`
  finiteness/cardinality (`:244-261`).
- `finite_zPoles_and_ncard_le_of_denominator_eq_coefficients` gives the same conclusion for the
  reciprocal-`z` set (`:263-280`).

The source's Definition 6 and Theorem 2 are printed at `FMICS15_1.txt:424-453`; the source excludes
`z = 0`. The extra removal of formal `q = 0` is the necessary consequence of the reciprocal
coordinate, not an identification of `q = 0` with source `z = 0`. Filtering and inversion cannot
increase cardinality, so both coordinate bounds hold.

All four new generic results are lemmas. They adapt the printed system statement to an already
reduced polynomial quotient and make the `q`/`z` coordinate transport explicit; they are not the
literal universally quantified printed Theorem 2 and therefore do not receive the `theorem`
keyword.

### DCDR maximum of two actual poles

The coherent unit-delay loop is proved directly to be one quadratic monomial and its denominator
to be `1 - C loopCoefficient * X^2` (`DCDR/SourceBridge.lean:91-118`). Hence the raw denominator
degree is at most two. For any `ResponseReduction`, polynomial divisibility shows cancellation
cannot increase the reduced denominator degree (`:127-140`). The selected actual reciprocal pole
set is finite and has cardinality at most two (`finite_actualPoles`,
`ncard_actualPoles_le_two`, `:143-155`). This is the cancellation-aware DCDR instance of the
paper's p. 174 remark that a unit-delay DCDR can have at most two poles
(`FMICS15_1.txt:604-606`).

The regression reaches the bound without invoking the bound lemma:

- `unstableReducedResponse_zPoles_eq_pair` expands `1 + 4*q^2` and proves the pole set exactly
  `{2*I,-2*I}` (`SourceBridgeRegression.lean:70-112`).
- `unstableResponseReduction_ncard_actualPoles_eq_two` computes its `Set.ncard` as two
  (`:115-125`).
- The separate zero-feedback fixture expands the raw denominator to one and the selected
  numerator to `q` (`:133-161`), builds an explicit response-indexed reduction (`:164-190`), and
  proves its actual pole set empty and cardinality zero (`:192-204`).

These anchors use polynomial evaluation and elementary complex algebra, not either generic or
DCDR cardinality result. They can fail if the coefficients, reciprocal coordinate, or selected
reduction changes.

## SourceParameters dictionary

The design follows the ring source-bridge pattern:

- DATE carries a source structure, an explicit map, and a `_data` dictionary at
  `Physlib/Optics/Systems/Microring/SourceBridgeDate.lean:64-79,410-435`; its gated response bridge
  is `dateForwardTransfer_eq_n5Response` at `:538-550`.
- SysCon carries the analogous structure, explicit map, and `_data` dictionary at
  `Physlib/Optics/Systems/Microring/SourceBridgeSysCon.lean:84-120`; its gated response bridge is
  `sysConDropTransfer_eq_n5Response` at `:250-261`.

`Optics.DCDRSourceBridge.SourceParameters` carries real `G1 G2 G3 k1 k2`
(`DCDR/SourceBridge.lean:196-206`). The paper quantifies complex symbols; the dictionary is
explicitly the real-valued subfamily that can map into Physlib's real coherent amplitudes and path
gains without discarding imaginary parts.

The map and its exact data are `SourceParameters.toUnitDelayParameters` and `_data`
(`:220-241`). It sends the source intensity `k_i` to through amplitude `sqrt (1-k_i)` and cross
amplitude `sqrt k_i`, while preserving `G1/G2/G3` as upper/lower/feedback gains. On the declared
coupling domain the four squared-amplitude identities recover `1-k_i` and `k_i` (`:250-271`).
The actual coherent cross coefficient remains `-I * crossAmplitude`, as defined at
`Physlib/Optics/Components/DirectionalCoupler.lean:68-70`.

The coherent coefficient and denominator identities are named separately
(`DCDR/SourceBridge.lean:274-295`). The printed incoherent linear, cubic, and loop coefficients,
numerator, denominator, and explicit coefficient list are at `:304-333`. The printed denominator
is proved equal to its `{0,1,2}` coefficient sum, has degree at most two, and gives finite
reciprocal poles with cardinality at most two (`:335-370`). None of these statements equates the
printed incoherent denominator with the coherent one.

The model-divergence regression makes that separation executable: with all five printed symbols
one, the incoherent loop coefficient is `1`, while two coherent `-I` cross edges give coefficient
`-1` (`SourceBridgeRegression.lean:213-239`).

## Withheld strict Theorem 4 bridge

No strict corrected Theorem 4 lemma is forced from this dictionary. FMICS'15 Theorem 3's printed
unit-delay denominator contains `k1*k2*G1*G3` (`FMICS15_1.txt:572-577`), while its Theorem 4
condition contains `k1*k2*G1*G2` (`:610-618`). The two printed expressions are preserved
separately in production.

The withholding has an independent exact witness. At `G1=1`, `G2=1/4`, `G3=4`, `k1=k2=1`, the
strict version of the Theorem 4 square-root bound holds with nonzero expression `1/4`, but the
Theorem 3 denominator is `1-4*q^2` and has reciprocal pole `z=2`, outside the unit disk
(`SourceBridgeRegression.lean:242-314`). Therefore the strict printed condition cannot imply
Schur stability of the differently indexed printed denominator as written. The existing
non-strict audit predicate remains separate in production (`DCDR/SourceBridge.lean:166-178`) and
its boundary failure remains in `PolesRegression.lean:89-98`.

## Public declaration inventory

New declarations in `Optics.DelayTransfer.ReducedRationalResponse`
(`DelayTransfer/Stability.lean`):

- `ncard_poles_le_natDegree` (`:138`).
- `ncard_zPoles_le_natDegree` (`:239`).
- `finite_poles_and_ncard_le_of_denominator_eq_coefficients` (`:250`).
- `finite_zPoles_and_ncard_le_of_denominator_eq_coefficients` (`:269`).

New declarations in `Optics.DCDR` and `Optics.DCDR.ResponseReduction`
(`DCDR/SourceBridge.lean`):

- `UnitDelayParameters.loopCoefficient` (`:91`).
- `UnitDelayParameters.loopPolynomial_eq_C_mul_X_sq` (`:99`).
- `UnitDelayParameters.denominatorPolynomial_eq_one_sub_C_mul_X_sq` (`:109`).
- `UnitDelayParameters.denominatorPolynomial_natDegree_le_two` (`:115`).
- `ResponseReduction.reducedDenominator_natDegree_le_two` (`:127`).
- `ResponseReduction.finite_actualPoles` (`:143`).
- `ResponseReduction.ncard_actualPoles_le_two` (`:152`).
- `printedIncoherentStabilityExpression` (`:166`) and
  `PrintedIncoherentStabilityConditions` (`:175`) moved from `PolesRegression.lean` into production;
  their public names and statements are unchanged.

New declarations in `Optics.DCDRSourceBridge` (`DCDR/SourceBridge.lean`):

- `SourceParameters` (`:196`).
- `SourceParameters.HasAdmissibleCouplings` (`:209`).
- `SourceParameters.HasNonnegativeGains` (`:213`).
- `SourceParameters.toUnitDelayParameters` (`:220`).
- `SourceParameters.toUnitDelayParameters_data` (`:233`).
- `SourceParameters.toUnitDelayParameters_isAdmissible` (`:244`).
- `SourceParameters.firstThroughAmplitude_sq` (`:250`).
- `SourceParameters.firstCrossAmplitude_sq` (`:256`).
- `SourceParameters.secondThroughAmplitude_sq` (`:262`).
- `SourceParameters.secondCrossAmplitude_sq` (`:268`).
- `SourceParameters.coherentLoopCoefficient` (`:274`).
- `SourceParameters.toUnitDelayParameters_loopCoefficient` (`:285`).
- `SourceParameters.toUnitDelayParameters_denominatorPolynomial` (`:291`).
- `SourceParameters.printedLinearCoefficient` (`:304`).
- `SourceParameters.printedCubicCoefficient` (`:308`).
- `SourceParameters.printedLoopCoefficient` (`:312`).
- `SourceParameters.printedNumeratorPolynomial` (`:317`).
- `SourceParameters.printedDenominatorPolynomial` (`:323`).
- `SourceParameters.printedDenominatorCoefficients` (`:328`).
- `SourceParameters.printedDenominatorCoefficients_nonzero` (`:335`).
- `SourceParameters.printedDenominatorPolynomial_eq_coefficients` (`:341`).
- `SourceParameters.printedDenominatorPolynomial_natDegree_le_two` (`:350`).
- `SourceParameters.finite_zPoles_and_ncard_le_two` (`:365`).

New regression declarations in `Optics.DCDR` (`DCDR/SourceBridgeRegression.lean`):

- `unstableReducedResponse_zPoles_eq_pair` (`:70`).
- `unstableResponseReduction_ncard_actualPoles_eq_two` (`:115`).
- `degreeDropCoupler` (`:133`) and `degreeDropParameters` (`:138`).
- `degreeDrop_denominatorPolynomial_expansion` (`:146`).
- `degreeDrop_responseNumeratorPolynomial_expansion` (`:154`).
- `degreeDropReducedResponse` (`:164`).
- `degreeDropRationalReduction` (`:172`).
- `degreeDropResponseReduction` (`:186`).
- `degreeDropResponseReduction_actualPoles_eq_empty` (`:192`).
- `degreeDropResponseReduction_ncard_actualPoles_eq_zero` (`:201`).
- `sourceDictionaryDivergenceParameters` (`:213`).
- `sourceDictionaryDivergence_printedLoopCoefficient` (`:221`).
- `sourceDictionaryDivergence_coherentLoopCoefficient` (`:227`).
- `sourceDictionaryDivergence_loopCoefficients_ne` (`:234`).
- `sourceThmFourMismatchParameters` (`:242`).
- `sourceThmFourMismatch_strictConditions` (`:250`).
- `sourceThmFourMismatch_denominatorPolynomial_expansion` (`:276`).
- `sourceThmFourMismatchReducedResponse` (`:284`).
- `sourceThmFourMismatch_two_mem_zPoles` (`:296`).
- `sourceThmFourMismatch_not_isSchurStable` (`:309`).

No public declaration was removed or renamed.

## Validation binding map

The validation lane should bind at least:

- `Optics.DelayTransfer.ReducedRationalResponse.ncard_poles_le_natDegree`.
- `Optics.DelayTransfer.ReducedRationalResponse.ncard_zPoles_le_natDegree`.
- `Optics.DelayTransfer.ReducedRationalResponse.finite_zPoles_and_ncard_le_of_denominator_eq_coefficients`.
- `Optics.DCDR.ResponseReduction.ncard_actualPoles_le_two`.
- `Optics.DCDRSourceBridge.SourceParameters.toUnitDelayParameters_data`.
- `Optics.DCDRSourceBridge.SourceParameters.toUnitDelayParameters_denominatorPolynomial`.
- `Optics.DCDRSourceBridge.SourceParameters.printedDenominatorPolynomial_eq_coefficients`.
- `Optics.DCDRSourceBridge.SourceParameters.finite_zPoles_and_ncard_le_two`.
- `Optics.DCDR.unstableResponseReduction_ncard_actualPoles_eq_two`.
- `Optics.DCDR.degreeDropResponseReduction_ncard_actualPoles_eq_zero`.
- `Optics.DCDR.sourceDictionaryDivergence_loopCoefficients_ne`.
- `Optics.DCDR.sourceThmFourMismatch_not_isSchurStable`.

## Goal scope and non-claims

This cutoff supplies the IP-22 source-parity leg of the quoted S7D bullet

> "poles, zeros, and stability results"

at `goal.md:2424`, while retaining the already certified response-indexed cancellation gate. It
does not alter S-06, S-07, G-04, or X-01 evidence from earlier slices.

No physical resonance, coherent/incoherent response equivalence, general BIBO theorem,
normalized-modal power, electromagnetic power, causality or time-domain result, or
physical-frequency interpretation is claimed. Formal `q` and reciprocal `z` remain explicitly
distinct algebraic coordinates. The printed incoherent formulas and the source's own unprinted
coherent branch are retained as different cases.

## Gate record

At committed source head `d4115de3`, the focused production/regression builds passed. The shipped
`./scripts/lint-style.sh` exited zero on committed state, including every DCDR file.

With `SourceBridge` and `SourceBridgeRegression` inserted temporarily in sorted order in
`Physlib.lean`, this single locked command exited zero:

```text
lake-lock env bash -c 'lake exe cache get &&
  lake --wfail build <all fourteen DCDR production/regression targets> &&
  lake exe runPhyslibLinters && lake exe lint_all'
```

The warnings-as-errors DCDR build completed successfully with 2789 jobs. `runPhyslibLinters`
passed for Physlib and QuantumInfo. `lint_all` exited zero: its full build, file/illegal-import,
PhyslibAlpha-registration, duplicate-tag, sorry/pseudo-attribution, declaration, and transitive
import phases completed. Its registration advisory named only unrelated modules already present
at the sync target. Its repository-baseline style/transitive advisories named neither edited nor
new slice-5 module. `Physlib.lean` was restored byte-identically before this HANDOFF was written.
