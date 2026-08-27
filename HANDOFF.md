# HANDOFF

- Branch: `optics/s8-tbd`
- Gated source: `4e02a9ec497099d07475427324f2947d385cf365`
- Source file: `Physlib/Mathematics/ZTransform/DifferenceEquationRegression.lean`
- Registration: none; the source file is already registered in `Physlib.lean`.

## Declarations

- `Physlib.ZTransform.IsLowPassModel` — `Physlib/Mathematics/ZTransform/DifferenceEquationRegression.lean:241` @ `4e02a9ec497099d07475427324f2947d385cf365`
- `Physlib.ZTransform.transferFunction_lowPass_eq` — `Physlib/Mathematics/ZTransform/DifferenceEquationRegression.lean:261` @ `4e02a9ec497099d07475427324f2947d385cf365`
- `Physlib.ZTransform.lowPass_transform_div_eq_transferFunction` — `Physlib/Mathematics/ZTransform/DifferenceEquationRegression.lean:271` @ `4e02a9ec497099d07475427324f2947d385cf365`
- `Physlib.ZTransform.transferFunction_lowPass_wrongFeedbackSign_ne` — `Physlib/Mathematics/ZTransform/DifferenceEquationRegression.lean:305` @ `4e02a9ec497099d07475427324f2947d385cf365`

## Pre-existing-line accounting

The source delta `9c1f4929d20a17fcc7ada2c37c1e5f2f82b3df38` → `4e02a9ec497099d07475427324f2947d385cf365` removes ten pre-existing lines. All ten are in
these forced module-document repairs:

- Overview — `Physlib/Mathematics/ZTransform/DifferenceEquationRegression.lean:31-36` @ `9c1f4929d20a17fcc7ada2c37c1e5f2f82b3df38` → `Physlib/Mathematics/ZTransform/DifferenceEquationRegression.lean:30-37` @
  `4e02a9ec497099d07475427324f2947d385cf365`. The old overview described symbols and two point values only. The new model,
  all-`z` symbolic quotient, and recurrence-derived transform ratio made that description false,
  so the replacement names them while retaining the no-frequency-interval boundary.
- References — `Physlib/Mathematics/ZTransform/DifferenceEquationRegression.lean:67-69` @ `9c1f4929d20a17fcc7ada2c37c1e5f2f82b3df38` → `Physlib/Mathematics/ZTransform/DifferenceEquationRegression.lean:72-76` @
  `4e02a9ec497099d07475427324f2947d385cf365`. The old paragraph contrasted the source's frequency response with only the two
  point checks. The replacement must attribute the newly added identity to ITP'14 Theorem 14,
  separate it from the still-withheld generic frequency response, and retain why the point checks
  remain useful.
- Scope — `Physlib/Mathematics/ZTransform/DifferenceEquationRegression.lean:72` @ `9c1f4929d20a17fcc7ada2c37c1e5f2f82b3df38` → `Physlib/Mathematics/ZTransform/DifferenceEquationRegression.lean:78-80` @ `4e02a9ec497099d07475427324f2947d385cf365`.
  The old neutral-mathematics and realizability non-claims remain, but the new source-named identity
  makes an explicit fence necessary: “low-pass” names the fixture and does not assert a
  frequency-response property.

The sole import at `Physlib/Mathematics/ZTransform/DifferenceEquationRegression.lean:8` is byte-stable. No pre-existing declaration statement or
proof changed. Direct committed-blob comparisons confirm that every reviewed declaration below is
byte-stable across the same delta:

- Coefficient declarations:
  - `Physlib.ZTransform.lowPassFeedback` — `Physlib/Mathematics/ZTransform/DifferenceEquationRegression.lean:200` @ `9c1f4929d20a17fcc7ada2c37c1e5f2f82b3df38` → `Physlib/Mathematics/ZTransform/DifferenceEquationRegression.lean:208` @ `4e02a9ec497099d07475427324f2947d385cf365`; byte-stable.
  - `Physlib.ZTransform.lowPassFeedback_one` — `Physlib/Mathematics/ZTransform/DifferenceEquationRegression.lean:204` @ `9c1f4929d20a17fcc7ada2c37c1e5f2f82b3df38` → `Physlib/Mathematics/ZTransform/DifferenceEquationRegression.lean:212` @ `4e02a9ec497099d07475427324f2947d385cf365`; byte-stable.
  - `Physlib.ZTransform.lowPassFeedback_two` — `Physlib/Mathematics/ZTransform/DifferenceEquationRegression.lean:207` @ `9c1f4929d20a17fcc7ada2c37c1e5f2f82b3df38` → `Physlib/Mathematics/ZTransform/DifferenceEquationRegression.lean:215` @ `4e02a9ec497099d07475427324f2947d385cf365`; byte-stable.
  - `Physlib.ZTransform.lowPassFeedforward` — `Physlib/Mathematics/ZTransform/DifferenceEquationRegression.lean:212` @ `9c1f4929d20a17fcc7ada2c37c1e5f2f82b3df38` → `Physlib/Mathematics/ZTransform/DifferenceEquationRegression.lean:220` @ `4e02a9ec497099d07475427324f2947d385cf365`; byte-stable.
  - `Physlib.ZTransform.lowPassFeedforward_zero` — `Physlib/Mathematics/ZTransform/DifferenceEquationRegression.lean:216` @ `9c1f4929d20a17fcc7ada2c37c1e5f2f82b3df38` → `Physlib/Mathematics/ZTransform/DifferenceEquationRegression.lean:224` @ `4e02a9ec497099d07475427324f2947d385cf365`; byte-stable.
  - `Physlib.ZTransform.lowPassFeedforward_one` — `Physlib/Mathematics/ZTransform/DifferenceEquationRegression.lean:219` @ `9c1f4929d20a17fcc7ada2c37c1e5f2f82b3df38` → `Physlib/Mathematics/ZTransform/DifferenceEquationRegression.lean:227` @ `4e02a9ec497099d07475427324f2947d385cf365`; byte-stable.
  - `Physlib.ZTransform.lowPassFeedforward_two` — `Physlib/Mathematics/ZTransform/DifferenceEquationRegression.lean:223` @ `9c1f4929d20a17fcc7ada2c37c1e5f2f82b3df38` → `Physlib/Mathematics/ZTransform/DifferenceEquationRegression.lean:231` @ `4e02a9ec497099d07475427324f2947d385cf365`; byte-stable.
- Delay-symbol declarations:
  - `Physlib.ZTransform.delaySymbol_lowPassFeedforward` — `Physlib/Mathematics/ZTransform/DifferenceEquationRegression.lean:232` @ `9c1f4929d20a17fcc7ada2c37c1e5f2f82b3df38` → `Physlib/Mathematics/ZTransform/DifferenceEquationRegression.lean:245` @ `4e02a9ec497099d07475427324f2947d385cf365`; byte-stable.
  - `Physlib.ZTransform.delaySymbol_lowPassFeedback` — `Physlib/Mathematics/ZTransform/DifferenceEquationRegression.lean:241` @ `9c1f4929d20a17fcc7ada2c37c1e5f2f82b3df38` → `Physlib/Mathematics/ZTransform/DifferenceEquationRegression.lean:254` @ `4e02a9ec497099d07475427324f2947d385cf365`; byte-stable.
- Point-value declarations:
  - `Physlib.ZTransform.transferFunction_lowPass_one` — `Physlib/Mathematics/ZTransform/DifferenceEquationRegression.lean:249` @ `9c1f4929d20a17fcc7ada2c37c1e5f2f82b3df38` → `Physlib/Mathematics/ZTransform/DifferenceEquationRegression.lean:291` @ `4e02a9ec497099d07475427324f2947d385cf365`; byte-stable.
  - `Physlib.ZTransform.transferFunction_lowPass_neg_one` — `Physlib/Mathematics/ZTransform/DifferenceEquationRegression.lean:255` @ `9c1f4929d20a17fcc7ada2c37c1e5f2f82b3df38` → `Physlib/Mathematics/ZTransform/DifferenceEquationRegression.lean:297` @ `4e02a9ec497099d07475427324f2947d385cf365`; byte-stable.

## Gates

- `lake-lock build Physlib.Mathematics.ZTransform.DifferenceEquationRegression`: pass.
- `lake-lock build Physlib`: pass.
- `lake-lock exe check_file_imports`: pass.
- `lake-lock exe sorry_lint`: pass.
- `lake-lock exe runPhyslibLinters`: pass for Physlib and QuantumInfo.
- `./scripts/lint-style.sh`: pass.

## Verbatim ledger row

`PARITY-LEDGER.md:228` @ `2ac998423caeb2e48b834023ae69b6497488055d`:

```text
| ZT-07 | ITP'14 Def. 14 + Thm. 14 p. 496–497: second-order low-pass IIR, `α = [0; 1.194; −0.436]`, `β = [0.0605; 0.121; 0.0605]` | The audited second-order low-pass, with **ITP'14's exact printed coefficients stored as rationals**: `lowPassFeedback` (`Physlib/Mathematics/ZTransform/DifferenceEquationRegression.lean:200` @ `110eb5cd`, `1194/1000` and `−(436/1000)`) and `lowPassFeedforward` (`:212`, `605/10000`, `121/1000`, `605/10000`) — matching `α = [0; 1.194; −0.436]`, `β = [0.0605; 0.121; 0.0605]` term for term, checked here. Hand-expanded delay symbols `delaySymbol_lowPassFeedforward` (`:232`) and `delaySymbol_lowPassFeedback` (`:241`); transfer values `transferFunction_lowPass_one` (`:249`) and `…_neg_one` (`:255`) by `norm_num` — **on `optics/development` @ `110eb5cd`** | rationals given as `&1194/&1000` etc. | — | **PARTIALLY proved and GATED on `optics/development` @ `110eb5cd`.** **S8 TRIAGE 2026-08-27 — MY OWN SWEEP CORRECTION WAS AN OVER-DISCHARGE, and S8 is right.** I checked this hardest because it reverses my own work. **ITP'14 Thm. 14 states an ALL-`z` identity** — `z_transform y z / z_transform x z` equals the full second-order quotient for every `z` in the ROC. Physlib has the exact coefficients, **both delay symbols as all-`u` polynomial identities** (`delaySymbol_lowPassFeedforward`, `delaySymbol_lowPassFeedback`), and **exactly two POINT values** — `transferFunction_lowPass_one` (`H(1) = 1`) and `…_neg_one` (`H(−1) = 0`). **No lemma states the quotient for general `z`.** So Def. 14 and the coefficient/point content are discharged; **Thm. 14's transfer identity is the OPEN leg.** The remaining step is one rewrite — `transferFunction` is definitionally the quotient of the two symbols — but *follows in one rewrite* is not *proved*, which is the standard applied to every other row here. **This does NOT reopen index row T-04** unless T-04's text claims the full identity. **NEW PRINTED DEFECT found while verifying this, glyph-checked at 300 dpi:** ITP'14's prose gives the feedback coefficients as *"[1.94, −0.436]"* while **Thm. 14 prints `Cx(&1194/&1000)` and Figure 2 shows `1.194`** — the prose drops the `1`. Physlib uses `1194/1000`, matching the theorem and figure, so it is unaffected. See §7 item 30. Regression **T-04** ("audited second-order low-pass"). **INTEGRITY NOTE — this row was STALE and is corrected 2026-08-27.** It read *"TBD — not yet formalized"* while its target already existed. Found by A7's regression index, verified here against the tree, and cited at `110eb5cd`. **It went stale invisibly:** `tools/sweep.py` exempts any row whose lean cell contains `TBD` from the location-ref check, so no check was ever looking at it — the exemption is now reported rather than silent. **S8 TRIAGE 2026-08-27 — OPEN**, smallest named slice: named in the triage. Implementation proceeds on the S8 lane in the triage's §8 order. **O3 FLIP PASS (rev 3): ITS ZT-07 INSTRUCTION IS NOT APPLIED, AND THE CONTRADICTION IS FLAGGED TO THE CONTROLLER RATHER THAN RESOLVED HERE.** The flip pass says *KEEP DISCHARGED*; the **accepted S8 triage commit `317532b` corrected this row to PARTIAL**, and the two differ on the verdict while agreeing on the facts — **the flip pass's own evidence says the two `transferFunction` lemmas "pin endpoint values"**, which is precisely S8's point. Re-checked against the paper again here: **ITP'14 Thm. 14 is an all-`z` identity over the ROC**, and no lemma states the quotient for general `z`. **RESOLVED 2026-08-27 — CONTROLLER RULING: PARTIAL STANDS.** The S8-triage verdict **SUPERSEDES** the flip pass's *keep-discharged* instruction, which was rebased **before the triage existed** and whose own evidence text concedes the point-value limitation. Nothing from the flip pass is applied to this row. **The leg closes properly through the normal pipeline, not by annotation:** S8 slice 2 is building `IsLowPassModel` and the all-`z` transfer identity, and this row flips when that theorem exists. | parity |
```

## Milestone

ITP'14 Thm. 14 full transfer identity added; row moves PARTIAL -> discharged on merge
