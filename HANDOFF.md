# S7C slice 8: convention-free linear-behavior conservation

## Cutoff and synchronization

This slice synchronized exactly onto the controller-authorized registered head
`cb89d1d2d5ff3459c2cb50f21274713cd00ad62f`. The synchronization merge is
`08d7e69773ad48821efeac14450e147d4ffbf311`; it contains the registered Slice 7 modules.
The gated source is `9b2d743d9762e69ee5056727e093c7cd42894637`. This cutoff is its
HANDOFF-only child.

Relative to the sync target, the source adds exactly the two authorized Network files. No
pre-existing Network or Mode file changed, and `Physlib.lean` remains byte-identical to the sync
target.

## Scope and classification

The controlling text at `goal.md:1942-1943` on the cutoff says:

> convention-free port/network power, passivity, and losslessness predicates that do not
> require time-reversal data;

This neutral Network slice discharges that item at the `LinearBehavior` level and targets ledger
row N-09 (`goal.md:2617`), whose failure mode is false square-port identification. Every result is
a `lemma`; this slice presents no literal physics theorem.

The two other open Network bullets remain at `goal.md:2184-2187`: component-owned physical-port
packaging, and frequency-parameterized propagation with explicit frequency-domain, causality, and
dispersion hypotheses. This slice does not address either item.

## Authorized files

- `Physlib/Optics/Network/LinearBehaviorConservation.lean` (398 lines);
- `Physlib/Optics/Network/LinearBehaviorConservationRegression.lean` (253 lines).

Production imports no regression module. No additive edit to an existing Network or Mode module
was needed.

## Singular-safe relational predicates

`LinearBehavior.IsPassive` and `LinearBehavior.IsPowerPreserving` are defined at
`LinearBehaviorConservation.lean:98` and `:106`. They quantify only over pairs already in the
relation, so they assert neither existence nor uniqueness and remain meaningful for singular
relations. Their input and output types are independent; no incident/outgoing equivalence is
introduced. Power preservation implies passivity at line 113.

For a rectangular transform graph, the relational classifications agree exactly with the existing
transform predicates. The passivity iff is at line 130 and the power-preservation iff is at line
144. Neither result requires a square matrix or a boundary pairing.

## Relabeling, rephasing, and netlist lifts

Independent input/output relabeling preserves and reflects passivity and power preservation at
`LinearBehaviorConservation.lean:169` and `:189`. Independent unit-phase coordinate changes do the
same at lines 209 and 228. These relation-level covariance lemmas never identify the two boundary
types.

For a supplied complete solution, component-transform passivity bounds its exposed readout at
line 278; component-transform power preservation gives equality at line 299. The hypotheses name
both the assembled scattering classification and the concrete solution membership. No existence,
uniqueness, determinant, functionality, or well-posedness premise is hidden.

The singular-safe external behavior lifts are at lines 317 and 325. Agreement with the extracted
response transform is stated only under the existing named `FlatNetlist.IsWellPosed` gate, at
lines 333 and 341.

Actual netlist rephasing reuses Slice 7's directed
`PortConnectionFamily.IsMatchedGauge` hypothesis. Singular-safe behavior covariance is at lines
354 and 363. Gated response-transform covariance is at lines 373 and 385; the original
well-posedness hypothesis is explicit in both statements.

## Independent N-09 regression

The positive fixture is genuinely rectangular: `Fin 1` input and `Fin 2` output. Its matrix and
hand-expanded output `(3/5, 4/5)` are at
`LinearBehaviorConservationRegression.lean:78` and `:87`. The primitive matrix action is expanded
from `Matrix.mulVec` and the singleton finite sum at line 92; graph membership is expanded at line
115. The input power is exactly `1` at line 129, and output power is exactly
`9/25 + 16/25 = 1` at line 136. Their equality is joined at line 142.

The all-input three-four-five calculation is expanded at line 154. The relation is then classified
directly as power-preserving from raw membership and that calculation at line 168, without the
transform/behavior classification iff. Line 181 proves `¬ Nonempty (Fin 1 ≃ Fin 2)` from finite
cardinality, so the predicate cannot rely on a manufactured boundary equivalence.

The hostile fixture duplicates `4/5` onto both outputs at lines 192-202. Its raw graph membership
is expanded from matrix multiplication at line 212. Its output power is exactly `32/25` at line
227, strictly greater than the same input's power `1` at line 234. The concrete member rejects
relational passivity at line 243. A duplicated output, square-boundary identification, or dropped
output coordinate therefore changes the fixture and can make the expected classification fail.

### Anchor-independence map

- `splitter_apply`, `splitter_mem`, and the exact positive powers do not use either
  transform/behavior iff, or any relabel, rephase, or netlist lift.
- `splitter_power` and `splitter_isPowerPreserving` do not use
  `ModeTransform.toBehavior_isPowerPreserving_iff`, or any covariance or netlist lift.
- `no_boundary_equiv` uses neither conservation predicate nor any classification or covariance
  result.
- `hostile_mem`, the exact `32/25`, the strict inequality, and the rejection do not use either
  transform/behavior iff, or any relabel, rephase, or netlist lift.

A declaration-name grep over the regression is empty for all production classification,
covariance, solution-lift, behavior-lift, and rephased-netlist lemmas under test.

## Non-claims

- `ModeAmplitude.power` is the squared finite `L²` norm of algebraic modal amplitudes. It is
  amplitude-squared bookkeeping, not an electromagnetic energy or power theorem.
- No time-reversal pairing, scattering interpretation, complete physical-port pairing,
  reciprocity, reference plane, propagation law, stability, causality, dispersion, measurement,
  or physical losslessness claim is made.
- “Power-preserving” is the convention-free relational name for the requested algebraic
  losslessness classification; it does not assert physical losslessness.
- The raw `FlatNetlist.solutionBehavior` is not itself classified as passive: its output is a full
  internal state. Only the derived external readout is compared with the external input.
- Response-transform statements are restricted to the existing well-posed domain. Relation-level
  statements remain singular-safe.
- Regression coefficients are algebraic sentinels, not a claimed physical splitter realization.
  Human verification remains required by `AI-POLICY.md`.

## Reviewer map

1. Read `LinearBehaviorConservation.lean:92-156` for the two relation predicates and rectangular
   transform iffs.
2. Read lines 162-245 for independent-side relabeling and rephasing covariance.
3. Read lines 252-346 for complete-solution evidence, singular-safe behavior lifts, and the named
   well-posed response gate.
4. Read lines 352-392 for matched-gauge netlist behavior and response covariance.
5. Read `LinearBehaviorConservationRegression.lean:73-174` for the primitive positive fixture and
   direct relation-level classification.
6. Read lines 180-249 for the no-equivalence proof and hostile duplicated-output sentinel.

## Exact validation record

The exact gated source `9b2d743d9762e69ee5056727e093c7cd42894637` was checked under
`lake-lock`. Temporary sorted registration of the two Slice 8 modules was used for declaration
linters and then removed.

- targeted build of `Physlib.Optics.Network.LinearBehaviorConservationRegression`: passed,
  2735 jobs;
- `runPhyslibLinters`: Physlib and QuantumInfo passed, including `simpNF`, with no Slice 8
  transitive-import advisory;
- committed-state `lint-style.sh`: passed;
- `module_doc_lint`: neither temporarily registered Slice 8 module produced a diagnostic; the
  command remains globally red on the pre-existing repository-wide documentation backlog;
- `git diff --check`: passed;
- line counts are 398 and 253, both below 1500, and no line exceeds 100 Unicode codepoints;
- neither file contains `theorem`, `sorry`, `axiom`, `native_decide`, `maxHeartbeats`, or
  `Lean.ofReduceBool`;
- production imports no regression module; and
- relative to `cb89d1d2`, the source diff contains exactly the two authorized new files.

Temporary registration was restored byte-identically. `Physlib.lean` had SHA-256
`85727e4debf1f8ad8c50abe04763611f45131275542b2b6ee18f1e28d5f538d0` before and after the gate.
This final cutoff child changes only `HANDOFF.md`.
