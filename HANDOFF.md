# S7D slice 8c handoff: DCDR causal-Z common-point fix

## Cutoff identity

- Exact sync target: `8e48a7d1fa1ef1080bfe75dbfc93c6768ec3bdcb`.
- Sync merge: `60d7f6ab7ed1a11f2ab23fc3433505aca1fb95bf`.
- Gated source: `439a36f52ec312dacb28aa3d85b4ca946d930e93`.
- `Physlib.lean` was not changed. Its restored SHA-256 is
  `18e578d35df5704c80de0d783d439ba9f3bf02f764549951eac2ae8548e2b85d`.

## Goal and scope

This slice addresses the DCDR half of goal.md X-01: one ring and one DCDR should
exercise relational, compiled, feedback, Mason, and recurrence/Z semantics on a
common domain. The applicable DCDR views now agree under one explicit domain.

The DCDR API has no chain representation: it has no declared left/right
traveling-wave boundary partition, reverse-transmission pivot, or chain transform.
Accordingly, this slice does not discharge the word `chain`, nor does it provide a
combined ring-and-DCDR aggregate regression. The two-system X-01 row remains open
for a joint boundary/chain slice; this handoff does not overclaim its closure.

## Files and registration request

- `Physlib/Optics/Systems/DCDR/ZTransform.lean`: causal recurrence, named ROC,
  reciprocal-Z transfer, and a sufficient Schur gate.
- `Physlib/Optics/Systems/DCDR/ZTransformBridge.lean`: common-domain bridges and
  the full-vector relational agreement record.
- `Physlib/Optics/Systems/DCDR/ZTransformMasonRegression.lean`: independent raw
  N5 equations and complete eleven-branch Mason enumeration.
- `Physlib/Optics/Systems/DCDR/ZTransformRegression.lean`: exact positive and
  negative fixtures, including analytic ROC and causal anchors.

Please register these imports in repository-sorted order:

```lean
public import Physlib.Optics.Systems.DCDR.ZTransform
public import Physlib.Optics.Systems.DCDR.ZTransformBridge
public import Physlib.Optics.Systems.DCDR.ZTransformMasonRegression
public import Physlib.Optics.Systems.DCDR.ZTransformRegression
```

## Claims delivered

`ZTransform.lean` constructs the causal recurrence directly from the unit-delay
response numerator and loop polynomials. Its `zTransferROC` is the generic
`iirROC`; membership separately yields `z != 0` and the recurrence-denominator
gate. The new lag-two lemma constructs the causal kernel as the average of two
geometric sequences and proves `‖r‖ < ‖z‖` implies actual ROC membership when
the retained feedback coefficient is `r^2`. On that ROC, the causal
impulse-response transform equals `zTransfer`, and `zTransfer` is the rational
response at the explicitly stated coordinate `q = z⁻¹`.
`UnitDelayParameters.IsZContractive` supplies a sufficient Schur result; the ROC
and Schur conditions remain distinct.

The GG2 fix applies the lag-two geometric ROC lemma again at the nonreal point
`z = I`, with `r = I/2` and formal coordinate `q = z⁻¹ = -I`. It then
assembles every field of
`IsZCrossSemanticsDomain stableUnitDelayParameters stableResponseReduction I`:
admissibility, recurrence contraction, reduced Schur stability, local loop
contraction, actual ROC membership, no cancellation, and reduced evaluation.
`zRegression_stable_I_commonDomain_independent_anchor` pairs the resulting
production agreement with the existing four independently expanded values at
that exact point; the independent conjunct does not use
`zCrossSemantics_agree`.

`ZTransformBridge.lean` proves the recurrence denominator is nonzero exactly when
the fixed N5 denominator gate holds. It identifies `zTransfer` with the compiled
reciprocal-Z N5F response, the response-indexed reduced quotient under its
no-cancellation and evaluation gates, the convergent circulation series, the fixed
N5 response, the complete Mason response, the packaged typed-scattering entry, and
the original relation. The relational field now stores membership of the complete
Mason output vector for the unit input, so both DCDR external outgoing coordinates
are pinned rather than only the selected scalar entry. The common-domain object
stores admissibility, recurrence contraction, reduced Schur stability, loop
contraction, ROC membership, no cancellation, and reduced evaluation separately.
The recurrence and reduced Schur fields are certification-only in
`zCrossSemantics_agree`; the equality proof does not consume them. Unitarity is not
assumed because none of these identifications uses it.

The production fixed N5 leg reuses the accepted raw-equation elimination bridge in
`Response.lean`, and the production Mason leg reuses the accepted G-04
instantiation in `Mason.lean`. The nonzero-loop regression separately expands all
eight N5 equations and the complete eleven-branch graph, so its audit does not
obtain the tested values through either production equality.

## Regression teeth

- The original exact common-domain point has couplers `t = 3/5`, `k = 4/5`,
  gains `(9/16, 1, 1)`, and `z = 1`. Its cancelling loop polynomial is zero, and
  the applicable scalar views remain pinned to `-1` without invoking
  `zCrossSemantics_agree`. Its relational conjunct is now full-vector Mason-output
  membership, not a selected-coordinate witness.
- The nonzero-loop point `stableUnitDelayParameters` has loop polynomial
  `-(1/4) q^2` and denominator `1 + (1/4) q^2`. With `r = I/2`, the strict bound
  `‖r‖ < ‖1‖` proves `z = 1` belongs to the actual analytic ROC; membership is
  no longer supplied only as fixture data.
- At the same nonzero-loop family, the strict bound `‖I/2‖ < ‖I‖` proves that
  `z = I`, hence `q = -I`, belongs to the actual analytic ROC. All common-domain
  fields are assembled at this same point. Primitive geometric transforms solve
  the causal recurrence as `-(7/8) I`; the existing generic S4 reciprocal reindex
  transports an independently expanded formal-q value to the raw compiled
  response, without the DCDR response-model bridge.
- At `q = -I`, the displayed eight-channel N5 state independently satisfies every
  raw equation and reads `-(7/8) I`. The full eleven-branch Mason audit enumerates
  upper and lower touching loops with gains `61/100` and `-9/25`, all four
  supported forward paths, determinant `3/4`, and numerator `-(21/32) I`, hence
  the same response `-(7/8) I`. A feedback, path, cofactor, or reciprocal-coordinate
  error changes an exact anchor.
- The active sentinel expands a nonsummable loop: `zTransfer = -67/20`, while the
  Mathlib-totalized circulation expression is `1/4`. Reduced Schur stability fails,
  so the common domain is impossible. The production documentation now states that
  `circulationSeries` is totalized outside contraction.

The main regression declarations are `zRegression_crossSemantics`,
`zRegression_stable_one_mem_zTransferROC`,
`zRegression_stable_I_mem_zTransferROC`,
`zRegression_stable_I_crossSemanticsDomain`,
`zRegression_stable_I_commonDomain_independent_anchor`,
`zRegression_stable_independent_nonzeroLoop_I`,
`zRegression_stable_auditedMasonResponse_neg_I`,
`zRegression_active_circulation_ne_transfer`, and
`zRegression_active_not_crossSemanticsDomain`.

## Reused foundations

- Ring promoted-rational pattern:
  `Physlib/Optics/Systems/Microring/AllPassDelayTransfer.lean:127-178`.
- Ring named-ROC pattern:
  `Physlib/Optics/Systems/Microring/AllPassZTransform.lean:193-346`.
- Ring common-domain pattern:
  `Physlib/Optics/Systems/Microring/AllPassZTransformBridge.lean:321-428`.
- DCDR unit-delay rational compilation:
  `Physlib/Optics/Systems/DCDR/Poles.lean:82-205,322-426,571-713`.
- DCDR two-channel external boundary:
  `Physlib/Optics/Systems/DCDR/Netlist.lean:351-398`.
- DCDR raw N5 response: `Physlib/Optics/Systems/DCDR/Response.lean:461-555`.
- DCDR G-04 Mason bridge: `Physlib/Optics/Systems/DCDR/Mason.lean:177-197`.
- Generic full Mason response equality:
  `Physlib/Optics/Network/FlatNetlistMason.lean:170-182`.
- Generic recurrence/ROC:
  `Physlib/Mathematics/ZTransform/DifferenceEquation.lean:271-295`.
- Generic Schur layer: `Physlib/Mathematics/ZTransform/Stability.lean:223-289`.

## Gate record

Targeted builds of all four new modules passed under `lake-lock`. With temporary
root registration of the accepted slice-7 modules and these four modules, cache
retrieval, `lake --wfail build Physlib`, `check_file_imports`, `sorry_lint`,
`runPhyslibLinters`, and `api_map_index` passed. `lint_all` exited successfully;
its lane-local double-blank and redundant-import findings were fixed, after which
the full root rebuild and the redundant-import scan were rerun. The latter now
reports no DCDR finding; its remaining findings are pre-existing modules outside
this lane.

Direct `lint-style.py` runs are clean for every DCDR file. The four new modules
have the literal module-doc headings and TOCs matching their numbered sections.
The shipped repository-wide style and module-doc tools still display legacy
findings outside these files.

For the scoped GG3 delta, the targeted
`Physlib.Optics.Systems.DCDR.ZTransformRegression` build passed under
`lake-lock`. With the four Z modules temporarily registered in the conductor's
requested order, the `Physlib` root rebuilt and `runPhyslibLinters` passed.
`lint-style.sh` passed on `ZTransformRegression.lean`; `Physlib.lean` was then
restored to the SHA recorded above.

The source has zero banned declarations, zero `theorem` declarations, maximum line
length 100 codepoints, and every DCDR file is below 1500 lines. `Physlib.lean` was
restored byte-for-byte after the temporary gate registration.

## Non-claims and human audit

This slice makes no claim of physical resonance, coherent-incoherent equivalence,
BIBO stability beyond the S4P gate, normalized-modal or electromagnetic power,
Maxwell time-domain meaning, reciprocity, physical-frequency meaning, or HOL-script
semantics. It also makes no DCDR chain claim.

Per `AI-POLICY.md`, a human author must independently certify the mathematical
statements, proofs, source mappings, and the stated X-01 boundary before merge.
