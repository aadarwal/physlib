# S7D slice 8 handoff: DCDR causal-Z cross-semantics leg

## Cutoff identity

- Exact sync target: `8e48a7d1fa1ef1080bfe75dbfc93c6768ec3bdcb`.
- Sync merge: `60d7f6ab7ed1a11f2ab23fc3433505aca1fb95bf`.
- Gated source: `c715d76079fa8457c5be328f1b287320fb4a77d7`.
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
  the agreement record.
- `Physlib/Optics/Systems/DCDR/ZTransformRegression.lean`: exact positive and
  negative fixtures.

Please register these imports in repository-sorted order:

```lean
public import Physlib.Optics.Systems.DCDR.ZTransform
public import Physlib.Optics.Systems.DCDR.ZTransformBridge
public import Physlib.Optics.Systems.DCDR.ZTransformRegression
```

## Claims delivered

`ZTransform.lean` constructs the causal recurrence directly from the unit-delay
response numerator and loop polynomials. Its `zTransferROC` is the generic
`iirROC`; membership separately yields `z != 0` and the recurrence-denominator
gate. On that ROC, the causal impulse-response transform equals `zTransfer`, and
`zTransfer` is the rational response at the explicitly stated coordinate
`q = z⁻¹`. `UnitDelayParameters.IsZContractive` supplies a sufficient Schur result;
the ROC and Schur conditions remain distinct.

`ZTransformBridge.lean` proves the recurrence denominator is nonzero exactly when
the fixed N5 denominator gate holds. It identifies `zTransfer` with the compiled
reciprocal-Z N5F response, the response-indexed reduced quotient under its
no-cancellation and evaluation gates, the convergent circulation series, the fixed
N5 response, the complete Mason response, the packaged typed-scattering entry, and
an original-relation witness. The common-domain object stores admissibility,
recurrence contraction, reduced Schur stability, loop contraction, ROC membership,
no cancellation, and reduced evaluation separately. Unitarity is not assumed
because none of these identifications uses it.

The fixed N5 leg reuses the accepted raw-equation elimination bridge in
`Response.lean`. The Mason leg reuses the accepted G-04 instantiation in
`Mason.lean`; neither result is reproved here.

## Regression teeth

- The stable exact point has couplers `t = 3/5`, `k = 4/5`, gains
  `(9/16, 1, 1)`, and `z = 1`. Its loop polynomial is zero, denominator is one,
  numerator is `-(7/16) q - (9/16) q^3`, and every applicable view is pinned to
  `-1` without invoking `zCrossSemantics_agree`.
- The nonreal point `z = I`, hence `q = -I`, expands the direct recurrence and raw
  compiled reciprocal-Z response to `-(7/8) I` without using the main bridge.
- The active sentinel expands a nonsummable loop: `zTransfer = -67/20`, while the
  totalized circulation series is `1/4`. Reduced Schur stability fails, so the
  common domain is impossible. This makes the gate load-bearing.

The main regression declarations are `zRegression_crossSemantics`,
`zRegression_nonreal_raw_compiled`,
`zRegression_active_circulation_ne_transfer`, and
`zRegression_active_not_crossSemanticsDomain`.

## Reused foundations

- Ring promoted-rational pattern:
  `Physlib/Optics/Systems/Microring/AllPassDelayTransfer.lean:127-178`.
- Ring named-ROC pattern:
  `Physlib/Optics/Systems/Microring/AllPassZTransform.lean:193-346`.
- Ring common-domain pattern:
  `Physlib/Optics/Systems/Microring/AllPassZTransformBridge.lean:95-122,321-428`.
- DCDR unit-delay rational compilation:
  `Physlib/Optics/Systems/DCDR/Poles.lean:82-205,322-426,571-713`.
- DCDR raw N5 response: `Physlib/Optics/Systems/DCDR/Response.lean:461-555`.
- DCDR G-04 Mason bridge: `Physlib/Optics/Systems/DCDR/Mason.lean:177-197`.
- Generic recurrence/ROC:
  `Physlib/Mathematics/ZTransform/DifferenceEquation.lean:271-295`.
- Generic Schur layer: `Physlib/Mathematics/ZTransform/Stability.lean:223-289`.

## Gate record

Targeted builds of all three new modules passed under `lake-lock`. With temporary
root registration of the accepted slice-7 modules and these three modules, the
following passed: cache retrieval, `lake --wfail build Physlib`,
`check_file_imports`, `sorry_lint`, `runPhyslibLinters`, `api_map_index`, and
`lint_all`. Exact filtered runs of `lint-style` and `module_doc_lint` are clean for
the new DCDR Z files. The shipped repository-wide module-doc script still reports
legacy findings outside these files.

The source has zero banned declarations, zero `theorem` declarations, maximum line
length 100 codepoints, and every new file is below 1500 lines.

## Non-claims and human audit

This slice makes no claim of physical resonance, coherent-incoherent equivalence,
BIBO stability beyond the S4P gate, normalized-modal or electromagnetic power,
Maxwell time-domain meaning, reciprocity, physical-frequency meaning, or HOL-script
semantics. It also makes no DCDR chain claim.

Per `AI-POLICY.md`, a human author must independently certify the mathematical
statements, proofs, source mappings, and the stated X-01 boundary before merge.
