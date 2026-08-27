# Slice 1B blocker record

The fixture proves uniform couplers and unit-amplitude, zero-phase propagation. R1, R2 and R3
travel; R1 is the two-lemma responseTransform instantiation, R2 the 1499-line headroom fact, and
R3 the provisional citation tags. R4 is owed at merge and R5 parked. The repeated false-fold was
status drift: I conflated an earlier repair plan with landed files.
Before writing residual status, resolve it against the cutoff tree; for R1 grep the target directory
for the named declaration.

## Enumeration-falsifiable blockers

1. **Refuted (CCC-1):** conversion exists as `TwoPortScatteringTransform.toBackwardFirstChainTransform`
(`Physlib/Optics/Network/TwoPortScatteringChain.lean:523`, gate
`HasBijectiveRightToLeftTransmission`) and the reverse
(`Physlib/Optics/Network/TwoPortChainScattering.lean:652`, gate `HasBijectiveLeadingBlock`),
with criteria/round trips at :617/:724/:781.
2. **Refuted (CCC-2) BY AN IFF:** `idealRouting_rephase_eq_iff` (:127),
`partialRouting_rephase_eq_iff` (:220), `externalIncidentInjection_rephase_eq` (:280),
`externalOutgoingReadout_rephase_eq` (:301), and `incidentAssembly_rephase` (:342) in
`Physlib/Optics/Network/ConnectionRoutingRephase.lean` provide transport. `D = diag(1,-1)` is a
`ModePhaseGauge` (Physlib/Optics/Mode/Rephase.lean:65) because `-1` is unit-complex.

## Reclassification

The surviving coordinate dictionary is a missing definition plus transport lemmas connecting
existing machinery on both sides, unlike family-fold and graft combinators, which are constructions
the library cannot express.

## Audit trail

SURFACE: `Physlib/` and `QuantumInfo/`, all `.lean`, unbounded output, three axes.
- Axis A, naming: `heebner|unitcell|unit_cell|blochmatrix|A_j|B_j` — 8 hits, of which the only
  optical ones are two prose citations (CROWRegression.lean:54 and the fixture's own References
  line at :28); the rest are an Electromagnetism index expression and QuantumInfo summation indices.
- Axis B, structural and deliberately vocabulary-independent: declarations named for internal/cut/
  boundary field states — 6 hits, all in the microring physical-realization stack. Inspected and
  rejected: `AllPassInternalFields` (`Physlib/Optics/Systems/Microring/PhysicalRealization.lean:127`,
  fields `launched`/`returning`) and `AddDropInternalFields` (:149), with
  `allPassInternalFieldsOfState` (:192), `addDropInternalFieldsOfState` (:263) and fixtures in
  `PhysicalRegression.lean:345/:370`. These are per-device circulation fields, not an ordered
  boundary pair at a repeated cell cut, and nothing maps them to `(A_j,B_j)`.
- Axis C, target-object: `table1|table 1` — 36 hits; every non-CROW one belongs to FMICS'15 DCDR or
  Saleh–Teich, different sources entirely.
CONCLUSION: the surviving claim — no coordinate dictionary identifying Heebner `(A_j,B_j)` with our
channels — SURVIVES this sweep. This sweep was performed by review (CCC-3) and adopted here; both
refuters were found by review, not by the lane audit, and the second lay outside its searched areas.

## Comparison status

Table-1 rows covered: **NONE (no entitlement to compare yet)**. Uniformity and unit amplitude alone
do not identify a comparable `(A,B)` entry without the surviving coordinate dictionary; the
anchor rule forbids comparison. No outcome is claimed.
