# S7C slice 5: DATE row and Physlib-original rectangular lattice

## Cutoff and synchronization

This cutoff implements the lattice slice requested by goal.md section S7C and regression row S-08.
The exact required sync target was
`fe56bbc20c930747bee5b23905187d734f09f5e5`. It was merged in
`cba99dc188576ab799682fab551c3dd0a4fe4003` before implementation. The later target
`5fc99609` was announced with an explicit instruction not to force a mid-slice resync.

The exact gated source head is
`13827bb6092099f0a54152c4bcde7aafbae2a32c`. Its three slice commits are:

- `e95c525fc7b5da803067dfc3f3c2203596e5f8ca`, module-doc normalization;
- `0075a77ea12a3128c12cde40d79c704ed7788e62`, lattice implementation; and
- `13827bb6092099f0a54152c4bcde7aafbae2a32c`, section-heading doc formatting.

The implementation adds two unregistered modules:

- `Physlib/Optics/Systems/Cascade/Lattice.lean` (1391 lines); and
- `Physlib/Optics/Systems/Cascade/LatticeRegression.lean` (699 lines).

Both are below the 1500-line cap. `Physlib.lean` is intentionally unchanged in this cutoff.

## Source scope and classification

The controlling goal text is:

- goal.md:2434, "the source-backed uncoupled row-sublattice result";
- goal.md:2435, "coupled row/column decompositions and the full `M × N` lattice theorem,
  explicitly classified as Physlib-original rather than DATE'14 parity"; and
- goal.md:2612, S-08: "Physlib extension: the `M × N` lattice flattening agrees with its
  row/column decomposition".

The corpus note at goal.md:153-155 says the lattice theorem is a Physlib extension and that
DATE'14 proves only the uncoupled row sublattice. DATE14.txt:204-207 says that Figure 3 decomposes
a two-dimensional lattice into an uncoupled row sublattice and a coupled column sublattice.
Its Figure 3 caption at lines 236-238 describes:

- a row sublattice consisting of a cascade of uncoupled MRRs periodically coupled to two side
  waveguides; and
- a column sublattice consisting of a linear cascade of mutually coupled MRRs.

DATE14.txt:372-373 says only that analysis of the coupled cascade "follows the similar pattern".
It supplies neither a formal coupled-column statement nor an `M × N` theorem. Parity IP-19
therefore classifies the source as incomplete: the row half is DATE'14 parity, while the column
and full lattice are the mandatory S7C Physlib extension.

Accordingly:

- Section A of `Lattice.lean` is the only DATE'14-parity content in this slice.
- Sections B-E and all of S-08 are Physlib-original.
- Every result introduced by the slice is a `lemma`; DATE'14 prints no lattice theorem.

## A. Source-backed uncoupled row

`DateUncoupledRowSublattice` at `Lattice.lean:86` stores exactly a list of existing
`DateCascadeStage` values. Its behavior and composition at lines 93 and 98 are definitions by
the existing heterogeneous cascade objects. It adds no ring, bus, or coupling physics.

The wrapper transfers the already discharged DATE results:

- `behavior_eq_composition_toBehavior` at `Lattice.lean:111` instantiates
  `dateCascadeBehavior_eq_composition_toBehavior` from
  `Heterogeneous.lean:227-241`;
- `identical_composition_eq_pow` at `Lattice.lean:120` instantiates the identical-stage power
  result from `Identical.lean:99-103`;
- `identical_composition_eq_sylvesterClosedForm` at `Lattice.lean:129` instantiates the exact
  Sylvester-domain result from `Identical.lean:336-343`;
- `TerminationHypotheses` at `Lattice.lean:137` is the existing corrected termination domain
  from `Termination.lean:321-330`;
- `reflectivity_eq_neg_entry12_div_entry11` at `Lattice.lean:155` reuses the relational
  reflection result from `Termination.lean:417-431`; and
- `transmissivity_eq_one_div_entry11` at `Lattice.lean:166` reuses the relational transmission
  result from `Termination.lean:433-447`.

Thus IP-15 through IP-18 transfer to the row without a new derivation or expanded parity claim.
The nonzero `M11` pivot remains part of the termination hypotheses.

## B. Physlib-original coupled column

`RectangularLatticeParameters` at `Lattice.lean:232` separates four-port ring-site scattering
laws from the horizontal and vertical neighbouring-coupler parameters. The construction then
provides explicit component and connection families:

- `rectangularLatticeComponents` at line 285;
- `rectangularHorizontalConnection` at line 385;
- `rectangularVerticalConnection` at line 406;
- `rectangularHorizontalConnections` at line 427; and
- `rectangularVerticalConnections` at line 442.

`rectangularCoupledColumnNetlist` at `Lattice.lean:635` is an explicit `FlatNetlist` for a
selected column. It contains one supplied four-port ring law per row and a separate directional
coupler between each pair of vertical neighbours. Its relational chain composition is
`rectangularCoupledColumnComposition` at line 658.

`rectangularCoupledColumn_behavior_eq_composition` at line 671 identifies the netlist behavior
with that singular-safe relational connection closure. This is a generic netlist instantiation,
not a DATE'14 statement and not a closed-form response.

## C. Full M by N lattice and S-08

The full lattice is one explicit `FlatNetlist`, not a behavior defined through either hierarchy.
`rectangularLatticeNetlist` at `Lattice.lean:868` directly specifies:

- all ring and coupler components;
- the sum of horizontal and vertical connection labels; and
- the appended physical connection family.

The canonical ordering is row-first: horizontal links are closed before vertical links. This
choice matches the direct connection-label order in the flat object. The alternate column-first
presentation follows only after a proved wiring reindex; the two label types are not silently
identified.

The hierarchy and response API is:

- `rectangularLatticeRowHierarchy` at line 724;
- `rectangularLatticeColumnHierarchy` at line 738;
- `rectangularRowColumnWiringEquiv` at line 1098;
- `rectangularRowDecompositionBehavior` at line 1111;
- `rectangularLatticeBehavior_eq_rowDecomposition` at line 1129;
- `rectangularColumnDecompositionBehavior` at line 1146;
- `rectangularColumnFlattenBehavior_eq_columnDecomposition` at line 1163;
- `rectangularLatticeBehaviorInColumnCoordinates` at line 1233;
- `rectangularColumnFlattenBehavior_eq_latticeBehavior_reindex` at line 1251;
- `rectangularColumnDecompositionInLatticeCoordinates` at line 1266; and
- `rectangularLatticeBehavior_eq_columnDecomposition` at line 1284.

These lemmas establish S-08 on the common relational domain without assuming well-posedness.
The row-first flatten is literally the canonical flat lattice. The column-first flatten agrees
after the explicit external-channel equivalence induced by connection-order reindexing.

## Regression and failure controls

`LatticeRegression.lean` uses a `2 × 2` fixture with distinct site coefficients
`2 * row + column + 1`, hence the site array `[[1, 2], [3, 4]]`. Couplers also have distinct
numbered parameters. The positive facts are expanded from the component, matrix, incident
assembly, connection, and output-readout primitives; they do not invoke either production S-08
behavior lemma.

The main positive anchors are:

- `latticeRegression_rawBehavior` at line 571, a direct witness in the canonical flat-netlist
  relation;
- `latticeRegression_outputEast` at line 584, whose selected response is `2`;
- `latticeRegression_rowFlatten_site01West_entry` at line 589, a direct entry calculation;
- `latticeRegression_columnFlatten_site01West_entry` at line 609, the independently selected
  column-first entry calculation;
- `latticeRegression_flatten_scattering_eq` at line 630, the directly reduced component-law
  equality; and
- `latticeRegression_selectedVerticalWire` and
  `latticeRegression_selectedColumnFirstVerticalWire` at lines 637 and 644, direct wiring
  anchors in the two label orders.

The negative fixture deliberately swaps each site's row and column indices:

- `latticeRegressionTransposedSites` at line 653;
- `latticeRegressionMisindexedColumnHierarchy` at line 660;
- `latticeRegression_misindexed_site01West_entry` at line 664, which computes `3` where the
  correct flattened lattice computes `2`; and
- `latticeRegression_misindexedFlatten_scattering_ne` at line 683, which proves the assembled
  flattened component laws unequal.

The negative proof is the required hierarchy/cascade-index sentinel: an index transposition
cannot be hidden by the correct decomposition API. It proves a concrete `2 != 3` matrix-entry
contradiction rather than testing a Boolean or reusing the production agreement lemma.

## Module-doc normalization (doc-only)

The literal module headings now used throughout this lane are:

- `## i. Overview`;
- `## ii. Key results`;
- `## iii. Table of contents`; and
- `## iv. References`.

Each table of contents matches its module's lettered section headings exactly. Existing
non-claims remain the first paragraph under `## iv. References`. The following existing-area
modules received comment-only normalization, with no declarations or proofs changed:

- `Heterogeneous.lean`;
- `HeterogeneousRegression.lean`;
- `Identical.lean`;
- `IdenticalRegression.lean`;
- `PandaBridge.lean`;
- `PandaGraph.lean`;
- `PandaMason.lean`;
- `PandaNetlist.lean`;
- `PandaRealization.lean`;
- `PandaResponse.lean`;
- `PandaResponseBridge.lean`;
- `PandaResponseRegression.lean`;
- `PandaTopologyRegression.lean`;
- `SourceMappedSfg.lean`;
- `SourceMappedSfgRegression.lean`;
- `Termination.lean`; and
- `TerminationRegression.lean`.

The standalone lettered headings in the new `LatticeRegression.lean` were also formatted as
module-doc comments. The heading-only commits preserve all existing declaration line numbers.

The prior PANDA HANDOFF citation is corrected here: `responseRegression_graphDet` is at
`PandaResponseRegression.lean:1201`, while
`responseRegression_graphDet_ne_zero` is at `PandaResponseRegression.lean:1207`.

## Non-claims

- No coupled-column or full-lattice result is presented as DATE'14 parity.
- No DATE'14 theorem is inferred from the phrase "follows the similar pattern".
- No closed form is claimed for the mutually coupled column or full lattice.
- No equality of differently labelled row-first and column-first channel types is claimed;
  column-first comparison uses the proved reindexing equivalence.
- No quadruple-ring row is introduced.
- No physical-realization claim is made for the supplied algebraic site or coupler laws.
- No passivity, losslessness, reciprocity, impedance matching, stability, causality,
  convergence, resonance, bandwidth, dispersion, pole/zero, bending-loss, insertion-loss,
  material, fabrication, or measurement-validation claim is made.
- No electromagnetic-power claim is made. Power remains normalized modal power until the
  hypotheses in `Physlib/Optics/HarmonicFlux/PropagatingModePower.lean:16-22,60-93` are supplied.
- Human verification of the source classification and intended physical model remains required
  by `AI-POLICY.md`.

## Reviewer map

1. Read `Lattice.lean:70-175` for the source-backed row aliases and transferred IP-15--18 API.
2. Read `Lattice.lean:620-676` for the explicit coupled-column netlist and relational behavior.
3. Read `Lattice.lean:724-875` for both hierarchies and the independent full flat netlist.
4. Read `Lattice.lean:1080-1301` for wiring reindexing and the two S-08 behavior equalities.
5. Read `LatticeRegression.lean:438-645` for the raw positive behavior and primitive anchors.
6. Read `LatticeRegression.lean:653-695` for the transposed-index negative control.
7. Review the two doc-only commits separately; their changes are confined to comments.

## Exact validation record

The exact implementation source head
`13827bb6092099f0a54152c4bcde7aafbae2a32c` passed one chained
`lake-lock env bash` gate. The gate temporarily registered only the two lattice modules and the
nine unregistered PANDA dependencies, then ran:

```text
lake exe cache get
lake --wfail build <the eleven unregistered Cascade modules>
lake exe runPhyslibLinters
lake exe lint_all
./scripts/lint-style.sh
git diff --check
the banned-token, declaration-kind, codepoint, line-cap, module-doc, and import audits
```

Results:

- cache: no downloads; 8690 files were already decompressed;
- targeted warning-as-error build: passed, 2783 jobs;
- `runPhyslibLinters`: Physlib and QuantumInfo passed;
- `lint_all`: full build and declaration linters passed;
- standalone committed-state `lint-style.sh`: passed;
- `git diff --check`: passed;
- the Cascade module-doc audit passed for all 19 lane modules;
- repository-wide module-doc diagnostics were confined to older out-of-lane files on this sync;
- the redundant-import audit named no Cascade module;
- no changed Lean file contains `sorry`, `axiom`, `native_decide`, `maxHeartbeats`, or
  `Lean.ofReduceBool`;
- the new lattice modules contain zero `theorem` declarations;
- every changed Lean line is at most 100 Unicode codepoints; and
- every new module is below 1500 lines.

The temporary registry was restored byte-identically. `Physlib.lean` had SHA-256
`88d1329fba21fc443261608300b3c922c4612d3cb4454a7f82e57e760aeaadb7` before and after the gate.
This final cutoff child changes only `HANDOFF.md`.
