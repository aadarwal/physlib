# S7C slice 5b: dynamic S-08 lattice regression

## Cutoff and synchronization

This cutoff completes the lattice slice requested by goal.md section S7C and regression row S-08.
The exact required sync target was
`fe56bbc20c930747bee5b23905187d734f09f5e5`. It was merged in
`cba99dc188576ab799682fab551c3dd0a4fe4003` before implementation. The later target
`5fc99609` was announced with an explicit instruction not to force a mid-slice resync.

The exact gated source head is
`9d737a7ebd8e74c03a1b3b386812f5a45a8b47a5`. The EE recut begins with
`348f95958156a998cb15cf2514ad58f0182b008c`, which extracts the neutral reindex API and shortens
the production proof. Commits `6fa7cee6` through `13faa391` replace the isolated regression with
the dynamic raw fixture, and `9d737a7e` applies the final committed-state style correction.

The implementation consists of:

- `Physlib/Optics/Network/LinearBehaviorReindex.lean` (66 lines), the authorized additive
  out-of-home neutral API module;
- `Physlib/Optics/Systems/Cascade/Lattice.lean` (1269 lines); and
- `Physlib/Optics/Systems/Cascade/LatticeRegression.lean` (972 lines).

All are below the 1500-line cap. `Physlib.lean` is intentionally unchanged in this cutoff.

## EE blocker disposition

The production construction had already passed EE. Slice 5b changes its implementation only by
extracting a generic inverse-reindex lemma, shortening the column-first proof, and clarifying that
`^ count` means matrix exponentiation. The substantive recut is the regression.

The new `2 × 2` fixture has distinct nonzero through and cross amplitudes. Its unit external drive
follows this directed route:

```text
ring(0,0).west -> ring(0,0).east -> H(row 0).right
  -> ring(0,1).west -> ring(0,1).south -> V(column 1).right
  -> ring(1,1).north -> ring(1,1).east
```

The horizontal and vertical wire amplitudes are respectively `-6 * I` and `-126`, and the final
external response is `-630`. The same concrete ambient state is established directly in the
canonical flat equations and independently through horizontal-inner then vertical-outer closure.
Neither proof invokes either production flattening equality.

The negative family swaps the successor-ring column on every vertical right endpoint. It therefore
mates `ring(1,1).north` with `V(column 0).right`, whose outgoing value is zero, instead of the
canonical `V(column 1).right`, whose outgoing value is `-126`. The hostile raw incident-assembly
equation is rejected by the concrete contradiction `-126 = 0`. This exercises the S-08 wiring and
hierarchy-index failure mode rather than merely comparing component scattering tables.

## Source scope and classification

The controlling goal text is:

- goal.md:2434, "the source-backed uncoupled row-sublattice result";
- goal.md:2435, "coupled row/column decompositions and the full `M × N` lattice theorem,
  explicitly classified as Physlib-original rather than DATE'14 parity"; and
- goal.md:2612, S-08: "Physlib extension: the `M × N` lattice flattening agrees with its
  row/column decomposition".

The corpus note at goal.md:153-155 says the lattice theorem is a Physlib extension and that
DATE'14 proves only the uncoupled row sublattice. DATE14.txt:204-207 says that Figure 3 decomposes
a two-dimensional lattice into an uncoupled row sublattice and a coupled column sublattice. Its
Figure 3 caption at lines 236-238 describes:

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
- Every result introduced by this slice is a `lemma`; DATE'14 prints no lattice theorem.

## A. Source-backed uncoupled row

`DateUncoupledRowSublattice` at `Lattice.lean:88` stores exactly a list of existing
`DateCascadeStage` values. Its behavior and composition at lines 95 and 100 are definitions by
the existing heterogeneous cascade objects. It adds no ring, bus, or coupling physics.

The wrapper transfers the already discharged DATE results:

- `behavior_eq_composition_toBehavior` at `Lattice.lean:113` instantiates
  `dateCascadeBehavior_eq_composition_toBehavior` at `Heterogeneous.lean:227`;
- `identical_composition_eq_pow` at `Lattice.lean:123` instantiates the matrix-exponentiation
  result at `Identical.lean:99`;
- `identical_composition_eq_sylvesterClosedForm` at `Lattice.lean:132` instantiates the exact
  Sylvester-domain result at `Identical.lean:337`;
- `TerminationHypotheses` at `Lattice.lean:140` is the corrected termination domain whose source
  structure is at `Termination.lean:326`;
- `reflectivity_eq_neg_entry12_div_entry11` at `Lattice.lean:158` reuses the relational
  reflection result at `Termination.lean:422`; and
- `transmissivity_eq_one_div_entry11` at `Lattice.lean:169` reuses the relational transmission
  result at `Termination.lean:438`.

Thus IP-15--17 and only the already-discharged DATE'14 Thm. 5 half of IP-18 transfer to the row.
This slice makes no new printed-Thm.-6 or broader IP-18 claim. The nonzero `M11` pivot remains in
the termination hypotheses.

## B. Neutral reindex API and Physlib-original coupled column

The authorized out-of-home module `LinearBehaviorReindex.lean` adds only
`LinearBehavior.reindex_symm_reindex` at line 51. It states that finite behavior relabelling
followed by the inverse relabelling recovers the original relation. No existing neutral declaration
was changed, and the neutral module imports no Cascade or regression module.

`RectangularLatticeParameters` at `Lattice.lean:235` separates four-port ring-site scattering laws
from horizontal and vertical neighbouring-coupler parameters. The explicit component and connection
families begin at:

- `rectangularLatticeComponents`, line 288;
- `rectangularHorizontalConnection`, line 388;
- `rectangularVerticalConnection`, line 409;
- `rectangularHorizontalConnections`, line 430; and
- `rectangularVerticalConnections`, line 445.

`rectangularCoupledColumnNetlist` at `Lattice.lean:638` is an explicit `FlatNetlist` for one
selected column. It contains a supplied four-port ring law per row and a separate directional
coupler between each pair of vertical neighbours. Its singular-safe relational composition is
`rectangularCoupledColumnComposition` at line 661, and
`rectangularCoupledColumn_behavior_eq_composition` at line 674 identifies the netlist behavior
with that closure. DATE'14 supplies no statement or closed form for this object.

## C. Full M by N lattice and S-08

The full lattice is one explicit `FlatNetlist`, not a behavior defined through either hierarchy.
`rectangularLatticeNetlist` at `Lattice.lean:871` directly specifies all components, the sum of
horizontal and vertical connection labels, and their appended physical connection family.

The canonical ordering is row-first: horizontal links are closed before vertical links. This
matches the direct connection-label order in the flat object. The alternate column-first
presentation follows only after a proved wiring reindex; the two label types are not silently
identified.

The hierarchy and response API is:

- `rectangularLatticeRowHierarchy`, line 727;
- `rectangularLatticeColumnHierarchy`, line 741;
- `rectangularRowColumnWiringEquiv`, line 1101;
- `rectangularRowDecompositionBehavior`, line 1114;
- `rectangularLatticeBehavior_eq_rowDecomposition`, line 1132;
- `rectangularColumnDecompositionBehavior`, line 1149;
- `rectangularColumnFlattenBehavior_eq_columnDecomposition`, line 1166;
- `rectangularLatticeBehaviorInColumnCoordinates`, line 1182;
- `rectangularColumnFlattenBehavior_eq_latticeBehavior_reindex`, line 1200;
- `rectangularColumnDecompositionInLatticeCoordinates`, line 1215; and
- `rectangularLatticeBehavior_eq_columnDecomposition`, line 1233.

These lemmas establish S-08 on the common relational domain without assuming well-posedness.
The row-first flatten is literally the canonical flat lattice. The column-first flatten agrees
after the explicit external-channel equivalence induced by connection-order reindexing. The final
column proof is now lines 1233-1263 and uses the neutral inverse-reindex lemma.

## Dynamic regression and wiring failure control

The positive anchor is expanded from Mathlib and Physlib primitives rather than either production
S-08 equality:

- `latticeRegression_mem_componentBehavior` at `LatticeRegression.lean:450` expands every
  component scattering equation for the concrete state;
- `latticeRegression_connectedEquation` at line 574 expands every canonical mate equation;
- `latticeRegression_incidentAssembly` at line 627 and
  `latticeRegression_outputReadout` at line 645 assemble the raw flat witness;
- `latticeRegression_mem_flatBehavior` at line 659 places that witness in the canonical flat
  relation;
- `latticeRegression_mem_innerClosure`, `latticeRegression_mem_innerBoundary`, and
  `latticeRegression_mem_outerClosure` at lines 689, 717, and 744 independently construct the
  horizontal-inner and vertical-outer stages;
- `latticeRegression_mem_rowDecomposition` at line 766 places the same pair in the staged
  row-first behavior;
- `latticeRegression_horizontalWire_nonzero` and
  `latticeRegression_verticalWire_nonzero` at lines 779 and 792 prove nonzero traversal of both
  connection families;
- `latticeRegression_crossParameters` at line 805 pins distinct nonzero coupler values;
- `latticeRegression_inputValue` and `latticeRegression_outputValue` at lines 822 and 827 pin
  the unit drive and `-630` response; and
- `latticeRegression_flat_and_rowDecomposition` at line 835 joins the independently proved
  memberships without a production flattening theorem.

The hostile wiring is an actual `PortConnectionFamily`, beginning with
`latticeRegressionMiswiredVerticalConnection` at `LatticeRegression.lean:849`.
`latticeRegressionMiswired_incidentAssembly_ring11North` at line 944 calculates the wrong mate,
and `latticeRegressionMiswired_incidentAssembly_rejected` at line 957 proves that no hostile
external input makes the canonical incident state satisfy that raw assembly. This is the requested
mis-lift/mis-mate negative pair, not a relabelled version of the old `2 != 3` fixture.

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

The prior PANDA citation is also corrected here: `responseRegression_graphDet` is at
`PandaResponseRegression.lean:1201`, while `responseRegression_graphDet_ne_zero` is at line 1207.

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
- No electromagnetic-power claim is made. The `^ count` notation is matrix exponentiation;
  modal power remains non-electromagnetic until the hypotheses in
  `Physlib/Optics/HarmonicFlux/PropagatingModePower.lean:16-22,60-93` are supplied.
- Human verification of the source classification and intended physical model remains required
  by `AI-POLICY.md`.

## Reviewer map

1. Read `LatticeRegression.lean:450-667` for the primitive component, mate, assembly, and flat
   behavior proof.
2. Read `LatticeRegression.lean:670-840` for the independently staged closure and nonzero
   horizontal/vertical traversal anchors.
3. Read `LatticeRegression.lean:843-967` for the hostile vertical endpoint and raw-equation
   rejection.
4. Read `LinearBehaviorReindex.lean:44-60` and `Lattice.lean:1233-1263` for the authorized neutral
   extraction and shortened production proof.
5. Read `Lattice.lean:79-174` for the source-backed row classification and narrowed IP-18 claim.
6. Read `Lattice.lean:614-678,722-877,1082-1263` for the explicit column, flat lattice, wiring
   reindex, and two Physlib-original decompositions.
7. Review the module-doc normalization commits separately; they change comments only.

## Exact validation record

The exact implementation source head
`9d737a7ebd8e74c03a1b3b386812f5a45a8b47a5` was tested with a temporary registration of the
neutral reindex module, both lattice modules, and the nine unregistered PANDA dependencies. One
chained `lake-lock env bash` hold ran:

```text
lake exe cache get
lake --wfail build Physlib
lake exe runPhyslibLinters
lake exe lint_all
./scripts/lint-style.sh
lake exe module_doc_lint
```

The frozen sync's repository-wide module-doc backlog makes the last command nonzero after all
in-scope files have been checked. The filename-filtered module-doc confirmation, `git diff --check`,
and the static audits were therefore run immediately afterward.

Results:

- cache: no downloads; 8690 files were already decompressed;
- warning-as-error `Physlib` build: passed, 4953 jobs;
- `runPhyslibLinters`: Physlib and QuantumInfo passed;
- `lint_all`: full build, illegal-import check, duplicate-tag check, sorry/pseudo check, and
  declaration linters passed; its listed missing registrations and transitive-import diagnostics
  are pre-existing and outside the lane on the frozen sync;
- standalone committed-state `lint-style.sh`: passed;
- repository-wide `module_doc_lint` reaches only legacy out-of-lane documentation failures on
  this frozen sync; a registration-active filename-filtered rerun reported no Cascade or
  `LinearBehaviorReindex.lean` error, and all 20 in-scope modules have the exact four headings and
  matching tables of contents;
- `git diff --check`: passed;
- no in-scope Lean file exceeds 100 Unicode codepoints per line;
- all twelve unregistered modules are below 1500 lines;
- no changed lattice or neutral Lean file contains `sorry`, `axiom`, `native_decide`,
  `maxHeartbeats`, or `Lean.ofReduceBool`;
- the two lattice modules contain zero `theorem` declarations; and
- production modules do not import regression modules.

The temporary registry was restored byte-identically. `Physlib.lean` had SHA-256
`88d1329fba21fc443261608300b3c922c4612d3cb4454a7f82e57e760aeaadb7` before and after the gate.
This final cutoff child changes only `HANDOFF.md`.
