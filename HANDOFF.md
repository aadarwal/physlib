# S4-B selected one-delay network pole criterion

## Cutoff

- Gated source candidate: `04e20c7b` on `wip/s4b-network-pole-criterion-aaa`.
- Merge the committed source, not a moving branch reference.
- Exclude this `HANDOFF.md` child from `optics/development`.
- The source stacks on the review-clean S4-A gated source `1765835f`.
- Files relative to `1765835f`:
  - new `Physlib/Optics/Systems/DelayTransfer/NetworkPoleCriterion.lean`;
  - new `Physlib/Optics/Systems/DelayTransfer/NetworkPoleCriterionRegression.lean`;
  - comment-only scope refresh in
    `Physlib/Optics/Systems/DelayTransfer/RationalElimination.lean`;
  - additive scope/ledger edits in `Physlib/Optics/API-map.yaml`, `goal.md`, and `tbd.md`.

## Claim and boundary

This slice connects one selected response entry of a one-delay `RationalNetlist` to the existing
abstract `RationalReduction` pole schema. An explicit certificate identifies the reduction's raw
numerator with the selected cleared adjugate numerator and its raw denominator with the cleared
internal determinant. Actual poles are therefore contained in candidate determinant roots. Under
component-entry regularity and pointwise no cancellation, actual-pole membership is equivalent to
failure of the N5F solve gate. On the N5F response domain, the reduced quotient equals the selected
proof-gated response entry.

The visible-pole regression uses exact `3/5` through, `-4*I/5` cross, and `q/2` propagation
entries. It independently expands the selected numerator to `3/5 - q/2`, the determinant to
`1 - 3*q/10`, and the raw N5 feedback matrix. At `q = 10/3`, the numerator is `-16/15`, the
explicit vector `[0, 5, 3]` is a nonzero kernel vector, and the wrong-feedback-sign determinant is
nonzero. The independent anchor does not use the production pole-identification criterion.

The certificate is supplied, not constructed. This slice does not provide a canonical gcd
reduction, a general reachability/observability test, or a minimal-realization theorem. It makes no
physical-frequency, resonance, causality, ROC, stability, BIBO, passivity, reciprocity, bandwidth,
or material claim. The S4/S4P completion is exactly the explicit-certificate/no-cancellation
alternative already named by the goal; it is not a claim that all internal singularities are poles.

## Documentation delta accounting

- `Physlib/Optics/Systems/DelayTransfer/RationalElimination.lean:45-53` replaces S4-A's now-stale
  statement that every network criterion is withheld. It points to this explicit-certificate
  bridge while retaining the canonical-reduction, reachability/observability, minimality, and
  physical non-claims. No declaration, proof, or import in that registered module changes.
- `Physlib/Optics/API-map.yaml:607-608` rewrites the delay-transfer description for the selected
  network certificate and changes the row from `done: false` to `done: true`.
- `Physlib/Optics/API-map.yaml:639-651` separately inserts the two module locations and their
  public evidence declarations.
- `goal.md:2311-2313` refines the already-checked S4 pole-schema item to include the certified
  selected one-delay network layer; this hunk does not flip a box.
- `goal.md:2326-2333` records the certificate, the solve-gate equivalence, response semantics, and
  the canonical-reduction/reachability/minimality fences.
- `goal.md:2341-2342` flips the sole remaining S4P implementation box: the explicit
  certificate-based, pointwise no-cancellation network criterion.
- `goal.md:2874` rewrites the already-`done` S4 status row to remove the retired S4P blocker.
- `goal.md:2875` changes S4P from `in progress` to `done`, explicitly retaining the general
  reachability/observability and minimal-realization non-claims.
- `tbd.md:1753-1766` replaces the retired S4-B implementation gap with one combined human-check
  of S4-A and S4-B, including both independent regressions and the stronger residual non-claims.

## Production declaration map

All declarations below are in
`Physlib/Optics/Systems/DelayTransfer/NetworkPoleCriterion.lean`.

### One-delay coordinates and certificate

- `oneDelayPolynomialEquiv`: line 75.
- `oneDelayPolynomialEquiv_eval`: line 79.
- `OneDelayNetworkResponseReduction`: line 93.
- `OneDelayNetworkResponseReduction.isGenericallyWellPosed`: line 114.

### Candidate singularities and actual poles

- `OneDelayNetworkResponseReduction.candidateSingularities`: line 129.
- `OneDelayNetworkResponseReduction.actualPoles`: line 134.
- `OneDelayNetworkResponseReduction.rawDenominatorRoots_eq_candidateSingularities`: line 139.
- `OneDelayNetworkResponseReduction.actualPoles_subset_candidateSingularities`: line 148.
- `OneDelayNetworkResponseReduction.mem_actualPoles_of_mem_candidateSingularities`: line 155.
- `OneDelayNetworkResponseReduction.candidateSingularities_subset_actualPoles`: line 168.
- `OneDelayNetworkResponseReduction.candidateSingularities_eq_actualPoles`: line 178.
- `OneDelayNetworkResponseReduction.mem_candidateSingularities_iff_not_mem_solveDomain`: line 189.
- `OneDelayNetworkResponseReduction.mem_actualPoles_iff_not_mem_solveDomain`: line 206.

### Reduced-response semantics

- `OneDelayNetworkResponseReduction.reduced_eval_eq_evaluatedResponseQuotient`: line 229.
- `OneDelayNetworkResponseReduction.noPoleCancellation_of_mem_responseDomain`: line 243.
- `OneDelayNetworkResponseReduction.reduced_eval_eq_response`: line 258.

## Regression declaration map

All declarations below are in
`Physlib/Optics/Systems/DelayTransfer/NetworkPoleCriterionRegression.lean`.

### Three-port fixture

- `VisiblePolePort`: line 65.
- `visiblePolePortFintype`: line 72.
- `visiblePolePortFamily`: line 79.
- `visiblePolePropagationPolynomial`: line 84.
- `visiblePoleEntryPolynomial`: line 88.
- `visiblePoleComponents`: line 98.
- `visiblePoleAggregateChannel`: line 106.
- `visiblePoleLeftPort`: line 111.
- `visiblePoleRightPort`: line 116.
- `visiblePoleConnection`: line 121.
- `visiblePoleConnections`: line 131.
- `visiblePoleNetlist`: line 145.
- `visiblePoleComponent`: line 151.
- `visiblePoleLocalChannel`: line 156.
- `visiblePoleChannel`: line 162.
- `visiblePoleComponent_channel`: line 166.
- `visiblePoleExternalChannel`: line 173.
- `visiblePoleAggregateExternal_not_mem_range`: line 184.

### Typed finite coordinates

- `visiblePoleChannelFintype`: line 202.
- `visiblePoleConnectedChannelFintype`: line 207.
- `visiblePoleConnectionChannelFintype`: line 213.
- `visiblePoleChannelDecidableEq`: line 219.
- `visiblePoleAggregateChannelDecidableEq`: line 223.
- `visiblePoleConnectedChannelDecidableEq`: line 229.
- `visiblePoleConnectionChannelDecidableEq`: line 233.
- `visiblePoleChannelEquiv`: line 237.
- `visiblePoleIncidentEquiv`: line 253.
- `visiblePoleOutgoingEquiv`: line 257.
- `visiblePoleIncidentEquiv_symm_zero`: line 261.
- `visiblePoleIncidentEquiv_symm_one`: line 265.
- `visiblePoleIncidentEquiv_symm_two`: line 269.
- `visiblePoleOutgoingEquiv_symm_zero`: line 273.
- `visiblePoleOutgoingEquiv_symm_one`: line 277.
- `visiblePoleOutgoingEquiv_symm_two`: line 281.
- `visiblePoleConnectedLeft`: line 285.
- `visiblePoleConnectedRight`: line 289.
- `visiblePoleConnectedLeft_embedding`: line 293.
- `visiblePoleConnectedRight_embedding`: line 298.
- `visiblePoleConnectedLeft_mate`: line 303.
- `visiblePoleConnectedRight_mate`: line 308.
- `visiblePoleExternalChannelUnique`: line 313.
- `visiblePoleExternalIncidentUnique`: line 325.
- `visiblePoleExternalOutgoingUnique`: line 332.
- `visiblePoleExternalIncidentEquiv`: line 339.
- `visiblePoleExternalOutgoingEquiv`: line 343.

### Cleared matrix expansion

- `visiblePole_scatteringEntryModel`: line 353.
- `visiblePole_scatteringEntryModel_denominator`: line 363.
- `visiblePole_commonDenominator`: line 383.
- `visiblePole_denominatorComplement`: line 391.
- `visiblePole_clearedScattering_entry`: line 400.
- `visiblePoleClearedScatteringMatrix`: line 413.
- `visiblePolePolynomialRoutingMatrix`: line 420.
- `visiblePoleClearedFeedbackMatrix`: line 426.
- `visiblePolePolynomialInputExposureMatrix`: line 432.
- `visiblePolePolynomialOutputReadoutMatrix`: line 437.
- `visiblePoleNumeratorPolynomial`: line 442.
- `visiblePoleDenominatorPolynomial`: line 446.
- `visiblePole_clearedScattering_reindex`: line 450.
- `visiblePole_polynomialRouting_external_row`: line 460.
- `visiblePole_polynomialRouting_external_column`: line 472.
- `visiblePole_polynomialRouting_left_left`: line 484.
- `visiblePole_polynomialRouting_left_right`: line 506.
- `visiblePole_polynomialRouting_right_left`: line 517.
- `visiblePole_polynomialRouting_right_right`: line 528.
- `visiblePole_polynomialRouting_reindex`: line 550.
- `visiblePole_clearedFeedback_reindex`: line 559.
- `visiblePole_polynomialInputExposure_reindex`: line 585.
- `visiblePole_polynomialOutputReadout_reindex`: line 626.
- `visiblePole_responseNumerator_factors_reindex`: line 667.
- `visiblePole_responseNumerator_reindex`: line 704.
- `visiblePole_responseNumerator_mv`: line 735.
- `visiblePole_responseNumerator`: line 750.
- `visiblePole_responseDenominator_mv`: line 760.
- `visiblePole_responseDenominator`: line 787.

### Reduction certificate and independent pole anchor

- `visiblePoleNumeratorPolynomial_ne_zero`: line 800.
- `visiblePoleDenominatorPolynomial_ne_zero`: line 806.
- `visiblePolePolynomials_isCoprime`: line 812.
- `visiblePoleReducedResponse`: line 824.
- `visiblePoleReduction`: line 832.
- `visiblePoleCertificate`: line 842.
- `visiblePoleFeedbackMatrix`: line 851.
- `visiblePole_componentEntriesRegularAt`: line 857.
- `visiblePole_feedbackOperator_reindex`: line 868.
- `visiblePoleRoot`: line 890.
- `visiblePoleKernelVector`: line 893.
- `visiblePoleWrongSignFeedbackMatrix`: line 896.
- `visiblePole_denominator_at_root`: line 902.
- `visiblePole_numerator_at_root`: line 907.
- `visiblePole_actualPole`: line 912.
- `visiblePole_feedback_mulVec_kernel`: line 917.
- `visiblePoleKernelVector_ne_zero`: line 926.
- `visiblePole_feedbackMatrix_det_zero`: line 932.
- `visiblePole_feedbackOperator_det_zero`: line 941.
- `visiblePole_not_mem_solveDomain`: line 950.
- `visiblePole_wrongSign_det_ne_zero`: line 959.
- `visiblePole_noPoleCancellation`: line 966.
- `visiblePole_networkCriterion`: line 972.
- `visiblePole_independent_anchor`: line 981.

The direct anchor uses none of
`OneDelayNetworkResponseReduction.mem_actualPoles_iff_not_mem_solveDomain`,
`OneDelayNetworkResponseReduction.mem_candidateSingularities_iff_not_mem_solveDomain`, or
`OneDelayNetworkResponseReduction.reduced_eval_eq_response`. The confirmatory
`visiblePole_networkCriterion` separately exercises the first of those production results.

## Gates run at the source candidate

- `lake-lock build Physlib.Optics.Systems.DelayTransfer.NetworkPoleCriterion`: pass.
- `lake-lock build Physlib.Optics.Systems.DelayTransfer.NetworkPoleCriterionRegression`: pass.
- `lake-lock build Physlib.Optics.Systems.DelayTransfer.RationalElimination` after the comment-only
  boundary refresh: pass.
- Temporary root registration of S4-A and S4-B followed by `lake-lock build Physlib`: pass
  (5025 jobs; one pre-existing informational `ring_nf` suggestion in DCDR Z-transform code).
- Full temporary-registry `lake-lock exe runPhyslibLinters`: pass for Physlib and QuantumInfo.
- `lake-lock exe api_map_index`: pass (34 maps, 653 requirements, 506 done).
- `module_doc_lint`: no finding on either new module; the command retains the known repository
  baseline outside this slice.
- `git diff --check`: pass.
- `scripts/lint-style.sh`: pass.
- Both Lean files have maximum line length at most 100 codepoints.
- Zero `sorry`, `axiom`, `native_decide`, `maxHeartbeats`, or `theorem` declarations.
- Production is 271 lines; regression is 995 lines. They are separate modules and commits. The
  regression exceeds the review guideline because the independently expanded typed three-port N5
  fixture carries its own channel equivalences, routing, scattering, exposure, readout, adjugate,
  determinant, kernel, and wrong-sign calculations.

## Registration after hostile review

Add these public imports to `Physlib.lean`, before `Physlib.Optics.Systems.DelayTransfer.Poles` in
repository-sorted order:

1. `Physlib.Optics.Systems.DelayTransfer.NetworkPoleCriterion`
2. `Physlib.Optics.Systems.DelayTransfer.NetworkPoleCriterionRegression`

S4-A separately registers `RationalElimination` and `RationalEliminationRegression`. Before
committing S4-B registration, temporarily register the S4-B modules, run a root build, then run the
full `runPhyslibLinters` registry linter. The final registration child should contain only
`Physlib.lean` unless hostile review requests a source correction.

## Reviewer order

1. Verify the certificate fields and one-delay evaluation equivalence, production lines 75-121.
2. Verify actual-pole containment, the no-cancellation converse, and the solve-gate IFF,
   production lines 129-220.
3. Verify reduced-quotient and N5F response semantics, production lines 229-266.
4. Verify the typed three-port and connected-channel ordering, regression lines 65-343.
5. Verify the displayed `S`, `C`, `1-C*S`, exposure, and readout matrices, regression lines
   353-666.
6. Verify the factored reindexing, four-factor adjugate numerator, and determinant expansions,
   regression lines 667-798.
7. Verify the explicit Bézout reduction and hostile anchor, regression lines 800-991; grep for the
   three production identification lemmas named above.
8. Check every documentation hunk and confirm that completion is limited to the explicit
   certificate/no-cancellation alternative, with canonical reduction and general
   reachability/observability/minimality still unclaimed.
