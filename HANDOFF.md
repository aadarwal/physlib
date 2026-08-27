# S7C Phase 9b: polarization and interface physical ports

## Cutoff and synchronization

This phase synchronized exactly onto the controller-authorized registered head
`9c1f4929d20a17fcc7ada2c37c1e5f2f82b3df38`. The synchronization merge is
`9b94c76ccb9ddb537c11745df0786bf9f9479d43`. The gated source is
`e81a48b71ef9be208ea461fecf65549277053039`. This cutoff is its HANDOFF-only child.

Relative to the sync target, the source adds exactly three files. The registered Phase 9a file
`Physlib/Optics/Components/PhysicalPortSuiteRegression.lean` is byte-identical to the sync
target. Its initially additive Phase 9b extension was moved, with public declaration names and
namespaces unchanged, into the controller-authorized split regression before the cutoff.
`Physlib.lean` remains byte-identical to the sync target.

## Goal and phase boundary

The controlling N7 text at `goal.md:2184-2186` on the gated source says:

> component-owned physical-port packaging consumed by `ScatteringComponentFamily`: the
> beam-splitter and mirror packages are complete, while polarization and interface primitives
> remain;

Phase 9b supplies both remaining packages. Together with the accepted Phase 9a beam-splitter and
mirror packages, this completes that four-member packaging bullet. The frequency-parameterized
propagation item at `goal.md:2187-2188` remains open. The separate reciprocity metadata slice is
also not part of this cutoff.

The adapters and regression are Physlib-original packaging. Every result is a `lemma`; this phase
asserts no literal printed physics theorem.

## Binding convention record

The implementation consumes the registered primitives without restating their conventions.

- C-02 / decision L1: `Phasor.realize` uses positive time, and the registered
  `JonesVector.plusIQuadrature` is right-circular in the receiver/optics observer convention.
  `PolarizationScatteringPhysical.lean:26-31` records this without adding a handedness alias.
- C-05 / decision L5: incident and transmitted angles are measured from the positive-side normal;
  the reflected angle is measured from the negative-side normal. The physical interface module
  cites the registered `AngularGeometry` declarations at lines 23-26.
- C-06: the full-vector Fresnel p sign is fork-declared. At normal incidence the registered
  convention has `r_p = -r_s` and `t_p = t_s`; the alternative literature convention is not
  forced to match. This is stated at `FresnelScatteringPhysical.lean:28-31`.
- Decision L6's typed reciprocity and tau-inverse-paired reference-plane law are not introduced
  here. They remain the separately assigned N2b network slice.

## Authorized files

- `Physlib/Optics/Components/PolarizationScatteringPhysical.lean` (249 lines);
- `Physlib/Optics/Interfaces/PlanarDielectric/FresnelScatteringPhysical.lean` (292 lines); and
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean` (831 lines).

No existing Components, Interface, Network, or Mode file changes. In particular, the registered
Phase 9a suite is byte-stable. Production imports no regression module.

## Jones polarization package

`JonesMatrix.Port` and `JonesMatrix.portFamily` at
`PolarizationScatteringPhysical.lean:69-84` give every Jones matrix one owned aperture carrying
the existing `Fin 2` coordinate fiber. `JonesMatrix.channelEquiv` at lines 86-97 pins both raw
coordinates to that aperture. The incident and outgoing endpoint equivalences are at lines
112-130.

`JonesMatrix.outputMap` and `JonesMatrix.behavior` at lines 136-166 transport the registered
`JonesMatrix.act` as the independent primitive behavior. `JonesMatrix.scattering` stores the
registered entries, and `JonesMatrix.scattering_realizes_behavior` proves exact graph realization
at lines 168-178. The owned behavior and scattering are transported separately at lines 180-217.
Algebraic losslessness under the existing `JonesMatrix.IsUnitary` hypothesis is at lines 219-223.
The direct singleton `ScatteringComponentFamily` witness is at lines 229-243.

The public declaration inventory is `JonesMatrix.Port`, `JonesMatrix.portFamily`,
`JonesMatrix.channelEquiv`, `JonesMatrix.channelFintype`,
`JonesMatrix.channelDecidableEq`, `JonesMatrix.channelEquiv_apply`,
`JonesMatrix.incidentChannelEquiv`, `JonesMatrix.outgoingChannelEquiv`,
`JonesMatrix.incidentChannelEquiv_apply`, `JonesMatrix.outgoingChannelEquiv_apply`,
`JonesMatrix.outputMap`, `JonesMatrix.outputMap_apply`, `JonesMatrix.behavior`,
`JonesMatrix.mem_behavior_iff`, `JonesMatrix.scattering`,
`JonesMatrix.scattering_realizes_behavior`, `JonesMatrix.physicalBehavior`,
`JonesMatrix.mem_physicalBehavior_iff`, `JonesMatrix.physicalScattering`,
`JonesMatrix.physicalScattering_toOrientedModeTransform`,
`JonesMatrix.physicalScattering_realizes_physicalBehavior`,
`JonesMatrix.physicalScattering_isLossless`, `JonesMatrix.componentFamily`,
`JonesMatrix.componentFamily_portFamily`, and `JonesMatrix.componentFamily_scattering`, plus the
finite `JonesMatrix.Port` instance.

## Polarized Fresnel interface package

`PlanarDielectricInterface.Port`, `PolarizationMode`, and `portFamily` at
`FresnelScatteringPhysical.lean:71-98` give the interface owned negative- and positive-side ports,
each with distinct s and p modes. `sideEquiv` and `channelEquiv` at lines 100-126 pin the raw order
as s negative/positive followed by p negative/positive. The four coordinate anchors are at lines
136-154, and the endpoint equivalences are at lines 156-164.

`PlanarDielectricInterface.polarizedScattering` at lines 170-174 is only the direct sum of the
already registered s and p Fresnel scattering kernels. The raw behavior, exact realization, owned
behavior, and owned scattering occupy lines 176-253. Algebraic losslessness under the existing
named positive propagating-normal hypotheses `0 < chi_i` and `0 < chi_t` is at lines 255-262. The
direct singleton `ScatteringComponentFamily` witness is at lines 268-286.

The public declaration inventory is `PlanarDielectricInterface.Port`,
`PlanarDielectricInterface.PolarizationMode`, `PlanarDielectricInterface.portFamily`,
`PlanarDielectricInterface.sideEquiv`, `PlanarDielectricInterface.channelEquiv`,
`PlanarDielectricInterface.channelFintype`,
`PlanarDielectricInterface.channelDecidableEq`, the four
`PlanarDielectricInterface.channelEquiv_apply_*` lemmas,
`PlanarDielectricInterface.incidentChannelEquiv`,
`PlanarDielectricInterface.outgoingChannelEquiv`,
`PlanarDielectricInterface.polarizedScattering`, `PlanarDielectricInterface.outputMap`,
`PlanarDielectricInterface.behavior`, `PlanarDielectricInterface.mem_behavior_iff`,
`PlanarDielectricInterface.polarizedScattering_realizes_behavior`,
`PlanarDielectricInterface.physicalBehavior`,
`PlanarDielectricInterface.mem_physicalBehavior_iff`,
`PlanarDielectricInterface.physicalScattering`,
`PlanarDielectricInterface.physicalScattering_toOrientedModeTransform`,
`PlanarDielectricInterface.physicalScattering_realizes_physicalBehavior`,
`PlanarDielectricInterface.physicalScattering_isLossless`,
`PlanarDielectricInterface.componentFamily`,
`PlanarDielectricInterface.componentFamily_portFamily`, and
`PlanarDielectricInterface.componentFamily_scattering`, plus finite instances for the owned port
and polarization-mode types.

## Fail-capable mixed-family regression

The interface fixture has negative-side wave admittance four and positive-side wave admittance
one (`PolarizationPortSuiteRegression.lean:64-96`). Direct expansion gives flux factor `1/4`,
s coefficients `r = 3/5`, `t = 8/5`, p coefficients `r = -3/5`, `t = 8/5`, and normalized
transmission `4/5` at lines 98-122.

The primitive quarter-wave-plate input `(5, 6)` gives `(5, -6I)` at lines 124-143. The interface
input has s block `(1, 2)` and p block `(3, 4)`; direct registered-kernel multiplication gives
s output `(11/5, -2/5)` and p output `(7/5, 24/5)` at lines 145-238. The signs therefore pin both
the positive-time quarter-wave-plate convention and the fork-declared p reflection convention.

The mixed dependent family is defined at lines 298-372. Its six named indexed channels and
complete finite-sum expansion are at lines 374-466. The primitive indexed matrix is written out
entry by entry at lines 468-509 and joined to the family matrix by finite cases at lines 519-544.
All six output coordinates are then expanded as finite sums at lines 567-612. Reindexing that raw
action gives the exact aggregate component-owned action at lines 614-635.

The hostile fixture swaps only the s/p output fiber at the negative-side interface port at lines
641-716. The positive indexed negative-side-s value is `11/5` at lines 718-735. The hostile
matrix is joined entrywise to the one-block output-row reindex at lines 764-784 and produces
`7/5` on that same channel at lines 786-815. The concrete inequality `7/5 ≠ 11/5` is proved at
lines 817-827. Thus the negative case changes the same nonzero mixed-family output and can fail on
a side, mode-fiber, component-index, or aggregate-channel reindex error.

The regression declaration inventory comprises:

- fixture data and raw anchors: `physicalPortSuite9bNegativeMedium`,
  `physicalPortSuite9bPositiveMedium`, `physicalPortSuite9b_negative_waveImpedance_inv`,
  `physicalPortSuite9b_positive_waveImpedance_inv`, `physicalPortSuite9bInterface`,
  `physicalPortSuite9b_fresnel_values`, `physicalPortSuite9b_normalized_transmission`,
  `physicalPortSuite9bPolarizationRawInput`, `physicalPortSuite9bPolarizationRawOutput`,
  `physicalPortSuite9b_polarization_raw_action`, `physicalPortSuite9bInterfaceRawInput`,
  `physicalPortSuite9bInterfaceRawOutput`, the four
  `physicalPortSuite9b_channelEquiv_symm_*` lemmas, `physicalPortSuite9b_s_kernel`,
  `physicalPortSuite9b_p_kernel`, and `physicalPortSuite9b_interface_raw_action`;
- owned local actions: `physicalPortSuite9bPolarizationLocalInput`,
  `physicalPortSuite9bPolarizationLocalOutput`, `physicalPortSuite9b_polarization_local_action`,
  `physicalPortSuite9bInterfaceLocalInput`, `physicalPortSuite9bInterfaceLocalOutput`, and
  `physicalPortSuite9b_interface_local_action`;
- mixed-family construction: `PhysicalPortSuite9bComponent`,
  `physicalPortSuite9bPortFamily`, `physicalPortSuite9bScattering`,
  `physicalPortSuite9bFamily`, `PhysicalPortSuite9bIndexedChannel`,
  `physicalPortSuite9bIndexedInput`, `physicalPortSuite9bIndexedOutput`, the six named
  `physicalPortSuite9b*Indexed` channels, `physicalPortSuite9b_sum_indexed`,
  `physicalPortSuite9bExplicitIndexedTransform`,
  `physicalPortSuite9b_quarterWavePlate_entries`,
  `physicalPortSuite9b_indexedScatteringMatrix_eq_explicit`, the two
  `physicalPortSuite9bIndexedInput_restrict_*` lemmas, `physicalPortSuite9b_indexed_action`,
  `physicalPortSuite9bAggregateInput`, `physicalPortSuite9bAggregateOutput`, and
  `physicalPortSuite9b_aggregate_action`; and
- hostile construction: `physicalPortSuite9bInterfaceNegativePolarizationSwap`,
  `physicalPortSuite9bHostileInterfaceScattering`,
  `physicalPortSuite9bHostileInterfaceLocalOutput`,
  `physicalPortSuite9b_hostile_interface_local_action`,
  `physicalPortSuite9bHostileScattering`, `physicalPortSuite9bHostileFamily`,
  `physicalPortSuite9b_indexed_negative_s_value`,
  `physicalPortSuite9bIndexedNegativePolarizationSwap`,
  `physicalPortSuite9b_hostile_indexedScatteringMatrix_eq_reindex`,
  `physicalPortSuite9b_hostile_indexed_negative_s_value`, and
  `physicalPortSuite9b_hostile_action_ne`.

The file additionally provides the finite component instance and five local finite/decidable
instances used only to enumerate the dependent six-channel fixture.

### Anchor-independence map

- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:133`
  `physicalPortSuite9b_polarization_raw_action` unfolds the registered quarter-wave-plate matrix.
  It is independent of every declaration in `PolarizationScatteringPhysical.lean`, both physical
  realization lemmas, and all component-family action lemmas.
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:99`, `:116`, `:191`, `:208`,
  and `:225` expand the medium data, normalization, registered s/p kernels, and four-coordinate
  raw action. They are independent of `FresnelScatteringPhysical.lean`, its realization and
  component-family lemmas, and every assembled-family action lemma.
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:520`
  `physicalPortSuite9b_indexedScatteringMatrix_eq_explicit` unfolds the two adapters into the
  independently displayed six-channel primitive matrix by finite cases. It uses no realization,
  losslessness, component-family projection, or assembled-entry lemma.
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:568`
  `physicalPortSuite9b_indexed_action` expands `Matrix.mulVec` using the explicit six-term sum. It
  is independent of every packaged assembled-action lemma and both realization lemmas.
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:627`
  `physicalPortSuite9b_aggregate_action` uses the raw indexed action and the definition of the
  aggregate reindex. It does not use an assembled-action convenience lemma.
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:765`, `:787`, and `:818` join
  the hostile family to the concrete one-fiber row swap and prove `7/5 ≠ 11/5` on the same input.
  They do not substitute an unrelated manually chosen output.

A declaration-name grep over the regression is empty for both
`physicalScattering_realizes_physicalBehavior` lemmas, both
`physicalScattering_toOrientedModeTransform` lemmas, both `componentFamily_*` projection pairs,
both raw scattering-realization lemmas, both losslessness lemmas,
`assembledScatteringMatrix_apply_component`, and `assembledScatteringMatrix_entry`.

## Non-claims

- The matrices describe fixed-carrier algebraic modal amplitudes. Their losslessness statements
  are squared-amplitude bookkeeping, not electromagnetic energy or power theorems.
- No reciprocity, time reversal, tau pairing, reverse-incidence Maxwell, reference-plane,
  modal-completeness, handedness transport, or observer-change claim is made.
- The Fresnel package is the registered algebraic orthogonal completion, not an E6 physical
  bidirectional-interface derivation. No reverse-incidence material boundary problem is solved.
- No geometry synthesis, coating, propagation, physical time/group delay, bandwidth, stability,
  causality, dispersion, measurement, modal normalization, or fabrication claim is made.
- Exact “realization” means equality of the transported algebraic behavior and scattering graph;
  it does not certify a physical realization.
- The regression coefficients are fail-capable algebraic sentinels, not measured component data.
  Human verification remains required by `AI-POLICY.md`.

## Reviewer map

1. Read `PolarizationScatteringPhysical.lean:69-130` for the owned aperture and pinned Jones order.
2. Read lines 136-223 for registered action, independent behavior, realization, and bookkeeping.
3. Read `FresnelScatteringPhysical.lean:71-164` for owned sides, s/p fibers, and pinned order.
4. Read lines 170-286 for registered-kernel composition, realization, and direct family witness.
5. Read `PolarizationPortSuiteRegression.lean:64-238` for all primitive convention-sensitive
   matrix values.
6. Read lines 298-635 for the explicit six-channel mixed-family action.
7. Read lines 641-827 for the connected hostile one-side s/p swap and concrete inequality.

## Exact validation record

The exact gated source `e81a48b71ef9be208ea461fecf65549277053039` was checked under
`lake-lock`. Temporary sorted registration of all three modules was used for aggregate and
declaration linters, then removed.

- targeted build of `Physlib.Optics.Components.PolarizationPortSuiteRegression`: passed, 3604
  jobs, with no warnings;
- warning-fatal aggregate build of `Physlib`: passed, 5014 jobs;
- `check_file_imports`: all files imported correctly and the temporary list sorted;
- `sorry_lint`: passed;
- `runPhyslibLinters`: Physlib and QuantumInfo passed, including `simpNF`;
- `api_map_index`: passed;
- `lint_all`: completed all seven stages, including build, imports, sorry attribution, Lean
  linters, and transitive-import scanning; its repository-wide style/transitive notices name only
  untouched files;
- committed-state `lint-style.sh`: passed;
- the exact `module_doc_lint.checkHeadings` implementation passed each of the three Phase 9b
  modules. The unfiltered repository-wide `module_doc_lint` command still exits on the existing
  documentation backlog in unrelated modules; none of these three files appears in its errors;
- `git diff --check`: passed;
- file lengths are 249, 292, and 831, all below 1500 lines;
- maximum line lengths are 98, 99, and 96 Unicode codepoints;
- no file contains `theorem`, `sorry`, `axiom`, `native_decide`, `maxHeartbeats`, or
  `Lean.ofReduceBool`;
- all module docs use the four literal required headings and exact matching TOCs;
- production imports no regression module;
- relative to `9c1f4929`, the source diff contains exactly the three authorized new files; and
- `PhysicalPortSuiteRegression.lean` is byte-identical to `9c1f4929`.

Temporary registration was restored byte-identically. `Physlib.lean` had SHA-256
`f7486c686c1d5087c1cb8a87f33b3af2dd11cb761b14fa0ebbc0a0e9489d0a20` before and after the
gate. This final cutoff child changes only `HANDOFF.md`.
