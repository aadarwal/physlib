# S7C Phase 9b QQ-2: polarization and interface physical ports

## Cutoff and synchronization

The controller-authorized registered base is
`9c1f4929d20a17fcc7ada2c37c1e5f2f82b3df38`. The exact synchronization merge is
`9b94c76ccb9ddb537c11745df0786bf9f9479d43`. The gated source is
`b5409983a036a3097df18b0a316f4c6c5b1f2bc2`. This cutoff is its HANDOFF-only child.

Relative to the base, the source adds exactly the three authorized Phase 9b files.
The registered Phase 9a regression is byte-identical to the base. `Physlib.lean` is also
byte-identical to the base.

## Goal and supplied scope

The controlling text at `goal.md:2184-2186` on the gated source is:

> component-owned physical-port packaging consumed by `ScatteringComponentFamily`: the
> beam-splitter and mirror packages are complete, while polarization and interface primitives
> remain;

Phase 9b supplies the remaining Jones-polarization and polarized Fresnel-interface packages.
Together with accepted Phase 9a, this implements the four named packages. Updating the ledger
checkbox remains controller-owned. The frequency-dependent propagation item at
`goal.md:2187-2188` and the separately assigned reciprocity-metadata slice remain open.

All adapters and regression facts are Physlib-original packaging. Every result is a `lemma`;
the phase claims no literal printed physics theorem.

## QQ semantic repair

The Jones package was already independent and is unchanged by this repair. Its behavior
transports the registered `JonesMatrix.act`; its scattering is separately constructed from matrix
entries; the realization proof connects the two.

The Fresnel package now follows the same pattern. `sideOutputMap` states the two side-coordinate
laws directly from reflection and normalized-transmission coefficients. `endpointOutput` states
all four s/p endpoint equations directly from the registered s/p coefficient primitives.
`outputMap` and `behavior` are built only from those endpoint equations and do not call
`polarizedScattering`, a scattering action, or a scattering graph. Only afterward is
`polarizedScattering` constructed as the direct sum of the registered kernels. The finite
coordinate lemma `polarizedScattering_toLinearMap_apply` expands that direct sum to the four
endpoint equations, and `polarizedScattering_realizes_behavior` uses this substantive equality.

The primitive regression anchors and connected hostile s/p swap were not changed by this repair.

## Binding convention record

- Decision L1 / C-02: `Phasor.realize` uses positive time. Registered
  `JonesVector.plusIQuadrature` is right-circular in the receiver/optics observer convention.
- Decision L5 / C-05: incident and transmitted angles use the positive-side normal; reflected
  angles use the negative-side normal. The interface package cites registered angular geometry.
- C-06: the full-vector Fresnel p sign is fork-declared. At normal incidence the registered
  convention gives `r_p = -r_s` and `t_p = t_s`; no literature convention is forced to match.
- Decision L6's typed reciprocity and tau-inverse-paired rephasing law are not introduced here.
  They remain the separately assigned reciprocity-metadata slice.

## Authorized files and registration order

Registration order:

1. `Physlib/Optics/Components/PolarizationScatteringPhysical.lean` — 249 lines.
2. `Physlib/Optics/Interfaces/PlanarDielectric/FresnelScatteringPhysical.lean` — 394 lines.
3. `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean` — 832 lines.

There are no edits to existing Components, Interface, Network, or Mode modules. In particular,
`Physlib/Optics/Components/PhysicalPortSuiteRegression.lean` is byte-stable. Production imports
no regression module.

## Exact declaration inventory: Jones package

Each entry gives the committed source location followed by the exact declaration name.

- `Physlib/Optics/Components/PolarizationScatteringPhysical.lean:70`
  `Optics.JonesMatrix.Port`
- `Physlib/Optics/Components/PolarizationScatteringPhysical.lean:75`
  anonymous `Fintype Optics.JonesMatrix.Port` instance
- `Physlib/Optics/Components/PolarizationScatteringPhysical.lean:82`
  `Optics.JonesMatrix.portFamily`
- `Physlib/Optics/Components/PolarizationScatteringPhysical.lean:87`
  `Optics.JonesMatrix.channelEquiv`
- `Physlib/Optics/Components/PolarizationScatteringPhysical.lean:100`
  `Optics.JonesMatrix.channelFintype`
- `Physlib/Optics/Components/PolarizationScatteringPhysical.lean:104`
  `Optics.JonesMatrix.channelDecidableEq`
- `Physlib/Optics/Components/PolarizationScatteringPhysical.lean:109`
  `Optics.JonesMatrix.channelEquiv_apply`
- `Physlib/Optics/Components/PolarizationScatteringPhysical.lean:113`
  `Optics.JonesMatrix.incidentChannelEquiv`
- `Physlib/Optics/Components/PolarizationScatteringPhysical.lean:117`
  `Optics.JonesMatrix.outgoingChannelEquiv`
- `Physlib/Optics/Components/PolarizationScatteringPhysical.lean:122`
  `Optics.JonesMatrix.incidentChannelEquiv_apply`
- `Physlib/Optics/Components/PolarizationScatteringPhysical.lean:128`
  `Optics.JonesMatrix.outgoingChannelEquiv_apply`
- `Physlib/Optics/Components/PolarizationScatteringPhysical.lean:137`
  `Optics.JonesMatrix.outputMap`
- `Physlib/Optics/Components/PolarizationScatteringPhysical.lean:146`
  `Optics.JonesMatrix.outputMap_apply`
- `Physlib/Optics/Components/PolarizationScatteringPhysical.lean:154`
  `Optics.JonesMatrix.behavior`
- `Physlib/Optics/Components/PolarizationScatteringPhysical.lean:160`
  `Optics.JonesMatrix.mem_behavior_iff`
- `Physlib/Optics/Components/PolarizationScatteringPhysical.lean:169`
  `Optics.JonesMatrix.scattering`
- `Physlib/Optics/Components/PolarizationScatteringPhysical.lean:173`
  `Optics.JonesMatrix.scattering_realizes_behavior`
- `Physlib/Optics/Components/PolarizationScatteringPhysical.lean:181`
  `Optics.JonesMatrix.physicalBehavior`
- `Physlib/Optics/Components/PolarizationScatteringPhysical.lean:187`
  `Optics.JonesMatrix.mem_physicalBehavior_iff`
- `Physlib/Optics/Components/PolarizationScatteringPhysical.lean:196`
  `Optics.JonesMatrix.physicalScattering`
- `Physlib/Optics/Components/PolarizationScatteringPhysical.lean:200`
  `Optics.JonesMatrix.physicalScattering_toOrientedModeTransform`
- `Physlib/Optics/Components/PolarizationScatteringPhysical.lean:212`
  `Optics.JonesMatrix.physicalScattering_realizes_physicalBehavior`
- `Physlib/Optics/Components/PolarizationScatteringPhysical.lean:220`
  `Optics.JonesMatrix.physicalScattering_isLossless`
- `Physlib/Optics/Components/PolarizationScatteringPhysical.lean:230`
  `Optics.JonesMatrix.componentFamily`
- `Physlib/Optics/Components/PolarizationScatteringPhysical.lean:237`
  `Optics.JonesMatrix.componentFamily_portFamily`
- `Physlib/Optics/Components/PolarizationScatteringPhysical.lean:242`
  `Optics.JonesMatrix.componentFamily_scattering`

## Exact declaration inventory: Fresnel package

- `Physlib/Optics/Interfaces/PlanarDielectric/FresnelScatteringPhysical.lean:74`
  `Optics.PlanarDielectricInterface.Port`
- `Physlib/Optics/Interfaces/PlanarDielectric/FresnelScatteringPhysical.lean:80`
  anonymous `Fintype Optics.PlanarDielectricInterface.Port` instance
- `Physlib/Optics/Interfaces/PlanarDielectric/FresnelScatteringPhysical.lean:86`
  `Optics.PlanarDielectricInterface.PolarizationMode`
- `Physlib/Optics/Interfaces/PlanarDielectric/FresnelScatteringPhysical.lean:92`
  anonymous `Fintype Optics.PlanarDielectricInterface.PolarizationMode` instance
- `Physlib/Optics/Interfaces/PlanarDielectric/FresnelScatteringPhysical.lean:98`
  `Optics.PlanarDielectricInterface.portFamily`
- `Physlib/Optics/Interfaces/PlanarDielectric/FresnelScatteringPhysical.lean:103`
  `Optics.PlanarDielectricInterface.sideEquiv`
- `Physlib/Optics/Interfaces/PlanarDielectric/FresnelScatteringPhysical.lean:116`
  `Optics.PlanarDielectricInterface.channelEquiv`
- `Physlib/Optics/Interfaces/PlanarDielectric/FresnelScatteringPhysical.lean:131`
  `Optics.PlanarDielectricInterface.channelFintype`
- `Physlib/Optics/Interfaces/PlanarDielectric/FresnelScatteringPhysical.lean:135`
  `Optics.PlanarDielectricInterface.channelDecidableEq`
- `Physlib/Optics/Interfaces/PlanarDielectric/FresnelScatteringPhysical.lean:140`
  `Optics.PlanarDielectricInterface.channelEquiv_apply_s_negative`
- `Physlib/Optics/Interfaces/PlanarDielectric/FresnelScatteringPhysical.lean:145`
  `Optics.PlanarDielectricInterface.channelEquiv_apply_s_positive`
- `Physlib/Optics/Interfaces/PlanarDielectric/FresnelScatteringPhysical.lean:150`
  `Optics.PlanarDielectricInterface.channelEquiv_apply_p_negative`
- `Physlib/Optics/Interfaces/PlanarDielectric/FresnelScatteringPhysical.lean:155`
  `Optics.PlanarDielectricInterface.channelEquiv_apply_p_positive`
- `Physlib/Optics/Interfaces/PlanarDielectric/FresnelScatteringPhysical.lean:159`
  `Optics.PlanarDielectricInterface.incidentChannelEquiv`
- `Physlib/Optics/Interfaces/PlanarDielectric/FresnelScatteringPhysical.lean:164`
  `Optics.PlanarDielectricInterface.outgoingChannelEquiv`
- `Physlib/Optics/Interfaces/PlanarDielectric/FresnelScatteringPhysical.lean:177`
  `Optics.PlanarDielectricInterface.sideOutputMap`
- `Physlib/Optics/Interfaces/PlanarDielectric/FresnelScatteringPhysical.lean:184`
  `Optics.PlanarDielectricInterface.sideOutputMap_apply`
- `Physlib/Optics/Interfaces/PlanarDielectric/FresnelScatteringPhysical.lean:202`
  `Optics.PlanarDielectricInterface.endpointOutput`
- `Physlib/Optics/Interfaces/PlanarDielectric/FresnelScatteringPhysical.lean:224`
  `Optics.PlanarDielectricInterface.outputMap`
- `Physlib/Optics/Interfaces/PlanarDielectric/FresnelScatteringPhysical.lean:253`
  `Optics.PlanarDielectricInterface.outputMap_apply`
- `Physlib/Optics/Interfaces/PlanarDielectric/FresnelScatteringPhysical.lean:271`
  `Optics.PlanarDielectricInterface.behavior`
- `Physlib/Optics/Interfaces/PlanarDielectric/FresnelScatteringPhysical.lean:277`
  `Optics.PlanarDielectricInterface.mem_behavior_iff`
- `Physlib/Optics/Interfaces/PlanarDielectric/FresnelScatteringPhysical.lean:287`
  `Optics.PlanarDielectricInterface.polarizedScattering`
- `Physlib/Optics/Interfaces/PlanarDielectric/FresnelScatteringPhysical.lean:293`
  `Optics.PlanarDielectricInterface.polarizedScattering_toLinearMap_apply`
- `Physlib/Optics/Interfaces/PlanarDielectric/FresnelScatteringPhysical.lean:306`
  `Optics.PlanarDielectricInterface.polarizedScattering_realizes_behavior`
- `Physlib/Optics/Interfaces/PlanarDielectric/FresnelScatteringPhysical.lean:316`
  `Optics.PlanarDielectricInterface.physicalBehavior`
- `Physlib/Optics/Interfaces/PlanarDielectric/FresnelScatteringPhysical.lean:322`
  `Optics.PlanarDielectricInterface.mem_physicalBehavior_iff`
- `Physlib/Optics/Interfaces/PlanarDielectric/FresnelScatteringPhysical.lean:332`
  `Optics.PlanarDielectricInterface.physicalScattering`
- `Physlib/Optics/Interfaces/PlanarDielectric/FresnelScatteringPhysical.lean:337`
  `Optics.PlanarDielectricInterface.physicalScattering_toOrientedModeTransform`
- `Physlib/Optics/Interfaces/PlanarDielectric/FresnelScatteringPhysical.lean:349`
  `Optics.PlanarDielectricInterface.physicalScattering_realizes_physicalBehavior`
- `Physlib/Optics/Interfaces/PlanarDielectric/FresnelScatteringPhysical.lean:358`
  `Optics.PlanarDielectricInterface.physicalScattering_isLossless`
- `Physlib/Optics/Interfaces/PlanarDielectric/FresnelScatteringPhysical.lean:371`
  `Optics.PlanarDielectricInterface.componentFamily`
- `Physlib/Optics/Interfaces/PlanarDielectric/FresnelScatteringPhysical.lean:379`
  `Optics.PlanarDielectricInterface.componentFamily_portFamily`
- `Physlib/Optics/Interfaces/PlanarDielectric/FresnelScatteringPhysical.lean:385`
  `Optics.PlanarDielectricInterface.componentFamily_scattering`

## Exact declaration inventory: mixed regression

- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:66`
  `Optics.physicalPortSuite9bNegativeMedium`
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:73`
  `Optics.physicalPortSuite9bPositiveMedium`
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:80`
  `Optics.physicalPortSuite9b_negative_waveImpedance_inv`
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:88`
  `Optics.physicalPortSuite9b_positive_waveImpedance_inv`
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:94`
  `Optics.physicalPortSuite9bInterface`
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:100`
  `Optics.physicalPortSuite9b_fresnel_values`
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:117`
  `Optics.physicalPortSuite9b_normalized_transmission`
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:126`
  `Optics.physicalPortSuite9bPolarizationRawInput`
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:130`
  `Optics.physicalPortSuite9bPolarizationRawOutput`
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:134`
  `Optics.physicalPortSuite9b_polarization_raw_action`
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:147`
  `Optics.physicalPortSuite9bInterfaceRawInput`
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:151`
  `Optics.physicalPortSuite9bInterfaceRawOutput`
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:157`
  `Optics.physicalPortSuite9b_channelEquiv_symm_negative_s`
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:166`
  `Optics.physicalPortSuite9b_channelEquiv_symm_positive_s`
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:175`
  `Optics.physicalPortSuite9b_channelEquiv_symm_negative_p`
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:184`
  `Optics.physicalPortSuite9b_channelEquiv_symm_positive_p`
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:192`
  `Optics.physicalPortSuite9b_s_kernel`
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:209`
  `Optics.physicalPortSuite9b_p_kernel`
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:226`
  `Optics.physicalPortSuite9b_interface_raw_action`
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:246`
  `Optics.physicalPortSuite9bPolarizationLocalInput`
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:252`
  `Optics.physicalPortSuite9bPolarizationLocalOutput`
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:258`
  `Optics.physicalPortSuite9b_polarization_local_action`
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:273`
  `Optics.physicalPortSuite9bInterfaceLocalInput`
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:279`
  `Optics.physicalPortSuite9bInterfaceLocalOutput`
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:285`
  `Optics.physicalPortSuite9b_interface_local_action`
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:300`
  `Optics.PhysicalPortSuite9bComponent`
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:306`
  anonymous `Fintype Optics.PhysicalPortSuite9bComponent` instance
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:313`
  `Optics.physicalPortSuite9bPortFamily`
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:322`
  `Optics.physicalPortSuite9bScattering`
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:329`
  `Optics.physicalPortSuite9bFamily`
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:335`
  `Optics.PhysicalPortSuite9bIndexedChannel`
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:340`
  local instance `Optics.physicalPortSuite9bLocalChannelFintype`
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:350`
  local instance `Optics.physicalPortSuite9bLocalChannelDecidableEq`
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:360`
  local instance `Optics.physicalPortSuite9bIndexedChannelDecidableEq`
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:365`
  local instance `Optics.physicalPortSuite9bAggregateChannelFintype`
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:371`
  local instance `Optics.physicalPortSuite9bAggregateChannelDecidableEq`
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:376`
  `Optics.physicalPortSuite9bIndexedInput`
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:386`
  `Optics.physicalPortSuite9bIndexedOutput`
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:396`
  `Optics.physicalPortSuite9bPolarizationZeroIndexed`
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:402`
  `Optics.physicalPortSuite9bPolarizationOneIndexed`
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:408`
  `Optics.physicalPortSuite9bInterfaceNegativeSIndexed`
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:415`
  `Optics.physicalPortSuite9bInterfacePositiveSIndexed`
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:422`
  `Optics.physicalPortSuite9bInterfaceNegativePIndexed`
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:429`
  `Optics.physicalPortSuite9bInterfacePositivePIndexed`
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:436`
  `Optics.physicalPortSuite9b_sum_indexed`
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:470`
  `Optics.physicalPortSuite9bExplicitIndexedTransform`
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:513`
  `Optics.physicalPortSuite9b_quarterWavePlate_entries`
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:521`
  `Optics.physicalPortSuite9b_indexedScatteringMatrix_eq_explicit`
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:548`
  `Optics.physicalPortSuite9bIndexedInput_restrict_polarization`
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:559`
  `Optics.physicalPortSuite9bIndexedInput_restrict_interface`
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:569`
  `Optics.physicalPortSuite9b_indexed_action`
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:616`
  `Optics.physicalPortSuite9bAggregateInput`
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:622`
  `Optics.physicalPortSuite9bAggregateOutput`
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:628`
  `Optics.physicalPortSuite9b_aggregate_action`
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:643`
  `Optics.physicalPortSuite9bInterfaceNegativePolarizationSwap`
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:676`
  `Optics.physicalPortSuite9bHostileInterfaceScattering`
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:684`
  `Optics.physicalPortSuite9bHostileInterfaceLocalOutput`
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:690`
  `Optics.physicalPortSuite9b_hostile_interface_local_action`
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:707`
  `Optics.physicalPortSuite9bHostileScattering`
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:714`
  `Optics.physicalPortSuite9bHostileFamily`
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:720`
  `Optics.physicalPortSuite9b_indexed_negative_s_value`
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:739`
  `Optics.physicalPortSuite9bIndexedNegativePolarizationSwap`
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:766`
  `Optics.physicalPortSuite9b_hostile_indexedScatteringMatrix_eq_reindex`
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:788`
  `Optics.physicalPortSuite9b_hostile_indexed_negative_s_value`
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:819`
  `Optics.physicalPortSuite9b_hostile_action_ne`

## Anchor independence and exact values

- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:134`
  `Optics.physicalPortSuite9b_polarization_raw_action` expands the registered quarter-wave-plate
  matrix from primitives: `(5, 6) -> (5, -6I)`. It uses no physical-port packaging or realization
  lemma.
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:100`
  `Optics.physicalPortSuite9b_fresnel_values` proves `1/4`, `3/5`, `-3/5`, and `8/5` directly
  from the fixture media and registered coefficient formulas.
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:117`
  `Optics.physicalPortSuite9b_normalized_transmission` proves the normalized value `4/5` from
  primitives.
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:226`
  `Optics.physicalPortSuite9b_interface_raw_action` expands the registered s/p kernels:
  `((1,2),(3,4)) -> ((11/5,-2/5),(7/5,24/5))`.
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:569`
  `Optics.physicalPortSuite9b_indexed_action` expands all six indexed matrix coordinates from the
  independently displayed transform.
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:628`
  `Optics.physicalPortSuite9b_aggregate_action` reindexes the independent indexed expansion into
  the aggregate component-owned channel family.
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:788`
  `Optics.physicalPortSuite9b_hostile_indexed_negative_s_value` proves that the connected hostile
  output-fiber swap changes the negative-side s value to `7/5`.
- `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:819`
  `Optics.physicalPortSuite9b_hostile_action_ne` proves `7/5 != 11/5` on the same nonzero input.

The first four anchors unfold registered primitive matrices and coefficients. They do not use
the package realization, losslessness, family projection, or assembled-action lemmas. The indexed
and aggregate anchors use the independently displayed six-channel matrix, not a packaged action
shortcut. The hostile anchor is a reindex of the actual interface scattering block, not an
unrelated manually chosen output.

The regression contains no use of either
`physicalScattering_realizes_physicalBehavior` declaration, either
`physicalScattering_toOrientedModeTransform` declaration, either raw realization declaration,
either losslessness declaration, any `componentFamily_*` projection, or the assembled entry and
component-action convenience lemmas.

## QQ realization validation names

- `Physlib/Optics/Interfaces/PlanarDielectric/FresnelScatteringPhysical.lean:184`
  `Optics.PlanarDielectricInterface.sideOutputMap_apply` expands each two-side endpoint law.
- `Physlib/Optics/Interfaces/PlanarDielectric/FresnelScatteringPhysical.lean:253`
  `Optics.PlanarDielectricInterface.outputMap_apply` displays all four independent s/p equations.
- `Physlib/Optics/Interfaces/PlanarDielectric/FresnelScatteringPhysical.lean:277`
  `Optics.PlanarDielectricInterface.mem_behavior_iff` characterizes the endpoint-equation graph.
- `Physlib/Optics/Interfaces/PlanarDielectric/FresnelScatteringPhysical.lean:293`
  `Optics.PlanarDielectricInterface.polarizedScattering_toLinearMap_apply` expands the separately
  constructed direct-sum scattering to the endpoint-equation output.
- `Physlib/Optics/Interfaces/PlanarDielectric/FresnelScatteringPhysical.lean:306`
  `Optics.PlanarDielectricInterface.polarizedScattering_realizes_behavior` proves exact
  realization from that substantive expansion.

## Per-module claim boundary

All three module docs state the following boundary locally rather than delegating it here:

- no reciprocity or time-reversal claim;
- no tau pairing or reference-plane claim;
- no reverse-incidence Maxwell law or modal-completeness claim;
- no propagation, causality, dispersion, or measurement claim;
- losslessness is squared-amplitude/modal bookkeeping, not an electromagnetic-power theorem; and
- exact algebraic graph realization is not a physical-realization certification.

The Fresnel package is the registered algebraic orthogonal completion. It does not solve a
reverse-incidence material-boundary problem. It makes no geometry synthesis, coating, bandwidth,
stability, fabrication, modal normalization, or measured-device claim. Human verification remains
required by `AI-POLICY.md`.

## Reviewer map

1. Read `Physlib/Optics/Components/PolarizationScatteringPhysical.lean:70` for owned Jones ports,
   then lines 137-220 for independent action, scattering realization, and modal bookkeeping.
2. Read `Physlib/Optics/Interfaces/PlanarDielectric/FresnelScatteringPhysical.lean:74` for owned
   side/polarization channels.
3. Read that Fresnel file at lines 177-280 for independent endpoint equations and behavior.
4. Read that Fresnel file at lines 287-362 for direct-sum expansion, realization, and bookkeeping.
5. Read `Physlib/Optics/Components/PolarizationPortSuiteRegression.lean:66` through line 226 for
   all convention-sensitive primitive values.
6. Read that regression at lines 300-628 for the six-channel mixed-family action.
7. Read that regression at lines 643-823 for the connected hostile one-fiber swap.

## Exact validation record

The root-first cutoff chain for exact gated source
`b5409983a036a3097df18b0a316f4c6c5b1f2bc2` ran under one `lake-lock` hold. Temporary sorted
registration of the three modules was used for aggregate checks and then removed. The later
file-scoped module-doc check also ran under `lake-lock`.

- Targeted regression build: passed 3604 jobs with no warnings.
- Warning-fatal aggregate `Physlib` build: passed 5014 jobs.
- `check_file_imports`: passed with the temporary list sorted.
- `sorry_lint`: passed.
- `runPhyslibLinters`: Physlib and QuantumInfo passed, including `simpNF`.
- `api_map_index`: passed.
- `lint_all`: completed all seven stages. Repository-wide style/transitive notices identify only
  untouched files.
- Committed-state `lint-style.sh`: passed.
- File-scoped `module_doc_lint.checkHeadings`: passed for all three Phase 9b modules.
- `git diff --check`: passed.
- File lengths are 249, 394, and 832; all are below 1500 lines.
- Maximum line lengths are 98, 99, and 96 Unicode codepoints.
- No new file contains `theorem`, `sorry`, `axiom`, `native_decide`, `maxHeartbeats`, or
  `Lean.ofReduceBool`.
- All module docs have the four literal headings and matching tables of contents.
- Production imports no regression module.
- Relative to the base, the source diff contains exactly the three authorized new files.
- `PhysicalPortSuiteRegression.lean` is byte-identical to the base.

Temporary registration was restored byte-identically. `Physlib.lean` had SHA-256
`f7486c686c1d5087c1cb8a87f33b3af2dd11cb761b14fa0ebbc0a0e9489d0a20` before and after the
gate. This final cutoff child changes only `HANDOFF.md`.
