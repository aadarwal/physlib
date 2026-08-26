# S0 physical microring realization handoff

## Branch and cutoff state

- Branch: `optics/s0-physical-ring`.
- Worktree: `/Users/aadarwal/src/aadarwal/physlib-wt/optics-s0-physical-ring`.
- Development head merged at cutoff: `9f23e522`.
- Post-sync merge commit: `32514e95`.
- Crash-safe implementation commits: `5cac7028` and `96367bf0`.
- Slice 1b crash-safe commits begin at `c0014de3`.
- The four recovered files were substantive but ungated drafts. They are now complete for the
  stated S0 contract and pass the post-sync build and declaration-linter gates.
- No existing production module, registry, API map, `goal.md`, or `tbd.md` is changed by the lane
  diff. Integration-file changes in the merge commit came from `optics/development`.

## Files and requested registrations

New production modules:

- `Physlib/Optics/Systems/Microring/PhysicalParameters.lean`
- `Physlib/Optics/Systems/Microring/PhysicalRealization.lean`
- `Physlib/Optics/Systems/Microring/PhysicalSourceBridge.lean`

New regression module:

- `Physlib/Optics/Systems/Microring/PhysicalRegression.lean`

Add these sorted public imports to `Physlib.lean`:

```lean
public import Physlib.Optics.Systems.Microring.PhysicalParameters
public import Physlib.Optics.Systems.Microring.PhysicalRealization
public import Physlib.Optics.Systems.Microring.PhysicalRegression
public import Physlib.Optics.Systems.Microring.PhysicalSourceBridge
```

`PhysicalSourceBridge` imports the merged `SourceBridge` umbrella and reuses
`Optics.MicroringSourceBridge.DateParameters`, `SysConParameters`, and `SfgParameters`. It does
not define a replacement source dictionary.

## Goal text implemented

The slice implements each literal S0 milestone bullet:

> ring parameters for through/cross amplitude coefficients, optical path length, field
> attenuation, effective index or propagation constant, and wavelength/frequency;

> validity predicates distinguishing field from power attenuation and amplitude from power
> coupling coefficients;

> one-bus/all-pass and two-bus/add-drop typed port topologies;

> an independent relation between internal and external travelling fields;

> realization from N7 couplers and propagation delays; and

> proofs that each realization satisfies its field relation and induces the source-level
> transfer/chain matrices under their actual nondegeneracy hypotheses.

The exit condition is met by proof direction: the independent relations contain only local
coupler and propagation equations; the netlist behavior is proved to satisfy them; transfer and
chain formulas are then consequences under named gates. No formula record is used as a physical
realization certificate.

The exact named regression row is:

> S-04: **met:** the physical add-drop realization yields both exact transfer responses

### Slice 1b formal role design

Slice 1b chooses distinct role-indexed wrappers. `FieldAttenuation` and `PowerAttenuation` are
different Lean types, as are amplitude-role `CouplingParameters` and
`PowerCouplingParameters`. Their unit-interval or normalization conditions remain typed
predicates rather than proof fields so the singular-safe algebraic parameter layer stays total.
A power-role value therefore cannot be passed to a field predicate or physical field map without
an explicit, visible reconstruction. `PhysicalParameters.fieldAttenuation` and
`.powerAttenuation` return the distinct wrappers, the typed conversion proves their square
relation, and both S2 parameter maps project only the field wrapper's value.

## N7 and network declarations used

The physical maps and certificates build on these registered N7 declarations. Line references
were re-grepped after the final development sync:

- `Optics.DirectionalCoupler.Parameters`, `.crossCoefficient`, and `.mixing`:
  `Physlib/Optics/Components/DirectionalCoupler.lean:62`, `:69`, and `:73`.
- `Optics.DirectionalCoupler.physicalScattering` and
  `.physicalScattering_realizes_physicalBehavior`:
  `Physlib/Optics/Components/DirectionalCouplerPhysical.lean:161` and `:176`.
- `Optics.MatchedPropagation.Parameters`, `.Parameters.IsValid`, and
  `.transmissionCoefficient`:
  `Physlib/Optics/Components/MatchedPropagation.lean:79`, `:90`, and `:102`.
- `Optics.MatchedPropagation.physicalScattering` and
  `.physicalScattering_realizes_physicalBehavior`:
  `Physlib/Optics/Components/MatchedPropagationPhysical.lean:167` and `:182`.

The realized S2 topologies are `Optics.AllPass.netlist` at
`Physlib/Optics/Systems/Microring/AllPass.lean:297` and `Optics.AddDrop.netlist` at
`Physlib/Optics/Systems/Microring/AddDropNetwork.lean:485`. Their component families select the
physical N7 scattering matrices at `AllPass.lean:225-226` and
`AddDropNetwork.lean:381-384`.

The behavior certificate expands N5's `Optics.FlatNetlist.mem_behavior_iff_equations` at
`Physlib/Optics/Network/FlatNetlist.lean:487`. Its functional consequence uses
`Optics.FlatNetlist.responseTransform` and `.toBehavior_responseTransform` at
`Physlib/Optics/Network/FlatNetlistElimination.lean:443` and `:455`.

The DATE matrix consequence uses N3T's
`Optics.TwoPortScatteringTransform.toBackwardFirstChainTransform` through the already audited
merged `SourceBridgeDate` results. No full-matrix inverse is introduced by this slice.

## Public declaration inventory

Unless stated otherwise, names in the first three inventories are in `Optics.Microring`.

### Physical parameters

- `FieldAttenuation`
- `PowerAttenuation`
- `IsFieldAttenuation`
- `IsPowerAttenuation`
- `fieldToPowerAttenuation`
- `powerToFieldAttenuation`
- `isPowerAttenuation_fieldToPower`
- `powerToFieldAttenuation_sq`
- `isFieldAttenuation_powerToField`
- `CouplingParameters`
- `PowerCouplingParameters`
- `IsAmplitudeCoupling`
- `IsPowerCoupling`
- `amplitudeToPowerCoupling`
- `powerToAmplitudeCoupling`
- `isPowerCoupling_sq_of_isAmplitudeCoupling`
- `isAmplitudeCoupling_sqrt_of_isPowerCoupling`
- `sqrt_coupling_squares`
- `CouplingParameters.toDirectionalCoupler`
- `CouplingParameters.IsValid`
- `CouplingParameters.IsValid.toDirectionalCoupler`
- `CouplingParameters.IsValid.isPowerCoupling`
- `CouplingParameters.toTwoPortScattering`
- `PhysicalParameters`
- `PhysicalParameters.IsValid`
- `PhysicalParameters.opticalPathLength`
- `PhysicalParameters.powerAttenuation`
- `PhysicalParameters.fieldAttenuation`
- `PhysicalParameters.propagationConstant`
- `PhysicalParameters.roundTripPhaseLift`
- `PhysicalParameters.roundTripPhase`
- `PhysicalParameters.propagationConstant_mul_pathLength`
- `PhysicalParameters.roundTripPhaseLift_eq_opticalPathLength`
- `PhysicalParameters.fieldAttenuation_pos`
- `PhysicalParameters.powerAttenuation_pos`
- `PhysicalParameters.fieldAttenuation_sq`
- `PhysicalParameters.fieldAttenuation_toPower`
- `PhysicalParameters.IsValid.isFieldAttenuation`
- `PhysicalParameters.IsValid.isPowerAttenuation`
- `AllPassPhysicalParameters`
- `AllPassPhysicalParameters.IsValid`
- `AllPassPhysicalParameters.toParameters`
- `AllPassPhysicalParameters.toParameters_data`
- `AllPassPhysicalParameters.IsValid.toParameters`
- `AddDropPhysicalParameters`
- `AddDropPhysicalParameters.IsValid`
- `AddDropPhysicalParameters.toParameters`
- `AddDropPhysicalParameters.toParameters_data`
- `AddDropPhysicalParameters.IsValid.toParameters`

### Independent relations and realization certificates

- `allPassTopology`
- `allPassInputChannel`
- `allPassThroughChannel`
- `addDropTopology`
- `addDropInputChannel`
- `addDropThroughChannel`
- `addDropAddChannel`
- `addDropDropChannel`
- `AllPassInternalFields`
- `AllPassFieldRelation`
- `AddDropInternalFields`
- `AddDropFieldRelation`
- `allPassInternalFieldsOfState`
- `allPass_realization_satisfies_fieldRelation`
- `allPassTopology_satisfies_fieldRelation`
- `addDropInternalFieldsOfState`
- `addDrop_realization_satisfies_fieldRelation`
- `addDropTopology_satisfies_fieldRelation`
- `AllPassFieldRelation.through_eq_transfer`
- `AddDropFieldRelation.through_drop_eq_transfer`
- `allPass_physicalResponse_satisfies_fieldRelation`
- `allPass_physicalResponse_eq_transfer`
- `addDrop_physicalResponse_satisfies_fieldRelation`
- `addDrop_physicalResponse_eq_transfers`

### Source composition

These names are in `Optics.MicroringSourceBridge`:

- `DateParameters.toPhysicalCoupling`
- `DateParameters.toPhysicalPropagation`
- `DateParameters.toPhysicalAddDrop`
- `DateParameters.toPhysicalPropagation_fieldAttenuation`
- `DateParameters.toPhysicalPropagation_roundTripPhaseLift`
- `DateParameters.toPhysicalAddDrop_toParameters`
- `DateParameters.toPhysicalAddDrop_isValid`
- `DateParameters.toPhysicalAddDrop_hasNonzeroDenominator`
- `DateParameters.toPhysicalCoupling_toTwoPortScattering`
- `DateParameters.toPhysicalCoupling_hasBijectiveRightToLeftTransmission`
- `dateTwoPortChainMatrix_eq_gauged_physicalCouplerChain`
- `datePhysicalN5FourPortScattering`
- `datePhysicalN5FourPortScattering_eq_n5Response`
- `datePhysicalN5FourPortScattering_eq_source`
- `datePhysicalN5FourPortScattering_hasBijectiveRightToLeftTransmission`
- `dateForwardTransfer_eq_physicalResponse`
- `dateBackwardTransfer_eq_physicalResponse`
- `datePhysicalFourPortChainTransform_eq`
- `dateFourPortChainMatrix_eq_reindexed_physicalResponse`
- `addDropPhysicalToSysConParameters`
- `addDropPhysicalToSysConParameters_toAddDrop`
- `addDropPhysicalToSysConParameters_fieldAttenuation_pos`
- `addDropPhysicalToSysConParameters_hasNonzeroDenominator`
- `addDropPhysicalToSysConParameters_isContractive_toParameters`
- `sysConDropTransfer_eq_physicalResponse`
- `sysConDropResponseSeries_eq_physicalResponse`
- `sysConDropPower_eq_physicalResponsePower`
- `sfgAddDropTransfer_eq_physicalResponse`

### Regression declarations

These names are in `Optics.Microring`:

- `physicalRegressionCoupling`
- `physicalRegression_coupling_isValid`
- `physicalRegression_coupling_powers`
- `physicalRegression_powerFractions_not_amplitudeCoupling`
- `physicalRegression_amplitudes_not_powerCoupling`
- `physicalRegressionHalfAttenuation`
- `physicalRegression_halfAttenuation`
- `physicalRegression_halfPowerAttenuation`
- `physicalRegression_halfAttenuation_sq`
- `physicalRegression_attenuation_roleSwap_rejected`
- `physicalRegressionQuarterAttenuation`
- `physicalRegression_quarterAttenuation`
- `physicalRegressionRationalZeroPhase`
- `physicalRegression_zeroPhase_opticalDepth`
- `physicalRegression_zeroPhase_normalizedOpticalPath`
- `physicalRegression_zeroPhase_lift`
- `physicalRegressionRationalHalfTurn`
- `physicalRegression_halfTurn_opticalDepth`
- `physicalRegression_halfTurn_normalizedOpticalPath`
- `physicalRegression_halfTurn_lift`
- `physicalRegressionRationalQuarterTurn`
- `physicalRegression_quarterTurn_opticalDepth`
- `physicalRegression_quarterTurn_normalizedOpticalPath`
- `physicalRegression_quarterTurn_lift`
- `physicalRegression_quarterTurn_carrierPhaseFactor`
- `physicalRegressionAllPass`
- `physicalRegression_allPass_toParameters`
- `physicalRegressionAddDrop`
- `physicalRegression_addDrop_toParameters`
- `physicalRegressionAddDropHalfTurn`
- `physicalRegression_addDropHalfTurn_toParameters`
- `physicalRegressionAllPassInternalFields`
- `physicalRegression_allPass_fieldRelation`
- `physicalRegressionAddDropInternalFields`
- `physicalRegression_addDrop_fieldRelation`
- `physicalRegression_allPass_isWellPosed`
- `physicalRegression_allPass_response`
- `physicalRegression_addDrop_isWellPosed`
- `physicalRegression_addDrop_responses`
- `physicalRegressionDateParameters`
- `physicalRegression_date_toPhysicalAddDrop`
- `physicalRegression_date_fieldAttenuation`
- `physicalRegression_date_phaseFactors`
- `physicalRegression_date_denominator`
- `physicalRegression_date_backwardTransfer`
- `physicalRegression_date_backwardTransfer_eq_response`
- `physicalRegressionSysConParameters`
- `physicalRegression_toSysConParameters`
- `physicalRegression_sysCon_loopGain_denominator`
- `physicalRegression_sysCon_dropTransfer`
- `physicalRegression_sysCon_dropTransfer_eq_response`
- `physicalRegressionSfgParameters`
- `physicalRegression_toSfgParameters`
- `physicalRegression_sfg_dropTransfer`
- `physicalRegression_sfg_dropTransfer_eq_response`

## Exact validation bindings

The validation lane should bind at least these fully qualified names:

- `Optics.Microring.PhysicalParameters.fieldAttenuation_sq`
- `Optics.Microring.PhysicalParameters.fieldAttenuation_toPower`
- `Optics.Microring.PhysicalParameters.roundTripPhaseLift_eq_opticalPathLength`
- `Optics.Microring.isPowerCoupling_sq_of_isAmplitudeCoupling`
- `Optics.Microring.physicalRegression_powerFractions_not_amplitudeCoupling`
- `Optics.Microring.physicalRegression_amplitudes_not_powerCoupling`
- `Optics.Microring.physicalRegression_attenuation_roleSwap_rejected`
- `Optics.Microring.physicalRegression_quarterTurn_carrierPhaseFactor`
- `Optics.Microring.AllPassPhysicalParameters.IsValid.toParameters`
- `Optics.Microring.AddDropPhysicalParameters.IsValid.toParameters`
- `Optics.Microring.AllPassFieldRelation`
- `Optics.Microring.AddDropFieldRelation`
- `Optics.Microring.allPassTopology_satisfies_fieldRelation`
- `Optics.Microring.addDropTopology_satisfies_fieldRelation`
- `Optics.Microring.AllPassFieldRelation.through_eq_transfer`
- `Optics.Microring.AddDropFieldRelation.through_drop_eq_transfer`
- `Optics.Microring.allPass_physicalResponse_eq_transfer`
- `Optics.Microring.addDrop_physicalResponse_eq_transfers`
- `Optics.MicroringSourceBridge.DateParameters.toPhysicalAddDrop_toParameters`
- `Optics.MicroringSourceBridge.dateTwoPortChainMatrix_eq_gauged_physicalCouplerChain`
- `Optics.MicroringSourceBridge.dateForwardTransfer_eq_physicalResponse`
- `Optics.MicroringSourceBridge.dateBackwardTransfer_eq_physicalResponse`
- `Optics.MicroringSourceBridge.dateFourPortChainMatrix_eq_reindexed_physicalResponse`
- `Optics.MicroringSourceBridge.sysConDropTransfer_eq_physicalResponse`
- `Optics.MicroringSourceBridge.sysConDropResponseSeries_eq_physicalResponse`
- `Optics.MicroringSourceBridge.sysConDropPower_eq_physicalResponsePower`
- `Optics.MicroringSourceBridge.sfgAddDropTransfer_eq_physicalResponse`
- `Optics.Microring.physicalRegression_zeroPhase_lift`
- `Optics.Microring.physicalRegression_halfTurn_lift`
- `Optics.Microring.physicalRegression_allPass_fieldRelation`
- `Optics.Microring.physicalRegression_addDrop_fieldRelation`
- `Optics.Microring.physicalRegression_allPass_response`
- `Optics.Microring.physicalRegression_addDrop_responses`
- `Optics.Microring.physicalRegression_date_backwardTransfer_eq_response`
- `Optics.Microring.physicalRegression_sysCon_dropTransfer_eq_response`
- `Optics.Microring.physicalRegression_sfg_dropTransfer_eq_response`

## Source-parity consequences and exact gates

- IP-03's DATE two-port chain matrix is a physical N7 chain conversion under
  `DateParameters.IsUnitary` and `transmissivity != 0`. The matrix is related by the existing
  algebraic `dateChainGauge`; no reference-plane provenance is inferred for that sign gauge.
- IP-04's DATE four-port chain matrix is a reindexed physical N5 response under source unitarity,
  the ring `HasNonzeroDenominator` gate, and `dateForwardTransfer p != 0` for the chain pivot.
- IP-05's SysCon quotient is the physical input-to-drop response under the ring denominator gate.
  Its infinite-series meaning additionally requires the existing source `IsContractive` gate.
- IP-06 gains only the amplitude-derived normalized-modal-power consequence
  `sysConDropPower_eq_physicalResponsePower`. The disputed printed Thm. 6 denominator remains
  withheld.
- IP-07 gains no log-base claim. The source's unspecified logarithm base remains unresolved.
- IP-12 is a physical response consequence only under the explicit principal-square-root branch
  equality and the ring denominator gate.
- The DATE and SysCon parameter maps provide the physically parameterized validation hooks for
  the relevant source rows. This slice makes no MZI parity claim and does not rewrite ledger
  status fields.

## Independent regression certificates

- The attenuation anchors expand `exp (-alpha * L / 2)` by hand to `1 / 2` and `1 / 4`.
- Rational normalized optical paths give phase lifts `0`, `Real.pi / 2`, and `Real.pi` exactly.
- The quarter-turn carrier factor expands directly to `-Complex.I`, pinning the exponent sign.
- Negative controls reject squared powers as amplitudes, amplitudes as power fractions, and a
  swapped field/power attenuation pair through the typed conversion.
- The field-relation fixtures substitute all internal fields directly.
- The N5 response fixtures transport the independently eliminated S2 named values; they do not
  use the new physical-response theorems.
- DATE, SysCon, and SFG source fields are separately expanded to `-32 / 91` and then compared
  with the independently anchored N5 response. They do not invoke the source-composition theorem
  being tested.
- The drop value uses the N7 `-I * k` gauge and symmetric first-half-arc reference plane. It is
  gauge- and reference-plane-dependent. The all-pass through value is gauge-insensitive.

## Totalized-versus-gated split

- Physical parameter functions, parameter maps, topologies, and field relations are total.
- N5 `FlatNetlist.behavior` remains singular-safe and relational.
- A functional all-pass or add-drop response requires the corresponding S2
  `HasNonzeroDenominator` gate.
- The DATE two-port chain representation additionally requires a nonzero scalar transmission
  pivot and source unitarity for the closed-form identification.
- The DATE four-port chain representation additionally requires source unitarity, ring
  solvability, and a nonzero forward-response pivot.
- The SysCon quotient requires ring solvability; the geometric series requires contraction.
- The SFG transfer comparison requires its explicit square-root branch equality and ring
  solvability.
- No determinant or full-matrix inverse identity is claimed outside those gates.

## Conventions and non-claims

- `powerAttenuationCoefficient` is a power-loss coefficient per unit geometric path length.
  Therefore round-trip power retention is `exp (-alpha * L)` and field retention is its explicit
  square root `exp (-alpha * L / 2)`.
- Effective index is constant at one selected carrier. No dispersion, group-delay, or actual
  time-delay model is supplied.
- There is no bending-loss, coupling-length, material, thermal, nonlinear, bandwidth, causality,
  omitted-loss-channel, reciprocity, or measurement-validation claim.
- Coupler amplitudes remain free N7 parameters; there is no coupling-length law.
- Power means normalized modal power, not electromagnetic power before a Poynting-normalization
  bridge. `Physlib/Optics/HarmonicFlux/PropagatingModePower.lean:16-22,60-93` requires a finite,
  common-frequency Maxwell family with pairwise-integrable measured profiles that are mutually
  flux-orthogonal and unit normalized. Those hypotheses are not inferred here.
- All-pass through amplitude is insensitive to the quadrature cross-sign gauge. Add-drop drop
  amplitude is gauge- and reference-plane-dependent.
- No named phase point is claimed to be an extremum.

## Gate record

After merging `optics/development`, the following single locked command exited successfully:

```text
lake-lock env bash -c 'lake build <four S0 modules> &&
  lake exe runPhyslibLinters && lake exe lint_all'
```

Detailed results:

- all four S0 modules built successfully;
- `runPhyslibLinters` passed for both Physlib and QuantumInfo;
- `lint_all` reported a successful build, complete registry coverage, legal imports, no duplicate
  TODO tags, correct sorry/pseudo attribution, and passing Lean declaration linters;
- the aggregate style and transitive-import reports contain only pre-existing repository paths,
  with no S0 file named; and
- `lint_all` exited with status zero.

The temporary sorted `Physlib.lean` imports used for the registry-aware gate were removed
byte-for-byte before this handoff.
