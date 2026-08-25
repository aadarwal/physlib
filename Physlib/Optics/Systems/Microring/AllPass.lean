/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Components.DirectionalCouplerPhysicalPower
public import Physlib.Optics.Components.MatchedPropagationPhysicalPower
public import Physlib.Optics.Network.FlatNetlistElimination

/-!
# All-pass microring feedback networks

## i. Overview

This file constructs a one-bus microring as an explicit `FlatNetlist`: one physical directional
coupler supplies the bus/ring mixing and one physical matched-propagation component closes the ring.
The two ring ports of the coupler are connected to the two propagation ports, while the two bus
ports remain external. The response is therefore obtained from `FlatNetlist.responseTransform`,
not stored as a component behavior.

The construction uses `DirectionalCoupler.Parameters` and
`DirectionalCoupler.physicalScattering` from
`Physlib/Optics/Components/DirectionalCoupler.lean:62` and
`Physlib/Optics/Components/DirectionalCouplerPhysical.lean:161`, together with
`MatchedPropagation.Parameters` and `MatchedPropagation.physicalScattering` from
`Physlib/Optics/Components/MatchedPropagation.lean:79` and
`Physlib/Optics/Components/MatchedPropagationPhysical.lean:167`. The component power laws used by
later system results are `DirectionalCoupler.physicalBehavior_output_power` and
`DirectionalCoupler.physicalScattering_isLossless` at
`Physlib/Optics/Components/DirectionalCouplerPhysicalPower.lean:51,72`, and the corresponding
matched-propagation results at
`Physlib/Optics/Components/MatchedPropagationPhysicalPower.lean:59,86`.

The N7 cross-arm coefficient is `-I * k`, as defined at
`Physlib/Optics/Components/DirectionalCoupler.lean:68-70`. A source model using `+I * k` differs by
an arm-gauge choice; the ring formulas below retain the N7 sign rather than silently changing it.

The algebraic solve domain is exactly the nonvanishing of `1 - t * gamma`, where `gamma` is the
single-pass complex field coefficient. The multiple-round-trip expansion is asserted only when
`norm (t * gamma) < 1`; invertibility alone remains sufficient for algebraic elimination.

This is a fixed-carrier, single-mode model. Power means normalized modal power, not electromagnetic
power before a Poynting-normalization bridge. The file makes no reciprocity, bandwidth, causality,
dispersion, group-delay, material-realization, or omitted-loss-channel claim.

## ii. Key results

- `AllPass.netlist`: the explicit coupler-and-propagation feedback network.
- `AllPass.isWellPosed_iff`: the exact algebraic denominator gate.
- `AllPass.response_through`: the all-pass transfer amplitude derived from N5 elimination.
- `AllPass.throughTransfer_eq_roundTripSeries`: agreement with the convergent round-trip series.

## iii. Table of contents

- A. Parameters and algebraic response
- B. Explicit component family and feedback wiring
- C. Exact component and routing equations
- D. Well-posedness and N5 elimination
- E. Convergent multiple-round-trip view

## iv. References

The explicit network construction and its component laws are Physlib-original. The derived transfer
shape corresponds to the standard one-bus microring response. Source-parity port-order bridges to
DATE 2014 and SysCon 2015 remain separate declarations with their corrected nondegeneracy gates.
-/

@[expose] public section

namespace Optics

noncomputable section

namespace AllPass

/-! ## A. Parameters and algebraic response -/

/-- Fixed-carrier parameters of a single-mode all-pass microring. -/
structure Parameters where
  /-- Same-arm field transmission amplitude of the directional coupler. -/
  throughAmplitude : ℝ
  /-- Cross-arm field coupling amplitude before the coupler's pinned `-I` phase. -/
  crossAmplitude : ℝ
  /-- Retained field-amplitude factor for one pass around the ring. -/
  fieldAttenuation : ℝ
  /-- Carrier phase accumulated in one pass around the ring. -/
  roundTripPhase : Real.Angle

/-- The N7 directional-coupler parameters selected by an all-pass ring. -/
def Parameters.coupler (p : Parameters) : DirectionalCoupler.Parameters where
  throughAmplitude := p.throughAmplitude
  crossAmplitude := p.crossAmplitude

/-- The all-pass coupler projection retains the declared field amplitudes. -/
@[simp]
lemma Parameters.coupler_amplitudes (p : Parameters) :
    p.coupler.throughAmplitude = p.throughAmplitude ∧
      p.coupler.crossAmplitude = p.crossAmplitude := ⟨rfl, rfl⟩

/-- The N7 matched-propagation parameters selected by an all-pass ring. -/
def Parameters.propagation (p : Parameters) : MatchedPropagation.Parameters where
  amplitudeTransmission := p.fieldAttenuation
  carrierPathPhase := p.roundTripPhase

/-- The all-pass propagation projection retains attenuation and phase. -/
@[simp]
lemma Parameters.propagation_data (p : Parameters) :
    p.propagation.amplitudeTransmission = p.fieldAttenuation ∧
      p.propagation.carrierPathPhase = p.roundTripPhase := ⟨rfl, rfl⟩

/-- The single-pass complex field coefficient supplied by N7 matched propagation. -/
def Parameters.loopCoefficient (p : Parameters) : ℂ :=
  MatchedPropagation.transmissionCoefficient p.propagation

/-- The loop coefficient is field attenuation times the pinned negative carrier phase. -/
lemma Parameters.loopCoefficient_eq (p : Parameters) :
    p.loopCoefficient =
      (p.fieldAttenuation : ℂ) *
        MatchedPropagation.carrierPhaseFactor p.roundTripPhase := rfl

/-- The complex multiplier acquired by one additional circulation after the coupler. -/
def Parameters.loopGain (p : Parameters) : ℂ :=
  (p.throughAmplitude : ℂ) * p.loopCoefficient

/-- The loop gain is the product of the coupler through amplitude and one-pass coefficient. -/
lemma Parameters.loopGain_eq (p : Parameters) :
    p.loopGain = (p.throughAmplitude : ℂ) * p.loopCoefficient := rfl

/-- The scalar feedback denominator `1 - t * gamma`. -/
def Parameters.denominator (p : Parameters) : ℂ :=
  1 - p.loopGain

/-- The denominator expands to the exact coupler-propagation loop factor. -/
lemma Parameters.denominator_eq (p : Parameters) :
    p.denominator = 1 - (p.throughAmplitude : ℂ) * p.loopCoefficient := rfl

/-- The exact algebraic solve gate for the all-pass feedback loop. -/
def Parameters.HasNonzeroDenominator (p : Parameters) : Prop :=
  p.denominator ≠ 0

/-- The named solve gate is exactly nonvanishing of `1 - t * gamma`. -/
lemma Parameters.hasNonzeroDenominator_iff (p : Parameters) :
    p.HasNonzeroDenominator ↔
      1 - (p.throughAmplitude : ℂ) * p.loopCoefficient ≠ 0 := Iff.rfl

/-- The sufficient convergence gate for the multiple-round-trip expansion. -/
def Parameters.IsContractive (p : Parameters) : Prop :=
  ‖p.loopGain‖ < 1

/-- The named contraction gate is exactly the norm bound on one circulation. -/
lemma Parameters.isContractive_iff (p : Parameters) :
    p.IsContractive ↔ ‖(p.throughAmplitude : ℂ) * p.loopCoefficient‖ < 1 := Iff.rfl

/-- The component-validity predicate for the reduced fixed-carrier model. -/
def Parameters.IsValid (p : Parameters) : Prop :=
  p.coupler.IsValid ∧ p.propagation.IsValid

/-- All-pass validity is exactly the conjunction of the two N7 component predicates. -/
lemma Parameters.isValid_iff (p : Parameters) :
    p.IsValid ↔ p.coupler.IsValid ∧ p.propagation.IsValid := Iff.rfl

/-- The algebraic through-port transfer amplitude, totalized outside the solve domain. -/
def throughTransfer (p : Parameters) : ℂ :=
  (p.throughAmplitude : ℂ) +
    DirectionalCoupler.crossCoefficient p.coupler ^ 2 * p.loopCoefficient / p.denominator

/-- On the solve domain, the through transfer satisfies its denominator-cleared identity. -/
lemma throughTransfer_mul_denominator (p : Parameters) (hDenominator : p.HasNonzeroDenominator) :
    throughTransfer p * p.denominator =
      (p.throughAmplitude : ℂ) * p.denominator +
        DirectionalCoupler.crossCoefficient p.coupler ^ 2 * p.loopCoefficient := by
  rw [throughTransfer, add_mul, div_mul_cancel₀ _ hDenominator]

/-- The conventional unitary-coupler presentation of the all-pass transfer amplitude. -/
def standardThroughTransfer (p : Parameters) : ℂ :=
  ((p.throughAmplitude : ℂ) - p.loopCoefficient) / p.denominator

/-- Unitary coupler normalization reduces the N7-phase transfer to `(t - gamma)/(1 - t*gamma)`. -/
theorem throughTransfer_eq_standard (p : Parameters) (hUnitary : p.coupler.IsUnitary)
    (hDenominator : p.HasNonzeroDenominator) :
    throughTransfer p = standardThroughTransfer p := by
  have hNormalization :
      (p.throughAmplitude : ℂ) ^ 2 + (p.crossAmplitude : ℂ) ^ 2 = 1 := by
    exact_mod_cast hUnitary
  apply mul_right_cancel₀ hDenominator
  rw [throughTransfer_mul_denominator p hDenominator, standardThroughTransfer,
    div_mul_cancel₀ _ hDenominator, Parameters.denominator, Parameters.loopGain]
  change
    (p.throughAmplitude : ℂ) *
          (1 - (p.throughAmplitude : ℂ) * p.loopCoefficient) +
        (-Complex.I * (p.crossAmplitude : ℂ)) ^ 2 * p.loopCoefficient =
      (p.throughAmplitude : ℂ) - p.loopCoefficient
  rw [mul_pow, show (-Complex.I : ℂ) ^ 2 = -1 by norm_num [Complex.I_sq], neg_one_mul]
  linear_combination -p.loopCoefficient * hNormalization

/-! ## B. Explicit component family and feedback wiring -/

/-- The two physical components of the all-pass ring. -/
inductive Component
  | coupler
  | propagation
  deriving DecidableEq

/-- The all-pass component labels form a finite type. -/
instance : Fintype Component where
  elems := {Component.coupler, Component.propagation}
  complete component := by cases component <;> simp

/-- The owned physical-port family of each all-pass component. -/
def componentPortFamily : Component → PortModeFamily
  | .coupler => DirectionalCoupler.portFamily Unit
  | .propagation => MatchedPropagation.portFamily Unit

/-- The component port families are exactly the two N7 physical presentations. -/
lemma componentPortFamily_eq :
    componentPortFamily Component.coupler = DirectionalCoupler.portFamily Unit ∧
      componentPortFamily Component.propagation = MatchedPropagation.portFamily Unit :=
  ⟨rfl, rfl⟩

/-- The parameterized local scattering law of each all-pass component. -/
def componentScattering (p : Parameters) :
    (component : Component) → ScatteringMatrix (componentPortFamily component).Channel
  | .coupler => DirectionalCoupler.physicalScattering p.coupler Unit
  | .propagation => MatchedPropagation.physicalScattering p.propagation Unit

/-- Component scattering selects the two N7 physical scattering matrices exactly. -/
lemma componentScattering_eq (p : Parameters) :
    componentScattering p Component.coupler =
        DirectionalCoupler.physicalScattering p.coupler Unit ∧
      componentScattering p Component.propagation =
        MatchedPropagation.physicalScattering p.propagation Unit := ⟨rfl, rfl⟩

/-- The two N7 components before the ring feedback wiring is installed. -/
def components (p : Parameters) : ScatteringComponentFamily where
  Component := Component
  portFamily := componentPortFamily
  scattering := componentScattering p

/-- The all-pass component family exposes the declared port and scattering data. -/
lemma components_data (p : Parameters) :
    (components p).portFamily = componentPortFamily ∧
      (components p).scattering = componentScattering p := ⟨rfl, rfl⟩

/-- The concrete component labels remain finite through the component-family projection. -/
noncomputable instance componentsComponentFintype (p : Parameters) :
    Fintype (components p).Component := by
  change Fintype Component
  infer_instance

/-- The concrete component labels retain decidable equality through the family projection. -/
noncomputable instance componentsComponentDecidableEq (p : Parameters) :
    DecidableEq (components p).Component := by
  change DecidableEq Component
  infer_instance

/-- The two physical connections closing the ring around the coupler's second arm. -/
inductive Connection
  | rightToPropagation
  | propagationToLeft
  deriving DecidableEq

/-- The all-pass connection labels form a finite type. -/
instance : Fintype Connection where
  elems := {Connection.rightToPropagation, Connection.propagationToLeft}
  complete connection := by cases connection <;> simp

/-- The proof-carrying ring connections; the two first-arm bus ports remain external. -/
def connections (p : Parameters) :
    PortConnectionFamily (components p).aggregatePortModeFamily Connection where
  connection
    | .rightToPropagation =>
        { left := ⟨Component.coupler, DirectionalCoupler.Port.rightSecond⟩
          right := ⟨Component.propagation, MatchedPropagation.Port.left⟩
          left_ne_right := by intro h; cases h
          modeEquiv := Equiv.refl Unit }
    | .propagationToLeft =>
        { left := ⟨Component.propagation, MatchedPropagation.Port.right⟩
          right := ⟨Component.coupler, DirectionalCoupler.Port.leftSecond⟩
          left_ne_right := by intro h; cases h
          modeEquiv := Equiv.refl Unit }
  endpointPort_injective := by
    rintro ⟨firstConnection, firstEnd⟩ ⟨secondConnection, secondEnd⟩ hPort
    cases firstConnection <;> cases firstEnd <;>
      cases secondConnection <;> cases secondEnd
    all_goals first | rfl | cases hPort

/-- The connection family chooses exactly the two declared coupler-propagation pairs. -/
lemma connections_pairs (p : Parameters) :
    ((connections p).connection Connection.rightToPropagation).left =
        ⟨Component.coupler, DirectionalCoupler.Port.rightSecond⟩ ∧
      ((connections p).connection Connection.propagationToLeft).right =
        ⟨Component.coupler, DirectionalCoupler.Port.leftSecond⟩ := ⟨rfl, rfl⟩

/-- The explicit all-pass microring flat netlist. -/
def netlist (p : Parameters) : FlatNetlist where
  components := components p
  Connection := Connection
  connections := connections p

/-- The all-pass netlist compiles exactly the declared components and ring wiring. -/
lemma netlist_data (p : Parameters) :
    (netlist p).components = components p ∧ (netlist p).connections = connections p :=
  ⟨rfl, rfl⟩

/-- Every local all-pass component channel family is finite. -/
noncomputable instance localChannelFintype (component : Component) :
    Fintype (componentPortFamily component).Channel := by
  cases component
  · exact DirectionalCoupler.channelFintype
  · exact MatchedPropagation.channelFintype

/-- Every local all-pass component channel family has decidable equality. -/
noncomputable instance localChannelDecidableEq (component : Component) :
    DecidableEq (componentPortFamily component).Channel := by
  cases component
  · exact DirectionalCoupler.channelDecidableEq
  · exact MatchedPropagation.channelDecidableEq

/-- Projected local component channels remain finite. -/
noncomputable instance componentsLocalChannelFintype (p : Parameters)
    (component : (components p).Component) :
    Fintype ((components p).portFamily component).Channel := by
  change Fintype (componentPortFamily component).Channel
  exact localChannelFintype component

/-- Projected local component channels retain decidable equality. -/
noncomputable instance componentsLocalChannelDecidableEq (p : Parameters)
    (component : (components p).Component) :
    DecidableEq ((components p).portFamily component).Channel := by
  change DecidableEq (componentPortFamily component).Channel
  exact localChannelDecidableEq component

/-- The aggregate channel family of the projected components is finite. -/
noncomputable instance componentsChannelFintype (p : Parameters) :
    Fintype (components p).aggregatePortModeFamily.Channel := by
  letI : Fintype (components p).IndexedChannel := by
    change Fintype (Σ component : Component, (componentPortFamily component).Channel)
    infer_instance
  exact Fintype.ofEquiv (components p).IndexedChannel (components p).channelEquiv

/-- The aggregate channel family of the projected components has decidable equality. -/
noncomputable instance componentsChannelDecidableEq (p : Parameters) :
    DecidableEq (components p).aggregatePortModeFamily.Channel := Classical.decEq _

/-- Each projected local incident-end family is finite. -/
noncomputable instance componentsLocalIncidentFintype (p : Parameters)
    (component : (components p).Component) :
    Fintype (Incident ((components p).portFamily component).Channel) :=
  Incident.fintypeOf (componentsLocalChannelFintype p component)

/-- Each projected local incident-end family has decidable equality. -/
noncomputable instance componentsLocalIncidentDecidableEq (p : Parameters)
    (component : (components p).Component) :
    DecidableEq (Incident ((components p).portFamily component).Channel) := Classical.decEq _

/-- The netlist projection retains the finite concrete component labels. -/
noncomputable instance netlistComponentFintype (p : Parameters) :
    Fintype (netlist p).components.Component := by
  change Fintype Component
  infer_instance

/-- The netlist projection retains decidable equality on component labels. -/
noncomputable instance netlistComponentDecidableEq (p : Parameters) :
    DecidableEq (netlist p).components.Component := by
  change DecidableEq Component
  infer_instance

/-- Every local channel family exposed by the all-pass netlist is finite. -/
noncomputable instance netlistLocalChannelFintype (p : Parameters)
    (component : (netlist p).components.Component) :
    Fintype ((netlist p).components.portFamily component).Channel := by
  change Fintype (componentPortFamily component).Channel
  exact localChannelFintype component

/-- Every local channel family exposed by the netlist has decidable equality. -/
noncomputable instance netlistLocalChannelDecidableEq (p : Parameters)
    (component : (netlist p).components.Component) :
    DecidableEq ((netlist p).components.portFamily component).Channel := by
  change DecidableEq (componentPortFamily component).Channel
  exact localChannelDecidableEq component

/-- Aggregate all-pass channels are finite. -/
noncomputable instance channelFintype (p : Parameters) : Fintype (netlist p).Channel := by
  letI : Fintype (components p).IndexedChannel := by
    change Fintype (Σ component : Component, (componentPortFamily component).Channel)
    infer_instance
  exact Fintype.ofEquiv (components p).IndexedChannel (components p).channelEquiv

/-- Aggregate all-pass channels have decidable equality. -/
noncomputable instance channelDecidableEq (p : Parameters) : DecidableEq (netlist p).Channel :=
  Classical.decEq _

/-- Each concrete ring connection carries its finite two-ended local channel family. -/
noncomputable instance connectionLocalChannelFintype (p : Parameters)
    (connection : Connection) :
    Fintype ((connections p).connection connection).LocalChannel := by
  cases connection
  · change Fintype (Unit ⊕ Unit)
    exact inferInstance
  · change Fintype (Unit ⊕ Unit)
    exact inferInstance

/-- Internally connected all-pass channels are finite. -/
noncomputable instance connectedChannelFintype (p : Parameters) :
    Fintype (netlist p).ConnectedChannel := by
  change Fintype (connections p).Channel
  infer_instance

/-- Internally connected all-pass channels have decidable equality. -/
noncomputable instance connectedChannelDecidableEq (p : Parameters) :
    DecidableEq (netlist p).ConnectedChannel := Classical.decEq _

/-- External all-pass channels are finite. -/
noncomputable instance externalChannelFintype (p : Parameters) :
    Fintype (netlist p).ExternalChannel :=
  (netlist p).eliminationExternalChannelFintype

/-- The aggregate channel owned by a selected physical coupler port. -/
def couplerChannel (p : Parameters) (port : DirectionalCoupler.Port) : (netlist p).Channel :=
  ⟨⟨Component.coupler, port⟩, ()⟩

/-- Distinct physical coupler ports give distinct aggregate channels. -/
lemma couplerChannel_injective (p : Parameters) : Function.Injective (couplerChannel p) := by
  intro first second hChannel
  injection hChannel with hPort
  injection hPort

/-- Equality of coupler aggregate channels is equality of their physical port labels. -/
@[simp]
lemma couplerChannel_eq_iff (p : Parameters) (first second : DirectionalCoupler.Port) :
    couplerChannel p first = couplerChannel p second ↔ first = second := by
  constructor
  · intro hChannel
    exact couplerChannel_injective p hChannel
  · intro hPort
    rw [hPort]

/-- The aggregate channel owned by a selected physical propagation port. -/
def propagationChannel (p : Parameters) (port : MatchedPropagation.Port) : (netlist p).Channel :=
  ⟨⟨Component.propagation, port⟩, ()⟩

/-- Distinct physical propagation ports give distinct aggregate channels. -/
lemma propagationChannel_injective (p : Parameters) :
    Function.Injective (propagationChannel p) := by
  intro first second hChannel
  injection hChannel with hPort
  injection hPort

/-- Equality of propagation aggregate channels is equality of their physical port labels. -/
@[simp]
lemma propagationChannel_eq_iff (p : Parameters) (first second : MatchedPropagation.Port) :
    propagationChannel p first = propagationChannel p second ↔ first = second := by
  constructor
  · intro hChannel
    exact propagationChannel_injective p hChannel
  · intro hPort
    rw [hPort]

/-- A coupler channel cannot equal a propagation-component channel. -/
@[simp]
lemma couplerChannel_ne_propagationChannel (p : Parameters)
    (couplerPort : DirectionalCoupler.Port) (propagationPort : MatchedPropagation.Port) :
    couplerChannel p couplerPort ≠ propagationChannel p propagationPort := by
  intro hChannel
  have hComponent := congrArg (fun channel => channel.1.1) hChannel
  cases hComponent

/-- A propagation-component channel cannot equal a coupler channel. -/
@[simp]
lemma propagationChannel_ne_couplerChannel (p : Parameters)
    (propagationPort : MatchedPropagation.Port) (couplerPort : DirectionalCoupler.Port) :
    propagationChannel p propagationPort ≠ couplerChannel p couplerPort := by
  exact Ne.symm (couplerChannel_ne_propagationChannel p couplerPort propagationPort)

/-- The left first-arm bus channel is not selected by either internal ring connection. -/
lemma couplerChannel_leftFirst_not_connected (p : Parameters) :
    couplerChannel p DirectionalCoupler.Port.leftFirst ∉
      Set.range (netlist p).connections.channelEmbedding := by
  rintro ⟨⟨connection, channel⟩, hChannel⟩
  cases connection <;> rcases channel with mode | mode <;> cases mode
  all_goals cases hChannel

/-- The right first-arm bus channel is not selected by either internal ring connection. -/
lemma couplerChannel_rightFirst_not_connected (p : Parameters) :
    couplerChannel p DirectionalCoupler.Port.rightFirst ∉
      Set.range (netlist p).connections.channelEmbedding := by
  rintro ⟨⟨connection, channel⟩, hChannel⟩
  cases connection <;> rcases channel with mode | mode <;> cases mode
  all_goals cases hChannel

/-- The packaged external input-side bus channel. -/
def inputChannel (p : Parameters) : (netlist p).ExternalChannel :=
  ⟨couplerChannel p DirectionalCoupler.Port.leftFirst,
    couplerChannel_leftFirst_not_connected p⟩

/-- The input channel exposes the coupler's physical `leftFirst` port. -/
@[simp]
lemma inputChannel_val (p : Parameters) :
    (inputChannel p).1 = couplerChannel p DirectionalCoupler.Port.leftFirst := rfl

/-- The packaged external through-side bus channel. -/
def throughChannel (p : Parameters) : (netlist p).ExternalChannel :=
  ⟨couplerChannel p DirectionalCoupler.Port.rightFirst,
    couplerChannel_rightFirst_not_connected p⟩

/-- The through channel exposes the coupler's physical `rightFirst` port. -/
@[simp]
lemma throughChannel_val (p : Parameters) :
    (throughChannel p).1 = couplerChannel p DirectionalCoupler.Port.rightFirst := rfl

/-- The input and through external channels are distinct. -/
lemma inputChannel_ne_throughChannel (p : Parameters) : inputChannel p ≠ throughChannel p := by
  intro hChannel
  have hPort := couplerChannel_injective p (congrArg Subtype.val hChannel)
  cases hPort

/-- A coherent scalar amplitude injected only at the left bus input. -/
def inputAmplitude (p : Parameters) (amplitude : ℂ) :
    ModeAmplitude (netlist p).ExternalIncident :=
  PiLp.single 2 (Incident.mk (inputChannel p)) amplitude

/-- The declared all-pass input amplitude has its supplied value at the input channel. -/
@[simp]
lemma inputAmplitude_apply_input (p : Parameters) (amplitude : ℂ) :
    inputAmplitude p amplitude (Incident.mk (inputChannel p)) = amplitude := by
  simp [inputAmplitude]

/-- The declared all-pass input amplitude vanishes at the opposite bus channel. -/
@[simp]
lemma inputAmplitude_apply_through (p : Parameters) (amplitude : ℂ) :
    inputAmplitude p amplitude (Incident.mk (throughChannel p)) = 0 := by
  rw [inputAmplitude]
  simp [Ne.symm (inputChannel_ne_throughChannel p)]

/-! ## C. Exact component and routing equations -/

/-- The local physical coupler sends the left bus/ring inputs to the right bus output. -/
lemma couplerScattering_apply_rightFirst (p : Parameters)
    (incident : ModeAmplitude (Incident (DirectionalCoupler.portFamily Unit).Channel)) :
    (DirectionalCoupler.physicalScattering p.coupler Unit).toOrientedModeTransform.toLinearMap
        incident (Outgoing.mk ⟨DirectionalCoupler.Port.rightFirst, ()⟩) =
      (p.throughAmplitude : ℂ) *
          incident (Incident.mk ⟨DirectionalCoupler.Port.leftFirst, ()⟩) +
        DirectionalCoupler.crossCoefficient p.coupler *
          incident (Incident.mk ⟨DirectionalCoupler.Port.leftSecond, ()⟩) := by
  rw [DirectionalCoupler.physicalScattering_toOrientedModeTransform,
    ModeTransform.toLinearMap_reindex_eq,
    DirectionalCoupler.scattering_toTwoPortScatteringTransform_toLinearMap_apply,
    ReflectionlessTwoPort.outputMap_apply,
    DirectionalCoupler.mixing_toLinearMap_apply,
    DirectionalCoupler.mixing_toLinearMap_apply]
  rfl

/-- The local physical coupler sends the left bus/ring inputs to the right ring output. -/
lemma couplerScattering_apply_rightSecond (p : Parameters)
    (incident : ModeAmplitude (Incident (DirectionalCoupler.portFamily Unit).Channel)) :
    (DirectionalCoupler.physicalScattering p.coupler Unit).toOrientedModeTransform.toLinearMap
        incident (Outgoing.mk ⟨DirectionalCoupler.Port.rightSecond, ()⟩) =
      DirectionalCoupler.crossCoefficient p.coupler *
          incident (Incident.mk ⟨DirectionalCoupler.Port.leftFirst, ()⟩) +
        (p.throughAmplitude : ℂ) *
          incident (Incident.mk ⟨DirectionalCoupler.Port.leftSecond, ()⟩) := by
  rw [DirectionalCoupler.physicalScattering_toOrientedModeTransform,
    ModeTransform.toLinearMap_reindex_eq,
    DirectionalCoupler.scattering_toTwoPortScatteringTransform_toLinearMap_apply,
    ReflectionlessTwoPort.outputMap_apply,
    DirectionalCoupler.mixing_toLinearMap_apply,
    DirectionalCoupler.mixing_toLinearMap_apply]
  rfl

/-- The local physical coupler sends the right bus/ring inputs to the left ring output. -/
lemma couplerScattering_apply_leftSecond (p : Parameters)
    (incident : ModeAmplitude (Incident (DirectionalCoupler.portFamily Unit).Channel)) :
    (DirectionalCoupler.physicalScattering p.coupler Unit).toOrientedModeTransform.toLinearMap
        incident (Outgoing.mk ⟨DirectionalCoupler.Port.leftSecond, ()⟩) =
      DirectionalCoupler.crossCoefficient p.coupler *
          incident (Incident.mk ⟨DirectionalCoupler.Port.rightFirst, ()⟩) +
        (p.throughAmplitude : ℂ) *
          incident (Incident.mk ⟨DirectionalCoupler.Port.rightSecond, ()⟩) := by
  rw [DirectionalCoupler.physicalScattering_toOrientedModeTransform,
    ModeTransform.toLinearMap_reindex_eq,
    DirectionalCoupler.scattering_toTwoPortScatteringTransform_toLinearMap_apply,
    ReflectionlessTwoPort.outputMap_apply,
    DirectionalCoupler.mixing_toLinearMap_apply]
  rfl

/-- The local matched propagation sends the left incident amplitude to the right output. -/
lemma propagationScattering_apply_right (p : Parameters)
    (incident : ModeAmplitude (Incident (MatchedPropagation.portFamily Unit).Channel)) :
    (MatchedPropagation.physicalScattering p.propagation Unit).toOrientedModeTransform.toLinearMap
        incident (Outgoing.mk ⟨MatchedPropagation.Port.right, ()⟩) =
      p.loopCoefficient * incident (Incident.mk ⟨MatchedPropagation.Port.left, ()⟩) := by
  let outgoing :=
    (MatchedPropagation.physicalScattering p.propagation Unit).toOrientedModeTransform.toLinearMap
      incident
  have hMember :
      (incident, outgoing) ∈ MatchedPropagation.physicalBehavior p.propagation := by
    rw [← MatchedPropagation.physicalScattering_realizes_physicalBehavior]
    exact (ModeTransform.mem_toBehavior_iff_toLinearMap _ _ _).mpr rfl
  have hRaw := (MatchedPropagation.mem_physicalBehavior_iff p.propagation incident outgoing).mp
    hMember
  rw [MatchedPropagation.mem_behavior_iff] at hRaw
  have hCoordinate := congrArg (fun amplitude => amplitude (Sum.inr (Outgoing.mk ()))) hRaw
  simpa [outgoing, Parameters.loopCoefficient, ModeAmplitude.reindex_apply] using hCoordinate

/-- The local matched propagation sends the right incident amplitude to the left output. -/
lemma propagationScattering_apply_left (p : Parameters)
    (incident : ModeAmplitude (Incident (MatchedPropagation.portFamily Unit).Channel)) :
    (MatchedPropagation.physicalScattering p.propagation Unit).toOrientedModeTransform.toLinearMap
        incident (Outgoing.mk ⟨MatchedPropagation.Port.left, ()⟩) =
      p.loopCoefficient * incident (Incident.mk ⟨MatchedPropagation.Port.right, ()⟩) := by
  let outgoing :=
    (MatchedPropagation.physicalScattering p.propagation Unit).toOrientedModeTransform.toLinearMap
      incident
  have hMember :
      (incident, outgoing) ∈ MatchedPropagation.physicalBehavior p.propagation := by
    rw [← MatchedPropagation.physicalScattering_realizes_physicalBehavior]
    exact (ModeTransform.mem_toBehavior_iff_toLinearMap _ _ _).mpr rfl
  have hRaw := (MatchedPropagation.mem_physicalBehavior_iff p.propagation incident outgoing).mp
    hMember
  rw [MatchedPropagation.mem_behavior_iff] at hRaw
  have hCoordinate := congrArg (fun amplitude => amplitude (Sum.inl (Outgoing.mk ()))) hRaw
  simpa [outgoing, Parameters.loopCoefficient, ModeAmplitude.reindex_apply] using hCoordinate

/-! ## D. Well-posedness and N5 elimination -/

/-- The connected coordinate at the coupler's right second-arm endpoint. -/
def connectedCouplerRightSecond (p : Parameters) : (netlist p).ConnectedChannel :=
  ⟨Connection.rightToPropagation, Sum.inl ()⟩

/-- This connected coordinate embeds as the coupler's right second-arm channel. -/
@[simp]
lemma connectedCouplerRightSecond_embedding (p : Parameters) :
    (netlist p).connections.channelEmbedding (connectedCouplerRightSecond p) =
      couplerChannel p DirectionalCoupler.Port.rightSecond := rfl

/-- The connected coordinate at the propagation component's left endpoint. -/
def connectedPropagationLeft (p : Parameters) : (netlist p).ConnectedChannel :=
  ⟨Connection.rightToPropagation, Sum.inr ()⟩

/-- This connected coordinate embeds as the propagation component's left channel. -/
@[simp]
lemma connectedPropagationLeft_embedding (p : Parameters) :
    (netlist p).connections.channelEmbedding (connectedPropagationLeft p) =
      propagationChannel p MatchedPropagation.Port.left := rfl

/-- The connected coordinate at the propagation component's right endpoint. -/
def connectedPropagationRight (p : Parameters) : (netlist p).ConnectedChannel :=
  ⟨Connection.propagationToLeft, Sum.inl ()⟩

/-- This connected coordinate embeds as the propagation component's right channel. -/
@[simp]
lemma connectedPropagationRight_embedding (p : Parameters) :
    (netlist p).connections.channelEmbedding (connectedPropagationRight p) =
      propagationChannel p MatchedPropagation.Port.right := rfl

/-- The connected coordinate at the coupler's left second-arm endpoint. -/
def connectedCouplerLeftSecond (p : Parameters) : (netlist p).ConnectedChannel :=
  ⟨Connection.propagationToLeft, Sum.inr ()⟩

/-- This connected coordinate embeds as the coupler's left second-arm channel. -/
@[simp]
lemma connectedCouplerLeftSecond_embedding (p : Parameters) :
    (netlist p).connections.channelEmbedding (connectedCouplerLeftSecond p) =
      couplerChannel p DirectionalCoupler.Port.leftSecond := rfl

/-- The first feedback connection exchanges the coupler and propagation endpoints. -/
lemma connectedCouplerRightSecond_mate (p : Parameters) :
    (netlist p).connections.mateEquiv (connectedCouplerRightSecond p) =
      connectedPropagationLeft p := rfl

/-- The reverse orientation of the first feedback connection has the coupler endpoint as mate. -/
lemma connectedPropagationLeft_mate (p : Parameters) :
    (netlist p).connections.mateEquiv (connectedPropagationLeft p) =
      connectedCouplerRightSecond p := rfl

/-- The second feedback connection exchanges propagation and coupler endpoints. -/
lemma connectedPropagationRight_mate (p : Parameters) :
    (netlist p).connections.mateEquiv (connectedPropagationRight p) =
      connectedCouplerLeftSecond p := rfl

/-- The reverse orientation of the second feedback connection has propagation as mate. -/
lemma connectedCouplerLeftSecond_mate (p : Parameters) :
    (netlist p).connections.mateEquiv (connectedCouplerLeftSecond p) =
      connectedPropagationRight p := rfl

/-- A global component-scattering equation restricts to the N7 physical coupler behavior. -/
lemma coupler_physicalBehavior_of_scatteringEquation (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident) :
    (incident.restrictEmbedding
          (Incident.relabelEmbedding
            ((components p).componentChannelEmbedding Component.coupler)),
      outgoing.restrictEmbedding
          (Outgoing.relabelEmbedding
            ((components p).componentChannelEmbedding Component.coupler))) ∈
        DirectionalCoupler.physicalBehavior p.coupler := by
  have hMember : (incident, outgoing) ∈ (netlist p).componentBehavior :=
    ((netlist p).mem_componentBehavior_iff incident outgoing).mpr hScattering
  have hLocal :=
    ((netlist p).mem_componentBehavior_iff_forall_component incident outgoing).mp
      hMember Component.coupler
  change
    (incident.restrictEmbedding
          (Incident.relabelEmbedding
            ((components p).componentChannelEmbedding Component.coupler)),
      outgoing.restrictEmbedding
          (Outgoing.relabelEmbedding
            ((components p).componentChannelEmbedding Component.coupler))) ∈
        (DirectionalCoupler.physicalScattering p.coupler Unit).toOrientedModeTransform.toBehavior
    at hLocal
  rw [DirectionalCoupler.physicalScattering_realizes_physicalBehavior] at hLocal
  exact hLocal

/-- A global component-scattering equation restricts to N7 matched propagation. -/
lemma propagation_physicalBehavior_of_scatteringEquation (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident) :
    (incident.restrictEmbedding
          (Incident.relabelEmbedding
            ((components p).componentChannelEmbedding Component.propagation)),
      outgoing.restrictEmbedding
          (Outgoing.relabelEmbedding
            ((components p).componentChannelEmbedding Component.propagation))) ∈
        MatchedPropagation.physicalBehavior p.propagation := by
  have hMember : (incident, outgoing) ∈ (netlist p).componentBehavior :=
    ((netlist p).mem_componentBehavior_iff incident outgoing).mpr hScattering
  have hLocal :=
    ((netlist p).mem_componentBehavior_iff_forall_component incident outgoing).mp
      hMember Component.propagation
  change
    (incident.restrictEmbedding
          (Incident.relabelEmbedding
            ((components p).componentChannelEmbedding Component.propagation)),
      outgoing.restrictEmbedding
          (Outgoing.relabelEmbedding
            ((components p).componentChannelEmbedding Component.propagation))) ∈
        ModeTransform.toBehavior
          (ScatteringMatrix.toOrientedModeTransform
            (MatchedPropagation.physicalScattering p.propagation Unit))
    at hLocal
  rw [MatchedPropagation.physicalScattering_realizes_physicalBehavior] at hLocal
  exact hLocal

/-- A component-scattering equation implies the local right-bus coupler equation. -/
lemma scatteringEquation_coupler_rightFirst (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident) :
    outgoing (Outgoing.mk (couplerChannel p DirectionalCoupler.Port.rightFirst)) =
      (p.throughAmplitude : ℂ) *
          incident (Incident.mk (couplerChannel p DirectionalCoupler.Port.leftFirst)) +
        DirectionalCoupler.crossCoefficient p.coupler *
          incident (Incident.mk (couplerChannel p DirectionalCoupler.Port.leftSecond)) := by
  have hPhysical := coupler_physicalBehavior_of_scatteringEquation p incident outgoing hScattering
  have hRaw := (DirectionalCoupler.mem_physicalBehavior_iff p.coupler _ _).mp hPhysical
  rw [DirectionalCoupler.mem_behavior_iff,
    DirectionalCoupler.mixing_toLinearMap_apply,
    DirectionalCoupler.mixing_toLinearMap_apply] at hRaw
  have hCoordinate := congrArg
    (fun amplitude => amplitude (Sum.inr (Outgoing.mk (Sum.inl ())))) hRaw
  change
    outgoing (Outgoing.mk (couplerChannel p DirectionalCoupler.Port.rightFirst)) =
      (p.throughAmplitude : ℂ) *
          incident (Incident.mk (couplerChannel p DirectionalCoupler.Port.leftFirst)) +
        DirectionalCoupler.crossCoefficient p.coupler *
          incident (Incident.mk (couplerChannel p DirectionalCoupler.Port.leftSecond))
    at hCoordinate
  exact hCoordinate

/-- A component-scattering equation implies the local right-ring coupler equation. -/
lemma scatteringEquation_coupler_rightSecond (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident) :
    outgoing (Outgoing.mk (couplerChannel p DirectionalCoupler.Port.rightSecond)) =
      DirectionalCoupler.crossCoefficient p.coupler *
          incident (Incident.mk (couplerChannel p DirectionalCoupler.Port.leftFirst)) +
        (p.throughAmplitude : ℂ) *
          incident (Incident.mk (couplerChannel p DirectionalCoupler.Port.leftSecond)) := by
  have hPhysical := coupler_physicalBehavior_of_scatteringEquation p incident outgoing hScattering
  have hRaw := (DirectionalCoupler.mem_physicalBehavior_iff p.coupler _ _).mp hPhysical
  rw [DirectionalCoupler.mem_behavior_iff,
    DirectionalCoupler.mixing_toLinearMap_apply,
    DirectionalCoupler.mixing_toLinearMap_apply] at hRaw
  have hCoordinate := congrArg
    (fun amplitude => amplitude (Sum.inr (Outgoing.mk (Sum.inr ())))) hRaw
  change
    outgoing (Outgoing.mk (couplerChannel p DirectionalCoupler.Port.rightSecond)) =
      DirectionalCoupler.crossCoefficient p.coupler *
          incident (Incident.mk (couplerChannel p DirectionalCoupler.Port.leftFirst)) +
        (p.throughAmplitude : ℂ) *
          incident (Incident.mk (couplerChannel p DirectionalCoupler.Port.leftSecond))
    at hCoordinate
  exact hCoordinate

/-- A component-scattering equation implies the local left-ring coupler equation. -/
lemma scatteringEquation_coupler_leftSecond (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident) :
    outgoing (Outgoing.mk (couplerChannel p DirectionalCoupler.Port.leftSecond)) =
      DirectionalCoupler.crossCoefficient p.coupler *
          incident (Incident.mk (couplerChannel p DirectionalCoupler.Port.rightFirst)) +
        (p.throughAmplitude : ℂ) *
          incident (Incident.mk (couplerChannel p DirectionalCoupler.Port.rightSecond)) := by
  have hPhysical := coupler_physicalBehavior_of_scatteringEquation p incident outgoing hScattering
  have hRaw := (DirectionalCoupler.mem_physicalBehavior_iff p.coupler _ _).mp hPhysical
  rw [DirectionalCoupler.mem_behavior_iff,
    DirectionalCoupler.mixing_toLinearMap_apply,
    DirectionalCoupler.mixing_toLinearMap_apply] at hRaw
  have hCoordinate := congrArg
    (fun amplitude => amplitude (Sum.inl (Outgoing.mk (Sum.inr ())))) hRaw
  change
    outgoing (Outgoing.mk (couplerChannel p DirectionalCoupler.Port.leftSecond)) =
      DirectionalCoupler.crossCoefficient p.coupler *
          incident (Incident.mk (couplerChannel p DirectionalCoupler.Port.rightFirst)) +
        (p.throughAmplitude : ℂ) *
          incident (Incident.mk (couplerChannel p DirectionalCoupler.Port.rightSecond))
    at hCoordinate
  exact hCoordinate

/-- A component-scattering equation implies forward propagation around the ring. -/
lemma scatteringEquation_propagation_right (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident) :
    outgoing (Outgoing.mk (propagationChannel p MatchedPropagation.Port.right)) =
      p.loopCoefficient *
        incident (Incident.mk (propagationChannel p MatchedPropagation.Port.left)) := by
  have hPhysical :=
    propagation_physicalBehavior_of_scatteringEquation p incident outgoing hScattering
  have hRaw := (MatchedPropagation.mem_physicalBehavior_iff p.propagation _ _).mp hPhysical
  rw [MatchedPropagation.mem_behavior_iff] at hRaw
  have hCoordinate := congrArg (fun amplitude => amplitude (Sum.inr (Outgoing.mk ()))) hRaw
  change
    outgoing (Outgoing.mk (propagationChannel p MatchedPropagation.Port.right)) =
      p.loopCoefficient *
        incident (Incident.mk (propagationChannel p MatchedPropagation.Port.left))
    at hCoordinate
  exact hCoordinate

/-- A component-scattering equation implies reverse propagation around the ring. -/
lemma scatteringEquation_propagation_left (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident) :
    outgoing (Outgoing.mk (propagationChannel p MatchedPropagation.Port.left)) =
      p.loopCoefficient *
        incident (Incident.mk (propagationChannel p MatchedPropagation.Port.right)) := by
  have hPhysical :=
    propagation_physicalBehavior_of_scatteringEquation p incident outgoing hScattering
  have hRaw := (MatchedPropagation.mem_physicalBehavior_iff p.propagation _ _).mp hPhysical
  rw [MatchedPropagation.mem_behavior_iff] at hRaw
  have hCoordinate := congrArg (fun amplitude => amplitude (Sum.inl (Outgoing.mk ()))) hRaw
  change
    outgoing (Outgoing.mk (propagationChannel p MatchedPropagation.Port.left)) =
      p.loopCoefficient *
        incident (Incident.mk (propagationChannel p MatchedPropagation.Port.right))
    at hCoordinate
  exact hCoordinate

/-- Incident assembly returns the supplied left-bus external input. -/
lemma incidentAssembly_apply_leftFirst (p : Parameters)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (external : ModeAmplitude (netlist p).ExternalIncident) :
    (netlist p).connections.incidentAssembly outgoing external
        (Incident.mk (couplerChannel p DirectionalCoupler.Port.leftFirst)) =
      external (Incident.mk (inputChannel p)) := by
  exact (netlist p).connections.incidentAssembly_apply_external
    outgoing external (inputChannel p)

/-- Incident assembly returns the supplied right-bus external input. -/
lemma incidentAssembly_apply_rightFirst (p : Parameters)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (external : ModeAmplitude (netlist p).ExternalIncident) :
    (netlist p).connections.incidentAssembly outgoing external
        (Incident.mk (couplerChannel p DirectionalCoupler.Port.rightFirst)) =
      external (Incident.mk (throughChannel p)) := by
  exact (netlist p).connections.incidentAssembly_apply_external
    outgoing external (throughChannel p)

/-- The coupler's right ring input is routed from the propagation left output. -/
lemma incidentAssembly_apply_coupler_rightSecond (p : Parameters)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (external : ModeAmplitude (netlist p).ExternalIncident) :
    (netlist p).connections.incidentAssembly outgoing external
        (Incident.mk (couplerChannel p DirectionalCoupler.Port.rightSecond)) =
      outgoing (Outgoing.mk (propagationChannel p MatchedPropagation.Port.left)) := by
  rw [← connectedCouplerRightSecond_embedding,
    (netlist p).connections.incidentAssembly_apply_connected_channel,
    connectedCouplerRightSecond_mate, connectedPropagationLeft_embedding]

/-- The propagation left input is routed from the coupler's right ring output. -/
lemma incidentAssembly_apply_propagation_left (p : Parameters)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (external : ModeAmplitude (netlist p).ExternalIncident) :
    (netlist p).connections.incidentAssembly outgoing external
        (Incident.mk (propagationChannel p MatchedPropagation.Port.left)) =
      outgoing (Outgoing.mk (couplerChannel p DirectionalCoupler.Port.rightSecond)) := by
  rw [← connectedPropagationLeft_embedding,
    (netlist p).connections.incidentAssembly_apply_connected_channel,
    connectedPropagationLeft_mate, connectedCouplerRightSecond_embedding]

/-- The propagation right input is routed from the coupler's left ring output. -/
lemma incidentAssembly_apply_propagation_right (p : Parameters)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (external : ModeAmplitude (netlist p).ExternalIncident) :
    (netlist p).connections.incidentAssembly outgoing external
        (Incident.mk (propagationChannel p MatchedPropagation.Port.right)) =
      outgoing (Outgoing.mk (couplerChannel p DirectionalCoupler.Port.leftSecond)) := by
  rw [← connectedPropagationRight_embedding,
    (netlist p).connections.incidentAssembly_apply_connected_channel,
    connectedPropagationRight_mate, connectedCouplerLeftSecond_embedding]

/-- The coupler's left ring input is routed from the propagation right output. -/
lemma incidentAssembly_apply_coupler_leftSecond (p : Parameters)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (external : ModeAmplitude (netlist p).ExternalIncident) :
    (netlist p).connections.incidentAssembly outgoing external
        (Incident.mk (couplerChannel p DirectionalCoupler.Port.leftSecond)) =
      outgoing (Outgoing.mk (propagationChannel p MatchedPropagation.Port.right)) := by
  rw [← connectedCouplerLeftSecond_embedding,
    (netlist p).connections.incidentAssembly_apply_connected_channel,
    connectedCouplerLeftSecond_mate, connectedPropagationRight_embedding]

/-- A homogeneous all-pass feedback state vanishes when its scalar denominator is nonzero. -/
lemma feedback_fixedPoint_eq_zero (p : Parameters) (hDenominator : p.HasNonzeroDenominator)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident)
    (hAssembly : incident = (netlist p).connections.incidentAssembly outgoing 0) :
    incident = 0 := by
  have hLeftBus := congrArg
    (fun amplitude =>
      amplitude (Incident.mk (couplerChannel p DirectionalCoupler.Port.leftFirst)))
    hAssembly
  have hRightBus := congrArg
    (fun amplitude =>
      amplitude (Incident.mk (couplerChannel p DirectionalCoupler.Port.rightFirst)))
    hAssembly
  rw [incidentAssembly_apply_leftFirst] at hLeftBus
  rw [incidentAssembly_apply_rightFirst] at hRightBus
  simp only [PiLp.zero_apply] at hLeftBus hRightBus
  have hCouplerLeft := congrArg
    (fun amplitude =>
      amplitude (Incident.mk (couplerChannel p DirectionalCoupler.Port.leftSecond)))
    hAssembly
  have hPropagationLeft := congrArg
    (fun amplitude =>
      amplitude (Incident.mk (propagationChannel p MatchedPropagation.Port.left)))
    hAssembly
  rw [incidentAssembly_apply_coupler_leftSecond,
    scatteringEquation_propagation_right p incident outgoing hScattering] at hCouplerLeft
  rw [incidentAssembly_apply_propagation_left,
    scatteringEquation_coupler_rightSecond p incident outgoing hScattering,
    hLeftBus, mul_zero, zero_add] at hPropagationLeft
  have hLeftDenominator : p.denominator *
      incident (Incident.mk (couplerChannel p DirectionalCoupler.Port.leftSecond)) = 0 := by
    calc
      p.denominator *
            incident (Incident.mk (couplerChannel p DirectionalCoupler.Port.leftSecond)) =
          incident (Incident.mk (couplerChannel p DirectionalCoupler.Port.leftSecond)) -
            p.loopCoefficient *
              ((p.throughAmplitude : ℂ) *
                incident
                  (Incident.mk (couplerChannel p DirectionalCoupler.Port.leftSecond))) := by
            rw [Parameters.denominator, Parameters.loopGain]
            ring
      _ = incident (Incident.mk (couplerChannel p DirectionalCoupler.Port.leftSecond)) -
            p.loopCoefficient *
              incident (Incident.mk (propagationChannel p MatchedPropagation.Port.left)) := by
            rw [← hPropagationLeft]
      _ = 0 := sub_eq_zero.mpr hCouplerLeft
  have hCouplerLeftZero :
      incident (Incident.mk (couplerChannel p DirectionalCoupler.Port.leftSecond)) = 0 :=
    (mul_eq_zero.mp hLeftDenominator).resolve_left hDenominator
  have hPropagationLeftZero :
      incident (Incident.mk (propagationChannel p MatchedPropagation.Port.left)) = 0 := by
    rw [hPropagationLeft, hCouplerLeftZero, mul_zero]
  have hCouplerRight := congrArg
    (fun amplitude =>
      amplitude (Incident.mk (couplerChannel p DirectionalCoupler.Port.rightSecond)))
    hAssembly
  have hPropagationRight := congrArg
    (fun amplitude =>
      amplitude (Incident.mk (propagationChannel p MatchedPropagation.Port.right)))
    hAssembly
  rw [incidentAssembly_apply_coupler_rightSecond,
    scatteringEquation_propagation_left p incident outgoing hScattering] at hCouplerRight
  rw [incidentAssembly_apply_propagation_right,
    scatteringEquation_coupler_leftSecond p incident outgoing hScattering,
    hRightBus, mul_zero, zero_add] at hPropagationRight
  have hRightDenominator : p.denominator *
      incident (Incident.mk (couplerChannel p DirectionalCoupler.Port.rightSecond)) = 0 := by
    calc
      p.denominator *
            incident (Incident.mk (couplerChannel p DirectionalCoupler.Port.rightSecond)) =
          incident (Incident.mk (couplerChannel p DirectionalCoupler.Port.rightSecond)) -
            p.loopCoefficient *
              ((p.throughAmplitude : ℂ) *
                incident
                  (Incident.mk (couplerChannel p DirectionalCoupler.Port.rightSecond))) := by
            rw [Parameters.denominator, Parameters.loopGain]
            ring
      _ = incident (Incident.mk (couplerChannel p DirectionalCoupler.Port.rightSecond)) -
            p.loopCoefficient *
              incident (Incident.mk (propagationChannel p MatchedPropagation.Port.right)) := by
            rw [← hPropagationRight]
      _ = 0 := sub_eq_zero.mpr hCouplerRight
  have hCouplerRightZero :
      incident (Incident.mk (couplerChannel p DirectionalCoupler.Port.rightSecond)) = 0 :=
    (mul_eq_zero.mp hRightDenominator).resolve_left hDenominator
  have hPropagationRightZero :
      incident (Incident.mk (propagationChannel p MatchedPropagation.Port.right)) = 0 := by
    rw [hPropagationRight, hCouplerRightZero, mul_zero]
  apply WithLp.ofLp_injective 2
  funext endpoint
  rcases endpoint with ⟨⟨⟨component, port⟩, mode⟩⟩
  cases component
  · cases port <;> cases mode
    · simpa [couplerChannel] using hLeftBus
    · simpa [couplerChannel] using hCouplerLeftZero
    · simpa [couplerChannel] using hRightBus
    · simpa [couplerChannel] using hCouplerRightZero
  · cases port <;> cases mode
    · simpa [propagationChannel] using hPropagationLeftZero
    · simpa [propagationChannel] using hPropagationRightZero

/-- A nonzero scalar denominator makes the explicit all-pass feedback network well posed. -/
lemma isWellPosed_of_hasNonzeroDenominator (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) : (netlist p).IsWellPosed := by
  rw [(netlist p).isWellPosed_iff_feedbackOperator_injective]
  intro first second hFeedback
  let difference := first - second
  have hKernel : (netlist p).feedbackOperator.toLinearMap difference = 0 := by
    simp [difference, hFeedback]
  let outgoing := (netlist p).scatteringTransform.toLinearMap difference
  have hAssembly :
      difference = (netlist p).connections.incidentAssembly outgoing 0 := by
    rw [PortConnectionFamily.incidentAssembly, map_zero, add_zero]
    rw [(netlist p).feedbackOperator_apply] at hKernel
    exact sub_eq_zero.mp hKernel
  have hDifference := feedback_fixedPoint_eq_zero p hDenominator difference outgoing rfl hAssembly
  exact sub_eq_zero.mp hDifference

/-- A displayed incident state spanning the forward loop at a singular denominator. -/
def singularIncident (p : Parameters) : ModeAmplitude (netlist p).IncidentIndex :=
  WithLp.toLp 2 fun endpoint =>
    if endpoint.channel = propagationChannel p MatchedPropagation.Port.left then 1
    else if endpoint.channel = couplerChannel p DirectionalCoupler.Port.leftSecond then
      p.loopCoefficient
    else 0

/-- The singular incident state is given by its two explicitly selected coordinates. -/
lemma singularIncident_apply (p : Parameters) (endpoint : (netlist p).IncidentIndex) :
    singularIncident p endpoint =
      if endpoint.channel = propagationChannel p MatchedPropagation.Port.left then 1
      else if endpoint.channel = couplerChannel p DirectionalCoupler.Port.leftSecond then
        p.loopCoefficient
      else 0 := rfl

/-- The displayed singular incident state is nonzero. -/
lemma singularIncident_ne_zero (p : Parameters) : singularIncident p ≠ 0 := by
  intro hZero
  have hCoordinate := congrArg
    (fun amplitude =>
      amplitude (Incident.mk (propagationChannel p MatchedPropagation.Port.left))) hZero
  simp [singularIncident] at hCoordinate

/-- At a zero denominator, the displayed singular incident state closes through the wiring. -/
lemma singularIncident_fixedPoint (p : Parameters) (hDenominator : p.denominator = 0) :
    singularIncident p =
      (netlist p).connections.incidentAssembly
        ((netlist p).scatteringTransform.toLinearMap (singularIncident p)) 0 := by
  have hGain : p.loopGain = 1 := by
    have hDifference : (1 : ℂ) - p.loopGain = 0 := by
      simpa only [Parameters.denominator] using hDenominator
    exact (sub_eq_zero.mp hDifference).symm
  apply WithLp.ofLp_injective 2
  funext endpoint
  rcases endpoint with ⟨⟨⟨component, port⟩, mode⟩⟩
  cases component
  · cases port <;> cases mode
    · change singularIncident p
          (Incident.mk (couplerChannel p DirectionalCoupler.Port.leftFirst)) =
        (netlist p).connections.incidentAssembly
          ((netlist p).scatteringTransform.toLinearMap (singularIncident p)) 0
            (Incident.mk (couplerChannel p DirectionalCoupler.Port.leftFirst))
      rw [incidentAssembly_apply_leftFirst]
      simp [singularIncident]
    · change singularIncident p
          (Incident.mk (couplerChannel p DirectionalCoupler.Port.leftSecond)) =
        (netlist p).connections.incidentAssembly
          ((netlist p).scatteringTransform.toLinearMap (singularIncident p)) 0
            (Incident.mk (couplerChannel p DirectionalCoupler.Port.leftSecond))
      rw [incidentAssembly_apply_coupler_leftSecond,
        scatteringEquation_propagation_right p _ _ rfl]
      simp [singularIncident]
    · change singularIncident p
          (Incident.mk (couplerChannel p DirectionalCoupler.Port.rightFirst)) =
        (netlist p).connections.incidentAssembly
          ((netlist p).scatteringTransform.toLinearMap (singularIncident p)) 0
            (Incident.mk (couplerChannel p DirectionalCoupler.Port.rightFirst))
      rw [incidentAssembly_apply_rightFirst]
      simp [singularIncident]
    · change singularIncident p
          (Incident.mk (couplerChannel p DirectionalCoupler.Port.rightSecond)) =
        (netlist p).connections.incidentAssembly
          ((netlist p).scatteringTransform.toLinearMap (singularIncident p)) 0
            (Incident.mk (couplerChannel p DirectionalCoupler.Port.rightSecond))
      rw [incidentAssembly_apply_coupler_rightSecond,
        scatteringEquation_propagation_left p _ _ rfl]
      simp [singularIncident]
  · cases port <;> cases mode
    · change singularIncident p
          (Incident.mk (propagationChannel p MatchedPropagation.Port.left)) =
        (netlist p).connections.incidentAssembly
          ((netlist p).scatteringTransform.toLinearMap (singularIncident p)) 0
            (Incident.mk (propagationChannel p MatchedPropagation.Port.left))
      rw [incidentAssembly_apply_propagation_left,
        scatteringEquation_coupler_rightSecond p _ _ rfl]
      simp [singularIncident, Parameters.loopGain] at hGain ⊢
      exact hGain.symm
    · change singularIncident p
          (Incident.mk (propagationChannel p MatchedPropagation.Port.right)) =
        (netlist p).connections.incidentAssembly
          ((netlist p).scatteringTransform.toLinearMap (singularIncident p)) 0
            (Incident.mk (propagationChannel p MatchedPropagation.Port.right))
      rw [incidentAssembly_apply_propagation_right,
        scatteringEquation_coupler_leftSecond p _ _ rfl]
      simp [singularIncident]

/-- At a zero denominator, the displayed nonzero state lies in the feedback kernel. -/
lemma singularIncident_feedbackOperator_eq_zero (p : Parameters)
    (hDenominator : p.denominator = 0) :
    (netlist p).feedbackOperator.toLinearMap (singularIncident p) = 0 := by
  rw [(netlist p).feedbackOperator_apply]
  apply sub_eq_zero.mpr
  have hFixed := singularIncident_fixedPoint p hDenominator
  rw [PortConnectionFamily.incidentAssembly, map_zero, add_zero] at hFixed
  exact hFixed

/-- A zero scalar denominator prevents well-posedness of the explicit feedback network. -/
lemma not_isWellPosed_of_denominator_eq_zero (p : Parameters)
    (hDenominator : p.denominator = 0) : ¬(netlist p).IsWellPosed := by
  rw [(netlist p).isWellPosed_iff_feedbackOperator_injective]
  intro hInjective
  apply singularIncident_ne_zero p
  apply hInjective
  rw [singularIncident_feedbackOperator_eq_zero p hDenominator, map_zero]

/-- N5 well-posedness is exactly the nonvanishing of `1 - t * gamma`. -/
lemma isWellPosed_iff (p : Parameters) :
    (netlist p).IsWellPosed ↔ p.HasNonzeroDenominator := by
  constructor
  · intro hWellPosed hZero
    exact not_isWellPosed_of_denominator_eq_zero p hZero hWellPosed
  · exact isWellPosed_of_hasNonzeroDenominator p

/-- External readout returns the aggregate through-bus outgoing coordinate. -/
lemma outputReadout_apply_through (p : Parameters)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex) :
    (netlist p).outputReadout.toLinearMap outgoing (Outgoing.mk (throughChannel p)) =
      outgoing (Outgoing.mk (couplerChannel p DirectionalCoupler.Port.rightFirst)) := by
  rw [FlatNetlist.outputReadout,
    (netlist p).connections.externalOutgoingReadout_apply,
    ModeAmplitude.restrictEmbedding_apply]
  rfl

/-- The N5 response transform acts on a left-bus input by the all-pass transfer amplitude. -/
theorem response_through (p : Parameters) (hDenominator : p.HasNonzeroDenominator)
    (amplitude : ℂ) :
    ((netlist p).responseTransform
        (isWellPosed_of_hasNonzeroDenominator p hDenominator)).toLinearMap
        (inputAmplitude p amplitude) (Outgoing.mk (throughChannel p)) =
      throughTransfer p * amplitude := by
  let hWellPosed := isWellPosed_of_hasNonzeroDenominator p hDenominator
  let output := (netlist p).responseTransform hWellPosed |>.toLinearMap
    (inputAmplitude p amplitude)
  have hMember : (inputAmplitude p amplitude, output) ∈ (netlist p).behavior := by
    rw [← (netlist p).toBehavior_responseTransform hWellPosed,
      ModeTransform.mem_toBehavior_iff_toLinearMap]
  rcases ((netlist p).mem_behavior_iff_equations (inputAmplitude p amplitude) output).mp
      hMember with ⟨incident, outgoing, hScattering, hAssembly, hOutput⟩
  have hAssembly' :
      incident = (netlist p).connections.incidentAssembly
        outgoing (inputAmplitude p amplitude) := by
    simpa only [PortConnectionFamily.incidentAssembly] using hAssembly
  have hInput := congrArg
    (fun state => state (Incident.mk (couplerChannel p DirectionalCoupler.Port.leftFirst)))
    hAssembly'
  rw [incidentAssembly_apply_leftFirst, inputAmplitude_apply_input] at hInput
  have hCouplerLeft := congrArg
    (fun state => state (Incident.mk (couplerChannel p DirectionalCoupler.Port.leftSecond)))
    hAssembly'
  rw [incidentAssembly_apply_coupler_leftSecond,
    scatteringEquation_propagation_right p incident outgoing hScattering] at hCouplerLeft
  have hPropagationLeft := congrArg
    (fun state => state (Incident.mk (propagationChannel p MatchedPropagation.Port.left)))
    hAssembly'
  rw [incidentAssembly_apply_propagation_left,
    scatteringEquation_coupler_rightSecond p incident outgoing hScattering,
    hInput] at hPropagationLeft
  have hLoop : p.denominator *
      incident (Incident.mk (couplerChannel p DirectionalCoupler.Port.leftSecond)) =
        p.loopCoefficient * DirectionalCoupler.crossCoefficient p.coupler * amplitude := by
    rw [Parameters.denominator, Parameters.loopGain]
    linear_combination hCouplerLeft + p.loopCoefficient * hPropagationLeft
  have hLoopSolution :
      incident (Incident.mk (couplerChannel p DirectionalCoupler.Port.leftSecond)) =
        p.loopCoefficient * DirectionalCoupler.crossCoefficient p.coupler * amplitude /
          p.denominator := by
    apply (eq_div_iff hDenominator).2
    rw [mul_comm, hLoop]
  have hThrough :=
    scatteringEquation_coupler_rightFirst p incident outgoing hScattering
  rw [hInput] at hThrough
  have hReadout := congrArg (fun state => state (Outgoing.mk (throughChannel p))) hOutput
  rw [outputReadout_apply_through] at hReadout
  change
    ((netlist p).responseTransform hWellPosed).toLinearMap
        (inputAmplitude p amplitude) (Outgoing.mk (throughChannel p)) =
      throughTransfer p * amplitude
  rw [show hWellPosed = isWellPosed_of_hasNonzeroDenominator p hDenominator from
      Subsingleton.elim _ _, hReadout, hThrough, hLoopSolution, throughTransfer]
  ring

/-- The input-to-through entry of the N5 response matrix is the all-pass transfer amplitude. -/
theorem responseTransform_entry_through_input (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) :
    (netlist p).responseTransform (isWellPosed_of_hasNonzeroDenominator p hDenominator)
        (Outgoing.mk (throughChannel p)) (Incident.mk (inputChannel p)) =
      throughTransfer p := by
  have hResponse := response_through p hDenominator 1
  simpa [inputAmplitude, Matrix.toLpLin_apply] using hResponse

/-! ## E. Convergent multiple-round-trip view -/

/-- The infinite sum of successive powers of the scalar circulation gain. -/
def roundTripSeries (p : Parameters) : ℂ :=
  ∑' circulation : ℕ, p.loopGain ^ circulation

/-- The round-trip expansion is summable under the explicit contraction gate. -/
lemma summable_roundTripSeries (p : Parameters) (hContractive : p.IsContractive) :
    Summable (fun circulation : ℕ => p.loopGain ^ circulation) :=
  summable_geometric_of_norm_lt_one hContractive

/-- Contraction implies the exact nonzero-denominator gate needed by N5 elimination. -/
lemma Parameters.IsContractive.hasNonzeroDenominator {p : Parameters}
    (hContractive : p.IsContractive) : p.HasNonzeroDenominator := by
  intro hDenominator
  have hDifference : (1 : ℂ) - p.loopGain = 0 := by
    simpa only [Parameters.denominator] using hDenominator
  have hGain : p.loopGain = 1 := (sub_eq_zero.mp hDifference).symm
  rw [Parameters.IsContractive, hGain, norm_one] at hContractive
  exact (lt_irrefl 1) hContractive

/-- The convergent round-trip series sums to the inverse feedback denominator. -/
lemma roundTripSeries_eq_inverse (p : Parameters) (hContractive : p.IsContractive) :
    roundTripSeries p = p.denominator⁻¹ := by
  simpa only [roundTripSeries, Parameters.denominator] using
    (tsum_geometric_of_norm_lt_one hContractive)

/-- The through amplitude obtained by summing all successive loop circulations. -/
def throughTransferSeries (p : Parameters) : ℂ :=
  (p.throughAmplitude : ℂ) +
    DirectionalCoupler.crossCoefficient p.coupler ^ 2 * p.loopCoefficient *
      roundTripSeries p

/-- On the contraction domain, the geometric-series and algebraic-elimination views agree. -/
theorem throughTransfer_eq_roundTripSeries (p : Parameters)
    (hContractive : p.IsContractive) :
    throughTransfer p = throughTransferSeries p := by
  rw [throughTransfer, throughTransferSeries, roundTripSeries_eq_inverse p hContractive,
    div_eq_mul_inv]

/-- The N5 response therefore agrees with the convergent multiple-round-trip expansion. -/
theorem response_through_eq_roundTripSeries (p : Parameters)
    (hContractive : p.IsContractive) (amplitude : ℂ) :
    ((netlist p).responseTransform
          (isWellPosed_of_hasNonzeroDenominator p hContractive.hasNonzeroDenominator)).toLinearMap
        (inputAmplitude p amplitude) (Outgoing.mk (throughChannel p)) =
      throughTransferSeries p * amplitude := by
  rw [response_through p hContractive.hasNonzeroDenominator,
    throughTransfer_eq_roundTripSeries p hContractive]

end AllPass

end

end Optics
