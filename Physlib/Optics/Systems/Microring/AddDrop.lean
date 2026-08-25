/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Systems.Microring.AllPass

/-!
# Add-drop microring feedback networks

## i. Overview

This file constructs a four-port add-drop microring as an explicit `FlatNetlist`. Two physical N7
directional couplers are joined by two physical N7 matched-propagation arcs. All four second-arm
coupler ports participate in the feedback loop; the two first arms remain the input/through and
add/drop buses. The response is obtained from `FlatNetlist.responseTransform`, not stored as a
component behavior.

The N7 component declarations are `DirectionalCoupler.Parameters` and
`DirectionalCoupler.physicalScattering` at
`Physlib/Optics/Components/DirectionalCoupler.lean:62` and
`Physlib/Optics/Components/DirectionalCouplerPhysical.lean:161`, and
`MatchedPropagation.Parameters` and `MatchedPropagation.physicalScattering` at
`Physlib/Optics/Components/MatchedPropagation.lean:79` and
`Physlib/Optics/Components/MatchedPropagationPhysical.lean:167`. In particular, the coupler cross
coefficient is the pinned `-I * k` from
`Physlib/Optics/Components/DirectionalCoupler.lean:68-70`. A source convention using `+I * k` is
related by an arm gauge; this file keeps the N7 sign.

The total round-trip attenuation is split symmetrically as `sqrt a` on each arc, and a chosen real
phase lift is split as `phi / 2` before coercion to `Real.Angle`. This is a modeling choice fixing
the drop-port reference plane; it is not a claim that every physical ring has uniform distributed
loss. The exact N5 solve gate is nonvanishing of the actual two-arc loop denominator.
`roundTripSeries`, `throughTransferSeries`, and `dropTransferSeries` are totalized `tsum`
expressions. They have no convergent-circulation or network-response meaning here without the
stated summability or contraction gate; only the series theorems are gated.

This is a fixed-carrier, single-mode model. Power means normalized modal power. The file makes no
bandwidth, causality, dispersion, group-delay, nonlinear, thermal, material-realization, or
omitted-loss-channel claim. It does not derive through/drop powers, power balance, resonance or
antiresonance extrema, critical coupling, extinction, rejection ratio, parameter recovery, or free
spectral range.

## ii. Key results

- `AddDrop.netlist`: the explicit two-coupler, two-arc feedback network.
- `AddDrop.isWellPosed_iff`: the exact scalar denominator gate.
- `AddDrop.response_through` and `AddDrop.response_drop`: the N5-derived transfer amplitudes.
- `AddDrop.throughTransfer_eq_roundTripSeries` and `AddDrop.dropTransfer_eq_roundTripSeries`:
  equality of algebraic elimination and the convergent circulation series.

## iii. Table of contents

- A. Parameters and algebraic transfer amplitudes
- B. Explicit component family and feedback wiring
- C. External channels and coherent excitation
- D. Exact component and routing equations
- E. Exact well-posedness and N5 response
- F. Convergent multiple-round-trip view

## iv. References

The explicit network construction and its N7-to-N5 derivation are Physlib-original. The resulting
transfer shapes agree with the standard add-drop microring formulas after the declared port,
carrier-phase, and arm-gauge conventions are mapped.
-/

@[expose] public section

namespace Optics

noncomputable section

namespace AddDrop

/-! ## A. Parameters and algebraic transfer amplitudes -/

/-- Fixed-carrier parameters of a symmetric-arc add-drop microring. -/
structure Parameters where
  /-- Same-arm amplitude of the input/through directional coupler. -/
  inputThroughAmplitude : ℝ
  /-- Cross-arm amplitude of the input/through directional coupler. -/
  inputCrossAmplitude : ℝ
  /-- Same-arm amplitude of the add/drop directional coupler. -/
  dropThroughAmplitude : ℝ
  /-- Cross-arm amplitude of the add/drop directional coupler. -/
  dropCrossAmplitude : ℝ
  /-- Retained field-amplitude factor for one complete ring circulation. -/
  fieldAttenuation : ℝ
  /-- A real lift of the phase accumulated in one complete circulation. -/
  roundTripPhase : ℝ

/-- The N7 coupler on the input/through bus. -/
def Parameters.inputCoupler (p : Parameters) : DirectionalCoupler.Parameters where
  throughAmplitude := p.inputThroughAmplitude
  crossAmplitude := p.inputCrossAmplitude

/-- The input coupler projection retains its declared amplitudes. -/
@[simp]
lemma Parameters.inputCoupler_amplitudes (p : Parameters) :
    p.inputCoupler.throughAmplitude = p.inputThroughAmplitude ∧
      p.inputCoupler.crossAmplitude = p.inputCrossAmplitude := ⟨rfl, rfl⟩

/-- The N7 coupler on the add/drop bus. -/
def Parameters.dropCoupler (p : Parameters) : DirectionalCoupler.Parameters where
  throughAmplitude := p.dropThroughAmplitude
  crossAmplitude := p.dropCrossAmplitude

/-- The drop coupler projection retains its declared amplitudes. -/
@[simp]
lemma Parameters.dropCoupler_amplitudes (p : Parameters) :
    p.dropCoupler.throughAmplitude = p.dropThroughAmplitude ∧
      p.dropCoupler.crossAmplitude = p.dropCrossAmplitude := ⟨rfl, rfl⟩

/-- The field-amplitude retention assigned to each of the two symmetric arcs. -/
def Parameters.halfArcAttenuation (p : Parameters) : ℝ :=
  Real.sqrt p.fieldAttenuation

/-- The selected real half-phase lift assigned to each symmetric arc. -/
def Parameters.halfArcPhase (p : Parameters) : Real.Angle :=
  ((p.roundTripPhase / 2 : ℝ) : Real.Angle)

/-- Squaring the symmetric half-arc attenuation recovers a nonnegative round-trip factor. -/
lemma Parameters.halfArcAttenuation_sq (p : Parameters) (hAttenuation : 0 ≤ p.fieldAttenuation) :
    p.halfArcAttenuation ^ 2 = p.fieldAttenuation := by
  rw [Parameters.halfArcAttenuation, pow_two, Real.mul_self_sqrt hAttenuation]

/-- Two symmetric half-phase factors compose to the declared round-trip phase factor. -/
lemma Parameters.halfArcPhase_factor_sq (p : Parameters) :
    MatchedPropagation.carrierPhaseFactor p.halfArcPhase ^ 2 =
      MatchedPropagation.carrierPhaseFactor
        ((p.roundTripPhase : ℝ) : Real.Angle) := by
  rw [pow_two, MatchedPropagation.carrierPhaseFactor,
    MatchedPropagation.carrierPhaseFactor, ← Circle.coe_mul,
    ← Real.Angle.toCircle_add]
  congr 2
  rw [Parameters.halfArcPhase, ← Real.Angle.coe_neg, ← Real.Angle.coe_add,
    ← Real.Angle.coe_neg]
  congr 1
  ring

/-- The N7 propagation parameters on the arc from the input coupler to the drop coupler. -/
def Parameters.firstPropagation (p : Parameters) : MatchedPropagation.Parameters where
  amplitudeTransmission := p.halfArcAttenuation
  carrierPathPhase := p.halfArcPhase

/-- The N7 propagation parameters on the return arc from the drop coupler. -/
def Parameters.secondPropagation (p : Parameters) : MatchedPropagation.Parameters where
  amplitudeTransmission := p.halfArcAttenuation
  carrierPathPhase := p.halfArcPhase

/-- Both propagation projections retain the declared symmetric half-arc data. -/
lemma Parameters.propagation_data (p : Parameters) :
    p.firstPropagation.amplitudeTransmission = p.halfArcAttenuation ∧
      p.secondPropagation.amplitudeTransmission = p.halfArcAttenuation ∧
      p.firstPropagation.carrierPathPhase = p.halfArcPhase ∧
      p.secondPropagation.carrierPathPhase = p.halfArcPhase := ⟨rfl, rfl, rfl, rfl⟩

/-- The complex N7 field coefficient of the first ring arc. -/
def Parameters.firstArcCoefficient (p : Parameters) : ℂ :=
  MatchedPropagation.transmissionCoefficient p.firstPropagation

/-- The complex N7 field coefficient of the second ring arc. -/
def Parameters.secondArcCoefficient (p : Parameters) : ℂ :=
  MatchedPropagation.transmissionCoefficient p.secondPropagation

/-- The complex coefficient accumulated over both propagation arcs. -/
def Parameters.roundTripCoefficient (p : Parameters) : ℂ :=
  p.firstArcCoefficient * p.secondArcCoefficient

/-- The round-trip coefficient is the ordered product of the two N7 arc coefficients. -/
lemma Parameters.roundTripCoefficient_eq (p : Parameters) :
    p.roundTripCoefficient = p.firstArcCoefficient * p.secondArcCoefficient := rfl

/-- For nonnegative attenuation, the two arcs realize the declared round-trip field factor. -/
lemma Parameters.roundTripCoefficient_eq_fieldAttenuation (p : Parameters)
    (hAttenuation : 0 ≤ p.fieldAttenuation) :
    p.roundTripCoefficient =
      (p.fieldAttenuation : ℂ) * MatchedPropagation.carrierPhaseFactor
        ((p.roundTripPhase : ℝ) : Real.Angle) := by
  have hAttenuationSq :
      (p.halfArcAttenuation : ℂ) ^ 2 = (p.fieldAttenuation : ℂ) := by
    exact_mod_cast p.halfArcAttenuation_sq hAttenuation
  rw [Parameters.roundTripCoefficient, Parameters.firstArcCoefficient,
    Parameters.secondArcCoefficient, MatchedPropagation.transmissionCoefficient,
    MatchedPropagation.transmissionCoefficient, Parameters.firstPropagation,
    Parameters.secondPropagation]
  change
    ((p.halfArcAttenuation : ℂ) *
          MatchedPropagation.carrierPhaseFactor p.halfArcPhase) *
        ((p.halfArcAttenuation : ℂ) *
          MatchedPropagation.carrierPhaseFactor p.halfArcPhase) = _
  rw [show
    ((p.halfArcAttenuation : ℂ) *
          MatchedPropagation.carrierPhaseFactor p.halfArcPhase) *
        ((p.halfArcAttenuation : ℂ) *
          MatchedPropagation.carrierPhaseFactor p.halfArcPhase) =
      (p.halfArcAttenuation : ℂ) ^ 2 *
        MatchedPropagation.carrierPhaseFactor p.halfArcPhase ^ 2 by ring]
  rw [hAttenuationSq, p.halfArcPhase_factor_sq]

/-- The scalar gain acquired by one further complete ring circulation. -/
def Parameters.loopGain (p : Parameters) : ℂ :=
  (p.inputThroughAmplitude : ℂ) * (p.dropThroughAmplitude : ℂ) *
    p.roundTripCoefficient

/-- The loop gain expands to the two through amplitudes and both propagation arcs. -/
lemma Parameters.loopGain_eq (p : Parameters) :
    p.loopGain =
      (p.inputThroughAmplitude : ℂ) * (p.dropThroughAmplitude : ℂ) *
        p.firstArcCoefficient * p.secondArcCoefficient := by
  rw [Parameters.loopGain, Parameters.roundTripCoefficient]
  ring

/-- The scalar feedback denominator of the add-drop ring. -/
def Parameters.denominator (p : Parameters) : ℂ :=
  1 - p.loopGain

/-- The denominator expands to `1` minus the complete circulation gain. -/
lemma Parameters.denominator_eq (p : Parameters) :
    p.denominator =
      1 - (p.inputThroughAmplitude : ℂ) * (p.dropThroughAmplitude : ℂ) *
        p.roundTripCoefficient := rfl

/-- The exact algebraic solve gate of the add-drop feedback loop. -/
def Parameters.HasNonzeroDenominator (p : Parameters) : Prop :=
  p.denominator ≠ 0

/-- The named solve gate is exactly nonvanishing of the displayed denominator. -/
lemma Parameters.hasNonzeroDenominator_iff (p : Parameters) :
    p.HasNonzeroDenominator ↔
      1 - (p.inputThroughAmplitude : ℂ) * (p.dropThroughAmplitude : ℂ) *
        p.roundTripCoefficient ≠ 0 := Iff.rfl

/-- The sufficient convergence gate for the multiple-round-trip expansion. -/
def Parameters.IsContractive (p : Parameters) : Prop :=
  ‖p.loopGain‖ < 1

/-- The contraction gate is exactly the norm bound on one full circulation. -/
lemma Parameters.isContractive_iff (p : Parameters) :
    p.IsContractive ↔
      ‖(p.inputThroughAmplitude : ℂ) * (p.dropThroughAmplitude : ℂ) *
        p.roundTripCoefficient‖ < 1 := Iff.rfl

/-- Component validity for the two couplers and two propagation arcs. -/
def Parameters.IsValid (p : Parameters) : Prop :=
  p.inputCoupler.IsValid ∧ p.dropCoupler.IsValid ∧
    p.firstPropagation.IsValid ∧ p.secondPropagation.IsValid

/-- Add-drop validity is exactly the four N7 component-validity predicates. -/
lemma Parameters.isValid_iff (p : Parameters) :
    p.IsValid ↔
      p.inputCoupler.IsValid ∧ p.dropCoupler.IsValid ∧
        p.firstPropagation.IsValid ∧ p.secondPropagation.IsValid := Iff.rfl

/-- The totalized input-to-through algebraic transfer amplitude. -/
def throughTransfer (p : Parameters) : ℂ :=
  (p.inputThroughAmplitude : ℂ) +
    DirectionalCoupler.crossCoefficient p.inputCoupler ^ 2 *
      (p.dropThroughAmplitude : ℂ) * p.roundTripCoefficient / p.denominator

/-- The totalized input-to-drop algebraic transfer amplitude. -/
def dropTransfer (p : Parameters) : ℂ :=
  DirectionalCoupler.crossCoefficient p.inputCoupler *
    DirectionalCoupler.crossCoefficient p.dropCoupler * p.firstArcCoefficient /
      p.denominator

/-- Clearing a nonzero denominator gives the through-transfer numerator identity. -/
lemma throughTransfer_mul_denominator (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) :
    throughTransfer p * p.denominator =
      (p.inputThroughAmplitude : ℂ) * p.denominator +
        DirectionalCoupler.crossCoefficient p.inputCoupler ^ 2 *
          (p.dropThroughAmplitude : ℂ) * p.roundTripCoefficient := by
  rw [throughTransfer, add_mul, div_mul_cancel₀ _ hDenominator]

/-- Clearing a nonzero denominator gives the drop-transfer numerator identity. -/
lemma dropTransfer_mul_denominator (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) :
    dropTransfer p * p.denominator =
      DirectionalCoupler.crossCoefficient p.inputCoupler *
        DirectionalCoupler.crossCoefficient p.dropCoupler * p.firstArcCoefficient := by
  rw [dropTransfer, div_mul_cancel₀ _ hDenominator]

/-- The conventional unitary-input-coupler presentation of the through transfer. -/
def standardThroughTransfer (p : Parameters) : ℂ :=
  ((p.inputThroughAmplitude : ℂ) -
      (p.dropThroughAmplitude : ℂ) * p.roundTripCoefficient) /
    p.denominator

/-- Input-coupler unitarity reduces the through amplitude to the conventional quotient. -/
theorem throughTransfer_eq_standard (p : Parameters)
    (hUnitary : p.inputCoupler.IsUnitary)
    (hDenominator : p.HasNonzeroDenominator) :
    throughTransfer p = standardThroughTransfer p := by
  have hNormalization :
      (p.inputThroughAmplitude : ℂ) ^ 2 + (p.inputCrossAmplitude : ℂ) ^ 2 = 1 := by
    exact_mod_cast hUnitary
  apply mul_right_cancel₀ hDenominator
  rw [throughTransfer_mul_denominator p hDenominator, standardThroughTransfer,
    div_mul_cancel₀ _ hDenominator, Parameters.denominator, Parameters.loopGain]
  change
    (p.inputThroughAmplitude : ℂ) *
          (1 - (p.inputThroughAmplitude : ℂ) *
            (p.dropThroughAmplitude : ℂ) * p.roundTripCoefficient) +
        (-Complex.I * (p.inputCrossAmplitude : ℂ)) ^ 2 *
          (p.dropThroughAmplitude : ℂ) * p.roundTripCoefficient =
      (p.inputThroughAmplitude : ℂ) -
        (p.dropThroughAmplitude : ℂ) * p.roundTripCoefficient
  rw [mul_pow, show (-Complex.I : ℂ) ^ 2 = -1 by norm_num [Complex.I_sq], neg_one_mul]
  linear_combination
    -(p.dropThroughAmplitude : ℂ) * p.roundTripCoefficient * hNormalization

/-- The conventional N7-phase presentation of the input-to-drop transfer. -/
def standardDropTransfer (p : Parameters) : ℂ :=
  -((p.inputCrossAmplitude : ℂ) * (p.dropCrossAmplitude : ℂ) *
      p.firstArcCoefficient) / p.denominator

/-- The two pinned negative-quadrature cross coefficients give the displayed drop sign. -/
theorem dropTransfer_eq_standard (p : Parameters) :
    dropTransfer p = standardDropTransfer p := by
  simp [dropTransfer, standardDropTransfer, DirectionalCoupler.crossCoefficient,
    Parameters.inputCoupler, Parameters.dropCoupler]
  ring_nf
  rw [Complex.I_sq]
  ring

/-! ## B. Explicit component family and feedback wiring -/

/-- The two couplers and two matched-propagation arcs of the add-drop ring. -/
inductive Component
  | inputCoupler
  | dropCoupler
  | firstArc
  | secondArc
  deriving DecidableEq

/-- Add-drop component labels form a finite type. -/
instance : Fintype Component where
  elems := {Component.inputCoupler, Component.dropCoupler, Component.firstArc,
    Component.secondArc}
  complete component := by cases component <;> simp

/-- The owned physical-port family of each add-drop component. -/
def componentPortFamily : Component → PortModeFamily
  | .inputCoupler => DirectionalCoupler.portFamily Unit
  | .dropCoupler => DirectionalCoupler.portFamily Unit
  | .firstArc => MatchedPropagation.portFamily Unit
  | .secondArc => MatchedPropagation.portFamily Unit

/-- The four component port families select the corresponding N7 physical presentations. -/
lemma componentPortFamily_eq :
    componentPortFamily Component.inputCoupler = DirectionalCoupler.portFamily Unit ∧
      componentPortFamily Component.dropCoupler = DirectionalCoupler.portFamily Unit ∧
      componentPortFamily Component.firstArc = MatchedPropagation.portFamily Unit ∧
      componentPortFamily Component.secondArc = MatchedPropagation.portFamily Unit :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The parameterized local scattering law of each add-drop component. -/
def componentScattering (p : Parameters) :
    (component : Component) → ScatteringMatrix (componentPortFamily component).Channel
  | .inputCoupler => DirectionalCoupler.physicalScattering p.inputCoupler Unit
  | .dropCoupler => DirectionalCoupler.physicalScattering p.dropCoupler Unit
  | .firstArc => MatchedPropagation.physicalScattering p.firstPropagation Unit
  | .secondArc => MatchedPropagation.physicalScattering p.secondPropagation Unit

/-- Component scattering selects the four declared N7 scattering matrices. -/
lemma componentScattering_eq (p : Parameters) :
    componentScattering p Component.inputCoupler =
        DirectionalCoupler.physicalScattering p.inputCoupler Unit ∧
      componentScattering p Component.dropCoupler =
        DirectionalCoupler.physicalScattering p.dropCoupler Unit ∧
      componentScattering p Component.firstArc =
        MatchedPropagation.physicalScattering p.firstPropagation Unit ∧
      componentScattering p Component.secondArc =
        MatchedPropagation.physicalScattering p.secondPropagation Unit := ⟨rfl, rfl, rfl, rfl⟩

/-- The four N7 components before the ring wiring is installed. -/
def components (p : Parameters) : ScatteringComponentFamily where
  Component := Component
  portFamily := componentPortFamily
  scattering := componentScattering p

/-- The add-drop component family exposes the declared port and scattering data. -/
lemma components_data (p : Parameters) :
    (components p).portFamily = componentPortFamily ∧
      (components p).scattering = componentScattering p := ⟨rfl, rfl⟩

/-- Concrete add-drop component labels remain finite after projection. -/
noncomputable instance componentsComponentFintype (p : Parameters) :
    Fintype (components p).Component := by
  change Fintype Component
  infer_instance

/-- Concrete add-drop component labels retain decidable equality after projection. -/
noncomputable instance componentsComponentDecidableEq (p : Parameters) :
    DecidableEq (components p).Component := by
  change DecidableEq Component
  infer_instance

/-- The four physical connections around the ring. -/
inductive Connection
  | inputToFirst
  | firstToDrop
  | dropToSecond
  | secondToInput
  deriving DecidableEq

/-- Add-drop connection labels form a finite type. -/
instance : Fintype Connection where
  elems := {Connection.inputToFirst, Connection.firstToDrop, Connection.dropToSecond,
    Connection.secondToInput}
  complete connection := by cases connection <;> simp

/-- The proof-carrying ring connections; both first-arm buses remain external. -/
def connections (p : Parameters) :
    PortConnectionFamily (components p).aggregatePortModeFamily Connection where
  connection
    | .inputToFirst =>
        { left := ⟨Component.inputCoupler, DirectionalCoupler.Port.rightSecond⟩
          right := ⟨Component.firstArc, MatchedPropagation.Port.left⟩
          left_ne_right := by intro h; cases h
          modeEquiv := Equiv.refl Unit }
    | .firstToDrop =>
        { left := ⟨Component.firstArc, MatchedPropagation.Port.right⟩
          right := ⟨Component.dropCoupler, DirectionalCoupler.Port.leftSecond⟩
          left_ne_right := by intro h; cases h
          modeEquiv := Equiv.refl Unit }
    | .dropToSecond =>
        { left := ⟨Component.dropCoupler, DirectionalCoupler.Port.rightSecond⟩
          right := ⟨Component.secondArc, MatchedPropagation.Port.left⟩
          left_ne_right := by intro h; cases h
          modeEquiv := Equiv.refl Unit }
    | .secondToInput =>
        { left := ⟨Component.secondArc, MatchedPropagation.Port.right⟩
          right := ⟨Component.inputCoupler, DirectionalCoupler.Port.leftSecond⟩
          left_ne_right := by intro h; cases h
          modeEquiv := Equiv.refl Unit }
  endpointPort_injective := by
    rintro ⟨firstConnection, firstEnd⟩ ⟨secondConnection, secondEnd⟩ hPort
    cases firstConnection <;> cases firstEnd <;>
      cases secondConnection <;> cases secondEnd
    all_goals first | rfl | cases hPort

/-- The four connection labels select the declared consecutive component pairs. -/
lemma connections_pairs (p : Parameters) :
    ((connections p).connection Connection.inputToFirst).left =
        ⟨Component.inputCoupler, DirectionalCoupler.Port.rightSecond⟩ ∧
      ((connections p).connection Connection.firstToDrop).right =
        ⟨Component.dropCoupler, DirectionalCoupler.Port.leftSecond⟩ ∧
      ((connections p).connection Connection.dropToSecond).right =
        ⟨Component.secondArc, MatchedPropagation.Port.left⟩ ∧
      ((connections p).connection Connection.secondToInput).right =
        ⟨Component.inputCoupler, DirectionalCoupler.Port.leftSecond⟩ :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The explicit add-drop microring flat netlist. -/
def netlist (p : Parameters) : FlatNetlist where
  components := components p
  Connection := Connection
  connections := connections p

/-- The add-drop netlist compiles exactly the declared components and ring wiring. -/
lemma netlist_data (p : Parameters) :
    (netlist p).components = components p ∧ (netlist p).connections = connections p :=
  ⟨rfl, rfl⟩

/-- Every local add-drop component channel family is finite. -/
noncomputable instance localChannelFintype (component : Component) :
    Fintype (componentPortFamily component).Channel := by
  cases component
  · exact DirectionalCoupler.channelFintype
  · exact DirectionalCoupler.channelFintype
  · exact MatchedPropagation.channelFintype
  · exact MatchedPropagation.channelFintype

/-- Every local add-drop component channel family has decidable equality. -/
noncomputable instance localChannelDecidableEq (component : Component) :
    DecidableEq (componentPortFamily component).Channel := by
  cases component
  · exact DirectionalCoupler.channelDecidableEq
  · exact DirectionalCoupler.channelDecidableEq
  · exact MatchedPropagation.channelDecidableEq
  · exact MatchedPropagation.channelDecidableEq

/-- Projected local add-drop channels remain finite. -/
noncomputable instance componentsLocalChannelFintype (p : Parameters)
    (component : (components p).Component) :
    Fintype ((components p).portFamily component).Channel := by
  change Fintype (componentPortFamily component).Channel
  exact localChannelFintype component

/-- Projected local add-drop channels retain decidable equality. -/
noncomputable instance componentsLocalChannelDecidableEq (p : Parameters)
    (component : (components p).Component) :
    DecidableEq ((components p).portFamily component).Channel := by
  change DecidableEq (componentPortFamily component).Channel
  exact localChannelDecidableEq component

/-- The projected aggregate add-drop channel family is finite. -/
noncomputable instance componentsChannelFintype (p : Parameters) :
    Fintype (components p).aggregatePortModeFamily.Channel := by
  letI : Fintype (components p).IndexedChannel := by
    change Fintype (Σ component : Component, (componentPortFamily component).Channel)
    infer_instance
  exact Fintype.ofEquiv (components p).IndexedChannel (components p).channelEquiv

/-- The projected aggregate add-drop channel family has decidable equality. -/
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

/-- Every local channel family exposed by the add-drop netlist is finite. -/
noncomputable instance netlistLocalChannelFintype (p : Parameters)
    (component : (netlist p).components.Component) :
    Fintype ((netlist p).components.portFamily component).Channel := by
  change Fintype (componentPortFamily component).Channel
  exact localChannelFintype component

/-- Every local channel family exposed by the add-drop netlist has decidable equality. -/
noncomputable instance netlistLocalChannelDecidableEq (p : Parameters)
    (component : (netlist p).components.Component) :
    DecidableEq ((netlist p).components.portFamily component).Channel := by
  change DecidableEq (componentPortFamily component).Channel
  exact localChannelDecidableEq component

/-- Aggregate add-drop channels are finite. -/
noncomputable instance channelFintype (p : Parameters) : Fintype (netlist p).Channel := by
  letI : Fintype (components p).IndexedChannel := by
    change Fintype (Σ component : Component, (componentPortFamily component).Channel)
    infer_instance
  exact Fintype.ofEquiv (components p).IndexedChannel (components p).channelEquiv

/-- Aggregate add-drop channels have decidable equality. -/
noncomputable instance channelDecidableEq (p : Parameters) : DecidableEq (netlist p).Channel :=
  Classical.decEq _

/-- Each concrete ring connection carries a finite two-ended local channel family. -/
noncomputable instance connectionLocalChannelFintype (p : Parameters)
    (connection : Connection) :
    Fintype ((connections p).connection connection).LocalChannel := by
  cases connection <;> change Fintype (Unit ⊕ Unit) <;> infer_instance

/-- Internally connected add-drop channels are finite. -/
noncomputable instance connectedChannelFintype (p : Parameters) :
    Fintype (netlist p).ConnectedChannel := by
  change Fintype (connections p).Channel
  infer_instance

/-- Internally connected add-drop channels have decidable equality. -/
noncomputable instance connectedChannelDecidableEq (p : Parameters) :
    DecidableEq (netlist p).ConnectedChannel := Classical.decEq _

/-- External add-drop channels are finite. -/
noncomputable instance externalChannelFintype (p : Parameters) :
    Fintype (netlist p).ExternalChannel :=
  (netlist p).eliminationExternalChannelFintype

/-- The aggregate channel owned by a selected input-coupler port. -/
def inputCouplerChannel (p : Parameters) (port : DirectionalCoupler.Port) :
    (netlist p).Channel :=
  ⟨⟨Component.inputCoupler, port⟩, ()⟩

/-- Distinct input-coupler ports give distinct aggregate channels. -/
lemma inputCouplerChannel_injective (p : Parameters) :
    Function.Injective (inputCouplerChannel p) := by
  intro first second hChannel
  injection hChannel with hPort
  injection hPort

/-- Equality of input-coupler channels is equality of their physical port labels. -/
@[simp]
lemma inputCouplerChannel_eq_iff (p : Parameters) (first second : DirectionalCoupler.Port) :
    inputCouplerChannel p first = inputCouplerChannel p second ↔ first = second := by
  constructor
  · intro hChannel
    exact inputCouplerChannel_injective p hChannel
  · intro hPort
    rw [hPort]

/-- The aggregate channel owned by a selected drop-coupler port. -/
def dropCouplerChannel (p : Parameters) (port : DirectionalCoupler.Port) :
    (netlist p).Channel :=
  ⟨⟨Component.dropCoupler, port⟩, ()⟩

/-- Distinct drop-coupler ports give distinct aggregate channels. -/
lemma dropCouplerChannel_injective (p : Parameters) :
    Function.Injective (dropCouplerChannel p) := by
  intro first second hChannel
  injection hChannel with hPort
  injection hPort

/-- Equality of drop-coupler channels is equality of their physical port labels. -/
@[simp]
lemma dropCouplerChannel_eq_iff (p : Parameters) (first second : DirectionalCoupler.Port) :
    dropCouplerChannel p first = dropCouplerChannel p second ↔ first = second := by
  constructor
  · intro hChannel
    exact dropCouplerChannel_injective p hChannel
  · intro hPort
    rw [hPort]

/-- The aggregate channel owned by a selected first-arc propagation port. -/
def firstArcChannel (p : Parameters) (port : MatchedPropagation.Port) :
    (netlist p).Channel :=
  ⟨⟨Component.firstArc, port⟩, ()⟩

/-- Distinct first-arc ports give distinct aggregate channels. -/
lemma firstArcChannel_injective (p : Parameters) : Function.Injective (firstArcChannel p) := by
  intro first second hChannel
  injection hChannel with hPort
  injection hPort

/-- Equality of first-arc channels is equality of their physical port labels. -/
@[simp]
lemma firstArcChannel_eq_iff (p : Parameters) (first second : MatchedPropagation.Port) :
    firstArcChannel p first = firstArcChannel p second ↔ first = second := by
  constructor
  · intro hChannel
    exact firstArcChannel_injective p hChannel
  · intro hPort
    rw [hPort]

/-- The aggregate channel owned by a selected second-arc propagation port. -/
def secondArcChannel (p : Parameters) (port : MatchedPropagation.Port) :
    (netlist p).Channel :=
  ⟨⟨Component.secondArc, port⟩, ()⟩

/-- Distinct second-arc ports give distinct aggregate channels. -/
lemma secondArcChannel_injective (p : Parameters) : Function.Injective (secondArcChannel p) := by
  intro first second hChannel
  injection hChannel with hPort
  injection hPort

/-- Equality of second-arc channels is equality of their physical port labels. -/
@[simp]
lemma secondArcChannel_eq_iff (p : Parameters) (first second : MatchedPropagation.Port) :
    secondArcChannel p first = secondArcChannel p second ↔ first = second := by
  constructor
  · intro hChannel
    exact secondArcChannel_injective p hChannel
  · intro hPort
    rw [hPort]

/-- Input- and drop-coupler aggregate channels are disjoint. -/
@[simp]
lemma inputCouplerChannel_ne_dropCouplerChannel (p : Parameters)
    (inputPort dropPort : DirectionalCoupler.Port) :
    inputCouplerChannel p inputPort ≠ dropCouplerChannel p dropPort := by
  intro hChannel
  have hComponent := congrArg (fun channel => channel.1.1) hChannel
  cases hComponent

/-- Drop- and input-coupler aggregate channels are disjoint. -/
@[simp]
lemma dropCouplerChannel_ne_inputCouplerChannel (p : Parameters)
    (dropPort inputPort : DirectionalCoupler.Port) :
    dropCouplerChannel p dropPort ≠ inputCouplerChannel p inputPort :=
  Ne.symm (inputCouplerChannel_ne_dropCouplerChannel p inputPort dropPort)

/-- Input-coupler and first-arc aggregate channels are disjoint. -/
@[simp]
lemma inputCouplerChannel_ne_firstArcChannel (p : Parameters)
    (couplerPort : DirectionalCoupler.Port) (arcPort : MatchedPropagation.Port) :
    inputCouplerChannel p couplerPort ≠ firstArcChannel p arcPort := by
  intro hChannel
  have hComponent := congrArg (fun channel => channel.1.1) hChannel
  cases hComponent

/-- First-arc and input-coupler aggregate channels are disjoint. -/
@[simp]
lemma firstArcChannel_ne_inputCouplerChannel (p : Parameters)
    (arcPort : MatchedPropagation.Port) (couplerPort : DirectionalCoupler.Port) :
    firstArcChannel p arcPort ≠ inputCouplerChannel p couplerPort :=
  Ne.symm (inputCouplerChannel_ne_firstArcChannel p couplerPort arcPort)

/-- Input-coupler and second-arc aggregate channels are disjoint. -/
@[simp]
lemma inputCouplerChannel_ne_secondArcChannel (p : Parameters)
    (couplerPort : DirectionalCoupler.Port) (arcPort : MatchedPropagation.Port) :
    inputCouplerChannel p couplerPort ≠ secondArcChannel p arcPort := by
  intro hChannel
  have hComponent := congrArg (fun channel => channel.1.1) hChannel
  cases hComponent

/-- Second-arc and input-coupler aggregate channels are disjoint. -/
@[simp]
lemma secondArcChannel_ne_inputCouplerChannel (p : Parameters)
    (arcPort : MatchedPropagation.Port) (couplerPort : DirectionalCoupler.Port) :
    secondArcChannel p arcPort ≠ inputCouplerChannel p couplerPort :=
  Ne.symm (inputCouplerChannel_ne_secondArcChannel p couplerPort arcPort)

/-- Drop-coupler and first-arc aggregate channels are disjoint. -/
@[simp]
lemma dropCouplerChannel_ne_firstArcChannel (p : Parameters)
    (couplerPort : DirectionalCoupler.Port) (arcPort : MatchedPropagation.Port) :
    dropCouplerChannel p couplerPort ≠ firstArcChannel p arcPort := by
  intro hChannel
  have hComponent := congrArg (fun channel => channel.1.1) hChannel
  cases hComponent

/-- First-arc and drop-coupler aggregate channels are disjoint. -/
@[simp]
lemma firstArcChannel_ne_dropCouplerChannel (p : Parameters)
    (arcPort : MatchedPropagation.Port) (couplerPort : DirectionalCoupler.Port) :
    firstArcChannel p arcPort ≠ dropCouplerChannel p couplerPort :=
  Ne.symm (dropCouplerChannel_ne_firstArcChannel p couplerPort arcPort)

/-- Drop-coupler and second-arc aggregate channels are disjoint. -/
@[simp]
lemma dropCouplerChannel_ne_secondArcChannel (p : Parameters)
    (couplerPort : DirectionalCoupler.Port) (arcPort : MatchedPropagation.Port) :
    dropCouplerChannel p couplerPort ≠ secondArcChannel p arcPort := by
  intro hChannel
  have hComponent := congrArg (fun channel => channel.1.1) hChannel
  cases hComponent

/-- Second-arc and drop-coupler aggregate channels are disjoint. -/
@[simp]
lemma secondArcChannel_ne_dropCouplerChannel (p : Parameters)
    (arcPort : MatchedPropagation.Port) (couplerPort : DirectionalCoupler.Port) :
    secondArcChannel p arcPort ≠ dropCouplerChannel p couplerPort :=
  Ne.symm (dropCouplerChannel_ne_secondArcChannel p couplerPort arcPort)

/-- The two propagation components own disjoint aggregate channels. -/
@[simp]
lemma firstArcChannel_ne_secondArcChannel (p : Parameters)
    (firstPort secondPort : MatchedPropagation.Port) :
    firstArcChannel p firstPort ≠ secondArcChannel p secondPort := by
  intro hChannel
  have hComponent := congrArg (fun channel => channel.1.1) hChannel
  cases hComponent

/-- The reverse ordering of the two propagation-component channel families is disjoint. -/
@[simp]
lemma secondArcChannel_ne_firstArcChannel (p : Parameters)
    (secondPort firstPort : MatchedPropagation.Port) :
    secondArcChannel p secondPort ≠ firstArcChannel p firstPort :=
  Ne.symm (firstArcChannel_ne_secondArcChannel p firstPort secondPort)

/-- The input-coupler left bus port is external to the four ring connections. -/
lemma inputCoupler_leftFirst_not_connected (p : Parameters) :
    inputCouplerChannel p DirectionalCoupler.Port.leftFirst ∉
      Set.range (netlist p).connections.channelEmbedding := by
  rintro ⟨⟨connection, channel⟩, hChannel⟩
  cases connection <;> rcases channel with mode | mode <;> cases mode
  all_goals cases hChannel

/-- The input-coupler right bus port is external to the four ring connections. -/
lemma inputCoupler_rightFirst_not_connected (p : Parameters) :
    inputCouplerChannel p DirectionalCoupler.Port.rightFirst ∉
      Set.range (netlist p).connections.channelEmbedding := by
  rintro ⟨⟨connection, channel⟩, hChannel⟩
  cases connection <;> rcases channel with mode | mode <;> cases mode
  all_goals cases hChannel

/-- The drop-coupler left bus port is external to the four ring connections. -/
lemma dropCoupler_leftFirst_not_connected (p : Parameters) :
    dropCouplerChannel p DirectionalCoupler.Port.leftFirst ∉
      Set.range (netlist p).connections.channelEmbedding := by
  rintro ⟨⟨connection, channel⟩, hChannel⟩
  cases connection <;> rcases channel with mode | mode <;> cases mode
  all_goals cases hChannel

/-- The drop-coupler right bus port is external to the four ring connections. -/
lemma dropCoupler_rightFirst_not_connected (p : Parameters) :
    dropCouplerChannel p DirectionalCoupler.Port.rightFirst ∉
      Set.range (netlist p).connections.channelEmbedding := by
  rintro ⟨⟨connection, channel⟩, hChannel⟩
  cases connection <;> rcases channel with mode | mode <;> cases mode
  all_goals cases hChannel

/-! ## C. External channels and coherent excitation -/

/-- The packaged external input channel on the first bus. -/
def inputChannel (p : Parameters) : (netlist p).ExternalChannel :=
  ⟨inputCouplerChannel p DirectionalCoupler.Port.leftFirst,
    inputCoupler_leftFirst_not_connected p⟩

/-- The packaged external through channel on the first bus. -/
def throughChannel (p : Parameters) : (netlist p).ExternalChannel :=
  ⟨inputCouplerChannel p DirectionalCoupler.Port.rightFirst,
    inputCoupler_rightFirst_not_connected p⟩

/-- The packaged external add channel on the second bus. -/
def addChannel (p : Parameters) : (netlist p).ExternalChannel :=
  ⟨dropCouplerChannel p DirectionalCoupler.Port.leftFirst,
    dropCoupler_leftFirst_not_connected p⟩

/-- The packaged external drop channel on the second bus. -/
def dropChannel (p : Parameters) : (netlist p).ExternalChannel :=
  ⟨dropCouplerChannel p DirectionalCoupler.Port.rightFirst,
    dropCoupler_rightFirst_not_connected p⟩

/-- The input and through external channels are distinct. -/
lemma inputChannel_ne_throughChannel (p : Parameters) : inputChannel p ≠ throughChannel p := by
  intro hChannel
  have hPort := inputCouplerChannel_injective p (congrArg Subtype.val hChannel)
  cases hPort

/-- The input and add external channels belong to different physical couplers. -/
lemma inputChannel_ne_addChannel (p : Parameters) : inputChannel p ≠ addChannel p := by
  intro hChannel
  have hValue := congrArg Subtype.val hChannel
  cases hValue

/-- The input and drop external channels belong to different physical couplers. -/
lemma inputChannel_ne_dropChannel (p : Parameters) : inputChannel p ≠ dropChannel p := by
  intro hChannel
  have hValue := congrArg Subtype.val hChannel
  cases hValue

/-- A coherent scalar amplitude injected only at the first-bus input. -/
def inputAmplitude (p : Parameters) (amplitude : ℂ) :
    ModeAmplitude (netlist p).ExternalIncident :=
  PiLp.single 2 (Incident.mk (inputChannel p)) amplitude

/-- The coherent input has its supplied value at the input channel. -/
@[simp]
lemma inputAmplitude_apply_input (p : Parameters) (amplitude : ℂ) :
    inputAmplitude p amplitude (Incident.mk (inputChannel p)) = amplitude := by
  simp [inputAmplitude]

/-- The coherent input vanishes at the through-side incident channel. -/
@[simp]
lemma inputAmplitude_apply_through (p : Parameters) (amplitude : ℂ) :
    inputAmplitude p amplitude (Incident.mk (throughChannel p)) = 0 := by
  rw [inputAmplitude]
  simp [Ne.symm (inputChannel_ne_throughChannel p)]

/-- The coherent input vanishes at the add-side incident channel. -/
@[simp]
lemma inputAmplitude_apply_add (p : Parameters) (amplitude : ℂ) :
    inputAmplitude p amplitude (Incident.mk (addChannel p)) = 0 := by
  rw [inputAmplitude]
  simp [Ne.symm (inputChannel_ne_addChannel p)]

/-- The coherent input vanishes at the drop-side incident channel. -/
@[simp]
lemma inputAmplitude_apply_drop (p : Parameters) (amplitude : ℂ) :
    inputAmplitude p amplitude (Incident.mk (dropChannel p)) = 0 := by
  rw [inputAmplitude]
  simp [Ne.symm (inputChannel_ne_dropChannel p)]

/-! ## D. Exact component and routing equations -/

/-- The input-coupler restriction satisfies the corresponding N7 physical behavior. -/
lemma inputCoupler_physicalBehavior_of_scatteringEquation (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident) :
    (incident.restrictEmbedding
          (Incident.relabelEmbedding
            ((components p).componentChannelEmbedding Component.inputCoupler)),
      outgoing.restrictEmbedding
          (Outgoing.relabelEmbedding
            ((components p).componentChannelEmbedding Component.inputCoupler))) ∈
        DirectionalCoupler.physicalBehavior p.inputCoupler := by
  have hMember : (incident, outgoing) ∈ (netlist p).componentBehavior :=
    ((netlist p).mem_componentBehavior_iff incident outgoing).mpr hScattering
  have hLocal :=
    ((netlist p).mem_componentBehavior_iff_forall_component incident outgoing).mp
      hMember Component.inputCoupler
  change
    (incident.restrictEmbedding
          (Incident.relabelEmbedding
            ((components p).componentChannelEmbedding Component.inputCoupler)),
      outgoing.restrictEmbedding
          (Outgoing.relabelEmbedding
            ((components p).componentChannelEmbedding Component.inputCoupler))) ∈
        ModeTransform.toBehavior
          (ScatteringMatrix.toOrientedModeTransform
            (DirectionalCoupler.physicalScattering p.inputCoupler Unit)) at hLocal
  rw [DirectionalCoupler.physicalScattering_realizes_physicalBehavior] at hLocal
  exact hLocal

/-- The drop-coupler restriction satisfies the corresponding N7 physical behavior. -/
lemma dropCoupler_physicalBehavior_of_scatteringEquation (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident) :
    (incident.restrictEmbedding
          (Incident.relabelEmbedding
            ((components p).componentChannelEmbedding Component.dropCoupler)),
      outgoing.restrictEmbedding
          (Outgoing.relabelEmbedding
            ((components p).componentChannelEmbedding Component.dropCoupler))) ∈
        DirectionalCoupler.physicalBehavior p.dropCoupler := by
  have hMember : (incident, outgoing) ∈ (netlist p).componentBehavior :=
    ((netlist p).mem_componentBehavior_iff incident outgoing).mpr hScattering
  have hLocal :=
    ((netlist p).mem_componentBehavior_iff_forall_component incident outgoing).mp
      hMember Component.dropCoupler
  change
    (incident.restrictEmbedding
          (Incident.relabelEmbedding
            ((components p).componentChannelEmbedding Component.dropCoupler)),
      outgoing.restrictEmbedding
          (Outgoing.relabelEmbedding
            ((components p).componentChannelEmbedding Component.dropCoupler))) ∈
        ModeTransform.toBehavior
          (ScatteringMatrix.toOrientedModeTransform
            (DirectionalCoupler.physicalScattering p.dropCoupler Unit)) at hLocal
  rw [DirectionalCoupler.physicalScattering_realizes_physicalBehavior] at hLocal
  exact hLocal

/-- The first-arc restriction satisfies the corresponding N7 physical behavior. -/
lemma firstArc_physicalBehavior_of_scatteringEquation (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident) :
    (incident.restrictEmbedding
          (Incident.relabelEmbedding
            ((components p).componentChannelEmbedding Component.firstArc)),
      outgoing.restrictEmbedding
          (Outgoing.relabelEmbedding
            ((components p).componentChannelEmbedding Component.firstArc))) ∈
        MatchedPropagation.physicalBehavior p.firstPropagation := by
  have hMember : (incident, outgoing) ∈ (netlist p).componentBehavior :=
    ((netlist p).mem_componentBehavior_iff incident outgoing).mpr hScattering
  have hLocal :=
    ((netlist p).mem_componentBehavior_iff_forall_component incident outgoing).mp
      hMember Component.firstArc
  change
    (incident.restrictEmbedding
          (Incident.relabelEmbedding
            ((components p).componentChannelEmbedding Component.firstArc)),
      outgoing.restrictEmbedding
          (Outgoing.relabelEmbedding
            ((components p).componentChannelEmbedding Component.firstArc))) ∈
        ModeTransform.toBehavior
          (ScatteringMatrix.toOrientedModeTransform
            (MatchedPropagation.physicalScattering p.firstPropagation Unit)) at hLocal
  rw [MatchedPropagation.physicalScattering_realizes_physicalBehavior] at hLocal
  exact hLocal

/-- The second-arc restriction satisfies the corresponding N7 physical behavior. -/
lemma secondArc_physicalBehavior_of_scatteringEquation (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident) :
    (incident.restrictEmbedding
          (Incident.relabelEmbedding
            ((components p).componentChannelEmbedding Component.secondArc)),
      outgoing.restrictEmbedding
          (Outgoing.relabelEmbedding
            ((components p).componentChannelEmbedding Component.secondArc))) ∈
        MatchedPropagation.physicalBehavior p.secondPropagation := by
  have hMember : (incident, outgoing) ∈ (netlist p).componentBehavior :=
    ((netlist p).mem_componentBehavior_iff incident outgoing).mpr hScattering
  have hLocal :=
    ((netlist p).mem_componentBehavior_iff_forall_component incident outgoing).mp
      hMember Component.secondArc
  change
    (incident.restrictEmbedding
          (Incident.relabelEmbedding
            ((components p).componentChannelEmbedding Component.secondArc)),
      outgoing.restrictEmbedding
          (Outgoing.relabelEmbedding
            ((components p).componentChannelEmbedding Component.secondArc))) ∈
        ModeTransform.toBehavior
          (ScatteringMatrix.toOrientedModeTransform
            (MatchedPropagation.physicalScattering p.secondPropagation Unit)) at hLocal
  rw [MatchedPropagation.physicalScattering_realizes_physicalBehavior] at hLocal
  exact hLocal

/-- A global scattering equation gives the input-coupler through-bus coordinate law. -/
lemma scatteringEquation_inputCoupler_rightFirst (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident) :
    outgoing (Outgoing.mk
        (inputCouplerChannel p DirectionalCoupler.Port.rightFirst)) =
      (p.inputThroughAmplitude : ℂ) *
          incident (Incident.mk
            (inputCouplerChannel p DirectionalCoupler.Port.leftFirst)) +
        DirectionalCoupler.crossCoefficient p.inputCoupler *
          incident (Incident.mk
            (inputCouplerChannel p DirectionalCoupler.Port.leftSecond)) := by
  have hPhysical :=
    inputCoupler_physicalBehavior_of_scatteringEquation p incident outgoing hScattering
  have hRaw :=
    (DirectionalCoupler.mem_physicalBehavior_iff p.inputCoupler _ _).mp hPhysical
  rw [DirectionalCoupler.mem_behavior_iff,
    DirectionalCoupler.mixing_toLinearMap_apply,
    DirectionalCoupler.mixing_toLinearMap_apply] at hRaw
  have hCoordinate := congrArg
    (fun amplitude => amplitude (Sum.inr (Outgoing.mk (Sum.inl ())))) hRaw
  change
    outgoing (Outgoing.mk
        (inputCouplerChannel p DirectionalCoupler.Port.rightFirst)) =
      (p.inputThroughAmplitude : ℂ) *
          incident (Incident.mk
            (inputCouplerChannel p DirectionalCoupler.Port.leftFirst)) +
        DirectionalCoupler.crossCoefficient p.inputCoupler *
          incident (Incident.mk
            (inputCouplerChannel p DirectionalCoupler.Port.leftSecond)) at hCoordinate
  exact hCoordinate

/-- A global scattering equation gives the input coupler's forward ring coordinate law. -/
lemma scatteringEquation_inputCoupler_rightSecond (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident) :
    outgoing (Outgoing.mk
        (inputCouplerChannel p DirectionalCoupler.Port.rightSecond)) =
      DirectionalCoupler.crossCoefficient p.inputCoupler *
          incident (Incident.mk
            (inputCouplerChannel p DirectionalCoupler.Port.leftFirst)) +
        (p.inputThroughAmplitude : ℂ) *
          incident (Incident.mk
            (inputCouplerChannel p DirectionalCoupler.Port.leftSecond)) := by
  have hPhysical :=
    inputCoupler_physicalBehavior_of_scatteringEquation p incident outgoing hScattering
  have hRaw :=
    (DirectionalCoupler.mem_physicalBehavior_iff p.inputCoupler _ _).mp hPhysical
  rw [DirectionalCoupler.mem_behavior_iff,
    DirectionalCoupler.mixing_toLinearMap_apply,
    DirectionalCoupler.mixing_toLinearMap_apply] at hRaw
  have hCoordinate := congrArg
    (fun amplitude => amplitude (Sum.inr (Outgoing.mk (Sum.inr ())))) hRaw
  change
    outgoing (Outgoing.mk
        (inputCouplerChannel p DirectionalCoupler.Port.rightSecond)) =
      DirectionalCoupler.crossCoefficient p.inputCoupler *
          incident (Incident.mk
            (inputCouplerChannel p DirectionalCoupler.Port.leftFirst)) +
        (p.inputThroughAmplitude : ℂ) *
          incident (Incident.mk
            (inputCouplerChannel p DirectionalCoupler.Port.leftSecond)) at hCoordinate
  exact hCoordinate

/-- A global scattering equation gives the input coupler's reverse ring coordinate law. -/
lemma scatteringEquation_inputCoupler_leftSecond (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident) :
    outgoing (Outgoing.mk
        (inputCouplerChannel p DirectionalCoupler.Port.leftSecond)) =
      DirectionalCoupler.crossCoefficient p.inputCoupler *
          incident (Incident.mk
            (inputCouplerChannel p DirectionalCoupler.Port.rightFirst)) +
        (p.inputThroughAmplitude : ℂ) *
          incident (Incident.mk
            (inputCouplerChannel p DirectionalCoupler.Port.rightSecond)) := by
  have hPhysical :=
    inputCoupler_physicalBehavior_of_scatteringEquation p incident outgoing hScattering
  have hRaw :=
    (DirectionalCoupler.mem_physicalBehavior_iff p.inputCoupler _ _).mp hPhysical
  rw [DirectionalCoupler.mem_behavior_iff,
    DirectionalCoupler.mixing_toLinearMap_apply,
    DirectionalCoupler.mixing_toLinearMap_apply] at hRaw
  have hCoordinate := congrArg
    (fun amplitude => amplitude (Sum.inl (Outgoing.mk (Sum.inr ())))) hRaw
  change
    outgoing (Outgoing.mk
        (inputCouplerChannel p DirectionalCoupler.Port.leftSecond)) =
      DirectionalCoupler.crossCoefficient p.inputCoupler *
          incident (Incident.mk
            (inputCouplerChannel p DirectionalCoupler.Port.rightFirst)) +
        (p.inputThroughAmplitude : ℂ) *
          incident (Incident.mk
            (inputCouplerChannel p DirectionalCoupler.Port.rightSecond)) at hCoordinate
  exact hCoordinate

/-- A global scattering equation gives the drop-coupler drop-bus coordinate law. -/
lemma scatteringEquation_dropCoupler_rightFirst (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident) :
    outgoing (Outgoing.mk
        (dropCouplerChannel p DirectionalCoupler.Port.rightFirst)) =
      (p.dropThroughAmplitude : ℂ) *
          incident (Incident.mk
            (dropCouplerChannel p DirectionalCoupler.Port.leftFirst)) +
        DirectionalCoupler.crossCoefficient p.dropCoupler *
          incident (Incident.mk
            (dropCouplerChannel p DirectionalCoupler.Port.leftSecond)) := by
  have hPhysical :=
    dropCoupler_physicalBehavior_of_scatteringEquation p incident outgoing hScattering
  have hRaw :=
    (DirectionalCoupler.mem_physicalBehavior_iff p.dropCoupler _ _).mp hPhysical
  rw [DirectionalCoupler.mem_behavior_iff,
    DirectionalCoupler.mixing_toLinearMap_apply,
    DirectionalCoupler.mixing_toLinearMap_apply] at hRaw
  have hCoordinate := congrArg
    (fun amplitude => amplitude (Sum.inr (Outgoing.mk (Sum.inl ())))) hRaw
  change
    outgoing (Outgoing.mk
        (dropCouplerChannel p DirectionalCoupler.Port.rightFirst)) =
      (p.dropThroughAmplitude : ℂ) *
          incident (Incident.mk
            (dropCouplerChannel p DirectionalCoupler.Port.leftFirst)) +
        DirectionalCoupler.crossCoefficient p.dropCoupler *
          incident (Incident.mk
            (dropCouplerChannel p DirectionalCoupler.Port.leftSecond)) at hCoordinate
  exact hCoordinate

/-- A global scattering equation gives the drop coupler's forward ring coordinate law. -/
lemma scatteringEquation_dropCoupler_rightSecond (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident) :
    outgoing (Outgoing.mk
        (dropCouplerChannel p DirectionalCoupler.Port.rightSecond)) =
      DirectionalCoupler.crossCoefficient p.dropCoupler *
          incident (Incident.mk
            (dropCouplerChannel p DirectionalCoupler.Port.leftFirst)) +
        (p.dropThroughAmplitude : ℂ) *
          incident (Incident.mk
            (dropCouplerChannel p DirectionalCoupler.Port.leftSecond)) := by
  have hPhysical :=
    dropCoupler_physicalBehavior_of_scatteringEquation p incident outgoing hScattering
  have hRaw :=
    (DirectionalCoupler.mem_physicalBehavior_iff p.dropCoupler _ _).mp hPhysical
  rw [DirectionalCoupler.mem_behavior_iff,
    DirectionalCoupler.mixing_toLinearMap_apply,
    DirectionalCoupler.mixing_toLinearMap_apply] at hRaw
  have hCoordinate := congrArg
    (fun amplitude => amplitude (Sum.inr (Outgoing.mk (Sum.inr ())))) hRaw
  change
    outgoing (Outgoing.mk
        (dropCouplerChannel p DirectionalCoupler.Port.rightSecond)) =
      DirectionalCoupler.crossCoefficient p.dropCoupler *
          incident (Incident.mk
            (dropCouplerChannel p DirectionalCoupler.Port.leftFirst)) +
        (p.dropThroughAmplitude : ℂ) *
          incident (Incident.mk
            (dropCouplerChannel p DirectionalCoupler.Port.leftSecond)) at hCoordinate
  exact hCoordinate

/-- A global scattering equation gives the drop coupler's reverse ring coordinate law. -/
lemma scatteringEquation_dropCoupler_leftSecond (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident) :
    outgoing (Outgoing.mk
        (dropCouplerChannel p DirectionalCoupler.Port.leftSecond)) =
      DirectionalCoupler.crossCoefficient p.dropCoupler *
          incident (Incident.mk
            (dropCouplerChannel p DirectionalCoupler.Port.rightFirst)) +
        (p.dropThroughAmplitude : ℂ) *
          incident (Incident.mk
            (dropCouplerChannel p DirectionalCoupler.Port.rightSecond)) := by
  have hPhysical :=
    dropCoupler_physicalBehavior_of_scatteringEquation p incident outgoing hScattering
  have hRaw :=
    (DirectionalCoupler.mem_physicalBehavior_iff p.dropCoupler _ _).mp hPhysical
  rw [DirectionalCoupler.mem_behavior_iff,
    DirectionalCoupler.mixing_toLinearMap_apply,
    DirectionalCoupler.mixing_toLinearMap_apply] at hRaw
  have hCoordinate := congrArg
    (fun amplitude => amplitude (Sum.inl (Outgoing.mk (Sum.inr ())))) hRaw
  change
    outgoing (Outgoing.mk
        (dropCouplerChannel p DirectionalCoupler.Port.leftSecond)) =
      DirectionalCoupler.crossCoefficient p.dropCoupler *
          incident (Incident.mk
            (dropCouplerChannel p DirectionalCoupler.Port.rightFirst)) +
        (p.dropThroughAmplitude : ℂ) *
          incident (Incident.mk
            (dropCouplerChannel p DirectionalCoupler.Port.rightSecond)) at hCoordinate
  exact hCoordinate

/-- A global scattering equation gives forward propagation through the first arc. -/
lemma scatteringEquation_firstArc_right (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident) :
    outgoing (Outgoing.mk (firstArcChannel p MatchedPropagation.Port.right)) =
      p.firstArcCoefficient *
        incident (Incident.mk (firstArcChannel p MatchedPropagation.Port.left)) := by
  have hPhysical :=
    firstArc_physicalBehavior_of_scatteringEquation p incident outgoing hScattering
  have hRaw :=
    (MatchedPropagation.mem_physicalBehavior_iff p.firstPropagation _ _).mp hPhysical
  rw [MatchedPropagation.mem_behavior_iff] at hRaw
  have hCoordinate := congrArg
    (fun amplitude => amplitude (Sum.inr (Outgoing.mk ()))) hRaw
  change
    outgoing (Outgoing.mk (firstArcChannel p MatchedPropagation.Port.right)) =
      p.firstArcCoefficient *
        incident (Incident.mk (firstArcChannel p MatchedPropagation.Port.left)) at hCoordinate
  exact hCoordinate

/-- A global scattering equation gives reverse propagation through the first arc. -/
lemma scatteringEquation_firstArc_left (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident) :
    outgoing (Outgoing.mk (firstArcChannel p MatchedPropagation.Port.left)) =
      p.firstArcCoefficient *
        incident (Incident.mk (firstArcChannel p MatchedPropagation.Port.right)) := by
  have hPhysical :=
    firstArc_physicalBehavior_of_scatteringEquation p incident outgoing hScattering
  have hRaw :=
    (MatchedPropagation.mem_physicalBehavior_iff p.firstPropagation _ _).mp hPhysical
  rw [MatchedPropagation.mem_behavior_iff] at hRaw
  have hCoordinate := congrArg
    (fun amplitude => amplitude (Sum.inl (Outgoing.mk ()))) hRaw
  change
    outgoing (Outgoing.mk (firstArcChannel p MatchedPropagation.Port.left)) =
      p.firstArcCoefficient *
        incident (Incident.mk (firstArcChannel p MatchedPropagation.Port.right)) at hCoordinate
  exact hCoordinate

/-- A global scattering equation gives forward propagation through the second arc. -/
lemma scatteringEquation_secondArc_right (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident) :
    outgoing (Outgoing.mk (secondArcChannel p MatchedPropagation.Port.right)) =
      p.secondArcCoefficient *
        incident (Incident.mk (secondArcChannel p MatchedPropagation.Port.left)) := by
  have hPhysical :=
    secondArc_physicalBehavior_of_scatteringEquation p incident outgoing hScattering
  have hRaw :=
    (MatchedPropagation.mem_physicalBehavior_iff p.secondPropagation _ _).mp hPhysical
  rw [MatchedPropagation.mem_behavior_iff] at hRaw
  have hCoordinate := congrArg
    (fun amplitude => amplitude (Sum.inr (Outgoing.mk ()))) hRaw
  change
    outgoing (Outgoing.mk (secondArcChannel p MatchedPropagation.Port.right)) =
      p.secondArcCoefficient *
        incident (Incident.mk (secondArcChannel p MatchedPropagation.Port.left)) at hCoordinate
  exact hCoordinate

/-- A global scattering equation gives reverse propagation through the second arc. -/
lemma scatteringEquation_secondArc_left (p : Parameters)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident) :
    outgoing (Outgoing.mk (secondArcChannel p MatchedPropagation.Port.left)) =
      p.secondArcCoefficient *
        incident (Incident.mk (secondArcChannel p MatchedPropagation.Port.right)) := by
  have hPhysical :=
    secondArc_physicalBehavior_of_scatteringEquation p incident outgoing hScattering
  have hRaw :=
    (MatchedPropagation.mem_physicalBehavior_iff p.secondPropagation _ _).mp hPhysical
  rw [MatchedPropagation.mem_behavior_iff] at hRaw
  have hCoordinate := congrArg
    (fun amplitude => amplitude (Sum.inl (Outgoing.mk ()))) hRaw
  change
    outgoing (Outgoing.mk (secondArcChannel p MatchedPropagation.Port.left)) =
      p.secondArcCoefficient *
        incident (Incident.mk (secondArcChannel p MatchedPropagation.Port.right)) at hCoordinate
  exact hCoordinate

/-- Incident assembly returns the supplied first-bus input amplitude. -/
lemma incidentAssembly_apply_input_leftFirst (p : Parameters)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (external : ModeAmplitude (netlist p).ExternalIncident) :
    (netlist p).connections.incidentAssembly outgoing external
        (Incident.mk
          (inputCouplerChannel p DirectionalCoupler.Port.leftFirst)) =
      external (Incident.mk (inputChannel p)) := by
  exact (netlist p).connections.incidentAssembly_apply_external
    outgoing external (inputChannel p)

/-- Incident assembly returns the supplied through-side incident amplitude. -/
lemma incidentAssembly_apply_input_rightFirst (p : Parameters)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (external : ModeAmplitude (netlist p).ExternalIncident) :
    (netlist p).connections.incidentAssembly outgoing external
        (Incident.mk
          (inputCouplerChannel p DirectionalCoupler.Port.rightFirst)) =
      external (Incident.mk (throughChannel p)) := by
  exact (netlist p).connections.incidentAssembly_apply_external
    outgoing external (throughChannel p)

/-- Incident assembly returns the supplied add-side incident amplitude. -/
lemma incidentAssembly_apply_drop_leftFirst (p : Parameters)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (external : ModeAmplitude (netlist p).ExternalIncident) :
    (netlist p).connections.incidentAssembly outgoing external
        (Incident.mk
          (dropCouplerChannel p DirectionalCoupler.Port.leftFirst)) =
      external (Incident.mk (addChannel p)) := by
  exact (netlist p).connections.incidentAssembly_apply_external
    outgoing external (addChannel p)

/-- Incident assembly returns the supplied drop-side incident amplitude. -/
lemma incidentAssembly_apply_drop_rightFirst (p : Parameters)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (external : ModeAmplitude (netlist p).ExternalIncident) :
    (netlist p).connections.incidentAssembly outgoing external
        (Incident.mk
          (dropCouplerChannel p DirectionalCoupler.Port.rightFirst)) =
      external (Incident.mk (dropChannel p)) := by
  exact (netlist p).connections.incidentAssembly_apply_external
    outgoing external (dropChannel p)

/-- The input coupler's right ring input is routed from the first arc's left output. -/
lemma incidentAssembly_apply_inputCoupler_rightSecond (p : Parameters)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (external : ModeAmplitude (netlist p).ExternalIncident) :
    (netlist p).connections.incidentAssembly outgoing external
        (Incident.mk
          (inputCouplerChannel p DirectionalCoupler.Port.rightSecond)) =
      outgoing (Outgoing.mk (firstArcChannel p MatchedPropagation.Port.left)) := by
  change
    (netlist p).connections.incidentAssembly outgoing external
        (Incident.mk ((netlist p).connections.channelEmbedding
          ⟨Connection.inputToFirst, Sum.inl ()⟩)) = _
  rw [(netlist p).connections.incidentAssembly_apply_connected_channel]
  rfl

/-- The first arc's left input is routed from the input coupler's right ring output. -/
lemma incidentAssembly_apply_firstArc_left (p : Parameters)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (external : ModeAmplitude (netlist p).ExternalIncident) :
    (netlist p).connections.incidentAssembly outgoing external
        (Incident.mk (firstArcChannel p MatchedPropagation.Port.left)) =
      outgoing (Outgoing.mk
        (inputCouplerChannel p DirectionalCoupler.Port.rightSecond)) := by
  change
    (netlist p).connections.incidentAssembly outgoing external
        (Incident.mk ((netlist p).connections.channelEmbedding
          ⟨Connection.inputToFirst, Sum.inr ()⟩)) = _
  rw [(netlist p).connections.incidentAssembly_apply_connected_channel]
  rfl

/-- The first arc's right input is routed from the drop coupler's left ring output. -/
lemma incidentAssembly_apply_firstArc_right (p : Parameters)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (external : ModeAmplitude (netlist p).ExternalIncident) :
    (netlist p).connections.incidentAssembly outgoing external
        (Incident.mk (firstArcChannel p MatchedPropagation.Port.right)) =
      outgoing (Outgoing.mk
        (dropCouplerChannel p DirectionalCoupler.Port.leftSecond)) := by
  change
    (netlist p).connections.incidentAssembly outgoing external
        (Incident.mk ((netlist p).connections.channelEmbedding
          ⟨Connection.firstToDrop, Sum.inl ()⟩)) = _
  rw [(netlist p).connections.incidentAssembly_apply_connected_channel]
  rfl

/-- The drop coupler's left ring input is routed from the first arc's right output. -/
lemma incidentAssembly_apply_dropCoupler_leftSecond (p : Parameters)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (external : ModeAmplitude (netlist p).ExternalIncident) :
    (netlist p).connections.incidentAssembly outgoing external
        (Incident.mk
          (dropCouplerChannel p DirectionalCoupler.Port.leftSecond)) =
      outgoing (Outgoing.mk (firstArcChannel p MatchedPropagation.Port.right)) := by
  change
    (netlist p).connections.incidentAssembly outgoing external
        (Incident.mk ((netlist p).connections.channelEmbedding
          ⟨Connection.firstToDrop, Sum.inr ()⟩)) = _
  rw [(netlist p).connections.incidentAssembly_apply_connected_channel]
  rfl

/-- The drop coupler's right ring input is routed from the second arc's left output. -/
lemma incidentAssembly_apply_dropCoupler_rightSecond (p : Parameters)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (external : ModeAmplitude (netlist p).ExternalIncident) :
    (netlist p).connections.incidentAssembly outgoing external
        (Incident.mk
          (dropCouplerChannel p DirectionalCoupler.Port.rightSecond)) =
      outgoing (Outgoing.mk (secondArcChannel p MatchedPropagation.Port.left)) := by
  change
    (netlist p).connections.incidentAssembly outgoing external
        (Incident.mk ((netlist p).connections.channelEmbedding
          ⟨Connection.dropToSecond, Sum.inl ()⟩)) = _
  rw [(netlist p).connections.incidentAssembly_apply_connected_channel]
  rfl

/-- The second arc's left input is routed from the drop coupler's right ring output. -/
lemma incidentAssembly_apply_secondArc_left (p : Parameters)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (external : ModeAmplitude (netlist p).ExternalIncident) :
    (netlist p).connections.incidentAssembly outgoing external
        (Incident.mk (secondArcChannel p MatchedPropagation.Port.left)) =
      outgoing (Outgoing.mk
        (dropCouplerChannel p DirectionalCoupler.Port.rightSecond)) := by
  change
    (netlist p).connections.incidentAssembly outgoing external
        (Incident.mk ((netlist p).connections.channelEmbedding
          ⟨Connection.dropToSecond, Sum.inr ()⟩)) = _
  rw [(netlist p).connections.incidentAssembly_apply_connected_channel]
  rfl

/-- The second arc's right input is routed from the input coupler's left ring output. -/
lemma incidentAssembly_apply_secondArc_right (p : Parameters)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (external : ModeAmplitude (netlist p).ExternalIncident) :
    (netlist p).connections.incidentAssembly outgoing external
        (Incident.mk (secondArcChannel p MatchedPropagation.Port.right)) =
      outgoing (Outgoing.mk
        (inputCouplerChannel p DirectionalCoupler.Port.leftSecond)) := by
  change
    (netlist p).connections.incidentAssembly outgoing external
        (Incident.mk ((netlist p).connections.channelEmbedding
          ⟨Connection.secondToInput, Sum.inl ()⟩)) = _
  rw [(netlist p).connections.incidentAssembly_apply_connected_channel]
  rfl

/-- The input coupler's left ring input is routed from the second arc's right output. -/
lemma incidentAssembly_apply_inputCoupler_leftSecond (p : Parameters)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (external : ModeAmplitude (netlist p).ExternalIncident) :
    (netlist p).connections.incidentAssembly outgoing external
        (Incident.mk
          (inputCouplerChannel p DirectionalCoupler.Port.leftSecond)) =
      outgoing (Outgoing.mk (secondArcChannel p MatchedPropagation.Port.right)) := by
  change
    (netlist p).connections.incidentAssembly outgoing external
        (Incident.mk ((netlist p).connections.channelEmbedding
          ⟨Connection.secondToInput, Sum.inr ()⟩)) = _
  rw [(netlist p).connections.incidentAssembly_apply_connected_channel]
  rfl

/-! ## E. Exact well-posedness and N5 response -/

/-- The forward-circulating input-coupler coordinate vanishes in a homogeneous fixed point. -/
lemma forwardLoop_inputCoupler_leftSecond_eq_zero (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident)
    (hAssembly : incident = (netlist p).connections.incidentAssembly outgoing 0) :
    incident (Incident.mk
        (inputCouplerChannel p DirectionalCoupler.Port.leftSecond)) = 0 := by
  have hInput := congrArg
    (fun state => state (Incident.mk
      (inputCouplerChannel p DirectionalCoupler.Port.leftFirst))) hAssembly
  rw [incidentAssembly_apply_input_leftFirst] at hInput
  simp at hInput
  have hDrop := congrArg
    (fun state => state (Incident.mk
      (dropCouplerChannel p DirectionalCoupler.Port.leftFirst))) hAssembly
  rw [incidentAssembly_apply_drop_leftFirst] at hDrop
  simp at hDrop
  have hFirst := congrArg
    (fun state => state (Incident.mk
      (firstArcChannel p MatchedPropagation.Port.left))) hAssembly
  rw [incidentAssembly_apply_firstArc_left,
    scatteringEquation_inputCoupler_rightSecond p incident outgoing hScattering,
    hInput, mul_zero, zero_add] at hFirst
  have hDropRing := congrArg
    (fun state => state (Incident.mk
      (dropCouplerChannel p DirectionalCoupler.Port.leftSecond))) hAssembly
  rw [incidentAssembly_apply_dropCoupler_leftSecond,
    scatteringEquation_firstArc_right p incident outgoing hScattering] at hDropRing
  have hSecond := congrArg
    (fun state => state (Incident.mk
      (secondArcChannel p MatchedPropagation.Port.left))) hAssembly
  rw [incidentAssembly_apply_secondArc_left,
    scatteringEquation_dropCoupler_rightSecond p incident outgoing hScattering,
    hDrop, mul_zero, zero_add] at hSecond
  have hInputRing := congrArg
    (fun state => state (Incident.mk
      (inputCouplerChannel p DirectionalCoupler.Port.leftSecond))) hAssembly
  rw [incidentAssembly_apply_inputCoupler_leftSecond,
    scatteringEquation_secondArc_right p incident outgoing hScattering] at hInputRing
  have hProduct : p.denominator *
      incident (Incident.mk
        (inputCouplerChannel p DirectionalCoupler.Port.leftSecond)) = 0 := by
    calc
      p.denominator *
            incident (Incident.mk
              (inputCouplerChannel p DirectionalCoupler.Port.leftSecond)) =
          incident (Incident.mk
              (inputCouplerChannel p DirectionalCoupler.Port.leftSecond)) -
            p.secondArcCoefficient *
              ((p.dropThroughAmplitude : ℂ) *
                (p.firstArcCoefficient *
                  ((p.inputThroughAmplitude : ℂ) *
                    incident (Incident.mk
                      (inputCouplerChannel p
                        DirectionalCoupler.Port.leftSecond))))) := by
            rw [Parameters.denominator, Parameters.loopGain,
              Parameters.roundTripCoefficient]
            ring
      _ = 0 := by rw [← hFirst, ← hDropRing, ← hSecond, ← hInputRing, sub_self]
  exact (mul_eq_zero.mp hProduct).resolve_left hDenominator

/-- The reverse-circulating input-coupler coordinate vanishes in a homogeneous fixed point. -/
lemma reverseLoop_inputCoupler_rightSecond_eq_zero (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident)
    (hAssembly : incident = (netlist p).connections.incidentAssembly outgoing 0) :
    incident (Incident.mk
        (inputCouplerChannel p DirectionalCoupler.Port.rightSecond)) = 0 := by
  have hThrough := congrArg
    (fun state => state (Incident.mk
      (inputCouplerChannel p DirectionalCoupler.Port.rightFirst))) hAssembly
  rw [incidentAssembly_apply_input_rightFirst] at hThrough
  simp at hThrough
  have hDrop := congrArg
    (fun state => state (Incident.mk
      (dropCouplerChannel p DirectionalCoupler.Port.rightFirst))) hAssembly
  rw [incidentAssembly_apply_drop_rightFirst] at hDrop
  simp at hDrop
  have hSecond := congrArg
    (fun state => state (Incident.mk
      (secondArcChannel p MatchedPropagation.Port.right))) hAssembly
  rw [incidentAssembly_apply_secondArc_right,
    scatteringEquation_inputCoupler_leftSecond p incident outgoing hScattering,
    hThrough, mul_zero, zero_add] at hSecond
  have hDropRing := congrArg
    (fun state => state (Incident.mk
      (dropCouplerChannel p DirectionalCoupler.Port.rightSecond))) hAssembly
  rw [incidentAssembly_apply_dropCoupler_rightSecond,
    scatteringEquation_secondArc_left p incident outgoing hScattering] at hDropRing
  have hFirst := congrArg
    (fun state => state (Incident.mk
      (firstArcChannel p MatchedPropagation.Port.right))) hAssembly
  rw [incidentAssembly_apply_firstArc_right,
    scatteringEquation_dropCoupler_leftSecond p incident outgoing hScattering,
    hDrop, mul_zero, zero_add] at hFirst
  have hInputRing := congrArg
    (fun state => state (Incident.mk
      (inputCouplerChannel p DirectionalCoupler.Port.rightSecond))) hAssembly
  rw [incidentAssembly_apply_inputCoupler_rightSecond,
    scatteringEquation_firstArc_left p incident outgoing hScattering] at hInputRing
  have hProduct : p.denominator *
      incident (Incident.mk
        (inputCouplerChannel p DirectionalCoupler.Port.rightSecond)) = 0 := by
    calc
      p.denominator *
            incident (Incident.mk
              (inputCouplerChannel p DirectionalCoupler.Port.rightSecond)) =
          incident (Incident.mk
              (inputCouplerChannel p DirectionalCoupler.Port.rightSecond)) -
            p.firstArcCoefficient *
              ((p.dropThroughAmplitude : ℂ) *
                (p.secondArcCoefficient *
                  ((p.inputThroughAmplitude : ℂ) *
                    incident (Incident.mk
                      (inputCouplerChannel p
                        DirectionalCoupler.Port.rightSecond))))) := by
            rw [Parameters.denominator, Parameters.loopGain,
              Parameters.roundTripCoefficient]
            ring
      _ = 0 := by rw [← hSecond, ← hDropRing, ← hFirst, ← hInputRing, sub_self]
  exact (mul_eq_zero.mp hProduct).resolve_left hDenominator

/-- Every homogeneous add-drop feedback state vanishes at a nonzero denominator. -/
lemma feedback_fixedPoint_eq_zero (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident)
    (hAssembly : incident = (netlist p).connections.incidentAssembly outgoing 0) :
    incident = 0 := by
  have hInputLeft := congrArg
    (fun state => state (Incident.mk
      (inputCouplerChannel p DirectionalCoupler.Port.leftFirst))) hAssembly
  rw [incidentAssembly_apply_input_leftFirst] at hInputLeft
  simp at hInputLeft
  have hInputRight := congrArg
    (fun state => state (Incident.mk
      (inputCouplerChannel p DirectionalCoupler.Port.rightFirst))) hAssembly
  rw [incidentAssembly_apply_input_rightFirst] at hInputRight
  simp at hInputRight
  have hDropLeft := congrArg
    (fun state => state (Incident.mk
      (dropCouplerChannel p DirectionalCoupler.Port.leftFirst))) hAssembly
  rw [incidentAssembly_apply_drop_leftFirst] at hDropLeft
  simp at hDropLeft
  have hDropRight := congrArg
    (fun state => state (Incident.mk
      (dropCouplerChannel p DirectionalCoupler.Port.rightFirst))) hAssembly
  rw [incidentAssembly_apply_drop_rightFirst] at hDropRight
  simp at hDropRight
  have hForward := forwardLoop_inputCoupler_leftSecond_eq_zero p hDenominator
    incident outgoing hScattering hAssembly
  have hReverse := reverseLoop_inputCoupler_rightSecond_eq_zero p hDenominator
    incident outgoing hScattering hAssembly
  have hFirstLeft := congrArg
    (fun state => state (Incident.mk
      (firstArcChannel p MatchedPropagation.Port.left))) hAssembly
  rw [incidentAssembly_apply_firstArc_left,
    scatteringEquation_inputCoupler_rightSecond p incident outgoing hScattering] at hFirstLeft
  simp [hInputLeft, hForward] at hFirstLeft
  have hDropLeftSecond := congrArg
    (fun state => state (Incident.mk
      (dropCouplerChannel p DirectionalCoupler.Port.leftSecond))) hAssembly
  rw [incidentAssembly_apply_dropCoupler_leftSecond,
    scatteringEquation_firstArc_right p incident outgoing hScattering] at hDropLeftSecond
  simp [hFirstLeft] at hDropLeftSecond
  have hSecondLeft := congrArg
    (fun state => state (Incident.mk
      (secondArcChannel p MatchedPropagation.Port.left))) hAssembly
  rw [incidentAssembly_apply_secondArc_left,
    scatteringEquation_dropCoupler_rightSecond p incident outgoing hScattering] at hSecondLeft
  simp [hDropLeft, hDropLeftSecond] at hSecondLeft
  have hSecondRight := congrArg
    (fun state => state (Incident.mk
      (secondArcChannel p MatchedPropagation.Port.right))) hAssembly
  rw [incidentAssembly_apply_secondArc_right,
    scatteringEquation_inputCoupler_leftSecond p incident outgoing hScattering] at hSecondRight
  simp [hInputRight, hReverse] at hSecondRight
  have hDropRightSecond := congrArg
    (fun state => state (Incident.mk
      (dropCouplerChannel p DirectionalCoupler.Port.rightSecond))) hAssembly
  rw [incidentAssembly_apply_dropCoupler_rightSecond,
    scatteringEquation_secondArc_left p incident outgoing hScattering] at hDropRightSecond
  simp [hSecondRight] at hDropRightSecond
  have hFirstRight := congrArg
    (fun state => state (Incident.mk
      (firstArcChannel p MatchedPropagation.Port.right))) hAssembly
  rw [incidentAssembly_apply_firstArc_right,
    scatteringEquation_dropCoupler_leftSecond p incident outgoing hScattering] at hFirstRight
  simp [hDropRight, hDropRightSecond] at hFirstRight
  apply WithLp.ofLp_injective 2
  funext endpoint
  rcases endpoint with ⟨⟨⟨component, port⟩, mode⟩⟩
  cases component
  · cases port <;> cases mode
    · simpa [inputCouplerChannel] using hInputLeft
    · simpa [inputCouplerChannel] using hForward
    · simpa [inputCouplerChannel] using hInputRight
    · simpa [inputCouplerChannel] using hReverse
  · cases port <;> cases mode
    · simpa [dropCouplerChannel] using hDropLeft
    · simpa [dropCouplerChannel] using hDropLeftSecond
    · simpa [dropCouplerChannel] using hDropRight
    · simpa [dropCouplerChannel] using hDropRightSecond
  · cases port <;> cases mode
    · simpa [firstArcChannel] using hFirstLeft
    · simpa [firstArcChannel] using hFirstRight
  · cases port <;> cases mode
    · simpa [secondArcChannel] using hSecondLeft
    · simpa [secondArcChannel] using hSecondRight

/-- A nonzero scalar denominator makes the explicit add-drop feedback network well posed. -/
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

/-- A displayed incident state spanning one circulation at a singular denominator. -/
def singularIncident (p : Parameters) : ModeAmplitude (netlist p).IncidentIndex :=
  WithLp.toLp 2 fun endpoint =>
    if endpoint.channel = firstArcChannel p MatchedPropagation.Port.left then 1
    else if endpoint.channel =
        dropCouplerChannel p DirectionalCoupler.Port.leftSecond then
      p.firstArcCoefficient
    else if endpoint.channel = secondArcChannel p MatchedPropagation.Port.left then
      (p.dropThroughAmplitude : ℂ) * p.firstArcCoefficient
    else if endpoint.channel =
        inputCouplerChannel p DirectionalCoupler.Port.leftSecond then
      p.secondArcCoefficient * (p.dropThroughAmplitude : ℂ) * p.firstArcCoefficient
    else 0

/-- The singular incident state is given by its four displayed circulation coordinates. -/
lemma singularIncident_apply (p : Parameters) (endpoint : (netlist p).IncidentIndex) :
    singularIncident p endpoint =
      if endpoint.channel = firstArcChannel p MatchedPropagation.Port.left then 1
      else if endpoint.channel =
          dropCouplerChannel p DirectionalCoupler.Port.leftSecond then
        p.firstArcCoefficient
      else if endpoint.channel = secondArcChannel p MatchedPropagation.Port.left then
        (p.dropThroughAmplitude : ℂ) * p.firstArcCoefficient
      else if endpoint.channel =
          inputCouplerChannel p DirectionalCoupler.Port.leftSecond then
        p.secondArcCoefficient * (p.dropThroughAmplitude : ℂ) * p.firstArcCoefficient
      else 0 := rfl

/-- The displayed singular incident state is nonzero. -/
lemma singularIncident_ne_zero (p : Parameters) : singularIncident p ≠ 0 := by
  intro hZero
  have hCoordinate := congrArg
    (fun amplitude => amplitude
      (Incident.mk (firstArcChannel p MatchedPropagation.Port.left))) hZero
  simp [singularIncident] at hCoordinate

/-- At a zero denominator, the displayed singular incident state closes through all four wires. -/
lemma singularIncident_fixedPoint (p : Parameters) (hDenominator : p.denominator = 0) :
    singularIncident p =
      (netlist p).connections.incidentAssembly
        ((netlist p).scatteringTransform.toLinearMap (singularIncident p)) 0 := by
  have hDifference : (1 : ℂ) - p.loopGain = 0 := by
    simpa only [Parameters.denominator] using hDenominator
  have hGain : p.loopGain = 1 := (sub_eq_zero.mp hDifference).symm
  apply WithLp.ofLp_injective 2
  funext endpoint
  rcases endpoint with ⟨⟨⟨component, port⟩, mode⟩⟩
  cases component
  · cases port <;> cases mode
    · change singularIncident p
          (Incident.mk
            (inputCouplerChannel p DirectionalCoupler.Port.leftFirst)) =
        (netlist p).connections.incidentAssembly
          ((netlist p).scatteringTransform.toLinearMap (singularIncident p)) 0
            (Incident.mk
              (inputCouplerChannel p DirectionalCoupler.Port.leftFirst))
      rw [incidentAssembly_apply_input_leftFirst]
      simp [singularIncident]
    · change singularIncident p
          (Incident.mk
            (inputCouplerChannel p DirectionalCoupler.Port.leftSecond)) =
        (netlist p).connections.incidentAssembly
          ((netlist p).scatteringTransform.toLinearMap (singularIncident p)) 0
            (Incident.mk
              (inputCouplerChannel p DirectionalCoupler.Port.leftSecond))
      rw [incidentAssembly_apply_inputCoupler_leftSecond,
        scatteringEquation_secondArc_right p _ _ rfl]
      simp [singularIncident]
      ring
    · change singularIncident p
          (Incident.mk
            (inputCouplerChannel p DirectionalCoupler.Port.rightFirst)) =
        (netlist p).connections.incidentAssembly
          ((netlist p).scatteringTransform.toLinearMap (singularIncident p)) 0
            (Incident.mk
              (inputCouplerChannel p DirectionalCoupler.Port.rightFirst))
      rw [incidentAssembly_apply_input_rightFirst]
      simp [singularIncident]
    · change singularIncident p
          (Incident.mk
            (inputCouplerChannel p DirectionalCoupler.Port.rightSecond)) =
        (netlist p).connections.incidentAssembly
          ((netlist p).scatteringTransform.toLinearMap (singularIncident p)) 0
            (Incident.mk
              (inputCouplerChannel p DirectionalCoupler.Port.rightSecond))
      rw [incidentAssembly_apply_inputCoupler_rightSecond,
        scatteringEquation_firstArc_left p _ _ rfl]
      simp [singularIncident]
  · cases port <;> cases mode
    · change singularIncident p
          (Incident.mk
            (dropCouplerChannel p DirectionalCoupler.Port.leftFirst)) =
        (netlist p).connections.incidentAssembly
          ((netlist p).scatteringTransform.toLinearMap (singularIncident p)) 0
            (Incident.mk
              (dropCouplerChannel p DirectionalCoupler.Port.leftFirst))
      rw [incidentAssembly_apply_drop_leftFirst]
      simp [singularIncident]
    · change singularIncident p
          (Incident.mk
            (dropCouplerChannel p DirectionalCoupler.Port.leftSecond)) =
        (netlist p).connections.incidentAssembly
          ((netlist p).scatteringTransform.toLinearMap (singularIncident p)) 0
            (Incident.mk
              (dropCouplerChannel p DirectionalCoupler.Port.leftSecond))
      rw [incidentAssembly_apply_dropCoupler_leftSecond,
        scatteringEquation_firstArc_right p _ _ rfl]
      simp [singularIncident]
    · change singularIncident p
          (Incident.mk
            (dropCouplerChannel p DirectionalCoupler.Port.rightFirst)) =
        (netlist p).connections.incidentAssembly
          ((netlist p).scatteringTransform.toLinearMap (singularIncident p)) 0
            (Incident.mk
              (dropCouplerChannel p DirectionalCoupler.Port.rightFirst))
      rw [incidentAssembly_apply_drop_rightFirst]
      simp [singularIncident]
    · change singularIncident p
          (Incident.mk
            (dropCouplerChannel p DirectionalCoupler.Port.rightSecond)) =
        (netlist p).connections.incidentAssembly
          ((netlist p).scatteringTransform.toLinearMap (singularIncident p)) 0
            (Incident.mk
              (dropCouplerChannel p DirectionalCoupler.Port.rightSecond))
      rw [incidentAssembly_apply_dropCoupler_rightSecond,
        scatteringEquation_secondArc_left p _ _ rfl]
      simp [singularIncident]
  · cases port <;> cases mode
    · change singularIncident p
          (Incident.mk (firstArcChannel p MatchedPropagation.Port.left)) =
        (netlist p).connections.incidentAssembly
          ((netlist p).scatteringTransform.toLinearMap (singularIncident p)) 0
            (Incident.mk (firstArcChannel p MatchedPropagation.Port.left))
      rw [incidentAssembly_apply_firstArc_left,
        scatteringEquation_inputCoupler_rightSecond p _ _ rfl]
      simp [singularIncident]
      symm
      calc
        (p.inputThroughAmplitude : ℂ) *
              (p.secondArcCoefficient * (p.dropThroughAmplitude : ℂ) *
                p.firstArcCoefficient) = p.loopGain := by
            rw [Parameters.loopGain, Parameters.roundTripCoefficient]
            ring
        _ = 1 := hGain
    · change singularIncident p
          (Incident.mk (firstArcChannel p MatchedPropagation.Port.right)) =
        (netlist p).connections.incidentAssembly
          ((netlist p).scatteringTransform.toLinearMap (singularIncident p)) 0
            (Incident.mk (firstArcChannel p MatchedPropagation.Port.right))
      rw [incidentAssembly_apply_firstArc_right,
        scatteringEquation_dropCoupler_leftSecond p _ _ rfl]
      simp [singularIncident]
  · cases port <;> cases mode
    · change singularIncident p
          (Incident.mk (secondArcChannel p MatchedPropagation.Port.left)) =
        (netlist p).connections.incidentAssembly
          ((netlist p).scatteringTransform.toLinearMap (singularIncident p)) 0
            (Incident.mk (secondArcChannel p MatchedPropagation.Port.left))
      rw [incidentAssembly_apply_secondArc_left,
        scatteringEquation_dropCoupler_rightSecond p _ _ rfl]
      simp [singularIncident]
    · change singularIncident p
          (Incident.mk (secondArcChannel p MatchedPropagation.Port.right)) =
        (netlist p).connections.incidentAssembly
          ((netlist p).scatteringTransform.toLinearMap (singularIncident p)) 0
            (Incident.mk (secondArcChannel p MatchedPropagation.Port.right))
      rw [incidentAssembly_apply_secondArc_right,
        scatteringEquation_inputCoupler_leftSecond p _ _ rfl]
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

/-- A zero scalar denominator prevents well-posedness of the explicit add-drop network. -/
lemma not_isWellPosed_of_denominator_eq_zero (p : Parameters)
    (hDenominator : p.denominator = 0) : ¬(netlist p).IsWellPosed := by
  rw [(netlist p).isWellPosed_iff_feedbackOperator_injective]
  intro hInjective
  apply singularIncident_ne_zero p
  apply hInjective
  rw [singularIncident_feedbackOperator_eq_zero p hDenominator, map_zero]

/-- N5 well-posedness is exactly nonvanishing of the complete circulation denominator. -/
lemma isWellPosed_iff (p : Parameters) :
    (netlist p).IsWellPosed ↔ p.HasNonzeroDenominator := by
  constructor
  · intro hWellPosed hZero
    exact not_isWellPosed_of_denominator_eq_zero p hZero hWellPosed
  · exact isWellPosed_of_hasNonzeroDenominator p

/-- External readout returns the outgoing coordinate on the through bus. -/
lemma outputReadout_apply_through (p : Parameters)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex) :
    (netlist p).outputReadout.toLinearMap outgoing (Outgoing.mk (throughChannel p)) =
      outgoing
        (Outgoing.mk (inputCouplerChannel p DirectionalCoupler.Port.rightFirst)) := by
  rw [FlatNetlist.outputReadout,
    (netlist p).connections.externalOutgoingReadout_apply,
    ModeAmplitude.restrictEmbedding_apply]
  rfl

/-- External readout returns the outgoing coordinate on the drop bus. -/
lemma outputReadout_apply_drop (p : Parameters)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex) :
    (netlist p).outputReadout.toLinearMap outgoing (Outgoing.mk (dropChannel p)) =
      outgoing
        (Outgoing.mk (dropCouplerChannel p DirectionalCoupler.Port.rightFirst)) := by
  rw [FlatNetlist.outputReadout,
    (netlist p).connections.externalOutgoingReadout_apply,
    ModeAmplitude.restrictEmbedding_apply]
  rfl

/-- The forward return coordinate obtained by solving the four N5 channel equations. -/
lemma inputCoupler_leftSecond_solution (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) (amplitude : ℂ)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident)
    (hAssembly : incident =
      (netlist p).connections.incidentAssembly outgoing (inputAmplitude p amplitude)) :
    incident
        (Incident.mk (inputCouplerChannel p DirectionalCoupler.Port.leftSecond)) =
      p.secondArcCoefficient * (p.dropThroughAmplitude : ℂ) *
          p.firstArcCoefficient *
          DirectionalCoupler.crossCoefficient p.inputCoupler * amplitude /
        p.denominator := by
  have hInput := congrArg
    (fun state => state (Incident.mk
      (inputCouplerChannel p DirectionalCoupler.Port.leftFirst))) hAssembly
  rw [incidentAssembly_apply_input_leftFirst, inputAmplitude_apply_input] at hInput
  have hAdd := congrArg
    (fun state => state (Incident.mk
      (dropCouplerChannel p DirectionalCoupler.Port.leftFirst))) hAssembly
  rw [incidentAssembly_apply_drop_leftFirst, inputAmplitude_apply_add] at hAdd
  have hFirst := congrArg
    (fun state => state (Incident.mk
      (firstArcChannel p MatchedPropagation.Port.left))) hAssembly
  rw [incidentAssembly_apply_firstArc_left,
    scatteringEquation_inputCoupler_rightSecond p incident outgoing hScattering,
    hInput] at hFirst
  have hDropRing := congrArg
    (fun state => state (Incident.mk
      (dropCouplerChannel p DirectionalCoupler.Port.leftSecond))) hAssembly
  rw [incidentAssembly_apply_dropCoupler_leftSecond,
    scatteringEquation_firstArc_right p incident outgoing hScattering,
    hFirst] at hDropRing
  have hSecond := congrArg
    (fun state => state (Incident.mk
      (secondArcChannel p MatchedPropagation.Port.left))) hAssembly
  rw [incidentAssembly_apply_secondArc_left,
    scatteringEquation_dropCoupler_rightSecond p incident outgoing hScattering,
    hAdd, hDropRing, mul_zero, zero_add] at hSecond
  have hReturn := congrArg
    (fun state => state (Incident.mk
      (inputCouplerChannel p DirectionalCoupler.Port.leftSecond))) hAssembly
  rw [incidentAssembly_apply_inputCoupler_leftSecond,
    scatteringEquation_secondArc_right p incident outgoing hScattering,
    hSecond] at hReturn
  have hLoop : p.denominator *
      incident
          (Incident.mk (inputCouplerChannel p DirectionalCoupler.Port.leftSecond)) =
        p.secondArcCoefficient * (p.dropThroughAmplitude : ℂ) *
          p.firstArcCoefficient *
          DirectionalCoupler.crossCoefficient p.inputCoupler * amplitude := by
    rw [Parameters.denominator, Parameters.loopGain, Parameters.roundTripCoefficient]
    linear_combination hReturn
  apply (eq_div_iff hDenominator).2
  rw [mul_comm, hLoop]

/-- The forward drop-coupler ring coordinate obtained from the solved return coordinate. -/
lemma dropCoupler_leftSecond_solution (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) (amplitude : ℂ)
    (incident : ModeAmplitude (netlist p).IncidentIndex)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex)
    (hScattering : outgoing = (netlist p).scatteringTransform.toLinearMap incident)
    (hAssembly : incident =
      (netlist p).connections.incidentAssembly outgoing (inputAmplitude p amplitude)) :
    incident
        (Incident.mk (dropCouplerChannel p DirectionalCoupler.Port.leftSecond)) =
      DirectionalCoupler.crossCoefficient p.inputCoupler * p.firstArcCoefficient *
        amplitude / p.denominator := by
  have hInput := congrArg
    (fun state => state (Incident.mk
      (inputCouplerChannel p DirectionalCoupler.Port.leftFirst))) hAssembly
  rw [incidentAssembly_apply_input_leftFirst, inputAmplitude_apply_input] at hInput
  have hFirst := congrArg
    (fun state => state (Incident.mk
      (firstArcChannel p MatchedPropagation.Port.left))) hAssembly
  rw [incidentAssembly_apply_firstArc_left,
    scatteringEquation_inputCoupler_rightSecond p incident outgoing hScattering,
    hInput] at hFirst
  have hDropRing := congrArg
    (fun state => state (Incident.mk
      (dropCouplerChannel p DirectionalCoupler.Port.leftSecond))) hAssembly
  rw [incidentAssembly_apply_dropCoupler_leftSecond,
    scatteringEquation_firstArc_right p incident outgoing hScattering,
    hFirst] at hDropRing
  have hReturn := inputCoupler_leftSecond_solution p hDenominator amplitude
    incident outgoing hScattering hAssembly
  rw [hReturn] at hDropRing
  have hCancel :
      (p.secondArcCoefficient * (p.dropThroughAmplitude : ℂ) *
            p.firstArcCoefficient *
            DirectionalCoupler.crossCoefficient p.inputCoupler * amplitude /
          p.denominator) * p.denominator =
        p.secondArcCoefficient * (p.dropThroughAmplitude : ℂ) *
          p.firstArcCoefficient *
          DirectionalCoupler.crossCoefficient p.inputCoupler * amplitude :=
    div_mul_cancel₀ _ hDenominator
  apply (eq_div_iff hDenominator).2
  calc
    incident
          (Incident.mk (dropCouplerChannel p DirectionalCoupler.Port.leftSecond)) *
        p.denominator =
      p.firstArcCoefficient *
          (DirectionalCoupler.crossCoefficient p.inputCoupler * amplitude +
            (p.inputThroughAmplitude : ℂ) *
              (p.secondArcCoefficient * (p.dropThroughAmplitude : ℂ) *
                    p.firstArcCoefficient *
                    DirectionalCoupler.crossCoefficient p.inputCoupler * amplitude /
                  p.denominator)) *
        p.denominator := by rw [hDropRing]
    _ = p.firstArcCoefficient *
          DirectionalCoupler.crossCoefficient p.inputCoupler * amplitude *
            p.denominator +
        p.firstArcCoefficient * (p.inputThroughAmplitude : ℂ) *
          (p.secondArcCoefficient * (p.dropThroughAmplitude : ℂ) *
            p.firstArcCoefficient *
            DirectionalCoupler.crossCoefficient p.inputCoupler * amplitude) := by
      linear_combination
        p.firstArcCoefficient * (p.inputThroughAmplitude : ℂ) * hCancel
    _ = DirectionalCoupler.crossCoefficient p.inputCoupler *
        p.firstArcCoefficient * amplitude := by
      rw [Parameters.denominator, Parameters.loopGain, Parameters.roundTripCoefficient]
      ring

/-- The N5 response from the input bus to the through bus is the add-drop transfer amplitude. -/
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
    (fun state => state (Incident.mk
      (inputCouplerChannel p DirectionalCoupler.Port.leftFirst))) hAssembly'
  rw [incidentAssembly_apply_input_leftFirst, inputAmplitude_apply_input] at hInput
  have hReturn := inputCoupler_leftSecond_solution p hDenominator amplitude
    incident outgoing hScattering hAssembly'
  have hThrough :=
    scatteringEquation_inputCoupler_rightFirst p incident outgoing hScattering
  rw [hInput] at hThrough
  have hReadout := congrArg (fun state => state (Outgoing.mk (throughChannel p))) hOutput
  rw [outputReadout_apply_through] at hReadout
  change
    ((netlist p).responseTransform hWellPosed).toLinearMap
        (inputAmplitude p amplitude) (Outgoing.mk (throughChannel p)) =
      throughTransfer p * amplitude
  rw [show hWellPosed = isWellPosed_of_hasNonzeroDenominator p hDenominator from
      Subsingleton.elim _ _, hReadout, hThrough, hReturn, throughTransfer]
  rw [Parameters.roundTripCoefficient]
  ring

/-- The N5 response from the input bus to the drop bus is the add-drop transfer amplitude. -/
theorem response_drop (p : Parameters) (hDenominator : p.HasNonzeroDenominator)
    (amplitude : ℂ) :
    ((netlist p).responseTransform
        (isWellPosed_of_hasNonzeroDenominator p hDenominator)).toLinearMap
        (inputAmplitude p amplitude) (Outgoing.mk (dropChannel p)) =
      dropTransfer p * amplitude := by
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
  have hAdd := congrArg
    (fun state => state (Incident.mk
      (dropCouplerChannel p DirectionalCoupler.Port.leftFirst))) hAssembly'
  rw [incidentAssembly_apply_drop_leftFirst, inputAmplitude_apply_add] at hAdd
  have hDropRing := dropCoupler_leftSecond_solution p hDenominator amplitude
    incident outgoing hScattering hAssembly'
  have hDrop := scatteringEquation_dropCoupler_rightFirst p incident outgoing hScattering
  rw [hAdd, hDropRing, mul_zero, zero_add] at hDrop
  have hReadout := congrArg (fun state => state (Outgoing.mk (dropChannel p))) hOutput
  rw [outputReadout_apply_drop] at hReadout
  change
    ((netlist p).responseTransform hWellPosed).toLinearMap
        (inputAmplitude p amplitude) (Outgoing.mk (dropChannel p)) =
      dropTransfer p * amplitude
  rw [show hWellPosed = isWellPosed_of_hasNonzeroDenominator p hDenominator from
      Subsingleton.elim _ _, hReadout, hDrop, dropTransfer]
  ring

/-- The input-to-through entry of the N5 response matrix is the through transfer. -/
lemma responseTransform_entry_through_input (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) :
    (netlist p).responseTransform (isWellPosed_of_hasNonzeroDenominator p hDenominator)
        (Outgoing.mk (throughChannel p)) (Incident.mk (inputChannel p)) =
      throughTransfer p := by
  have hResponse := response_through p hDenominator 1
  simpa [inputAmplitude, Matrix.toLpLin_apply] using hResponse

/-- The input-to-drop entry of the N5 response matrix is the drop transfer. -/
lemma responseTransform_entry_drop_input (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) :
    (netlist p).responseTransform (isWellPosed_of_hasNonzeroDenominator p hDenominator)
        (Outgoing.mk (dropChannel p)) (Incident.mk (inputChannel p)) =
      dropTransfer p := by
  have hResponse := response_drop p hDenominator 1
  simpa [inputAmplitude, Matrix.toLpLin_apply] using hResponse

/-! ## F. Convergent multiple-round-trip view -/

/-- The totalized `tsum` of circulation powers, with series meaning only under summability. -/
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

/-- A totalized through expression, interpreted as a circulation response only when gated. -/
def throughTransferSeries (p : Parameters) : ℂ :=
  (p.inputThroughAmplitude : ℂ) +
    DirectionalCoupler.crossCoefficient p.inputCoupler ^ 2 *
      (p.dropThroughAmplitude : ℂ) * p.roundTripCoefficient * roundTripSeries p

/-- A totalized drop expression, interpreted as a circulation response only when gated. -/
def dropTransferSeries (p : Parameters) : ℂ :=
  DirectionalCoupler.crossCoefficient p.inputCoupler *
    DirectionalCoupler.crossCoefficient p.dropCoupler * p.firstArcCoefficient *
      roundTripSeries p

/-- On the contraction domain, through-series and algebraic-elimination views agree. -/
lemma throughTransfer_eq_roundTripSeries (p : Parameters)
    (hContractive : p.IsContractive) :
    throughTransfer p = throughTransferSeries p := by
  rw [throughTransfer, throughTransferSeries, roundTripSeries_eq_inverse p hContractive,
    div_eq_mul_inv]

/-- On the contraction domain, drop-series and algebraic-elimination views agree. -/
lemma dropTransfer_eq_roundTripSeries (p : Parameters)
    (hContractive : p.IsContractive) :
    dropTransfer p = dropTransferSeries p := by
  rw [dropTransfer, dropTransferSeries, roundTripSeries_eq_inverse p hContractive,
    div_eq_mul_inv]

/-- The N5 through response agrees with the convergent multiple-round-trip expression. -/
lemma response_through_eq_roundTripSeries (p : Parameters)
    (hContractive : p.IsContractive) (amplitude : ℂ) :
    ((netlist p).responseTransform
          (isWellPosed_of_hasNonzeroDenominator p hContractive.hasNonzeroDenominator)).toLinearMap
        (inputAmplitude p amplitude) (Outgoing.mk (throughChannel p)) =
      throughTransferSeries p * amplitude := by
  rw [response_through p hContractive.hasNonzeroDenominator,
    throughTransfer_eq_roundTripSeries p hContractive]

/-- The N5 drop response agrees with the convergent multiple-round-trip expression. -/
lemma response_drop_eq_roundTripSeries (p : Parameters)
    (hContractive : p.IsContractive) (amplitude : ℂ) :
    ((netlist p).responseTransform
          (isWellPosed_of_hasNonzeroDenominator p hContractive.hasNonzeroDenominator)).toLinearMap
        (inputAmplitude p amplitude) (Outgoing.mk (dropChannel p)) =
      dropTransferSeries p * amplitude := by
  rw [response_drop p hContractive.hasNonzeroDenominator,
    dropTransfer_eq_roundTripSeries p hContractive]

end AddDrop

end

end Optics
