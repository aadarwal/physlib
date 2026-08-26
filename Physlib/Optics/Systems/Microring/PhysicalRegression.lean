/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Systems.Microring.AddDropRegression
public import Physlib.Optics.Systems.Microring.AllPassRegression
public import Physlib.Optics.Systems.Microring.PhysicalSourceBridge

/-!
# Symbolic regressions for physical microring realization

## i. Overview

These fixtures pin the conversion from physical path data to the S2 field parameters and the
independent travelling-field relations. Positive anchors square the canonical `3-4-5` amplitudes
and the half field attenuation. Negative controls reject squared powers in the amplitude role,
raw amplitudes in the power role, and a swapped field/power attenuation pair through the typed
conversion API. Exact logarithmic attenuation data gives field factors `1 / 2` and `1 / 4`.
Separate rational optical-depth fixtures use `alpha * L = 0` and normalized optical paths
`n_eff * L / lambda = 0, 1 / 4, 1 / 2`, giving phase lifts `0`, `pi / 2`, and `pi`. The quarter-turn
fixture directly pins the negative-exponential carrier factor to `-I`.

The relation anchors substitute internal fields by hand. The response anchors reuse the S2
regressions that eliminate the concrete netlist channel equations directly; they do not rewrite
with `allPass_physicalResponse_eq_transfer` or `addDrop_physicalResponse_eq_transfers`.
The source-composition anchors independently expand DATE, SysCon, and SFG fields at the same
physical point before comparing them with that response; they do not use the physical source
bridge lemmas under test.

The zero-phase add-drop fixture uses the S2 symmetric half-arc reference plane and N7 `-I * k`
gauge. Its drop value `-32 / 91` is gauge- and reference-plane-dependent. No named phase point is
claimed to be an extremum. No dispersion, bending loss, coupling-length, material, thermal,
nonlinear, or bandwidth claim is made. Power means normalized modal power, not electromagnetic
power before the finite, common-frequency, Maxwell-qualified, pairwise-integrable, mutually
flux-orthogonal, unit-normalized bridge at
`Physlib/Optics/HarmonicFlux/PropagatingModePower.lean:16-22,60-93`.

## ii. Key results

- `physicalRegression_halfAttenuation`: exact field factor `1 / 2`.
- `physicalRegression_quarterAttenuation`: exact field factor `1 / 4`.
- `physicalRegression_powerFractions_not_amplitudeCoupling`: amplitude-role negative control.
- `physicalRegression_amplitudes_not_powerCoupling`: power-role negative control.
- `physicalRegression_attenuation_roleSwap_rejected`: attenuation-role negative control.
- `physicalRegression_quarterTurn_carrierPhaseFactor`: the carrier sign at phase `pi / 2`.
- `physicalRegression_allPass_toParameters`: the named S2 one-bus parameter point.
- `physicalRegression_addDrop_toParameters`: the named S2 two-bus parameter point.
- `physicalRegression_allPass_fieldRelation`: direct one-bus internal-field solution.
- `physicalRegression_addDrop_fieldRelation`: direct two-bus internal-field solution.
- `physicalRegression_allPass_response`: independently eliminated N5 response `1 / 7`.
- `physicalRegression_addDrop_responses`: independently eliminated N5 responses.
- `physicalRegression_date_backwardTransfer_eq_response`: DATE and physical N5 agreement.
- `physicalRegression_sysCon_dropTransfer_eq_response`: SysCon and physical N5 agreement.
- `physicalRegression_sfg_dropTransfer_eq_response`: SFG-TR and physical N5 agreement.

## iii. Table of contents

- A. Exact attenuation and coupling data
- B. Exact zero- and half-turn physical phase points
- C. Maps to the named S2 parameters
- D. Direct internal-field anchors
- E. Independent N5 response anchors
- F. Independently expanded source-composition anchors

## iv. References

The named target values are defined in
`Physlib/Optics/Systems/Microring/AllPassRegression.lean:61-108,218-245` and
`Physlib/Optics/Systems/Microring/AddDropRegression.lean:64-170,404-430`.
-/

@[expose] public section

namespace Optics

noncomputable section

namespace Microring

/-! ## A. Exact attenuation and coupling data -/

/-- The exact `3-4-5` amplitude coupler used by the physical fixtures. -/
def physicalRegressionCoupling : CouplingParameters where
  throughAmplitude := 3 / 5
  crossAmplitude := 4 / 5

/-- The exact amplitude fixture satisfies `t² + k² = 1`. -/
lemma physicalRegression_coupling_isValid : physicalRegressionCoupling.IsValid := by
  norm_num [physicalRegressionCoupling, CouplingParameters.IsValid, IsAmplitudeCoupling]

/-- Squared `3-4-5` amplitudes give power fractions `9 / 25` and `16 / 25`. -/
lemma physicalRegression_coupling_powers :
    physicalRegressionCoupling.throughAmplitude ^ 2 = 9 / 25 ∧
      physicalRegressionCoupling.crossAmplitude ^ 2 = 16 / 25 := by
  norm_num [physicalRegressionCoupling]

/-- Squared power fractions do not satisfy the amplitude normalization. -/
lemma physicalRegression_powerFractions_not_amplitudeCoupling :
    ¬ IsAmplitudeCoupling
      ({ throughAmplitude := 9 / 25
         crossAmplitude := 16 / 25 } : CouplingParameters) := by
  norm_num [IsAmplitudeCoupling]

/-- Raw `3-4-5` amplitudes do not satisfy the power-fraction normalization. -/
lemma physicalRegression_amplitudes_not_powerCoupling :
    ¬ IsPowerCoupling
      ({ throughPower := 3 / 5
         crossPower := 4 / 5 } : PowerCouplingParameters) := by
  norm_num [IsPowerCoupling]

/-- Unit path length with power coefficient `2 * log 2` and zero phase lift. -/
def physicalRegressionHalfAttenuation : PhysicalParameters where
  pathLength := 1
  powerAttenuationCoefficient := 2 * Real.log 2
  effectiveIndex := 0
  wavelength := 1

/-- Direct exponential evaluation gives the field factor `1 / 2`. -/
lemma physicalRegression_halfAttenuation :
    physicalRegressionHalfAttenuation.fieldAttenuation.value = 1 / 2 := by
  rw [PhysicalParameters.fieldAttenuation]
  change Real.exp (-(2 * Real.log 2) * 1 / 2) = 1 / 2
  rw [show -(2 * Real.log 2) * 1 / 2 = -Real.log 2 by ring,
    Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  norm_num

/-- Direct exponential evaluation gives the corresponding power factor `1 / 4`. -/
lemma physicalRegression_halfPowerAttenuation :
    physicalRegressionHalfAttenuation.powerAttenuation.value = 1 / 4 := by
  rw [PhysicalParameters.powerAttenuation]
  change Real.exp (-(2 * Real.log 2) * 1) = 1 / 4
  rw [show -(2 * Real.log 2) * 1 = -(Real.log 2 + Real.log 2) by ring,
    Real.exp_neg, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  norm_num

/-- At this point the explicit field square equals the power attenuation. -/
lemma physicalRegression_halfAttenuation_sq :
    physicalRegressionHalfAttenuation.fieldAttenuation.value ^ 2 =
      physicalRegressionHalfAttenuation.powerAttenuation.value := by
  rw [physicalRegression_halfAttenuation, physicalRegression_halfPowerAttenuation]
  norm_num

/-- A power value used as a field value fails the field-to-power consistency equation. -/
lemma physicalRegression_attenuation_roleSwap_rejected :
    fieldToPowerAttenuation ({ value := 1 / 4 } : FieldAttenuation) ≠
      ({ value := 1 / 2 } : PowerAttenuation) := by
  intro hSwap
  have hValue := congrArg PowerAttenuation.value hSwap
  norm_num [fieldToPowerAttenuation] at hValue

/-- Unit path length with power coefficient `4 * log 2` and zero phase lift. -/
def physicalRegressionQuarterAttenuation : PhysicalParameters where
  pathLength := 1
  powerAttenuationCoefficient := 4 * Real.log 2
  effectiveIndex := 0
  wavelength := 1

/-- Direct exponential evaluation gives the field factor `1 / 4`. -/
lemma physicalRegression_quarterAttenuation :
    physicalRegressionQuarterAttenuation.fieldAttenuation.value = 1 / 4 := by
  rw [PhysicalParameters.fieldAttenuation]
  change Real.exp (-(4 * Real.log 2) * 1 / 2) = 1 / 4
  rw [show -(4 * Real.log 2) * 1 / 2 = -(Real.log 2 + Real.log 2) by ring,
    Real.exp_neg, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  norm_num

/-! ## B. Exact zero- and half-turn physical phase points -/

/-- A rational zero-optical-depth, zero-phase physical propagation point. -/
def physicalRegressionRationalZeroPhase : PhysicalParameters where
  pathLength := 1
  powerAttenuationCoefficient := 0
  effectiveIndex := 0
  wavelength := 1

/-- The zero-phase fixture has rational optical depth `alpha * L = 0`. -/
lemma physicalRegression_zeroPhase_opticalDepth :
    physicalRegressionRationalZeroPhase.powerAttenuationCoefficient *
      physicalRegressionRationalZeroPhase.pathLength = 0 := by
  norm_num [physicalRegressionRationalZeroPhase]

/-- Its normalized optical path is zero. -/
lemma physicalRegression_zeroPhase_normalizedOpticalPath :
    physicalRegressionRationalZeroPhase.effectiveIndex *
        physicalRegressionRationalZeroPhase.pathLength /
      physicalRegressionRationalZeroPhase.wavelength = 0 := by
  norm_num [physicalRegressionRationalZeroPhase]

/-- Direct evaluation gives real round-trip phase lift zero. -/
lemma physicalRegression_zeroPhase_lift :
    physicalRegressionRationalZeroPhase.roundTripPhaseLift = 0 := by
  norm_num [PhysicalParameters.roundTripPhaseLift,
    PhysicalParameters.propagationConstant, physicalRegressionRationalZeroPhase]

/-- A rational zero-optical-depth, half-turn physical propagation point. -/
def physicalRegressionRationalHalfTurn : PhysicalParameters where
  pathLength := 1
  powerAttenuationCoefficient := 0
  effectiveIndex := 1 / 2
  wavelength := 1

/-- The half-turn fixture also has rational optical depth `alpha * L = 0`. -/
lemma physicalRegression_halfTurn_opticalDepth :
    physicalRegressionRationalHalfTurn.powerAttenuationCoefficient *
      physicalRegressionRationalHalfTurn.pathLength = 0 := by
  norm_num [physicalRegressionRationalHalfTurn]

/-- Its normalized optical path is exactly `1 / 2`. -/
lemma physicalRegression_halfTurn_normalizedOpticalPath :
    physicalRegressionRationalHalfTurn.effectiveIndex *
        physicalRegressionRationalHalfTurn.pathLength /
      physicalRegressionRationalHalfTurn.wavelength = 1 / 2 := by
  norm_num [physicalRegressionRationalHalfTurn]

/-- Direct evaluation gives the real round-trip phase lift `pi`. -/
lemma physicalRegression_halfTurn_lift :
    physicalRegressionRationalHalfTurn.roundTripPhaseLift = Real.pi := by
  norm_num [PhysicalParameters.roundTripPhaseLift,
    PhysicalParameters.propagationConstant, physicalRegressionRationalHalfTurn]
  ring

/-- A rational zero-optical-depth point with normalized optical path `1 / 4`. -/
def physicalRegressionRationalQuarterTurn : PhysicalParameters where
  pathLength := 1
  powerAttenuationCoefficient := 0
  effectiveIndex := 1 / 4
  wavelength := 1

/-- The quarter-turn fixture has rational optical depth `alpha * L = 0`. -/
lemma physicalRegression_quarterTurn_opticalDepth :
    physicalRegressionRationalQuarterTurn.powerAttenuationCoefficient *
      physicalRegressionRationalQuarterTurn.pathLength = 0 := by
  norm_num [physicalRegressionRationalQuarterTurn]

/-- Its normalized optical path is exactly `1 / 4`. -/
lemma physicalRegression_quarterTurn_normalizedOpticalPath :
    physicalRegressionRationalQuarterTurn.effectiveIndex *
        physicalRegressionRationalQuarterTurn.pathLength /
      physicalRegressionRationalQuarterTurn.wavelength = 1 / 4 := by
  norm_num [physicalRegressionRationalQuarterTurn]

/-- Direct evaluation gives the real round-trip phase lift `pi / 2`. -/
lemma physicalRegression_quarterTurn_lift :
    physicalRegressionRationalQuarterTurn.roundTripPhaseLift = Real.pi / 2 := by
  norm_num [PhysicalParameters.roundTripPhaseLift,
    PhysicalParameters.propagationConstant, physicalRegressionRationalQuarterTurn]
  ring

/-- At phase `pi / 2`, the negative-exponential carrier convention gives `-I`. -/
lemma physicalRegression_quarterTurn_carrierPhaseFactor :
    MatchedPropagation.carrierPhaseFactor
      physicalRegressionRationalQuarterTurn.roundTripPhase = -Complex.I := by
  simp [PhysicalParameters.roundTripPhase, PhysicalParameters.roundTripPhaseLift,
    PhysicalParameters.propagationConstant, physicalRegressionRationalQuarterTurn,
    MatchedPropagation.carrierPhaseFactor, Real.Angle.toCircle_coe, Circle.coe_exp]
  apply Complex.ext <;> norm_num

/-! ## C. Maps to the named S2 parameters -/

/-- The physical point whose derived parameters are the named S2 all-pass resonance point. -/
def physicalRegressionAllPass : AllPassPhysicalParameters where
  coupling := physicalRegressionCoupling
  propagation := physicalRegressionHalfAttenuation

/-- The all-pass physical data maps exactly to the S2 `3-4-5`, half-retention, zero-phase point. -/
lemma physicalRegression_allPass_toParameters :
    physicalRegressionAllPass.toParameters = AllPass.allPassRegressionResonanceParameters := by
  change
    ({ throughAmplitude := 3 / 5
       crossAmplitude := 4 / 5
       fieldAttenuation := physicalRegressionHalfAttenuation.fieldAttenuation.value
       roundTripPhase := physicalRegressionHalfAttenuation.roundTripPhase } :
      AllPass.Parameters) = AllPass.allPassRegressionResonanceParameters
  rw [physicalRegression_halfAttenuation]
  simp [AllPass.allPassRegressionResonanceParameters, PhysicalParameters.roundTripPhase,
    PhysicalParameters.roundTripPhaseLift, PhysicalParameters.propagationConstant,
    physicalRegressionHalfAttenuation]

/-- The physical point whose derived parameters are the named S2 add-drop resonance point. -/
def physicalRegressionAddDrop : AddDropPhysicalParameters where
  inputCoupling := physicalRegressionCoupling
  dropCoupling := physicalRegressionCoupling
  propagation := physicalRegressionQuarterAttenuation

/-- The add-drop physical data maps exactly to the S2 `3-4-5`, quarter-retention point. -/
lemma physicalRegression_addDrop_toParameters :
    physicalRegressionAddDrop.toParameters = AddDrop.addDropRegressionResonanceParameters := by
  change
    ({ inputThroughAmplitude := 3 / 5
       inputCrossAmplitude := 4 / 5
       dropThroughAmplitude := 3 / 5
       dropCrossAmplitude := 4 / 5
       fieldAttenuation := physicalRegressionQuarterAttenuation.fieldAttenuation.value
       roundTripPhase := physicalRegressionQuarterAttenuation.roundTripPhaseLift } :
      AddDrop.Parameters) = AddDrop.addDropRegressionResonanceParameters
  rw [physicalRegression_quarterAttenuation]
  simp [AddDrop.addDropRegressionResonanceParameters,
    PhysicalParameters.roundTripPhaseLift, PhysicalParameters.propagationConstant,
    physicalRegressionQuarterAttenuation]

/-- The same add-drop point with normalized optical path `1 / 2`, hence phase lift `pi`. -/
def physicalRegressionAddDropHalfTurn : AddDropPhysicalParameters where
  inputCoupling := physicalRegressionCoupling
  dropCoupling := physicalRegressionCoupling
  propagation :=
    { physicalRegressionQuarterAttenuation with effectiveIndex := 1 / 2 }

/-- The half-turn physical data maps exactly to the named S2 antiresonance parameter point. -/
lemma physicalRegression_addDropHalfTurn_toParameters :
    physicalRegressionAddDropHalfTurn.toParameters =
      AddDrop.addDropRegressionAntiresonanceParameters := by
  change
    ({ inputThroughAmplitude := 3 / 5
       inputCrossAmplitude := 4 / 5
       dropThroughAmplitude := 3 / 5
       dropCrossAmplitude := 4 / 5
       fieldAttenuation := physicalRegressionQuarterAttenuation.fieldAttenuation.value
       roundTripPhase :=
         ({ physicalRegressionQuarterAttenuation with effectiveIndex := 1 / 2 } :
           PhysicalParameters).roundTripPhaseLift } : AddDrop.Parameters) =
      AddDrop.addDropRegressionAntiresonanceParameters
  rw [physicalRegression_quarterAttenuation]
  simp [AddDrop.addDropRegressionAntiresonanceParameters,
    PhysicalParameters.roundTripPhaseLift, PhysicalParameters.propagationConstant,
    physicalRegressionQuarterAttenuation]
  ring

/-! ## D. Direct internal-field anchors -/

/-- Direct one-bus internal fields at the exact resonance fixture. -/
def physicalRegressionAllPassInternalFields : AllPassInternalFields where
  launched := -(8 / 7) * Complex.I
  returning := -(4 / 7) * Complex.I

/-- Hand substitution proves the one-bus relation and through value `1 / 7`. -/
lemma physicalRegression_allPass_fieldRelation :
    AllPassFieldRelation physicalRegressionAllPass 1 (1 / 7)
      physicalRegressionAllPassInternalFields := by
  rw [AllPassFieldRelation, physicalRegression_allPass_toParameters]
  refine ⟨?_, ?_, ?_⟩
  · simp [physicalRegressionAllPassInternalFields,
      AllPass.allPassRegressionResonanceParameters, AllPass.Parameters.coupler,
      DirectionalCoupler.crossCoefficient]
    ring_nf
    rw [Complex.I_sq]
    norm_num
  · simp [physicalRegressionAllPassInternalFields,
      AllPass.allPassRegressionResonanceParameters, AllPass.Parameters.coupler,
      DirectionalCoupler.crossCoefficient]
    ring
  · rw [AllPass.allPassRegression_resonance_loopCoefficient]
    simp [physicalRegressionAllPassInternalFields]
    ring

/-- Direct two-bus internal fields at the exact zero-phase fixture. -/
def physicalRegressionAddDropInternalFields : AddDropInternalFields where
  inputCouplerOutput := -(80 / 91) * Complex.I
  dropCouplerInput := -(40 / 91) * Complex.I
  dropCouplerOutput := -(24 / 91) * Complex.I
  inputCouplerInput := -(12 / 91) * Complex.I

/-- Hand substitution proves the two-bus relation and the values `45 / 91`, `-32 / 91`. -/
lemma physicalRegression_addDrop_fieldRelation :
    AddDropFieldRelation physicalRegressionAddDrop 1 0 (45 / 91) (-32 / 91)
      physicalRegressionAddDropInternalFields := by
  rw [AddDropFieldRelation, physicalRegression_addDrop_toParameters]
  rw [AddDrop.addDropRegression_resonance_firstArcCoefficient,
    AddDrop.addDropRegression_resonance_secondArcCoefficient]
  simp [physicalRegressionAddDropInternalFields,
    AddDrop.addDropRegressionResonanceParameters, AddDrop.Parameters.inputCoupler,
    AddDrop.Parameters.dropCoupler, DirectionalCoupler.crossCoefficient]
  ring_nf
  rw [Complex.I_sq]
  norm_num

/-! ## E. Independent N5 response anchors -/

/-- The physical one-bus topology is well posed at the named exact point. -/
lemma physicalRegression_allPass_isWellPosed :
    (allPassTopology physicalRegressionAllPass).IsWellPosed := by
  change (AllPass.netlist physicalRegressionAllPass.toParameters).IsWellPosed
  rw [physicalRegression_allPass_toParameters]
  exact AllPass.allPassRegression_resonance_isWellPosed

/-- The direct S2 netlist elimination gives the physical one-bus response `1 / 7`. -/
lemma physicalRegression_allPass_response :
    (allPassTopology physicalRegressionAllPass).responseTransform
        physicalRegression_allPass_isWellPosed
        (Outgoing.mk (allPassThroughChannel physicalRegressionAllPass))
        (Incident.mk (allPassInputChannel physicalRegressionAllPass)) = 1 / 7 := by
  have hTransport :
      ∀ (p q : AllPass.Parameters) (hpq : p = q)
        (hp : (AllPass.netlist p).IsWellPosed)
        (hq : (AllPass.netlist q).IsWellPosed),
        (AllPass.netlist p).responseTransform hp
            (Outgoing.mk (AllPass.throughChannel p))
            (Incident.mk (AllPass.inputChannel p)) =
          (AllPass.netlist q).responseTransform hq
            (Outgoing.mk (AllPass.throughChannel q))
            (Incident.mk (AllPass.inputChannel q)) := by
    intro p q hpq hp hq
    subst q
    rw [Subsingleton.elim hp hq]
  exact (hTransport physicalRegressionAllPass.toParameters
    AllPass.allPassRegressionResonanceParameters
    physicalRegression_allPass_toParameters physicalRegression_allPass_isWellPosed
    AllPass.allPassRegression_resonance_isWellPosed).trans
      AllPass.allPassRegression_resonance_responseTransform_entry

/-- The physical two-bus topology is well posed at the named exact point. -/
lemma physicalRegression_addDrop_isWellPosed :
    (addDropTopology physicalRegressionAddDrop).IsWellPosed := by
  change (AddDrop.netlist physicalRegressionAddDrop.toParameters).IsWellPosed
  rw [physicalRegression_addDrop_toParameters]
  exact AddDrop.addDropRegression_resonance_isWellPosed

/-- Direct S2 netlist elimination gives both physical two-bus response entries. -/
lemma physicalRegression_addDrop_responses :
    (addDropTopology physicalRegressionAddDrop).responseTransform
        physicalRegression_addDrop_isWellPosed
        (Outgoing.mk (addDropThroughChannel physicalRegressionAddDrop))
        (Incident.mk (addDropInputChannel physicalRegressionAddDrop)) = 45 / 91 ∧
      (addDropTopology physicalRegressionAddDrop).responseTransform
        physicalRegression_addDrop_isWellPosed
        (Outgoing.mk (addDropDropChannel physicalRegressionAddDrop))
        (Incident.mk (addDropInputChannel physicalRegressionAddDrop)) = -32 / 91 := by
  have hTransport :
      ∀ (p q : AddDrop.Parameters) (hpq : p = q)
        (hp : (AddDrop.netlist p).IsWellPosed)
        (hq : (AddDrop.netlist q).IsWellPosed)
        (output : (r : AddDrop.Parameters) → (AddDrop.netlist r).ExternalChannel),
        (AddDrop.netlist p).responseTransform hp (Outgoing.mk (output p))
            (Incident.mk (AddDrop.inputChannel p)) =
          (AddDrop.netlist q).responseTransform hq (Outgoing.mk (output q))
            (Incident.mk (AddDrop.inputChannel q)) := by
    intro p q hpq hp hq output
    subst q
    rw [Subsingleton.elim hp hq]
  constructor
  · exact (hTransport physicalRegressionAddDrop.toParameters
      AddDrop.addDropRegressionResonanceParameters
      physicalRegression_addDrop_toParameters physicalRegression_addDrop_isWellPosed
      AddDrop.addDropRegression_resonance_isWellPosed
      AddDrop.throughChannel).trans
        AddDrop.addDropRegression_resonance_responseTransform_entry_through
  · exact (hTransport physicalRegressionAddDrop.toParameters
      AddDrop.addDropRegressionResonanceParameters
      physicalRegression_addDrop_toParameters physicalRegression_addDrop_isWellPosed
      AddDrop.addDropRegression_resonance_isWellPosed
      AddDrop.dropChannel).trans
        AddDrop.addDropRegression_resonance_responseTransform_entry_drop

/-! ## F. Independently expanded source-composition anchors -/

open MicroringSourceBridge
open scoped ComplexOrder

/-- DATE data whose physical interpretation is the exact zero-phase add-drop fixture. -/
def physicalRegressionDateParameters : DateParameters where
  reflectivity := 3 / 5
  transmissivity := 4 / 5
  couplingLength := 1
  powerAttenuation := 4 * Real.log 2
  wavelength := 1
  effectiveIndex := 0

/-- Direct record expansion identifies the DATE and physical parameter points. -/
lemma physicalRegression_date_toPhysicalAddDrop :
    physicalRegressionDateParameters.toPhysicalAddDrop = physicalRegressionAddDrop := rfl

/-- Direct evaluation of `SourceBridgeDate.lean:86-87` gives DATE's field factor `1 / 4`. -/
lemma physicalRegression_date_fieldAttenuation :
    physicalRegressionDateParameters.fieldAttenuation = 1 / 4 := by
  rw [DateParameters.fieldAttenuation]
  change Real.exp (-(4 * Real.log 2) * 1 / 2) = 1 / 4
  rw [show -(4 * Real.log 2) * 1 / 2 = -(Real.log 2 + Real.log 2) by ring,
    Real.exp_neg, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  norm_num

/-- Direct phase expansion gives DATE's full- and half-round-trip factors as one. -/
lemma physicalRegression_date_phaseFactors :
    physicalRegressionDateParameters.phaseFactor = 1 ∧
      physicalRegressionDateParameters.halfPhaseFactor = 1 := by
  constructor <;>
    norm_num [DateParameters.phaseFactor, DateParameters.halfPhaseFactor,
      DateParameters.roundTripPhase, physicalRegressionDateParameters,
      MatchedPropagation.carrierPhaseFactor]

/-- Direct expansion gives DATE's zero-phase denominator `91 / 100`. -/
lemma physicalRegression_date_denominator :
    physicalRegressionDateParameters.denominator = 91 / 100 := by
  rw [DateParameters.denominator, physicalRegression_date_fieldAttenuation,
    physicalRegression_date_phaseFactors.1]
  norm_num [physicalRegressionDateParameters]

/-- Direct expansion of `SourceBridgeDate.lean:486-488` gives DATE's drop field `-32 / 91`. -/
lemma physicalRegression_date_backwardTransfer :
    dateBackwardTransfer physicalRegressionDateParameters = -32 / 91 := by
  rw [dateBackwardTransfer, physicalRegression_date_fieldAttenuation,
    physicalRegression_date_phaseFactors.2, physicalRegression_date_denominator]
  have hSqrt : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
    apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2
    norm_num
  norm_num [physicalRegressionDateParameters, hSqrt]

/-- Independent DATE and netlist expansions agree at the physical zero-phase point. -/
lemma physicalRegression_date_backwardTransfer_eq_response :
    dateBackwardTransfer physicalRegressionDateParameters =
      (addDropTopology physicalRegressionAddDrop).responseTransform
        physicalRegression_addDrop_isWellPosed
        (Outgoing.mk (addDropDropChannel physicalRegressionAddDrop))
        (Incident.mk (addDropInputChannel physicalRegressionAddDrop)) := by
  rw [physicalRegression_date_backwardTransfer,
    physicalRegression_addDrop_responses.2]

/-- Exact SysCon data selected by the physical zero-phase add-drop fixture. -/
def physicalRegressionSysConParameters : SysConParameters where
  phase := 0
  fieldAttenuation := 1 / 4
  inputCrossAmplitude := 4 / 5
  dropCrossAmplitude := 4 / 5
  inputThroughAmplitude := 3 / 5
  dropThroughAmplitude := 3 / 5

/-- Direct expansion identifies the physical and SysCon parameter dictionaries. -/
lemma physicalRegression_toSysConParameters :
    addDropPhysicalToSysConParameters physicalRegressionAddDrop =
      physicalRegressionSysConParameters := by
  change
    ({ phase := physicalRegressionQuarterAttenuation.roundTripPhaseLift
       fieldAttenuation := physicalRegressionQuarterAttenuation.fieldAttenuation.value
       inputCrossAmplitude := 4 / 5
       dropCrossAmplitude := 4 / 5
       inputThroughAmplitude := 3 / 5
       dropThroughAmplitude := 3 / 5 } : SysConParameters) =
      physicalRegressionSysConParameters
  rw [physicalRegression_quarterAttenuation]
  norm_num [physicalRegressionQuarterAttenuation,
    PhysicalParameters.roundTripPhaseLift, PhysicalParameters.propagationConstant,
    physicalRegressionSysConParameters]

/-- Direct expansion gives SysCon's zero-phase loop gain and denominator. -/
lemma physicalRegression_sysCon_loopGain_denominator :
    physicalRegressionSysConParameters.loopGain = 9 / 100 ∧
      physicalRegressionSysConParameters.denominator = 91 / 100 := by
  constructor
  · norm_num [SysConParameters.loopGain, physicalRegressionSysConParameters,
      MatchedPropagation.carrierPhaseFactor]
  · rw [SysConParameters.denominator]
    norm_num [SysConParameters.loopGain, physicalRegressionSysConParameters,
      MatchedPropagation.carrierPhaseFactor]

/-- Direct expansion of `SourceBridgeSysCon.lean:160-165` gives SysCon's drop field `-32 / 91`. -/
lemma physicalRegression_sysCon_dropTransfer :
    sysConDropTransfer physicalRegressionSysConParameters = -32 / 91 := by
  have hSqrt : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
    apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2
    norm_num
  rw [sysConDropTransfer, physicalRegression_sysCon_loopGain_denominator.2]
  norm_num [physicalRegressionSysConParameters,
    MatchedPropagation.carrierPhaseFactor, hSqrt]

/-- Independent SysCon and netlist expansions agree at the physical zero-phase point. -/
lemma physicalRegression_sysCon_dropTransfer_eq_response :
    sysConDropTransfer
        (addDropPhysicalToSysConParameters physicalRegressionAddDrop) =
      (addDropTopology physicalRegressionAddDrop).responseTransform
        physicalRegression_addDrop_isWellPosed
        (Outgoing.mk (addDropDropChannel physicalRegressionAddDrop))
        (Incident.mk (addDropInputChannel physicalRegressionAddDrop)) := by
  rw [physicalRegression_toSysConParameters,
    physicalRegression_sysCon_dropTransfer,
    physicalRegression_addDrop_responses.2]

/-- Exact SFG-TR coefficients selected by the physical zero-phase add-drop fixture. -/
def physicalRegressionSfgParameters : SfgParameters where
  roundTripCoefficient := 1 / 4
  inputCrossAmplitude := 4 / 5
  dropCrossAmplitude := 4 / 5
  inputThroughAmplitude := 3 / 5
  dropThroughAmplitude := 3 / 5

/-- Direct expansion identifies the physical and SFG-TR parameter dictionaries. -/
lemma physicalRegression_toSfgParameters :
    SfgParameters.ofAddDrop physicalRegressionAddDrop.toParameters =
      physicalRegressionSfgParameters := by
  rw [physicalRegression_addDrop_toParameters]
  unfold SfgParameters.ofAddDrop
  rw [AddDrop.addDropRegression_resonance_roundTripCoefficient]
  norm_num [AddDrop.addDropRegressionResonanceParameters,
    physicalRegressionSfgParameters]

/-- Direct expansion of `SourceBridgeSfg.lean:87-92` gives SFG-TR's drop field `-32 / 91`. -/
lemma physicalRegression_sfg_dropTransfer :
    sfgAddDropTransfer physicalRegressionSfgParameters = -32 / 91 := by
  have hRealSqrt : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
    apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2
    norm_num
  have hSqrt : Complex.sqrt (1 / 4) = 1 / 2 := by
    have hNonneg : (0 : ℂ) ≤ 1 / 4 := by
      norm_num [Complex.nonneg_iff]
    calc
      Complex.sqrt (1 / 4) = (Real.sqrt (1 / 4 : ℝ) : ℂ) := by
        rw [Complex.sqrt_of_nonneg hNonneg]
        norm_num
      _ = 1 / 2 := by rw [hRealSqrt]; norm_num
  rw [sfgAddDropTransfer]
  norm_num [physicalRegressionSfgParameters, hSqrt]

/-- Independent SFG-TR and netlist expansions agree at the physical zero-phase point. -/
lemma physicalRegression_sfg_dropTransfer_eq_response :
    sfgAddDropTransfer
        (SfgParameters.ofAddDrop physicalRegressionAddDrop.toParameters) =
      (addDropTopology physicalRegressionAddDrop).responseTransform
        physicalRegression_addDrop_isWellPosed
        (Outgoing.mk (addDropDropChannel physicalRegressionAddDrop))
        (Incident.mk (addDropInputChannel physicalRegressionAddDrop)) := by
  rw [physicalRegression_toSfgParameters,
    physicalRegression_sfg_dropTransfer,
    physicalRegression_addDrop_responses.2]

end Microring

end

end Optics
