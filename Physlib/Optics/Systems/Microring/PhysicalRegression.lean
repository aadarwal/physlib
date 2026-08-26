/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Systems.Microring.AddDropRegression
public import Physlib.Optics.Systems.Microring.AllPassRegression
public import Physlib.Optics.Systems.Microring.PhysicalRealization

/-!
# Symbolic regressions for physical microring realization

## i. Overview

These fixtures pin the conversion from physical path data to the S2 field parameters, the
distinction between amplitude and power quantities, and the independent travelling-field
relations. The canonical `3-4-5` couplers are combined with exact logarithmic attenuation data so
that the derived field factors are `1 / 2` and `1 / 4`. Separate rational optical-depth fixtures
use `alpha * L = 0` and normalized optical paths `n_eff * L / lambda = 0, 1 / 2`, giving real phase
lifts `0` and `pi` exactly.

The relation anchors substitute internal fields by hand. The response anchors reuse the S2
regressions that eliminate the concrete netlist channel equations directly; they do not rewrite
with `allPass_physicalResponse_eq_transfer` or `addDrop_physicalResponse_eq_transfers`.

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
- `physicalRegression_allPass_toParameters`: the named S2 one-bus parameter point.
- `physicalRegression_addDrop_toParameters`: the named S2 two-bus parameter point.
- `physicalRegression_allPass_fieldRelation`: direct one-bus internal-field solution.
- `physicalRegression_addDrop_fieldRelation`: direct two-bus internal-field solution.
- `physicalRegression_allPass_response`: independently eliminated N5 response `1 / 7`.
- `physicalRegression_addDrop_responses`: independently eliminated N5 responses.

## iii. Table of contents

- A. Exact attenuation and coupling data
- B. Exact zero- and half-turn physical phase points
- C. Maps to the named S2 parameters
- D. Direct internal-field anchors
- E. Independent N5 response anchors

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

/-- Unit path length with power coefficient `2 * log 2` and zero phase lift. -/
def physicalRegressionHalfAttenuation : PhysicalParameters where
  pathLength := 1
  powerAttenuationCoefficient := 2 * Real.log 2
  effectiveIndex := 0
  wavelength := 1

/-- Direct exponential evaluation gives the field factor `1 / 2`. -/
lemma physicalRegression_halfAttenuation :
    physicalRegressionHalfAttenuation.fieldAttenuation = 1 / 2 := by
  rw [PhysicalParameters.fieldAttenuation]
  change Real.exp (-(2 * Real.log 2) * 1 / 2) = 1 / 2
  rw [show -(2 * Real.log 2) * 1 / 2 = -Real.log 2 by ring,
    Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  norm_num

/-- Direct exponential evaluation gives the corresponding power factor `1 / 4`. -/
lemma physicalRegression_halfPowerAttenuation :
    physicalRegressionHalfAttenuation.powerAttenuation = 1 / 4 := by
  rw [PhysicalParameters.powerAttenuation]
  change Real.exp (-(2 * Real.log 2) * 1) = 1 / 4
  rw [show -(2 * Real.log 2) * 1 = -(Real.log 2 + Real.log 2) by ring,
    Real.exp_neg, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  norm_num

/-- At this point the explicit field square equals the power attenuation. -/
lemma physicalRegression_halfAttenuation_sq :
    physicalRegressionHalfAttenuation.fieldAttenuation ^ 2 =
      physicalRegressionHalfAttenuation.powerAttenuation := by
  rw [physicalRegression_halfAttenuation, physicalRegression_halfPowerAttenuation]
  norm_num

/-- Unit path length with power coefficient `4 * log 2` and zero phase lift. -/
def physicalRegressionQuarterAttenuation : PhysicalParameters where
  pathLength := 1
  powerAttenuationCoefficient := 4 * Real.log 2
  effectiveIndex := 0
  wavelength := 1

/-- Direct exponential evaluation gives the field factor `1 / 4`. -/
lemma physicalRegression_quarterAttenuation :
    physicalRegressionQuarterAttenuation.fieldAttenuation = 1 / 4 := by
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
       fieldAttenuation := physicalRegressionHalfAttenuation.fieldAttenuation
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
       fieldAttenuation := physicalRegressionQuarterAttenuation.fieldAttenuation
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
       fieldAttenuation := physicalRegressionQuarterAttenuation.fieldAttenuation
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

end Microring

end

end Optics
