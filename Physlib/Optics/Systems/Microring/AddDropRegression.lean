/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Systems.Microring.AddDrop

/-!
# Regression tests for the add-drop microring

## i. Overview

The exact fixture uses two unitary `3-4-5` couplers and total field attenuation `1 / 4`,
split as `1 / 2` on each arc. At zero round-trip phase the circulation gain is `9 / 100`,
the through transfer is `45 / 91`, and the drop transfer is `-32 / 91`. At phase `pi`, the
corresponding values are `-9 / 100`, `75 / 109`, and `32 * I / 109`.

The scalar checks directly expand the N7 component coefficients and transfer definitions. The
response fixtures separately solve the N5 channel equations at zero phase, so changing an explicit
feedback pairing can break them. A structural sentinel separately pins both endpoints of every
connection; this claim is about that sentinel, not about numeric detectability of every arc-port
permutation. A further independent fixture sums the concrete geometric series with circulation
gain `9 / 100`.

“Resonance” and “antiresonance” below name the zero- and half-turn phase points. The fixtures
do not prove an extremum, minimum, maximum, or global resonance characterization. They make no
frequency-sweep, power-balance, linewidth, dispersion, or material-realization claim.

## ii. Key results

- `addDropRegression_resonance_responseTransform_entry_through`: direct through-response check.
- `addDropRegression_resonance_responseTransform_entry_drop`: direct drop-response check.
- `addDropRegression_resonance_roundTripSeries`: direct geometric-series evaluation.
- `addDropRegression_resonance_response_through_eq_series`: independent views agree.
- `addDropRegression_antiresonance_throughTransfer`: the half-turn through amplitude.
- `addDropRegression_antiresonance_dropTransfer`: the half-turn drop amplitude.

## iii. Table of contents

- A. Exact zero-phase fixture
- B. Direct N5 response and convergent-series anchors
- C. Exact half-turn fixture

## iv. References

These exact values are source-neutral phase-point regressions. The response and series anchors,
rather than the scalar transfer checks alone, pin the explicit N5 feedback construction.
-/

@[expose] public section

namespace Optics

noncomputable section

namespace AddDrop

/-! ## A. Exact zero-phase fixture -/

/-- Two `3-4-5` couplers, quarter round-trip field retention, and zero phase. -/
def addDropRegressionResonanceParameters : Parameters where
  inputThroughAmplitude := 3 / 5
  inputCrossAmplitude := 4 / 5
  dropThroughAmplitude := 3 / 5
  dropCrossAmplitude := 4 / 5
  fieldAttenuation := 1 / 4
  roundTripPhase := 0

/-- The structural fixture pins both endpoints of all four feedback connections. -/
lemma addDropRegression_connections_pairs :
    ((connections addDropRegressionResonanceParameters).connection
        Connection.inputToFirst).left =
      ⟨Component.inputCoupler, DirectionalCoupler.Port.rightSecond⟩ ∧
    ((connections addDropRegressionResonanceParameters).connection
        Connection.inputToFirst).right =
      ⟨Component.firstArc, MatchedPropagation.Port.left⟩ ∧
    ((connections addDropRegressionResonanceParameters).connection
        Connection.firstToDrop).left =
      ⟨Component.firstArc, MatchedPropagation.Port.right⟩ ∧
    ((connections addDropRegressionResonanceParameters).connection
        Connection.firstToDrop).right =
      ⟨Component.dropCoupler, DirectionalCoupler.Port.leftSecond⟩ ∧
    ((connections addDropRegressionResonanceParameters).connection
        Connection.dropToSecond).left =
      ⟨Component.dropCoupler, DirectionalCoupler.Port.rightSecond⟩ ∧
    ((connections addDropRegressionResonanceParameters).connection
        Connection.dropToSecond).right =
      ⟨Component.secondArc, MatchedPropagation.Port.left⟩ ∧
    ((connections addDropRegressionResonanceParameters).connection
        Connection.secondToInput).left =
      ⟨Component.secondArc, MatchedPropagation.Port.right⟩ ∧
    ((connections addDropRegressionResonanceParameters).connection
        Connection.secondToInput).right =
      ⟨Component.inputCoupler, DirectionalCoupler.Port.leftSecond⟩ := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The zero-phase fixture satisfies the attenuation bounds and all four N7 validity predicates. -/
lemma addDropRegression_resonance_isValid :
    addDropRegressionResonanceParameters.IsValid := by
  have hSqrt : Real.sqrt 4 = 2 := by
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
  constructor
  · norm_num [addDropRegressionResonanceParameters, Parameters.inputCoupler,
      DirectionalCoupler.Parameters.IsValid, DirectionalCoupler.Parameters.IsUnitary,
      DirectionalCoupler.Parameters.powerFactor]
  · constructor
    · norm_num [addDropRegressionResonanceParameters, Parameters.dropCoupler,
        DirectionalCoupler.Parameters.IsValid, DirectionalCoupler.Parameters.IsUnitary,
        DirectionalCoupler.Parameters.powerFactor]
    · constructor
      · norm_num [addDropRegressionResonanceParameters]
      · constructor
        · norm_num [addDropRegressionResonanceParameters]
        · constructor <;>
            norm_num [addDropRegressionResonanceParameters, Parameters.firstPropagation,
              Parameters.secondPropagation, Parameters.halfArcAttenuation,
              MatchedPropagation.Parameters.IsValid, hSqrt]

/-- Direct expansion gives the first zero-phase arc coefficient `1 / 2`. -/
lemma addDropRegression_resonance_firstArcCoefficient :
    addDropRegressionResonanceParameters.firstArcCoefficient = 1 / 2 := by
  have hSqrt : Real.sqrt 4 = 2 := by
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
  norm_num [addDropRegressionResonanceParameters, Parameters.firstArcCoefficient,
    Parameters.firstPropagation, Parameters.halfArcAttenuation, Parameters.halfArcPhase,
    MatchedPropagation.transmissionCoefficient, MatchedPropagation.carrierPhaseFactor, hSqrt]

/-- Direct expansion gives the second zero-phase arc coefficient `1 / 2`. -/
lemma addDropRegression_resonance_secondArcCoefficient :
    addDropRegressionResonanceParameters.secondArcCoefficient = 1 / 2 := by
  have hSqrt : Real.sqrt 4 = 2 := by
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
  norm_num [addDropRegressionResonanceParameters, Parameters.secondArcCoefficient,
    Parameters.secondPropagation, Parameters.halfArcAttenuation, Parameters.halfArcPhase,
    MatchedPropagation.transmissionCoefficient, MatchedPropagation.carrierPhaseFactor, hSqrt]

/-- Direct expansion gives the zero-phase round-trip propagation coefficient `1 / 4`. -/
lemma addDropRegression_resonance_roundTripCoefficient :
    addDropRegressionResonanceParameters.roundTripCoefficient = 1 / 4 := by
  rw [Parameters.roundTripCoefficient,
    addDropRegression_resonance_firstArcCoefficient,
    addDropRegression_resonance_secondArcCoefficient]
  norm_num

/-- Direct expansion gives the zero-phase circulation gain `9 / 100`. -/
lemma addDropRegression_resonance_loopGain :
    addDropRegressionResonanceParameters.loopGain = 9 / 100 := by
  rw [Parameters.loopGain, addDropRegression_resonance_roundTripCoefficient]
  norm_num [addDropRegressionResonanceParameters]

/-- Direct expansion gives the zero-phase feedback denominator `91 / 100`. -/
lemma addDropRegression_resonance_denominator :
    addDropRegressionResonanceParameters.denominator = 91 / 100 := by
  rw [Parameters.denominator, addDropRegression_resonance_loopGain]
  norm_num

/-- Direct expansion gives the zero-phase through transfer `45 / 91`. -/
lemma addDropRegression_resonance_throughTransfer :
    throughTransfer addDropRegressionResonanceParameters = 45 / 91 := by
  rw [throughTransfer, addDropRegression_resonance_roundTripCoefficient,
    addDropRegression_resonance_denominator]
  simp [addDropRegressionResonanceParameters, Parameters.inputCoupler,
    DirectionalCoupler.crossCoefficient]
  rw [mul_pow, Complex.I_sq]
  norm_num

/-- Direct expansion gives the zero-phase drop transfer `-32 / 91`. -/
lemma addDropRegression_resonance_dropTransfer :
    dropTransfer addDropRegressionResonanceParameters = -32 / 91 := by
  rw [dropTransfer, addDropRegression_resonance_firstArcCoefficient,
    addDropRegression_resonance_denominator]
  simp [addDropRegressionResonanceParameters, Parameters.inputCoupler,
    Parameters.dropCoupler, DirectionalCoupler.crossCoefficient]
  ring_nf
  rw [Complex.I_sq]
  norm_num

/-- The exact zero-phase fixture satisfies the N5 well-posedness gate. -/
lemma addDropRegression_resonance_isWellPosed :
    (netlist addDropRegressionResonanceParameters).IsWellPosed := by
  apply isWellPosed_of_hasNonzeroDenominator
  rw [Parameters.HasNonzeroDenominator, addDropRegression_resonance_denominator]
  norm_num

/-! ## B. Direct N5 response and convergent-series anchors -/

/-- Direct N5 channel elimination gives the zero-phase input-to-through entry `45 / 91`. -/
lemma addDropRegression_resonance_responseTransform_entry_through :
    (netlist addDropRegressionResonanceParameters).responseTransform
        addDropRegression_resonance_isWellPosed
        (Outgoing.mk (throughChannel addDropRegressionResonanceParameters))
        (Incident.mk (inputChannel addDropRegressionResonanceParameters)) =
      45 / 91 := by
  let p := addDropRegressionResonanceParameters
  let output := (netlist p).responseTransform
    addDropRegression_resonance_isWellPosed |>.toLinearMap (inputAmplitude p 1)
  have hMember : (inputAmplitude p 1, output) ∈ (netlist p).behavior := by
    rw [← (netlist p).toBehavior_responseTransform
      addDropRegression_resonance_isWellPosed,
      ModeTransform.mem_toBehavior_iff_toLinearMap]
  rcases ((netlist p).mem_behavior_iff_equations (inputAmplitude p 1) output).mp
      hMember with ⟨incident, outgoing, hScattering, hAssembly, hOutput⟩
  have hAssembly' :
      incident = (netlist p).connections.incidentAssembly outgoing (inputAmplitude p 1) := by
    simpa only [PortConnectionFamily.incidentAssembly] using hAssembly
  have hInput := congrArg
    (fun state => state (Incident.mk
      (inputCouplerChannel p DirectionalCoupler.Port.leftFirst))) hAssembly'
  rw [incidentAssembly_apply_input_leftFirst, inputAmplitude_apply_input] at hInput
  have hAdd := congrArg
    (fun state => state (Incident.mk
      (dropCouplerChannel p DirectionalCoupler.Port.leftFirst))) hAssembly'
  rw [incidentAssembly_apply_drop_leftFirst, inputAmplitude_apply_add] at hAdd
  have hFirst := congrArg
    (fun state => state (Incident.mk
      (firstArcChannel p MatchedPropagation.Port.left))) hAssembly'
  rw [incidentAssembly_apply_firstArc_left,
    scatteringEquation_inputCoupler_rightSecond p incident outgoing hScattering,
    hInput] at hFirst
  have hDropRing := congrArg
    (fun state => state (Incident.mk
      (dropCouplerChannel p DirectionalCoupler.Port.leftSecond))) hAssembly'
  rw [incidentAssembly_apply_dropCoupler_leftSecond,
    scatteringEquation_firstArc_right p incident outgoing hScattering,
    hFirst] at hDropRing
  have hSecond := congrArg
    (fun state => state (Incident.mk
      (secondArcChannel p MatchedPropagation.Port.left))) hAssembly'
  rw [incidentAssembly_apply_secondArc_left,
    scatteringEquation_dropCoupler_rightSecond p incident outgoing hScattering,
    hAdd, hDropRing, mul_zero, zero_add] at hSecond
  have hReturn := congrArg
    (fun state => state (Incident.mk
      (inputCouplerChannel p DirectionalCoupler.Port.leftSecond))) hAssembly'
  rw [incidentAssembly_apply_inputCoupler_leftSecond,
    scatteringEquation_secondArc_right p incident outgoing hScattering,
    hSecond] at hReturn
  have hReturn' := hReturn
  simp only [p, addDropRegression_resonance_firstArcCoefficient,
    addDropRegression_resonance_secondArcCoefficient] at hReturn'
  norm_num [addDropRegressionResonanceParameters, Parameters.inputCoupler,
    DirectionalCoupler.crossCoefficient] at hReturn'
  have hLoopSolution :
      incident
          (Incident.mk (inputCouplerChannel p DirectionalCoupler.Port.leftSecond)) =
        -(12 / 91 : ℂ) * Complex.I := by
    linear_combination (100 / 91 : ℂ) * hReturn'
  have hThrough :=
    scatteringEquation_inputCoupler_rightFirst p incident outgoing hScattering
  rw [hInput] at hThrough
  have hReadout := congrArg (fun state => state (Outgoing.mk (throughChannel p))) hOutput
  rw [outputReadout_apply_through] at hReadout
  have hOutputCoordinate :
      ((netlist p).responseTransform addDropRegression_resonance_isWellPosed).toLinearMap
          (inputAmplitude p 1) (Outgoing.mk (throughChannel p)) =
        45 / 91 := by
    rw [hReadout, hThrough, hLoopSolution]
    simp [p, addDropRegressionResonanceParameters, Parameters.inputCoupler,
      DirectionalCoupler.crossCoefficient]
    ring_nf
    rw [Complex.I_sq]
    norm_num
  simpa [p, inputAmplitude, Matrix.toLpLin_apply] using hOutputCoordinate

/-- Direct N5 channel elimination gives the zero-phase input-to-drop entry `-32 / 91`. -/
lemma addDropRegression_resonance_responseTransform_entry_drop :
    (netlist addDropRegressionResonanceParameters).responseTransform
        addDropRegression_resonance_isWellPosed
        (Outgoing.mk (dropChannel addDropRegressionResonanceParameters))
        (Incident.mk (inputChannel addDropRegressionResonanceParameters)) =
      -32 / 91 := by
  let p := addDropRegressionResonanceParameters
  let output := (netlist p).responseTransform
    addDropRegression_resonance_isWellPosed |>.toLinearMap (inputAmplitude p 1)
  have hMember : (inputAmplitude p 1, output) ∈ (netlist p).behavior := by
    rw [← (netlist p).toBehavior_responseTransform
      addDropRegression_resonance_isWellPosed,
      ModeTransform.mem_toBehavior_iff_toLinearMap]
  rcases ((netlist p).mem_behavior_iff_equations (inputAmplitude p 1) output).mp
      hMember with ⟨incident, outgoing, hScattering, hAssembly, hOutput⟩
  have hAssembly' :
      incident = (netlist p).connections.incidentAssembly outgoing (inputAmplitude p 1) := by
    simpa only [PortConnectionFamily.incidentAssembly] using hAssembly
  have hInput := congrArg
    (fun state => state (Incident.mk
      (inputCouplerChannel p DirectionalCoupler.Port.leftFirst))) hAssembly'
  rw [incidentAssembly_apply_input_leftFirst, inputAmplitude_apply_input] at hInput
  have hAdd := congrArg
    (fun state => state (Incident.mk
      (dropCouplerChannel p DirectionalCoupler.Port.leftFirst))) hAssembly'
  rw [incidentAssembly_apply_drop_leftFirst, inputAmplitude_apply_add] at hAdd
  have hFirst := congrArg
    (fun state => state (Incident.mk
      (firstArcChannel p MatchedPropagation.Port.left))) hAssembly'
  rw [incidentAssembly_apply_firstArc_left,
    scatteringEquation_inputCoupler_rightSecond p incident outgoing hScattering,
    hInput] at hFirst
  have hDropRing := congrArg
    (fun state => state (Incident.mk
      (dropCouplerChannel p DirectionalCoupler.Port.leftSecond))) hAssembly'
  rw [incidentAssembly_apply_dropCoupler_leftSecond,
    scatteringEquation_firstArc_right p incident outgoing hScattering,
    hFirst] at hDropRing
  have hSecond := congrArg
    (fun state => state (Incident.mk
      (secondArcChannel p MatchedPropagation.Port.left))) hAssembly'
  rw [incidentAssembly_apply_secondArc_left,
    scatteringEquation_dropCoupler_rightSecond p incident outgoing hScattering,
    hAdd, hDropRing, mul_zero, zero_add] at hSecond
  have hReturn := congrArg
    (fun state => state (Incident.mk
      (inputCouplerChannel p DirectionalCoupler.Port.leftSecond))) hAssembly'
  rw [incidentAssembly_apply_inputCoupler_leftSecond,
    scatteringEquation_secondArc_right p incident outgoing hScattering,
    hSecond] at hReturn
  have hReturn' := hReturn
  simp only [p, addDropRegression_resonance_firstArcCoefficient,
    addDropRegression_resonance_secondArcCoefficient] at hReturn'
  norm_num [addDropRegressionResonanceParameters, Parameters.inputCoupler,
    DirectionalCoupler.crossCoefficient] at hReturn'
  have hLoopSolution :
      incident
          (Incident.mk (inputCouplerChannel p DirectionalCoupler.Port.leftSecond)) =
        -(12 / 91 : ℂ) * Complex.I := by
    linear_combination (100 / 91 : ℂ) * hReturn'
  rw [hLoopSolution] at hDropRing
  have hDrop := scatteringEquation_dropCoupler_rightFirst p incident outgoing hScattering
  rw [hAdd, hDropRing, mul_zero, zero_add] at hDrop
  have hReadout := congrArg (fun state => state (Outgoing.mk (dropChannel p))) hOutput
  rw [outputReadout_apply_drop] at hReadout
  have hOutputCoordinate :
      ((netlist p).responseTransform addDropRegression_resonance_isWellPosed).toLinearMap
          (inputAmplitude p 1) (Outgoing.mk (dropChannel p)) =
        -32 / 91 := by
    rw [hReadout, hDrop]
    simp only [p, addDropRegression_resonance_firstArcCoefficient]
    simp [addDropRegressionResonanceParameters, Parameters.inputCoupler,
      Parameters.dropCoupler, DirectionalCoupler.crossCoefficient]
    ring_nf
    rw [Complex.I_sq]
    norm_num
  simpa [p, inputAmplitude, Matrix.toLpLin_apply] using hOutputCoordinate

/-- The concrete zero-phase circulation gain satisfies the strict convergence gate. -/
lemma addDropRegression_resonance_isContractive :
    addDropRegressionResonanceParameters.IsContractive := by
  rw [Parameters.IsContractive, addDropRegression_resonance_loopGain]
  norm_num

/-- Summing the concrete geometric series with ratio `9 / 100` gives `100 / 91`. -/
lemma addDropRegression_resonance_roundTripSeries :
    roundTripSeries addDropRegressionResonanceParameters = 100 / 91 := by
  rw [roundTripSeries, addDropRegression_resonance_loopGain]
  rw [tsum_geometric_of_norm_lt_one (by norm_num : ‖(9 / 100 : ℂ)‖ < 1)]
  apply Complex.ext <;> norm_num

/-- Direct expansion of the concrete through-series expression gives `45 / 91`. -/
lemma addDropRegression_resonance_throughTransferSeries :
    throughTransferSeries addDropRegressionResonanceParameters = 45 / 91 := by
  rw [throughTransferSeries, addDropRegression_resonance_roundTripCoefficient,
    addDropRegression_resonance_roundTripSeries]
  simp [addDropRegressionResonanceParameters, Parameters.inputCoupler,
    DirectionalCoupler.crossCoefficient]
  rw [mul_pow, Complex.I_sq]
  norm_num

/-- Direct expansion of the concrete drop-series expression gives `-32 / 91`. -/
lemma addDropRegression_resonance_dropTransferSeries :
    dropTransferSeries addDropRegressionResonanceParameters = -32 / 91 := by
  rw [dropTransferSeries, addDropRegression_resonance_firstArcCoefficient,
    addDropRegression_resonance_roundTripSeries]
  simp [addDropRegressionResonanceParameters, Parameters.inputCoupler,
    Parameters.dropCoupler, DirectionalCoupler.crossCoefficient]
  ring_nf
  rw [Complex.I_sq]
  norm_num

/-- The independently evaluated through response and convergent series agree at zero phase. -/
lemma addDropRegression_resonance_response_through_eq_series :
    (netlist addDropRegressionResonanceParameters).responseTransform
        addDropRegression_resonance_isWellPosed
        (Outgoing.mk (throughChannel addDropRegressionResonanceParameters))
        (Incident.mk (inputChannel addDropRegressionResonanceParameters)) =
      throughTransferSeries addDropRegressionResonanceParameters := by
  rw [addDropRegression_resonance_responseTransform_entry_through,
    addDropRegression_resonance_throughTransferSeries]

/-- The independently evaluated drop response and convergent series agree at zero phase. -/
lemma addDropRegression_resonance_response_drop_eq_series :
    (netlist addDropRegressionResonanceParameters).responseTransform
        addDropRegression_resonance_isWellPosed
        (Outgoing.mk (dropChannel addDropRegressionResonanceParameters))
        (Incident.mk (inputChannel addDropRegressionResonanceParameters)) =
      dropTransferSeries addDropRegressionResonanceParameters := by
  rw [addDropRegression_resonance_responseTransform_entry_drop,
    addDropRegression_resonance_dropTransferSeries]

/-! ## C. Exact half-turn fixture -/

/-- The same exact add-drop fixture with a half-turn round-trip phase. -/
def addDropRegressionAntiresonanceParameters : Parameters where
  inputThroughAmplitude := 3 / 5
  inputCrossAmplitude := 4 / 5
  dropThroughAmplitude := 3 / 5
  dropCrossAmplitude := 4 / 5
  fieldAttenuation := 1 / 4
  roundTripPhase := Real.pi

/-- The half-turn fixture satisfies the attenuation bounds and all four N7 validity predicates. -/
lemma addDropRegression_antiresonance_isValid :
    addDropRegressionAntiresonanceParameters.IsValid := by
  have hSqrt : Real.sqrt 4 = 2 := by
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
  constructor
  · norm_num [addDropRegressionAntiresonanceParameters, Parameters.inputCoupler,
      DirectionalCoupler.Parameters.IsValid, DirectionalCoupler.Parameters.IsUnitary,
      DirectionalCoupler.Parameters.powerFactor]
  · constructor
    · norm_num [addDropRegressionAntiresonanceParameters, Parameters.dropCoupler,
        DirectionalCoupler.Parameters.IsValid, DirectionalCoupler.Parameters.IsUnitary,
        DirectionalCoupler.Parameters.powerFactor]
    · constructor
      · norm_num [addDropRegressionAntiresonanceParameters]
      · constructor
        · norm_num [addDropRegressionAntiresonanceParameters]
        · constructor <;>
            norm_num [addDropRegressionAntiresonanceParameters, Parameters.firstPropagation,
              Parameters.secondPropagation, Parameters.halfArcAttenuation,
              MatchedPropagation.Parameters.IsValid, hSqrt]

/-- Direct expansion gives the first half-turn arc coefficient `-I / 2`. -/
lemma addDropRegression_antiresonance_firstArcCoefficient :
    addDropRegressionAntiresonanceParameters.firstArcCoefficient = -Complex.I / 2 := by
  have hSqrt : Real.sqrt 4 = 2 := by
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
  simp [addDropRegressionAntiresonanceParameters, Parameters.firstArcCoefficient,
    Parameters.firstPropagation, Parameters.halfArcAttenuation, Parameters.halfArcPhase,
    MatchedPropagation.transmissionCoefficient, MatchedPropagation.carrierPhaseFactor,
    Real.Angle.toCircle_coe, Circle.coe_exp, hSqrt]
  apply Complex.ext <;> norm_num

/-- Direct expansion gives the second half-turn arc coefficient `-I / 2`. -/
lemma addDropRegression_antiresonance_secondArcCoefficient :
    addDropRegressionAntiresonanceParameters.secondArcCoefficient = -Complex.I / 2 := by
  have hSqrt : Real.sqrt 4 = 2 := by
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
  simp [addDropRegressionAntiresonanceParameters, Parameters.secondArcCoefficient,
    Parameters.secondPropagation, Parameters.halfArcAttenuation, Parameters.halfArcPhase,
    MatchedPropagation.transmissionCoefficient, MatchedPropagation.carrierPhaseFactor,
    Real.Angle.toCircle_coe, Circle.coe_exp, hSqrt]
  apply Complex.ext <;> norm_num

/-- Direct expansion gives the half-turn round-trip propagation coefficient `-1 / 4`. -/
lemma addDropRegression_antiresonance_roundTripCoefficient :
    addDropRegressionAntiresonanceParameters.roundTripCoefficient = -1 / 4 := by
  rw [Parameters.roundTripCoefficient,
    addDropRegression_antiresonance_firstArcCoefficient,
    addDropRegression_antiresonance_secondArcCoefficient]
  ring_nf
  rw [Complex.I_sq]
  norm_num

/-- Direct expansion gives the half-turn circulation gain `-9 / 100`. -/
lemma addDropRegression_antiresonance_loopGain :
    addDropRegressionAntiresonanceParameters.loopGain = -9 / 100 := by
  rw [Parameters.loopGain, addDropRegression_antiresonance_roundTripCoefficient]
  norm_num [addDropRegressionAntiresonanceParameters]

/-- Direct expansion gives the half-turn feedback denominator `109 / 100`. -/
lemma addDropRegression_antiresonance_denominator :
    addDropRegressionAntiresonanceParameters.denominator = 109 / 100 := by
  rw [Parameters.denominator, addDropRegression_antiresonance_loopGain]
  norm_num

/-- Direct expansion gives the half-turn through transfer `75 / 109`. -/
lemma addDropRegression_antiresonance_throughTransfer :
    throughTransfer addDropRegressionAntiresonanceParameters = 75 / 109 := by
  rw [throughTransfer, addDropRegression_antiresonance_roundTripCoefficient,
    addDropRegression_antiresonance_denominator]
  simp [addDropRegressionAntiresonanceParameters, Parameters.inputCoupler,
    DirectionalCoupler.crossCoefficient]
  rw [mul_pow, Complex.I_sq]
  norm_num

/-- Direct expansion gives the half-turn drop transfer `32 * I / 109`. -/
lemma addDropRegression_antiresonance_dropTransfer :
    dropTransfer addDropRegressionAntiresonanceParameters = 32 * Complex.I / 109 := by
  rw [dropTransfer, addDropRegression_antiresonance_firstArcCoefficient,
    addDropRegression_antiresonance_denominator]
  simp [addDropRegressionAntiresonanceParameters, Parameters.inputCoupler,
    Parameters.dropCoupler, DirectionalCoupler.crossCoefficient]
  ring_nf
  have hIcube : Complex.I ^ 3 = -Complex.I := by
    calc
      Complex.I ^ 3 = Complex.I ^ 2 * Complex.I := by ring
      _ = -Complex.I := by rw [Complex.I_sq]; ring
  rw [hIcube]
  ring

end AddDrop

end

end Optics
