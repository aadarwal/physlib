/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Components.DirectionalCouplerPhysicalPower
public import Physlib.Optics.Components.MatchedPropagationPhysicalPower
public import Physlib.Optics.Network.Coherency
public import Physlib.Optics.Systems.MachZehnder.Construction

/-!
# Mach--Zehnder powers and balanced specializations

## i. Overview

This file derives powers and canonical Mach--Zehnder specializations from the two-coupler,
two-arm netlist and N5 amplitudes in `MachZehnder.Construction`. No interferometer transfer or
power formula is stored in a definition. System losslessness is obtained through N6's
`FlatNetlist.externalScatteringMatrix_isLossless_of_components_isLossless`, after classifying the
four N7 physical scattering components.

The directional-coupler cross coefficient is the exact `-I * k` definition at
`Physlib/Optics/Components/DirectionalCoupler.lean:68-77`. A model using the opposite cross phase
is related by an arm gauge and has the same power-transfer law. The arm coefficient is the N7
fixed-carrier `a * exp (-I * φ)` law at
`Physlib/Optics/Components/MatchedPropagation.lean:93-103`.

This is the Physlib extension recorded at `goal.md:2150-2160`, not a HOL-corpus parity result.
Powers are normalized modal powers, not electromagnetic powers without a separate Poynting
normalization. The model has no polarization or dispersion, and attenuation occurs only through
the explicitly parameterized arm amplitude factors. The phase parameters are fixed-frequency
path phases, not time-domain delays.

## ii. Key results

- `MachZehnder.output_powers`: both right-output powers for arbitrary coherent left input.
- `MachZehnder.balanced_output_amplitudes`: the balanced phase-difference transfer law.
- `MachZehnder.balanced_output_powers`: the balanced cosine phase-sensing law.
- `MachZehnder.balanced_phase_zero_dark_port` and `balanced_phase_pi_dark_port`: exact dark ports.
- `MachZehnder.balanced_output_power_balance`: N6 lossless balance at every arm phase.

## iii. Table of contents

- A. Output powers and balanced phase specializations
- B. N6 conservation, identifiability, and coherency

## iv. References

The component definitions and program-ledger locations are quoted above. The conservation path is
the N6 network theorem, not an interferometer-specific response-matrix unitarity calculation.
-/

@[expose] public section

namespace Optics

noncomputable section

namespace MachZehnder

/-! ## A. Output powers and balanced phase specializations -/

/-- The two right-output normalized modal powers are the squared moduli of the amplitudes
extracted by N5. -/
lemma output_powers (p : Parameters) (first second : ℂ) :
    Complex.normSq
        (((netlist p).responseTransform (isWellPosed p)).toLinearMap
          (leftInput p first second) (externalOutgoingEquiv p .outputFirst)) =
      Complex.normSq
        ((p.outputCoupler.throughAmplitude : ℂ) *
            MatchedPropagation.transmissionCoefficient p.upperArm *
              ((p.inputCoupler.throughAmplitude : ℂ) * first +
                DirectionalCoupler.crossCoefficient p.inputCoupler * second) +
          DirectionalCoupler.crossCoefficient p.outputCoupler *
            MatchedPropagation.transmissionCoefficient p.lowerArm *
              (DirectionalCoupler.crossCoefficient p.inputCoupler * first +
                (p.inputCoupler.throughAmplitude : ℂ) * second)) ∧
      Complex.normSq
          (((netlist p).responseTransform (isWellPosed p)).toLinearMap
            (leftInput p first second) (externalOutgoingEquiv p .outputSecond)) =
        Complex.normSq
          (DirectionalCoupler.crossCoefficient p.outputCoupler *
              MatchedPropagation.transmissionCoefficient p.upperArm *
                ((p.inputCoupler.throughAmplitude : ℂ) * first +
                  DirectionalCoupler.crossCoefficient p.inputCoupler * second) +
            (p.outputCoupler.throughAmplitude : ℂ) *
              MatchedPropagation.transmissionCoefficient p.lowerArm *
                (DirectionalCoupler.crossCoefficient p.inputCoupler * first +
                  (p.inputCoupler.throughAmplitude : ℂ) * second)) := by
  rcases output_amplitudes p first second with ⟨hFirst, hSecond⟩
  exact ⟨congrArg Complex.normSq hFirst, congrArg Complex.normSq hSecond⟩

/-- The fixed-carrier phase factor in real and imaginary coordinates. -/
lemma carrierPhaseFactor_eq_cos_sub_sin_mul_I (phase : Real.Angle) :
    MatchedPropagation.carrierPhaseFactor phase =
      (phase.cos : ℂ) - (phase.sin : ℂ) * Complex.I := by
  rw [MatchedPropagation.carrierPhaseFactor, Real.Angle.coe_toCircle]
  simp [sub_eq_add_neg]

/-- The squared modulus of the difference of two arm phase factors. -/
lemma normSq_carrierPhaseFactor_sub (upper lower : Real.Angle) :
    Complex.normSq
        (MatchedPropagation.carrierPhaseFactor upper -
          MatchedPropagation.carrierPhaseFactor lower) =
      2 * (1 - Real.Angle.cos (upper - lower)) := by
  rw [carrierPhaseFactor_eq_cos_sub_sin_mul_I,
    carrierPhaseFactor_eq_cos_sub_sin_mul_I]
  rw [show upper - lower = upper + -lower by abel, Real.Angle.cos_add]
  simp [Complex.normSq_apply]
  nlinarith [Real.Angle.cos_sq_add_sin_sq upper,
    Real.Angle.cos_sq_add_sin_sq lower]

/-- The squared modulus of the sum of two arm phase factors. -/
lemma normSq_carrierPhaseFactor_add (upper lower : Real.Angle) :
    Complex.normSq
        (MatchedPropagation.carrierPhaseFactor upper +
          MatchedPropagation.carrierPhaseFactor lower) =
      2 * (1 + Real.Angle.cos (upper - lower)) := by
  rw [carrierPhaseFactor_eq_cos_sub_sin_mul_I,
    carrierPhaseFactor_eq_cos_sub_sin_mul_I]
  rw [show upper - lower = upper + -lower by abel, Real.Angle.cos_add]
  simp [Complex.normSq_apply]
  nlinarith [Real.Angle.cos_sq_add_sin_sq upper,
    Real.Angle.cos_sq_add_sin_sq lower]

/-- The canonical 50:50 N7 directional-coupler parameters. -/
def balancedCoupler : DirectionalCoupler.Parameters where
  throughAmplitude := Real.sqrt 2 / 2
  crossAmplitude := Real.sqrt 2 / 2

/-- The canonical 50:50 coupler is unitary in normalized modal power. -/
lemma balancedCoupler_isUnitary : balancedCoupler.IsUnitary := by
  rw [DirectionalCoupler.Parameters.IsUnitary,
    DirectionalCoupler.Parameters.powerFactor]
  change (Real.sqrt 2 / 2) ^ 2 + (Real.sqrt 2 / 2) ^ 2 = 1
  rw [div_pow]
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- The canonical 50:50 coupler lies in the N7 ideal-coupler validity domain. -/
lemma balancedCoupler_isValid : balancedCoupler.IsValid := by
  refine ⟨?_, ?_, balancedCoupler_isUnitary⟩ <;>
    exact div_nonneg (Real.sqrt_nonneg _) (by norm_num)

/-- A unit-amplitude matched-propagation arm with the selected fixed-carrier phase. -/
def losslessArm (phase : Real.Angle) : MatchedPropagation.Parameters where
  amplitudeTransmission := 1
  carrierPathPhase := phase

/-- A unit-amplitude arm lies in the N7 matched-propagation validity domain. -/
lemma losslessArm_isValid (phase : Real.Angle) : (losslessArm phase).IsValid := by
  change 0 ≤ (1 : ℝ) ∧ (1 : ℝ) ≤ 1
  norm_num

/-- A unit-amplitude arm transmits by its fixed-carrier phase factor. -/
lemma losslessArm_transmissionCoefficient (phase : Real.Angle) :
    MatchedPropagation.transmissionCoefficient (losslessArm phase) =
      MatchedPropagation.carrierPhaseFactor phase := by
  simp [MatchedPropagation.transmissionCoefficient, losslessArm]

/-- The canonical balanced Mach--Zehnder with independently selected lossless arm phases. -/
def balancedParameters (upperPhase lowerPhase : Real.Angle) : Parameters where
  inputCoupler := balancedCoupler
  upperArm := losslessArm upperPhase
  lowerArm := losslessArm lowerPhase
  outputCoupler := balancedCoupler

/-- Balanced lossless parameters lie in every N7 component validity domain. -/
lemma balancedParameters_isValid (upperPhase lowerPhase : Real.Angle) :
    (balancedParameters upperPhase lowerPhase).IsValid := by
  exact ⟨balancedCoupler_isValid, losslessArm_isValid upperPhase,
    losslessArm_isValid lowerPhase, balancedCoupler_isValid⟩

/-- Every component of the balanced, unit-amplitude specialization is lossless. -/
lemma balancedParameters_isLossless (upperPhase lowerPhase : Real.Angle) :
    (balancedParameters upperPhase lowerPhase).IsLossless := by
  exact ⟨balancedCoupler_isUnitary, rfl, rfl, balancedCoupler_isUnitary⟩

/-- The balanced Mach--Zehnder transfer amplitudes for excitation of the first left input.

The first output senses the arm-phase-factor difference; the second senses their sum with the
negative-quadrature phase fixed by N7 at
`Physlib/Optics/Components/DirectionalCoupler.lean:68-77`.
-/
lemma balanced_output_amplitudes (upperPhase lowerPhase : Real.Angle) (input : ℂ) :
    ((netlist (balancedParameters upperPhase lowerPhase)).responseTransform
          (isWellPosed (balancedParameters upperPhase lowerPhase))).toLinearMap
        (leftInput (balancedParameters upperPhase lowerPhase) input 0)
          (externalOutgoingEquiv (balancedParameters upperPhase lowerPhase) .outputFirst) =
      (MatchedPropagation.carrierPhaseFactor upperPhase -
          MatchedPropagation.carrierPhaseFactor lowerPhase) * input / 2 ∧
    ((netlist (balancedParameters upperPhase lowerPhase)).responseTransform
          (isWellPosed (balancedParameters upperPhase lowerPhase))).toLinearMap
        (leftInput (balancedParameters upperPhase lowerPhase) input 0)
          (externalOutgoingEquiv (balancedParameters upperPhase lowerPhase) .outputSecond) =
      -Complex.I *
        (MatchedPropagation.carrierPhaseFactor upperPhase +
          MatchedPropagation.carrierPhaseFactor lowerPhase) * input / 2 := by
  rcases output_amplitudes (balancedParameters upperPhase lowerPhase) input 0 with
    ⟨hFirst, hSecond⟩
  have hSqrtSquare : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  constructor
  · refine hFirst.trans ?_
    simp only [balancedParameters, losslessArm_transmissionCoefficient,
      balancedCoupler, DirectionalCoupler.crossCoefficient, mul_zero, add_zero,
      Complex.ofReal_div, Complex.ofReal_ofNat]
    ring_nf
    rw [hSqrtSquare]
    rw [Complex.I_sq]
    ring
  · refine hSecond.trans ?_
    simp only [balancedParameters, losslessArm_transmissionCoefficient,
      balancedCoupler, DirectionalCoupler.crossCoefficient, mul_zero, add_zero,
      Complex.ofReal_div, Complex.ofReal_ofNat]
    ring_nf
    rw [hSqrtSquare]
    ring

/-- The balanced output powers expose the cosine of the arm phase difference. -/
lemma balanced_output_powers (upperPhase lowerPhase : Real.Angle) (input : ℂ) :
    Complex.normSq
        (((netlist (balancedParameters upperPhase lowerPhase)).responseTransform
            (isWellPosed (balancedParameters upperPhase lowerPhase))).toLinearMap
          (leftInput (balancedParameters upperPhase lowerPhase) input 0)
            (externalOutgoingEquiv (balancedParameters upperPhase lowerPhase) .outputFirst)) =
      (1 - Real.Angle.cos (upperPhase - lowerPhase)) / 2 * Complex.normSq input ∧
    Complex.normSq
        (((netlist (balancedParameters upperPhase lowerPhase)).responseTransform
            (isWellPosed (balancedParameters upperPhase lowerPhase))).toLinearMap
          (leftInput (balancedParameters upperPhase lowerPhase) input 0)
            (externalOutgoingEquiv (balancedParameters upperPhase lowerPhase) .outputSecond)) =
      (1 + Real.Angle.cos (upperPhase - lowerPhase)) / 2 *
        Complex.normSq input := by
  rcases balanced_output_amplitudes upperPhase lowerPhase input with
    ⟨hFirst, hSecond⟩
  constructor
  · rw [hFirst, Complex.normSq_div, Complex.normSq_mul,
      normSq_carrierPhaseFactor_sub]
    norm_num
    ring
  · rw [hSecond, Complex.normSq_div, Complex.normSq_mul,
      Complex.normSq_mul, Complex.normSq_neg, Complex.normSq_I,
      normSq_carrierPhaseFactor_add]
    norm_num
    ring

/-- The N7 fixed-carrier phase factor at zero path phase. -/
lemma carrierPhaseFactor_zero :
    MatchedPropagation.carrierPhaseFactor (0 : Real.Angle) = 1 := by
  simp [MatchedPropagation.carrierPhaseFactor]

/-- The N7 fixed-carrier phase factor at a path phase of `π`. -/
lemma carrierPhaseFactor_pi :
    MatchedPropagation.carrierPhaseFactor (Real.pi : Real.Angle) = -1 := by
  rw [MatchedPropagation.carrierPhaseFactor, Real.Angle.neg_coe_pi,
    Real.Angle.coe_toCircle]
  simp

/-- The named balanced Mach--Zehnder point with equal zero arm phases. -/
def balancedPhaseZero : Parameters := balancedParameters 0 0

/-- The phase-zero point is a valid N7 component assembly. -/
lemma balancedPhaseZero_isValid : balancedPhaseZero.IsValid :=
  balancedParameters_isValid 0 0

/-- The phase-zero point is a lossless N7 component assembly. -/
lemma balancedPhaseZero_isLossless : balancedPhaseZero.IsLossless :=
  balancedParameters_isLossless 0 0

/-- The named balanced Mach--Zehnder point with lower-arm phase `π`. -/
def balancedPhasePi : Parameters := balancedParameters 0 (Real.pi : Real.Angle)

/-- The phase-`π` point is a valid N7 component assembly. -/
lemma balancedPhasePi_isValid : balancedPhasePi.IsValid :=
  balancedParameters_isValid 0 (Real.pi : Real.Angle)

/-- The phase-`π` point is a lossless N7 component assembly. -/
lemma balancedPhasePi_isLossless : balancedPhasePi.IsLossless :=
  balancedParameters_isLossless 0 (Real.pi : Real.Angle)

/-- At the balanced equal-phase point, the first output is dark and the second carries the input
with N7's negative-quadrature phase. -/
lemma balanced_phase_zero_output_amplitudes (input : ℂ) :
    ((netlist balancedPhaseZero).responseTransform
          (isWellPosed balancedPhaseZero)).toLinearMap
        (leftInput balancedPhaseZero input 0)
          (externalOutgoingEquiv balancedPhaseZero .outputFirst) = 0 ∧
      ((netlist balancedPhaseZero).responseTransform
          (isWellPosed balancedPhaseZero)).toLinearMap
        (leftInput balancedPhaseZero input 0)
          (externalOutgoingEquiv balancedPhaseZero .outputSecond) =
        -Complex.I * input := by
  rcases balanced_output_amplitudes 0 0 input with ⟨hFirst, hSecond⟩
  constructor
  · change ((netlist (balancedParameters 0 0)).responseTransform
        (isWellPosed (balancedParameters 0 0))).toLinearMap
      (leftInput (balancedParameters 0 0) input 0)
        (externalOutgoingEquiv (balancedParameters 0 0) .outputFirst) = 0
    rw [hFirst, carrierPhaseFactor_zero]
    ring
  · change ((netlist (balancedParameters 0 0)).responseTransform
        (isWellPosed (balancedParameters 0 0))).toLinearMap
      (leftInput (balancedParameters 0 0) input 0)
        (externalOutgoingEquiv (balancedParameters 0 0) .outputSecond) = _
    rw [hSecond, carrierPhaseFactor_zero]
    ring

/-- The first output is the exact dark port at the balanced phase-zero point. -/
lemma balanced_phase_zero_dark_port (input : ℂ) :
    ((netlist balancedPhaseZero).responseTransform
          (isWellPosed balancedPhaseZero)).toLinearMap
        (leftInput balancedPhaseZero input 0)
          (externalOutgoingEquiv balancedPhaseZero .outputFirst) = 0 :=
  (balanced_phase_zero_output_amplitudes input).1

/-- At a lower-arm phase of `π`, the first balanced output carries the input and the second is
dark. -/
lemma balanced_phase_pi_output_amplitudes (input : ℂ) :
    ((netlist balancedPhasePi).responseTransform
          (isWellPosed balancedPhasePi)).toLinearMap
        (leftInput balancedPhasePi input 0)
          (externalOutgoingEquiv balancedPhasePi .outputFirst) = input ∧
      ((netlist balancedPhasePi).responseTransform
          (isWellPosed balancedPhasePi)).toLinearMap
        (leftInput balancedPhasePi input 0)
          (externalOutgoingEquiv balancedPhasePi .outputSecond) = 0 := by
  rcases balanced_output_amplitudes 0 (Real.pi : Real.Angle) input with
    ⟨hFirst, hSecond⟩
  constructor
  · change ((netlist (balancedParameters 0 (Real.pi : Real.Angle))).responseTransform
        (isWellPosed (balancedParameters 0 (Real.pi : Real.Angle)))).toLinearMap
      (leftInput (balancedParameters 0 (Real.pi : Real.Angle)) input 0)
        (externalOutgoingEquiv (balancedParameters 0 (Real.pi : Real.Angle))
          .outputFirst) = input
    rw [hFirst, carrierPhaseFactor_zero, carrierPhaseFactor_pi]
    ring
  · change ((netlist (balancedParameters 0 (Real.pi : Real.Angle))).responseTransform
        (isWellPosed (balancedParameters 0 (Real.pi : Real.Angle)))).toLinearMap
      (leftInput (balancedParameters 0 (Real.pi : Real.Angle)) input 0)
        (externalOutgoingEquiv (balancedParameters 0 (Real.pi : Real.Angle))
          .outputSecond) = 0
    rw [hSecond, carrierPhaseFactor_zero, carrierPhaseFactor_pi]
    ring

/-- The second output is the exact dark port at the balanced phase-`π` point. -/
lemma balanced_phase_pi_dark_port (input : ℂ) :
    ((netlist balancedPhasePi).responseTransform
          (isWellPosed balancedPhasePi)).toLinearMap
        (leftInput balancedPhasePi input 0)
          (externalOutgoingEquiv balancedPhasePi .outputSecond) = 0 :=
  (balanced_phase_pi_output_amplitudes input).2

/-! ## B. N6 conservation, identifiability, and coherency -/

/-- The N7 losslessness hypotheses on the four parameters classify every netlist component as
lossless. -/
lemma components_isLossless (p : Parameters) (hp : p.IsLossless) :
    ∀ component : Component, ((components p).scattering component).IsLossless := by
  rcases hp with ⟨hInput, hUpper, hLower, hOutput⟩
  intro component
  cases component
  · exact (ScatteringMatrix.isLossless_reindex_iff couplerChannelEquiv
      (DirectionalCoupler.physicalScattering p.inputCoupler Unit)).mpr
        (DirectionalCoupler.physicalScattering_isLossless p.inputCoupler hInput)
  · exact (ScatteringMatrix.isLossless_reindex_iff armChannelEquiv
      (MatchedPropagation.physicalScattering p.upperArm Unit)).mpr
        (MatchedPropagation.physicalScattering_isLossless p.upperArm hUpper)
  · exact (ScatteringMatrix.isLossless_reindex_iff armChannelEquiv
      (MatchedPropagation.physicalScattering p.lowerArm Unit)).mpr
        (MatchedPropagation.physicalScattering_isLossless p.lowerArm hLower)
  · exact (ScatteringMatrix.isLossless_reindex_iff couplerChannelEquiv
      (DirectionalCoupler.physicalScattering p.outputCoupler Unit)).mpr
        (DirectionalCoupler.physicalScattering_isLossless p.outputCoupler hOutput)

/-- N6 conservation packages the external Mach--Zehnder response as a lossless scattering
matrix whenever all four N7 components are lossless. -/
lemma externalScatteringMatrix_isLossless (p : Parameters) (hp : p.IsLossless) :
    ((netlist p).externalScatteringMatrix (isWellPosed p)).IsLossless := by
  apply (netlist p).externalScatteringMatrix_isLossless_of_components_isLossless
    (isWellPosed p)
  simpa only [netlist] using components_isLossless p hp

/-- The response transform preserves normalized modal power, obtained only by unpacking the N6
external-scattering losslessness theorem. -/
lemma responseTransform_isPowerPreserving (p : Parameters) (hp : p.IsLossless) :
    ((netlist p).responseTransform (isWellPosed p)).IsPowerPreserving := by
  have hExternal := externalScatteringMatrix_isLossless p hp
  rw [ScatteringMatrix.isLossless_iff_isPowerPreserving] at hExternal
  change (((netlist p).responseTransform (isWellPosed p)).reindex
    Incident.channelEquiv Outgoing.channelEquiv).IsPowerPreserving at hExternal
  exact (ModeTransform.isPowerPreserving_reindex_iff Incident.channelEquiv
    Outgoing.channelEquiv ((netlist p).responseTransform (isWellPosed p))).mp hExternal

/-- For nonzero first-port excitation, the ratio of the two arm phase factors is recoverable from
the two balanced complex outputs. Thus the arm phase difference is identifiable modulo the
`Real.Angle` period. -/
lemma balanced_phase_factor_ratio_eq_output_ratio
    (upperPhase lowerPhase : Real.Angle) (input : ℂ) (hInput : input ≠ 0) :
    let firstOutput :=
      ((netlist (balancedParameters upperPhase lowerPhase)).responseTransform
          (isWellPosed (balancedParameters upperPhase lowerPhase))).toLinearMap
        (leftInput (balancedParameters upperPhase lowerPhase) input 0)
          (externalOutgoingEquiv (balancedParameters upperPhase lowerPhase) .outputFirst)
    let secondOutput :=
      ((netlist (balancedParameters upperPhase lowerPhase)).responseTransform
          (isWellPosed (balancedParameters upperPhase lowerPhase))).toLinearMap
        (leftInput (balancedParameters upperPhase lowerPhase) input 0)
          (externalOutgoingEquiv (balancedParameters upperPhase lowerPhase) .outputSecond)
    MatchedPropagation.carrierPhaseFactor lowerPhase /
        MatchedPropagation.carrierPhaseFactor upperPhase =
      (-firstOutput + Complex.I * secondOutput) /
        (firstOutput + Complex.I * secondOutput) := by
  dsimp only
  rcases balanced_output_amplitudes upperPhase lowerPhase input with
    ⟨hFirst, hSecond⟩
  rw [hFirst, hSecond]
  have hUpper : MatchedPropagation.carrierPhaseFactor upperPhase ≠ 0 := by
    intro hZero
    have hNorm := MatchedPropagation.normSq_carrierPhaseFactor upperPhase
    simp [hZero] at hNorm
  ring_nf
  field_simp [hUpper, hInput]
  rw [Complex.I_sq]
  ring

set_option maxHeartbeats 800000 in
/-- A left-incident field produces no reflected amplitudes at either left external port. -/
lemma reflected_amplitudes_eq_zero (p : Parameters) (first second : ℂ) :
    ((netlist p).responseTransform (isWellPosed p)).toLinearMap
          (leftInput p first second) (externalOutgoingEquiv p .inputFirst) = 0 ∧
      ((netlist p).responseTransform (isWellPosed p)).toLinearMap
          (leftInput p first second) (externalOutgoingEquiv p .inputSecond) = 0 := by
  let input := leftInput p first second
  let incident := (netlist p).incidentSolutionBlockFormula (isWellPosed p) |>.toLinearMap input
  let outgoing := (netlist p).scatteringTransform.toLinearMap incident
  have hFeedback : (netlist p).feedbackOperator.toLinearMap incident =
      (netlist p).inputExposure.toLinearMap input := by
    change (netlist p).feedbackOperator.toLinearMap
      ((netlist p).incidentSolutionBlockFormula (isWellPosed p) |>.toLinearMap input) = _
    change (netlist p).feedbackOperator.toLinearMap
      (ModeTransform.toLinearMap
        ((netlist p).feedbackInverse (isWellPosed p) * (netlist p).inputExposure)
          input) = _
    rw [ModeTransform.toLinearMap_mul_apply,
      (netlist p).feedbackOperator_apply_feedbackInverse]
  have hAssembly : incident =
      (netlist p).connections.incidentAssembly outgoing input := by
    exact incident_eq_incidentAssembly_of_feedbackEquation p input incident hFeedback
  have hExternal (port : ExternalPort) :
      incident (Incident.mk (externalAmbientChannel p port)) =
        input (externalIncidentEquiv p port) := by
    rw [hAssembly]
    have h := (netlist p).connections.incidentAssembly_apply_external outgoing input
      (externalChannel p port)
    rw [externalChannel_val] at h
    rw [externalIncidentEquiv_apply]
    exact h
  have hConnected (channel : (netlist p).ConnectedChannel) :
      incident (Incident.mk ((netlist p).connections.channelEmbedding channel)) =
        outgoing (Outgoing.mk ((netlist p).connections.channelEmbedding
          ((netlist p).connections.mateEquiv channel))) := by
    rw [hAssembly]
    exact (netlist p).connections.incidentAssembly_apply_connected_channel
      outgoing input channel
  have hOutputRightFirst :
      incident (Incident.mk (ambientChannel p .outputCoupler (couplerChannel 2))) = 0 := by
    have h := hExternal .outputFirst
    change incident (Incident.mk (ambientChannel p .outputCoupler (couplerChannel 2))) =
      input (externalIncidentEquiv p .outputFirst) at h
    exact h.trans (by simpa only [input] using leftInput_apply p first second .outputFirst)
  have hOutputRightSecond :
      incident (Incident.mk (ambientChannel p .outputCoupler (couplerChannel 3))) = 0 := by
    have h := hExternal .outputSecond
    change incident (Incident.mk (ambientChannel p .outputCoupler (couplerChannel 3))) =
      input (externalIncidentEquiv p .outputSecond) at h
    exact h.trans (by simpa only [input] using leftInput_apply p first second .outputSecond)
  have hOutputOutgoingLeftFirst :
      outgoing (Outgoing.mk (ambientChannel p .outputCoupler (couplerChannel 0))) = 0 := by
    change (netlist p).scatteringTransform.toLinearMap incident
      (Outgoing.mk (ambientChannel p .outputCoupler (couplerChannel 0))) = 0
    rw [scatteringTransform_apply_component p incident .outputCoupler (couplerChannel 0)]
    change (couplerScattering p.outputCoupler).toModeTransform.toLinearMap
      (localIncident p incident .outputCoupler) (couplerChannel 0) = 0
    rw [couplerScattering_apply_leftFirst, localIncident_apply, localIncident_apply,
      hOutputRightFirst, hOutputRightSecond]
    simp
  have hOutputOutgoingLeftSecond :
      outgoing (Outgoing.mk (ambientChannel p .outputCoupler (couplerChannel 1))) = 0 := by
    change (netlist p).scatteringTransform.toLinearMap incident
      (Outgoing.mk (ambientChannel p .outputCoupler (couplerChannel 1))) = 0
    rw [scatteringTransform_apply_component p incident .outputCoupler (couplerChannel 1)]
    change (couplerScattering p.outputCoupler).toModeTransform.toLinearMap
      (localIncident p incident .outputCoupler) (couplerChannel 1) = 0
    rw [couplerScattering_apply_leftSecond, localIncident_apply, localIncident_apply,
      hOutputRightFirst, hOutputRightSecond]
    simp
  have hUpperRight :
      incident (Incident.mk (ambientChannel p .upperArm (armChannel 1))) = 0 := by
    have h := hConnected ⟨Connection.upperOutput, Sum.inl ()⟩
    change incident (Incident.mk (ambientChannel p .upperArm (armChannel 1))) =
      outgoing (Outgoing.mk (ambientChannel p .outputCoupler (couplerChannel 0))) at h
    exact h.trans hOutputOutgoingLeftFirst
  have hLowerRight :
      incident (Incident.mk (ambientChannel p .lowerArm (armChannel 1))) = 0 := by
    have h := hConnected ⟨Connection.lowerOutput, Sum.inl ()⟩
    change incident (Incident.mk (ambientChannel p .lowerArm (armChannel 1))) =
      outgoing (Outgoing.mk (ambientChannel p .outputCoupler (couplerChannel 1))) at h
    exact h.trans hOutputOutgoingLeftSecond
  have hUpperOutgoingLeft :
      outgoing (Outgoing.mk (ambientChannel p .upperArm (armChannel 0))) = 0 := by
    change (netlist p).scatteringTransform.toLinearMap incident
      (Outgoing.mk (ambientChannel p .upperArm (armChannel 0))) = 0
    rw [scatteringTransform_apply_component p incident .upperArm (armChannel 0)]
    change (armScattering p.upperArm).toModeTransform.toLinearMap
      (localIncident p incident .upperArm) (armChannel 0) = 0
    rw [armScattering_apply_left, localIncident_apply, hUpperRight]
    simp
  have hLowerOutgoingLeft :
      outgoing (Outgoing.mk (ambientChannel p .lowerArm (armChannel 0))) = 0 := by
    change (netlist p).scatteringTransform.toLinearMap incident
      (Outgoing.mk (ambientChannel p .lowerArm (armChannel 0))) = 0
    rw [scatteringTransform_apply_component p incident .lowerArm (armChannel 0)]
    change (armScattering p.lowerArm).toModeTransform.toLinearMap
      (localIncident p incident .lowerArm) (armChannel 0) = 0
    rw [armScattering_apply_left, localIncident_apply, hLowerRight]
    simp
  have hInputRightFirst :
      incident (Incident.mk (ambientChannel p .inputCoupler (couplerChannel 2))) = 0 := by
    have h := hConnected ⟨Connection.upperInput, Sum.inl ()⟩
    change incident (Incident.mk (ambientChannel p .inputCoupler (couplerChannel 2))) =
      outgoing (Outgoing.mk (ambientChannel p .upperArm (armChannel 0))) at h
    exact h.trans hUpperOutgoingLeft
  have hInputRightSecond :
      incident (Incident.mk (ambientChannel p .inputCoupler (couplerChannel 3))) = 0 := by
    have h := hConnected ⟨Connection.lowerInput, Sum.inl ()⟩
    change incident (Incident.mk (ambientChannel p .inputCoupler (couplerChannel 3))) =
      outgoing (Outgoing.mk (ambientChannel p .lowerArm (armChannel 0))) at h
    exact h.trans hLowerOutgoingLeft
  have hInputOutgoingFirst :
      outgoing (Outgoing.mk (ambientChannel p .inputCoupler (couplerChannel 0))) = 0 := by
    change (netlist p).scatteringTransform.toLinearMap incident
      (Outgoing.mk (ambientChannel p .inputCoupler (couplerChannel 0))) = 0
    rw [scatteringTransform_apply_component p incident .inputCoupler (couplerChannel 0)]
    change (couplerScattering p.inputCoupler).toModeTransform.toLinearMap
      (localIncident p incident .inputCoupler) (couplerChannel 0) = 0
    rw [couplerScattering_apply_leftFirst, localIncident_apply, localIncident_apply,
      hInputRightFirst, hInputRightSecond]
    simp
  have hInputOutgoingSecond :
      outgoing (Outgoing.mk (ambientChannel p .inputCoupler (couplerChannel 1))) = 0 := by
    change (netlist p).scatteringTransform.toLinearMap incident
      (Outgoing.mk (ambientChannel p .inputCoupler (couplerChannel 1))) = 0
    rw [scatteringTransform_apply_component p incident .inputCoupler (couplerChannel 1)]
    change (couplerScattering p.inputCoupler).toModeTransform.toLinearMap
      (localIncident p incident .inputCoupler) (couplerChannel 1) = 0
    rw [couplerScattering_apply_leftSecond, localIncident_apply, localIncident_apply,
      hInputRightFirst, hInputRightSecond]
    simp
  have hResponse :
      ((netlist p).responseTransform (isWellPosed p)).toLinearMap input =
        (netlist p).outputReadout.toLinearMap outgoing := by
    calc
      ((netlist p).responseTransform (isWellPosed p)).toLinearMap input =
          ((netlist p).responseBlockFormula (isWellPosed p)).toLinearMap input :=
        congrArg (fun transform => transform.toLinearMap input)
          ((netlist p).responseTransform_eq_blockFormula (isWellPosed p))
      _ = (netlist p).outputReadout.toLinearMap
          (((netlist p).outgoingSolutionBlockFormula (isWellPosed p)).toLinearMap input) :=
        (netlist p).responseBlockFormula_apply (isWellPosed p) input
      _ = (netlist p).outputReadout.toLinearMap
          ((netlist p).scatteringTransform.toLinearMap
            (((netlist p).incidentSolutionBlockFormula (isWellPosed p)).toLinearMap input)) :=
        congrArg ((netlist p).outputReadout.toLinearMap)
          ((netlist p).outgoingSolutionBlockFormula_apply (isWellPosed p) input)
      _ = (netlist p).outputReadout.toLinearMap outgoing := rfl
  have hReadout (port : ExternalPort) :
      (netlist p).outputReadout.toLinearMap outgoing (externalOutgoingEquiv p port) =
        outgoing (Outgoing.mk (externalAmbientChannel p port)) := by
    rw [PortConnectionFamily.externalOutgoingReadout_apply]
    rfl
  constructor
  · change ((netlist p).responseTransform (isWellPosed p)).toLinearMap input
      (externalOutgoingEquiv p .inputFirst) = 0
    rw [hResponse, hReadout]
    exact hInputOutgoingFirst
  · change ((netlist p).responseTransform (isWellPosed p)).toLinearMap input
      (externalOutgoingEquiv p .inputSecond) = 0
    rw [hResponse, hReadout]
    exact hInputOutgoingSecond

/-- A sum over the four named external ports in their declared order. -/
lemma sum_externalPort (value : ExternalPort → ℝ) :
    ∑ port, value port =
      value .inputFirst + value .inputSecond + value .outputFirst + value .outputSecond := by
  classical
  rw [show (Finset.univ : Finset ExternalPort) =
      {.inputFirst, .inputSecond, .outputFirst, .outputSecond} by
    ext port
    fin_cases port <;> simp]
  simp only [Finset.mem_insert, reduceCtorEq, Finset.mem_singleton, or_self,
    not_false_eq_true, Finset.sum_insert, Finset.sum_singleton]
  ring

/-- The coherent left excitation carries the sum of its two incident modal powers. -/
lemma leftInput_power (p : Parameters) (first second : ℂ) :
    (leftInput p first second).power =
      Complex.normSq first + Complex.normSq second := by
  rw [ModeAmplitude.power_eq_sum_normSq]
  rw [← Fintype.sum_equiv (externalIncidentEquiv p)
    (fun port => Complex.normSq
      (leftInput p first second (externalIncidentEquiv p port)))
    (fun endpoint => Complex.normSq (leftInput p first second endpoint))
    (fun _ => rfl)]
  rw [sum_externalPort]
  simp only [leftInput_apply, Complex.normSq_zero, add_zero]

/-- N6 losslessness gives exact two-output power balance for arbitrary coherent excitation at the
two left ports. -/
lemma lossless_output_power_balance (p : Parameters) (hp : p.IsLossless)
    (first second : ℂ) :
    Complex.normSq
        (((netlist p).responseTransform (isWellPosed p)).toLinearMap
          (leftInput p first second) (externalOutgoingEquiv p .outputFirst)) +
      Complex.normSq
        (((netlist p).responseTransform (isWellPosed p)).toLinearMap
          (leftInput p first second) (externalOutgoingEquiv p .outputSecond)) =
      Complex.normSq first + Complex.normSq second := by
  have hPower := responseTransform_isPowerPreserving p hp (leftInput p first second)
  rw [ModeAmplitude.power_eq_sum_normSq, ModeAmplitude.power_eq_sum_normSq] at hPower
  rw [← Fintype.sum_equiv (externalOutgoingEquiv p)
    (fun port => Complex.normSq
      (((netlist p).responseTransform (isWellPosed p)).toLinearMap
        (leftInput p first second) (externalOutgoingEquiv p port)))
    (fun endpoint => Complex.normSq
      (((netlist p).responseTransform (isWellPosed p)).toLinearMap
        (leftInput p first second) endpoint))
    (fun _ => rfl)] at hPower
  rw [← Fintype.sum_equiv (externalIncidentEquiv p)
    (fun port => Complex.normSq
      (leftInput p first second (externalIncidentEquiv p port)))
    (fun endpoint => Complex.normSq (leftInput p first second endpoint))
    (fun _ => rfl)] at hPower
  rw [sum_externalPort, sum_externalPort] at hPower
  rcases reflected_amplitudes_eq_zero p first second with ⟨hFirst, hSecond⟩
  rw [hFirst, hSecond] at hPower
  simp only [Complex.normSq_zero, zero_add, leftInput_apply, add_zero] at hPower
  exact hPower

/-- A lossless Mach--Zehnder sends all power from one left input into the two right outputs. -/
lemma lossless_single_input_output_power_balance (p : Parameters) (hp : p.IsLossless)
    (input : ℂ) :
    Complex.normSq
        (((netlist p).responseTransform (isWellPosed p)).toLinearMap
          (leftInput p input 0) (externalOutgoingEquiv p .outputFirst)) +
      Complex.normSq
        (((netlist p).responseTransform (isWellPosed p)).toLinearMap
          (leftInput p input 0) (externalOutgoingEquiv p .outputSecond)) =
      Complex.normSq input := by
  simpa only [Complex.normSq_zero, add_zero] using
    lossless_output_power_balance p hp input 0

/-- At every arm phase, the two balanced output powers sum to the incident power. -/
lemma balanced_output_power_balance (upperPhase lowerPhase : Real.Angle) (input : ℂ) :
    Complex.normSq
        (((netlist (balancedParameters upperPhase lowerPhase)).responseTransform
            (isWellPosed (balancedParameters upperPhase lowerPhase))).toLinearMap
          (leftInput (balancedParameters upperPhase lowerPhase) input 0)
            (externalOutgoingEquiv (balancedParameters upperPhase lowerPhase) .outputFirst)) +
      Complex.normSq
        (((netlist (balancedParameters upperPhase lowerPhase)).responseTransform
            (isWellPosed (balancedParameters upperPhase lowerPhase))).toLinearMap
          (leftInput (balancedParameters upperPhase lowerPhase) input 0)
            (externalOutgoingEquiv (balancedParameters upperPhase lowerPhase) .outputSecond)) =
      Complex.normSq input :=
  lossless_single_input_output_power_balance
    (balancedParameters upperPhase lowerPhase)
    (balancedParameters_isLossless upperPhase lowerPhase) input

/-- N6 coherency transport identifies each coherent output-channel power with the squared modulus
of the N5 response amplitude. -/
lemma coherent_output_channelPower (p : Parameters)
    (input : ModeAmplitude (netlist p).ExternalIncident) (port : ExternalPort) :
    ((netlist p).responseCoherency (isWellPosed p)
        (CoherencyMatrix.ofAmplitude input)).channelPower (externalOutgoingEquiv p port) =
      Complex.normSq
        (((netlist p).responseTransform (isWellPosed p)).toLinearMap input
          (externalOutgoingEquiv p port)) := by
  exact CoherencyMatrix.channelPower_map_ofAmplitude input
    ((netlist p).responseTransform (isWellPosed p)) (externalOutgoingEquiv p port)

/-- N6 coherency transport makes the power at every named output additive for mutually
decorrelated input data. -/
lemma incoherent_output_channelPower_add (p : Parameters)
    (first second : CoherencyMatrix (netlist p).ExternalIncident) (port : ExternalPort) :
    ((netlist p).responseCoherency (isWellPosed p)
        (first.incoherentSum second)).channelPower (externalOutgoingEquiv p port) =
      ((netlist p).responseCoherency (isWellPosed p) first).channelPower
          (externalOutgoingEquiv p port) +
        ((netlist p).responseCoherency (isWellPosed p) second).channelPower
          (externalOutgoingEquiv p port) := by
  exact CoherencyMatrix.channelPower_map_incoherentSum first second
    ((netlist p).responseTransform (isWellPosed p)) (externalOutgoingEquiv p port)

end MachZehnder

end

end Optics
