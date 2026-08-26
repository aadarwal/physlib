/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Systems.MachZehnder.Basic

/-!
# Symbolic regressions for the Mach--Zehnder interferometer

## i. Overview

These regressions pin row `S-01` at the balanced field-amplitude point. The phase-zero and
phase-`π` anchors independently extract incident and outgoing states from the N4 behavior
equations, traverse the declared connections, and read the actual N5 response. They do not invoke
the headline transfer result or its balanced and named-point corollaries. Thus a changed pairing or
port map can fail the exact negative-quadrature convention pinned at
`Physlib/Optics/Components/DirectionalCoupler.lean:68-77`.

The all-phase power check is an N6 API fixture through
`MachZehnder.lossless_single_input_output_power_balance`; it is not convention-sensitive wiring
evidence. It does not establish unitarity by checking an interferometer-specific response formula.
The ratio-shape check is bound to the actual two response coordinates and verifies recovery of the
arm phase-factor ratio.

This is a Physlib extension regression, not a HOL-corpus parity result. Powers are normalized
modal powers, not electromagnetic powers without a Poynting normalization. The fixtures have no
polarization or dispersion, and loss is absent because both arm amplitude factors are exactly
one.

## ii. Key results

- `machZehnderRegression_phase_zero_output_amplitudes`: the first balanced output is dark.
- `machZehnderRegression_phase_pi_output_amplitudes`: the second balanced output is dark.
- `machZehnderRegression_power_balance`: the two output powers sum to input power at every phase.
- `machZehnderRegression_phase_factor_ratio`: the balanced output ratio identifies arm phase.

## iii. Table of contents

- A. Hand-expanded component values
- B. Exact balanced phase points
- C. N6 power balance and phase-ratio identifiability

## iv. References

Row `S-01` is declared at `goal.md:2482`; the S1 extension milestone is at `goal.md:2150-2160`.
-/

@[expose] public section

namespace Optics

noncomputable section

namespace MachZehnder

/-!
## A. Hand-expanded component values
-/

/-- The balanced through coefficient times the pinned N7 cross coefficient is exactly
`-I / 2`. -/
lemma machZehnderRegression_balanced_through_mul_cross :
    (balancedCoupler.throughAmplitude : ℂ) *
        DirectionalCoupler.crossCoefficient balancedCoupler = -Complex.I / 2 := by
  have hSqrtSquare : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  simp only [balancedCoupler, DirectionalCoupler.crossCoefficient,
    Complex.ofReal_div, Complex.ofReal_ofNat]
  ring_nf
  rw [hSqrtSquare]
  ring

/-- Direct expansion of the N7 phase factor gives `1` at zero and `-1` at `π`. -/
lemma machZehnderRegression_carrierPhaseFactor_points :
    MatchedPropagation.carrierPhaseFactor (0 : Real.Angle) = 1 ∧
      MatchedPropagation.carrierPhaseFactor (Real.pi : Real.Angle) = -1 := by
  constructor
  · simp [MatchedPropagation.carrierPhaseFactor]
  · rw [MatchedPropagation.carrierPhaseFactor, Real.Angle.neg_coe_pi,
      Real.Angle.coe_toCircle]
    simp

/-!
## B. Exact balanced phase points
-/

/-- The actual N5 response exposes incident and outgoing states satisfying the raw N4 channel
equations. This helper contains no Mach--Zehnder transfer formula. -/
lemma machZehnderRegression_response_equations (p : Parameters)
    (drive : ModeAmplitude (netlist p).ExternalIncident) :
    let response :=
      ((netlist p).responseTransform (isWellPosed p)).toLinearMap drive
    ∃ incident outgoing,
      outgoing = (netlist p).scatteringTransform.toLinearMap incident ∧
        incident = (netlist p).connections.incidentAssembly outgoing drive ∧
          response = (netlist p).outputReadout.toLinearMap outgoing := by
  let response := ((netlist p).responseTransform (isWellPosed p)).toLinearMap drive
  change ∃ incident outgoing,
    outgoing = (netlist p).scatteringTransform.toLinearMap incident ∧
      incident = (netlist p).connections.incidentAssembly outgoing drive ∧
        response = (netlist p).outputReadout.toLinearMap outgoing
  have hMember : (drive, response) ∈ (netlist p).behavior := by
    rw [← (netlist p).toBehavior_responseTransform (isWellPosed p),
      ModeTransform.mem_toBehavior_iff_toLinearMap]
  rcases ((netlist p).mem_behavior_iff_equations drive response).mp hMember with
    ⟨incident, outgoing, hScattering, hAssembly, hOutput⟩
  refine ⟨incident, outgoing, hScattering, ?_, hOutput⟩
  simpa only [PortConnectionFamily.incidentAssembly] using hAssembly

/-- Row `S-01`: hand expansion of the N5 transfer at equal zero phases gives a dark first output
and a negative-quadrature second output. -/
lemma machZehnderRegression_phase_zero_output_amplitudes (input : ℂ) :
    ((netlist balancedPhaseZero).responseTransform
          (isWellPosed balancedPhaseZero)).toLinearMap
        (leftInput balancedPhaseZero input 0)
          (externalOutgoingEquiv balancedPhaseZero .outputFirst) = 0 ∧
      ((netlist balancedPhaseZero).responseTransform
          (isWellPosed balancedPhaseZero)).toLinearMap
        (leftInput balancedPhaseZero input 0)
          (externalOutgoingEquiv balancedPhaseZero .outputSecond) =
        -Complex.I * input := by
  let p := balancedPhaseZero
  let drive := leftInput p input 0
  let response := ((netlist p).responseTransform (isWellPosed p)).toLinearMap drive
  change response (externalOutgoingEquiv p .outputFirst) = 0 ∧
    response (externalOutgoingEquiv p .outputSecond) = -Complex.I * input
  -- Start from the raw N4 behavior equations for the actual N5 response.
  rcases machZehnderRegression_response_equations p drive with
    ⟨incident, outgoing, hScattering, hAssembly, hOutput⟩
  have hExternal (port : ExternalPort) :
      incident (Incident.mk (externalAmbientChannel p port)) =
        drive (externalIncidentEquiv p port) := by
    rw [hAssembly]
    have h := (netlist p).connections.incidentAssembly_apply_external outgoing drive
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
      outgoing drive channel
  have hReadout (port : ExternalPort) :
      response (externalOutgoingEquiv p port) =
        outgoing (Outgoing.mk (externalAmbientChannel p port)) := by
    have h := congrArg (fun amplitude => amplitude (externalOutgoingEquiv p port)) hOutput
    change response (externalOutgoingEquiv p port) =
      (netlist p).outputReadout.toLinearMap outgoing (externalOutgoingEquiv p port) at h
    rw [PortConnectionFamily.externalOutgoingReadout_apply] at h
    exact h
  have hInputFirst :
      incident (Incident.mk (ambientChannel p .inputCoupler (couplerChannel 0))) = input := by
    have h := hExternal .inputFirst
    change incident (Incident.mk (ambientChannel p .inputCoupler (couplerChannel 0))) =
      drive (externalIncidentEquiv p .inputFirst) at h
    exact h.trans (by simpa only [drive] using leftInput_apply p input 0 .inputFirst)
  have hInputSecond :
      incident (Incident.mk (ambientChannel p .inputCoupler (couplerChannel 1))) = 0 := by
    have h := hExternal .inputSecond
    change incident (Incident.mk (ambientChannel p .inputCoupler (couplerChannel 1))) =
      drive (externalIncidentEquiv p .inputSecond) at h
    exact h.trans (by simpa only [drive] using leftInput_apply p input 0 .inputSecond)
  -- Traverse the declared input-coupler and arm connections coordinate by coordinate.
  rcases inputCoupler_outgoing_right p incident with ⟨hLaunchUpper, hLaunchLower⟩
  rw [← hScattering, hInputFirst, hInputSecond] at hLaunchUpper hLaunchLower
  have hUpperLeft :
      incident (Incident.mk (ambientChannel p .upperArm (armChannel 0))) =
        (p.inputCoupler.throughAmplitude : ℂ) * input := by
    have h := hConnected ⟨Connection.upperInput, Sum.inr ()⟩
    change incident (Incident.mk (ambientChannel p .upperArm (armChannel 0))) =
      outgoing (Outgoing.mk (ambientChannel p .inputCoupler (couplerChannel 2))) at h
    exact h.trans (hLaunchUpper.trans (by simp only [mul_zero, add_zero]))
  have hLowerLeft :
      incident (Incident.mk (ambientChannel p .lowerArm (armChannel 0))) =
        DirectionalCoupler.crossCoefficient p.inputCoupler * input := by
    have h := hConnected ⟨Connection.lowerInput, Sum.inr ()⟩
    change incident (Incident.mk (ambientChannel p .lowerArm (armChannel 0))) =
      outgoing (Outgoing.mk (ambientChannel p .inputCoupler (couplerChannel 3))) at h
    exact h.trans (hLaunchLower.trans (by simp only [mul_zero, add_zero]))
  have hUpperOutgoing := upperArm_outgoing_right p incident
  have hLowerOutgoing := lowerArm_outgoing_right p incident
  rw [← hScattering, hUpperLeft] at hUpperOutgoing
  rw [← hScattering, hLowerLeft] at hLowerOutgoing
  have hOutputLeftFirst :
      incident (Incident.mk (ambientChannel p .outputCoupler (couplerChannel 0))) =
        MatchedPropagation.transmissionCoefficient p.upperArm *
          (p.inputCoupler.throughAmplitude : ℂ) * input := by
    have h := hConnected ⟨Connection.upperOutput, Sum.inr ()⟩
    change incident (Incident.mk (ambientChannel p .outputCoupler (couplerChannel 0))) =
      outgoing (Outgoing.mk (ambientChannel p .upperArm (armChannel 1))) at h
    exact h.trans (hUpperOutgoing.trans (by ring))
  have hOutputLeftSecond :
      incident (Incident.mk (ambientChannel p .outputCoupler (couplerChannel 1))) =
        MatchedPropagation.transmissionCoefficient p.lowerArm *
          DirectionalCoupler.crossCoefficient p.inputCoupler * input := by
    have h := hConnected ⟨Connection.lowerOutput, Sum.inr ()⟩
    change incident (Incident.mk (ambientChannel p .outputCoupler (couplerChannel 1))) =
      outgoing (Outgoing.mk (ambientChannel p .lowerArm (armChannel 1))) at h
    exact h.trans (hLowerOutgoing.trans (by ring))
  -- Apply the output coupler, then read the two declared external output coordinates.
  rcases outputCoupler_outgoing_right p incident with ⟨hOutputFirst, hOutputSecond⟩
  rw [← hScattering, hOutputLeftFirst, hOutputLeftSecond] at hOutputFirst hOutputSecond
  have hReadoutFirst := hReadout .outputFirst
  have hReadoutSecond := hReadout .outputSecond
  change response (externalOutgoingEquiv p .outputFirst) =
    outgoing (Outgoing.mk (ambientChannel p .outputCoupler (couplerChannel 2))) at hReadoutFirst
  change response (externalOutgoingEquiv p .outputSecond) =
    outgoing (Outgoing.mk (ambientChannel p .outputCoupler (couplerChannel 3))) at hReadoutSecond
  have hSqrtSquare : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  constructor
  · rw [hReadoutFirst, hOutputFirst]
    simp only [p, balancedPhaseZero, balancedParameters, losslessArm,
      MatchedPropagation.transmissionCoefficient, balancedCoupler,
      DirectionalCoupler.crossCoefficient, Complex.ofReal_div, Complex.ofReal_ofNat]
    simp only [MatchedPropagation.carrierPhaseFactor, neg_zero, Real.Angle.toCircle_zero,
      Circle.coe_one]
    ring_nf
    rw [hSqrtSquare, Complex.I_sq]
    ring
  · rw [hReadoutSecond, hOutputSecond]
    simp only [p, balancedPhaseZero, balancedParameters, losslessArm,
      MatchedPropagation.transmissionCoefficient, balancedCoupler,
      DirectionalCoupler.crossCoefficient, Complex.ofReal_div, Complex.ofReal_ofNat]
    simp only [MatchedPropagation.carrierPhaseFactor, neg_zero, Real.Angle.toCircle_zero,
      Circle.coe_one]
    ring_nf
    rw [hSqrtSquare]
    norm_num
    ring

/-- The hand-expanded equal-phase fixture has an exactly dark first output. -/
lemma machZehnderRegression_phase_zero_dark_port (input : ℂ) :
    ((netlist balancedPhaseZero).responseTransform
          (isWellPosed balancedPhaseZero)).toLinearMap
        (leftInput balancedPhaseZero input 0)
          (externalOutgoingEquiv balancedPhaseZero .outputFirst) = 0 :=
  (machZehnderRegression_phase_zero_output_amplitudes input).1

/-- Row `S-01`: hand expansion at a lower-arm phase of `π` sends the input to the first output
and makes the second output dark. -/
lemma machZehnderRegression_phase_pi_output_amplitudes (input : ℂ) :
    ((netlist balancedPhasePi).responseTransform
          (isWellPosed balancedPhasePi)).toLinearMap
        (leftInput balancedPhasePi input 0)
          (externalOutgoingEquiv balancedPhasePi .outputFirst) = input ∧
      ((netlist balancedPhasePi).responseTransform
          (isWellPosed balancedPhasePi)).toLinearMap
        (leftInput balancedPhasePi input 0)
          (externalOutgoingEquiv balancedPhasePi .outputSecond) = 0 := by
  let p := balancedPhasePi
  let drive := leftInput p input 0
  let response := ((netlist p).responseTransform (isWellPosed p)).toLinearMap drive
  change response (externalOutgoingEquiv p .outputFirst) = input ∧
    response (externalOutgoingEquiv p .outputSecond) = 0
  -- Repeat the raw-equation traversal at the distinct phase-`π` anchor.
  rcases machZehnderRegression_response_equations p drive with
    ⟨incident, outgoing, hScattering, hAssembly, hOutput⟩
  have hExternal (port : ExternalPort) :
      incident (Incident.mk (externalAmbientChannel p port)) =
        drive (externalIncidentEquiv p port) := by
    rw [hAssembly]
    have h := (netlist p).connections.incidentAssembly_apply_external outgoing drive
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
      outgoing drive channel
  have hReadout (port : ExternalPort) :
      response (externalOutgoingEquiv p port) =
        outgoing (Outgoing.mk (externalAmbientChannel p port)) := by
    have h := congrArg (fun amplitude => amplitude (externalOutgoingEquiv p port)) hOutput
    change response (externalOutgoingEquiv p port) =
      (netlist p).outputReadout.toLinearMap outgoing (externalOutgoingEquiv p port) at h
    rw [PortConnectionFamily.externalOutgoingReadout_apply] at h
    exact h
  have hInputFirst :
      incident (Incident.mk (ambientChannel p .inputCoupler (couplerChannel 0))) = input := by
    have h := hExternal .inputFirst
    change incident (Incident.mk (ambientChannel p .inputCoupler (couplerChannel 0))) =
      drive (externalIncidentEquiv p .inputFirst) at h
    exact h.trans (by simpa only [drive] using leftInput_apply p input 0 .inputFirst)
  have hInputSecond :
      incident (Incident.mk (ambientChannel p .inputCoupler (couplerChannel 1))) = 0 := by
    have h := hExternal .inputSecond
    change incident (Incident.mk (ambientChannel p .inputCoupler (couplerChannel 1))) =
      drive (externalIncidentEquiv p .inputSecond) at h
    exact h.trans (by simpa only [drive] using leftInput_apply p input 0 .inputSecond)
  -- The routing below names each physical arm connection, so a changed pairing can fail it.
  rcases inputCoupler_outgoing_right p incident with ⟨hLaunchUpper, hLaunchLower⟩
  rw [← hScattering, hInputFirst, hInputSecond] at hLaunchUpper hLaunchLower
  have hUpperLeft :
      incident (Incident.mk (ambientChannel p .upperArm (armChannel 0))) =
        (p.inputCoupler.throughAmplitude : ℂ) * input := by
    have h := hConnected ⟨Connection.upperInput, Sum.inr ()⟩
    change incident (Incident.mk (ambientChannel p .upperArm (armChannel 0))) =
      outgoing (Outgoing.mk (ambientChannel p .inputCoupler (couplerChannel 2))) at h
    exact h.trans (hLaunchUpper.trans (by simp only [mul_zero, add_zero]))
  have hLowerLeft :
      incident (Incident.mk (ambientChannel p .lowerArm (armChannel 0))) =
        DirectionalCoupler.crossCoefficient p.inputCoupler * input := by
    have h := hConnected ⟨Connection.lowerInput, Sum.inr ()⟩
    change incident (Incident.mk (ambientChannel p .lowerArm (armChannel 0))) =
      outgoing (Outgoing.mk (ambientChannel p .inputCoupler (couplerChannel 3))) at h
    exact h.trans (hLaunchLower.trans (by simp only [mul_zero, add_zero]))
  have hUpperOutgoing := upperArm_outgoing_right p incident
  have hLowerOutgoing := lowerArm_outgoing_right p incident
  rw [← hScattering, hUpperLeft] at hUpperOutgoing
  rw [← hScattering, hLowerLeft] at hLowerOutgoing
  have hOutputLeftFirst :
      incident (Incident.mk (ambientChannel p .outputCoupler (couplerChannel 0))) =
        MatchedPropagation.transmissionCoefficient p.upperArm *
          (p.inputCoupler.throughAmplitude : ℂ) * input := by
    have h := hConnected ⟨Connection.upperOutput, Sum.inr ()⟩
    change incident (Incident.mk (ambientChannel p .outputCoupler (couplerChannel 0))) =
      outgoing (Outgoing.mk (ambientChannel p .upperArm (armChannel 1))) at h
    exact h.trans (hUpperOutgoing.trans (by ring))
  have hOutputLeftSecond :
      incident (Incident.mk (ambientChannel p .outputCoupler (couplerChannel 1))) =
        MatchedPropagation.transmissionCoefficient p.lowerArm *
          DirectionalCoupler.crossCoefficient p.inputCoupler * input := by
    have h := hConnected ⟨Connection.lowerOutput, Sum.inr ()⟩
    change incident (Incident.mk (ambientChannel p .outputCoupler (couplerChannel 1))) =
      outgoing (Outgoing.mk (ambientChannel p .lowerArm (armChannel 1))) at h
    exact h.trans (hLowerOutgoing.trans (by ring))
  -- Read the actual outputs before specializing the two component phase factors.
  rcases outputCoupler_outgoing_right p incident with ⟨hOutputFirst, hOutputSecond⟩
  rw [← hScattering, hOutputLeftFirst, hOutputLeftSecond] at hOutputFirst hOutputSecond
  have hReadoutFirst := hReadout .outputFirst
  have hReadoutSecond := hReadout .outputSecond
  change response (externalOutgoingEquiv p .outputFirst) =
    outgoing (Outgoing.mk (ambientChannel p .outputCoupler (couplerChannel 2))) at hReadoutFirst
  change response (externalOutgoingEquiv p .outputSecond) =
    outgoing (Outgoing.mk (ambientChannel p .outputCoupler (couplerChannel 3))) at hReadoutSecond
  have hSqrtSquare : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hPi : MatchedPropagation.carrierPhaseFactor (Real.pi : Real.Angle) = -1 :=
    machZehnderRegression_carrierPhaseFactor_points.2
  constructor
  · rw [hReadoutFirst, hOutputFirst]
    simp only [p, balancedPhasePi, balancedParameters, losslessArm,
      MatchedPropagation.transmissionCoefficient, balancedCoupler,
      DirectionalCoupler.crossCoefficient, Complex.ofReal_div, Complex.ofReal_ofNat]
    rw [show MatchedPropagation.carrierPhaseFactor (0 : Real.Angle) = 1 by
      simp only [MatchedPropagation.carrierPhaseFactor, neg_zero, Real.Angle.toCircle_zero,
        Circle.coe_one], hPi]
    ring_nf
    rw [hSqrtSquare, Complex.I_sq]
    norm_num
    ring
  · rw [hReadoutSecond, hOutputSecond]
    simp only [p, balancedPhasePi, balancedParameters, losslessArm,
      MatchedPropagation.transmissionCoefficient, balancedCoupler,
      DirectionalCoupler.crossCoefficient, Complex.ofReal_div, Complex.ofReal_ofNat]
    rw [show MatchedPropagation.carrierPhaseFactor (0 : Real.Angle) = 1 by
      simp only [MatchedPropagation.carrierPhaseFactor, neg_zero, Real.Angle.toCircle_zero,
        Circle.coe_one], hPi]
    ring_nf

/-- The hand-expanded phase-`π` fixture has an exactly dark second output. -/
lemma machZehnderRegression_phase_pi_dark_port (input : ℂ) :
    ((netlist balancedPhasePi).responseTransform
          (isWellPosed balancedPhasePi)).toLinearMap
        (leftInput balancedPhasePi input 0)
          (externalOutgoingEquiv balancedPhasePi .outputSecond) = 0 :=
  (machZehnderRegression_phase_pi_output_amplitudes input).2

/-!
## C. N6 power balance and phase-ratio identifiability
-/

/-- Row `S-01`: an N6 API fixture specializes network conservation to every balanced arm-phase
pair. It is not convention-sensitive evidence for the explicit wiring. -/
lemma machZehnderRegression_power_balance
    (upperPhase lowerPhase : Real.Angle) (input : ℂ) :
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
      Complex.normSq input := by
  exact lossless_single_input_output_power_balance
    (balancedParameters upperPhase lowerPhase)
    (balancedParameters_isLossless upperPhase lowerPhase) input

/-- The ratio of the actual balanced response coordinates recovers the lower-to-upper arm phase
factor. -/
lemma machZehnderRegression_phase_factor_ratio
    (upperPhase lowerPhase : Real.Angle) (input : ℂ) (hInput : input ≠ 0) :
    let upper := MatchedPropagation.carrierPhaseFactor upperPhase
    let lower := MatchedPropagation.carrierPhaseFactor lowerPhase
    let p := balancedParameters upperPhase lowerPhase
    let firstOutput :=
      ((netlist p).responseTransform (isWellPosed p)).toLinearMap
        (leftInput p input 0) (externalOutgoingEquiv p .outputFirst)
    let secondOutput :=
      ((netlist p).responseTransform (isWellPosed p)).toLinearMap
        (leftInput p input 0) (externalOutgoingEquiv p .outputSecond)
    (-firstOutput + Complex.I * secondOutput) /
        (firstOutput + Complex.I * secondOutput) = lower / upper := by
  dsimp only
  exact (balanced_phase_factor_ratio_eq_output_ratio upperPhase lowerPhase input hInput).symm

end MachZehnder

end

end Optics
