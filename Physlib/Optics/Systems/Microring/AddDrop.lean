/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Systems.Microring.AddDropNetwork

/-!
# Add-drop microring elimination and circulation series

## i. Overview

This file solves the explicit two-coupler, two-arc feedback network defined at
`Physlib/Optics/Systems/Microring/AddDropNetwork.lean:435-489`. It proves that N5 well-posedness is
exactly nonvanishing of the complete circulation denominator and derives the input-to-through and
input-to-drop responses from the N5 channel equations.

`roundTripSeries`, `throughTransferSeries`, and `dropTransferSeries` are totalized `tsum`
expressions. They have no convergent-circulation or network-response meaning here without the
stated summability or contraction gate; only the series theorems are gated.

This is a fixed-carrier, single-mode model. Power means normalized modal power. The file makes no
bandwidth, causality, dispersion, group-delay, nonlinear, thermal, material-realization, or
omitted-loss-channel claim. It does not derive through/drop powers, power balance, resonance or
antiresonance extrema, critical coupling, extinction, rejection ratio, parameter recovery, or free
spectral range. It asserts neither reciprocity nor a time-reversed pairing of external ports.

## ii. Key results

- `AddDrop.isWellPosed_iff`: the exact scalar denominator gate.
- `AddDrop.response_through` and `AddDrop.response_drop`: the N5-derived transfer amplitudes.
- `AddDrop.throughTransfer_eq_roundTripSeries` and `AddDrop.dropTransfer_eq_roundTripSeries`:
  equality of algebraic elimination and the convergent circulation series.

## iii. Table of contents

- A. Exact well-posedness and N5 response
- B. Convergent multiple-round-trip view

## iv. References

The elimination proofs are Physlib-original. The resulting transfer shapes agree with the standard
add-drop microring formulas after the declared port, carrier-phase, and arm-gauge conventions are
mapped.
-/

@[expose] public section

namespace Optics

noncomputable section

namespace AddDrop

/-!
## A. Exact well-posedness and N5 response
-/

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

/-!
## B. Convergent multiple-round-trip view
-/

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
