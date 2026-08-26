/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Systems.DCDR.NominalChain
public import Physlib.Optics.Systems.DCDR.ZTransformRegression

/-!
# Regression tests for the nominal DCDR chain

## i. Overview

The exact stable fixture uses `z = I`, hence formal delay `q = z⁻¹ = -I`, and the nonzero
loop polynomial `-(1/4)q²`. Both nominal scalar transmissions are `-(7/8)I`; the right-to-left
pivot inverse is `(8/7)I`. Consequently the backward-first chain has diagonal
`((8/7)I, -(7/8)I)`.

The scalar data are expanded from the parameter definitions. The chain entries unfold the generic
N3T block construction and never use `nominalBackwardFirstChainTransform_eq_matrix` or
`zChainCrossSemantics_agree`. The causal, reciprocal-Z, raw N5, and eleven-branch Mason values reuse
the accepted independent nonzero-loop audit. Swapping the nominal reference-plane order gives the
opposite diagonal and is rejected at the same fixture.

## ii. Key results

- `DCDR.zChainRegression_reverse_transfer`: the independently expanded pivot scalar.
- `DCDR.zChainRegression_independent_packaged_blocks`: the four raw-N7 N5 blocks.
- `DCDR.zChainRegression_pivotInverse_entry`: the independently solved inverse pivot.
- `DCDR.zChainRegression_chain_leading`: the exact `(8/7)I` leading entry.
- `DCDR.zChainRegression_independent_common_point`: all independent DCDR X-01 anchors together.
- `DCDR.zChainRegression_chain_ne_wrongReferencePlaneMatrix`: fail-capable ordering sentinel.

## iii. Table of contents

- A. Exact scalar data and pivot
- B. Independent backward-first chain entries
- C. Extended common-domain witness
- D. Wrong-reference-plane sentinel

## iv. References

These fixtures are Physlib-original algebraic checks. Nominal left and right labels do not assert
physical reference planes, reciprocity, physical time reversal, physical resonance,
coherent--incoherent equivalence, power, Maxwell time-domain meaning, or physical-frequency
meaning.
-/

@[expose] public section

namespace Optics.DCDR

noncomputable section

open Physlib.ZTransform

/-- The chain regression uses the same external-channel instance as N5 elimination. -/
local instance zChainRegressionExternalChannelFintype (p : Parameters) :
    Fintype (netlist p).ExternalChannel :=
  (netlist p).eliminationExternalChannelFintype

/-!

## A. Exact scalar data and pivot

-/

/-- The fixed-carrier stable chain fixture at formal delay `q = -I`. -/
def zChainRegressionParameters : Parameters :=
  stableUnitDelayParameters.at (-Complex.I)

/-- Direct parameter expansion gives the stable forward transmission `-(7/8)I`. -/
lemma zChainRegression_forward_transfer :
    transfer zChainRegressionParameters = -(7 / 8) * Complex.I := by
  have hDenominator : zChainRegressionParameters.HasNonzeroDenominator := by
    simpa [zChainRegressionParameters] using
      zRegression_stable_fixed_hasNonzeroDenominator_I
  rw [transfer]
  apply (div_eq_iff hDenominator).2
  norm_num [zChainRegressionParameters, Parameters.responseNumerator,
    Parameters.denominator, Parameters.loopGain, Parameters.directGain,
    Parameters.feedbackReadoutGain, Parameters.feedbackDrive,
    UnitDelayParameters.at, stableUnitDelayParameters, poleRegressionCoupler,
    Parameters.upperCoefficient, Parameters.lowerCoefficient,
    Parameters.feedbackCoefficient, DirectionalCoupler.crossCoefficient]
  ring_nf
  have hI3 : Complex.I ^ 3 = -Complex.I := by
    calc
      Complex.I ^ 3 = (Complex.I * Complex.I) * Complex.I := by ring
      _ = -Complex.I := by rw [Complex.I_mul_I]; ring
  have hI5 : Complex.I ^ 5 = Complex.I := by
    calc
      Complex.I ^ 5 = (Complex.I * Complex.I) * (Complex.I * Complex.I) * Complex.I := by
        ring
      _ = Complex.I := by rw [Complex.I_mul_I]; norm_num
  have hI7 : Complex.I ^ 7 = -Complex.I := by
    calc
      Complex.I ^ 7 = (Complex.I * Complex.I) * (Complex.I * Complex.I) *
          (Complex.I * Complex.I) * Complex.I := by ring
      _ = -Complex.I := by rw [Complex.I_mul_I]; ring
  rw [hI3, hI5, hI7]
  ring

/-- Direct parameter expansion gives the independently stated reverse transmission `-(7/8)I`. -/
lemma zChainRegression_reverse_transfer :
    transfer zChainRegressionParameters.reverse = -(7 / 8) * Complex.I := by
  change transfer zChainRegressionParameters = -(7 / 8) * Complex.I
  exact zChainRegression_forward_transfer

/-- The stable fixed-carrier N5 denominator gate, restated at the chain fixture. -/
lemma zChainRegression_hasNonzeroDenominator :
    zChainRegressionParameters.HasNonzeroDenominator := by
  simpa [zChainRegressionParameters] using zRegression_stable_fixed_hasNonzeroDenominator_I

/-- Swapping the equal couplers leaves the fixed regression parameters unchanged. -/
lemma zChainRegression_reverse_parameters :
    zChainRegressionParameters.reverse = zChainRegressionParameters := by
  rfl

/-- The eight raw N7 equations determine the fixed fixture's outgoing coordinate.

This is a direct feedback solve and does not use `ForwardEquations.output_eq_transfer`.
-/
lemma zChainRegression_forwardEquations_output {input : ℂ} {state : Node → ℂ}
    (hEquations : ForwardEquations zChainRegressionParameters input state) :
    state 7 = -(7 / 8) * Complex.I * input := by
  have hLoop : state 1 =
      zChainRegressionParameters.loopGain * state 1 +
        zChainRegressionParameters.feedbackDrive * input := by
    calc
      state 1 = zChainRegressionParameters.feedbackCoefficient * state 6 :=
        hEquations.nodeTwo
      _ = zChainRegressionParameters.feedbackCoefficient *
          ((zChainRegressionParameters.secondCoupler.throughAmplitude : ℂ) * state 4 +
            DirectionalCoupler.crossCoefficient
              zChainRegressionParameters.secondCoupler * state 5) := by
          rw [hEquations.nodeSeven]
      _ = zChainRegressionParameters.loopGain * state 1 +
          zChainRegressionParameters.feedbackDrive * input := by
          rw [hEquations.nodeFive, hEquations.nodeSix, hEquations.nodeThree,
            hEquations.nodeFour, hEquations.nodeOne]
          simp [Parameters.loopGain, Parameters.feedbackDrive]
          ring
  have hFeedback : state 1 =
      zChainRegressionParameters.feedbackDrive * input /
        zChainRegressionParameters.denominator := by
    apply (eq_div_iff zChainRegression_hasNonzeroDenominator).2
    rw [Parameters.denominator]
    linear_combination hLoop
  have hOutput : state 7 =
      zChainRegressionParameters.directGain * input +
        zChainRegressionParameters.feedbackReadoutGain * state 1 := by
    rw [hEquations.nodeEight, hEquations.nodeFive, hEquations.nodeSix,
      hEquations.nodeThree, hEquations.nodeFour, hEquations.nodeOne]
    simp [Parameters.directGain, Parameters.feedbackReadoutGain]
    ring
  have hInverse : zChainRegressionParameters.denominator *
      zChainRegressionParameters.denominator⁻¹ = 1 :=
    mul_inv_cancel₀ zChainRegression_hasNonzeroDenominator
  calc
    state 7 = zChainRegressionParameters.directGain * input +
        zChainRegressionParameters.feedbackReadoutGain * state 1 := hOutput
    _ = zChainRegressionParameters.directGain * input +
        zChainRegressionParameters.feedbackReadoutGain *
          (zChainRegressionParameters.feedbackDrive * input /
            zChainRegressionParameters.denominator) := by rw [hFeedback]
    _ = transfer zChainRegressionParameters * input := by
      rw [transfer, Parameters.responseNumerator, div_eq_mul_inv]
      calc
        _ = zChainRegressionParameters.directGain * input +
            zChainRegressionParameters.feedbackReadoutGain *
              zChainRegressionParameters.feedbackDrive * input *
                zChainRegressionParameters.denominator⁻¹ := by ring
        _ = zChainRegressionParameters.directGain * input *
              (zChainRegressionParameters.denominator *
                zChainRegressionParameters.denominator⁻¹) +
            zChainRegressionParameters.feedbackReadoutGain *
              zChainRegressionParameters.feedbackDrive * input *
                zChainRegressionParameters.denominator⁻¹ := by simp [hInverse]
        _ = (zChainRegressionParameters.directGain *
              zChainRegressionParameters.denominator +
            zChainRegressionParameters.feedbackReadoutGain *
              zChainRegressionParameters.feedbackDrive) *
                zChainRegressionParameters.denominator⁻¹ * input := by ring
    _ = -(7 / 8) * Complex.I * input := by rw [zChainRegression_forward_transfer]

/-- The left external readout is unfolded directly to the first N7 outgoing coordinate. -/
lemma zChainRegression_outputReadout_left
    (outgoing : ModeAmplitude (netlist zChainRegressionParameters).OutgoingIndex) :
    (netlist zChainRegressionParameters).outputReadout.toLinearMap outgoing
        (Outgoing.mk (inputChannel zChainRegressionParameters)) =
      outgoing (Outgoing.mk (firstCouplerChannel zChainRegressionParameters
        DirectionalCoupler.Port.leftFirst)) := by
  rw [FlatNetlist.outputReadout,
    (netlist zChainRegressionParameters).connections.externalOutgoingReadout_apply,
    ModeAmplitude.restrictEmbedding_apply]
  rfl

/-- The right external readout is unfolded directly to the second N7 outgoing coordinate. -/
lemma zChainRegression_outputReadout_right
    (outgoing : ModeAmplitude (netlist zChainRegressionParameters).OutgoingIndex) :
    (netlist zChainRegressionParameters).outputReadout.toLinearMap outgoing
        (Outgoing.mk (outputChannel zChainRegressionParameters)) =
      outgoing (Outgoing.mk (secondCouplerChannel zChainRegressionParameters
        DirectionalCoupler.Port.rightFirst)) := by
  rw [FlatNetlist.outputReadout,
    (netlist zChainRegressionParameters).connections.externalOutgoingReadout_apply,
    ModeAmplitude.restrictEmbedding_apply]
  rfl

/-- Raw forward and reverse N7 equations pin both response coordinates at the fixture. -/
lemma zChainRegression_response_coordinates
    (external : ModeAmplitude (netlist zChainRegressionParameters).ExternalIncident) :
    let response := (netlist zChainRegressionParameters).responseTransform
      (isWellPosed_of_hasNonzeroDenominator zChainRegressionParameters
        zChainRegression_hasNonzeroDenominator) |>.toLinearMap external
    response (Outgoing.mk (inputChannel zChainRegressionParameters)) =
        -(7 / 8) * Complex.I *
          external (Incident.mk (outputChannel zChainRegressionParameters)) ∧
      response (Outgoing.mk (outputChannel zChainRegressionParameters)) =
        -(7 / 8) * Complex.I *
          external (Incident.mk (inputChannel zChainRegressionParameters)) := by
  let hWellPosed := isWellPosed_of_hasNonzeroDenominator zChainRegressionParameters
    zChainRegression_hasNonzeroDenominator
  let response := (netlist zChainRegressionParameters).responseTransform hWellPosed
    |>.toLinearMap external
  have hMember : (external, response) ∈ (netlist zChainRegressionParameters).behavior := by
    rw [← (netlist zChainRegressionParameters).toBehavior_responseTransform hWellPosed,
      ModeTransform.mem_toBehavior_iff_toLinearMap]
  rcases ((netlist zChainRegressionParameters).mem_behavior_iff_equations
      external response).mp hMember with
    ⟨incident, outgoing, hScattering, hAssembly, hOutput⟩
  have hAssembly' : incident =
      (netlist zChainRegressionParameters).connections.incidentAssembly outgoing external := by
    simpa only [PortConnectionFamily.incidentAssembly] using hAssembly
  have hForward := forwardEquations_of_netlistEquations zChainRegressionParameters
    external incident outgoing hScattering hAssembly'
  have hReverse := reverseEquations_of_netlistEquations zChainRegressionParameters
    external incident outgoing hScattering hAssembly'
  rw [zChainRegression_reverse_parameters] at hReverse
  have hForwardValue := zChainRegression_forwardEquations_output hForward
  have hReverseValue := zChainRegression_forwardEquations_output hReverse
  have hReadoutLeft := congrArg
    (fun state => state (Outgoing.mk (inputChannel zChainRegressionParameters))) hOutput
  have hReadoutRight := congrArg
    (fun state => state (Outgoing.mk (outputChannel zChainRegressionParameters))) hOutput
  rw [zChainRegression_outputReadout_left] at hReadoutLeft
  rw [zChainRegression_outputReadout_right] at hReadoutRight
  change response (Outgoing.mk (inputChannel zChainRegressionParameters)) = _ ∧
    response (Outgoing.mk (outputChannel zChainRegressionParameters)) = _
  constructor
  · exact hReadoutLeft.trans (by simpa [reverseState] using hReverseValue)
  · exact hReadoutRight.trans (by simpa [forwardState] using hForwardValue)

/-- Raw N7 equations give zero nominal-left reflection at the fixed fixture. -/
lemma zChainRegression_response_left_left :
    (netlist zChainRegressionParameters).responseTransform
        (isWellPosed_of_hasNonzeroDenominator zChainRegressionParameters
          zChainRegression_hasNonzeroDenominator)
        (Outgoing.mk (inputChannel zChainRegressionParameters))
        (Incident.mk (inputChannel zChainRegressionParameters)) = 0 := by
  have hResponse := (zChainRegression_response_coordinates
    (inputAmplitude zChainRegressionParameters 1)).1
  simpa [inputAmplitude, Matrix.toLpLin_apply,
    (inputChannel_ne_outputChannel zChainRegressionParameters).symm] using hResponse

/-- Raw N7 equations give the nominal right-to-left entry `-(7/8)I`. -/
lemma zChainRegression_response_left_right :
    (netlist zChainRegressionParameters).responseTransform
        (isWellPosed_of_hasNonzeroDenominator zChainRegressionParameters
          zChainRegression_hasNonzeroDenominator)
        (Outgoing.mk (inputChannel zChainRegressionParameters))
        (Incident.mk (outputChannel zChainRegressionParameters)) =
      -(7 / 8) * Complex.I := by
  have hResponse := (zChainRegression_response_coordinates
    (nominalRightIncidentAmplitude zChainRegressionParameters 1)).1
  simpa [nominalRightIncidentAmplitude, Matrix.toLpLin_apply] using hResponse

/-- Raw N7 equations give the nominal left-to-right entry `-(7/8)I`. -/
lemma zChainRegression_response_right_left :
    (netlist zChainRegressionParameters).responseTransform
        (isWellPosed_of_hasNonzeroDenominator zChainRegressionParameters
          zChainRegression_hasNonzeroDenominator)
        (Outgoing.mk (outputChannel zChainRegressionParameters))
        (Incident.mk (inputChannel zChainRegressionParameters)) =
      -(7 / 8) * Complex.I := by
  have hResponse := (zChainRegression_response_coordinates
    (inputAmplitude zChainRegressionParameters 1)).2
  simpa [inputAmplitude, Matrix.toLpLin_apply] using hResponse

/-- Raw N7 equations give zero nominal-right reflection at the fixed fixture. -/
lemma zChainRegression_response_right_right :
    (netlist zChainRegressionParameters).responseTransform
        (isWellPosed_of_hasNonzeroDenominator zChainRegressionParameters
          zChainRegression_hasNonzeroDenominator)
        (Outgoing.mk (outputChannel zChainRegressionParameters))
        (Incident.mk (outputChannel zChainRegressionParameters)) = 0 := by
  have hResponse := (zChainRegression_response_coordinates
    (nominalRightIncidentAmplitude zChainRegressionParameters 1)).2
  simpa [nominalRightIncidentAmplitude, Matrix.toLpLin_apply,
    inputChannel_ne_outputChannel zChainRegressionParameters] using hResponse

/-- Definitional packaging preserves the independently derived nominal-left reflection value. -/
lemma zChainRegression_packaged_inl_inl :
    packagedNominalTwoPortScattering zChainRegressionParameters
        zChainRegression_hasNonzeroDenominator
        (Sum.inl (Outgoing.mk ())) (Sum.inl (Incident.mk ())) = 0 := by
  change (netlist zChainRegressionParameters).responseTransform
    (isWellPosed_of_hasNonzeroDenominator zChainRegressionParameters
      zChainRegression_hasNonzeroDenominator)
    (Outgoing.mk (inputChannel zChainRegressionParameters))
    (Incident.mk (inputChannel zChainRegressionParameters)) = 0
  exact zChainRegression_response_left_left

/-- Definitional packaging preserves the independently derived right-to-left value. -/
lemma zChainRegression_packaged_inl_inr :
    packagedNominalTwoPortScattering zChainRegressionParameters
        zChainRegression_hasNonzeroDenominator
        (Sum.inl (Outgoing.mk ())) (Sum.inr (Incident.mk ())) =
      -(7 / 8) * Complex.I := by
  change (netlist zChainRegressionParameters).responseTransform
    (isWellPosed_of_hasNonzeroDenominator zChainRegressionParameters
      zChainRegression_hasNonzeroDenominator)
    (Outgoing.mk (inputChannel zChainRegressionParameters))
    (Incident.mk (outputChannel zChainRegressionParameters)) = -(7 / 8) * Complex.I
  exact zChainRegression_response_left_right

/-- Definitional packaging preserves the independently derived left-to-right value. -/
lemma zChainRegression_packaged_inr_inl :
    packagedNominalTwoPortScattering zChainRegressionParameters
        zChainRegression_hasNonzeroDenominator
        (Sum.inr (Outgoing.mk ())) (Sum.inl (Incident.mk ())) =
      -(7 / 8) * Complex.I := by
  change (netlist zChainRegressionParameters).responseTransform
    (isWellPosed_of_hasNonzeroDenominator zChainRegressionParameters
      zChainRegression_hasNonzeroDenominator)
    (Outgoing.mk (outputChannel zChainRegressionParameters))
    (Incident.mk (inputChannel zChainRegressionParameters)) = -(7 / 8) * Complex.I
  exact zChainRegression_response_right_left

/-- Definitional packaging preserves the independently derived nominal-right reflection value. -/
lemma zChainRegression_packaged_inr_inr :
    packagedNominalTwoPortScattering zChainRegressionParameters
        zChainRegression_hasNonzeroDenominator
        (Sum.inr (Outgoing.mk ())) (Sum.inr (Incident.mk ())) = 0 := by
  change (netlist zChainRegressionParameters).responseTransform
    (isWellPosed_of_hasNonzeroDenominator zChainRegressionParameters
      zChainRegression_hasNonzeroDenominator)
    (Outgoing.mk (outputChannel zChainRegressionParameters))
    (Incident.mk (outputChannel zChainRegressionParameters)) = 0
  exact zChainRegression_response_right_right

/-- The four packaged N5 blocks are pinned independently from the raw N7 equations. -/
lemma zChainRegression_independent_packaged_blocks :
    packagedNominalTwoPortScattering zChainRegressionParameters
          zChainRegression_hasNonzeroDenominator
          (Sum.inl (Outgoing.mk ())) (Sum.inl (Incident.mk ())) = 0 ∧
      packagedNominalTwoPortScattering zChainRegressionParameters
          zChainRegression_hasNonzeroDenominator
          (Sum.inl (Outgoing.mk ())) (Sum.inr (Incident.mk ())) =
        -(7 / 8) * Complex.I ∧
      packagedNominalTwoPortScattering zChainRegressionParameters
          zChainRegression_hasNonzeroDenominator
          (Sum.inr (Outgoing.mk ())) (Sum.inl (Incident.mk ())) =
        -(7 / 8) * Complex.I ∧
      packagedNominalTwoPortScattering zChainRegressionParameters
          zChainRegression_hasNonzeroDenominator
          (Sum.inr (Outgoing.mk ())) (Sum.inr (Incident.mk ())) = 0 :=
  ⟨zChainRegression_packaged_inl_inl, zChainRegression_packaged_inl_inr,
    zChainRegression_packaged_inr_inl, zChainRegression_packaged_inr_inr⟩

/-- The independently expanded nominal right-to-left transmission is nonzero. -/
lemma zChainRegression_reverse_transfer_ne_zero :
    transfer zChainRegressionParameters.reverse ≠ 0 := by
  rw [zChainRegression_reverse_transfer]
  intro hZero
  have hImaginary := congrArg Complex.im hZero
  norm_num at hImaginary

/-- The independently computed pivot scalar and its displayed inverse multiply to one. -/
lemma zChainRegression_pivotProduct :
    (-(7 / 8) * Complex.I) * ((8 / 7) * Complex.I) = (1 : ℂ) := by
  calc
    (-(7 / 8) * Complex.I) * ((8 / 7) * Complex.I) =
        (-(7 / 8) * (8 / 7)) * (Complex.I * Complex.I) := by ring
    _ = 1 := by rw [Complex.I_mul_I]; norm_num

/-- A constant amplitude on the singleton regression backward-wave family. -/
def zChainRegressionBackwardAmplitude (value : ℂ) :
    ModeAmplitude (BackwardWave Unit) :=
  WithLp.toLp 2 fun _ => value

/-- The packaged pivot entry, obtained from the raw N7 right-to-left block. -/
lemma zChainRegression_rightToLeftTransmission_entry :
    (packagedNominalTwoPortScattering zChainRegressionParameters
      zChainRegression_hasNonzeroDenominator).rightToLeftTransmission
        (BackwardWave.mk ()) (BackwardWave.mk ()) = -(7 / 8) * Complex.I := by
  change packagedNominalTwoPortScattering zChainRegressionParameters
    zChainRegression_hasNonzeroDenominator
    (Sum.inl (Outgoing.mk ())) (Sum.inr (Incident.mk ())) = -(7 / 8) * Complex.I
  exact zChainRegression_packaged_inl_inr

/-- The packaged forward entry, obtained from the raw N7 left-to-right block. -/
lemma zChainRegression_leftToRightTransmission_entry :
    (packagedNominalTwoPortScattering zChainRegressionParameters
      zChainRegression_hasNonzeroDenominator).leftToRightTransmission
        (ForwardWave.mk ()) (ForwardWave.mk ()) = -(7 / 8) * Complex.I := by
  change packagedNominalTwoPortScattering zChainRegressionParameters
    zChainRegression_hasNonzeroDenominator
    (Sum.inr (Outgoing.mk ())) (Sum.inl (Incident.mk ())) = -(7 / 8) * Complex.I
  exact zChainRegression_packaged_inr_inl

/-- The complete packaged left-reflection block vanishes by the raw N7 block audit. -/
lemma zChainRegression_leftReflection_eq_zero :
    (packagedNominalTwoPortScattering zChainRegressionParameters
      zChainRegression_hasNonzeroDenominator).leftReflection = 0 := by
  ext output input
  rcases output with ⟨⟨⟩⟩
  rcases input with ⟨⟨⟩⟩
  change packagedNominalTwoPortScattering zChainRegressionParameters
    zChainRegression_hasNonzeroDenominator
    (Sum.inl (Outgoing.mk ())) (Sum.inl (Incident.mk ())) = 0
  exact zChainRegression_packaged_inl_inl

/-- The complete packaged right-reflection block vanishes by the raw N7 block audit. -/
lemma zChainRegression_rightReflection_eq_zero :
    (packagedNominalTwoPortScattering zChainRegressionParameters
      zChainRegression_hasNonzeroDenominator).rightReflection = 0 := by
  ext output input
  rcases output with ⟨⟨⟩⟩
  rcases input with ⟨⟨⟩⟩
  change packagedNominalTwoPortScattering zChainRegressionParameters
    zChainRegression_hasNonzeroDenominator
    (Sum.inr (Outgoing.mk ())) (Sum.inr (Incident.mk ())) = 0
  exact zChainRegression_packaged_inr_inr

/-- The raw N7 pivot block acts by the independently computed scalar `-(7/8)I`. -/
lemma zChainRegression_rightToLeftTransmission_action
    (amplitude : ModeAmplitude (BackwardWave Unit)) :
    (packagedNominalTwoPortScattering zChainRegressionParameters
      zChainRegression_hasNonzeroDenominator).rightToLeftTransmission.toLinearMap
        amplitude = WithLp.toLp 2 (fun _ =>
          (-(7 / 8) * Complex.I) * amplitude (BackwardWave.mk ())) := by
  apply WithLp.ofLp_injective 2
  funext output
  rcases output with ⟨⟨⟩⟩
  simp only [ModeTransform.toLinearMap, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]
  rw [← BackwardWave.channelEquiv.symm.sum_comp, Fintype.sum_unique]
  change (packagedNominalTwoPortScattering zChainRegressionParameters
      zChainRegression_hasNonzeroDenominator).rightToLeftTransmission
        (BackwardWave.mk ()) (BackwardWave.mk ()) * amplitude (BackwardWave.mk ()) =
    (-(7 / 8) * Complex.I) * amplitude (BackwardWave.mk ())
  rw [zChainRegression_rightToLeftTransmission_entry]

/-- The exact right-to-left pivot is bijective without using the production pivot iff. -/
lemma zChainRegression_hasBijectiveRightToLeftTransmission :
    TwoPortScatteringTransform.HasBijectiveRightToLeftTransmission
      (packagedNominalTwoPortScattering zChainRegressionParameters
        zChainRegression_hasNonzeroDenominator) := by
  constructor
  · intro first second hEqual
    apply WithLp.ofLp_injective 2
    funext index
    rcases index with ⟨⟨⟩⟩
    rw [zChainRegression_rightToLeftTransmission_action,
      zChainRegression_rightToLeftTransmission_action] at hEqual
    have hCoordinate := congrArg
      (fun amplitude : ModeAmplitude (BackwardWave Unit) =>
        amplitude (BackwardWave.mk ())) hEqual
    simpa using mul_left_cancel₀
      (by
        intro hZero
        have hImaginary := congrArg Complex.im hZero
        norm_num at hImaginary) hCoordinate
  · intro output
    refine ⟨zChainRegressionBackwardAmplitude
      ((8 / 7) * Complex.I * output (BackwardWave.mk ())), ?_⟩
    rw [zChainRegression_rightToLeftTransmission_action]
    apply WithLp.ofLp_injective 2
    funext index
    rcases index with ⟨⟨⟩⟩
    simp only [zChainRegressionBackwardAmplitude]
    calc
      (-(7 / 8) * Complex.I) *
          ((8 / 7) * Complex.I * output (BackwardWave.mk ())) =
        ((-(7 / 8) * Complex.I) * ((8 / 7) * Complex.I)) *
          output (BackwardWave.mk ()) := by ring
      _ = output (BackwardWave.mk ()) := by rw [zChainRegression_pivotProduct, one_mul]

/-!

## B. Independent backward-first chain entries

-/

/-- The behavior-derived chain at the exact nonzero-loop fixture. -/
noncomputable def zChainRegressionChain : BackwardFirstChainTransform Unit Unit :=
  (packagedNominalTwoPortScattering zChainRegressionParameters
    zChainRegression_hasNonzeroDenominator).toBackwardFirstChainTransform
      zChainRegression_hasBijectiveRightToLeftTransmission

/-- The proof-dependent inverse pivot is `(8/7)I`, derived from the inverse product law. -/
lemma zChainRegression_pivotInverse_entry :
    let scattering := packagedNominalTwoPortScattering zChainRegressionParameters
      zChainRegression_hasNonzeroDenominator
    let hPivot := zChainRegression_hasBijectiveRightToLeftTransmission
    (scattering.rightToLeftTransmissionInverse hPivot)
        (BackwardWave.mk ()) (BackwardWave.mk ()) = (8 / 7) * Complex.I := by
  let scattering := packagedNominalTwoPortScattering zChainRegressionParameters
    zChainRegression_hasNonzeroDenominator
  let hPivot := zChainRegression_hasBijectiveRightToLeftTransmission
  have hMatrix := scattering.inverse_mul_rightToLeftTransmission hPivot
  have hEntry := congrArg
    (fun matrix : ModeTransform (BackwardWave Unit) (BackwardWave Unit) =>
      matrix (BackwardWave.mk ()) (BackwardWave.mk ())) hMatrix
  have hInverseProduct :
      (scattering.rightToLeftTransmissionInverse hPivot)
          (BackwardWave.mk ()) (BackwardWave.mk ()) * (-(7 / 8) * Complex.I) = 1 := by
    simp only [Matrix.mul_apply] at hEntry
    rw [← BackwardWave.channelEquiv.symm.sum_comp, Fintype.sum_unique] at hEntry
    rw [zChainRegression_rightToLeftTransmission_entry] at hEntry
    simpa [scattering] using hEntry
  calc
    _ = _ * 1 := by rw [mul_one]
    _ = _ * ((-(7 / 8) * Complex.I) * ((8 / 7) * Complex.I)) := by
      rw [zChainRegression_pivotProduct]
    _ = (_ * (-(7 / 8) * Complex.I)) * ((8 / 7) * Complex.I) := by ring
    _ = (8 / 7) * Complex.I := by rw [hInverseProduct, one_mul]

/-- The leading backward-first chain entry is the inverse pivot `(8/7)I`. -/
lemma zChainRegression_chain_leading :
    zChainRegressionChain
        (Sum.inl (BackwardWave.mk ())) (Sum.inl (BackwardWave.mk ())) =
      (8 / 7) * Complex.I := by
  rw [zChainRegressionChain,
    TwoPortScatteringTransform.toBackwardFirstChainTransform_eq_blockFormula]
  unfold TwoPortScatteringTransform.backwardFirstChainBlockFormula
  exact zChainRegression_pivotInverse_entry

/-- The upper-right backward-first chain entry is zero. -/
lemma zChainRegression_chain_upperRight :
    zChainRegressionChain
        (Sum.inl (BackwardWave.mk ())) (Sum.inr (ForwardWave.mk ())) = 0 := by
  rw [zChainRegressionChain,
    TwoPortScatteringTransform.toBackwardFirstChainTransform_eq_blockFormula]
  unfold TwoPortScatteringTransform.backwardFirstChainBlockFormula
  simp only [Matrix.fromBlocks_apply₁₂, Matrix.neg_apply]
  rw [zChainRegression_leftReflection_eq_zero, Matrix.mul_zero, Matrix.zero_apply, neg_zero]

/-- The lower-left backward-first chain entry is zero. -/
lemma zChainRegression_chain_lowerLeft :
    zChainRegressionChain
        (Sum.inr (ForwardWave.mk ())) (Sum.inl (BackwardWave.mk ())) = 0 := by
  rw [zChainRegressionChain,
    TwoPortScatteringTransform.toBackwardFirstChainTransform_eq_blockFormula]
  unfold TwoPortScatteringTransform.backwardFirstChainBlockFormula
  simp only [Matrix.fromBlocks_apply₂₁]
  rw [zChainRegression_rightReflection_eq_zero, Matrix.zero_mul, Matrix.zero_apply]

/-- The bottom-right backward-first chain entry is the forward response `-(7/8)I`. -/
lemma zChainRegression_chain_lowerRight :
    zChainRegressionChain
        (Sum.inr (ForwardWave.mk ())) (Sum.inr (ForwardWave.mk ())) =
      -(7 / 8) * Complex.I := by
  rw [zChainRegressionChain,
    TwoPortScatteringTransform.toBackwardFirstChainTransform_eq_blockFormula]
  unfold TwoPortScatteringTransform.backwardFirstChainBlockFormula
  simp only [Matrix.fromBlocks_apply₂₂]
  rw [zChainRegression_leftReflection_eq_zero, Matrix.mul_zero, sub_zero]
  exact zChainRegression_leftToRightTransmission_entry

/-- The production chain agrees with the independently folded N3T chain and its four entries.

The first conjunct is the production-agreement check. The remaining conjuncts pair it with the
independently computed values; none of those value proofs uses the production chain.
-/
lemma zChainRegression_productionChain_with_independent_entries :
    nominalBackwardFirstChainTransform zChainRegressionParameters
        zChainRegression_hasNonzeroDenominator zChainRegression_reverse_transfer_ne_zero =
      zChainRegressionChain ∧
    zChainRegressionChain
        (Sum.inl (BackwardWave.mk ())) (Sum.inl (BackwardWave.mk ())) =
      (8 / 7) * Complex.I ∧
    zChainRegressionChain
        (Sum.inl (BackwardWave.mk ())) (Sum.inr (ForwardWave.mk ())) = 0 ∧
    zChainRegressionChain
        (Sum.inr (ForwardWave.mk ())) (Sum.inl (BackwardWave.mk ())) = 0 ∧
    zChainRegressionChain
        (Sum.inr (ForwardWave.mk ())) (Sum.inr (ForwardWave.mk ())) =
      -(7 / 8) * Complex.I := by
  refine ⟨?_, zChainRegression_chain_leading, zChainRegression_chain_upperRight,
    zChainRegression_chain_lowerLeft, zChainRegression_chain_lowerRight⟩
  unfold nominalBackwardFirstChainTransform zChainRegressionChain
  congr

/-!

## C. Extended common-domain witness

-/

/-- The stable `z = I` fixture meets the base domain and the independent nominal chain pivot. -/
lemma zChainRegression_crossSemanticsDomain :
    IsZChainCrossSemanticsDomain stableUnitDelayParameters
      stableResponseReduction Complex.I where
  toIsZCrossSemanticsDomain := zRegression_stable_I_crossSemanticsDomain
  nominalRightToLeftTransmission_ne_zero := by
    simpa [Complex.inv_I, zChainRegressionParameters] using
      zChainRegression_reverse_transfer_ne_zero

/-- Independent causal, compiled, raw-N5, Mason, and chain expansions meet at the same fixture.

This conjunction does not invoke `zChainCrossSemantics_agree` or
`nominalBackwardFirstChainTransform_eq_matrix`.
-/
lemma zChainRegression_independent_common_point :
    transform (causalOutput stableUnitDelayParameters unitImpulse) Complex.I =
        -(7 / 8) * Complex.I ∧
      rationalZEliminationResponse stableUnitDelayParameters Complex.I
          stable_I_mem_reciprocalZResponseDomain = -(7 / 8) * Complex.I ∧
      eliminationResponse zChainRegressionParameters
          (isWellPosed_of_hasNonzeroDenominator zChainRegressionParameters
            zChainRegression_hasNonzeroDenominator) = -(7 / 8) * Complex.I ∧
      auditedMasonResponse zChainRegressionParameters = -(7 / 8) * Complex.I ∧
      zChainRegressionChain
          (Sum.inl (BackwardWave.mk ())) (Sum.inl (BackwardWave.mk ())) =
        (8 / 7) * Complex.I ∧
      zChainRegressionChain
          (Sum.inr (ForwardWave.mk ())) (Sum.inr (ForwardWave.mk ())) =
        -(7 / 8) * Complex.I := by
  rcases zRegression_stable_independent_nonzeroLoop_I with
    ⟨hCausal, hCompiled, hN5, hMason⟩
  exact ⟨hCausal, hCompiled,
    by simpa [zChainRegressionParameters] using hN5,
    by simpa [zChainRegressionParameters] using hMason,
    zChainRegression_chain_leading, zChainRegression_chain_lowerRight⟩

/-- The production DCDR X-01 agreement is paired with independently computed fixture values. -/
lemma zChainRegression_productionAgreement_with_independent_anchor :
    ZChainCrossSemanticsAgreement stableUnitDelayParameters stableResponseReduction Complex.I
        zChainRegression_crossSemanticsDomain ∧
      transform (causalOutput stableUnitDelayParameters unitImpulse) Complex.I =
        -(7 / 8) * Complex.I ∧
      zChainRegressionChain
          (Sum.inl (BackwardWave.mk ())) (Sum.inl (BackwardWave.mk ())) =
        (8 / 7) * Complex.I ∧
      zChainRegressionChain
          (Sum.inr (ForwardWave.mk ())) (Sum.inr (ForwardWave.mk ())) =
        -(7 / 8) * Complex.I := by
  rcases zChainRegression_independent_common_point with
    ⟨hCausal, _, _, _, hLeading, hLowerRight⟩
  exact ⟨zChainCrossSemantics_agree stableUnitDelayParameters stableResponseReduction
      Complex.I zChainRegression_crossSemanticsDomain,
    hCausal, hLeading, hLowerRight⟩

/-!

## D. Wrong-reference-plane sentinel

-/

/-- The deliberately wrong reference-plane matrix swaps the two correct diagonal entries. -/
def zChainRegressionWrongReferencePlaneMatrix : BackwardFirstChainTransform Unit Unit
  | Sum.inl _, Sum.inl _ => -(7 / 8) * Complex.I
  | Sum.inl _, Sum.inr _ => 0
  | Sum.inr _, Sum.inl _ => 0
  | Sum.inr _, Sum.inr _ => (8 / 7) * Complex.I

/-- The same fixture rejects the wrong nominal reference-plane order. -/
lemma zChainRegression_chain_ne_wrongReferencePlaneMatrix :
    zChainRegressionChain ≠ zChainRegressionWrongReferencePlaneMatrix := by
  intro hWrong
  have hLeading := congrArg
    (fun chain : BackwardFirstChainTransform Unit Unit =>
      chain (Sum.inl (BackwardWave.mk ())) (Sum.inl (BackwardWave.mk ()))) hWrong
  rw [zChainRegression_chain_leading] at hLeading
  change (8 / 7 : ℂ) * Complex.I = -(7 / 8) * Complex.I at hLeading
  have hImaginary := congrArg Complex.im hLeading
  norm_num at hImaginary

end

end Optics.DCDR
