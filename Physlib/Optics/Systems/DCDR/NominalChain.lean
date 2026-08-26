/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.TwoPortChainScattering
public import Physlib.Optics.Systems.DCDR.ZTransformBridge

/-!
# Nominal two-port and chain semantics of the DCDR

## i. Overview

The coherent DCDR netlist has exactly two external N7 channels. This module labels the first
coupler's `leftFirst` endpoint as the nominal left reference plane and the second coupler's
`rightFirst` endpoint as the nominal right reference plane. These labels are algebraic coordinates;
they do not assert physical reference planes or physical time reversal.

The complete forward and reverse N7 equations independently derive all four entries of the
well-posed N5 response. Both nominal reflection entries vanish. Left-to-right transmission is
`transfer p`; right-to-left transmission is separately stated as `transfer p.reverse`. The latter
is the scalar chain pivot. Its nonvanishing is kept separate from N5 well-posedness, analytic ROC
membership, recurrence contraction, and Schur certification.

On the solve and pivot gates, generic N3T conversion supplies the backward-first chain and its
scattering round trip. A downstream common-domain record adds this chain leg to the existing DCDR
causal-Z agreement without deriving any gate from another.

## ii. Key results

- `DCDR.response_nominal_reference_coordinates`: both N5 output coordinates from raw N7 equations.
- `DCDR.packagedNominalTwoPortScattering_eq_nominalTwoPortScatteringTransform`: all four blocks.
- `DCDR.packagedNominalTwoPortScattering_hasBijectiveRightToLeftTransmission_iff`: scalar pivot.
- `DCDR.nominalBackwardFirstChainTransform_eq_matrix`: the explicit backward-first chain.
- `DCDR.nominalBackwardFirstChainTransform_roundTrip`: the generic N3T scattering round trip.
- `DCDR.zChainCrossSemantics_agree`: the DCDR X-01 agreement including the chain leg.

## iii. Table of contents

- A. Nominal external reference-plane coordinates
- B. Complete forward and reverse N5 response
- C. Independent and packaged two-port scattering
- D. Scalar pivot and backward-first chain
- E. Common-domain Z and chain agreement

## iv. References

This nominal two-port and chain presentation is Physlib-original. It makes no claim of physical
reference planes, reciprocity, physical time reversal, physical resonance, coherent--incoherent
equivalence, BIBO stability beyond S4P's gate, normalized-modal or electromagnetic power,
Maxwell time-domain meaning, physical-frequency meaning, or HOL-script semantics.

The scattering-to-chain convention and round trip reuse
`Physlib/Optics/Network/TwoPortChainScattering.lean`.
-/

@[expose] public section

namespace Optics.DCDR

noncomputable section

/-- The nominal-chain layer uses the same external-channel instance as N5 elimination. -/
local instance nominalChainExternalChannelFintype (p : Parameters) :
    Fintype (netlist p).ExternalChannel :=
  (netlist p).eliminationExternalChannelFintype

/-!

## A. Nominal external reference-plane coordinates

-/

/-- The nominal left-then-right labels select the exposed first-arm endpoints.

`Sum.inl` is the first coupler's `leftFirst` endpoint and `Sum.inr` is the second coupler's
`rightFirst` endpoint. The labels are algebraic and do not assert physical reference planes.
-/
def nominalTwoPortExternalChannel (p : Parameters) :
    Unit ⊕ Unit → (netlist p).ExternalChannel
  | Sum.inl _ => inputChannel p
  | Sum.inr _ => outputChannel p

/-- The two nominal external labels are injective. -/
lemma nominalTwoPortExternalChannel_injective (p : Parameters) :
    Function.Injective (nominalTwoPortExternalChannel p) := by
  rintro (left | right) (left' | right') hEqual
  · cases left
    cases left'
    rfl
  · cases left
    cases right'
    exact (inputChannel_ne_outputChannel p hEqual).elim
  · cases right
    cases left'
    exact (inputChannel_ne_outputChannel p hEqual.symm).elim
  · cases right
    cases right'
    rfl

/-- The two nominal labels exhaust the complete external DCDR channel family. -/
lemma nominalTwoPortExternalChannel_surjective (p : Parameters) :
    Function.Surjective (nominalTwoPortExternalChannel p) := by
  intro channel
  rcases externalChannel_eq_input_or_output p channel with rfl | rfl
  · exact ⟨Sum.inl (), rfl⟩
  · exact ⟨Sum.inr (), rfl⟩

/-- The nominal left-then-right equivalence for the two external DCDR channels. -/
noncomputable def nominalTwoPortExternalChannelEquiv (p : Parameters) :
    Unit ⊕ Unit ≃ (netlist p).ExternalChannel :=
  Equiv.ofBijective (nominalTwoPortExternalChannel p)
    ⟨nominalTwoPortExternalChannel_injective p,
      nominalTwoPortExternalChannel_surjective p⟩

/-- The nominal left label is the first coupler's exposed `leftFirst` endpoint. -/
@[simp]
lemma nominalTwoPortExternalChannelEquiv_apply_inl (p : Parameters) (mode : Unit) :
    nominalTwoPortExternalChannelEquiv p (Sum.inl mode) = inputChannel p := rfl

/-- The nominal right label is the second coupler's exposed `rightFirst` endpoint. -/
@[simp]
lemma nominalTwoPortExternalChannelEquiv_apply_inr (p : Parameters) (mode : Unit) :
    nominalTwoPortExternalChannelEquiv p (Sum.inr mode) = outputChannel p := rfl

/-- External incident endpoints in nominal left/right order. -/
noncomputable def nominalTwoPortExternalIncidentEquiv (p : Parameters) :
    (netlist p).ExternalIncident ≃ Incident Unit ⊕ Incident Unit :=
  (Incident.relabelEquiv (nominalTwoPortExternalChannelEquiv p).symm).trans
    Incident.splitSumEquiv

/-- External outgoing endpoints in nominal left/right order. -/
noncomputable def nominalTwoPortExternalOutgoingEquiv (p : Parameters) :
    (netlist p).ExternalOutgoing ≃ Outgoing Unit ⊕ Outgoing Unit :=
  (Outgoing.relabelEquiv (nominalTwoPortExternalChannelEquiv p).symm).trans
    Outgoing.splitSumEquiv

/-- A coherent scalar incident only at the nominal right endpoint. -/
def nominalRightIncidentAmplitude (p : Parameters) (amplitude : ℂ) :
    ModeAmplitude (netlist p).ExternalIncident :=
  PiLp.single 2 (Incident.mk (outputChannel p)) amplitude

/-- The nominal-right excitation has its supplied value at the right endpoint. -/
@[simp]
lemma nominalRightIncidentAmplitude_apply_right (p : Parameters) (amplitude : ℂ) :
    nominalRightIncidentAmplitude p amplitude (Incident.mk (outputChannel p)) = amplitude := by
  simp [nominalRightIncidentAmplitude]

/-- The nominal-right excitation vanishes at the left endpoint. -/
@[simp]
lemma nominalRightIncidentAmplitude_apply_left (p : Parameters) (amplitude : ℂ) :
    nominalRightIncidentAmplitude p amplitude (Incident.mk (inputChannel p)) = 0 := by
  rw [nominalRightIncidentAmplitude]
  simp [inputChannel_ne_outputChannel p]

/-!

## B. Complete forward and reverse N5 response

-/

/-- External readout at the nominal left endpoint is the first coupler's `leftFirst` output. -/
lemma outputReadout_apply_nominalLeft (p : Parameters)
    (outgoing : ModeAmplitude (netlist p).OutgoingIndex) :
    (netlist p).outputReadout.toLinearMap outgoing (Outgoing.mk (inputChannel p)) =
      outgoing (Outgoing.mk
        (firstCouplerChannel p DirectionalCoupler.Port.leftFirst)) := by
  rw [FlatNetlist.outputReadout,
    (netlist p).connections.externalOutgoingReadout_apply,
    ModeAmplitude.restrictEmbedding_apply]
  rfl

/-- Raw forward and reverse N7 equations determine both nominal N5 output coordinates.

The nominal-left output depends only on nominal-right incidence through `transfer p.reverse`.
The nominal-right output depends only on nominal-left incidence through `transfer p`.
-/
lemma response_nominal_reference_coordinates (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator)
    (external : ModeAmplitude (netlist p).ExternalIncident) :
    let response := (netlist p).responseTransform
      (isWellPosed_of_hasNonzeroDenominator p hDenominator) |>.toLinearMap external
    response (Outgoing.mk (inputChannel p)) =
        transfer p.reverse * external (Incident.mk (outputChannel p)) ∧
      response (Outgoing.mk (outputChannel p)) =
        transfer p * external (Incident.mk (inputChannel p)) := by
  let hWellPosed := isWellPosed_of_hasNonzeroDenominator p hDenominator
  let response := (netlist p).responseTransform hWellPosed |>.toLinearMap external
  have hMember : (external, response) ∈ (netlist p).behavior := by
    rw [← (netlist p).toBehavior_responseTransform hWellPosed,
      ModeTransform.mem_toBehavior_iff_toLinearMap]
  rcases ((netlist p).mem_behavior_iff_equations external response).mp hMember with
    ⟨incident, outgoing, hScattering, hAssembly, hOutput⟩
  have hAssembly' :
      incident = (netlist p).connections.incidentAssembly outgoing external := by
    simpa only [PortConnectionFamily.incidentAssembly] using hAssembly
  have hForward := forwardEquations_of_netlistEquations p external incident outgoing
    hScattering hAssembly'
  have hReverse := reverseEquations_of_netlistEquations p external incident outgoing
    hScattering hAssembly'
  have hReverseDenominator : p.reverse.HasNonzeroDenominator := by
    simpa [Parameters.HasNonzeroDenominator, Parameters.denominator_reverse] using hDenominator
  have hForwardValue := hForward.output_eq_transfer hDenominator
  have hReverseValue := hReverse.output_eq_transfer hReverseDenominator
  have hReadoutLeft := congrArg
    (fun state => state (Outgoing.mk (inputChannel p))) hOutput
  have hReadoutRight := congrArg
    (fun state => state (Outgoing.mk (outputChannel p))) hOutput
  rw [outputReadout_apply_nominalLeft] at hReadoutLeft
  rw [outputReadout_apply_output] at hReadoutRight
  change response (Outgoing.mk (inputChannel p)) = _ ∧
    response (Outgoing.mk (outputChannel p)) = _
  constructor
  · exact hReadoutLeft.trans (by simpa [reverseState] using hReverseValue)
  · exact hReadoutRight.trans (by simpa [forwardState] using hForwardValue)

/-- The nominal-left N5 reflection entry is zero. -/
lemma responseTransform_entry_nominalLeft_nominalLeft (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) :
    (netlist p).responseTransform (isWellPosed_of_hasNonzeroDenominator p hDenominator)
        (Outgoing.mk (inputChannel p)) (Incident.mk (inputChannel p)) = 0 := by
  have hResponse :=
    (response_nominal_reference_coordinates p hDenominator (inputAmplitude p 1)).1
  simpa [inputAmplitude, Matrix.toLpLin_apply,
    (inputChannel_ne_outputChannel p).symm] using hResponse

/-- The nominal right-to-left N5 entry is the independently stated reverse transmission. -/
lemma responseTransform_entry_nominalLeft_nominalRight (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) :
    (netlist p).responseTransform (isWellPosed_of_hasNonzeroDenominator p hDenominator)
        (Outgoing.mk (inputChannel p)) (Incident.mk (outputChannel p)) =
      transfer p.reverse := by
  have hResponse := (response_nominal_reference_coordinates p hDenominator
    (nominalRightIncidentAmplitude p 1)).1
  simpa [nominalRightIncidentAmplitude, Matrix.toLpLin_apply] using hResponse

/-- The nominal left-to-right N5 entry is the forward transmission. -/
lemma responseTransform_entry_nominalRight_nominalLeft (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) :
    (netlist p).responseTransform (isWellPosed_of_hasNonzeroDenominator p hDenominator)
        (Outgoing.mk (outputChannel p)) (Incident.mk (inputChannel p)) = transfer p := by
  have hResponse :=
    (response_nominal_reference_coordinates p hDenominator (inputAmplitude p 1)).2
  simpa [inputAmplitude, Matrix.toLpLin_apply] using hResponse

/-- The nominal-right N5 reflection entry is zero. -/
lemma responseTransform_entry_nominalRight_nominalRight (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) :
    (netlist p).responseTransform (isWellPosed_of_hasNonzeroDenominator p hDenominator)
        (Outgoing.mk (outputChannel p)) (Incident.mk (outputChannel p)) = 0 := by
  have hResponse := (response_nominal_reference_coordinates p hDenominator
    (nominalRightIncidentAmplitude p 1)).2
  simpa [nominalRightIncidentAmplitude, Matrix.toLpLin_apply,
    inputChannel_ne_outputChannel p] using hResponse

/-!

## C. Independent and packaged two-port scattering

-/

/-- The independently stated nominal right-to-left scalar transmission. -/
def nominalRightToLeftTransmission (p : Parameters) : ModeTransform Unit Unit :=
  fun _ _ => transfer p.reverse

/-- The independently stated nominal left-to-right scalar transmission. -/
def nominalLeftToRightTransmission (p : Parameters) : ModeTransform Unit Unit :=
  fun _ _ => transfer p

/-- The independent reflectionless nominal two-port behavior of the DCDR. -/
def nominalTwoPortBehavior (p : Parameters) : TwoPortScatteringBehavior Unit Unit :=
  ReflectionlessTwoPort.behavior
    (nominalRightToLeftTransmission p) (nominalLeftToRightTransmission p)

/-- The independent reflectionless nominal two-port scattering matrix of the DCDR. -/
def nominalTwoPortScattering (p : Parameters) : ScatteringMatrix (Unit ⊕ Unit) :=
  ReflectionlessTwoPort.scattering
    (nominalRightToLeftTransmission p) (nominalLeftToRightTransmission p)

/-- The independent nominal scattering matrix realizes its stated behavior. -/
lemma nominalTwoPortScattering_realizes_behavior (p : Parameters) :
    (nominalTwoPortScattering p).toTwoPortScatteringBehavior = nominalTwoPortBehavior p := by
  exact ReflectionlessTwoPort.scattering_realizes_behavior
    (nominalRightToLeftTransmission p) (nominalLeftToRightTransmission p)

/-- The original relation reindexed into nominal left/right coordinates. -/
def nominalExternalBehavior (p : Parameters) : TwoPortScatteringBehavior Unit Unit :=
  (netlist p).behavior.reindex
    (nominalTwoPortExternalIncidentEquiv p) (nominalTwoPortExternalOutgoingEquiv p)

/-- The well-posed N5 response packaged in nominal left/right coordinates. -/
noncomputable def packagedNominalTwoPortScattering (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) :
    TwoPortScatteringTransform Unit Unit :=
  ((((netlist p).packagedScattering
      (isWellPosed_of_hasNonzeroDenominator p hDenominator)).reindex
        (nominalTwoPortExternalChannelEquiv p).symm).toTwoPortScatteringTransform)

/-- Nominal packaging is direct endpoint relabeling of the proof-gated N5 response. -/
lemma packagedNominalTwoPortScattering_eq_responseTransform_reindex (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) :
    packagedNominalTwoPortScattering p hDenominator =
      ((netlist p).responseTransform
        (isWellPosed_of_hasNonzeroDenominator p hDenominator)).reindex
          (nominalTwoPortExternalIncidentEquiv p)
          (nominalTwoPortExternalOutgoingEquiv p) := by
  ext (output | output) (input | input) <;>
    rcases output with ⟨⟨⟩⟩ <;>
    rcases input with ⟨⟨⟩⟩ <;> rfl

/-- The packaged nominal N5 scattering has zero left reflection. -/
@[simp]
lemma packagedNominalTwoPortScattering_apply_inl_inl (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) :
    packagedNominalTwoPortScattering p hDenominator
        (Sum.inl (Outgoing.mk ())) (Sum.inl (Incident.mk ())) = 0 := by
  rw [packagedNominalTwoPortScattering_eq_responseTransform_reindex]
  exact responseTransform_entry_nominalLeft_nominalLeft p hDenominator

/-- The packaged nominal N5 scattering has the independent right-to-left entry. -/
@[simp]
lemma packagedNominalTwoPortScattering_apply_inl_inr (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) :
    packagedNominalTwoPortScattering p hDenominator
        (Sum.inl (Outgoing.mk ())) (Sum.inr (Incident.mk ())) = transfer p.reverse := by
  rw [packagedNominalTwoPortScattering_eq_responseTransform_reindex]
  exact responseTransform_entry_nominalLeft_nominalRight p hDenominator

/-- The packaged nominal N5 scattering has the independent left-to-right entry. -/
@[simp]
lemma packagedNominalTwoPortScattering_apply_inr_inl (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) :
    packagedNominalTwoPortScattering p hDenominator
        (Sum.inr (Outgoing.mk ())) (Sum.inl (Incident.mk ())) = transfer p := by
  rw [packagedNominalTwoPortScattering_eq_responseTransform_reindex]
  exact responseTransform_entry_nominalRight_nominalLeft p hDenominator

/-- The packaged nominal N5 scattering has zero right reflection. -/
@[simp]
lemma packagedNominalTwoPortScattering_apply_inr_inr (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) :
    packagedNominalTwoPortScattering p hDenominator
        (Sum.inr (Outgoing.mk ())) (Sum.inr (Incident.mk ())) = 0 := by
  rw [packagedNominalTwoPortScattering_eq_responseTransform_reindex]
  exact responseTransform_entry_nominalRight_nominalRight p hDenominator

/-- The packaged nominal graph is exactly the reindexed original netlist behavior. -/
lemma toBehavior_packagedNominalTwoPortScattering (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) :
    (packagedNominalTwoPortScattering p hDenominator).toBehavior =
      nominalExternalBehavior p := by
  rw [packagedNominalTwoPortScattering_eq_responseTransform_reindex,
    ModeTransform.toBehavior_reindex, nominalExternalBehavior]
  ext state
  rcases state with ⟨input, output⟩
  rw [LinearBehavior.mem_reindex_iff, LinearBehavior.mem_reindex_iff]
  have hGraph := (netlist p).toBehavior_responseTransform
    (isWellPosed_of_hasNonzeroDenominator p hDenominator)
  constructor
  · intro hMember
    exact hGraph ▸ hMember
  · intro hMember
    exact hGraph.symm ▸ hMember

/-- The packaged N5 transform realizes the independent nominal two-port law. -/
lemma packagedNominalTwoPortScattering_eq_nominalTwoPortScatteringTransform
    (p : Parameters) (hDenominator : p.HasNonzeroDenominator) :
    packagedNominalTwoPortScattering p hDenominator =
      (nominalTwoPortScattering p).toTwoPortScatteringTransform := by
  rw [packagedNominalTwoPortScattering_eq_responseTransform_reindex]
  ext (output | output) (input | input) <;>
    rcases output with ⟨⟨⟩⟩ <;>
    rcases input with ⟨⟨⟩⟩
  · exact responseTransform_entry_nominalLeft_nominalLeft p hDenominator
  · exact responseTransform_entry_nominalLeft_nominalRight p hDenominator
  · exact responseTransform_entry_nominalRight_nominalLeft p hDenominator
  · exact responseTransform_entry_nominalRight_nominalRight p hDenominator

/-- On the solve gate, the reindexed relation equals the independent nominal behavior. -/
lemma nominalExternalBehavior_eq_nominalTwoPortBehavior (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) :
    nominalExternalBehavior p = nominalTwoPortBehavior p := by
  calc
    nominalExternalBehavior p =
        (packagedNominalTwoPortScattering p hDenominator).toBehavior :=
      (toBehavior_packagedNominalTwoPortScattering p hDenominator).symm
    _ = (nominalTwoPortScattering p).toTwoPortScatteringTransform.toBehavior := by
      rw [packagedNominalTwoPortScattering_eq_nominalTwoPortScatteringTransform]
    _ = nominalTwoPortBehavior p := nominalTwoPortScattering_realizes_behavior p

/-!

## D. Scalar pivot and backward-first chain

-/

/-- The packaged nominal right-to-left block has the independently stated scalar entry. -/
lemma packagedNominalTwoPortScattering_rightToLeftTransmission_entry (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) :
    (packagedNominalTwoPortScattering p hDenominator).rightToLeftTransmission
        (BackwardWave.mk ()) (BackwardWave.mk ()) = transfer p.reverse := by
  rw [TwoPortScatteringTransform.rightToLeftTransmission_apply]
  exact packagedNominalTwoPortScattering_apply_inl_inr p hDenominator

/-- The packaged nominal left-to-right block has the independently stated scalar entry. -/
lemma packagedNominalTwoPortScattering_leftToRightTransmission_entry (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) :
    (packagedNominalTwoPortScattering p hDenominator).leftToRightTransmission
        (ForwardWave.mk ()) (ForwardWave.mk ()) = transfer p := by
  rw [TwoPortScatteringTransform.leftToRightTransmission_apply]
  exact packagedNominalTwoPortScattering_apply_inr_inl p hDenominator

/-- The complete packaged nominal left-reflection block is zero. -/
lemma packagedNominalTwoPortScattering_leftReflection_eq_zero (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) :
    (packagedNominalTwoPortScattering p hDenominator).leftReflection = 0 := by
  ext output input
  rcases output with ⟨⟨⟩⟩
  rcases input with ⟨⟨⟩⟩
  rw [TwoPortScatteringTransform.leftReflection_apply]
  exact packagedNominalTwoPortScattering_apply_inl_inl p hDenominator

/-- The complete packaged nominal right-reflection block is zero. -/
lemma packagedNominalTwoPortScattering_rightReflection_eq_zero (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) :
    (packagedNominalTwoPortScattering p hDenominator).rightReflection = 0 := by
  ext output input
  rcases output with ⟨⟨⟩⟩
  rcases input with ⟨⟨⟩⟩
  rw [TwoPortScatteringTransform.rightReflection_apply]
  exact packagedNominalTwoPortScattering_apply_inr_inr p hDenominator

/-- A constant amplitude on the singleton nominal backward-wave family. -/
private def nominalBackwardAmplitude (value : ℂ) :
    ModeAmplitude (BackwardWave Unit) :=
  WithLp.toLp 2 fun _ => value

/-- The nominal right-to-left block acts by its independently stated scalar transmission. -/
lemma packagedNominalTwoPortScattering_rightToLeftTransmission_apply (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator)
    (amplitude : ModeAmplitude (BackwardWave Unit)) :
    (packagedNominalTwoPortScattering p hDenominator).rightToLeftTransmission.toLinearMap
        amplitude =
      WithLp.toLp 2 (fun _ => transfer p.reverse * amplitude (BackwardWave.mk ())) := by
  apply WithLp.ofLp_injective 2
  funext output
  rcases output with ⟨⟨⟩⟩
  simp only [ModeTransform.toLinearMap, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]
  rw [← BackwardWave.channelEquiv.symm.sum_comp, Fintype.sum_unique]
  simp

/-- The nominal chain pivot is bijective exactly when right-to-left transmission is nonzero. -/
lemma packagedNominalTwoPortScattering_hasBijectiveRightToLeftTransmission_iff
    (p : Parameters) (hDenominator : p.HasNonzeroDenominator) :
    (packagedNominalTwoPortScattering p hDenominator).HasBijectiveRightToLeftTransmission ↔
      transfer p.reverse ≠ 0 := by
  constructor
  · intro hBijective hZero
    have hMapped :
        (packagedNominalTwoPortScattering p hDenominator).rightToLeftTransmission.toLinearMap
            (nominalBackwardAmplitude 1) =
          (packagedNominalTwoPortScattering p hDenominator).rightToLeftTransmission.toLinearMap
            0 := by
      rw [packagedNominalTwoPortScattering_rightToLeftTransmission_apply,
        packagedNominalTwoPortScattering_rightToLeftTransmission_apply]
      apply WithLp.ofLp_injective 2
      funext index
      rcases index with ⟨⟨⟩⟩
      simp [hZero]
    have hEqual := hBijective.1 hMapped
    have hCoordinate := congrArg
      (fun amplitude : ModeAmplitude (BackwardWave Unit) =>
        amplitude (BackwardWave.mk ())) hEqual
    norm_num [nominalBackwardAmplitude] at hCoordinate
  · intro hTransmission
    constructor
    · intro first second hEqual
      apply WithLp.ofLp_injective 2
      funext index
      rcases index with ⟨⟨⟩⟩
      have hCoordinate := congrArg
        (fun amplitude : ModeAmplitude (BackwardWave Unit) =>
          amplitude (BackwardWave.mk ())) hEqual
      rw [packagedNominalTwoPortScattering_rightToLeftTransmission_apply,
        packagedNominalTwoPortScattering_rightToLeftTransmission_apply] at hCoordinate
      simpa using mul_left_cancel₀ hTransmission hCoordinate
    · intro output
      refine ⟨nominalBackwardAmplitude
        ((transfer p.reverse)⁻¹ * output (BackwardWave.mk ())), ?_⟩
      rw [packagedNominalTwoPortScattering_rightToLeftTransmission_apply]
      apply WithLp.ofLp_injective 2
      funext index
      rcases index with ⟨⟨⟩⟩
      simp [nominalBackwardAmplitude, hTransmission]

/-- A nonzero nominal right-to-left transmission supplies the exact N3T pivot. -/
lemma packagedNominalTwoPortScattering_hasBijectiveRightToLeftTransmission
    (p : Parameters) (hDenominator : p.HasNonzeroDenominator)
    (hTransmission : transfer p.reverse ≠ 0) :
    (packagedNominalTwoPortScattering p hDenominator).HasBijectiveRightToLeftTransmission :=
  (packagedNominalTwoPortScattering_hasBijectiveRightToLeftTransmission_iff
    p hDenominator).2 hTransmission

/-- The totalized explicit nominal chain matrix in backward-first order. -/
def nominalBackwardFirstChainMatrix (p : Parameters) :
    BackwardFirstChainTransform Unit Unit
  | Sum.inl _, Sum.inl _ => (transfer p.reverse)⁻¹
  | Sum.inl _, Sum.inr _ => 0
  | Sum.inr _, Sum.inl _ => 0
  | Sum.inr _, Sum.inr _ => transfer p

/-- The behavior-derived nominal chain on the independent solve and pivot gates. -/
noncomputable def nominalBackwardFirstChainTransform (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) (hTransmission : transfer p.reverse ≠ 0) :
    BackwardFirstChainTransform Unit Unit :=
  (packagedNominalTwoPortScattering p hDenominator).toBackwardFirstChainTransform
    (packagedNominalTwoPortScattering_hasBijectiveRightToLeftTransmission
      p hDenominator hTransmission)

/-- The proof-dependent nominal pivot inverse has the reciprocal scalar entry. -/
lemma packagedNominalTwoPortScattering_rightToLeftTransmissionInverse_entry
    (p : Parameters) (hDenominator : p.HasNonzeroDenominator)
    (hTransmission : transfer p.reverse ≠ 0) :
    let hPivot := packagedNominalTwoPortScattering_hasBijectiveRightToLeftTransmission
      p hDenominator hTransmission
    ((packagedNominalTwoPortScattering p hDenominator).rightToLeftTransmissionInverse hPivot)
        (BackwardWave.mk ()) (BackwardWave.mk ()) = (transfer p.reverse)⁻¹ := by
  let scattering := packagedNominalTwoPortScattering p hDenominator
  let hPivot := packagedNominalTwoPortScattering_hasBijectiveRightToLeftTransmission
    p hDenominator hTransmission
  have hMatrix := scattering.inverse_mul_rightToLeftTransmission hPivot
  have hEntry := congrArg
    (fun matrix : ModeTransform (BackwardWave Unit) (BackwardWave Unit) =>
      matrix (BackwardWave.mk ()) (BackwardWave.mk ())) hMatrix
  have hProduct :
      (scattering.rightToLeftTransmissionInverse hPivot)
          (BackwardWave.mk ()) (BackwardWave.mk ()) * transfer p.reverse = 1 := by
    simp only [Matrix.mul_apply] at hEntry
    rw [← BackwardWave.channelEquiv.symm.sum_comp, Fintype.sum_unique] at hEntry
    simpa [scattering] using hEntry
  exact (mul_eq_one_iff_eq_inv₀ hTransmission).mp hProduct

/-- The behavior-derived nominal chain is the explicit diagonal matrix. -/
lemma nominalBackwardFirstChainTransform_eq_matrix (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) (hTransmission : transfer p.reverse ≠ 0) :
    nominalBackwardFirstChainTransform p hDenominator hTransmission =
      nominalBackwardFirstChainMatrix p := by
  rw [nominalBackwardFirstChainTransform,
    TwoPortScatteringTransform.toBackwardFirstChainTransform_eq_blockFormula]
  ext (output | output) (input | input) <;>
    rcases output with ⟨⟨⟩⟩ <;>
    rcases input with ⟨⟨⟩⟩ <;>
    simp [TwoPortScatteringTransform.backwardFirstChainBlockFormula,
      nominalBackwardFirstChainMatrix,
      packagedNominalTwoPortScattering_leftReflection_eq_zero,
      packagedNominalTwoPortScattering_rightReflection_eq_zero,
      packagedNominalTwoPortScattering_rightToLeftTransmissionInverse_entry
        p hDenominator hTransmission]

/-- The nominal chain graph is the backward-first regrouping of the reindexed N5 relation. -/
lemma toBehavior_nominalBackwardFirstChainTransform (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) (hTransmission : transfer p.reverse ≠ 0) :
    (nominalBackwardFirstChainTransform p hDenominator hTransmission).toBehavior =
      (nominalExternalBehavior p).toBackwardFirst := by
  rw [nominalBackwardFirstChainTransform,
    TwoPortScatteringTransform.toBehavior_toBackwardFirstChainTransform]
  unfold TwoPortScatteringTransform.toBackwardFirstBehavior
  rw [toBehavior_packagedNominalTwoPortScattering]

/-- The nominal DCDR chain has the automatically transported leading-block pivot. -/
lemma nominalBackwardFirstChainTransform_hasBijectiveLeadingBlock (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) (hTransmission : transfer p.reverse ≠ 0) :
    (nominalBackwardFirstChainTransform p hDenominator hTransmission).HasBijectiveLeadingBlock :=
  TwoPortScatteringTransform.hasBijectiveLeadingBlock_toBackwardFirstChainTransform
    (packagedNominalTwoPortScattering p hDenominator)
    (packagedNominalTwoPortScattering_hasBijectiveRightToLeftTransmission
      p hDenominator hTransmission)

/-- Generic N3T conversion of the nominal chain back to scattering recovers the N5 two-port. -/
lemma nominalBackwardFirstChainTransform_roundTrip (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) (hTransmission : transfer p.reverse ≠ 0) :
    (nominalBackwardFirstChainTransform p hDenominator hTransmission).toTwoPortScatteringTransform
        (nominalBackwardFirstChainTransform_hasBijectiveLeadingBlock
          p hDenominator hTransmission) =
      packagedNominalTwoPortScattering p hDenominator :=
  TwoPortScatteringTransform.toTwoPortScatteringTransform_toBackwardFirstChainTransform
    (packagedNominalTwoPortScattering p hDenominator)
    (packagedNominalTwoPortScattering_hasBijectiveRightToLeftTransmission
      p hDenominator hTransmission)
    (nominalBackwardFirstChainTransform_hasBijectiveLeadingBlock
      p hDenominator hTransmission)

/-!

## E. Common-domain Z and chain agreement

-/

/-- The DCDR Z common domain extended by the independent nominal chain pivot.

The pivot is a separate field. It is not derived from ROC membership, either Schur certificate,
local loop contraction, no cancellation, reduced evaluation, or N5 well-posedness.
-/
structure IsZChainCrossSemanticsDomain (p : UnitDelayParameters)
    (certificate : ResponseReduction p) (z : ℂ) : Prop
    extends IsZCrossSemanticsDomain p certificate z where
  /-- The nominal right-to-left scalar transmission is nonzero at `q = z⁻¹`. -/
  nominalRightToLeftTransmission_ne_zero : transfer (p.at z⁻¹).reverse ≠ 0

/-- The extended domain's base witness supplies the fixed N5 solve gate. -/
lemma IsZChainCrossSemanticsDomain.hasNonzeroDenominator
    {p : UnitDelayParameters} {certificate : ResponseReduction p} {z : ℂ}
    (h : IsZChainCrossSemanticsDomain p certificate z) :
    (p.at z⁻¹).HasNonzeroDenominator :=
  h.toIsZCrossSemanticsDomain.hasNonzeroDenominator

/-- On the solve and pivot gates, recurrence response equals the nominal chain response entry. -/
lemma zTransfer_eq_nominalBackwardFirstChainTransform_entry
    (p : UnitDelayParameters) (z : ℂ)
    (hDenominator : (p.at z⁻¹).HasNonzeroDenominator)
    (hTransmission : transfer (p.at z⁻¹).reverse ≠ 0) :
    zTransfer p z =
      nominalBackwardFirstChainTransform (p.at z⁻¹) hDenominator hTransmission
        (Sum.inr (ForwardWave.mk ())) (Sum.inr (ForwardWave.mk ())) := by
  rw [zTransfer_eq_transfer,
    nominalBackwardFirstChainTransform_eq_matrix]
  rfl

/-- Proof object collecting the complete DCDR X-01 agreement including the nominal chain. -/
structure ZChainCrossSemanticsAgreement (p : UnitDelayParameters)
    (certificate : ResponseReduction p) (z : ℂ)
    (h : IsZChainCrossSemanticsDomain p certificate z) : Prop where
  /-- All causal-Z, rational, N5, Mason, scattering, and relational fields agree. -/
  base : ZCrossSemanticsAgreement p certificate z h.toIsZCrossSemanticsDomain
  /-- The recurrence response equals the bottom-right backward-first chain entry. -/
  backwardFirstChain :
    zTransfer p z =
      nominalBackwardFirstChainTransform (p.at z⁻¹) h.hasNonzeroDenominator
          h.nominalRightToLeftTransmission_ne_zero
        (Sum.inr (ForwardWave.mk ())) (Sum.inr (ForwardWave.mk ()))
  /-- The derived chain graph is the nominal backward-first original relation. -/
  chainBehavior :
    (nominalBackwardFirstChainTransform (p.at z⁻¹) h.hasNonzeroDenominator
        h.nominalRightToLeftTransmission_ne_zero).toBehavior =
      (nominalExternalBehavior (p.at z⁻¹)).toBackwardFirst
  /-- Generic N3T conversion recovers the complete nominal packaged scattering law. -/
  scatteringRoundTrip :
    let chain := nominalBackwardFirstChainTransform
      (p.at z⁻¹) h.hasNonzeroDenominator h.nominalRightToLeftTransmission_ne_zero
    chain.toTwoPortScatteringTransform
        (nominalBackwardFirstChainTransform_hasBijectiveLeadingBlock
          (p.at z⁻¹) h.hasNonzeroDenominator
            h.nominalRightToLeftTransmission_ne_zero) =
      packagedNominalTwoPortScattering (p.at z⁻¹) h.hasNonzeroDenominator

/-- On the explicit extended domain, every applicable DCDR X-01 view agrees.

The base record supplies causal impulse Z, reduced rational response, reciprocal-Z N5F,
circulation, fixed N5, complete Mason, packaged scattering, and full-vector relational behavior.
This extension adds the independently gated nominal backward-first chain and its N3T round trip.
-/
lemma zChainCrossSemantics_agree (p : UnitDelayParameters)
    (certificate : ResponseReduction p) (z : ℂ)
    (h : IsZChainCrossSemanticsDomain p certificate z) :
    ZChainCrossSemanticsAgreement p certificate z h where
  base := zCrossSemantics_agree p certificate z h.toIsZCrossSemanticsDomain
  backwardFirstChain :=
    zTransfer_eq_nominalBackwardFirstChainTransform_entry p z
      h.hasNonzeroDenominator h.nominalRightToLeftTransmission_ne_zero
  chainBehavior :=
    toBehavior_nominalBackwardFirstChainTransform (p.at z⁻¹)
      h.hasNonzeroDenominator h.nominalRightToLeftTransmission_ne_zero
  scatteringRoundTrip :=
    nominalBackwardFirstChainTransform_roundTrip (p.at z⁻¹)
      h.hasNonzeroDenominator h.nominalRightToLeftTransmission_ne_zero

end

end Optics.DCDR
