/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Systems.Microring.AllPassChain
public import Physlib.Optics.Systems.Microring.AllPassDelayTransfer
public import Physlib.Optics.Systems.Microring.AllPassMason
public import Physlib.Optics.Systems.Microring.AllPassZTransform

/-!
# Fixed-carrier bridge for the all-pass Z-transform semantics

## i. Overview

This file compares the independently stated causal recurrence with the existing fixed-carrier
all-pass ring. The selected point `carrierPoint p` has reciprocal equal to the N7 propagation
component's negative-exponential carrier phase. Coupler unitarity converts the N5 response to the
standard recurrence quotient; the exact feedback solve gate remains explicit. The sequence-level
bridge additionally keeps transform convergence as hypotheses.

On their common domains, the recurrence transfer agrees with the circulation series, N5 response,
complete Mason response, typed scattering entry, and backward-first chain entry. None of these
equalities infers causality or an ROC from a fixed-carrier matrix. No material dispersion law,
physical group delay, time-domain Maxwell realization, or reciprocity statement is made.

## ii. Key results

- `AllPass.carrierPoint`: the fixed-carrier Z evaluation point.
- `AllPass.zTransfer_eq_throughTransfer`: the algebraic recurrence/ring bridge.
- `AllPass.zTransfer_eq_reciprocalZThroughResponse`: the causal recurrence and the proof-gated
  rational/N5F response agree by their common cleared equation.
- `AllPass.transform_causalOutput_eq_responseTransform_entry_mul`: the sequence-level N5 bridge.
- `AllPass.zTransfer_eq_masonResponseTransform_entry`: agreement with Mason semantics.
- `AllPass.zTransfer_eq_backwardFirstChainTransform_entry`: agreement with chain semantics.

## iii. Table of contents

- A. Fixed-carrier evaluation point
- B. N5 response and circulation series
- C. Sequence-level response bridge
- D. Mason, scattering, and chain views

## iv. References

This cross-semantics bridge is Physlib-original. The neutral Z-transform layer carries the cited
ITP 2014 and JAL 2018 source comparisons; the microring realization is derived separately.
-/

@[expose] public section

namespace Optics

noncomputable section

namespace AllPass

open Physlib.ZTransform
open DelayTransfer

/-! ## A. Fixed-carrier evaluation point -/

/-- The selected Z evaluation point whose reciprocal is the fixed-carrier phase factor. -/
def carrierPoint (p : Parameters) : ℂ :=
  (MatchedPropagation.carrierPhaseFactor p.roundTripPhase)⁻¹

/-- The reciprocal of the selected carrier point is exactly the negative-exponential phase
factor stored by the fixed-carrier propagation component. -/
@[simp]
lemma carrierPoint_inv (p : Parameters) :
    (carrierPoint p)⁻¹ = MatchedPropagation.carrierPhaseFactor p.roundTripPhase := by
  rw [carrierPoint, inv_inv]

/-- The ring's one-pass coefficient is field attenuation times the reciprocal carrier point. -/
lemma loopCoefficient_eq_fieldAttenuation_mul_carrierPoint_inv (p : Parameters) :
    p.loopCoefficient = (p.fieldAttenuation : ℂ) * (carrierPoint p)⁻¹ := by
  rw [carrierPoint_inv]
  rfl

/-! ## B. N5 response and circulation series -/

/-- After the formal loop factor is identified with `a*z⁻¹`, the recurrence and fixed-ring
denominators have exactly the same nonvanishing gate. This does not identify the analytic ROC with
the algebraic N5 solve domain. -/
lemma recurrenceDenominator_ne_zero_iff_hasNonzeroDenominator (p : Parameters) (z : ℂ)
    (hLoop : p.loopCoefficient = (p.fieldAttenuation : ℂ) * z⁻¹) :
    1 - (p.throughAmplitude : ℂ) * (p.fieldAttenuation : ℂ) * z⁻¹ ≠ 0 ↔
      p.HasNonzeroDenominator := by
  simp only [Parameters.HasNonzeroDenominator, Parameters.denominator,
    Parameters.loopGain, hLoop]
  rw [mul_assoc]

/-- Valid component models and the exact ring solve gate put `z` in the reciprocal-Z response
domain of the rational all-pass netlist. -/
lemma allPassRationalNetlist_mem_reciprocalZ_responseDomain (p : Parameters) (z : ℂ)
    (hLoop : p.loopCoefficient = (p.fieldAttenuation : ℂ) * z⁻¹)
    (hp : p.IsValid) (hDenominator : p.HasNonzeroDenominator) :
    z ∈ (allPassRationalNetlist p).reciprocalZ.responseDomain := by
  change zInverseEvaluation z ∈
    (allPassRationalNetlist p).toParameterizedNetlist.responseDomain
  convert allPassRationalNetlist_mem_responseDomain p z⁻¹ hLoop hp hDenominator using 1
  rfl

/-- The selected input-to-through entry of the proof-gated reciprocal-Z response. -/
noncomputable def reciprocalZThroughResponse (p : Parameters) (z : ℂ)
    (hZ : z ∈ (allPassRationalNetlist p).reciprocalZ.responseDomain) : ℂ :=
  (((allPassRationalNetlist p).reciprocalZ.response
        hZ).reindex
      (Incident.relabelEquiv
        (allPassRationalNetlist p).reciprocalZExternalChannelEquiv)
      (Outgoing.relabelEquiv
        (allPassRationalNetlist p).reciprocalZExternalChannelEquiv))
    (Outgoing.mk (allPassRationalFormalThroughChannel p))
    (Incident.mk (allPassRationalFormalInputChannel p))

/-- The reciprocal-Z response obeys the same cleared equation as the causal recurrence transfer.

The response side is transported to the formal-delay model and then discharged by
`allPassRationalNetlist_response_cleared`, whose proof expands the compiled N7 component and N5
wiring equations.
-/
lemma recurrenceDenominator_mul_reciprocalZThroughResponse (p : Parameters) (z : ℂ)
    (hZ : z ∈ (allPassRationalNetlist p).reciprocalZ.responseDomain)
    (hLoop : p.loopCoefficient = (p.fieldAttenuation : ℂ) * z⁻¹)
    (hp : p.IsValid) (hUnitary : p.coupler.IsUnitary)
    (hDenominator : p.HasNonzeroDenominator) :
    (1 - (p.throughAmplitude : ℂ) * (p.fieldAttenuation : ℂ) * z⁻¹) *
        reciprocalZThroughResponse p z hZ =
      (p.throughAmplitude : ℂ) - (p.fieldAttenuation : ℂ) * z⁻¹ := by
  have hResponse := (allPassRationalNetlist p).response_reciprocalZ_reindex hZ
  have hTransport := congrArg
    (fun transform =>
      (1 - (p.throughAmplitude : ℂ) * (p.fieldAttenuation : ℂ) * z⁻¹) *
        transform (Outgoing.mk (allPassRationalFormalThroughChannel p))
          (Incident.mk (allPassRationalFormalInputChannel p)))
    hResponse
  have hCleared := allPassRationalNetlist_response_cleared
    p z⁻¹ hLoop hp hUnitary hDenominator
  change
    (1 - (p.throughAmplitude : ℂ) * (p.fieldAttenuation : ℂ) * z⁻¹) *
        (((allPassRationalNetlist p).reciprocalZ.response hZ).reindex
          (Incident.relabelEquiv
            (allPassRationalNetlist p).reciprocalZExternalChannelEquiv)
          (Outgoing.relabelEquiv
            (allPassRationalNetlist p).reciprocalZExternalChannelEquiv))
          (Outgoing.mk (allPassRationalFormalThroughChannel p))
          (Incident.mk (allPassRationalFormalInputChannel p)) =
      (p.throughAmplitude : ℂ) - (p.fieldAttenuation : ℂ) * z⁻¹
  exact hTransport.trans hCleared

/-- On the rational response domain, the causal recurrence transfer equals the proof-gated
reciprocal-Z response derived from the compiled N7/N5 channel equations. -/
lemma zTransfer_eq_reciprocalZThroughResponse (p : Parameters) (z : ℂ)
    (hZ : z ∈ (allPassRationalNetlist p).reciprocalZ.responseDomain)
    (hLoop : p.loopCoefficient = (p.fieldAttenuation : ℂ) * z⁻¹)
    (hp : p.IsValid) (hUnitary : p.coupler.IsUnitary)
    (hDenominator : p.HasNonzeroDenominator) :
    zTransfer (p.throughAmplitude : ℂ) (p.fieldAttenuation : ℂ) z =
      reciprocalZThroughResponse p z hZ := by
  have hRecurrenceDenominator :=
    (recurrenceDenominator_ne_zero_iff_hasNonzeroDenominator p z hLoop).2 hDenominator
  apply mul_left_cancel₀ hRecurrenceDenominator
  rw [recurrenceDenominator_mul_zTransfer hRecurrenceDenominator,
    recurrenceDenominator_mul_reciprocalZThroughResponse
      p z hZ hLoop hp hUnitary hDenominator]

/-- Evaluating the recurrence delay at the stored carrier factor recovers the N7/N5 all-pass
through transfer. -/
lemma zTransfer_eq_throughTransfer (p : Parameters) (z : ℂ)
    (hUnitary : p.coupler.IsUnitary) (hDenominator : p.HasNonzeroDenominator)
    (hLoop : p.loopCoefficient = (p.fieldAttenuation : ℂ) * z⁻¹) :
    zTransfer (p.throughAmplitude : ℂ) (p.fieldAttenuation : ℂ) z =
      throughTransfer p := by
  rw [zTransfer_eq, throughTransfer_eq_standard p hUnitary hDenominator]
  simp [standardThroughTransfer, Parameters.denominator, Parameters.loopGain,
    hLoop, mul_assoc]

/-- Under contraction, the recurrence transfer agrees with the convergent circulation series on
the same selected delay value. -/
lemma zTransfer_eq_throughTransferSeries (p : Parameters) (z : ℂ)
    (hUnitary : p.coupler.IsUnitary) (hContractive : p.IsContractive)
    (hLoop : p.loopCoefficient = (p.fieldAttenuation : ℂ) * z⁻¹) :
    zTransfer (p.throughAmplitude : ℂ) (p.fieldAttenuation : ℂ) z =
      throughTransferSeries p := by
  rw [zTransfer_eq_throughTransfer p z hUnitary hContractive.hasNonzeroDenominator hLoop,
    throughTransfer_eq_roundTripSeries p hContractive]

/-- The recurrence transfer equals the input-to-through N5 response entry on the common domain. -/
lemma zTransfer_eq_responseTransform_entry (p : Parameters) (z : ℂ)
    (hUnitary : p.coupler.IsUnitary) (hDenominator : p.HasNonzeroDenominator)
    (hLoop : p.loopCoefficient = (p.fieldAttenuation : ℂ) * z⁻¹) :
    zTransfer (p.throughAmplitude : ℂ) (p.fieldAttenuation : ℂ) z =
      (netlist p).responseTransform
        (isWellPosed_of_hasNonzeroDenominator p hDenominator)
        (Outgoing.mk (throughChannel p)) (Incident.mk (inputChannel p)) := by
  rw [zTransfer_eq_throughTransfer p z hUnitary hDenominator hLoop,
    responseTransform_entry_through_input p hDenominator]

/-! ## C. Sequence-level response bridge -/

/-- On the common convergence and solve domain, the transform of the causal recurrence output is
the N5 input-to-through response entry times the input transform. The summability hypotheses are
not inferred from the fixed-carrier network. -/
lemma transform_causalOutput_eq_responseTransform_entry_mul (p : Parameters) (z : ℂ)
    {input : ℤ → ℂ} (hInput : IsCausal input)
    (hInputSummable : Summable (seriesTerm input z))
    (hOutputSummable : Summable
      (seriesTerm
        (causalOutput (p.throughAmplitude : ℂ) (p.fieldAttenuation : ℂ) input) z))
    (hUnitary : p.coupler.IsUnitary) (hDenominator : p.HasNonzeroDenominator)
    (hLoop : p.loopCoefficient = (p.fieldAttenuation : ℂ) * z⁻¹) :
    transform
        (causalOutput (p.throughAmplitude : ℂ) (p.fieldAttenuation : ℂ) input) z =
      (netlist p).responseTransform
          (isWellPosed_of_hasNonzeroDenominator p hDenominator)
          (Outgoing.mk (throughChannel p)) (Incident.mk (inputChannel p)) *
        transform input z := by
  have hRecurrenceDenominator :
      1 - (p.throughAmplitude : ℂ) * (p.fieldAttenuation : ℂ) * z⁻¹ ≠ 0 := by
    simpa [Parameters.HasNonzeroDenominator, Parameters.denominator,
      Parameters.loopGain, hLoop, mul_assoc] using hDenominator
  rw [transform_causalOutput hInput hInputSummable hOutputSummable
      hRecurrenceDenominator,
    zTransfer_eq_responseTransform_entry p z hUnitary hDenominator hLoop]

/-- Under contraction, the canonical fixed-carrier point gives the sequence-level N5 bridge.
Contraction supplies the solve gate, while transform convergence remains explicit. -/
lemma transform_causalOutput_carrierPoint_eq_responseTransform_entry_mul (p : Parameters)
    {input : ℤ → ℂ} (hInput : IsCausal input)
    (hInputSummable : Summable (seriesTerm input (carrierPoint p)))
    (hOutputSummable : Summable
      (seriesTerm
        (causalOutput (p.throughAmplitude : ℂ) (p.fieldAttenuation : ℂ) input)
        (carrierPoint p)))
    (hUnitary : p.coupler.IsUnitary) (hContractive : p.IsContractive) :
    transform
        (causalOutput (p.throughAmplitude : ℂ) (p.fieldAttenuation : ℂ) input)
        (carrierPoint p) =
      (netlist p).responseTransform
          (isWellPosed_of_hasNonzeroDenominator p hContractive.hasNonzeroDenominator)
          (Outgoing.mk (throughChannel p)) (Incident.mk (inputChannel p)) *
        transform input (carrierPoint p) := by
  exact transform_causalOutput_eq_responseTransform_entry_mul p (carrierPoint p)
    hInput hInputSummable hOutputSummable hUnitary hContractive.hasNonzeroDenominator
    (loopCoefficient_eq_fieldAttenuation_mul_carrierPoint_inv p)

/-! ## D. Mason, scattering, and chain views -/

/-- The recurrence transfer equals the complete extracted Mason response entry. -/
lemma zTransfer_eq_masonResponseTransform_entry (p : Parameters) (z : ℂ)
    (hUnitary : p.coupler.IsUnitary) (hDenominator : p.HasNonzeroDenominator)
    (hLoop : p.loopCoefficient = (p.fieldAttenuation : ℂ) * z⁻¹) :
    zTransfer (p.throughAmplitude : ℂ) (p.fieldAttenuation : ℂ) z =
      (netlist p).masonResponseTransform
        (Outgoing.mk (throughChannel p)) (Incident.mk (inputChannel p)) := by
  rw [zTransfer_eq_throughTransfer p z hUnitary hDenominator hLoop,
    masonResponseTransform_entry_through_input p hDenominator]

/-- The recurrence transfer equals the packaged left-to-right typed-scattering entry. -/
lemma zTransfer_eq_packagedScattering_entry (p : Parameters) (z : ℂ)
    (hUnitary : p.coupler.IsUnitary) (hDenominator : p.HasNonzeroDenominator)
    (hLoop : p.loopCoefficient = (p.fieldAttenuation : ℂ) * z⁻¹) :
    zTransfer (p.throughAmplitude : ℂ) (p.fieldAttenuation : ℂ) z =
      (packagedTwoPortScattering p hDenominator).leftToRightTransmission
        (ForwardWave.mk ()) (ForwardWave.mk ()) := by
  rw [zTransfer_eq_throughTransfer p z hUnitary hDenominator hLoop,
    packagedTwoPortScattering_leftToRightTransmission_entry p hDenominator]

/-- Under the additional chain-pivot gate, the recurrence transfer equals the bottom-right
backward-first chain entry. -/
lemma zTransfer_eq_backwardFirstChainTransform_entry (p : Parameters) (z : ℂ)
    (hUnitary : p.coupler.IsUnitary) (hDenominator : p.HasNonzeroDenominator)
    (hLoop : p.loopCoefficient = (p.fieldAttenuation : ℂ) * z⁻¹)
    (hTransmission : throughTransfer p ≠ 0) :
    zTransfer (p.throughAmplitude : ℂ) (p.fieldAttenuation : ℂ) z =
      backwardFirstChainTransform p hDenominator hTransmission
        (Sum.inr (ForwardWave.mk ())) (Sum.inr (ForwardWave.mk ())) := by
  rw [zTransfer_eq_throughTransfer p z hUnitary hDenominator hLoop,
    backwardFirstChainTransform_eq_matrix p hDenominator hTransmission]
  rfl

end AllPass

end

end Optics
