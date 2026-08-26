/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.Hierarchical
public import Physlib.Optics.Systems.DCDR.Mason
public import Physlib.Optics.Systems.DCDR.ZTransform

/-!
# Cross-semantics bridge for the DCDR Z-transform

## i. Overview

This file identifies the causal recurrence with the existing coherent DCDR semantics on an
explicit common domain. The rational N7 family and compiled N5 response come from
`Physlib/Optics/Systems/DCDR/Poles.lean:323-612`; the fixed N5 response comes from
`Physlib/Optics/Systems/DCDR/Response.lean:461-555`; and G-04 is the generic Mason/N5
instantiation at `Physlib/Optics/Systems/DCDR/Mason.lean:184-197`.

The organization follows the ring Z leg: promoted rational compilation in
`Physlib/Optics/Systems/Microring/AllPassDelayTransfer.lean:127-172`, the named ROC in
`AllPassZTransform.lean:234-289`, and the common-domain object and agreement in
`AllPassZTransformBridge.lean:321-428`. Here the recurrence polynomial is already the coherent
DCDR rational polynomial, so no coupler-unitarity identity is needed.

The DCDR netlist has a canonical typed two-channel packaged scattering boundary. It does not yet
have a declared left/right traveling-wave boundary partition, reverse-transmission pivot, or chain
transform. Consequently the agreement below includes the packaged scattering entry but does not
invent a chain view. A later joint boundary/chain slice would be needed before adding that field.

The ROC, recurrence coefficient contraction, local circulation contraction, reduced-response
Schur predicate, cancellation gates, and compiled solve domain remain distinct. No physical
resonance, coherent--incoherent equivalence, BIBO conclusion beyond S4P's gates, modal or
electromagnetic power statement, Maxwell time-domain interpretation, reciprocity, physical
frequency interpretation, or claim about the unavailable HOL script is made.

## ii. Key results

- `DCDR.zTransfer_eq_rationalZEliminationResponse`: causal and compiled reciprocal-Z responses.
- `DCDR.zTransfer_eq_reducedResponse`: the response-indexed S4 reduction on its cancellation
  gates.
- `DCDR.zTransfer_eq_circulationSeries`: the convergent coherent feedback expansion.
- `DCDR.IsZCrossSemanticsDomain`: the explicit common domain.
- `DCDR.zCrossSemantics_agree`: agreement of causal Z, reduced and compiled rational response,
  circulation, fixed N5, complete Mason, typed scattering, and relational behavior.

## iii. Table of contents

- A. Reciprocal-Z compiled response
- B. Circulation, fixed N5, Mason, and scattering
- C. Original relational behavior
- D. Common-domain agreement

## iv. References

This cross-semantics bridge is Physlib-original. FMICS'15 Theorem 3 supplies the printed
incoherent quotient shape; the coherent N7 branch used here is the source's own unprinted coherent
case and is not identified with the printed one.
-/

@[expose] public section

namespace Optics.DCDR

noncomputable section

open DelayTransfer
open Physlib.ZTransform

/-!

## A. Reciprocal-Z compiled response

-/

/-- Admissibility and a nonzero reciprocal-coordinate denominator put `z` in the compiled
reciprocal-Z response domain. -/
lemma rationalNetlist_mem_reciprocalZ_responseDomain (p : UnitDelayParameters) (z : ℂ)
    (hp : p.IsAdmissible) (hDenominator : p.denominatorPolynomial.eval z⁻¹ ≠ 0) :
    z ∈ (rationalNetlist p).reciprocalZ.responseDomain := by
  change zInverseEvaluation z ∈ (rationalNetlist p).responseDomain
  convert rationalNetlist_mem_responseDomain p z⁻¹ hp hDenominator using 1
  funext delay
  exact zInverseEvaluation_apply z delay

/-- The recurrence loop symbol is exactly the fixed-carrier loop gain at `q = z⁻¹`. -/
lemma delaySymbol_eq_fixedLoopGain (p : UnitDelayParameters) (z : ℂ) :
    delaySymbol (zFeedbackLags p) (zFeedbackCoefficients p) z⁻¹ =
      (p.at z⁻¹).loopGain := by
  rw [delaySymbol_zFeedbackCoefficients, p.eval_loopPolynomial]

/-- The recurrence and fixed-carrier N5 solve gates are the same at `q = z⁻¹`.

This equality of algebraic gates does not identify either gate with the analytic ROC.
-/
lemma recurrenceDenominator_ne_zero_iff_hasNonzeroDenominator
    (p : UnitDelayParameters) (z : ℂ) :
    p.denominatorPolynomial.eval z⁻¹ ≠ 0 ↔ (p.at z⁻¹).HasNonzeroDenominator := by
  rw [Parameters.HasNonzeroDenominator, ← p.eval_denominatorPolynomial]

/-- The recurrence transfer equals the proof-gated compiled reciprocal-Z response. -/
lemma zTransfer_eq_rationalZEliminationResponse (p : UnitDelayParameters) (z : ℂ)
    (hZ : z ∈ (rationalNetlist p).reciprocalZ.responseDomain) :
    zTransfer p z = rationalZEliminationResponse p z hZ := by
  rw [zTransfer_eq_responseModel, rationalZEliminationResponse_eq_responseModel]

/-- On the S4 cancellation and evaluation gates, the recurrence transfer equals the selected
reduced quotient. -/
lemma zTransfer_eq_reducedResponse {p : UnitDelayParameters}
    (certificate : ResponseReduction p) (z : ℂ)
    (hFactor : certificate.reduction.NoPoleCancellation z⁻¹)
    (hReduced : z⁻¹ ∈ certificate.reduction.reduced.evaluationDomain) :
    zTransfer p z = certificate.reduction.reduced.eval z⁻¹ := by
  rw [zTransfer_eq_responseModel]
  exact (certificate.reduced_eval_eq_responseModel z⁻¹ hFactor hReduced).symm

/-!

## B. Circulation, fixed N5, Mason, and scattering

-/

/-- The coherent DCDR circulation expansion at the reciprocal point `q = z⁻¹`. -/
def circulationSeries (p : UnitDelayParameters) (z : ℂ) : ℂ :=
  let fixed := p.at z⁻¹
  fixed.directGain + fixed.feedbackReadoutGain * fixed.feedbackDrive *
    ∑' n : ℕ, fixed.loopGain ^ n

/-- Strict loop contraction supplies the fixed-carrier scalar solve gate. -/
lemma hasNonzeroDenominator_of_norm_loopGain_lt_one (p : Parameters)
    (hContractive : ‖p.loopGain‖ < 1) : p.HasNonzeroDenominator := by
  rw [Parameters.HasNonzeroDenominator, Parameters.denominator]
  intro hZero
  have hLoop : p.loopGain = 1 := (sub_eq_zero.mp hZero).symm
  have hNorm := congrArg norm hLoop
  norm_num at hNorm
  linarith

/-- Under local loop contraction, the circulation series equals the fixed-carrier transfer. -/
lemma circulationSeries_eq_transfer (p : UnitDelayParameters) (z : ℂ)
    (hContractive : ‖(p.at z⁻¹).loopGain‖ < 1) :
    circulationSeries p z = transfer (p.at z⁻¹) := by
  have hDenominator : (p.at z⁻¹).HasNonzeroDenominator :=
    hasNonzeroDenominator_of_norm_loopGain_lt_one (p.at z⁻¹) hContractive
  change (p.at z⁻¹).denominator ≠ 0 at hDenominator
  rw [circulationSeries, tsum_geometric_of_norm_lt_one hContractive]
  rw [transfer, Parameters.responseNumerator, div_eq_mul_inv]
  have hInverse :
      (p.at z⁻¹).denominator * (p.at z⁻¹).denominator⁻¹ = 1 :=
    mul_inv_cancel₀ hDenominator
  calc
    (p.at z⁻¹).directGain +
          (p.at z⁻¹).feedbackReadoutGain * (p.at z⁻¹).feedbackDrive *
            (p.at z⁻¹).denominator⁻¹ =
        (p.at z⁻¹).directGain *
            ((p.at z⁻¹).denominator * (p.at z⁻¹).denominator⁻¹) +
          (p.at z⁻¹).feedbackReadoutGain * (p.at z⁻¹).feedbackDrive *
            (p.at z⁻¹).denominator⁻¹ := by rw [hInverse]; ring
    _ = ((p.at z⁻¹).directGain * (p.at z⁻¹).denominator +
          (p.at z⁻¹).feedbackReadoutGain * (p.at z⁻¹).feedbackDrive) *
            (p.at z⁻¹).denominator⁻¹ := by ring

/-- Under local contraction, the recurrence transfer equals the coherent circulation series. -/
lemma zTransfer_eq_circulationSeries (p : UnitDelayParameters) (z : ℂ)
    (hContractive : ‖(p.at z⁻¹).loopGain‖ < 1) :
    zTransfer p z = circulationSeries p z := by
  rw [zTransfer_eq_transfer, circulationSeries_eq_transfer p z hContractive]

/-- On the fixed solve gate, the recurrence transfer equals the selected fixed N5 response. -/
lemma zTransfer_eq_eliminationResponse (p : UnitDelayParameters) (z : ℂ)
    (hDenominator : (p.at z⁻¹).HasNonzeroDenominator) :
    zTransfer p z = eliminationResponse (p.at z⁻¹)
      (isWellPosed_of_hasNonzeroDenominator (p.at z⁻¹) hDenominator) := by
  rw [zTransfer_eq_transfer, eliminationResponse_eq_transfer (p.at z⁻¹) hDenominator]

/-- On the fixed solve gate, the recurrence transfer equals the complete Mason response. -/
lemma zTransfer_eq_masonResponse (p : UnitDelayParameters) (z : ℂ)
    (hDenominator : (p.at z⁻¹).HasNonzeroDenominator) :
    zTransfer p z = masonResponse (p.at z⁻¹) := by
  rw [zTransfer_eq_eliminationResponse p z hDenominator]
  exact (masonResponse_eq_eliminationResponse (p.at z⁻¹) hDenominator).symm

/-- The recurrence transfer equals the selected entry of the typed packaged scattering boundary. -/
lemma zTransfer_eq_packagedScattering_entry (p : UnitDelayParameters) (z : ℂ)
    (hDenominator : (p.at z⁻¹).HasNonzeroDenominator) :
    zTransfer p z =
      ((netlist (p.at z⁻¹)).packagedScattering
        (isWellPosed_of_hasNonzeroDenominator (p.at z⁻¹) hDenominator)).toModeTransform
          (outputChannel (p.at z⁻¹)) (inputChannel (p.at z⁻¹)) := by
  rw [zTransfer_eq_eliminationResponse p z hDenominator]
  rfl

/-!

## C. Original relational behavior

/-- The selected scalar value occurs in the original singular-safe external relation. -/
def HasSelectedRelationalResponse (p : Parameters) (value : ℂ) : Prop :=
  ∃ output : ModeAmplitude (netlist p).ExternalOutgoing,
    (inputAmplitude p 1, output) ∈ (netlist p).behavior ∧
      output (Outgoing.mk (outputChannel p)) = value

/-- On the solve gate, the recurrence value occurs in the original fixed-carrier relation. -/
lemma zTransfer_hasSelectedRelationalResponse (p : UnitDelayParameters) (z : ℂ)
    (hDenominator : (p.at z⁻¹).HasNonzeroDenominator) :
    HasSelectedRelationalResponse (p.at z⁻¹) (zTransfer p z) := by
  let fixed := p.at z⁻¹
  let hWellPosed := isWellPosed_of_hasNonzeroDenominator fixed hDenominator
  let output := (netlist fixed).responseTransform hWellPosed |>.toLinearMap
    (inputAmplitude fixed 1)
  refine ⟨output, ?_, ?_⟩
  · exact ((netlist fixed).mem_behavior_iff_eq_responseTransform
      hWellPosed _ _).2 rfl
  · have hEntry := responseTransform_apply_inputAmplitude fixed hWellPosed 1
    calc
      output (Outgoing.mk (outputChannel fixed)) =
          eliminationResponse fixed hWellPosed * 1 := by
        simpa [output] using hEntry
      _ = eliminationResponse fixed hWellPosed := by ring
      _ = zTransfer p z :=
        (zTransfer_eq_eliminationResponse p z hDenominator).symm

-/

/-!

## D. Common-domain agreement

-/

/-- The common domain on which the DCDR semantics used by X-01 are simultaneously meaningful.

The response-reduction certificate is an explicit parameter. Its pointwise cancellation and
evaluation gates, reduced Schur predicate, recurrence contraction, local circulation contraction,
and analytic ROC membership are separate fields. Coupler unitarity is absent because none of the
coherent DCDR response identifications uses it.
-/
structure IsZCrossSemanticsDomain (p : UnitDelayParameters)
    (certificate : ResponseReduction p) (z : ℂ) : Prop where
  /-- The real path gains lie in the rational component family's algebraic validity domain. -/
  isAdmissible : p.IsAdmissible
  /-- The recurrence coefficients satisfy the neutral strict Schur criterion. -/
  recurrenceIsContractive : p.IsZContractive
  /-- The response-indexed reduced quotient satisfies S4P's strict Schur predicate. -/
  reducedIsSchurStable : certificate.reduction.reduced.IsSchurStable
  /-- The evaluated coherent feedback loop has a convergent geometric circulation series. -/
  loopIsContractive : ‖(p.at z⁻¹).loopGain‖ < 1
  /-- The selected Z point belongs to the causal impulse-response transfer ROC. -/
  mem_zTransferROC : z ∈ zTransferROC p
  /-- The cancelled factor is nonzero at the selected reciprocal point. -/
  noPoleCancellation : certificate.reduction.NoPoleCancellation z⁻¹
  /-- The reciprocal point avoids the reduced denominator zeros. -/
  mem_reducedEvaluationDomain :
    z⁻¹ ∈ certificate.reduction.reduced.evaluationDomain

/-- A common-domain witness supplies the recurrence denominator gate from its ROC field. -/
lemma IsZCrossSemanticsDomain.recurrenceDenominator_ne_zero
    {p : UnitDelayParameters} {certificate : ResponseReduction p} {z : ℂ}
    (h : IsZCrossSemanticsDomain p certificate z) :
    p.denominatorPolynomial.eval z⁻¹ ≠ 0 :=
  recurrenceDenominator_ne_zero_of_mem_zTransferROC h.mem_zTransferROC

/-- A common-domain witness supplies the fixed-carrier N5 solve gate. -/
lemma IsZCrossSemanticsDomain.hasNonzeroDenominator
    {p : UnitDelayParameters} {certificate : ResponseReduction p} {z : ℂ}
    (h : IsZCrossSemanticsDomain p certificate z) :
    (p.at z⁻¹).HasNonzeroDenominator :=
  (recurrenceDenominator_ne_zero_iff_hasNonzeroDenominator p z).1
    h.recurrenceDenominator_ne_zero

/-- A common-domain witness supplies the proof-gated reciprocal-Z compiled response point. -/
lemma IsZCrossSemanticsDomain.mem_reciprocalZResponseDomain
    {p : UnitDelayParameters} {certificate : ResponseReduction p} {z : ℂ}
    (h : IsZCrossSemanticsDomain p certificate z) :
    z ∈ (rationalNetlist p).reciprocalZ.responseDomain :=
  rationalNetlist_mem_reciprocalZ_responseDomain p z h.isAdmissible
    h.recurrenceDenominator_ne_zero

/-- Recurrence contraction gives the neutral Z-transform Schur predicate independently of ROC. -/
lemma IsZCrossSemanticsDomain.zFeedback_isSchurStable
    {p : UnitDelayParameters} {certificate : ResponseReduction p} {z : ℂ}
    (h : IsZCrossSemanticsDomain p certificate z) :
    IsSchurStable (zFeedbackLags p) (zFeedbackCoefficients p) :=
  zFeedback_isSchurStable_of_isZContractive p h.recurrenceIsContractive

/-- Proof object collecting the DCDR cross-semantics agreement on its explicit common domain. -/
structure ZCrossSemanticsAgreement (p : UnitDelayParameters)
    (certificate : ResponseReduction p) (z : ℂ)
    (h : IsZCrossSemanticsDomain p certificate z) : Prop where
  /-- The recurrence loop symbol equals the evaluated coherent N7 loop gain. -/
  feedbackLoop :
    delaySymbol (zFeedbackLags p) (zFeedbackCoefficients p) z⁻¹ =
      (p.at z⁻¹).loopGain
  /-- The causal impulse-response transform equals the recurrence transfer. -/
  causalImpulseResponse : transform (causalOutput p unitImpulse) z = zTransfer p z
  /-- The recurrence transfer equals the response-indexed reduced quotient. -/
  reducedRationalResponse :
    zTransfer p z = certificate.reduction.reduced.eval z⁻¹
  /-- The recurrence transfer equals the compiled reciprocal-Z N5F response. -/
  rationalN5F :
    zTransfer p z = rationalZEliminationResponse p z h.mem_reciprocalZResponseDomain
  /-- The recurrence transfer equals the convergent coherent circulation series. -/
  circulation : zTransfer p z = circulationSeries p z
  /-- The recurrence transfer equals the selected fixed-carrier N5 response. -/
  fixedN5Response :
    zTransfer p z = eliminationResponse (p.at z⁻¹)
      (isWellPosed_of_hasNonzeroDenominator (p.at z⁻¹) h.hasNonzeroDenominator)
  /-- The recurrence transfer equals the complete extracted Mason response. -/
  completeMason : zTransfer p z = masonResponse (p.at z⁻¹)
  /-- The recurrence transfer equals the selected typed packaged-scattering entry. -/
  packagedScattering :
    zTransfer p z =
      ((netlist (p.at z⁻¹)).packagedScattering
        (isWellPosed_of_hasNonzeroDenominator
          (p.at z⁻¹) h.hasNonzeroDenominator)).toModeTransform
            (outputChannel (p.at z⁻¹)) (inputChannel (p.at z⁻¹))
  /-- The common scalar occurs in the original singular-safe relational behavior. -/
  relationalBehavior :
    HasSelectedRelationalResponse (p.at z⁻¹) (zTransfer p z)

/-- On the explicit common domain, all applicable DCDR views in the X-01 spine agree.

The applicable views are causal impulse Z, reduced response, compiled reciprocal-Z N5F,
circulation, fixed N5, complete Mason, typed packaged scattering, and the original relation. The
chain view is omitted for the boundary-and-pivot reason documented in the module overview.
-/
lemma zCrossSemantics_agree (p : UnitDelayParameters)
    (certificate : ResponseReduction p) (z : ℂ)
    (h : IsZCrossSemanticsDomain p certificate z) :
    ZCrossSemanticsAgreement p certificate z h where
  feedbackLoop := delaySymbol_eq_fixedLoopGain p z
  causalImpulseResponse :=
    transform_causalImpulseResponse_eq_zTransfer h.mem_zTransferROC
  reducedRationalResponse := zTransfer_eq_reducedResponse certificate z
    h.noPoleCancellation h.mem_reducedEvaluationDomain
  rationalN5F := zTransfer_eq_rationalZEliminationResponse p z
    h.mem_reciprocalZResponseDomain
  circulation := zTransfer_eq_circulationSeries p z h.loopIsContractive
  fixedN5Response := zTransfer_eq_eliminationResponse p z h.hasNonzeroDenominator
  completeMason := zTransfer_eq_masonResponse p z h.hasNonzeroDenominator
  packagedScattering :=
    zTransfer_eq_packagedScattering_entry p z h.hasNonzeroDenominator
  relationalBehavior :=
    zTransfer_hasSelectedRelationalResponse p z h.hasNonzeroDenominator

end

end Optics.DCDR
