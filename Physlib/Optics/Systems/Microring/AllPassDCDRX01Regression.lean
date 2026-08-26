/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Systems.DCDR.NominalChainRegression
public import Physlib.Optics.Systems.Microring.AllPassZTransformBridgeRegression

/-!
# Joint all-pass ring and DCDR X-01 regression

## i. Overview

This module combines the accepted all-pass ring X-01 witness with the nominal-chain DCDR witness.
The joint predicate is a conjunction of two system-specific agreement records. It deliberately
contains no equality between the ring and DCDR response values.

The ring fixture has response `1/7` and backward-first diagonal `(7, 1/7)`. The DCDR fixture uses
`z = I`, response `-(7/8)I`, and diagonal `((8/7)I, -(7/8)I)`. Independent recurrence, raw N5,
Mason, and chain anchors establish those different values without invoking the joint predicate.
The DCDR wrong-reference-plane matrix swaps its diagonal and is rejected on the same fixture.

## ii. Key results

- `Optics.RingDCDRX01Agreement`: the joint predicate with no cross-system value equality.
- `Optics.ringDCDRX01Regression_hasAgreement`: one accepted ring and one DCDR inhabit it.
- `Optics.ringDCDRX01Regression_independentAnchors`: independently pinned unequal values.
- `Optics.ringDCDRX01Regression_wrongReferencePlane_rejected`: fail-capable joint sentinel.

## iii. Table of contents

- A. Joint two-system predicate
- B. Independent unequal anchors
- C. Joint negative sentinel

## iv. References

This regression closes only the algebraic cross-semantics row X-01. It makes no claim of physical
reference planes, reciprocity, physical time reversal, physical resonance, coherent--incoherent
equivalence, power, Maxwell time-domain meaning, physical-frequency meaning, or shared response
value between the two systems.
-/

@[expose] public section

namespace Optics

noncomputable section

open Physlib.ZTransform

/-!

## A. Joint two-system predicate

-/

/-- A ring and a DCDR each carry their complete X-01 agreement on their own common domain.

The predicate intentionally has no equation relating the two systems' response values.
-/
def RingDCDRX01Agreement
    (ring : AllPass.Parameters) (ringZ : ℂ)
    (ringDomain : AllPass.IsZCrossSemanticsDomain ring ringZ)
    (dcdr : DCDR.UnitDelayParameters) (certificate : DCDR.ResponseReduction dcdr)
    (dcdrZ : ℂ)
    (dcdrDomain : DCDR.IsZChainCrossSemanticsDomain dcdr certificate dcdrZ) : Prop :=
  AllPass.ZCrossSemanticsAgreement ring ringZ ringDomain ∧
    DCDR.ZChainCrossSemanticsAgreement dcdr certificate dcdrZ dcdrDomain

/-- The accepted resonant ring and stable nonreal DCDR fixtures inhabit the joint predicate. -/
lemma ringDCDRX01Regression_hasAgreement :
    RingDCDRX01Agreement AllPass.allPassRegressionResonanceParameters 1
      AllPass.allPassZRegression_resonance_crossSemanticsDomain
      DCDR.stableUnitDelayParameters DCDR.stableResponseReduction Complex.I
      DCDR.zChainRegression_crossSemanticsDomain := by
  exact ⟨AllPass.zCrossSemantics_agree AllPass.allPassRegressionResonanceParameters 1
      AllPass.allPassZRegression_resonance_crossSemanticsDomain,
    DCDR.zChainRegression_crossSemanticsAgreement⟩

/-!

## B. Independent unequal anchors

-/

/-- Independent ring and DCDR audits pin their distinct responses and chain diagonals.

The ring conjunct uses direct recurrence coefficients, raw N5 channel elimination, the enumerated
loop Mason value, and independently unfolded chain entries. The DCDR conjunct is its causal,
reciprocal-Z, raw-N5, eleven-branch Mason, and chain audit. No joint or DCDR cross-semantics lemma
is used.
-/
lemma ringDCDRX01Regression_independentAnchors :
    AllPass.zTransfer (3 / 5) (1 / 2) 1 = 1 / 7 ∧
      (AllPass.netlist AllPass.allPassRegressionResonanceParameters).responseTransform
          AllPass.allPassRegression_resonance_isWellPosed
          (Outgoing.mk
            (AllPass.throughChannel AllPass.allPassRegressionResonanceParameters))
          (Incident.mk
            (AllPass.inputChannel AllPass.allPassRegressionResonanceParameters)) = 1 / 7 ∧
      AllPass.loopMasonThroughTransfer AllPass.allPassRegressionResonanceParameters = 1 / 7 ∧
      AllPass.allPassChainRegressionResonanceChain
          (Sum.inl (BackwardWave.mk ())) (Sum.inl (BackwardWave.mk ())) = 7 ∧
      AllPass.allPassChainRegressionResonanceChain
          (Sum.inr (ForwardWave.mk ())) (Sum.inr (ForwardWave.mk ())) = 1 / 7 ∧
      transform (DCDR.causalOutput DCDR.stableUnitDelayParameters unitImpulse) Complex.I =
          -(7 / 8) * Complex.I ∧
      DCDR.rationalZEliminationResponse DCDR.stableUnitDelayParameters Complex.I
          DCDR.stable_I_mem_reciprocalZResponseDomain = -(7 / 8) * Complex.I ∧
      DCDR.eliminationResponse DCDR.zChainRegressionParameters
          (DCDR.isWellPosed_of_hasNonzeroDenominator DCDR.zChainRegressionParameters
            DCDR.zChainRegression_hasNonzeroDenominator) = -(7 / 8) * Complex.I ∧
      DCDR.auditedMasonResponse DCDR.zChainRegressionParameters =
        -(7 / 8) * Complex.I ∧
      DCDR.zChainRegressionChain
          (Sum.inl (BackwardWave.mk ())) (Sum.inl (BackwardWave.mk ())) =
        (8 / 7) * Complex.I ∧
      DCDR.zChainRegressionChain
          (Sum.inr (ForwardWave.mk ())) (Sum.inr (ForwardWave.mk ())) =
        -(7 / 8) * Complex.I ∧
      (1 / 7 : ℂ) ≠ -(7 / 8) * Complex.I := by
  rcases DCDR.zChainRegression_independent_common_point with
    ⟨hCausal, hCompiled, hN5, hMason, hLeading, hLowerRight⟩
  refine ⟨AllPass.allPassZRegression_transfer_one,
    AllPass.allPassRegression_resonance_responseTransform_entry,
    AllPass.allPassMasonRegression_loopMasonThroughTransfer,
    AllPass.allPassChainRegression_resonance_chain_inl_inl,
    AllPass.allPassChainRegression_resonance_chain_inr_inr,
    hCausal, hCompiled, hN5, hMason, hLeading, hLowerRight, ?_⟩
  intro hEqual
  have hImaginary := congrArg Complex.im hEqual
  norm_num at hImaginary

/-!

## C. Joint negative sentinel

-/

/-- The joint fixture rejects the swapped DCDR reference-plane matrix while retaining both stated
leading values `7` and `(8/7)I`. -/
lemma ringDCDRX01Regression_wrongReferencePlane_rejected :
    DCDR.zChainRegressionChain ≠ DCDR.zChainRegressionWrongReferencePlaneMatrix ∧
      AllPass.allPassChainRegressionResonanceChain
          (Sum.inl (BackwardWave.mk ())) (Sum.inl (BackwardWave.mk ())) = 7 ∧
      DCDR.zChainRegressionChain
          (Sum.inl (BackwardWave.mk ())) (Sum.inl (BackwardWave.mk ())) =
        (8 / 7) * Complex.I :=
  ⟨DCDR.zChainRegression_chain_ne_wrongReferencePlaneMatrix,
    AllPass.allPassChainRegression_resonance_chain_inl_inl,
    DCDR.zChainRegression_chain_leading⟩

end

end Optics
