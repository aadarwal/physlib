/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Systems.Microring.AllPassChain
public import Physlib.Optics.Systems.Microring.AllPassRegression

/-!
# Regression tests for all-pass microring chain semantics

## i. Overview

The exact `3-4-5` resonant ring has bus transmission `1 / 7`, so its backward-first chain is
`diag(7, 1 / 7)`. Four entry checks independently expand the generic block formula and pin the
reciprocal-versus-direct diagonal placement and zero reflection terms. The generic asymmetric
two-port chain regression remains the broader left/right orientation sentinel.

A separate critical-coupling fixture has nonzero feedback denominator but zero through transfer.
Its N5 netlist is therefore well posed while the right-to-left scattering pivot is not bijective.
This mechanically proves that the internal solve gate does not imply the chain-coordinate gate.

These fixed-carrier algebraic fixtures make no reciprocity, passivity, losslessness, delay,
causality, ROC, frequency, material, source-parity, or complete X-01 claim.

## ii. Key results

- `AllPass.allPassChainRegression_resonance_chain_inl_inl` and the other three entry lemmas:
  independent expansion of the exact resonant chain.
- `AllPass.allPassChainRegression_critical_not_hasBijectiveRightToLeftTransmission`: a direct
  nonzero-kernel sentinel despite well-posed internal elimination.

## iii. Table of contents

- A. Exact resonant chain matrix
- B. Well-posed extinction without the chosen chain view

## iv. References

The fixtures are Physlib-original and source-neutral.

-/

@[expose] public section

namespace Optics

noncomputable section

namespace AllPass

/-!
## A. Exact resonant chain matrix
-/

/-- The resonant fixture satisfies the exact scalar feedback-denominator gate. -/
lemma allPassChainRegression_resonance_hasNonzeroDenominator :
    allPassRegressionResonanceParameters.HasNonzeroDenominator := by
  rw [Parameters.HasNonzeroDenominator, allPassRegression_resonance_denominator]
  norm_num

/-- The resonant through transfer is nonzero and therefore supplies the chain pivot. -/
lemma allPassChainRegression_resonance_throughTransfer_ne_zero :
    throughTransfer allPassRegressionResonanceParameters ≠ 0 := by
  rw [allPassRegression_resonance_throughTransfer]
  norm_num

/-- A constant amplitude on the singleton regression pivot family. -/
def allPassChainRegressionBackwardAmplitude (value : ℂ) :
    ModeAmplitude (BackwardWave Unit) :=
  WithLp.toLp 2 fun _ => value

/-- The exact resonant pivot is bijective, independently of the production iff theorem. -/
lemma allPassChainRegression_resonance_hasBijectiveRightToLeftTransmission :
    TwoPortScatteringTransform.HasBijectiveRightToLeftTransmission
      (packagedTwoPortScattering allPassRegressionResonanceParameters
        allPassChainRegression_resonance_hasNonzeroDenominator) := by
  constructor
  · intro first second hEqual
    apply WithLp.ofLp_injective 2
    funext index
    rcases index with ⟨⟨⟩⟩
    have hCoordinate := congrArg
      (fun amplitude : ModeAmplitude (BackwardWave Unit) =>
        amplitude (BackwardWave.mk ())) hEqual
    rw [packagedTwoPortScattering_rightToLeftTransmission_apply,
      packagedTwoPortScattering_rightToLeftTransmission_apply,
      allPassRegression_resonance_throughTransfer] at hCoordinate
    simpa using mul_left_cancel₀ (by norm_num : (1 / 7 : ℂ) ≠ 0) hCoordinate
  · intro output
    refine ⟨allPassChainRegressionBackwardAmplitude
      (7 * output (BackwardWave.mk ())), ?_⟩
    rw [packagedTwoPortScattering_rightToLeftTransmission_apply,
      allPassRegression_resonance_throughTransfer]
    apply WithLp.ofLp_injective 2
    funext index
    rcases index with ⟨⟨⟩⟩
    simp only [allPassChainRegressionBackwardAmplitude]
    ring

/-- The behavior-derived backward-first chain of the exact resonant fixture. -/
noncomputable def allPassChainRegressionResonanceChain :
    BackwardFirstChainTransform Unit Unit :=
  backwardFirstChainTransform allPassRegressionResonanceParameters
    allPassChainRegression_resonance_hasNonzeroDenominator
    allPassChainRegression_resonance_throughTransfer_ne_zero

/-- The proof-dependent resonant pivot inverse has independently derived entry `7`. -/
lemma allPassChainRegression_resonance_pivotInverse_entry :
    let scattering := packagedTwoPortScattering allPassRegressionResonanceParameters
      allPassChainRegression_resonance_hasNonzeroDenominator
    (scattering.rightToLeftTransmissionInverse
      allPassChainRegression_resonance_hasBijectiveRightToLeftTransmission)
        (BackwardWave.mk ()) (BackwardWave.mk ()) = 7 := by
  let scattering := packagedTwoPortScattering allPassRegressionResonanceParameters
    allPassChainRegression_resonance_hasNonzeroDenominator
  let hPivot := allPassChainRegression_resonance_hasBijectiveRightToLeftTransmission
  have hMatrix := scattering.inverse_mul_rightToLeftTransmission hPivot
  have hEntry := congrArg
    (fun matrix : ModeTransform (BackwardWave Unit) (BackwardWave Unit) =>
      matrix (BackwardWave.mk ()) (BackwardWave.mk ())) hMatrix
  simp only [Matrix.mul_apply] at hEntry
  rw [← BackwardWave.channelEquiv.symm.sum_comp, Fintype.sum_unique] at hEntry
  rw [packagedTwoPortScattering_rightToLeftTransmission_entry,
    allPassRegression_resonance_throughTransfer] at hEntry
  have hProduct :
      (scattering.rightToLeftTransmissionInverse hPivot)
          (BackwardWave.mk ()) (BackwardWave.mk ()) * (1 / 7 : ℂ) = 1 := by
    simpa using hEntry
  linear_combination 7 * hProduct

/-- The leading chain entry is the reciprocal transmission `7`. -/
lemma allPassChainRegression_resonance_chain_inl_inl :
    allPassChainRegressionResonanceChain
        (Sum.inl (BackwardWave.mk ())) (Sum.inl (BackwardWave.mk ())) = 7 := by
  rw [allPassChainRegressionResonanceChain, backwardFirstChainTransform,
    TwoPortScatteringTransform.toBackwardFirstChainTransform_eq_blockFormula]
  exact allPassChainRegression_resonance_pivotInverse_entry

/-- The upper-right chain entry is zero. -/
lemma allPassChainRegression_resonance_chain_inl_inr :
    allPassChainRegressionResonanceChain
        (Sum.inl (BackwardWave.mk ())) (Sum.inr (ForwardWave.mk ())) = 0 := by
  rw [allPassChainRegressionResonanceChain, backwardFirstChainTransform,
    TwoPortScatteringTransform.toBackwardFirstChainTransform_eq_blockFormula]
  simp [TwoPortScatteringTransform.backwardFirstChainBlockFormula,
    packagedTwoPortScattering_leftReflection_eq_zero]

/-- The lower-left chain entry is zero. -/
lemma allPassChainRegression_resonance_chain_inr_inl :
    allPassChainRegressionResonanceChain
        (Sum.inr (ForwardWave.mk ())) (Sum.inl (BackwardWave.mk ())) = 0 := by
  rw [allPassChainRegressionResonanceChain, backwardFirstChainTransform,
    TwoPortScatteringTransform.toBackwardFirstChainTransform_eq_blockFormula]
  simp [TwoPortScatteringTransform.backwardFirstChainBlockFormula,
    packagedTwoPortScattering_rightReflection_eq_zero]

/-- The bottom-right chain entry is the forward transmission `1 / 7`. -/
lemma allPassChainRegression_resonance_chain_inr_inr :
    allPassChainRegressionResonanceChain
        (Sum.inr (ForwardWave.mk ())) (Sum.inr (ForwardWave.mk ())) = 1 / 7 := by
  rw [allPassChainRegressionResonanceChain, backwardFirstChainTransform,
    TwoPortScatteringTransform.toBackwardFirstChainTransform_eq_blockFormula]
  simp [TwoPortScatteringTransform.backwardFirstChainBlockFormula,
    packagedTwoPortScattering_leftReflection_eq_zero,
    packagedTwoPortScattering_rightReflection_eq_zero,
    allPassRegression_resonance_throughTransfer]

/-!
## B. Well-posed extinction without the chosen chain view
-/

/-- A unitary `3-4-5` coupler whose retained field amplitude equals its through amplitude. -/
def allPassChainRegressionCriticalParameters : Parameters where
  throughAmplitude := 3 / 5
  crossAmplitude := 4 / 5
  fieldAttenuation := 3 / 5
  roundTripPhase := 0

/-- The critical fixture retains a zero-phase loop coefficient `3 / 5`. -/
lemma allPassChainRegression_critical_loopCoefficient :
    allPassChainRegressionCriticalParameters.loopCoefficient = 3 / 5 := by
  norm_num [allPassChainRegressionCriticalParameters, Parameters.loopCoefficient,
    Parameters.propagation, MatchedPropagation.transmissionCoefficient,
    MatchedPropagation.carrierPhaseFactor]

/-- The critical fixture has nonzero feedback denominator `16 / 25`. -/
lemma allPassChainRegression_critical_denominator :
    allPassChainRegressionCriticalParameters.denominator = 16 / 25 := by
  rw [Parameters.denominator, Parameters.loopGain,
    allPassChainRegression_critical_loopCoefficient]
  norm_num [allPassChainRegressionCriticalParameters]

/-- The critical fixture remains inside the exact N5 solve domain. -/
lemma allPassChainRegression_critical_hasNonzeroDenominator :
    allPassChainRegressionCriticalParameters.HasNonzeroDenominator := by
  rw [Parameters.HasNonzeroDenominator, allPassChainRegression_critical_denominator]
  norm_num

/-- The critical fixture has exact through-port extinction. -/
lemma allPassChainRegression_critical_throughTransfer :
    throughTransfer allPassChainRegressionCriticalParameters = 0 := by
  rw [throughTransfer, allPassChainRegression_critical_loopCoefficient,
    allPassChainRegression_critical_denominator]
  simp [allPassChainRegressionCriticalParameters, Parameters.coupler,
    DirectionalCoupler.crossCoefficient]
  rw [mul_pow, Complex.I_sq]
  norm_num

/-- The critical fixture's complete internal netlist is well posed. -/
lemma allPassChainRegression_critical_isWellPosed :
    (netlist allPassChainRegressionCriticalParameters).IsWellPosed :=
  isWellPosed_of_hasNonzeroDenominator allPassChainRegressionCriticalParameters
    allPassChainRegression_critical_hasNonzeroDenominator

/-- A unit singleton pivot amplitude is nonzero. -/
lemma allPassChainRegressionBackwardAmplitude_one_ne_zero :
    allPassChainRegressionBackwardAmplitude 1 ≠ 0 := by
  intro hZero
  have hCoordinate := congrArg
    (fun amplitude : ModeAmplitude (BackwardWave Unit) =>
      amplitude (BackwardWave.mk ())) hZero
  norm_num [allPassChainRegressionBackwardAmplitude] at hCoordinate

/-- The critical pivot sends a nonzero singleton amplitude to zero. -/
lemma allPassChainRegression_critical_pivot_witness_mapsToZero :
    (packagedTwoPortScattering allPassChainRegressionCriticalParameters
      allPassChainRegression_critical_hasNonzeroDenominator).rightToLeftTransmission.toLinearMap
        (allPassChainRegressionBackwardAmplitude 1) = 0 := by
  rw [packagedTwoPortScattering_rightToLeftTransmission_apply,
    allPassChainRegression_critical_throughTransfer]
  apply WithLp.ofLp_injective 2
  funext index
  rcases index with ⟨⟨⟩⟩
  simp

/-- Despite well-posed elimination, extinction prevents the chosen backward-first chain view. -/
lemma allPassChainRegression_critical_not_hasBijectiveRightToLeftTransmission :
    ¬ TwoPortScatteringTransform.HasBijectiveRightToLeftTransmission
      (packagedTwoPortScattering allPassChainRegressionCriticalParameters
        allPassChainRegression_critical_hasNonzeroDenominator) := by
  intro hBijective
  apply allPassChainRegressionBackwardAmplitude_one_ne_zero
  apply hBijective.1
  rw [allPassChainRegression_critical_pivot_witness_mapsToZero, map_zero]

end AllPass

end

end Optics
