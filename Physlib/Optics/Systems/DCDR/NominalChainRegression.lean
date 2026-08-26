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

/-!

## A. Exact scalar data and pivot

-/

/-- The fixed-carrier stable chain fixture at formal delay `q = -I`. -/
def zChainRegressionParameters : Parameters :=
  stableUnitDelayParameters.at (-Complex.I)

/-- Direct parameter expansion gives the stable forward transmission `-(7/8)I`. -/
lemma zChainRegression_forward_transfer :
    transfer zChainRegressionParameters = -(7 / 8) * Complex.I := by
  norm_num [zChainRegressionParameters, transfer, Parameters.responseNumerator,
    Parameters.denominator, Parameters.loopGain, Parameters.directGain,
    Parameters.feedbackReadoutGain, Parameters.feedbackDrive,
    UnitDelayParameters.at, stableUnitDelayParameters, poleRegressionCoupler,
    Parameters.upperCoefficient, Parameters.lowerCoefficient,
    Parameters.feedbackCoefficient, DirectionalCoupler.crossCoefficient,
    Complex.I_mul_I]
  ring

/-- Direct parameter expansion gives the independently stated reverse transmission `-(7/8)I`. -/
lemma zChainRegression_reverse_transfer :
    transfer zChainRegressionParameters.reverse = -(7 / 8) * Complex.I := by
  norm_num [zChainRegressionParameters, transfer, Parameters.responseNumerator,
    Parameters.denominator, Parameters.loopGain, Parameters.directGain,
    Parameters.feedbackReadoutGain, Parameters.feedbackDrive, Parameters.reverse,
    UnitDelayParameters.at, stableUnitDelayParameters, poleRegressionCoupler,
    Parameters.upperCoefficient, Parameters.lowerCoefficient,
    Parameters.feedbackCoefficient, DirectionalCoupler.crossCoefficient,
    Complex.I_mul_I]
  ring

/-- The stable fixed-carrier N5 denominator gate, restated at the chain fixture. -/
lemma zChainRegression_hasNonzeroDenominator :
    zChainRegressionParameters.HasNonzeroDenominator := by
  simpa [zChainRegressionParameters] using zRegression_stable_fixed_hasNonzeroDenominator_I

/-- The independently expanded nominal right-to-left transmission is nonzero. -/
lemma zChainRegression_reverse_transfer_ne_zero :
    transfer zChainRegressionParameters.reverse ≠ 0 := by
  rw [zChainRegression_reverse_transfer]
  intro hZero
  have hImaginary := congrArg Complex.im hZero
  norm_num at hImaginary

/-- A constant amplitude on the singleton regression backward-wave family. -/
def zChainRegressionBackwardAmplitude (value : ℂ) :
    ModeAmplitude (BackwardWave Unit) :=
  WithLp.toLp 2 fun _ => value

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
    have hCoordinate := congrArg
      (fun amplitude : ModeAmplitude (BackwardWave Unit) =>
        amplitude (BackwardWave.mk ())) hEqual
    rw [packagedNominalTwoPortScattering_rightToLeftTransmission_apply,
      packagedNominalTwoPortScattering_rightToLeftTransmission_apply,
      zChainRegression_reverse_transfer] at hCoordinate
    simpa using mul_left_cancel₀
      (by exact zChainRegression_reverse_transfer_ne_zero) hCoordinate
  · intro output
    refine ⟨zChainRegressionBackwardAmplitude
      ((8 / 7) * Complex.I * output (BackwardWave.mk ())), ?_⟩
    rw [packagedNominalTwoPortScattering_rightToLeftTransmission_apply,
      zChainRegression_reverse_transfer]
    apply WithLp.ofLp_injective 2
    funext index
    rcases index with ⟨⟨⟩⟩
    simp only [zChainRegressionBackwardAmplitude]
    have hProduct : (-(7 / 8) * Complex.I) * ((8 / 7) * Complex.I) = (1 : ℂ) := by
      norm_num [Complex.I_mul_I]
      ring
    rw [mul_assoc, hProduct, one_mul]

/-!

## B. Independent backward-first chain entries

-/

/-- The behavior-derived chain at the exact nonzero-loop fixture. -/
noncomputable def zChainRegressionChain : BackwardFirstChainTransform Unit Unit :=
  nominalBackwardFirstChainTransform zChainRegressionParameters
    zChainRegression_hasNonzeroDenominator zChainRegression_reverse_transfer_ne_zero

/-- The proof-dependent inverse pivot is `(8/7)I`, derived from the inverse product law. -/
lemma zChainRegression_pivotInverse_entry :
    let scattering := packagedNominalTwoPortScattering zChainRegressionParameters
      zChainRegression_hasNonzeroDenominator
    let hPivot := packagedNominalTwoPortScattering_hasBijectiveRightToLeftTransmission
      zChainRegressionParameters zChainRegression_hasNonzeroDenominator
        zChainRegression_reverse_transfer_ne_zero
    (scattering.rightToLeftTransmissionInverse hPivot)
        (BackwardWave.mk ()) (BackwardWave.mk ()) = (8 / 7) * Complex.I := by
  let scattering := packagedNominalTwoPortScattering zChainRegressionParameters
    zChainRegression_hasNonzeroDenominator
  let hPivot := packagedNominalTwoPortScattering_hasBijectiveRightToLeftTransmission
    zChainRegressionParameters zChainRegression_hasNonzeroDenominator
      zChainRegression_reverse_transfer_ne_zero
  have hMatrix := scattering.inverse_mul_rightToLeftTransmission hPivot
  have hEntry := congrArg
    (fun matrix : ModeTransform (BackwardWave Unit) (BackwardWave Unit) =>
      matrix (BackwardWave.mk ()) (BackwardWave.mk ())) hMatrix
  have hInverseProduct :
      (scattering.rightToLeftTransmissionInverse hPivot)
          (BackwardWave.mk ()) (BackwardWave.mk ()) * (-(7 / 8) * Complex.I) = 1 := by
    simp only [Matrix.mul_apply] at hEntry
    rw [← BackwardWave.channelEquiv.symm.sum_comp, Fintype.sum_unique] at hEntry
    rw [packagedNominalTwoPortScattering_rightToLeftTransmission_entry,
      zChainRegression_reverse_transfer] at hEntry
    simpa [scattering] using hEntry
  have hScalarProduct :
      (-(7 / 8) * Complex.I) * ((8 / 7) * Complex.I) = (1 : ℂ) := by
    norm_num [Complex.I_mul_I]
    ring
  calc
    _ = _ * 1 := by rw [mul_one]
    _ = _ * ((-(7 / 8) * Complex.I) * ((8 / 7) * Complex.I)) := by
      rw [hScalarProduct]
    _ = (_ * (-(7 / 8) * Complex.I)) * ((8 / 7) * Complex.I) := by ring
    _ = (8 / 7) * Complex.I := by rw [hInverseProduct, one_mul]

/-- The leading backward-first chain entry is the inverse pivot `(8/7)I`. -/
lemma zChainRegression_chain_leading :
    zChainRegressionChain
        (Sum.inl (BackwardWave.mk ())) (Sum.inl (BackwardWave.mk ())) =
      (8 / 7) * Complex.I := by
  rw [zChainRegressionChain, nominalBackwardFirstChainTransform,
    TwoPortScatteringTransform.toBackwardFirstChainTransform_eq_blockFormula]
  exact zChainRegression_pivotInverse_entry

/-- The upper-right backward-first chain entry is zero. -/
lemma zChainRegression_chain_upperRight :
    zChainRegressionChain
        (Sum.inl (BackwardWave.mk ())) (Sum.inr (ForwardWave.mk ())) = 0 := by
  rw [zChainRegressionChain, nominalBackwardFirstChainTransform,
    TwoPortScatteringTransform.toBackwardFirstChainTransform_eq_blockFormula]
  simp [TwoPortScatteringTransform.backwardFirstChainBlockFormula,
    packagedNominalTwoPortScattering_leftReflection_eq_zero]

/-- The lower-left backward-first chain entry is zero. -/
lemma zChainRegression_chain_lowerLeft :
    zChainRegressionChain
        (Sum.inr (ForwardWave.mk ())) (Sum.inl (BackwardWave.mk ())) = 0 := by
  rw [zChainRegressionChain, nominalBackwardFirstChainTransform,
    TwoPortScatteringTransform.toBackwardFirstChainTransform_eq_blockFormula]
  simp [TwoPortScatteringTransform.backwardFirstChainBlockFormula,
    packagedNominalTwoPortScattering_rightReflection_eq_zero]

/-- The bottom-right backward-first chain entry is the forward response `-(7/8)I`. -/
lemma zChainRegression_chain_lowerRight :
    zChainRegressionChain
        (Sum.inr (ForwardWave.mk ())) (Sum.inr (ForwardWave.mk ())) =
      -(7 / 8) * Complex.I := by
  rw [zChainRegressionChain, nominalBackwardFirstChainTransform,
    TwoPortScatteringTransform.toBackwardFirstChainTransform_eq_blockFormula]
  simp [TwoPortScatteringTransform.backwardFirstChainBlockFormula,
    packagedNominalTwoPortScattering_leftReflection_eq_zero,
    packagedNominalTwoPortScattering_rightReflection_eq_zero,
    packagedNominalTwoPortScattering_leftToRightTransmission_entry,
    zChainRegression_forward_transfer]

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

/-- The production DCDR X-01 agreement is inhabited at the stable nonreal fixture. -/
lemma zChainRegression_crossSemanticsAgreement :
    ZChainCrossSemanticsAgreement stableUnitDelayParameters stableResponseReduction Complex.I
      zChainRegression_crossSemanticsDomain :=
  zChainCrossSemantics_agree stableUnitDelayParameters stableResponseReduction Complex.I
    zChainRegression_crossSemanticsDomain

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
