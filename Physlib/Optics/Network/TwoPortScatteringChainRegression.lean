/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.TwoPortScatteringChain

/-!
# Regression tests for two-port scattering-to-chain conversion

## i. Overview

A scalar scattering matrix has a bijective right-to-left transmission block while its full
scattering transform has a nonzero kernel. The derived chain matrix is checked entrywise and fixes
the pivot, signs, state order, and all four block placements. A two-mode fixture then distinguishes
the noncommuting product `Rr * Rl` from its reversal. Zero scattering supplies the exact negative
chain-view case.

## ii. Key results

## iii. Table of contents

- A. Singular full scattering with a bijective pivot
- B. Exact derived chain matrix
- C. Noncommuting block order
- D. Zero-pivot negative case

## iv. References

These are algebraic fixed-frequency orientation sentinels. Their coefficients make no
losslessness, passivity, reciprocity, causality, or physical-realization claim.

-/

@[expose] public section

namespace Optics

noncomputable section

/-!

## A. Singular full scattering with a bijective pivot

-/

/-- A constant scalar amplitude on an arbitrary regression mode family. -/
def twoPortScatteringChainRegressionAmplitude {ι : Type*} (value : ℂ) : ModeAmplitude ι :=
  WithLp.toLp 2 fun _ => value

/-- A raw scalar scattering matrix with blocks `[[2, I], [-6 I, 3]]`.

Its right-to-left transmission block is multiplication by `I`, while the complete matrix is
singular. -/
def twoPortScatteringChainRegressionRaw : ScatteringMatrix (Unit ⊕ Unit) where
  toModeTransform
    | Sum.inl _, Sum.inl _ => 2
    | Sum.inl _, Sum.inr _ => Complex.I
    | Sum.inr _, Sum.inl _ => -6 * Complex.I
    | Sum.inr _, Sum.inr _ => 3

/-- The typed two-port presentation of the singular raw scattering fixture. -/
def twoPortScatteringChainRegressionScattering : TwoPortScatteringTransform Unit Unit :=
  twoPortScatteringChainRegressionRaw.toTwoPortScatteringTransform

/-- The typed scattering transform retains the raw left-reflection entry. -/
@[simp]
lemma twoPortScatteringChainRegression_scattering_inl_inl (output input : Unit) :
    twoPortScatteringChainRegressionScattering
      (Sum.inl (Outgoing.mk output)) (Sum.inl (Incident.mk input)) = 2 := by
  cases output
  cases input
  simp [twoPortScatteringChainRegressionScattering, twoPortScatteringChainRegressionRaw]

/-- The typed scattering transform retains the raw right-to-left transmission entry. -/
@[simp]
lemma twoPortScatteringChainRegression_scattering_inl_inr (output input : Unit) :
    twoPortScatteringChainRegressionScattering
      (Sum.inl (Outgoing.mk output)) (Sum.inr (Incident.mk input)) = Complex.I := by
  cases output
  cases input
  simp [twoPortScatteringChainRegressionScattering, twoPortScatteringChainRegressionRaw]

/-- The typed scattering transform retains the raw left-to-right transmission entry. -/
@[simp]
lemma twoPortScatteringChainRegression_scattering_inr_inl (output input : Unit) :
    twoPortScatteringChainRegressionScattering
      (Sum.inr (Outgoing.mk output)) (Sum.inl (Incident.mk input)) = -6 * Complex.I := by
  cases output
  cases input
  simp [twoPortScatteringChainRegressionScattering, twoPortScatteringChainRegressionRaw]

/-- The typed scattering transform retains the raw right-reflection entry. -/
@[simp]
lemma twoPortScatteringChainRegression_scattering_inr_inr (output input : Unit) :
    twoPortScatteringChainRegressionScattering
      (Sum.inr (Outgoing.mk output)) (Sum.inr (Incident.mk input)) = 3 := by
  cases output
  cases input
  simp [twoPortScatteringChainRegressionScattering, twoPortScatteringChainRegressionRaw]

/-- The left-reflection block has scalar entry two. -/
lemma twoPortScatteringChainRegression_leftReflection_entry :
    twoPortScatteringChainRegressionScattering.leftReflection
      (BackwardWave.mk ()) (ForwardWave.mk ()) = 2 := by
  simp [twoPortScatteringChainRegressionScattering, twoPortScatteringChainRegressionRaw]

/-- The right-to-left transmission block has scalar entry `I`. -/
lemma twoPortScatteringChainRegression_rightToLeftTransmission_entry :
    twoPortScatteringChainRegressionScattering.rightToLeftTransmission
      (BackwardWave.mk ()) (BackwardWave.mk ()) = Complex.I := by
  simp [twoPortScatteringChainRegressionScattering, twoPortScatteringChainRegressionRaw]

/-- The left-to-right transmission block has scalar entry `-6 I`. -/
lemma twoPortScatteringChainRegression_leftToRightTransmission_entry :
    twoPortScatteringChainRegressionScattering.leftToRightTransmission
      (ForwardWave.mk ()) (ForwardWave.mk ()) = -6 * Complex.I := by
  simp [twoPortScatteringChainRegressionScattering, twoPortScatteringChainRegressionRaw]

/-- The right-reflection block has scalar entry three. -/
lemma twoPortScatteringChainRegression_rightReflection_entry :
    twoPortScatteringChainRegressionScattering.rightReflection
      (ForwardWave.mk ()) (BackwardWave.mk ()) = 3 := by
  simp [twoPortScatteringChainRegressionScattering, twoPortScatteringChainRegressionRaw]

/-- The fixture's right-to-left transmission block acts by multiplication by `I`. -/
lemma twoPortScatteringChainRegression_rightToLeftTransmission_action
    (amplitude : ModeAmplitude (BackwardWave Unit)) :
    twoPortScatteringChainRegressionScattering.rightToLeftTransmission.toLinearMap amplitude =
      twoPortScatteringChainRegressionAmplitude
        (Complex.I * amplitude (BackwardWave.mk ())) := by
  apply WithLp.ofLp_injective 2
  funext index
  rcases index with ⟨⟨⟩⟩
  simp only [ModeTransform.toLinearMap, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    twoPortScatteringChainRegressionAmplitude]
  rw [← BackwardWave.channelEquiv.symm.sum_comp]
  simp

/-- The right-to-left transmission block is bijective despite singularity of the full scattering
transform. -/
lemma twoPortScatteringChainRegression_hasBijectiveRightToLeftTransmission :
    twoPortScatteringChainRegressionScattering.HasBijectiveRightToLeftTransmission := by
  constructor
  · intro first second hEqual
    apply WithLp.ofLp_injective 2
    funext index
    rcases index with ⟨⟨⟩⟩
    have hCoordinate := congrArg
      (fun amplitude : ModeAmplitude (BackwardWave Unit) =>
        amplitude (BackwardWave.mk ())) hEqual
    rw [twoPortScatteringChainRegression_rightToLeftTransmission_action,
      twoPortScatteringChainRegression_rightToLeftTransmission_action] at hCoordinate
    exact mul_left_cancel₀ Complex.I_ne_zero hCoordinate
  · intro output
    refine ⟨twoPortScatteringChainRegressionAmplitude
      (-Complex.I * output (BackwardWave.mk ())), ?_⟩
    rw [twoPortScatteringChainRegression_rightToLeftTransmission_action]
    apply WithLp.ofLp_injective 2
    funext index
    rcases index with ⟨⟨⟩⟩
    change Complex.I * (-Complex.I * output (BackwardWave.mk ())) =
      output (BackwardWave.mk ())
    calc
      Complex.I * (-Complex.I * output (BackwardWave.mk ())) =
          -(Complex.I * Complex.I) * output (BackwardWave.mk ()) := by ring
      _ = output (BackwardWave.mk ()) := by rw [← pow_two, Complex.I_sq]; ring

/-- A nonzero incident vector in the kernel of the complete scattering transform. -/
def twoPortScatteringChainRegressionKernelInput :
    ModeAmplitude (Incident Unit ⊕ Incident Unit) :=
  (twoPortScatteringChainRegressionAmplitude 1 : ModeAmplitude (Incident Unit)).directSum
    (twoPortScatteringChainRegressionAmplitude (2 * Complex.I) :
      ModeAmplitude (Incident Unit))

/-- The full scattering transform sends the kernel sentinel to zero. -/
lemma twoPortScatteringChainRegression_kernel_action :
    twoPortScatteringChainRegressionScattering.toLinearMap
      twoPortScatteringChainRegressionKernelInput = 0 := by
  apply WithLp.ofLp_injective 2
  funext index
  rcases index with ⟨⟨⟩⟩ | ⟨⟨⟩⟩
  · simp only [ModeTransform.toLinearMap, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
      Fintype.sum_sum_type]
    rw [← Incident.channelEquiv.symm.sum_comp, ← Incident.channelEquiv.symm.sum_comp]
    simp [twoPortScatteringChainRegressionKernelInput,
      twoPortScatteringChainRegressionAmplitude]
    calc
      (2 : ℂ) + Complex.I * (2 * Complex.I) =
          2 + 2 * (Complex.I * Complex.I) := by ring
      _ = 0 := by rw [Complex.I_mul_I]; ring
  · simp only [ModeTransform.toLinearMap, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
      Fintype.sum_sum_type]
    rw [← Incident.channelEquiv.symm.sum_comp, ← Incident.channelEquiv.symm.sum_comp]
    simp [twoPortScatteringChainRegressionKernelInput,
      twoPortScatteringChainRegressionAmplitude]
    ring

/-- The kernel sentinel is nonzero. -/
lemma twoPortScatteringChainRegressionKernelInput_ne_zero :
    twoPortScatteringChainRegressionKernelInput ≠ 0 := by
  intro hZero
  have hCoordinate := congrArg
    (fun amplitude : ModeAmplitude (Incident Unit ⊕ Incident Unit) =>
      amplitude (Sum.inl (Incident.mk ()))) hZero
  norm_num [twoPortScatteringChainRegressionKernelInput,
    twoPortScatteringChainRegressionAmplitude] at hCoordinate

/-- Bijectivity of the pivot does not imply injectivity of the full scattering transform. -/
lemma twoPortScatteringChainRegression_fullScattering_not_injective :
    ¬Function.Injective twoPortScatteringChainRegressionScattering.toLinearMap := by
  intro hInjective
  apply twoPortScatteringChainRegressionKernelInput_ne_zero
  apply hInjective
  rw [twoPortScatteringChainRegression_kernel_action, map_zero]

/-!

## B. Exact derived chain matrix

-/

/-- The explicit inverse of the fixture's `I` transmission block. -/
def twoPortScatteringChainRegressionTransmissionInverse :
    ModeTransform (BackwardWave Unit) (BackwardWave Unit) :=
  fun _ _ => -Complex.I

/-- The explicit inverse is a right inverse of the fixture's transmission block. -/
lemma twoPortScatteringChainRegression_transmission_mul_explicitInverse :
    twoPortScatteringChainRegressionScattering.rightToLeftTransmission *
      twoPortScatteringChainRegressionTransmissionInverse = 1 := by
  ext ⟨⟨⟩⟩ ⟨⟨⟩⟩
  rw [Matrix.mul_apply, ← BackwardWave.channelEquiv.symm.sum_comp]
  simp [twoPortScatteringChainRegressionTransmissionInverse]

/-- The proof-selected inverse matrix equals the explicit scalar inverse `-I`. -/
lemma twoPortScatteringChainRegression_transmissionInverse_eq :
    twoPortScatteringChainRegressionScattering.rightToLeftTransmissionInverse
        twoPortScatteringChainRegression_hasBijectiveRightToLeftTransmission =
      twoPortScatteringChainRegressionTransmissionInverse := by
  let inverse :=
    twoPortScatteringChainRegressionScattering.rightToLeftTransmissionInverse
      twoPortScatteringChainRegression_hasBijectiveRightToLeftTransmission
  calc
    inverse = inverse * 1 := (Matrix.mul_one inverse).symm
    _ = inverse *
        (twoPortScatteringChainRegressionScattering.rightToLeftTransmission *
          twoPortScatteringChainRegressionTransmissionInverse) := by
      rw [twoPortScatteringChainRegression_transmission_mul_explicitInverse]
    _ = (inverse *
          twoPortScatteringChainRegressionScattering.rightToLeftTransmission) *
        twoPortScatteringChainRegressionTransmissionInverse := (Matrix.mul_assoc _ _ _).symm
    _ = twoPortScatteringChainRegressionTransmissionInverse := by
      rw [TwoPortScatteringTransform.inverse_mul_rightToLeftTransmission,
        Matrix.one_mul]

/-- The exact expected backward-first chain matrix `[[−I, 2I], [−3I, 0]]`. -/
def twoPortScatteringChainRegressionExpectedChain :
    ModeTransform (BackwardWave Unit ⊕ ForwardWave Unit)
      (BackwardWave Unit ⊕ ForwardWave Unit)
  | Sum.inl _, Sum.inl _ => -Complex.I
  | Sum.inl _, Sum.inr _ => 2 * Complex.I
  | Sum.inr _, Sum.inl _ => -3 * Complex.I
  | Sum.inr _, Sum.inr _ => 0

/-- The behavior-derived chain transform is exactly the expected singular-scattering conversion. -/
lemma twoPortScatteringChainRegression_chainTransform :
    twoPortScatteringChainRegressionScattering.toBackwardFirstChainTransform
        twoPortScatteringChainRegression_hasBijectiveRightToLeftTransmission =
      twoPortScatteringChainRegressionExpectedChain := by
  rw [TwoPortScatteringTransform.toBackwardFirstChainTransform_eq_blockFormula]
  unfold TwoPortScatteringTransform.backwardFirstChainBlockFormula
  rw [twoPortScatteringChainRegression_transmissionInverse_eq]
  ext (output | output) (input | input) <;>
    rcases output with ⟨⟨⟩⟩ <;>
    rcases input with ⟨⟨⟩⟩ <;>
    simp [Matrix.mul_apply,
      twoPortScatteringChainRegressionTransmissionInverse,
      twoPortScatteringChainRegressionExpectedChain,
      ← BackwardWave.channelEquiv.symm.sum_comp] <;>
    ring

/-!

## C. Noncommuting block order

-/

/-- The two-mode left-reflection shear before direction-wrapper relabeling. -/
def twoPortScatteringChainRegressionLeftReflectionRaw :
    ModeTransform (Fin 2) (Fin 2) :=
  !![(1 : ℂ), 2; 0, 1]

/-- The direction-typed two-mode left-reflection shear. -/
def twoPortScatteringChainRegressionLeftReflection :
    ModeTransform (ForwardWave (Fin 2)) (BackwardWave (Fin 2)) :=
  twoPortScatteringChainRegressionLeftReflectionRaw.reindex
    ForwardWave.channelEquiv.symm BackwardWave.channelEquiv.symm

/-- The two-mode right-reflection shear before direction-wrapper relabeling. -/
def twoPortScatteringChainRegressionRightReflectionRaw :
    ModeTransform (Fin 2) (Fin 2) :=
  !![(1 : ℂ), 0; 3, 1]

/-- The direction-typed two-mode right-reflection shear. -/
def twoPortScatteringChainRegressionRightReflection :
    ModeTransform (BackwardWave (Fin 2)) (ForwardWave (Fin 2)) :=
  twoPortScatteringChainRegressionRightReflectionRaw.reindex
    BackwardWave.channelEquiv.symm ForwardWave.channelEquiv.symm

/-- A direction-typed scattering transform with identity pivot, zero forward transmission, and
noncommuting reflection shears. -/
def twoPortScatteringChainRegressionNoncommutingDirectional :
    ModeTransform (ForwardWave (Fin 2) ⊕ BackwardWave (Fin 2))
      (BackwardWave (Fin 2) ⊕ ForwardWave (Fin 2)) :=
  Matrix.fromBlocks twoPortScatteringChainRegressionLeftReflection 1 0
    twoPortScatteringChainRegressionRightReflection

/-- The noncommuting directional fixture relabeled as a typed two-port scattering transform. -/
def twoPortScatteringChainRegressionNoncommuting :
    TwoPortScatteringTransform (Fin 2) (Fin 2) :=
  twoPortScatteringChainRegressionNoncommutingDirectional.reindex
    TwoPortScatteringTransform.incidentTravellingWaveEquiv.symm
    TwoPortScatteringTransform.outgoingTravellingWaveEquiv.symm

/-- Returning the noncommuting fixture to travelling-wave coordinates recovers its four blocks. -/
lemma twoPortScatteringChainRegressionNoncommuting_toTravellingWaveCoordinates :
    twoPortScatteringChainRegressionNoncommuting.toTravellingWaveCoordinates =
      twoPortScatteringChainRegressionNoncommutingDirectional := by
  exact ModeTransform.reindex_reindex_symm
    TwoPortScatteringTransform.incidentTravellingWaveEquiv
    TwoPortScatteringTransform.outgoingTravellingWaveEquiv
    twoPortScatteringChainRegressionNoncommutingDirectional

/-- The noncommuting fixture has the declared left-reflection block. -/
lemma twoPortScatteringChainRegressionNoncommuting_leftReflection :
    twoPortScatteringChainRegressionNoncommuting.leftReflection =
      twoPortScatteringChainRegressionLeftReflection := by
  rw [TwoPortScatteringTransform.leftReflection,
    twoPortScatteringChainRegressionNoncommuting_toTravellingWaveCoordinates]
  exact Matrix.toBlocks_fromBlocks₁₁ _ _ _ _

/-- The noncommuting fixture has identity right-to-left transmission. -/
lemma twoPortScatteringChainRegressionNoncommuting_rightToLeftTransmission :
    twoPortScatteringChainRegressionNoncommuting.rightToLeftTransmission = 1 := by
  rw [TwoPortScatteringTransform.rightToLeftTransmission,
    twoPortScatteringChainRegressionNoncommuting_toTravellingWaveCoordinates]
  exact Matrix.toBlocks_fromBlocks₁₂ _ _ _ _

/-- The noncommuting fixture has zero left-to-right transmission. -/
lemma twoPortScatteringChainRegressionNoncommuting_leftToRightTransmission :
    twoPortScatteringChainRegressionNoncommuting.leftToRightTransmission = 0 := by
  rw [TwoPortScatteringTransform.leftToRightTransmission,
    twoPortScatteringChainRegressionNoncommuting_toTravellingWaveCoordinates]
  exact Matrix.toBlocks_fromBlocks₂₁ _ _ _ _

/-- The noncommuting fixture has the declared right-reflection block. -/
lemma twoPortScatteringChainRegressionNoncommuting_rightReflection :
    twoPortScatteringChainRegressionNoncommuting.rightReflection =
      twoPortScatteringChainRegressionRightReflection := by
  rw [TwoPortScatteringTransform.rightReflection,
    twoPortScatteringChainRegressionNoncommuting_toTravellingWaveCoordinates]
  exact Matrix.toBlocks_fromBlocks₂₂ _ _ _ _

/-- The identity pivot of the noncommuting fixture is bijective. -/
lemma twoPortScatteringChainRegressionNoncommuting_hasBijectiveRightToLeftTransmission :
    twoPortScatteringChainRegressionNoncommuting.HasBijectiveRightToLeftTransmission := by
  rw [TwoPortScatteringTransform.HasBijectiveRightToLeftTransmission,
    twoPortScatteringChainRegressionNoncommuting_rightToLeftTransmission]
  constructor
  · intro first second hEqual
    simpa only [ModeTransform.toLinearMap, Matrix.toLpLin_one,
      LinearMap.id_apply] using hEqual
  · intro amplitude
    exact ⟨amplitude, by
      simp only [ModeTransform.toLinearMap, Matrix.toLpLin_one,
        LinearMap.id_apply]⟩

/-- The proof-selected inverse of the identity pivot is itself the identity matrix. -/
lemma twoPortScatteringChainRegressionNoncommuting_transmissionInverse :
    twoPortScatteringChainRegressionNoncommuting.rightToLeftTransmissionInverse
        twoPortScatteringChainRegressionNoncommuting_hasBijectiveRightToLeftTransmission = 1 := by
  have hInverse := TwoPortScatteringTransform.inverse_mul_rightToLeftTransmission
    twoPortScatteringChainRegressionNoncommuting
    twoPortScatteringChainRegressionNoncommuting_hasBijectiveRightToLeftTransmission
  rw [twoPortScatteringChainRegressionNoncommuting_rightToLeftTransmission,
    Matrix.mul_one] at hInverse
  exact hInverse

/-- The lower-right chain block uses `-Rr * Rl`: its lower-right entry is `-7`. -/
lemma twoPortScatteringChainRegressionNoncommuting_chain_lowerRight :
    (twoPortScatteringChainRegressionNoncommuting.toBackwardFirstChainTransform
      twoPortScatteringChainRegressionNoncommuting_hasBijectiveRightToLeftTransmission)
        (Sum.inr (ForwardWave.mk 1)) (Sum.inr (ForwardWave.mk 1)) = -7 := by
  rw [TwoPortScatteringTransform.toBackwardFirstChainTransform_eq_blockFormula]
  unfold TwoPortScatteringTransform.backwardFirstChainBlockFormula
  rw [twoPortScatteringChainRegressionNoncommuting_transmissionInverse]
  simp only [Matrix.fromBlocks_apply₂₂, Matrix.one_mul, Matrix.mul_one,
    twoPortScatteringChainRegressionNoncommuting_leftToRightTransmission,
    twoPortScatteringChainRegressionNoncommuting_leftReflection,
    twoPortScatteringChainRegressionNoncommuting_rightReflection,
    zero_sub, Matrix.neg_apply, Matrix.mul_apply]
  rw [← BackwardWave.channelEquiv.symm.sum_comp]
  norm_num [twoPortScatteringChainRegressionLeftReflection,
    twoPortScatteringChainRegressionLeftReflectionRaw,
    twoPortScatteringChainRegressionRightReflection,
    twoPortScatteringChainRegressionRightReflectionRaw]

/-- Reversing the two reflection blocks gives lower-right entry `-1`, not the chain result. -/
lemma twoPortScatteringChainRegressionNoncommuting_reverse_lowerRight :
    (-(twoPortScatteringChainRegressionLeftReflection *
      twoPortScatteringChainRegressionRightReflection))
        (BackwardWave.mk 1) (BackwardWave.mk 1) = -1 := by
  simp only [Matrix.neg_apply, Matrix.mul_apply]
  rw [← ForwardWave.channelEquiv.symm.sum_comp]
  norm_num [twoPortScatteringChainRegressionLeftReflection,
    twoPortScatteringChainRegressionLeftReflectionRaw,
    twoPortScatteringChainRegressionRightReflection,
    twoPortScatteringChainRegressionRightReflectionRaw]

/-- The exact lower-right chain block is not the reversed reflection product. -/
lemma twoPortScatteringChainRegressionNoncommuting_chain_ne_reverseProduct :
    (twoPortScatteringChainRegressionNoncommuting.toBackwardFirstChainTransform
      twoPortScatteringChainRegressionNoncommuting_hasBijectiveRightToLeftTransmission)
        (Sum.inr (ForwardWave.mk 1)) (Sum.inr (ForwardWave.mk 1)) ≠
      (-(twoPortScatteringChainRegressionLeftReflection *
        twoPortScatteringChainRegressionRightReflection))
          (BackwardWave.mk 1) (BackwardWave.mk 1) := by
  rw [twoPortScatteringChainRegressionNoncommuting_chain_lowerRight,
    twoPortScatteringChainRegressionNoncommuting_reverse_lowerRight]
  norm_num

/-!

## D. Zero-pivot negative case

-/

/-- The zero typed two-port scattering transform. -/
def twoPortScatteringChainRegressionZero : TwoPortScatteringTransform Unit Unit := 0

/-- The zero scattering transform has the zero right-to-left transmission block. -/
lemma twoPortScatteringChainRegressionZero_rightToLeftTransmission :
    twoPortScatteringChainRegressionZero.rightToLeftTransmission = 0 := by
  rfl

/-- The zero transform's right-to-left transmission block is not surjective. -/
lemma twoPortScatteringChainRegressionZero_not_hasBijectiveRightToLeftTransmission :
    ¬twoPortScatteringChainRegressionZero.HasBijectiveRightToLeftTransmission := by
  intro hBijective
  let nonzero :=
    (twoPortScatteringChainRegressionAmplitude 1 : ModeAmplitude (BackwardWave Unit))
  rcases hBijective.2 nonzero with ⟨input, hInput⟩
  rw [twoPortScatteringChainRegressionZero_rightToLeftTransmission] at hInput
  have hCoordinate := congrArg
    (fun amplitude : ModeAmplitude (BackwardWave Unit) =>
      amplitude (BackwardWave.mk ())) hInput
  simp only [ModeTransform.toLinearMap, Matrix.toLpLin_apply, Matrix.mulVec,
    dotProduct] at hCoordinate
  rw [← BackwardWave.channelEquiv.symm.sum_comp] at hCoordinate
  simp only [Matrix.zero_apply, zero_mul, Finset.sum_const_zero] at hCoordinate
  change (0 : ℂ) = nonzero (BackwardWave.mk ()) at hCoordinate
  change (0 : ℂ) = 1 at hCoordinate
  norm_num at hCoordinate

/-- The zero scattering graph has no backward-first left-to-right chain view by the exact pivot
criterion. -/
lemma twoPortScatteringChainRegressionZero_not_hasChainView :
    ¬twoPortScatteringChainRegressionZero.toBackwardFirstBehavior.HasLeftToRightChainView := by
  rw [TwoPortScatteringTransform.hasLeftToRightChainView_iff_rightToLeftTransmission_bijective]
  exact twoPortScatteringChainRegressionZero_not_hasBijectiveRightToLeftTransmission

end

end Optics
