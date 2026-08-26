/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.TwoPortChainScattering
public import Physlib.Optics.Systems.Microring.AllPassTwoPort

/-!
# Backward-first chain semantics of the all-pass microring

## i. Overview

The complete typed all-pass scattering law has zero reflection and the same totalized bus
transmission `throughTransfer` in both directions. This file proves that its right-to-left pivot is
bijective exactly when that scalar is nonzero. Under this pivot gate and the independent N5 solve
gate, the behavior-derived backward-first chain matrix is
`diag((throughTransfer p)⁻¹, throughTransfer p)`.

The two gates are intentionally separate. `Parameters.HasNonzeroDenominator` makes the internal
netlist response functional; `throughTransfer p ≠ 0` makes the chosen scattering-to-chain
coordinate solve possible. Neither is presented as a consequence of the other.

The endpoint wrappers and backward-first ordering are nominal travelling-wave coordinates. No
physical time reversal, reciprocity, passivity, losslessness, causality, delay, ROC, dispersion,
group-delay, material, source-parity, add-drop, DCDR, or complete X-01 claim is made here.

## ii. Key results

- `AllPass.packagedTwoPortScattering_hasBijectiveRightToLeftTransmission_iff`: the exact
  pivot gate.
- `AllPass.backwardFirstChainMatrix`: the explicit totalized diagonal chain matrix.
- `AllPass.backwardFirstChainTransform_eq_matrix`: the behavior-derived chain equals that matrix.
- `AllPass.toBehavior_backwardFirstChainTransform`: agreement with the singular-safe N5 relation.
- `AllPass.backwardFirstChainTransform_roundTrip`: exact reconstruction of the typed
  scattering law.

## iii. Table of contents

- A. Scalar pivot
- B. Explicit backward-first chain matrix
- C. Behavioral agreement and round trip

## iv. References

This chain realization is Physlib-original. Its conversion convention is the one registered in
`TwoPortScatteringChain.lean` and `TwoPortChainScattering.lean`.

-/

@[expose] public section

namespace Optics

noncomputable section

namespace AllPass

/-!
## A. Scalar pivot
-/

/-- A constant amplitude on the singleton backward-wave family. -/
private def backwardAmplitude (value : ℂ) : ModeAmplitude (BackwardWave Unit) :=
  WithLp.toLp 2 fun _ => value

/-- The packaged right-to-left pivot has the all-pass scalar entry. -/
lemma packagedTwoPortScattering_rightToLeftTransmission_entry (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) :
    (packagedTwoPortScattering p hDenominator).rightToLeftTransmission
        (BackwardWave.mk ()) (BackwardWave.mk ()) = throughTransfer p := by
  rw [TwoPortScatteringTransform.rightToLeftTransmission_apply,
    packagedTwoPortScattering_eq_twoPortScatteringTransform]
  rfl

/-- The packaged left reflection has its declared zero entry. -/
lemma packagedTwoPortScattering_leftReflection_entry (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) :
    (packagedTwoPortScattering p hDenominator).leftReflection
        (BackwardWave.mk ()) (ForwardWave.mk ()) = 0 := by
  rw [TwoPortScatteringTransform.leftReflection_apply,
    packagedTwoPortScattering_eq_twoPortScatteringTransform]
  rfl

/-- The packaged left-to-right transmission has the all-pass scalar entry. -/
lemma packagedTwoPortScattering_leftToRightTransmission_entry (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) :
    (packagedTwoPortScattering p hDenominator).leftToRightTransmission
        (ForwardWave.mk ()) (ForwardWave.mk ()) = throughTransfer p := by
  rw [TwoPortScatteringTransform.leftToRightTransmission_apply,
    packagedTwoPortScattering_eq_twoPortScatteringTransform]
  rfl

/-- The packaged right reflection has its declared zero entry. -/
lemma packagedTwoPortScattering_rightReflection_entry (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) :
    (packagedTwoPortScattering p hDenominator).rightReflection
        (ForwardWave.mk ()) (BackwardWave.mk ()) = 0 := by
  rw [TwoPortScatteringTransform.rightReflection_apply,
    packagedTwoPortScattering_eq_twoPortScatteringTransform]
  rfl

/-- The complete packaged left-reflection block is zero. -/
lemma packagedTwoPortScattering_leftReflection_eq_zero (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) :
    (packagedTwoPortScattering p hDenominator).leftReflection = 0 := by
  ext output input
  rcases output with ⟨⟨⟩⟩
  rcases input with ⟨⟨⟩⟩
  exact packagedTwoPortScattering_leftReflection_entry p hDenominator

/-- The complete packaged right-reflection block is zero. -/
lemma packagedTwoPortScattering_rightReflection_eq_zero (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) :
    (packagedTwoPortScattering p hDenominator).rightReflection = 0 := by
  ext output input
  rcases output with ⟨⟨⟩⟩
  rcases input with ⟨⟨⟩⟩
  exact packagedTwoPortScattering_rightReflection_entry p hDenominator

/-- The packaged right-to-left block acts by scalar multiplication by `throughTransfer`. -/
lemma packagedTwoPortScattering_rightToLeftTransmission_apply (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator)
    (amplitude : ModeAmplitude (BackwardWave Unit)) :
    (packagedTwoPortScattering p hDenominator).rightToLeftTransmission.toLinearMap amplitude =
      WithLp.toLp 2 (fun _ => throughTransfer p * amplitude (BackwardWave.mk ())) := by
  apply WithLp.ofLp_injective 2
  funext output
  rcases output with ⟨⟨⟩⟩
  simp only [ModeTransform.toLinearMap, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]
  rw [← BackwardWave.channelEquiv.symm.sum_comp]
  rw [Fintype.sum_unique]
  simp

/-- The packaged all-pass pivot is bijective exactly when its scalar transmission is nonzero. -/
lemma packagedTwoPortScattering_hasBijectiveRightToLeftTransmission_iff
    (p : Parameters) (hDenominator : p.HasNonzeroDenominator) :
    (packagedTwoPortScattering p hDenominator).HasBijectiveRightToLeftTransmission ↔
      throughTransfer p ≠ 0 := by
  constructor
  · intro hBijective hZero
    have hMapped :
        (packagedTwoPortScattering p hDenominator).rightToLeftTransmission.toLinearMap
            (backwardAmplitude 1) =
          (packagedTwoPortScattering p hDenominator).rightToLeftTransmission.toLinearMap 0 := by
      rw [packagedTwoPortScattering_rightToLeftTransmission_apply,
        packagedTwoPortScattering_rightToLeftTransmission_apply]
      apply WithLp.ofLp_injective 2
      funext index
      rcases index with ⟨⟨⟩⟩
      simp [hZero]
    have hEqual := hBijective.1 hMapped
    have hCoordinate := congrArg
      (fun amplitude : ModeAmplitude (BackwardWave Unit) =>
        amplitude (BackwardWave.mk ())) hEqual
    norm_num [backwardAmplitude] at hCoordinate
  · intro hTransmission
    constructor
    · intro first second hEqual
      apply WithLp.ofLp_injective 2
      funext index
      rcases index with ⟨⟨⟩⟩
      have hCoordinate := congrArg
        (fun amplitude : ModeAmplitude (BackwardWave Unit) =>
          amplitude (BackwardWave.mk ())) hEqual
      rw [packagedTwoPortScattering_rightToLeftTransmission_apply,
        packagedTwoPortScattering_rightToLeftTransmission_apply] at hCoordinate
      simpa using mul_left_cancel₀ hTransmission hCoordinate
    · intro output
      refine ⟨backwardAmplitude
        ((throughTransfer p)⁻¹ * output (BackwardWave.mk ())), ?_⟩
      rw [packagedTwoPortScattering_rightToLeftTransmission_apply]
      apply WithLp.ofLp_injective 2
      funext index
      rcases index with ⟨⟨⟩⟩
      simp [backwardAmplitude, hTransmission]

/-- A nonzero bus transmission supplies the exact packaged chain-view pivot. -/
lemma packagedTwoPortScattering_hasBijectiveRightToLeftTransmission
    (p : Parameters) (hDenominator : p.HasNonzeroDenominator)
    (hTransmission : throughTransfer p ≠ 0) :
    (packagedTwoPortScattering p hDenominator).HasBijectiveRightToLeftTransmission :=
  (packagedTwoPortScattering_hasBijectiveRightToLeftTransmission_iff p hDenominator).2
    hTransmission

/-!
## B. Explicit backward-first chain matrix
-/

/-- The totalized explicit all-pass chain matrix in backward-first order.

Columns are the left state `(bL, aL)` and rows are the right state `(aR, bR)`. Thus the leading
block is the inverse right-to-left transmission and the bottom-right block is the left-to-right
transmission.
-/
def backwardFirstChainMatrix (p : Parameters) : BackwardFirstChainTransform Unit Unit
  | Sum.inl _, Sum.inl _ => (throughTransfer p)⁻¹
  | Sum.inl _, Sum.inr _ => 0
  | Sum.inr _, Sum.inl _ => 0
  | Sum.inr _, Sum.inr _ => throughTransfer p

/-- The behavior-derived all-pass chain transform on the independent solve and pivot gates. -/
noncomputable def backwardFirstChainTransform (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) (hTransmission : throughTransfer p ≠ 0) :
    BackwardFirstChainTransform Unit Unit :=
  (packagedTwoPortScattering p hDenominator).toBackwardFirstChainTransform
    (packagedTwoPortScattering_hasBijectiveRightToLeftTransmission
      p hDenominator hTransmission)

/-- The proof-dependent pivot inverse has the expected reciprocal scalar entry. -/
lemma packagedTwoPortScattering_rightToLeftTransmissionInverse_entry
    (p : Parameters) (hDenominator : p.HasNonzeroDenominator)
    (hTransmission : throughTransfer p ≠ 0) :
    let hPivot := packagedTwoPortScattering_hasBijectiveRightToLeftTransmission
      p hDenominator hTransmission
    ((packagedTwoPortScattering p hDenominator).rightToLeftTransmissionInverse hPivot)
        (BackwardWave.mk ()) (BackwardWave.mk ()) = (throughTransfer p)⁻¹ := by
  let scattering := packagedTwoPortScattering p hDenominator
  let hPivot := packagedTwoPortScattering_hasBijectiveRightToLeftTransmission
    p hDenominator hTransmission
  have hMatrix := scattering.inverse_mul_rightToLeftTransmission hPivot
  have hEntry := congrArg
    (fun matrix : ModeTransform (BackwardWave Unit) (BackwardWave Unit) =>
      matrix (BackwardWave.mk ()) (BackwardWave.mk ())) hMatrix
  have hProduct :
      (scattering.rightToLeftTransmissionInverse hPivot)
          (BackwardWave.mk ()) (BackwardWave.mk ()) * throughTransfer p = 1 := by
    simp only [Matrix.mul_apply] at hEntry
    rw [← BackwardWave.channelEquiv.symm.sum_comp, Fintype.sum_unique] at hEntry
    simpa [scattering] using hEntry
  exact (mul_eq_one_iff_eq_inv₀ hTransmission).mp hProduct

/-- The behavior-derived all-pass chain is the explicit diagonal matrix. -/
lemma backwardFirstChainTransform_eq_matrix (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) (hTransmission : throughTransfer p ≠ 0) :
    backwardFirstChainTransform p hDenominator hTransmission = backwardFirstChainMatrix p := by
  rw [backwardFirstChainTransform,
    TwoPortScatteringTransform.toBackwardFirstChainTransform_eq_blockFormula]
  ext (output | output) (input | input) <;>
    rcases output with ⟨⟨⟩⟩ <;>
    rcases input with ⟨⟨⟩⟩ <;>
    simp [TwoPortScatteringTransform.backwardFirstChainBlockFormula,
      backwardFirstChainMatrix,
      packagedTwoPortScattering_leftReflection_eq_zero,
      packagedTwoPortScattering_rightReflection_eq_zero,
      packagedTwoPortScattering_rightToLeftTransmissionInverse_entry p hDenominator
        hTransmission]

/-!
## C. Behavioral agreement and round trip
-/

/-- The derived chain graph is the backward-first regrouping of the singular-safe N5 behavior. -/
lemma toBehavior_backwardFirstChainTransform (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) (hTransmission : throughTransfer p ≠ 0) :
    (backwardFirstChainTransform p hDenominator hTransmission).toBehavior =
      (externalBehavior p).toBackwardFirst := by
  rw [backwardFirstChainTransform,
    TwoPortScatteringTransform.toBehavior_toBackwardFirstChainTransform]
  unfold TwoPortScatteringTransform.toBackwardFirstBehavior
  rw [toBehavior_packagedTwoPortScattering]

/-- The explicit diagonal chain graph is the backward-first regrouping of the N5 behavior. -/
lemma toBehavior_backwardFirstChainMatrix (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) (hTransmission : throughTransfer p ≠ 0) :
    (backwardFirstChainMatrix p).toBehavior = (externalBehavior p).toBackwardFirst := by
  rw [← backwardFirstChainTransform_eq_matrix p hDenominator hTransmission]
  exact toBehavior_backwardFirstChainTransform p hDenominator hTransmission

/-- The derived all-pass chain has the automatically transported bijective leading block. -/
lemma backwardFirstChainTransform_hasBijectiveLeadingBlock (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) (hTransmission : throughTransfer p ≠ 0) :
    (backwardFirstChainTransform p hDenominator hTransmission).HasBijectiveLeadingBlock :=
  TwoPortScatteringTransform.hasBijectiveLeadingBlock_toBackwardFirstChainTransform
    (packagedTwoPortScattering p hDenominator)
    (packagedTwoPortScattering_hasBijectiveRightToLeftTransmission
      p hDenominator hTransmission)

/-- Converting the derived chain back to scattering recovers the packaged N5 two-port exactly. -/
lemma backwardFirstChainTransform_roundTrip (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) (hTransmission : throughTransfer p ≠ 0) :
    (backwardFirstChainTransform p hDenominator hTransmission).toTwoPortScatteringTransform
        (backwardFirstChainTransform_hasBijectiveLeadingBlock
          p hDenominator hTransmission) =
      packagedTwoPortScattering p hDenominator :=
  TwoPortScatteringTransform.toTwoPortScatteringTransform_toBackwardFirstChainTransform
    (packagedTwoPortScattering p hDenominator)
    (packagedTwoPortScattering_hasBijectiveRightToLeftTransmission
      p hDenominator hTransmission)
    (backwardFirstChainTransform_hasBijectiveLeadingBlock p hDenominator hTransmission)

end AllPass

end

end Optics
