/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Rays.Transfer

/-!
# Regression tests for ray-transfer matrices and ordered systems

## i. Overview

This file carries regression `R-01` of `goal.md` §I.3, whose stated target is multiplication-order
errors in the system fold.

The order sentinel is deliberately built so that the determinant law cannot detect the swap. Two
thin lenses of different focal lengths, at different distances, are assembled in both orders. Both
systems are valid, both have determinant `1`, and both leave the `A` entry unchanged; only `B` and
`C` differ. A fold written in the wrong order therefore still passes every index and determinant
check and is caught only here.

The remaining sections pin the canonical closed forms that later slices build on: the symmetric
two-lens system, whose `A = D` symmetry is a sharper sentinel than its determinant, and the
positive-focal-length `2f`-to-`2f` configuration, whose vanishing `B` entry is the imaging
condition that `Physlib.Optics.Rays.Imaging` will interpret. Both are obtained from the system
fold rather than by multiplying matrices by hand.

## ii. Key results

- `Optics.transferRegression_order_matters`: the two orders of the same two components give
  different system matrices, while both have determinant `1`.
- `Optics.transferRegression_ray_order_matters`: the two orders send the same incoming ray to
  different outgoing rays, through the relational system law.
- `Optics.transferRegression_symmetricTwoLens_matrix`: the symmetric two-lens system matrix, with
  its `A = D` symmetry and unit determinant.
- `Optics.transferRegression_imaging_twoFocalLengths`: the `2f`-to-`2f` configuration has
  vanishing `B` entry and transverse magnification `-1`.
- `Optics.transferRegression_det_indexStep`: the telescoped determinant law on a system that
  changes refractive index.

## iii. Table of contents

- A. Fold-order sentinels
- B. The symmetric two-lens system
- C. Thin-lens imaging at twice the focal length
- D. The determinant law across an index step
- E. Output-angle reversal
- F. Identity and zero limits

## iv. References

The fixtures use only the public declarations of `Physlib.Optics.Rays.Transfer`. Their
coefficients make no material or fabrication claim.

-/

@[expose] public section

namespace Optics

noncomputable section

/-!

## A. Fold-order sentinels

-/

/-- A lens-shaped prescribed matrix parameterized by the algebraic value `f`, in unit index.

Its entries satisfy the index-ratio determinant condition between equal indices, so it is a valid
prescribed component for any `f`. At `f = 0` totalized division makes it the identity; physical
focal-length fixtures below impose `f ≠ 0` or `0 < f`.
-/
def transferRegressionLens (f : ℝ) : ParaxialInterface :=
  ParaxialInterface.prescribed 1 0 (-1 / f) 1

/-- The lens-shaped prescribed matrix is algebraically valid between equal unit indices. -/
lemma transferRegressionLens_isValid (f : ℝ) : (transferRegressionLens f).IsValid 1 1 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  norm_num

/-- The first ordered component: a gap of length `1`, then a lens of focal length `2`. -/
def transferRegressionFirst : ParaxialComponent := ⟨⟨1, 1⟩, transferRegressionLens 2⟩

/-- The second ordered component: a gap of length `2`, then a lens of focal length `1`. -/
def transferRegressionSecond : ParaxialComponent := ⟨⟨1, 2⟩, transferRegressionLens 1⟩

/-- The gap the regression systems are left through. -/
def transferRegressionExit : ParaxialGap := ⟨1, 0⟩

/-- Both orders of the two regression components form valid systems. -/
lemma transferRegression_isValid :
    ParaxialSystem.IsValid [transferRegressionFirst, transferRegressionSecond]
      transferRegressionExit ∧
    ParaxialSystem.IsValid [transferRegressionSecond, transferRegressionFirst]
      transferRegressionExit := by
  refine ⟨⟨⟨?_, ?_⟩, transferRegressionLens_isValid 2, ⟨?_, ?_⟩,
      transferRegressionLens_isValid 1, ?_, ?_⟩,
    ⟨⟨?_, ?_⟩, transferRegressionLens_isValid 1, ⟨?_, ?_⟩,
      transferRegressionLens_isValid 2, ?_, ?_⟩⟩ <;>
    norm_num [transferRegressionFirst, transferRegressionSecond, transferRegressionExit]

/-- The system matrix in the order first, then second. -/
lemma transferRegression_matrix :
    ParaxialSystem.matrix [transferRegressionFirst, transferRegressionSecond]
        transferRegressionExit = !![0, 2; -1 / 2, -3 / 2] := by
  simp only [ParaxialSystem.matrix, transferRegressionFirst,
    transferRegressionSecond, transferRegressionExit, transferRegressionLens,
    ParaxialInterface.transferMatrix, ParaxialGap.transferMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- The system matrix in the reversed order. -/
lemma transferRegression_matrix_swapped :
    ParaxialSystem.matrix [transferRegressionSecond, transferRegressionFirst]
        transferRegressionExit = !![0, 1; -1, -3 / 2] := by
  simp only [ParaxialSystem.matrix, transferRegressionFirst,
    transferRegressionSecond, transferRegressionExit, transferRegressionLens,
    ParaxialInterface.transferMatrix, ParaxialGap.transferMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- **Regression R-01.** Reversing the order of the components changes the system matrix. -/
lemma transferRegression_order_matters :
    ParaxialSystem.matrix [transferRegressionFirst, transferRegressionSecond]
        transferRegressionExit ≠
      ParaxialSystem.matrix [transferRegressionSecond, transferRegressionFirst]
        transferRegressionExit := by
  rw [transferRegression_matrix, transferRegression_matrix_swapped]
  intro hEq
  have h01 : (!![(0 : ℝ), 2; -1 / 2, -3 / 2]) 0 1 = (!![(0 : ℝ), 1; -1, -3 / 2]) 0 1 := by
    rw [hEq]
  norm_num at h01

/-- Neither the determinant law nor the `A` entry detects the swap: both determinants are `1` and
the `A` entries agree. Only the full matrix does. -/
lemma transferRegression_det_blind_to_order :
    (ParaxialSystem.matrix [transferRegressionFirst, transferRegressionSecond]
        transferRegressionExit).det = 1 ∧
    (ParaxialSystem.matrix [transferRegressionSecond, transferRegressionFirst]
        transferRegressionExit).det = 1 ∧
      ParaxialSystem.matrix [transferRegressionFirst, transferRegressionSecond]
          transferRegressionExit 0 0 =
        ParaxialSystem.matrix [transferRegressionSecond, transferRegressionFirst]
          transferRegressionExit 0 0 := by
  rw [transferRegression_matrix, transferRegression_matrix_swapped]
  norm_num [Matrix.det_fin_two_of]

/-- The order sentinel reaches the outgoing ray itself, through the relational system law rather
than through the matrix: the same incoming ray leaves the two orders differently. -/
lemma transferRegression_ray_order_matters :
    ParaxialSystem.RayBehavior [transferRegressionFirst, transferRegressionSecond]
        transferRegressionExit ⟨1, 0⟩ ⟨0, -1 / 2⟩ ∧
    ParaxialSystem.RayBehavior [transferRegressionSecond, transferRegressionFirst]
        transferRegressionExit ⟨1, 0⟩ ⟨0, -1⟩ := by
  refine ⟨?_, ?_⟩
  · refine ⟨⟨1, 0⟩, ⟨1, -1 / 2⟩, ?_, ?_,
      ⟨⟨0, -1 / 2⟩, ⟨0, -1 / 2⟩, ?_, ?_, ?_⟩⟩ <;>
      norm_num [transferRegressionFirst, transferRegressionSecond, transferRegressionExit,
        transferRegressionLens, ParaxialSystem.RayBehavior, ParaxialGap.RayBehavior,
        ParaxialInterface.RayBehavior]
  · refine ⟨⟨1, 0⟩, ⟨1, -1⟩, ?_, ?_,
      ⟨⟨0, -1⟩, ⟨0, -1⟩, ?_, ?_, ?_⟩⟩ <;>
      norm_num [transferRegressionFirst, transferRegressionSecond, transferRegressionExit,
        transferRegressionLens, ParaxialSystem.RayBehavior, ParaxialGap.RayBehavior,
        ParaxialInterface.RayBehavior]

/-!

## B. The symmetric two-lens system

-/

/-- The symmetric two-lens system: two identical thin lenses of focal length `f` separated by a
gap of length `d`, in a medium of index `1`. -/
def transferRegressionSymmetricTwoLens (f d : ℝ) : List ParaxialComponent :=
  [⟨⟨1, 0⟩, transferRegressionLens f⟩, ⟨⟨1, d⟩, transferRegressionLens f⟩]

/-- The algebraic prescribed-component system is valid for every focal parameter and nonnegative
separation. Physical focal-length use additionally requires `f ≠ 0`. -/
lemma transferRegressionSymmetricTwoLens_isValid (f d : ℝ) (hd : 0 ≤ d) :
    ParaxialSystem.IsValid (transferRegressionSymmetricTwoLens f d) ⟨1, 0⟩ := by
  refine ⟨⟨by norm_num, by norm_num⟩, transferRegressionLens_isValid f,
    ⟨by norm_num, hd⟩, transferRegressionLens_isValid f, by norm_num, by norm_num⟩

/-- The symmetric two-lens system matrix, obtained from the system fold. -/
lemma transferRegression_symmetricTwoLens_matrix (f d : ℝ) (hf : f ≠ 0) :
    ParaxialSystem.matrix (transferRegressionSymmetricTwoLens f d) ⟨1, 0⟩ =
      !![1 - d / f, d; d / f ^ 2 - 2 / f, 1 - d / f] := by
  simp only [transferRegressionSymmetricTwoLens, ParaxialSystem.matrix,
    transferRegressionLens, ParaxialInterface.transferMatrix, ParaxialGap.transferMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

/-- A symmetric system has equal `A` and `D` entries. This is a sharper sentinel than the
determinant, which is `1` for many systems that are not symmetric. -/
lemma transferRegression_symmetricTwoLens_symmetric (f d : ℝ) (hf : f ≠ 0) :
    ParaxialSystem.matrix (transferRegressionSymmetricTwoLens f d) ⟨1, 0⟩ 0 0 =
      ParaxialSystem.matrix (transferRegressionSymmetricTwoLens f d) ⟨1, 0⟩ 1 1 := by
  rw [transferRegression_symmetricTwoLens_matrix f d hf]
  norm_num

/-- The symmetric two-lens system has unit determinant, as the index-ratio law requires between
equal indices. -/
lemma transferRegression_symmetricTwoLens_det (f d : ℝ) (hf : f ≠ 0) :
    (ParaxialSystem.matrix (transferRegressionSymmetricTwoLens f d) ⟨1, 0⟩).det = 1 := by
  rw [transferRegression_symmetricTwoLens_matrix f d hf, Matrix.det_fin_two_of]
  field_simp
  ring

/-!

## C. Thin-lens imaging at twice the focal length

-/

/-- The `2f`-to-`2f` thin-lens configuration: an object plane a distance `2 * f` in front of a
lens of focal length `f`, and an image plane the same distance behind it. -/
def transferRegressionTwoFocalLengths (f : ℝ) : List ParaxialComponent :=
  [⟨⟨1, 2 * f⟩, transferRegressionLens f⟩]

/-- The `2f`-to-`2f` fixture is valid for a positive focal length. -/
lemma transferRegressionTwoFocalLengths_isValid (f : ℝ) (hf : 0 < f) :
    ParaxialSystem.IsValid (transferRegressionTwoFocalLengths f) ⟨1, 2 * f⟩ := by
  refine ⟨⟨by norm_num, by linarith⟩, transferRegressionLens_isValid f, by norm_num, by linarith⟩

/-- **Thin-lens imaging at twice the focal length.** The `2f`-to-`2f` system matrix is
`!![-1, 0; -1 / f, -1]`.

The vanishing `B` entry is the imaging condition and the `A` entry `-1` is the transverse
magnification, so this configuration images with unit magnification and inversion.
`Physlib.Optics.Rays.Imaging` gives those two readings their general statements; here they are
pinned as matrix entries obtained from the system fold.
-/
lemma transferRegression_imaging_twoFocalLengths (f : ℝ) (hf : f ≠ 0) :
    ParaxialSystem.matrix (transferRegressionTwoFocalLengths f) ⟨1, 2 * f⟩ =
      !![-1, 0; -1 / f, -1] := by
  simp only [transferRegressionTwoFocalLengths, ParaxialSystem.matrix,
    transferRegressionLens, ParaxialInterface.transferMatrix, ParaxialGap.transferMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

/-- A unit-height axis-parallel input reaches height `-1` and slope `-1 / f` at the second
conjugate plane. -/
lemma transferRegression_imaging_twoFocalLengths_ray (f : ℝ) (hf : 0 < f) :
    ParaxialSystem.RayBehavior (transferRegressionTwoFocalLengths f) ⟨1, 2 * f⟩ ⟨1, 0⟩
      ⟨-1, -1 / f⟩ := by
  rw [ParaxialSystem.rayBehavior_iff_matrix _ _
    (transferRegressionTwoFocalLengths_isValid f hf),
    transferRegression_imaging_twoFocalLengths f hf.ne']
  ext <;> norm_num

/-!

## D. The determinant law across an index step

-/

/-- A two-surface system that carries a ray from index `1` through index `2` into index `3`. -/
def transferRegressionIndexStep : List ParaxialComponent :=
  [⟨⟨1, 1⟩, ParaxialInterface.planeRefracting⟩, ⟨⟨2, 0⟩, ParaxialInterface.planeRefracting⟩]

/-- The index-step system is valid. -/
lemma transferRegressionIndexStep_isValid :
    ParaxialSystem.IsValid transferRegressionIndexStep ⟨3, 0⟩ := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;>
    norm_num [transferRegressionIndexStep, ParaxialSystem.headIndex]

/-- The index-step system matrix. -/
lemma transferRegressionIndexStep_matrix :
    ParaxialSystem.matrix transferRegressionIndexStep ⟨3, 0⟩ = !![1, 1; 0, 1 / 3] := by
  simp only [transferRegressionIndexStep, ParaxialSystem.matrix, ParaxialSystem.headIndex,
    ParaxialInterface.transferMatrix, ParaxialGap.transferMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- **The telescoped determinant law, checked two ways.** The general law and the explicitly
computed matrix agree on `1 / 3`, the ratio of the entry index to the exit index. -/
lemma transferRegression_det_indexStep :
    (ParaxialSystem.matrix transferRegressionIndexStep ⟨3, 0⟩).det = 1 / 3 ∧
      ParaxialSystem.headIndex transferRegressionIndexStep ⟨3, 0⟩ / (⟨3, 0⟩ : ParaxialGap).index =
        1 / 3 := by
  refine ⟨?_, by norm_num [ParaxialSystem.headIndex, transferRegressionIndexStep]⟩
  rw [transferRegressionIndexStep_matrix, Matrix.det_fin_two_of]
  norm_num

/-- The determinant obtained from the general law is the one obtained by computing the matrix. -/
lemma transferRegression_det_indexStep_law :
    (ParaxialSystem.matrix transferRegressionIndexStep ⟨3, 0⟩).det = 1 / 3 := by
  rw [ParaxialSystem.det_matrix transferRegressionIndexStep ⟨3, 0⟩
    transferRegressionIndexStep_isValid
    (by
      intro c hc
      fin_cases hc <;> exact fun h => ParaxialInterface.noConfusion h)]
  norm_num [ParaxialSystem.headIndex, transferRegressionIndexStep]

/-!

## E. Output-angle reversal

-/

/-- The folded radius-`2` mirror matrix has determinant `1`; reversing its output-angle coordinate
gives determinant `-1`.

This pins the coordinate operation only; it does not classify the mirror as concave or identify a
particular source convention.
-/
lemma transferRegression_outputAngleReversed_det (n : ℝ) :
    ((ParaxialInterface.sphericalMirror 2).transferMatrix n n).det = 1 ∧
      ((ParaxialInterface.sphericalMirror 2).outputAngleReversedTransferMatrix n n).det = -1 := by
  refine ⟨by simp [ParaxialInterface.transferMatrix, Matrix.det_fin_two_of], ?_⟩
  rw [ParaxialInterface.det_outputAngleReversedTransferMatrix,
    ParaxialInterface.transferMatrix, Matrix.det_fin_two_of]
  norm_num

/-- The output-angle-reversed matrix of the radius-`2` spherical-mirror fixture. -/
lemma transferRegression_outputAngleReversed_sphericalMirror (n : ℝ) :
    (ParaxialInterface.sphericalMirror 2).outputAngleReversedTransferMatrix n n =
      !![1, 0; 1, -1] := by
  rw [ParaxialInterface.outputAngleReversedTransferMatrix_sphericalMirror]
  norm_num

/-!

## F. Identity and zero limits

-/

/-- Individually valid subsystems with mismatched adjacent refractive indices do not form a valid
composed optical system. -/
lemma transferRegression_mismatchedIndices_not_composedIsValid :
    ¬ParaxialSystem.ComposedIsValid
      [(([] : List ParaxialComponent), ⟨1, 0⟩),
        (([] : List ParaxialComponent), ⟨2, 0⟩)] := by
  intro hValid
  norm_num [ParaxialSystem.ComposedIsValid, ParaxialSystem.ComposedIndicesCompatible,
    ParaxialSystem.headIndex] at hValid

/-- A system with no components and a zero-length exit gap is the identity. -/
lemma transferRegression_matrix_nil : ParaxialSystem.matrix [] ⟨1, 0⟩ = 1 := by
  rw [ParaxialSystem.matrix, ParaxialGap.transferMatrix, Matrix.one_fin_two]

/-- A composed system with no subsystems is the identity. -/
lemma transferRegression_composedMatrix_nil : ParaxialSystem.composedMatrix [] = 1 := rfl

/-- A lens whose material index equals the surrounding index is the identity, whatever its
surface radii: with no index step there is nothing to refract. -/
lemma transferRegression_thinLens_matched (n R₁ R₂ : ℝ) (hn : n ≠ 0) (hR₁ : R₁ ≠ 0)
    (hR₂ : R₂ ≠ 0) :
    ParaxialSystem.matrix (thinLensSystem n n R₁ R₂) ⟨n, 0⟩ = 1 := by
  rw [thinLens_matrix n n R₁ R₂ hn hn hR₁ hR₂, Matrix.one_fin_two, div_self hn]
  norm_num

/-- The opposite-unit-radius glass-lens fixture has focal parameter `1`, since its lensmaker
expression is `(3 / 2 - 1) (1 - (-1)) = 1`. No convexity label is attached before the signed-radius
source convention is independently audited. -/
lemma transferRegression_thinLens_oppositeRadii :
    ParaxialSystem.matrix (thinLensSystem 1 (3 / 2) 1 (-1)) ⟨1, 0⟩ =
      thinLensMatrix 1 := by
  rw [thinLens_matrix_eq_thinLensMatrix 1 (3 / 2) 1 (-1) 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)]

end

end Optics
