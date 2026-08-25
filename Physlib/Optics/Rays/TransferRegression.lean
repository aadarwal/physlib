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
`2f`-to-`2f` thin-lens configuration, whose vanishing `B` entry is the imaging condition that
`Physlib.Optics.Rays.Imaging` will interpret. Both are obtained from the system fold rather than
by multiplying matrices by hand.

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
- `Optics.transferRegression_roundTrip_trace`: the two-mirror round-trip trace is `4 g₁ g₂ - 2`,
  the convention guard against double-counting the reflection direction reversal.

## iii. Table of contents

- A. Fold-order sentinels
- B. The symmetric two-lens system
- C. Thin-lens imaging at twice the focal length
- D. The determinant law across an index step
- E. The unfolded reflection convention
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

/-- A thin lens of focal length `f`, in a medium of index `1`, as a prescribed component.

Its entries satisfy the index-ratio determinant condition between equal indices, so it is a valid
prescribed component for any `f`.
-/
def transferRegressionLens (f : ℝ) : ParaxialInterface :=
  ParaxialInterface.prescribed 1 0 (-1 / f) 1

/-- A regression thin lens is a valid component between equal unit indices. -/
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

/-- Neither the determinant law nor the `A` entry detects the swap: both orders have determinant
`1` and the same `A` entry. Only the full matrix does. -/
lemma transferRegression_det_blind_to_order :
    (ParaxialSystem.matrix [transferRegressionFirst, transferRegressionSecond]
        transferRegressionExit).det =
      (ParaxialSystem.matrix [transferRegressionSecond, transferRegressionFirst]
        transferRegressionExit).det ∧
    ParaxialSystem.matrix [transferRegressionFirst, transferRegressionSecond]
        transferRegressionExit 0 0 =
      ParaxialSystem.matrix [transferRegressionSecond, transferRegressionFirst]
        transferRegressionExit 0 0 := by
  rw [transferRegression_matrix, transferRegression_matrix_swapped]
  refine ⟨?_, by norm_num⟩
  rw [Matrix.det_fin_two_of, Matrix.det_fin_two_of]
  norm_num

/-- The order sentinel reaches the outgoing ray itself, through the relational system law rather
than through the matrix: the same incoming ray leaves the two orders differently. -/
lemma transferRegression_ray_order_matters :
    ParaxialSystem.RayBehavior [transferRegressionFirst, transferRegressionSecond]
        transferRegressionExit ⟨1, 0⟩ ⟨0, -1 / 2⟩ ∧
    ParaxialSystem.RayBehavior [transferRegressionSecond, transferRegressionFirst]
        transferRegressionExit ⟨1, 0⟩ ⟨0, -1⟩ := by
  obtain ⟨hFirst, hSecond⟩ := transferRegression_isValid
  refine ⟨?_, ?_⟩
  · rw [ParaxialSystem.rayBehavior_iff_matrix _ _ hFirst, transferRegression_matrix]
    ext <;> norm_num
  · rw [ParaxialSystem.rayBehavior_iff_matrix _ _ hSecond, transferRegression_matrix_swapped]
    ext <;> norm_num

/-!

## B. The symmetric two-lens system

-/

/-- The symmetric two-lens system: two identical thin lenses of focal length `f` separated by a
gap of length `d`, in a medium of index `1`. -/
def transferRegressionSymmetricTwoLens (f d : ℝ) : List ParaxialComponent :=
  [⟨⟨1, 0⟩, transferRegressionLens f⟩, ⟨⟨1, d⟩, transferRegressionLens f⟩]

/-- The symmetric two-lens system is valid for every focal length and separation. -/
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

/-- The `2f`-to-`2f` configuration is valid for a nonnegative focal length. -/
lemma transferRegressionTwoFocalLengths_isValid (f : ℝ) (hf : 0 ≤ f) :
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

/-- At the `2f` conjugate planes an on-axis object height is imaged to its negative, with the ray
angle unchanged up to sign for an axis-parallel input. -/
lemma transferRegression_imaging_twoFocalLengths_ray (f : ℝ) (hf : f ≠ 0) (hfPos : 0 ≤ f) :
    ParaxialSystem.RayBehavior (transferRegressionTwoFocalLengths f) ⟨1, 2 * f⟩ ⟨1, 0⟩
      ⟨-1, -1 / f⟩ := by
  rw [ParaxialSystem.rayBehavior_iff_matrix _ _ (transferRegressionTwoFocalLengths_isValid f hfPos),
    transferRegression_imaging_twoFocalLengths f hf]
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

## E. The unfolded reflection convention

-/

/-- In the folded convention a concave mirror of radius `2` has determinant `1`; in the unfolded
convention the same mirror has determinant `-1`.

The two conventions differ by exactly one angle reversal, so any comparison against a source
using the other one must account for this sign.
-/
lemma transferRegression_unfolded_det (n : ℝ) :
    ((ParaxialInterface.sphericalMirror 2).transferMatrix n n).det = 1 ∧
      ((ParaxialInterface.sphericalMirror 2).unfoldedTransferMatrix n n).det = -1 := by
  refine ⟨by simp [ParaxialInterface.transferMatrix, Matrix.det_fin_two_of], ?_⟩
  rw [ParaxialInterface.det_unfoldedTransferMatrix, ParaxialInterface.transferMatrix,
    Matrix.det_fin_two_of]
  norm_num

/-- The unfolded matrix of a concave mirror of radius `2`. -/
lemma transferRegression_unfolded_sphericalMirror (n : ℝ) :
    (ParaxialInterface.sphericalMirror 2).unfoldedTransferMatrix n n = !![1, 0; 1, -1] := by
  rw [ParaxialInterface.unfoldedTransferMatrix_sphericalMirror]
  norm_num

/-- A two-mirror round trip: travel the cavity length, reflect off the far mirror, travel back,
reflect off the near mirror. -/
def transferRegressionRoundTrip (d R₁ R₂ : ℝ) : List ParaxialComponent :=
  [⟨⟨1, d⟩, ParaxialInterface.sphericalMirror R₂⟩,
    ⟨⟨1, d⟩, ParaxialInterface.sphericalMirror R₁⟩]

/-- The two-mirror round trip is a valid system for a nonnegative cavity length and nonzero mirror
radii. -/
lemma transferRegressionRoundTrip_isValid (d R₁ R₂ : ℝ) (hd : 0 ≤ d) (hR₁ : R₁ ≠ 0)
    (hR₂ : R₂ ≠ 0) :
    ParaxialSystem.IsValid (transferRegressionRoundTrip d R₁ R₂) ⟨1, 0⟩ := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, ?_⟩ <;>
    norm_num [transferRegressionRoundTrip, ParaxialSystem.headIndex, hd, hR₁, hR₂]

/-- **The two-mirror round-trip trace.** The trace of the round-trip matrix is `4 g₁ g₂ - 2` with
`gᵢ = 1 - d / Rᵢ`.

This is the convention guard the reflection bookkeeping needs. The direction reversal at a mirror
can be absorbed into the matrix, as the folded convention here does, or kept explicit, as
`ParaxialInterface.unfoldedTransferMatrix` does; but it must not be counted twice. A treatment
that keeps the reversal explicit *and* negates the radii on unfolding computes the round trip of
the negated radii instead, and `transferRegression_roundTrip_negated_radii` shows that changes the
answer in a way a single-mirror check cannot see.
-/
lemma transferRegression_roundTrip_matrix (d R₁ R₂ : ℝ) (hR₁ : R₁ ≠ 0) (hR₂ : R₂ ≠ 0) :
    ParaxialSystem.matrix (transferRegressionRoundTrip d R₁ R₂) ⟨1, 0⟩ =
      !![1 - 2 * d / R₂, 2 * d - 2 * d ^ 2 / R₂;
        -2 / R₁ + 4 * d / (R₁ * R₂) - 2 / R₂,
        1 - 2 * d / R₂ - 4 * d / R₁ + 4 * d ^ 2 / (R₁ * R₂)] := by
  simp only [transferRegressionRoundTrip, ParaxialSystem.matrix,
    ParaxialInterface.transferMatrix, ParaxialGap.transferMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

/-- **The two-mirror round-trip trace.** The trace of the round-trip matrix is `4 g₁ g₂ - 2` with
`gᵢ = 1 - d / Rᵢ`. -/
lemma transferRegression_roundTrip_trace (d R₁ R₂ : ℝ) (hR₁ : R₁ ≠ 0) (hR₂ : R₂ ≠ 0) :
    ParaxialSystem.matrix (transferRegressionRoundTrip d R₁ R₂) ⟨1, 0⟩ 0 0 +
        ParaxialSystem.matrix (transferRegressionRoundTrip d R₁ R₂) ⟨1, 0⟩ 1 1 =
      4 * (1 - d / R₁) * (1 - d / R₂) - 2 := by
  rw [transferRegression_roundTrip_matrix d R₁ R₂ hR₁ hR₂]
  norm_num
  field_simp
  ring

/-- The round trip has unit determinant, so the determinant hypothesis of the source's stability
theorem is met directly in the folded convention used here. -/
lemma transferRegression_roundTrip_det (d R₁ R₂ : ℝ) (hd : 0 ≤ d) (hR₁ : R₁ ≠ 0) (hR₂ : R₂ ≠ 0) :
    (ParaxialSystem.matrix (transferRegressionRoundTrip d R₁ R₂) ⟨1, 0⟩).det = 1 := by
  rw [ParaxialSystem.det_matrix _ _ (transferRegressionRoundTrip_isValid d R₁ R₂ hd hR₁ hR₂)
    (by
      intro c hc
      fin_cases hc <;> exact fun h => ParaxialInterface.noConfusion h)]
  norm_num [ParaxialSystem.headIndex, transferRegressionRoundTrip]

/-- **The double-counting sentinel.** For a cavity of length `1` between two mirrors of radius `2`
the round-trip trace is `-1`, inside the stable band `[-2, 2]`; negating both radii, which is what
counting the reflection reversal twice amounts to, gives `7` instead.

A single-mirror check cannot see this: it is only the round trip that exposes the compensating
pair of conventions.
-/
lemma transferRegression_roundTrip_negated_radii :
    ParaxialSystem.matrix (transferRegressionRoundTrip 1 2 2) ⟨1, 0⟩ 0 0 +
        ParaxialSystem.matrix (transferRegressionRoundTrip 1 2 2) ⟨1, 0⟩ 1 1 = -1 ∧
      ParaxialSystem.matrix (transferRegressionRoundTrip 1 (-2) (-2)) ⟨1, 0⟩ 0 0 +
        ParaxialSystem.matrix (transferRegressionRoundTrip 1 (-2) (-2)) ⟨1, 0⟩ 1 1 = 7 := by
  constructor
  · rw [transferRegression_roundTrip_trace 1 2 2 (by norm_num) (by norm_num)]
    norm_num
  · rw [transferRegression_roundTrip_trace 1 (-2) (-2) (by norm_num) (by norm_num)]
    norm_num

/-- Two explicit direction reversals compose to the identity, which is why an even number of
mirrors returns the round trip to the folded convention unchanged. -/
lemma transferRegression_twoReversals : angleReversal * angleReversal = 1 :=
  angleReversal_mul_self

/-!

## F. Identity and zero limits

-/

/-- A system with no components and a zero-length exit gap is the identity. -/
lemma transferRegression_matrix_nil : ParaxialSystem.matrix [] ⟨1, 0⟩ = 1 := by
  rw [ParaxialSystem.matrix, ParaxialGap.transferMatrix, Matrix.one_fin_two]

/-- A composed system with no subsystems is the identity. -/
lemma transferRegression_composedMatrix_nil : ParaxialSystem.composedMatrix [] = 1 := rfl

/-- A lens whose material index equals the surrounding index is the identity, whatever its
surface radii: with no index step there is nothing to refract. -/
lemma transferRegression_thinLens_matched (n R₁ R₂ : ℝ) (hn : n ≠ 0) (hR₁ : R₁ ≠ 0)
    (hR₂ : R₂ ≠ 0) :
    ParaxialSystem.matrix
        [⟨⟨n, 0⟩, ParaxialInterface.sphericalRefracting R₁⟩,
          ⟨⟨n, 0⟩, ParaxialInterface.sphericalRefracting R₂⟩] ⟨n, 0⟩ = 1 := by
  rw [thinLens_matrix n n R₁ R₂ hn hn hR₁ hR₂, Matrix.one_fin_two, div_self hn]
  norm_num

/-- A biconvex glass lens of unit radii in air has focal length `1`, so its matrix is
`!![1, 0; -1, 1]`. The lensmaker's equation gives `1 / f = (3 / 2 - 1) (1 + 1) = 1`. -/
lemma transferRegression_thinLens_biconvex :
    ParaxialSystem.matrix
        [⟨⟨1, 0⟩, ParaxialInterface.sphericalRefracting 1⟩,
          ⟨⟨3 / 2, 0⟩, ParaxialInterface.sphericalRefracting (-1)⟩] ⟨1, 0⟩ =
      thinLensMatrix 1 := by
  rw [thinLens_matrix_eq_thinLensMatrix 1 (3 / 2) 1 (-1) 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)]

end

end Optics
