/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Rays.Resonator

/-!
# Regression tests for optical resonators

## i. Overview

This file carries regression `R-04` of `goal.md` §I.3, whose stated target is a trace criterion
used without its determinant and domain assumptions.

The three fixtures are chosen to settle the strict-versus-non-strict question by example rather
than by assertion. A cavity strictly inside the stable region is stable. The confocal cavity sits
exactly on the boundary, with trace `-2`, and is stable, because its round-trip matrix is exactly
`-1`. The plane-parallel Fabry-Perot cavity also sits exactly on the boundary, with trace `2`, and
is **not** stable, because its round trip is a shear and the ray walks off the axis linearly. So
`|A + D| ≤ 2` is not a sufficient condition, `|A + D| < 2` is, and the closure `0 ≤ g₁ g₂ ≤ 1`
cannot be used as a criterion without deciding its endpoints separately.

The fourth fixture is the reflection-bookkeeping guard. Negating both mirror radii, which is what
counting the direction reversal twice amounts to in the folded convention used here, turns the
stable cavity into an unstable one. That is proved at the level of `IsStable`, not merely at the
level of the trace, so the guard is load-bearing for a stability claim and not only for an
arithmetic one.

## ii. Key results

- `Optics.resonatorRegression_stable`: a two-mirror cavity with `g₁ g₂ = 1 / 4` is stable.
- `Optics.resonatorRegression_confocal_isStable`: the confocal cavity is stable at trace `-2`.
- `Optics.resonatorRegression_fabryPerot_not_isStable`: the plane-parallel Fabry-Perot cavity is
  not stable at trace `2`.
- `Optics.resonatorRegression_negated_radii_not_isStable`: the doubly-counted reflection
  convention turns the stable cavity unstable.
- `Optics.resonatorRegression_eigenmode`: the stable cavity has a Gaussian eigenmode.

## iii. Table of contents

- A. A cavity strictly inside the stable region
- B. The confocal boundary case
- C. The plane-parallel Fabry-Perot boundary case
- D. The reflection-bookkeeping guard
- E. The Gaussian eigenmode

## iv. References

The fixtures use only the public declarations of `Physlib.Optics.Rays.Resonator`.

-/

@[expose] public section

namespace Optics

noncomputable section

open Real

/-!

## A. A cavity strictly inside the stable region

-/

/-- A two-mirror cavity of length `1` between mirrors of radius `2`, so `g₁ = g₂ = 1 / 2`. -/
def resonatorRegressionStableMatrix : RayTransferMatrix :=
  ParaxialSystem.matrix (twoMirrorRoundTrip 1 2 2) ⟨1, 0⟩

/-- The stable cavity has trace `-1`, strictly inside the band. -/
lemma resonatorRegression_stable_trace : rayTrace resonatorRegressionStableMatrix = -1 := by
  rw [resonatorRegressionStableMatrix, twoMirror_trace 1 2 2 (by norm_num) (by norm_num)]
  norm_num [gParameter]

/-- **Regression R-04.** The cavity with `g₁ g₂ = 1 / 4` is stable. -/
lemma resonatorRegression_stable : IsStable resonatorRegressionStableMatrix := by
  refine isStable_twoMirror 1 2 2 (by norm_num) (by norm_num) (by norm_num) ?_ ?_ <;>
    norm_num [gParameter]

/-- The determinant hypothesis of the criterion is met, not assumed: the folded mirrors are
unimodular. -/
lemma resonatorRegression_stable_det : resonatorRegressionStableMatrix.det = 1 :=
  twoMirror_det 1 2 2 (by norm_num) (by norm_num) (by norm_num)

/-!

## B. The confocal boundary case

-/

/-- The confocal cavity: length equal to both mirror radii, so `g₁ = g₂ = 0`. -/
def resonatorRegressionConfocalMatrix : RayTransferMatrix :=
  ParaxialSystem.matrix (twoMirrorRoundTrip 1 1 1) ⟨1, 0⟩

/-- The confocal round-trip matrix is exactly `-1`. -/
lemma resonatorRegression_confocal_matrix : resonatorRegressionConfocalMatrix = -1 := by
  have hneg : (-1 : RayTransferMatrix) = !![(-1 : ℝ), 0; 0, -1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [resonatorRegressionConfocalMatrix, twoMirror_matrix 1 1 1 one_ne_zero one_ne_zero, hneg]
  norm_num

/-- The confocal cavity sits exactly on the stability boundary, at trace `-2`. -/
lemma resonatorRegression_confocal_trace : rayTrace resonatorRegressionConfocalMatrix = -2 := by
  rw [resonatorRegressionConfocalMatrix, twoMirror_trace 1 1 1 one_ne_zero one_ne_zero]
  norm_num [gParameter]

/-- A round trip whose matrix is `-1` either returns a ray unchanged or negates both its
coordinates. -/
lemma roundTripRay_neg_one (r : ParaxialRay) (n : ℕ) :
    roundTripRay (-1 : RayTransferMatrix) r n = r ∨
      roundTripRay (-1 : RayTransferMatrix) r n = ⟨-r.height, -r.angle⟩ := by
  induction n with
  | zero => exact Or.inl (roundTripRay_zero _ _)
  | succ n ih =>
      rw [roundTripRay_succ]
      rcases ih with h | h <;> rw [h] <;> [right; left] <;>
        · ext <;> simp

/-- The confocal round trip either returns a ray unchanged or negates both its coordinates. -/
lemma resonatorRegression_confocal_roundTripRay (r : ParaxialRay) (n : ℕ) :
    roundTripRay resonatorRegressionConfocalMatrix r n = r ∨
      roundTripRay resonatorRegressionConfocalMatrix r n = ⟨-r.height, -r.angle⟩ := by
  rw [resonatorRegression_confocal_matrix]
  exact roundTripRay_neg_one r n

/-- **The confocal cavity is stable even though its trace is exactly `-2`.**

The trace criterion is strict and says nothing here, yet the cavity is stable: its round-trip
matrix is exactly `-1`, so the ray simply alternates sign.
-/
lemma resonatorRegression_confocal_isStable : IsStable resonatorRegressionConfocalMatrix := by
  intro r
  refine ⟨|r.height|, |r.angle|, fun n => ?_⟩
  rcases resonatorRegression_confocal_roundTripRay r n with h | h <;> rw [h] <;> simp

/-!

## C. The plane-parallel Fabry-Perot boundary case

-/

/-- The plane-parallel Fabry-Perot cavity: two flat mirrors a unit distance apart. -/
def resonatorRegressionFabryPerot : List ParaxialComponent :=
  [⟨⟨1, 1⟩, ParaxialInterface.planeMirror⟩, ⟨⟨1, 1⟩, ParaxialInterface.planeMirror⟩]

/-- Its round-trip matrix is the shear through twice the cavity length. -/
lemma resonatorRegression_fabryPerot_matrix :
    ParaxialSystem.matrix resonatorRegressionFabryPerot ⟨1, 0⟩ = !![1, 2; 0, 1] := by
  simp only [resonatorRegressionFabryPerot, ParaxialSystem.matrix,
    ParaxialInterface.transferMatrix, ParaxialGap.transferMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- The Fabry-Perot cavity also sits exactly on the stability boundary, at trace `2`. -/
lemma resonatorRegression_fabryPerot_trace :
    rayTrace (ParaxialSystem.matrix resonatorRegressionFabryPerot ⟨1, 0⟩) = 2 := by
  rw [rayTrace, resonatorRegression_fabryPerot_matrix]
  norm_num

/-- One Fabry-Perot round trip advances the height by twice the cavity length. -/
lemma resonatorRegression_fabryPerot_step (s : ParaxialRay) :
    rayTransfer (!![1, 2; 0, 1] : RayTransferMatrix) s =
      ⟨s.height + 2 * s.angle, s.angle⟩ := by
  ext <;> norm_num

/-- Under the Fabry-Perot round trip an inclined ray walks off the axis linearly. -/
lemma resonatorRegression_fabryPerot_roundTripRay (n : ℕ) :
    roundTripRay (ParaxialSystem.matrix resonatorRegressionFabryPerot ⟨1, 0⟩) ⟨0, 1⟩ n =
      ⟨2 * n, 1⟩ := by
  rw [resonatorRegression_fabryPerot_matrix]
  induction n with
  | zero =>
      rw [roundTripRay_zero]
      ext <;> norm_num
  | succ n ih =>
      rw [roundTripRay_succ, ih, resonatorRegression_fabryPerot_step]
      ext
      · dsimp only
        push_cast
        ring
      · rfl

/-- **The plane-parallel Fabry-Perot cavity is not stable, although its trace is exactly `2`.**

Together with the confocal case this settles the strict-versus-non-strict question: both cavities
sit on the boundary `|A + D| = 2`, and one is stable while the other is not, so the non-strict
inequality is not a criterion.
-/
lemma resonatorRegression_fabryPerot_not_isStable :
    ¬ IsStable (ParaxialSystem.matrix resonatorRegressionFabryPerot ⟨1, 0⟩) := by
  intro hStable
  obtain ⟨heightBound, angleBound, hbound⟩ := hStable ⟨0, 1⟩
  obtain ⟨n, hn⟩ := exists_nat_gt heightBound
  have h := (hbound n).1
  rw [resonatorRegression_fabryPerot_roundTripRay n] at h
  simp only [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * (n : ℝ))] at h
  linarith

/-!

## D. The reflection-bookkeeping guard

-/

/-- The stable cavity with both mirror radii negated, which is what counting the reflection
direction reversal a second time amounts to in the folded convention. -/
def resonatorRegressionNegatedMatrix : RayTransferMatrix :=
  ParaxialSystem.matrix (twoMirrorRoundTrip 1 (-2) (-2)) ⟨1, 0⟩

/-- The doubly-counted convention gives the matrix `!![2, 3; 3, 5]`, of trace `7`. -/
lemma resonatorRegression_negated_matrix :
    resonatorRegressionNegatedMatrix = !![2, 3; 3, 5] := by
  rw [resonatorRegressionNegatedMatrix, twoMirror_matrix 1 (-2) (-2) (by norm_num) (by norm_num)]
  norm_num

/-- One doubly-counted round trip, written out. -/
lemma resonatorRegression_negated_step (s : ParaxialRay) :
    rayTransfer (!![2, 3; 3, 5] : RayTransferMatrix) s =
      ⟨2 * s.height + 3 * s.angle, 3 * s.height + 5 * s.angle⟩ := by
  ext <;> norm_num

/-- Under the doubly-counted round trip a ray in the first quadrant grows without bound. -/
lemma resonatorRegression_negated_growth (n : ℕ) :
    0 ≤ (roundTripRay (!![2, 3; 3, 5] : RayTransferMatrix) ⟨1, 1⟩ n).height ∧
      (roundTripRay (!![2, 3; 3, 5] : RayTransferMatrix) ⟨1, 1⟩ n).height ≤
        (roundTripRay (!![2, 3; 3, 5] : RayTransferMatrix) ⟨1, 1⟩ n).angle ∧
      (5 : ℝ) ^ n ≤ (roundTripRay (!![2, 3; 3, 5] : RayTransferMatrix) ⟨1, 1⟩ n).angle := by
  induction n with
  | zero =>
      rw [roundTripRay_zero]
      norm_num
  | succ n ih =>
      obtain ⟨hnonneg, horder, hgrow⟩ := ih
      rw [roundTripRay_succ, resonatorRegression_negated_step]
      refine ⟨?_, ?_, ?_⟩ <;> dsimp only
      · linarith
      · linarith
      · rw [pow_succ]
        linarith

/-- **The doubly-counted reflection convention turns the stable cavity unstable.**

This is the guard the reflection bookkeeping needs, stated where it matters. The folded mirrors
used here already contain the direction reversal, so the radii keep their signs on the return leg;
negating them as well computes a different cavity, and that cavity is unstable while the original
is stable. A single-mirror check cannot see the difference.
-/
lemma resonatorRegression_negated_radii_not_isStable :
    ¬ IsStable resonatorRegressionNegatedMatrix := by
  intro hStable
  obtain ⟨heightBound, angleBound, hbound⟩ := hStable ⟨1, 1⟩
  rw [resonatorRegression_negated_matrix] at hbound
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt angleBound (by norm_num : (1 : ℝ) < 5)
  obtain ⟨-, -, hgrow⟩ := resonatorRegression_negated_growth n
  have h := (hbound n).2
  have hle := le_abs_self (roundTripRay (!![2, 3; 3, 5] : RayTransferMatrix) ⟨1, 1⟩ n).angle
  linarith

/-- The two cavities differ in stability, so the guard is load-bearing for a stability claim. -/
lemma resonatorRegression_guard :
    IsStable resonatorRegressionStableMatrix ∧ ¬ IsStable resonatorRegressionNegatedMatrix :=
  ⟨resonatorRegression_stable, resonatorRegression_negated_radii_not_isStable⟩

/-!

## E. The Gaussian eigenmode

-/

/-- **The stable cavity supports a Gaussian eigenmode**, whose beam parameter the round trip
reproduces exactly. -/
lemma resonatorRegression_eigenmode :
    ∃ q : ℂ, 0 < q.im ∧ abcdTransform resonatorRegressionStableMatrix q = q := by
  refine exists_gaussian_eigenmode resonatorRegressionStableMatrix
    resonatorRegression_stable_det ?_
  rw [resonatorRegression_stable_trace]
  norm_num

end

end Optics
