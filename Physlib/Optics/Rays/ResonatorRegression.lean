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

This file carries regression `R-04` of `goal.md` §I.3, whose target is that the resonator trace
criterion implies the fixed-point stability condition. Missing determinant or physical-domain
assumptions are the failure mode guarded here.

The three fixtures are chosen to settle the strict-versus-non-strict question by example rather
than by assertion. A cavity strictly inside the stable region is stable. The confocal cavity sits
exactly on the boundary, with trace `-2`, and is stable, because its round-trip matrix is exactly
`-1`. The plane-parallel Fabry-Perot cavity also sits exactly on the boundary, with trace `2`, and
is **not** stable, because its round trip is a shear and the ray walks off the axis linearly. Even
under `det M = 1`, the non-strict condition `|A + D| ≤ 2` is not sufficient. The sufficient
criterion proved here is the conjunction `det M = 1` and `|A + D| < 2`; the closure
`0 ≤ g₁ g₂ ≤ 1` cannot be used without deciding its endpoints separately.

The fourth fixture is the signed-radius guard. Negating both stored radii turns the stable cavity
into a different, unstable one. That is proved at the level of `IsStable`, not merely at the level
of the trace. No equivalence with inserting explicit angle-coordinate reversals is claimed without
a separate covariance theorem.

## ii. Key results

- `Optics.resonatorRegression_stable`: a two-mirror cavity with `g₁ g₂ = 1 / 4` is stable.
- `Optics.resonatorRegression_confocal_isStable`: the confocal cavity is stable at trace `-2`.
- `Optics.resonatorRegression_fabryPerot_not_isStable`: the plane-parallel Fabry-Perot cavity is
  not stable at trace `2`.
- `Optics.resonatorRegression_negated_radii_not_isStable`: negating the stored signed radii turns
  the stable fixture into a different, unstable cavity.
- `Optics.resonatorRegression_nonUnimodular_not_isStable`: a positive-determinant matrix with
  subcritical trace is unstable, showing the determinant-one hypothesis is load-bearing.
- `Optics.resonatorRegression_eigenbeam`: the stable cavity has a complete Gaussian eigenbeam.

## iii. Table of contents

- A. A cavity strictly inside the stable region
- B. The confocal boundary case
- C. The plane-parallel Fabry-Perot boundary case
- D. The signed-radius guard
- E. The Gaussian eigenbeam

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

/-- The bounded-ray half of regression R-04: the cavity with `g₁ g₂ = 1 / 4` is stable. -/
lemma resonatorRegression_stable : IsStable resonatorRegressionStableMatrix := by
  refine isStable_twoMirror 1 2 2 (by norm_num) (by norm_num) (by norm_num) ?_ ?_ <;>
    norm_num [gParameter]

/-- The determinant hypothesis of the criterion is met, not assumed: the folded mirrors are
unimodular. -/
lemma resonatorRegression_stable_det : resonatorRegressionStableMatrix.det = 1 :=
  twoMirror_det 1 2 2 (by norm_num) (by norm_num) (by norm_num)

/-- A positive-determinant, non-unimodular matrix with subcritical trace. -/
def resonatorRegressionNonUnimodularMatrix : RayTransferMatrix :=
  !![(3 / 2 : ℝ), 0; 0, 1 / 4]

/-- The non-unimodular sentinel has positive determinant and subcritical trace, but determinant
`3 / 8` rather than one. -/
lemma resonatorRegression_nonUnimodular_parameters :
    resonatorRegressionNonUnimodularMatrix.det = 3 / 8 ∧
      rayTrace resonatorRegressionNonUnimodularMatrix = 7 / 4 ∧
      |rayTrace resonatorRegressionNonUnimodularMatrix| < 2 := by
  norm_num [resonatorRegressionNonUnimodularMatrix, Matrix.det_fin_two_of, rayTrace]

/-- One application of the non-unimodular sentinel expands height by `3 / 2`. -/
lemma resonatorRegression_nonUnimodular_step (r : ParaxialRay) :
    rayTransfer resonatorRegressionNonUnimodularMatrix r =
      ⟨(3 / 2 : ℝ) * r.height, (1 / 4 : ℝ) * r.angle⟩ := by
  ext <;> norm_num [resonatorRegressionNonUnimodularMatrix]

/-- The axial-height ray grows geometrically under the non-unimodular sentinel. -/
lemma resonatorRegression_nonUnimodular_roundTripRay (n : ℕ) :
    roundTripRay resonatorRegressionNonUnimodularMatrix ⟨1, 0⟩ n =
      ⟨(3 / 2 : ℝ) ^ n, 0⟩ := by
  induction n with
  | zero => rw [roundTripRay_zero]; ext <;> norm_num
  | succ n ih =>
      rw [roundTripRay_succ, ih, resonatorRegression_nonUnimodular_step, pow_succ]
      ext
      · norm_num
        ring
      · norm_num

/-- **The determinant-one hypothesis is load-bearing.** Positive determinant and subcritical
trace alone do not imply stability. -/
lemma resonatorRegression_nonUnimodular_not_isStable :
    ¬ IsStable resonatorRegressionNonUnimodularMatrix := by
  intro hStable
  obtain ⟨heightBound, _angleBound, hBound⟩ := hStable ⟨1, 0⟩
  obtain ⟨n, hn⟩ :=
    pow_unbounded_of_one_lt heightBound (by norm_num : (1 : ℝ) < 3 / 2)
  have h := (hBound n).1
  rw [resonatorRegression_nonUnimodular_roundTripRay] at h
  have hpow : 0 ≤ (3 / 2 : ℝ) ^ n := pow_nonneg (by norm_num) n
  rw [abs_of_nonneg hpow] at h
  linarith

/-- Swapping unequal mirror radii changes the round-trip matrix even though trace and determinant
cannot detect the swap. -/
lemma resonatorRegression_asymmetric_mirror_order :
    ParaxialSystem.matrix (twoMirrorRoundTrip 1 2 4) ⟨1, 0⟩ =
        !![(1 / 2 : ℝ), 3 / 2; -1, -1] ∧
      ParaxialSystem.matrix (twoMirrorRoundTrip 1 4 2) ⟨1, 0⟩ =
        !![(0 : ℝ), 1; -1, -1 / 2] ∧
      ParaxialSystem.matrix (twoMirrorRoundTrip 1 2 4) ⟨1, 0⟩ ≠
        ParaxialSystem.matrix (twoMirrorRoundTrip 1 4 2) ⟨1, 0⟩ := by
  constructor
  · rw [twoMirror_matrix 1 2 4 (by norm_num) (by norm_num)]
    norm_num
  constructor
  · rw [twoMirror_matrix 1 4 2 (by norm_num) (by norm_num)]
    norm_num
  · intro hEqual
    have hEntry := congrArg (fun M : RayTransferMatrix => M 0 0) hEqual
    rw [twoMirror_matrix 1 2 4 (by norm_num) (by norm_num),
      twoMirror_matrix 1 4 2 (by norm_num) (by norm_num)] at hEntry
    norm_num at hEntry

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

## D. The signed-radius guard

-/

/-- The stable fixture with both stored mirror radii negated. This is a different cavity in the
fixed folded convention. -/
def resonatorRegressionNegatedMatrix : RayTransferMatrix :=
  ParaxialSystem.matrix (twoMirrorRoundTrip 1 (-2) (-2)) ⟨1, 0⟩

/-- The negative-radius fixture gives the matrix `!![2, 3; 3, 5]`, of trace `7`. -/
lemma resonatorRegression_negated_matrix :
    resonatorRegressionNegatedMatrix = !![2, 3; 3, 5] := by
  rw [resonatorRegressionNegatedMatrix, twoMirror_matrix 1 (-2) (-2) (by norm_num) (by norm_num)]
  norm_num

/-- One negative-radius round trip, written out. -/
lemma resonatorRegression_negated_step (s : ParaxialRay) :
    rayTransfer (!![2, 3; 3, 5] : RayTransferMatrix) s =
      ⟨2 * s.height + 3 * s.angle, 3 * s.height + 5 * s.angle⟩ := by
  ext <;> norm_num

/-- Under the negative-radius round trip a ray in the first quadrant grows without bound. -/
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

/-- **Negating both stored radii turns the stable fixture into an unstable cavity.**

This is the signed-radius guard stated where it matters. In the fixed folded convention, the
negative-radius fixture is a different cavity, and it is unstable while the original is stable.
No relation to an explicit angle-coordinate reversal is asserted here.
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

## E. The Gaussian eigenbeam

-/

/-- The stable fixture's complete matrix, pinning every entry rather than only trace and
determinant. -/
lemma resonatorRegression_stable_matrix :
    resonatorRegressionStableMatrix = !![(0 : ℝ), 1; -1, -1] := by
  rw [resonatorRegressionStableMatrix, twoMirror_matrix 1 2 2 (by norm_num) (by norm_num)]
  norm_num

/-- The proof-gated eigenparameter candidate of the stable fixture is
`-1 / 2 + (√3 / 2) i`. -/
lemma resonatorRegression_eigenparameter :
    gaussianEigenparameterCandidate resonatorRegressionStableMatrix =
      (-1 / 2 : ℝ) + (√3 / 2 : ℝ) * Complex.I := by
  rw [gaussianEigenparameterCandidate, resonatorRegression_stable_matrix, rayTrace]
  norm_num

/-- The ray invariant of the stable fixture is the negative of the same quadratic whose complex
root is the Gaussian eigenparameter. -/
lemma resonatorRegression_rayInvariant (r : ParaxialRay) :
    rayInvariant resonatorRegressionStableMatrix r =
      -(r.height ^ 2 + r.height * r.angle + r.angle ^ 2) := by
  rw [resonatorRegression_stable_matrix, rayInvariant]
  norm_num
  ring

/-- The stable fixture's eigenparameter satisfies the concrete quadratic `q² + q + 1 = 0`. -/
lemma resonatorRegression_eigenparameter_quadratic :
    gaussianEigenparameterCandidate resonatorRegressionStableMatrix ^ 2 +
        gaussianEigenparameterCandidate resonatorRegressionStableMatrix + 1 = 0 := by
  have h := quadratic_gaussianEigenparameterCandidate resonatorRegressionStableMatrix
    resonatorRegression_stable_det (by rw [resonatorRegression_stable_trace]; norm_num)
  rw [resonatorRegression_stable_matrix] at h ⊢
  norm_num at h ⊢
  linear_combination -h

/-- **The stable cavity supports a physical Gaussian eigenparameter**, reproduced exactly by the
round trip. -/
lemma resonatorRegression_eigenparameter_exists :
    ∃ q : ℂ, 0 < q.im ∧ abcdTransform resonatorRegressionStableMatrix q = q := by
  refine exists_gaussian_eigenparameter resonatorRegressionStableMatrix
    resonatorRegression_stable_det ?_
  rw [resonatorRegression_stable_trace]
  norm_num

/-- **The stable cavity supports a complete Gaussian eigenbeam**, including a positive wavelength
that is unchanged by the round trip. -/
lemma resonatorRegression_eigenbeam :
    ∃ b : GaussianBeam,
      b.transform resonatorRegressionStableMatrix
        (show 0 < resonatorRegressionStableMatrix.det by
          rw [resonatorRegression_stable_det]
          norm_num) = b := by
  refine exists_gaussian_eigenbeam resonatorRegressionStableMatrix
    resonatorRegression_stable_det ?_
  rw [resonatorRegression_stable_trace]
  norm_num

/-- **Regression R-04.** The determinant-one strict-trace criterion reaches both matrix-level
bounded-ray stability and the named fixed-Gaussian-beam condition. -/
lemma resonatorRegression_traceCriterion_stable_and_fixedBeam :
    IsStable resonatorRegressionStableMatrix ∧
      ∃ b : GaussianBeam, IsFixedBeam resonatorRegressionStableMatrix b := by
  refine isStable_and_exists_isFixedBeam_of_abs_trace_lt_two
    resonatorRegressionStableMatrix resonatorRegression_stable_det ?_
  rw [resonatorRegression_stable_trace]
  norm_num

end

end Optics
