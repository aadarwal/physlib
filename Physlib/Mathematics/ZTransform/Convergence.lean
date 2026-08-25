/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Mathematics.ZTransform.Basic

/-!
# The region of convergence of the unilateral Z-transform

## i. Overview

Absolute convergence of the transform series at `z` depends only on `‖z‖`. Its `n`-th term has
norm `‖f n‖ * ‖z‖⁻¹ ^ n`.
This gives rotation invariance and upward closure for the resulting absolute region. Every
nonempty such region contains the exterior of a circle.

The non-strict inequality `‖w‖ ≤ ‖z‖` gives upward closure by comparison of term norms.
No boundedness or limit argument is required. This absolute-convergence statement has different
hypotheses from an ordered-convergence Abel theorem and is not compared to it by strength.

The substitution `u = z⁻¹` turns the transform into an ordinary power series
`∑' n, f n * u ^ n`. That identity is recorded here because it is the bridge to
inverse-transform and uniqueness results, which are developed separately.

The concrete sequences are the causal unit step and the causal geometric sequence. Both have an
absolute region of convergence computed exactly, not merely bounded: `‖z‖ > 1` for the step
and `‖z‖ > ‖a‖` for the geometric sequence with ratio `a ≠ 0`. The geometric transform is
obtained from the step transform through the `z`-domain scaling law rather than resummed.

Nothing here asserts that the absolute and conditional regions of convergence coincide. They do
not, and the witness separating them is in the companion regression file.

## ii. Key results

- `Physlib.ZTransform.norm_seriesTerm`: the term norm depends on `z` only through `‖z‖`.
- `Physlib.ZTransform.summable_seriesTerm_of_norm_le`: absolute convergence propagates outward
  in modulus, with a non-strict inequality.
- `Physlib.ZTransform.ROC_mem_of_mem_of_norm_le`: the absolute region of convergence is closed
  upward in modulus.
- `Physlib.ZTransform.IsExteriorOfCircle`: a set contains the exterior of some circle.
- `Physlib.ZTransform.isExteriorOfCircle_ROC_iff`: the absolute region of convergence contains
  the exterior of a circle exactly when it is nonempty.
- `Physlib.ZTransform.transform_inv`: the transform at `u⁻¹` is the power series in `u`.
- `Physlib.ZTransform.ROC_unitStep`, `Physlib.ZTransform.transform_unitStep`: the unit step.
- `Physlib.ZTransform.ROC_geometricSeq`, `Physlib.ZTransform.transform_geometricSeq`: the
  geometric sequence with ratio `a`.

## iii. Table of contents

- A. Absolute convergence depends only on the modulus
- B. The region of convergence as an exterior of a circle
- C. The transform as a power series in the reciprocal variable
- D. The unit step
- E. The geometric sequence

## iv. References

The predicate `IsExteriorOfCircle` keeps the `0 < R` form of Definition 19 (p. 893) in
U. Siddique, M. Y. Mahmoud, and S. Tahar, "Formal Analysis of Discrete-Time Systems using
z-Transform", Journal of Applied Logics 5(4), 2018, pp. 875-906. That source applies the
predicate to its ordered-convergence region. The results here instead concern Physlib's stronger
absolute region, so they are not literal restatements of the source's three region-shape lemmas.

Table 1 (p. 888) of the same paper supplies the geometric transform formulas, including the unit
step as ratio one. The exact absolute-region equalities proved here are Physlib results. A
textbook reference is A. V. Oppenheim and R. W. Schafer, *Discrete-Time Signal Processing*,
3rd ed., Pearson, 2010, chapter 3.

Two Physlib-specific results are recorded. First, `summable_seriesTerm_of_norm_le` propagates
absolute convergence under a non-strict modulus inequality, so the absolute region is also
proved invariant under rotation. This has different hypotheses from the source's ordered-region
exterior results and is not described as a strengthening of them. Second, the absolute regions
of the unit step and the geometric sequence are computed exactly as set equalities.

This file is neutral mathematics and imports no physics. It asserts no inverse transform, no
uniqueness, no stability, and no optical interpretation.

-/

@[expose] public section

namespace Physlib.ZTransform

noncomputable section

open Filter

/-!

## A. Absolute convergence depends only on the modulus

-/

/-- The norm of the `n`-th transform series term depends on `z` only through `‖z‖`. -/
lemma norm_seriesTerm (f : ℤ → ℂ) (z : ℂ) (n : ℕ) :
    ‖seriesTerm f z n‖ = ‖f n‖ * (‖z‖⁻¹) ^ n := by
  rw [seriesTerm, norm_mul, norm_pow, norm_inv]

/-- Absolute convergence of the transform series propagates outward in modulus. The modulus
inequality is not strict, so the conclusion also gives invariance under rotation. -/
lemma summable_seriesTerm_of_norm_le {f : ℤ → ℂ} {w z : ℂ}
    (hw : w ≠ 0) (hle : ‖w‖ ≤ ‖z‖)
    (hs : Summable (seriesTerm f w)) : Summable (seriesTerm f z) := by
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  refine Summable.of_norm_bounded (summable_norm_iff.mpr hs) fun n => ?_
  rw [norm_seriesTerm, norm_seriesTerm]
  gcongr

/-- The point `z` is nonzero whenever a nonzero `w` has modulus at most `‖z‖`. -/
lemma ne_zero_of_norm_le {w z : ℂ} (hw : w ≠ 0) (hle : ‖w‖ ≤ ‖z‖) : z ≠ 0 := by
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  exact norm_pos_iff.mp (hwpos.trans_le hle)

/-!

## B. The region of convergence as an exterior of a circle

-/

/-- The absolute region of convergence is closed upward in modulus. -/
lemma ROC_mem_of_mem_of_norm_le {f : ℤ → ℂ} {w z : ℂ}
    (hw : w ∈ ROC f) (hle : ‖w‖ ≤ ‖z‖) :
    z ∈ ROC f :=
  ⟨ne_zero_of_norm_le hw.1 hle, summable_seriesTerm_of_norm_le hw.1 hle hw.2⟩

/-- The absolute region of convergence is invariant under any change of `z` preserving the
modulus, in particular under rotation. -/
lemma ROC_mem_of_mem_of_norm_eq {f : ℤ → ℂ} {w z : ℂ}
    (hw : w ∈ ROC f) (heq : ‖w‖ = ‖z‖) :
    z ∈ ROC f :=
  ROC_mem_of_mem_of_norm_le hw heq.le

/-- A set of complex numbers contains the exterior of a circle of positive radius. -/
def IsExteriorOfCircle (s : Set ℂ) : Prop :=
  ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, R < ‖z‖ → z ∈ s

/-- The exterior of a circle is nonempty. -/
lemma IsExteriorOfCircle.nonempty {s : Set ℂ} (hs : IsExteriorOfCircle s) : s.Nonempty := by
  obtain ⟨R, hR, hmem⟩ := hs
  have hnorm : ‖((R + 1 : ℝ) : ℂ)‖ = R + 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  exact ⟨((R + 1 : ℝ) : ℂ), hmem _ (by rw [hnorm]; linarith)⟩

/-- A nonempty absolute region of convergence contains the exterior of a circle, whose radius may
be taken to be the modulus of any of its points. -/
lemma isExteriorOfCircle_ROC {f : ℤ → ℂ} {w : ℂ} (hw : w ∈ ROC f) :
    IsExteriorOfCircle (ROC f) :=
  ⟨‖w‖, norm_pos_iff.mpr hw.1, fun _ hz => ROC_mem_of_mem_of_norm_le hw hz.le⟩

/-- The absolute region of convergence contains the exterior of a circle exactly when it is
nonempty. -/
lemma isExteriorOfCircle_ROC_iff {f : ℤ → ℂ} :
    IsExteriorOfCircle (ROC f) ↔ (ROC f).Nonempty :=
  ⟨IsExteriorOfCircle.nonempty, fun ⟨_, hw⟩ => isExteriorOfCircle_ROC hw⟩

/-!

## C. The transform as a power series in the reciprocal variable

-/

/-- Under the substitution `u = z⁻¹` the transform is an ordinary power series with the sequence
values as coefficients. -/
lemma transform_inv (f : ℤ → ℂ) (u : ℂ) :
    transform f u⁻¹ = ∑' n : ℕ, f n * u ^ n := by
  rw [transform]
  exact tsum_congr fun n => by rw [seriesTerm, inv_inv]

/-- The reciprocal power series converges absolutely exactly on the reciprocal of the absolute
region of convergence. -/
lemma summable_pow_iff_inv_mem_ROC {f : ℤ → ℂ} {u : ℂ} (hu : u ≠ 0) :
    (Summable fun n : ℕ => f n * u ^ n) ↔ u⁻¹ ∈ ROC f := by
  have hterm : (fun n : ℕ => f n * u ^ n) = seriesTerm f u⁻¹ := by
    funext n
    rw [seriesTerm, inv_inv]
  rw [hterm]
  exact ⟨fun h => ⟨inv_ne_zero hu, h⟩, fun h => h.2⟩

/-!

## D. The unit step

-/

/-- The causal unit step sequence. -/
def unitStep : ℤ → ℂ := fun n => if 0 ≤ n then 1 else 0

/-- The unit step is causal. -/
lemma unitStep_isCausal : IsCausal unitStep := by
  intro n hn
  simp [unitStep, not_le.mpr hn]

/-- The transform series of the unit step is the geometric series in `z⁻¹`. -/
@[simp]
lemma seriesTerm_unitStep (z : ℂ) (n : ℕ) : seriesTerm unitStep z n = z⁻¹ ^ n := by
  simp [seriesTerm, unitStep]

/-- The transform series of the unit step converges absolutely exactly outside the unit
circle. -/
lemma summable_seriesTerm_unitStep_iff {z : ℂ} (hz : z ≠ 0) :
    Summable (seriesTerm unitStep z) ↔ 1 < ‖z‖ := by
  have hpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hfun : seriesTerm unitStep z = fun n : ℕ => z⁻¹ ^ n := funext (seriesTerm_unitStep z)
  rw [hfun, summable_geometric_iff_norm_lt_one, norm_inv, inv_lt_one₀ hpos]

/-- The absolute region of convergence of the unit step is the exterior of the unit circle. -/
lemma ROC_unitStep : ROC unitStep = {z : ℂ | 1 < ‖z‖} := by
  ext z
  constructor
  · rintro ⟨hz, hs⟩
    exact (summable_seriesTerm_unitStep_iff hz).mp hs
  · intro hz
    have hne : z ≠ 0 := by
      refine norm_pos_iff.mp ?_
      exact lt_trans zero_lt_one hz
    exact ⟨hne, (summable_seriesTerm_unitStep_iff hne).mpr hz⟩

/-- The unit step transforms to `(1 - z⁻¹)⁻¹` outside the unit circle. -/
lemma transform_unitStep {z : ℂ} (hz : 1 < ‖z‖) :
    transform unitStep z = (1 - z⁻¹)⁻¹ := by
  have hne : z ≠ 0 := norm_pos_iff.mp (lt_trans zero_lt_one hz)
  have hpos : 0 < ‖z‖ := norm_pos_iff.mpr hne
  have hlt : ‖z⁻¹‖ < 1 := by rw [norm_inv]; exact (inv_lt_one₀ hpos).mpr hz
  rw [transform]
  rw [tsum_congr (seriesTerm_unitStep z)]
  exact tsum_geometric_of_norm_lt_one hlt

/-!

## E. The geometric sequence

-/

/-- The causal geometric sequence with ratio `a`, obtained by scaling the unit step. -/
def geometricSeq (a : ℂ) : ℤ → ℂ := zScale a unitStep

/-- The geometric sequence takes the value `a ^ n` at every nonnegative index. -/
@[simp]
lemma geometricSeq_natCast (a : ℂ) (n : ℕ) : geometricSeq a (n : ℤ) = a ^ n := by
  simp [geometricSeq, ZTransform.zScale, unitStep]

/-- The geometric sequence is causal. -/
lemma geometricSeq_isCausal (a : ℂ) : IsCausal (geometricSeq a) :=
  unitStep_isCausal.zScale a

/-- The absolute region of convergence of a geometric sequence with nonzero ratio is the exterior
of the circle of radius `‖a‖`. -/
lemma ROC_geometricSeq {a : ℂ} (ha : a ≠ 0) :
    ROC (geometricSeq a) = {z : ℂ | ‖a‖ < ‖z‖} := by
  have hapos : 0 < ‖a‖ := norm_pos_iff.mpr ha
  rw [geometricSeq, ROC_zScale ha, ROC_unitStep]
  ext z
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, norm_div]
  rw [lt_div_iff₀ hapos, one_mul]

/-- A geometric sequence with ratio `a` transforms to `(1 - a * z⁻¹)⁻¹` outside the circle of
radius `‖a‖`. -/
lemma transform_geometricSeq {a z : ℂ} (ha : a ≠ 0) (hz : ‖a‖ < ‖z‖) :
    transform (geometricSeq a) z = (1 - a * z⁻¹)⁻¹ := by
  have hapos : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hstep : 1 < ‖z / a‖ := by
    rw [norm_div, lt_div_iff₀ hapos, one_mul]
    exact hz
  rw [geometricSeq, transform_zScale, transform_unitStep hstep, div_eq_mul_inv, mul_inv_rev,
    inv_inv]

end

end Physlib.ZTransform
