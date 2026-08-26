/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.SpaceAndTime.Space.Integrals.PlanarThinCell

/-!
# Convergence of planar thin-cell averages

## i. Overview

This file supplies the analytic estimates that turn local uniform control on shrinking planar
cells into convergence of the normalized interval and square averages defined in
`Space.Integrals.PlanarThinCell`. Integrability remains explicit, so Mathlib's totalized integral
cannot create a spurious zero value.

The estimates are neutral: they mention neither Maxwell fields nor boundary laws. Later sections
specialize them to genuine one-sided traces and continuous carrier sources.

## ii. Key results

- `abs_normalizedIntervalAverage_sub_le`: a uniform interval error bounds the average error.
- `abs_normalizedSquareAverage_sub_le`: the corresponding iterated-square estimate.
- `tendsto_normalizedIntervalAverage`: convergence from eventual uniform control.
- `tendsto_normalizedSquareAverage`: convergence of shrinking square averages.

## iii. Table of contents

- A. Uniform bounds for normalized averages
- B. Convergence from eventual uniform control

## iv. References

This is neutral analysis infrastructure for the E4b planar Maxwell derivation.
-/

@[expose] public section

open Filter
open scoped Interval

namespace Space

noncomputable section

/-! ## A. Uniform bounds for normalized averages -/

/-- A pointwise error bound on a nondegenerate interval bounds the error of its normalized
average. -/
lemma abs_normalizedIntervalAverage_sub_le {radius error limit : ℝ} {f : ℝ → ℝ}
    (hRadius : 0 < radius) (hIntegrable : SymmetricIntervalIntegrable radius f)
    (hBound : ∀ u ∈ Set.uIcc (-radius) radius, |f u - limit| ≤ error) :
    |normalizedIntervalAverage radius f - limit| ≤ error := by
  have hTwoRadius : 0 < 2 * radius := mul_pos two_pos hRadius
  have hConstant :
      ∫ _ in -radius..radius, limit = (2 * radius) * limit := by
    rw [intervalIntegral.integral_const]
    ring
  have hIntegral :
      |(∫ u in -radius..radius, (f u - limit))| ≤ error * (2 * radius) := by
    have hNorm := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun u ↦ f u - limit)
      (fun u hu ↦ hBound u (Set.uIoc_subset_uIcc hu))
    calc
      |(∫ u in -radius..radius, (f u - limit))| ≤
          error * |radius - -radius| := by
        simpa [Real.norm_eq_abs] using hNorm
      _ = error * (2 * radius) := by
        rw [abs_of_pos]
        · ring
        · linarith
  rw [normalizedIntervalAverage]
  have hAverageSub :
      (2 * radius)⁻¹ * (∫ u in -radius..radius, f u) - limit =
        (2 * radius)⁻¹ * (∫ u in -radius..radius, (f u - limit)) := by
    rw [intervalIntegral.integral_sub hIntegrable intervalIntegrable_const, hConstant]
    field_simp [hTwoRadius.ne']
  rw [hAverageSub]
  rw [abs_mul, abs_inv, abs_of_pos hTwoRadius]
  calc
    (2 * radius)⁻¹ * |(∫ u in -radius..radius, (f u - limit))| ≤
        (2 * radius)⁻¹ * (error * (2 * radius)) := by
      exact mul_le_mul_of_nonneg_left hIntegral (inv_nonneg.mpr hTwoRadius.le)
    _ = error := by field_simp

/-- A uniform error bound on a square bounds the error of its iterated normalized average. -/
lemma abs_normalizedSquareAverage_sub_le {radius error limit : ℝ}
    {f : ℝ → ℝ → ℝ} (hRadius : 0 < radius)
    (hIntegrable : IteratedSquareIntegrable radius f)
    (hBound : ∀ u ∈ Set.uIcc (-radius) radius,
      ∀ v ∈ Set.uIcc (-radius) radius, |f u v - limit| ≤ error) :
    |normalizedSquareAverage radius f - limit| ≤ error := by
  apply abs_normalizedIntervalAverage_sub_le hRadius hIntegrable.2
  intro u hu
  exact abs_normalizedIntervalAverage_sub_le hRadius (hIntegrable.1 u)
    (hBound u hu)

/-! ## B. Convergence from eventual uniform control -/

/-- Normalized averages over positive shrinking intervals converge when their integrands are
eventually uniformly close to the proposed limit. -/
lemma tendsto_normalizedIntervalAverage {radius : ℕ → ℝ} {f : ℕ → ℝ → ℝ}
    {limit : ℝ} (hRadius : ∀ scale, 0 < radius scale)
    (hIntegrable : ∀ scale, SymmetricIntervalIntegrable (radius scale) (f scale))
    (hUniform : ∀ ε > 0, ∀ᶠ scale in atTop,
      ∀ u ∈ Set.uIcc (-(radius scale)) (radius scale),
        |f scale u - limit| ≤ ε) :
    Tendsto (fun scale ↦ normalizedIntervalAverage (radius scale) (f scale))
      atTop (nhds limit) := by
  refine Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
  filter_upwards [hUniform (ε / 2) (half_pos hε)] with scale hScale
  rw [Real.dist_eq]
  exact lt_of_le_of_lt
    (abs_normalizedIntervalAverage_sub_le (hRadius scale) (hIntegrable scale) hScale)
    (half_lt_self hε)

/-- Normalized averages over positive shrinking squares converge when their integrands are
eventually uniformly close to the proposed limit. -/
lemma tendsto_normalizedSquareAverage {radius : ℕ → ℝ}
    {f : ℕ → ℝ → ℝ → ℝ} {limit : ℝ}
    (hRadius : ∀ scale, 0 < radius scale)
    (hIntegrable : ∀ scale, IteratedSquareIntegrable (radius scale) (f scale))
    (hUniform : ∀ ε > 0, ∀ᶠ scale in atTop,
      ∀ u ∈ Set.uIcc (-(radius scale)) (radius scale),
        ∀ v ∈ Set.uIcc (-(radius scale)) (radius scale),
          |f scale u v - limit| ≤ ε) :
    Tendsto (fun scale ↦ normalizedSquareAverage (radius scale) (f scale))
      atTop (nhds limit) := by
  refine Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
  filter_upwards [hUniform (ε / 2) (half_pos hε)] with scale hScale
  rw [Real.dist_eq]
  exact lt_of_le_of_lt
    (abs_normalizedSquareAverage_sub_le (hRadius scale) (hIntegrable scale) hScale)
    (half_lt_self hε)

end
end Space
