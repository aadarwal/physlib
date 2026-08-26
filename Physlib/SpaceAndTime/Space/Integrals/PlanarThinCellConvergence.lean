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
- `OrientedAffineHyperplane.dist_sidePoint_le`: a side sample stays within its tangential and
  normal offsets from the carrier point.

## iii. Table of contents

- A. Uniform bounds for normalized averages
- B. Convergence from eventual uniform control
- C. Shrinking planar sample geometry
- D. Trace and carrier-source averages

## iv. References

This is neutral analysis infrastructure for the E4b planar Maxwell derivation.
-/

@[expose] public section

open Filter
open Matrix
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

/-! ## C. Shrinking planar sample geometry -/

namespace OrientedAffineHyperplane

/-- A side sample lies no farther from its carrier point than the sum of the norms of its
tangential offset and its positive normal height. -/
lemma dist_sidePoint_le {d : ℕ} (plane : OrientedAffineHyperplane d) (side : Side)
    (x : plane.carrier) (offset : plane.tangentSubmodule) (height : ℝ)
    (hHeight : 0 < height) :
    dist ((plane.sidePoint side x offset height hHeight : plane.openHalfSpace side) : Space d)
        (x : Space d) ≤
      ‖(offset : EuclideanSpace ℝ (Fin d))‖ + height := by
  change dist
      (((offset : EuclideanSpace ℝ (Fin d)) + height • plane.sideNormalVector side) +ᵥ
        (x : Space d))
      (x : Space d) ≤ _
  rw [dist_vadd_left]
  calc
    ‖(offset : EuclideanSpace ℝ (Fin d)) + height • plane.sideNormalVector side‖ ≤
        ‖(offset : EuclideanSpace ℝ (Fin d))‖ +
          ‖height • plane.sideNormalVector side‖ := norm_add_le _ _
    _ = ‖(offset : EuclideanSpace ℝ (Fin d))‖ + height := by
      rw [norm_smul, plane.sideNormalVector_norm, mul_one, Real.norm_eq_abs,
        abs_of_pos hHeight]

/-- A tangential sample is exactly the norm of its offset away from its carrier point. -/
lemma dist_tangentPoint {d : ℕ} (plane : OrientedAffineHyperplane d)
    (x : plane.carrier) (offset : plane.tangentSubmodule) :
    dist ((plane.tangentPoint x offset : plane.carrier) : Space d) (x : Space d) =
      ‖(offset : EuclideanSpace ℝ (Fin d))‖ := by
  change dist
      ((offset : EuclideanSpace ℝ (Fin d)) +ᵥ (x : Space d))
      (x : Space d) = _
  exact dist_vadd_left _ _

end OrientedAffineHyperplane

/-! ## D. Trace and carrier-source averages -/

/-- A convergent function is uniformly close to its limit on any family of samples whose
ambient distance from the convergence point has a common envelope tending to zero. -/
private lemma eventually_uniform_of_tendsto_comap_nhds
    {X A Y B : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {inclusion : A → X} {center : X} {f : A → Y} {limit : Y}
    (hTendsto : Tendsto f (comap inclusion (nhds center)) (nhds limit))
    (sample : ℕ → B → A) (valid : ℕ → B → Prop) (bound : ℕ → ℝ)
    (hBound : Tendsto bound atTop (nhds 0))
    (hSample : ∀ scale point, valid scale point →
      dist (inclusion (sample scale point)) center ≤ bound scale) :
    ∀ ε > 0, ∀ᶠ scale in atTop,
      ∀ point, valid scale point → dist (f (sample scale point)) limit < ε := by
  intro ε hε
  have hEventually := (Metric.tendsto_nhds.mp hTendsto) ε hε
  rcases Filter.mem_comap.mp hEventually with ⟨set, hSet, hSetSubset⟩
  rcases Metric.mem_nhds_iff.mp hSet with ⟨δ, hδ, hBall⟩
  filter_upwards [(Metric.tendsto_nhds.mp hBound) δ hδ] with scale hScale
  intro point hValid
  apply hSetSubset
  apply hBall
  apply Metric.mem_ball.mpr
  refine lt_of_le_of_lt (hSample scale point hValid) ?_
  exact lt_of_le_of_lt (le_abs_self (bound scale)) (by
    simpa [Real.dist_eq] using hScale)

namespace PlanarThinLoopFamily

/-- The normalized selected-side long-edge average converges to the corresponding tangent
pairing of a genuine one-sided trace. -/
lemma sideLongEdgeAverage_tendsto_trace
    {plane : OrientedAffineHyperplane 3} {tangent : plane.tangentSubmodule}
    (loop : PlanarThinLoopFamily plane tangent) (side : OrientedAffineHyperplane.Side)
    {P : Type*} (field : plane.SideField side P (EuclideanSpace ℝ (Fin 3)))
    (trace : plane.BoundaryField P (EuclideanSpace ℝ (Fin 3)))
    (hTrace : plane.HasOneSidedTrace field trace) (parameter : P)
    (x : plane.carrier)
    (hIntegrable : ∀ scale, loop.SideLongEdgeIntegrable side field parameter x scale) :
    Tendsto (fun scale ↦ loop.sideLongEdgeAverage side field parameter x scale) atTop
      (nhds (inner ℝ (trace parameter x) (tangent : EuclideanSpace ℝ (Fin 3)))) := by
  have hScalar :
      Tendsto (fun y ↦ inner ℝ (field parameter y)
          (tangent : EuclideanSpace ℝ (Fin 3)))
        (plane.oneSidedNhds side x)
        (nhds (inner ℝ (trace parameter x) (tangent : EuclideanSpace ℝ (Fin 3)))) :=
    (hTrace parameter x).inner tendsto_const_nhds
  have hEnvelope :
      Tendsto (fun scale ↦
          loop.radius scale * ‖(tangent : EuclideanSpace ℝ (Fin 3))‖ +
            loop.halfThickness scale)
        atTop (nhds 0) := by
    convert (loop.radius_tendsto_zero.mul_const
      ‖(tangent : EuclideanSpace ℝ (Fin 3))‖).add loop.halfThickness_tendsto_zero using 1;
      simp
  have hUniformDist : ∀ ε > 0, ∀ᶠ scale in atTop,
      ∀ u, u ∈ Set.uIcc (-(loop.radius scale)) (loop.radius scale) →
        dist
            (inner ℝ
              (field parameter
                (plane.sidePoint side x (u • tangent) (loop.halfThickness scale)
                  (loop.halfThickness_pos scale)))
              (tangent : EuclideanSpace ℝ (Fin 3)))
            (inner ℝ (trace parameter x) (tangent : EuclideanSpace ℝ (Fin 3))) < ε := by
    apply eventually_uniform_of_tendsto_comap_nhds
      (inclusion := ((↑) : plane.openHalfSpace side → Space 3))
      (center := (x : Space 3))
      (f := fun y ↦ inner ℝ (field parameter y)
        (tangent : EuclideanSpace ℝ (Fin 3)))
      (limit := inner ℝ (trace parameter x) (tangent : EuclideanSpace ℝ (Fin 3)))
      (hTendsto := by
        simpa [OrientedAffineHyperplane.oneSidedNhds] using hScalar)
      (sample := fun scale u ↦
        plane.sidePoint side x (u • tangent) (loop.halfThickness scale)
          (loop.halfThickness_pos scale))
      (valid := fun scale u ↦
        u ∈ Set.uIcc (-(loop.radius scale)) (loop.radius scale))
      (bound := fun scale ↦
        loop.radius scale * ‖(tangent : EuclideanSpace ℝ (Fin 3))‖ +
          loop.halfThickness scale)
      hEnvelope
    intro scale u hu
    have hAbs : |u| ≤ loop.radius scale := by
      rw [Set.uIcc_of_le (by linarith [loop.radius_pos scale])] at hu
      exact abs_le.mpr hu
    calc
      dist
          (((plane.sidePoint side x (u • tangent) (loop.halfThickness scale)
            (loop.halfThickness_pos scale) : plane.openHalfSpace side)) : Space 3)
          (x : Space 3) ≤
          ‖((u • tangent : plane.tangentSubmodule) : EuclideanSpace ℝ (Fin 3))‖ +
            loop.halfThickness scale :=
        plane.dist_sidePoint_le side x (u • tangent) (loop.halfThickness scale)
          (loop.halfThickness_pos scale)
      _ = |u| * ‖(tangent : EuclideanSpace ℝ (Fin 3))‖ +
            loop.halfThickness scale := by
        congr 1
        change ‖u • (tangent : EuclideanSpace ℝ (Fin 3))‖ = _
        rw [norm_smul, Real.norm_eq_abs]
      _ ≤ loop.radius scale * ‖(tangent : EuclideanSpace ℝ (Fin 3))‖ +
            loop.halfThickness scale := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right hAbs (norm_nonneg _)) le_rfl
  apply tendsto_normalizedIntervalAverage loop.radius_pos hIntegrable
  intro ε hε
  filter_upwards [hUniformDist ε hε] with scale hScale
  intro u hu
  rw [← Real.dist_eq]
  exact (hScale u hu).le

/-- The normalized carrier line average of a spatially continuous tangent source converges to
its local pairing with the oriented spanning-surface normal. -/
lemma surfaceLineAverage_tendsto_of_continuousAt
    {plane : OrientedAffineHyperplane 3} {tangent : plane.tangentSubmodule}
    (loop : PlanarThinLoopFamily plane tangent)
    {P : Type*} (source : plane.BoundaryField P plane.tangentSubmodule)
    (parameter : P) (x : plane.carrier) (hSource : ContinuousAt (source parameter) x)
    (hIntegrable : ∀ scale, loop.SurfaceLineIntegrable source parameter x scale) :
    Tendsto (fun scale ↦ loop.surfaceLineAverage source parameter x scale) atTop
      (nhds (inner ℝ (source parameter x : EuclideanSpace ℝ (Fin 3))
        (plane.normalVector ⨯ₑ₃ (tangent : EuclideanSpace ℝ (Fin 3))))) := by
  let spanningNormal :=
    plane.normalVector ⨯ₑ₃ (tangent : EuclideanSpace ℝ (Fin 3))
  have hVector : ContinuousAt
      (fun y ↦ (source parameter y : EuclideanSpace ℝ (Fin 3))) x := by
    exact continuousAt_subtype_val.comp hSource
  have hScalar : ContinuousAt
      (fun y ↦ inner ℝ (source parameter y : EuclideanSpace ℝ (Fin 3)) spanningNormal)
      x := hVector.inner continuousAt_const
  have hEnvelope :
      Tendsto (fun scale ↦
          loop.radius scale * ‖(tangent : EuclideanSpace ℝ (Fin 3))‖)
        atTop (nhds 0) := by
    simpa using loop.radius_tendsto_zero.mul_const
      ‖(tangent : EuclideanSpace ℝ (Fin 3))‖
  have hUniformDist : ∀ ε > 0, ∀ᶠ scale in atTop,
      ∀ u, u ∈ Set.uIcc (-(loop.radius scale)) (loop.radius scale) →
        dist
            (inner ℝ
              (source parameter (plane.tangentPoint x (u • tangent)) :
                EuclideanSpace ℝ (Fin 3))
              spanningNormal)
            (inner ℝ (source parameter x : EuclideanSpace ℝ (Fin 3))
              spanningNormal) < ε := by
    apply eventually_uniform_of_tendsto_comap_nhds
      (inclusion := id)
      (center := x)
      (f := fun y ↦ inner ℝ (source parameter y : EuclideanSpace ℝ (Fin 3))
        spanningNormal)
      (limit := inner ℝ (source parameter x : EuclideanSpace ℝ (Fin 3))
        spanningNormal)
      (hTendsto := by
        rw [Filter.comap_id]
        exact hScalar.tendsto)
      (sample := fun _ u ↦ plane.tangentPoint x (u • tangent))
      (valid := fun scale u ↦
        u ∈ Set.uIcc (-(loop.radius scale)) (loop.radius scale))
      (bound := fun scale ↦
        loop.radius scale * ‖(tangent : EuclideanSpace ℝ (Fin 3))‖)
      hEnvelope
    intro scale u hu
    have hAbs : |u| ≤ loop.radius scale := by
      rw [Set.uIcc_of_le (by linarith [loop.radius_pos scale])] at hu
      exact abs_le.mpr hu
    rw [id_eq, Subtype.dist_eq, plane.dist_tangentPoint]
    change ‖u • (tangent : EuclideanSpace ℝ (Fin 3))‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hAbs (norm_nonneg _)
  apply tendsto_normalizedIntervalAverage loop.radius_pos hIntegrable
  intro ε hε
  filter_upwards [hUniformDist ε hε] with scale hScale
  intro u hu
  rw [← Real.dist_eq]
  exact (hScale u hu).le

end PlanarThinLoopFamily

namespace PlanarPillboxFamily

/-- Coordinates bounded by `radius` in the pillbox tangent frame give an offset of norm at most
`2 * radius`. -/
lemma norm_squareOffset_le_two_mul_radius {plane : OrientedAffineHyperplane 3}
    (pillbox : PlanarPillboxFamily plane) {radius u v : ℝ}
    (hU : |u| ≤ radius) (hV : |v| ≤ radius) :
    ‖(((u • pillbox.tangent + v • plane.quarterTurnTangent pillbox.tangent) :
      plane.tangentSubmodule) : EuclideanSpace ℝ (Fin 3))‖ ≤ 2 * radius := by
  have hTangent :
      ‖((u • pillbox.tangent : plane.tangentSubmodule) :
        EuclideanSpace ℝ (Fin 3))‖ ≤ radius := by
    change ‖u • (pillbox.tangent : EuclideanSpace ℝ (Fin 3))‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs, pillbox.tangent_norm, mul_one]
    exact hU
  have hQuarterTurn :
      ‖((v • plane.quarterTurnTangent pillbox.tangent : plane.tangentSubmodule) :
        EuclideanSpace ℝ (Fin 3))‖ ≤ radius := by
    change ‖v • (plane.quarterTurnTangent pillbox.tangent :
      EuclideanSpace ℝ (Fin 3))‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs, plane.norm_quarterTurnTangent,
      pillbox.tangent_norm, mul_one]
    exact hV
  calc
    ‖(((u • pillbox.tangent + v • plane.quarterTurnTangent pillbox.tangent) :
      plane.tangentSubmodule) : EuclideanSpace ℝ (Fin 3))‖ ≤
        ‖((u • pillbox.tangent : plane.tangentSubmodule) :
          EuclideanSpace ℝ (Fin 3))‖ +
        ‖((v • plane.quarterTurnTangent pillbox.tangent : plane.tangentSubmodule) :
          EuclideanSpace ℝ (Fin 3))‖ := norm_add_le _ _
    _ ≤ radius + radius := add_le_add hTangent hQuarterTurn
    _ = 2 * radius := by ring

/-- The normalized selected-side principal-face average converges to the normal pairing of a
genuine one-sided trace. -/
lemma sideFaceAverage_tendsto_trace {plane : OrientedAffineHyperplane 3}
    (pillbox : PlanarPillboxFamily plane) (side : OrientedAffineHyperplane.Side)
    {P : Type*} (field : plane.SideField side P (EuclideanSpace ℝ (Fin 3)))
    (trace : plane.BoundaryField P (EuclideanSpace ℝ (Fin 3)))
    (hTrace : plane.HasOneSidedTrace field trace) (parameter : P)
    (x : plane.carrier)
    (hIntegrable : ∀ scale, pillbox.SideFaceIntegrable side field parameter x scale) :
    Tendsto (fun scale ↦ pillbox.sideFaceAverage side field parameter x scale) atTop
      (nhds (inner ℝ plane.normalVector (trace parameter x))) := by
  have hScalar :
      Tendsto (fun y ↦ inner ℝ plane.normalVector (field parameter y))
        (plane.oneSidedNhds side x)
        (nhds (inner ℝ plane.normalVector (trace parameter x))) :=
    tendsto_const_nhds.inner (hTrace parameter x)
  have hEnvelope :
      Tendsto (fun scale ↦ 2 * pillbox.radius scale + pillbox.halfThickness scale)
        atTop (nhds 0) := by
    simpa using (pillbox.radius_tendsto_zero.const_mul 2).add
      pillbox.halfThickness_tendsto_zero
  have hUniformPair : ∀ ε > 0, ∀ᶠ scale in atTop,
      ∀ point : ℝ × ℝ,
        point.1 ∈ Set.uIcc (-(pillbox.radius scale)) (pillbox.radius scale) ∧
            point.2 ∈ Set.uIcc (-(pillbox.radius scale)) (pillbox.radius scale) →
          dist
              (inner ℝ plane.normalVector
                (field parameter
                  (plane.sidePoint side x
                    (point.1 • pillbox.tangent +
                      point.2 • plane.quarterTurnTangent pillbox.tangent)
                    (pillbox.halfThickness scale) (pillbox.halfThickness_pos scale))))
              (inner ℝ plane.normalVector (trace parameter x)) < ε := by
    apply eventually_uniform_of_tendsto_comap_nhds
      (inclusion := ((↑) : plane.openHalfSpace side → Space 3))
      (center := (x : Space 3))
      (f := fun y ↦ inner ℝ plane.normalVector (field parameter y))
      (limit := inner ℝ plane.normalVector (trace parameter x))
      (hTendsto := by
        simpa [OrientedAffineHyperplane.oneSidedNhds] using hScalar)
      (sample := fun scale (point : ℝ × ℝ) ↦
        plane.sidePoint side x
          (point.1 • pillbox.tangent +
            point.2 • plane.quarterTurnTangent pillbox.tangent)
          (pillbox.halfThickness scale) (pillbox.halfThickness_pos scale))
      (valid := fun scale (point : ℝ × ℝ) ↦
        point.1 ∈ Set.uIcc (-(pillbox.radius scale)) (pillbox.radius scale) ∧
          point.2 ∈ Set.uIcc (-(pillbox.radius scale)) (pillbox.radius scale))
      (bound := fun scale ↦ 2 * pillbox.radius scale + pillbox.halfThickness scale)
      hEnvelope
    intro scale point hPoint
    rcases point with ⟨u, v⟩
    have hAbsU : |u| ≤ pillbox.radius scale := by
      rw [Set.uIcc_of_le (by linarith [pillbox.radius_pos scale])] at hPoint
      exact abs_le.mpr hPoint.1
    have hAbsV : |v| ≤ pillbox.radius scale := by
      rw [Set.uIcc_of_le (by linarith [pillbox.radius_pos scale])] at hPoint
      exact abs_le.mpr hPoint.2
    calc
      dist
          (((plane.sidePoint side x
            (u • pillbox.tangent + v • plane.quarterTurnTangent pillbox.tangent)
            (pillbox.halfThickness scale) (pillbox.halfThickness_pos scale) :
              plane.openHalfSpace side)) : Space 3)
          (x : Space 3) ≤
          ‖(((u • pillbox.tangent + v • plane.quarterTurnTangent pillbox.tangent) :
            plane.tangentSubmodule) : EuclideanSpace ℝ (Fin 3))‖ +
            pillbox.halfThickness scale :=
        plane.dist_sidePoint_le side x _ _ (pillbox.halfThickness_pos scale)
      _ ≤ 2 * pillbox.radius scale + pillbox.halfThickness scale := by
        exact add_le_add
          (pillbox.norm_squareOffset_le_two_mul_radius hAbsU hAbsV) le_rfl
  have hUniformDist : ∀ ε > 0, ∀ᶠ scale in atTop,
      ∀ u, u ∈ Set.uIcc (-(pillbox.radius scale)) (pillbox.radius scale) →
        ∀ v, v ∈ Set.uIcc (-(pillbox.radius scale)) (pillbox.radius scale) →
          dist
              (inner ℝ plane.normalVector
                (field parameter
                  (plane.sidePoint side x
                    (u • pillbox.tangent +
                      v • plane.quarterTurnTangent pillbox.tangent)
                    (pillbox.halfThickness scale) (pillbox.halfThickness_pos scale))))
              (inner ℝ plane.normalVector (trace parameter x)) < ε := by
    intro ε hε
    filter_upwards [hUniformPair ε hε] with scale hScale
    intro u hu v hv
    exact hScale (u, v) ⟨hu, hv⟩
  apply tendsto_normalizedSquareAverage pillbox.radius_pos hIntegrable
  intro ε hε
  filter_upwards [hUniformDist ε hε] with scale hScale
  intro u hu v hv
  rw [← Real.dist_eq]
  exact (hScale u hu v hv).le

/-- The normalized carrier-face average of a spatially continuous scalar source converges to
its value at the carrier point. -/
lemma surfaceFaceAverage_tendsto_of_continuousAt
    {plane : OrientedAffineHyperplane 3} (pillbox : PlanarPillboxFamily plane)
    {P : Type*} (source : plane.BoundaryField P ℝ) (parameter : P)
    (x : plane.carrier) (hSource : ContinuousAt (source parameter) x)
    (hIntegrable : ∀ scale, pillbox.SurfaceFaceIntegrable source parameter x scale) :
    Tendsto (fun scale ↦ pillbox.surfaceFaceAverage source parameter x scale) atTop
      (nhds (source parameter x)) := by
  have hEnvelope : Tendsto (fun scale ↦ 2 * pillbox.radius scale) atTop (nhds 0) := by
    simpa using pillbox.radius_tendsto_zero.const_mul 2
  have hUniformPair : ∀ ε > 0, ∀ᶠ scale in atTop,
      ∀ point : ℝ × ℝ,
        point.1 ∈ Set.uIcc (-(pillbox.radius scale)) (pillbox.radius scale) ∧
            point.2 ∈ Set.uIcc (-(pillbox.radius scale)) (pillbox.radius scale) →
          dist
              (source parameter
                (plane.tangentPoint x
                  (point.1 • pillbox.tangent +
                    point.2 • plane.quarterTurnTangent pillbox.tangent)))
              (source parameter x) < ε := by
    apply eventually_uniform_of_tendsto_comap_nhds
      (inclusion := id)
      (center := x)
      (f := source parameter)
      (limit := source parameter x)
      (hTendsto := by
        rw [Filter.comap_id]
        exact hSource.tendsto)
      (sample := fun _ (point : ℝ × ℝ) ↦
        plane.tangentPoint x
          (point.1 • pillbox.tangent +
            point.2 • plane.quarterTurnTangent pillbox.tangent))
      (valid := fun scale (point : ℝ × ℝ) ↦
        point.1 ∈ Set.uIcc (-(pillbox.radius scale)) (pillbox.radius scale) ∧
          point.2 ∈ Set.uIcc (-(pillbox.radius scale)) (pillbox.radius scale))
      (bound := fun scale ↦ 2 * pillbox.radius scale)
      hEnvelope
    intro scale point hPoint
    rcases point with ⟨u, v⟩
    have hAbsU : |u| ≤ pillbox.radius scale := by
      rw [Set.uIcc_of_le (by linarith [pillbox.radius_pos scale])] at hPoint
      exact abs_le.mpr hPoint.1
    have hAbsV : |v| ≤ pillbox.radius scale := by
      rw [Set.uIcc_of_le (by linarith [pillbox.radius_pos scale])] at hPoint
      exact abs_le.mpr hPoint.2
    rw [id_eq, Subtype.dist_eq, plane.dist_tangentPoint]
    exact pillbox.norm_squareOffset_le_two_mul_radius hAbsU hAbsV
  have hUniformDist : ∀ ε > 0, ∀ᶠ scale in atTop,
      ∀ u, u ∈ Set.uIcc (-(pillbox.radius scale)) (pillbox.radius scale) →
        ∀ v, v ∈ Set.uIcc (-(pillbox.radius scale)) (pillbox.radius scale) →
          dist
              (source parameter
                (plane.tangentPoint x
                  (u • pillbox.tangent +
                    v • plane.quarterTurnTangent pillbox.tangent)))
              (source parameter x) < ε := by
    intro ε hε
    filter_upwards [hUniformPair ε hε] with scale hScale
    intro u hu v hv
    exact hScale (u, v) ⟨hu, hv⟩
  apply tendsto_normalizedSquareAverage pillbox.radius_pos hIntegrable
  intro ε hε
  filter_upwards [hUniformDist ε hε] with scale hScale
  intro u hu v hv
  rw [← Real.dist_eq]
  exact (hScale u hu v hv).le

end PlanarPillboxFamily

end
end Space
