/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Mathlib.Analysis.Matrix.Order
public import Physlib.Mathematics.MatrixRank
public import Physlib.Optics.Polarization.Stokes

/-!
# The Poincare ball of polarization states

## i. Overview

This file identifies unit-intensity physical Stokes data, and equivalently unit-trace polarization
coherency data, with the closed unit ball in the three real polarization coordinates. Restricting
to unit intensity excludes zero coherency without assigning a polarization direction to it.

The equivalences here classify the entire closed ball. Determinant and matrix-rank results identify
its boundary with rank-one coherency and its interior with positive-definite, rank-two coherency.
The unit-Jones quotient description of the sphere is developed in a later part of the Poincare API.

## ii. Key results

- `PoincareBall`: the closed unit ball of three real polarization coordinates.
- `unitIntensityStokesPoincareEquiv`: unit-intensity physical Stokes data as the closed ball.
- `unitTraceCoherencyStokesEquiv`: unit-trace coherency as unit-intensity physical Stokes data.
- `unitTraceCoherencyPoincareEquiv`: unit-trace coherency as the closed Poincare ball.
- `PolarizationCoherency.rank_eq_one_iff_trace_pos_and_polarization_norm_eq_trace`: the exact
  positive-intensity boundary criterion for rank-one coherency.
- `UnitTracePolarizationCoherency.rank_eq_two_iff_poincare_norm_lt_one`: the rank-two interior
  classification of normalized coherency.

## iii. Table of contents

- A. The closed Poincare ball
- B. Unit-intensity physical Stokes data
- C. Unit-trace polarization coherency
- D. Determinant and rank classification
- E. Boundary and interior of the normalized Poincare ball

## iv. References

The normalization is fixed internally by the already-proved identity between Stokes intensity and
coherency trace. Circular-polarization handedness plays no role in this ball-level classification.
-/

@[expose] public section

namespace Optics

open Matrix
open scoped ComplexOrder

noncomputable section

/-!

## A. The closed Poincare ball

-/

/-- The three real coordinates of the Poincare polarization ball. -/
abbrev PoincareVector := EuclideanSpace ℝ (Fin 3)

/-- The closed unit ball of three real polarization coordinates. -/
abbrev PoincareBall := Metric.closedBall (0 : PoincareVector) 1

/-- The unit sphere forming the boundary of the Poincare ball. -/
abbrev PoincareSphere := Metric.sphere (0 : PoincareVector) 1

/-- The open unit ball forming the interior of the Poincare ball. -/
abbrev PoincareBallInterior := Metric.ball (0 : PoincareVector) 1

/-- The frontier of the closed Poincare ball is the Poincare sphere. -/
lemma frontier_poincareBall : frontier PoincareBall = PoincareSphere := by
  exact frontier_closedBall (0 : PoincareVector) one_ne_zero

/-- The topological interior of the closed Poincare ball is its open unit ball. -/
lemma interior_poincareBall : interior PoincareBall = PoincareBallInterior := by
  exact interior_closedBall (0 : PoincareVector) one_ne_zero

/-!

## B. Unit-intensity physical Stokes data

-/

/-- Physical Stokes data normalized to unit total intensity. -/
abbrev UnitIntensityStokesVector :=
  {S : PhysicalStokesVector // S.val.intensity = 1}

/-- Unit-intensity physical Stokes data is equivalent to the closed Poincare ball. -/
noncomputable def unitIntensityStokesPoincareEquiv :
    UnitIntensityStokesVector ≃ PoincareBall where
  toFun S := ⟨S.val.val.polarization, by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact S.val.property.trans_eq S.property⟩
  invFun p := ⟨⟨StokesVector.ofIntensityPolarization 1 p.val, by
    rw [StokesVector.IsPhysical, StokesVector.polarization_ofIntensityPolarization,
      StokesVector.intensity_ofIntensityPolarization]
    simpa only [Metric.mem_closedBall, dist_zero_right] using p.property⟩, by simp⟩
  left_inv S := by
    apply Subtype.ext
    apply Subtype.ext
    calc
      StokesVector.ofIntensityPolarization 1 S.val.val.polarization =
          StokesVector.ofIntensityPolarization S.val.val.intensity S.val.val.polarization := by
        exact congrArg
          (fun s₀ => StokesVector.ofIntensityPolarization s₀ S.val.val.polarization)
          S.property.symm
      _ = S.val.val := StokesVector.ofIntensityPolarization_intensity_polarization S.val.val
  right_inv p := by
    apply Subtype.ext
    rfl

/-- The ball coordinate of unit-intensity Stokes data is its polarization projection. -/
@[simp]
lemma unitIntensityStokesPoincareEquiv_apply_val (S : UnitIntensityStokesVector) :
    (unitIntensityStokesPoincareEquiv S).val = S.val.val.polarization := by
  rfl

/-- The raw Stokes data reconstructed from a ball point has unit intensity and that point's
polarization coordinates. -/
@[simp]
lemma unitIntensityStokesPoincareEquiv_symm_apply_val (p : PoincareBall) :
    (unitIntensityStokesPoincareEquiv.symm p).val.val =
      StokesVector.ofIntensityPolarization 1 p.val := by
  rfl

/-!

## C. Unit-trace polarization coherency

-/

/-- Polarization coherency normalized to unit trace. -/
abbrev UnitTracePolarizationCoherency :=
  {C : PolarizationCoherency // C.trace = 1}

/-- Unit-trace coherency is equivalent to unit-intensity physical Stokes data. -/
noncomputable def unitTraceCoherencyStokesEquiv :
    UnitTracePolarizationCoherency ≃ UnitIntensityStokesVector :=
  coherencyStokesEquiv.subtypeEquiv fun C => by simp

/-- Unit-trace polarization coherency is equivalent to the closed Poincare ball. -/
noncomputable def unitTraceCoherencyPoincareEquiv :
    UnitTracePolarizationCoherency ≃ PoincareBall :=
  unitTraceCoherencyStokesEquiv.trans unitIntensityStokesPoincareEquiv

/-- The ball coordinate of unit-trace coherency is its Stokes polarization projection. -/
@[simp]
lemma unitTraceCoherencyPoincareEquiv_apply_val (C : UnitTracePolarizationCoherency) :
    (unitTraceCoherencyPoincareEquiv C).val = C.val.stokes.polarization := by
  rfl

/-!

## D. Determinant and rank classification

-/

namespace PolarizationCoherency

/-- The determinant of polarization coherency is one quarter of the squared Stokes intensity
minus the squared polarization norm. -/
lemma det_eq_trace_sq_sub_polarization_norm_sq (C : PolarizationCoherency) :
    C.toMatrix.det =
      (((C.trace ^ 2 - ‖C.stokes.polarization‖ ^ 2) / 4 : ℝ) : ℂ) := by
  rw [← C.toSelfAdjoint_val, ← C.stokes_toSelfAdjoint,
    StokesVector.det_toSelfAdjoint, C.stokes_intensity_eq_trace]

/-- Polarization coherency has zero determinant exactly on the boundary of the physical Stokes
cone. This includes the zero-intensity origin. -/
lemma det_eq_zero_iff_polarization_norm_eq_trace (C : PolarizationCoherency) :
    C.toMatrix.det = 0 ↔ ‖C.stokes.polarization‖ = C.trace := by
  have hphysical : ‖C.stokes.polarization‖ ≤ C.trace := by
    simpa only [StokesVector.IsPhysical, C.stokes_intensity_eq_trace] using C.stokes_isPhysical
  rw [det_eq_trace_sq_sub_polarization_norm_sq]
  constructor
  · intro h
    have hr : (C.trace ^ 2 - ‖C.stokes.polarization‖ ^ 2) / 4 = 0 := by
      apply Complex.ofReal_injective
      simpa only [Complex.ofReal_zero] using h
    nlinarith [norm_nonneg C.stokes.polarization]
  · intro h
    rw [h]
    norm_num

/-- A positive-semidefinite polarization coherency matrix is zero exactly when its trace is zero. -/
lemma trace_eq_zero_iff_toMatrix_eq_zero (C : PolarizationCoherency) :
    C.trace = 0 ↔ C.toMatrix = 0 := by
  rw [← Complex.ofReal_inj, C.coe_trace, Complex.ofReal_zero]
  exact C.posSemidef.trace_eq_zero_iff

/-- Polarization coherency has matrix rank zero exactly when it has zero trace. -/
lemma rank_eq_zero_iff_trace_eq_zero (C : PolarizationCoherency) :
    C.toMatrix.rank = 0 ↔ C.trace = 0 := by
  rw [Matrix.rank_eq_zero_iff, ← C.trace_eq_zero_iff_toMatrix_eq_zero]

/-- Polarization coherency is positive definite exactly in the strict interior of its physical
Stokes cone. -/
lemma posDef_iff_polarization_norm_lt_trace (C : PolarizationCoherency) :
    C.toMatrix.PosDef ↔ ‖C.stokes.polarization‖ < C.trace := by
  have hphysical : ‖C.stokes.polarization‖ ≤ C.trace := by
    simpa only [StokesVector.IsPhysical, C.stokes_intensity_eq_trace] using C.stokes_isPhysical
  rw [C.posSemidef.posDef_iff_det_ne_zero]
  constructor
  · intro hdet
    apply lt_of_le_of_ne hphysical
    intro hboundary
    exact hdet ((det_eq_zero_iff_polarization_norm_eq_trace C).mpr hboundary)
  · intro hstrict hdet
    have hboundary := (det_eq_zero_iff_polarization_norm_eq_trace C).mp hdet
    exact (ne_of_lt hstrict) hboundary

/-- A polarization coherency matrix has full rank exactly when it is positive definite. -/
lemma rank_eq_two_iff_posDef (C : PolarizationCoherency) :
    C.toMatrix.rank = 2 ↔ C.toMatrix.PosDef := by
  simpa only [Fintype.card_fin] using
    (Matrix.rank_eq_card_iff_det_ne_zero C.toMatrix).trans
      C.posSemidef.posDef_iff_det_ne_zero.symm

/-- A polarization coherency matrix has full rank exactly in the strict interior of its physical
Stokes cone. -/
lemma rank_eq_two_iff_polarization_norm_lt_trace (C : PolarizationCoherency) :
    C.toMatrix.rank = 2 ↔ ‖C.stokes.polarization‖ < C.trace := by
  rw [rank_eq_two_iff_posDef, posDef_iff_polarization_norm_lt_trace]

/-- Polarization coherency has rank one exactly on the positive-intensity boundary of its physical
Stokes cone. -/
lemma rank_eq_one_iff_trace_pos_and_polarization_norm_eq_trace
    (C : PolarizationCoherency) :
    C.toMatrix.rank = 1 ↔
      0 < C.trace ∧ ‖C.stokes.polarization‖ = C.trace := by
  have hnonzero : C.toMatrix ≠ 0 ↔ 0 < C.trace := by
    constructor
    · intro hmatrix
      exact lt_of_le_of_ne C.trace_nonneg fun htrace =>
        hmatrix (C.trace_eq_zero_iff_toMatrix_eq_zero.mp htrace.symm)
    · intro htrace hmatrix
      have := C.trace_eq_zero_iff_toMatrix_eq_zero.mpr hmatrix
      linarith
  rw [Matrix.rank_eq_one_iff_ne_zero_and_det_eq_zero, hnonzero,
    det_eq_zero_iff_polarization_norm_eq_trace]

end PolarizationCoherency

/-!

## E. Boundary and interior of the normalized Poincare ball

-/

namespace UnitIntensityStokesVector

/-- Unit-intensity physical Stokes data maps to the Poincare sphere exactly when its reconstructed
matrix has zero determinant. -/
lemma poincare_mem_sphere_iff_det_eq_zero (S : UnitIntensityStokesVector) :
    (unitIntensityStokesPoincareEquiv S).val ∈ PoincareSphere ↔
      S.val.val.toSelfAdjoint.val.det = 0 := by
  rw [Metric.mem_sphere, dist_zero_right,
    unitIntensityStokesPoincareEquiv_apply_val,
    ← S.val.coherency_toMatrix,
    PolarizationCoherency.det_eq_zero_iff_polarization_norm_eq_trace,
    ← PolarizationCoherency.stokes_intensity_eq_trace S.val.coherency,
    S.val.coherency_stokes, S.property]

/-- Unit-intensity physical Stokes data maps to the Poincare-ball interior exactly when its
reconstructed matrix is positive definite. -/
lemma poincare_mem_interior_iff_posDef (S : UnitIntensityStokesVector) :
    (unitIntensityStokesPoincareEquiv S).val ∈ interior PoincareBall ↔
      S.val.val.toSelfAdjoint.val.PosDef := by
  rw [interior_poincareBall, Metric.mem_ball, dist_zero_right,
    unitIntensityStokesPoincareEquiv_apply_val,
    ← S.val.coherency_toMatrix,
    PolarizationCoherency.posDef_iff_polarization_norm_lt_trace,
    ← PolarizationCoherency.stokes_intensity_eq_trace S.val.coherency,
    S.val.coherency_stokes, S.property]

end UnitIntensityStokesVector

namespace UnitTracePolarizationCoherency

/-- A unit-trace coherency lies on the Poincare-ball boundary exactly when its determinant
vanishes. -/
lemma det_eq_zero_iff_poincare_norm_eq_one (C : UnitTracePolarizationCoherency) :
    C.val.toMatrix.det = 0 ↔ ‖(unitTraceCoherencyPoincareEquiv C).val‖ = 1 := by
  rw [unitTraceCoherencyPoincareEquiv_apply_val,
    PolarizationCoherency.det_eq_zero_iff_polarization_norm_eq_trace, C.property]

/-- A unit-trace coherency has rank one exactly on the Poincare-ball boundary. -/
lemma rank_eq_one_iff_poincare_norm_eq_one (C : UnitTracePolarizationCoherency) :
    C.val.toMatrix.rank = 1 ↔ ‖(unitTraceCoherencyPoincareEquiv C).val‖ = 1 := by
  rw [unitTraceCoherencyPoincareEquiv_apply_val,
    PolarizationCoherency.rank_eq_one_iff_trace_pos_and_polarization_norm_eq_trace, C.property]
  norm_num

/-- A unit-trace coherency is positive definite exactly in the strict Poincare-ball interior. -/
lemma posDef_iff_poincare_norm_lt_one (C : UnitTracePolarizationCoherency) :
    C.val.toMatrix.PosDef ↔ ‖(unitTraceCoherencyPoincareEquiv C).val‖ < 1 := by
  rw [unitTraceCoherencyPoincareEquiv_apply_val,
    PolarizationCoherency.posDef_iff_polarization_norm_lt_trace, C.property]

/-- A unit-trace coherency has rank two exactly in the strict Poincare-ball interior. -/
lemma rank_eq_two_iff_poincare_norm_lt_one (C : UnitTracePolarizationCoherency) :
    C.val.toMatrix.rank = 2 ↔ ‖(unitTraceCoherencyPoincareEquiv C).val‖ < 1 := by
  rw [unitTraceCoherencyPoincareEquiv_apply_val,
    PolarizationCoherency.rank_eq_two_iff_polarization_norm_lt_trace, C.property]

/-- A unit-trace coherency maps to the Poincare sphere exactly when its determinant vanishes. -/
lemma poincare_mem_sphere_iff_det_eq_zero (C : UnitTracePolarizationCoherency) :
    (unitTraceCoherencyPoincareEquiv C).val ∈ PoincareSphere ↔
      C.val.toMatrix.det = 0 := by
  rw [Metric.mem_sphere, dist_zero_right]
  exact (det_eq_zero_iff_poincare_norm_eq_one C).symm

/-- A unit-trace coherency maps to the Poincare sphere exactly when it has rank one. -/
lemma poincare_mem_sphere_iff_rank_eq_one (C : UnitTracePolarizationCoherency) :
    (unitTraceCoherencyPoincareEquiv C).val ∈ PoincareSphere ↔
      C.val.toMatrix.rank = 1 := by
  rw [Metric.mem_sphere, dist_zero_right]
  exact (rank_eq_one_iff_poincare_norm_eq_one C).symm

/-- A unit-trace coherency maps to the Poincare-ball interior exactly when it is positive
definite. -/
lemma poincare_mem_interior_iff_posDef (C : UnitTracePolarizationCoherency) :
    (unitTraceCoherencyPoincareEquiv C).val ∈ interior PoincareBall ↔
      C.val.toMatrix.PosDef := by
  rw [interior_poincareBall, Metric.mem_ball, dist_zero_right]
  exact (posDef_iff_poincare_norm_lt_one C).symm

/-- A unit-trace coherency maps to the Poincare-ball interior exactly when it has rank two. -/
lemma poincare_mem_interior_iff_rank_eq_two (C : UnitTracePolarizationCoherency) :
    (unitTraceCoherencyPoincareEquiv C).val ∈ interior PoincareBall ↔
      C.val.toMatrix.rank = 2 := by
  rw [interior_poincareBall, Metric.mem_ball, dist_zero_right]
  exact (rank_eq_two_iff_poincare_norm_lt_one C).symm

end UnitTracePolarizationCoherency

end

end Optics
