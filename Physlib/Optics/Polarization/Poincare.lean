/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Polarization.Stokes

/-!
# The Poincare ball of polarization states

## i. Overview

This file identifies unit-intensity physical Stokes data, and equivalently unit-trace polarization
coherency data, with the closed unit ball in the three real polarization coordinates. Restricting
to unit intensity excludes zero coherency without assigning a polarization direction to it.

The equivalences here classify the entire closed ball. Its boundary, matrix-rank classification,
and the unit-Jones quotient description of the sphere are developed in later sections of the
Poincare API.

## ii. Key results

- `PoincareBall`: the closed unit ball of three real polarization coordinates.
- `unitIntensityStokesPoincareEquiv`: unit-intensity physical Stokes data as the closed ball.
- `unitTraceCoherencyStokesEquiv`: unit-trace coherency as unit-intensity physical Stokes data.
- `unitTraceCoherencyPoincareEquiv`: unit-trace coherency as the closed Poincare ball.

## iii. Table of contents

- A. The closed Poincare ball
- B. Unit-intensity physical Stokes data
- C. Unit-trace polarization coherency

## iv. References

The normalization is fixed internally by the already-proved identity between Stokes intensity and
coherency trace. Circular-polarization handedness plays no role in this ball-level classification.
-/

@[expose] public section

namespace Optics

noncomputable section

/-!

## A. The closed Poincare ball

-/

/-- The three real coordinates of the Poincare polarization ball. -/
abbrev PoincareVector := EuclideanSpace ℝ (Fin 3)

/-- The closed unit ball of three real polarization coordinates. -/
abbrev PoincareBall := Metric.closedBall (0 : PoincareVector) 1

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

end

end Optics
