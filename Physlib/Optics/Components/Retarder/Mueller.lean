/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Components.Retarder.Basic
public import Physlib.Optics.Polarization.Mueller.Basic
public import Physlib.Optics.Polarization.RelativePhaseStokes

/-!
# Mueller representation of an ideal linear retarder

## i. Overview

This file derives the deterministic Mueller representation of the ideal linear retarder from its
public Jones matrix. The total Stokes intensity coordinate is fixed, while the three polarization
coordinates are acted on by one explicit real `3 × 3` block.

For `a = cos (2 • axis)`, `b = sin (2 • axis)`, `c = cos retardance`, and
`s = sin retardance`, the sign-sensitive entries are

`[[a ^ 2 + c * b ^ 2, (1 - c) * a * b, -s * b],
  [(1 - c) * a * b, b ^ 2 + c * a ^ 2, s * a], [s * b, -s * a, c]]`.

This algebraic sign pattern follows from the Jones eigenvalue `exp (-I * retardance)` and the
established third Stokes coordinate. Unguarded convention statement (review only): no
observer-dependent Poincare-sphere orientation or circular-handedness name is assigned here.
No electromagnetic irradiance, Poynting flux, or modal-power interpretation is assigned either.

## ii. Key results

- `JonesMatrix.linearRetarderPolarizationBlock`: the exact real polarization block.
- `JonesMatrix.linearRetarder_mueller_entries`: the induced block-diagonal Mueller matrix.
- `JonesMatrix.linearRetarder_mueller_act`: the arbitrary raw-Stokes action.
- `JonesMatrix.linearRetarder_act_stokes`: agreement with arbitrary Jones input.
- `JonesMatrix.linearRetarder_map_stokes`: agreement with arbitrary coherency input.

## iii. Table of contents

- A. Polarization block
- B. Induced Mueller matrix and arbitrary action
- C. Connected Jones and coherency descriptions

## iv. References

The formulas are derived from the public Jones retarder API and deterministic
Jones/coherency/Mueller commuting squares.
-/

@[expose] public section

namespace Optics

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace JonesMatrix

/-!

## A. Polarization block
-/

/-- The `3 × 3` polarization-coordinate block induced by an ideal linear retarder. -/
def linearRetarderPolarizationBlock (axis retardance : Real.Angle) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  let a := Real.Angle.cos (2 • axis)
  let b := Real.Angle.sin (2 • axis)
  let c := Real.Angle.cos retardance
  let s := Real.Angle.sin retardance
  !![a ^ 2 + c * b ^ 2, (1 - c) * a * b, -s * b;
    (1 - c) * a * b, b ^ 2 + c * a ^ 2, s * a;
    s * b, -s * a, c]

private lemma angle_sin_sq_complex (angle : Real.Angle) :
    (Real.Angle.sin angle : ℂ) ^ 2 =
      1 - (Real.Angle.cos angle : ℂ) ^ 2 := by
  have htrig : (Real.Angle.cos angle : ℂ) ^ 2 +
      (Real.Angle.sin angle : ℂ) ^ 2 = 1 := by
    exact_mod_cast angle.cos_sq_add_sin_sq
  linear_combination htrig

private lemma angle_sin_cube_complex (angle : Real.Angle) :
    (Real.Angle.sin angle : ℂ) ^ 3 =
      (Real.Angle.sin angle : ℂ) *
        (1 - (Real.Angle.cos angle : ℂ) ^ 2) := by
  calc
    (Real.Angle.sin angle : ℂ) ^ 3 =
        (Real.Angle.sin angle : ℂ) *
          (Real.Angle.sin angle : ℂ) ^ 2 := by ring
    _ = _ := by rw [angle_sin_sq_complex]

private lemma angle_sin_fourth_complex (angle : Real.Angle) :
    (Real.Angle.sin angle : ℂ) ^ 4 =
      (1 - (Real.Angle.cos angle : ℂ) ^ 2) ^ 2 := by
  calc
    (Real.Angle.sin angle : ℂ) ^ 4 =
        ((Real.Angle.sin angle : ℂ) ^ 2) ^ 2 := by ring
    _ = _ := by rw [angle_sin_sq_complex]

/-!

## B. Induced Mueller matrix and arbitrary action
-/

/-- An ideal linear retarder fixes raw Stokes intensity and applies its polarization block to the
remaining three coordinates. -/
lemma linearRetarder_mueller_act (axis retardance : Real.Angle) (S : StokesVector) :
    (linearRetarder axis retardance).mueller.act S =
      StokesVector.ofIntensityPolarization S.intensity
        (Matrix.toLpLin 2 2 (linearRetarderPolarizationBlock axis retardance)
          S.polarization) := by
  apply selfAdjointStokesEquiv.symm.injective
  apply Subtype.ext
  change ((linearRetarder axis retardance).mueller.act S).toSelfAdjoint.val =
    (StokesVector.ofIntensityPolarization S.intensity
      (Matrix.toLpLin 2 2 (linearRetarderPolarizationBlock axis retardance)
        S.polarization)).toSelfAdjoint.val
  rw [(linearRetarder axis retardance).mueller_act_toSelfAdjoint,
    StokesVector.toSelfAdjoint_val_eq_matrix,
    StokesVector.toSelfAdjoint_val_eq_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.toLpLin_apply, linearRetarderPolarizationBlock,
      linearRetarder, JonesVector.linearPolarization, Matrix.vecMulVec,
      StokesVector.ofIntensityPolarization, StokesVector.intensity,
      StokesVector.polarization, Matrix.mul_apply, Matrix.vecHead,
      Matrix.vecTail, Fin.sum_univ_two,
      linearRetarderPhase_eq_cos_sub_sin_mul_I,
      two_nsmul, Real.Angle.cos_add, Real.Angle.sin_add] <;>
    ring_nf
  all_goals rw [Complex.I_sq]
  all_goals rw [angle_sin_sq_complex axis, angle_sin_cube_complex axis,
    angle_sin_fourth_complex axis, angle_sin_sq_complex retardance]
  all_goals ring

/-- The induced Mueller matrix of a linear retarder is block diagonal, fixing intensity and
acting on polarization coordinates by `linearRetarderPolarizationBlock`. -/
lemma linearRetarder_mueller_entries (axis retardance : Real.Angle) :
    (linearRetarder axis retardance).mueller.entries =
      Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 0
        (linearRetarderPolarizationBlock axis retardance) := by
  ext i j
  rw [mueller_apply]
  have h := congrArg (fun S : StokesVector ↦ S i)
    (linearRetarder_mueller_act axis retardance (EuclideanSpace.single j 1))
  rcases i with i | i <;> rcases j with j | j
  all_goals fin_cases i <;> fin_cases j
  all_goals
    simpa [MuellerMatrix.act_apply, Matrix.toLpLin_apply,
      linearRetarderPolarizationBlock, StokesVector.ofIntensityPolarization,
      StokesVector.intensity, StokesVector.polarization,
      Matrix.fromBlocks, Matrix.vecHead, Matrix.vecTail,
      Fin.sum_univ_three] using h

/-!

## C. Connected Jones and coherency descriptions
-/

/-- The Stokes data of an arbitrary Jones input transformed by a retarder has the same explicit
polarization-block action as its induced Mueller description. -/
lemma linearRetarder_act_stokes (axis retardance : Real.Angle) (J : JonesVector) :
    ((linearRetarder axis retardance).act J).stokes =
      StokesVector.ofIntensityPolarization J.intensity
        (Matrix.toLpLin 2 2 (linearRetarderPolarizationBlock axis retardance)
          J.stokes.polarization) := by
  rw [← (linearRetarder axis retardance).mueller_jones,
    linearRetarder_mueller_act, JonesVector.stokes_intensity_eq_intensity]

/-- The Stokes data of arbitrary polarization coherency transformed by a retarder has the same
explicit polarization-block action as its induced Mueller description. -/
lemma linearRetarder_map_stokes (axis retardance : Real.Angle)
    (C : PolarizationCoherency) :
    PolarizationCoherency.stokes
        (C.map (linearRetarder axis retardance).entries) =
      StokesVector.ofIntensityPolarization C.trace
        (Matrix.toLpLin 2 2 (linearRetarderPolarizationBlock axis retardance)
          C.stokes.polarization) := by
  rw [← (linearRetarder axis retardance).mueller_coherency,
    linearRetarder_mueller_act,
    PolarizationCoherency.stokes_intensity_eq_trace]

/-- At zero axis, the Mueller action subtracts retardance from the equal-amplitude relative-phase
family and produces its exact Stokes direction. -/
lemma linearRetarder_zero_axis_mueller_equalAmplitudeRelativePhase
    (retardance relativePhase : Real.Angle) :
    (linearRetarder 0 retardance).mueller.act
        (JonesVector.equalAmplitudeRelativePhase relativePhase).stokes =
      StokesVector.ofIntensityPolarization 1
        (StokesVector.equalAmplitudeRelativePhaseDirection
          (relativePhase - retardance)) := by
  rw [(linearRetarder 0 retardance).mueller_jones,
    linearRetarder_zero_axis_act_equalAmplitudeRelativePhase,
    JonesVector.stokes_equalAmplitudeRelativePhase]

end JonesMatrix

end

end Optics
