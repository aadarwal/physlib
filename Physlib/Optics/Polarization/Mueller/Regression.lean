/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Polarization.Mueller.Algebra

/-!
# Regression theorems for deterministic Mueller conventions

## i. Overview

The algebraically named matrix diag(1, I) detects the selected Stokes ordering, factor, third
coordinate sign, and Jones/Mueller action agreement without an optical-component interpretation.
Unguarded convention statement (review only): the matrix is assigned no handedness name. A
separate scalar regression distinguishes Jones amplitude scaling from Mueller intensity scaling.

## ii. Key results

## iii. Table of contents

- A. Sign- and scaling-sensitive regressions

## iv. References

-/

@[expose] public section

namespace Optics

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace JonesMatrix

/-!
## A. Sign- and scaling-sensitive regressions
-/

/-- The algebraic Jones matrix that fixes the first coordinate and multiplies the second by `I`.

This name records only the matrix action. Its interpretation as a particular oriented optical
retarder belongs in the later component layer. -/
def secondCoordinateIPhase : JonesMatrix :=
  ⟨!![1, 0; 0, Complex.I]⟩

/-- Multiplication of the second Jones coordinate by `I` is unitary. -/
lemma secondCoordinateIPhase_isUnitary : secondCoordinateIPhase.IsUnitary := by
  rw [IsUnitary, Matrix.mem_unitaryGroup_iff']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.star_eq_conjTranspose, secondCoordinateIPhase, Matrix.mul_apply]

/-- The second-coordinate `I` phase sends the diagonal Jones state to positive quadrature. -/
lemma secondCoordinateIPhase_act_diagonal :
    secondCoordinateIPhase.act JonesVector.diagonal = JonesVector.plusIQuadrature := by
  ext i
  fin_cases i
  · simp [secondCoordinateIPhase, act, JonesVector.diagonal,
      JonesVector.plusIQuadrature, JonesVector.ofComponents]
  · simp [secondCoordinateIPhase, act, JonesVector.diagonal,
      JonesVector.plusIQuadrature, JonesVector.ofComponents]
    ring

/-- The second-coordinate `I` phase sends positive quadrature to antidiagonal. -/
lemma secondCoordinateIPhase_act_plusIQuadrature :
    secondCoordinateIPhase.act JonesVector.plusIQuadrature = JonesVector.antidiagonal := by
  ext i
  fin_cases i
  · simp [secondCoordinateIPhase, act, JonesVector.antidiagonal,
      JonesVector.plusIQuadrature, JonesVector.ofComponents]
  · simp [secondCoordinateIPhase, act, JonesVector.antidiagonal,
      JonesVector.plusIQuadrature, JonesVector.ofComponents]
    calc
      Complex.I * (JonesVector.unitEqualAmplitude : ℂ) * Complex.I =
          Complex.I ^ 2 * JonesVector.unitEqualAmplitude := by ring
      _ = -JonesVector.unitEqualAmplitude := by rw [Complex.I_sq]; simp

/-- The second-coordinate `I` phase acts on Stokes data by
`(S₀, S₁, S₂, S₃) ↦ (S₀, S₁, -S₃, S₂)`. -/
lemma secondCoordinateIPhase_mueller_act (S : StokesVector) :
    secondCoordinateIPhase.mueller.act S =
      StokesVector.ofIntensityPolarization S.intensity
        (WithLp.toLp 2 ![S.polarization 0, -S.polarization 2, S.polarization 1]) := by
  apply selfAdjointStokesEquiv.symm.injective
  apply Subtype.ext
  change (secondCoordinateIPhase.mueller.act S).toSelfAdjoint.val =
    (StokesVector.ofIntensityPolarization S.intensity
      (WithLp.toLp 2 ![S.polarization 0, -S.polarization 2,
        S.polarization 1])).toSelfAdjoint.val
  rw [secondCoordinateIPhase.mueller_act_toSelfAdjoint,
    StokesVector.toSelfAdjoint_val_eq_matrix, StokesVector.toSelfAdjoint_val_eq_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [secondCoordinateIPhase, StokesVector.ofIntensityPolarization,
      StokesVector.intensity, StokesVector.polarization, Matrix.mul_apply,
      Matrix.conjTranspose_apply] <;> ring_nf
  all_goals rw [Complex.I_sq]
  all_goals ring

/-- The Mueller/Jones commuting square sends diagonal Stokes data to positive quadrature. -/
lemma secondCoordinateIPhase_mueller_diagonal :
    secondCoordinateIPhase.mueller.act JonesVector.diagonal.stokes =
      JonesVector.plusIQuadrature.stokes := by
  rw [secondCoordinateIPhase.mueller_jones, secondCoordinateIPhase_act_diagonal]

/-- The Mueller/Jones commuting square sends positive-quadrature Stokes data to antidiagonal. -/
lemma secondCoordinateIPhase_mueller_plusIQuadrature :
    secondCoordinateIPhase.mueller.act JonesVector.plusIQuadrature.stokes =
      JonesVector.antidiagonal.stokes := by
  rw [secondCoordinateIPhase.mueller_jones, secondCoordinateIPhase_act_plusIQuadrature]

/-- Scaling the identity Jones matrix by two scales its Mueller matrix by four. -/
lemma scale_two_identity_mueller :
    (identity.scale 2).mueller = MuellerMatrix.identity.scale 4 := by
  rw [mueller_scale, mueller_identity]
  norm_num [Complex.normSq]

end JonesMatrix

end

end Optics
