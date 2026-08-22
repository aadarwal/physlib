/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Physlib.Optics.Polarization.Basic

/-!
# Equal-amplitude relative-phase Jones states

## i. Overview

This file defines a normalized one-parameter family of Jones states whose two coordinate
amplitudes have equal magnitude and whose second coordinate has a declared relative phase. The
family includes diagonal, antidiagonal, and the two algebraic quadrature states, while assigning
no observer-dependent circular-polarization handedness.

Generic phases in this family provide selected elliptical states for exact retarder calculations.
The definition concerns raw Jones amplitudes, not electromagnetic irradiance or modal power.

## ii. Key results

- `JonesVector.equalAmplitudeRelativePhase`: the normalized relative-phase family.
- `JonesVector.intensity_equalAmplitudeRelativePhase`: its squared Jones intensity is one.
- The four canonical phase regressions at `0`, `π`, and `±π / 2`.

## iii. Table of contents

- A. Relative-phase family
- B. Canonical phases

## iv. References

The construction uses the existing Jones-coordinate and `Real.Angle` conventions.
-/

@[expose] public section

namespace Optics

noncomputable section

namespace JonesVector

/-!

## A. Relative-phase family
-/

/-- The unit-intensity Jones state with equal coordinate magnitudes and the declared phase of the
second coordinate relative to the first. -/
def equalAmplitudeRelativePhase (relativePhase : Real.Angle) : JonesVector :=
  ofComponents unitEqualAmplitude
    ((relativePhase.toCircle : ℂ) * unitEqualAmplitude)

/-- Every equal-amplitude relative-phase state has unit squared Jones intensity. -/
@[simp]
lemma intensity_equalAmplitudeRelativePhase (relativePhase : Real.Angle) :
    (equalAmplitudeRelativePhase relativePhase).intensity = 1 := by
  rw [intensity_eq_sum_normSq, Fin.sum_univ_two]
  simp only [equalAmplitudeRelativePhase, ofComponents_zero, ofComponents_one,
    Complex.normSq_mul, Complex.normSq_ofReal]
  rw [← Complex.sq_norm, Circle.norm_coe, one_pow, one_mul]
  norm_num [unitEqualAmplitude_mul_self]

/-!

## B. Canonical phases
-/

/-- Zero relative phase is the diagonal linear-polarization state. -/
@[simp]
lemma equalAmplitudeRelativePhase_zero :
    equalAmplitudeRelativePhase 0 = diagonal := by
  ext i
  fin_cases i <;>
    simp [equalAmplitudeRelativePhase, diagonal, ofComponents]

/-- Relative phase `π` is the antidiagonal linear-polarization state. -/
@[simp]
lemma equalAmplitudeRelativePhase_pi :
    equalAmplitudeRelativePhase (Real.pi : Real.Angle) = antidiagonal := by
  ext i
  fin_cases i <;>
    simp [equalAmplitudeRelativePhase, antidiagonal, ofComponents,
      Real.Angle.toCircle_coe, Circle.coe_exp]

/-- Relative phase `π / 2` is the positive-`I` quadrature state. -/
@[simp]
lemma equalAmplitudeRelativePhase_pi_div_two :
    equalAmplitudeRelativePhase (((Real.pi / 2 : ℝ) : Real.Angle)) =
      plusIQuadrature := by
  ext i
  fin_cases i <;>
    simp [equalAmplitudeRelativePhase, plusIQuadrature, ofComponents,
      Real.Angle.toCircle_coe, Circle.coe_exp]

/-- Relative phase `-π / 2` is the negative-`I` quadrature state. -/
@[simp]
lemma equalAmplitudeRelativePhase_neg_pi_div_two :
    equalAmplitudeRelativePhase (((-Real.pi / 2 : ℝ) : Real.Angle)) =
      minusIQuadrature := by
  ext i
  fin_cases i <;>
    simp [equalAmplitudeRelativePhase, minusIQuadrature, ofComponents,
      Real.Angle.toCircle_coe, Circle.coe_exp]

end JonesVector

end

end Optics
