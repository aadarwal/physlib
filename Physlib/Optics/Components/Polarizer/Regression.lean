/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Components.Polarizer.Basic

/-!
# Ideal linear-polarizer convention regressions

## i. Overview

This file pins the Jones-coordinate and angle conventions of the ideal linear polarizer at the
canonical axes `0`, `π / 2`, and `π / 4`. The general projector and Mueller results remain in
their semantic modules; these exact matrices are symbolic regression checks.

## ii. Key results

- `JonesMatrix.linearPolarizer_zero_entries`: the first-coordinate projector.
- `JonesMatrix.linearPolarizer_pi_div_two_entries`: the second-coordinate projector.
- `JonesMatrix.linearPolarizer_pi_div_four_entries`: the equal one-half matrix.

## iii. Table of contents

- A. Canonical Jones matrices

## iv. References

The regressions specialize the imported ideal-projector definition exactly.
-/

@[expose] public section

namespace Optics

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace JonesMatrix

/-!

## A. Canonical Jones matrices
-/

/-- A zero-axis ideal linear polarizer transmits the first Jones coordinate. -/
lemma linearPolarizer_zero_entries :
    (linearPolarizer 0).entries = !![1, 0; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [linearPolarizer, JonesVector.linearPolarization, Matrix.vecMulVec]

/-- A `π / 2` ideal linear polarizer transmits the second Jones coordinate. -/
lemma linearPolarizer_pi_div_two_entries :
    (linearPolarizer ((Real.pi / 2 : ℝ) : Real.Angle)).entries =
      !![0, 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [linearPolarizer, JonesVector.linearPolarization, Matrix.vecMulVec]

/-- A `π / 4` ideal linear polarizer has equal one-half entries. -/
lemma linearPolarizer_pi_div_four_entries :
    (linearPolarizer ((Real.pi / 4 : ℝ) : Real.Angle)).entries =
      !![(1 / 2 : ℂ), 1 / 2; 1 / 2, 1 / 2] := by
  change Matrix.vecMulVec
      (JonesVector.linearPolarization
        ((Real.pi / 4 : ℝ) : Real.Angle)).components
      (star (JonesVector.linearPolarization
        ((Real.pi / 4 : ℝ) : Real.Angle)).components) = _
  rw [JonesVector.linearPolarization_pi_div_four]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [JonesVector.diagonal, Matrix.vecMulVec]
  all_goals
    rw [← Complex.ofReal_mul, JonesVector.unitEqualAmplitude_mul_self]
    norm_num

end JonesMatrix

end

end Optics
