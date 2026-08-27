/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Components.Retarder.Mueller
public import Physlib.Optics.Components.Retarder.Regression
public import Physlib.Optics.Polarization.Mueller.Regression

/-!
# Mueller convention regressions for ideal wave plates

## i. Overview

This file pins the sign of the retarder Mueller block against the established deterministic
Mueller convention. The negative zero-axis quarter-wave plate is identified exactly with the
existing algebraic Jones regression `diag(1, I)`. The positive plate and a rotated positive plate
then provide arbitrary-Stokes coordinate regressions.

These checks use algebraic coordinate names. Unguarded convention statement (review only): they
assign no circular-handedness name. They make no electromagnetic-power claim.

## ii. Key results

- `JonesMatrix.negativeQuarterWavePlate_zero_eq_secondCoordinateIPhase`.
- `JonesMatrix.quarterWavePlate_zero_mueller_act`.
- `JonesMatrix.quarterWavePlate_pi_div_four_mueller_act`.

## iii. Table of contents

- A. Established sign regression
- B. Positive-quarter-wave Mueller actions

## iv. References

The results compare the retarder block with the public deterministic Mueller regression suite.
-/

@[expose] public section

namespace Optics

noncomputable section

namespace JonesMatrix

/-!

## A. Established sign regression
-/

/-- The negative zero-axis quarter-wave plate is exactly the established algebraic Jones matrix
that multiplies the second coordinate by `I`. -/
lemma negativeQuarterWavePlate_zero_eq_secondCoordinateIPhase :
    negativeQuarterWavePlate 0 = secondCoordinateIPhase := by
  apply JonesMatrix.ext
  rw [negativeQuarterWavePlate_zero_entries]
  rfl

/-!

## B. Positive-quarter-wave Mueller actions
-/

/-- A positive zero-axis quarter-wave plate sends
`(S₁, S₂, S₃)` to `(S₁, S₃, -S₂)`. -/
lemma quarterWavePlate_zero_mueller_act (S : StokesVector) :
    (quarterWavePlate 0).mueller.act S =
      StokesVector.ofIntensityPolarization S.intensity
        (WithLp.toLp 2 ![
          S.polarization 0, S.polarization 2, -S.polarization 1]) := by
  rw [quarterWavePlate, linearRetarder_mueller_act]
  ext i
  rcases i with i | i
  · fin_cases i
    rfl
  · fin_cases i <;>
      simp [Matrix.toLpLin_apply, linearRetarderPolarizationBlock,
        StokesVector.ofIntensityPolarization, StokesVector.polarization,
        Matrix.vecHead, Matrix.vecTail]

/-- A positive quarter-wave plate at axis `π / 4` sends
`(S₁, S₂, S₃)` to `(-S₃, S₂, S₁)`. -/
lemma quarterWavePlate_pi_div_four_mueller_act (S : StokesVector) :
    (quarterWavePlate ((Real.pi / 4 : ℝ) : Real.Angle)).mueller.act S =
      StokesVector.ofIntensityPolarization S.intensity
        (WithLp.toLp 2 ![
          -S.polarization 2, S.polarization 1, S.polarization 0]) := by
  have haxis : 2 • (((Real.pi / 4 : ℝ) : Real.Angle)) =
      ((Real.pi / 2 : ℝ) : Real.Angle) := by
    rw [← Real.Angle.coe_nsmul]
    congr 1
    ring
  rw [quarterWavePlate, linearRetarder_mueller_act]
  ext i
  rcases i with i | i
  · fin_cases i
    rfl
  · fin_cases i <;>
      simp [Matrix.toLpLin_apply, linearRetarderPolarizationBlock,
        StokesVector.ofIntensityPolarization, StokesVector.polarization,
        Matrix.vecHead, Matrix.vecTail, haxis]

end JonesMatrix

end

end Optics
