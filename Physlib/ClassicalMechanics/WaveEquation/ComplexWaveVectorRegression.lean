/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.ClassicalMechanics.WaveEquation.ComplexWaveVector

/-!
# Complex wave-vector sign regressions

## i. Overview

This file pins the positive-normal decay sign in the standard three-coordinate frame. The selected
normal is the positive third coordinate direction, the phase wave vector lies in the positive
first coordinate direction, and the resulting complex wave vector is `(kappa, 0, -I * alpha)`.
Displacement by positive third-coordinate depth `z` therefore multiplies the spatial factor by
`exp (-alpha * z)`.

These are algebraic sign regressions. They do not assign an interface side, transmitted-wave role,
square-root branch, or electromagnetic power interpretation.

## ii. Key results

- `positiveNormalDecayRegression_waveVector`: exact complex wave-vector coordinates.
- `positiveNormalDecayRegression_spatialFactor_vadd`: exact positive-third-coordinate decay.

## iii. Table of contents

- A. Fixed coordinate data
- B. Wave-vector and decay regressions
-/

@[expose] public section

namespace ClassicalMechanics

open Space Matrix InnerProductSpace

noncomputable section

namespace ComplexWaveVector

/-!

## A. Fixed coordinate data

-/

/-- The positive third-coordinate direction used by the complex-wave-vector regression. -/
def positiveNormalDecayRegressionDirection : Space.Direction 3 :=
  ⟨Space.basis 2, by simp⟩

/-- The first-coordinate tangential phase vector used by the regression. -/
def positiveNormalDecayRegressionTangentialVector (waveNumber : ℝ) : WaveVector 3 :=
  WithLp.toLp 2 ![waveNumber, 0, 0]

/-- Positive-normal decay data with phase along the first coordinate and decay along the third. -/
def positiveNormalDecayRegression (waveNumber decayRate : ℝ) (hdecayRate : 0 < decayRate) :
    PositiveNormalDecayWaveVector positiveNormalDecayRegressionDirection where
  tangentialWaveVector := positiveNormalDecayRegressionTangentialVector waveNumber
  tangential := by
    simp [positiveNormalDecayRegressionDirection,
      positiveNormalDecayRegressionTangentialVector, PiLp.inner_apply,
      RCLike.inner_apply]
  decayRate := decayRate
  decayRate_pos := hdecayRate

/-- The coordinate displacement `(0, 0, depth)` used by the regression. -/
def positiveNormalDecayRegressionDisplacement (depth : ℝ) : WaveVector 3 :=
  WithLp.toLp 2 ![0, 0, depth]

/-!

## B. Wave-vector and decay regressions

-/

/-- The selected normal has coordinate vector `(0, 0, 1)`. -/
lemma positiveNormalDecayRegression_normalVector
    (waveNumber decayRate : ℝ) (hdecayRate : 0 < decayRate) :
    (positiveNormalDecayRegression waveNumber decayRate hdecayRate).normalVector =
      WithLp.toLp 2 ![0, 0, 1] := by
  ext i
  fin_cases i <;>
    simp [PositiveNormalDecayWaveVector.normalVector,
      positiveNormalDecayRegressionDirection]

/-- The positive-normal decay convention gives the exact wave vector
`(waveNumber, 0, -I * decayRate)`. -/
lemma positiveNormalDecayRegression_waveVector
    (waveNumber decayRate : ℝ) (hdecayRate : 0 < decayRate) :
    (positiveNormalDecayRegression waveNumber decayRate hdecayRate).waveVector =
      WithLp.toLp 2 ![(waveNumber : ℂ), 0, -Complex.I * (decayRate : ℂ)] := by
  ext i
  fin_cases i <;>
    simp [PositiveNormalDecayWaveVector.waveVector,
      positiveNormalDecayRegression, positiveNormalDecayRegressionTangentialVector,
      PositiveNormalDecayWaveVector.normalVector, positiveNormalDecayRegressionDirection,
      ofPhaseAttenuation]

/-- Scaling the selected normal coordinate vector by `depth` gives `(0, 0, depth)`. -/
lemma positiveNormalDecayRegressionDisplacement_eq_smul_normalVector
    (waveNumber decayRate : ℝ) (hdecayRate : 0 < decayRate) (depth : ℝ) :
    positiveNormalDecayRegressionDisplacement depth =
      depth • (positiveNormalDecayRegression waveNumber decayRate hdecayRate).normalVector := by
  rw [positiveNormalDecayRegression_normalVector]
  ext i
  fin_cases i <;> simp [positiveNormalDecayRegressionDisplacement]

/-- Positive third-coordinate displacement multiplies the spatial factor by
`exp (-decayRate * depth)`. -/
lemma positiveNormalDecayRegression_spatialFactor_vadd
    (waveNumber decayRate : ℝ) (hdecayRate : 0 < decayRate)
    (depth : ℝ) (x : Space) :
    (positiveNormalDecayRegression waveNumber decayRate hdecayRate).waveVector.spatialFactor
        (positiveNormalDecayRegressionDisplacement depth +ᵥ x) =
      (Real.exp (-decayRate * depth) : ℂ) *
        (positiveNormalDecayRegression waveNumber decayRate hdecayRate).waveVector.spatialFactor
          x := by
  rw [positiveNormalDecayRegressionDisplacement_eq_smul_normalVector]
  exact PositiveNormalDecayWaveVector.spatialFactor_vadd _ _ _

end ComplexWaveVector

end

end ClassicalMechanics
