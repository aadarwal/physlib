/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Polarization.JonesStokes
public import Physlib.Optics.Polarization.RelativePhase

/-!
# Stokes coordinates of equal-amplitude relative-phase Jones states

## i. Overview

This file connects the normalized equal-amplitude Jones family to raw Stokes coordinates. A
relative phase `φ` maps to the unit polarization direction `(0, cos φ, sin φ)` under Physlib's
established third-coordinate sign.

Unguarded convention statement (review only): the coordinate names remain algebraic and are
assigned no observer-dependent circular-polarization handedness name. No electromagnetic
irradiance or modal-power interpretation is assigned here.

## ii. Key results

- `StokesVector.equalAmplitudeRelativePhaseDirection`: the unit Stokes direction of the family.
- `JonesVector.stokes_equalAmplitudeRelativePhase`: the exact Jones-to-Stokes formula.

## iii. Table of contents

- A. Relative-phase Stokes directions
- B. Jones-to-Stokes formula

## iv. References

The formula is derived from the public Jones-to-Stokes convention and the relative-phase family.
-/

@[expose] public section

namespace Optics

open Matrix

noncomputable section

namespace StokesVector

/-!

## A. Relative-phase Stokes directions
-/

/-- The unit Stokes polarization direction of an equal-amplitude Jones state with the declared
relative phase. -/
def equalAmplitudeRelativePhaseDirection (relativePhase : Real.Angle) :
    EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![0, Real.Angle.cos relativePhase, Real.Angle.sin relativePhase]

/-- The first polarization coordinate of an equal-amplitude relative-phase direction is zero. -/
@[simp]
lemma equalAmplitudeRelativePhaseDirection_zero (relativePhase : Real.Angle) :
    equalAmplitudeRelativePhaseDirection relativePhase 0 = 0 := rfl

/-- The second polarization coordinate records the cosine of the relative phase. -/
@[simp]
lemma equalAmplitudeRelativePhaseDirection_one (relativePhase : Real.Angle) :
    equalAmplitudeRelativePhaseDirection relativePhase 1 =
      Real.Angle.cos relativePhase := rfl

/-- The third polarization coordinate records the sine of the relative phase. -/
@[simp]
lemma equalAmplitudeRelativePhaseDirection_two (relativePhase : Real.Angle) :
    equalAmplitudeRelativePhaseDirection relativePhase 2 =
      Real.Angle.sin relativePhase := rfl

/-- An equal-amplitude relative-phase Stokes direction has unit Euclidean norm. -/
@[simp]
lemma norm_equalAmplitudeRelativePhaseDirection (relativePhase : Real.Angle) :
    ‖equalAmplitudeRelativePhaseDirection relativePhase‖ = 1 := by
  have hsq : ‖equalAmplitudeRelativePhaseDirection relativePhase‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
    simp [equalAmplitudeRelativePhaseDirection]
  nlinarith [norm_nonneg (equalAmplitudeRelativePhaseDirection relativePhase)]

end StokesVector

namespace JonesVector

/-!

## B. Jones-to-Stokes formula
-/

/-- A normalized equal-amplitude relative-phase Jones state has unit intensity and Stokes
polarization direction `(0, cos φ, sin φ)`. -/
lemma stokes_equalAmplitudeRelativePhase (relativePhase : Real.Angle) :
    (equalAmplitudeRelativePhase relativePhase).stokes =
      StokesVector.ofIntensityPolarization 1
        (StokesVector.equalAmplitudeRelativePhaseDirection relativePhase) := by
  ext μ
  rcases μ with μ | μ
  · fin_cases μ
    change (equalAmplitudeRelativePhase relativePhase).stokes.intensity = 1
    rw [stokes_intensity_eq_intensity]
    exact intensity_equalAmplitudeRelativePhase relativePhase
  · fin_cases μ
    · simp [StokesVector.ofIntensityPolarization,
        StokesVector.equalAmplitudeRelativePhaseDirection,
        equalAmplitudeRelativePhase, Complex.normSq_mul,
        Complex.normSq_ofReal]
    · simp [StokesVector.ofIntensityPolarization,
        StokesVector.equalAmplitudeRelativePhaseDirection,
        equalAmplitudeRelativePhase, Real.Angle.coe_toCircle]
      ring_nf
      rw [unitEqualAmplitude_sq]
      ring
    · simp [StokesVector.ofIntensityPolarization,
        StokesVector.equalAmplitudeRelativePhaseDirection,
        equalAmplitudeRelativePhase, Real.Angle.coe_toCircle]
      ring_nf
      rw [unitEqualAmplitude_sq]
      ring

end JonesVector

end

end Optics
