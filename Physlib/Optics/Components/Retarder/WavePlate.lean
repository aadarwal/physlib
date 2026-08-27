/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Components.Retarder.Basic

/-!
# Ideal quarter-wave and half-wave plates

## i. Overview

This file specializes the ideal linear retarder to positive and negative quarter-wave retardance
and to half-wave retardance. Positive quarter-wave retardance delays the axis orthogonal to the
declared reference principal axis by `π / 2` under Physlib's positive-carrier-phase realization
convention.

The resulting laws are exact Jones-amplitude statements. In particular, the half-wave plate
reflects a linear-polarization angle across its reference axis. Unguarded convention statement
(review only): no circular-polarization handedness name is assigned here. No electromagnetic-power
interpretation is assigned either.

## ii. Key results

- `JonesMatrix.quarterWavePlate` and `JonesMatrix.negativeQuarterWavePlate`.
- `JonesMatrix.halfWavePlate`.
- `JonesMatrix.quarterWavePlate_comp_self`: two aligned quarter-wave plates form a half-wave plate.
- `JonesMatrix.halfWavePlate_act_linearPolarization`: the general linear-angle reflection law.

## iii. Table of contents

- A. Wave-plate definitions
- B. Composition and unitarity
- C. Action on linear polarization

## iv. References

The specializations inherit the phase convention and common-phase gauge documented in
`Optics.Components.Retarder.Basic`.
-/

@[expose] public section

namespace Optics

noncomputable section

namespace JonesMatrix

/-!

## A. Wave-plate definitions
-/

/-- An ideal positive quarter-wave plate whose orthogonal principal axis is delayed by `π / 2`. -/
def quarterWavePlate (axis : Real.Angle) : JonesMatrix :=
  linearRetarder axis ((Real.pi / 2 : ℝ) : Real.Angle)

/-- An ideal negative quarter-wave plate whose orthogonal principal axis has retardance
`-π / 2`. -/
def negativeQuarterWavePlate (axis : Real.Angle) : JonesMatrix :=
  linearRetarder axis ((-Real.pi / 2 : ℝ) : Real.Angle)

/-- An ideal half-wave plate whose orthogonal principal axis is delayed by `π`. -/
def halfWavePlate (axis : Real.Angle) : JonesMatrix :=
  linearRetarder axis (Real.pi : Real.Angle)

/-!

## B. Composition and unitarity
-/

/-- Every ideal positive quarter-wave plate is algebraically unitary. -/
lemma quarterWavePlate_isUnitary (axis : Real.Angle) :
    (quarterWavePlate axis).IsUnitary :=
  linearRetarder_isUnitary axis ((Real.pi / 2 : ℝ) : Real.Angle)

/-- Every ideal negative quarter-wave plate is algebraically unitary. -/
lemma negativeQuarterWavePlate_isUnitary (axis : Real.Angle) :
    (negativeQuarterWavePlate axis).IsUnitary :=
  linearRetarder_isUnitary axis ((-Real.pi / 2 : ℝ) : Real.Angle)

/-- Every ideal half-wave plate is algebraically unitary. -/
lemma halfWavePlate_isUnitary (axis : Real.Angle) :
    (halfWavePlate axis).IsUnitary :=
  linearRetarder_isUnitary axis (Real.pi : Real.Angle)

/-- Two quarter-wave plates with the same reference axis compose to one half-wave plate. -/
lemma quarterWavePlate_comp_self (axis : Real.Angle) :
    (quarterWavePlate axis).comp (quarterWavePlate axis) =
      halfWavePlate axis := by
  rw [quarterWavePlate, linearRetarder_comp, halfWavePlate]
  congr 2
  rw [← Real.Angle.coe_add]
  congr 1
  ring

/-- Aligned positive and negative quarter-wave plates compose to the identity. -/
lemma negativeQuarterWavePlate_comp_quarterWavePlate (axis : Real.Angle) :
    (negativeQuarterWavePlate axis).comp (quarterWavePlate axis) = identity := by
  rw [negativeQuarterWavePlate, quarterWavePlate]
  have hneg : ((-Real.pi / 2 : ℝ) : Real.Angle) =
      -(((Real.pi / 2 : ℝ) : Real.Angle)) := by
    rw [← Real.Angle.coe_neg]
    congr 1
    ring
  rw [hneg]
  exact linearRetarder_neg_comp axis ((Real.pi / 2 : ℝ) : Real.Angle)

/-- Two half-wave plates with the same reference axis compose to the identity. -/
@[simp]
lemma halfWavePlate_comp_self (axis : Real.Angle) :
    (halfWavePlate axis).comp (halfWavePlate axis) = identity := by
  rw [halfWavePlate, linearRetarder_comp, Real.Angle.coe_pi_add_coe_pi]
  exact linearRetarder_zero axis

/-!

## C. Action on linear polarization
-/

/-- A positive quarter-wave plate gives the orthogonal component of a linear input relative phase
`-I`. -/
lemma quarterWavePlate_act_linearPolarization (axis input : Real.Angle) :
    (quarterWavePlate axis).act (JonesVector.linearPolarization input) =
      JonesVector.ofLinearComponents axis
        (Real.Angle.cos (input - axis))
        (-Complex.I * Real.Angle.sin (input - axis)) := by
  rw [quarterWavePlate, linearRetarder_act_linearPolarization,
    linearRetarderPhase_pi_div_two]

/-- A negative quarter-wave plate gives the orthogonal component of a linear input relative phase
`I`. -/
lemma negativeQuarterWavePlate_act_linearPolarization (axis input : Real.Angle) :
    (negativeQuarterWavePlate axis).act (JonesVector.linearPolarization input) =
      JonesVector.ofLinearComponents axis
        (Real.Angle.cos (input - axis))
        (Complex.I * Real.Angle.sin (input - axis)) := by
  rw [negativeQuarterWavePlate, linearRetarder_act_linearPolarization,
    linearRetarderPhase_neg_pi_div_two]

/-- A half-wave plate reflects a linear-polarization angle across its reference principal axis. -/
lemma halfWavePlate_act_linearPolarization (axis input : Real.Angle) :
    (halfWavePlate axis).act (JonesVector.linearPolarization input) =
      JonesVector.linearPolarization (2 • axis - input) := by
  rw [halfWavePlate, linearRetarder_act_linearPolarization,
    linearRetarderPhase_pi,
    JonesVector.linearPolarization_eq_ofLinearComponents axis]
  have hangle : (2 • axis - input) - axis = -(input - axis) := by
    abel
  rw [hangle, Real.Angle.cos_neg, Real.Angle.sin_neg]
  congr 2
  norm_num

end JonesMatrix

end

end Optics
