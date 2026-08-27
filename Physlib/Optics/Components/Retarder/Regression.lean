/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Components.Retarder.WavePlate

/-!
# Ideal-retarder convention regressions

## i. Overview

This file pins the phase, coordinate, and cascade conventions of ideal retarders at canonical
axes and polarization states. The positive zero-axis quarter-wave plate is exactly `diag(1, -I)`,
so it sends diagonal polarization to the negative-`I` quadrature state. Its negative-retardance
counterpart reverses these mappings.

Unguarded convention statement (review only): the regression suite retains algebraic quadrature
names and assigns no observer-based circular-polarization handedness name. It makes no
electromagnetic-power claim.

## ii. Key results

- Canonical zero-axis retarder, quarter-wave, and half-wave matrices.
- Exact quarter-wave mappings among diagonal, antidiagonal, and quadrature states.
- Exact inverse-quarter-wave and half-wave mappings derived by component composition.
- The `π / 4` half-wave plate exchange of the two coordinate-axis states.

## iii. Table of contents

- A. Canonical Jones matrices
- B. Quarter-wave state mappings
- C. Half-wave state mappings

## iv. References

These symbolic regressions specialize the public retarder and relative-phase APIs.
-/

@[expose] public section

namespace Optics

open Matrix

noncomputable section

namespace JonesMatrix

/-!

## A. Canonical Jones matrices
-/

/-- The positive zero-axis quarter-wave plate is `diag(1, -I)`. -/
lemma quarterWavePlate_zero_entries :
    (quarterWavePlate 0).entries = !![1, 0; 0, -Complex.I] := by
  rw [quarterWavePlate, linearRetarder_zero_axis_entries]
  simp

/-- The negative zero-axis quarter-wave plate is `diag(1, I)`. -/
lemma negativeQuarterWavePlate_zero_entries :
    (negativeQuarterWavePlate 0).entries = !![1, 0; 0, Complex.I] := by
  rw [negativeQuarterWavePlate, linearRetarder_zero_axis_entries]
  simp

/-- The positive zero-axis half-wave plate is `diag(1, -1)`. -/
lemma halfWavePlate_zero_entries :
    (halfWavePlate 0).entries = !![1, 0; 0, -1] := by
  rw [halfWavePlate, linearRetarder_zero_axis_entries]
  simp

/-!

## B. Quarter-wave state mappings
-/

/-- A positive zero-axis quarter-wave plate sends diagonal polarization to negative quadrature. -/
lemma quarterWavePlate_zero_act_diagonal :
    (quarterWavePlate 0).act JonesVector.diagonal =
      JonesVector.minusIQuadrature := by
  have hphase : (0 : Real.Angle) - ((Real.pi / 2 : ℝ) : Real.Angle) =
      ((-Real.pi / 2 : ℝ) : Real.Angle) := by
    rw [zero_sub, ← Real.Angle.coe_neg]
    congr 1
    ring
  rw [quarterWavePlate, ← JonesVector.equalAmplitudeRelativePhase_zero,
    linearRetarder_zero_axis_act_equalAmplitudeRelativePhase, hphase,
    JonesVector.equalAmplitudeRelativePhase_neg_pi_div_two]

/-- A positive zero-axis quarter-wave plate sends antidiagonal polarization to positive
quadrature. -/
lemma quarterWavePlate_zero_act_antidiagonal :
    (quarterWavePlate 0).act JonesVector.antidiagonal =
      JonesVector.plusIQuadrature := by
  rw [quarterWavePlate, ← JonesVector.equalAmplitudeRelativePhase_pi,
    linearRetarder_zero_axis_act_equalAmplitudeRelativePhase]
  have hphase : (Real.pi : Real.Angle) - ((Real.pi / 2 : ℝ) : Real.Angle) =
      ((Real.pi / 2 : ℝ) : Real.Angle) := by
    rw [← Real.Angle.coe_sub]
    congr 1
    ring
  rw [hphase, JonesVector.equalAmplitudeRelativePhase_pi_div_two]

/-- A positive zero-axis quarter-wave plate sends positive quadrature back to diagonal
polarization. -/
lemma quarterWavePlate_zero_act_plusIQuadrature :
    (quarterWavePlate 0).act JonesVector.plusIQuadrature =
      JonesVector.diagonal := by
  rw [quarterWavePlate, ← JonesVector.equalAmplitudeRelativePhase_pi_div_two,
    linearRetarder_zero_axis_act_equalAmplitudeRelativePhase, sub_self,
    JonesVector.equalAmplitudeRelativePhase_zero]

/-- A positive zero-axis quarter-wave plate sends negative quadrature to antidiagonal
polarization. -/
lemma quarterWavePlate_zero_act_minusIQuadrature :
    (quarterWavePlate 0).act JonesVector.minusIQuadrature =
      JonesVector.antidiagonal := by
  rw [quarterWavePlate, ← JonesVector.equalAmplitudeRelativePhase_neg_pi_div_two,
    linearRetarder_zero_axis_act_equalAmplitudeRelativePhase]
  have hphase : ((-Real.pi / 2 : ℝ) : Real.Angle) -
      ((Real.pi / 2 : ℝ) : Real.Angle) = (Real.pi : Real.Angle) := by
    rw [← Real.Angle.coe_sub]
    have hreal : -Real.pi / 2 - Real.pi / 2 = -Real.pi := by ring
    rw [hreal, Real.Angle.coe_neg, Real.Angle.neg_coe_pi]
  rw [hphase, JonesVector.equalAmplitudeRelativePhase_pi]

/-- A negative zero-axis quarter-wave plate reverses the diagonal-to-negative-quadrature map. -/
lemma negativeQuarterWavePlate_zero_act_minusIQuadrature :
    (negativeQuarterWavePlate 0).act JonesVector.minusIQuadrature =
      JonesVector.diagonal := by
  have hinverse := congrArg (fun M : JonesMatrix ↦ M.act JonesVector.diagonal)
    (negativeQuarterWavePlate_comp_quarterWavePlate 0)
  rw [comp_act, identity_act, quarterWavePlate_zero_act_diagonal] at hinverse
  exact hinverse

/-- A negative zero-axis quarter-wave plate sends diagonal polarization to positive quadrature. -/
lemma negativeQuarterWavePlate_zero_act_diagonal :
    (negativeQuarterWavePlate 0).act JonesVector.diagonal =
      JonesVector.plusIQuadrature := by
  have hinverse := congrArg (fun M : JonesMatrix ↦ M.act JonesVector.plusIQuadrature)
    (negativeQuarterWavePlate_comp_quarterWavePlate 0)
  rw [comp_act, identity_act, quarterWavePlate_zero_act_plusIQuadrature] at hinverse
  exact hinverse

/-- A negative zero-axis quarter-wave plate sends positive quadrature to antidiagonal
polarization. -/
lemma negativeQuarterWavePlate_zero_act_plusIQuadrature :
    (negativeQuarterWavePlate 0).act JonesVector.plusIQuadrature =
      JonesVector.antidiagonal := by
  have hinverse := congrArg (fun M : JonesMatrix ↦ M.act JonesVector.antidiagonal)
    (negativeQuarterWavePlate_comp_quarterWavePlate 0)
  rw [comp_act, identity_act, quarterWavePlate_zero_act_antidiagonal] at hinverse
  exact hinverse

/-- A negative zero-axis quarter-wave plate sends antidiagonal polarization to negative
quadrature. -/
lemma negativeQuarterWavePlate_zero_act_antidiagonal :
    (negativeQuarterWavePlate 0).act JonesVector.antidiagonal =
      JonesVector.minusIQuadrature := by
  have hinverse := congrArg (fun M : JonesMatrix ↦ M.act JonesVector.minusIQuadrature)
    (negativeQuarterWavePlate_comp_quarterWavePlate 0)
  rw [comp_act, identity_act, quarterWavePlate_zero_act_minusIQuadrature] at hinverse
  exact hinverse

/-!

## C. Half-wave state mappings
-/

/-- A zero-axis half-wave plate sends diagonal polarization to antidiagonal polarization. -/
lemma halfWavePlate_zero_act_diagonal :
    (halfWavePlate 0).act JonesVector.diagonal =
      JonesVector.antidiagonal := by
  rw [← quarterWavePlate_comp_self, comp_act,
    quarterWavePlate_zero_act_diagonal, quarterWavePlate_zero_act_minusIQuadrature]

/-- A zero-axis half-wave plate sends antidiagonal polarization to diagonal polarization. -/
lemma halfWavePlate_zero_act_antidiagonal :
    (halfWavePlate 0).act JonesVector.antidiagonal =
      JonesVector.diagonal := by
  rw [← quarterWavePlate_comp_self, comp_act,
    quarterWavePlate_zero_act_antidiagonal, quarterWavePlate_zero_act_plusIQuadrature]

/-- A zero-axis half-wave plate sends positive quadrature to negative quadrature. -/
lemma halfWavePlate_zero_act_plusIQuadrature :
    (halfWavePlate 0).act JonesVector.plusIQuadrature =
      JonesVector.minusIQuadrature := by
  rw [← quarterWavePlate_comp_self, comp_act,
    quarterWavePlate_zero_act_plusIQuadrature, quarterWavePlate_zero_act_diagonal]

/-- A zero-axis half-wave plate sends negative quadrature to positive quadrature. -/
lemma halfWavePlate_zero_act_minusIQuadrature :
    (halfWavePlate 0).act JonesVector.minusIQuadrature =
      JonesVector.plusIQuadrature := by
  rw [← quarterWavePlate_comp_self, comp_act,
    quarterWavePlate_zero_act_minusIQuadrature,
    quarterWavePlate_zero_act_antidiagonal]

/-- A `π / 4` half-wave plate sends the first coordinate-axis state to the second. -/
lemma halfWavePlate_pi_div_four_act_horizontal :
    (halfWavePlate ((Real.pi / 4 : ℝ) : Real.Angle)).act JonesVector.horizontal =
      JonesVector.vertical := by
  rw [← JonesVector.linearPolarization_zero,
    halfWavePlate_act_linearPolarization]
  have hangle : 2 • (((Real.pi / 4 : ℝ) : Real.Angle)) - 0 =
      ((Real.pi / 2 : ℝ) : Real.Angle) := by
    rw [sub_zero, ← Real.Angle.coe_nsmul]
    congr 1
    ring
  rw [hangle, JonesVector.linearPolarization_pi_div_two]

/-- A `π / 4` half-wave plate sends the second coordinate-axis state to the first. -/
lemma halfWavePlate_pi_div_four_act_vertical :
    (halfWavePlate ((Real.pi / 4 : ℝ) : Real.Angle)).act JonesVector.vertical =
      JonesVector.horizontal := by
  rw [← JonesVector.linearPolarization_pi_div_two,
    halfWavePlate_act_linearPolarization]
  have hangle : 2 • (((Real.pi / 4 : ℝ) : Real.Angle)) -
      ((Real.pi / 2 : ℝ) : Real.Angle) = 0 := by
    rw [← Real.Angle.coe_nsmul, ← Real.Angle.coe_sub]
    congr 1
    ring
  rw [hangle, JonesVector.linearPolarization_zero]

end JonesMatrix

end

end Optics
