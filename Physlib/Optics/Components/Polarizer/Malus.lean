/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Components.Polarizer.Basic

/-!
# Malus' law for ideal linear polarizers

## i. Overview

This file derives the coherent amplitude and squared-Jones-intensity laws for one or two ideal
linear polarizers from the projector action in `Optics.Components.Polarizer.Basic`. In
`M.comp N`, the component `N` acts first and `M` acts second.

The amplitude law retains the signed angle-difference cosine, including its coherent phase sign.
The squared-intensity law then contains its square. These statements concern raw Jones amplitudes;
they do not yet identify that quantity with electromagnetic irradiance or modal power.

## ii. Key results

- `JonesMatrix.linearPolarizer_act_scaled_linearPolarization`: coherent analyzer amplitude.
- `JonesMatrix.linearPolarizer_malus`: Malus' law for a scaled linear input.
- `JonesMatrix.linearPolarizer_comp_act`: exact two-stage cascade action.
- `JonesMatrix.linearPolarizer_comp_intensity`: two-stage intensity law for an arbitrary input.

## iii. Table of contents

- A. One polarizer acting on a linear input
- B. Sequential polarizers
- C. Convention-sensitive regressions

## iv. References

All results are derived from the ideal projector and the existing squared-Jones-intensity
definition.
-/

@[expose] public section

namespace Optics

noncomputable section

namespace JonesMatrix

/-!

## A. One polarizer acting on a linear input
-/

/-- A linear polarizer sends a linear input to its axis with the signed angle-difference cosine
amplitude. -/
lemma linearPolarizer_act_linearPolarization (analyzer input : Real.Angle) :
    (linearPolarizer analyzer).act (JonesVector.linearPolarization input) =
      JonesVector.scale (Real.Angle.cos (input - analyzer))
        (JonesVector.linearPolarization analyzer) := by
  rw [linearPolarizer_act, JonesVector.linearComponent_linearPolarization]

/-- A linear polarizer sends a scaled linear input to its axis with the input amplitude multiplied
by the signed angle-difference cosine. -/
lemma linearPolarizer_act_scaled_linearPolarization (z : ℂ)
    (analyzer input : Real.Angle) :
    (linearPolarizer analyzer).act
      (JonesVector.scale z (JonesVector.linearPolarization input)) =
        JonesVector.scale
          (z * (Real.Angle.cos (input - analyzer) : ℂ))
          (JonesVector.linearPolarization analyzer) := by
  rw [linearPolarizer_act, JonesVector.linearComponent_scale,
    JonesVector.linearComponent_linearPolarization]

/-- Malus' law for a scaled linear-polarization input in squared Jones intensity. -/
lemma linearPolarizer_malus (z : ℂ) (analyzer input : Real.Angle) :
    ((linearPolarizer analyzer).act
      (JonesVector.scale z (JonesVector.linearPolarization input))).intensity =
        (JonesVector.scale z (JonesVector.linearPolarization input)).intensity *
          Real.Angle.cos (input - analyzer) ^ 2 := by
  rw [linearPolarizer_act_intensity, JonesVector.linearComponent_scale,
    JonesVector.linearComponent_linearPolarization, Complex.normSq_mul,
    JonesVector.intensity_scale, JonesVector.intensity_linearPolarization]
  rw [Complex.normSq_ofReal]
  ring

/-!

## B. Sequential polarizers
-/

/-- Composing polarizers with axes `first` and `second` first applies `first`, then multiplies the
resulting amplitude by the signed cosine between the axes and outputs along `second`. -/
lemma linearPolarizer_comp_act (first second : Real.Angle) (J : JonesVector) :
    ((linearPolarizer second).comp (linearPolarizer first)).act J =
      JonesVector.scale
        (J.linearComponent first * (Real.Angle.cos (first - second) : ℂ))
        (JonesVector.linearPolarization second) := by
  rw [JonesMatrix.comp_act, linearPolarizer_act, linearPolarizer_act,
    JonesVector.linearComponent_scale,
    JonesVector.linearComponent_linearPolarization]

/-- After two ideal linear polarizers, the first output's squared Jones intensity is multiplied by
the squared cosine of the angle between their axes. -/
lemma linearPolarizer_comp_intensity (first second : Real.Angle) (J : JonesVector) :
    (((linearPolarizer second).comp (linearPolarizer first)).act J).intensity =
      ((linearPolarizer first).act J).intensity *
        Real.Angle.cos (first - second) ^ 2 := by
  rw [linearPolarizer_comp_act, JonesVector.intensity_scale,
    JonesVector.intensity_linearPolarization, linearPolarizer_act_intensity,
    Complex.normSq_mul, Complex.normSq_ofReal]
  ring

/-!

## C. Convention-sensitive regressions
-/

/-- Two crossed linear polarizers extinguish every Jones input. -/
lemma linearPolarizer_comp_orthogonal (first : Real.Angle) (J : JonesVector) :
    ((linearPolarizer (first + (Real.pi / 2 : ℝ))).comp
      (linearPolarizer first)).act J = JonesVector.ofComponents 0 0 := by
  rw [linearPolarizer_comp_act]
  ext i
  fin_cases i <;> simp [JonesVector.scale, JonesVector.ofComponents]

/-- A zero-axis polarizer transmits the horizontal coordinate state. -/
@[simp]
lemma linearPolarizer_zero_act_horizontal :
    (linearPolarizer 0).act JonesVector.horizontal = JonesVector.horizontal := by
  rw [← JonesVector.linearPolarization_zero]
  exact linearPolarizer_act_axis 0

/-- A zero-axis polarizer extinguishes the vertical coordinate state. -/
@[simp]
lemma linearPolarizer_zero_act_vertical :
    (linearPolarizer 0).act JonesVector.vertical = JonesVector.ofComponents 0 0 := by
  rw [← JonesVector.linearPolarization_pi_div_two]
  simpa using linearPolarizer_act_orthogonal 0

/-- A horizontal unit input analyzed at `π / 4` has squared Jones intensity `1 / 2`. -/
lemma linearPolarizer_pi_div_four_horizontal_intensity :
    ((linearPolarizer ((Real.pi / 4 : ℝ) : Real.Angle)).act
      JonesVector.horizontal).intensity = 1 / 2 := by
  rw [← JonesVector.linearPolarization_zero,
    linearPolarizer_act_linearPolarization, JonesVector.intensity_scale,
    JonesVector.intensity_linearPolarization, Complex.normSq_ofReal]
  rw [zero_sub, Real.Angle.cos_neg]
  simp only [Real.Angle.cos_coe, mul_one]
  rw [← pow_two]
  rw [Real.cos_pi_div_four, div_pow, Real.sq_sqrt (by norm_num)]
  norm_num

end JonesMatrix

end

end Optics
