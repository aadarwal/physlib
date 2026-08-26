/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Components.Polarizer.Mueller
public import Physlib.Optics.Components.Retarder.Mueller
public import Physlib.Optics.Components.Retarder.WavePlate
public import Physlib.Optics.Polarization.Mueller.Algebra

/-!
# Polarizer-retarder systems

## i. Overview

This file connects an ideal linear polarizer followed by an ideal linear retarder in Jones,
pure-coherency, and raw-Stokes representations. The existing Jones-matrix composition convention
applies its right-hand component first, so the polarizer acts first and the retarder acts second.

The Jones result retains the selected complex analyzer amplitude and gives the retarder output in
its principal-axis basis. The induced Mueller result selects the same raw Stokes scalar and then
applies the retarder polarization block. A canonical `pi / 4` analyzer followed by a positive
zero-axis quarter-wave plate pins both the order and the phase sign.

All intensity language refers only to squared raw Jones amplitude or the corresponding raw Stokes
coordinate. No electromagnetic irradiance, Poynting flux, modal power, passivity, or
circular-polarization handedness is assigned here.

## ii. Key results

- `JonesMatrix.linearRetarder_comp_linearPolarizer_act`: exact arbitrary-Jones output.
- `JonesMatrix.linearRetarder_comp_linearPolarizer_map_coherency`: exact pure-coherency output.
- `JonesMatrix.linearRetarder_comp_linearPolarizer_mueller_act`: arbitrary raw-Stokes output.
- `JonesMatrix.quarterWavePlate_zero_comp_linearPolarizer_pi_div_four_act_horizontal`: connected
  order, amplitude, and sign regression.

## iii. Table of contents

- A. Exact Jones and pure-coherency output
- B. Arbitrary raw-Stokes action
- C. Convention-sensitive connected regression

## iv. References

The results are derived from the imported ideal-polarizer, ideal-retarder, coherency, and
Jones-induced Mueller APIs.
-/

@[expose] public section

namespace Optics

noncomputable section

namespace JonesMatrix

/-!

## A. Exact Jones and pure-coherency output
-/

/-- A linear polarizer followed by a linear retarder selects the analyzer amplitude and then
expresses the transmitted axis in the retarder principal-axis basis. -/
lemma linearRetarder_comp_linearPolarizer_act
    (retarderAxis retardance polarizerAxis : Real.Angle) (J : JonesVector) :
    ((linearRetarder retarderAxis retardance).comp
      (linearPolarizer polarizerAxis)).act J =
        JonesVector.scale (J.linearComponent polarizerAxis)
          (JonesVector.ofLinearComponents retarderAxis
            (Real.Angle.cos (polarizerAxis - retarderAxis))
            (linearRetarderPhase retardance *
              Real.Angle.sin (polarizerAxis - retarderAxis))) := by
  rw [comp_act, linearPolarizer_act, act_scale,
    linearRetarder_act_linearPolarization]

/-- Pure-coherency transport through the polarizer-retarder cascade agrees with the coherency of
the exact Jones output. -/
lemma linearRetarder_comp_linearPolarizer_map_coherency
    (retarderAxis retardance polarizerAxis : Real.Angle) (J : JonesVector) :
    J.coherency.map
        (((linearRetarder retarderAxis retardance).comp
          (linearPolarizer polarizerAxis)).entries) =
      (JonesVector.scale (J.linearComponent polarizerAxis)
        (JonesVector.ofLinearComponents retarderAxis
          (Real.Angle.cos (polarizerAxis - retarderAxis))
          (linearRetarderPhase retardance *
            Real.Angle.sin (polarizerAxis - retarderAxis)))).coherency := by
  rw [← act_coherency, linearRetarder_comp_linearPolarizer_act]

/-!

## B. Arbitrary raw-Stokes action
-/

/-- The induced Mueller action of a polarizer-retarder cascade selects the polarizer's raw Stokes
scalar and applies the retarder polarization block to the resulting axial polarization. -/
lemma linearRetarder_comp_linearPolarizer_mueller_act
    (retarderAxis retardance polarizerAxis : Real.Angle) (S : StokesVector) :
    let q := S.linearPolarizerOutputIntensity polarizerAxis
    ((linearRetarder retarderAxis retardance).comp
      (linearPolarizer polarizerAxis)).mueller.act S =
        StokesVector.ofIntensityPolarization q
          (Matrix.toLpLin 2 2
            (linearRetarderPolarizationBlock retarderAxis retardance)
            (q • StokesVector.linearPolarizationDirection polarizerAxis)) := by
  rw [mueller_comp, MuellerMatrix.comp_act, linearPolarizer_mueller_act,
    linearRetarder_mueller_act]
  rfl

/-!

## C. Convention-sensitive connected regression
-/

/-- A `pi / 4` linear polarizer followed by a positive zero-axis quarter-wave plate sends the
horizontal unit input to the negative-`I` quadrature state with equal-component amplitude. -/
lemma quarterWavePlate_zero_comp_linearPolarizer_pi_div_four_act_horizontal :
    ((quarterWavePlate 0).comp
      (linearPolarizer ((Real.pi / 4 : ℝ) : Real.Angle))).act
        JonesVector.horizontal =
      JonesVector.scale JonesVector.unitEqualAmplitude
        JonesVector.minusIQuadrature := by
  have hQuarterWavePlate :
      (quarterWavePlate 0).act JonesVector.diagonal =
        JonesVector.minusIQuadrature := by
    have hPhase : (0 : Real.Angle) - ((Real.pi / 2 : ℝ) : Real.Angle) =
        ((-Real.pi / 2 : ℝ) : Real.Angle) := by
      rw [zero_sub, ← Real.Angle.coe_neg]
      congr 1
      ring
    rw [quarterWavePlate, ← JonesVector.equalAmplitudeRelativePhase_zero,
      linearRetarder_zero_axis_act_equalAmplitudeRelativePhase, hPhase,
      JonesVector.equalAmplitudeRelativePhase_neg_pi_div_two]
  rw [← JonesVector.linearPolarization_zero, comp_act,
    linearPolarizer_act_linearPolarization, act_scale,
    JonesVector.linearPolarization_pi_div_four,
    hQuarterWavePlate]
  congr 1
  rw [zero_sub, Real.Angle.cos_neg]
  change (Real.cos (Real.pi / 4) : ℂ) = JonesVector.unitEqualAmplitude
  rw [Real.cos_pi_div_four]
  rfl

end JonesMatrix

end

end Optics
