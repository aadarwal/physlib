/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Components.Retarder.Basic
public import Physlib.Optics.Polarization.JonesCoherency

/-!
# Pure-coherency transport through ideal linear retarders

## i. Overview

This file connects the exact Jones actions of an ideal linear retarder to pure polarization
coherency. It records the output coherency matrices for arbitrary linear input and for the
normalized equal-amplitude relative-phase family.

The generic congruence law remains in `Optics.Polarization.JonesCoherency`; this component module
adds only exact-output retarder formulas. No electromagnetic power interpretation is made.

## ii. Key results

- `JonesMatrix.linearRetarder_map_linearPolarization`.
- `JonesMatrix.linearRetarder_zero_axis_map_equalAmplitudeRelativePhase`.

## iii. Table of contents

- A. Exact pure-coherency outputs

## iv. References

Both results are derived from the public Jones/coherency commuting square.
-/

@[expose] public section

namespace Optics

noncomputable section

namespace JonesMatrix

/-!

## A. Exact pure-coherency outputs
-/

/-- Retarder coherency transport of a pure linear input agrees with its exact principal-axis
Jones decomposition. -/
lemma linearRetarder_map_linearPolarization (axis retardance input : Real.Angle) :
    (JonesVector.linearPolarization input).coherency.map
        (linearRetarder axis retardance).entries =
      (JonesVector.ofLinearComponents axis
        (Real.Angle.cos (input - axis))
        (linearRetarderPhase retardance *
          Real.Angle.sin (input - axis))).coherency := by
  rw [← act_coherency, linearRetarder_act_linearPolarization]

/-- Zero-axis retarder coherency transport subtracts retardance from the relative phase of the
equal-amplitude Jones family. -/
lemma linearRetarder_zero_axis_map_equalAmplitudeRelativePhase
    (retardance relativePhase : Real.Angle) :
    (JonesVector.equalAmplitudeRelativePhase relativePhase).coherency.map
        (linearRetarder 0 retardance).entries =
      (JonesVector.equalAmplitudeRelativePhase
        (relativePhase - retardance)).coherency := by
  rw [← act_coherency,
    linearRetarder_zero_axis_act_equalAmplitudeRelativePhase]

end JonesMatrix

end

end Optics
