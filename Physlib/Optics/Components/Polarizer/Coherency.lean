/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Components.Polarizer.Malus
public import Physlib.Optics.Polarization.JonesCoherency

/-!
# Coherency transport through an ideal linear polarizer

## i. Overview

This file connects the ideal linear-polarizer Jones action to the shared polarization-coherency
API. For a scaled linear Jones input, coherency transport returns the outer product of the exact
Malus amplitude, and its trace obeys the same squared-cosine law.

The results are derived through `JonesMatrix.act_coherency`; they do not introduce a second
component-specific transport definition.

## ii. Key results

- `JonesMatrix.linearPolarizer_map_scaled_linearPolarization`: exact transported coherency.
- `JonesMatrix.linearPolarizer_map_scaled_linearPolarization_trace`: trace form of Malus' law.

## iii. Table of contents

- A. Pure linear coherency

## iv. References

The connection is derived through Physlib's existing Jones/coherency commuting square.
-/

@[expose] public section

namespace Optics

noncomputable section

namespace JonesMatrix

/-!

## A. Pure linear coherency
-/

/-- Coherency transport through a linear polarizer agrees with the coherency of the exact coherent
Malus output amplitude. -/
lemma linearPolarizer_map_scaled_linearPolarization (z : ℂ)
    (analyzer input : Real.Angle) :
    (JonesVector.scale z (JonesVector.linearPolarization input)).coherency.map
        (linearPolarizer analyzer).entries =
      (JonesVector.scale
        (z * (Real.Angle.cos (input - analyzer) : ℂ))
        (JonesVector.linearPolarization analyzer)).coherency := by
  rw [← act_coherency, linearPolarizer_act_scaled_linearPolarization]

/-- The trace of transported pure linear coherency obeys the squared-cosine law. -/
lemma linearPolarizer_map_scaled_linearPolarization_trace (z : ℂ)
    (analyzer input : Real.Angle) :
    ((JonesVector.scale z (JonesVector.linearPolarization input)).coherency.map
        (linearPolarizer analyzer).entries).trace =
      (JonesVector.scale z (JonesVector.linearPolarization input)).coherency.trace *
        Real.Angle.cos (input - analyzer) ^ 2 := by
  rw [← act_coherency, JonesVector.coherency_trace, JonesVector.coherency_trace,
    linearPolarizer_malus]

end JonesMatrix

end

end Optics
