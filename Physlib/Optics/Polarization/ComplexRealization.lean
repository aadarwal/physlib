/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.ClassicalMechanics.WaveEquation.ComplexWaveVector
public import Physlib.Optics.Polarization.Basic

/-!
# Complex realization of Euclidean phasor arrays

## i. Overview

This file connects the Optics componentwise phasor-realization convention to the componentwise
real-part operation used by complex wave carriers. It records the positive-exponential carrier
and scalar-action order explicitly, so later field bridges can reuse the convention without
adding wave-equation dependencies to the Jones foundations.

## ii. Key results

- `Phasor.realizeEuclidean_eq_realPart_exp_smul`: Euclidean phasor realization as the real part
  of a positive-exponential carrier scaling.

## iii. Table of contents

- A. Positive-exponential carrier realization

## iv. References

The result is a pointwise representation identity. It introduces no wave vector,
electromagnetic-field, harmonic-average, irradiance, power, or evanescence claim.

-/

@[expose] public section

namespace Optics

open ClassicalMechanics

noncomputable section

/-!

## A. Positive-exponential carrier realization

-/

/-- Componentwise phasor realization is the componentwise real part of the amplitude scaled by
the positive-exponential carrier phase.

This is the vector form of
`Phasor.realize z phase = Re (z * exp ((phase : ℂ) * I))`; complex commutativity writes the
common carrier as the scalar action `exp ((phase : ℂ) * I) • amplitude`. -/
lemma Phasor.realizeEuclidean_eq_realPart_exp_smul {d : ℕ}
    (amplitude : EuclideanSpace ℂ (Fin d)) (carrierPhase : ℝ) :
    Phasor.realizeEuclidean amplitude carrierPhase =
      ComplexWaveVector.realPart
        (Complex.exp ((carrierPhase : ℂ) * Complex.I) • amplitude) := by
  ext i
  simp only [Phasor.realizeEuclidean_apply, Phasor.realize,
    ComplexWaveVector.realPart_apply, PiLp.smul_apply, smul_eq_mul]
  rw [mul_comm]

end

end Optics
