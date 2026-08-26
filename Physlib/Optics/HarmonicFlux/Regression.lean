/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.HarmonicFlux.Basic

/-!
# Harmonic Poynting-flux convention regressions

## i. Overview

This file pins the factor and conjugation conventions in `timeAveragedPoyntingVector` with exact
three-coordinate phasors. The linear case fixes the factor one half. The quadrature case has a
nonzero result precisely because the magnetic phasor is conjugated before taking the complex
cross product.

## ii. Key results

- `timeAveragedPoyntingVector_linear_phasor_regression`: factor-one-half regression.
- `timeAveragedPoyntingVector_conjugation_regression`: second-phasor conjugation regression.

## iii. Table of contents

- A. Exact phasor regressions

## iv. References

These results test only the local peak-phasor formula. They assign no polarization handedness,
Maxwell, propagation, irradiance, or modal-power meaning to the selected coordinate arrays.

-/

@[expose] public section

namespace Optics

open ClassicalMechanics Electromagnetism.ThreeDimension Matrix

noncomputable section

/-!

## A. Exact phasor regressions

-/

/-- Orthogonal real unit phasors have average Poynting vector one half along the third
coordinate. -/
lemma timeAveragedPoyntingVector_linear_phasor_regression :
    timeAveragedPoyntingVector
        (WithLp.toLp 2 ![(1 : ℂ), 0, 0])
        (WithLp.toLp 2 ![(0 : ℂ), 1, 0]) =
      WithLp.toLp 2 ![(0 : ℝ), 0, 1 / 2] := by
  ext i
  fin_cases i <;>
    simp [timeAveragedPoyntingVector,
      ComplexMonochromaticPlaneWave.complexCross, ComplexWaveVector.realPart,
      Phasor.conjugateEuclidean, crossProduct]

/-- The quadrature phasors `(1, I, 0)` and `(-I, 1, 0)` give unit average flux along the third
coordinate, which detects conjugation of the magnetic phasor. -/
lemma timeAveragedPoyntingVector_conjugation_regression :
    timeAveragedPoyntingVector
        (WithLp.toLp 2 ![(1 : ℂ), Complex.I, 0])
        (WithLp.toLp 2 ![-Complex.I, 1, 0]) =
      WithLp.toLp 2 ![(0 : ℝ), 0, 1] := by
  ext i
  fin_cases i <;>
    simp [timeAveragedPoyntingVector,
      ComplexMonochromaticPlaneWave.complexCross, ComplexWaveVector.realPart,
      Phasor.conjugateEuclidean, crossProduct]
  norm_num

end

end Optics
