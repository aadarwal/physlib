/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public
import Physlib.Electromagnetism.ThreeDimension.MonochromaticPlaneWave.ComplexDispersionRegression
public import Physlib.Optics.Polarization.PositiveNormalDecayFrame

/-!
# Regression tests for positive-normal-decay polarization frames

## i. Overview

This file applies `PositiveNormalDecayPolarizationFrame` to the independently defined exact
complex plane-wave fixture

`K = (5, 0, -4 I), beta = 3`.

With positive third-coordinate decay normal, the canonical axes are

```text
s = (0, 1, 0), p = (4 I / 3, 0, 5 / 3).
```

The regression checks `p dot p = 1` for the complex-bilinear pairing while its Hermitian squared
norm is `41 / 9`. It also recovers the existing TE amplitude from Jones coordinates `(1, 0)` and
the existing TM amplitude from `(0, -3 I)`, including both independently defined compatible
magnetic-induction amplitudes. The identities `K cross E0 = B0` use the fixture's unit angular
frequency.

## ii. Key results

- `complexDecayRegressionPolarizationFrame_sAxis`: the exact canonical `s` axis.
- `complexDecayRegressionPolarizationFrame_planePAxis`: the exact real fixed-plane `p` axis.
- `complexDecayRegressionPolarizationFrame_pAxis`: the exact complex `p` axis.
- `complexDecayRegressionPolarizationFrame_tangentialProjection_pAxis`: the exact fixed-plane
  tangential `p` component, including its convention-dependent sign.
- `complexDecayRegressionPolarizationFrame_pAxis_bilinearSquare`: bilinear unit normalization.
- `complexDecayRegressionPolarizationFrame_pAxis_norm_sq`: Hermitian squared norm `41 / 9`.
- `complexDecayRegressionPolarizationFrame_embedJones_TE` and
  `complexDecayRegressionPolarizationFrame_embedJones_TM`: recovery of both existing electric
  amplitudes.
- `complexDecayRegressionPolarizationFrame_cross_embedJones_TE` and
  `complexDecayRegressionPolarizationFrame_cross_embedJones_TM`: recovery of both existing
  magnetic amplitudes.

## iii. Table of contents

- A. Exact decay frame
- B. Bilinear and Hermitian axis checks
- C. Electric and magnetic amplitude recovery

## iv. References

These are exact regressions for Physlib's existing complex-decay carrier and the independently
defined positive-normal-decay polarization-frame API. No external source is used.
-/

@[expose] public section

namespace Optics

open ClassicalMechanics Electromagnetism Electromagnetism.ThreeDimension Space Matrix
open ClassicalMechanics.ComplexWaveVector
open Electromagnetism.ThreeDimension.ComplexMonochromaticPlaneWave
open PositiveNormalDecayPolarizationFrame

noncomputable section

/-!

## A. Exact decay frame

-/

/-- The coordinate plane with positive third-coordinate normal used to decode tangential
components of the exact decay frame. -/
def complexDecayRegressionPlane : OrientedAffineHyperplane 3 where
  point := 0
  normal := positiveNormalDecayRegressionDirection

/-- The positive-normal-decay polarization frame for the exact `5-4-3` complex-wave fixture. -/
def complexDecayRegressionPolarizationFrame :
    PositiveNormalDecayPolarizationFrame complexDecayRegressionPlane.normal where
  data := positiveNormalDecayRegression 5 4 (by norm_num)
  waveNumber := 3
  waveNumber_pos := by norm_num
  bilinearSquare := by
    change bilinearDot complexDecayRegressionWaveVector complexDecayRegressionWaveVector =
      (3 : ℂ) ^ 2
    rw [complexDecayRegression_bilinearSquare]
    norm_num

/-- The exact frame has shell wavenumber three. -/
lemma complexDecayRegressionPolarizationFrame_waveNumber :
    complexDecayRegressionPolarizationFrame.waveNumber = 3 := rfl

/-- The exact frame carries the existing complex wave vector `(5, 0, -4 I)`. -/
lemma complexDecayRegressionPolarizationFrame_waveVector :
    complexDecayRegressionPolarizationFrame.data.waveVector =
      complexDecayRegressionWaveVector := rfl

/-- The exact canonical `s` axis is the positive second-coordinate unit vector. -/
lemma complexDecayRegressionPolarizationFrame_sAxis :
    complexDecayRegressionPolarizationFrame.sAxis =
      WithLp.toLp 2 ![(0 : ℂ), 1, 0] := by
  ext i
  fin_cases i <;>
    simp [PositiveNormalDecayPolarizationFrame.sAxis,
      PositiveNormalDecayPolarizationFrame.realSAxis,
      complexDecayRegressionPolarizationFrame, positiveNormalDecayRegression,
      positiveNormalDecayRegressionTangentialVector,
      PositiveNormalDecayWaveVector.normalVector,
      complexDecayRegressionPlane, positiveNormalDecayRegressionDirection,
      NormedSpace.normalize,
      EuclideanSpace.norm_eq, Fin.sum_univ_three, crossProduct]

/-- The exact real in-plane `p` axis is the negative first-coordinate unit vector. -/
lemma complexDecayRegressionPolarizationFrame_planePAxis :
    complexDecayRegressionPolarizationFrame.planePAxis =
      WithLp.toLp 2 ![-1, 0, 0] := by
  rw [PositiveNormalDecayPolarizationFrame.planePAxis_eq_normalVector_cross_realSAxis]
  ext i
  fin_cases i <;>
    simp [complexDecayRegressionPolarizationFrame, positiveNormalDecayRegression,
      PositiveNormalDecayWaveVector.normalVector,
      complexDecayRegressionPlane, positiveNormalDecayRegressionDirection,
      PositiveNormalDecayPolarizationFrame.realSAxis, NormedSpace.normalize,
      positiveNormalDecayRegressionTangentialVector, EuclideanSpace.norm_eq,
      Fin.sum_univ_three, crossProduct]

/-- The exact complex `p` axis is `(4 I / 3, 0, 5 / 3)`. -/
lemma complexDecayRegressionPolarizationFrame_pAxis :
    complexDecayRegressionPolarizationFrame.pAxis =
      WithLp.toLp 2 ![4 * Complex.I / 3, 0, (5 / 3 : ℂ)] := by
  ext i
  fin_cases i <;>
    simp [PositiveNormalDecayPolarizationFrame.pAxis,
      complexDecayRegressionPolarizationFrame_sAxis,
      complexDecayRegressionPolarizationFrame_waveVector,
      complexDecayRegressionPolarizationFrame_waveNumber,
      complexDecayRegressionWaveVector_eq, complexCross, crossProduct]
  all_goals ring

/-- The exact normalized normal factor is `-4 I / 3`. -/
lemma complexDecayRegressionPolarizationFrame_normalizedWaveVectorNormalComponent :
    complexDecayRegressionPolarizationFrame.normalizedWaveVectorNormalComponent
        complexDecayRegressionPlane =
      -4 * Complex.I / 3 := by
  rw [normalizedWaveVectorNormalComponent_eq_neg_I_mul]
  norm_num [complexDecayRegressionPolarizationFrame,
    positiveNormalDecayRegression]
  ring

/-- The exact fixed-plane tangential projection of `p` is `(4 I / 3, 0, 0)`. -/
lemma complexDecayRegressionPolarizationFrame_tangentialProjection_pAxis :
    hyperplaneTangentialProjection complexDecayRegressionPlane
        complexDecayRegressionPolarizationFrame.pAxis =
      WithLp.toLp 2 ![4 * Complex.I / 3, 0, 0] := by
  rw [complexDecayRegressionPolarizationFrame.hyperplaneTangentialProjection_pAxis,
    complexDecayRegressionPolarizationFrame_normalizedWaveVectorNormalComponent,
    complexDecayRegressionPolarizationFrame_planePAxis]
  ext i
  fin_cases i <;> simp [ComplexWaveVector.ofReal]
  ring

/-!

## B. Bilinear and Hermitian axis checks

-/

/-- The exact complex `p` axis has bilinear square one. -/
lemma complexDecayRegressionPolarizationFrame_pAxis_bilinearSquare :
    bilinearDot complexDecayRegressionPolarizationFrame.pAxis
      complexDecayRegressionPolarizationFrame.pAxis = 1 :=
  complexDecayRegressionPolarizationFrame.bilinearDot_pAxis_self

/-- The exact complex `p` axis has Hermitian squared norm `41 / 9`, not one. -/
lemma complexDecayRegressionPolarizationFrame_pAxis_norm_sq :
    ‖complexDecayRegressionPolarizationFrame.pAxis‖ ^ 2 = 41 / 9 := by
  rw [complexDecayRegressionPolarizationFrame_pAxis, EuclideanSpace.norm_sq_eq]
  simp [Fin.sum_univ_three]
  norm_num

/-- The exact complex `p` axis is not Hermitian-unit. -/
lemma complexDecayRegressionPolarizationFrame_pAxis_norm_sq_ne_one :
    ‖complexDecayRegressionPolarizationFrame.pAxis‖ ^ 2 ≠ 1 := by
  rw [complexDecayRegressionPolarizationFrame_pAxis_norm_sq]
  norm_num

/-- The exact frame satisfies `K cross p = -3 s`. -/
lemma complexDecayRegressionPolarizationFrame_cross_pAxis :
    complexCross complexDecayRegressionWaveVector
        complexDecayRegressionPolarizationFrame.pAxis =
      -(3 : ℂ) • complexDecayRegressionPolarizationFrame.sAxis := by
  rw [← complexDecayRegressionPolarizationFrame_waveVector]
  exact complexDecayRegressionPolarizationFrame.complexCross_waveVector_pAxis

/-!

## C. Electric and magnetic amplitude recovery

-/

/-- The raw TE Jones coordinates `(1, 0)`. -/
def complexDecayRegressionTEJones : JonesVector :=
  JonesVector.ofComponents 1 0

/-- The raw TM Jones coordinates `(0, -3 I)` in the bilinearly normalized complex frame. -/
def complexDecayRegressionTMJones : JonesVector :=
  JonesVector.ofComponents 0 (-3 * Complex.I)

/-- Embedding the TE coordinates recovers the existing TE electric amplitude. -/
lemma complexDecayRegressionPolarizationFrame_embedJones_TE :
    complexDecayRegressionPolarizationFrame.embedJones complexDecayRegressionTEJones =
      complexDecayRegressionTE.electricAmplitude := by
  rw [PositiveNormalDecayPolarizationFrame.embedJones_eq,
    complexDecayRegressionPolarizationFrame_sAxis,
    complexDecayRegressionPolarizationFrame_pAxis]
  ext i
  fin_cases i <;> simp [complexDecayRegressionTEJones, complexDecayRegressionTE]

/-- Embedding the TM coordinates recovers the existing TM electric amplitude. -/
lemma complexDecayRegressionPolarizationFrame_embedJones_TM :
    complexDecayRegressionPolarizationFrame.embedJones complexDecayRegressionTMJones =
      complexDecayRegressionTM.electricAmplitude := by
  rw [PositiveNormalDecayPolarizationFrame.embedJones_eq,
    complexDecayRegressionPolarizationFrame_sAxis,
    complexDecayRegressionPolarizationFrame_pAxis]
  ext i
  fin_cases i <;>
    simp [complexDecayRegressionTMJones, complexDecayRegressionTM]
  all_goals ring_nf
  all_goals rw [Complex.I_sq]
  all_goals norm_num

/-- The exact TM electric amplitude projects to `(4, 0, 0)` in the stored decay-normal plane. -/
lemma complexDecayRegressionPolarizationFrame_tangentialProjection_embedJones_TM :
    hyperplaneTangentialProjection complexDecayRegressionPlane
        (complexDecayRegressionPolarizationFrame.embedJones complexDecayRegressionTMJones) =
      WithLp.toLp 2 ![(4 : ℂ), 0, 0] := by
  rw [complexDecayRegressionPolarizationFrame_embedJones_TM]
  ext i
  fin_cases i <;>
    simp [hyperplaneTangentialProjection, hyperplaneNormalComponent,
      bilinearDot, complexDecayRegressionTM, complexDecayRegressionPlane,
      positiveNormalDecayRegressionDirection, ComplexWaveVector.ofReal,
      OrientedAffineHyperplane.normalVector, Space.basis,
      Fin.sum_univ_three]

/-- Applying the Jones propagation quarter-turn to the exact TM coordinates embeds as
`(0, 3 I, 0)`. -/
lemma complexDecayRegressionPolarizationFrame_embedJones_propagationCross_TM :
    complexDecayRegressionPolarizationFrame.embedJones
        complexDecayRegressionTMJones.propagationCross =
      WithLp.toLp 2 ![(0 : ℂ), 3 * Complex.I, 0] := by
  rw [PositiveNormalDecayPolarizationFrame.embedJones_eq,
    complexDecayRegressionPolarizationFrame_sAxis,
    complexDecayRegressionPolarizationFrame_pAxis]
  ext i
  fin_cases i <;> simp [complexDecayRegressionTMJones]

/-- The quarter-turned exact TM embedding is already tangent to the stored decay-normal plane. -/
lemma complexDecayRegressionPolarizationFrame_tangentialProjection_embedJones_propagationCross_TM :
    hyperplaneTangentialProjection complexDecayRegressionPlane
        (complexDecayRegressionPolarizationFrame.embedJones
          complexDecayRegressionTMJones.propagationCross) =
      WithLp.toLp 2 ![(0 : ℂ), 3 * Complex.I, 0] := by
  rw [complexDecayRegressionPolarizationFrame_embedJones_propagationCross_TM]
  ext i
  fin_cases i <;>
    simp [hyperplaneTangentialProjection, hyperplaneNormalComponent,
      bilinearDot, complexDecayRegressionPlane,
      positiveNormalDecayRegressionDirection, ComplexWaveVector.ofReal,
      OrientedAffineHyperplane.normalVector, Space.basis,
      Fin.sum_univ_three]

/-- Crossing `K` with the embedded TE coordinates recovers the existing compatible TE magnetic
amplitude. -/
lemma complexDecayRegressionPolarizationFrame_cross_embedJones_TE :
    complexCross complexDecayRegressionWaveVector
        (complexDecayRegressionPolarizationFrame.embedJones complexDecayRegressionTEJones) =
      complexDecayRegressionTE.magneticAmplitude := by
  rw [complexDecayRegressionPolarizationFrame_embedJones_TE,
    complexDecayRegressionTE_magneticAmplitude]
  ext i
  fin_cases i <;>
    simp [complexDecayRegressionTE, complexDecayRegressionWaveVector_eq,
      complexCross, crossProduct]

/-- Crossing `K` with the embedded TM coordinates recovers the existing compatible TM magnetic
amplitude. -/
lemma complexDecayRegressionPolarizationFrame_cross_embedJones_TM :
    complexCross complexDecayRegressionWaveVector
        (complexDecayRegressionPolarizationFrame.embedJones complexDecayRegressionTMJones) =
      complexDecayRegressionTM.magneticAmplitude := by
  rw [complexDecayRegressionPolarizationFrame_embedJones_TM,
    complexDecayRegressionTM_magneticAmplitude]
  ext i
  fin_cases i <;>
    simp [complexDecayRegressionTM, complexDecayRegressionWaveVector_eq,
      complexCross, crossProduct]
  all_goals ring

end

end Optics
