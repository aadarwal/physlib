/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Interfaces.PlanarDielectric.FresnelFluxRegression
public import Physlib.Optics.Interfaces.PlanarDielectric.FresnelScattering

/-!
# Regressions for power-normalized scalar Fresnel scattering

## i. Overview

This file applies the scalar scattering kernels to the exact oblique unequal-admittance fixture.
The raw normal-admittance ratio is `3/8`; square-root normalization converts the established s/p
electric transmission amplitudes into `4 sqrt(6) / 11` and `2 sqrt(6) / 5`. The complete matrices
pin the negative-side/positive-side ordering, the full-vector p reflection sign, the opposite
second diagonal, and equal off-diagonal completion entries.

These regressions test an algebraic unitary completion of the established left-incident columns.
They do not provide the still-missing reverse-incidence Maxwell derivation or physical port/frame
transport.

## ii. Key results

- `fresnelScatteringRegression_s_normalizedTransmission`: exact normalized s transmission.
- `fresnelScatteringRegression_p_normalizedTransmission`: exact normalized p transmission.
- `fresnelScatteringRegression_kernel_values`: both exact matrices and losslessness certificates.

## iii. Table of contents

- A. Exact square-root normalization
- B. Exact s/p kernels

## iv. References

The fixture is the existing independently solved `3-4-5` planar-boundary regression. No external
scattering implementation is copied or translated here. No outgoing, reciprocity, reverse-
incidence, modal-completeness, grazing, TIR-port, or lossy-medium claim is made.
-/

@[expose] public section

namespace Optics

open Electromagnetism Matrix PlanarDielectricInterface

noncomputable section

/-!
## A. Exact square-root normalization
-/

/-- The oblique s electric transmission amplitude becomes `4 sqrt(6) / 11` after power
normalization. -/
lemma fresnelScatteringRegression_s_normalizedTransmission :
    powerNormalizedFresnelTransmissionCoefficient (3 / 8) (16 / 11) =
      4 * Real.sqrt 6 / 11 := by
  have hFactor : (0 : ℝ) ≤ 3 / 8 := by norm_num
  have hSix : (0 : ℝ) ≤ 6 := by norm_num
  have hFactorSq : Real.sqrt (3 / 8 : ℝ) ^ 2 = 3 / 8 := Real.sq_sqrt hFactor
  have hSixSq : Real.sqrt (6 : ℝ) ^ 2 = 6 := Real.sq_sqrt hSix
  have hLeft : 0 ≤ Real.sqrt (3 / 8 : ℝ) * (16 / 11) :=
    mul_nonneg (Real.sqrt_nonneg _) (by norm_num)
  have hRight : 0 ≤ 4 * Real.sqrt (6 : ℝ) / 11 := by positivity
  rw [powerNormalizedFresnelTransmissionCoefficient]
  nlinarith

/-- The oblique p electric transmission amplitude becomes `2 sqrt(6) / 5` after power
normalization. -/
lemma fresnelScatteringRegression_p_normalizedTransmission :
    powerNormalizedFresnelTransmissionCoefficient (3 / 8) (8 / 5) =
      2 * Real.sqrt 6 / 5 := by
  have hFactor : (0 : ℝ) ≤ 3 / 8 := by norm_num
  have hSix : (0 : ℝ) ≤ 6 := by norm_num
  have hFactorSq : Real.sqrt (3 / 8 : ℝ) ^ 2 = 3 / 8 := Real.sq_sqrt hFactor
  have hSixSq : Real.sqrt (6 : ℝ) ^ 2 = 6 := Real.sq_sqrt hSix
  have hLeft : 0 ≤ Real.sqrt (3 / 8 : ℝ) * (8 / 5) :=
    mul_nonneg (Real.sqrt_nonneg _) (by norm_num)
  have hRight : 0 ≤ 2 * Real.sqrt (6 : ℝ) / 5 := by positivity
  rw [powerNormalizedFresnelTransmissionCoefficient]
  nlinarith

/-!
## B. Exact s/p kernels
-/

/-- The unequal-admittance fixture fixes both normalized scalar kernels and their losslessness.

The two diagonal signs differ in each kernel, while the s and p first-column reflections remain
distinct. This prevents raw electric transmission, an inverted flux ratio, a p-sign change, or a
same-sign reverse diagonal from satisfying the fixture. -/
lemma fresnelScatteringRegression_kernel_values :
    (jonesBoundaryRegressionInterface.sFresnelScatteringKernel
      (4 / 5) (3 / 5)).toModeTransform =
      !![
        (((5 / 11 : ℝ) : ℂ)), (((4 * Real.sqrt 6 / 11 : ℝ) : ℂ));
        (((4 * Real.sqrt 6 / 11 : ℝ) : ℂ)), (((-5 / 11 : ℝ) : ℂ))] ∧
    (jonesBoundaryRegressionInterface.pFresnelScatteringKernel
      (4 / 5) (3 / 5)).toModeTransform =
      !![
        (((-1 / 5 : ℝ) : ℂ)), (((2 * Real.sqrt 6 / 5 : ℝ) : ℂ));
        (((2 * Real.sqrt 6 / 5 : ℝ) : ℂ)), (((1 / 5 : ℝ) : ℂ))] ∧
    (jonesBoundaryRegressionInterface.sFresnelScatteringKernel
      (4 / 5) (3 / 5)).IsLossless ∧
    (jonesBoundaryRegressionInterface.pFresnelScatteringKernel
      (4 / 5) (3 / 5)).IsLossless := by
  rcases jonesBoundaryRegression_fresnelCoefficient_values with ⟨hrs, hts, hrp, htp⟩
  have hFactor := fresnelFluxRegression_oblique.1
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [sFresnelScatteringKernel, scalarFresnelScatteringKernel, hrs, hts, hFactor,
        fresnelScatteringRegression_s_normalizedTransmission]; norm_num
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pFresnelScatteringKernel, scalarFresnelScatteringKernel, hrp, htp, hFactor,
        fresnelScatteringRegression_p_normalizedTransmission]; norm_num
  exact ⟨
    jonesBoundaryRegressionInterface.sFresnelScatteringKernel_isLossless
      (by norm_num) (by norm_num),
    jonesBoundaryRegressionInterface.pFresnelScatteringKernel_isLossless
      (by norm_num) (by norm_num)⟩

end

end Optics
