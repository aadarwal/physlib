/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Electromagnetism.ThreeDimension.MonochromaticPlaneWave.ComplexConverse
public
import Physlib.Electromagnetism.ThreeDimension.MonochromaticPlaneWave.ComplexDispersionRegression
public import Physlib.Electromagnetism.ThreeDimension.MonochromaticPlaneWave.Converse

/-!
# Regression tests for complex plane-wave Maxwell laws

## i. Overview

This module connects the exact attenuating TE and TM algebra from
`ComplexDispersionRegression` to ordinary real electromagnetic fields and to the source-free
macroscopic Maxwell predicate. With

`A(x) = exp (-4 x_2)` and `theta(t, x) = t - 5 x_0`,

it fixes the exact fields

`E_TE = (0, A cos theta, 0)`, `B_TE = (-4 A sin theta, 0, 5 A cos theta)`,

`E_TM = (4 A cos theta, 0, 5 A sin theta)`, `B_TM = (0, -9 A sin theta, 0)`.

The module also fixes three counterexamples around the converse boundary. Zero electric amplitude
solves Maxwell off shell. A nontransverse candidate has zero electric-displacement divergence at
one carrier phase but not one quarter-period later. A nonzero complex-null electric amplitude can be
bilinearly transverse and satisfy magnetic Gauss, Faraday, and electric Gauss while failing
Ampere--Maxwell.

Finally, a concrete nonzero real-quadrature wave exercises the exact amplitude guard and shows
that the real and embedded-complex guarded converses reduce to the same real transversality and
dispersion predicates. This embedded-image check does not validate the genuinely complex
counterexamples; those are tested separately.

These are exact regression fixtures, not a completeness result. The attenuating data has no
interface-side, transmitted, outgoing, or evanescent-wave role here. No result assigns irradiance
or power, and the degenerate fixtures are not asserted to be physical propagation modes.

## ii. Key results

- `complexDecayRegressionTE_electricField` and
  `complexDecayRegressionTM_electricField`: exact ordinary real electric fields.
- `complexDecayRegressionTE_magneticInduction` and
  `complexDecayRegressionTM_magneticInduction`: exact ordinary real magnetic inductions.
- `complexDecayRegressionTE_isSourceFreeMacroscopicMaxwell` and
  `complexDecayRegressionTM_isSourceFreeMacroscopicMaxwell`: exact Maxwell endpoints.
- `complexZeroAmplitudeRegression_not_isDispersionMatched`: the necessary zero-amplitude guard.
- `complexOnePhaseRegression_electricDisplacement_div_samples`: one phase does not recover a complex
  amplitude equation.
- `complexNullVectorRegression_ampereMaxwellLaw_fails_at_origin`: three source-free laws do not
  imply the fourth for a complex-null fixture.
- `realEmbeddingRegression_ofReal_isSourceFreeMacroscopicMaxwell_iff`: the embedded complex
  converse has exactly the existing real predicates.

## iii. Table of contents

- A. Shared exact carrier
- B. TE ordinary fields and Maxwell laws
- C. TM ordinary fields and Maxwell laws
- D. Zero-amplitude off-shell degeneracy
- E. One-phase divergence counterexample
- F. Complex-null-vector counterexample
- G. Embedded real-wave coherence

## iv. References

This file regresses Physlib's own complex-carrier, dispersion, and Maxwell APIs. No external
formal-development source is copied or translated here.
-/

@[expose] public section

namespace Electromagnetism
namespace ThreeDimension

open Space Time InnerProductSpace Matrix ClassicalMechanics

noncomputable section

namespace ComplexMonochromaticPlaneWave

/-!

## A. Shared exact carrier

-/

/-- The positive real decay factor of the complex-decay Maxwell regression carrier. -/
def complexDecayRegressionDecayFactor (x : Space) : ℝ :=
  Real.exp (-4 * x 2)

/-- The real oscillatory phase of the complex-decay Maxwell regression carrier. -/
def complexDecayRegressionPhase (t : Time) (x : Space) : ℝ :=
  t - 5 * x 0

/-- The TE carrier is exactly `exp (-4 x_2) * exp (I * (t - 5 x_0))`. -/
lemma complexDecayRegressionTE_carrier (t : Time) (x : Space) :
    complexDecayRegressionTE.carrier t x =
      (complexDecayRegressionDecayFactor x : ℂ) *
        Complex.exp ((complexDecayRegressionPhase t x : ℝ) * Complex.I) := by
  rw [carrier_eq_exp]
  have hexponent :
      ((((complexDecayRegressionTE.angularFrequency * t : ℝ) : ℂ) -
          complexDecayRegressionTE.waveVector.spatialPairing x) * Complex.I) =
        ((-4 * x 2 : ℝ) : ℂ) +
          ((t - 5 * x 0 : ℝ) : ℂ) * Complex.I := by
    simp [complexDecayRegressionTE, complexDecayRegressionWaveVector_eq,
      ComplexWaveVector.spatialPairing, ComplexWaveVector.bilinearDot,
      Fin.sum_univ_three, Matrix.cons_val_two, Matrix.head_cons]
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [hexponent, Complex.exp_add, ← Complex.ofReal_exp]
  rfl

private lemma complexDecayRegressionTE_carrier_re (t : Time) (x : Space) :
    (complexDecayRegressionTE.carrier t x).re =
      complexDecayRegressionDecayFactor x *
        Real.cos (complexDecayRegressionPhase t x) := by
  rw [complexDecayRegressionTE_carrier]
  simp [Complex.mul_re]

private lemma complexDecayRegressionTE_carrier_im (t : Time) (x : Space) :
    (complexDecayRegressionTE.carrier t x).im =
      complexDecayRegressionDecayFactor x *
        Real.sin (complexDecayRegressionPhase t x) := by
  rw [complexDecayRegressionTE_carrier]
  simp [Complex.mul_im]

/-!

## B. TE ordinary fields and Maxwell laws

-/

private lemma complexDecayRegressionTE_electricAmplitude_eq :
    complexDecayRegressionTE.electricAmplitude =
      WithLp.toLp 2 ![(0 : ℂ), 1, 0] := rfl

/-- The TE fixture realizes the ordinary real electric field `(0, A cos theta, 0)`. -/
lemma complexDecayRegressionTE_electricField (t : Time) (x : Space) :
    complexDecayRegressionTE.electricField t x =
      WithLp.toLp 2 ![
        (0 : ℝ),
        complexDecayRegressionDecayFactor x *
          Real.cos (complexDecayRegressionPhase t x),
        0] := by
  ext i
  rw [electricField_apply, complexDecayRegressionTE_electricAmplitude_eq]
  fin_cases i <;>
    simp [complexDecayRegressionTE_carrier_re,
      Matrix.cons_val_two, Matrix.head_cons]

/-- The TE fixture realizes the ordinary real magnetic induction
`(-4 A sin theta, 0, 5 A cos theta)`. -/
lemma complexDecayRegressionTE_magneticInduction (t : Time) (x : Space) :
    complexDecayRegressionTE.magneticInduction t x =
      WithLp.toLp 2 ![
        -4 * complexDecayRegressionDecayFactor x *
          Real.sin (complexDecayRegressionPhase t x),
        (0 : ℝ),
        5 * complexDecayRegressionDecayFactor x *
          Real.cos (complexDecayRegressionPhase t x)] := by
  ext i
  rw [magneticInduction_apply, complexDecayRegressionTE_magneticAmplitude]
  fin_cases i <;>
    simp [Complex.mul_re, complexDecayRegressionTE_carrier_re,
      complexDecayRegressionTE_carrier_im,
      Matrix.cons_val_two, Matrix.head_cons]
  all_goals ring

/-- The TE fixture solves the source-free macroscopic Maxwell equations. -/
lemma complexDecayRegressionTE_isSourceFreeMacroscopicMaxwell :
    IsSourceFreeMacroscopicMaxwell complexDecayRegressionTE.electricField
      (complexDecayRegressionTE.electricDisplacement complexDecayRegressionMedium)
      complexDecayRegressionTE.magneticInduction
      (complexDecayRegressionTE.magneticFieldStrength complexDecayRegressionMedium) := by
  exact complexDecayRegressionTE.isSourceFreeMacroscopicMaxwell
    complexDecayRegressionMedium complexDecayRegressionTE_isTransverse
    complexDecayRegressionTE_isDispersionMatched

/-- The guarded source-free characterization specializes exactly to the TE fixture. -/
lemma complexDecayRegressionTE_isSourceFreeMacroscopicMaxwell_iff :
    IsSourceFreeMacroscopicMaxwell complexDecayRegressionTE.electricField
        (complexDecayRegressionTE.electricDisplacement complexDecayRegressionMedium)
        complexDecayRegressionTE.magneticInduction
        (complexDecayRegressionTE.magneticFieldStrength complexDecayRegressionMedium) ↔
      complexDecayRegressionTE.IsTransverse ∧
        complexDecayRegressionTE.IsDispersionMatched complexDecayRegressionMedium := by
  apply complexDecayRegressionTE.isSourceFreeMacroscopicMaxwell_iff
  intro h
  have hi := congrArg (fun v : EuclideanSpace ℂ (Fin 3) ↦ v 1) h
  norm_num [complexDecayRegressionTE] at hi

/-!

## C. TM ordinary fields and Maxwell laws

-/

private lemma complexDecayRegressionTM_electricAmplitude_eq :
    complexDecayRegressionTM.electricAmplitude =
      WithLp.toLp 2 ![(4 : ℂ), 0, -5 * Complex.I] := rfl

/-- The TM carrier is exactly `exp (-4 x_2) * exp (I * (t - 5 x_0))`. -/
lemma complexDecayRegressionTM_carrier (t : Time) (x : Space) :
    complexDecayRegressionTM.carrier t x =
      (complexDecayRegressionDecayFactor x : ℂ) *
        Complex.exp ((complexDecayRegressionPhase t x : ℝ) * Complex.I) := by
  change complexDecayRegressionTE.carrier t x = _
  exact complexDecayRegressionTE_carrier t x

private lemma complexDecayRegressionTM_carrier_re (t : Time) (x : Space) :
    (complexDecayRegressionTM.carrier t x).re =
      complexDecayRegressionDecayFactor x *
        Real.cos (complexDecayRegressionPhase t x) := by
  rw [complexDecayRegressionTM_carrier]
  simp [Complex.mul_re]

private lemma complexDecayRegressionTM_carrier_im (t : Time) (x : Space) :
    (complexDecayRegressionTM.carrier t x).im =
      complexDecayRegressionDecayFactor x *
        Real.sin (complexDecayRegressionPhase t x) := by
  rw [complexDecayRegressionTM_carrier]
  simp [Complex.mul_im]

/-- The TM fixture realizes the ordinary real electric field `(4 A cos theta, 0, 5 A sin theta)`. -/
lemma complexDecayRegressionTM_electricField (t : Time) (x : Space) :
    complexDecayRegressionTM.electricField t x =
      WithLp.toLp 2 ![
        4 * complexDecayRegressionDecayFactor x *
          Real.cos (complexDecayRegressionPhase t x),
        (0 : ℝ),
        5 * complexDecayRegressionDecayFactor x *
          Real.sin (complexDecayRegressionPhase t x)] := by
  ext i
  rw [electricField_apply, complexDecayRegressionTM_electricAmplitude_eq]
  fin_cases i <;>
    simp [Complex.mul_re, complexDecayRegressionTM_carrier_re,
      complexDecayRegressionTM_carrier_im,
      Matrix.cons_val_two, Matrix.head_cons]
  all_goals ring

/-- The TM fixture realizes the ordinary real magnetic induction `(0, -9 A sin theta, 0)`. -/
lemma complexDecayRegressionTM_magneticInduction (t : Time) (x : Space) :
    complexDecayRegressionTM.magneticInduction t x =
      WithLp.toLp 2 ![
        (0 : ℝ),
        -9 * complexDecayRegressionDecayFactor x *
          Real.sin (complexDecayRegressionPhase t x),
        0] := by
  ext i
  rw [magneticInduction_apply, complexDecayRegressionTM_magneticAmplitude]
  fin_cases i <;>
    simp [Complex.mul_re, complexDecayRegressionTM_carrier_im,
      Matrix.cons_val_two, Matrix.head_cons]
  all_goals ring

/-- The imaginary third TM amplitude is `-5 I`, is hidden at phase zero, and is realized with
value `5` one quarter-period later at the spatial origin. -/
lemma complexDecayRegressionTM_thirdComponent_samples :
    complexDecayRegressionTM.electricAmplitude 2 = -5 * Complex.I ∧
      complexDecayRegressionTM.electricField 0 (0 : Space) 2 = 0 ∧
      complexDecayRegressionTM.electricField ((Real.pi / 2 : ℝ) : Time) (0 : Space) 2 = 5 := by
  constructor
  · rw [complexDecayRegressionTM_electricAmplitude_eq]
    norm_num [Matrix.cons_val_two, Matrix.head_cons]
  constructor <;>
    rw [complexDecayRegressionTM_electricField] <;>
    norm_num [complexDecayRegressionDecayFactor, complexDecayRegressionPhase,
      Matrix.cons_val_two, Matrix.head_cons]

/-- The TM fixture solves the source-free macroscopic Maxwell equations. -/
lemma complexDecayRegressionTM_isSourceFreeMacroscopicMaxwell :
    IsSourceFreeMacroscopicMaxwell complexDecayRegressionTM.electricField
      (complexDecayRegressionTM.electricDisplacement complexDecayRegressionMedium)
      complexDecayRegressionTM.magneticInduction
      (complexDecayRegressionTM.magneticFieldStrength complexDecayRegressionMedium) := by
  exact complexDecayRegressionTM.isSourceFreeMacroscopicMaxwell
    complexDecayRegressionMedium complexDecayRegressionTM_isTransverse
    complexDecayRegressionTM_isDispersionMatched

/-- The guarded source-free characterization specializes exactly to the TM fixture. -/
lemma complexDecayRegressionTM_isSourceFreeMacroscopicMaxwell_iff :
    IsSourceFreeMacroscopicMaxwell complexDecayRegressionTM.electricField
        (complexDecayRegressionTM.electricDisplacement complexDecayRegressionMedium)
        complexDecayRegressionTM.magneticInduction
        (complexDecayRegressionTM.magneticFieldStrength complexDecayRegressionMedium) ↔
      complexDecayRegressionTM.IsTransverse ∧
        complexDecayRegressionTM.IsDispersionMatched complexDecayRegressionMedium := by
  apply complexDecayRegressionTM.isSourceFreeMacroscopicMaxwell_iff
  intro h
  have hi := congrArg (fun v : EuclideanSpace ℂ (Fin 3) ↦ v 0) h
  norm_num [complexDecayRegressionTM] at hi

/-!

## D. Zero-amplitude off-shell degeneracy

-/

/-- The unit homogeneous medium used by the converse-boundary regressions. -/
def complexMaxwellRegressionMedium : HomogeneousIsotropicMedium where
  ε := 1
  μ := 1
  ε_pos := by norm_num
  μ_pos := by norm_num

/-- The zero-amplitude, zero-wave-vector candidate used to regress the dispersion guard. -/
def complexZeroAmplitudeRegression : ComplexMonochromaticPlaneWave where
  angularFrequency := 1
  angularFrequency_pos := by norm_num
  waveVector := 0
  electricAmplitude := 0

/-- The zero-amplitude off-shell fixture solves source-free Maxwell. -/
lemma complexZeroAmplitudeRegression_isSourceFreeMacroscopicMaxwell :
    IsSourceFreeMacroscopicMaxwell complexZeroAmplitudeRegression.electricField
      (complexZeroAmplitudeRegression.electricDisplacement complexMaxwellRegressionMedium)
      complexZeroAmplitudeRegression.magneticInduction
      (complexZeroAmplitudeRegression.magneticFieldStrength complexMaxwellRegressionMedium) := by
  exact complexZeroAmplitudeRegression.isSourceFreeMacroscopicMaxwell_of_electricAmplitude_eq_zero
    complexMaxwellRegressionMedium rfl

/-- The unguarded Maxwell converse recovers the zero-amplitude fixture's bilinear transversality,
which also holds algebraically because its electric amplitude vanishes. -/
lemma complexZeroAmplitudeRegression_isTransverse :
    complexZeroAmplitudeRegression.IsTransverse := by
  exact complexZeroAmplitudeRegression.isTransverse_of_isSourceFreeMacroscopicMaxwell
    complexMaxwellRegressionMedium
    complexZeroAmplitudeRegression_isSourceFreeMacroscopicMaxwell

/-- The zero-amplitude Maxwell fixture does not satisfy the unit-medium material shell. -/
lemma complexZeroAmplitudeRegression_not_isDispersionMatched :
    ¬ complexZeroAmplitudeRegression.IsDispersionMatched complexMaxwellRegressionMedium := by
  intro h
  have hre := congrArg Complex.re h
  norm_num [IsDispersionMatched, complexZeroAmplitudeRegression,
    complexMaxwellRegressionMedium, ComplexWaveVector.bilinearDot] at hre

/-!

## E. One-phase divergence counterexample

-/

/-- A nontransverse unit-frequency candidate whose electric Gauss expression vanishes at phase
zero only. -/
def complexOnePhaseRegression : ComplexMonochromaticPlaneWave where
  angularFrequency := 1
  angularFrequency_pos := by norm_num
  waveVector := WithLp.toLp 2 ![(1 : ℂ), 0, 0]
  electricAmplitude := WithLp.toLp 2 ![(1 : ℂ), 0, 0]

/-- The one-phase fixture has bilinear electric pairing one. -/
lemma complexOnePhaseRegression_bilinearDot :
    ComplexWaveVector.bilinearDot complexOnePhaseRegression.waveVector
      complexOnePhaseRegression.electricAmplitude = 1 := by
  norm_num [complexOnePhaseRegression, ComplexWaveVector.bilinearDot,
    Fin.sum_univ_three, Matrix.cons_val_two, Matrix.head_cons]

/-- The one-phase fixture is not bilinearly transverse. -/
lemma complexOnePhaseRegression_not_isTransverse :
    ¬ complexOnePhaseRegression.IsTransverse := by
  intro h
  rw [IsTransverse, complexOnePhaseRegression_bilinearDot] at h
  norm_num at h

/-- Electric-displacement divergence vanishes at phase zero for the nontransverse fixture but
equals one after a positive quarter-period. -/
lemma complexOnePhaseRegression_electricDisplacement_div_samples :
    (∇ ⬝ complexOnePhaseRegression.electricDisplacement
        complexMaxwellRegressionMedium 0) (0 : Space) = 0 ∧
      (∇ ⬝ complexOnePhaseRegression.electricDisplacement
        complexMaxwellRegressionMedium ((Real.pi / 2 : ℝ) : Time)) (0 : Space) = 1 := by
  constructor <;>
    rw [complexOnePhaseRegression.electricDisplacement_div] <;>
    norm_num [complexMaxwellRegressionMedium, complexOnePhaseRegression, carrier,
      ComplexWaveVector.spatialFactor, ComplexWaveVector.spatialPairing,
      ComplexWaveVector.bilinearDot, Fin.sum_univ_three,
      Matrix.cons_val_two, Matrix.head_cons]

/-!

## F. Complex-null-vector counterexample

-/

/-- The nonzero complex-null fixture with `K = E0 = (1, 0, -I)`. -/
def complexNullVectorRegression : ComplexMonochromaticPlaneWave where
  angularFrequency := 1
  angularFrequency_pos := by norm_num
  waveVector := WithLp.toLp 2 ![(1 : ℂ), 0, -Complex.I]
  electricAmplitude := WithLp.toLp 2 ![(1 : ℂ), 0, -Complex.I]

private lemma complexNullVectorRegression_electricAmplitude_eq_waveVector :
    complexNullVectorRegression.electricAmplitude = complexNullVectorRegression.waveVector := rfl

/-- The complex-null electric amplitude is nonzero. -/
lemma complexNullVectorRegression_electricAmplitude_ne_zero :
    complexNullVectorRegression.electricAmplitude ≠ 0 := by
  intro h
  have h0 := congrArg (fun v : EuclideanSpace ℂ (Fin 3) ↦ v 0) h
  norm_num [complexNullVectorRegression] at h0

/-- The complex-bilinear square of the null fixture is zero. -/
lemma complexNullVectorRegression_bilinearSquare :
    ComplexWaveVector.bilinearDot complexNullVectorRegression.waveVector
      complexNullVectorRegression.waveVector = 0 := by
  norm_num [complexNullVectorRegression, ComplexWaveVector.bilinearDot,
    Fin.sum_univ_three, Matrix.cons_val_two, Matrix.head_cons]

/-- The Hermitian pairing of the same vectors is two, not zero. -/
lemma complexNullVectorRegression_hermitianPairing :
    inner ℂ complexNullVectorRegression.waveVector
      complexNullVectorRegression.electricAmplitude = 2 := by
  change inner ℂ (WithLp.toLp 2 ![(1 : ℂ), 0, -Complex.I])
    (WithLp.toLp 2 ![(1 : ℂ), 0, -Complex.I]) = 2
  rw [PiLp.inner_apply]
  simp [Fin.sum_univ_three, Matrix.cons_val_two, Matrix.head_cons]
  norm_num [map_ofNat]

/-- Equality of `K` and `E0` is compatible with bilinear transversality for this complex-null
fixture. -/
lemma complexNullVectorRegression_isTransverse : complexNullVectorRegression.IsTransverse := by
  rw [IsTransverse, complexNullVectorRegression_electricAmplitude_eq_waveVector,
    complexNullVectorRegression_bilinearSquare]

/-- The complex-null fixture does not satisfy the unit-medium material shell. -/
lemma complexNullVectorRegression_not_isDispersionMatched :
    ¬ complexNullVectorRegression.IsDispersionMatched complexMaxwellRegressionMedium := by
  intro h
  rw [IsDispersionMatched, complexNullVectorRegression_bilinearSquare] at h
  norm_num [complexNullVectorRegression, complexMaxwellRegressionMedium] at h

/-- The complex-null fixture has zero compatible magnetic amplitude. -/
lemma complexNullVectorRegression_magneticAmplitude_eq_zero :
    complexNullVectorRegression.magneticAmplitude = 0 := by
  rw [magneticAmplitude, complexNullVectorRegression_electricAmplitude_eq_waveVector]
  simp [complexCross, cross_self]

/-- Magnetic Gauss holds for the complex-null fixture. -/
lemma complexNullVectorRegression_gaussLawMagnetic (t : Time) (x : Space) :
    (∇ ⬝ complexNullVectorRegression.magneticInduction t) x = 0 := by
  exact complexNullVectorRegression.gaussLawMagnetic t x

/-- Faraday's law holds for the complex-null fixture. -/
lemma complexNullVectorRegression_faradayLaw (t : Time) (x : Space) :
    (∇ ⨯ complexNullVectorRegression.electricField t) x =
      -∂ₜ (fun s ↦ complexNullVectorRegression.magneticInduction s x) t := by
  exact complexNullVectorRegression.faradayLaw t x

/-- Electric Gauss holds for the bilinearly transverse complex-null fixture. -/
lemma complexNullVectorRegression_gaussLawElectric (t : Time) (x : Space) :
    (∇ ⬝ complexNullVectorRegression.electricDisplacement
      complexMaxwellRegressionMedium t) x = 0 := by
  exact complexNullVectorRegression.gaussLawElectric complexMaxwellRegressionMedium
    complexNullVectorRegression_isTransverse t x

private lemma complexNullVectorRegression_magneticFieldStrength_curl_at_origin :
    (∇ ⨯ complexNullVectorRegression.magneticFieldStrength
      complexMaxwellRegressionMedium 0) (0 : Space) = 0 := by
  rw [complexNullVectorRegression.magneticFieldStrength_curl,
    complexNullVectorRegression_magneticAmplitude_eq_zero]
  ext i
  simp [realFieldOfAmplitude_apply, complexCross]

private lemma complexNullVectorRegression_electricDisplacement_timeDeriv_at_origin :
    ∂ₜ (fun s ↦ complexNullVectorRegression.electricDisplacement
        complexMaxwellRegressionMedium s (0 : Space)) 0 =
      WithLp.toLp 2 ![0, 0, 1] := by
  rw [complexNullVectorRegression.electricDisplacement_timeDeriv]
  ext i
  fin_cases i <;>
    norm_num [complexMaxwellRegressionMedium, realFieldOfAmplitude_apply,
      complexNullVectorRegression, carrier, ComplexWaveVector.spatialFactor,
      ComplexWaveVector.spatialPairing, ComplexWaveVector.bilinearDot,
      Fin.sum_univ_three, Matrix.cons_val_two, Matrix.head_cons]

/-- Ampere--Maxwell fails for the complex-null fixture at the spacetime origin: the
magnetic-field-strength curl is zero while the electric-displacement time derivative is
`(0, 0, 1)`. -/
lemma complexNullVectorRegression_ampereMaxwellLaw_fails_at_origin :
    (∇ ⨯ complexNullVectorRegression.magneticFieldStrength
        complexMaxwellRegressionMedium 0) (0 : Space) ≠
      ∂ₜ (fun s ↦ complexNullVectorRegression.electricDisplacement
        complexMaxwellRegressionMedium s (0 : Space)) 0 := by
  rw [complexNullVectorRegression_magneticFieldStrength_curl_at_origin,
    complexNullVectorRegression_electricDisplacement_timeDeriv_at_origin]
  intro h
  have h2 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) ↦ v 2) h
  norm_num [Matrix.cons_val_two, Matrix.head_cons] at h2

/-!

## G. Embedded real-wave coherence

-/

/-- A nonzero transverse real-quadrature candidate in the exact regression medium. -/
def realEmbeddingRegressionWave : MonochromaticPlaneWave :=
  MonochromaticPlaneWave.inMedium complexDecayRegressionMedium
    ⟨Space.basis 0, by simp⟩ 1 (by norm_num)
    (WithLp.toLp 2 ![(0 : ℝ), 1, 0])
    (WithLp.toLp 2 ![(0 : ℝ), 0, 1])

/-- At least one quadrature of the real-embedding regression is nonzero. -/
lemma realEmbeddingRegression_electricQuadratures_ne_zero :
    realEmbeddingRegressionWave.electricReal ≠ 0 ∨
      realEmbeddingRegressionWave.electricImag ≠ 0 := by
  left
  simp [realEmbeddingRegressionWave, MonochromaticPlaneWave.inMedium]

/-- The embedded complex electric amplitude is nonzero by the exact guard bridge. -/
lemma realEmbeddingRegression_ofReal_electricAmplitude_ne_zero :
    (ofReal realEmbeddingRegressionWave).electricAmplitude ≠ 0 :=
  (ofReal_electricAmplitude_ne_zero_iff realEmbeddingRegressionWave).mpr
    realEmbeddingRegression_electricQuadratures_ne_zero

/-- The existing real guarded converse specializes to the real-embedding regression. -/
lemma realEmbeddingRegression_isSourceFreeMacroscopicMaxwell_iff :
    IsSourceFreeMacroscopicMaxwell realEmbeddingRegressionWave.electricField
        (realEmbeddingRegressionWave.electricDisplacement complexDecayRegressionMedium)
        realEmbeddingRegressionWave.magneticInduction
        (realEmbeddingRegressionWave.magneticFieldStrength complexDecayRegressionMedium) ↔
      realEmbeddingRegressionWave.IsTransverse ∧
        realEmbeddingRegressionWave.IsDispersionMatched complexDecayRegressionMedium :=
  realEmbeddingRegressionWave.isSourceFreeMacroscopicMaxwell_iff
    complexDecayRegressionMedium realEmbeddingRegression_electricQuadratures_ne_zero

/-- The complex guarded converse on the embedded wave has exactly the same real predicates. -/
lemma realEmbeddingRegression_ofReal_isSourceFreeMacroscopicMaxwell_iff :
    IsSourceFreeMacroscopicMaxwell (ofReal realEmbeddingRegressionWave).electricField
        ((ofReal realEmbeddingRegressionWave).electricDisplacement
          complexDecayRegressionMedium)
        (ofReal realEmbeddingRegressionWave).magneticInduction
        ((ofReal realEmbeddingRegressionWave).magneticFieldStrength
          complexDecayRegressionMedium) ↔
      realEmbeddingRegressionWave.IsTransverse ∧
        realEmbeddingRegressionWave.IsDispersionMatched complexDecayRegressionMedium := by
  rw [(ofReal realEmbeddingRegressionWave).isSourceFreeMacroscopicMaxwell_iff
      complexDecayRegressionMedium
      realEmbeddingRegression_ofReal_electricAmplitude_ne_zero,
    isTransverse_ofReal_iff, isDispersionMatched_ofReal_iff]

end ComplexMonochromaticPlaneWave
end
end ThreeDimension
end Electromagnetism
