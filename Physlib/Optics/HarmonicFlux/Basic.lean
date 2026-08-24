/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalAverage
public import Physlib.Electromagnetism.ThreeDimension.Energy
public import Physlib.Electromagnetism.ThreeDimension.MonochromaticPlaneWave.ComplexBasic
public import Physlib.Optics.Polarization.Basic

/-!
# Harmonic Poynting-flux averaging

## i. Overview

This file derives the time-averaged Poynting vector for the peak-phasor convention fixed by
`Phasor.realize`. For local electric and magnetic-field-strength phasors `E₀` and `H₀`, the
result is

`(1 / 2) Re (E₀ × conj H₀)`.

The factor one half, cross-product order, and conjugation of the second phasor are proved from the
ordinary real fields. The final bridge averages the actual instantaneous electromagnetic
definition `poyntingVector E H` over one positive-frequency period, starting at an arbitrary
time.

The phasors in the local bridge are amplitudes at the selected spatial point. For an attenuating
complex plane wave, they therefore include its spatial factor at that point; replacing them by
stored reference amplitudes would not preserve spatial decay.

## ii. Key results

- `intervalAverage_comp_carrierPhase`: change from one time period to one carrier-phase cycle.
- `Phasor.intervalAverage_realize_mul_realize`: the scalar coherent-product average.
- `timeAveragedPoyntingVector`: the closed complex-phasor expression.
- `intervalAverage_cross_realizeEuclidean`: derivation of the vector expression.
- `intervalAverage_poyntingVector_eq_timeAveragedPoyntingVector`: connection to the
  instantaneous electromagnetic Poynting vector.

## iii. Table of contents

- A. Time and carrier-phase averages
- B. Scalar phasor-product average
- C. Vector phasor average
- D. Electromagnetic Poynting-vector bridge

## iv. Scope

These are local kinematic averaging identities. They require no Maxwell, transversality,
dispersion, nonzero-amplitude, propagation-direction, or outgoing-wave hypothesis. This file does
not define irradiance, interface-normal flux, aperture-integrated power, modal normalization,
passivity, or evanescence.
-/

@[expose] public section

namespace Optics

open ClassicalMechanics Electromagnetism Electromagnetism.ThreeDimension Matrix MeasureTheory
  Space Time
open scoped ComplexConjugate Interval Real

noncomputable section

/-!

## A. Time and carrier-phase averages

-/

/-- An interval average over one positive-frequency time period equals the corresponding
carrier-phase average for a full-cycle-periodic signal. -/
lemma intervalAverage_comp_carrierPhase {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (angularFrequency phaseOffset : ℝ)
    (hfrequency : 0 < angularFrequency) (startTime : Time) (signal : ℝ → V)
    (hsignal_periodic : Function.Periodic signal (2 * Real.pi)) :
    (⨍ time in startTime.val..startTime.val + 2 * Real.pi / angularFrequency,
      signal (angularFrequency * time + phaseOffset)) =
      ⨍ phase in 0..2 * Real.pi, signal phase := by
  have hfrequency_ne : angularFrequency ≠ 0 := ne_of_gt hfrequency
  have hsubstitution :
      angularFrequency •
          ∫ time in startTime.val..startTime.val + 2 * Real.pi / angularFrequency,
            signal (angularFrequency * time + phaseOffset) =
        ∫ phase in angularFrequency * startTime.val + phaseOffset..
            angularFrequency * (startTime.val + 2 * Real.pi / angularFrequency) + phaseOffset,
          signal phase := by
    exact intervalIntegral.smul_integral_comp_mul_add signal angularFrequency phaseOffset
  have hphase_end :
      angularFrequency * (startTime.val + 2 * Real.pi / angularFrequency) + phaseOffset =
        angularFrequency * startTime.val + phaseOffset + 2 * Real.pi := by
    field_simp
    ring
  rw [hphase_end,
    hsignal_periodic.intervalIntegral_add_eq
      (angularFrequency * startTime.val + phaseOffset) 0] at hsubstitution
  rw [interval_average_eq, interval_average_eq]
  simp only [add_sub_cancel_left, sub_zero]
  change (2 * Real.pi / angularFrequency)⁻¹ •
      (∫ time in startTime.val..startTime.val + 2 * Real.pi / angularFrequency,
        signal (angularFrequency * time + phaseOffset)) = _
  calc
    (2 * Real.pi / angularFrequency)⁻¹ •
        (∫ time in startTime.val..startTime.val + 2 * Real.pi / angularFrequency,
          signal (angularFrequency * time + phaseOffset)) =
      (2 * Real.pi)⁻¹ •
        (angularFrequency •
          ∫ time in startTime.val..startTime.val + 2 * Real.pi / angularFrequency,
            signal (angularFrequency * time + phaseOffset)) := by
        rw [smul_smul]
        congr 1
        field_simp
    _ = (2 * Real.pi)⁻¹ • ∫ phase in 0..2 * Real.pi, signal phase := by
      rw [hsubstitution]
      simp

/-!

## B. Scalar phasor-product average

-/

/-- The elementary antiderivative used to average the product of two realized phasors. -/
private def phasorProductPrimitive (z w : Phasor) (phase : ℝ) : ℝ :=
  (z.re * w.re + z.im * w.im) / 2 * phase +
    (z.re * w.re - z.im * w.im) / 4 * Real.sin (2 * phase) +
    (z.re * w.im + z.im * w.re) / 4 * Real.cos (2 * phase)

private lemma phasorProductPrimitive_hasDerivAt (z w : Phasor) (phase : ℝ) :
    HasDerivAt (phasorProductPrimitive z w)
      (z.realize phase * w.realize phase) phase := by
  let A : ℝ := (z.re * w.re + z.im * w.im) / 2
  let B : ℝ := (z.re * w.re - z.im * w.im) / 4
  let C : ℝ := (z.re * w.im + z.im * w.re) / 4
  have hlinear : HasDerivAt (fun x : ℝ ↦ 2 * x) 2 phase := by
    simpa using (hasDerivAt_id phase).const_mul 2
  have hsin : HasDerivAt (fun x : ℝ ↦ Real.sin (2 * x))
      (Real.cos (2 * phase) * 2) phase := by
    simpa only [Function.comp_def] using
      (Real.hasDerivAt_sin (2 * phase)).comp phase hlinear
  have hcos : HasDerivAt (fun x : ℝ ↦ Real.cos (2 * x))
      (-Real.sin (2 * phase) * 2) phase := by
    simpa only [Function.comp_def] using
      (Real.hasDerivAt_cos (2 * phase)).comp phase hlinear
  have hraw := (((hasDerivAt_id phase).const_mul A).add (hsin.const_mul B)).add
    (hcos.const_mul C)
  change HasDerivAt (phasorProductPrimitive z w) _ phase at hraw
  convert hraw using 1
  rw [Phasor.realize_eq_re_cos_sub_im_sin,
    Phasor.realize_eq_re_cos_sub_im_sin, Real.sin_two_mul, Real.cos_two_mul]
  dsimp [A, B, C]
  linear_combination (z.im * w.im) * (Real.sin_sq_add_cos_sq phase)

private lemma intervalIntegral_phasor_product_zero (z w : Phasor) :
    (∫ phase in (0 : ℝ)..2 * Real.pi, z.realize phase * w.realize phase) =
      Real.pi * (z * star w).re := by
  have hcontinuous : Continuous fun phase ↦ z.realize phase * w.realize phase := by
    simp only [Phasor.realize_eq_re_cos_sub_im_sin]
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun phase _ ↦ phasorProductPrimitive_hasDerivAt z w phase)
    (hcontinuous.intervalIntegrable 0 (2 * Real.pi))]
  simp only [phasorProductPrimitive]
  have hsin_four : Real.sin (2 * (2 * Real.pi)) = 0 := by
    rw [show 2 * (2 * Real.pi) = 2 * Real.pi + 2 * Real.pi by ring,
      Real.sin_add_two_pi, Real.sin_two_pi]
  have hcos_four : Real.cos (2 * (2 * Real.pi)) = 1 := by
    rw [show 2 * (2 * Real.pi) = 2 * Real.pi + 2 * Real.pi by ring,
      Real.cos_add_two_pi, Real.cos_two_pi]
  rw [hsin_four, hcos_four]
  simp [Complex.mul_re]
  ring

/-- The interval average of two coherently realized peak phasors is one half the real part of the
first phasor times the conjugate of the second. -/
lemma Phasor.intervalAverage_realize_mul_realize (z w : Phasor) (phaseOffset : ℝ) :
    (⨍ phase : ℝ in phaseOffset..phaseOffset + 2 * Real.pi,
      z.realize phase * w.realize phase) =
      (1 / 2 : ℝ) * (z * star w).re := by
  have hperiodic : Function.Periodic
      (fun phase : ℝ ↦ z.realize phase * w.realize phase) (2 * Real.pi) := by
    intro phase
    simp only [Phasor.realize_eq_re_cos_sub_im_sin]
    rw [Real.cos_add_two_pi, Real.sin_add_two_pi]
  rw [interval_average_eq]
  rw [hperiodic.intervalIntegral_add_eq phaseOffset 0]
  simp only [add_sub_cancel_left, zero_add, smul_eq_mul]
  rw [intervalIntegral_phasor_product_zero]
  have hpi_ne : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp

/-!

## C. Vector phasor average

-/

private lemma continuous_cross_realizeEuclidean
    (electricPhasor magneticFieldStrengthPhasor : EuclideanSpace ℂ (Fin 3)) :
    Continuous (fun phase : ℝ ↦
      Phasor.realizeEuclidean electricPhasor phase ⨯ₑ₃
        Phasor.realizeEuclidean magneticFieldStrengthPhasor phase) := by
  change Continuous (fun phase : ℝ ↦ WithLp.toLp 2
    (crossProduct (Phasor.realizeEuclidean electricPhasor phase)
      (Phasor.realizeEuclidean magneticFieldStrengthPhasor phase)))
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  have hE (j : Fin 3) : Continuous (fun phase ↦
      Phasor.realizeEuclidean electricPhasor phase j) :=
    (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 3 ↦ ℝ) j).comp
      (Phasor.continuous_realizeEuclidean electricPhasor)
  have hH (j : Fin 3) : Continuous (fun phase ↦
      Phasor.realizeEuclidean magneticFieldStrengthPhasor phase j) :=
    (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 3 ↦ ℝ) j).comp
      (Phasor.continuous_realizeEuclidean magneticFieldStrengthPhasor)
  fin_cases i
  · exact (hE 1).mul (hH 2) |>.sub ((hE 2).mul (hH 1))
  · exact (hE 2).mul (hH 0) |>.sub ((hE 0).mul (hH 2))
  · exact (hE 0).mul (hH 1) |>.sub ((hE 1).mul (hH 0))

private lemma intervalAverage_euclidean_apply {d : ℕ}
    (signal : ℝ → EuclideanSpace ℝ (Fin d)) (hsignal : Continuous signal)
    (a b : ℝ) (i : Fin d) :
    (⨍ phase in a..b, signal phase) i = ⨍ phase in a..b, signal phase i := by
  rw [interval_average_eq, interval_average_eq]
  simp only [PiLp.smul_apply, smul_eq_mul]
  have hcommute := ContinuousLinearMap.intervalIntegral_comp_comm (μ := volume)
    (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin d ↦ ℝ) i)
    (hsignal.intervalIntegrable a b)
  exact congrArg (fun x : ℝ ↦ (b - a)⁻¹ * x) hcommute.symm

private lemma intervalAverage_sub (f g : ℝ → ℝ) (hf : Continuous f)
    (hg : Continuous g) (a b : ℝ) :
    (⨍ phase in a..b, f phase - g phase) =
      (⨍ phase in a..b, f phase) - ⨍ phase in a..b, g phase := by
  rw [interval_average_eq, interval_average_eq, interval_average_eq,
    intervalIntegral.integral_sub (hf.intervalIntegrable a b) (hg.intervalIntegrable a b),
    smul_sub]

/-- The time-averaged Poynting vector computed from local peak phasors.

The magnetic phasor is magnetic field strength `H`, not magnetic induction `B`. -/
def timeAveragedPoyntingVector
    (electricPhasor magneticFieldStrengthPhasor : EuclideanSpace ℂ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) :=
  (1 / 2 : ℝ) • ComplexWaveVector.realPart
    (ComplexMonochromaticPlaneWave.complexCross electricPhasor
      (Phasor.conjugateEuclidean magneticFieldStrengthPhasor))

/-- Averaging the cross product of two coherently realized harmonic vector phasors over one
carrier cycle gives one half the real part of the first phasor crossed with the conjugate of the
second. -/
lemma intervalAverage_cross_realizeEuclidean
    (electricPhasor magneticFieldStrengthPhasor : EuclideanSpace ℂ (Fin 3))
    (phaseOffset : ℝ) :
    (⨍ phase in phaseOffset..phaseOffset + 2 * Real.pi,
      Phasor.realizeEuclidean electricPhasor phase ⨯ₑ₃
        Phasor.realizeEuclidean magneticFieldStrengthPhasor phase) =
      timeAveragedPoyntingVector electricPhasor magneticFieldStrengthPhasor := by
  ext i
  rw [intervalAverage_euclidean_apply _
    (continuous_cross_realizeEuclidean electricPhasor magneticFieldStrengthPhasor)]
  fin_cases i
  all_goals
    simp [crossProduct]
    rw [intervalAverage_sub]
    · rw [Phasor.intervalAverage_realize_mul_realize,
        Phasor.intervalAverage_realize_mul_realize]
      simp [timeAveragedPoyntingVector,
        ComplexMonochromaticPlaneWave.complexCross, ComplexWaveVector.realPart,
        Phasor.conjugateEuclidean, crossProduct, Complex.mul_re]
      ring
    · simp only [Phasor.realize_eq_re_cos_sub_im_sin]
      fun_prop
    · simp only [Phasor.realize_eq_re_cos_sub_im_sin]
      fun_prop

/-!

## D. Electromagnetic Poynting-vector bridge

-/

/-- The one-period average of the actual instantaneous Poynting vector for locally realized
common-frequency phasors is the closed complex-phasor Poynting vector.

The supplied phasors are local at `x`; the hypotheses state exact ordinary-real field
realizations there. -/
lemma intervalAverage_poyntingVector_eq_timeAveragedPoyntingVector
    {E : ElectricField} {H : MagneticFieldStrength}
    (electricPhasor magneticFieldStrengthPhasor : EuclideanSpace ℂ (Fin 3))
    (angularFrequency : ℝ) (hfrequency : 0 < angularFrequency)
    (startTime : Time) (x : Space)
    (hE : ∀ time : ℝ, E (time : Time) x =
      Phasor.realizeEuclidean electricPhasor (angularFrequency * time))
    (hH : ∀ time : ℝ, H (time : Time) x =
      Phasor.realizeEuclidean magneticFieldStrengthPhasor (angularFrequency * time)) :
    (⨍ time in startTime.val..startTime.val + 2 * Real.pi / angularFrequency,
      ThreeDimension.poyntingVector E H (time : Time) x) =
      timeAveragedPoyntingVector electricPhasor magneticFieldStrengthPhasor := by
  let signal : ℝ → EuclideanSpace ℝ (Fin 3) := fun phase ↦
    Phasor.realizeEuclidean electricPhasor phase ⨯ₑ₃
      Phasor.realizeEuclidean magneticFieldStrengthPhasor phase
  have hsignal_periodic : Function.Periodic signal (2 * Real.pi) := by
    intro phase
    simp only [signal, Phasor.realizeEuclidean_add_two_pi]
  calc
    (⨍ time in startTime.val..startTime.val + 2 * Real.pi / angularFrequency,
        ThreeDimension.poyntingVector E H (time : Time) x) =
      ⨍ time in startTime.val..startTime.val + 2 * Real.pi / angularFrequency,
        signal (angularFrequency * time + 0) := by
          congr 1
          funext time
          rw [ThreeDimension.poyntingVector, hE, hH]
          simp [signal]
    _ = ⨍ phase in 0..2 * Real.pi, signal phase :=
      intervalAverage_comp_carrierPhase angularFrequency 0 hfrequency startTime signal
        hsignal_periodic
    _ = timeAveragedPoyntingVector electricPhasor magneticFieldStrengthPhasor := by
      simpa [signal] using intervalAverage_cross_realizeEuclidean electricPhasor
        magneticFieldStrengthPhasor 0

end

end Optics
