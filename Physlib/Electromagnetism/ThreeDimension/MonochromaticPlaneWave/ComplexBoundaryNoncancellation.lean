/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public
import Physlib.Electromagnetism.ThreeDimension.MonochromaticPlaneWave.ComplexBoundaryAmplitude
public import Physlib.Mathematics.ComplexExponentialCharacter

/-!
# Positive-rate uniqueness for joint electric boundary amplitudes

## i. Overview

This file lifts finite positive-rate uniqueness for ordinary real parts of scalar complex
exponential characters to the joint tangential-electric and normal-electric-displacement
calculation amplitudes used by the complex plane-wave boundary API. A finitely supported family is
keyed by its exact complex-valued real-linear exponent functional, so repeated exponents have
already been aggregated before the theorem is applied.

The proof projects the three coordinates of the ambient complex vector slot used to store
tangential electric amplitudes and the scalar complex normal-displacement coordinate separately,
applies scalar harmonic uniqueness to each projection, and reconstructs the joint coefficient.
Consequently, vanishing of the ordinary-real joint sum at every parameter is equivalent to the
entire aggregated complex coefficient map being zero when every supported exponent has strictly
positive imaginary rate on one common probe.

This is finite character uniqueness, not a Fourier transform or convergence theorem. It assumes no
wave, medium, affine plane, interface, boundary law, or nonzero labeled contribution. It gives no
labelwise matching, frequency or wave-vector conservation, propagation branch, Fresnel coefficient,
observable, or power result. In particular, a nonzero complex coefficient need not have nonzero
ordinary-real realization at any selected single parameter.

## ii. Key results

- `ComplexMonochromaticPlaneWave.jointElectricHarmonicSum`: ordinary-real joint data formed from
  an exponent-keyed finite complex coefficient map.
- `ComplexMonochromaticPlaneWave.jointElectricHarmonicSum_eq_zero_iff_of_im_pos`: all-parameter
  vanishing is equivalent to zero of the aggregated coefficient map under a common positive-rate
  hypothesis.

## iii. Table of contents

- A. Joint harmonic sums
- B. Coordinate scalarization
- C. Positive-rate uniqueness

## iv. References

The proof applies Physlib's finite positive-rate real exponential-character uniqueness theorem
coordinatewise. No external formal-development source is copied or translated here.
-/

@[expose] public section

namespace Electromagnetism
namespace ThreeDimension

noncomputable section

namespace ComplexMonochromaticPlaneWave

variable {V : Type*} [AddCommMonoid V] [Module ℝ V]

/-!

## A. Joint harmonic sums

-/

/-- The ordinary-real joint harmonic data of a finite complex coefficient map keyed by exact
complex-valued real-linear exponent functionals.

Coincident exponent keys are already aggregated by the `Finsupp`; this definition does not retain
the labels from which its coefficients may have been assembled. -/
def jointElectricHarmonicSum
    (a : (V →ₗ[ℝ] ℂ) →₀ JointElectricTraceAmplitude) (v : V) :
    EuclideanSpace ℝ (Fin 3) × ℝ :=
  a.sum fun L A =>
    realPartJointElectricTraceAmplitude (Complex.exp (L v) • A)

/-!

## B. Coordinate scalarization

-/

/-- Extract one complex coordinate of the ambient vector slot used to store a tangential electric
amplitude. -/
private def jointTangentialCoordinate (j : Fin 3) : JointElectricTraceAmplitude →+ ℂ where
  toFun z := z.1 j
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Extract the complex scalar normal-displacement amplitude. -/
private def jointNormalCoordinate : JointElectricTraceAmplitude →+ ℂ where
  toFun z := z.2
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Extract one real coordinate of realized tangential-vector data. -/
private def jointRealTangentialCoordinate (j : Fin 3) :
    (EuclideanSpace ℝ (Fin 3) × ℝ) →+ ℝ where
  toFun z := z.1 j
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Extract the realized scalar normal-displacement data. -/
private def jointRealNormalCoordinate : (EuclideanSpace ℝ (Fin 3) × ℝ) →+ ℝ where
  toFun z := z.2
  map_zero' := rfl
  map_add' _ _ := rfl

private lemma tangential_scalarization_sum
    (a : (V →ₗ[ℝ] ℂ) →₀ JointElectricTraceAmplitude) (j : Fin 3) (v : V) :
    ((Finsupp.mapRange.addMonoidHom (jointTangentialCoordinate j)) a).sum
        (fun L c => (c * Complex.exp (L v)).re) =
      (jointElectricHarmonicSum a v).1 j := by
  rw [Finsupp.mapRange.addMonoidHom_apply,
    Finsupp.sum_mapRange_index (by simp)]
  change _ = jointRealTangentialCoordinate j
    (a.sum fun L z => realPartJointElectricTraceAmplitude (Complex.exp (L v) • z))
  rw [map_finsuppSum]
  apply Finsupp.sum_congr
  intro L _
  change ((a L).1 j * Complex.exp (L v)).re =
    (Complex.exp (L v) * (a L).1 j).re
  rw [mul_comm]

private lemma normal_scalarization_sum
    (a : (V →ₗ[ℝ] ℂ) →₀ JointElectricTraceAmplitude) (v : V) :
    ((Finsupp.mapRange.addMonoidHom jointNormalCoordinate) a).sum
        (fun L c => (c * Complex.exp (L v)).re) =
      (jointElectricHarmonicSum a v).2 := by
  rw [Finsupp.mapRange.addMonoidHom_apply,
    Finsupp.sum_mapRange_index (by simp)]
  change _ = jointRealNormalCoordinate
    (a.sum fun L z => realPartJointElectricTraceAmplitude (Complex.exp (L v) • z))
  rw [map_finsuppSum]
  apply Finsupp.sum_congr
  intro L _
  change ((a L).2 * Complex.exp (L v)).re =
    (Complex.exp (L v) * (a L).2).re
  rw [mul_comm]

/-!

## C. Positive-rate uniqueness

-/

/-- A finite positive-rate joint electric harmonic sum vanishes at every parameter exactly when
its exponent-aggregated complex coefficient map is zero. -/
lemma jointElectricHarmonicSum_eq_zero_iff_of_im_pos
    (a : (V →ₗ[ℝ] ℂ) →₀ JointElectricTraceAmplitude) (probe : V)
    (hPositive : ∀ L ∈ a.support, 0 < (L probe).im) :
    (∀ v : V, jointElectricHarmonicSum a v = 0) ↔ a = 0 := by
  constructor
  · intro h
    apply Finsupp.ext
    intro L
    apply Prod.ext
    · ext j
      let b := (Finsupp.mapRange.addMonoidHom (jointTangentialCoordinate j)) a
      have hbPositive : ∀ M ∈ b.support, 0 < (M probe).im := by
        intro M hM
        apply hPositive M
        apply Finsupp.support_mapRange (hf := (jointTangentialCoordinate j).map_zero)
        simpa [b] using hM
      have hbSum : ∀ v : V, b.sum (fun M c => (c * Complex.exp (M v)).re) = 0 := by
        intro v
        rw [tangential_scalarization_sum]
        simpa using congrArg (fun z => z.1 j) (h v)
      have hb : b = 0 :=
        (Complex.finsupp_sum_re_mul_exp_eq_zero_iff_of_im_pos b probe hbPositive).mp hbSum
      have hbL := congrArg (fun c => c L) hb
      change (jointTangentialCoordinate j) (a L) = 0 at hbL
      exact hbL
    · let b := (Finsupp.mapRange.addMonoidHom jointNormalCoordinate) a
      have hbPositive : ∀ M ∈ b.support, 0 < (M probe).im := by
        intro M hM
        apply hPositive M
        apply Finsupp.support_mapRange (hf := jointNormalCoordinate.map_zero)
        simpa [b] using hM
      have hbSum : ∀ v : V, b.sum (fun M c => (c * Complex.exp (M v)).re) = 0 := by
        intro v
        rw [normal_scalarization_sum]
        simpa using congrArg Prod.snd (h v)
      have hb : b = 0 :=
        (Complex.finsupp_sum_re_mul_exp_eq_zero_iff_of_im_pos b probe hbPositive).mp hbSum
      have hbL := congrArg (fun c => c L) hb
      change jointNormalCoordinate (a L) = 0 at hbL
      exact hbL
  · rintro rfl
    simp [jointElectricHarmonicSum]

end ComplexMonochromaticPlaneWave

end
end ThreeDimension
end Electromagnetism
