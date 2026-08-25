/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Rays.Gaussian

/-!
# Regression tests for Gaussian beams and the complex ABCD law

## i. Overview

This file carries regression `R-03` of `goal.md` §I.3, whose stated target is beam algebra that
is not connected to anything: a set of mutually consistent formulas that no wave equation and no
optical system backs up. Both halves are checked here, on the same beam.

Two sentinels are about hypotheses rather than values, and they are the ones worth reading.

The determinant hypothesis of the domain theorem is *necessary*, not decorative: a
phase-conjugating mirror has determinant `-1` and carries the regression beam parameter out of the
physical domain entirely, so the ABCD law is not a map of Gaussian beams for it. That is the same
component that is the exception to the index-ratio determinant law in
`Physlib.Optics.Rays.Transfer`, and the two exceptions are the same fact seen twice.

The singular-matrix sentinel closes a gap in the source. There the free-form interface constructor
is unconditionally valid, so it admits a singular matrix; with a total division the ABCD law then
asserts that the outgoing beam parameter is zero. Here validity rejects it, and both halves are
exhibited: the matrix fails `IsValid`, and applying the formula to it anyway would indeed produce
the junk value.

## ii. Key results

- `Optics.gaussianRegression_beamRadius_at_rayleighRange`: the beam radius grows to `√2` times the
  waist radius one Rayleigh range from the waist.
- `Optics.gaussianRegression_thinLens_beamRadius`: a thin lens does not change the beam radius.
- `Optics.gaussianRegression_phaseConjugate_leaves_domain`: the positive-determinant hypothesis is
  necessary.
- `Optics.gaussianRegression_singular_not_isValid` and
  `Optics.gaussianRegression_singular_would_be_junk`: the singular matrix is rejected by validity,
  and what would go wrong without that.
- `Optics.gaussianRegression_helmholtz`: the regression beam solves the paraxial Helmholtz
  equation.

## iii. Table of contents

- A. The regression beam
- B. Free propagation and the thin lens
- C. The denominator and the domain
- D. The paraxial Helmholtz solution

## iv. References

The fixtures use only the public declarations of `Physlib.Optics.Rays.Gaussian`.

-/

@[expose] public section

namespace Optics

noncomputable section

open Real

/-!

## A. The regression beam

-/

/-- The regression beam: unit wavelength, beam parameter `i`, so it sits at its waist with unit
Rayleigh range. -/
def gaussianRegressionBeam : GaussianBeam where
  wavelength := 1
  q := Complex.I
  wavelength_pos := one_pos
  q_im_pos := by simp

/-- The regression beam is at its waist. -/
lemma gaussianRegressionBeam_isAtWaist : gaussianRegressionBeam.IsAtWaist := by
  rw [GaussianBeam.IsAtWaist]
  simp [gaussianRegressionBeam]

/-- The regression beam has unit Rayleigh range. -/
@[simp]
lemma gaussianRegressionBeam_rayleighRange : gaussianRegressionBeam.rayleighRange = 1 := by
  rw [GaussianBeam.rayleighRange]
  simp [gaussianRegressionBeam]

/-- At the waist the beam radius is the waist radius. -/
lemma gaussianRegression_beamRadius_at_waist :
    gaussianRegressionBeam.beamRadius = gaussianRegressionBeam.waistRadius :=
  gaussianRegressionBeam.beamRadius_of_isAtWaist gaussianRegressionBeam_isAtWaist

/-- At the waist the wavefront is plane. -/
lemma gaussianRegression_wavefrontCurvature_at_waist :
    gaussianRegressionBeam.wavefrontCurvature = 0 :=
  gaussianRegressionBeam.wavefrontCurvature_of_isAtWaist gaussianRegressionBeam_isAtWaist

/-!

## B. Free propagation and the thin lens

-/

/-- **One Rayleigh range from the waist the beam radius is `√2` times the waist radius.**

This is the physical content of the Rayleigh range, and it comes out of the ABCD law rather than
out of a definition.
-/
lemma gaussianRegression_beamRadius_at_rayleighRange :
    (gaussianRegressionBeam.transform (translationMatrix 1)
        (det_translationMatrix_pos 1)).beamRadius =
      gaussianRegressionBeam.waistRadius * √2 := by
  rw [GaussianBeam.beamRadius_translation_of_isAtWaist gaussianRegressionBeam
    gaussianRegressionBeam_isAtWaist 1, gaussianRegressionBeam_rayleighRange]
  norm_num

/-- Free propagation moves the beam off its waist. -/
lemma gaussianRegression_not_isAtWaist_after_propagation :
    ¬ (gaussianRegressionBeam.transform (translationMatrix 1)
      (det_translationMatrix_pos 1)).IsAtWaist := by
  rw [GaussianBeam.IsAtWaist, GaussianBeam.transform_translationMatrix_q]
  simp [gaussianRegressionBeam]

/-- **A thin lens does not change the beam radius**, whatever its focal length: it reshapes the
wavefront, not the spot. -/
lemma gaussianRegression_thinLens_beamRadius (f : ℝ) :
    (gaussianRegressionBeam.transform (thinLensMatrix f)
        (by rw [det_thinLensMatrix]; norm_num)).beamRadius =
      gaussianRegressionBeam.beamRadius :=
  GaussianBeam.beamRadius_transform_of_entries gaussianRegressionBeam (thinLensMatrix f)
    (by rw [det_thinLensMatrix]; norm_num) rfl rfl

/-!

## C. The denominator and the domain

-/

/-- The ABCD denominator of a thin lens acting on the regression beam is nonzero, discharged by
the general theorem rather than assumed. -/
lemma gaussianRegression_denominator_ne_zero (f : ℝ) :
    abcdDenominator (thinLensMatrix f) gaussianRegressionBeam.q ≠ 0 :=
  abcdDenominator_ne_zero (thinLensMatrix f) gaussianRegressionBeam.q
    gaussianRegressionBeam.q_im_pos (by rw [det_thinLensMatrix]; norm_num)

/-- **The positive-determinant hypothesis of the domain theorem is necessary.**

A phase-conjugating mirror has determinant `-1`, and it sends the regression beam parameter to
`-i`, which is outside the physical domain. The complex ABCD law is therefore not a map of
Gaussian beams for that component, which is the same exception that
`ParaxialInterface.det_transferMatrix` carries at the ray level.
-/
lemma gaussianRegression_phaseConjugate_leaves_domain (n : ℝ) :
    (abcdTransform (ParaxialInterface.phaseConjugate.transferMatrix n n)
      gaussianRegressionBeam.q).im < 0 := by
  rw [abcdTransform, abcdDenominator, ParaxialInterface.transferMatrix]
  norm_num [gaussianRegressionBeam, Complex.div_im]

/-- **A singular prescribed component is rejected by validity.**

The source's corresponding constructor is unconditionally valid, so it admits this matrix. Here
the index-ratio determinant condition excludes it.
-/
lemma gaussianRegression_singular_not_isValid (n₀ n₁ : ℝ) :
    ¬ (ParaxialInterface.prescribed 0 0 0 0).IsValid n₀ n₁ := by
  rintro ⟨hn₀, hn₁, hdet⟩
  rw [show (0 : ℝ) * 0 - 0 * 0 = 0 from by ring] at hdet
  exact absurd hdet.symm (div_pos hn₀ hn₁).ne'

/-- **What the rejection prevents.** Applied to the singular matrix the ABCD formula returns the
junk value zero, which is not a beam parameter at all: its imaginary part is not positive. -/
lemma gaussianRegression_singular_would_be_junk :
    abcdDenominator (!![0, 0; 0, 0] : RayTransferMatrix) gaussianRegressionBeam.q = 0 ∧
      abcdTransform (!![0, 0; 0, 0] : RayTransferMatrix) gaussianRegressionBeam.q = 0 := by
  constructor
  · rw [abcdDenominator]
    norm_num
  · rw [abcdTransform, abcdDenominator]
    norm_num

/-!

## D. The paraxial Helmholtz solution

-/

/-- **Regression R-03, the wave-equation half.** The `q`-parameter Gaussian of unit Rayleigh range
solves the paraxial Helmholtz equation at every wavenumber. -/
lemma gaussianRegression_helmholtz (k : ℝ) :
    SatisfiesParaxialHelmholtz k (gaussianAmplitude k 1) :=
  gaussianAmplitude_satisfiesParaxialHelmholtz one_pos k

/-- The beam parameter used by the Helmholtz solution is the one the beam algebra uses: at the
waist plane it is purely imaginary with the Rayleigh range as imaginary part. -/
lemma gaussianRegression_waistBeamParameter :
    waistBeamParameter 1 0 = Complex.I ∧
      waistBeamParameter 1 0 = gaussianRegressionBeam.q := by
  refine ⟨?_, ?_⟩ <;> simp [waistBeamParameter, gaussianRegressionBeam]

end

end Optics
