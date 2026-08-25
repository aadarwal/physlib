/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Rays.Imaging

/-!
# Gaussian beams and the complex ABCD law

## i. Overview

A Gaussian beam is carried by its complex beam parameter `q` together with the wavelength in the
medium it occupies. The physically valid domain is `0 < q.im`, and that single condition is what
makes every derived quantity well defined: it forces `q ≠ 0`, it makes the beam radius and
Rayleigh range positive, and it makes the ABCD denominator nonvanishing.

The last point is the reason the domain is built into `Optics.GaussianBeam` rather than left as a
side condition. The source development states the ABCD law `q' = (A q + B) / (C q + D)` with no
hypothesis on the denominator. Here `Optics.abcdDenominator_ne_zero` *proves* the denominator is
nonzero: if `C q + D` vanished then, `C` and `D` being real and `q.im` positive, `C` would vanish
and then `D` too, which a system of nonzero determinant cannot do. So the missing hypothesis is
not added as an assumption; it is discharged on the physical domain.

`Optics.im_abcdTransform_pos` is the companion domain statement: a system of positive determinant
maps the physical domain into itself, because the imaginary part transforms by the determinant
divided by the squared modulus of the denominator. Since a valid system has determinant
`n₀ / n₁ > 0`, no application has to re-establish that its output beam is physical.

The wavelength transforms too. A system that changes refractive index changes the wavelength in
the medium by the same ratio, so `GaussianBeam.transform` multiplies it by the determinant. That
is what makes the beam radius continuous across a plane refracting surface, which
`Optics.beamRadius_transform_of_entries` records.

Two further points where this development and its source differ, both recorded so the parity
ledger can be audited rather than guessed at.

First, the source's free-form interface constructor is unconditionally valid, so it admits a
*singular* matrix, and with a total division the ABCD law would then assert `q' = 0`, which is
physically wrong. The corresponding constructor here, `ParaxialInterface.prescribed`, carries the
index-ratio determinant condition in its validity predicate, so a singular matrix is rejected as
invalid rather than silently producing a zero beam parameter. That is a documented improvement
over the source, and `Physlib.Optics.Rays.GaussianRegression` exhibits the rejected case.

Second, the positivity conditions live in different places. The source embeds them in its beam
predicates; here they are fields of `Optics.GaussianBeam`. A port that hoists them onto theorem
statements instead would not be statement-for-statement comparable with the source, and this one
does not: it hoists them into the structure. The ledger row should record that choice.

Explicit non-claims. This file is beam algebra plus one differential-equation verification. It
carries no power, irradiance, or polarization, and no aperture, truncation, or higher-order mode
content: the beam here is the fundamental mode of an unbounded paraxial medium. The Gaussian
solution is verified against the *paraxial* Helmholtz equation, which is itself an approximation
to the Helmholtz equation, and this file makes no claim about that further step.

## ii. Key results

- `Optics.abcdDenominator_ne_zero`: the ABCD denominator cannot vanish on the physical domain,
  discharging the hypothesis the source omits.
- `Optics.im_abcdTransform`: the imaginary part transforms by the determinant.
- `Optics.im_abcdTransform_pos`: a system of positive determinant preserves the physical domain.
- `Optics.GaussianBeam.inv_q_eq`: `1 / q = 1 / R - i λ / (π w²)`, tying the beam radius and
  wavefront curvature to the beam parameter.
- `Optics.GaussianBeam.beamRadius_translation_of_isAtWaist`: `w(z) = w₀ √(1 + (z / z_R)²)`,
  derived from the ABCD law rather than defined.
- `Optics.GaussianBeam.isAtWaist_transform_outputWaistDistance` and
  `Optics.GaussianBeam.waistRadius_sq_transform_of_isAtWaist`: the output waist location and
  radius.
- `Optics.gaussianAmplitude_satisfiesParaxialHelmholtz`: the `q`-parameter amplitude solves the
  paraxial Helmholtz equation.
- `Optics.GaussianBeam.waistRadius_sq_at_outputWaist`: the output waist radius at the plane where
  the output beam is at its waist, with the output waist condition derived rather than assumed.

## iii. Table of contents

- A. The complex beam parameter
- B. Beam radius, wavefront curvature, and the waist
- C. The complex ABCD law
- D. Free propagation and the output waist
- E. The paraxial Helmholtz equation

## iv. References

- B. E. A. Saleh and M. C. Teich, *Fundamentals of Photonics*, 3rd edition, chapter 3, for the
  beam parameter, the `q`-transformation, and the waist formulas.
- M. U. Siddique, *Formal Analysis of Geometrical Optics using Theorem Proving*, PhD thesis,
  Concordia University, 2015, chapter 4, definitions 4.1 to 4.13 and theorems 4.1 to 4.13, for
  the corresponding development, which states the ABCD law without a denominator hypothesis.

-/

@[expose] public section

namespace Optics

noncomputable section

open Real

/-!

## A. The complex beam parameter

-/

/-- A Gaussian beam at a reference plane: the wavelength in the medium it occupies, and its
complex beam parameter.

The validity fields are the physical domain. Positivity of the imaginary part of `q` is the
condition that makes the beam a beam rather than a formal solution, and every result below uses
it rather than assuming a separate side condition.
-/
structure GaussianBeam where
  /-- The wavelength in the medium the beam occupies at this reference plane. -/
  wavelength : ℝ
  /-- The complex beam parameter at this reference plane. -/
  q : ℂ
  /-- A wavelength is positive. -/
  wavelength_pos : 0 < wavelength
  /-- The physical domain of the complex beam parameter. -/
  q_im_pos : 0 < q.im

namespace GaussianBeam

variable (b : GaussianBeam)

/-- A physical beam parameter is nonzero, because its imaginary part is positive. -/
lemma q_ne_zero : b.q ≠ 0 := by
  intro h
  have him := b.q_im_pos
  rw [h] at him
  simp at him

/-- The squared modulus of a physical beam parameter is positive. -/
lemma normSq_q_pos : 0 < Complex.normSq b.q := Complex.normSq_pos.mpr b.q_ne_zero

/-- The Rayleigh range of a Gaussian beam, the imaginary part of its beam parameter. -/
def rayleighRange : ℝ := b.q.im

/-- The Rayleigh range is positive. -/
lemma rayleighRange_pos : 0 < b.rayleighRange := b.q_im_pos

/-- The waist radius of a Gaussian beam, recovered from its Rayleigh range. -/
def waistRadius : ℝ := √(b.wavelength * b.rayleighRange / π)

/-- The waist radius is positive. -/
lemma waistRadius_pos : 0 < b.waistRadius := by
  rw [waistRadius, Real.sqrt_pos]
  exact div_pos (mul_pos b.wavelength_pos b.rayleighRange_pos) pi_pos

/-- The defining relation between the Rayleigh range and the waist radius,
`z_R = π w₀² / λ`. -/
lemma rayleighRange_eq : b.rayleighRange = π * b.waistRadius ^ 2 / b.wavelength := by
  have hlam : b.wavelength ≠ 0 := b.wavelength_pos.ne'
  rw [waistRadius, Real.sq_sqrt (le_of_lt (div_pos (mul_pos b.wavelength_pos b.rayleighRange_pos)
    pi_pos))]
  field_simp

/-!

## B. Beam radius, wavefront curvature, and the waist

-/

/-- The beam radius at the reference plane. -/
def beamRadius : ℝ := √(b.wavelength * Complex.normSq b.q / (π * b.rayleighRange))

/-- The beam radius is positive. -/
lemma beamRadius_pos : 0 < b.beamRadius := by
  rw [beamRadius, Real.sqrt_pos]
  exact div_pos (mul_pos b.wavelength_pos b.normSq_q_pos) (mul_pos pi_pos b.rayleighRange_pos)

/-- The wavefront curvature at the reference plane, the reciprocal of the wavefront radius of
curvature.

The curvature rather than the radius is the primitive notion here, because it is defined at the
waist, where the wavefront is plane and the radius is infinite.
-/
def wavefrontCurvature : ℝ := b.q.re / Complex.normSq b.q

/-- **The defining relation of the complex beam parameter**, `1 / q = 1 / R - i λ / (π w²)`.

This is what makes `beamRadius` and `wavefrontCurvature` the standard quantities rather than two
independent definitions: they are exactly the real and imaginary parts of `1 / q`.
-/
lemma inv_q_eq :
    b.q⁻¹ = Complex.ofReal b.wavefrontCurvature -
      Complex.ofReal (b.wavelength / (π * b.beamRadius ^ 2)) * Complex.I := by
  have hlam : b.wavelength ≠ 0 := b.wavelength_pos.ne'
  have hzR : b.q.im ≠ 0 := b.q_im_pos.ne'
  have hnorm : Complex.normSq b.q ≠ 0 := b.normSq_q_pos.ne'
  have hw : b.beamRadius ^ 2 = b.wavelength * Complex.normSq b.q / (π * b.rayleighRange) := by
    rw [beamRadius, Real.sq_sqrt]
    exact le_of_lt (div_pos (mul_pos b.wavelength_pos b.normSq_q_pos)
      (mul_pos pi_pos b.rayleighRange_pos))
  apply Complex.ext
  · rw [Complex.inv_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, wavefrontCurvature]
    ring
  · rw [Complex.inv_im, hw, rayleighRange]
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_sub]
    field_simp

/-- The wavefront radius of curvature at the reference plane.

The curvature above is the primitive notion, because it is defined at the waist where the
wavefront is plane and the radius is infinite. The radius needs a side condition, and it is the
one the source carries in the corresponding place: the source's `R (z)` divides by `z`, and the
condition here is that `q.re`, which is that `z`, is nonzero.
-/
def wavefrontRadius : ℝ := Complex.normSq b.q / b.q.re

/-- Away from the waist the wavefront radius and curvature are reciprocal. -/
lemma wavefrontRadius_mul_wavefrontCurvature (h : b.q.re ≠ 0) :
    b.wavefrontRadius * b.wavefrontCurvature = 1 := by
  have hnorm : Complex.normSq b.q ≠ 0 := b.normSq_q_pos.ne'
  rw [wavefrontRadius, wavefrontCurvature]
  field_simp

/-- A beam is at its waist when its beam parameter is purely imaginary. -/
def IsAtWaist : Prop := b.q.re = 0

/-- At the waist the beam radius is the waist radius. -/
lemma beamRadius_of_isAtWaist (h : b.IsAtWaist) : b.beamRadius = b.waistRadius := by
  have hzR : b.q.im ≠ 0 := b.q_im_pos.ne'
  rw [beamRadius, waistRadius]
  congr 1
  rw [Complex.normSq_apply, rayleighRange, h]
  field_simp
  ring

/-- At the waist the wavefront is plane. -/
lemma wavefrontCurvature_of_isAtWaist (h : b.IsAtWaist) : b.wavefrontCurvature = 0 := by
  rw [wavefrontCurvature, h, zero_div]

end GaussianBeam

/-!

## C. The complex ABCD law

-/

/-- The denominator of the complex ABCD law. -/
def abcdDenominator (M : RayTransferMatrix) (q : ℂ) : ℂ := (M 1 0 : ℂ) * q + (M 1 1 : ℂ)

/-- The complex ABCD transformation of a beam parameter. -/
def abcdTransform (M : RayTransferMatrix) (q : ℂ) : ℂ :=
  ((M 0 0 : ℂ) * q + (M 0 1 : ℂ)) / abcdDenominator M q

@[simp]
lemma abcdDenominator_im (M : RayTransferMatrix) (q : ℂ) :
    (abcdDenominator M q).im = M 1 0 * q.im := by
  simp [abcdDenominator]

@[simp]
lemma abcdDenominator_re (M : RayTransferMatrix) (q : ℂ) :
    (abcdDenominator M q).re = M 1 0 * q.re + M 1 1 := by
  simp [abcdDenominator]

/-- **The ABCD denominator cannot vanish on the physical domain.**

The source states the ABCD law with no hypothesis on the denominator. It does not need one: if
`C q + D` vanished then, since `C` and `D` are real and `q.im` is positive, `C` would vanish and
hence `D` too, so the lower row of the matrix would be zero and its determinant would vanish.
-/
lemma abcdDenominator_ne_zero (M : RayTransferMatrix) (q : ℂ) (hq : 0 < q.im)
    (hdet : M.det ≠ 0) : abcdDenominator M q ≠ 0 := by
  intro h
  have hIm : M 1 0 * q.im = 0 := by
    rw [← abcdDenominator_im M q, h, Complex.zero_im]
  have hC : M 1 0 = 0 := by
    rcases mul_eq_zero.mp hIm with hC | hIm'
    · exact hC
    · exact absurd hIm' hq.ne'
  have hRe : M 1 0 * q.re + M 1 1 = 0 := by
    rw [← abcdDenominator_re M q, h, Complex.zero_re]
  have hD : M 1 1 = 0 := by
    rw [hC, zero_mul, zero_add] at hRe
    exact hRe
  exact hdet (by rw [Matrix.det_fin_two, hC, hD]; ring)

/-- **The imaginary part transforms by the determinant.** -/
lemma im_abcdTransform (M : RayTransferMatrix) (q : ℂ) :
    (abcdTransform M q).im = M.det * q.im / Complex.normSq (abcdDenominator M q) := by
  rw [abcdTransform, Complex.div_im, Matrix.det_fin_two]
  simp only [Complex.add_im, Complex.add_re, Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, abcdDenominator_im, abcdDenominator_re, zero_mul, add_zero, sub_zero]
  field_simp
  ring

/-- **A system of positive determinant preserves the physical domain.**

This is the domain proof `goal.md` §R4 asks for. A valid optical system has determinant
`n₀ / n₁ > 0`, so the output beam of a valid system is automatically physical and no application
has to re-establish it.
-/
theorem im_abcdTransform_pos (M : RayTransferMatrix) (q : ℂ) (hq : 0 < q.im)
    (hdet : 0 < M.det) : 0 < (abcdTransform M q).im := by
  have hden := abcdDenominator_ne_zero M q hq hdet.ne'
  rw [im_abcdTransform M q]
  exact div_pos (mul_pos hdet hq) (Complex.normSq_pos.mpr hden)

namespace GaussianBeam

/-- **The complex ABCD law.** A Gaussian beam transported through a system of positive
determinant.

The wavelength is multiplied by the determinant because a system that changes refractive index
changes the wavelength in the medium by the same ratio.
-/
def transform (b : GaussianBeam) (M : RayTransferMatrix) (hdet : 0 < M.det) : GaussianBeam where
  wavelength := b.wavelength * M.det
  q := abcdTransform M b.q
  wavelength_pos := mul_pos b.wavelength_pos hdet
  q_im_pos := im_abcdTransform_pos M b.q b.q_im_pos hdet

@[simp]
lemma transform_wavelength (b : GaussianBeam) (M : RayTransferMatrix) (hdet : 0 < M.det) :
    (b.transform M hdet).wavelength = b.wavelength * M.det := rfl

@[simp]
lemma transform_q (b : GaussianBeam) (M : RayTransferMatrix) (hdet : 0 < M.det) :
    (b.transform M hdet).q = abcdTransform M b.q := rfl

/-- **A component with `A = 1` and `B = 0` leaves the beam radius unchanged.**

A thin lens and a plane refracting surface are the cases of interest: a lens changes the wavefront
curvature but not the spot size, and a plane interface changes neither. The wavelength factor in
`transform` is exactly what makes this work across an index step.
-/
lemma beamRadius_transform_of_entries (b : GaussianBeam) (M : RayTransferMatrix)
    (hdet : 0 < M.det) (hA : M 0 0 = 1) (hB : M 0 1 = 0) :
    (b.transform M hdet).beamRadius = b.beamRadius := by
  have hden := abcdDenominator_ne_zero M b.q b.q_im_pos hdet.ne'
  have hdenSq : Complex.normSq (abcdDenominator M b.q) ≠ 0 := (Complex.normSq_pos.mpr hden).ne'
  rw [beamRadius, beamRadius, rayleighRange, rayleighRange, transform_wavelength, transform_q]
  congr 1
  rw [im_abcdTransform M b.q, abcdTransform, Complex.normSq_div, hA, hB]
  simp only [Complex.ofReal_one, Complex.ofReal_zero, one_mul, add_zero]
  field_simp

end GaussianBeam

/-!

## D. Free propagation and the output waist

-/

/-- A translation has unit determinant. -/
@[simp]
lemma det_translationMatrix (d : ℝ) : (translationMatrix d).det = 1 := by
  rw [translationMatrix, Matrix.det_fin_two_of]
  ring

/-- A translation has positive determinant, so it preserves the physical domain. -/
lemma det_translationMatrix_pos (d : ℝ) : 0 < (translationMatrix d).det := by
  rw [det_translationMatrix]
  norm_num

/-- **The free-propagation law.** Propagating a distance `d` adds `d` to the beam parameter. -/
@[simp]
lemma abcdTransform_translationMatrix (d : ℝ) (q : ℂ) :
    abcdTransform (translationMatrix d) q = q + d := by
  rw [abcdTransform, abcdDenominator]
  simp [translationMatrix]

namespace GaussianBeam

lemma transform_translationMatrix_q (b : GaussianBeam) (d : ℝ) :
    (b.transform (translationMatrix d) (det_translationMatrix_pos d)).q = b.q + d := by
  rw [transform_q, abcdTransform_translationMatrix]

lemma transform_translationMatrix_wavelength (b : GaussianBeam) (d : ℝ) :
    (b.transform (translationMatrix d) (det_translationMatrix_pos d)).wavelength =
      b.wavelength := by
  rw [transform_wavelength, det_translationMatrix, mul_one]

/-- Free propagation does not change the Rayleigh range. -/
@[simp]
lemma rayleighRange_transform_translationMatrix (b : GaussianBeam) (d : ℝ) :
    (b.transform (translationMatrix d) (det_translationMatrix_pos d)).rayleighRange =
      b.rayleighRange := by
  rw [rayleighRange, rayleighRange, transform_translationMatrix_q]
  simp

/-- **The beam radius along free propagation**, `w(z) = w₀ √(1 + (z / z_R)²)`.

The formula is derived from the ABCD law applied to a beam at its waist, not stipulated.
-/
theorem beamRadius_translation_of_isAtWaist (b : GaussianBeam) (h : b.IsAtWaist) (z : ℝ) :
    (b.transform (translationMatrix z) (det_translationMatrix_pos z)).beamRadius =
      b.waistRadius * √(1 + (z / b.rayleighRange) ^ 2) := by
  have hzR : b.rayleighRange ≠ 0 := b.rayleighRange_pos.ne'
  have hzR' : b.q.im ≠ 0 := b.q_im_pos.ne'
  rw [beamRadius, waistRadius, transform_translationMatrix_wavelength,
    rayleighRange_transform_translationMatrix, transform_translationMatrix_q,
    ← Real.sqrt_mul (le_of_lt (div_pos (mul_pos b.wavelength_pos b.rayleighRange_pos) pi_pos))]
  congr 1
  rw [Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, add_zero]
  rw [h, zero_add, rayleighRange]
  field_simp
  ring

/-- Free propagation does not change the waist radius, because it changes neither the wavelength
nor the Rayleigh range. -/
@[simp]
lemma waistRadius_transform_translationMatrix (b : GaussianBeam) (d : ℝ) :
    (b.transform (translationMatrix d) (det_translationMatrix_pos d)).waistRadius =
      b.waistRadius := by
  rw [waistRadius, waistRadius, transform_translationMatrix_wavelength,
    rayleighRange_transform_translationMatrix]

/-- **The wavefront radius along free propagation**, `R(z) = z (1 + (z_R / z)²)`.

The hypothesis `z ≠ 0` is the source's own side condition on the wavefront radius, reproduced
here: at the waist the wavefront is plane and the radius is not defined.
-/
theorem wavefrontRadius_translation_of_isAtWaist (b : GaussianBeam) (h : b.IsAtWaist) (z : ℝ)
    (hz : z ≠ 0) :
    (b.transform (translationMatrix z) (det_translationMatrix_pos z)).wavefrontRadius =
      z * (1 + (b.rayleighRange / z) ^ 2) := by
  rw [wavefrontRadius, transform_translationMatrix_q, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, add_zero]
  rw [h, zero_add, rayleighRange]
  field_simp

/-- The distance from the exit plane of a system to the output beam waist. -/
def outputWaistDistance (b : GaussianBeam) (M : RayTransferMatrix) (hdet : 0 < M.det) : ℝ :=
  -(b.transform M hdet).q.re

/-- **The output waist location.** Propagating the output beam by `outputWaistDistance` reaches
its waist. -/
theorem isAtWaist_transform_outputWaistDistance (b : GaussianBeam) (M : RayTransferMatrix)
    (hdet : 0 < M.det) :
    ((b.transform M hdet).transform (translationMatrix (b.outputWaistDistance M hdet))
      (det_translationMatrix_pos _)).IsAtWaist := by
  rw [IsAtWaist, transform_translationMatrix_q, outputWaistDistance]
  simp

/-- **The output waist for an input at its waist.** For a beam entering at its waist, the output
beam parameter has the stated real and imaginary parts, which give the output waist location and
Rayleigh range in closed form.
-/
theorem transform_q_of_isAtWaist (b : GaussianBeam) (h : b.IsAtWaist) (M : RayTransferMatrix)
    (hdet : 0 < M.det) :
    (b.transform M hdet).q.re =
        (M 0 1 * M 1 1 + M 0 0 * M 1 0 * b.rayleighRange ^ 2) /
          (M 1 0 ^ 2 * b.rayleighRange ^ 2 + M 1 1 ^ 2) ∧
      (b.transform M hdet).q.im =
        M.det * b.rayleighRange / (M 1 0 ^ 2 * b.rayleighRange ^ 2 + M 1 1 ^ 2) := by
  have hden := abcdDenominator_ne_zero M b.q b.q_im_pos hdet.ne'
  have hnormSq : Complex.normSq (abcdDenominator M b.q) =
      M 1 0 ^ 2 * b.rayleighRange ^ 2 + M 1 1 ^ 2 := by
    rw [Complex.normSq_apply, abcdDenominator_re, abcdDenominator_im, rayleighRange, h]
    ring
  constructor
  · rw [transform_q, abcdTransform, Complex.div_re, hnormSq]
    simp only [Complex.add_im, Complex.add_re, Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, abcdDenominator_im, abcdDenominator_re, zero_mul, add_zero, sub_zero]
    rw [rayleighRange, h]
    field_simp
    ring
  · rw [transform_q, im_abcdTransform M b.q, hnormSq, rayleighRange]

/-- **The output waist location in closed form**, for a beam entering at its waist. -/
theorem outputWaistDistance_of_isAtWaist (b : GaussianBeam) (h : b.IsAtWaist)
    (M : RayTransferMatrix) (hdet : 0 < M.det) :
    b.outputWaistDistance M hdet =
      -((M 0 1 * M 1 1 + M 0 0 * M 1 0 * b.rayleighRange ^ 2) /
        (M 1 0 ^ 2 * b.rayleighRange ^ 2 + M 1 1 ^ 2)) := by
  rw [outputWaistDistance, (transform_q_of_isAtWaist b h M hdet).1]

/-- **The output waist radius** for a beam entering at its waist,
`w₀'² = (det M)² w₀² / (C² z_R² + D²)`.

The statement is squared because that is the form in which the relation is algebraic; taking a
square root would add nothing but a side condition.
-/
theorem waistRadius_sq_transform_of_isAtWaist (b : GaussianBeam) (h : b.IsAtWaist)
    (M : RayTransferMatrix) (hdet : 0 < M.det) :
    (b.transform M hdet).waistRadius ^ 2 =
      M.det ^ 2 * b.waistRadius ^ 2 / (M 1 0 ^ 2 * b.rayleighRange ^ 2 + M 1 1 ^ 2) := by
  have hden := abcdDenominator_ne_zero M b.q b.q_im_pos hdet.ne'
  have hnormSq : Complex.normSq (abcdDenominator M b.q) =
      M 1 0 ^ 2 * b.rayleighRange ^ 2 + M 1 1 ^ 2 := by
    rw [Complex.normSq_apply, abcdDenominator_re, abcdDenominator_im, rayleighRange, h]
    ring
  have hpos : 0 < M 1 0 ^ 2 * b.rayleighRange ^ 2 + M 1 1 ^ 2 := by
    rw [← hnormSq]
    exact Complex.normSq_pos.mpr hden
  obtain ⟨-, him⟩ := transform_q_of_isAtWaist b h M hdet
  rw [waistRadius, waistRadius,
    Real.sq_sqrt (le_of_lt (div_pos (mul_pos (b.transform M hdet).wavelength_pos
      (b.transform M hdet).rayleighRange_pos) pi_pos)),
    Real.sq_sqrt (le_of_lt (div_pos (mul_pos b.wavelength_pos b.rayleighRange_pos) pi_pos)),
    transform_wavelength, rayleighRange, him, rayleighRange]
  field_simp

/-- **The waist-to-waist output waist radius.**

The source's waist theorem constrains the beam to be at its waist at *both* ends. Here only the
input waist is a hypothesis: the output waist plane is produced by
`isAtWaist_transform_outputWaistDistance` and its radius is the one below, because free
propagation changes neither the wavelength nor the Rayleigh range. The restriction on the input
is kept and the restriction on the output is discharged, rather than either being dropped
silently.
-/
theorem waistRadius_sq_at_outputWaist (b : GaussianBeam) (h : b.IsAtWaist)
    (M : RayTransferMatrix) (hdet : 0 < M.det) :
    ((b.transform M hdet).transform (translationMatrix (b.outputWaistDistance M hdet))
        (det_translationMatrix_pos _)).waistRadius ^ 2 =
      M.det ^ 2 * b.waistRadius ^ 2 / (M 1 0 ^ 2 * b.rayleighRange ^ 2 + M 1 1 ^ 2) := by
  rw [waistRadius_transform_translationMatrix]
  exact waistRadius_sq_transform_of_isAtWaist b h M hdet

end GaussianBeam

/-!

## E. The paraxial Helmholtz equation

-/

/-- The complex beam parameter at axial position `z` of a beam whose waist is at the origin with
Rayleigh range `zR`. -/
def waistBeamParameter (zR z : ℝ) : ℂ := (z : ℂ) + (zR : ℂ) * Complex.I

@[simp]
lemma waistBeamParameter_re (zR z : ℝ) : (waistBeamParameter zR z).re = z := by
  simp [waistBeamParameter]

@[simp]
lemma waistBeamParameter_im (zR z : ℝ) : (waistBeamParameter zR z).im = zR := by
  simp [waistBeamParameter]

/-- A positive Rayleigh range puts the beam parameter in the physical domain, so it is nonzero at
every axial position. -/
lemma waistBeamParameter_ne_zero {zR : ℝ} (hzR : 0 < zR) (z : ℝ) :
    waistBeamParameter zR z ≠ 0 := by
  intro h
  have him : (waistBeamParameter zR z).im = 0 := by rw [h, Complex.zero_im]
  rw [waistBeamParameter_im] at him
  exact hzR.ne' him

/-- The coefficient of the transverse quadratic in the exponent of the fundamental Gaussian
beam, written as a product so that it differentiates through the reciprocal of the beam
parameter. -/
def gaussianExponentCoefficient (k zR z : ℝ) : ℂ :=
  -Complex.I * (k : ℂ) / 2 * (waistBeamParameter zR z)⁻¹

/-- The exponent coefficient in its familiar quotient form, `- i k / (2 q)`. -/
lemma gaussianExponentCoefficient_eq {zR : ℝ} (hzR : 0 < zR) (k z : ℝ) :
    gaussianExponentCoefficient k zR z = -Complex.I * k / (2 * waistBeamParameter zR z) := by
  have hne := waistBeamParameter_ne_zero hzR z
  rw [gaussianExponentCoefficient]
  field_simp

/-- The complex amplitude of the fundamental Gaussian beam of wavenumber `k` whose waist lies at
the origin with Rayleigh range `zR`.

This is the `q`-parameter form: an amplitude `1 / q` times a transverse Gaussian whose complex
width is set by the same `q`.
-/
def gaussianAmplitude (k zR x y z : ℝ) : ℂ :=
  (waistBeamParameter zR z)⁻¹ *
    Complex.exp (gaussianExponentCoefficient k zR z * ((x : ℂ) ^ 2 + (y : ℂ) ^ 2))

/-- **The paraxial Helmholtz equation.**

The convention is fixed here and is not the only one in use: the Laplacian is the **transverse**
one, in the two coordinates orthogonal to the optical axis, and the axial term enters as
`- 2 i k ∂_z`, which is the form taken by the suppressed carrier `exp (- i k z)`. A development
using the full three-dimensional Laplacian, or the opposite carrier sign, states a different
equation, and nothing here is a claim about those.

One divergence from the source is a typing choice, not a physical one, and it goes against this
development. The source types its amplitude on complex arguments and quantifies its verification
over complex `x`, `y`, and `z`, which is an artifact of the complex-differentiation tactic it
uses; it therefore asserts strictly more instances than the statement here, which takes real
transverse and axial coordinates and real derivatives. The version here is the physically faithful
one and the logically narrower one on that axis, so it is not the same statement.
-/
def SatisfiesParaxialHelmholtz (k : ℝ) (u : ℝ → ℝ → ℝ → ℂ) : Prop :=
  ∀ x y z : ℝ,
    deriv (fun x' => deriv (fun x'' => u x'' y z) x') x +
        deriv (fun y' => deriv (fun y'' => u x y'' z) y') y -
      2 * Complex.I * k * deriv (fun z' => u x y z') z = 0

/-- The Gaussian amplitude is symmetric in its two transverse arguments. -/
lemma gaussianAmplitude_comm (k zR x y z : ℝ) :
    gaussianAmplitude k zR x y z = gaussianAmplitude k zR y x z := by
  rw [gaussianAmplitude, gaussianAmplitude, add_comm]

/-- The first transverse derivative of the Gaussian amplitude. -/
lemma hasDerivAt_gaussianAmplitude_transverse (k zR y z x : ℝ) :
    HasDerivAt (fun x' : ℝ => gaussianAmplitude k zR x' y z)
      (gaussianAmplitude k zR x y z * (2 * gaussianExponentCoefficient k zR z * (x : ℂ))) x := by
  have hcoe : HasDerivAt (fun x' : ℝ => (x' : ℂ)) 1 x := (hasDerivAt_id x).ofReal_comp
  have hsq : HasDerivAt (fun x' : ℝ => ((x' : ℂ) ^ 2 + (y : ℂ) ^ 2)) (2 * (x : ℂ)) x := by
    simpa using (hcoe.pow 2).add_const ((y : ℂ) ^ 2)
  have hexp := (hsq.const_mul (gaussianExponentCoefficient k zR z)).cexp
  refine (hexp.const_mul ((waistBeamParameter zR z)⁻¹)).congr_deriv ?_
  rw [gaussianAmplitude]
  ring

/-- The second transverse derivative of the Gaussian amplitude. -/
lemma hasDerivAt_deriv_gaussianAmplitude_transverse (k zR y z x : ℝ) :
    HasDerivAt
      (fun x' : ℝ =>
        gaussianAmplitude k zR x' y z * (2 * gaussianExponentCoefficient k zR z * (x' : ℂ)))
      (gaussianAmplitude k zR x y z *
        (2 * gaussianExponentCoefficient k zR z +
          4 * gaussianExponentCoefficient k zR z ^ 2 * (x : ℂ) ^ 2)) x := by
  have hcoe : HasDerivAt (fun x' : ℝ => (x' : ℂ)) 1 x := (hasDerivAt_id x).ofReal_comp
  have hlin := hcoe.const_mul (2 * gaussianExponentCoefficient k zR z)
  exact ((hasDerivAt_gaussianAmplitude_transverse k zR y z x).mul hlin).congr_deriv (by ring)

/-- The transverse second derivative, as an equation between derivatives. -/
lemma deriv_deriv_gaussianAmplitude_transverse (k zR y z x : ℝ) :
    deriv (fun x' : ℝ => deriv (fun x'' : ℝ => gaussianAmplitude k zR x'' y z) x') x =
      gaussianAmplitude k zR x y z *
        (2 * gaussianExponentCoefficient k zR z +
          4 * gaussianExponentCoefficient k zR z ^ 2 * (x : ℂ) ^ 2) := by
  have hfun : (fun x' : ℝ => deriv (fun x'' : ℝ => gaussianAmplitude k zR x'' y z) x') =
      fun x' : ℝ =>
        gaussianAmplitude k zR x' y z * (2 * gaussianExponentCoefficient k zR z * (x' : ℂ)) :=
    funext fun x' => (hasDerivAt_gaussianAmplitude_transverse k zR y z x').deriv
  rw [hfun]
  exact (hasDerivAt_deriv_gaussianAmplitude_transverse k zR y z x).deriv

/-- The axial derivative of the Gaussian amplitude. -/
lemma hasDerivAt_gaussianAmplitude_axial {zR : ℝ} (hzR : 0 < zR) (k x y z : ℝ) :
    HasDerivAt (fun z' : ℝ => gaussianAmplitude k zR x y z')
      (gaussianAmplitude k zR x y z *
        (-(waistBeamParameter zR z)⁻¹ +
          Complex.I * k / (2 * waistBeamParameter zR z ^ 2) * ((x : ℂ) ^ 2 + (y : ℂ) ^ 2))) z := by
  have hne := waistBeamParameter_ne_zero hzR z
  have hcoe : HasDerivAt (fun z' : ℝ => (z' : ℂ)) 1 z := (hasDerivAt_id z).ofReal_comp
  have hq : HasDerivAt (fun z' : ℝ => waistBeamParameter zR z') 1 z :=
    hcoe.add_const ((zR : ℂ) * Complex.I)
  have hinv : HasDerivAt (fun z' : ℝ => (waistBeamParameter zR z')⁻¹)
      (-1 / waistBeamParameter zR z ^ 2) z := hq.inv hne
  have hcoeff : HasDerivAt (fun z' : ℝ => gaussianExponentCoefficient k zR z')
      (Complex.I * (k : ℂ) / (2 * waistBeamParameter zR z ^ 2)) z := by
    refine (hinv.const_mul (-Complex.I * (k : ℂ) / 2)).congr_deriv ?_
    field_simp
  have hexp := (hcoeff.mul_const ((x : ℂ) ^ 2 + (y : ℂ) ^ 2)).cexp
  refine (hinv.mul hexp).congr_deriv ?_
  rw [gaussianAmplitude]
  field_simp

/-- **The `q`-parameter Gaussian solves the paraxial Helmholtz equation.**

This is the verification that the beam algebra of the preceding sections describes an actual
solution of a wave equation rather than a self-consistent set of formulas. The equation, and in
particular which Laplacian it uses, is the one fixed by `Optics.SatisfiesParaxialHelmholtz`.
-/
theorem gaussianAmplitude_satisfiesParaxialHelmholtz {zR : ℝ} (hzR : 0 < zR) (k : ℝ) :
    SatisfiesParaxialHelmholtz k (gaussianAmplitude k zR) := by
  intro x y z
  have hne := waistBeamParameter_ne_zero hzR z
  have hx := deriv_deriv_gaussianAmplitude_transverse k zR y z x
  have hy : deriv (fun y' : ℝ => deriv (fun y'' : ℝ => gaussianAmplitude k zR x y'' z) y') y =
      gaussianAmplitude k zR x y z *
        (2 * gaussianExponentCoefficient k zR z +
          4 * gaussianExponentCoefficient k zR z ^ 2 * (y : ℂ) ^ 2) := by
    simp only [gaussianAmplitude_comm k zR x]
    rw [deriv_deriv_gaussianAmplitude_transverse k zR x z y, gaussianAmplitude_comm k zR y x]
  have hz := (hasDerivAt_gaussianAmplitude_axial hzR k x y z).deriv
  rw [hx, hy, hz, gaussianExponentCoefficient]
  field_simp
  ring

end

end Optics
