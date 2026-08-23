/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.ClassicalMechanics.WaveEquation.ComplexWaveVector.Hyperplane

/-!
# Real-radicand normal roots of complex wave vectors

## i. Overview

This file classifies the complex normal component of a wave vector when its square is a real
number. A nonnegative radicand gives the two real alternatives `±√c`; a nonpositive radicand
gives the two imaginary alternatives `±I * √(-c)`. At zero all alternatives agree with the
unique zero normal component.

The neutral results classify algebraic roots without choosing a sign. With a separately supplied
strict phase or attenuation direction, later results select the side-compatible algebraic root and
also force the radicand's strict sign and the complementary real normal component to vanish.

None of these results assigns a medium, interface wave role, propagation, grazing, evanescence,
group velocity, energy flux, outgoing condition, or power meaning.

## ii. Key results

- `normalComponent_eq_sqrt_or_eq_neg_sqrt_of_sq_eq_of_nonneg`: the nonnegative-radicand roots.
- `normalComponent_eq_zero_of_sq_eq_zero`: the unique zero root.
- `normalComponent_eq_I_mul_sqrt_or_eq_neg_I_mul_sqrt_of_sq_eq_of_nonpos`: the
  nonpositive-radicand roots.
- `normalRoot_data_of_sq_eq_real_of_isPhaseDirectedInto`: strict phase
  direction selects the corresponding real root.
- `normalRoot_data_of_sq_eq_real_of_isAttenuationDirectedInto`:
  strict attenuation direction selects the root with the opposite imaginary sign.

## iii. Table of contents

- A. Nonnegative radicands
- B. Zero radicand
- C. Nonpositive radicands
- D. Phase-directed real roots
- E. Attenuation-directed imaginary roots

## iv. References

The proofs combine Physlib's complex hyperplane-normal component with Mathlib's real square root
and two-root classification in an integral domain. The directed results additionally use the real
and imaginary parts of a complex square. No external formal-development source is copied or
translated here.
-/

@[expose] public section

namespace ClassicalMechanics

open Space

noncomputable section

namespace ComplexWaveVector

variable {d : ℕ}

/-!

## A. Nonnegative radicands

-/

/-- If a complex wave vector's squared hyperplane-normal component is a nonnegative real number,
then the normal component is its positive or negative real square root. The alternatives coincide
when the radicand is zero. -/
lemma normalComponent_eq_sqrt_or_eq_neg_sqrt_of_sq_eq_of_nonneg
    (plane : OrientedAffineHyperplane d) (z : ComplexWaveVector d) (radicand : ℝ)
    (hSquare : hyperplaneNormalComponent plane z ^ 2 = (radicand : ℂ))
    (hRadicand : 0 ≤ radicand) :
    hyperplaneNormalComponent plane z = (Real.sqrt radicand : ℂ) ∨
      hyperplaneNormalComponent plane z = -(Real.sqrt radicand : ℂ) := by
  have hRootSquare : (Real.sqrt radicand : ℂ) ^ 2 = (radicand : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hRadicand]
  exact eq_or_eq_neg_of_sq_eq_sq _ _ (hSquare.trans hRootSquare.symm)

/-!

## B. Zero radicand

-/

/-- A complex wave vector whose squared hyperplane-normal component is zero has zero normal
component.

This records the unique normal-root case needed at a later critical or grazing boundary; by itself
it assigns neither interpretation. -/
lemma normalComponent_eq_zero_of_sq_eq_zero
    (plane : OrientedAffineHyperplane d) (z : ComplexWaveVector d)
    (hSquare : hyperplaneNormalComponent plane z ^ 2 = 0) :
    hyperplaneNormalComponent plane z = 0 := by
  exact sq_eq_zero_iff.mp hSquare

/-!

## C. Nonpositive radicands

-/

/-- If a complex wave vector's squared hyperplane-normal component is a nonpositive real number,
then the normal component is plus or minus `I` times the positive real square root of the negated
radicand. The alternatives coincide when the radicand is zero. -/
lemma normalComponent_eq_I_mul_sqrt_or_eq_neg_I_mul_sqrt_of_sq_eq_of_nonpos
    (plane : OrientedAffineHyperplane d) (z : ComplexWaveVector d) (radicand : ℝ)
    (hSquare : hyperplaneNormalComponent plane z ^ 2 = (radicand : ℂ))
    (hRadicand : radicand ≤ 0) :
    hyperplaneNormalComponent plane z =
        Complex.I * (Real.sqrt (-radicand) : ℂ) ∨
      hyperplaneNormalComponent plane z =
        -(Complex.I * (Real.sqrt (-radicand) : ℂ)) := by
  have hRootSquare :
      (Complex.I * (Real.sqrt (-radicand) : ℂ)) ^ 2 = (radicand : ℂ) := by
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow,
      Real.sq_sqrt (neg_nonneg.mpr hRadicand)]
    simp only [neg_mul, one_mul, Complex.ofReal_neg, neg_neg]
  exact eq_or_eq_neg_of_sq_eq_sq _ _ (hSquare.trans hRootSquare.symm)

/-!

## D. Phase-directed real roots

-/

private lemma sq_eq_real_parts {w : ℂ} {radicand : ℝ}
    (hSquare : w ^ 2 = (radicand : ℂ)) :
    w.re ^ 2 - w.im ^ 2 = radicand ∧ w.re * w.im = 0 := by
  have hSquareIm := congrArg Complex.im hSquare
  have hSquareRe := congrArg Complex.re hSquare
  simp only [pow_two, Complex.mul_im, Complex.ofReal_im] at hSquareIm
  simp only [pow_two, Complex.mul_re, Complex.ofReal_re] at hSquareRe
  constructor <;> nlinarith

private lemma real_root_data {w : ℂ} {radicand : ℝ}
    (hSquare : w ^ 2 = (radicand : ℂ)) (hRe : w.re ≠ 0) :
    0 < radicand ∧ w.im = 0 := by
  obtain ⟨hSquareRe, hProduct⟩ := sq_eq_real_parts hSquare
  have hIm : w.im = 0 := (mul_eq_zero.mp hProduct).resolve_left hRe
  exact ⟨by nlinarith [sq_pos_of_ne_zero hRe], hIm⟩

/-- If a complex normal component has real square and its phase vector points strictly into a
selected side, then the radicand is positive, its attenuation normal component vanishes, and its
normal component is the real square root with that side's sign.

This is side-relative algebraic root selection, not a group-velocity, energy-flux, outgoing, or
power statement. -/
lemma normalRoot_data_of_sq_eq_real_of_isPhaseDirectedInto
    (plane : OrientedAffineHyperplane d) (z : ComplexWaveVector d) (radicand : ℝ)
    (side : OrientedAffineHyperplane.Side)
    (hSquare : hyperplaneNormalComponent plane z ^ 2 = (radicand : ℂ))
    (hDirection : z.IsPhaseDirectedInto plane side) :
    0 < radicand ∧ plane.normalComponent z.attenuationVector = 0 ∧
      hyperplaneNormalComponent plane z =
        ((side.sign * Real.sqrt radicand : ℝ) : ℂ) := by
  have hReNe : (hyperplaneNormalComponent plane z).re ≠ 0 := by
    intro hRe
    rw [IsPhaseDirectedInto, hRe, mul_zero] at hDirection
    exact (lt_irrefl 0 hDirection)
  obtain ⟨hRadicand, hIm⟩ := real_root_data hSquare hReNe
  refine ⟨hRadicand, ?_, ?_⟩
  · simpa only [hyperplaneNormalComponent_im, neg_eq_zero] using hIm
  · cases side with
    | negative =>
        rcases normalComponent_eq_sqrt_or_eq_neg_sqrt_of_sq_eq_of_nonneg
            plane z radicand hSquare hRadicand.le with hRoot | hRoot
        · have hNormal :=
            (isPhaseDirectedInto_negative_iff z plane).mp hDirection
          have hRootRe := congrArg Complex.re hRoot
          simp only [hyperplaneNormalComponent_re, Complex.ofReal_re] at hRootRe
          exfalso
          nlinarith [Real.sqrt_nonneg radicand]
        · simpa using hRoot
    | positive =>
        rcases normalComponent_eq_sqrt_or_eq_neg_sqrt_of_sq_eq_of_nonneg
            plane z radicand hSquare hRadicand.le with hRoot | hRoot
        · simpa using hRoot
        · have hNormal :=
            (isPhaseDirectedInto_positive_iff z plane).mp hDirection
          have hRootRe := congrArg Complex.re hRoot
          simp only [hyperplaneNormalComponent_re, Complex.neg_re,
            Complex.ofReal_re] at hRootRe
          exfalso
          nlinarith [Real.sqrt_nonneg radicand]

/-!

## E. Attenuation-directed imaginary roots

-/

private lemma imaginary_root_data {w : ℂ} {radicand : ℝ}
    (hSquare : w ^ 2 = (radicand : ℂ)) (hIm : w.im ≠ 0) :
    radicand < 0 ∧ w.re = 0 := by
  obtain ⟨hSquareRe, hProduct⟩ := sq_eq_real_parts hSquare
  have hRe : w.re = 0 := (mul_eq_zero.mp hProduct).resolve_right hIm
  exact ⟨by nlinarith [sq_pos_of_ne_zero hIm], hRe⟩

/-- If a complex normal component has real square and its attenuation vector points strictly into
a selected side, then the radicand is negative, its phase normal component vanishes, and its normal
component is `-I` times the square root with that side's sign.

For `K = q - I a`, the positive-side root is `-I * √(-c)` and the negative-side root is
`I * √(-c)`. This does not assert zero tangential attenuation or assign a transmitted,
evanescent, outgoing, energy-flux, or power role. -/
lemma normalRoot_data_of_sq_eq_real_of_isAttenuationDirectedInto
    (plane : OrientedAffineHyperplane d) (z : ComplexWaveVector d) (radicand : ℝ)
    (side : OrientedAffineHyperplane.Side)
    (hSquare : hyperplaneNormalComponent plane z ^ 2 = (radicand : ℂ))
    (hDirection : z.IsAttenuationDirectedInto plane side) :
    radicand < 0 ∧ plane.normalComponent z.phaseVector = 0 ∧
      hyperplaneNormalComponent plane z =
        -Complex.I * ((side.sign * Real.sqrt (-radicand) : ℝ) : ℂ) := by
  have hImNe : (hyperplaneNormalComponent plane z).im ≠ 0 := by
    intro hIm
    rw [IsAttenuationDirectedInto, hIm, neg_zero, mul_zero] at hDirection
    exact (lt_irrefl 0 hDirection)
  obtain ⟨hRadicand, hRe⟩ := imaginary_root_data hSquare hImNe
  refine ⟨hRadicand, ?_, ?_⟩
  · simpa only [hyperplaneNormalComponent_re] using hRe
  · cases side with
    | negative =>
        rcases normalComponent_eq_I_mul_sqrt_or_eq_neg_I_mul_sqrt_of_sq_eq_of_nonpos
            plane z radicand hSquare hRadicand.le with hRoot | hRoot
        · calc
            hyperplaneNormalComponent plane z =
                Complex.I * (Real.sqrt (-radicand) : ℂ) := hRoot
            _ = -Complex.I *
                ((OrientedAffineHyperplane.Side.negative.sign *
                  Real.sqrt (-radicand) : ℝ) : ℂ) := by simp
        · have hNormal :=
            (isAttenuationDirectedInto_negative_iff z plane).mp hDirection
          have hRootIm := congrArg Complex.im hRoot
          simp only [hyperplaneNormalComponent_im, Complex.neg_im, Complex.mul_im,
            Complex.I_re, Complex.ofReal_im, mul_zero, Complex.I_im,
            Complex.ofReal_re, one_mul, zero_add] at hRootIm
          exfalso
          nlinarith [Real.sqrt_nonneg (-radicand)]
    | positive =>
        rcases normalComponent_eq_I_mul_sqrt_or_eq_neg_I_mul_sqrt_of_sq_eq_of_nonpos
            plane z radicand hSquare hRadicand.le with hRoot | hRoot
        · have hNormal :=
            (isAttenuationDirectedInto_positive_iff z plane).mp hDirection
          have hRootIm := congrArg Complex.im hRoot
          simp only [hyperplaneNormalComponent_im, Complex.mul_im, Complex.I_re,
            Complex.ofReal_im, mul_zero, Complex.I_im, Complex.ofReal_re,
            one_mul, zero_add] at hRootIm
          exfalso
          nlinarith [Real.sqrt_nonneg (-radicand)]
        · calc
            hyperplaneNormalComponent plane z =
                -(Complex.I * (Real.sqrt (-radicand) : ℂ)) := hRoot
            _ = -Complex.I *
                ((OrientedAffineHyperplane.Side.positive.sign *
                  Real.sqrt (-radicand) : ℝ) : ℂ) := by simp

end ComplexWaveVector

end
end ClassicalMechanics
