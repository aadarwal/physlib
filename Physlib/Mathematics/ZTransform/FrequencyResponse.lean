/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Mathematics.ZTransform.DifferenceEquation

/-!
# Frequency response of finite-lag difference equations

## i. Overview

For a real angular frequency `ω`, the point `unitCirclePoint ω = exp (ω I)` has norm one and
its reciprocal is `exp (-ω I)`. Evaluating a finite delay symbol at that reciprocal separates
it into a cosine sum minus `I` times a sine sum. Consequently, the transfer function of a
finite-lag difference equation is the quotient of an explicit trigonometric numerator and
denominator.

The final result retains the semantic hypotheses of the difference equation. If causal input and
output sequences solve the recurrence, the unit-circle point lies in their IIR region of
convergence, and the input transform is nonzero there, then their transform quotient equals the
polar decomposition of that trigonometric quotient. The proof first invokes the recurrence-based
transfer law; it does not identify the transform quotient by unfolding a definition.

The coefficient functions take complex values. Thus `delayCosineSum` and `delaySineSum` name the
cosine-weighted and sine-weighted sums; they are not claims that those sums are respectively the
real and imaginary parts of a complex number.

## ii. Key results

- `Physlib.ZTransform.unitCirclePoint`: the point `exp (ω I)` for real `ω`.
- `Physlib.ZTransform.delaySymbol_unitCircle`: the cosine-sine expansion of a delay symbol.
- `Physlib.ZTransform.transferFunction_unitCircle`: the trigonometric transfer quotient.
- `Physlib.ZTransform.transferFunction_unitCircle_norm`: its magnitude decomposition.
- `Physlib.ZTransform.transferFunction_unitCircle_polar`: its bundled polar decomposition.
- `Physlib.ZTransform.transform_div_unitCircle_polar`: the recurrence-derived IIR frequency
  response.

## iii. Table of contents

- A. The unit-circle substitution
- B. Cosine and sine delay sums
- C. Transfer magnitude, phase, and the recurrence-derived response

## iv. References and scope

The result formalizes Theorem 13 (IIR Frequency Response, p. 496) of U. Siddique,
M. Y. Mahmoud, and S. Tahar, "On the Formalization of Z-Transform in HOL", ITP 2014,
LNCS 8558. The source ranges `0..N` and `1..M` are represented by `Finset.Icc 0 N` and
`Finset.Icc 1 M`. Omitting lag zero from the feedback range represents the source's stipulated
zero leading feedback coefficient.

The source's formal script states the magnitude through complex norms, which remains meaningful
for complex coefficients. The angular frequency is real here, so `unitCirclePoint` genuinely
lies on the unit circle. The IIR region and nonzero-input-transform hypotheses are explicit, and
the final statement is conditional on a supplied causal recurrence solution.

This is neutral mathematics. It asserts no stability, frequency-band classification, physical
realization, dispersion, propagation, or existence of a recurrence solution.

-/

@[expose] public section

namespace Physlib.ZTransform

noncomputable section

variable {s t : Finset ℕ} {α β c : ℕ → ℂ} {x y : ℤ → ℂ} {ω : ℝ}

/-!

## A. The unit-circle substitution

-/

/-- The unit-circle point at real angular frequency `ω`, written as `exp (ω I)`. -/
def unitCirclePoint (ω : ℝ) : ℂ :=
  Complex.exp ((ω : ℂ) * Complex.I)

/-- A unit-circle point has norm one. -/
@[simp]
lemma norm_unitCirclePoint (ω : ℝ) : ‖unitCirclePoint ω‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I ω

/-- A unit-circle point is nonzero. -/
@[simp]
lemma unitCirclePoint_ne_zero (ω : ℝ) : unitCirclePoint ω ≠ 0 :=
  Complex.exp_ne_zero

/-- The reciprocal unit-circle point is the exponential with negated angle. -/
lemma unitCirclePoint_inv (ω : ℝ) :
    (unitCirclePoint ω)⁻¹ = Complex.exp (-((ω : ℂ) * Complex.I)) := by
  exact (Complex.exp_neg ((ω : ℂ) * Complex.I)).symm

/-- A power of the reciprocal unit-circle point has the expected cosine-sine form. -/
lemma unitCirclePoint_inv_pow (ω : ℝ) (k : ℕ) :
    (unitCirclePoint ω)⁻¹ ^ k =
      (Real.cos ((k : ℝ) * ω) : ℂ) -
        (Real.sin ((k : ℝ) * ω) : ℂ) * Complex.I := by
  rw [unitCirclePoint_inv, ← Complex.exp_nat_mul]
  have harg :
      (k : ℂ) * -((ω : ℂ) * Complex.I) =
        ((-((k : ℝ) * ω) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg, Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
  push_cast
  ring

/-!

## B. Cosine and sine delay sums

-/

/-- The cosine-weighted part of a finite delay symbol at angular frequency `ω`. -/
def delayCosineSum (s : Finset ℕ) (c : ℕ → ℂ) (ω : ℝ) : ℂ :=
  ∑ k ∈ s, c k * (Real.cos ((k : ℝ) * ω) : ℂ)

/-- The sine-weighted part of a finite delay symbol at angular frequency `ω`. -/
def delaySineSum (s : Finset ℕ) (c : ℕ → ℂ) (ω : ℝ) : ℂ :=
  ∑ k ∈ s, c k * (Real.sin ((k : ℝ) * ω) : ℂ)

/-- The trigonometric numerator of the unit-circle transfer quotient. -/
def frequencyNumerator (t : Finset ℕ) (β : ℕ → ℂ) (ω : ℝ) : ℂ :=
  delayCosineSum t β ω - Complex.I * delaySineSum t β ω

/-- The trigonometric denominator of the unit-circle transfer quotient. -/
def frequencyDenominator (s : Finset ℕ) (α : ℕ → ℂ) (ω : ℝ) : ℂ :=
  (1 - delayCosineSum s α ω) + Complex.I * delaySineSum s α ω

/-- A delay symbol at a reciprocal unit-circle point is its cosine sum minus `I` times its sine
sum. -/
lemma delaySymbol_unitCircle (s : Finset ℕ) (c : ℕ → ℂ) (ω : ℝ) :
    delaySymbol s c (unitCirclePoint ω)⁻¹ =
      delayCosineSum s c ω - Complex.I * delaySineSum s c ω := by
  rw [delaySymbol, delayCosineSum, delaySineSum]
  simp_rw [unitCirclePoint_inv_pow]
  rw [Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- The recurrence denominator at a unit-circle point is its trigonometric denominator. -/
lemma one_sub_delaySymbol_unitCircle (s : Finset ℕ) (α : ℕ → ℂ) (ω : ℝ) :
    1 - delaySymbol s α (unitCirclePoint ω)⁻¹ = frequencyDenominator s α ω := by
  rw [delaySymbol_unitCircle]
  simp only [frequencyDenominator]
  ring

/-!

## C. Transfer magnitude, phase, and the recurrence-derived response

-/

/-- On the unit circle, the transfer function is the quotient of its trigonometric numerator and
denominator. -/
lemma transferFunction_unitCircle (s t : Finset ℕ) (α β : ℕ → ℂ) (ω : ℝ) :
    transferFunction s t α β (unitCirclePoint ω) =
      frequencyNumerator t β ω / frequencyDenominator s α ω := by
  rw [transferFunction, delaySymbol_unitCircle, one_sub_delaySymbol_unitCircle]
  rfl

/-- The magnitude of the unit-circle transfer function is the quotient of the numerator and
denominator magnitudes. -/
lemma transferFunction_unitCircle_norm (s t : Finset ℕ) (α β : ℕ → ℂ) (ω : ℝ) :
    ‖transferFunction s t α β (unitCirclePoint ω)‖ =
      ‖frequencyNumerator t β ω‖ / ‖frequencyDenominator s α ω‖ := by
  rw [transferFunction_unitCircle, norm_div]

/-- The unit-circle transfer function is the polar decomposition of its explicit trigonometric
quotient. The denominator hypothesis records the non-pole domain used by the IIR statement. -/
lemma transferFunction_unitCircle_polar (s t : Finset ℕ) (α β : ℕ → ℂ) (ω : ℝ)
    (hden : frequencyDenominator s α ω ≠ 0) :
    transferFunction s t α β (unitCirclePoint ω) =
      ((‖frequencyNumerator t β ω‖ / ‖frequencyDenominator s α ω‖ : ℝ) : ℂ) *
        Complex.exp
          (Complex.arg (frequencyNumerator t β ω / frequencyDenominator s α ω) *
            Complex.I) := by
  rw [transferFunction_unitCircle]
  have hpolar :=
    Complex.norm_mul_exp_arg_mul_I
      (frequencyNumerator t β ω / frequencyDenominator s α ω)
  rw [norm_div] at hpolar
  apply mul_right_cancel₀ hden
  rw [div_mul_cancel₀ _ hden, hpolar, div_mul_cancel₀ _ hden]

/-- Membership in the IIR region makes the trigonometric denominator nonzero. -/
lemma frequencyDenominator_ne_zero_of_mem_iirROC
    (hz : unitCirclePoint ω ∈ iirROC s α x y) : frequencyDenominator s α ω ≠ 0 := by
  rw [← one_sub_delaySymbol_unitCircle]
  exact hz.2

/-- The IIR frequency response: for the source lag ranges, the transform quotient is the polar
decomposition of the trigonometric coefficient quotient. The equality is derived from the
recurrence transfer law on the IIR region, not from a definition of the transform quotient. -/
lemma transform_div_unitCircle_polar {M N : ℕ}
    (hx : IsCausal x) (hy : IsCausal y)
    (hz : unitCirclePoint ω ∈ iirROC (Finset.Icc 1 M) α x y)
    (hInput : transform x (unitCirclePoint ω) ≠ 0)
    (hModel : IsRecurrenceSolution (Finset.Icc 1 M) (Finset.Icc 0 N) α β x y) :
    transform y (unitCirclePoint ω) / transform x (unitCirclePoint ω) =
      ((‖frequencyNumerator (Finset.Icc 0 N) β ω‖ /
          ‖frequencyDenominator (Finset.Icc 1 M) α ω‖ : ℝ) : ℂ) *
        Complex.exp
          (Complex.arg
              (frequencyNumerator (Finset.Icc 0 N) β ω /
                frequencyDenominator (Finset.Icc 1 M) α ω) * Complex.I) := by
  have hTransfer :
      transform y (unitCirclePoint ω) =
        transferFunction (Finset.Icc 1 M) (Finset.Icc 0 N) α β (unitCirclePoint ω) *
          transform x (unitCirclePoint ω) :=
    transform_eq_transferFunction_mul_of_mem_iirROC hx hy hz hModel
  have hden : frequencyDenominator (Finset.Icc 1 M) α ω ≠ 0 :=
    frequencyDenominator_ne_zero_of_mem_iirROC hz
  calc
    transform y (unitCirclePoint ω) / transform x (unitCirclePoint ω) =
        transferFunction (Finset.Icc 1 M) (Finset.Icc 0 N) α β
          (unitCirclePoint ω) := by
      rw [hTransfer, mul_div_assoc, div_self hInput, mul_one]
    _ = _ := transferFunction_unitCircle_polar _ _ _ _ _ hden

end

end Physlib.ZTransform
