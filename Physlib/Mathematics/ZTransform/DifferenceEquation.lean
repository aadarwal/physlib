/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Physlib.Mathematics.ZTransform.Convergence

/-!
# Linear difference equations and rational transfer functions

## i. Overview

A linear constant-coefficient difference equation is written here as an equality of sequences,
`y = delayCombination s α y + delayCombination t β x`, where `s` and `t` are finite sets of lags
and `α`, `β` are coefficient functions on lags. Nothing in that statement asserts that a solution
exists or that the equation determines one; those are separate questions, and only the second is
answered here.

The transform of a finite delay combination is the combination's symbol, a polynomial in `z⁻¹`,
times the transform of the delayed sequence. Applying that to both sides of the difference
equation gives the cleared identity
`(1 - delaySymbol s α z⁻¹) * transform y z = delaySymbol t β z⁻¹ * transform x z`,
which carries no division and therefore no nondegeneracy hypothesis. Dividing by the denominator
is a separate step with its own explicit hypothesis, and the transfer function is the resulting
ratio of two polynomials in `z⁻¹`.

The region on which the ratio form holds is the intersection of the two absolute regions of
convergence with the zeros of the denominator removed. Zeros of the denominator are candidate
poles of the transfer function; this file does not claim they are poles, because a numerator zero
at the same point can cancel one.

Causality of the feedback, `0 ∉ s`, is a nondegeneracy hypothesis kept separate from the
transform theory. It is not needed to transform the equation, and it suffices to prove that there
is at most one causal solution for a fixed input. Existence and necessity are not asserted.

Rationality here is rationality in `z⁻¹`, not in a physical frequency. The substitution
`z = exp w`, recorded at the end, is the only bridge offered towards a delay variable
`q = exp (-s * τ)`; it is an identity about evaluation and asserts nothing about a physical
model.

## ii. Key results

- `Physlib.ZTransform.delayCombination`, `Physlib.ZTransform.delaySymbol`: a finite delay
  combination and its polynomial symbol in the reciprocal variable.
- `Physlib.ZTransform.transform_delayCombination`: the symbol multiplies the transform.
- `Physlib.ZTransform.IsRecurrenceSolution`: a sequence satisfies a difference equation.
- `Physlib.ZTransform.transform_isRecurrenceSolution`: the cleared, division-free transform of a
  difference equation.
- `Physlib.ZTransform.eq_of_isRecurrenceSolution`: a strictly causal difference equation has at
  most one causal solution for a given input.
- `Physlib.ZTransform.transferFunction`: the ratio of the two symbols.
- `Physlib.ZTransform.transform_eq_transferFunction_mul`: the transfer relation where the
  denominator does not vanish.
- `Physlib.ZTransform.iirROC`: the region of convergence of the transfer relation.
- `Physlib.ZTransform.transferFunction_exp`: the frequency-response substitution `z = exp w`.

## iii. Table of contents

- A. Transforms of finite sums of sequences
- B. Finite delay combinations and their symbols
- C. Linear constant-coefficient difference equations
- D. Uniqueness of the causal solution
- E. The transfer function and its region of convergence
- F. The frequency-response substitution

## iv. References

The development follows U. Siddique, M. Y. Mahmoud, and S. Tahar, "On the Formalization of
Z-Transform in HOL", ITP 2014, LNCS 8558: Definition 10, Theorem 11, and Lemma 4 (difference
equation and its transform, p. 492), Definitions 11-13 (infinite-impulse-response model, causality
condition, and the model's region of convergence, pp. 494-495), and Theorems 12-13 (transfer
function and frequency response, pp. 495-496). The journal version is U. Siddique,
M. Y. Mahmoud, and S. Tahar, "Formal Analysis of Discrete-Time Systems using z-Transform",
Journal of Applied Logics 5(4), 2018, pp. 875-906, Definitions 15-18 and Theorems 13-14
(pp. 890-891). A textbook reference is A. V. Oppenheim and R. W. Schafer, *Discrete-Time Signal
Processing*, 3rd ed., Pearson, 2010, chapter 3.

Four differences from those sources are recorded. First, the sources index coefficients by
lists and impose the structural constraint that the head of the feedback list is zero; this file
indexes by an arbitrary finite set of lags and states the same constraint as `0 ∉ s`, which is
used only where it is needed. Second, the sources state the transfer function directly as a
quotient; here the cleared identity `transform_isRecurrenceSolution` is proved first, without
division, and the quotient is a corollary with an explicit nonvanishing hypothesis. Third, the
uniqueness of the causal solution, `eq_of_isRecurrenceSolution`, has no counterpart in the
sources. Fourth, the sources use their ordered-convergence region, whereas `iirROC` uses the
stronger absolute regions of both input and output.

Two things are deliberately not claimed. No existence theorem for a causal solution is proved
here, so every transfer-function statement is conditional on being given a solution; the
companion regression file exhibits a solved case, so the theory is not vacuous. And a zero of the
denominator is only a candidate pole: no theorem here asserts that the transfer function has a
pole there, since a numerator zero at the same point can cancel it.

This file is neutral mathematics and imports no physics.

-/

@[expose] public section

namespace Physlib.ZTransform

noncomputable section

variable {s t : Finset ℕ} {α β c : ℕ → ℂ} {x y f : ℤ → ℂ} {z : ℂ}

/-!

## A. Transforms of finite sums of sequences

-/

/-- The transform series of the zero sequence vanishes identically. -/
@[simp]
lemma seriesTerm_zero_fun (z : ℂ) : seriesTerm (0 : ℤ → ℂ) z = 0 := by
  funext n
  simp [seriesTerm]

/-- A finite sum of sequences whose transform series all converge absolutely has an absolutely
convergent transform series. -/
lemma summable_seriesTerm_finsetSum {ι : Type*} (u : Finset ι) (g : ι → ℤ → ℂ) (z : ℂ)
    (h : ∀ i ∈ u, Summable (seriesTerm (g i) z)) :
    Summable (seriesTerm (∑ i ∈ u, g i) z) := by
  classical
  induction u using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, seriesTerm_zero_fun]
    exact summable_zero
  | insert i u hi ih =>
    rw [Finset.sum_insert hi]
    exact summable_seriesTerm_add (h i (Finset.mem_insert_self i u))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-- The transform of a finite sum of sequences is the sum of their transforms. -/
lemma transform_finsetSum {ι : Type*} (u : Finset ι) (g : ι → ℤ → ℂ) (z : ℂ)
    (h : ∀ i ∈ u, Summable (seriesTerm (g i) z)) :
    transform (∑ i ∈ u, g i) z = ∑ i ∈ u, transform (g i) z := by
  classical
  induction u using Finset.induction_on with
  | empty => simp
  | insert i u hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      transform_add (h i (Finset.mem_insert_self i u))
        (summable_seriesTerm_finsetSum u g z fun j hj => h j (Finset.mem_insert_of_mem hj)),
      ih fun j hj => h j (Finset.mem_insert_of_mem hj)]

/-!

## B. Finite delay combinations and their symbols

-/

/-- The finite delay combination `n ↦ ∑ k ∈ s, c k * f (n - k)`. -/
def delayCombination (s : Finset ℕ) (c : ℕ → ℂ) (f : ℤ → ℂ) : ℤ → ℂ :=
  fun n => ∑ k ∈ s, c k * f (n - k)

/-- The symbol of a finite delay combination, a polynomial `∑ k ∈ s, c k * u ^ k` in the
reciprocal variable. -/
def delaySymbol (s : Finset ℕ) (c : ℕ → ℂ) (u : ℂ) : ℂ := ∑ k ∈ s, c k * u ^ k

/-- A delay combination written as a finite sum of scaled delays. -/
lemma delayCombination_eq_sum (s : Finset ℕ) (c : ℕ → ℂ) (f : ℤ → ℂ) :
    delayCombination s c f = ∑ k ∈ s, fun n : ℤ => c k * delay k f n := by
  funext n
  simp [delayCombination, delay, Finset.sum_apply]

/-- A delay combination of a causal sequence is causal. -/
lemma IsCausal.delayCombination (hf : IsCausal f) (s : Finset ℕ) (c : ℕ → ℂ) :
    IsCausal (ZTransform.delayCombination s c f) := by
  intro n hn
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [hf _ (by omega), mul_zero]

/-- A delay combination of a sequence with an absolutely convergent transform series again has an
absolutely convergent transform series. -/
lemma summable_seriesTerm_delayCombination (s : Finset ℕ) (c : ℕ → ℂ)
    (hs : Summable (seriesTerm f z)) : Summable (seriesTerm (delayCombination s c f) z) := by
  rw [delayCombination_eq_sum]
  exact summable_seriesTerm_finsetSum s _ z fun k _ =>
    summable_seriesTerm_const_mul (c k) (summable_seriesTerm_delay k hs)

/-- The transform of a finite delay combination of a causal sequence is its symbol at `z⁻¹` times
the transform of the sequence. -/
lemma transform_delayCombination (hf : IsCausal f) (hs : Summable (seriesTerm f z))
    (s : Finset ℕ) (c : ℕ → ℂ) :
    transform (delayCombination s c f) z = delaySymbol s c z⁻¹ * transform f z := by
  rw [delayCombination_eq_sum,
    transform_finsetSum s _ z fun k _ =>
      summable_seriesTerm_const_mul (c k) (summable_seriesTerm_delay k hs),
    delaySymbol, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [transform_const_mul, transform_delay hf k hs, mul_assoc]

/-!

## C. Linear constant-coefficient difference equations

-/

/-- The sequence `y` satisfies the linear constant-coefficient difference equation with feedback
lags `s` and coefficients `α`, feedforward lags `t` and coefficients `β`, and input `x`. -/
def IsRecurrenceSolution (s t : Finset ℕ) (α β : ℕ → ℂ) (x y : ℤ → ℂ) : Prop :=
  y = delayCombination s α y + delayCombination t β x

/-- The difference equation evaluated at one index. -/
lemma IsRecurrenceSolution.apply (hr : IsRecurrenceSolution s t α β x y) (n : ℤ) :
    y n = (∑ k ∈ s, α k * y (n - k)) + ∑ k ∈ t, β k * x (n - k) :=
  congrFun hr n

/-- The transform of a linear constant-coefficient difference equation, cleared of denominators.
This statement needs no nondegeneracy hypothesis. -/
lemma transform_isRecurrenceSolution (hx : IsCausal x) (hy : IsCausal y)
    (hxs : Summable (seriesTerm x z)) (hys : Summable (seriesTerm y z))
    (hr : IsRecurrenceSolution s t α β x y) :
    (1 - delaySymbol s α z⁻¹) * transform y z = delaySymbol t β z⁻¹ * transform x z := by
  have hcy : Summable (seriesTerm (delayCombination s α y) z) :=
    summable_seriesTerm_delayCombination s α hys
  have hcx : Summable (seriesTerm (delayCombination t β x) z) :=
    summable_seriesTerm_delayCombination t β hxs
  have key : transform y z =
      delaySymbol s α z⁻¹ * transform y z + delaySymbol t β z⁻¹ * transform x z := by
    calc transform y z
        = transform (delayCombination s α y) z + transform (delayCombination t β x) z := by
          conv_lhs => rw [hr]
          exact transform_add hcy hcx
      _ = delaySymbol s α z⁻¹ * transform y z + delaySymbol t β z⁻¹ * transform x z := by
          rw [transform_delayCombination hy hys, transform_delayCombination hx hxs]
  linear_combination key

/-!

## D. Uniqueness of the causal solution

-/

/-- A strictly causal difference equation, one whose feedback lags are all positive, has at most
one causal solution for a given input. The zero initial conditions are supplied by causality. -/
lemma eq_of_isRecurrenceSolution {y₁ y₂ : ℤ → ℂ} (h0 : 0 ∉ s) (hc₁ : IsCausal y₁)
    (hc₂ : IsCausal y₂) (hr₁ : IsRecurrenceSolution s t α β x y₁)
    (hr₂ : IsRecurrenceSolution s t α β x y₂) : y₁ = y₂ := by
  have key : ∀ N : ℕ, ∀ n : ℤ, n < (N : ℤ) → y₁ n = y₂ n := by
    intro N
    induction N with
    | zero =>
      intro n hn
      rw [hc₁ n (by exact_mod_cast hn), hc₂ n (by exact_mod_cast hn)]
    | succ N ih =>
      intro n hn
      rcases lt_or_ge n (N : ℤ) with hlt | hge
      · exact ih n hlt
      · have hnN : n = (N : ℤ) := by
          have : n < (N : ℤ) + 1 := by exact_mod_cast hn
          omega
        subst hnN
        rw [hr₁.apply, hr₂.apply]
        congr 1
        refine Finset.sum_congr rfl fun k hk => ?_
        have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr fun h => h0 (h ▸ hk)
        rw [ih _ (by omega)]
  funext n
  exact key (n.toNat + 1) n (by omega)

/-!

## E. The transfer function and its region of convergence

-/

/-- The transfer function of a difference equation: the ratio of the feedforward symbol to one
minus the feedback symbol, both polynomials in `z⁻¹`. -/
def transferFunction (s t : Finset ℕ) (α β : ℕ → ℂ) (z : ℂ) : ℂ :=
  delaySymbol t β z⁻¹ / (1 - delaySymbol s α z⁻¹)

/-- The region of convergence of the transfer relation: the common absolute region of convergence
of input and output, with the zeros of the denominator removed. -/
def iirROC (s : Finset ℕ) (α : ℕ → ℂ) (x y : ℤ → ℂ) : Set ℂ :=
  (ROC x ∩ ROC y) \ {z : ℂ | 1 - delaySymbol s α z⁻¹ = 0}

/-- Where the denominator does not vanish, the output transform is the transfer function times
the input transform. -/
lemma transform_eq_transferFunction_mul (hx : IsCausal x) (hy : IsCausal y)
    (hxs : Summable (seriesTerm x z)) (hys : Summable (seriesTerm y z))
    (hden : 1 - delaySymbol s α z⁻¹ ≠ 0) (hr : IsRecurrenceSolution s t α β x y) :
    transform y z = transferFunction s t α β z * transform x z := by
  have h := transform_isRecurrenceSolution hx hy hxs hys hr
  rw [transferFunction, div_mul_eq_mul_div, eq_div_iff hden]
  linear_combination h

/-- The same statement on the region of convergence of the transfer relation. -/
lemma transform_eq_transferFunction_mul_of_mem_iirROC (hx : IsCausal x) (hy : IsCausal y)
    (hz : z ∈ iirROC s α x y) (hr : IsRecurrenceSolution s t α β x y) :
    transform y z = transferFunction s t α β z * transform x z :=
  transform_eq_transferFunction_mul hx hy hz.1.1.2 hz.1.2.2 hz.2 hr

/-- Where the denominator does not vanish and the input transform is nonzero, the transfer
function is the ratio of the two transforms. -/
lemma transferFunction_eq_div (hx : IsCausal x) (hy : IsCausal y)
    (hxs : Summable (seriesTerm x z)) (hys : Summable (seriesTerm y z))
    (hden : 1 - delaySymbol s α z⁻¹ ≠ 0) (hnz : transform x z ≠ 0)
    (hr : IsRecurrenceSolution s t α β x y) :
    transform y z / transform x z = transferFunction s t α β z := by
  rw [transform_eq_transferFunction_mul hx hy hxs hys hden hr, mul_div_assoc,
    div_self hnz, mul_one]

/-!

## F. The frequency-response substitution

-/

/-- The reciprocal of an exponential is the exponential of the negation. This is the translation
between a Z variable `z = exp w` and a delay variable `q = exp (-w)`. -/
lemma inv_exp (w : ℂ) : (Complex.exp w)⁻¹ = Complex.exp (-w) := (Complex.exp_neg w).symm

/-- Evaluating the transform at `z = exp w` gives the ordinary power series in `exp (-w)`, so the
delay-variable substitution commutes with evaluation. -/
lemma transform_exp (f : ℤ → ℂ) (w : ℂ) :
    transform f (Complex.exp w) = ∑' n : ℕ, f n * Complex.exp (-w) ^ n := by
  rw [← transform_inv f (Complex.exp (-w)), inv_exp, neg_neg]

/-- The frequency response: the transfer function at `z = exp w` is the ratio of the two symbols
evaluated at the delay variable `exp (-w)`. -/
lemma transferFunction_exp (s t : Finset ℕ) (α β : ℕ → ℂ) (w : ℂ) :
    transferFunction s t α β (Complex.exp w) =
      delaySymbol t β (Complex.exp (-w)) / (1 - delaySymbol s α (Complex.exp (-w))) := by
  rw [transferFunction, inv_exp]

/-- The modulus and argument decomposition of the transfer function at a point. -/
lemma transferFunction_eq_norm_mul_exp_arg (s t : Finset ℕ) (α β : ℕ → ℂ) (z : ℂ) :
    transferFunction s t α β z =
      (‖transferFunction s t α β z‖ : ℂ) *
        Complex.exp (Complex.arg (transferFunction s t α β z) * Complex.I) :=
  (Complex.norm_mul_exp_arg_mul_I _).symm

end

end Physlib.ZTransform
