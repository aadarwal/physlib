/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Mathematics.ZTransform.DifferenceEquation

/-!
# Existence of the causal solution of a difference equation

## i. Overview

A strictly causal linear constant-coefficient difference equation has a causal solution for every
causal input, and by the uniqueness result of
`Physlib.Mathematics.ZTransform.DifferenceEquation` it has exactly one. This file constructs it.

The construction is direct recursion on the index. At index `n` the value is the driving term at
`n` plus the feedback combination of values already constructed; the guard `0 < k ∧ k ≤ n` on
each lag `k` is what makes the recursion decrease, and the lag set is required to exclude zero so
that no term is discarded by that guard which the equation actually needs. Values at negative
indices are zero by construction, which supplies the zero initial conditions.

The consequence is that the transfer-function statements of the previous file stop being
conditional. Previously every one of them began "given a causal solution"; now a causal solution
exists and is unique, so the transfer relation is a statement about the difference equation
itself rather than about a solution someone supplies.

## ii. Key results

- `Physlib.ZTransform.solveNat`: the recursion producing the nonnegative-index samples.
- `Physlib.ZTransform.recurrenceSolution`: its zero extension, the causal solution.
- `Physlib.ZTransform.isRecurrenceSolution_recurrenceSolution`: the construction solves the
  difference equation.
- `Physlib.ZTransform.existsUnique_causal_isRecurrenceSolution`: existence and uniqueness of the
  causal solution.
- `Physlib.ZTransform.transform_recurrenceSolution`: the transfer relation, stated for the
  constructed solution rather than for a hypothetical one.

## iii. Table of contents

- A. The recursive construction
- B. The construction solves the difference equation
- C. Existence and uniqueness
- D. The transfer relation without a solution hypothesis

## iv. References

`goal.md` section H.4 S5 requires "finite convolution and linear recurrences with initial
conditions". The initial conditions here are the zero ones supplied by causality, matching the
unilateral transform. Inhomogeneous initial conditions are not treated; they would need the
equation restated with a separate initial-state argument, and no theorem here asserts anything
about them.

The Concordia HVG corpus contains no existence theorem for solutions of a difference equation in
any fetched source; U. Siddique, M. Y. Mahmoud, and S. Tahar, "On the Formalization of Z-Transform
in HOL", ITP 2014, LNCS 8558, Definition 10 and Theorem 11 (p. 492) take a solution as given, as
does the journal version. So this file is not a parity claim.

The strict-causality hypothesis `0 ∉ s` is the same structural constraint the sources write as
"the head of the feedback coefficient list is zero".

This file is neutral mathematics and imports no physics.

-/

@[expose] public section

namespace Physlib.ZTransform

noncomputable section

variable {s t : Finset ℕ} {α β : ℕ → ℂ} {x : ℤ → ℂ}

/-!

## A. The recursive construction

-/

/-- The nonnegative-index samples of the causal solution of a strictly causal difference equation
with feedback lags `s`, feedback coefficients `α`, and driving sequence `d`. The guard on each lag
is what makes the recursion decrease. -/
def solveNat (s : Finset ℕ) (α : ℕ → ℂ) (d : ℤ → ℂ) : ℕ → ℂ
  | n => (∑ k ∈ s, α k * (if _hk : 0 < k ∧ k ≤ n then solveNat s α d (n - k) else 0)) + d n
  decreasing_by omega

/-- The causal solution of a strictly causal difference equation: the recursive construction
extended by zero to negative indices. -/
def recurrenceSolution (s t : Finset ℕ) (α β : ℕ → ℂ) (x : ℤ → ℂ) : ℤ → ℂ :=
  zeroExtend (solveNat s α (delayCombination t β x))

/-- The constructed solution is causal. -/
lemma recurrenceSolution_isCausal (s t : Finset ℕ) (α β : ℕ → ℂ) (x : ℤ → ℂ) :
    IsCausal (recurrenceSolution s t α β x) :=
  zeroExtend_isCausal _

/-- A finite delay combination evaluated at an index. -/
lemma delayCombination_apply (s : Finset ℕ) (c : ℕ → ℂ) (f : ℤ → ℂ) (n : ℤ) :
    delayCombination s c f n = ∑ k ∈ s, c k * f (n - k) := rfl

/-- A zero extension at a nonnegative index. -/
lemma zeroExtend_apply_of_nonneg (a : ℕ → ℂ) {n : ℤ} (hn : 0 ≤ n) :
    zeroExtend a n = a n.toNat := by
  simp [zeroExtend, hn]

/-!

## B. The construction solves the difference equation

-/

/-- The constructed solution satisfies the difference equation, given that the feedback is
strictly causal and the input is causal. -/
theorem isRecurrenceSolution_recurrenceSolution (h0 : 0 ∉ s) (hx : IsCausal x) :
    IsRecurrenceSolution s t α β x (recurrenceSolution s t α β x) := by
  funext n
  rw [Pi.add_apply]
  rcases lt_or_ge n 0 with hn | hn
  · have hlhs : recurrenceSolution s t α β x n = 0 :=
      recurrenceSolution_isCausal s t α β x n hn
    have hfb : delayCombination s α (recurrenceSolution s t α β x) n = 0 :=
      Finset.sum_eq_zero fun k _ => by
        rw [recurrenceSolution_isCausal s t α β x _ (by omega), mul_zero]
    have hff : delayCombination t β x n = 0 :=
      Finset.sum_eq_zero fun k _ => by rw [hx _ (by omega), mul_zero]
    rw [hlhs, hfb, hff, add_zero]
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    have hlhs : recurrenceSolution s t α β x (m : ℤ)
        = solveNat s α (delayCombination t β x) m := by
      rw [recurrenceSolution, zeroExtend_natCast]
    rw [hlhs, solveNat, delayCombination_apply s α (recurrenceSolution s t α β x) (m : ℤ)]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkpos : 0 < k := Nat.pos_of_ne_zero fun hzero => h0 (hzero ▸ hk)
    rcases le_or_gt k m with hkm | hkm
    · have hnn : (0 : ℤ) ≤ (m : ℤ) - (k : ℤ) := by omega
      have htn : ((m : ℤ) - (k : ℤ)).toNat = m - k := by omega
      rw [dif_pos ⟨hkpos, hkm⟩, recurrenceSolution, zeroExtend_apply_of_nonneg _ hnn, htn]
    · have hneg : (m : ℤ) - (k : ℤ) < 0 := by omega
      rw [dif_neg (by omega), recurrenceSolution_isCausal s t α β x _ hneg, mul_zero]

/-!

## C. Existence and uniqueness

-/

/-- A strictly causal difference equation driven by a causal input has exactly one causal
solution. -/
theorem existsUnique_causal_isRecurrenceSolution (h0 : 0 ∉ s) (hx : IsCausal x) :
    ∃! y : ℤ → ℂ, IsCausal y ∧ IsRecurrenceSolution s t α β x y := by
  refine ⟨recurrenceSolution s t α β x,
    ⟨recurrenceSolution_isCausal s t α β x, isRecurrenceSolution_recurrenceSolution h0 hx⟩,
    fun y hy => ?_⟩
  exact eq_of_isRecurrenceSolution h0 hy.1 (recurrenceSolution_isCausal s t α β x) hy.2
    (isRecurrenceSolution_recurrenceSolution h0 hx)

/-- Every causal solution of a strictly causal difference equation is the constructed one. -/
theorem eq_recurrenceSolution {y : ℤ → ℂ} (h0 : 0 ∉ s) (hx : IsCausal x) (hy : IsCausal y)
    (hr : IsRecurrenceSolution s t α β x y) : y = recurrenceSolution s t α β x :=
  eq_of_isRecurrenceSolution h0 hy (recurrenceSolution_isCausal s t α β x) hr
    (isRecurrenceSolution_recurrenceSolution h0 hx)

/-!

## D. The transfer relation without a solution hypothesis

-/

/-- The cleared transform identity for the constructed solution. No solution needs to be
supplied. -/
theorem transform_recurrenceSolution_cleared {z : ℂ} (h0 : 0 ∉ s) (hx : IsCausal x)
    (hxs : Summable (seriesTerm x z))
    (hys : Summable (seriesTerm (recurrenceSolution s t α β x) z)) :
    (1 - delaySymbol s α z⁻¹) * transform (recurrenceSolution s t α β x) z
      = delaySymbol t β z⁻¹ * transform x z :=
  transform_isRecurrenceSolution hx (recurrenceSolution_isCausal s t α β x) hxs hys
    (isRecurrenceSolution_recurrenceSolution h0 hx)

/-- The transfer relation for the constructed solution, where the denominator does not vanish. -/
theorem transform_recurrenceSolution {z : ℂ} (h0 : 0 ∉ s) (hx : IsCausal x)
    (hxs : Summable (seriesTerm x z))
    (hys : Summable (seriesTerm (recurrenceSolution s t α β x) z))
    (hden : 1 - delaySymbol s α z⁻¹ ≠ 0) :
    transform (recurrenceSolution s t α β x) z
      = transferFunction s t α β z * transform x z :=
  transform_eq_transferFunction_mul hx (recurrenceSolution_isCausal s t α β x) hxs hys hden
    (isRecurrenceSolution_recurrenceSolution h0 hx)

end

end Physlib.ZTransform
