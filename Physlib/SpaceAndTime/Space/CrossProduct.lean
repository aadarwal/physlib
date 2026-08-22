/-
Copyright (c) 2025 Zhi Kai Pong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhi Kai Pong, Joseph Tooby-Smith
-/
module

public import Mathlib.LinearAlgebra.CrossProduct
public import Physlib.SpaceAndTime.Time.Derivatives
/-!

# The cross product on Euclidean vectors in three dimensions

## i. Overview

In this module we define the cross product on `EuclideanSpace ℝ (Fin 3)`,
and prove various properties about it related to time derivatives and inner products.

## ii. Key results

- `⨯ₑ₃` : The cross product on `EuclideanSpace ℝ (Fin 3)`.
- `cross_add`, `add_cross`, `cross_smul`, `smul_cross` : Bilinearity of the cross product.
- `cross_cross_eq_smul_sub_smul` : The vector triple-product identity.
- `inner_cross_cross` : The inner product of two cross products as a Gram determinant.
- `time_deriv_cross_commute` : Time derivatives move out of cross products.
- `inner_cross_self` : Inner product of a vector with the cross product of another vector
  and itself is zero.
- `inner_self_cross` : Inner product of a vector with the cross product of itself
  and another vector is zero.

## iii. Table of contents

- A. The notation for the cross product
- B. Algebra of the cross product
- C. Time derivatives move out of cross products
- D. Inner product of vectors with cross products involving themselves

## iv. References

-/

@[expose] public section

namespace Space
open Time Matrix

/-!

## A. The notation for the cross product

-/

set_option quotPrecheck false in
/-- Cross product in `EuclideanSpace ℝ (Fin 3)`. Uses `⨯` which is typed using `\X` or
`\vectorproduct` or `\crossproduct`. -/
infixl:70 " ⨯ₑ₃ " => fun a b => (WithLp.equiv 2 (Fin 3 → ℝ)).symm
    (WithLp.equiv 2 (Fin 3 → ℝ) a ⨯₃ WithLp.equiv 2 (Fin 3 → ℝ) b)

/-!

## B. Algebra of the cross product

-/

/-- The cross product is additive in its second argument. -/
lemma cross_add (u v w : EuclideanSpace ℝ (Fin 3)) :
    u ⨯ₑ₃ (v + w) = u ⨯ₑ₃ v + u ⨯ₑ₃ w := by
  ext i
  fin_cases i <;> simp [crossProduct] <;> ring

/-- The cross product is additive in its first argument. -/
lemma add_cross (u v w : EuclideanSpace ℝ (Fin 3)) :
    (u + v) ⨯ₑ₃ w = u ⨯ₑ₃ w + v ⨯ₑ₃ w := by
  ext i
  fin_cases i <;> simp [crossProduct]

/-- The cross product commutes with scalar multiplication in its second argument. -/
lemma cross_smul (u v : EuclideanSpace ℝ (Fin 3)) (a : ℝ) :
    u ⨯ₑ₃ (a • v) = a • (u ⨯ₑ₃ v) := by
  ext i
  fin_cases i <;> simp [crossProduct]

/-- The cross product commutes with scalar multiplication in its first argument. -/
lemma smul_cross (a : ℝ) (u v : EuclideanSpace ℝ (Fin 3)) :
    (a • u) ⨯ₑ₃ v = a • (u ⨯ₑ₃ v) := by
  ext i
  fin_cases i <;> simp [crossProduct]

/-- The vector triple product `(u × v) × w` in Euclidean coordinates. -/
lemma cross_cross_eq_smul_sub_smul (u v w : EuclideanSpace ℝ (Fin 3)) :
    (u ⨯ₑ₃ v) ⨯ₑ₃ w = inner ℝ u w • v - inner ℝ v w • u := by
  ext i
  fin_cases i <;>
    simp [crossProduct, PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply] <;>
    ring

/-- The vector triple product `u × (v × w)` in Euclidean coordinates. -/
lemma cross_cross_eq_smul_sub_smul' (u v w : EuclideanSpace ℝ (Fin 3)) :
    u ⨯ₑ₃ (v ⨯ₑ₃ w) = inner ℝ u w • v - inner ℝ v u • w := by
  ext i
  fin_cases i <;>
    simp [crossProduct, PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply] <;>
    ring

/-- The inner product of two cross products is the determinant of their pairwise
inner products. -/
lemma inner_cross_cross (u v w x : EuclideanSpace ℝ (Fin 3)) :
    inner ℝ (u ⨯ₑ₃ v) (w ⨯ₑ₃ x) =
      inner ℝ u w * inner ℝ v x - inner ℝ u x * inner ℝ v w := by
  cases u using WithLp.rec with | _ u =>
  cases v using WithLp.rec with | _ v =>
  cases w using WithLp.rec with | _ w =>
  cases x using WithLp.rec with | _ x =>
  simpa [PiLp.inner_apply, RCLike.inner_apply, dotProduct, mul_comm] using
    cross_dot_cross u v w x

/-!

## C. Time derivatives move out of cross products

-/

/-- Cross product and fderiv commute. -/
lemma fderiv_cross_commute {t : Time} {s : EuclideanSpace ℝ (Fin 3)}
    {f : Time → EuclideanSpace ℝ (Fin 3)} (hf : Differentiable ℝ f) :
    s ⨯ₑ₃ (fderiv ℝ (fun t' => f t') t) 1
    = fderiv ℝ (fun t' => s ⨯ₑ₃ (f t')) t 1 := by
  have h (i j : Fin 3) : s i * (fderiv ℝ (fun u => f u) t) 1 j -
      s j * (fderiv ℝ (fun u => f u) t) 1 i
      = (fderiv ℝ (fun t => s i * f t j - s j * f t i) t) 1:= by
    rw [fderiv_fun_sub, fderiv_const_mul, fderiv_const_mul]
    · simp only [FunLike.coe_sub, FunLike.coe_smul, Pi.sub_apply,
        Pi.smul_apply, smul_eq_mul]
      rw [Time.fderiv_euclid, Time.fderiv_euclid]
      · intro i
        repeat fun_prop
      · fun_prop
    · fun_prop
    · fun_prop
    · fun_prop
    · fun_prop
  rw [crossProduct]
  ext i
  fin_cases i <;>
  · simp [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, WithLp.equiv_apply,
      LinearMap.mk₂_apply, Fin.reduceFinMk, WithLp.equiv_symm_apply,
      PiLp.toLp_apply, cons_val]
    rw [h]
    simp only [Fin.isValue]
    rw [← Time.fderiv_euclid]
    simp [Fin.isValue, cons_val_zero]
    apply Time.differentiable_euclid
    intro i
    fin_cases i
    · simp [Fin.zero_eta, Fin.isValue]
      fun_prop
    · simp [Fin.isValue]
      fun_prop
    · simp [Fin.isValue]
      fun_prop

/-- Cross product and time derivative commute. -/
lemma time_deriv_cross_commute {s : EuclideanSpace ℝ (Fin 3)} {f : Time → EuclideanSpace ℝ (Fin 3)}
    (hf : Differentiable ℝ f) :
    s ⨯ₑ₃ (∂ₜ (fun t => f t) t) = ∂ₜ (fun t => s ⨯ₑ₃ (f t)) t := by
  repeat rw [Time.deriv]
  rw [fderiv_cross_commute]
  fun_prop

/-!

## D. Inner product of vectors with cross products involving themselves

-/

lemma inner_cross_self (v w : EuclideanSpace ℝ (Fin 3)) :
    inner ℝ v (w ⨯ₑ₃ v) = 0 := by
  cases v using WithLp.rec with | _ v =>
  cases w using WithLp.rec with | _ w =>
  simp only [WithLp.equiv_apply, WithLp.equiv_symm_apply]
  change (crossProduct w) v ⬝ᵥ v = _
  rw [dotProduct_comm, dot_cross_self]

lemma inner_self_cross (v w : EuclideanSpace ℝ (Fin 3)) :
    inner ℝ v (v ⨯ₑ₃ w) = 0 := by
  cases v using WithLp.rec with | _ v =>
  cases w using WithLp.rec with | _ w =>
  simp only [WithLp.equiv_apply, WithLp.equiv_symm_apply, PiLp.inner_apply]
  change (crossProduct v) w ⬝ᵥ v = _
  rw [dotProduct_comm, dot_self_cross]

end Space
