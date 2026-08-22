/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.ClassicalMechanics.WaveEquation.Basic
public import Physlib.SpaceAndTime.Space.Derivatives.Curl

/-!

# Vector calculus of three-dimensional plane waves

## i. Overview

This module computes the divergence and curl of a differentiable three-dimensional plane wave.
It extends the dimension-independent derivative API in `WaveEquation.Basic` without making that
foundational module import the specifically three-dimensional curl operator.

For a profile `f₀`, propagation speed `c`, and unit direction `s`, both results express the spatial
operator through the profile derivative at the travelling coordinate
`⟪x, s.unit⟫_ℝ - c * t`. These identities are independent of any electromagnetic field role or
constitutive law.

## ii. Key results

- `planeWave_div`: divergence of a differentiable three-dimensional plane wave.
- `planeWave_curl`: curl of a differentiable three-dimensional plane wave.

## iii. Table of contents

- A. Divergence
- B. Curl

## iv. References

-/

@[expose] public section

namespace ClassicalMechanics

open Space Time InnerProductSpace Matrix

/-!

## A. Divergence

-/

/-- The divergence of a differentiable three-dimensional plane wave is the inner product of its
unit propagation vector with its profile derivative. -/
lemma planeWave_div {f₀ : ℝ → EuclideanSpace ℝ (Fin 3)} {c : ℝ}
    {s : Direction 3} (h : Differentiable ℝ f₀) (t : Time) (x : Space) :
    (∇ ⬝ planeWave f₀ c s t) x =
      ⟪Space.basis.repr s.unit, fderiv ℝ f₀ (⟪x, s.unit⟫_ℝ - c * t) 1⟫_ℝ := by
  unfold Space.div
  simp_rw [planeWave_apply_space_deriv h]
  simp [planeWave_eq, PiLp.inner_apply, RCLike.inner_apply, mul_comm]

/-!

## B. Curl

-/

/-- The curl of a differentiable three-dimensional plane wave is the cross product of its unit
propagation vector with its profile derivative. -/
lemma planeWave_curl {f₀ : ℝ → EuclideanSpace ℝ (Fin 3)} {c : ℝ}
    {s : Direction 3} (h : Differentiable ℝ f₀) (t : Time) (x : Space) :
    (∇ ⨯ planeWave f₀ c s t) x =
      Space.basis.repr s.unit ⨯ₑ₃ fderiv ℝ f₀ (⟪x, s.unit⟫_ℝ - c * t) 1 := by
  unfold Space.curl
  ext i
  fin_cases i <;>
    simp only [Fin.zero_eta, Fin.isValue, Fin.reduceAdd] <;>
    rw [planeWave_apply_space_deriv h, planeWave_apply_space_deriv h] <;>
    simp [planeWave_eq, crossProduct]

end ClassicalMechanics
