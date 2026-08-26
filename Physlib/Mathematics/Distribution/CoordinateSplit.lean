/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Mathematics.Distribution.Basic

/-!
# Coordinate splitting

## i. Overview

This file splits one coordinate from a finite-dimensional Euclidean space and records the
measure-preserving coordinate equivalence used by coordinate-hyperplane distributions.

## ii. Key results

- `Distribution.coordinateSplit`: the measurable selected-coordinate splitting.
- `Distribution.coordinateSplit_measurePreserving`: preservation of Lebesgue volume.

## iii. Table of contents

- A. Coordinate splitting

## iv. References

This is neutral finite-dimensional measure theory.
-/

@[expose] public section

open MeasureTheory SchwartzMap
open scoped SchwartzMap

namespace Physlib
namespace Distribution

noncomputable section

/-!
## A. Coordinate splitting
-/

/-- The measurable coordinate split selecting one Euclidean coordinate and retaining the
remaining coordinates with their Euclidean `L2` norm. -/
def coordinateSplit (d : ℕ) (i : Fin d.succ) :
    EuclideanSpace ℝ (Fin d.succ) ≃ᵐ ℝ × EuclideanSpace ℝ (Fin d) :=
  (MeasurableEquiv.toLp 2 (Fin d.succ → ℝ)).symm |>.trans <|
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin d.succ => ℝ) i).trans <|
      MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
        (MeasurableEquiv.toLp 2 (Fin d → ℝ))

@[simp]
lemma coordinateSplit_apply_fst (d : ℕ) (i : Fin d.succ)
    (x : EuclideanSpace ℝ (Fin d.succ)) :
    (coordinateSplit d i x).1 = x i := rfl

@[simp]
lemma coordinateSplit_apply_snd (d : ℕ) (i : Fin d.succ)
    (x : EuclideanSpace ℝ (Fin d.succ)) (j : Fin d) :
    (coordinateSplit d i x).2 j = x (i.succAbove j) := rfl

@[simp]
lemma coordinateSplit_symm_apply_self (d : ℕ) (i : Fin d.succ)
    (r : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    (coordinateSplit d i).symm (r, x) i = r := by
  simpa using
    (coordinateSplit_apply_fst d i ((coordinateSplit d i).symm (r, x))).symm

@[simp]
lemma coordinateSplit_symm_apply_succAbove (d : ℕ) (i : Fin d.succ)
    (r : ℝ) (x : EuclideanSpace ℝ (Fin d)) (j : Fin d) :
    (coordinateSplit d i).symm (r, x) (i.succAbove j) = x j := by
  simpa using
    (coordinateSplit_apply_snd d i ((coordinateSplit d i).symm (r, x)) j).symm

/-- Splitting a Euclidean coordinate preserves Lebesgue volume. -/
lemma coordinateSplit_measurePreserving (d : ℕ) (i : Fin d.succ) :
    MeasurePreserving (coordinateSplit d i) := by
  exact (PiLp.volume_preserving_ofLp (Fin d.succ)).trans <|
    (volume_preserving_piFinSuccAbove (fun _ : Fin d.succ => ℝ) i).trans <|
      MeasurePreserving.prod (MeasurePreserving.id volume)
        (PiLp.volume_preserving_toLp (Fin d))

end
end Distribution
end Physlib
