/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.TwoPortRedhefferStar

/-!
# Reflection-free series cascade as a Redheffer specialization

## i. Overview

When the first device has no right reflection and the second has no left reflection, the internal
feedback block is the identity. The Redheffer product then reduces to ordinary directional
transmission multiplication while retaining the two devices' external reflection blocks.

Scope:

Only the two facing reflection blocks are assumed zero. The result does not infer impedance
matching, reciprocity, passivity, losslessness, causality, or absence of the two external
reflections. Matrix multiplication is recovered for the directional transmission blocks, not for
the complete reflective scattering matrices.

## ii. Key results

- `TwoPortScatteringTransform.hasBijectiveRedhefferFeedback_of_facingReflections_eq_zero`.
- `TwoPortScatteringTransform.reflectionFreeSeriesCascade`.
- The four named cascade-block lemmas, including the two ordered transmission products.

## iii. Table of contents

- A. Identity feedback pivot
- B. Ordinary directional cascade

## iv. References

This specialization is Physlib-original; no external source is used here.

-/

@[expose] public section

namespace Optics

noncomputable section

universe u v w

namespace TwoPortScatteringTransform

variable {ι : Type u} {κ : Type v} {μ : Type w}

/-!

## A. Identity feedback pivot

-/

/-- Zero facing reflections make the Redheffer feedback block bijective. -/
lemma hasBijectiveRedhefferFeedback_of_facingReflections_eq_zero
    [Fintype κ] [DecidableEq κ]
    (first : TwoPortScatteringTransform ι κ)
    (second : TwoPortScatteringTransform κ μ)
    (hFirst : first.rightReflection = 0)
    (hSecond : second.leftReflection = 0) :
    first.HasBijectiveRedhefferFeedback second := by
  unfold HasBijectiveRedhefferFeedback redhefferFeedbackBlock
  rw [hFirst, hSecond]
  simpa using Function.bijective_id

/-- Under zero facing reflections, every proof-gated feedback inverse is the identity matrix. -/
lemma redhefferFeedbackInverse_eq_one_of_facingReflections_eq_zero
    [Fintype κ] [DecidableEq κ]
    (first : TwoPortScatteringTransform ι κ)
    (second : TwoPortScatteringTransform κ μ)
    (hFeedback : first.HasBijectiveRedhefferFeedback second)
    (hFirst : first.rightReflection = 0)
    (hSecond : second.leftReflection = 0) :
    first.redhefferFeedbackInverse second hFeedback = 1 := by
  apply Matrix.toEuclideanLin.injective
  rw [Matrix.toLpLin_one]
  apply LinearMap.ext
  intro amplitude
  have hInverse :=
    first.redhefferFeedbackBlock_apply_inverse second hFeedback amplitude
  simpa [redhefferFeedbackBlock, hFirst, hSecond] using hInverse

/-!

## B. Ordinary directional cascade

-/

/-- The ordinary two-port cascade obtained from the Redheffer product when the two facing
reflection blocks vanish. -/
noncomputable def reflectionFreeSeriesCascade
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype μ] [DecidableEq μ]
    (first : TwoPortScatteringTransform ι κ)
    (second : TwoPortScatteringTransform κ μ)
    (hFirst : first.rightReflection = 0)
    (hSecond : second.leftReflection = 0) : TwoPortScatteringTransform ι μ :=
  first.redhefferStar second
    (first.hasBijectiveRedhefferFeedback_of_facingReflections_eq_zero
      second hFirst hSecond)

/-- A reflection-free interface leaves the first device's external left reflection unchanged. -/
lemma leftReflection_reflectionFreeSeriesCascade
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype μ] [DecidableEq μ]
    (first : TwoPortScatteringTransform ι κ)
    (second : TwoPortScatteringTransform κ μ)
    (hFirst : first.rightReflection = 0)
    (hSecond : second.leftReflection = 0) :
    (first.reflectionFreeSeriesCascade second hFirst hSecond).leftReflection =
      first.leftReflection := by
  unfold reflectionFreeSeriesCascade
  rw [first.redhefferStar_eq_blockFormula,
    first.leftReflection_redhefferBlockFormula, hSecond]
  simp

/-- Right-to-left transmission through a reflection-free interface is the ordered product of the
two directional transmission blocks. -/
lemma rightToLeftTransmission_reflectionFreeSeriesCascade
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype μ] [DecidableEq μ]
    (first : TwoPortScatteringTransform ι κ)
    (second : TwoPortScatteringTransform κ μ)
    (hFirst : first.rightReflection = 0)
    (hSecond : second.leftReflection = 0) :
    (first.reflectionFreeSeriesCascade second hFirst hSecond).rightToLeftTransmission =
      first.rightToLeftTransmission * second.rightToLeftTransmission := by
  unfold reflectionFreeSeriesCascade
  rw [first.redhefferStar_eq_blockFormula,
    first.rightToLeftTransmission_redhefferBlockFormula,
    first.redhefferFeedbackInverse_eq_one_of_facingReflections_eq_zero
      second _ hFirst hSecond]
  simp

/-- Left-to-right transmission through a reflection-free interface is the ordered product with
the later device on the left. -/
lemma leftToRightTransmission_reflectionFreeSeriesCascade
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype μ] [DecidableEq μ]
    (first : TwoPortScatteringTransform ι κ)
    (second : TwoPortScatteringTransform κ μ)
    (hFirst : first.rightReflection = 0)
    (hSecond : second.leftReflection = 0) :
    (first.reflectionFreeSeriesCascade second hFirst hSecond).leftToRightTransmission =
      second.leftToRightTransmission * first.leftToRightTransmission := by
  unfold reflectionFreeSeriesCascade
  rw [first.redhefferStar_eq_blockFormula,
    first.leftToRightTransmission_redhefferBlockFormula, hFirst]
  simp

/-- A reflection-free interface leaves the second device's external right reflection unchanged. -/
lemma rightReflection_reflectionFreeSeriesCascade
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype μ] [DecidableEq μ]
    (first : TwoPortScatteringTransform ι κ)
    (second : TwoPortScatteringTransform κ μ)
    (hFirst : first.rightReflection = 0)
    (hSecond : second.leftReflection = 0) :
    (first.reflectionFreeSeriesCascade second hFirst hSecond).rightReflection =
      second.rightReflection := by
  unfold reflectionFreeSeriesCascade
  rw [first.redhefferStar_eq_blockFormula,
    first.rightReflection_redhefferBlockFormula, hFirst]
  simp

end TwoPortScatteringTransform

end

end Optics
