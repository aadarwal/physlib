/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Mode.Embedding

/-!
# Regression tests for optical mode-family embeddings

## i. Overview

This file uses two separated coordinates in a three-mode ambient family. The embedding maps
the two `Bool` modes to coordinates zero and two, with coordinate one external. A
nonzero amplitude supported only at the external coordinate distinguishes restriction from a
unitary relabeling and distinguishes the ambient range projector from the identity.

A nonsymmetric two-mode transform and an independent complex input amplitude check the row,
column, multiplication-order, conjugation, and zero-padding conventions of
`ModeTransform.zeroExtend`.

## ii. Key results

## iii. Table of contents

- A. A non-surjective, non-prefix embedding
- B. Exact restriction, extension, and projection
- C. Power and contraction laws
- D. Zero-extending a nonsymmetric transform

## iv. References

These are finite-dimensional algebraic regressions for power-normalized modal coordinates. The
strict loss shown by restriction means only that an external coordinate is discarded; it does
not model physical absorption or prove electromagnetic energy-flux conservation.

-/

@[expose] public section

namespace Optics

open scoped ComplexConjugate

noncomputable section

/-!

## A. A non-surjective, non-prefix embedding

-/

/-- Select ambient coordinates zero and two, leaving coordinate one external. -/
def modeEmbeddingRegressionEmbedding : Bool ↪ Fin 3 where
  toFun
    | false => 0
    | true => 2
  inj' := by
    intro first second
    cases first <;> cases second <;> simp

/-- Ambient coordinate one is not selected by the regression embedding. -/
lemma modeEmbeddingRegression_one_not_mem_range :
    (1 : Fin 3) ∉ Set.range modeEmbeddingRegressionEmbedding := by
  rintro ⟨mode, hMode⟩
  cases mode <;> norm_num [modeEmbeddingRegressionEmbedding] at hMode
  omega

/-- The regression embedding is not surjective. -/
lemma modeEmbeddingRegression_not_surjective :
    ¬Function.Surjective modeEmbeddingRegressionEmbedding :=
  fun hSurjective => modeEmbeddingRegression_one_not_mem_range (hSurjective 1)

/-- A selected amplitude with complex entries. -/
def modeEmbeddingRegressionAmplitude : ModeAmplitude Bool :=
  WithLp.toLp 2 fun
    | false => (1 : ℂ) + Complex.I
    | true => 2 - Complex.I

/-- A nonzero ambient amplitude supported only at the external coordinate. -/
def modeEmbeddingRegressionExternalBasis : ModeAmplitude (Fin 3) :=
  WithLp.toLp 2 ![(0 : ℂ), 2 + Complex.I, 0]

/-- Coordinate restriction for the regression embedding. -/
abbrev modeEmbeddingRegressionRestriction : ModeTransform (Fin 3) Bool :=
  ModeTransform.restriction modeEmbeddingRegressionEmbedding

/-- Zero extension for the regression embedding. -/
abbrev modeEmbeddingRegressionZeroExtension : ModeTransform Bool (Fin 3) :=
  ModeTransform.zeroExtension modeEmbeddingRegressionEmbedding

/-- The ambient selected-coordinate projector in the regression fixture. -/
abbrev modeEmbeddingRegressionProjector : ModeTransform (Fin 3) (Fin 3) :=
  ModeTransform.rangeProjector modeEmbeddingRegressionEmbedding

/-!

## B. Exact restriction, extension, and projection

-/

/-- Restriction evaluates ambient coordinate zero as the false selected mode. -/
lemma modeEmbeddingRegression_restriction_false (amplitude : ModeAmplitude (Fin 3)) :
    modeEmbeddingRegressionRestriction.toLinearMap amplitude false = amplitude 0 := by
  rw [ModeTransform.toLinearMap_restriction]
  rfl

/-- Restriction evaluates ambient coordinate two as the true selected mode. -/
lemma modeEmbeddingRegression_restriction_true (amplitude : ModeAmplitude (Fin 3)) :
    modeEmbeddingRegressionRestriction.toLinearMap amplitude true = amplitude 2 := by
  rw [ModeTransform.toLinearMap_restriction]
  rfl

/-- Zero extension writes the false selected mode at ambient coordinate zero. -/
lemma modeEmbeddingRegression_zeroExtension_zero (amplitude : ModeAmplitude Bool) :
    modeEmbeddingRegressionZeroExtension.toLinearMap amplitude 0 = amplitude false := by
  change (ModeTransform.zeroExtension modeEmbeddingRegressionEmbedding).toLinearMap amplitude 0 =
    amplitude false
  exact ModeTransform.zeroExtension_apply_image modeEmbeddingRegressionEmbedding amplitude false

/-- Zero extension writes zero at the external ambient coordinate. -/
lemma modeEmbeddingRegression_zeroExtension_one (amplitude : ModeAmplitude Bool) :
    modeEmbeddingRegressionZeroExtension.toLinearMap amplitude 1 = 0 :=
  ModeTransform.zeroExtension_apply_of_not_mem_range modeEmbeddingRegressionEmbedding amplitude 1
    modeEmbeddingRegression_one_not_mem_range

/-- Zero extension writes the true selected mode at ambient coordinate two. -/
lemma modeEmbeddingRegression_zeroExtension_two (amplitude : ModeAmplitude Bool) :
    modeEmbeddingRegressionZeroExtension.toLinearMap amplitude 2 = amplitude true := by
  change (ModeTransform.zeroExtension modeEmbeddingRegressionEmbedding).toLinearMap amplitude 2 =
    amplitude true
  exact ModeTransform.zeroExtension_apply_image modeEmbeddingRegressionEmbedding amplitude true

/-- Restriction maps an amplitude supported only on the external coordinate to zero. -/
lemma modeEmbeddingRegression_restriction_externalBasis :
    modeEmbeddingRegressionRestriction.toLinearMap
        modeEmbeddingRegressionExternalBasis = 0 := by
  rw [ModeTransform.toLinearMap_restriction]
  apply WithLp.ofLp_injective 2
  funext mode
  cases mode <;>
    norm_num [ModeAmplitude.restrictEmbedding, modeEmbeddingRegressionEmbedding,
      modeEmbeddingRegressionExternalBasis, Matrix.cons_val_two, Matrix.head_cons]

/-- The range projector maps an amplitude supported only on the external coordinate to zero. -/
lemma modeEmbeddingRegression_projector_externalBasis :
    modeEmbeddingRegressionProjector.toLinearMap
        modeEmbeddingRegressionExternalBasis = 0 := by
  simp only [modeEmbeddingRegressionProjector, ModeTransform.rangeProjector,
    ModeTransform.toLinearMap, Matrix.toLpLin_mul_same, LinearMap.comp_apply]
  rw [modeEmbeddingRegression_restriction_externalBasis]
  simp

/-- The range projector is the identity on every amplitude obtained by zero extension. -/
lemma modeEmbeddingRegression_projector_zeroExtension (amplitude : ModeAmplitude Bool) :
    modeEmbeddingRegressionProjector.toLinearMap
        (modeEmbeddingRegressionZeroExtension.toLinearMap amplitude) =
      modeEmbeddingRegressionZeroExtension.toLinearMap amplitude := by
  change (ModeTransform.rangeProjector modeEmbeddingRegressionEmbedding).toLinearMap
      ((ModeTransform.zeroExtension modeEmbeddingRegressionEmbedding).toLinearMap
        amplitude) =
    (ModeTransform.zeroExtension modeEmbeddingRegressionEmbedding).toLinearMap
      amplitude
  simp only [ModeTransform.rangeProjector, ModeTransform.toLinearMap,
    Matrix.toLpLin_mul_same, LinearMap.comp_apply]
  rw [ModeTransform.restriction_apply_zeroExtension]

/-- The range projector retains the full selected amplitude while discarding an independent
external amplitude. -/
lemma modeEmbeddingRegression_projector_mixedAmplitude :
    modeEmbeddingRegressionProjector.toLinearMap
        (modeEmbeddingRegressionZeroExtension.toLinearMap modeEmbeddingRegressionAmplitude +
          modeEmbeddingRegressionExternalBasis) =
      modeEmbeddingRegressionZeroExtension.toLinearMap
        modeEmbeddingRegressionAmplitude := by
  rw [map_add, modeEmbeddingRegression_projector_zeroExtension,
    modeEmbeddingRegression_projector_externalBasis, add_zero]

/-!

## C. Power and contraction laws

-/

/-- The external-coordinate amplitude has normalized modal power `5`. -/
lemma modeEmbeddingRegression_externalBasis_power :
    modeEmbeddingRegressionExternalBasis.power = 5 := by
  rw [ModeAmplitude.power_eq_sum_normSq, Fin.sum_univ_three]
  norm_num [modeEmbeddingRegressionExternalBasis, Complex.normSq,
    Matrix.cons_val_two, Matrix.head_cons]

/-- Zero extension preserves the power of every selected amplitude in the fixture. -/
lemma modeEmbeddingRegression_zeroExtension_isPowerPreserving :
    modeEmbeddingRegressionZeroExtension.IsPowerPreserving :=
  ModeTransform.zeroExtension_isPowerPreserving modeEmbeddingRegressionEmbedding

/-- Zero extension is an isometry in the fixture. -/
lemma modeEmbeddingRegression_zeroExtension_isometry :
    Isometry modeEmbeddingRegressionZeroExtension.toLinearMap :=
  ModeTransform.zeroExtension_isometry modeEmbeddingRegressionEmbedding

/-- Restriction is passive in the fixture. -/
lemma modeEmbeddingRegression_restriction_isPassive :
    modeEmbeddingRegressionRestriction.IsPassive :=
  ModeTransform.restriction_isPassive modeEmbeddingRegressionEmbedding

/-- The external-coordinate amplitude shows strict power loss under restriction. -/
lemma modeEmbeddingRegression_restriction_strict_power_loss :
    (modeEmbeddingRegressionRestriction.toLinearMap
        modeEmbeddingRegressionExternalBasis).power <
      modeEmbeddingRegressionExternalBasis.power := by
  rw [modeEmbeddingRegression_restriction_externalBasis,
    modeEmbeddingRegression_externalBasis_power]
  simp [ModeAmplitude.power]

/-- Restriction is not globally power-preserving for this embedding, which is not surjective. -/
lemma modeEmbeddingRegression_restriction_not_powerPreserving :
    ¬modeEmbeddingRegressionRestriction.IsPowerPreserving := by
  intro hPower
  exact (ne_of_lt modeEmbeddingRegression_restriction_strict_power_loss)
    (hPower modeEmbeddingRegressionExternalBasis)

/-- The ambient selected-coordinate projector is a star projection. -/
lemma modeEmbeddingRegression_projector_isStarProjection :
    IsStarProjection modeEmbeddingRegressionProjector :=
  ModeTransform.rangeProjector_isStarProjection modeEmbeddingRegressionEmbedding

/-- The ambient selected-coordinate projector is passive. -/
lemma modeEmbeddingRegression_projector_isPassive :
    modeEmbeddingRegressionProjector.IsPassive :=
  ModeTransform.rangeProjector_isPassive modeEmbeddingRegressionEmbedding

/-- The ambient projector is not globally power-preserving because it discards the external
coordinate. -/
lemma modeEmbeddingRegression_projector_not_powerPreserving :
    ¬modeEmbeddingRegressionProjector.IsPowerPreserving := by
  intro hPower
  have hExternal := hPower modeEmbeddingRegressionExternalBasis
  rw [modeEmbeddingRegression_projector_externalBasis,
    modeEmbeddingRegression_externalBasis_power] at hExternal
  simp [ModeAmplitude.power] at hExternal

/-- The ambient range projector is not the identity transform. -/
lemma modeEmbeddingRegression_projector_ne_one :
    modeEmbeddingRegressionProjector ≠ (1 : ModeTransform (Fin 3) (Fin 3)) := by
  intro hProjector
  apply modeEmbeddingRegression_projector_not_powerPreserving
  rw [hProjector]
  exact ModeTransform.isPowerPreserving_one

/-!

## D. Zero-extending a nonsymmetric transform

-/

/-- A nonsymmetric selected-mode transform that checks a row-column swap. -/
def modeEmbeddingRegressionTransform : ModeTransform Bool Bool
  | false, false => Complex.I
  | false, true => 2
  | true, false => 3
  | true, true => 4

/-- The nonsymmetric transform inserted at ambient coordinates zero and two. -/
abbrev modeEmbeddingRegressionZeroExtendedTransform : ModeTransform (Fin 3) (Fin 3) :=
  modeEmbeddingRegressionTransform.zeroExtend modeEmbeddingRegressionEmbedding
    modeEmbeddingRegressionEmbedding

/-- The selected row zero, column zero entry retains the imaginary matrix coefficient. -/
lemma modeEmbeddingRegression_zeroExtend_entry_zero_zero :
    modeEmbeddingRegressionZeroExtendedTransform 0 0 = Complex.I := by
  change modeEmbeddingRegressionTransform.zeroExtend modeEmbeddingRegressionEmbedding
      modeEmbeddingRegressionEmbedding (modeEmbeddingRegressionEmbedding false)
        (modeEmbeddingRegressionEmbedding false) = Complex.I
  exact ModeTransform.zeroExtend_entry_image modeEmbeddingRegressionTransform
    modeEmbeddingRegressionEmbedding modeEmbeddingRegressionEmbedding false false

/-- The selected row zero, column two entry retains the upper-right coefficient. -/
lemma modeEmbeddingRegression_zeroExtend_entry_zero_two :
    modeEmbeddingRegressionZeroExtendedTransform 0 2 = 2 := by
  change modeEmbeddingRegressionTransform.zeroExtend modeEmbeddingRegressionEmbedding
      modeEmbeddingRegressionEmbedding (modeEmbeddingRegressionEmbedding false)
        (modeEmbeddingRegressionEmbedding true) = 2
  exact ModeTransform.zeroExtend_entry_image modeEmbeddingRegressionTransform
    modeEmbeddingRegressionEmbedding modeEmbeddingRegressionEmbedding false true

/-- The selected row two, column zero entry retains the distinct lower-left coefficient. -/
lemma modeEmbeddingRegression_zeroExtend_entry_two_zero :
    modeEmbeddingRegressionZeroExtendedTransform 2 0 = 3 := by
  change modeEmbeddingRegressionTransform.zeroExtend modeEmbeddingRegressionEmbedding
      modeEmbeddingRegressionEmbedding (modeEmbeddingRegressionEmbedding true)
        (modeEmbeddingRegressionEmbedding false) = 3
  exact ModeTransform.zeroExtend_entry_image modeEmbeddingRegressionTransform
    modeEmbeddingRegressionEmbedding modeEmbeddingRegressionEmbedding true false

/-- The external output coordinate gives a zero row in the zero-extended transform. -/
lemma modeEmbeddingRegression_zeroExtend_entry_external_output :
    modeEmbeddingRegressionZeroExtendedTransform 1 0 = 0 := by
  exact ModeTransform.zeroExtend_entry_of_output_not_mem_range
    modeEmbeddingRegressionTransform modeEmbeddingRegressionEmbedding
      modeEmbeddingRegressionEmbedding 1 0 modeEmbeddingRegression_one_not_mem_range

/-- The external input coordinate gives a zero column in the zero-extended transform. -/
lemma modeEmbeddingRegression_zeroExtend_entry_external_input :
    modeEmbeddingRegressionZeroExtendedTransform 0 1 = 0 := by
  exact ModeTransform.zeroExtend_entry_of_input_not_mem_range
    modeEmbeddingRegressionTransform modeEmbeddingRegressionEmbedding
      modeEmbeddingRegressionEmbedding 0 1 modeEmbeddingRegression_one_not_mem_range

/-- The zero-extended transform retains the selected row-column orientation, acts on separated
coordinates, and maps the external output coordinate to zero. -/
lemma modeEmbeddingRegression_zeroExtend_action :
    modeEmbeddingRegressionZeroExtendedTransform.toLinearMap
        (modeEmbeddingRegressionZeroExtension.toLinearMap
          modeEmbeddingRegressionAmplitude) =
      WithLp.toLp 2 ![(3 : ℂ) - Complex.I, 0, 11 - Complex.I] := by
  rw [ModeTransform.zeroExtend_apply_zeroExtension]
  apply WithLp.ofLp_injective 2
  funext ambient
  fin_cases ambient
  · calc
      (ModeTransform.zeroExtension modeEmbeddingRegressionEmbedding).toLinearMap
          (modeEmbeddingRegressionTransform.toLinearMap
            modeEmbeddingRegressionAmplitude) 0 =
          modeEmbeddingRegressionTransform.toLinearMap
            modeEmbeddingRegressionAmplitude false :=
        ModeTransform.zeroExtension_apply_image modeEmbeddingRegressionEmbedding _ false
      _ = (3 : ℂ) - Complex.I := by
        norm_num [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
          modeEmbeddingRegressionTransform, modeEmbeddingRegressionAmplitude,
          Fintype.sum_bool, Matrix.head_cons]
        ring_nf
        rw [Complex.I_sq]
        ring
  · change (ModeTransform.zeroExtension modeEmbeddingRegressionEmbedding).toLinearMap
        (modeEmbeddingRegressionTransform.toLinearMap
          modeEmbeddingRegressionAmplitude) 1 = 0
    rw [ModeTransform.zeroExtension_apply_of_not_mem_range
      modeEmbeddingRegressionEmbedding _ 1 modeEmbeddingRegression_one_not_mem_range]
  · calc
      (ModeTransform.zeroExtension modeEmbeddingRegressionEmbedding).toLinearMap
          (modeEmbeddingRegressionTransform.toLinearMap
            modeEmbeddingRegressionAmplitude) 2 =
          modeEmbeddingRegressionTransform.toLinearMap
            modeEmbeddingRegressionAmplitude true :=
        ModeTransform.zeroExtension_apply_image modeEmbeddingRegressionEmbedding _ true
      _ = 11 - Complex.I := by
        norm_num [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
          modeEmbeddingRegressionTransform, modeEmbeddingRegressionAmplitude,
          Fintype.sum_bool, Matrix.cons_val_two]
        ring

/-- The zero-extended transform maps an input supported only on the external coordinate to zero. -/
lemma modeEmbeddingRegression_zeroExtend_externalBasis :
    modeEmbeddingRegressionZeroExtendedTransform.toLinearMap
        modeEmbeddingRegressionExternalBasis = 0 := by
  simp only [modeEmbeddingRegressionZeroExtendedTransform, ModeTransform.zeroExtend,
    ModeTransform.toLinearMap, Matrix.toLpLin_mul_same, LinearMap.comp_apply]
  rw [modeEmbeddingRegression_restriction_externalBasis]
  simp

/-- Adding an external-coordinate input does not change the exact selected-mode output. -/
lemma modeEmbeddingRegression_zeroExtend_mixed_action :
    modeEmbeddingRegressionZeroExtendedTransform.toLinearMap
        (modeEmbeddingRegressionZeroExtension.toLinearMap modeEmbeddingRegressionAmplitude +
          modeEmbeddingRegressionExternalBasis) =
      WithLp.toLp 2 ![(3 : ℂ) - Complex.I, 0, 11 - Complex.I] := by
  rw [map_add, modeEmbeddingRegression_zeroExtend_action,
    modeEmbeddingRegression_zeroExtend_externalBasis, add_zero]

/-- Zero-extending the selected identity gives a passive ambient transform. -/
lemma modeEmbeddingRegression_zeroExtend_one_isPassive :
    ((1 : ModeTransform Bool Bool).zeroExtend modeEmbeddingRegressionEmbedding
      modeEmbeddingRegressionEmbedding).IsPassive :=
  ModeTransform.isPowerPreserving_one.isPassive.zeroExtend modeEmbeddingRegressionEmbedding
    modeEmbeddingRegressionEmbedding

end

end Optics
