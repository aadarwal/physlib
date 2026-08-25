/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Mode.Basic

/-!
# Embeddings of optical mode families

## i. Overview

This file uses an embedding between a selected family of power-normalized modes and a full ambient
family. Amplitude restriction and its bundled linear map evaluate the selected coordinates without
a finiteness assumption. For finite coordinate families, the corresponding restriction transform
and its adjoint distinguish the selected identity from the ambient range projector.

The same maps zero-extend a rectangular mode transform into full input and output families.
This is the linear-algebra interface needed to include a connected optical system in an ambient
family containing exposed channels.

## ii. Main definitions

- `ModeAmplitude.restrictEmbedding`: restrict an ambient amplitude along an embedding.
- `ModeAmplitude.restrictEmbeddingLinearMap`: the bundled complex-linear amplitude restriction.
- `ModeTransform.restriction`: select the coordinates in an embedding's range.
- `ModeTransform.blockDiagonal'_apply`: evaluate a dependent block-diagonal transform on one
  output block using the matching restricted input amplitude.
- `ModeTransform.zeroExtension`: extend selected amplitudes by zero.
- `ModeTransform.rangeProjector`: map ambient amplitudes onto the selected coordinates.
- `ModeTransform.zeroExtend`: include a transform in full input and output mode families.

## iii. Scope

Amplitude restriction and its bundled linear map do not require finite index families. The matrix,
power, and norm results concern finite power-normalized coordinate families. A restriction is
passive but generally not power-preserving, because it discards amplitudes not in the selected
range. Zero extension is power-preserving but generally not surjective. Neither operation claims
physical absorption, electromagnetic flux conservation, or a physical-port partition.

-/

@[expose] public section

namespace Optics

open Matrix
open scoped ComplexConjugate

noncomputable section

/-!

## A. Restricted amplitudes

-/

/-- Restrict an ambient mode amplitude to the coordinates selected by an embedding. -/
def ModeAmplitude.restrictEmbedding {ι κ : Type*} (embedding : ι ↪ κ)
    (amplitude : ModeAmplitude κ) : ModeAmplitude ι :=
  WithLp.toLp 2 (WithLp.ofLp amplitude ∘ embedding)

/-- Complex-linear restriction of an ambient amplitude along an embedding. -/
def ModeAmplitude.restrictEmbeddingLinearMap {ι κ : Type*} (embedding : ι ↪ κ) :
    ModeAmplitude κ →ₗ[ℂ] ModeAmplitude ι where
  toFun := ModeAmplitude.restrictEmbedding embedding
  map_add' first second := by
    apply WithLp.ofLp_injective 2
    funext index
    rfl
  map_smul' scalar amplitude := by
    apply WithLp.ofLp_injective 2
    funext index
    rfl

/-- Restriction evaluates an amplitude at the corresponding ambient coordinate. -/
@[simp]
lemma ModeAmplitude.restrictEmbedding_apply {ι κ : Type*} (embedding : ι ↪ κ)
    (amplitude : ModeAmplitude κ) (mode : ι) :
    amplitude.restrictEmbedding embedding mode = amplitude (embedding mode) := rfl

/-- Bundled embedding restriction agrees with coordinate restriction. -/
@[simp]
lemma ModeAmplitude.restrictEmbeddingLinearMap_apply {ι κ : Type*} (embedding : ι ↪ κ)
    (amplitude : ModeAmplitude κ) :
    ModeAmplitude.restrictEmbeddingLinearMap embedding amplitude =
      amplitude.restrictEmbedding embedding := rfl

/-- The power of a restricted amplitude is the sum over the selected ambient coordinates. -/
lemma ModeAmplitude.power_restrictEmbedding_eq_sum {ι κ : Type*} [Fintype ι]
    (embedding : ι ↪ κ) (amplitude : ModeAmplitude κ) :
    (amplitude.restrictEmbedding embedding).power =
      ∑ mode : ι, Complex.normSq (amplitude (embedding mode)) := by
  simp only [ModeAmplitude.power_eq_sum_normSq, ModeAmplitude.restrictEmbedding_apply]

/-- Restriction of a finite power-normalized amplitude has no greater modal power. -/
lemma ModeAmplitude.power_restrictEmbedding_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (embedding : ι ↪ κ) (amplitude : ModeAmplitude κ) :
    (amplitude.restrictEmbedding embedding).power ≤ amplitude.power := by
  classical
  rw [ModeAmplitude.power_restrictEmbedding_eq_sum,
    ModeAmplitude.power_eq_sum_normSq]
  calc
    (∑ mode : ι, Complex.normSq (amplitude (embedding mode))) =
        ∑ mode ∈ Finset.univ.image embedding, Complex.normSq (amplitude mode) := by
      simp only [Finset.sum_image embedding.injective.injOn]
    _ ≤ ∑ mode : κ, Complex.normSq (amplitude mode) :=
      Finset.sum_le_univ_sum_of_nonneg fun mode => Complex.normSq_nonneg (amplitude mode)

/-- Restriction preserves all modal power exactly when every omitted ambient coordinate has zero
amplitude. -/
lemma ModeAmplitude.power_restrictEmbedding_eq_iff {ι κ : Type*} [Fintype ι] [Fintype κ]
    (embedding : ι ↪ κ) (amplitude : ModeAmplitude κ) :
    (amplitude.restrictEmbedding embedding).power = amplitude.power ↔
      ∀ ambient, ambient ∉ Set.range embedding → amplitude ambient = 0 := by
  classical
  have hRestricted :
      (amplitude.restrictEmbedding embedding).power =
        ∑ ambient ∈ Finset.univ.image embedding, Complex.normSq (amplitude ambient) := by
    rw [ModeAmplitude.power_restrictEmbedding_eq_sum]
    simp only [Finset.sum_image embedding.injective.injOn]
  have hDecomposition :
      amplitude.power =
        (∑ ambient ∈ Finset.univ \ Finset.univ.image embedding,
          Complex.normSq (amplitude ambient)) +
        ∑ ambient ∈ Finset.univ.image embedding, Complex.normSq (amplitude ambient) := by
    rw [ModeAmplitude.power_eq_sum_normSq]
    exact (Finset.sum_sdiff (f := fun ambient => Complex.normSq (amplitude ambient))
      (Finset.subset_univ (Finset.univ.image embedding))).symm
  constructor
  · intro hPower ambient hAmbient
    have hComplementPower :
        (∑ mode ∈ Finset.univ \ Finset.univ.image embedding,
          Complex.normSq (amplitude mode)) = 0 := by
      rw [hRestricted, hDecomposition] at hPower
      linarith
    have hEveryComplement :
        ∀ mode ∈ Finset.univ \ Finset.univ.image embedding,
          Complex.normSq (amplitude mode) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun mode _ =>
        Complex.normSq_nonneg (amplitude mode)).mp hComplementPower
    apply Complex.normSq_eq_zero.mp
    apply hEveryComplement ambient
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
    intro hImage
    rw [Finset.mem_image] at hImage
    obtain ⟨mode, _, hMode⟩ := hImage
    exact hAmbient ⟨mode, hMode⟩
  · intro hZero
    rw [hRestricted, hDecomposition]
    have hComplementPower :
        (∑ ambient ∈ Finset.univ \ Finset.univ.image embedding,
          Complex.normSq (amplitude ambient)) = 0 := by
      apply Finset.sum_eq_zero
      intro ambient hAmbient
      apply Complex.normSq_eq_zero.mpr
      apply hZero ambient
      rintro ⟨mode, rfl⟩
      have hNotImage : embedding mode ∉ Finset.univ.image embedding := by
        simpa only [Finset.mem_sdiff, Finset.mem_univ, true_and] using hAmbient
      exact hNotImage (Finset.mem_image.mpr ⟨mode, Finset.mem_univ _, rfl⟩)
    rw [hComplementPower, zero_add]

/-!

## B. Restriction and zero extension

-/

/-- The coordinate-selection transform associated with an embedding of mode families. -/
def ModeTransform.restriction {ι κ : Type*} [DecidableEq κ] (embedding : ι ↪ κ) :
    ModeTransform κ ι :=
  (1 : ModeTransform κ κ).submatrix embedding id

/-- A restriction entry is one exactly when its selected row names the ambient column. -/
@[simp]
lemma ModeTransform.restriction_entry {ι κ : Type*} [DecidableEq κ]
    (embedding : ι ↪ κ) (selected : ι) (ambient : κ) :
    ModeTransform.restriction embedding selected ambient =
      if embedding selected = ambient then 1 else 0 := by
  simp [ModeTransform.restriction, Matrix.one_apply]

/-- Restriction acts on amplitudes by evaluating the selected ambient coordinates. -/
@[simp]
lemma ModeTransform.toLinearMap_restriction {ι κ : Type*} [Fintype κ] [DecidableEq κ]
    (embedding : ι ↪ κ) (amplitude : ModeAmplitude κ) :
    (ModeTransform.restriction embedding).toLinearMap amplitude =
      amplitude.restrictEmbedding embedding := by
  apply WithLp.ofLp_injective 2
  funext selected
  simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    ModeTransform.restriction_entry]

/-- A dependent block-diagonal transform acts on one output block using only the corresponding
restricted input amplitude. -/
lemma ModeTransform.blockDiagonal'_apply {ο : Type*} {ι : ο → Type*} {κ : ο → Type*}
    [Fintype ο] [DecidableEq ο] [∀ o, Fintype (ι o)] [∀ o, DecidableEq (ι o)]
    (transform : ∀ o, ModeTransform (ι o) (κ o))
    (amplitude : ModeAmplitude (Σ o, ι o)) (o : ο) (output : κ o) :
    ModeTransform.toLinearMap
        (Matrix.blockDiagonal' transform : ModeTransform (Σ o, ι o) (Σ o, κ o))
        amplitude ⟨o, output⟩ =
      ModeTransform.toLinearMap (transform o)
        (amplitude.restrictEmbedding (Function.Embedding.sigmaMk o)) output := by
  simp only [ModeTransform.toLinearMap, Matrix.toLpLin_apply, Matrix.mulVec,
    dotProduct, ← Finset.univ_sigma_univ, Finset.sum_sigma,
    Matrix.blockDiagonal'_apply]
  rw [Fintype.sum_eq_single o]
  · simp [ModeAmplitude.restrictEmbedding_apply]
  · intro j hji
    exact Finset.sum_eq_zero fun _ _ => by
      rw [dif_neg hji.symm, zero_mul]

/-- The adjoint of coordinate restriction extends selected amplitudes by zero. -/
def ModeTransform.zeroExtension {ι κ : Type*} [DecidableEq κ] (embedding : ι ↪ κ) :
    ModeTransform ι κ :=
  (ModeTransform.restriction embedding)ᴴ

/-- A zero-extension entry is one exactly on the graph of the mode embedding. -/
@[simp]
lemma ModeTransform.zeroExtension_entry {ι κ : Type*} [DecidableEq κ]
    (embedding : ι ↪ κ) (ambient : κ) (selected : ι) :
    ModeTransform.zeroExtension embedding ambient selected =
      if embedding selected = ambient then 1 else 0 := by
  simp [ModeTransform.zeroExtension, ModeTransform.restriction_entry]

/-- Zero extension then restriction is the identity on the selected mode family. -/
@[simp]
lemma ModeTransform.restriction_mul_zeroExtension {ι κ : Type*} [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (embedding : ι ↪ κ) :
    ModeTransform.restriction embedding * ModeTransform.zeroExtension embedding =
      (1 : ModeTransform ι ι) := by
  ext first second
  simp [Matrix.mul_apply, ModeTransform.restriction_entry,
    ModeTransform.zeroExtension_entry, Matrix.one_apply, embedding.injective.eq_iff]

/-- Taking the adjoint of restriction gives zero extension. -/
@[simp]
lemma ModeTransform.restriction_conjTranspose {ι κ : Type*} [DecidableEq κ]
    (embedding : ι ↪ κ) :
    (ModeTransform.restriction embedding)ᴴ = ModeTransform.zeroExtension embedding := rfl

/-- Taking the adjoint of zero extension gives restriction. -/
@[simp]
lemma ModeTransform.zeroExtension_conjTranspose {ι κ : Type*} [DecidableEq κ]
    (embedding : ι ↪ κ) :
    (ModeTransform.zeroExtension embedding)ᴴ = ModeTransform.restriction embedding := by
  change ((ModeTransform.restriction embedding)ᴴ)ᴴ = ModeTransform.restriction embedding
  exact Matrix.conjTranspose_conjTranspose _

/-- Zero extension recovers an amplitude at every selected ambient coordinate. -/
@[simp]
lemma ModeTransform.zeroExtension_apply_image {ι κ : Type*} [Fintype ι]
    [DecidableEq ι] [DecidableEq κ] (embedding : ι ↪ κ)
    (amplitude : ModeAmplitude ι) (mode : ι) :
    (ModeTransform.zeroExtension embedding).toLinearMap amplitude (embedding mode) =
      amplitude mode := by
  simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    ModeTransform.zeroExtension_entry, embedding.injective.eq_iff]

/-- Zero extension vanishes at every ambient coordinate not in the embedding's range. -/
lemma ModeTransform.zeroExtension_apply_of_not_mem_range {ι κ : Type*} [Fintype ι]
    [DecidableEq ι] [DecidableEq κ] (embedding : ι ↪ κ)
    (amplitude : ModeAmplitude ι) (ambient : κ) (hAmbient : ambient ∉ Set.range embedding) :
    (ModeTransform.zeroExtension embedding).toLinearMap amplitude ambient = 0 := by
  have hNe : ∀ mode : ι, embedding mode ≠ ambient := by
    intro mode hMode
    exact hAmbient ⟨mode, hMode⟩
  simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    ModeTransform.zeroExtension_entry, hNe]

/-- Restriction of a zero-extended amplitude recovers the selected amplitude. -/
lemma ModeTransform.restriction_apply_zeroExtension {ι κ : Type*} [Fintype ι]
    [Fintype κ] [DecidableEq ι] [DecidableEq κ] (embedding : ι ↪ κ)
    (amplitude : ModeAmplitude ι) :
    (ModeTransform.restriction embedding).toLinearMap
        ((ModeTransform.zeroExtension embedding).toLinearMap amplitude) = amplitude := by
  apply WithLp.ofLp_injective 2
  funext mode
  simp

/-!

## C. The selected-coordinate projector

-/

/-- The ambient projector that retains the selected coordinates and zeros their complement. -/
def ModeTransform.rangeProjector {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (embedding : ι ↪ κ) : ModeTransform κ κ :=
  ModeTransform.zeroExtension embedding * ModeTransform.restriction embedding

/-- The range projector retains every coordinate selected by the embedding. -/
@[simp]
lemma ModeTransform.rangeProjector_apply_image {ι κ : Type*} [Fintype ι]
    [Fintype κ] [DecidableEq κ] (embedding : ι ↪ κ)
    (amplitude : ModeAmplitude κ) (mode : ι) :
    (ModeTransform.rangeProjector embedding).toLinearMap amplitude (embedding mode) =
      amplitude (embedding mode) := by
  classical
  simp [ModeTransform.rangeProjector, Matrix.toLpLin_mul_same]

/-- The range projector zeros every ambient coordinate not in the embedding's range. -/
lemma ModeTransform.rangeProjector_apply_of_not_mem_range {ι κ : Type*} [Fintype ι]
    [Fintype κ] [DecidableEq κ] (embedding : ι ↪ κ)
    (amplitude : ModeAmplitude κ) (ambient : κ) (hAmbient : ambient ∉ Set.range embedding) :
    (ModeTransform.rangeProjector embedding).toLinearMap amplitude ambient = 0 := by
  classical
  simp only [ModeTransform.rangeProjector, ModeTransform.toLinearMap,
    Matrix.toLpLin_mul_same, LinearMap.comp_apply]
  exact ModeTransform.zeroExtension_apply_of_not_mem_range embedding _ ambient hAmbient

/-- The range projectors of two embeddings that form a sum partition resolve the ambient
identity. -/
lemma ModeTransform.rangeProjector_add_rangeProjector_eq_one
    {ι μ κ : Type*} [Fintype ι] [Fintype μ] [Fintype κ] [DecidableEq κ]
    (left : ι ↪ κ) (right : μ ↪ κ) (partition : ι ⊕ μ ≃ κ)
    (hLeft : ∀ mode, partition (Sum.inl mode) = left mode)
    (hRight : ∀ mode, partition (Sum.inr mode) = right mode) :
    ModeTransform.rangeProjector left + ModeTransform.rangeProjector right =
      (1 : ModeTransform κ κ) := by
  classical
  apply (Matrix.toLpLin 2 2).injective
  simp only [map_add, Matrix.toLpLin_one]
  ext amplitude ambient
  change
    (ModeTransform.rangeProjector left).toLinearMap amplitude ambient +
        (ModeTransform.rangeProjector right).toLinearMap amplitude ambient =
      amplitude ambient
  rcases hPartition : partition.symm ambient with selected | selected
  · have hAmbient : ambient = left selected := by
      calc
        ambient = partition (partition.symm ambient) := (partition.apply_symm_apply ambient).symm
        _ = partition (Sum.inl selected) := congrArg partition hPartition
        _ = left selected := hLeft selected
    subst ambient
    rw [ModeTransform.rangeProjector_apply_image]
    rw [ModeTransform.rangeProjector_apply_of_not_mem_range]
    · simp
    · rintro ⟨other, hOther⟩
      have hImpossible : Sum.inl selected = Sum.inr other := partition.injective <| by
        rw [hLeft selected, hRight other]
        exact hOther.symm
      cases hImpossible
  · have hAmbient : ambient = right selected := by
      calc
        ambient = partition (partition.symm ambient) := (partition.apply_symm_apply ambient).symm
        _ = partition (Sum.inr selected) := congrArg partition hPartition
        _ = right selected := hRight selected
    subst ambient
    rw [ModeTransform.rangeProjector_apply_of_not_mem_range,
      ModeTransform.rangeProjector_apply_image]
    · simp
    · rintro ⟨other, hOther⟩
      have hImpossible : Sum.inl other = Sum.inr selected := partition.injective <| by
        rw [hLeft other, hRight selected]
        exact hOther
      cases hImpossible

/-- The selected-coordinate range projector is a self-adjoint idempotent. -/
lemma ModeTransform.rangeProjector_isStarProjection {ι κ : Type*} [Fintype ι]
    [Fintype κ] [DecidableEq κ] (embedding : ι ↪ κ) :
    IsStarProjection (ModeTransform.rangeProjector embedding) := by
  classical
  rw [isStarProjection_iff']
  constructor
  · calc
      ModeTransform.rangeProjector embedding * ModeTransform.rangeProjector embedding =
          (ModeTransform.zeroExtension embedding * ModeTransform.restriction embedding) *
            (ModeTransform.zeroExtension embedding *
              ModeTransform.restriction embedding) := rfl
      _ = ModeTransform.zeroExtension embedding *
          (ModeTransform.restriction embedding * ModeTransform.zeroExtension embedding) *
            ModeTransform.restriction embedding := by
        simp only [Matrix.mul_assoc]
      _ = ModeTransform.rangeProjector embedding := by
        rw [ModeTransform.restriction_mul_zeroExtension]
        simp [ModeTransform.rangeProjector]
  · change (ModeTransform.rangeProjector embedding)ᴴ =
      ModeTransform.rangeProjector embedding
    simp [ModeTransform.rangeProjector]

/-!

## D. Power and norm laws

-/

/-- Zero extension preserves normalized modal power. -/
lemma ModeTransform.zeroExtension_isPowerPreserving {ι κ : Type*} [Fintype ι]
    [Fintype κ] [DecidableEq ι] [DecidableEq κ] (embedding : ι ↪ κ) :
    (ModeTransform.zeroExtension embedding).IsPowerPreserving := by
  apply ModeTransform.isPowerPreserving_of_conjTranspose_mul_self
  simpa only [ModeTransform.zeroExtension_conjTranspose] using
    ModeTransform.restriction_mul_zeroExtension embedding

/-- Zero extension is an isometry of finite mode-amplitude spaces. -/
lemma ModeTransform.zeroExtension_isometry {ι κ : Type*} [Fintype ι]
    [Fintype κ] [DecidableEq ι] [DecidableEq κ] (embedding : ι ↪ κ) :
    Isometry (ModeTransform.zeroExtension embedding).toLinearMap := by
  rw [AddMonoidHomClass.isometry_iff_norm]
  intro amplitude
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simpa only [ModeAmplitude.power] using
    ModeTransform.zeroExtension_isPowerPreserving embedding amplitude

/-- Coordinate restriction is passive for finite power-normalized mode families. -/
lemma ModeTransform.restriction_isPassive {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (embedding : ι ↪ κ) :
    (ModeTransform.restriction embedding).IsPassive := by
  intro amplitude
  rw [ModeTransform.toLinearMap_restriction]
  exact ModeAmplitude.power_restrictEmbedding_le embedding amplitude

/-- Coordinate restriction is a norm contraction. -/
lemma ModeTransform.restriction_norm_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (embedding : ι ↪ κ) (amplitude : ModeAmplitude κ) :
    ‖(ModeTransform.restriction embedding).toLinearMap amplitude‖ ≤ ‖amplitude‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simpa only [ModeAmplitude.power] using
    ModeTransform.restriction_isPassive embedding amplitude

/-- The selected-coordinate range projector is passive. -/
lemma ModeTransform.rangeProjector_isPassive {ι κ : Type*} [Fintype ι]
    [Fintype κ] [DecidableEq κ] (embedding : ι ↪ κ) :
    (ModeTransform.rangeProjector embedding).IsPassive := by
  classical
  exact (ModeTransform.zeroExtension_isPowerPreserving embedding).isPassive.mul
    (ModeTransform.restriction_isPassive embedding)

/-!

## E. Zero-extending mode transforms

-/

/-- Include a mode transform in full input and output mode families, with zero action on
coordinates not in the selected range. -/
def ModeTransform.zeroExtend {ι ι' κ κ' : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι'] [DecidableEq κ'] (transform : ModeTransform ι κ)
    (inputEmbedding : ι ↪ ι') (outputEmbedding : κ ↪ κ') : ModeTransform ι' κ' :=
  ModeTransform.zeroExtension outputEmbedding * transform *
    ModeTransform.restriction inputEmbedding

/-- If a transform's input-side Gram matrix is the identity, the input-side Gram matrix of its
zero extension is exactly the selected-coordinate range projector. -/
lemma ModeTransform.zeroExtend_conjTranspose_mul_self
    {ι ι' κ κ' : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq ι'] [DecidableEq κ']
    (transform : ModeTransform ι κ) (inputEmbedding : ι ↪ ι')
    (outputEmbedding : κ ↪ κ') (hTransform : transformᴴ * transform = 1) :
    (transform.zeroExtend inputEmbedding outputEmbedding)ᴴ *
        transform.zeroExtend inputEmbedding outputEmbedding =
      ModeTransform.rangeProjector inputEmbedding := by
  change
    ((ModeTransform.zeroExtension outputEmbedding * transform *
          ModeTransform.restriction inputEmbedding)ᴴ *
        (ModeTransform.zeroExtension outputEmbedding * transform *
          ModeTransform.restriction inputEmbedding)) =
      ModeTransform.zeroExtension inputEmbedding *
        ModeTransform.restriction inputEmbedding
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    ModeTransform.restriction_conjTranspose,
    ModeTransform.zeroExtension_conjTranspose]
  calc
    (ModeTransform.zeroExtension inputEmbedding *
          (transformᴴ * ModeTransform.restriction outputEmbedding)) *
        (ModeTransform.zeroExtension outputEmbedding * transform *
          ModeTransform.restriction inputEmbedding) =
      ModeTransform.zeroExtension inputEmbedding *
        (transformᴴ *
          (ModeTransform.restriction outputEmbedding *
            ModeTransform.zeroExtension outputEmbedding) * transform) *
        ModeTransform.restriction inputEmbedding := by
      simp only [Matrix.mul_assoc]
    _ = ModeTransform.zeroExtension inputEmbedding * (transformᴴ * transform) *
        ModeTransform.restriction inputEmbedding := by
      rw [ModeTransform.restriction_mul_zeroExtension]
      simp
    _ = ModeTransform.zeroExtension inputEmbedding *
        ModeTransform.restriction inputEmbedding := by
      rw [hTransform]
      simp

/-- If a transform's output-side Gram matrix is the identity, the output-side Gram matrix of its
zero extension is exactly the selected-coordinate range projector. -/
lemma ModeTransform.zeroExtend_mul_conjTranspose
    {ι ι' κ κ' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι']
    [Fintype κ] [DecidableEq κ] [DecidableEq ι'] [DecidableEq κ']
    (transform : ModeTransform ι κ) (inputEmbedding : ι ↪ ι')
    (outputEmbedding : κ ↪ κ') (hTransform : transform * transformᴴ = 1) :
    transform.zeroExtend inputEmbedding outputEmbedding *
        (transform.zeroExtend inputEmbedding outputEmbedding)ᴴ =
      ModeTransform.rangeProjector outputEmbedding := by
  change
    (ModeTransform.zeroExtension outputEmbedding * transform *
          ModeTransform.restriction inputEmbedding) *
        (ModeTransform.zeroExtension outputEmbedding * transform *
          ModeTransform.restriction inputEmbedding)ᴴ =
      ModeTransform.zeroExtension outputEmbedding *
        ModeTransform.restriction outputEmbedding
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    ModeTransform.restriction_conjTranspose,
    ModeTransform.zeroExtension_conjTranspose]
  calc
    (ModeTransform.zeroExtension outputEmbedding * transform *
          ModeTransform.restriction inputEmbedding) *
        (ModeTransform.zeroExtension inputEmbedding *
          (transformᴴ * ModeTransform.restriction outputEmbedding)) =
      ModeTransform.zeroExtension outputEmbedding *
        (transform *
          (ModeTransform.restriction inputEmbedding *
            ModeTransform.zeroExtension inputEmbedding) * transformᴴ) *
        ModeTransform.restriction outputEmbedding := by
      simp only [Matrix.mul_assoc]
    _ = ModeTransform.zeroExtension outputEmbedding * (transform * transformᴴ) *
        ModeTransform.restriction outputEmbedding := by
      rw [ModeTransform.restriction_mul_zeroExtension]
      simp
    _ = ModeTransform.zeroExtension outputEmbedding *
        ModeTransform.restriction outputEmbedding := by
      rw [hTransform]
      simp

/-- Zero-extending a transform preserves every matrix entry whose row and column are both
selected. -/
@[simp]
lemma ModeTransform.zeroExtend_entry_image {ι ι' κ κ' : Type*} [Fintype ι]
    [Fintype κ] [DecidableEq ι'] [DecidableEq κ']
    (transform : ModeTransform ι κ) (inputEmbedding : ι ↪ ι')
    (outputEmbedding : κ ↪ κ') (output : κ) (input : ι) :
    transform.zeroExtend inputEmbedding outputEmbedding (outputEmbedding output)
        (inputEmbedding input) = transform output input := by
  classical
  simp [ModeTransform.zeroExtend, Matrix.mul_apply,
    ModeTransform.zeroExtension_entry, ModeTransform.restriction_entry,
    inputEmbedding.injective.eq_iff, outputEmbedding.injective.eq_iff]

/-- A zero-extended transform has a zero row not in the selected output range. -/
lemma ModeTransform.zeroExtend_entry_of_output_not_mem_range
    {ι ι' κ κ' : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι'] [DecidableEq κ']
    (transform : ModeTransform ι κ) (inputEmbedding : ι ↪ ι')
    (outputEmbedding : κ ↪ κ') (output : κ') (input : ι')
    (hOutput : output ∉ Set.range outputEmbedding) :
    transform.zeroExtend inputEmbedding outputEmbedding output input = 0 := by
  have hNe : ∀ mode : κ, outputEmbedding mode ≠ output := by
    intro mode hMode
    exact hOutput ⟨mode, hMode⟩
  simp [ModeTransform.zeroExtend, Matrix.mul_apply,
    ModeTransform.zeroExtension_entry, hNe]

/-- A zero-extended transform has a zero column not in the selected input range. -/
lemma ModeTransform.zeroExtend_entry_of_input_not_mem_range
    {ι ι' κ κ' : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι'] [DecidableEq κ']
    (transform : ModeTransform ι κ) (inputEmbedding : ι ↪ ι')
    (outputEmbedding : κ ↪ κ') (output : κ') (input : ι')
    (hInput : input ∉ Set.range inputEmbedding) :
    transform.zeroExtend inputEmbedding outputEmbedding output input = 0 := by
  have hNe : ∀ mode : ι, inputEmbedding mode ≠ input := by
    intro mode hMode
    exact hInput ⟨mode, hMode⟩
  simp [ModeTransform.zeroExtend, Matrix.mul_apply,
    ModeTransform.restriction_entry, hNe]

/-- A zero-extended transform restricts an arbitrary ambient input, applies the original
transform, and then extends the result by zero. -/
lemma ModeTransform.zeroExtend_apply
    {ι ι' κ κ' : Type*} [Fintype ι] [Fintype ι'] [Fintype κ]
    [DecidableEq ι] [DecidableEq ι'] [DecidableEq κ] [DecidableEq κ']
    (transform : ModeTransform ι κ) (inputEmbedding : ι ↪ ι')
    (outputEmbedding : κ ↪ κ') (amplitude : ModeAmplitude ι') :
    (transform.zeroExtend inputEmbedding outputEmbedding).toLinearMap amplitude =
      (ModeTransform.zeroExtension outputEmbedding).toLinearMap
        (transform.toLinearMap (amplitude.restrictEmbedding inputEmbedding)) := by
  simp only [ModeTransform.zeroExtend, ModeTransform.toLinearMap,
    Matrix.toLpLin_mul_same, LinearMap.comp_apply,
    ModeTransform.toLinearMap_restriction]

/-- The output power of a zero-extended transform is exactly the power obtained after restricting
the ambient input and applying the original transform. -/
lemma ModeTransform.zeroExtend_power
    {ι ι' κ κ' : Type*} [Fintype ι] [Fintype ι'] [Fintype κ] [Fintype κ']
    [DecidableEq ι] [DecidableEq ι'] [DecidableEq κ] [DecidableEq κ']
    (transform : ModeTransform ι κ) (inputEmbedding : ι ↪ ι')
    (outputEmbedding : κ ↪ κ') (amplitude : ModeAmplitude ι') :
    ((transform.zeroExtend inputEmbedding outputEmbedding).toLinearMap amplitude).power =
      (transform.toLinearMap (amplitude.restrictEmbedding inputEmbedding)).power := by
  rw [ModeTransform.zeroExtend_apply]
  exact ModeTransform.zeroExtension_isPowerPreserving outputEmbedding _

/-- On zero-extended inputs, a zero-extended transform has exactly the zero extension of the
original transform's action. -/
lemma ModeTransform.zeroExtend_apply_zeroExtension
    {ι ι' κ κ' : Type*} [Fintype ι] [Fintype ι'] [Fintype κ]
    [DecidableEq ι] [DecidableEq ι'] [DecidableEq κ] [DecidableEq κ']
    (transform : ModeTransform ι κ) (inputEmbedding : ι ↪ ι')
    (outputEmbedding : κ ↪ κ') (amplitude : ModeAmplitude ι) :
    (transform.zeroExtend inputEmbedding outputEmbedding).toLinearMap
        ((ModeTransform.zeroExtension inputEmbedding).toLinearMap amplitude) =
      (ModeTransform.zeroExtension outputEmbedding).toLinearMap
        (transform.toLinearMap amplitude) := by
  simp only [ModeTransform.zeroExtend, ModeTransform.toLinearMap,
    Matrix.toLpLin_mul_same, LinearMap.comp_apply]
  rw [ModeTransform.restriction_apply_zeroExtension]

/-- Zero-extending a finite mode transform preserves passivity. -/
lemma ModeTransform.IsPassive.zeroExtend
    {ι ι' κ κ' : Type*} [Fintype ι] [Fintype ι'] [Fintype κ] [Fintype κ']
    [DecidableEq ι] [DecidableEq ι'] [DecidableEq κ']
    {transform : ModeTransform ι κ} (hTransform : transform.IsPassive)
    (inputEmbedding : ι ↪ ι') (outputEmbedding : κ ↪ κ') :
    ModeTransform.IsPassive
      (ModeTransform.zeroExtend transform inputEmbedding outputEmbedding) := by
  classical
  intro amplitude
  rw [ModeTransform.zeroExtend_power]
  exact (hTransform (amplitude.restrictEmbedding inputEmbedding)).trans
    (ModeAmplitude.power_restrictEmbedding_le inputEmbedding amplitude)

end

end Optics
