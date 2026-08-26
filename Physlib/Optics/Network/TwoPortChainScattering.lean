/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.TwoPortScatteringChain

/-!
# Two-port chain-to-scattering conversion

## i. Overview

A backward-first chain transform maps `(bL, aL)` to `(aR, bR)`. This file proves that regrouping
its graph as a scattering relation determines `(bL, bR)` uniquely from `(aL, aR)` exactly when the
leading block `K₁₁ : bL → aR` is bijective.

Under that exact block hypothesis, the public scattering transform is extracted from the
functional regrouped behavior. Its four-block formula and both conversion round trips are then
proved as derived results. No inverse of the complete chain or scattering matrix is used.

## ii. Key results

- `BackwardFirstChainTransform.HasBijectiveLeadingBlock`: the exact scattering-view pivot.
- `BackwardFirstChainTransform.hasScatteringView_iff_hasBijectiveLeadingBlock`: the exact
  solvability criterion.
- `BackwardFirstChainTransform.toTwoPortScatteringTransform`: behavior-derived conversion.
- `BackwardFirstChainTransform.toTwoPortScatteringTransform_eq_blockFormula`: the exact block
  formula.
- `BackwardFirstChainTransform.toBackwardFirstChainTransform_toTwoPortScatteringTransform` and
  `TwoPortScatteringTransform.toTwoPortScatteringTransform_toBackwardFirstChainTransform`: the
  matrix round trips.

## iii. Table of contents

- A. Backward-first chain blocks
- B. Leading-block inverse and scattering formula
- C. Exact scattering-view criterion
- D. Behavior-derived scattering conversion
- E. Behavioral and matrix round trips

## iv. References

The chain equation is `(aR, bR) = K (bL, aL)`, while scattering rows are `(bL, bR)` and columns are
`(aL, aR)`. Thus the reverse conversion pivots `K₁₁`, and its lower-left scattering block is
`K₂₂ - K₂₁ * K₁₁⁻¹ * K₁₂` in precisely that order.

These are fixed-frequency complex-linear semantics. The pivot is a solvability condition for the
chosen coordinate presentation; it does not imply losslessness, passivity, reciprocity, causality,
reference-plane transport, or electromagnetic realization.

-/

@[expose] public section

namespace Optics

noncomputable section

universe u v

namespace BackwardFirstChainTransform

variable {ι : Type u} {κ : Type v}

/-!

## A. Backward-first chain blocks

-/

/-- The leading chain block mapping the left backward wave `bL` to the right backward wave `aR`. -/
abbrev leadingBlock (chain : BackwardFirstChainTransform ι κ) :
    ModeTransform (BackwardWave ι) (BackwardWave κ) :=
  chain.toBlocks₁₁

/-- The upper-right chain block mapping the left forward wave `aL` to the right backward wave
`aR`. -/
abbrev upperRightBlock (chain : BackwardFirstChainTransform ι κ) :
    ModeTransform (ForwardWave ι) (BackwardWave κ) :=
  chain.toBlocks₁₂

/-- The lower-left chain block mapping the left backward wave `bL` to the right forward wave
`bR`. -/
abbrev lowerLeftBlock (chain : BackwardFirstChainTransform ι κ) :
    ModeTransform (BackwardWave ι) (ForwardWave κ) :=
  chain.toBlocks₂₁

/-- The lower-right chain block mapping the left forward wave `aL` to the right forward wave
`bR`. -/
abbrev lowerRightBlock (chain : BackwardFirstChainTransform ι κ) :
    ModeTransform (ForwardWave ι) (ForwardWave κ) :=
  chain.toBlocks₂₂

/-- The algebraic pivot required by the chosen incident-to-outgoing scattering presentation.

The leading block maps `bL` to `aR`. Its bijectivity is a solvability condition for this
regrouping; it does not assert invertibility, losslessness, reciprocity, or realizability of the
complete chain transform.
-/
def HasBijectiveLeadingBlock [Fintype ι] [DecidableEq ι]
    (chain : BackwardFirstChainTransform ι κ) : Prop :=
  Function.Bijective chain.leadingBlock.toLinearMap

/-- A backward-first chain transform acts by its four coupled blocks. -/
lemma toLinearMap_eq_blocks [Fintype ι] [DecidableEq ι]
    (chain : BackwardFirstChainTransform ι κ)
    (leftBackward : ModeAmplitude (BackwardWave ι))
    (leftForward : ModeAmplitude (ForwardWave ι)) :
    chain.toLinearMap (leftBackward.directSum leftForward) =
      (chain.leadingBlock.toLinearMap leftBackward +
          chain.upperRightBlock.toLinearMap leftForward).directSum
        (chain.lowerLeftBlock.toLinearMap leftBackward +
          chain.lowerRightBlock.toLinearMap leftForward) := by
  rw [← Matrix.fromBlocks_toBlocks chain]
  exact ModeTransform.fromBlocks_apply _ _ _ _ leftBackward leftForward

/-- Membership in a backward-first chain graph is exactly its two coupled block equations. -/
lemma mem_toBehavior_iff_blockEquations [Fintype ι] [DecidableEq ι]
    (chain : BackwardFirstChainTransform ι κ)
    (left : BackwardFirstTravellingWaveState ι)
    (right : BackwardFirstTravellingWaveState κ) :
    (left, right) ∈ chain.toBehavior ↔
      right.restrictInl =
          chain.leadingBlock.toLinearMap left.restrictInl +
            chain.upperRightBlock.toLinearMap left.restrictInr ∧
        right.restrictInr =
          chain.lowerLeftBlock.toLinearMap left.restrictInl +
            chain.lowerRightBlock.toLinearMap left.restrictInr := by
  rw [ModeTransform.mem_toBehavior_iff_toLinearMap, ← left.directSum_restrict,
    chain.toLinearMap_eq_blocks]
  simp only [ModeAmplitude.restrictInl_directSum, ModeAmplitude.restrictInr_directSum]
  constructor
  · intro hRight
    exact ⟨congrArg ModeAmplitude.restrictInl hRight,
      congrArg ModeAmplitude.restrictInr hRight⟩
  · rintro ⟨hBackward, hForward⟩
    rw [← right.directSum_restrict, hBackward, hForward]

/-!

## B. Leading-block inverse and scattering formula

-/

/-- The bijective leading block as a heterogeneous linear equivalence. -/
noncomputable def leadingBlockEquiv [Fintype ι] [DecidableEq ι]
    (chain : BackwardFirstChainTransform ι κ)
    (hLeading : chain.HasBijectiveLeadingBlock) :
    ModeAmplitude (BackwardWave ι) ≃ₗ[ℂ] ModeAmplitude (BackwardWave κ) :=
  LinearEquiv.ofBijective chain.leadingBlock.toLinearMap hLeading

/-- The mode-transform matrix of the inverse leading-block equivalence. -/
noncomputable def leadingBlockInverse
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (chain : BackwardFirstChainTransform ι κ)
    (hLeading : chain.HasBijectiveLeadingBlock) :
    ModeTransform (BackwardWave κ) (BackwardWave ι) :=
  Matrix.toEuclideanLin.symm (chain.leadingBlockEquiv hLeading).symm.toLinearMap

/-- The inverse leading-block matrix induces the inverse linear map. -/
@[simp]
lemma toLinearMap_leadingBlockInverse
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (chain : BackwardFirstChainTransform ι κ)
    (hLeading : chain.HasBijectiveLeadingBlock) :
    (chain.leadingBlockInverse hLeading).toLinearMap =
      (chain.leadingBlockEquiv hLeading).symm.toLinearMap :=
  Matrix.toEuclideanLin.apply_symm_apply _

/-- Applying the leading block after its inverse is the identity on right backward amplitudes. -/
lemma leadingBlock_apply_inverse
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (chain : BackwardFirstChainTransform ι κ)
    (hLeading : chain.HasBijectiveLeadingBlock)
    (amplitude : ModeAmplitude (BackwardWave κ)) :
    chain.leadingBlock.toLinearMap
        ((chain.leadingBlockInverse hLeading).toLinearMap amplitude) = amplitude := by
  rw [toLinearMap_leadingBlockInverse]
  exact (chain.leadingBlockEquiv hLeading).apply_symm_apply amplitude

/-- Applying the leading-block inverse after the leading block is the identity on left backward
amplitudes. -/
lemma inverse_apply_leadingBlock
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (chain : BackwardFirstChainTransform ι κ)
    (hLeading : chain.HasBijectiveLeadingBlock)
    (amplitude : ModeAmplitude (BackwardWave ι)) :
    (chain.leadingBlockInverse hLeading).toLinearMap
        (chain.leadingBlock.toLinearMap amplitude) = amplitude := by
  rw [toLinearMap_leadingBlockInverse]
  exact (chain.leadingBlockEquiv hLeading).symm_apply_apply amplitude

/-- The reverse block formula in direction-typed scattering coordinates `(aL, aR) ↦ (bL, bR)`. -/
noncomputable def travellingWaveScatteringBlockFormula
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (chain : BackwardFirstChainTransform ι κ)
    (hLeading : chain.HasBijectiveLeadingBlock) :
    ModeTransform (ForwardWave ι ⊕ BackwardWave κ)
      (BackwardWave ι ⊕ ForwardWave κ) :=
  Matrix.fromBlocks
    (-(chain.leadingBlockInverse hLeading * chain.upperRightBlock))
    (chain.leadingBlockInverse hLeading)
    (chain.lowerRightBlock -
      chain.lowerLeftBlock * chain.leadingBlockInverse hLeading * chain.upperRightBlock)
    (chain.lowerLeftBlock * chain.leadingBlockInverse hLeading)

/-- The reverse block formula relabeled as a typed left/right incident-to-outgoing scattering
transform. -/
noncomputable def scatteringBlockFormula
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (chain : BackwardFirstChainTransform ι κ)
    (hLeading : chain.HasBijectiveLeadingBlock) : TwoPortScatteringTransform ι κ :=
  (chain.travellingWaveScatteringBlockFormula hLeading).reindex
    TwoPortScatteringTransform.incidentTravellingWaveEquiv.symm
    TwoPortScatteringTransform.outgoingTravellingWaveEquiv.symm

/-- Returning the typed reverse block formula to travelling-wave coordinates recovers its exact
four-block matrix. -/
lemma toTravellingWaveCoordinates_scatteringBlockFormula
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (chain : BackwardFirstChainTransform ι κ)
    (hLeading : chain.HasBijectiveLeadingBlock) :
    (chain.scatteringBlockFormula hLeading).toTravellingWaveCoordinates =
      chain.travellingWaveScatteringBlockFormula hLeading :=
  ModeTransform.reindex_reindex_symm
    TwoPortScatteringTransform.incidentTravellingWaveEquiv
    TwoPortScatteringTransform.outgoingTravellingWaveEquiv
    (chain.travellingWaveScatteringBlockFormula hLeading)

/-- The reverse formula has left-reflection block `-K₁₁⁻¹ K₁₂`. -/
lemma leftReflection_scatteringBlockFormula
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (chain : BackwardFirstChainTransform ι κ)
    (hLeading : chain.HasBijectiveLeadingBlock) :
    (chain.scatteringBlockFormula hLeading).leftReflection =
      -(chain.leadingBlockInverse hLeading * chain.upperRightBlock) := by
  rw [TwoPortScatteringTransform.leftReflection,
    chain.toTravellingWaveCoordinates_scatteringBlockFormula hLeading]
  exact Matrix.toBlocks_fromBlocks₁₁ _ _ _ _

/-- The reverse formula has right-to-left transmission block `K₁₁⁻¹`. -/
lemma rightToLeftTransmission_scatteringBlockFormula
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (chain : BackwardFirstChainTransform ι κ)
    (hLeading : chain.HasBijectiveLeadingBlock) :
    (chain.scatteringBlockFormula hLeading).rightToLeftTransmission =
      chain.leadingBlockInverse hLeading := by
  rw [TwoPortScatteringTransform.rightToLeftTransmission,
    chain.toTravellingWaveCoordinates_scatteringBlockFormula hLeading]
  exact Matrix.toBlocks_fromBlocks₁₂ _ _ _ _

/-- The reverse formula has left-to-right transmission block
`K₂₂ - K₂₁ K₁₁⁻¹ K₁₂`. -/
lemma leftToRightTransmission_scatteringBlockFormula
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (chain : BackwardFirstChainTransform ι κ)
    (hLeading : chain.HasBijectiveLeadingBlock) :
    (chain.scatteringBlockFormula hLeading).leftToRightTransmission =
      chain.lowerRightBlock -
        chain.lowerLeftBlock * chain.leadingBlockInverse hLeading * chain.upperRightBlock := by
  rw [TwoPortScatteringTransform.leftToRightTransmission,
    chain.toTravellingWaveCoordinates_scatteringBlockFormula hLeading]
  exact Matrix.toBlocks_fromBlocks₂₁ _ _ _ _

/-- The reverse formula has right-reflection block `K₂₁ K₁₁⁻¹`. -/
lemma rightReflection_scatteringBlockFormula
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (chain : BackwardFirstChainTransform ι κ)
    (hLeading : chain.HasBijectiveLeadingBlock) :
    (chain.scatteringBlockFormula hLeading).rightReflection =
      chain.lowerLeftBlock * chain.leadingBlockInverse hLeading := by
  rw [TwoPortScatteringTransform.rightReflection,
    chain.toTravellingWaveCoordinates_scatteringBlockFormula hLeading]
  exact Matrix.toBlocks_fromBlocks₂₂ _ _ _ _

private lemma toLinearMap_neg_apply [Fintype ι] [DecidableEq ι]
    (transform : ModeTransform ι κ) (amplitude : ModeAmplitude ι) :
    (-transform).toLinearMap amplitude = -(transform.toLinearMap amplitude) := by
  change Matrix.toEuclideanLin (-transform) amplitude =
    -(Matrix.toEuclideanLin transform amplitude)
  rw [map_neg]
  rfl

private lemma toLinearMap_sub_apply [Fintype ι] [DecidableEq ι]
    (first second : ModeTransform ι κ) (amplitude : ModeAmplitude ι) :
    (first - second).toLinearMap amplitude =
      first.toLinearMap amplitude - second.toLinearMap amplitude := by
  change Matrix.toEuclideanLin (first - second) amplitude =
    Matrix.toEuclideanLin first amplitude - Matrix.toEuclideanLin second amplitude
  rw [map_sub]
  rfl

private lemma scatteringBlockEquations_iff_chainBlockEquations
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (chain : BackwardFirstChainTransform ι κ)
    (hLeading : chain.HasBijectiveLeadingBlock)
    (leftBackward : ModeAmplitude (BackwardWave ι))
    (leftForward : ModeAmplitude (ForwardWave ι))
    (rightBackward : ModeAmplitude (BackwardWave κ))
    (rightForward : ModeAmplitude (ForwardWave κ)) :
    (leftBackward = ModeTransform.toLinearMap
          (-(chain.leadingBlockInverse hLeading * chain.upperRightBlock)) leftForward +
        (chain.leadingBlockInverse hLeading).toLinearMap rightBackward ∧
      rightForward = ModeTransform.toLinearMap
          (chain.lowerRightBlock - chain.lowerLeftBlock *
            chain.leadingBlockInverse hLeading * chain.upperRightBlock) leftForward +
        ModeTransform.toLinearMap
          (chain.lowerLeftBlock * chain.leadingBlockInverse hLeading) rightBackward) ↔
      (rightBackward = chain.leadingBlock.toLinearMap leftBackward +
          chain.upperRightBlock.toLinearMap leftForward ∧
        rightForward = chain.lowerLeftBlock.toLinearMap leftBackward +
          chain.lowerRightBlock.toLinearMap leftForward) := by
  constructor
  · rintro ⟨hLeft, hRight⟩
    have hBackward : rightBackward = chain.leadingBlock.toLinearMap leftBackward +
        chain.upperRightBlock.toLinearMap leftForward := by
      rw [hLeft, toLinearMap_neg_apply, ModeTransform.toLinearMap_mul_apply]
      simp only [map_add, map_neg, chain.leadingBlock_apply_inverse hLeading]
      abel
    refine ⟨hBackward, ?_⟩
    rw [hRight, hLeft, toLinearMap_sub_apply, toLinearMap_neg_apply]
    simp only [ModeTransform.toLinearMap_mul_apply, map_add, map_neg]
    abel
  · rintro ⟨hBackward, hForward⟩
    have hLeft : leftBackward = ModeTransform.toLinearMap
        (-(chain.leadingBlockInverse hLeading * chain.upperRightBlock)) leftForward +
        (chain.leadingBlockInverse hLeading).toLinearMap rightBackward := by
      rw [hBackward, toLinearMap_neg_apply, ModeTransform.toLinearMap_mul_apply]
      simp only [map_add, chain.inverse_apply_leadingBlock hLeading]
      abel
    refine ⟨hLeft, ?_⟩
    rw [hForward, hLeft, toLinearMap_neg_apply, toLinearMap_sub_apply]
    simp only [ModeTransform.toLinearMap_mul_apply, map_add, map_neg]
    abel

/-- The exact reverse block formula has the original chain graph after backward-first
regrouping. -/
lemma toBackwardFirstBehavior_scatteringBlockFormula
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (chain : BackwardFirstChainTransform ι κ)
    (hLeading : chain.HasBijectiveLeadingBlock) :
    (chain.scatteringBlockFormula hLeading).toBackwardFirstBehavior = chain.toBehavior := by
  ext ⟨left, right⟩
  rw [TwoPortScatteringTransform.mem_toBackwardFirstBehavior_iff_blockEquations,
    chain.mem_toBehavior_iff_blockEquations,
    chain.leftReflection_scatteringBlockFormula hLeading,
    chain.rightToLeftTransmission_scatteringBlockFormula hLeading,
    chain.leftToRightTransmission_scatteringBlockFormula hLeading,
    chain.rightReflection_scatteringBlockFormula hLeading]
  exact scatteringBlockEquations_iff_chainBlockEquations chain hLeading
    left.restrictInl left.restrictInr right.restrictInl right.restrictInr

/-!

## C. Exact scattering-view criterion

-/

/-- Regroup the graph of a backward-first chain transform as a scattering-coordinate behavior. -/
def toScatteringBehavior [Fintype ι] (chain : BackwardFirstChainTransform ι κ) :
    TwoPortScatteringBehavior ι κ :=
  BackwardFirstTwoPortBehavior.toScattering chain.toBehavior

/-- A backward-first chain transform has a scattering view when its regrouped behavior determines
one outgoing amplitude for every incident amplitude. -/
abbrev HasScatteringView [Fintype ι] (chain : BackwardFirstChainTransform ι κ) : Prop :=
  chain.toScatteringBehavior.IsFunctional

/-- Membership in the regrouped scattering behavior is exactly the two chain-block equations on
the corresponding backward-first states. -/
lemma mem_toScatteringBehavior_iff_blockEquations
    [Fintype ι] [DecidableEq ι]
    (chain : BackwardFirstChainTransform ι κ)
    (incident : ModeAmplitude (Incident ι ⊕ Incident κ))
    (outgoing : ModeAmplitude (Outgoing ι ⊕ Outgoing κ)) :
    (incident, outgoing) ∈ chain.toScatteringBehavior ↔
      let states := scatteringBackwardFirstLinearEquiv (incident, outgoing)
      states.2.restrictInl =
          chain.leadingBlock.toLinearMap states.1.restrictInl +
            chain.upperRightBlock.toLinearMap states.1.restrictInr ∧
        states.2.restrictInr =
          chain.lowerLeftBlock.toLinearMap states.1.restrictInl +
            chain.lowerRightBlock.toLinearMap states.1.restrictInr := by
  rw [toScatteringBehavior, BackwardFirstTwoPortBehavior.mem_toScattering_iff,
    chain.mem_toBehavior_iff_blockEquations]

/-- The scattering-coordinate probe with `aL = 0`, `bL = backward`, and chain-determined
right state. -/
private def leadingBlockProbe [Fintype ι] [DecidableEq ι]
    (chain : BackwardFirstChainTransform ι κ)
    (backward : ModeAmplitude (BackwardWave ι)) :
    ModeAmplitude (Incident ι ⊕ Incident κ) ×
      ModeAmplitude (Outgoing ι ⊕ Outgoing κ) :=
  scatteringBackwardFirstLinearEquiv.symm
    (backward.directSum (0 : ModeAmplitude (ForwardWave ι)),
      (chain.leadingBlock.toLinearMap backward).directSum
        (chain.lowerLeftBlock.toLinearMap backward))

private lemma leadingBlockProbe_mem_toScatteringBehavior
    [Fintype ι] [DecidableEq ι]
    (chain : BackwardFirstChainTransform ι κ)
    (backward : ModeAmplitude (BackwardWave ι)) :
    chain.leadingBlockProbe backward ∈ chain.toScatteringBehavior := by
  rw [toScatteringBehavior, BackwardFirstTwoPortBehavior.mem_toScattering_iff]
  have hStates :
      scatteringBackwardFirstLinearEquiv (chain.leadingBlockProbe backward) =
        (backward.directSum (0 : ModeAmplitude (ForwardWave ι)),
          (chain.leadingBlock.toLinearMap backward).directSum
            (chain.lowerLeftBlock.toLinearMap backward)) := by
    exact LinearEquiv.apply_symm_apply _ _
  rw [hStates, chain.mem_toBehavior_iff_blockEquations]
  simp

private lemma leadingBlock_injective_of_hasScatteringView
    [Fintype ι] [DecidableEq ι]
    (chain : BackwardFirstChainTransform ι κ)
    (hScattering : chain.HasScatteringView) :
    Function.Injective chain.leadingBlock.toLinearMap := by
  intro first second hLeading
  let firstWaves := chain.leadingBlockProbe first
  let secondWaves := chain.leadingBlockProbe second
  have hFirst : firstWaves ∈ chain.toScatteringBehavior :=
    chain.leadingBlockProbe_mem_toScatteringBehavior first
  have hSecond : secondWaves ∈ chain.toScatteringBehavior :=
    chain.leadingBlockProbe_mem_toScatteringBehavior second
  have hIncident : firstWaves.1 = secondWaves.1 := by
    apply WithLp.ofLp_injective 2
    funext index
    rcases index with incident | incident
    · cases incident with
      | mk channel => rfl
    · cases incident with
      | mk channel =>
        exact congrArg (fun amplitude => amplitude (BackwardWave.mk channel)) hLeading
  have hSecond' : (firstWaves.1, secondWaves.2) ∈ chain.toScatteringBehavior := by
    rw [hIncident]
    exact hSecond
  have hOutgoing := hScattering.2 hFirst hSecond'
  apply WithLp.ofLp_injective 2
  funext ⟨channel⟩
  have hCoordinate := congrArg
    (fun amplitude : ModeAmplitude (Outgoing ι ⊕ Outgoing κ) =>
      amplitude (Sum.inl (Outgoing.mk channel))) hOutgoing
  simpa only [firstWaves, secondWaves, leadingBlockProbe,
    scatteringBackwardFirstLinearEquiv_symm_apply,
    ModeAmplitude.directSum_apply_inl] using hCoordinate

private lemma leadingBlock_surjective_of_hasScatteringView
    [Fintype ι] [DecidableEq ι]
    (chain : BackwardFirstChainTransform ι κ)
    (hScattering : chain.HasScatteringView) :
    Function.Surjective chain.leadingBlock.toLinearMap := by
  intro target
  let seedLeft :=
    (0 : ModeAmplitude (BackwardWave ι)).directSum (0 : ModeAmplitude (ForwardWave ι))
  let seedRight := target.directSum (0 : ModeAmplitude (ForwardWave κ))
  let incident := (scatteringBackwardFirstLinearEquiv.symm (seedLeft, seedRight)).1
  rcases hScattering.1 incident with ⟨outgoing, hMember⟩
  let states := scatteringBackwardFirstLinearEquiv (incident, outgoing)
  refine ⟨states.1.restrictInl, ?_⟩
  have hBlocks := (chain.mem_toScatteringBehavior_iff_blockEquations incident outgoing).mp hMember
  change states.2.restrictInl =
      chain.leadingBlock.toLinearMap states.1.restrictInl +
        chain.upperRightBlock.toLinearMap states.1.restrictInr ∧ _ at hBlocks
  have hLeftForward : states.1.restrictInr = 0 := by
    apply WithLp.ofLp_injective 2
    funext ⟨channel⟩
    rfl
  have hRightBackward : states.2.restrictInl = target := by
    apply WithLp.ofLp_injective 2
    funext ⟨channel⟩
    rfl
  rw [hRightBackward, hLeftForward, map_zero, add_zero] at hBlocks
  exact hBlocks.1.symm

private lemma toScatteringBehavior_isTotal_of_hasBijectiveLeadingBlock
    [Fintype ι] [DecidableEq ι]
    (chain : BackwardFirstChainTransform ι κ)
    (hLeading : chain.HasBijectiveLeadingBlock) :
    chain.toScatteringBehavior.IsTotal := by
  intro incident
  let seedStates := scatteringBackwardFirstLinearEquiv
    (incident, (0 : ModeAmplitude (Outgoing ι ⊕ Outgoing κ)))
  let leftIncident := seedStates.1.restrictInr
  let rightIncident := seedStates.2.restrictInl
  rcases hLeading.2
    (rightIncident - chain.upperRightBlock.toLinearMap leftIncident) with
    ⟨leftOutgoing, hLeftOutgoing⟩
  let rightOutgoing := chain.lowerLeftBlock.toLinearMap leftOutgoing +
    chain.lowerRightBlock.toLinearMap leftIncident
  let left := leftOutgoing.directSum leftIncident
  let right := rightIncident.directSum rightOutgoing
  let waves := scatteringBackwardFirstLinearEquiv.symm (left, right)
  have hIncident : waves.1 = incident := by
    apply WithLp.ofLp_injective 2
    funext index
    rcases index with endpoint | endpoint
    · cases endpoint
      rfl
    · cases endpoint
      rfl
  refine ⟨waves.2, ?_⟩
  rw [← hIncident, mem_toScatteringBehavior_iff_blockEquations]
  have hRoundTrip :
      scatteringBackwardFirstLinearEquiv (waves.1, waves.2) = (left, right) := by
    rw [← Prod.eta waves]
    exact LinearEquiv.apply_symm_apply _ _
  rw [hRoundTrip]
  change rightIncident =
      chain.leadingBlock.toLinearMap leftOutgoing +
        chain.upperRightBlock.toLinearMap leftIncident ∧
    rightOutgoing = chain.lowerLeftBlock.toLinearMap leftOutgoing +
      chain.lowerRightBlock.toLinearMap leftIncident
  constructor
  · rw [hLeftOutgoing]
    abel
  · rfl

private lemma leftOutgoingState_eq_of_hasBijectiveLeadingBlock
    [Fintype ι] [DecidableEq ι]
    (chain : BackwardFirstChainTransform ι κ)
    (hLeading : chain.HasBijectiveLeadingBlock)
    (incident : ModeAmplitude (Incident ι ⊕ Incident κ))
    (firstOutgoing secondOutgoing : ModeAmplitude (Outgoing ι ⊕ Outgoing κ))
    (hFirst : (incident, firstOutgoing) ∈ chain.toScatteringBehavior)
    (hSecond : (incident, secondOutgoing) ∈ chain.toScatteringBehavior) :
    (scatteringBackwardFirstLinearEquiv (incident, firstOutgoing)).1.restrictInl =
      (scatteringBackwardFirstLinearEquiv (incident, secondOutgoing)).1.restrictInl := by
  let firstStates := scatteringBackwardFirstLinearEquiv (incident, firstOutgoing)
  let secondStates := scatteringBackwardFirstLinearEquiv (incident, secondOutgoing)
  have hFirstBlocks :=
    (chain.mem_toScatteringBehavior_iff_blockEquations incident firstOutgoing).mp hFirst
  have hSecondBlocks :=
    (chain.mem_toScatteringBehavior_iff_blockEquations incident secondOutgoing).mp hSecond
  change firstStates.2.restrictInl =
      chain.leadingBlock.toLinearMap firstStates.1.restrictInl +
        chain.upperRightBlock.toLinearMap firstStates.1.restrictInr ∧ _ at hFirstBlocks
  change secondStates.2.restrictInl =
      chain.leadingBlock.toLinearMap secondStates.1.restrictInl +
        chain.upperRightBlock.toLinearMap secondStates.1.restrictInr ∧ _ at hSecondBlocks
  apply hLeading.1
  calc
    chain.leadingBlock.toLinearMap firstStates.1.restrictInl =
        firstStates.2.restrictInl -
          chain.upperRightBlock.toLinearMap firstStates.1.restrictInr := by
      rw [hFirstBlocks.1]
      abel
    _ = secondStates.2.restrictInl -
        chain.upperRightBlock.toLinearMap secondStates.1.restrictInr := rfl
    _ = chain.leadingBlock.toLinearMap secondStates.1.restrictInl := by
      rw [hSecondBlocks.1]
      abel

private lemma rightOutgoingState_eq_of_leftOutgoingState_eq
    [Fintype ι] [DecidableEq ι]
    (chain : BackwardFirstChainTransform ι κ)
    (incident : ModeAmplitude (Incident ι ⊕ Incident κ))
    (firstOutgoing secondOutgoing : ModeAmplitude (Outgoing ι ⊕ Outgoing κ))
    (hFirst : (incident, firstOutgoing) ∈ chain.toScatteringBehavior)
    (hSecond : (incident, secondOutgoing) ∈ chain.toScatteringBehavior)
    (hLeft :
      (scatteringBackwardFirstLinearEquiv (incident, firstOutgoing)).1.restrictInl =
        (scatteringBackwardFirstLinearEquiv (incident, secondOutgoing)).1.restrictInl) :
    (scatteringBackwardFirstLinearEquiv (incident, firstOutgoing)).2.restrictInr =
      (scatteringBackwardFirstLinearEquiv (incident, secondOutgoing)).2.restrictInr := by
  let firstStates := scatteringBackwardFirstLinearEquiv (incident, firstOutgoing)
  let secondStates := scatteringBackwardFirstLinearEquiv (incident, secondOutgoing)
  have hFirstBlocks :=
    (chain.mem_toScatteringBehavior_iff_blockEquations incident firstOutgoing).mp hFirst
  have hSecondBlocks :=
    (chain.mem_toScatteringBehavior_iff_blockEquations incident secondOutgoing).mp hSecond
  change _ ∧ firstStates.2.restrictInr =
      chain.lowerLeftBlock.toLinearMap firstStates.1.restrictInl +
        chain.lowerRightBlock.toLinearMap firstStates.1.restrictInr at hFirstBlocks
  change _ ∧ secondStates.2.restrictInr =
      chain.lowerLeftBlock.toLinearMap secondStates.1.restrictInl +
        chain.lowerRightBlock.toLinearMap secondStates.1.restrictInr at hSecondBlocks
  have hLeftIncident : firstStates.1.restrictInr = secondStates.1.restrictInr := rfl
  calc
    firstStates.2.restrictInr =
        chain.lowerLeftBlock.toLinearMap firstStates.1.restrictInl +
          chain.lowerRightBlock.toLinearMap firstStates.1.restrictInr := hFirstBlocks.2
    _ = chain.lowerLeftBlock.toLinearMap secondStates.1.restrictInl +
        chain.lowerRightBlock.toLinearMap secondStates.1.restrictInr := by
      rw [hLeft, hLeftIncident]
    _ = secondStates.2.restrictInr := hSecondBlocks.2.symm

private lemma toScatteringBehavior_isSingleValued_of_hasBijectiveLeadingBlock
    [Fintype ι] [DecidableEq ι]
    (chain : BackwardFirstChainTransform ι κ)
    (hLeading : chain.HasBijectiveLeadingBlock) :
    chain.toScatteringBehavior.IsSingleValued := by
  intro incident firstOutgoing secondOutgoing hFirst hSecond
  let firstStates := scatteringBackwardFirstLinearEquiv (incident, firstOutgoing)
  let secondStates := scatteringBackwardFirstLinearEquiv (incident, secondOutgoing)
  have hLeftOutgoing := chain.leftOutgoingState_eq_of_hasBijectiveLeadingBlock
    hLeading incident firstOutgoing secondOutgoing hFirst hSecond
  have hRightOutgoing := chain.rightOutgoingState_eq_of_leftOutgoingState_eq
    incident firstOutgoing secondOutgoing hFirst hSecond hLeftOutgoing
  have hLeftIncident : firstStates.1.restrictInr = secondStates.1.restrictInr := rfl
  have hRightIncident : firstStates.2.restrictInl = secondStates.2.restrictInl := rfl
  have hLeftState : firstStates.1 = secondStates.1 := by
    rw [← firstStates.1.directSum_restrict, ← secondStates.1.directSum_restrict,
      hLeftOutgoing, hLeftIncident]
  have hRightState : firstStates.2 = secondStates.2 := by
    rw [← firstStates.2.directSum_restrict, ← secondStates.2.directSum_restrict,
      hRightIncident, hRightOutgoing]
  have hStates : firstStates = secondStates := Prod.ext hLeftState hRightState
  have hWaves := congrArg scatteringBackwardFirstLinearEquiv.symm hStates
  simpa only [firstStates, secondStates, LinearEquiv.symm_apply_apply] using
    congrArg Prod.snd hWaves

/-- The regrouped chain graph has an incident-to-outgoing scattering view exactly when the
leading chain block `K₁₁ : bL → aR` is bijective. -/
lemma hasScatteringView_iff_hasBijectiveLeadingBlock
    [Fintype ι] [DecidableEq ι]
    (chain : BackwardFirstChainTransform ι κ) :
    chain.HasScatteringView ↔ chain.HasBijectiveLeadingBlock :=
  ⟨fun hScattering =>
    ⟨leadingBlock_injective_of_hasScatteringView chain hScattering,
      leadingBlock_surjective_of_hasScatteringView chain hScattering⟩,
    fun hLeading =>
      ⟨toScatteringBehavior_isTotal_of_hasBijectiveLeadingBlock chain hLeading,
        toScatteringBehavior_isSingleValued_of_hasBijectiveLeadingBlock chain hLeading⟩⟩

/-- The reverse block formula has exactly the chain transform's regrouped scattering behavior. -/
lemma toBehavior_scatteringBlockFormula
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (chain : BackwardFirstChainTransform ι κ)
    (hLeading : chain.HasBijectiveLeadingBlock) :
    (chain.scatteringBlockFormula hLeading).toBehavior = chain.toScatteringBehavior := by
  calc
    (chain.scatteringBlockFormula hLeading).toBehavior =
        (chain.scatteringBlockFormula hLeading).toBackwardFirstBehavior.toScattering := by
      rw [TwoPortScatteringTransform.toBackwardFirstBehavior,
        TwoPortScatteringBehavior.toScattering_toBackwardFirst]
    _ = BackwardFirstTwoPortBehavior.toScattering chain.toBehavior :=
      congrArg BackwardFirstTwoPortBehavior.toScattering
        (chain.toBackwardFirstBehavior_scatteringBlockFormula hLeading)
    _ = chain.toScatteringBehavior := rfl

/-!

## D. Behavior-derived scattering conversion

-/

/-- The typed two-port scattering transform derived from a backward-first chain behavior under
the exact leading-block hypothesis. -/
noncomputable def toTwoPortScatteringTransform
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (chain : BackwardFirstChainTransform ι κ)
    (hLeading : chain.HasBijectiveLeadingBlock) : TwoPortScatteringTransform ι κ :=
  chain.toScatteringBehavior.toModeTransform
    ((chain.hasScatteringView_iff_hasBijectiveLeadingBlock).2 hLeading)

/-- The behavior-derived chain-to-scattering conversion recovers the regrouped chain behavior
exactly. -/
@[simp]
lemma toBehavior_toTwoPortScatteringTransform
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (chain : BackwardFirstChainTransform ι κ)
    (hLeading : chain.HasBijectiveLeadingBlock) :
    (chain.toTwoPortScatteringTransform hLeading).toBehavior =
      chain.toScatteringBehavior :=
  LinearBehavior.toBehavior_toModeTransform _ _

/-- The behavior-derived chain-to-scattering conversion equals the exact four-block formula. -/
lemma toTwoPortScatteringTransform_eq_blockFormula
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (chain : BackwardFirstChainTransform ι κ)
    (hLeading : chain.HasBijectiveLeadingBlock) :
    chain.toTwoPortScatteringTransform hLeading = chain.scatteringBlockFormula hLeading :=
  LinearBehavior.toModeTransform_unique chain.toScatteringBehavior
    ((chain.hasScatteringView_iff_hasBijectiveLeadingBlock).2 hLeading)
    (chain.scatteringBlockFormula hLeading)
    (chain.toBehavior_scatteringBlockFormula hLeading)

/-- Regrouping the behavior-derived scattering transform returns the original chain graph. -/
@[simp]
lemma toBackwardFirstBehavior_toTwoPortScatteringTransform
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (chain : BackwardFirstChainTransform ι κ)
    (hLeading : chain.HasBijectiveLeadingBlock) :
    (chain.toTwoPortScatteringTransform hLeading).toBackwardFirstBehavior =
      chain.toBehavior := by
  rw [TwoPortScatteringTransform.toBackwardFirstBehavior,
    chain.toBehavior_toTwoPortScatteringTransform hLeading,
    toScatteringBehavior, BackwardFirstTwoPortBehavior.toBackwardFirst_toScattering]

/-!

## E. Behavioral and matrix round trips

-/

/-- The right-to-left transmission block produced by reverse conversion is the inverse leading
chain block. -/
lemma rightToLeftTransmission_toTwoPortScatteringTransform
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (chain : BackwardFirstChainTransform ι κ)
    (hLeading : chain.HasBijectiveLeadingBlock) :
    (chain.toTwoPortScatteringTransform hLeading).rightToLeftTransmission =
      chain.leadingBlockInverse hLeading := by
  rw [chain.toTwoPortScatteringTransform_eq_blockFormula hLeading,
    chain.rightToLeftTransmission_scatteringBlockFormula hLeading]

/-- Reverse conversion transports leading-block bijectivity to bijectivity of the resulting
right-to-left scattering transmission block. -/
lemma hasBijectiveRightToLeftTransmission_toTwoPortScatteringTransform
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (chain : BackwardFirstChainTransform ι κ)
    (hLeading : chain.HasBijectiveLeadingBlock) :
    (chain.toTwoPortScatteringTransform hLeading).HasBijectiveRightToLeftTransmission := by
  rw [TwoPortScatteringTransform.HasBijectiveRightToLeftTransmission,
    chain.rightToLeftTransmission_toTwoPortScatteringTransform hLeading,
    chain.toLinearMap_leadingBlockInverse hLeading]
  exact (chain.leadingBlockEquiv hLeading).symm.bijective

/-- Converting a chain transform to scattering and back recovers the chain transform for any
proof of the transported scattering pivot hypothesis. -/
lemma toBackwardFirstChainTransform_toTwoPortScatteringTransform
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (chain : BackwardFirstChainTransform ι κ)
    (hLeading : chain.HasBijectiveLeadingBlock)
    (hTransmission :
      (chain.toTwoPortScatteringTransform hLeading).HasBijectiveRightToLeftTransmission) :
    (chain.toTwoPortScatteringTransform hLeading).toBackwardFirstChainTransform hTransmission =
      chain := by
  apply ModeTransform.toBehavior_injective
  rw [TwoPortScatteringTransform.toBehavior_toBackwardFirstChainTransform,
    chain.toBackwardFirstBehavior_toTwoPortScatteringTransform hLeading]

end BackwardFirstChainTransform

namespace TwoPortScatteringTransform

variable {ι : Type u} {κ : Type v}

/-- The leading block produced by scattering-to-chain conversion is the inverse right-to-left
transmission block. -/
lemma leadingBlock_toBackwardFirstChainTransform
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (scattering : TwoPortScatteringTransform ι κ)
    (hTransmission : scattering.HasBijectiveRightToLeftTransmission) :
    (scattering.toBackwardFirstChainTransform hTransmission).leadingBlock =
      scattering.rightToLeftTransmissionInverse hTransmission := by
  rw [scattering.toBackwardFirstChainTransform_eq_blockFormula hTransmission]
  unfold backwardFirstChainBlockFormula
  exact Matrix.toBlocks_fromBlocks₁₁ _ _ _ _

/-- Scattering-to-chain conversion transports transmission-block bijectivity to bijectivity of
the resulting leading chain block. -/
lemma hasBijectiveLeadingBlock_toBackwardFirstChainTransform
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (scattering : TwoPortScatteringTransform ι κ)
    (hTransmission : scattering.HasBijectiveRightToLeftTransmission) :
    (scattering.toBackwardFirstChainTransform hTransmission).HasBijectiveLeadingBlock := by
  rw [BackwardFirstChainTransform.HasBijectiveLeadingBlock,
    scattering.leadingBlock_toBackwardFirstChainTransform hTransmission,
    scattering.toLinearMap_rightToLeftTransmissionInverse hTransmission]
  exact (scattering.rightToLeftTransmissionEquiv hTransmission).symm.bijective

/-- Regrouping the behavior-derived chain transform back to scattering coordinates recovers the
original scattering graph. -/
@[simp]
lemma toScatteringBehavior_toBackwardFirstChainTransform
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (scattering : TwoPortScatteringTransform ι κ)
    (hTransmission : scattering.HasBijectiveRightToLeftTransmission) :
    (scattering.toBackwardFirstChainTransform hTransmission).toScatteringBehavior =
      scattering.toBehavior := by
  rw [BackwardFirstChainTransform.toScatteringBehavior,
    scattering.toBehavior_toBackwardFirstChainTransform hTransmission,
    toBackwardFirstBehavior, TwoPortScatteringBehavior.toScattering_toBackwardFirst]

/-- Converting a scattering transform to a chain transform and back recovers the scattering
transform for any proof of the transported leading-block hypothesis. -/
lemma toTwoPortScatteringTransform_toBackwardFirstChainTransform
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (scattering : TwoPortScatteringTransform ι κ)
    (hTransmission : scattering.HasBijectiveRightToLeftTransmission)
    (hLeading :
      (scattering.toBackwardFirstChainTransform hTransmission).HasBijectiveLeadingBlock) :
    (scattering.toBackwardFirstChainTransform hTransmission).toTwoPortScatteringTransform
        hLeading = scattering := by
  apply ModeTransform.toBehavior_injective
  rw [BackwardFirstChainTransform.toBehavior_toTwoPortScatteringTransform,
    scattering.toScatteringBehavior_toBackwardFirstChainTransform hTransmission]

end TwoPortScatteringTransform

end

end Optics
