/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.TwoPortChain
public import Physlib.Optics.Network.TwoPortScattering

/-!
# Two-port scattering-to-chain conversion

## i. Overview

A typed two-port scattering transform maps incident `(aL, aR)` amplitudes to outgoing `(bL, bR)`
amplitudes. This file reindexes those coordinates by propagation direction and proves that the
regrouped behavior determines `(aR, bR)` uniquely from `(bL, aL)` exactly when the
right-incident-to-left-outgoing transmission block is bijective.

Under that exact block hypothesis, the public chain transform is extracted from the functional
behavior. Its four-block formula is then proved as a derived representation. No inverse of the
full scattering matrix is used.

## ii. Key results

- `TwoPortScatteringTransform.toTravellingWaveCoordinates`: direction-typed scattering
  coordinates.
- `TwoPortScatteringTransform.rightToLeftTransmission`: the exact chain-view pivot block.
- `TwoPortScatteringTransform.mem_toBackwardFirstBehavior_iff_blockEquations`: the two scattering
  equations in backward-first variables.
- `TwoPortScatteringTransform.hasLeftToRightChainView_iff_rightToLeftTransmission_bijective`: the
  exact solvability criterion.
- `TwoPortScatteringTransform.toBackwardFirstChainTransform`: behavior-derived conversion.
- `TwoPortScatteringTransform.toBackwardFirstChainTransform_eq_blockFormula`: the exact block
  formula.

## iii. Table of contents

- A. Direction-typed scattering blocks
- B. Backward-first block equations
- C. Exact chain-view criterion
- D. Pivot inverse and block formula
- E. Behavior-derived chain conversion

## iv. References

Rows of the scattering transform are `(bL, bR)` and columns are `(aL, aR)`. Backward-first chain
states satisfy `(aR, bR) = K (bL, aL)`. Therefore the pivot is scattering block `₁₂`, and the
bottom-right chain block is `Tlr - Rr * Trl⁻¹ * Rl` in precisely that order.

These are fixed-frequency complex-linear semantics. No losslessness, passivity, reciprocity,
causality, reference-plane transport, termination, or electromagnetic realization is inferred.

-/

@[expose] public section

namespace Optics

noncomputable section

universe u v

namespace TwoPortScatteringTransform

variable {ι : Type u} {κ : Type v}

/-!

## A. Direction-typed scattering blocks

-/

/-- The endpoint relabeling from left/right incident channels `(aL, aR)` to their corresponding
forward/backward travelling-wave channels. -/
def incidentTravellingWaveEquiv :
    Incident ι ⊕ Incident κ ≃ ForwardWave ι ⊕ BackwardWave κ :=
  (Incident.channelEquiv.trans ForwardWave.channelEquiv.symm).sumCongr
    (Incident.channelEquiv.trans BackwardWave.channelEquiv.symm)

/-- The endpoint relabeling from left/right outgoing channels `(bL, bR)` to their corresponding
backward/forward travelling-wave channels. -/
def outgoingTravellingWaveEquiv :
    Outgoing ι ⊕ Outgoing κ ≃ BackwardWave ι ⊕ ForwardWave κ :=
  (Outgoing.channelEquiv.trans BackwardWave.channelEquiv.symm).sumCongr
    (Outgoing.channelEquiv.trans ForwardWave.channelEquiv.symm)

/-- Relabel scattering coordinates by the propagation direction of every two-port wave. -/
def toTravellingWaveCoordinates (scattering : TwoPortScatteringTransform ι κ) :
    ModeTransform (ForwardWave ι ⊕ BackwardWave κ)
      (BackwardWave ι ⊕ ForwardWave κ) :=
  scattering.reindex incidentTravellingWaveEquiv outgoingTravellingWaveEquiv

/-- The block mapping left-incident forward waves to left-outgoing backward waves. -/
abbrev leftReflection (scattering : TwoPortScatteringTransform ι κ) :
    ModeTransform (ForwardWave ι) (BackwardWave ι) :=
  scattering.toTravellingWaveCoordinates.toBlocks₁₁

/-- The block mapping right-incident backward waves to left-outgoing backward waves. -/
abbrev rightToLeftTransmission (scattering : TwoPortScatteringTransform ι κ) :
    ModeTransform (BackwardWave κ) (BackwardWave ι) :=
  scattering.toTravellingWaveCoordinates.toBlocks₁₂

/-- The block mapping left-incident forward waves to right-outgoing forward waves. -/
abbrev leftToRightTransmission (scattering : TwoPortScatteringTransform ι κ) :
    ModeTransform (ForwardWave ι) (ForwardWave κ) :=
  scattering.toTravellingWaveCoordinates.toBlocks₂₁

/-- The block mapping right-incident backward waves to right-outgoing forward waves. -/
abbrev rightReflection (scattering : TwoPortScatteringTransform ι κ) :
    ModeTransform (BackwardWave κ) (ForwardWave κ) :=
  scattering.toTravellingWaveCoordinates.toBlocks₂₂

/-- The left-reflection block retains its corresponding typed scattering entry. -/
@[simp]
lemma leftReflection_apply (scattering : TwoPortScatteringTransform ι κ)
    (output input : ι) :
    scattering.leftReflection ⟨output⟩ ⟨input⟩ =
      scattering (Sum.inl ⟨output⟩) (Sum.inl ⟨input⟩) := rfl

/-- The right-to-left transmission block retains its corresponding typed scattering entry. -/
@[simp]
lemma rightToLeftTransmission_apply (scattering : TwoPortScatteringTransform ι κ)
    (output : ι) (input : κ) :
    scattering.rightToLeftTransmission ⟨output⟩ ⟨input⟩ =
      scattering (Sum.inl ⟨output⟩) (Sum.inr ⟨input⟩) := rfl

/-- The left-to-right transmission block retains its corresponding typed scattering entry. -/
@[simp]
lemma leftToRightTransmission_apply (scattering : TwoPortScatteringTransform ι κ)
    (output : κ) (input : ι) :
    scattering.leftToRightTransmission ⟨output⟩ ⟨input⟩ =
      scattering (Sum.inr ⟨output⟩) (Sum.inl ⟨input⟩) := rfl

/-- The right-reflection block retains its corresponding typed scattering entry. -/
@[simp]
lemma rightReflection_apply (scattering : TwoPortScatteringTransform ι κ)
    (output input : κ) :
    scattering.rightReflection ⟨output⟩ ⟨input⟩ =
      scattering (Sum.inr ⟨output⟩) (Sum.inr ⟨input⟩) := rfl

/-- The algebraic pivot required by the chosen backward-first left-to-right chain presentation.

Equivalently, the block mapping right-incident waves to left-outgoing waves is bijective. This is a
solvability condition for this coordinate presentation; it does not assert invertibility,
losslessness, reciprocity, or realizability of the full scattering transform.
-/
def HasBijectiveRightToLeftTransmission [Fintype κ] [DecidableEq κ]
    (scattering : TwoPortScatteringTransform ι κ) : Prop :=
  Function.Bijective scattering.rightToLeftTransmission.toLinearMap

/-- The direction-typed scattering transform acts by its four coupled blocks. -/
lemma toLinearMap_toTravellingWaveCoordinates [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (scattering : TwoPortScatteringTransform ι κ)
    (leftIncident : ModeAmplitude (ForwardWave ι))
    (rightIncident : ModeAmplitude (BackwardWave κ)) :
    scattering.toTravellingWaveCoordinates.toLinearMap
        (leftIncident.directSum rightIncident) =
      (scattering.leftReflection.toLinearMap leftIncident +
          scattering.rightToLeftTransmission.toLinearMap rightIncident).directSum
        (scattering.leftToRightTransmission.toLinearMap leftIncident +
          scattering.rightReflection.toLinearMap rightIncident) := by
  rw [← Matrix.fromBlocks_toBlocks scattering.toTravellingWaveCoordinates]
  exact ModeTransform.fromBlocks_apply _ _ _ _ leftIncident rightIncident

/-!

## B. Backward-first block equations

-/

/-- The backward-first behavior obtained by graphing and regrouping a typed two-port scattering
transform. -/
def toBackwardFirstBehavior [Fintype ι] [Fintype κ]
    (scattering : TwoPortScatteringTransform ι κ) :
    BackwardFirstTwoPortBehavior ι κ :=
  TwoPortScatteringBehavior.toBackwardFirst
    (scattering.toBehavior : TwoPortScatteringBehavior ι κ)

/-- Backward-first membership is the direction-typed scattering graph equation before splitting
it into its two output blocks. -/
lemma mem_toBackwardFirstBehavior_iff_eq_toTravellingWaveCoordinates
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (scattering : TwoPortScatteringTransform ι κ)
    (left : BackwardFirstTravellingWaveState ι)
    (right : BackwardFirstTravellingWaveState κ) :
    (left, right) ∈ scattering.toBackwardFirstBehavior ↔
      left.restrictInl.directSum right.restrictInr =
        scattering.toTravellingWaveCoordinates.toLinearMap
          (left.restrictInr.directSum right.restrictInl) := by
  let scatteringPair := scatteringBackwardFirstLinearEquiv.symm (left, right)
  let incident := scatteringPair.1
  let outgoing := scatteringPair.2
  have hIncident :
      ModeAmplitude.reindex incidentTravellingWaveEquiv incident =
        left.restrictInr.directSum right.restrictInl := by
    apply WithLp.ofLp_injective 2
    funext index
    rcases index with ⟨index⟩ | ⟨index⟩ <;> rfl
  have hOutgoing :
      ModeAmplitude.reindex outgoingTravellingWaveEquiv outgoing =
        left.restrictInl.directSum right.restrictInr := by
    apply WithLp.ofLp_injective 2
    funext index
    rcases index with ⟨index⟩ | ⟨index⟩ <;> rfl
  rw [toBackwardFirstBehavior, TwoPortScatteringBehavior.mem_toBackwardFirst_iff,
    ModeTransform.mem_toBehavior_iff_toLinearMap]
  change outgoing = scattering.toLinearMap incident ↔ _
  constructor
  · intro hScattering
    calc
      left.restrictInl.directSum right.restrictInr =
          ModeAmplitude.reindex outgoingTravellingWaveEquiv outgoing := hOutgoing.symm
      _ = ModeAmplitude.reindex outgoingTravellingWaveEquiv
          (scattering.toLinearMap incident) := congrArg _ hScattering
      _ = scattering.toTravellingWaveCoordinates.toLinearMap
          (ModeAmplitude.reindex incidentTravellingWaveEquiv incident) :=
        (ModeTransform.toLinearMap_reindex_apply incidentTravellingWaveEquiv
          outgoingTravellingWaveEquiv scattering incident).symm
      _ = scattering.toTravellingWaveCoordinates.toLinearMap
          (left.restrictInr.directSum right.restrictInl) := congrArg _ hIncident
  · intro hScattering
    apply (ModeAmplitude.reindex outgoingTravellingWaveEquiv).injective
    calc
      ModeAmplitude.reindex outgoingTravellingWaveEquiv outgoing =
          left.restrictInl.directSum right.restrictInr := hOutgoing
      _ = scattering.toTravellingWaveCoordinates.toLinearMap
          (left.restrictInr.directSum right.restrictInl) := hScattering
      _ = scattering.toTravellingWaveCoordinates.toLinearMap
          (ModeAmplitude.reindex incidentTravellingWaveEquiv incident) := congrArg _ hIncident.symm
      _ = ModeAmplitude.reindex outgoingTravellingWaveEquiv
          (scattering.toLinearMap incident) :=
        ModeTransform.toLinearMap_reindex_apply incidentTravellingWaveEquiv
          outgoingTravellingWaveEquiv scattering incident

/-- A backward-first pair satisfies a scattering graph exactly when its four waves satisfy the two
direction-typed block equations. -/
lemma mem_toBackwardFirstBehavior_iff_blockEquations
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (scattering : TwoPortScatteringTransform ι κ)
    (left : BackwardFirstTravellingWaveState ι)
    (right : BackwardFirstTravellingWaveState κ) :
    (left, right) ∈ scattering.toBackwardFirstBehavior ↔
      left.restrictInl =
          scattering.leftReflection.toLinearMap left.restrictInr +
            scattering.rightToLeftTransmission.toLinearMap right.restrictInl ∧
        right.restrictInr =
          scattering.leftToRightTransmission.toLinearMap left.restrictInr +
            scattering.rightReflection.toLinearMap right.restrictInl := by
  rw [mem_toBackwardFirstBehavior_iff_eq_toTravellingWaveCoordinates,
    toLinearMap_toTravellingWaveCoordinates]
  constructor
  · intro hBlocks
    exact ⟨congrArg ModeAmplitude.restrictInl hBlocks,
      congrArg ModeAmplitude.restrictInr hBlocks⟩
  · rintro ⟨hLeft, hRight⟩
    exact congrArg₂ ModeAmplitude.directSum hLeft hRight

/-!

## C. Exact chain-view criterion

-/

private lemma rightToLeftTransmission_bijective_of_hasLeftToRightChainView
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (scattering : TwoPortScatteringTransform ι κ)
    (hChain : scattering.toBackwardFirstBehavior.HasLeftToRightChainView) :
    scattering.HasBijectiveRightToLeftTransmission := by
  constructor
  · intro first second hTransmission
    let left :=
      (scattering.rightToLeftTransmission.toLinearMap first).directSum
        (0 : ModeAmplitude (ForwardWave ι))
    let firstRight := first.directSum
      (scattering.rightReflection.toLinearMap first)
    let secondRight := second.directSum
      (scattering.rightReflection.toLinearMap second)
    have hFirst : (left, firstRight) ∈ scattering.toBackwardFirstBehavior := by
      rw [mem_toBackwardFirstBehavior_iff_blockEquations]
      simp [left, firstRight]
    have hSecond : (left, secondRight) ∈ scattering.toBackwardFirstBehavior := by
      rw [mem_toBackwardFirstBehavior_iff_blockEquations]
      simp [left, secondRight, hTransmission]
    have hRight := hChain.2 hFirst hSecond
    exact congrArg ModeAmplitude.restrictInl hRight
  · intro leftOutgoing
    let left := leftOutgoing.directSum (0 : ModeAmplitude (ForwardWave ι))
    rcases hChain.1 left with ⟨right, hRight⟩
    refine ⟨right.restrictInl, ?_⟩
    have hBlocks :=
      (mem_toBackwardFirstBehavior_iff_blockEquations scattering left right).mp hRight
    simpa [left] using hBlocks.1.symm

private lemma hasLeftToRightChainView_of_rightToLeftTransmission_bijective
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (scattering : TwoPortScatteringTransform ι κ)
    (hTransmission : scattering.HasBijectiveRightToLeftTransmission) :
    scattering.toBackwardFirstBehavior.HasLeftToRightChainView := by
  constructor
  · intro left
    rcases hTransmission.2
      (left.restrictInl - scattering.leftReflection.toLinearMap left.restrictInr) with
      ⟨rightIncident, hRightIncident⟩
    let right := rightIncident.directSum
      (scattering.leftToRightTransmission.toLinearMap left.restrictInr +
        scattering.rightReflection.toLinearMap rightIncident)
    refine ⟨right, (mem_toBackwardFirstBehavior_iff_blockEquations
      scattering left right).mpr ?_⟩
    constructor
    · simp only [right, ModeAmplitude.restrictInl_directSum]
      rw [hRightIncident]
      abel
    · simp [right]
  · intro left firstRight secondRight hFirst hSecond
    have hFirstBlocks :=
      (mem_toBackwardFirstBehavior_iff_blockEquations scattering left firstRight).mp hFirst
    have hSecondBlocks :=
      (mem_toBackwardFirstBehavior_iff_blockEquations scattering left secondRight).mp hSecond
    have hTransmissionEq :
        scattering.rightToLeftTransmission.toLinearMap firstRight.restrictInl =
          scattering.rightToLeftTransmission.toLinearMap secondRight.restrictInl :=
      add_left_cancel (hFirstBlocks.1.symm.trans hSecondBlocks.1)
    have hBackward := hTransmission.1 hTransmissionEq
    have hForward : firstRight.restrictInr = secondRight.restrictInr := by
      calc
        firstRight.restrictInr =
            scattering.leftToRightTransmission.toLinearMap left.restrictInr +
              scattering.rightReflection.toLinearMap firstRight.restrictInl := hFirstBlocks.2
        _ = scattering.leftToRightTransmission.toLinearMap left.restrictInr +
              scattering.rightReflection.toLinearMap secondRight.restrictInl := by rw [hBackward]
        _ = secondRight.restrictInr := hSecondBlocks.2.symm
    rw [← firstRight.directSum_restrict, ← secondRight.directSum_restrict,
      hBackward, hForward]

/-- The regrouped scattering behavior has a left-to-right chain view exactly when the
right-incident-to-left-outgoing transmission block is bijective. -/
lemma hasLeftToRightChainView_iff_rightToLeftTransmission_bijective
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (scattering : TwoPortScatteringTransform ι κ) :
    scattering.toBackwardFirstBehavior.HasLeftToRightChainView ↔
      scattering.HasBijectiveRightToLeftTransmission :=
  ⟨rightToLeftTransmission_bijective_of_hasLeftToRightChainView scattering,
    hasLeftToRightChainView_of_rightToLeftTransmission_bijective scattering⟩

/-!

## D. Pivot inverse and block formula

-/

/-- The bijective right-to-left transmission block as a heterogeneous linear equivalence. -/
noncomputable def rightToLeftTransmissionEquiv [Fintype κ] [DecidableEq κ]
    (scattering : TwoPortScatteringTransform ι κ)
    (hTransmission : scattering.HasBijectiveRightToLeftTransmission) :
    ModeAmplitude (BackwardWave κ) ≃ₗ[ℂ] ModeAmplitude (BackwardWave ι) :=
  LinearEquiv.ofBijective scattering.rightToLeftTransmission.toLinearMap hTransmission

/-- The mode-transform matrix of the inverse right-to-left transmission equivalence. -/
noncomputable def rightToLeftTransmissionInverse
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (scattering : TwoPortScatteringTransform ι κ)
    (hTransmission : scattering.HasBijectiveRightToLeftTransmission) :
    ModeTransform (BackwardWave ι) (BackwardWave κ) :=
  Matrix.toEuclideanLin.symm
    (scattering.rightToLeftTransmissionEquiv hTransmission).symm.toLinearMap

/-- The inverse transmission matrix induces the inverse linear map. -/
@[simp]
lemma toLinearMap_rightToLeftTransmissionInverse
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (scattering : TwoPortScatteringTransform ι κ)
    (hTransmission : scattering.HasBijectiveRightToLeftTransmission) :
    (scattering.rightToLeftTransmissionInverse hTransmission).toLinearMap =
      (scattering.rightToLeftTransmissionEquiv hTransmission).symm.toLinearMap :=
  Matrix.toEuclideanLin.apply_symm_apply _

/-- Applying the pivot after its inverse is the identity on left-outgoing backward amplitudes. -/
lemma rightToLeftTransmission_apply_inverse
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (scattering : TwoPortScatteringTransform ι κ)
    (hTransmission : scattering.HasBijectiveRightToLeftTransmission)
    (amplitude : ModeAmplitude (BackwardWave ι)) :
    scattering.rightToLeftTransmission.toLinearMap
        ((scattering.rightToLeftTransmissionInverse hTransmission).toLinearMap amplitude) =
      amplitude := by
  rw [toLinearMap_rightToLeftTransmissionInverse]
  exact (scattering.rightToLeftTransmissionEquiv hTransmission).apply_symm_apply amplitude

/-- Applying the pivot inverse after the pivot is the identity on right-incident backward
amplitudes. -/
lemma inverse_apply_rightToLeftTransmission
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (scattering : TwoPortScatteringTransform ι κ)
    (hTransmission : scattering.HasBijectiveRightToLeftTransmission)
    (amplitude : ModeAmplitude (BackwardWave κ)) :
    (scattering.rightToLeftTransmissionInverse hTransmission).toLinearMap
        (scattering.rightToLeftTransmission.toLinearMap amplitude) = amplitude := by
  rw [toLinearMap_rightToLeftTransmissionInverse]
  exact (scattering.rightToLeftTransmissionEquiv hTransmission).symm_apply_apply amplitude

/-- The transmission block followed by its inverse matrix is the identity. -/
lemma rightToLeftTransmission_mul_inverse
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (scattering : TwoPortScatteringTransform ι κ)
    (hTransmission : scattering.HasBijectiveRightToLeftTransmission) :
    scattering.rightToLeftTransmission *
        scattering.rightToLeftTransmissionInverse hTransmission = 1 := by
  apply Matrix.toEuclideanLin.injective
  rw [Matrix.toLpLin_mul_same, Matrix.toLpLin_one]
  apply LinearMap.ext
  intro amplitude
  exact scattering.rightToLeftTransmission_apply_inverse hTransmission amplitude

/-- The inverse transmission matrix followed by the transmission block is the identity. -/
lemma inverse_mul_rightToLeftTransmission
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (scattering : TwoPortScatteringTransform ι κ)
    (hTransmission : scattering.HasBijectiveRightToLeftTransmission) :
    scattering.rightToLeftTransmissionInverse hTransmission *
        scattering.rightToLeftTransmission = 1 := by
  apply Matrix.toEuclideanLin.injective
  rw [Matrix.toLpLin_mul_same, Matrix.toLpLin_one]
  apply LinearMap.ext
  intro amplitude
  exact scattering.inverse_apply_rightToLeftTransmission hTransmission amplitude

/-- The backward-first chain matrix obtained by solving only the bijective right-to-left
transmission block. -/
noncomputable def backwardFirstChainBlockFormula
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (scattering : TwoPortScatteringTransform ι κ)
    (hTransmission : scattering.HasBijectiveRightToLeftTransmission) :
    BackwardFirstChainTransform ι κ :=
  let inverseTransmission := scattering.rightToLeftTransmissionInverse hTransmission
  Matrix.fromBlocks inverseTransmission
    (-(inverseTransmission * scattering.leftReflection))
    (scattering.rightReflection * inverseTransmission)
    (scattering.leftToRightTransmission -
      scattering.rightReflection * inverseTransmission * scattering.leftReflection)

/-- The chain block formula maps `(bL, aL)` to the solution `(aR, bR)` obtained by the pivot
inverse and the second scattering equation. -/
lemma toLinearMap_backwardFirstChainBlockFormula
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (scattering : TwoPortScatteringTransform ι κ)
    (hTransmission : scattering.HasBijectiveRightToLeftTransmission)
    (left : BackwardFirstTravellingWaveState ι) :
    (scattering.backwardFirstChainBlockFormula hTransmission).toLinearMap left =
      let rightIncident :=
        (scattering.rightToLeftTransmissionInverse hTransmission).toLinearMap
          (left.restrictInl - scattering.leftReflection.toLinearMap left.restrictInr)
      rightIncident.directSum
        (scattering.leftToRightTransmission.toLinearMap left.restrictInr +
          scattering.rightReflection.toLinearMap rightIncident) := by
  rw [← left.directSum_restrict]
  unfold backwardFirstChainBlockFormula
  rw [ModeTransform.fromBlocks_apply]
  simp only [ModeTransform.toLinearMap, Matrix.toLpLin_mul_same, LinearMap.comp_apply,
    map_neg, map_sub, LinearMap.neg_apply, LinearMap.sub_apply,
    ModeAmplitude.restrictInl_directSum, ModeAmplitude.restrictInr_directSum]
  apply congrArg₂ ModeAmplitude.directSum
  all_goals module

/-- The exact block formula has the same graph as the original scattering behavior regrouped into
backward-first states. -/
lemma toBehavior_backwardFirstChainBlockFormula
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (scattering : TwoPortScatteringTransform ι κ)
    (hTransmission : scattering.HasBijectiveRightToLeftTransmission) :
    (scattering.backwardFirstChainBlockFormula hTransmission).toBehavior =
      scattering.toBackwardFirstBehavior := by
  ext ⟨left, right⟩
  rw [ModeTransform.mem_toBehavior_iff_toLinearMap,
    mem_toBackwardFirstBehavior_iff_blockEquations,
    toLinearMap_backwardFirstChainBlockFormula]
  let rightIncident :=
    (scattering.rightToLeftTransmissionInverse hTransmission).toLinearMap
      (left.restrictInl - scattering.leftReflection.toLinearMap left.restrictInr)
  constructor
  · intro hRight
    have hBackward := congrArg ModeAmplitude.restrictInl hRight
    have hForward := congrArg ModeAmplitude.restrictInr hRight
    change right.restrictInl = rightIncident at hBackward
    change right.restrictInr =
      scattering.leftToRightTransmission.toLinearMap left.restrictInr +
        scattering.rightReflection.toLinearMap rightIncident at hForward
    constructor
    · rw [hBackward]
      change left.restrictInl = scattering.leftReflection.toLinearMap left.restrictInr +
        scattering.rightToLeftTransmission.toLinearMap
          ((scattering.rightToLeftTransmissionInverse hTransmission).toLinearMap
            (left.restrictInl -
              scattering.leftReflection.toLinearMap left.restrictInr))
      rw [scattering.rightToLeftTransmission_apply_inverse hTransmission]
      abel
    · simpa only [hBackward] using hForward
  · rintro ⟨hLeft, hRight⟩
    have hBackward : right.restrictInl = rightIncident := by
      change right.restrictInl =
        (scattering.rightToLeftTransmissionInverse hTransmission).toLinearMap
          (left.restrictInl - scattering.leftReflection.toLinearMap left.restrictInr)
      rw [← scattering.inverse_apply_rightToLeftTransmission
        hTransmission right.restrictInl]
      congr 1
      rw [hLeft]
      abel
    have hForward : right.restrictInr =
        scattering.leftToRightTransmission.toLinearMap left.restrictInr +
          scattering.rightReflection.toLinearMap rightIncident := by
      simpa only [hBackward] using hRight
    rw [← right.directSum_restrict, hBackward, hForward]

/-!

## E. Behavior-derived chain conversion

-/

/-- The backward-first chain transform derived from a scattering behavior under the exact
right-to-left transmission-block hypothesis. -/
noncomputable def toBackwardFirstChainTransform
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (scattering : TwoPortScatteringTransform ι κ)
    (hTransmission : scattering.HasBijectiveRightToLeftTransmission) :
    BackwardFirstChainTransform ι κ :=
  scattering.toBackwardFirstBehavior.leftToRightChainTransform
    ((scattering.hasLeftToRightChainView_iff_rightToLeftTransmission_bijective).2 hTransmission)

/-- The behavior-derived scattering-to-chain conversion recovers the regrouped scattering
behavior exactly. -/
@[simp]
lemma toBehavior_toBackwardFirstChainTransform
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (scattering : TwoPortScatteringTransform ι κ)
    (hTransmission : scattering.HasBijectiveRightToLeftTransmission) :
    (scattering.toBackwardFirstChainTransform hTransmission).toBehavior =
      scattering.toBackwardFirstBehavior :=
  BackwardFirstTwoPortBehavior.toBehavior_leftToRightChainTransform _ _

/-- The behavior-derived scattering-to-chain conversion equals the exact four-block formula. -/
lemma toBackwardFirstChainTransform_eq_blockFormula
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (scattering : TwoPortScatteringTransform ι κ)
    (hTransmission : scattering.HasBijectiveRightToLeftTransmission) :
    scattering.toBackwardFirstChainTransform hTransmission =
      scattering.backwardFirstChainBlockFormula hTransmission :=
  BackwardFirstTwoPortBehavior.leftToRightChainTransform_unique
    scattering.toBackwardFirstBehavior
    ((scattering.hasLeftToRightChainView_iff_rightToLeftTransmission_bijective).2 hTransmission)
    (scattering.backwardFirstChainBlockFormula hTransmission)
    (scattering.toBehavior_backwardFirstChainBlockFormula hTransmission)

end TwoPortScatteringTransform

end

end Optics
