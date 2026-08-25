/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.TwoPortChainScattering
public import Physlib.Optics.Network.TwoPortTermination

/-!
# Right termination of a backward-first chain transform

## i. Overview

For a chain equation

`aR = K₁₁ bL + K₁₂ aL`, `bR = K₂₁ bL + K₂₂ aL`,

a right-load reflection transform `Γ : bR ↦ aR` imposes `aR = Γ bR`. Eliminating `aR` gives

`(K₁₁ - Γ K₂₁) bL = (Γ K₂₂ - K₁₂) aL`.

This file first proves that equation from the relational termination semantics. It characterizes
well-posedness exactly by injectivity of the pivot together with solvability for every incident
wave. Bijectivity of the pivot is then used only as a stronger sufficient hypothesis for the
closed reflection and forward-transmission formulas.

## ii. Scope and convention

The load transform maps the forward wave `bR` arriving at the right boundary to the backward wave
`aR` returning toward the device. The reported forward response is `bR` at that boundary, not
transmission through or absorption by a physical load. No complete chain inverse, passivity,
losslessness, causality, impedance model, or electromagnetic realization is assumed.

## iii. Key definitions and results

- `BackwardFirstChainTransform.rightTerminationPivot`: `K₁₁ - Γ K₂₁`.
- `BackwardFirstChainTransform.rightTerminationIncidentBlock`: `Γ K₂₂ - K₁₂`.
- `BackwardFirstChainTransform.hasWellPosedRightTermination_iff_pivot_injective_and_solvable`:
  the exact criterion.
- `BackwardFirstChainTransform.rightTerminatedReflectionTransformOfWellPosed` and
  `BackwardFirstChainTransform.rightTerminatedTransmissionTransformOfWellPosed`: responses under
  the exact gate.
- `BackwardFirstChainTransform.HasBijectiveRightTerminationPivot`: the stronger formula gate.
- `BackwardFirstChainTransform.rightTerminatedReflectionTransform` and
  `BackwardFirstChainTransform.rightTerminatedTransmissionTransform`: bijective-pivot response
  conveniences with closed block formulas.

## iv. Table of contents

- A. Termination pivot and relational equations
- B. Exact well-posedness criterion
- C. Exact-gate responses and bijective-pivot formulas
- D. Zero-return specialization

-/

@[expose] public section

namespace Optics

noncomputable section

universe u v

namespace BackwardFirstChainTransform

variable {ι : Type u} {κ : Type v}

/-!

## A. Termination pivot and relational equations

-/

/-- The right-termination pivot `K₁₁ - Γ K₂₁`. -/
def rightTerminationPivot [Fintype κ] (chain : BackwardFirstChainTransform ι κ)
    (loadReflection : RightLoadTransform κ) :
    ModeTransform (BackwardWave ι) (BackwardWave κ) :=
  chain.leadingBlock - loadReflection * chain.lowerLeftBlock

/-- The incident forcing block `Γ K₂₂ - K₁₂` in the right-termination equation. -/
def rightTerminationIncidentBlock [Fintype κ] (chain : BackwardFirstChainTransform ι κ)
    (loadReflection : RightLoadTransform κ) :
    ModeTransform (ForwardWave ι) (BackwardWave κ) :=
  loadReflection * chain.lowerRightBlock - chain.upperRightBlock

/-- The complete relational solution for a chain graph terminated by a reflection-transform
graph. -/
def rightTerminationBehavior [Fintype ι] [Fintype κ]
    (chain : BackwardFirstChainTransform ι κ) (loadReflection : RightLoadTransform κ) :
    RightTerminatedSolutionBehavior ι κ :=
  BackwardFirstTwoPortBehavior.terminateRight chain.toBehavior
    (RightLoadBehavior.ofReflection loadReflection)

/-- A chain termination is well posed when every left incident wave has one complete solution
`(bL, aR, bR)`. -/
abbrev HasWellPosedRightTermination [Fintype ι] [Fintype κ]
    (chain : BackwardFirstChainTransform ι κ) (loadReflection : RightLoadTransform κ) : Prop :=
  (chain.rightTerminationBehavior loadReflection).IsFunctional

/-- The termination pivot acts as `K₁₁ bL - Γ (K₂₁ bL)`. -/
lemma toLinearMap_rightTerminationPivot [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (chain : BackwardFirstChainTransform ι κ)
    (loadReflection : RightLoadTransform κ) (leftBackward : ModeAmplitude (BackwardWave ι)) :
    (chain.rightTerminationPivot loadReflection).toLinearMap leftBackward =
      chain.leadingBlock.toLinearMap leftBackward -
        loadReflection.toLinearMap (chain.lowerLeftBlock.toLinearMap leftBackward) := by
  change Matrix.toEuclideanLin
      (chain.leadingBlock - loadReflection * chain.lowerLeftBlock) leftBackward = _
  rw [map_sub, LinearMap.sub_apply, ModeTransform.toLinearMap_mul_apply]

/-- The incident block acts as `Γ (K₂₂ aL) - K₁₂ aL`. -/
lemma toLinearMap_rightTerminationIncidentBlock [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (chain : BackwardFirstChainTransform ι κ)
    (loadReflection : RightLoadTransform κ) (leftIncident : ModeAmplitude (ForwardWave ι)) :
    (chain.rightTerminationIncidentBlock loadReflection).toLinearMap leftIncident =
      loadReflection.toLinearMap (chain.lowerRightBlock.toLinearMap leftIncident) -
        chain.upperRightBlock.toLinearMap leftIncident := by
  change Matrix.toEuclideanLin
      (loadReflection * chain.lowerRightBlock - chain.upperRightBlock) leftIncident = _
  rw [map_sub, LinearMap.sub_apply, ModeTransform.toLinearMap_mul_apply]

/-- Complete terminated membership is the two chain equations together with `aR = Γ bR`. -/
lemma mem_rightTerminationBehavior_iff_blockEquations
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (chain : BackwardFirstChainTransform ι κ) (loadReflection : RightLoadTransform κ)
    (leftIncident : ModeAmplitude (ForwardWave ι))
    (leftBackward : ModeAmplitude (BackwardWave ι))
    (rightBackward : ModeAmplitude (BackwardWave κ))
    (rightForward : ModeAmplitude (ForwardWave κ)) :
    (leftIncident, leftBackward.directSum (rightBackward.directSum rightForward)) ∈
        chain.rightTerminationBehavior loadReflection ↔
      rightBackward = chain.leadingBlock.toLinearMap leftBackward +
          chain.upperRightBlock.toLinearMap leftIncident ∧
        rightForward = chain.lowerLeftBlock.toLinearMap leftBackward +
          chain.lowerRightBlock.toLinearMap leftIncident ∧
        rightBackward = loadReflection.toLinearMap rightForward := by
  rw [rightTerminationBehavior,
    BackwardFirstTwoPortBehavior.mem_terminateRight_directSum_iff,
    chain.mem_toBehavior_iff_blockEquations,
    RightLoadBehavior.mem_ofReflection_iff]
  simp only [ModeAmplitude.restrictInl_directSum, ModeAmplitude.restrictInr_directSum]
  tauto

/-- Complete terminated membership reduces to the pivot equation, the forward-wave equation, and
the right-return equation. -/
lemma mem_rightTerminationBehavior_iff_reducedEquations
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (chain : BackwardFirstChainTransform ι κ) (loadReflection : RightLoadTransform κ)
    (leftIncident : ModeAmplitude (ForwardWave ι))
    (leftBackward : ModeAmplitude (BackwardWave ι))
    (rightBackward : ModeAmplitude (BackwardWave κ))
    (rightForward : ModeAmplitude (ForwardWave κ)) :
    (leftIncident, leftBackward.directSum (rightBackward.directSum rightForward)) ∈
        chain.rightTerminationBehavior loadReflection ↔
      (chain.rightTerminationPivot loadReflection).toLinearMap leftBackward =
          (chain.rightTerminationIncidentBlock loadReflection).toLinearMap leftIncident ∧
        rightForward = chain.lowerLeftBlock.toLinearMap leftBackward +
          chain.lowerRightBlock.toLinearMap leftIncident ∧
        rightBackward = loadReflection.toLinearMap rightForward := by
  rw [chain.mem_rightTerminationBehavior_iff_blockEquations loadReflection]
  constructor
  · rintro ⟨hBackward, hForward, hReturn⟩
    refine ⟨?_, hForward, hReturn⟩
    rw [chain.toLinearMap_rightTerminationPivot loadReflection,
      chain.toLinearMap_rightTerminationIncidentBlock loadReflection]
    rw [hForward, map_add] at hReturn
    have hSum := hBackward.symm.trans hReturn
    linear_combination (norm := module) hSum
  · rintro ⟨hPivot, hForward, hReturn⟩
    refine ⟨?_, hForward, hReturn⟩
    rw [chain.toLinearMap_rightTerminationPivot loadReflection,
      chain.toLinearMap_rightTerminationIncidentBlock loadReflection] at hPivot
    rw [hForward, map_add] at hReturn
    have hSum : chain.leadingBlock.toLinearMap leftBackward +
        chain.upperRightBlock.toLinearMap leftIncident =
        loadReflection.toLinearMap (chain.lowerLeftBlock.toLinearMap leftBackward) +
          loadReflection.toLinearMap (chain.lowerRightBlock.toLinearMap leftIncident) := by
      linear_combination (norm := module) hPivot
    exact hReturn.trans hSum.symm

/-- Reduced terminated equations for an arbitrarily packaged complete solution. -/
lemma mem_rightTerminationBehavior_iff_reduced
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (chain : BackwardFirstChainTransform ι κ) (loadReflection : RightLoadTransform κ)
    (leftIncident : ModeAmplitude (ForwardWave ι))
    (solution : ModeAmplitude (RightTerminatedSolutionChannel ι κ)) :
    (leftIncident, solution) ∈ chain.rightTerminationBehavior loadReflection ↔
      (chain.rightTerminationPivot loadReflection).toLinearMap solution.restrictInl =
          (chain.rightTerminationIncidentBlock loadReflection).toLinearMap leftIncident ∧
        solution.restrictInr.restrictInr =
          chain.lowerLeftBlock.toLinearMap solution.restrictInl +
            chain.lowerRightBlock.toLinearMap leftIncident ∧
        solution.restrictInr.restrictInl =
          loadReflection.toLinearMap solution.restrictInr.restrictInr := by
  simpa only [ModeAmplitude.directSum_restrict] using
    chain.mem_rightTerminationBehavior_iff_reducedEquations loadReflection leftIncident
      solution.restrictInl solution.restrictInr.restrictInl
        solution.restrictInr.restrictInr

/-- Reflection-projection membership is exactly solvability of the termination pivot equation. -/
lemma mem_rightTerminatedReflectionBehavior_iff_pivotEquation
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (chain : BackwardFirstChainTransform ι κ) (loadReflection : RightLoadTransform κ)
    (leftIncident : ModeAmplitude (ForwardWave ι))
    (leftBackward : ModeAmplitude (BackwardWave ι)) :
    (leftIncident, leftBackward) ∈
        BackwardFirstTwoPortBehavior.rightTerminatedReflectionBehavior chain.toBehavior
          (RightLoadBehavior.ofReflection loadReflection) ↔
      (chain.rightTerminationPivot loadReflection).toLinearMap leftBackward =
        (chain.rightTerminationIncidentBlock loadReflection).toLinearMap leftIncident := by
  rw [BackwardFirstTwoPortBehavior.mem_rightTerminatedReflectionBehavior_iff]
  constructor
  · rintro ⟨rightBackward, rightForward, hDevice, hLoad⟩
    have hSolution := (BackwardFirstTwoPortBehavior.mem_terminateRight_directSum_iff
      chain.toBehavior
      (RightLoadBehavior.ofReflection loadReflection) leftIncident leftBackward rightBackward
      rightForward).mpr ⟨hDevice, hLoad⟩
    exact (chain.mem_rightTerminationBehavior_iff_reducedEquations loadReflection leftIncident
      leftBackward rightBackward rightForward).mp hSolution |>.1
  · intro hPivot
    let rightForward := chain.lowerLeftBlock.toLinearMap leftBackward +
      chain.lowerRightBlock.toLinearMap leftIncident
    let rightBackward := loadReflection.toLinearMap rightForward
    refine ⟨rightBackward, rightForward, ?_⟩
    apply (BackwardFirstTwoPortBehavior.mem_terminateRight_directSum_iff chain.toBehavior
      (RightLoadBehavior.ofReflection loadReflection) leftIncident leftBackward rightBackward
      rightForward).mp
    apply (chain.mem_rightTerminationBehavior_iff_reducedEquations loadReflection leftIncident
      leftBackward rightBackward rightForward).mpr
    exact ⟨hPivot, rfl, rfl⟩

/-- Transmission-projection membership means that some pivot solution produces the reported
forward wave at the right termination plane. -/
lemma mem_rightTerminatedTransmissionBehavior_iff_pivotEquation
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (chain : BackwardFirstChainTransform ι κ) (loadReflection : RightLoadTransform κ)
    (leftIncident : ModeAmplitude (ForwardWave ι))
    (rightForward : ModeAmplitude (ForwardWave κ)) :
    (leftIncident, rightForward) ∈
        BackwardFirstTwoPortBehavior.rightTerminatedTransmissionBehavior chain.toBehavior
          (RightLoadBehavior.ofReflection loadReflection) ↔
      ∃ leftBackward : ModeAmplitude (BackwardWave ι),
        (chain.rightTerminationPivot loadReflection).toLinearMap leftBackward =
            (chain.rightTerminationIncidentBlock loadReflection).toLinearMap leftIncident ∧
          rightForward = chain.lowerLeftBlock.toLinearMap leftBackward +
            chain.lowerRightBlock.toLinearMap leftIncident := by
  rw [BackwardFirstTwoPortBehavior.mem_rightTerminatedTransmissionBehavior_iff]
  constructor
  · rintro ⟨leftBackward, rightBackward, hDevice, hLoad⟩
    refine ⟨leftBackward, ?_⟩
    have hSolution :=
      (BackwardFirstTwoPortBehavior.mem_terminateRight_directSum_iff chain.toBehavior
        (RightLoadBehavior.ofReflection loadReflection) leftIncident leftBackward rightBackward
        rightForward).mpr ⟨hDevice, hLoad⟩
    have hReduced := (chain.mem_rightTerminationBehavior_iff_reducedEquations loadReflection
      leftIncident leftBackward rightBackward rightForward).mp hSolution
    exact ⟨hReduced.1, hReduced.2.1⟩
  · rintro ⟨leftBackward, hPivot, hForward⟩
    let rightBackward := loadReflection.toLinearMap rightForward
    refine ⟨leftBackward, rightBackward, ?_⟩
    apply (BackwardFirstTwoPortBehavior.mem_terminateRight_directSum_iff chain.toBehavior
      (RightLoadBehavior.ofReflection loadReflection) leftIncident leftBackward rightBackward
      rightForward).mp
    apply (chain.mem_rightTerminationBehavior_iff_reducedEquations loadReflection leftIncident
      leftBackward rightBackward rightForward).mpr
    exact ⟨hPivot, hForward, rfl⟩

/-!

## B. Exact well-posedness criterion

-/

/-- The complete right-termination relation is total exactly when every incident forcing lies in
the range of the termination pivot. -/
lemma isTotal_rightTerminationBehavior_iff_pivot_solvable
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (chain : BackwardFirstChainTransform ι κ) (loadReflection : RightLoadTransform κ) :
    (chain.rightTerminationBehavior loadReflection).IsTotal ↔
      ∀ leftIncident : ModeAmplitude (ForwardWave ι),
        ∃ leftBackward : ModeAmplitude (BackwardWave ι),
          (chain.rightTerminationPivot loadReflection).toLinearMap leftBackward =
            (chain.rightTerminationIncidentBlock loadReflection).toLinearMap leftIncident := by
  constructor
  · intro hTotal leftIncident
    rcases hTotal leftIncident with ⟨solution, hSolution⟩
    refine ⟨solution.restrictInl, ?_⟩
    exact ((chain.mem_rightTerminationBehavior_iff_reduced loadReflection leftIncident
      solution).mp hSolution).1
  · intro hSolvable leftIncident
    rcases hSolvable leftIncident with ⟨leftBackward, hPivot⟩
    let rightForward := chain.lowerLeftBlock.toLinearMap leftBackward +
      chain.lowerRightBlock.toLinearMap leftIncident
    let rightBackward := loadReflection.toLinearMap rightForward
    refine ⟨leftBackward.directSum (rightBackward.directSum rightForward), ?_⟩
    exact (chain.mem_rightTerminationBehavior_iff_reducedEquations loadReflection leftIncident
      leftBackward rightBackward rightForward).mpr ⟨hPivot, rfl, rfl⟩

/-- Single-valuedness of the complete right-termination relation is exactly injectivity of the
termination pivot. -/
lemma isSingleValued_rightTerminationBehavior_iff_pivot_injective
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (chain : BackwardFirstChainTransform ι κ) (loadReflection : RightLoadTransform κ) :
    (chain.rightTerminationBehavior loadReflection).IsSingleValued ↔
      Function.Injective (chain.rightTerminationPivot loadReflection).toLinearMap := by
  constructor
  · intro hSingle first second hEqual
    have hKernel : (chain.rightTerminationPivot loadReflection).toLinearMap (first - second) =
        (chain.rightTerminationIncidentBlock loadReflection).toLinearMap 0 := by
      rw [map_sub, hEqual, sub_self, map_zero]
    let rightForward := chain.lowerLeftBlock.toLinearMap (first - second)
    let rightBackward := loadReflection.toLinearMap rightForward
    let solution := (first - second).directSum (rightBackward.directSum rightForward)
    have hSolution : (0, solution) ∈ chain.rightTerminationBehavior loadReflection := by
      apply (chain.mem_rightTerminationBehavior_iff_reducedEquations loadReflection 0
        (first - second) rightBackward rightForward).mpr
      refine ⟨hKernel, ?_, rfl⟩
      simp only [rightForward, map_zero, add_zero]
    have hZero : (0, (0 : ModeAmplitude (RightTerminatedSolutionChannel ι κ))) ∈
        chain.rightTerminationBehavior loadReflection :=
      (chain.rightTerminationBehavior loadReflection).zero_mem
    have hSolutionZero := hSingle hSolution hZero
    have hDifference : first - second = 0 :=
      congrArg ModeAmplitude.restrictInl hSolutionZero
    exact sub_eq_zero.mp hDifference
  · intro hInjective input firstSolution secondSolution hFirst hSecond
    have hFirstReduced :=
      (chain.mem_rightTerminationBehavior_iff_reduced loadReflection input
        firstSolution).mp hFirst
    have hSecondReduced :=
      (chain.mem_rightTerminationBehavior_iff_reduced loadReflection input
        secondSolution).mp hSecond
    have hLeft : firstSolution.restrictInl = secondSolution.restrictInl :=
      hInjective (hFirstReduced.1.trans hSecondReduced.1.symm)
    have hForward : firstSolution.restrictInr.restrictInr =
        secondSolution.restrictInr.restrictInr := by
      rw [hFirstReduced.2.1, hSecondReduced.2.1, hLeft]
    have hBackward : firstSolution.restrictInr.restrictInl =
        secondSolution.restrictInr.restrictInl := by
      rw [hFirstReduced.2.2, hSecondReduced.2.2, hForward]
    rw [← firstSolution.directSum_restrict, ← secondSolution.directSum_restrict]
    apply congrArg₂ ModeAmplitude.directSum hLeft
    rw [← firstSolution.restrictInr.directSum_restrict,
      ← secondSolution.restrictInr.directSum_restrict, hBackward, hForward]

/-- Exact right-termination well-posedness: the pivot is injective and every incident forcing is
solvable. Bijectivity is not necessary when the incident block occupies only part of the pivot
codomain. -/
lemma hasWellPosedRightTermination_iff_pivot_injective_and_solvable
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (chain : BackwardFirstChainTransform ι κ) (loadReflection : RightLoadTransform κ) :
    chain.HasWellPosedRightTermination loadReflection ↔
      Function.Injective (chain.rightTerminationPivot loadReflection).toLinearMap ∧
        ∀ leftIncident : ModeAmplitude (ForwardWave ι),
          ∃ leftBackward : ModeAmplitude (BackwardWave ι),
            (chain.rightTerminationPivot loadReflection).toLinearMap leftBackward =
              (chain.rightTerminationIncidentBlock loadReflection).toLinearMap leftIncident := by
  constructor
  · rintro ⟨hTotal, hSingle⟩
    exact ⟨(chain.isSingleValued_rightTerminationBehavior_iff_pivot_injective
      loadReflection).mp hSingle,
      (chain.isTotal_rightTerminationBehavior_iff_pivot_solvable loadReflection).mp hTotal⟩
  · rintro ⟨hInjective, hSolvable⟩
    exact ⟨(chain.isTotal_rightTerminationBehavior_iff_pivot_solvable
      loadReflection).mpr hSolvable,
      (chain.isSingleValued_rightTerminationBehavior_iff_pivot_injective
        loadReflection).mpr hInjective⟩

/-- Bijectivity of the right-termination pivot, a sufficient gate for the closed block formulas. -/
def HasBijectiveRightTerminationPivot [Fintype ι] [DecidableEq ι]
    [Fintype κ] (chain : BackwardFirstChainTransform ι κ)
    (loadReflection : RightLoadTransform κ) : Prop :=
  Function.Bijective (chain.rightTerminationPivot loadReflection).toLinearMap

/-- A bijective right-termination pivot makes the complete terminated solution well posed. -/
lemma hasWellPosedRightTermination_of_hasBijectivePivot
    [Fintype ι] [DecidableEq ι] [Fintype κ]
    (chain : BackwardFirstChainTransform ι κ) (loadReflection : RightLoadTransform κ)
    (hPivot : chain.HasBijectiveRightTerminationPivot loadReflection) :
    chain.HasWellPosedRightTermination loadReflection := by
  classical
  apply (chain.hasWellPosedRightTermination_iff_pivot_injective_and_solvable
    loadReflection).mpr
  refine ⟨hPivot.1, ?_⟩
  intro leftIncident
  exact hPivot.2 ((chain.rightTerminationIncidentBlock loadReflection).toLinearMap leftIncident)

/-!

## C. Exact-gate responses and bijective-pivot formulas

-/

/-- The bijective right-termination pivot as a heterogeneous linear equivalence. -/
noncomputable def rightTerminationPivotEquiv
    [Fintype ι] [DecidableEq ι] [Fintype κ]
    (chain : BackwardFirstChainTransform ι κ) (loadReflection : RightLoadTransform κ)
    (hPivot : chain.HasBijectiveRightTerminationPivot loadReflection) :
    ModeAmplitude (BackwardWave ι) ≃ₗ[ℂ] ModeAmplitude (BackwardWave κ) :=
  LinearEquiv.ofBijective (chain.rightTerminationPivot loadReflection).toLinearMap hPivot

/-- The mode-transform matrix of the inverse right-termination pivot. -/
noncomputable def rightTerminationPivotInverse
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (chain : BackwardFirstChainTransform ι κ) (loadReflection : RightLoadTransform κ)
    (hPivot : chain.HasBijectiveRightTerminationPivot loadReflection) :
    ModeTransform (BackwardWave κ) (BackwardWave ι) :=
  Matrix.toEuclideanLin.symm
    (chain.rightTerminationPivotEquiv loadReflection hPivot).symm.toLinearMap

/-- The inverse pivot matrix induces the inverse pivot linear map. -/
@[simp]
lemma toLinearMap_rightTerminationPivotInverse
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (chain : BackwardFirstChainTransform ι κ) (loadReflection : RightLoadTransform κ)
    (hPivot : chain.HasBijectiveRightTerminationPivot loadReflection) :
    (chain.rightTerminationPivotInverse loadReflection hPivot).toLinearMap =
      (chain.rightTerminationPivotEquiv loadReflection hPivot).symm.toLinearMap :=
  Matrix.toEuclideanLin.apply_symm_apply _

/-- Applying the termination pivot after its inverse recovers a right backward amplitude. -/
lemma rightTerminationPivot_apply_inverse
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (chain : BackwardFirstChainTransform ι κ) (loadReflection : RightLoadTransform κ)
    (hPivot : chain.HasBijectiveRightTerminationPivot loadReflection)
    (amplitude : ModeAmplitude (BackwardWave κ)) :
    (chain.rightTerminationPivot loadReflection).toLinearMap
        ((chain.rightTerminationPivotInverse loadReflection hPivot).toLinearMap amplitude) =
      amplitude := by
  rw [chain.toLinearMap_rightTerminationPivotInverse loadReflection hPivot]
  exact (chain.rightTerminationPivotEquiv loadReflection hPivot).apply_symm_apply amplitude

/-- Applying the inverse termination pivot after the pivot recovers a left backward amplitude. -/
lemma rightTerminationPivot_inverse_apply
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (chain : BackwardFirstChainTransform ι κ) (loadReflection : RightLoadTransform κ)
    (hPivot : chain.HasBijectiveRightTerminationPivot loadReflection)
    (amplitude : ModeAmplitude (BackwardWave ι)) :
    (chain.rightTerminationPivotInverse loadReflection hPivot).toLinearMap
        ((chain.rightTerminationPivot loadReflection).toLinearMap amplitude) = amplitude := by
  rw [chain.toLinearMap_rightTerminationPivotInverse loadReflection hPivot]
  exact (chain.rightTerminationPivotEquiv loadReflection hPivot).symm_apply_apply amplitude

/-- The closed left-reflection formula
`(K₁₁ - Γ K₂₁)⁻¹ (Γ K₂₂ - K₁₂)`. -/
noncomputable def rightTerminatedReflectionBlockFormula
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (chain : BackwardFirstChainTransform ι κ) (loadReflection : RightLoadTransform κ)
    (hPivot : chain.HasBijectiveRightTerminationPivot loadReflection) :
    ModeTransform (ForwardWave ι) (BackwardWave ι) :=
  chain.rightTerminationPivotInverse loadReflection hPivot *
    chain.rightTerminationIncidentBlock loadReflection

/-- The closed forward-response formula at the right termination plane,
`K₂₁ RΓ + K₂₂`. -/
noncomputable def rightTerminatedTransmissionBlockFormula
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (chain : BackwardFirstChainTransform ι κ) (loadReflection : RightLoadTransform κ)
    (hPivot : chain.HasBijectiveRightTerminationPivot loadReflection) :
    ModeTransform (ForwardWave ι) (ForwardWave κ) :=
  chain.lowerLeftBlock *
      chain.rightTerminatedReflectionBlockFormula loadReflection hPivot +
    chain.lowerRightBlock

/-- The forward-response formula acts as `K₂₁ (RΓ aL) + K₂₂ aL`. -/
lemma toLinearMap_rightTerminatedTransmissionBlockFormula
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (chain : BackwardFirstChainTransform ι κ) (loadReflection : RightLoadTransform κ)
    (hPivot : chain.HasBijectiveRightTerminationPivot loadReflection)
    (leftIncident : ModeAmplitude (ForwardWave ι)) :
    (chain.rightTerminatedTransmissionBlockFormula loadReflection hPivot).toLinearMap
        leftIncident =
      chain.lowerLeftBlock.toLinearMap
          ((chain.rightTerminatedReflectionBlockFormula loadReflection hPivot).toLinearMap
            leftIncident) +
        chain.lowerRightBlock.toLinearMap leftIncident := by
  change Matrix.toEuclideanLin
      (chain.lowerLeftBlock *
          chain.rightTerminatedReflectionBlockFormula loadReflection hPivot +
        chain.lowerRightBlock) leftIncident = _
  rw [map_add, LinearMap.add_apply, ModeTransform.toLinearMap_mul_apply]

/-- The reflection formula's graph is exactly the relational reflection projection. -/
lemma toBehavior_rightTerminatedReflectionBlockFormula
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (chain : BackwardFirstChainTransform ι κ) (loadReflection : RightLoadTransform κ)
    (hPivot : chain.HasBijectiveRightTerminationPivot loadReflection) :
    (chain.rightTerminatedReflectionBlockFormula loadReflection hPivot).toBehavior =
      BackwardFirstTwoPortBehavior.rightTerminatedReflectionBehavior chain.toBehavior
        (RightLoadBehavior.ofReflection loadReflection) := by
  ext ⟨leftIncident, leftBackward⟩
  rw [ModeTransform.mem_toBehavior_iff_toLinearMap,
    chain.mem_rightTerminatedReflectionBehavior_iff_pivotEquation loadReflection]
  constructor
  · intro hReflection
    rw [hReflection, rightTerminatedReflectionBlockFormula,
      ModeTransform.toLinearMap_mul_apply]
    exact chain.rightTerminationPivot_apply_inverse loadReflection hPivot _
  · intro hPivotEquation
    calc
      leftBackward = (chain.rightTerminationPivotInverse loadReflection hPivot).toLinearMap
          ((chain.rightTerminationPivot loadReflection).toLinearMap leftBackward) :=
            (chain.rightTerminationPivot_inverse_apply loadReflection hPivot leftBackward).symm
      _ = (chain.rightTerminationPivotInverse loadReflection hPivot).toLinearMap
          ((chain.rightTerminationIncidentBlock loadReflection).toLinearMap leftIncident) := by
            rw [hPivotEquation]
      _ = (chain.rightTerminatedReflectionBlockFormula loadReflection hPivot).toLinearMap
          leftIncident := by
            rw [rightTerminatedReflectionBlockFormula,
              ModeTransform.toLinearMap_mul_apply]

/-- The transmission formula's graph is exactly the relational forward projection. -/
lemma toBehavior_rightTerminatedTransmissionBlockFormula
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (chain : BackwardFirstChainTransform ι κ) (loadReflection : RightLoadTransform κ)
    (hPivot : chain.HasBijectiveRightTerminationPivot loadReflection) :
    (chain.rightTerminatedTransmissionBlockFormula loadReflection hPivot).toBehavior =
      BackwardFirstTwoPortBehavior.rightTerminatedTransmissionBehavior chain.toBehavior
        (RightLoadBehavior.ofReflection loadReflection) := by
  ext ⟨leftIncident, rightForward⟩
  rw [ModeTransform.mem_toBehavior_iff_toLinearMap,
    chain.mem_rightTerminatedTransmissionBehavior_iff_pivotEquation loadReflection]
  constructor
  · intro hForward
    refine ⟨(chain.rightTerminatedReflectionBlockFormula loadReflection hPivot).toLinearMap
      leftIncident, ?_, ?_⟩
    · rw [rightTerminatedReflectionBlockFormula,
        ModeTransform.toLinearMap_mul_apply]
      exact chain.rightTerminationPivot_apply_inverse loadReflection hPivot _
    · rw [hForward,
        chain.toLinearMap_rightTerminatedTransmissionBlockFormula loadReflection hPivot]
  · rintro ⟨leftBackward, hPivotEquation, hForward⟩
    have hReflection : leftBackward =
        (chain.rightTerminatedReflectionBlockFormula loadReflection hPivot).toLinearMap
          leftIncident := by
      calc
        leftBackward = (chain.rightTerminationPivotInverse loadReflection hPivot).toLinearMap
            ((chain.rightTerminationPivot loadReflection).toLinearMap leftBackward) :=
              (chain.rightTerminationPivot_inverse_apply loadReflection hPivot leftBackward).symm
        _ = (chain.rightTerminationPivotInverse loadReflection hPivot).toLinearMap
            ((chain.rightTerminationIncidentBlock loadReflection).toLinearMap leftIncident) := by
              rw [hPivotEquation]
        _ = _ := by
          rw [rightTerminatedReflectionBlockFormula, ModeTransform.toLinearMap_mul_apply]
    calc
      rightForward = chain.lowerLeftBlock.toLinearMap leftBackward +
          chain.lowerRightBlock.toLinearMap leftIncident := hForward
      _ = chain.lowerLeftBlock.toLinearMap
          ((chain.rightTerminatedReflectionBlockFormula loadReflection hPivot).toLinearMap
            leftIncident) + chain.lowerRightBlock.toLinearMap leftIncident := by
            rw [hReflection]
      _ = (chain.rightTerminatedTransmissionBlockFormula loadReflection hPivot).toLinearMap
          leftIncident :=
            (chain.toLinearMap_rightTerminatedTransmissionBlockFormula loadReflection hPivot
              leftIncident).symm

/-- The chain-level pivot proof also proves well-posedness for the underlying relational
termination. -/
lemma toBehavior_hasWellPosedRightTermination_of_hasBijectivePivot
    [Fintype ι] [DecidableEq ι] [Fintype κ]
    (chain : BackwardFirstChainTransform ι κ) (loadReflection : RightLoadTransform κ)
    (hPivot : chain.HasBijectiveRightTerminationPivot loadReflection) :
    BackwardFirstTwoPortBehavior.HasWellPosedRightTermination chain.toBehavior
      (RightLoadBehavior.ofReflection loadReflection) := by
  classical
  change (chain.rightTerminationBehavior loadReflection).IsFunctional
  exact chain.hasWellPosedRightTermination_of_hasBijectivePivot loadReflection hPivot

/-- The behavior-derived left-reflection transform under the exact right-termination
well-posedness gate. -/
noncomputable def rightTerminatedReflectionTransformOfWellPosed
    [Fintype ι] [DecidableEq ι] [Fintype κ]
    (chain : BackwardFirstChainTransform ι κ) (loadReflection : RightLoadTransform κ)
    (hWellPosed : chain.HasWellPosedRightTermination loadReflection) :
    ModeTransform (ForwardWave ι) (BackwardWave ι) :=
  BackwardFirstTwoPortBehavior.rightTerminatedReflectionTransform chain.toBehavior
    (RightLoadBehavior.ofReflection loadReflection) hWellPosed

/-- The exact-gate reflection transform reconstructs the relational reflection projection. -/
@[simp]
lemma toBehavior_rightTerminatedReflectionTransformOfWellPosed
    [Fintype ι] [DecidableEq ι] [Fintype κ]
    (chain : BackwardFirstChainTransform ι κ) (loadReflection : RightLoadTransform κ)
    (hWellPosed : chain.HasWellPosedRightTermination loadReflection) :
    (chain.rightTerminatedReflectionTransformOfWellPosed loadReflection hWellPosed).toBehavior =
      BackwardFirstTwoPortBehavior.rightTerminatedReflectionBehavior chain.toBehavior
        (RightLoadBehavior.ofReflection loadReflection) :=
  BackwardFirstTwoPortBehavior.toBehavior_rightTerminatedReflectionTransform _ _ _

/-- The behavior-derived left-reflection transform supplied by a bijective pivot. -/
noncomputable def rightTerminatedReflectionTransform
    [Fintype ι] [DecidableEq ι] [Fintype κ]
    (chain : BackwardFirstChainTransform ι κ) (loadReflection : RightLoadTransform κ)
    (hPivot : chain.HasBijectiveRightTerminationPivot loadReflection) :
    ModeTransform (ForwardWave ι) (BackwardWave ι) := by
  classical
  exact chain.rightTerminatedReflectionTransformOfWellPosed loadReflection
    (chain.toBehavior_hasWellPosedRightTermination_of_hasBijectivePivot loadReflection hPivot)

/-- The behavior-derived reflection transform reconstructs the relational reflection projection. -/
@[simp]
lemma toBehavior_rightTerminatedReflectionTransform
    [Fintype ι] [DecidableEq ι] [Fintype κ]
    (chain : BackwardFirstChainTransform ι κ) (loadReflection : RightLoadTransform κ)
    (hPivot : chain.HasBijectiveRightTerminationPivot loadReflection) :
    (chain.rightTerminatedReflectionTransform loadReflection hPivot).toBehavior =
      BackwardFirstTwoPortBehavior.rightTerminatedReflectionBehavior chain.toBehavior
        (RightLoadBehavior.ofReflection loadReflection) := by
  classical
  exact chain.toBehavior_rightTerminatedReflectionTransformOfWellPosed loadReflection _

/-- The behavior-derived left-reflection transform has the closed pivot formula. -/
lemma rightTerminatedReflectionTransform_eq_blockFormula
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (chain : BackwardFirstChainTransform ι κ) (loadReflection : RightLoadTransform κ)
    (hPivot : chain.HasBijectiveRightTerminationPivot loadReflection) :
    chain.rightTerminatedReflectionTransform loadReflection hPivot =
      chain.rightTerminatedReflectionBlockFormula loadReflection hPivot := by
  apply ModeTransform.toBehavior_injective
  rw [chain.toBehavior_rightTerminatedReflectionTransform loadReflection hPivot,
    chain.toBehavior_rightTerminatedReflectionBlockFormula loadReflection hPivot]

/-- The behavior-derived forward transform under the exact right-termination well-posedness
gate. -/
noncomputable def rightTerminatedTransmissionTransformOfWellPosed
    [Fintype ι] [DecidableEq ι] [Fintype κ]
    (chain : BackwardFirstChainTransform ι κ) (loadReflection : RightLoadTransform κ)
    (hWellPosed : chain.HasWellPosedRightTermination loadReflection) :
    ModeTransform (ForwardWave ι) (ForwardWave κ) :=
  BackwardFirstTwoPortBehavior.rightTerminatedTransmissionTransform chain.toBehavior
    (RightLoadBehavior.ofReflection loadReflection) hWellPosed

/-- The exact-gate forward transform reconstructs the relational transmission projection. -/
@[simp]
lemma toBehavior_rightTerminatedTransmissionTransformOfWellPosed
    [Fintype ι] [DecidableEq ι] [Fintype κ]
    (chain : BackwardFirstChainTransform ι κ) (loadReflection : RightLoadTransform κ)
    (hWellPosed : chain.HasWellPosedRightTermination loadReflection) :
    (chain.rightTerminatedTransmissionTransformOfWellPosed loadReflection hWellPosed).toBehavior =
      BackwardFirstTwoPortBehavior.rightTerminatedTransmissionBehavior chain.toBehavior
        (RightLoadBehavior.ofReflection loadReflection) :=
  BackwardFirstTwoPortBehavior.toBehavior_rightTerminatedTransmissionTransform _ _ _

/-- The behavior-derived forward transform supplied by a bijective pivot. -/
noncomputable def rightTerminatedTransmissionTransform
    [Fintype ι] [DecidableEq ι] [Fintype κ]
    (chain : BackwardFirstChainTransform ι κ) (loadReflection : RightLoadTransform κ)
    (hPivot : chain.HasBijectiveRightTerminationPivot loadReflection) :
    ModeTransform (ForwardWave ι) (ForwardWave κ) := by
  classical
  exact chain.rightTerminatedTransmissionTransformOfWellPosed loadReflection
    (chain.toBehavior_hasWellPosedRightTermination_of_hasBijectivePivot loadReflection hPivot)

/-- The behavior-derived forward transform reconstructs the relational transmission projection. -/
@[simp]
lemma toBehavior_rightTerminatedTransmissionTransform
    [Fintype ι] [DecidableEq ι] [Fintype κ]
    (chain : BackwardFirstChainTransform ι κ) (loadReflection : RightLoadTransform κ)
    (hPivot : chain.HasBijectiveRightTerminationPivot loadReflection) :
    (chain.rightTerminatedTransmissionTransform loadReflection hPivot).toBehavior =
      BackwardFirstTwoPortBehavior.rightTerminatedTransmissionBehavior chain.toBehavior
        (RightLoadBehavior.ofReflection loadReflection) := by
  classical
  exact chain.toBehavior_rightTerminatedTransmissionTransformOfWellPosed loadReflection _

/-- The behavior-derived forward transform has the closed pivot formula. -/
lemma rightTerminatedTransmissionTransform_eq_blockFormula
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (chain : BackwardFirstChainTransform ι κ) (loadReflection : RightLoadTransform κ)
    (hPivot : chain.HasBijectiveRightTerminationPivot loadReflection) :
    chain.rightTerminatedTransmissionTransform loadReflection hPivot =
      chain.rightTerminatedTransmissionBlockFormula loadReflection hPivot := by
  apply ModeTransform.toBehavior_injective
  rw [chain.toBehavior_rightTerminatedTransmissionTransform loadReflection hPivot,
    chain.toBehavior_rightTerminatedTransmissionBlockFormula loadReflection hPivot]

/-!

## D. Zero-return specialization

-/

/-- With zero right return, the termination pivot is the leading chain block. -/
@[simp]
lemma rightTerminationPivot_zero [Fintype κ]
    (chain : BackwardFirstChainTransform ι κ) :
    chain.rightTerminationPivot (0 : RightLoadTransform κ) = chain.leadingBlock := by
  simp [rightTerminationPivot]

/-- With zero right return, the incident forcing block is `-K₁₂`. -/
@[simp]
lemma rightTerminationIncidentBlock_zero [Fintype κ]
    (chain : BackwardFirstChainTransform ι κ) :
    chain.rightTerminationIncidentBlock (0 : RightLoadTransform κ) =
      -chain.upperRightBlock := by
  simp [rightTerminationIncidentBlock]

/-- Bijectivity of the leading block supplies the zero-return termination pivot. -/
lemma hasBijectiveRightTerminationPivot_zero
    [Fintype ι] [DecidableEq ι] [Fintype κ]
    (chain : BackwardFirstChainTransform ι κ)
    (hLeading : chain.HasBijectiveLeadingBlock) :
    chain.HasBijectiveRightTerminationPivot (0 : RightLoadTransform κ) := by
  change Function.Bijective
    (chain.rightTerminationPivot (0 : RightLoadTransform κ)).toLinearMap
  rw [chain.rightTerminationPivot_zero]
  exact hLeading

/-- The inverse zero-return termination pivot is the existing inverse leading block, independently
of the particular proofs of their bijectivity. -/
lemma rightTerminationPivotInverse_zero
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (chain : BackwardFirstChainTransform ι κ)
    (hLeading : chain.HasBijectiveLeadingBlock)
    (hPivot : chain.HasBijectiveRightTerminationPivot (0 : RightLoadTransform κ)) :
    chain.rightTerminationPivotInverse 0 hPivot = chain.leadingBlockInverse hLeading := by
  apply Matrix.toEuclideanLin.injective
  apply LinearMap.ext
  intro amplitude
  apply hLeading.1
  calc
    chain.leadingBlock.toLinearMap
        ((chain.rightTerminationPivotInverse 0 hPivot).toLinearMap amplitude) = amplitude := by
      simpa only [chain.rightTerminationPivot_zero] using
        chain.rightTerminationPivot_apply_inverse 0 hPivot amplitude
    _ = chain.leadingBlock.toLinearMap
        ((chain.leadingBlockInverse hLeading).toLinearMap amplitude) :=
      (chain.leadingBlock_apply_inverse hLeading amplitude).symm

/-- The zero-return reflection formula is `-K₁₁⁻¹ K₁₂`. -/
lemma rightTerminatedReflectionBlockFormula_zero
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (chain : BackwardFirstChainTransform ι κ)
    (hLeading : chain.HasBijectiveLeadingBlock)
    (hPivot : chain.HasBijectiveRightTerminationPivot (0 : RightLoadTransform κ)) :
    chain.rightTerminatedReflectionBlockFormula 0 hPivot =
      -(chain.leadingBlockInverse hLeading * chain.upperRightBlock) := by
  rw [rightTerminatedReflectionBlockFormula,
    chain.rightTerminationPivotInverse_zero hLeading hPivot,
    chain.rightTerminationIncidentBlock_zero, Matrix.mul_neg]

/-- The zero-return forward formula is the left-to-right Schur block
`K₂₂ - K₂₁ K₁₁⁻¹ K₁₂`. -/
lemma rightTerminatedTransmissionBlockFormula_zero
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (chain : BackwardFirstChainTransform ι κ)
    (hLeading : chain.HasBijectiveLeadingBlock)
    (hPivot : chain.HasBijectiveRightTerminationPivot (0 : RightLoadTransform κ)) :
    chain.rightTerminatedTransmissionBlockFormula 0 hPivot =
      chain.lowerRightBlock -
        chain.lowerLeftBlock * chain.leadingBlockInverse hLeading * chain.upperRightBlock := by
  rw [rightTerminatedTransmissionBlockFormula,
    chain.rightTerminatedReflectionBlockFormula_zero hLeading hPivot]
  rw [Matrix.mul_neg, Matrix.mul_assoc]
  abel

/-- The behavior-derived zero-return reflection is the left-reflection block of the existing
chain-to-scattering conversion. -/
lemma rightTerminatedReflectionTransform_zero_eq_leftReflection
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (chain : BackwardFirstChainTransform ι κ)
    (hLeading : chain.HasBijectiveLeadingBlock)
    (hPivot : chain.HasBijectiveRightTerminationPivot (0 : RightLoadTransform κ)) :
    chain.rightTerminatedReflectionTransform 0 hPivot =
      (chain.toTwoPortScatteringTransform hLeading).leftReflection := by
  rw [chain.rightTerminatedReflectionTransform_eq_blockFormula 0 hPivot,
    chain.rightTerminatedReflectionBlockFormula_zero hLeading hPivot,
    chain.toTwoPortScatteringTransform_eq_blockFormula hLeading,
    chain.leftReflection_scatteringBlockFormula hLeading]

/-- The behavior-derived zero-return forward response is the left-to-right transmission block of
the existing chain-to-scattering conversion. -/
lemma rightTerminatedTransmissionTransform_zero_eq_leftToRightTransmission
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (chain : BackwardFirstChainTransform ι κ)
    (hLeading : chain.HasBijectiveLeadingBlock)
    (hPivot : chain.HasBijectiveRightTerminationPivot (0 : RightLoadTransform κ)) :
    chain.rightTerminatedTransmissionTransform 0 hPivot =
      (chain.toTwoPortScatteringTransform hLeading).leftToRightTransmission := by
  rw [chain.rightTerminatedTransmissionTransform_eq_blockFormula 0 hPivot,
    chain.rightTerminatedTransmissionBlockFormula_zero hLeading hPivot,
    chain.toTwoPortScatteringTransform_eq_blockFormula hLeading,
    chain.leftToRightTransmission_scatteringBlockFormula hLeading]

end BackwardFirstChainTransform

end

end Optics
