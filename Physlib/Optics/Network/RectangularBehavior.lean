/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.LinearBehavior

/-!
# Rectangular linear optical behaviors

## i. Overview

This file supplies explicit complex-linear signal operations whose input and output mode families
have different shapes. Copy sends one amplitude family to two equal branches, coherent sum adds
two branches, and selection retains one branch. Weighted split and weighted combine generalize
these operations by independent complex coefficients.

Each operation is defined first as a complex-linear map and then embedded as a graph behavior.
Their composition laws therefore connect the implicit behavior layer to later executable network
assembly without requiring any inverse.

## ii. Key results

- `LinearBehavior.copy`: equal amplitudes on two output branches.
- `LinearBehavior.coherentSum`: coherent addition of two input branches.
- `LinearBehavior.selectLeft` and `LinearBehavior.selectRight`: coordinate selection.
- `LinearBehavior.weightedSplit`: two independently weighted output branches.
- `LinearBehavior.weightedCombine`: coherent weighted addition of two input branches.
- `LinearBehavior.weightedSplit_series_weightedCombine_eq_identity`: a sufficient algebraic
  coefficient equation for a one-sided identity.

## iii. Table of contents

- A. Weighted split and combine maps
- B. Rectangular graph behaviors
- C. Composition and modal-power laws

## iv. References

These operations are algebraic constraints on fixed-frequency amplitudes. Copy's proved power law
doubles normalized modal power, so it is not passive on any mode family admitting a nonzero
amplitude. Coherent sum can include interference and need not be one-to-one on a nontrivial mode
family. Weighted split and combine state only their displayed equations; arbitrary coefficients
do not imply passivity, losslessness, reciprocity, realizability, or an adjoint relation. They are
not operations on quantum states.

Selecting one branch does not model a physical termination or absorption of the omitted branch. A
weighted split whose coefficient norm squares sum to one is an isometry from its one-family input,
not a complete square lossless optical device; such a device requires another independent input
channel and a unitary completion.

-/

@[expose] public section

namespace Optics

noncomputable section

universe u v

namespace LinearBehavior

variable {ι : Type u} {μ : Type v}

/-!

## A. Weighted split and combine maps

-/

/-- The complex-linear map sending an amplitude to two independently weighted copies. -/
def weightedSplitMap (leftWeight rightWeight : ℂ) :
    ModeAmplitude ι →ₗ[ℂ] ModeAmplitude (ι ⊕ ι) :=
  ModeAmplitude.directSumLinearEquiv.toLinearMap.comp
    ((leftWeight • (LinearMap.id : ModeAmplitude ι →ₗ[ℂ] ModeAmplitude ι)).prod
      (rightWeight • (LinearMap.id : ModeAmplitude ι →ₗ[ℂ] ModeAmplitude ι)))

/-- Weighted splitting scales the two output branches independently. -/
@[simp]
lemma weightedSplitMap_apply (leftWeight rightWeight : ℂ) (input : ModeAmplitude ι) :
    weightedSplitMap leftWeight rightWeight input =
      (leftWeight • input).directSum (rightWeight • input) := rfl

/-- The complex-linear map coherently adding two input branches with independent weights. -/
def weightedCombineMap (leftWeight rightWeight : ℂ) :
    ModeAmplitude (ι ⊕ ι) →ₗ[ℂ] ModeAmplitude ι :=
  (LinearMap.coprod
    (leftWeight • (LinearMap.id : ModeAmplitude ι →ₗ[ℂ] ModeAmplitude ι))
    (rightWeight • (LinearMap.id : ModeAmplitude ι →ₗ[ℂ] ModeAmplitude ι))).comp
      ModeAmplitude.directSumLinearEquiv.symm.toLinearMap

/-- Weighted combination adds the independently scaled input branches. -/
@[simp]
lemma weightedCombineMap_apply (leftWeight rightWeight : ℂ)
    (input : ModeAmplitude (ι ⊕ ι)) :
    weightedCombineMap leftWeight rightWeight input =
      leftWeight • input.restrictInl + rightWeight • input.restrictInr := rfl

/-!

## B. Rectangular graph behaviors

-/

/-- The behavior sending one amplitude family to two independently weighted branches. -/
def weightedSplit (leftWeight rightWeight : ℂ) : LinearBehavior ι (ι ⊕ ι) :=
  ofLinearMap (weightedSplitMap leftWeight rightWeight)

/-- Membership in weighted split states the two branch amplitudes exactly. -/
@[simp]
lemma mem_weightedSplit_iff (leftWeight rightWeight : ℂ)
    (input : ModeAmplitude ι) (output : ModeAmplitude (ι ⊕ ι)) :
    (input, output) ∈ weightedSplit leftWeight rightWeight ↔
      output = (leftWeight • input).directSum (rightWeight • input) := by
  simp [weightedSplit]

/-- The behavior coherently adding two branches with independent complex weights. -/
def weightedCombine (leftWeight rightWeight : ℂ) : LinearBehavior (ι ⊕ ι) ι :=
  ofLinearMap (weightedCombineMap leftWeight rightWeight)

/-- Membership in weighted combine states the coherent weighted sum exactly. -/
@[simp]
lemma mem_weightedCombine_iff (leftWeight rightWeight : ℂ)
    (input : ModeAmplitude (ι ⊕ ι)) (output : ModeAmplitude ι) :
    (input, output) ∈ weightedCombine leftWeight rightWeight ↔
      output = leftWeight • input.restrictInl + rightWeight • input.restrictInr := by
  simp [weightedCombine]

/-- The algebraic copy behavior, placing the input amplitude on both output branches.

This is not a passive optical splitter or a quantum-state cloning operation.
-/
def copy : LinearBehavior ι (ι ⊕ ι) :=
  weightedSplit 1 1

/-- Membership in copy means that both output branches equal the input. -/
@[simp]
lemma mem_copy_iff (input : ModeAmplitude ι) (output : ModeAmplitude (ι ⊕ ι)) :
    (input, output) ∈ (copy : LinearBehavior ι (ι ⊕ ι)) ↔
      output = input.directSum input := by
  simp [copy]

/-- The coherent-sum behavior, adding the left and right input amplitudes. -/
def coherentSum : LinearBehavior (ι ⊕ ι) ι :=
  weightedCombine 1 1

/-- Membership in coherent sum means that the output is the sum of both input branches. -/
@[simp]
lemma mem_coherentSum_iff (input : ModeAmplitude (ι ⊕ ι))
    (output : ModeAmplitude ι) :
    (input, output) ∈ (coherentSum : LinearBehavior (ι ⊕ ι) ι) ↔
      output = input.restrictInl + input.restrictInr := by
  simp [coherentSum]

/-- The behavior selecting the left branch of a disjoint input family. -/
def selectLeft : LinearBehavior (ι ⊕ μ) ι :=
  ofLinearMap ModeAmplitude.restrictInlLinearMap

/-- Membership in left selection means that the output is the left input branch. -/
@[simp]
lemma mem_selectLeft_iff (input : ModeAmplitude (ι ⊕ μ)) (output : ModeAmplitude ι) :
    (input, output) ∈ (selectLeft : LinearBehavior (ι ⊕ μ) ι) ↔
      output = input.restrictInl := by
  rfl

/-- The behavior selecting the right branch of a disjoint input family. -/
def selectRight : LinearBehavior (ι ⊕ μ) μ :=
  ofLinearMap ModeAmplitude.restrictInrLinearMap

/-- Membership in right selection means that the output is the right input branch. -/
@[simp]
lemma mem_selectRight_iff (input : ModeAmplitude (ι ⊕ μ)) (output : ModeAmplitude μ) :
    (input, output) ∈ (selectRight : LinearBehavior (ι ⊕ μ) μ) ↔
      output = input.restrictInr := by
  rfl

/-!

## C. Composition and modal-power laws

-/

/-- Selecting the left branch after algebraic copy is the identity behavior. -/
@[simp]
lemma copy_series_selectLeft :
    (copy : LinearBehavior ι (ι ⊕ ι)).series selectLeft = identity := by
  ext ⟨input, output⟩
  simp

/-- Selecting the right branch after algebraic copy is the identity behavior. -/
@[simp]
lemma copy_series_selectRight :
    (copy : LinearBehavior ι (ι ⊕ ι)).series selectRight = identity := by
  ext ⟨input, output⟩
  simp

/-- A weighted split followed by a weighted combine scales the input by the bilinear coefficient
pairing. No complex conjugation is implicit in this law. -/
lemma mem_weightedSplit_series_weightedCombine_iff
    (splitLeft splitRight combineLeft combineRight : ℂ)
    (input output : ModeAmplitude ι) :
    (input, output) ∈
        (weightedSplit splitLeft splitRight).series
          (weightedCombine combineLeft combineRight) ↔
      output = (combineLeft * splitLeft + combineRight * splitRight) • input := by
  constructor
  · rintro ⟨middle, hSplit, hCombine⟩
    rw [mem_weightedSplit_iff] at hSplit
    subst middle
    rw [mem_weightedCombine_iff] at hCombine
    simpa [smul_smul, add_smul] using hCombine
  · intro hOutput
    refine ⟨(splitLeft • input).directSum (splitRight • input), ?_, ?_⟩
    · simp
    · rw [mem_weightedCombine_iff]
      simpa [smul_smul, add_smul] using hOutput

/-- A weighted split and combine form a one-sided identity when their bilinear coefficient pairing
is one. -/
lemma weightedSplit_series_weightedCombine_eq_identity
    (splitLeft splitRight combineLeft combineRight : ℂ)
    (hWeights : combineLeft * splitLeft + combineRight * splitRight = 1) :
    (weightedSplit (ι := ι) splitLeft splitRight).series
        (weightedCombine combineLeft combineRight) =
      (identity : LinearBehavior ι ι) := by
  ext ⟨input, output⟩
  rw [mem_weightedSplit_series_weightedCombine_iff, mem_identity_iff, hWeights, one_smul]

/-- A weighted combine followed by a weighted split has the displayed branch action. -/
lemma mem_weightedCombine_series_weightedSplit_iff
    (combineLeft combineRight splitLeft splitRight : ℂ)
    (input output : ModeAmplitude (ι ⊕ ι)) :
    (input, output) ∈
        (weightedCombine combineLeft combineRight).series
          (weightedSplit splitLeft splitRight) ↔
      output =
        (splitLeft •
          (combineLeft • input.restrictInl + combineRight • input.restrictInr)).directSum
        (splitRight •
          (combineLeft • input.restrictInl + combineRight • input.restrictInr)) := by
  constructor
  · rintro ⟨middle, hCombine, hSplit⟩
    rw [mem_weightedCombine_iff] at hCombine
    subst middle
    exact (mem_weightedSplit_iff _ _ _ _).mp hSplit
  · intro hOutput
    refine ⟨combineLeft • input.restrictInl + combineRight • input.restrictInr, ?_, ?_⟩
    · simp
    · exact (mem_weightedSplit_iff _ _ _ _).mpr hOutput

/-- A weighted combine annihilates the displayed algebraic cancellation family. This statement
does not interpret the missing output power as absorption. -/
lemma weightedCombine_cancellation_mem (leftWeight rightWeight : ℂ)
    (amplitude : ModeAmplitude ι) :
    ((rightWeight • amplitude).directSum ((-leftWeight) • amplitude), 0) ∈
      weightedCombine leftWeight rightWeight := by
  rw [mem_weightedCombine_iff]
  apply WithLp.ofLp_injective 2
  funext index
  change 0 = leftWeight * (rightWeight * amplitude index) +
    rightWeight * (-leftWeight * amplitude index)
  ring

/-- When the split-combine scalar pairing is one, combining and then splitting is an algebraic
idempotent. It is not asserted to be an orthogonal projection. -/
lemma weightedCombine_series_weightedSplit_idempotent
    (splitLeft splitRight combineLeft combineRight : ℂ)
    (hWeights : combineLeft * splitLeft + combineRight * splitRight = 1) :
    ((weightedCombine (ι := ι) combineLeft combineRight).series
        (weightedSplit splitLeft splitRight)).series
      ((weightedCombine (ι := ι) combineLeft combineRight).series
        (weightedSplit splitLeft splitRight)) =
      (weightedCombine (ι := ι) combineLeft combineRight).series
        (weightedSplit splitLeft splitRight) := by
  calc
    ((weightedCombine combineLeft combineRight).series
          (weightedSplit splitLeft splitRight)).series
        ((weightedCombine combineLeft combineRight).series
          (weightedSplit splitLeft splitRight)) =
      (weightedCombine combineLeft combineRight).series
        ((weightedSplit splitLeft splitRight).series
          ((weightedCombine combineLeft combineRight).series
            (weightedSplit splitLeft splitRight))) :=
      series_assoc _ _ _
    _ = (weightedCombine combineLeft combineRight).series
        (((weightedSplit splitLeft splitRight).series
          (weightedCombine combineLeft combineRight)).series
            (weightedSplit splitLeft splitRight)) := by
      rw [series_assoc]
    _ = (weightedCombine combineLeft combineRight).series
        (weightedSplit splitLeft splitRight) := by
      rw [weightedSplit_series_weightedCombine_eq_identity (ι := ι) _ _ _ _ hWeights,
        identity_series]

/-- Algebraic copy doubles normalized modal power. -/
lemma copy_output_power [Fintype ι] (input : ModeAmplitude ι)
    (output : ModeAmplitude (ι ⊕ ι))
    (hCopy : (input, output) ∈ (copy : LinearBehavior ι (ι ⊕ ι))) :
    output.power = 2 * input.power := by
  rw [mem_copy_iff] at hCopy
  subst output
  rw [ModeAmplitude.power_directSum]
  ring

/-- Weighted split scales normalized modal power by the sum of the two squared coefficient
moduli. -/
lemma weightedSplit_output_power [Fintype ι] (leftWeight rightWeight : ℂ)
    (input : ModeAmplitude ι) (output : ModeAmplitude (ι ⊕ ι))
    (hSplit : (input, output) ∈ weightedSplit leftWeight rightWeight) :
    output.power =
      (Complex.normSq leftWeight + Complex.normSq rightWeight) * input.power := by
  rw [mem_weightedSplit_iff] at hSplit
  subst output
  rw [ModeAmplitude.power_directSum, ModeAmplitude.power_smul, ModeAmplitude.power_smul]
  ring

end LinearBehavior

end

end Optics
