/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.LinearBehavior

/-!
# Compositional relabelling of linear optical behaviors

## i. Overview

This file records inverse cancellation and functorial composition for transporting a finite
linear behavior along index equivalences.

## ii. Key results

- `LinearBehavior.reindex_symm_reindex`: inverse relabelling cancels behavior relabelling.
- `LinearBehavior.reindex_trans`: successive relabellings equal one composite relabelling.

## iii. Table of contents

- A. Inverse behavior relabelling
- B. Composite behavior relabelling

## iv. References

This is a neutral finite-index algebraic fact. It makes no optical realizability, functionality,
well-posedness, passivity, or electromagnetic-power claim.
-/

@[expose] public section

namespace Optics

noncomputable section

universe u v w x

namespace LinearBehavior

/-!

## A. Inverse behavior relabelling

-/

/-- Relabelling both sides of a finite behavior and then using the inverse labels changes
nothing. -/
@[simp]
lemma reindex_symm_reindex
    {input : Type u} {output : Type v} {reindexedInput : Type w}
    {reindexedOutput : Type x} [Fintype input] [Fintype output]
    [Fintype reindexedInput] [Fintype reindexedOutput]
    (inputEquiv : input ≃ reindexedInput) (outputEquiv : output ≃ reindexedOutput)
    (behavior : LinearBehavior input output) :
    (behavior.reindex inputEquiv outputEquiv).reindex inputEquiv.symm outputEquiv.symm =
      behavior := by
  ext ⟨inputAmplitude, outputAmplitude⟩
  simp

/-!

## B. Composite behavior relabelling

-/

/-- Two successive relabellings of a finite behavior equal relabelling along the composite
equivalences. -/
lemma reindex_trans
    {input : Type u} {output : Type v} {middleInput : Type w}
    {middleOutput : Type x} {finalInput finalOutput : Type*}
    [Fintype input] [Fintype output] [Fintype middleInput] [Fintype middleOutput]
    [Fintype finalInput] [Fintype finalOutput]
    (firstInput : input ≃ middleInput) (firstOutput : output ≃ middleOutput)
    (secondInput : middleInput ≃ finalInput)
    (secondOutput : middleOutput ≃ finalOutput) (behavior : LinearBehavior input output) :
    (behavior.reindex firstInput firstOutput).reindex secondInput secondOutput =
      behavior.reindex (firstInput.trans secondInput) (firstOutput.trans secondOutput) := by
  ext ⟨inputAmplitude, outputAmplitude⟩
  simp [LinearBehavior.mem_reindex_iff, ModeAmplitude.reindex_apply]

end LinearBehavior

end

end Optics
