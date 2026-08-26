/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.LinearBehavior

/-!
# Inverse relabelling of linear optical behaviors

## i. Overview

This file records that transporting a finite linear behavior along index equivalences and then
transporting it back along their inverses recovers the original relation.

## ii. Key results

- `LinearBehavior.reindex_symm_reindex`: inverse relabelling cancels behavior relabelling.

## iii. Table of contents

- A. Inverse behavior relabelling

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

end LinearBehavior

end

end Optics
