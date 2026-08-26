/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.SpaceAndTime.Space.Integrals.Basic

/-!
# Limits of normalized thin-cell balances

## i. Overview

This file isolates the limit algebra shared by thin-loop and pillbox arguments. A normalized
finite cell has a positive-side term, a negative-side term, a lateral remainder, a bulk term, and
a surface term. At every scale their signed balance is

```text
positive - negative + remainder = bulk + surface.
```

If the two principal terms converge to boundary values, the lateral and bulk terms vanish, and
the surface term converges, then the boundary-value jump equals the surface limit.

`NormalizedThinCellBalance` does not define a geometric cell or an integral. Electromagnetic
consumers must separately identify all five sequences with actual normalized integrals and prove
their limits. Keeping that realization outside this neutral lemma prevents a finite-cell balance
from being confused with the boundary law it is intended to derive.

## ii. Key results

- `NormalizedThinCellBalance`: the exact signed balance at every scale.
- `NormalizedThinCellBalance.HasBoundaryLimits`: convergence of each independently named term.
- `NormalizedThinCellBalance.boundaryJump_eq_surfaceLimit`: extraction of the limiting jump.

## iii. Table of contents

- A. Normalized finite-cell balances
- B. Boundary-limit extraction

## iv. References

This is neutral limit algebra used by the E4b Maxwell thin-loop and pillbox derivation.
-/

@[expose] public section

open Filter

namespace Space

/-! ## A. Normalized finite-cell balances -/

/-- Five normalized scalar terms satisfying one signed finite-cell balance at every scale.

The scale is indexed by natural numbers tending to infinity. The consumer chooses the actual cell
sizes and proves that they shrink along this index. -/
structure NormalizedThinCellBalance where
  /-- The normalized contribution from the positive-side principal face or edge. -/
  positiveBoundary : ℕ → ℝ
  /-- The normalized contribution from the negative-side principal face or edge. -/
  negativeBoundary : ℕ → ℝ
  /-- The normalized contribution from lateral faces or short edges. -/
  remainder : ℕ → ℝ
  /-- The normalized bulk-source or time-varying-flux contribution. -/
  bulk : ℕ → ℝ
  /-- The normalized singular surface-source contribution. -/
  surface : ℕ → ℝ
  /-- The signed finite-cell balance, before taking a limit. -/
  balance : ∀ scale,
    positiveBoundary scale - negativeBoundary scale + remainder scale =
      bulk scale + surface scale

namespace NormalizedThinCellBalance

/-! ## B. Boundary-limit extraction -/

/-- The five independently stated convergence conditions needed to extract a boundary jump from a
normalized finite-cell balance. -/
def HasBoundaryLimits (cell : NormalizedThinCellBalance)
    (positiveLimit negativeLimit surfaceLimit : ℝ) : Prop :=
  Tendsto cell.positiveBoundary atTop (nhds positiveLimit) ∧
  Tendsto cell.negativeBoundary atTop (nhds negativeLimit) ∧
  Tendsto cell.remainder atTop (nhds 0) ∧
  Tendsto cell.bulk atTop (nhds 0) ∧
  Tendsto cell.surface atTop (nhds surfaceLimit)

/-- A normalized finite-cell balance with vanishing lateral and bulk terms yields the limiting
positive-minus-negative boundary jump. -/
lemma boundaryJump_eq_surfaceLimit {cell : NormalizedThinCellBalance}
    {positiveLimit negativeLimit surfaceLimit : ℝ}
    (h : cell.HasBoundaryLimits positiveLimit negativeLimit surfaceLimit) :
    positiveLimit - negativeLimit = surfaceLimit := by
  have hLeft :
      Tendsto
        (fun scale ↦ cell.positiveBoundary scale - cell.negativeBoundary scale +
          cell.remainder scale)
        atTop (nhds (positiveLimit - negativeLimit)) := by
    simpa using h.1.sub h.2.1 |>.add h.2.2.1
  have hRight :
      Tendsto
        (fun scale ↦ cell.positiveBoundary scale - cell.negativeBoundary scale +
          cell.remainder scale)
        atTop (nhds surfaceLimit) := by
    simpa using
      (h.2.2.2.1.add h.2.2.2.2).congr'
        (Filter.Eventually.of_forall fun scale ↦ (cell.balance scale).symm)
  exact tendsto_nhds_unique hLeft hRight

/-- If the surface contribution vanishes, the two limiting boundary values agree. -/
lemma boundary_eq_of_surface_tendsto_zero {cell : NormalizedThinCellBalance}
    {positiveLimit negativeLimit : ℝ}
    (h : cell.HasBoundaryLimits positiveLimit negativeLimit 0) :
    positiveLimit = negativeLimit := by
  linarith [cell.boundaryJump_eq_surfaceLimit h]

end NormalizedThinCellBalance

end Space
