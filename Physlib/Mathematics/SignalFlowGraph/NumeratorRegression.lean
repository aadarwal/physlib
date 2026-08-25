/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Mathematics.SignalFlowGraph.MasonRegression
public import Physlib.Mathematics.SignalFlowGraph.Numerator

/-!
# Regression tests for the numerator in loop-family form

## i. Overview

The two-node feedback graph is carried through the loop-family form of Mason's formula. Its
numerator is the forward gain and its denominator is one minus the loop gain, and the quotient
agrees with the entry of the inverse system matrix that was computed from the adjugate in the
first regression file.

The same example also settles, for this graph, the one identity that the general development
still leaves open: the forward-path sum and the loop-family sum agree. So the open statement is
not merely plausible, it has a proved instance, and the two presentations of the numerator have
been checked against each other on a graph where both are computable.

## ii. Key results

- `Physlib.SignalFlowGraph.cyclicNumerator_twoNodeLoop`: the loop-family numerator is the forward
  gain.
- `Physlib.SignalFlowGraph.masonNumerator_eq_cyclicNumerator_twoNodeLoop`: the forward-path sum
  and the loop-family sum agree, an instance of the identity left open in general.
- `Physlib.SignalFlowGraph.gain_eq_cyclicNumerator_div_twoNodeLoop`: Mason's formula in
  loop-family form for this graph.

## iii. Table of contents

- A. The loop-family numerator of the single feedback loop
- B. The two presentations of the numerator agree here

## iv. References

The identity checked in section B is the one left open in
`Physlib.Mathematics.SignalFlowGraph.Numerator`, namely
`masonNumerator G s t = cyclicNumerator G s t`. Nothing here proves it in general.

These are algebraic regressions on complex matrices. No physical, optical, or signal-processing
interpretation is asserted.

-/

@[expose] public section

namespace Physlib.SignalFlowGraph

open Matrix

/-!

## A. The loop-family numerator of the single feedback loop

-/

/-- The loop-family numerator of the two-node feedback graph is its forward gain. -/
theorem cyclicNumerator_twoNodeLoop (a b : ℂ) :
    cyclicNumerator (twoNodeLoop a b) 0 1 = a := by
  rw [cyclicNumerator_eq_adjugate, systemMatrix_twoNodeLoop, adjugate_fin_two_of]
  simp

/-- Mason's formula in loop-family form for the two-node feedback graph. -/
theorem gain_eq_cyclicNumerator_div_twoNodeLoop (a b : ℂ) :
    gain (twoNodeLoop a b) 0 1 = a / (1 - a * b) := by
  rw [gain_eq_cyclicNumerator_div_graphDet, cyclicNumerator_twoNodeLoop, graphDet_twoNodeLoop]

/-!

## B. The two presentations of the numerator agree here

-/

/-- For the two-node feedback graph the forward-path sum and the loop-family sum agree. This is an
instance of the identity that the general development leaves open, so the open statement is
supported by a proved case rather than only by its plausibility. -/
theorem masonNumerator_eq_cyclicNumerator_twoNodeLoop (a b : ℂ) :
    masonNumerator (twoNodeLoop a b) 0 1 = cyclicNumerator (twoNodeLoop a b) 0 1 := by
  rw [masonNumerator_twoNodeLoop, cyclicNumerator_twoNodeLoop]

/-- Consequently Mason's quotient in path form and in loop-family form agree for this graph. -/
theorem masonGain_eq_cyclicNumerator_div_twoNodeLoop (a b : ℂ) :
    masonGain (twoNodeLoop a b) 0 1
      = cyclicNumerator (twoNodeLoop a b) 0 1 / graphDet (twoNodeLoop a b) := by
  rw [masonGain, masonNumerator_eq_cyclicNumerator_twoNodeLoop]

end Physlib.SignalFlowGraph
