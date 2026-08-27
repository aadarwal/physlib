/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Mathematics.ZTransform.BasicRegression
public import Physlib.Mathematics.ZTransform.ConvergenceRegression
public import Physlib.Mathematics.ZTransform.Inverse

/-!
# Regression tests for inversion and uniqueness

## i. Overview

The first example is negative and is the reason uniqueness carries a causality hypothesis. Adding
a single sample at index `-1` to the unit impulse changes the sequence but not its unilateral
transform, because the transform never sees a negative index. So two sequences with identical
transforms at every point can differ, and the hypothesis in
`Physlib.ZTransform.eq_of_isCausal_of_transform_eqOn` is load-bearing rather than decorative. The
source states uniqueness for one-sided sequences, where this cannot arise.

The remaining examples are positive. The initial-value theorem and the inversion formula are
instantiated at the causal geometric sequence, recovering its samples at indices zero and one as
limits at infinity. Then uniqueness is used in the direction one actually wants: any causal
sequence whose transform is the one-pole rational function on a suitable exterior *is* the
geometric sequence. That is a characterization, not a computation, and it is the form the
system-level track needs.

## ii. Key results

- `Physlib.ZTransform.transform_shiftedImpulse_eq`: a sequence differing from the unit impulse
  only at index `-1` has the same transform everywhere.
- `Physlib.ZTransform.shiftedImpulse_ne_unitImpulse`: but it is a different sequence, so
  uniqueness without causality is false.
- `Physlib.ZTransform.exists_common_ROC_transform_eqOn_but_ne`: the same example satisfies both
  absolute-ROC premises and exterior transform equality while the sequences remain unequal.
- `Physlib.ZTransform.tendsto_transform_geometricSeq`: the initial-value theorem at the geometric
  sequence.
- `Physlib.ZTransform.tendsto_inversion_geometricSeq_one`: the inversion formula recovering the
  sample at index one.
- `Physlib.ZTransform.eq_geometricSeq_of_transform_eq`: the geometric sequence is the unique
  causal sequence with the one-pole transform.

## iii. Table of contents

- A. Uniqueness fails without causality
- B. Inversion at the geometric sequence
- C. A uniqueness characterization

## iv. References

The related source results are Theorem 15 (inverse z-transform), Theorem 16 (uniqueness), and
Theorem 17 (initial value), all on p. 894 of U. Siddique, M. Y. Mahmoud, and S. Tahar, "Formal
Analysis of Discrete-Time Systems using z-Transform", Journal of Applied Logics 5(4), 2018,
pp. 875--906. These regressions exercise Physlib's absolute-ROC, limit-at-infinity alternatives;
they do not exercise the source's ordered-ROC exterior hypothesis or Taylor-coefficient formula.

Section A records a genuine gap between the source's setting and this one. The source works with
one-sided sequences, so its uniqueness theorem needs no causality hypothesis. Here sequences are
two-sided, and section A proves that the hypothesis cannot be dropped.

These are algebraic and analytic regressions on complex sequences. No physical, optical, or
signal-processing interpretation is asserted.

-/

@[expose] public section

namespace Physlib.ZTransform

noncomputable section

open Filter Bornology

/-!

## A. Uniqueness fails without causality

-/

/-- The unit impulse with an extra sample placed at the negative index `-1`. -/
def shiftedImpulse : ℤ → ℂ := unitImpulse + regressionAtNegOne

/-- The transform series of the added sample is summable, being identically zero. -/
lemma summable_seriesTerm_regressionAtNegOne (z : ℂ) :
    Summable (seriesTerm regressionAtNegOne z) := by
  have hfun : seriesTerm regressionAtNegOne z = 0 :=
    funext (seriesTerm_regressionAtNegOne z)
  rw [hfun]
  exact summable_zero

/-- The extra negative-index sample is invisible to the unilateral transform. -/
lemma transform_shiftedImpulse_eq (z : ℂ) :
    transform shiftedImpulse z = transform unitImpulse z := by
  rw [shiftedImpulse,
    transform_add (summable_seriesTerm_unitImpulse z) (summable_seriesTerm_regressionAtNegOne z),
    transform_regressionAtNegOne, add_zero]

/-- The two sequences are nevertheless different, at the index the transform cannot see. -/
lemma shiftedImpulse_ne_unitImpulse : shiftedImpulse ≠ unitImpulse := by
  intro hcon
  have h := congrFun hcon (-1)
  rw [shiftedImpulse, Pi.add_apply] at h
  simp only [unitImpulse, regressionAtNegOne, if_neg (by norm_num : ¬(-1 : ℤ) = 0),
    zero_add] at h
  exact one_ne_zero h

/-- The added sample is not causal, so the causality hypothesis of the uniqueness theorem is
what excludes this example. -/
lemma shiftedImpulse_not_isCausal : ¬ IsCausal shiftedImpulse := by
  intro hc
  have h := hc (-1) (by norm_num)
  rw [shiftedImpulse, Pi.add_apply] at h
  simp only [unitImpulse, regressionAtNegOne, if_neg (by norm_num : ¬(-1 : ℤ) = 0),
    zero_add] at h
  exact one_ne_zero h

/-- The shifted impulse has an absolute region-of-convergence witness, despite its noncausal
negative-index sample. -/
lemma one_mem_ROC_shiftedImpulse : (1 : ℂ) ∈ ROC shiftedImpulse := by
  refine ⟨one_ne_zero, ?_⟩
  rw [shiftedImpulse]
  exact summable_seriesTerm_add (summable_seriesTerm_unitImpulse 1)
    (summable_seriesTerm_regressionAtNegOne 1)

/-- The unit impulse has the same absolute region-of-convergence witness. -/
lemma one_mem_ROC_unitImpulse : (1 : ℂ) ∈ ROC unitImpulse := by
  rw [ROC_unitImpulse]
  exact one_ne_zero

/-- Without causality, the two absolute-ROC premises and exterior transform equality do not force
equality of two-sided sequences. This bundles the exact noncausal counterexample to the causal
uniqueness lemma. -/
lemma exists_common_ROC_transform_eqOn_but_ne :
    ∃ w : ℂ,
      w ∈ ROC shiftedImpulse ∧
      w ∈ ROC unitImpulse ∧
      (∀ z : ℂ, ‖w‖ ≤ ‖z‖ →
        transform shiftedImpulse z = transform unitImpulse z) ∧
      shiftedImpulse ≠ unitImpulse := by
  exact ⟨1, one_mem_ROC_shiftedImpulse, one_mem_ROC_unitImpulse,
    fun z _ => transform_shiftedImpulse_eq z, shiftedImpulse_ne_unitImpulse⟩

/-!

## B. Inversion at the geometric sequence

-/

/-- The initial-value theorem at the geometric sequence: its transform tends to `1`. -/
lemma tendsto_transform_geometricSeq {a : ℂ} (ha : a ≠ 0) :
    Tendsto (transform (geometricSeq a)) (cobounded ℂ) (nhds 1) := by
  have hzero : geometricSeq a 0 = 1 := by simpa using geometricSeq_natCast a 0
  have h := tendsto_transform_cobounded (two_mul_mem_ROC_geometricSeq ha)
  rwa [hzero] at h

/-- The inversion formula at the geometric sequence recovers the sample at index one, which is
the ratio `a`. -/
lemma tendsto_inversion_geometricSeq_one {a : ℂ} (ha : a ≠ 0) :
    Tendsto (fun z : ℂ => z ^ 1 *
        (transform (geometricSeq a) z - advanceStartup (geometricSeq a) z 1))
      (cobounded ℂ) (nhds a) := by
  have h := tendsto_inversion_cobounded (two_mul_mem_ROC_geometricSeq ha) 1
  rwa [geometricSeq_natCast, pow_one] at h

/-!

## C. A uniqueness characterization

-/

/-- The causal geometric sequence is the unique causal sequence whose transform is the one-pole
rational function on the closed exterior of a circle outside the pole. -/
lemma eq_geometricSeq_of_transform_eq {a : ℂ} (ha : a ≠ 0) {h : ℤ → ℂ} {w : ℂ}
    (hc : IsCausal h) (hw : w ∈ ROC h) (hwa : ‖a‖ < ‖w‖)
    (heq : ∀ z : ℂ, ‖w‖ ≤ ‖z‖ → transform h z = (1 - a * z⁻¹)⁻¹) :
    h = geometricSeq a := by
  have hgw : w ∈ ROC (geometricSeq a) := by
    rw [ROC_geometricSeq ha]
    exact hwa
  refine eq_of_isCausal_of_transform_eqOn hc (geometricSeq_isCausal a) hw hgw fun z hz => ?_
  rw [heq z hz, transform_geometricSeq ha (lt_of_lt_of_le hwa hz)]

end

end Physlib.ZTransform
