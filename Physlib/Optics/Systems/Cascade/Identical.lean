/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Physlib.Optics.Systems.Cascade.Heterogeneous

/-!
# Identical DATE cascades and the Sylvester form

## i. Overview

DATE'14 Thm. 4 specializes the source cascade to a replicated stage. The neutral fold theorem at
`Physlib/Optics/Network/TwoPortChainFold.lean:108-114` makes that specialization the power of one
stage matrix.

The source's following, unnumbered Sylvester result is recorded at `HOL-CORPUS.md:207`. Its
notation `|m| = 1` means the two-by-two determinant is one, not that a matrix norm is one. The
other hypotheses are retained literally: `-1 < Re(m11) < 1`, `m22 = conj(m11)`, and
`m12 = conj(m21)`. Coordinate zero is DATE's backward coordinate and coordinate one its forward
coordinate, using the reindex at
`Physlib/Optics/Systems/Microring/SourceBridgeDate.lean:990-1022`.

The determinant-one algebraic core uses Mathlib's integer-indexed second-kind polynomials
`Polynomial.Chebyshev.U`. The source domain then identifies the half trace with `Re(m11)`, puts
the real angle strictly between zero and `pi`, and converts the polynomial coefficients to sine
quotients. This yields the source display
`sin(N*theta)/sin(theta) * m - sin((N-1)*theta)/sin(theta) * 1`.

## ii. Key results

- `dateIdenticalCascadeComposition_eq_pow`: DATE Thm. 4 as a replicated-stage matrix power.
- `dateChain_pow_eq_chebyshevClosedForm_of_det_eq_one`: the determinant-one polynomial core.
- `DateSylvesterHypotheses`: the source's exact determinant, trace, and conjugacy domain.
- `dateChain_pow_eq_sylvesterClosedForm`: the source sine form on that domain.
- `dateIdenticalCascadeComposition_eq_sylvesterClosedForm`: the closed identical cascade.

## iii. Table of contents

- A. Identical DATE cascades
- B. Chebyshev matrix-power core
- C. Source hypotheses and Sylvester sine form

## iv. References and non-claims

DATE'14 Thm. 4 and the unnumbered Sylvester result are summarized at
`HOL-CORPUS.md:204-207`. The sine formula is asserted only under `DateSylvesterHypotheses`; no
claim is made at a zero sine denominator or outside the strict trace interval. The polynomial
core has the weaker determinant-one domain stated on its declaration. The matrices and sine
quotients remain totalized outside those gates, but no source identity is inferred there.

This module makes no quadruple-ring, coupled-lattice, full `M x N` lattice, termination, or
resonance claim. Effective index is constant at the selected carrier; no dispersion, bending
loss, bandwidth, causality, passivity, reciprocity, or material realization is modeled. It makes
no SFG-TR'14 or NSV'16 comparison; any later comparison must retain the explicit
principal-root/selected-half-arc branch gate.

Power means normalized modal power, not electromagnetic power before the bridge at
`Physlib/Optics/HarmonicFlux/PropagatingModePower.lean:16-22,60-93`. That bridge requires finite,
common-frequency Maxwell profiles which are pairwise integrable, mutually flux-orthogonal, and
unit normalized on the measured domain. None of those hypotheses is inferred here.
-/

@[expose] public section

namespace Optics

noncomputable section

namespace MicroringCascade

open MicroringSourceBridge
open scoped ComplexConjugate

/-!

## A. Identical DATE cascades

-/

/-- Relational DATE cascade formed by repeating one source stage `count` times. -/
def dateIdenticalCascadeBehavior (stage : DateCascadeStage) (count : ℕ) :
    BackwardFirstTwoPortBehavior Unit Unit :=
  dateCascadeBehavior (List.replicate count stage)

/-- DATE cascade composition formed by repeating one source stage `count` times. -/
def dateIdenticalCascadeComposition (stage : DateCascadeStage) (count : ℕ) :
    BackwardFirstChainTransform Unit Unit :=
  dateCascadeComposition (List.replicate count stage)

/-- DATE'14 Thm. 4: an identical cascade is the power of its one-stage matrix.

The list is in input-to-output order, and the fold-to-power result is
`Physlib/Optics/Network/TwoPortChainFold.lean:108-114`.
-/
theorem dateIdenticalCascadeComposition_eq_pow
    (stage : DateCascadeStage) (count : ℕ) :
    dateIdenticalCascadeComposition stage count = stage.compositionMatrix ^ count := by
  rw [dateIdenticalCascadeComposition, dateCascadeComposition, List.map_replicate,
    BackwardFirstChainTransform.fold_replicate]

/-- On the exact DATE ring pivot, the repeated relational cascade is the graph of the power. -/
theorem dateIdenticalCascadeBehavior_eq_pow_toBehavior
    (stage : DateCascadeStage) (count : ℕ)
    (hTransmission : stage.HasBijectiveRingTransmission) :
    dateIdenticalCascadeBehavior stage count =
      (stage.compositionMatrix ^ count).toBehavior := by
  rw [dateIdenticalCascadeBehavior,
    dateCascadeBehavior_eq_composition_toBehavior]
  · change (dateIdenticalCascadeComposition stage count).toBehavior = _
    rw [dateIdenticalCascadeComposition_eq_pow]
  · intro repeated hRepeated
    rw [List.eq_of_mem_replicate hRepeated]
    exact hTransmission

/-!

## B. Chebyshev matrix-power core

-/

/-- A chain-matrix entry in DATE's source `Fin 2` order.

The reindex is fixed at
`Physlib/Optics/Systems/Microring/SourceBridgeDate.lean:990-1022`: zero is backward and one is
forward.
-/
def dateChainEntry (matrix : BackwardFirstChainTransform Unit Unit)
    (output input : Fin 2) : ℂ :=
  matrix (dateBackwardFirstFinEquiv output) (dateBackwardFirstFinEquiv input)

/-- Half the trace of a DATE-ordered chain matrix. -/
def dateChainHalfTrace (matrix : BackwardFirstChainTransform Unit Unit) : ℂ :=
  Matrix.trace matrix / 2

/-- The evaluated second-kind Chebyshev coefficient `U_order(trace(matrix)/2)`. -/
def dateChebyshevCoefficient
    (matrix : BackwardFirstChainTransform Unit Unit) (order : ℤ) : ℂ :=
  (Polynomial.Chebyshev.U ℂ order).eval (dateChainHalfTrace matrix)

/-- The determinant-one Chebyshev candidate for a chain-matrix power.

Integer orders make the formula uniform at zero: Mathlib gives `U_(-1) = 0` and
`U_(-2) = -1`.
-/
def dateChebyshevClosedForm
    (matrix : BackwardFirstChainTransform Unit Unit) (count : ℕ) :
    BackwardFirstChainTransform Unit Unit :=
  dateChebyshevCoefficient matrix ((count : ℤ) - 1) • matrix -
    dateChebyshevCoefficient matrix ((count : ℤ) - 2) • 1

/-- DATE's typed chain trace is the sum of its two source diagonal entries. -/
lemma dateChain_trace_eq_entry11_add_entry22
    (matrix : BackwardFirstChainTransform Unit Unit) :
    Matrix.trace matrix = dateChainEntry matrix 0 0 + dateChainEntry matrix 1 1 := by
  rw [Matrix.trace]
  simp_rw [Fintype.sum_sum_type, ← BackwardWave.channelEquiv.symm.sum_comp,
    ← ForwardWave.channelEquiv.symm.sum_comp]
  simp [dateChainEntry, dateBackwardFirstFinEquiv]

/-- Evaluated second-kind Chebyshev coefficients obey their defining recurrence. -/
lemma dateChebyshevCoefficient_recurrence
    (matrix : BackwardFirstChainTransform Unit Unit) (order : ℤ) :
    dateChebyshevCoefficient matrix order =
      2 * dateChainHalfTrace matrix *
          dateChebyshevCoefficient matrix (order - 1) -
        dateChebyshevCoefficient matrix (order - 2) := by
  change (Polynomial.Chebyshev.U ℂ order).eval (dateChainHalfTrace matrix) = _
  rw [Polynomial.Chebyshev.U_eq]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_ofNat, Polynomial.eval_X, dateChebyshevCoefficient]

/-- Cayley--Hamilton for a determinant-one two-coordinate chain matrix. -/
lemma dateChain_sq_eq_trace_smul_sub_one
    (matrix : BackwardFirstChainTransform Unit Unit)
    (hDeterminant : Matrix.det matrix = 1) :
    matrix ^ 2 = Matrix.trace matrix • matrix - 1 := by
  have hCard : Fintype.card (BackwardWave Unit ⊕ ForwardWave Unit) = 2 := by
    simp [Fintype.card_sum, BackwardWave.fintype_card, ForwardWave.fintype_card]
  have hCayley := Matrix.aeval_self_charpoly matrix
  rw [matrix.charpoly_of_card_eq_two hCard] at hCayley
  simp [hDeterminant, pow_two] at hCayley
  rw [← Algebra.smul_def] at hCayley
  rw [pow_two, eq_sub_iff_add_eq]
  calc
    matrix * matrix + 1 = matrix * matrix - Matrix.trace matrix • matrix + 1 +
        Matrix.trace matrix • matrix := by abel
    _ = Matrix.trace matrix • matrix := by rw [hCayley, zero_add]

/-- A determinant-one two-coordinate chain power equals its Chebyshev closed form.

No trace bound or conjugacy is needed for this polynomial identity. Those stronger source
hypotheses enter only when the coefficients are divided by `sin(theta)` below.
-/
lemma dateChain_pow_eq_chebyshevClosedForm_of_det_eq_one
    (matrix : BackwardFirstChainTransform Unit Unit)
    (hDeterminant : Matrix.det matrix = 1) (count : ℕ) :
    matrix ^ count = dateChebyshevClosedForm matrix count := by
  have hCayley := dateChain_sq_eq_trace_smul_sub_one matrix hDeterminant
  have hTrace : Matrix.trace matrix = 2 * dateChainHalfTrace matrix := by
    simp only [dateChainHalfTrace]
    ring
  rw [hTrace] at hCayley
  induction count with
  | zero =>
      simp [dateChebyshevClosedForm, dateChebyshevCoefficient,
        Polynomial.Chebyshev.U_neg_one, Polynomial.Chebyshev.U_neg_two]
  | succ count ih =>
      rw [pow_succ, ih]
      change
        (dateChebyshevCoefficient matrix ((count : ℤ) - 1) • matrix -
            dateChebyshevCoefficient matrix ((count : ℤ) - 2) • 1) * matrix =
          dateChebyshevCoefficient matrix (((count + 1 : ℕ) : ℤ) - 1) • matrix -
            dateChebyshevCoefficient matrix (((count + 1 : ℕ) : ℤ) - 2) • 1
      simp only [sub_mul, Matrix.smul_mul, one_mul]
      rw [← pow_two, hCayley]
      ext output input
      simp only [Matrix.sub_apply, Matrix.smul_apply]
      rw [show (((count + 1 : ℕ) : ℤ) - 1) = count by omega,
        show (((count + 1 : ℕ) : ℤ) - 2) = (count : ℤ) - 1 by omega,
        show dateChebyshevCoefficient matrix count =
            2 * dateChainHalfTrace matrix *
                dateChebyshevCoefficient matrix ((count : ℤ) - 1) -
              dateChebyshevCoefficient matrix ((count : ℤ) - 2) by
          exact dateChebyshevCoefficient_recurrence matrix count]
      ring

/-!

## C. Source hypotheses and Sylvester sine form

-/

/-- The exact domain of DATE'14's unnumbered Sylvester/Chebyshev formula.

The source notation `|m| = 1` is represented by `Matrix.det matrix = 1`. The remaining fields are
the strict `Re(m11)` interval and its two printed complex-conjugacy equations, as recorded at
`HOL-CORPUS.md:207`.
-/
structure DateSylvesterHypotheses
    (matrix : BackwardFirstChainTransform Unit Unit) : Prop where
  /-- The source's `|m| = 1`, interpreted as determinant one. -/
  det_eq_one : Matrix.det matrix = 1
  /-- The strict lower trace-domain bound on `Re(m11)`. -/
  entry11_re_gt_neg_one : -1 < (dateChainEntry matrix 0 0).re
  /-- The strict upper trace-domain bound on `Re(m11)`. -/
  entry11_re_lt_one : (dateChainEntry matrix 0 0).re < 1
  /-- The source diagonal symmetry `m22 = conj(m11)`. -/
  entry22_eq_conj_entry11 :
    dateChainEntry matrix 1 1 = conj (dateChainEntry matrix 0 0)
  /-- The source off-diagonal symmetry `m12 = conj(m21)`. -/
  entry12_eq_conj_entry21 :
    dateChainEntry matrix 0 1 = conj (dateChainEntry matrix 1 0)

/-- The real Sylvester angle on the source trace branch. -/
def dateSylvesterAngle (matrix : BackwardFirstChainTransform Unit Unit) : ℝ :=
  Real.arccos (dateChainEntry matrix 0 0).re

/-- The source coefficient `sin(order*theta) / sin(theta)`, coerced to complex scalars. -/
def dateSylvesterSineCoefficient
    (matrix : BackwardFirstChainTransform Unit Unit) (order : ℤ) : ℂ :=
  (Real.sin ((order : ℝ) * dateSylvesterAngle matrix) /
    Real.sin (dateSylvesterAngle matrix) : ℝ)

/-- DATE'14's totalized Sylvester sine-form candidate.

At `count = N` this is
`sin(N*theta)/sin(theta) * matrix - sin((N-1)*theta)/sin(theta) * 1`.
-/
def dateSylvesterClosedForm
    (matrix : BackwardFirstChainTransform Unit Unit) (count : ℕ) :
    BackwardFirstChainTransform Unit Unit :=
  dateSylvesterSineCoefficient matrix count • matrix -
    dateSylvesterSineCoefficient matrix ((count : ℤ) - 1) • 1

/-- Source diagonal conjugacy makes the complex half trace equal to the real part of `m11`. -/
lemma DateSylvesterHypotheses.halfTrace_eq_entry11_re
    {matrix : BackwardFirstChainTransform Unit Unit}
    (h : DateSylvesterHypotheses matrix) :
    dateChainHalfTrace matrix = (dateChainEntry matrix 0 0).re := by
  rw [dateChainHalfTrace, dateChain_trace_eq_entry11_add_entry22,
    h.entry22_eq_conj_entry11, Complex.add_conj]
  norm_num

/-- The source's strict trace interval makes its sine denominator nonzero. -/
lemma DateSylvesterHypotheses.sin_angle_ne_zero
    {matrix : BackwardFirstChainTransform Unit Unit}
    (h : DateSylvesterHypotheses matrix) :
    Real.sin (dateSylvesterAngle matrix) ≠ 0 := by
  apply ne_of_gt
  exact Real.sin_pos_of_pos_of_lt_pi
    (Real.arccos_pos.mpr h.entry11_re_lt_one)
    (Real.arccos_lt_pi.mpr h.entry11_re_gt_neg_one)

/-- On the source domain, the complex half trace is the cosine of the real source angle. -/
lemma DateSylvesterHypotheses.halfTrace_eq_cos_angle
    {matrix : BackwardFirstChainTransform Unit Unit}
    (h : DateSylvesterHypotheses matrix) :
    dateChainHalfTrace matrix = (Real.cos (dateSylvesterAngle matrix) : ℂ) := by
  rw [h.halfTrace_eq_entry11_re]
  norm_cast
  symm
  exact Real.cos_arccos h.entry11_re_gt_neg_one.le h.entry11_re_lt_one.le

/-- On the source domain, `U_order` is the corresponding sine quotient. -/
lemma DateSylvesterHypotheses.chebyshevCoefficient_eq_sineCoefficient
    {matrix : BackwardFirstChainTransform Unit Unit}
    (h : DateSylvesterHypotheses matrix) (order : ℤ) :
    dateChebyshevCoefficient matrix order =
      dateSylvesterSineCoefficient matrix (order + 1) := by
  rw [dateChebyshevCoefficient, h.halfTrace_eq_cos_angle,
    ← Polynomial.Chebyshev.complex_ofReal_eval_U]
  change (((Polynomial.Chebyshev.U ℝ order).eval
      (Real.cos (dateSylvesterAngle matrix)) : ℝ) : ℂ) =
    ((Real.sin ((((order + 1 : ℤ) : ℝ)) * dateSylvesterAngle matrix) /
      Real.sin (dateSylvesterAngle matrix) : ℝ) : ℂ)
  norm_cast
  apply (eq_div_iff h.sin_angle_ne_zero).2
  rw [Int.cast_add, Int.cast_one]
  exact Polynomial.Chebyshev.U_real_cos (dateSylvesterAngle matrix) order

/-- Sylvester's formula for a DATE-ordered chain matrix on the exact source domain. -/
theorem dateChain_pow_eq_sylvesterClosedForm
    (matrix : BackwardFirstChainTransform Unit Unit)
    (h : DateSylvesterHypotheses matrix) (count : ℕ) :
    matrix ^ count = dateSylvesterClosedForm matrix count := by
  rw [dateChain_pow_eq_chebyshevClosedForm_of_det_eq_one matrix h.det_eq_one count]
  simp only [dateChebyshevClosedForm, dateSylvesterClosedForm]
  rw [h.chebyshevCoefficient_eq_sineCoefficient,
    h.chebyshevCoefficient_eq_sineCoefficient]
  congr 2 <;> congr 1 <;> omega

/-- DATE's identical cascade has the Sylvester sine form on the exact source domain. -/
theorem dateIdenticalCascadeComposition_eq_sylvesterClosedForm
    (stage : DateCascadeStage) (count : ℕ)
    (h : DateSylvesterHypotheses stage.compositionMatrix) :
    dateIdenticalCascadeComposition stage count =
      dateSylvesterClosedForm stage.compositionMatrix count := by
  rw [dateIdenticalCascadeComposition_eq_pow,
    dateChain_pow_eq_sylvesterClosedForm stage.compositionMatrix h count]

end MicroringCascade

end

end Optics
