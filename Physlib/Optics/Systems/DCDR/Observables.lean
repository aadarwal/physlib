/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Systems.DCDR.Poles

/-!
# Zero-location observables for the double-coupler double-ring

## i. Overview

This file gives the coherent DCDR response certificate a literal reciprocal-coordinate
zero-location observable. It reuses `ReducedRationalResponse.AllZerosInsideUnitDisk` from
`Physlib/Optics/Systems/DelayTransfer/Stability.lean:238-239`; it does not attach a physical
resonance interpretation to that predicate. FMICS'15 Definition 7, p. 170, calls this condition
"resonance", but states only that every nonzero numerator root has norm strictly below one; see
`goal.md:2313-2318`.

FMICS'15 Theorem 5, p. 174, concerns the separately printed incoherent `1 - k`/`k` formula. Its
three printed hypotheses are retained as `PrintedIncoherentTheoremFiveConditions`: a non-strict
complex-square-root bound and two nonzero conditions. The paper itself says that the last two
conditions are absent from Binh [5]'s paper-and-pencil derivation and are necessary for the formal
proof. They are therefore FMICS'15's discoveries, not Physlib corrections.

The printed bound is non-strict although Definition 7's conclusion is strict. Physlib keeps the
printed audit predicate and the strict sufficient predicate separate. The proved adaptation of
Theorem 5 strengthens only that first bound to `< 1`; a regression records that the printed
boundary assumptions do not imply the strict conclusion.

Coherent N7 `t`/`-I * k` is the FMICS'15 source's own unprinted coherent branch. The printed
incoherent `1 - k`/`k` numerator below is a different case. No theorem identifies it with the
coherent response certificate.

## ii. Key definitions and results

- `ResponseReduction.allZerosInsideUnitDisk`: the coherent reduced-response observable.
- `PrintedIncoherentTheoremFiveConditions`: all three hypotheses printed in FMICS'15 Theorem 5.
- `PrintedIncoherentStrictAllZerosConditions`: the strict Physlib sufficient conditions.
- `printedIncoherent_allZerosInsideUnitDisk_of_strict`: the strict zero-location result.

## iii. Table of contents

- A. Coherent reduced-response observable
- B. Printed incoherent zero data
- C. Audited and strict Theorem 5 conditions
- D. Strict zero-location result

## iv. References and non-claims

U. Siddique, S. M. Beillahi, and S. Tahar, "On the Formal Analysis of Photonic Signal
Processing Systems", FMICS 2015, LNCS 9128, Definitions 6-8 and Theorem 5.

This file proves no physical resonance, spectral-power, frequency-response, passivity, or BIBO
theorem. Formal `q` and reciprocal `z` are algebraic coordinates. The printed incoherent result is
not a parity bridge to the coherent N7 netlist.
-/

@[expose] public section

namespace Optics.DCDR

noncomputable section

open Polynomial

/-!

## A. Coherent reduced-response observable

-/

namespace ResponseReduction

variable {p : UnitDelayParameters}

/-- Every finite reciprocal-coordinate zero of the certified coherent DCDR response lies strictly
inside the unit disk.

This is the literal zero-location condition of FMICS'15 Definition 7 with Physlib naming. It is
not a physical resonance predicate.
-/
def allZerosInsideUnitDisk (certificate : ResponseReduction p) : Prop :=
  certificate.reduction.reduced.AllZerosInsideUnitDisk

end ResponseReduction

/-!

## B. Printed incoherent zero data

-/

/-- The coefficient of `q` in FMICS'15 Theorem 5's printed incoherent DCDR numerator. -/
def printedIncoherentZeroLinearCoefficient
    (G1 G2 k1 k2 : ℂ) : ℂ :=
  (1 - k1) * (1 - k2) * G1 + k1 * k2 * G2

/-- The coefficient subtracted at `q^3` in FMICS'15 Theorem 5's printed incoherent numerator. -/
def printedIncoherentZeroCubicCoefficient
    (G1 G2 G3 k1 k2 : ℂ) : ℂ :=
  (1 - 2 * k1) * (1 - 2 * k2) * G1 * G2 * G3

/-- The hand-transcribed unit-delay numerator `L*q - C*q^3` of the printed incoherent DCDR. -/
def printedIncoherentZeroPolynomial
    (G1 G2 G3 k1 k2 : ℂ) : Polynomial ℂ :=
  C (printedIncoherentZeroLinearCoefficient G1 G2 k1 k2) * X -
    C (printedIncoherentZeroCubicCoefficient G1 G2 G3 k1 k2) * X ^ 3

/-- Evaluation exposes the two printed incoherent numerator coefficients directly. -/
lemma eval_printedIncoherentZeroPolynomial
    (G1 G2 G3 k1 k2 q : ℂ) :
    (printedIncoherentZeroPolynomial G1 G2 G3 k1 k2).eval q =
      printedIncoherentZeroLinearCoefficient G1 G2 k1 k2 * q -
        printedIncoherentZeroCubicCoefficient G1 G2 G3 k1 k2 * q ^ 3 := by
  simp [printedIncoherentZeroPolynomial]

/-- Every finite reciprocal-coordinate root of the printed incoherent numerator lies strictly
inside the unit disk.

This states only the zero-location content of FMICS'15 Definition 7. It is deliberately not named
"resonance" and is not a claim about the coherent N7 response.
-/
def PrintedIncoherentAllZerosInsideUnitDisk
    (G1 G2 G3 k1 k2 : ℂ) : Prop :=
  ∀ z : ℂ, z ≠ 0 →
    (printedIncoherentZeroPolynomial G1 G2 G3 k1 k2).eval z⁻¹ = 0 →
      ‖z‖ < 1

/-!

## C. Audited and strict Theorem 5 conditions

-/

/-- The three hypotheses printed in FMICS'15 Theorem 5.

The last two nonzero hypotheses are discoveries reported by FMICS'15 itself: the paper says they
are absent from Binh [5] and necessary for verification. The first bound is printed as `≤ 1`, so
these conditions do not suffice for the paper's own strict Definition 7 conclusion.
-/
def PrintedIncoherentTheoremFiveConditions
    (G1 G2 G3 k1 k2 : ℂ) : Prop :=
  ‖Complex.sqrt
      (printedIncoherentZeroCubicCoefficient G1 G2 G3 k1 k2 /
        printedIncoherentZeroLinearCoefficient G1 G2 k1 k2)‖ ≤ 1 ∧
    printedIncoherentZeroCubicCoefficient G1 G2 G3 k1 k2 ≠ 0 ∧
    printedIncoherentZeroLinearCoefficient G1 G2 k1 k2 ≠ 0

/-- The conditions Physlib uses for the strict all-zeros-inside conclusion.

This retains both nonzero hypotheses discovered by FMICS'15 and strengthens only its non-strict
square-root bound to match Definition 7's strict unit-disk predicate.
-/
def PrintedIncoherentStrictAllZerosConditions
    (G1 G2 G3 k1 k2 : ℂ) : Prop :=
  ‖Complex.sqrt
      (printedIncoherentZeroCubicCoefficient G1 G2 G3 k1 k2 /
        printedIncoherentZeroLinearCoefficient G1 G2 k1 k2)‖ < 1 ∧
    printedIncoherentZeroCubicCoefficient G1 G2 G3 k1 k2 ≠ 0 ∧
    printedIncoherentZeroLinearCoefficient G1 G2 k1 k2 ≠ 0

/-- The strict sufficient conditions imply the exact non-strict source audit conditions. -/
lemma PrintedIncoherentStrictAllZerosConditions.toTheoremFiveConditions
    {G1 G2 G3 k1 k2 : ℂ}
    (hConditions : PrintedIncoherentStrictAllZerosConditions G1 G2 G3 k1 k2) :
    PrintedIncoherentTheoremFiveConditions G1 G2 G3 k1 k2 :=
  ⟨hConditions.1.le, hConditions.2⟩

/-!

## D. Strict zero-location result

-/

/-- FMICS'15 Theorem 5's printed incoherent zero calculation, with the first hypothesis made
strict so that its conclusion matches the paper's own strict Definition 7 predicate.

The two nonzero hypotheses are retained exactly. No coherent/incoherent identification is used.
-/
theorem printedIncoherent_allZerosInsideUnitDisk_of_strict
    (G1 G2 G3 k1 k2 : ℂ)
    (hConditions : PrintedIncoherentStrictAllZerosConditions G1 G2 G3 k1 k2) :
    PrintedIncoherentAllZerosInsideUnitDisk G1 G2 G3 k1 k2 := by
  intro z hz hRoot
  have hEquation :
      printedIncoherentZeroLinearCoefficient G1 G2 k1 k2 * z⁻¹ -
        printedIncoherentZeroCubicCoefficient G1 G2 G3 k1 k2 * z⁻¹ ^ 3 = 0 := by
    simpa [eval_printedIncoherentZeroPolynomial] using hRoot
  have hSquare : z ^ 2 =
      printedIncoherentZeroCubicCoefficient G1 G2 G3 k1 k2 /
        printedIncoherentZeroLinearCoefficient G1 G2 k1 k2 := by
    field_simp [hz, hConditions.2.2] at hEquation ⊢
    linear_combination hEquation
  have hSqrtNorm :
      ‖Complex.sqrt
          (printedIncoherentZeroCubicCoefficient G1 G2 G3 k1 k2 /
            printedIncoherentZeroLinearCoefficient G1 G2 k1 k2)‖ =
        √‖printedIncoherentZeroCubicCoefficient G1 G2 G3 k1 k2 /
            printedIncoherentZeroLinearCoefficient G1 G2 k1 k2‖ := by
    simpa [Complex.sqrt, Real.sqrt_eq_rpow, one_div] using
      Complex.norm_cpow_inv_nat
        (printedIncoherentZeroCubicCoefficient G1 G2 G3 k1 k2 /
          printedIncoherentZeroLinearCoefficient G1 G2 k1 k2) 2
  have hNorm :
      ‖z‖ =
        ‖Complex.sqrt
          (printedIncoherentZeroCubicCoefficient G1 G2 G3 k1 k2 /
            printedIncoherentZeroLinearCoefficient G1 G2 k1 k2)‖ := by
    rw [hSqrtNorm, Real.sqrt_eq_rpow, ← hSquare, norm_pow]
    symm
    simpa [one_div] using
      Real.pow_rpow_inv_natCast (norm_nonneg z) (by norm_num : (2 : ℕ) ≠ 0)
  exact hNorm.trans_lt hConditions.1

end

end Optics.DCDR
