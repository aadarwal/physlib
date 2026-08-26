/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Polarization.Mueller.Basic

/-!
# Pauli trace formula for Jones-induced Mueller matrices

## i. Overview

This file derives every induced Mueller entry from the audited Stokes-ordered Pauli trace pairing.
It separately proves that the complex trace has zero imaginary part, so the real matrix entries are
a theorem about Jones congruence rather than a projection that silently discards complex data.

## ii. Key results

## iii. Table of contents

- A. Pauli trace coefficients and reality

## iv. References

-/

@[expose] public section

namespace Optics

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace JonesMatrix

/-!
## A. Pauli trace coefficients and reality
-/

/-- The Pauli trace used for an induced Mueller entry has zero imaginary part. -/
lemma mueller_trace_im_eq_zero (M : JonesMatrix) (i j : StokesIndex) :
    (Matrix.trace
      (PauliMatrix.pauliMatrix (stokesPauliIndexEquiv i) *
        (M.entries * PauliMatrix.pauliMatrix (stokesPauliIndexEquiv j) *
          M.entriesᴴ))).im = 0 := by
  let A : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ) :=
    M.selfAdjointMap (PauliMatrix.pauliSelfAdjoint (stokesPauliIndexEquiv j))
  have h := PauliMatrix.trace_pauliMatrix_mul_selfAdjoint_re
    (stokesPauliIndexEquiv i) A
  have him := congrArg Complex.im h
  simpa [A, PauliMatrix.pauliSelfAdjoint] using him.symm

/-- An induced Mueller entry is one half of the real Pauli trace pairing. -/
lemma mueller_apply_eq_half_trace_re (M : JonesMatrix) (i j : StokesIndex) :
    M.mueller.entries i j =
      (Matrix.trace
        (PauliMatrix.pauliMatrix (stokesPauliIndexEquiv i) *
          (M.entries * PauliMatrix.pauliMatrix (stokesPauliIndexEquiv j) *
            M.entriesᴴ))).re / 2 := by
  have hsingle : selfAdjointStokesEquiv.symm (EuclideanSpace.single j 1) =
      (1 / 2 : ℝ) • PauliMatrix.pauliSelfAdjoint (stokesPauliIndexEquiv j) := by
    simpa only [StokesVector.toSelfAdjoint] using StokesVector.toSelfAdjoint_single j
  rw [mueller_apply, stokesLinearMap, LinearEquiv.conj_apply_apply, hsingle,
    map_smul, selfAdjointStokesEquiv_apply, PauliMatrix.pauliCoeff_eq_half_trace_re]
  simp only [selfAdjointMap_apply_val, selfAdjoint.val_smul, Matrix.mul_smul,
    Matrix.trace_smul]
  simp [PauliMatrix.pauliSelfAdjoint, Complex.real_smul]
  ring

/-- Casting an induced Mueller entry to `ℂ` gives one half of its Pauli trace pairing. -/
lemma mueller_trace_formula (M : JonesMatrix) (i j : StokesIndex) :
    (M.mueller.entries i j : ℂ) =
      Matrix.trace
        (PauliMatrix.pauliMatrix (stokesPauliIndexEquiv i) *
          (M.entries * PauliMatrix.pauliMatrix (stokesPauliIndexEquiv j) * M.entriesᴴ)) / 2 := by
  apply Complex.ext
  · simp [mueller_apply_eq_half_trace_re]
  · simp [mueller_trace_im_eq_zero]

end JonesMatrix

end

end Optics
