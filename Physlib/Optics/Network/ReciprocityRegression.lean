/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.Reciprocity

/-!
# Regression for nonidentity-pairing reciprocity gauges

## i. Overview

This file fixes a nonidentity pairing on `Fin 2` and an all-ones paired scattering matrix. Every
matrix value is expanded directly from the swap pairing, the phase gauges, and primitive rephasing.
The expansions do not use the relabeling, inverse-paired sufficiency, diagonal-congruence, or
constant-factor characterization results under test.

S-15 uses incident phases `(1, I)` and their same-label inverses `(1, -I)`. The rephased paired
off-diagonal entries are `-1` and `1`, so reciprocity fails. Moving the output inverse through the
nonidentity pairing gives `(-I, 1)` and restores the symmetric matrix
`!![1, -I; -I, -1]`.

S-16 uses `(1, -1)` on both same-label legs. Its pairing factor is constantly `-1`, and direct
expansion gives the symmetric matrix `!![-1, 1; 1, -1]`. This positive sentinel prevents the
general characterization from being weakened to nominal pairing or only the designated
inverse-paired gauge.

## ii. Key results

- `reciprocityRegression_s15_sameLabel_offDiagonal_ne`: the explicit `-1 != 1` witness.
- `reciprocityRegression_s15_sameLabel_not_reciprocal`: S-15 must fail.
- `reciprocityRegression_s15_restoring_matrix`: the pairing-aware restoring expansion.
- `reciprocityRegression_s15_restoring_isReciprocal`: the restoring gauge is symmetric.
- `reciprocityRegression_s16_pairingFactor`: the same-label factor is constantly `-1`.
- `reciprocityRegression_s16_matrix`: the direct nonidentity-pairing expansion.
- `reciprocityRegression_s16_isReciprocal`: S-16 must pass.

## iii. Table of contents

- A. Nonidentity pairing and primitive phases
- B. All-ones paired scattering fixture
- C. S-15 failure and pairing-aware restoration
- D. S-16 constant-factor preservation

## iv. References

S-15 and S-16 are the binding Revision 4 sentinels in
`scratchpad/lanes/decisions/decision-L6.md` and
`scratchpad/lanes/decisions/registry-draft-A1.md`. They exercise the rephasing part of N-07 at
`goal.md:2633` of registered base `b8ef3236`.

These are algebraic coordinate sentinels on a power-normalized `ScatteringMatrix`. A bare pairing
is not time reversal. The fixtures make no losslessness, passivity, raw Jones or Fresnel,
reverse-incidence Maxwell, component, propagation-distance, delay, electromagnetic-power,
measurement, or physical-realization claim. A reference-plane shift remains distinct from
`PortConnectionFamily.IsMatchedGauge`.
-/

@[expose] public section

namespace Optics

noncomputable section

/-!
## A. Nonidentity pairing and primitive phases
-/

/-- Positive quadrature as a unit-complex phase. -/
def reciprocityRegressionI : Circle :=
  ⟨Complex.I, by simp [Submonoid.unitSphere]⟩

/-- Negative quadrature as a unit-complex phase. -/
def reciprocityRegressionNegI : Circle :=
  ⟨-Complex.I, by simp [Submonoid.unitSphere]⟩

/-- The negative real unit phase. -/
def reciprocityRegressionNegOne : Circle :=
  ⟨-1, by simp [Submonoid.unitSphere]⟩

/-- The nonidentity pairing swaps the two underlying labels. -/
def reciprocityRegressionSwapPairing : ChannelPairing (Fin 2) :=
  Incident.channelEquiv.trans
    ((Equiv.swap (0 : Fin 2) 1).trans Outgoing.channelEquiv.symm)

/-- Label zero is paired with outgoing label one. -/
@[simp]
lemma reciprocityRegressionSwapPairing_zero :
    reciprocityRegressionSwapPairing (Incident.mk 0) = Outgoing.mk 1 := by
  simp [reciprocityRegressionSwapPairing]

/-- Label one is paired with outgoing label zero. -/
@[simp]
lemma reciprocityRegressionSwapPairing_one :
    reciprocityRegressionSwapPairing (Incident.mk 1) = Outgoing.mk 0 := by
  simp [reciprocityRegressionSwapPairing]

/-- S-15 incident phases are `1` and `I`. -/
def reciprocityRegressionS15Incident : ModePhaseGauge (Fin 2) :=
  ![(1 : Circle), reciprocityRegressionI]

/-- S-15's hostile same-label output phases are `1` and `-I`. -/
def reciprocityRegressionS15SameLabelOutgoing : ModePhaseGauge (Fin 2) :=
  ![(1 : Circle), reciprocityRegressionNegI]

/-- S-15's pairing-aware restoring output phases are `-I` and `1`. -/
def reciprocityRegressionS15RestoringOutgoing : ModePhaseGauge (Fin 2) :=
  ![reciprocityRegressionNegI, (1 : Circle)]

/-- S-16 uses the same-label phases `1` and `-1` on both legs. -/
def reciprocityRegressionS16Gauge : ModePhaseGauge (Fin 2) :=
  ![(1 : Circle), reciprocityRegressionNegOne]

/-!
## B. All-ones paired scattering fixture
-/

/-- The primitive scattering transform whose every entry is one. -/
def reciprocityRegressionAllOnes : ScatteringMatrix (Fin 2) where
  toModeTransform := fun _ _ => 1

/-- The primitive paired matrix is exactly the all-ones matrix. -/
lemma reciprocityRegressionAllOnes_pairedMatrix :
    reciprocityRegressionAllOnes.pairedMatrix reciprocityRegressionSwapPairing =
      !![(1 : ℂ), 1; 1, 1] := by
  ext output input
  fin_cases output <;> fin_cases input <;> rfl

/-- The all-ones fixture is symmetric before any rephasing. -/
lemma reciprocityRegressionAllOnes_isReciprocal :
    reciprocityRegressionAllOnes.IsReciprocal reciprocityRegressionSwapPairing := by
  change (reciprocityRegressionAllOnes.pairedMatrix
    reciprocityRegressionSwapPairing).IsSymm
  apply Matrix.IsSymm.ext
  intro first second
  rfl

/-!
## C. S-15 failure and pairing-aware restoration
-/

/-- Direct primitive expansion of the S-15 same-label rephasing. -/
lemma reciprocityRegression_s15_sameLabel_matrix :
    (reciprocityRegressionAllOnes.rephase reciprocityRegressionS15Incident
      reciprocityRegressionS15SameLabelOutgoing).pairedMatrix
        reciprocityRegressionSwapPairing =
      !![-Complex.I, (-1 : ℂ); 1, -Complex.I] := by
  ext output input
  fin_cases output <;> fin_cases input <;>
    norm_num [ScatteringMatrix.pairedMatrix, ScatteringMatrix.rephase,
      ModeTransform.rephase, reciprocityRegressionAllOnes,
      reciprocityRegressionSwapPairing, reciprocityRegressionS15Incident,
      reciprocityRegressionS15SameLabelOutgoing, reciprocityRegressionI,
      reciprocityRegressionNegI, Circle.coe_inv, Complex.ext_iff]

/-- S-15 has unequal off-diagonal entries `-1` and `1`. -/
lemma reciprocityRegression_s15_sameLabel_offDiagonal_ne :
    (reciprocityRegressionAllOnes.rephase reciprocityRegressionS15Incident
        reciprocityRegressionS15SameLabelOutgoing).pairedMatrix
          reciprocityRegressionSwapPairing 0 1 ≠
      (reciprocityRegressionAllOnes.rephase reciprocityRegressionS15Incident
        reciprocityRegressionS15SameLabelOutgoing).pairedMatrix
          reciprocityRegressionSwapPairing 1 0 := by
  rw [reciprocityRegression_s15_sameLabel_matrix]
  norm_num

/-- S-15: same-label inversion under the nonidentity pairing fails reciprocity. -/
lemma reciprocityRegression_s15_sameLabel_not_reciprocal :
    ¬(reciprocityRegressionAllOnes.rephase reciprocityRegressionS15Incident
      reciprocityRegressionS15SameLabelOutgoing).IsReciprocal
        reciprocityRegressionSwapPairing := by
  intro hReciprocal
  apply reciprocityRegression_s15_sameLabel_offDiagonal_ne
  exact Matrix.IsSymm.apply hReciprocal 1 0

/-- The restoring output gauge satisfies the designated inverse-paired law. -/
lemma reciprocityRegression_s15_restoring_inversePaired (label : Fin 2) :
    reciprocityRegressionS15RestoringOutgoing
        (reciprocityRegressionSwapPairing (Incident.mk label)).channel =
      (reciprocityRegressionS15Incident label)⁻¹ := by
  fin_cases label <;> apply Subtype.ext <;>
    norm_num [reciprocityRegressionS15RestoringOutgoing,
      reciprocityRegressionS15Incident, reciprocityRegressionSwapPairing,
      reciprocityRegressionI, reciprocityRegressionNegI, Circle.coe_inv,
      Complex.ext_iff]

/-- Direct primitive expansion of the S-15 pairing-aware restoring gauge. -/
lemma reciprocityRegression_s15_restoring_matrix :
    (reciprocityRegressionAllOnes.rephase reciprocityRegressionS15Incident
      reciprocityRegressionS15RestoringOutgoing).pairedMatrix
        reciprocityRegressionSwapPairing =
      !![(1 : ℂ), -Complex.I; -Complex.I, -1] := by
  ext output input
  fin_cases output <;> fin_cases input <;>
    norm_num [ScatteringMatrix.pairedMatrix, ScatteringMatrix.rephase,
      ModeTransform.rephase, reciprocityRegressionAllOnes,
      reciprocityRegressionSwapPairing, reciprocityRegressionS15Incident,
      reciprocityRegressionS15RestoringOutgoing, reciprocityRegressionI,
      reciprocityRegressionNegI, Circle.coe_inv, Complex.ext_iff]

/-- The pairing-aware S-15 gauge restores reciprocity by direct matrix expansion. -/
lemma reciprocityRegression_s15_restoring_isReciprocal :
    (reciprocityRegressionAllOnes.rephase reciprocityRegressionS15Incident
      reciprocityRegressionS15RestoringOutgoing).IsReciprocal
        reciprocityRegressionSwapPairing := by
  change ((reciprocityRegressionAllOnes.rephase reciprocityRegressionS15Incident
    reciprocityRegressionS15RestoringOutgoing).pairedMatrix
      reciprocityRegressionSwapPairing).IsSymm
  rw [reciprocityRegression_s15_restoring_matrix]
  apply Matrix.IsSymm.ext
  intro first second
  fin_cases first <;> fin_cases second <;> rfl

/-!
## D. S-16 constant-factor preservation
-/

/-- S-16's pairing factor is constantly `-1` on the nonidentity pairing. -/
lemma reciprocityRegression_s16_pairingFactor (label : Fin 2) :
    (reciprocityRegressionS16Gauge
        (reciprocityRegressionSwapPairing (Incident.mk label)).channel : ℂ) *
        (reciprocityRegressionS16Gauge label : ℂ) = -1 := by
  fin_cases label <;>
    norm_num [reciprocityRegressionS16Gauge, reciprocityRegressionSwapPairing,
      reciprocityRegressionNegOne, Complex.ext_iff]

/-- The S-16 same-label gauge is not the designated inverse-paired gauge. -/
lemma reciprocityRegression_s16_not_inversePaired :
    ¬∀ label,
      reciprocityRegressionS16Gauge
          (reciprocityRegressionSwapPairing (Incident.mk label)).channel =
        (reciprocityRegressionS16Gauge label)⁻¹ := by
  intro hInversePaired
  have hZero := hInversePaired (0 : Fin 2)
  have hZeroCoe := congrArg (fun phase : Circle => (phase : ℂ)) hZero
  norm_num [reciprocityRegressionS16Gauge, reciprocityRegressionSwapPairing,
    reciprocityRegressionNegOne, Circle.coe_inv, Complex.ext_iff] at hZeroCoe

/-- Direct primitive expansion of the S-16 constant-factor rephasing. -/
lemma reciprocityRegression_s16_matrix :
    (reciprocityRegressionAllOnes.rephase reciprocityRegressionS16Gauge
      reciprocityRegressionS16Gauge).pairedMatrix reciprocityRegressionSwapPairing =
      !![(-1 : ℂ), 1; 1, -1] := by
  ext output input
  fin_cases output <;> fin_cases input <;>
    norm_num [ScatteringMatrix.pairedMatrix, ScatteringMatrix.rephase,
      ModeTransform.rephase, reciprocityRegressionAllOnes,
      reciprocityRegressionSwapPairing, reciprocityRegressionS16Gauge,
      reciprocityRegressionNegOne, Circle.coe_inv, Complex.ext_iff]

/-- S-16: the nonidentity-pairing constant-factor gauge preserves reciprocity. -/
lemma reciprocityRegression_s16_isReciprocal :
    (reciprocityRegressionAllOnes.rephase reciprocityRegressionS16Gauge
      reciprocityRegressionS16Gauge).IsReciprocal reciprocityRegressionSwapPairing := by
  change ((reciprocityRegressionAllOnes.rephase reciprocityRegressionS16Gauge
    reciprocityRegressionS16Gauge).pairedMatrix reciprocityRegressionSwapPairing).IsSymm
  rw [reciprocityRegression_s16_matrix]
  apply Matrix.IsSymm.ext
  intro first second
  fin_cases first <;> fin_cases second <;> rfl

end

end Optics
