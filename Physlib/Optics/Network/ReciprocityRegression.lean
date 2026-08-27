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

The remaining fixtures enforce the convention registry at the algebraic structure level. A toy
four-predicate realization accepts the swap pairing and refuses the nominal pairing. A wrong-sign
reference-plane gauge changes `-I` to `I`. Finally, a raw-symmetric matrix fails paired symmetry,
while a Hermitian matrix fails transpose symmetry. These are finite sentinels, not physical
component instances.

## ii. Key results

- `reciprocityRegression_s15_sameLabel_offDiagonal_ne`: the explicit `-1 != 1` witness.
- `reciprocityRegression_s15_sameLabel_not_reciprocal`: S-15 must fail.
- `reciprocityRegression_s15_restoring_matrix`: the pairing-aware restoring expansion.
- `reciprocityRegression_s15_restoring_isReciprocal`: the restoring gauge is symmetric.
- `reciprocityRegression_s16_pairingFactor`: the same-label factor is constantly `-1`.
- `reciprocityRegression_s16_matrix`: the direct nonidentity-pairing expansion.
- `reciprocityRegression_s16_isReciprocal`: S-16 must pass.
- `reciprocityRegression_nominal_not_timeReversalRealization`: a wrong toy pairing is refused.
- `reciprocityRegression_s15_wrongSign_not_reciprocal`: a wrong shift sign is refused.
- `reciprocityRegression_rawSymmetric_not_reciprocal`: raw symmetry is insufficient.
- `reciprocityRegression_hermitian_not_reciprocal`: conjugate symmetry is insufficient.

## iii. Table of contents

- A. Nonidentity pairing and primitive phases
- B. All-ones paired scattering fixture
- C. S-15 failure and pairing-aware restoration
- D. S-16 constant-factor preservation
- E. Structure-level time-reversal pairing sentinel
- F. Wrong-sign reference-plane sentinel
- G. Raw-symmetry and conjugate-symmetry sentinels

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

C-07 is enforced here only for the abstract proof-bearing structure using explicitly toy
predicates. Supplying physical component instances remains N6b's obligation. C-08 and C-09 are
enforced only as the algebraic reference-plane and paired-transpose conventions represented by
the concrete fixtures below.
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

/-- The wrong-sign output gauge is `I` and `1` after transport through the swap pairing. -/
def reciprocityRegressionS15WrongSignOutgoing : ModePhaseGauge (Fin 2) :=
  ![reciprocityRegressionI, (1 : Circle)]

/-- S-16 uses the same-label phases `1` and `-1` on both legs. -/
def reciprocityRegressionS16Gauge : ModePhaseGauge (Fin 2) :=
  ![(1 : Circle), reciprocityRegressionNegOne]

/-- S-15 incident coordinate zero has phase one. -/
@[simp]
lemma reciprocityRegressionS15Incident_zero :
    reciprocityRegressionS15Incident 0 = 1 := rfl

/-- S-15 incident coordinate one has phase `I`. -/
@[simp]
lemma reciprocityRegressionS15Incident_one :
    reciprocityRegressionS15Incident 1 = reciprocityRegressionI := rfl

/-- S-15 hostile outgoing coordinate zero has phase one. -/
@[simp]
lemma reciprocityRegressionS15SameLabelOutgoing_zero :
    reciprocityRegressionS15SameLabelOutgoing 0 = 1 := rfl

/-- S-15 hostile outgoing coordinate one has phase `-I`. -/
@[simp]
lemma reciprocityRegressionS15SameLabelOutgoing_one :
    reciprocityRegressionS15SameLabelOutgoing 1 = reciprocityRegressionNegI := rfl

/-- S-15 restoring outgoing coordinate zero has phase `-I`. -/
@[simp]
lemma reciprocityRegressionS15RestoringOutgoing_zero :
    reciprocityRegressionS15RestoringOutgoing 0 = reciprocityRegressionNegI := rfl

/-- S-15 restoring outgoing coordinate one has phase one. -/
@[simp]
lemma reciprocityRegressionS15RestoringOutgoing_one :
    reciprocityRegressionS15RestoringOutgoing 1 = 1 := rfl

/-- The wrong-sign output gauge has phase `I` at coordinate zero. -/
@[simp]
lemma reciprocityRegressionS15WrongSignOutgoing_zero :
    reciprocityRegressionS15WrongSignOutgoing 0 = reciprocityRegressionI := rfl

/-- The wrong-sign output gauge has phase one at coordinate one. -/
@[simp]
lemma reciprocityRegressionS15WrongSignOutgoing_one :
    reciprocityRegressionS15WrongSignOutgoing 1 = 1 := rfl

/-- S-16 coordinate zero has phase one. -/
@[simp]
lemma reciprocityRegressionS16Gauge_zero :
    reciprocityRegressionS16Gauge 0 = 1 := rfl

/-- S-16 coordinate one has phase `-1`. -/
@[simp]
lemma reciprocityRegressionS16Gauge_one :
    reciprocityRegressionS16Gauge 1 = reciprocityRegressionNegOne := rfl

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
      reciprocityRegressionI, reciprocityRegressionNegI, Circle.coe_inv,
      Complex.ext_iff]

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
    simp only [Circle.coe_inv] <;>
    norm_num [reciprocityRegressionI, reciprocityRegressionNegI,
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
      reciprocityRegressionI, reciprocityRegressionNegI, Circle.coe_inv,
      Complex.ext_iff]

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
    norm_num [reciprocityRegressionNegOne, Complex.ext_iff]

/-- The S-16 same-label gauge is not the designated inverse-paired gauge. -/
lemma reciprocityRegression_s16_not_inversePaired :
    ¬∀ label,
      reciprocityRegressionS16Gauge
          (reciprocityRegressionSwapPairing (Incident.mk label)).channel =
        (reciprocityRegressionS16Gauge label)⁻¹ := by
  intro hInversePaired
  have hZero := hInversePaired (0 : Fin 2)
  have hZeroCoe := congrArg (fun phase : Circle => (phase : ℂ)) hZero
  norm_num [reciprocityRegressionNegOne, Circle.coe_inv,
    Complex.ext_iff] at hZeroCoe

/-- Direct primitive expansion of the S-16 constant-factor rephasing. -/
lemma reciprocityRegression_s16_matrix :
    (reciprocityRegressionAllOnes.rephase reciprocityRegressionS16Gauge
      reciprocityRegressionS16Gauge).pairedMatrix reciprocityRegressionSwapPairing =
      !![(-1 : ℂ), 1; 1, -1] := by
  ext output input
  fin_cases output <;> fin_cases input <;>
    norm_num [ScatteringMatrix.pairedMatrix, ScatteringMatrix.rephase,
      ModeTransform.rephase, reciprocityRegressionAllOnes,
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

/-!
## E. Structure-level time-reversal pairing sentinel
-/

/-- Toy transverse-mode matching requires the direction-reversing swap.

This predicate is a regression fixture and carries no component or physical-mode claim.
-/
def reciprocityRegressionToySameTransverseMode (incident : Incident (Fin 2))
    (outgoing : Outgoing (Fin 2)) : Prop :=
  outgoing.channel = (Equiv.swap (0 : Fin 2) 1) incident.channel

/-- Toy plane matching pins the complementary finite labels.

This predicate is a regression fixture and carries no reference-plane geometry.
-/
def reciprocityRegressionToySameReferencePlane (incident : Incident (Fin 2))
    (outgoing : Outgoing (Fin 2)) : Prop :=
  outgoing.channel.val + incident.channel.val = 1

/-- Toy normalization matching requires distinct finite labels.

This predicate is a regression fixture and carries no electromagnetic-power semantics.
-/
def reciprocityRegressionToyEqualPowerNormalization (incident : Incident (Fin 2))
    (outgoing : Outgoing (Fin 2)) : Prop :=
  outgoing.channel ≠ incident.channel

/-- Toy frame transport requires the direction-reversing swap.

This predicate is a regression fixture and carries no physical frame or Jones-vector data.
-/
def reciprocityRegressionToyExactFrameTransport (incident : Incident (Fin 2))
    (outgoing : Outgoing (Fin 2)) : Prop :=
  outgoing.channel = (Equiv.swap (0 : Fin 2) 1) incident.channel

/-- The explicit swap pairing satisfies all four toy component predicates. -/
lemma reciprocityRegressionSwap_timeReversalRealization :
    TimeReversalRealization reciprocityRegressionSwapPairing
      reciprocityRegressionToySameTransverseMode
      reciprocityRegressionToySameReferencePlane
      reciprocityRegressionToyEqualPowerNormalization
      reciprocityRegressionToyExactFrameTransport := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    intro incident
    rcases incident with ⟨label⟩
    fin_cases label <;>
      simp [reciprocityRegressionToySameTransverseMode,
        reciprocityRegressionToySameReferencePlane,
        reciprocityRegressionToyEqualPowerNormalization,
        reciprocityRegressionToyExactFrameTransport,
        reciprocityRegressionSwapPairing]

/-- The nominal identity pairing is refused when the toy predicates demand direction reversal. -/
lemma reciprocityRegression_nominal_not_timeReversalRealization :
    ¬TimeReversalRealization (nominalPairing : ChannelPairing (Fin 2))
      reciprocityRegressionToySameTransverseMode
      reciprocityRegressionToySameReferencePlane
      reciprocityRegressionToyEqualPowerNormalization
      reciprocityRegressionToyExactFrameTransport := by
  intro realization
  have hZero := realization.same_transverse_mode (Incident.mk 0)
  simp [reciprocityRegressionToySameTransverseMode, nominalPairing] at hZero

/-!
## F. Wrong-sign reference-plane sentinel
-/

/-- Direct primitive expansion when the output shift uses the incident sign after pairing. -/
lemma reciprocityRegression_s15_wrongSign_matrix :
    (reciprocityRegressionAllOnes.rephase reciprocityRegressionS15Incident
      reciprocityRegressionS15WrongSignOutgoing).pairedMatrix
        reciprocityRegressionSwapPairing =
      !![(1 : ℂ), -Complex.I; Complex.I, 1] := by
  ext output input
  fin_cases output <;> fin_cases input <;>
    norm_num [ScatteringMatrix.pairedMatrix, ScatteringMatrix.rephase,
      ModeTransform.rephase, reciprocityRegressionAllOnes,
      reciprocityRegressionI, Circle.coe_inv, Complex.ext_iff]

/-- The wrong-sign gauge changes the pinned lower-left value from `-I` to `I`. -/
lemma reciprocityRegression_s15_wrongSign_changes_pinned_entry :
    (reciprocityRegressionAllOnes.rephase reciprocityRegressionS15Incident
        reciprocityRegressionS15WrongSignOutgoing).pairedMatrix
          reciprocityRegressionSwapPairing 1 0 ≠
      (reciprocityRegressionAllOnes.rephase reciprocityRegressionS15Incident
        reciprocityRegressionS15RestoringOutgoing).pairedMatrix
          reciprocityRegressionSwapPairing 1 0 := by
  rw [reciprocityRegression_s15_wrongSign_matrix,
    reciprocityRegression_s15_restoring_matrix]
  norm_num [Complex.ext_iff]

/-- The wrong-sign reference-plane gauge fails paired reciprocity. -/
lemma reciprocityRegression_s15_wrongSign_not_reciprocal :
    ¬(reciprocityRegressionAllOnes.rephase reciprocityRegressionS15Incident
      reciprocityRegressionS15WrongSignOutgoing).IsReciprocal
        reciprocityRegressionSwapPairing := by
  intro hReciprocal
  have hOffDiagonal := Matrix.IsSymm.apply hReciprocal 1 0
  rw [reciprocityRegression_s15_wrongSign_matrix] at hOffDiagonal
  norm_num [Complex.ext_iff] at hOffDiagonal

/-!
## G. Raw-symmetry and conjugate-symmetry sentinels
-/

/-- A primitive raw-symmetric matrix whose diagonal entries distinguish the paired rows. -/
def reciprocityRegressionRawSymmetric : ScatteringMatrix (Fin 2) where
  toModeTransform := !![(1 : ℂ), 0; 0, 2]

/-- The fixture is symmetric in its unpaired coordinate order. -/
lemma reciprocityRegressionRawSymmetric_isSymm :
    reciprocityRegressionRawSymmetric.toModeTransform.IsSymm := by
  apply Matrix.IsSymm.ext
  intro first second
  fin_cases first <;> fin_cases second <;> rfl

/-- Swapping the outgoing pairing rows exposes the asymmetric values `2` and `1`. -/
lemma reciprocityRegressionRawSymmetric_pairedMatrix :
    reciprocityRegressionRawSymmetric.pairedMatrix
        reciprocityRegressionSwapPairing =
      !![(0 : ℂ), 2; 1, 0] := by
  ext output input
  fin_cases output <;> fin_cases input <;> rfl

/-- A raw-symmetric matrix is refused by paired reciprocity for the nonidentity pairing. -/
lemma reciprocityRegression_rawSymmetric_not_reciprocal :
    ¬reciprocityRegressionRawSymmetric.IsReciprocal
      reciprocityRegressionSwapPairing := by
  intro hReciprocal
  have hOffDiagonal := Matrix.IsSymm.apply hReciprocal 1 0
  rw [reciprocityRegressionRawSymmetric_pairedMatrix] at hOffDiagonal
  norm_num at hOffDiagonal

/-- A primitive Hermitian matrix with unequal transpose off-diagonal entries `I` and `-I`. -/
def reciprocityRegressionHermitian : ScatteringMatrix (Fin 2) where
  toModeTransform := !![(0 : ℂ), Complex.I; -Complex.I, 0]

/-- The primitive conjugate-transpose expansion verifies that the fixture is Hermitian. -/
lemma reciprocityRegressionHermitian_isHermitian :
    reciprocityRegressionHermitian.toModeTransform.IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro first second
  fin_cases first <;> fin_cases second <;>
    norm_num [reciprocityRegressionHermitian, Complex.ext_iff]

/-- The Hermitian fixture's transpose off-diagonal entries `I` and `-I` are unequal. -/
lemma reciprocityRegressionHermitian_offDiagonal_ne :
    reciprocityRegressionHermitian.toModeTransform 0 1 ≠
      reciprocityRegressionHermitian.toModeTransform 1 0 := by
  norm_num [reciprocityRegressionHermitian, Complex.ext_iff]

/-- Hermitian symmetry is refused as a substitute for nominal paired-transpose reciprocity. -/
lemma reciprocityRegression_hermitian_not_reciprocal :
    ¬reciprocityRegressionHermitian.IsReciprocal
      (nominalPairing : ChannelPairing (Fin 2)) := by
  intro hReciprocal
  apply reciprocityRegressionHermitian_offDiagonal_ne
  exact Matrix.IsSymm.apply hReciprocal 1 0

end

end Optics
