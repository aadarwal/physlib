/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.HarmonicFlux.ApertureRegressionOrthogonality
public import Physlib.Optics.HarmonicFlux.ModePower

/-!
# Finite-mode aperture-power bridge regressions

## i. Overview

This file packages the exact two-cell positive-flux profiles as a two-mode outgoing family. It
independently computes modal coordinate power and measured field flux before comparing the two
normalization conventions.

The outgoing amplitude `(2 + I, 1 - I)` has modal power seven and synthesized aperture flux seven.
These are statements only on the declared synthesis image, not completeness or whole-device
conservation.

## ii. Key results

- `apertureFluxRegressionPositiveModes_isApertureFluxOrthonormal`: exact outgoing normalization.
- `apertureFluxRegressionAmplitude_power`: independent modal power `7`.
- `apertureFluxRegressionSynthesis_pairing`: independent synthesized field pairing `7`.
- `apertureFluxRegressionSynthesis_pairing_smul_first` and
  `apertureFluxRegressionSynthesis_pairing_smul_second`: end-to-end complex slot convention.
- `apertureFluxRegressionSynthesis_flux`: independently computed outgoing flux `7`.

## iii. Table of contents

- A. Outgoing two-mode family
- B. Exact outgoing synthesis

## iv. References

This regression uses the finite-cell measure convention declared in `ApertureRegression`. It adds
no Jones coercion, Maxwell-mode, modal-completeness, or device-losslessness claim.
-/

@[expose] public section

namespace Optics

open InnerProductSpace MeasureTheory

noncomputable section

open HarmonicFieldProfile

/-!

## A. Outgoing two-mode family

-/

/-- The two positive-flux aperture profiles, indexed by `Bool`. -/
def apertureFluxRegressionPositiveModes : Bool → HarmonicFieldProfile (Fin 2)
  | false => apertureFluxRegressionPositive
  | true => apertureFluxRegressionSecond

/-- The exact two-profile family is pairwise integrable, mutually flux-orthogonal, and normalized
to positive unit flux. -/
lemma apertureFluxRegressionPositiveModes_isApertureFluxOrthonormal :
    IsApertureFluxOrthonormal Measure.count apertureFluxRegressionPlane .outgoing
      apertureFluxRegressionPositiveModes := by
  refine ⟨fun _ _ ↦ Integrable.of_finite, ?_, ?_⟩
  · intro i
    apply Complex.ofReal_injective
    rw [← signedNormalFluxPairing_self]
    cases i <;>
      simp [apertureFluxRegressionPositiveModes,
        apertureFluxRegressionPositive_self, apertureFluxRegressionSecond_self]
  · intro i j hij
    cases i <;> cases j
    · exact (hij rfl).elim
    · exact apertureFluxRegressionPositive_second
    · simp only [apertureFluxRegressionPositiveModes]
      rw [signedNormalFluxPairing_conj_symm,
        apertureFluxRegressionPositive_second]
      simp
    · exact (hij rfl).elim

/-!

## B. Exact outgoing synthesis

-/

/-- The exact outgoing modal amplitudes `(2 + I, 1 - I)`. -/
def apertureFluxRegressionAmplitude : ModeAmplitude Bool :=
  WithLp.toLp 2 fun
    | false => 2 + Complex.I
    | true => 1 - Complex.I

/-- The two outgoing modal coordinates have total normalized modal power seven. -/
lemma apertureFluxRegressionAmplitude_power :
    apertureFluxRegressionAmplitude.power = 7 := by
  rw [ModeAmplitude.power_eq_sum_normSq]
  norm_num [apertureFluxRegressionAmplitude, Complex.normSq_apply]

/-- Expanding all coherent cross terms gives synthesized signed aperture pairing seven. -/
lemma apertureFluxRegressionSynthesis_pairing :
    signedNormalFluxPairing Measure.count apertureFluxRegressionPlane
        (modeSynthesis apertureFluxRegressionPositiveModes apertureFluxRegressionAmplitude)
        (modeSynthesis apertureFluxRegressionPositiveModes
          apertureFluxRegressionAmplitude) = 7 := by
  have hreverse :
      signedNormalFluxPairing Measure.count apertureFluxRegressionPlane
          apertureFluxRegressionSecond apertureFluxRegressionPositive = 0 := by
    rw [signedNormalFluxPairing_conj_symm,
      apertureFluxRegressionPositive_second]
    simp
  rw [signedNormalFluxPairing_modeSynthesis Measure.count apertureFluxRegressionPlane
    apertureFluxRegressionPositiveModes (fun _ _ ↦ Integrable.of_finite)]
  norm_num [apertureFluxRegressionAmplitude, apertureFluxRegressionPositiveModes,
    apertureFluxRegressionPositive_self, apertureFluxRegressionSecond_self,
    apertureFluxRegressionPositive_second, hreverse, Fintype.sum_bool,
    Complex.star_def, map_add, map_sub, map_ofNat]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Scaling the first modal coordinate vector by `I` scales the synthesized pairing by `I`. -/
lemma apertureFluxRegressionSynthesis_pairing_smul_first :
    signedNormalFluxPairing Measure.count apertureFluxRegressionPlane
        (modeSynthesis apertureFluxRegressionPositiveModes
          (Complex.I • apertureFluxRegressionAmplitude))
        (modeSynthesis apertureFluxRegressionPositiveModes
          apertureFluxRegressionAmplitude) = 7 * Complex.I := by
  rw [map_smul, signedNormalFluxPairing_smul_left,
    apertureFluxRegressionSynthesis_pairing]
  ac_rfl

/-- Scaling the second modal coordinate vector by `I` conjugates that scalar in the pairing. -/
lemma apertureFluxRegressionSynthesis_pairing_smul_second :
    signedNormalFluxPairing Measure.count apertureFluxRegressionPlane
        (modeSynthesis apertureFluxRegressionPositiveModes
          apertureFluxRegressionAmplitude)
        (modeSynthesis apertureFluxRegressionPositiveModes
          (Complex.I • apertureFluxRegressionAmplitude)) = -7 * Complex.I := by
  rw [map_smul, signedNormalFluxPairing_smul_right,
    apertureFluxRegressionSynthesis_pairing]
  norm_num [Complex.star_def]
  ac_rfl

/-- The independently computed synthesized outgoing aperture flux is exactly seven. -/
lemma apertureFluxRegressionSynthesis_flux :
    integratedMeanNormalFlux Measure.count apertureFluxRegressionPlane
        (modeSynthesis apertureFluxRegressionPositiveModes
          apertureFluxRegressionAmplitude) = 7 := by
  have hself := signedNormalFluxPairing_self Measure.count apertureFluxRegressionPlane
    (modeSynthesis apertureFluxRegressionPositiveModes apertureFluxRegressionAmplitude)
  rw [apertureFluxRegressionSynthesis_pairing] at hself
  have hre := congrArg Complex.re hself
  norm_num at hre ⊢
  exact hre.symm

end


end Optics
