/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.HarmonicFlux.ModePowerRegression

/-!
# Nonorthogonal finite-mode power regression

## i. Overview

This file gives the mutual-orthogonality hypothesis in the aperture-power bridge an exact negative
control. Starting from the two orthonormal positive-flux profiles, it constructs one basis profile
and the normalized `3-4-5` superposition of both profiles. Each has unit self-flux, but their
cross-pairing is `3 / 5`, so the resulting two-profile family is not flux-orthonormal.

The regression prevents individual unit normalization from being mistaken for mutual
orthogonality. The statement remains on a supplied finite synthesis family and measured profile
domain. It is not a modal-completeness or Maxwell-qualification theorem.

## ii. Key results

- `apertureFluxRegressionNonorthogonalModes_each_normalized`: both profiles have unit self-flux.
- `apertureFluxRegressionNonorthogonalModes_cross`: their exact cross-pairing is `3 / 5`.
- `apertureFluxRegressionNonorthogonalSynthesis_pairing`: equal coordinates retain the coherent
  cross terms, giving field self-pairing `16 / 5` rather than coordinate power `2`.
- `apertureFluxRegressionNonorthogonalModes_not_isApertureFluxOrthonormal`: individual
  normalization does not satisfy the mode-power bridge's family predicate.

## iii. Table of contents

- A. Exact coefficient vectors and synthesized profiles
- B. Unit self-flux and nonzero cross flux

## iv. References

This is a hostile regression for Physlib's normalization predicate. It adds no external physical
claim.
-/

@[expose] public section

namespace Optics

open InnerProductSpace MeasureTheory

noncomputable section

open HarmonicFieldProfile

/-!

## A. Exact coefficient vectors and synthesized profiles

-/

/-- The first coordinate pulse in the orthonormal two-profile fixture. -/
def apertureFluxRegressionBasisAmplitude : ModeAmplitude Bool :=
  WithLp.toLp 2 fun
    | false => 1
    | true => 0

/-- The normalized real `3-4-5` superposition coefficients. -/
def apertureFluxRegressionMixedAmplitude : ModeAmplitude Bool :=
  WithLp.toLp 2 fun
    | false => 3 / 5
    | true => 4 / 5

/-- A two-profile family whose members are individually normalized but not mutually orthogonal. -/
def apertureFluxRegressionNonorthogonalModes : Bool → HarmonicFieldProfile (Fin 2)
  | false => modeSynthesis apertureFluxRegressionPositiveModes
      apertureFluxRegressionBasisAmplitude
  | true => modeSynthesis apertureFluxRegressionPositiveModes
      apertureFluxRegressionMixedAmplitude

/-- Equal coordinates on the individually normalized but nonorthogonal profile family. -/
def apertureFluxRegressionNonorthogonalAmplitude : ModeAmplitude Bool :=
  WithLp.toLp 2 fun _ ↦ 1

/-- The first coordinate pulse has modal power one. -/
lemma apertureFluxRegressionBasisAmplitude_power :
    apertureFluxRegressionBasisAmplitude.power = 1 := by
  rw [ModeAmplitude.power_eq_sum_normSq]
  norm_num [apertureFluxRegressionBasisAmplitude, Complex.normSq_apply,
    Fintype.sum_bool]

/-- The exact `3-4-5` coefficient vector has modal power one. -/
lemma apertureFluxRegressionMixedAmplitude_power :
    apertureFluxRegressionMixedAmplitude.power = 1 := by
  rw [ModeAmplitude.power_eq_sum_normSq]
  norm_num [apertureFluxRegressionMixedAmplitude, Complex.normSq_apply,
    Fintype.sum_bool]

/-- Equal coordinates on the nonorthogonal family have modal coordinate power two. -/
lemma apertureFluxRegressionNonorthogonalAmplitude_power :
    apertureFluxRegressionNonorthogonalAmplitude.power = 2 := by
  rw [ModeAmplitude.power_eq_sum_normSq]
  norm_num [apertureFluxRegressionNonorthogonalAmplitude, Complex.normSq_apply,
    Fintype.sum_bool]

/-!

## B. Unit self-flux and nonzero cross flux

-/

/-- Both members of the nonorthogonal family nevertheless have unit integrated self-flux. -/
lemma apertureFluxRegressionNonorthogonalModes_each_normalized (i : Bool) :
    integratedMeanNormalFlux Measure.count apertureFluxRegressionPlane
        (apertureFluxRegressionNonorthogonalModes i) = 1 := by
  cases i
  · rw [apertureFluxRegressionNonorthogonalModes,
      apertureFluxRegressionPositiveModes_isApertureFluxOrthonormal.outgoing_modeSynthesis_power,
      apertureFluxRegressionBasisAmplitude_power]
  · rw [apertureFluxRegressionNonorthogonalModes,
      apertureFluxRegressionPositiveModes_isApertureFluxOrthonormal.outgoing_modeSynthesis_power,
      apertureFluxRegressionMixedAmplitude_power]

/-- The basis profile and normalized mixed profile have exact nonzero cross-pairing `3 / 5`. -/
lemma apertureFluxRegressionNonorthogonalModes_cross :
    signedNormalFluxPairing Measure.count apertureFluxRegressionPlane
        (apertureFluxRegressionNonorthogonalModes false)
        (apertureFluxRegressionNonorthogonalModes true) = 3 / 5 := by
  simp only [apertureFluxRegressionNonorthogonalModes]
  rw [apertureFluxRegressionPositiveModes_isApertureFluxOrthonormal.pairing_modeSynthesis]
  norm_num [PiLp.inner_apply, RCLike.inner_apply, Fintype.sum_bool,
    apertureFluxRegressionBasisAmplitude, apertureFluxRegressionMixedAmplitude,
    Complex.star_def, map_div₀, map_ofNat]

/-- The reverse cross-pairing is also `3 / 5`, now derived through Hermitian symmetry. -/
lemma apertureFluxRegressionNonorthogonalModes_reverse_cross :
    signedNormalFluxPairing Measure.count apertureFluxRegressionPlane
        (apertureFluxRegressionNonorthogonalModes true)
        (apertureFluxRegressionNonorthogonalModes false) = 3 / 5 := by
  rw [signedNormalFluxPairing_conj_symm,
    apertureFluxRegressionNonorthogonalModes_cross]
  norm_num [Complex.star_def, map_div₀, map_ofNat]

/-- The complete coherent expansion for equal coordinates has exact self-pairing `16 / 5`. -/
lemma apertureFluxRegressionNonorthogonalSynthesis_pairing :
    signedNormalFluxPairing Measure.count apertureFluxRegressionPlane
        (modeSynthesis apertureFluxRegressionNonorthogonalModes
          apertureFluxRegressionNonorthogonalAmplitude)
        (modeSynthesis apertureFluxRegressionNonorthogonalModes
          apertureFluxRegressionNonorthogonalAmplitude) = 16 / 5 := by
  have hself (i : Bool) :
      signedNormalFluxPairing Measure.count apertureFluxRegressionPlane
          (apertureFluxRegressionNonorthogonalModes i)
          (apertureFluxRegressionNonorthogonalModes i) = 1 := by
    rw [signedNormalFluxPairing_self,
      apertureFluxRegressionNonorthogonalModes_each_normalized]
    norm_num
  rw [signedNormalFluxPairing_modeSynthesis Measure.count apertureFluxRegressionPlane
    apertureFluxRegressionNonorthogonalModes (fun _ _ ↦ Integrable.of_finite)]
  norm_num [apertureFluxRegressionNonorthogonalAmplitude, Fintype.sum_bool,
    hself, apertureFluxRegressionNonorthogonalModes_cross,
    apertureFluxRegressionNonorthogonalModes_reverse_cross]

/-- The coherent field self-pairing is not the coordinate power without mutual orthogonality. -/
lemma apertureFluxRegressionNonorthogonalSynthesis_pairing_ne_power :
    signedNormalFluxPairing Measure.count apertureFluxRegressionPlane
        (modeSynthesis apertureFluxRegressionNonorthogonalModes
          apertureFluxRegressionNonorthogonalAmplitude)
        (modeSynthesis apertureFluxRegressionNonorthogonalModes
          apertureFluxRegressionNonorthogonalAmplitude) ≠
      apertureFluxRegressionNonorthogonalAmplitude.power := by
  rw [apertureFluxRegressionNonorthogonalSynthesis_pairing,
    apertureFluxRegressionNonorthogonalAmplitude_power]
  norm_num

/-- Individual unit normalization does not make the two-profile family flux-orthonormal. -/
lemma apertureFluxRegressionNonorthogonalModes_not_isApertureFluxOrthonormal :
    ¬ IsApertureFluxOrthonormal Measure.count apertureFluxRegressionPlane .outgoing
      apertureFluxRegressionNonorthogonalModes := by
  intro h
  have hzero := h.2.2 false true (by decide)
  rw [apertureFluxRegressionNonorthogonalModes_cross] at hzero
  norm_num at hzero

end


end Optics
