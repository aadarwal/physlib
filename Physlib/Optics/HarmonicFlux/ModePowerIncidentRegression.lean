/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.HarmonicFlux.ApertureRegressionOrthogonality
public import Physlib.Optics.HarmonicFlux.ModePower

/-!
# Incident-mode aperture-power regressions

## i. Overview

This file packages the exact negative-flux two-cell profile as a singleton incident family. The
amplitude `1 + I` has modal power two, while its synthesized signed normal flux is minus two. Thus
negating the flux recovers the positive incident-power convention.

These statements concern only the declared synthesis image. They make no modal-completeness,
Maxwell-propagation, or whole-device conservation claim.

## ii. Key results

- `apertureFluxRegressionNegativeMode_isApertureFluxOrthonormal`: incident normalization.
- `apertureFluxRegressionIncidentAmplitude_power`: independent coordinate power `2`.
- `apertureFluxRegressionIncidentSynthesis_pairing`: signed field pairing `-2`.
- `apertureFluxRegressionIncidentSynthesis_flux`: negative incident flux has magnitude `2`.

## iii. Table of contents

- A. Incident one-mode family
- B. Exact incident synthesis

## iv. References

This regression uses the finite-cell measure convention declared in `ApertureRegression`. It adds
no physical modal-normalization or device-losslessness claim.
-/

@[expose] public section

namespace Optics

open InnerProductSpace MeasureTheory

noncomputable section

open HarmonicFieldProfile

/-!

## A. Incident one-mode family

-/

/-- The negative-flux profile as a singleton incident family. -/
def apertureFluxRegressionNegativeMode : Unit → HarmonicFieldProfile (Fin 2) :=
  fun _ ↦ apertureFluxRegressionNegative

/-- The singleton negative profile is an incident unit-flux family. -/
lemma apertureFluxRegressionNegativeMode_isApertureFluxOrthonormal :
    IsApertureFluxOrthonormal Measure.count apertureFluxRegressionPlane .incident
      apertureFluxRegressionNegativeMode := by
  refine ⟨fun _ _ ↦ Integrable.of_finite, ?_, ?_⟩
  · intro i
    apply Complex.ofReal_injective
    rw [← signedNormalFluxPairing_self]
    simpa [apertureFluxRegressionNegativeMode] using apertureFluxRegressionNegative_self
  · intro i j hij
    exact (hij (Subsingleton.elim i j)).elim

/-!

## B. Exact incident synthesis

-/

/-- The exact singleton incident amplitude `1 + I`. -/
def apertureFluxRegressionIncidentAmplitude : ModeAmplitude Unit :=
  WithLp.toLp 2 fun _ ↦ 1 + Complex.I

/-- The singleton incident coordinate has exact normalized modal power two. -/
lemma apertureFluxRegressionIncidentAmplitude_power :
    apertureFluxRegressionIncidentAmplitude.power = 2 := by
  rw [ModeAmplitude.power_eq_sum_normSq]
  norm_num [apertureFluxRegressionIncidentAmplitude, Complex.normSq_apply]

/-- Expanding the singleton synthesis gives exact signed incident field pairing minus two. -/
lemma apertureFluxRegressionIncidentSynthesis_pairing :
    signedNormalFluxPairing Measure.count apertureFluxRegressionPlane
        (modeSynthesis apertureFluxRegressionNegativeMode
          apertureFluxRegressionIncidentAmplitude)
        (modeSynthesis apertureFluxRegressionNegativeMode
          apertureFluxRegressionIncidentAmplitude) = -2 := by
  rw [signedNormalFluxPairing_modeSynthesis Measure.count apertureFluxRegressionPlane
    apertureFluxRegressionNegativeMode (fun _ _ ↦ Integrable.of_finite)]
  norm_num [apertureFluxRegressionNegativeMode,
    apertureFluxRegressionIncidentAmplitude, apertureFluxRegressionNegative_self]
  ring_nf
  rw [Complex.I_sq]
  norm_num

/-- The negative of the independently computed synthesized incident flux is exactly two. -/
lemma apertureFluxRegressionIncidentSynthesis_flux :
    -integratedMeanNormalFlux Measure.count apertureFluxRegressionPlane
        (modeSynthesis apertureFluxRegressionNegativeMode
          apertureFluxRegressionIncidentAmplitude) = 2 := by
  have hself := signedNormalFluxPairing_self Measure.count apertureFluxRegressionPlane
    (modeSynthesis apertureFluxRegressionNegativeMode apertureFluxRegressionIncidentAmplitude)
  rw [apertureFluxRegressionIncidentSynthesis_pairing] at hself
  have hre := congrArg Complex.re hself
  norm_num at hre ⊢
  linarith

end

end Optics
