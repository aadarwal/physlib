/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Systems.PolarizerRetarderPhysicalPower
public import Physlib.Optics.Systems.PolarizerRetarderPhysicalRegression

/-!
# Physical polarizer-retarder aperture-flux regression

## i. Overview

This regression completes the connected P6b-3 fixture by proving the E3b outgoing normalization
of the retarded carrier directly from its actual one-period Poynting flux. Together with the
independently normalized incident carrier, the production transport theorem gives signed aperture
fluxes `-1` and `1 / 2` for a horizontal input, a `pi / 4` analyzer, and a positive zero-axis
quarter-wave plate.

## ii. Key results

- `polarizerRetarderPhysicalPowerRegression_output_isApertureFluxOrthonormal`: direct outgoing
  E3b normalization.
- `polarizerRetarderPhysicalPowerRegression_actualFluxes`: exact incident and output fluxes.
- `polarizerRetarderPhysicalPowerRegression_malus`: the connected actual-flux Malus identity.

## iii. Table of contents

- A. Direct outgoing normalization
- B. Connected actual-flux Malus law
- C. Sign-negative control

## iv. References

The E3b normalization hypotheses are proved for this coherent singleton fixture; they are not
inferred from raw Jones unitarity. The result does not cover partially polarized or coherency-
matrix mixtures and does not model rejected polarization, absorption, heating, or a complete
scattering device. Counting measure supplies one measured profile weight and is not geometric
aperture area.
-/

@[expose] public section

namespace Optics

open Electromagnetism Electromagnetism.ThreeDimension
open MeasureTheory Space Time

noncomputable section

/-!

## A. Direct outgoing normalization

-/

/-- The retarded unit Jones carrier has directly computed outgoing integrated normal flux one. -/
lemma polarizerRetarderPhysicalPowerRegression_output_integratedMeanNormalFlux :
    HarmonicFieldProfile.integratedMeanNormalFlux Measure.count
      polarizerModeNormalizationRegressionOutputPlane
      ((MaterialJonesMode.polarizerRetarderOutputFamily 0
        ((Real.pi / 2 : ℝ) : Real.Angle) ((Real.pi / 4 : ℝ) : Real.Angle)
        polarizerModeNormalizationRegressionMedium
        polarizerModeNormalizationRegressionFrame 1
        (by norm_num)).modeProfile polarizerModeNormalizationRegressionPoint ()) = 1 := by
  rw [← (MaterialJonesMode.polarizerRetarderOutputFamily 0
    ((Real.pi / 2 : ℝ) : Real.Angle) ((Real.pi / 4 : ℝ) : Real.Angle)
    polarizerModeNormalizationRegressionMedium polarizerModeNormalizationRegressionFrame 1
    (by norm_num)).integral_intervalAverage_normalFlux_eq_integratedMeanNormalFlux Measure.count
      polarizerModeNormalizationRegressionOutputPlane
      polarizerModeNormalizationRegressionPoint () (0 : Time)]
  simp only [MeasureTheory.integral_count, Fintype.sum_unique,
    MaterialJonesMode.polarizerRetarderOutputFamily, MaterialJonesMode.family]
  rw [ComplexMonochromaticPlaneWave.ofReal_electricField,
    ComplexMonochromaticPlaneWave.ofReal_magneticFieldStrength,
    JonesVector.normalComponent_toMaterialPlaneWave_intervalAverage_poyntingVector,
    JonesVector.materialPlaneWaveIrradiance, JonesMatrix.linearRetarder_act_intensity,
    JonesVector.intensity_linearPolarization,
    polarizerModeNormalizationRegressionMedium_waveImpedance]
  norm_num [polarizerModeNormalizationRegressionOutputPlane,
    polarizerModeNormalizationRegressionFrame,
    polarizerModeNormalizationRegressionDirection, PolarizationFrame.propagationVector,
    OrientedAffineHyperplane.normalComponent, OrientedAffineHyperplane.normalVector,
    PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_three]

/-- The retarded carrier satisfies the outgoing E3b aperture-flux normalization predicate. -/
lemma polarizerRetarderPhysicalPowerRegression_output_isApertureFluxOrthonormal :
    HarmonicFieldProfile.IsApertureFluxOrthonormal Measure.count
      polarizerModeNormalizationRegressionOutputPlane .outgoing
      ((MaterialJonesMode.polarizerRetarderOutputFamily 0
        ((Real.pi / 2 : ℝ) : Real.Angle) ((Real.pi / 4 : ℝ) : Real.Angle)
        polarizerModeNormalizationRegressionMedium
        polarizerModeNormalizationRegressionFrame 1
        (by norm_num)).modeProfile polarizerModeNormalizationRegressionPoint) := by
  refine ⟨fun _ _ => Integrable.of_finite, ?_, ?_⟩
  · intro i
    cases i
    exact polarizerRetarderPhysicalPowerRegression_output_integratedMeanNormalFlux
  · intro i j hij
    exact (hij (Subsingleton.elim i j)).elim

/-!

## B. Connected actual-flux Malus law

-/

/-- The connected fixture has incident flux `-1` and retarded output flux `1 / 2`. -/
lemma polarizerRetarderPhysicalPowerRegression_actualFluxes (startTime : Time) :
    (MaterialJonesMode.linearPolarizationFamily 0
      polarizerModeNormalizationRegressionMedium polarizerModeNormalizationRegressionFrame 1
      (by norm_num)).integratedActualMeanNormalFlux Measure.count
        polarizerModeNormalizationRegressionInputPlane
        polarizerModeNormalizationRegressionPoint (MaterialJonesMode.amplitude 1) startTime = -1 ∧
      (MaterialJonesMode.polarizerRetarderOutputFamily 0
        ((Real.pi / 2 : ℝ) : Real.Angle) ((Real.pi / 4 : ℝ) : Real.Angle)
        polarizerModeNormalizationRegressionMedium
        polarizerModeNormalizationRegressionFrame 1
        (by norm_num)).integratedActualMeanNormalFlux Measure.count
          polarizerModeNormalizationRegressionOutputPlane
          polarizerModeNormalizationRegressionPoint
          (JonesMatrix.linearPolarizerOutputAmplitude 1
            ((Real.pi / 4 : ℝ) : Real.Angle) 0) startTime = 1 / 2 := by
  constructor
  · have h := (MaterialJonesMode.linearPolarizationFamily 0
      polarizerModeNormalizationRegressionMedium polarizerModeNormalizationRegressionFrame 1
      (by norm_num)).incident_integratedActualMeanNormalFlux_eq_neg_power
        (polarizerModeNormalizationRegression_incident_isApertureFluxOrthonormal 0)
        (MaterialJonesMode.amplitude 1) startTime
    rw [polarizerRetarderPhysicalRegression_modePowers.1] at h
    linarith
  · calc
      _ = (JonesMatrix.linearPolarizerOutputAmplitude 1
          ((Real.pi / 4 : ℝ) : Real.Angle) 0).power :=
        (MaterialJonesMode.polarizerRetarderOutputFamily 0
          ((Real.pi / 2 : ℝ) : Real.Angle) ((Real.pi / 4 : ℝ) : Real.Angle)
          polarizerModeNormalizationRegressionMedium
          polarizerModeNormalizationRegressionFrame 1
          (by norm_num)).outgoing_integratedActualMeanNormalFlux_eq_power
            polarizerRetarderPhysicalPowerRegression_output_isApertureFluxOrthonormal _ _
      _ = 1 / 2 := polarizerRetarderPhysicalRegression_modePowers.2

/-- The directly normalized connected fixture instantiates the actual-flux Malus transport law. -/
lemma polarizerRetarderPhysicalPowerRegression_malus (startTime : Time) :
    (MaterialJonesMode.polarizerRetarderOutputFamily 0
      ((Real.pi / 2 : ℝ) : Real.Angle) ((Real.pi / 4 : ℝ) : Real.Angle)
      polarizerModeNormalizationRegressionMedium polarizerModeNormalizationRegressionFrame 1
      (by norm_num)).integratedActualMeanNormalFlux Measure.count
        polarizerModeNormalizationRegressionOutputPlane
        polarizerModeNormalizationRegressionPoint
        (JonesMatrix.linearPolarizerOutputAmplitude 1
          ((Real.pi / 4 : ℝ) : Real.Angle) 0) startTime =
      -(MaterialJonesMode.linearPolarizationFamily 0
        polarizerModeNormalizationRegressionMedium polarizerModeNormalizationRegressionFrame 1
        (by norm_num)).integratedActualMeanNormalFlux Measure.count
          polarizerModeNormalizationRegressionInputPlane
          polarizerModeNormalizationRegressionPoint (MaterialJonesMode.amplitude 1) startTime *
        Real.Angle.cos ((0 : Real.Angle) - ((Real.pi / 4 : ℝ) : Real.Angle)) ^ 2 := by
  exact JonesMatrix.linearRetarder_comp_linearPolarizer_malus_integratedActualMeanNormalFlux
    1 0 ((Real.pi / 2 : ℝ) : Real.Angle) ((Real.pi / 4 : ℝ) : Real.Angle) 0
    polarizerModeNormalizationRegressionMedium polarizerModeNormalizationRegressionFrame 1
    (by norm_num) (polarizerModeNormalizationRegression_incident_isApertureFluxOrthonormal 0)
    polarizerRetarderPhysicalPowerRegression_output_isApertureFluxOrthonormal startTime

/-!

## C. Sign-negative control

-/

/-- The outgoing signed flux is positive, so it cannot be the incident-oriented value `-1 / 2`. -/
lemma polarizerRetarderPhysicalPowerRegression_outputFlux_ne_negative (startTime : Time) :
    (MaterialJonesMode.polarizerRetarderOutputFamily 0
      ((Real.pi / 2 : ℝ) : Real.Angle) ((Real.pi / 4 : ℝ) : Real.Angle)
      polarizerModeNormalizationRegressionMedium polarizerModeNormalizationRegressionFrame 1
      (by norm_num)).integratedActualMeanNormalFlux Measure.count
        polarizerModeNormalizationRegressionOutputPlane
        polarizerModeNormalizationRegressionPoint
        (JonesMatrix.linearPolarizerOutputAmplitude 1
          ((Real.pi / 4 : ℝ) : Real.Angle) 0) startTime ≠ -1 / 2 := by
  rw [polarizerRetarderPhysicalPowerRegression_actualFluxes startTime |>.2]
  norm_num

end

end Optics
